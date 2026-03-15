import random
import string
import time
import threading
import argparse
import os

from flask import Flask, render_template
from flask_socketio import SocketIO
from pytchat import create
from dotenv import load_dotenv

load_dotenv()

# ======================
# CONFIG
# ======================

VIDEO_ID = os.environ.get("VIDEO_ID", "").strip()
PORT = int(os.environ.get("PORT", "5000"))
MOCK_CHAT = os.environ.get("MOCK_CHAT", "false").strip().lower() in {"1", "true", "yes", "on"}

GRID_SIZE = 9
MIN_WORDS = 4
MAX_WORDS = 5
MAX_ATTEMPTS = 200
COOLDOWN = 2
LEADERBOARD_RESET_INTERVAL = 15 * 60  # 15 minutes in seconds
INTERMISSION_DURATION = 10             # 20-second leaderboard-only transmission after leaderboard reset
ROUND_RESET_DELAY = 2                  # seconds between round end and next round start
WORDS_PER_ROUND_LIMIT = 6             # round resets when this many words are found
STREAM_CHECK_INTERVAL = 60          # seconds if not live


DIRECTIONS = [
    (0, 1), (0, -1),
    (1, 0), (-1, 0),
    (1, 1), (-1, -1),
    (1, -1), (-1, 1)
]

# ======================
# DICTIONARY LOADING
# ======================

def load_dictionary():
    """
    Load a set of valid English words (uppercase) using nltk if available,
    falling back to the system word list (/usr/share/dict/words on Linux/macOS).
    Words are filtered to WORD_MIN_LEN–WORD_MAX_LEN alpha-only characters.
    """
    word_set = set()

    # --- Try nltk first ---
    try:
        from nltk.corpus import words as nltk_words
        raw = nltk_words.words()
        for w in raw:
            w_up = w.upper()
            if w_up.isalpha():
                word_set.add(w_up)
        if word_set:
            print(f"📚 Loaded {len(word_set):,} words from nltk corpus.")
            return word_set
    except Exception:
        pass  # nltk not installed or corpus not downloaded

    # --- Try downloading nltk corpus if nltk is installed but corpus missing ---
    try:
        import nltk
        nltk.download("words", quiet=True)
        from nltk.corpus import words as nltk_words
        raw = nltk_words.words()
        for w in raw:
            w_up = w.upper()
            if w_up.isalpha():
                word_set.add(w_up)
        if word_set:
            print(f"📚 Loaded {len(word_set):,} words from nltk corpus (auto-downloaded).")
            return word_set
    except Exception:
        pass

    # --- Fallback: system word list ---
    system_paths = [
        "/usr/share/dict/words",       # Linux / macOS
        "/usr/dict/words",
    ]
    for path in system_paths:
        if os.path.isfile(path):
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                for line in f:
                    w_up = line.strip().upper()
                    if w_up.isalpha():
                        word_set.add(w_up)
            if word_set:
                print(f"📚 Loaded {len(word_set):,} words from {path}.")
                return word_set

    # --- Last resort: hardcoded fallback list ---
    print("⚠️  No external dictionary found. Using built-in fallback word list.")
    fallback = [
        "HELLO", "WORLD", "PYTHON", "PUZZLE", "SEARCH", "GRID", "RANDOM", "CODE",
        "DEBUG", "ALPHA", "OMEGA", "ARRAY", "LOOP", "STACK", "QUEUE",
        "INPUT", "OUTPUT", "VALUE", "INDEX", "LOGIC", "FLOAT", "STRING", "CLASS",
        "OBJECT", "METHOD", "IMPORT", "EXPORT", "BINARY", "CACHE", "SERVER",
        "CLIENT", "SCRIPT", "BRANCH", "MERGE", "COMMIT", "PUSH", "PULL", "CLONE",
        "FETCH", "BUILD", "DEPLOY", "TEST", "ERROR", "PATCH",
        "UPDATE", "DELETE", "INSERT", "SELECT", "CREATE", "ALTER",
        "TABLE", "QUERY", "MODEL", "TRAIN", "DATA", "GRAPH", "NODE", "EDGE",
        "TREE", "HEAP", "SORT", "QUICK", "COUNT",
        "TOKEN", "PARSE", "SCAN", "WRITE", "READ", "OPEN", "CLOSE", "PRINT",
        "FILE", "FOLDER", "DRIVE", "CLOUD", "LOCAL", "HOST", "PORT",
        "ROUTE", "LOGIN", "LOGOUT", "ADMIN", "GUEST", "LEVEL", "SCOPE", "STATE",
        "EVENT", "CLICK", "PRESS", "HOVER"
    ]
    for w in fallback:
        word_set.add(w.upper())
    return word_set

# Full universal dictionary — every valid English word — used for answer validation
DICTIONARY: set = load_dictionary()

# Fixed word pool used when selecting words to place in the grid each round
EASY_WORDS: list = [
    "HELLO", "WORLD", "PYTHON", "PUZZLE", "SEARCH", "GRID", "RANDOM", "CODE",
    "PROGAM", "DEBUG", "ALPHA", "OMEGA", "ARRAY", "LOOP", "STACK", "QUEUE",
    "INPUT", "OUTPUT", "VALUE", "INDEX", "LOGIC", "FLOAT", "STRING", "CLASS",
    "OBJECT", "METHOD", "IMPORT", "EXPORT", "BINARY", "CACHE", "SERVER",
    "CLIENT", "SCRIPT", "BRANCH", "MERGE", "COMMIT", "PUSH", "PULL", "CLONE",
    "FETCH", "BUILD", "DEPLOY", "RUN", "TEST", "ERROR", "FIX", "PATCH",
    "UPDATE", "DELETE", "INSERT", "SELECT", "CREATE", "DROP", "ALTER",
    "TABLE", "QUERY", "MODEL", "TRAIN", "DATA", "GRAPH", "NODE", "EDGE",
    "TREE", "HEAP", "SORT",  "QUICK", "COUNT", "RADIX",
    "TOKEN", "PARSE", "SCAN", "WRITE", "READ", "OPEN", "CLOSE", "PRINT",
    "INPUT", "FILE", "FOLDER", "DRIVE", "CLOUD", "LOCAL", "HOST", "PORT",
    "ROUTE", "LOGIN", "LOGOUT", "ADMIN", "GUEST", "LEVEL", "SCOPE", "STATE",
    "EVENT", "CLICK", "PRESS", "HOVER"
]

print(f"Grid pool: {len(EASY_WORDS)} words | Validation pool: {len(DICTIONARY):,} total words")

# ======================
# GAME ENGINE
# ======================

def create_empty_grid(size):
    return [[None for _ in range(size)] for _ in range(size)]

def random_letter():
    return random.choice(string.ascii_uppercase)

def place_word(grid, word):
    size = len(grid)

    for _ in range(MAX_ATTEMPTS):
        dx, dy = random.choice(DIRECTIONS)
        row = random.randint(0, size - 1)
        col = random.randint(0, size - 1)

        end_row = row + dx * (len(word) - 1)
        end_col = col + dy * (len(word) - 1)

        if not (0 <= end_row < size and 0 <= end_col < size):
            continue

        valid = True
        for i in range(len(word)):
            r = row + dx * i
            c = col + dy * i
            if grid[r][c] is not None and grid[r][c] != word[i]:
                valid = False
                break

        if not valid:
            continue

        for i in range(len(word)):
            r = row + dx * i
            c = col + dy * i
            grid[r][c] = word[i]

        return True

    return False

def fill_random_letters(grid):
    for r in range(len(grid)):
        for c in range(len(grid)):
            if grid[r][c] is None:
                grid[r][c] = random_letter()

def search_word(grid, word):
    size = len(grid)

    for r in range(size):
        for c in range(size):
            if grid[r][c] != word[0]:
                continue

            for dx, dy in DIRECTIONS:
                match = True
                for i in range(len(word)):
                    nr = r + dx * i
                    nc = c + dy * i

                    if not (0 <= nr < size and 0 <= nc < size):
                        match = False
                        break

                    if grid[nr][nc] != word[i]:
                        match = False
                        break

                if match:
                    return True
    return False

def is_valid_dictionary_word(word: str) -> bool:
    """Return True if word (uppercase) exists in the loaded dictionary."""
    return word.upper() in DICTIONARY

# ======================
# GAME STATE
# ======================

grid = create_empty_grid(GRID_SIZE)
scores = {}
answered_words = set()
last_answer_time = {}
processed_messages = set()
current_words = []
round_number = 0
words_found_this_round = 0  # tracks how many words discovered this round

# scheduling flag and helper to delay round reset
next_round_scheduled = False

def schedule_next_round(delay=5):
    global next_round_scheduled
    if next_round_scheduled:
        return
    next_round_scheduled = True

    def worker():
        time.sleep(delay)
        print(f"⏳ {delay}s break over, generating new round")
        generate_round(reset_scores=False)
        global next_round_scheduled
        next_round_scheduled = False

    threading.Thread(target=worker, daemon=True).start()

# ======================
# PYTCHAT
# ======================

def get_chat_stream(video_id):
    """Initialize pytchat connection to YouTube live stream - must be called from main thread"""
    if not video_id:
        print("❌ VIDEO_ID is not configured.")
        return None

    try:
        chat = create(video_id=video_id)
        print(f"✅ Connected to YouTube live chat for video: {video_id}")
        return chat
    except RuntimeError as e:
        if "signal only works in main thread" in str(e):
            print(f"❌ Pytchat must run in main thread. Retrying...")
        else:
            print(f"❌ Error connecting to chat: {e}")
        return None
    except Exception as e:
        print(f"❌ Error connecting to chat: {e}")
        return None

# ======================
# ROUND SYSTEM
# ======================

def generate_round(emit=True, reset_scores=False):
    global grid, answered_words, current_words, scores, round_number, words_found_this_round

    grid = create_empty_grid(GRID_SIZE)
    answered_words = set()
    words_found_this_round = 0

    if reset_scores:
        scores = {}
        round_number = 1
        print("🔄 Leaderboard reset for new round.")
    else:
        round_number += 1

    # Pick random words from the loaded dictionary
    count = random.randint(MIN_WORDS, MAX_WORDS)
    current_words = random.sample(EASY_WORDS, count)

    for word in current_words:
        place_word(grid, word)

    fill_random_letters(grid)

    print(f"🎮 New round! Words in grid: {current_words}")

    if emit:
        socketio.emit("new_round", {"words": current_words, "round": round_number, "total_words": len(current_words)})
        update_ui()

def leaderboard_timer():
    """Fires every 15 minutes: show 20s leaderboard-only transmission, then reset scores and start new round."""
    while True:
        next_reset = time.time() + LEADERBOARD_RESET_INTERVAL
        while True:
            remaining = int(next_reset - time.time())
            if remaining <= 0:
                break
            try:
                socketio.emit('leaderboard_countdown', {'remaining': remaining})
            except Exception:
                pass
            time.sleep(1)

        print("⏱ 15-min leaderboard reset triggered — starting intermission...")
        start_intermission(duration=INTERMISSION_DURATION, reset_scores=True)

def start_intermission(duration=INTERMISSION_DURATION, reset_scores=False):
    global scores
    print(f"⏸ Intermission: showing leaderboard for {duration} seconds (reset_scores={reset_scores})")
    socketio.emit("intermission", {"scores": scores, "duration": duration})

    for remaining in range(duration, 0, -1):
        socketio.emit("intermission_tick", {"remaining": remaining})
        time.sleep(1)

    generate_round(reset_scores=reset_scores)

# ======================
# FLASK SERVER
# ======================

app = Flask(__name__)
socketio = SocketIO(app, async_mode="threading")

@app.route("/")
def index():
    return render_template("overlay.html")

@socketio.on("connect")
def handle_connect():
    print("Frontend connected")
    socketio.emit("update_grid", grid)
    socketio.emit("update_scores", scores)
    socketio.emit("new_round", {"words": current_words, "round": round_number})

def update_ui():
    socketio.emit("update_grid", grid)
    socketio.emit("update_scores", scores)


def announce_winner(user, word, points=0):
    payload = {"user": user, "word": word, "points": points}
    socketio.emit("winner", payload)

# ======================
# CHAT MESSAGE HANDLER
# ======================

def handle_chat_message(author: str, text: str):
    """
    Process a single chat message.
    Awards points if:
      1. The candidate word hasn't been found this round yet.
      2. The candidate word actually appears in the grid.
      3. The candidate word is a valid English word (exists in DICTIONARY).
    Round resets when 7 total words are found OR all fixed target words are found.
    """
    global answered_words, scores, words_found_this_round

    if not text:
        return

    candidate = text.split()[0].upper()

    # Must be alphabetic and more than 1 letter
    if not candidate.isalpha() or len(candidate) < 2:
        return

    # Must be more than 2 letters
    if len(candidate) <= 2:
        return

    # Cooldown check
    now = time.time()
    if author in last_answer_time:
        if now - last_answer_time[author] < COOLDOWN:
            return
    last_answer_time[author] = now

    # Already found this round
    if candidate in answered_words:
        return

    # Must exist in the grid
    if not search_word(grid, candidate):
        return

    # Must be a valid dictionary word
    if not is_valid_dictionary_word(candidate):
        print(f"❌ '{candidate}' found in grid but not a valid word — ignoring")
        return

    # ✅ Valid answer
    answered_words.add(candidate)
    words_found_this_round += 1
    points = len(candidate)
    scores[author] = scores.get(author, 0) + points
    print(f"✅ {author} found '{candidate}' (+{points} pts) | {'[BONUS]' if candidate not in current_words else '[TARGET]'} | words_this_round={words_found_this_round}")
    announce_winner(author, candidate, points)
    update_ui()

    # Round reset condition: 7 words found OR all fixed target words found
    all_targets_found = all(w in answered_words for w in current_words)
    if words_found_this_round >= WORDS_PER_ROUND_LIMIT or all_targets_found:
        reason = f"{WORDS_PER_ROUND_LIMIT} words found" if words_found_this_round >= WORDS_PER_ROUND_LIMIT else "all target words found"
        print(f"🎉 Round over ({reason})! Starting new round in {ROUND_RESET_DELAY}s…")
        schedule_next_round(delay=ROUND_RESET_DELAY)

# ======================
# CHAT LOOP
# ======================

def chat_loop():
    """Listen to YouTube live chat using pytchat - runs in main thread"""
    while True:
        chat = get_chat_stream(VIDEO_ID)
        if not chat:
            print("❌ Failed to connect to chat. Retrying in 10s...")
            time.sleep(10)
            continue

        try:
            while chat.is_alive():
                try:
                    chatdata = chat.get()
                    if not chatdata or not chatdata.items:
                        continue

                    for item in chatdata.items:
                        msg_id = item.id if hasattr(item, 'id') else ''
                        if msg_id in processed_messages:
                            continue
                        processed_messages.add(msg_id)

                        author = 'Unknown'
                        text = ''

                        if hasattr(item, 'author'):
                            author_info = item.author
                            if isinstance(author_info, dict):
                                author = author_info.get('name', 'Unknown')
                            elif hasattr(author_info, 'name'):
                                author = author_info.name

                        if hasattr(item, 'message'):
                            text = str(item.message).strip()

                        handle_chat_message(author, text)

                except Exception as inner_e:
                    print(f"[ERROR in message processing] {inner_e}")
                    import traceback
                    traceback.print_exc()

                time.sleep(0.5)

            print("⏱️ Stream ended, reconnecting...")
            time.sleep(5)

        except Exception as e:
            print(f"❌ Chat error: {e}")
            import traceback
            traceback.print_exc()
            time.sleep(5)

# ======================
# MAIN
# ======================

def mock_chat_loop():
    """Simulate chat messages for testing without YouTube auth"""
    test_users = ["Player1", "Player2", "Player3", "Player4"]

    time.sleep(3)
    while True:
        time.sleep(random.randint(2, 5))

        user = random.choice(test_users)
        # Mock players try current_words targets as well as random dictionary words
        if random.random() < 0.7 and current_words:
            word = random.choice(current_words)
        else:
            word = random.choice(EASY_WORDS)

        print(f"[MOCK] {user}: {word}")
        handle_chat_message(user, word)

def start_server():
    socketio.run(app, host="0.0.0.0", port=PORT, debug=False)


def run_application(use_mock=False):
    generate_round()

    threading.Thread(target=leaderboard_timer, daemon=True).start()

    if use_mock:
        print("🎮 Running in MOCK mode (simulated chat, no YouTube needed)")
        print(f"🌐 Starting Flask server on port {PORT}")
        threading.Thread(target=mock_chat_loop, daemon=True).start()
        start_server()
        return

    if VIDEO_ID:
        print("🔴 Running in LIVE mode (using pytchat for YouTube chat scraping)")
        print("📡 Connecting to YouTube live chat...")
        print(f"🌐 Starting Flask server on port {PORT}")
        threading.Thread(target=start_server, daemon=True).start()
        chat_loop()
        return

    print("⚠️ VIDEO_ID is not set. Starting overlay without chat input.")
    print(f"🌐 Starting Flask server on port {PORT}")
    start_server()

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run the word grid game or print the current round words.")
    parser.add_argument("--print-words", action="store_true", help="Generate a round and print the filled words and grid, then exit")
    parser.add_argument("--mock", action="store_true", help="Use mock chat for testing (no YouTube auth needed)")
    args = parser.parse_args()

    if args.print_words:
        generate_round(emit=False)
        print("Words in grid:", current_words)
        print("Grid:")
        for row in grid:
            print(" ".join(row))
        exit(0)

    try:
        run_application(use_mock=args.mock or MOCK_CHAT)
    except KeyboardInterrupt:
        print("\n👋 Shutting down...")