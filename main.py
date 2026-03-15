# main.py
"""
Word-hunt overlay server (Flask + SocketIO) optimized for Render Web Service.

Usage:
  - Start normally:       python main.py
  - Mock chat:            python main.py --mock
Environment variables:
  - PORT (render sets this automatically)
  - VIDEO_ID  (YouTube video id)
  - YT_API_KEY (optional) - if provided, will use YouTube Data API polling (recommended)
  - MOCK_CHAT (true/1/yes to enable mock)
"""

import os
import time
import random
import string
import threading
import argparse
import logging
import requests

from flask import Flask, render_template
from flask_socketio import SocketIO

# Try to import pytchat (fallback). If not installed, that's OK if YT_API_KEY is provided.
try:
    import pytchat
    HAVE_PYTCHAT = True
except Exception:
    HAVE_PYTCHAT = False

# Optional .env loader
try:
    from dotenv import load_dotenv
    load_dotenv()
except Exception:
    pass

# -----------------------
# Configuration / env
# -----------------------
VIDEO_ID = os.environ.get("VIDEO_ID", "").strip()
PORT = int(os.environ.get("PORT", os.environ.get("RENDER_PORT", 5000)))
MOCK_CHAT = os.environ.get("MOCK_CHAT", "false").strip().lower() in {"1", "true", "yes", "on"}
YT_API_KEY = os.environ.get("YT_API_KEY", "").strip()
USE_YT_API = bool(YT_API_KEY)

# Game tuning (you can tweak)
GRID_SIZE = 9
MIN_WORDS = 4
MAX_WORDS = 6
MAX_ATTEMPTS = 200
COOLDOWN = 2
LEADERBOARD_RESET_INTERVAL = 15 * 60
INTERMISSION_DURATION = 10
ROUND_RESET_DELAY = 2
WORDS_PER_ROUND_LIMIT = 6
STREAM_CHECK_INTERVAL = 60

DIRECTIONS = [
    (0, 1), (0, -1),
    (1, 0), (-1, 0),
    (1, 1), (-1, -1),
    (1, -1), (-1, 1)
]

# -----------------------
# Logging
# -----------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
)
log = logging.getLogger("wordhunt")

# -----------------------
# Dictionary & word pool
# -----------------------
def load_dictionary():
    word_set = set()
    try:
        from nltk.corpus import words as nltk_words
        raw = nltk_words.words()
        for w in raw:
            w_up = w.upper()
            if w_up.isalpha():
                word_set.add(w_up)
        if word_set:
            log.info("Loaded %d words from nltk corpus.", len(word_set))
            return word_set
    except Exception:
        pass

    # Fallback system files
    system_paths = ["/usr/share/dict/words", "/usr/dict/words"]
    for path in system_paths:
        if os.path.isfile(path):
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                for line in f:
                    w_up = line.strip().upper()
                    if w_up.isalpha():
                        word_set.add(w_up)
            if word_set:
                log.info("Loaded %d words from %s.", len(word_set), path)
                return word_set

    # Built-in fallback
    fallback = [
        "HELLO","WORLD","PYTHON","PUZZLE","SEARCH","GRID","RANDOM","CODE",
        "DEBUG","ALPHA","OMEGA","ARRAY","LOOP","STACK","QUEUE",
        "INPUT","OUTPUT","VALUE","INDEX","LOGIC","FLOAT","STRING","CLASS",
        "OBJECT","METHOD","IMPORT","EXPORT","BINARY","CACHE","SERVER",
        "CLIENT","SCRIPT","BRANCH","MERGE","COMMIT","PUSH","PULL","CLONE",
        "FETCH","BUILD","DEPLOY","TEST","ERROR","PATCH",
        "UPDATE","DELETE","INSERT","SELECT","CREATE","ALTER",
        "TABLE","QUERY","MODEL","TRAIN","DATA","GRAPH","NODE","EDGE",
        "TREE","HEAP","SORT","QUICK","COUNT","TOKEN","PARSE","SCAN",
        "WRITE","READ","OPEN","CLOSE","PRINT","FILE","FOLDER","DRIVE",
        "CLOUD","LOCAL","HOST","PORT","ROUTE","LOGIN","LOGOUT",
        "ATOM","ENERGY","MUSIC","MOVIE","LOVE","HAPPY","ROBOT","DRAGON"
    ]
    for w in fallback:
        word_set.add(w.upper())
    log.warning("No external dictionary found; using small built-in fallback (%d words).", len(word_set))
    return word_set

DICTIONARY = load_dictionary()

EASY_WORDS = list(DICTIONARY)[:200]  # keep a manageable pool; you can expand this list

log.info("Grid pool: %d words | Validation pool: %d total words", len(EASY_WORDS), len(DICTIONARY))

# -----------------------
# Game engine
# -----------------------
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
    return word.upper() in DICTIONARY

# -----------------------
# State
# -----------------------
grid = create_empty_grid(GRID_SIZE)
scores = {}
answered_words = set()
last_answer_time = {}
processed_messages = set()
current_words = []
round_number = 0
words_found_this_round = 0
next_round_scheduled = False
lock = threading.Lock()  # small lock for shared state updates

def schedule_next_round(delay=5):
    global next_round_scheduled
    if next_round_scheduled:
        return
    next_round_scheduled = True
    def worker():
        time.sleep(delay)
        log.info("%ds break over, generating new round", delay)
        generate_round(reset_scores=False)
        global next_round_scheduled
        next_round_scheduled = False
    threading.Thread(target=worker, daemon=True).start()

# -----------------------
# Pytchat (fallback)
# -----------------------
def get_pytchat_stream(video_id):
    if not HAVE_PYTCHAT:
        log.warning("pytchat not installed; skipping pytchat path.")
        return None
    try:
        chat = pytchat.create(video_id=video_id)
        log.info("pytchat connected to video: %s", video_id)
        return chat
    except RuntimeError as e:
        # pytchat may complain "signal only works in main thread" if run in non-main thread
        log.warning("pytchat runtime error: %s", e)
        return None
    except Exception as e:
        log.warning("pytchat error: %s", e)
        return None

# -----------------------
# YouTube Data API polling (recommended for cloud hosts)
# -----------------------
def youtube_api_get_live_chat_id(video_id):
    """Return liveChatId if live, else None."""
    if not YT_API_KEY:
        return None
    try:
        url = "https://www.googleapis.com/youtube/v3/videos"
        params = {"part": "liveStreamingDetails", "id": video_id, "key": YT_API_KEY}
        r = requests.get(url, params=params, timeout=10)
        r.raise_for_status()
        data = r.json()
        items = data.get("items", [])
        if not items:
            return None
        live_details = items[0].get("liveStreamingDetails", {})
        return live_details.get("activeLiveChatId")
    except Exception as e:
        log.warning("youtube_api_get_live_chat_id error: %s", e)
        return None

def youtube_api_poll_loop(video_id):
    """Poll YouTube LiveChatMessages using the Data API (requires YT_API_KEY)."""
    log.info("Starting YouTube Data API poller for video %s", video_id)
    live_chat_id = None
    next_page_token = None
    polling_interval = 2.0

    while True:
        try:
            if not live_chat_id:
                live_chat_id = youtube_api_get_live_chat_id(video_id)
                if not live_chat_id:
                    log.info("No active liveChatId for video %s (not live?) - retrying in 10s", video_id)
                    time.sleep(10)
                    continue
                log.info("Found liveChatId: %s", live_chat_id)

            url = "https://www.googleapis.com/youtube/v3/liveChat/messages"
            params = {
                "part": "snippet,authorDetails",
                "liveChatId": live_chat_id,
                "key": YT_API_KEY,
                "maxResults": 200
            }
            if next_page_token:
                params["pageToken"] = next_page_token

            r = requests.get(url, params=params, timeout=15)
            if r.status_code == 403:
                log.warning("YouTube API 403 (maybe quota or permission). Sleeping 30s.")
                time.sleep(30)
                continue
            r.raise_for_status()
            data = r.json()

            polling_interval_ms = data.get("pollingIntervalMillis")
            if polling_interval_ms:
                polling_interval = max(0.5, polling_interval_ms / 1000.0)

            items = data.get("items", [])
            for item in items:
                # message id (unique)
                msg_id = item.get("id")
                if not msg_id:
                    continue
                with lock:
                    if msg_id in processed_messages:
                        continue
                    processed_messages.add(msg_id)

                author = item.get("authorDetails", {}).get("displayName", "Unknown")
                snippet = item.get("snippet", {})
                # message text can be in 'displayMessage' or 'textMessageDetails'
                text = snippet.get("displayMessage") or ""
                # handle it
                handle_chat_message(author, text)

            next_page_token = data.get("nextPageToken")
            time.sleep(polling_interval)
        except Exception as e:
            log.exception("Error in youtube_api_poll_loop: %s", e)
            time.sleep(5)

# -----------------------
# Game rounds, timers, UI updates
# -----------------------
def generate_round(emit=True, reset_scores=False):
    global grid, answered_words, current_words, scores, round_number, words_found_this_round
    with lock:
        grid = create_empty_grid(GRID_SIZE)
        answered_words = set()
        words_found_this_round = 0
        if reset_scores:
            scores = {}
            round_number = 1
            log.info("Leaderboard reset for new round.")
        else:
            round_number += 1
    # pick words
    count = random.randint(MIN_WORDS, MAX_WORDS)
    current_words[:] = random.sample(EASY_WORDS, min(count, len(EASY_WORDS)))
    for word in current_words:
        place_word(grid, word)
    fill_random_letters(grid)
    log.info("New round created: %s", current_words)
    if emit:
        socketio.emit("new_round", {"words": current_words, "round": round_number, "total_words": len(current_words)})
        update_ui()

def leaderboard_timer():
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
        log.info("Leaderboard reset triggered — starting intermission...")
        start_intermission(duration=INTERMISSION_DURATION, reset_scores=True)

def start_intermission(duration=INTERMISSION_DURATION, reset_scores=False):
    global scores
    log.info("Intermission: showing leaderboard for %d seconds (reset_scores=%s)", duration, reset_scores)
    socketio.emit("intermission", {"scores": scores, "duration": duration})
    for remaining in range(duration, 0, -1):
        socketio.emit("intermission_tick", {"remaining": remaining})
        time.sleep(1)
    generate_round(reset_scores=reset_scores)

# -----------------------
# Flask + SocketIO
# -----------------------
app = Flask(__name__, template_folder="templates")
# let SocketIO choose the best async mode; eventlet recommended in requirements
socketio = SocketIO(app)

@app.route("/")
def index():
    # ensure overlay.html exists in templates/
    return render_template("overlay.html")

@socketio.on("connect")
def on_connect():
    log.info("Frontend connected")
    socketio.emit("update_grid", grid)
    socketio.emit("update_scores", scores)
    socketio.emit("new_round", {"words": current_words, "round": round_number})

def update_ui():
    socketio.emit("update_grid", grid)
    socketio.emit("update_scores", scores)

def announce_winner(user, word, points=0):
    payload = {"user": user, "word": word, "points": points}
    socketio.emit("winner", payload)

# -----------------------
# Chat message handler
# -----------------------
def handle_chat_message(author: str, text: str):
    """Process incoming chat message and award points if valid."""
    global answered_words, scores, words_found_this_round
    if not text:
        return
    # extract first alphabetic token longer than 2 chars
    tokens = [t.upper() for t in text.split() if t.isalpha() and len(t) > 2]
    if not tokens:
        return
    candidate = tokens[0]
    now = time.time()
    with lock:
        if author in last_answer_time and now - last_answer_time[author] < COOLDOWN:
            return
        last_answer_time[author] = now
        if candidate in answered_words:
            return
        if not search_word(grid, candidate):
            return
        if not is_valid_dictionary_word(candidate):
            log.info("'%s' found in grid but not in dictionary — ignoring", candidate)
            return
        # valid answer
        answered_words.add(candidate)
        words_found_this_round += 1
        points = len(candidate)
        scores[author] = scores.get(author, 0) + points
    log.info("%s found '%s' (+%d) | words_this_round=%d", author, candidate, points, words_found_this_round)
    announce_winner(author, candidate, points)
    update_ui()
    # round reset conditions
    with lock:
        all_targets_found = all(w in answered_words for w in current_words)
        if words_found_this_round >= WORDS_PER_ROUND_LIMIT or all_targets_found:
            reason = f"{WORDS_PER_ROUND_LIMIT} words found" if words_found_this_round >= WORDS_PER_ROUND_LIMIT else "all target words found"
            log.info("Round over (%s). Starting new round in %ds", reason, ROUND_RESET_DELAY)
            schedule_next_round(delay=ROUND_RESET_DELAY)

# -----------------------
# Chat loop (pytchat fallback)
# -----------------------
def pytchat_loop(video_id):
    log.info("Starting pytchat loop for video %s", video_id)
    while True:
        chat = get_pytchat_stream(video_id)
        if not chat:
            log.info("pytchat: failed to get chat; retrying in 10s")
            time.sleep(10)
            continue
        try:
            while chat.is_alive():
                chatdata = chat.get()
                if not chatdata or not chatdata.items:
                    time.sleep(0.5)
                    continue
                for item in chatdata.items:
                    msg_id = getattr(item, "id", None)
                    if not msg_id:
                        continue
                    with lock:
                        if msg_id in processed_messages:
                            continue
                        processed_messages.add(msg_id)
                    author = "Unknown"
                    if hasattr(item, "author"):
                        author_info = item.author
                        if isinstance(author_info, dict):
                            author = author_info.get("name", "Unknown")
                        elif hasattr(author_info, "name"):
                            author = author_info.name
                    text = getattr(item, "message", "") or ""
                    handle_chat_message(author, text)
                time.sleep(0.2)
            log.info("pytchat stream ended; reconnecting...")
            time.sleep(5)
        except Exception as e:
            log.exception("Error in pytchat loop: %s", e)
            time.sleep(5)

# -----------------------
# Mock chat loop (testing)
# -----------------------
def mock_chat_loop():
    test_users = ["Player1", "Player2", "Player3", "Player4"]
    time.sleep(2)
    while True:
        time.sleep(random.randint(2, 5))
        user = random.choice(test_users)
        if random.random() < 0.7 and current_words:
            word = random.choice(current_words)
        else:
            word = random.choice(EASY_WORDS)
        log.info("[MOCK] %s: %s", user, word)
        handle_chat_message(user, word)

# -----------------------
# Server start (must be main thread for Render port detection)
# -----------------------
def start_server():
    log.info("Starting Flask server on port %d", PORT)
    # allow_unsafe_werkzeug avoids the RuntimeError in some environments (Render)
    socketio.run(app, host="0.0.0.0", port=PORT, debug=False, allow_unsafe_werkzeug=True)

# -----------------------
# Application entrypoint
# -----------------------
def main(use_mock=False):
    # Prepare initial round and timers
    generate_round()
    threading.Thread(target=leaderboard_timer, daemon=True).start()
    # Chat source selection order:
    # 1) MOCK
    # 2) YouTube Data API (if YT_API_KEY set)
    # 3) pytchat fallback (if installed)
    if use_mock:
        log.info("Starting in MOCK mode")
        threading.Thread(target=mock_chat_loop, daemon=True).start()
    else:
        if USE_YT_API and VIDEO_ID:
            log.info("Using YouTube Data API (YT_API_KEY provided) for live chat polling")
            threading.Thread(target=youtube_api_poll_loop, args=(VIDEO_ID,), daemon=True).start()
        elif VIDEO_ID and HAVE_PYTCHAT:
            log.info("Using pytchat fallback for live chat (pytchat installed)")
            # pytchat sometimes expects main thread; keep it in a thread and let it retry if needed.
            threading.Thread(target=pytchat_loop, args=(VIDEO_ID,), daemon=True).start()
        elif VIDEO_ID and not HAVE_PYTCHAT and not USE_YT_API:
            log.warning("VIDEO_ID is set but neither YT_API_KEY nor pytchat available. Falling back to overlay-only.")
        else:
            log.info("No VIDEO_ID provided: starting overlay without chat input.")
    # Start Flask server in main thread so Render detects the port
    start_server()

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--mock", action="store_true", help="Run with mock chat messages")
    args = parser.parse_args()
    try:
        main(use_mock=args.mock or MOCK_CHAT)
    except KeyboardInterrupt:
        log.info("Shutting down...")
