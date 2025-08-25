from flask import Flask, request, jsonify, send_file
import subprocess
import os
import ast
import time
import re
from datetime import datetime, timezone, date
import sqlite3
import threading
import base64
from flask_cors import CORS
import logging
import tempfile

try:
    import resource
    IS_UNIX = True
except ImportError:
    IS_UNIX = False

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

app = Flask(__name__)
CORS(app)

DATA_DIR = os.environ.get("RENDER_DISK_PATH", "data")
TEMP_DIR = os.path.join(DATA_DIR, "temp")
DB_FILE = os.path.join(DATA_DIR, "ratelimit.db")

os.makedirs(DATA_DIR, exist_ok=True)
os.makedirs(TEMP_DIR, exist_ok=True)

API_KEY = os.environ.get("PYTHON_EXE_KEY")
BURST_LIMIT = 5
RPM_LIMIT = 5
REFILL_RATE_PER_SECOND = RPM_LIMIT / 60.0
RPD_LIMIT = 30
MAX_ATTACHMENTS = 2
MAX_FILE_SIZE_MB = 8
MAX_FILE_SIZE_BYTES = MAX_FILE_SIZE_MB * 1024 * 1024
MAX_CHILD_PROCESSES = 10
MAX_CONCURRENT_SUBPROCESSES = 5
CLEANUP_INTERVAL_SECONDS = 3600

rate_limit_lock = threading.Lock()
rate_limit_data = {}
subprocess_lock = threading.Lock()
active_subprocess_count = 0

ALLOWED_PUBLIC_IMPORTS = {
    "math", "statistics", "decimal", "fractions", "numbers", "random", "numpy",
    "datetime", "time", "calendar", "string", "re", "textwrap", "unicodedata",
    "collections", "itertools", "functools", "operator", "bisect", "heapq", "array",
    "json", "ast", "typing", "enum", "dataclasses", "copy", "pprint",
    "hashlib", "uuid", "secrets", "base64",
    "PIL", "reportlab", "fpdf",
}

def setup_database():
    conn = sqlite3.connect(DB_FILE)
    cursor = conn.cursor()
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS daily_requests (
            ip_address TEXT, request_date DATE, request_count INTEGER,
            PRIMARY KEY (ip_address, request_date)
        )''')
    conn.commit()
    conn.close()

setup_database()

def cleanup_task():
    while True:
        time.sleep(CLEANUP_INTERVAL_SECONDS)
        now = time.time()
        
        with rate_limit_lock:
            ips_to_remove = [ip for ip, (last_check, _) in rate_limit_data.items() if now - last_check > 600]
            for ip in ips_to_remove:
                del rate_limit_data[ip]
            if ips_to_remove:
                logging.info(f"RAM Cleanup: Removed {len(ips_to_remove)} inactive IP entries from memory.")
            
        try:
            conn = sqlite3.connect(DB_FILE)
            cursor = conn.cursor()
            today = date.today()
            cursor.execute("DELETE FROM daily_requests WHERE request_date < ?", (today,))
            deleted_count = cursor.rowcount
            conn.commit()
            conn.close()
            if deleted_count > 0:
                logging.info(f"Database Cleanup: Removed {deleted_count} old daily limit records.")
        except Exception as e:
            logging.error(f"Error during database cleanup: {e}")

cleanup_thread = threading.Thread(target=cleanup_task, daemon=True)
cleanup_thread.start()
logging.info("Background cleanup thread started.")

def get_user_ip():
    if 'X-Forwarded-For' in request.headers:
        return request.headers['X-Forwarded-For'].split(',')[0].strip()
    return request.remote_addr

def check_rate_limit(ip: str):
    with rate_limit_lock:
        now = time.time()
        last_check_time, tokens = rate_limit_data.get(ip, (now, BURST_LIMIT))
        
        time_elapsed = now - last_check_time
        new_tokens = time_elapsed * REFILL_RATE_PER_SECOND
        tokens = min(BURST_LIMIT, tokens + new_tokens)
        
        if tokens >= 1:
            tokens -= 1
            rate_limit_data[ip] = (now, tokens)
            return {"allowed": True}
        else:
            rate_limit_data[ip] = (now, tokens)
            time_to_wait = (1.0 - tokens) / REFILL_RATE_PER_SECOND
            return {"allowed": False, "retry_after": int(time_to_wait) + 1}

def check_daily_limit(ip: str):
    today = date.today()
    conn = sqlite3.connect(DB_FILE, timeout=10)
    cursor = conn.cursor()
    try:
        cursor.execute("SELECT request_count FROM daily_requests WHERE ip_address = ? AND request_date = ?", (ip, today))
        result = cursor.fetchone()
        current_count = result[0] if result else 0
        is_allowed = current_count < RPD_LIMIT
        
        if is_allowed:
            cursor.execute('''
                INSERT INTO daily_requests (ip_address, request_date, request_count) VALUES (?, ?, 1)
                ON CONFLICT(ip_address, request_date) DO UPDATE SET request_count = request_count + 1
            ''', (ip, today))
            conn.commit()
            return {"allowed": True, "requests_made_today": current_count + 1}
        else:
            return {"allowed": False, "requests_made_today": current_count}
            
    except sqlite3.OperationalError as e:
        logging.warning(f"Database was locked for IP {ip}. Error: {e}")
        return {"allowed": False, "requests_made_today": -1}
    finally:
        conn.close()

class ImportVisitor(ast.NodeVisitor):
    def __init__(self):
        self.imports = set()
    def visit_Import(self, node):
        for alias in node.names: self.imports.add(alias.name.split('.')[0])
        self.generic_visit(node)
    def visit_ImportFrom(self, node):
        if node.module: self.imports.add(node.module.split('.')[0])
        self.generic_visit(node)

def detect_disallowed_imports(code: str) -> list:
    tree = ast.parse(code)
    visitor = ImportVisitor()
    visitor.visit(tree)
    disallowed = visitor.imports - ALLOWED_PUBLIC_IMPORTS
    return list(disallowed)

def set_subprocess_limits():
    resource.setrlimit(resource.RLIMIT_NPROC, (MAX_CHILD_PROCESSES, MAX_CHILD_PROCESSES))

def execute_code(code: str, execution_dir: str, is_admin: bool = False, stdin_data: str = ""):
    if len(code) > 2000:
        return {"success": False, "error_type": "ValidationError", "error": "Code is too long (max 2000 characters)."}
    
    if not is_admin:
        try:
            disallowed_imports = detect_disallowed_imports(code)
            if disallowed_imports:
                error_message = (f"Disallowed imports: {', '.join(disallowed_imports)}.")
                return {"success": False, "error_type": "ForbiddenImportError", "error": error_message, "details": {"disallowed": disallowed_imports}}
        except SyntaxError as e:
            return {"success": False, "error_type": "SyntaxError", "error": f"Invalid Python syntax: {e}"}
    
    script_filename = os.path.join(execution_dir, "script.py")
    preexec_fn = set_subprocess_limits if IS_UNIX else None
    
    try:
        with open(script_filename, "w", encoding="utf-8") as f:
            f.write(code)
            
        start_time = time.perf_counter()
        result = subprocess.run(
            ["python", "script.py"], 
            capture_output=True, text=True, timeout=10, input=stdin_data,
            cwd=execution_dir, preexec_fn=preexec_fn
        )
        duration = time.perf_counter() - start_time
    except subprocess.TimeoutExpired:
        return {"success": False, "error_type": "TimeoutError", "error": "Execution timed out (10 seconds limit)."}
    except Exception as e:
        if "OSError" in str(e) and "resource" in str(e).lower():
            return {"success": False, "error_type": "ResourceLimitError", "error": f"Process limit ({MAX_CHILD_PROCESSES}) exceeded. Fork bomb detected?"}
        return {"success": False, "error_type": "InternalError", "error": "An unexpected server error occurred."}
    
    temp_dir_pattern = re.escape(os.path.abspath(execution_dir))
    pattern = r'File "({}[\\/].*?\.py)"'.format(temp_dir_pattern)
    sanitized_stderr = re.sub(pattern, 'File "your_script.py"', result.stderr)
    
    return {
        "success": result.returncode == 0, "stdout": result.stdout, "stderr": sanitized_stderr,
        "exit_code": result.returncode, "execution_duration_sec": round(duration, 4)
    }

@app.route('/')
def home():
    return send_file("index.html")

@app.route('/execute', methods=['POST'])
def handle_execute():
    global active_subprocess_count
    
    response_data = {"status": "error", "timestamp_utc": datetime.now(timezone.utc).isoformat()}
    data = request.get_json()
    
    if not data or 'code' not in data:
        response_data["error_details"] = {"type": "InvalidRequest", "message": "'code' field is mandatory."}
        return jsonify(response_data), 400

    user_info = {}
    request_context = {
        "code_length": len(data.get('code', '')),
        "attachment_count": len(data.get('attachments', [])),
        "stdin_provided": bool(data.get('stdin_data'))
    }
    
    is_admin = bool(API_KEY and data.get('api_key') == API_KEY)

    if is_admin:
        user_info = {"role": "admin", "rate_limits_applied": False}
    else:
        ip = get_user_ip()
        user_info["ip_address"] = ip
        user_info["daily_quota_limit"] = RPD_LIMIT

        rate_limit = check_rate_limit(ip)
        if not rate_limit["allowed"]:
            response_data["error_details"] = {"type": "RateLimitExceeded", "message": f"Rate limit of {RPM_LIMIT}/minute exceeded. Please slow down."}
            response_data["user_info"] = user_info
            response = jsonify(response_data)
            response.headers['Retry-After'] = rate_limit.get('retry_after', 10)
            return response, 429
            
        daily_limit = check_daily_limit(ip)
        requests_made = daily_limit.get("requests_made_today", 0)
        user_info["requests_today"] = requests_made
        user_info["requests_remaining_today"] = max(0, RPD_LIMIT - requests_made)

        if not daily_limit["allowed"]:
            response_data["error_details"] = {"type": "RateLimitExceeded", "message": f"Daily quota of {RPD_LIMIT} exceeded."}
            response_data["user_info"] = user_info
            return jsonify(response_data), 429

    with subprocess_lock:
        current_active_subprocesses = active_subprocess_count
        if current_active_subprocesses >= MAX_CONCURRENT_SUBPROCESSES:
            server_status = {
                "load": "high",
                "active_processes_at_request": current_active_subprocesses,
                "max_concurrent_processes": MAX_CONCURRENT_SUBPROCESSES
            }
            response_data["error_details"] = {"type": "ServerBusy", "message": "Server is busy, please try again after some time."}
            response_data["user_info"] = user_info
            response_data["server_status"] = server_status
            return jsonify(response_data), 503 
        active_subprocess_count += 1
    
    server_status = {
        "load": "normal",
        "active_processes_at_request": current_active_subprocesses,
        "max_concurrent_processes": MAX_CONCURRENT_SUBPROCESSES
    }

    try:
        with tempfile.TemporaryDirectory(dir=TEMP_DIR) as execution_dir:
            try:
                attachments = data.get('attachments', [])
                if len(attachments) > MAX_ATTACHMENTS:
                    response_data["error_details"] = {"type": "ValidationError", "message": f"Maximum of {MAX_ATTACHMENTS} attachments allowed."}
                    return jsonify(response_data), 400

                processed_attachments = []
                for attachment in attachments:
                    filename = attachment.get("filename")
                    if not filename or ".." in filename or os.path.isabs(filename):
                        response_data["error_details"] = {"type": "ValidationError", "message": "Invalid or missing attachment filename."}
                        return jsonify(response_data), 400
                    
                    content_b64 = attachment.get("content_base_64")
                    if not content_b64:
                        response_data["error_details"] = {"type": "ValidationError", "message": f"Attachment '{filename}' is missing 'content_base_64'."}
                        return jsonify(response_data), 400
                    
                    safe_filename = os.path.basename(filename)
                    try:
                        content_bytes = base64.b64decode(content_b64)
                    except (ValueError, TypeError):
                        response_data["error_details"] = {"type": "ValidationError", "message": f"Invalid Base64 content for file '{safe_filename}'."}
                        return jsonify(response_data), 400
                    
                    if len(content_bytes) > MAX_FILE_SIZE_BYTES:
                        response_data["error_details"] = {"type": "ValidationError", "message": f"File '{safe_filename}' exceeds the size limit of {MAX_FILE_SIZE_MB}MB."}
                        return jsonify(response_data), 400
                    
                    with open(os.path.join(execution_dir, safe_filename), "wb") as f:
                        f.write(content_bytes)
                    processed_attachments.append({"filename": safe_filename, "size_bytes": len(content_bytes)})
                
                request_context["processed_attachments"] = processed_attachments
                
                result = execute_code(
                    data.get('code', ''),
                    execution_dir=execution_dir,
                    is_admin=is_admin,
                    stdin_data=data.get('stdin_data', '')
                )
                
                output_files = {}
                if result["success"]:
                    files_to_return = data.get('return_files', [])
                    abs_execution_dir = os.path.abspath(execution_dir)

                    for filename in files_to_return:
                        if not filename or ".." in filename or os.path.isabs(filename):
                            output_files[filename] = {"error": "Invalid filename. Path traversal is not allowed."}
                            continue
                        
                        filepath = os.path.join(execution_dir, filename)
                        abs_filepath = os.path.abspath(filepath)
                        
                        if not abs_filepath.startswith(abs_execution_dir):
                            output_files[filename] = {"error": "Security violation: File is outside the allowed directory."}
                            continue

                        if os.path.exists(filepath) and os.path.isfile(filepath):
                            file_size = os.path.getsize(filepath)
                            if file_size <= MAX_FILE_SIZE_BYTES:
                                with open(filepath, "rb") as f:
                                    content_bytes = f.read()
                                output_files[filename] = {
                                    "content_base64": base64.b64encode(content_bytes).decode('utf-8'),
                                    "size_bytes": file_size
                                }
                            else:
                                output_files[filename] = {"error": "File is too large to return.", "size_bytes": file_size}
                        else:
                            output_files[filename] = {"error": "File not found after execution."}

                response_data["user_info"] = user_info
                response_data["server_status"] = server_status
                response_data["request_context"] = request_context

                if result["success"]:
                    response_data["status"] = "success"
                    execution_details = {
                        "success": result.get("success"),
                        "stdout": result.get("stdout"),
                        "stderr": result.get("stderr"),
                        "exit_code": result.get("exit_code"),
                        "execution_duration_sec": result.get("execution_duration_sec"),
                        "output_files": output_files
                    }
                    response_data["execution_details"] = execution_details
                    return jsonify(response_data), 200
                else:
                    error_details = {"type": result.get("error_type", "RuntimeError"), "message": result.get("error")}
                    if "details" in result:
                        error_details.update(result["details"])
                    
                    response_data["error_details"] = error_details
                    response_data["execution_result"] = {k: v for k, v in result.items() if k not in ['success', 'error_type', 'error', 'details']}
                    return jsonify(response_data), 400

            except Exception as e:
                logging.error(f"An unexpected error occurred in handle_execute: {e}")
                response_data["error_details"] = {"type": "InternalServerError", "message": "An unexpected server error occurred."}
                return jsonify(response_data), 500
    finally:
        with subprocess_lock:
            active_subprocess_count -= 1

if __name__ == '__main__':
    if not IS_UNIX:
        logging.warning("Not running on a UNIX-like system. Fork bomb protection will be disabled.")
    
    app.run(host="0.0.0.0", port=5000, debug=False)
