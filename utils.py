import os
import glob
import shutil
from datetime import datetime

def hash_msg(msg: tuple):
    msg = tuple(frozenset(e) if isinstance(e, set) else e for e in msg)
    return hash(msg)


def replace_node_ids(s, debug_names: dict):
    s = str(s)
    for pid_str, node_name in debug_names.items():
        s = s.replace(pid_str, node_name)
    return s


def log_to_file(filename: str, s: str, debug_names: dict, logs_dir: str = 'logs'):
    line = replace_node_ids(s, debug_names)
    os.makedirs(logs_dir, exist_ok=True)
    with open(os.path.join(logs_dir, filename), 'a') as f:
        f.write(f'[{datetime.now().isoformat()}] {line}\n')


def archive_logs(logs_dir: str = 'logs'):
    archive_dir = os.path.join(logs_dir, 'archives')
    if not os.path.isdir(logs_dir):
        return
    os.makedirs(archive_dir, exist_ok=True)
    for path in glob.glob(os.path.join(logs_dir, '*.txt')):
        if os.path.isfile(path):
            shutil.move(path, os.path.join(archive_dir, os.path.basename(path)))
