import os
from datetime import datetime

def hash_msg(msg: tuple):
    msg = tuple(frozenset(e) if isinstance(e, set) else e for e in msg)
    return hash(msg)


def replace_node_ids(s, debug_names: dict):
    s = str(s)
    for pid_str, node_name in debug_names.items():
        s = s.replace(pid_str, node_name)
    return s


def log_to_file(filename: str, s: str, debug_names: dict):
    line = replace_node_ids(s, debug_names)
    os.makedirs('logs', exist_ok=True)
    with open(os.path.join('logs', filename), 'a') as f:
        f.write(f'[{datetime.now().isoformat()}] {line}\n')
