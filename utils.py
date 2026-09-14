def hash_msg(msg: tuple):
    msg = tuple(frozenset(e) if isinstance(e, set) else e for e in msg)
    return hash(msg)
