#!/usr/bin/env python3
"""Trace helpers for the model-change experiment.

    model_change_trace.py dump    <recordings.db> <out.txt>
    model_change_trace.py compare <original.db> <modified.db> <out.json>

`dump` writes one block per recorded interaction, in recording order, with the
full (multi-line) SQL. Reads through the sqlite3 module rather than the sqlite3
CLI so SQL containing newlines stays one entry.

`compare` diffs two recordings keyed the way replay looks them up,
(unique_id, record_type), and reports keys only in one side and keys whose SQL
changed.
"""

import json
import sqlite3
import sys


def load(db):
    con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
    rows = con.execute(
        "SELECT rowid, unique_id, record_type, sql, error IS NOT NULL, "
        "COALESCE(LENGTH(data_base64), 0) FROM recordings ORDER BY rowid"
    ).fetchall()
    con.close()
    return rows


def dump(db, out):
    rows = load(db)
    with open(out, "w") as f:
        for i, (_, uid, rtype, sql, err, dlen) in enumerate(rows, 1):
            f.write(f"[{i:02d}] {rtype:<16} {uid}\n")
            body = (sql or "(no SQL)").strip("\n")
            for line in body.splitlines():
                f.write(f"     | {line.rstrip()}\n")
            f.write(f"     -> {'ERROR' if err else 'OK'}, result {dlen} bytes (base64)\n\n")
        f.write(f"Total: {len(rows)} interactions\n")


def compare(orig_db, mod_db, out):
    def keyed(rows):
        return {(uid, rtype): (sql or "") for _, uid, rtype, sql, _, _ in rows}

    o, m = keyed(load(orig_db)), keyed(load(mod_db))
    only_orig = sorted(k for k in o if k not in m)
    only_mod = sorted(k for k in m if k not in o)
    changed = sorted(k for k in o if k in m and o[k] != m[k])
    # Same SQL once whitespace is collapsed: a purely cosmetic difference.
    ws_only = [k for k in changed if " ".join(o[k].split()) == " ".join(m[k].split())]

    fmt = lambda ks: [f"{u} [{t}]" for u, t in ks]
    result = {
        "original_interactions": len(o),
        "modified_interactions": len(m),
        "only_in_original": fmt(only_orig),
        "only_in_modified": fmt(only_mod),
        "sql_changed": fmt(changed),
        "sql_changed_whitespace_only": fmt(ws_only),
        "trace_changed": bool(only_orig or only_mod or changed),
    }
    with open(out, "w") as f:
        json.dump(result, f, indent=2)
    print(f"    trace: {len(o)} -> {len(m)} interactions; "
          f"{len(changed)} changed SQL, {len(only_mod)} new, {len(only_orig)} gone")


if __name__ == "__main__":
    cmd, *args = sys.argv[1:]
    {"dump": dump, "compare": compare}[cmd](*args)
