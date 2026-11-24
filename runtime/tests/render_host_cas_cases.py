#!/usr/bin/env python3
"""Render the trusted host CAS fixture as a small TSV stream for the C++ smoke."""

import json
import pathlib
import sys


def plain(value):
    assert isinstance(value, str)
    assert not any(char in value for char in "\t\r\n")
    return value


fixture = json.loads(pathlib.Path(sys.argv[1]).read_text())
assert fixture["version"] == 1
pending = fixture["pending"]
pending_fields = (
    "requestId",
    "operation",
    "capability",
    "schema",
    "attemptId",
    "transactionId",
    "journalDigest",
    "baseRevision",
)
print("\t".join(["VERSION", str(fixture["version"])]))
print("\t".join(["PENDING", *(plain(str(pending[key])) for key in pending_fields)]))

cases = fixture["cases"]
assert len(cases) == 15
counts = {"pending": 0, "committed": 0, "conflict": 0, "rejected": 0}
for case in cases:
    name = plain(case["name"])
    after = plain(case["after"])
    expected = plain(case["expected"])
    counts[expected] += 1
    columns = ["CASE", name, after, expected]
    for key, value in case["overrides"].items():
        columns.extend((plain(key), json.dumps(value, separators=(",", ":"))))
    print("\t".join(columns))

assert counts == {"pending": 11, "committed": 1, "conflict": 1, "rejected": 2}
