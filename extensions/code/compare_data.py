#!/usr/bin/env python3
"""Compare packaged and regenerated JSON, ignoring only recorded environment versions."""
import json
import sys
from pathlib import Path

if len(sys.argv) != 3:
    raise SystemExit("usage: python compare_data.py expected_data_directory regenerated_data_directory")
left, right = map(Path, sys.argv[1:])
files = ["symbolic_minors.json", "small_minors_full.json", "generic_schur.json",
         "bijections.json", "hilbert_checks.json", "summary.json"]
for filename in files:
    a = json.loads((left / filename).read_text(encoding="utf-8"))
    b = json.loads((right / filename).read_text(encoding="utf-8"))
    if filename == "summary.json":
        a.pop("environment", None)
        b.pop("environment", None)
    if a != b:
        raise SystemExit("MISMATCH: " + filename)
    print("MATCH:", filename)
print("All mathematical data agree exactly.")
