#!/usr/bin/env python3
"""Verify the distributed files against MANIFEST.json (standard library only)."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / 'MANIFEST.json').read_text(encoding='utf-8'))
    errors = []
    for entry in manifest['files']:
        path = (root / entry['path']).resolve()
        if root not in path.parents:
            raise SystemExit('Unsafe path in manifest: ' + entry['path'])
        if not path.is_file():
            errors.append('MISSING: ' + entry['path'])
            continue
        raw = path.read_bytes()
        if len(raw) != entry['bytes'] or hashlib.sha256(raw).hexdigest() != entry['sha256']:
            errors.append('MISMATCH: ' + entry['path'])
        else:
            print('OK:', entry['path'])
    if errors:
        raise SystemExit('\n'.join(errors))
    print(f"All {len(manifest['files'])} distributed files agree with the manifest.")


if __name__ == '__main__':
    main()
