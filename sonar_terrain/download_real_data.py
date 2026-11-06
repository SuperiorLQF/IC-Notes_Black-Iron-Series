"""Verify or restore the pinned, licensed real sidescan image subset."""
import argparse
import hashlib
import json
from pathlib import Path
from urllib.request import urlopen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-only', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent/'data/real/garmin_sample'
    manifest = json.loads((root/'manifest.json').read_text())
    total = 0
    for entry in manifest['files']:
        dest = root/entry['path']
        data = dest.read_bytes() if dest.exists() else b''
        if hashlib.sha256(data).hexdigest() != entry['sha256']:
            if args.verify_only:
                raise SystemExit(f'Missing or modified file: {dest}')
            with urlopen(entry['url'], timeout=45) as response:
                data = response.read(entry['bytes']+1)
            if len(data) != entry['bytes'] or hashlib.sha256(data).hexdigest() != entry['sha256']:
                raise SystemExit(f'Download verification failed: {entry["path"]}')
            temporary = dest.with_suffix(dest.suffix+'.download')
            temporary.write_bytes(data)
            temporary.replace(dest)
        total += len(data)
    print(f'Verified {len(manifest["files"])} original files, {total} bytes.')


if __name__ == '__main__':
    main()
