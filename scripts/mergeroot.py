"""Resolve a conflicted surface root module.

    python scripts/mergeroot.py NumlibSurface/SaadSparse.lean

Every surface agent adds its chapter files to its book's root module, so each merge conflicts
there and always in the same harmless way: two disjoint sets of `import` lines. Rewrite the file
as the sorted union of every import mentioned anywhere in it, followed by the module doc comment
with the conflict markers stripped.
"""

import io
import re
import sys

MARKERS = ('<<<<<<<', '=======', '>>>>>>>')


def main(path: str) -> None:
    text = io.open(path, encoding='utf-8').read()
    imports = sorted(set(re.findall(r'^import (\S+)$', text, re.M)))
    if not imports:
        raise SystemExit(f'{path}: no imports found')
    try:
        doc = text[text.index('/-!'):]
    except ValueError:
        raise SystemExit(f'{path}: no module doc comment found')
    for marker in MARKERS:
        doc = doc.split(marker)[0]
    resolved = ''.join(f'import {m}\n' for m in imports) + '\n' + doc.rstrip() + '\n'
    if any(marker in resolved for marker in MARKERS):
        raise SystemExit(f'{path}: conflict markers survive; resolve by hand')
    io.open(path, 'w', encoding='utf-8', newline='').write(resolved)
    print(f'{path}: {len(imports)} imports')


if __name__ == '__main__':
    for arg in sys.argv[1:]:
        main(arg)
