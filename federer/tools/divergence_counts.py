"""Recompute the "Counts" section of docs/divergences.md from its tables.

Usage (from the repository root): python3 tools/divergence_counts.py
Counts the table rows per chapter and per kind and rewrites the section,
which must be the last section of the file.
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
KINDS = [
    ('proof route', 'Proof route'),
    ('statement correction (erratum)', 'Statement correction (erratum)'),
    ('statement correction (local)', 'Statement correction (local)'),
    ('hypothesis or convention', 'Hypothesis or convention'),
    ('interpretation', 'Interpretation'),
]


def main():
    path = ROOT / 'docs' / 'divergences.md'
    text = path.read_text()
    head, sep, tail = text.partition('\n## Counts\n')
    if not sep:
        raise SystemExit('no Counts section')
    if re.search(r'^\|', tail, re.M):
        raise SystemExit('table rows follow Counts; move them into their section before regenerating')
    rows = re.findall(r'^\| (\d+)\.[^|]* \| ([^|]+?) \|', head, re.M)
    per_kind = {k: 0 for k, _ in KINDS}
    per_chapter = {}
    for chapter, kind in rows:
        if kind not in per_kind:
            raise SystemExit('unknown kind: ' + kind)
        per_kind[kind] += 1
        per_chapter[chapter] = per_chapter.get(chapter, 0) + 1
    chapters = ' and '.join('%d in Chapter %s' % (n, c) for c, n in sorted(per_chapter.items()))
    lines = ['', '## Counts', '', 'The register has %d rows: %s.' % (len(rows), chapters), '']
    lines += ['- %s: %d.' % (label, per_kind[k]) for k, label in KINDS]
    path.write_text(head.rstrip('\n') + '\n' + '\n'.join(lines) + '\n')
    print('rows', len(rows), per_kind)


if __name__ == '__main__':
    main()
