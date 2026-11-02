"""Turn every mention of a Rocq source file in the Markdown documentation
into a relative link, and every code span naming a declaration that is
defined in exactly one file into a link to the line of its definition.

Usage (from the repository root): python3 tools/linkify_docs.py [FILE.md ...]
Without arguments, all tracked Markdown files are processed. A mention is
`Name.v`, `theories/Name.v`, `tests/Name.v` or the same without backticks;
it is linked when the file exists under theories/ or tests/. Existing
links, fenced code blocks and wildcard names such as `Word*.v` are left
unchanged, except that a link to a declaration line which no longer
contains the declaration is refreshed. Running the script twice changes
nothing.
"""
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LINK = re.compile(r'\[[^\]]*\]\([^)]*\)')
CODE = re.compile(r'`([^`]+)`')
BARE = re.compile(r'(?<![\w/.*-])((?:theories/|tests/)?[A-Za-z][A-Za-z0-9_]*\.v)\b(?![\w*])')


DECL = re.compile(r'^\s*(?:Local\s+|Global\s+|#\[[^\]]*\]\s*)?'
                  r'(?:Definition|Fixpoint|Lemma|Theorem|Corollary|Proposition|Record|Inductive|'
                  r'Example|Parameter|Fact|Remark|Structure|Variant)\s+([A-Za-z_][A-Za-z0-9_\']*)', re.M)


def declarations():
    """Map each declaration name defined in exactly one file to (file, line)."""
    found = {}
    for d in ('theories', 'tests'):
        for p in sorted((ROOT / d).glob('*.v')):
            s = p.read_text()
            for m in DECL.finditer(s):
                line = s.count('\n', 0, m.start(1)) + 1
                found.setdefault(m.group(1), {}).setdefault(p, line)
    result = {}
    for name, where in found.items():
        public = {p: l for p, l in where.items() if not p.stem.endswith('Construction')}
        where = public or where
        if len(where) == 1:
            result[name] = next(iter(where.items()))
    return result


DECLS = declarations()
OWN = re.compile(r'^\[`([A-Za-z_][A-Za-z0-9_\']*)`\]\((?:\.\./)*(?:theories|tests)/[A-Za-z0-9_]+\.v#L\d+\)$')


def current(md, link, name):
    """Whether a declaration link still points to a line containing the name."""
    path, _, line = link[link.index('](') + 2:-1].partition('#L')
    f = (md.parent / path).resolve()
    if not f.is_file():
        return False
    lines = f.read_text().split('\n')
    k = int(line)
    return 1 <= k <= len(lines) and re.search(r'\b' + re.escape(name) + r'\b', lines[k - 1]) is not None


def resolve(name):
    if name.startswith(('theories/', 'tests/')):
        p = ROOT / name
        return p if p.is_file() else None
    for d in ('theories', 'tests'):
        p = ROOT / d / name
        if p.is_file():
            return p
    return None


def target(md, path):
    return os.path.relpath(path, md.parent).replace(os.sep, '/')


def link_plain(md, text):
    def bare(m):
        p = resolve(m.group(1))
        if not p:
            return m.group(0)
        return '[%s](%s)' % (m.group(1), target(md, p))
    return BARE.sub(bare, text)


def link_segment(md, text):
    out, pos = [], 0
    for m in CODE.finditer(text):
        out.append(link_plain(md, text[pos:m.start()]))
        inner = m.group(1).strip()
        p = resolve(inner) if re.fullmatch(r'(?:theories/|tests/)?[A-Za-z][A-Za-z0-9_]*\.v', inner) else None
        if p:
            out.append('[`%s`](%s)' % (inner, target(md, p)))
        elif inner in DECLS:
            f, l = DECLS[inner]
            out.append('[`%s`](%s#L%d)' % (inner, target(md, f), l))
        else:
            out.append(m.group(0))
        pos = m.end()
    out.append(link_plain(md, text[pos:]))
    return ''.join(out)


def process(md):
    lines = md.read_text().split('\n')
    fenced = False
    for i, line in enumerate(lines):
        if line.lstrip().startswith('```'):
            fenced = not fenced
            continue
        if fenced:
            continue
        out, pos = [], 0
        for m in LINK.finditer(line):
            out.append(link_segment(md, line[pos:m.start()]))
            own = OWN.match(m.group(0))
            if own and own.group(1) in DECLS and not current(md, m.group(0), own.group(1)):
                f, l = DECLS[own.group(1)]
                out.append('[`%s`](%s#L%d)' % (own.group(1), target(md, f), l))
            else:
                out.append(m.group(0))
            pos = m.end()
        out.append(link_segment(md, line[pos:]))
        lines[i] = ''.join(out)
    new = '\n'.join(lines)
    if new != md.read_text():
        md.write_text(new)
        return True
    return False


def main():
    if len(sys.argv) > 1:
        files = [Path(a).resolve() for a in sys.argv[1:]]
    else:
        names = subprocess.check_output(['git', 'ls-files', '--cached', '--others', '--exclude-standard', '*.md'], cwd=ROOT, text=True).split()
        files = [ROOT / n for n in names]
    changed = [f for f in files if f.exists() and process(f)]
    for f in changed:
        print('linked', f.relative_to(ROOT))


if __name__ == '__main__':
    main()
