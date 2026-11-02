"""Write html/index.html, the landing page of the coqdoc documentation.

Usage (from the repository root, after `make doc` has run coqdoc):
    python3 tools/coqdoc_index.py

The page lists the public interface modules and then, for every numbered
item of Federer's book, the modules whose declarations serve it (as in
docs/contents.md), linking to the coqdoc pages and to the principal
declarations. The coqdoc table of contents and identifier index are
linked at the top.
"""
import html
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import contents  # noqa: E402
from build_tree import build_directory

ROOT = contents.ROOT
OUT = build_directory() / 'html'
INTERFACES = [
    ('theories/GrassmannSpaces.v', 'Chapter 1: Grassmann algebra'),
    ('theories/TensorFamily.v', 'Chapter 1.1: tensor products of families'),
    ('theories/Graded.v', 'Chapter 1.2: graded algebras and the tensor algebra'),
    ('theories/Exterior.v', 'Chapter 1.3: the exterior algebra'),
    ('theories/MeasureTheory.v', 'Chapter 2: general measure theory'),
    ('theories/Rectifiability.v', 'Chapter 3: rectifiability (development in progress)'),
]


_IDS = {}


def anchor(f, name):
    """The coqdoc anchor of a declaration: its name, or, inside a module,
    the first qualified anchor ending with the name."""
    p = OUT / page(f)
    if p not in _IDS:
        _IDS[p] = re.findall(r'id="([^"]+)"', p.read_text()) if p.exists() else []
    ids = _IDS[p]
    if name in ids:
        return name
    for i in ids:
        if i.endswith('.' + name):
            return i
    return None


def page(f):
    p = Path(f)
    prefix = 'Federer.' if p.parts[0] == 'theories' else 'FedererTests.'
    return prefix + p.stem + '.html'


def main():
    if not (OUT / 'toc.html').exists():
        raise SystemExit('html/toc.html missing: run coqdoc first (make doc)')
    items = contents.collect()
    titles = contents.titles()
    out = ['<!DOCTYPE html>', '<html lang="en">', '<head>', '<meta charset="utf-8">',
           '<meta name="viewport" content="width=device-width, initial-scale=1">',
           '<title>Federer-Rocq: Geometric Measure Theory in Rocq</title>',
           '<link href="coqdoc.css" rel="stylesheet" type="text/css">',
           '<style>body{max-width:60em;margin:0 auto;padding:0 1em}'
           'li{margin:.15em 0} .decls{font-size:90%} h4{margin-bottom:.2em}</style>',
           '</head>', '<body>', '<div id="main">',
           '<h1>Federer-Rocq: Geometric Measure Theory in Rocq</h1>',
           '<p>Generated documentation of the Rocq formalisation of Chapters 1 and 2 of '
           'Herbert Federer, <i>Geometric Measure Theory</i> (1969), with the developing Chapter 3. Statements and '
           'documentation comments are shown; proofs are omitted. Each declaration is '
           'preceded by a comment naming its source in the book.</p>',
           '<p><a href="toc.html">Table of contents (all modules)</a> &middot; '
           '<a href="identifiers.html">Index of identifiers</a></p>',
           '<h2>Interface modules</h2>', '<ul>']
    for f, what in INTERFACES:
        if (ROOT / f).exists():
            out.append('<li><a href="%s">%s</a>: %s</li>' % (page(f), html.escape(Path(f).stem),
                                                              html.escape(what)))
    out.append('</ul>')
    out.append('<h2>Modules by Federer item</h2>')
    out.append('<p>A declaration is attributed to the first item number in its source '
               'comment, so an item may be spread over several modules.</p>')
    section = None
    for it in sorted(items, key=contents.key):
        c, s_, _ = it.split('.')
        if (c, s_) != section:
            if section:
                out.append('</ul>')
            section = (c, s_)
            name = contents.SECTIONS.get(c + '.' + s_, '')
            out.append('<h3>%s.%s %s</h3>' % (c, s_, html.escape(name)))
            out.append('<ul>')
        title = titles.get(it, ('', ''))[0]
        out.append('<li><b>%s</b>%s<ul>' % (it, (' &mdash; ' + html.escape(title)) if title else ''))
        for f in sorted(items[it], key=lambda f: Path(f).name):
            seen, decls = set(), []
            for d in sorted(items[it][f]):
                if d[2] not in seen:
                    seen.add(d[2])
                    decls.append(d)
            parts = []
            for _, _, n, _ in decls[:contents.SHOWN]:
                a = anchor(f, n)
                ref = page(f) + ('#' + html.escape(a) if a else '')
                parts.append('<a href="%s"><code>%s</code></a>' % (ref, html.escape(n)))
            links = ', '.join(parts)
            if len(decls) > contents.SHOWN:
                links += ', and %d more' % (len(decls) - contents.SHOWN)
            out.append('<li><a href="%s">%s</a> <span class="decls">%s</span></li>'
                       % (page(f), html.escape(Path(f).stem), links))
        out.append('</ul></li>')
    if section:
        out.append('</ul>')
    out += ['</div>', '</body>', '</html>']
    (OUT / 'index.html').write_text('\n'.join(out) + '\n')
    print('wrote', OUT / 'index.html')


if __name__ == '__main__':
    main()
