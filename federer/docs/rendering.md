# Rendering the documentation

[Documentation](toc.md) · [Item map](contents.md) · [Index](index.md) · [Symbols](symbols.md) · [Divergences](divergences.md) · [Bibliography](bibliography.md)

The project offers two HTML views: rendered Markdown guides and generated
Rocq source documentation. Both retain the source links in their inputs.

## Generated documentation

`make doc` runs coqdoc over the library and writes HTML to the build
directory's `html/` (not tracked). This workspace uses
`/opt/rocq/federer-build/html/index.html`; other checkouts default to
`_build/html/index.html` (see the top-level README). It lists the interface modules and, for
each numbered item, the modules and declarations that serve it, with links
to the coqdoc table of contents and the index of identifiers. The pages
show statements and documentation comments; proofs are omitted.

## HTML copies of Markdown

[md_to_html.py](md_to_html.py) converts Markdown documentation to standalone
HTML using Python 3 and Pandoc. Mathematics uses native MathML and needs no
network connection or JavaScript library. It accepts `$...$`, `$$...$$`,
`\(...\)` and `\[...\]`, while preserving literal mathematics inside code.
Tables, fenced code and a page table of contents are included.

Run from the repository root:

```sh
# Write docs/contents.html next to the Markdown source.
python3 docs/md_to_html.py docs/contents.md

# Choose a filename for a single page.
python3 docs/md_to_html.py docs/symbols.md -o /tmp/symbols.html

# Convert a directory recursively, preserving the directory structure.
python3 docs/md_to_html.py docs --output-dir docs/html
```

Multiple Markdown filenames may also be supplied. With `--output-dir`,
paths are relative to their common parent directory. Links between pages
converted in the same invocation point to the generated HTML pages;
other local links and images are rebased to their original files.
Rocq source line fragments are retained. Add `--no-toc` to omit navigation.

Pandoc must understand the TeX expressions used by the document. Unsupported
math and other Pandoc warnings stop conversion before replacing that page's
output. The converter expands the standard `\S` and `\P` text symbols inside
math for compatibility with Pandoc 2.17's MathML writer. Generated HTML is
ignored by Git; it is separate from the Rocq source documentation produced
by `make doc`.
