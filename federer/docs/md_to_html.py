#!/usr/bin/env python3
"""Convert Markdown files to standalone HTML with offline MathML mathematics.

Requires Python 3 and pandoc on PATH. Examples, from the repository root:

    python3 docs/md_to_html.py docs/contents.md
    python3 docs/md_to_html.py docs/symbols.md -o /tmp/symbols.html
    python3 docs/md_to_html.py docs --output-dir docs/html

Files default to adjacent .html outputs. Directory inputs are recursive;
--output-dir preserves paths relative to the inputs' common parent.
Links to pages converted together use their HTML outputs. Other local links
and images continue to point to the original files, rebased when necessary.
Supports $...$, $$...$$, \\(...\\) and \\[...\\] outside code. Pandoc warnings,
including unsupported TeX, fail conversion rather than silently losing math.
"""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from urllib.parse import quote, unquote, urlsplit, urlunsplit


READER = "markdown+tex_math_dollars+tex_math_single_backslash+gfm_auto_identifiers-smart"
STYLE = """<style>
body { max-width: 78rem; margin: auto; padding: 1.5rem;
       color: #20252b; background: #fff; line-height: 1.6;
       font-family: system-ui, sans-serif; overflow-wrap: anywhere; }
a { color: #175a9b; }
h1, h2, h3, h4, h5, h6 { line-height: 1.3; scroll-margin-top: 1rem; }
h2 { margin-top: 2rem; padding-bottom: .25rem; border-bottom: 1px solid #ddd; }
code { font-size: .9em; background: #f3f5f7; padding: .1em .25em;
       white-space: pre-wrap; }
pre { padding: 1rem; overflow: auto; background: #f3f5f7; }
pre code { padding: 0; white-space: pre; overflow-wrap: normal; }
table { display: block; max-width: 100%; overflow-x: auto;
        border-collapse: collapse; margin: 1rem 0; }
th, td { border: 1px solid #d5dae0; padding: .4rem .65rem; text-align: left; }
th { background: #f3f5f7; }
img { max-width: 100%; }
blockquote { border-left: .25rem solid #d5dae0; padding-left: 1rem; margin-left: 0; }
nav#TOC { max-height: 16rem; overflow: auto; padding: .75rem 1rem;
          border: 1px solid #d5dae0; border-radius: .3rem; }
math { font-size: 1.08em; }
math[display="block"] { display: block; overflow-x: auto; margin: 1rem 0; }
@media (max-width: 40rem) { body { padding: .75rem; } }
@media print { body { max-width: none; padding: 0; color: #000; }
               nav#TOC { display: none; } }
</style>
"""


def plain_text(node):
    """Extract a page title from the first heading's Pandoc inline nodes."""
    if isinstance(node, list):
        return "".join(plain_text(child) for child in node)
    if not isinstance(node, dict):
        return ""
    kind, content = node.get("t"), node.get("c")
    if kind == "Str":
        return content
    if kind in {"Space", "SoftBreak", "LineBreak"}:
        return " "
    if kind in {"Code", "Math"}:
        return content[-1]
    return plain_text(content)


def rewrite(node, source, output, outputs):
    """Rebase actual links/images and normalize standard text math symbols."""
    if isinstance(node, list):
        for child in node:
            rewrite(child, source, output, outputs)
    elif isinstance(node, dict):
        if node.get("t") in {"Link", "Image"}:
            target = node["c"][2]
            url = urlsplit(target[0])
            if not url.scheme and not url.netloc and url.path and not url.path.startswith("/"):
                original = (source.parent / unquote(url.path)).resolve()
                destination = outputs.get(original, original)
                relative = os.path.relpath(destination, output.parent)
                target[0] = urlunsplit(("", "", quote(Path(relative).as_posix(), safe="/"),
                                       url.query, url.fragment))
        elif node.get("t") == "Math":
            # Pandoc 2.17's MathML writer does not recognize these standard
            # LaTeX text symbols. Expand them only inside parsed mathematics.
            symbols = {"S": "§", "P": "¶"}
            node["c"][1] = re.sub(r"\\([SP])(?![A-Za-z])",
                                  lambda m: r"\text{" + symbols[m[1]] + "}",
                                  node["c"][1])
        for child in node.values():
            rewrite(child, source, output, outputs)


def pandoc(arguments, data=None):
    return subprocess.run(["pandoc", "--fail-if-warnings", *arguments], input=data,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout


def convert(source, output, outputs, header, toc):
    document = json.loads(pandoc(["--from=" + READER, "--to=json", str(source)]))
    title = next((plain_text(block["c"][2]) for block in document["blocks"]
                  if block["t"] == "Header"), source.stem)
    document["meta"].setdefault("pagetitle", {"t": "MetaString", "c": title})
    rewrite(document, source, output, outputs)
    options = ["--from=json", "--to=html5", "--standalone", "--mathml",
               "--wrap=none", "--include-in-header=" + str(header)]
    if toc:
        options += ["--toc", "--toc-depth=3"]
    rendered = pandoc(options, json.dumps(document, ensure_ascii=False).encode("utf-8"))
    # Render completely before replacing any existing HTML output.
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(rendered)
    print(f"{source} -> {output}")


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("inputs", nargs="+", type=Path, help="Markdown files or directories")
    destination = parser.add_mutually_exclusive_group()
    destination.add_argument("-o", "--output", type=Path, help="HTML filename for one input file")
    destination.add_argument("--output-dir", type=Path, help="root of the generated HTML tree")
    parser.add_argument("--no-toc", action="store_true", help="omit the page table of contents")
    args = parser.parse_args()
    if not shutil.which("pandoc"):
        parser.error("pandoc is required; install it and ensure it is on PATH")

    sources = []
    for path in args.inputs:
        if path.is_dir():
            sources.extend(sorted(p.resolve() for p in path.rglob("*")
                                  if p.is_file() and p.suffix.lower() == ".md"))
        elif path.is_file() and path.suffix.lower() == ".md":
            sources.append(path.resolve())
        else:
            parser.error(f"not a Markdown file or directory: {path}")
    sources = list(dict.fromkeys(sources))
    if not sources:
        parser.error("no Markdown files found")
    if args.output and len(sources) != 1:
        parser.error("--output requires exactly one Markdown file; use --output-dir for batches")

    base = Path(os.path.commonpath([p.parent for p in sources]))
    outputs = {}
    for source in sources:
        if args.output:
            output = args.output.resolve()
        elif args.output_dir:
            output = (args.output_dir / source.relative_to(base)).with_suffix(".html").resolve()
        else:
            output = source.with_suffix(".html").resolve()
        if output.suffix.lower() not in {".html", ".htm"}:
            parser.error(f"output filename must end in .html or .htm: {output}")
        if output in outputs.values():
            parser.error(f"multiple input files would produce {output}")
        outputs[source] = output

    try:
        with tempfile.TemporaryDirectory(prefix="federer-markdown-") as work:
            header = Path(work) / "style.html"
            header.write_text(STYLE, encoding="utf-8")
            for source, output in outputs.items():
                convert(source, output, outputs, header, not args.no_toc)
    except subprocess.CalledProcessError as error:
        print(error.stderr.decode("utf-8", errors="replace").strip(), file=sys.stderr)
        return error.returncode
    except (OSError, ValueError) as error:
        print(f"{parser.prog}: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
