#!/usr/bin/env python3
"""Check documentation links and headings without changing any files.

Run from any directory. Python 3 and Pandoc are required. With no arguments,
check the top-level README and every Markdown file under docs/. Pass
--external to request external HTTP links as well. Network failures are
reported separately from broken local links; they never count as successes.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess
import sys
from urllib.error import HTTPError, URLError
from urllib.parse import unquote, urlsplit, urlunsplit
from urllib.request import Request, urlopen


ROOT = Path(__file__).resolve().parent.parent
READER = "markdown+tex_math_dollars+tex_math_single_backslash+gfm_auto_identifiers-smart"


class Anchors(HTMLParser):
    """Collect explicit HTML anchors retained in Markdown."""

    def __init__(self):
        super().__init__()
        self.ids = []

    def handle_starttag(self, tag, attrs):
        for key, value in attrs:
            if key == "id" or (tag == "a" and key == "name"):
                self.ids.append(value)


def plain(node):
    if isinstance(node, list):
        return "".join(plain(child) for child in node)
    if not isinstance(node, dict):
        return ""
    kind, content = node.get("t"), node.get("c")
    if kind == "Str":
        return content
    if kind in {"Space", "SoftBreak", "LineBreak"}:
        return " "
    if kind in {"Code", "Math"}:
        return content[-1]
    return plain(content)


def parse(path):
    result = subprocess.run(
        ["pandoc", "--fail-if-warnings", "--from=" + READER, "--to=json", str(path)],
        text=True, capture_output=True, check=True,
    )
    document = json.loads(result.stdout)
    headings, links = [], []
    anchors = Anchors()

    def walk(node):
        if isinstance(node, list):
            for child in node:
                walk(child)
        elif isinstance(node, dict):
            kind, content = node.get("t"), node.get("c")
            if kind == "Header":
                headings.append((content[0], content[1][0], plain(content[2])))
                anchors.ids.append(content[1][0])
            elif kind in {"Link", "Image"}:
                declaration = (kind == "Link" and len(content[1]) == 1
                               and content[1][0].get("t") == "Code")
                links.append((content[2][0], plain(content[1]), declaration))
            elif kind in {"RawInline", "RawBlock"} and content[0] == "html":
                anchors.feed(content[1])
            for child in node.values():
                walk(child)

    walk(document)
    return {"headings": headings, "anchors": anchors.ids, "links": links}


def external(url):
    # GET also checks sites that reject HEAD. Read only a small response prefix.
    request = Request(url, headers={"User-Agent": "Federer-documentation-link-check/1.0"})
    try:
        with urlopen(request, timeout=25) as response:
            response.read(1024)
            return {"url": url, "status": response.status, "destination": response.url}
    except HTTPError as error:
        return {"url": url, "status": error.code, "error": str(error)}
    except (URLError, TimeoutError, OSError) as error:
        return {"url": url, "error": str(error)}


def check(paths, request_external=False):
    pages, source_lines, failures, urls = {}, {}, [], set()
    links_checked = 0

    def page(path):
        if path not in pages:
            pages[path] = parse(path)
        return pages[path]

    def fail(path, target, reason):
        failures.append({"page": str(path.relative_to(ROOT)) if path.is_relative_to(ROOT)
                         else str(path), "target": target, "reason": reason})

    for path in paths:
        data = page(path)
        if re.fullmatch(r"[123]\.\d+\.md", path.name) and re.fullmatch(r"chapter[123]", path.parent.name):
            level = 0
            titles = 0
            for depth, anchor, label in data["headings"]:
                if depth > level + 1:
                    fail(path, "#" + anchor, "skipped heading level")
                level = depth
                titles += depth == 1
            if titles != 1:
                fail(path, "", "section guide must have one title")
            sections = [label for depth, _, label in data["headings"] if depth == 2]
            expected = ["Overview", "Contents", "Numbered items"]
            if "Section notes" in sections:
                expected.append("Section notes")
            expected.append("Navigation")
            if sections != expected:
                fail(path, "", "inconsistent section-guide structure")
        seen = set()
        for anchor in data["anchors"]:
            if anchor in seen:
                fail(path, "#" + anchor, "duplicate anchor")
            seen.add(anchor)
        for target, label, declaration in data["links"]:
            links_checked += 1
            url = urlsplit(target)
            if url.scheme in {"http", "https"}:
                urls.add(urlunsplit((url.scheme, url.netloc, url.path, url.query, "")))
                continue
            if url.scheme or url.netloc:
                if url.scheme != "mailto":
                    fail(path, target, "unsupported URL scheme")
                continue
            destination = (path.parent / unquote(url.path)).resolve() if url.path else path
            if not destination.exists():
                fail(path, target, "missing file")
                continue
            fragment = unquote(url.fragment)
            if not fragment:
                continue
            if destination.suffix == ".md":
                if fragment not in page(destination)["anchors"]:
                    fail(path, target, "missing heading or explicit anchor")
                continue
            line = re.fullmatch(r"L([1-9][0-9]*)(?:-L([1-9][0-9]*))?", fragment)
            if line:
                if destination not in source_lines:
                    source_lines[destination] = destination.read_text().splitlines()
                text = source_lines[destination]
                start, end = int(line[1]), int(line[2] or line[1])
                if not (1 <= start <= end <= len(text)):
                    fail(path, target, "source line outside file")
                elif declaration and destination.suffix == ".v" and re.fullmatch(r"[A-Za-z_][\w']*", label):
                    if not re.search(r"(?<![\w'])" + re.escape(label) + r"(?![\w'])",
                                     "\n".join(text[start - 1:end])):
                        fail(path, target, "declaration label absent from linked source line")
            elif destination.suffix == ".pdf" and re.fullmatch(r"page=[1-9][0-9]*", fragment):
                pass
            else:
                fail(path, target, "unsupported local fragment")

    remote = []
    if request_external:
        with ThreadPoolExecutor(max_workers=4) as pool:
            remote = list(pool.map(external, sorted(urls)))
    return {"markdown_files": len(paths), "links_checked": links_checked,
            "external_requested": request_external,
            "external_urls": sorted(urls), "local_failures": failures,
            "external_results": remote}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path)
    parser.add_argument("--external", action="store_true", help="also request external HTTP links")
    parser.add_argument("--report", type=Path, help="write a JSON report")
    args = parser.parse_args()
    paths = [p.resolve() for p in args.paths] if args.paths else [
        ROOT / "README.md", *sorted((ROOT / "docs").rglob("*.md")),
    ]
    try:
        report = check(paths, args.external)
    except (OSError, subprocess.CalledProcessError) as error:
        parser.exit(2, str(error) + "\n")
    if args.report:
        args.report.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"Checked {report['markdown_files']} Markdown files and {report['links_checked']} links; "
          f"{len(report['external_urls'])} distinct external URLs.")
    for failure in report["local_failures"]:
        print(f"{failure['page']}: {failure['target']}: {failure['reason']}")
    unresolved = [r for r in report["external_results"] if r.get("error")]
    for result in unresolved:
        print(f"External: {result['url']}: {result['error']}")
    print(f"Local failures: {len(report['local_failures'])}; "
          f"external requests unresolved: {len(unresolved)}.")
    return bool(report["local_failures"] or unresolved)


if __name__ == "__main__":
    sys.exit(main())
