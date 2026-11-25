"""Prepare the external build tree of a Rocq subproject other than federer1969.

The sources stay in the checkout. ``prepare`` links every ``.v`` file named in
the subproject's ``_CoqProject`` into the build directory, copies
``_CoqProject`` there and regenerates ``Makefile.coq`` when needed.
Compilation then runs in the build directory, so the ordinary relative load
paths of ``_CoqProject`` work and no artifact is written beside the sources.

A link whose source has disappeared is removed together with its artifacts.
Artifacts of unchanged sources are kept; make decides what to recompile from
the timestamps of the linked sources.

Usage (from a subproject folder; the Makefile does this):

    python3 -B ../tools/subproject_build.py --build-dir DIR prepare
"""
import argparse
import os
from pathlib import Path
import subprocess

SUFFIXES = ('.vo', '.vos', '.vok', '.glob')


def sources(project):
    return [line.strip() for line in project.read_text().splitlines()
            if line.strip().endswith('.v') and not line.startswith('-')]


def artifacts(link):
    for suffix in SUFFIXES:
        yield link.with_suffix(suffix)
    yield link.parent / ('.' + link.stem + '.aux')


def prepare(root, build, coqmakefile):
    if build == root or root in build.parents or build in root.parents:
        raise SystemExit(f'build directory {build} must be outside the checkout {root}')
    project = root / '_CoqProject'
    wanted = sources(project)
    build.mkdir(parents=True, exist_ok=True)
    for folder in ('theories', 'tests'):
        (build / folder).mkdir(exist_ok=True)
    for folder in ('theories', 'tests'):
        base = build / folder
        if not base.exists():
            continue
        for link in base.rglob('*.v'):
            if link.is_symlink() and not link.exists():
                for artifact in artifacts(link):
                    if artifact.exists():
                        artifact.unlink()
                link.unlink()
    for rel in wanted:
        source = root / rel
        if not source.exists():
            raise SystemExit(f'missing source named in _CoqProject: {rel}')
        link = build / rel
        link.parent.mkdir(parents=True, exist_ok=True)
        if link.is_symlink() and os.readlink(link) == str(source):
            continue
        if link.exists() or link.is_symlink():
            if not link.is_symlink():
                raise SystemExit(f'refusing to replace a regular file: {link}')
            link.unlink()
        link.symlink_to(source)
    target = build / '_CoqProject'
    text = project.read_text()
    if not target.exists() or target.read_text() != text:
        target.write_text(text)
    makefile = build / 'Makefile.coq'
    if not makefile.exists() or target.stat().st_mtime > makefile.stat().st_mtime:
        subprocess.run([*coqmakefile.split(), '-f', '_CoqProject', '-o', 'Makefile.coq'],
                       cwd=build, check=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--build-dir', required=True)
    parser.add_argument('--coqmakefile', default='rocq makefile')
    parser.add_argument('command', choices=['prepare', 'path'])
    args = parser.parse_args()
    root = Path.cwd().resolve()
    build = Path(args.build_dir).resolve()
    if args.command == 'path':
        print(build)
    else:
        prepare(root, build, args.coqmakefile)


if __name__ == '__main__':
    main()
