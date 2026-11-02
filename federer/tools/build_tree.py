"""Prepare a separate Rocq build tree, or relocate existing generated files.

Sources remain in the checkout and are symlinked individually into the build
tree. Compilation runs there, so Rocq's ordinary relative paths still work.
The owner marker records which checkout the links point to. Two checkouts may
use the same tree in turn, never at the same time: a checkout takes the tree
over with ``prepare --adopt`` (``ADOPT=1 make prepare-build``), which repoints
the links to itself, keeps the artifacts of sources whose bytes are unchanged
(carrying the earlier timestamp onto the identical new source so that make
sees them as current), deletes the artifacts of changed or removed sources
so that make recompiles them, and rewrites the marker.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parent.parent
MARKER = '.federer-build.json'
SUFFIXES = {'.vo', '.vos', '.vok', '.glob', '.aux'}


def build_directory(value=None):
    config = ROOT / '.build-dir'
    value = value or os.environ.get('BUILD_DIR')
    if not value:
        value = config.read_text().strip() if config.exists() else '_build'
    path = (ROOT / value).resolve()
    if path == ROOT or path in ROOT.parents or any(c.isspace() for c in str(path)):
        raise ValueError('Build directory must be separate from the checkout and contain no whitespace')
    if path.is_relative_to(ROOT) and path.parts[len(ROOT.parts)] != '_build':
        raise ValueError('Within the checkout, use _build/ for generated output')
    return path


def check_owner(build, adopt=False):
    marker = build / MARKER
    if marker.exists():
        state = json.loads(marker.read_text())
        if state['source'] != str(ROOT) and not adopt:
            raise ValueError(f'{build} belongs to another checkout: {state["source"]}; '
                             'run `ADOPT=1 make prepare-build` to take it over')
        return state
    if build.exists() and any(build.iterdir()):
        raise ValueError(f'Refusing to adopt a nonempty unmarked directory: {build}')
    return {'source': str(ROOT), 'links': []}


def artifact_paths(source):
    for suffix in ('.vo', '.vos', '.vok', '.glob'):
        yield source.with_suffix(suffix)
    yield source.parent / ('.' + source.stem + '.aux')


def remove_artifacts(source):
    for artifact in artifact_paths(source):
        if artifact.exists():
            artifact.unlink()


def same_bytes(old, new):
    try:
        return old.is_file() and digest(old) == digest(new)
    except OSError:
        return False


def prepare(build, adopt=False):
    state = check_owner(build, adopt)
    previous = Path(state['source'])
    takeover = previous != ROOT
    sources = sorted(str(p.relative_to(ROOT)) for folder in ('theories', 'tests')
                     for p in (ROOT / folder).rglob('*.v'))
    links = ['_CoqProject'] + sources
    build.mkdir(parents=True, exist_ok=True)
    if takeover:
        for folder in ('', 'theories', 'tests'):
            if (build / folder).exists() and not os.access(build / folder, os.W_OK):
                raise ValueError(f'{build / folder} is not writable by this user; '
                                 'the owner must grant write access before adoption')
    # Claim the directory before creating links, so an interrupted preparation
    # can be retried without adopting someone else's files. During a takeover
    # the previous owner stays recorded until every link has been repointed.
    (build / MARKER).write_text(json.dumps(state, indent=2) + '\n')
    kept = recompiled = added = 0
    for rel in links:
        target = build / rel
        new = ROOT / rel
        if target.is_symlink() and os.readlink(target) == str(new):
            continue
        if takeover and target.is_symlink() and os.readlink(target) == str(previous / rel):
            old = previous / rel
            if same_bytes(old, new):
                # Unchanged bytes: the existing artifacts were compiled from this
                # very content, so the identical new source inherits the earlier
                # timestamp and make leaves them alone.
                old_stat = old.stat()
                if new.stat().st_mtime_ns > old_stat.st_mtime_ns:
                    os.utime(new, ns=(old_stat.st_atime_ns, old_stat.st_mtime_ns))
                kept += 1
            else:
                remove_artifacts(target)
                recompiled += 1
            target.unlink()
            target.symlink_to(new)
            continue
        if target.exists() or target.is_symlink():
            raise ValueError(f'Refusing to replace existing file: {target}')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.symlink_to(new)
        added += 1
    # Removed or renamed modules must not remain importable from the build tree.
    removed = 0
    for rel in set(state['links']) - set(links):
        old = build / rel
        if old.is_symlink() and os.readlink(old) in {str(ROOT / rel), str(previous / rel)}:
            old.unlink()
            remove_artifacts(old)
            removed += 1
    (build / MARKER).write_text(json.dumps({'source': str(ROOT), 'links': links}, indent=2) + '\n')
    if takeover:
        print(f'Adopted {build} from {previous}: {kept} unchanged sources keep their '
              f'artifacts, {recompiled} changed sources will be recompiled, '
              f'{added} new and {removed} removed modules.')


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def migrate(build):
    """Copy, verify, then remove each old artifact; preserve timestamps exactly.

    This relocates caches, not validation status. Older outputs remain older
    than edited sources and will be rebuilt normally by make.
    """
    prepare(build)
    files = [p for folder in ('theories', 'tests') for p in (ROOT / folder).rglob('*')
             if p.is_file() and (p.suffix in SUFFIXES or p.name in
                                {'.lia.cache', '.nia.cache', '.nra.cache'})]
    files += [ROOT / name for name in ('Makefile.coq', 'Makefile.coq.conf',
              '.Makefile.coq.d', '.lia.cache', '.nia.cache', '.nra.cache')
              if (ROOT / name).is_file()]
    # Generated Makefiles contain checkout paths: preserve them as history,
    # then generate fresh ones in the external tree.
    count = size = 0
    for source in files:
        rel = source.relative_to(ROOT)
        if source.name in {'Makefile.coq', 'Makefile.coq.conf', '.Makefile.coq.d'}:
            rel = Path('previous-build') / rel
        elif source.suffix in SUFFIXES:
            stem = source.stem.lstrip('.') if source.suffix == '.aux' else source.stem
            if not (source.parent / (stem + '.v')).exists():
                rel = Path('previous-build') / rel
        target = build / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() or target.is_symlink():
            raise ValueError(f'Migration destination already exists: {target}')
        shutil.copy2(source, target)
        if digest(source) != digest(target):
            raise ValueError(f'Copy verification failed: {source}')
        size += source.stat().st_size
        source.unlink()
        count += 1
    for folder in ('html', 'theories/.coq-native', 'tests/.coq-native', '.coq-native'):
        source, target = ROOT / folder, build / folder
        if source.exists():
            if target.exists():
                raise ValueError(f'Migration destination already exists: {target}')
            shutil.copytree(source, target, copy_function=shutil.copy2)
            for p in source.rglob('*'):
                if p.is_file() and digest(p) != digest(target / p.relative_to(source)):
                    raise ValueError(f'Copy verification failed: {p}')
            shutil.rmtree(source)
    print(f'Relocated {count} files ({size:,} bytes) to {build}; SHA-256 copies verified.')


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--build-dir')
    parser.add_argument('--adopt', action='store_true',
                        help='take over a tree whose marker names another checkout')
    parser.add_argument('action', choices=('prepare', 'migrate', 'path'))
    args = parser.parse_args()
    build = build_directory(args.build_dir)
    if args.action == 'path':
        print(build)
    elif args.action == 'prepare':
        prepare(build, adopt=args.adopt)
    else:
        migrate(build)


if __name__ == '__main__':
    main()
