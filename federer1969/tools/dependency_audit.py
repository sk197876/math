"""Audit only the entries of tests/Assumptions.v whose dependencies changed.

Usage (from the repository root, after a successful build):
    python3 tools/dependency_audit.py BASE [--dry-run] [--targeted-imports]
        [--workers N]
BASE is the last commit whose docs/assumptions.log is a complete audit of
its tests/Assumptions.v. An entry `Print Assumptions N.` is audited again
when N belongs to a module that changed since BASE or depends, directly or
transitively, on such a module (dependencies from .Makefile.coq.d), when its
module cannot be determined, or when the entry was appended after BASE. The
selected entries are compiled together with every import line of
tests/Assumptions.v, in the original order, so that names resolve as in the
full audit. The fresh results replace the old ones, and docs/assumptions.log
is rewritten as a complete log. Old entries must keep their results, and
only the three permitted boolp assumptions may occur. Prints a JSON summary
and exits with status 1 on any error. With --dry-run only the selection is
reported.

With --targeted-imports every selected query must be fully qualified and
resolve to exactly its named module. Only those modules are imported; Rocq
loads their complete transitive dependencies normally. Query selection,
ordinary compiler checks, permitted assumptions and preservation of every
old result are unchanged. Unqualified or ambiguous selected queries fail
closed in this mode; use the original full-import mode for such entries.
This avoids loading unrelated historical theories into focused audits.

Optional --workers N with N greater than one requires targeted imports.
Every independent ordinary compiler imports the same sorted selected module
union. Unique scratch trees retain each log; results merge by original query
position, including repeated names. The existing resource policy caps the
requested count and interrupts a parallel run when weekday limits resume.
Use the outer resource guard with a whole-job estimate of at least 3072 MiB
per admitted worker. The serial path and its default import order are unchanged.

Compiled metadata and scratch files live in BUILD_DIR (environment), the
directory named in .build-dir, or _build/ by default. Tracked audit records
remain in the source checkout.
"""
import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from build_tree import build_directory, check_owner

ROOT = Path(__file__).resolve().parent.parent
BUILD = build_directory()
ALLOWED = {'boolp.propositional_extensionality', 'boolp.functional_extensionality_dep',
           'boolp.constructive_indefinite_description'}
WARNINGS = '-notation-overridden,-ambiguous-paths,-redundant-canonical-projection,-notation-incompatible-prefix'
SWITCH = 'RP.2026.02.0~9.1~2026.01'
GLOB_KINDS = {'def', 'prf', 'thm', 'lem', 'ax', 'ind', 'constr', 'rec', 'proj', 'inst',
              'class', 'coe', 'abbrev', 'syndef', 'scheme', 'canonstruc'}


def git(*args, quiet=False):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True,
                                   stderr=subprocess.DEVNULL if quiet else None)


def show_at(base, rel):
    """The file rel of this subproject at revision base.

    Revisions before the move into federer1969/ have the subproject at the
    repository root; the plain path then names the same file.
    """
    try:
        return git('show', base + ':./' + rel, quiet=True)
    except subprocess.CalledProcessError:
        return git('show', base + ':' + rel)


def changed_paths(base):
    """Paths, relative to this subproject, changed since base.

    A pure rename that keeps the path relative to the subproject, as in the
    move into federer1969/, is not a change.
    """
    prefix = git('rev-parse', '--show-prefix').strip()
    paths = []
    for line in git('diff', '--name-status', '-M', base, '--').splitlines():
        status, *names = line.split('\t')
        new = names[-1]
        if new.startswith(prefix):
            rel = new[len(prefix):]
        elif prefix and new.split('/')[0] in ('theories', 'tests'):
            rel = new  # a deleted file of the layout before the move
        else:
            continue
        if status == 'R100' and names[0] in (rel, prefix + rel):
            continue
        paths.append(rel)
    return paths + git('ls-files', '--others', '--exclude-standard').split()


def split_results(log):
    """The Print Assumptions results of a log, in order."""
    results, cur = [], None
    for line in log.splitlines():
        if line == 'Closed under the global context' or line == 'Axioms:':
            cur = [line]
            results.append(cur)
        elif line.startswith('===') and line.endswith('==='):
            cur = None
        elif cur is not None:
            cur.append(line)
    return ['\n'.join(r) for r in results]


def module_graph():
    deps = {}
    for line in (BUILD / '.Makefile.coq.d').read_text().splitlines():
        m = re.match(r'^(\S+)\.vo \S.*?:\s(.*)$', line)
        if m:
            deps[m.group(1)] = {d[:-3] for d in m.group(2).split() if d.endswith('.vo')}
    return deps


def glob_names():
    names = {}
    for glob in list((BUILD / 'theories').glob('*.glob')) + list((BUILD / 'tests').glob('*.glob')):
        module = str(glob.relative_to(BUILD).with_suffix(''))
        for line in glob.read_text(errors='replace').splitlines():
            parts = line.split()
            if len(parts) == 4 and parts[0] in GLOB_KINDS:
                full = parts[3] if parts[2] == '<>' else parts[2] + '.' + parts[3]
                names.setdefault(full, set()).add(module)
    return names


def entry_modules(name, files, names):
    for prefix in ('Federer.', 'FedererTests.'):
        if name.startswith(prefix):
            name = name[len(prefix):]
    first = name.split('.', 1)[0]
    if '.' in name and first in files:
        return {files[first]}
    return names.get(name)


def qualified_query_import(name, modules):
    """Require the exact module of a fully qualified selected constant."""
    match = re.fullmatch(r'(Federer|FedererTests)\.([A-Za-z][A-Za-z0-9_]*)\.(.+)', name)
    if match is None:
        raise ValueError('targeted imports require a fully qualified query: ' + name)
    namespace, module, _ = match.groups()
    expected = ('theories/' if namespace == 'Federer' else 'tests/') + module
    if modules != {expected}:
        raise ValueError('targeted query module is unresolved or ambiguous: ' + name)
    return 'From %s Require Import %s.' % (namespace, module)


def parse_options(argv):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('base')
    parser.add_argument('--dry-run', action='store_true')
    parser.add_argument('--targeted-imports', action='store_true')
    parser.add_argument('--workers', type=int, default=1)
    args = parser.parse_args(argv)
    if args.workers < 1:
        parser.error('--workers must be positive')
    if args.workers > 1 and not args.targeted_imports:
        parser.error('--workers greater than one requires --targeted-imports')
    return args


def main():
    args = parse_options(sys.argv[1:])
    os.umask(0o002)
    check_owner(BUILD)
    base = args.base
    dry = args.dry_run
    targeted = args.targeted_imports
    old_file = show_at(base, 'tests/Assumptions.v')
    old_log = show_at(base, 'docs/assumptions.log')
    new_file = (ROOT / 'tests' / 'Assumptions.v').read_text()
    errors = []
    if not new_file.startswith(old_file):
        raise SystemExit('tests/Assumptions.v was not only appended to since ' + base)
    old_results = split_results(old_log)
    n_old = len(re.findall(r'^Print Assumptions ', old_file, re.M))
    if len(old_results) != n_old:
        raise SystemExit('the log of %s has %d results for %d entries' % (base, len(old_results), n_old))

    changed = {str(Path(p).with_suffix('')) for p in changed_paths(base)
               if p.endswith('.v') and p.split('/')[0] in ('theories', 'tests')
               and p != 'tests/Assumptions.v'}
    deps = module_graph()
    affected = set(changed)
    grew = True
    while grew:
        grew = False
        for mod, ds in deps.items():
            if mod not in affected and ds & affected:
                affected.add(mod)
                grew = True
    files = {Path(m).name: m for m in deps}
    names = glob_names()

    lines = new_file.splitlines()
    keep, selected, unresolved, k = [], [], 0, 0
    pending_label = None
    target_imports, target_queries = set(), []
    for line in lines:
        if line.startswith('Print Assumptions '):
            name = line[len('Print Assumptions '):].rstrip().rstrip('.')
            mods = entry_modules(name, files, names)
            if mods is None:
                unresolved += 1
            if k >= n_old or mods is None or mods & affected:
                if pending_label is not None:
                    keep.append(pending_label)
                    pending_label = None
                keep.append(line)
                selected.append(k)
                if targeted:
                    try:
                        target_imports.add(qualified_query_import(name, mods))
                    except ValueError as error:
                        raise SystemExit(str(error)) from error
                    target_queries.append(line)
            k += 1
        elif line.startswith('Goal True. idtac "==='):
            pending_label = line
        else:
            keep.append(line)
    if dry:
        print(json.dumps({'base': base, 'changed_modules': sorted(changed), 'affected_modules': len(affected),
                          'entries': k, 'old_entries': n_old, 'audited': len(selected),
                          'audited_old': sum(1 for i in selected if i < n_old),
                          'unresolved_names': unresolved}, indent=2))
        return
    if targeted:
        keep = sorted(target_imports) + [''] + target_queries
    parallel = None
    if args.workers > 1:
        import resource_guard as guard
        from parallel_dependency_audit import (admitted_workers,
            current_worker_ceiling, run_parallel_audit)
        try:
            workers = admitted_workers(args.workers, target_queries, guard)
        except ValueError as error:
            raise SystemExit(str(error)) from error
        prefix = ['opam', 'exec', '--switch=' + SWITCH, '--', 'rocq',
                  'compile', '-w', WARNINGS, '-Q', 'theories', 'Federer',
                  '-Q', 'tests', 'FedererTests']
        parallel = run_parallel_audit(target_queries, target_imports,
            workers, BUILD, prefix, split_results, ALLOWED,
            ceiling_now=lambda: current_worker_ceiling(guard))
        errors.extend(parallel['errors'])
        log = parallel['log']
        r = subprocess.CompletedProcess(prefix, 0, log, '')
    else:
        scratch = BUILD / 'tests' / 'DependencyAuditScratch.v'
        scratch.write_text('\n'.join(keep) + '\n')
        try:
            r = subprocess.run(['opam', 'exec', '--switch=' + SWITCH, '--', 'rocq', 'compile',
                                '-w', WARNINGS, '-Q', 'theories', 'Federer', '-Q', 'tests', 'FedererTests',
                                str(scratch)], cwd=BUILD, capture_output=True, text=True)
        finally:
            for suffix in ('.v', '.vo', '.vos', '.vok', '.glob'):
                p = scratch.with_suffix(suffix)
                if p.exists():
                    p.unlink()
            aux = scratch.parent / ('.' + scratch.stem + '.aux')
            if aux.exists():
                aux.unlink()

        log = r.stdout + r.stderr
        (BUILD / 'tests' / 'DependencyAuditScratch.log').write_text(log)
    if r.returncode:
        errors.append('compile failed')
    if re.search('Warning:|Error:', log):
        errors.append('warning or error')
    fresh = split_results(log)
    if len(fresh) != len(selected):
        errors.append('result count mismatch %d != %d' % (len(fresh), len(selected)))
    found = set(re.findall(r"^([A-Za-z][A-Za-z0-9_'.]*)\s*:", log, re.M)) - {'Axioms'}
    if parallel is not None:
        found.update(parallel['assumptions'])
    if found - ALLOWED:
        errors.append('unexpected assumptions: ' + ', '.join(sorted(found - ALLOWED)))
    results = old_results + [None] * (k - n_old)
    changed_results = 0
    if not errors:
        for i, res in zip(selected, fresh):
            if i < n_old and res != old_results[i]:
                changed_results += 1
            results[i] = res
        if changed_results:
            errors.append('%d existing entries changed their assumptions' % changed_results)
    if not errors:
        out, k = [], 0
        for line in lines:
            if line.startswith('Goal True. idtac "==='):
                out.append(line.split('idtac "', 1)[1].split('".', 1)[0])
            elif line.startswith('Print Assumptions '):
                out.append(results[k])
                k += 1
        (ROOT / 'docs' / 'assumptions.log').write_text('\n'.join(out) + '\n')
    print(json.dumps({
        'base': base, 'changed_modules': len(changed), 'affected_modules': len(affected),
        'entries': k, 'old_entries': n_old, 'audited': len(selected),
        'audited_old': sum(1 for i in selected if i < n_old), 'audited_new': sum(1 for i in selected if i >= n_old),
        'unresolved_names': unresolved,
        'closed': sum(1 for x in fresh if x.startswith('Closed')),
        'assumptions': sorted(found), 'errors': errors,
        'targeted_imports': targeted, 'imported_query_modules': len(target_imports) if targeted else None,
        **({'requested_workers': args.workers, 'workers': parallel['workers'],
            'parallel_run_directory': parallel['run_directory'],
            'parallel_merged_log': (str(Path(parallel['run_directory'])/'merged.log')
                if parallel['run_directory'] is not None else None)}
           if parallel is not None else {})}, indent=2))
    sys.exit(1 if errors else 0)


if __name__ == '__main__':
    main()
