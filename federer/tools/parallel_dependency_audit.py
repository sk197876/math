"""Run independently checked, targeted audit shards in private scratch trees.

This module is optional. The original serial audit remains the default.
No result is usable until every shard and the caller's complete old-result
preservation check pass. No private object is copied into the library.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import time


def partition_queries(queries, workers):
    """Keep repeated names as distinct, ordered selected-query positions."""
    if workers < 1:
        raise ValueError('workers must be positive')
    count = min(workers, len(queries))
    return [list(enumerate(queries))[number::count]
            for number in range(count)]


def validate_output(log, returncode, expected, split_results, allowed):
    """Apply the serial audit's checks independently to one compiler log."""
    errors = []
    if returncode:
        errors.append('compile failed')
    if re.search('Warning:|Error:', log):
        errors.append('warning or error')
    results = split_results(log)
    if len(results) != expected:
        errors.append('result count mismatch %d != %d' %
                      (len(results), expected))
    found = set(re.findall(r"^([A-Za-z][A-Za-z0-9_'.]*)\s*:",
                           log, re.M)) - {'Axioms'}
    if found - allowed:
        errors.append('unexpected assumptions: ' +
                      ', '.join(sorted(found - allowed)))
    return results, found, errors


def admitted_workers(requested, queries, guard):
    """Respect the existing RAM estimate, CPU detection and current profile."""
    if requested < 1:
        raise ValueError('workers must be positive')
    if not queries:
        return 0
    profile = guard.profile_at(guard.read_policy())
    # The last measured targeted audit used 2811.273 MiB. Round it up.
    ceiling = guard.worker_limit(profile, 3072, guard.available_mib(),
                                 guard.cpu_count())
    if ceiling < 1:
        raise ValueError('resource policy admits no targeted audit worker')
    return min(requested, len(queries), ceiling)


def current_worker_ceiling(guard):
    """The outer resource guard retains whole-scope CPU and RAM enforcement."""
    return guard.profile_at(guard.read_policy())['max_workers']


def _save_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def _remove_objects(source):
    for suffix in ('.vo', '.vos', '.vok', '.glob'):
        source.with_suffix(suffix).unlink(missing_ok=True)
    (source.parent / ('.' + source.stem + '.aux')).unlink(missing_ok=True)


def _terminate_owned(active):
    """Stop only process groups launched by this invocation."""
    processes = [row['process'] for row in active
                 if row['process'].poll() is None]
    for process in processes:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    deadline = time.monotonic() + 5
    for process in processes:
        try:
            process.wait(timeout=max(0.01, deadline-time.monotonic()))
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()


def run_parallel_audit(queries, imports, workers, build, command_prefix,
                       split_results, allowed, ceiling_now=None,
                       poll_seconds=0.25):
    """Compile exact selected positions, then merge in their original order.

    Each shard uses the SAME sorted union of selected imports. This preserves
    notation and printing context even for fully qualified query names.
    Full imports and unqualified names remain the serial caller's concern.
    """
    os.umask(0o002)
    build = Path(build)
    shards = partition_queries(queries, workers) if queries else []
    if not shards:
        return {'log': '', 'results': [], 'assumptions': [],
                'errors': [], 'run_directory': None, 'workers': 0}
    run = Path(tempfile.mkdtemp(prefix='dependency-audit-parallel-',
                                dir=build))
    os.chmod(run, 0o2775)
    common_imports = sorted(set(imports))
    preamble = '\n'.join(common_imports) + '\n\n'
    rows = []
    for number, shard in enumerate(shards):
        source = run / ('Shard%04d.v' % number)
        source.write_text(preamble +
                          '\n'.join(query for _, query in shard) + '\n')
        rows.append({'number': number,
                     'positions': [position for position, _ in shard],
                     'queries': [query for _, query in shard],
                     'source': source.name,
                     'source_sha256': hashlib.sha256(
                         source.read_bytes()).hexdigest(),
                     'command': list(command_prefix) +
                         ['-Q', str(run), 'FedererAuditScratch', str(source)],
                     'status': 'prepared'})
    record = {'status': 'prepared', 'scope': 'targeted_shards_only',
              'old_result_preservation': 'caller_must_check',
              'complete_audit_accepted': False, 'workers': len(shards),
              'selected_queries': len(queries),
              'common_imports': common_imports, 'shards': rows,
              'ordinary_rocq_required': True,
              'private_objects_adopted': False}
    _save_json(run / 'status.json', record)
    errors, found, active = [], set(), []
    ordered = [None] * len(queries)
    interrupted = False
    try:
        for row in rows:
            ceiling = ceiling_now() if ceiling_now else None
            if ceiling is not None and len(shards) > ceiling:
                raise RuntimeError(
                    'current resource profile disallows %d audit workers' %
                    len(shards))
            stem = Path(row['source']).stem
            with (run / (stem + '.stdout')).open('w') as output, \
                    (run / (stem + '.stderr')).open('w') as error:
                process = subprocess.Popen(row['command'], cwd=build,
                                           stdout=output, stderr=error,
                                           start_new_session=True)
            row['process'] = process
            row['pid'] = process.pid
            row['status'] = 'running'
            active.append(row)
        record['status'] = 'running'
        _save_json(run / 'status.json',
                   {**record, 'shards': [
                       {k: v for k, v in row.items() if k != 'process'}
                       for row in rows]})
        while active:
            ceiling = ceiling_now() if ceiling_now else None
            if ceiling is not None and len(shards) > ceiling:
                raise RuntimeError(
                    'resource profile changed: retry the audit with at most '
                    '%d worker(s)' % ceiling)
            for row in list(active):
                returncode = row['process'].poll()
                if returncode is None:
                    continue
                stem = Path(row['source']).stem
                log = ((run / (stem + '.stdout')).read_text() +
                       (run / (stem + '.stderr')).read_text())
                (run / (stem + '.log')).write_text(log)
                row['log_sha256'] = hashlib.sha256(
                    log.encode()).hexdigest()
                fresh, assumptions, shard_errors = validate_output(
                    log, returncode, len(row['positions']),
                    split_results, allowed)
                found.update(assumptions)
                errors.extend('shard %d: %s' % (row['number'], error)
                              for error in shard_errors)
                if not shard_errors:
                    for position, result in zip(row['positions'], fresh):
                        if ordered[position] is not None:
                            raise RuntimeError(
                                'duplicate selected query position')
                        ordered[position] = result
                row['returncode'] = returncode
                row['errors'] = shard_errors
                row['assumptions'] = sorted(assumptions)
                row['status'] = 'failed' if shard_errors else 'passed'
                active.remove(row)
            if active:
                time.sleep(poll_seconds)
    except (Exception, KeyboardInterrupt) as error:
        interrupted = True
        errors.append('%s: %s' % (type(error).__name__, error))
        _terminate_owned(active)
        for row in active:
            row['status'] = 'interrupted'
            row['returncode'] = row['process'].returncode
    finally:
        for row in rows:
            _remove_objects(run / row['source'])
            row.pop('process', None)
        record['status'] = 'failed' if errors else 'passed'
        record['interrupted'] = interrupted
        record['errors'] = errors
        record['assumptions'] = sorted(found)
        _save_json(run / 'status.json', record)
    if not errors and any(result is None for result in ordered):
        errors.append('not every selected position has a checked result')
        record['errors'] = errors
        record['status'] = 'failed'
        _save_json(run / 'status.json', record)
    log = '\n'.join(result for result in ordered if result is not None)
    if log:
        log += '\n'
    (run / 'merged.log').write_text(log)
    return {'log': log, 'results': ordered, 'assumptions': sorted(found),
            'errors': errors, 'run_directory': str(run),
            'workers': len(shards)}
