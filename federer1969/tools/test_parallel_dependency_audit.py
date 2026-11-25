"""Exercise audit scheduling and preservation without launching any prover."""
from contextlib import ExitStack, redirect_stderr, redirect_stdout
import importlib.util
import io
import hashlib
import json
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

STAGED = Path(__file__).resolve().parent
sys.path.insert(0, str(STAGED))

import parallel_dependency_audit as parallel
import resource_guard as guard


def load_audit(name, source):
    spec = importlib.util.spec_from_file_location(name, source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


candidate = load_audit('candidate_audit', STAGED / 'dependency_audit.py')
ORACLE_PATH = STAGED / 'fixtures' / 'dependency_audit_serial_oracle.py'
oracle = load_audit('serial_oracle', ORACLE_PATH)
CLOSED = 'Closed under the global context'
FUNCTIONAL = ('Axioms:\n'
              'boolp.functional_extensionality_dep : Type')
PROPOSITIONAL = ('Axioms:\n'
                 'boolp.propositional_extensionality : Type')


class FakeCompiler:
    """Write ordinary-looking logs while retaining every launched command."""
    def __init__(self, output, returncode=0, stderr='', delay=None):
        self.output = output
        self.returncode = returncode
        self.stderr = stderr
        self.delay = delay or {}
        self.commands = []
        self.sources = []
        self.processes = []

    def run(self, command, **kwargs):
        source = Path(command[-1]).read_text()
        self.commands.append(command)
        self.sources.append(source)
        return subprocess.CompletedProcess(
            command, self.returncode, self.output(source), self.stderr)

    def popen(self, command, **kwargs):
        source = Path(command[-1]).read_text()
        self.commands.append(command)
        self.sources.append(source)
        kwargs['stdout'].write(self.output(source))
        kwargs['stdout'].flush()
        kwargs['stderr'].write(self.stderr)
        kwargs['stderr'].flush()
        number = len(self.commands) - 1
        fake = SimpleNamespace(pid=45000+number, returncode=None)
        remaining = [self.delay.get(number, 0)]

        def poll():
            if remaining[0] > 0:
                remaining[0] -= 1
                return None
            fake.returncode = self.returncode
            return fake.returncode

        def wait(timeout=None):
            fake.returncode = -signal.SIGTERM
            return fake.returncode

        fake.poll, fake.wait = poll, wait
        self.processes.append(fake)
        return fake


class ShardTests(unittest.TestCase):
    def run_shards(self, compiler, queries=None, workers=2, imports=None,
                   ceiling=None, build=None):
        queries = queries or [
            'Print Assumptions Federer.A.first.',
            'Print Assumptions Federer.B.second.',
            'Print Assumptions Federer.A.first.',
            'Print Assumptions Federer.C.third.',
        ]
        imports = imports or [
            'From Federer Require Import C.',
            'From Federer Require Import A.',
            'From Federer Require Import B.',
        ]
        prefix = ['opam', 'exec', '--switch='+candidate.SWITCH, '--',
                  'rocq', 'compile', '-w', candidate.WARNINGS,
                  '-Q', 'theories', 'Federer',
                  '-Q', 'tests', 'FedererTests']
        with patch.object(parallel.subprocess, 'Popen',
                          side_effect=compiler.popen), \
             patch.object(parallel.time, 'sleep'):
            return parallel.run_parallel_audit(
                queries, imports, workers, build, prefix,
                candidate.split_results, candidate.ALLOWED,
                ceiling_now=ceiling)

    def test_partition_retains_duplicate_positions(self):
        self.assertEqual(parallel.partition_queries(['A', 'B', 'A', 'C'], 2),
                         [[(0, 'A'), (2, 'A')], [(1, 'B'), (3, 'C')]])
        self.assertEqual(parallel.partition_queries([], 4), [])
        self.assertEqual(parallel.partition_queries(['A'], 4),
                         [[(0, 'A')]])
        with self.assertRaises(ValueError):
            parallel.partition_queries(['A'], 0)

    def test_reverse_completion_merges_by_position_and_common_context(self):
        def output(source):
            blocks = {0: [CLOSED, CLOSED],
                      1: [FUNCTIONAL, PROPOSITIONAL]}
            shard = 0 if source.count('Federer.A.first') == 2 else 1
            return '\n'.join(blocks[shard]) + '\n'
        compiler = FakeCompiler(output, delay={0: 3, 1: 0})
        with tempfile.TemporaryDirectory() as folder:
            result = self.run_shards(compiler, build=folder)
            self.assertEqual(result['errors'], [])
            self.assertEqual(result['results'],
                             [CLOSED, FUNCTIONAL, CLOSED, PROPOSITIONAL])
            record = json.loads((Path(result['run_directory']) /
                                 'status.json').read_text())
            self.assertEqual([r['positions'] for r in record['shards']],
                             [[0, 2], [1, 3]])
            self.assertEqual(record['status'], 'passed')
            self.assertFalse(record['private_objects_adopted'])
            imports = '\n'.join(sorted(record['common_imports']))+'\n\n'
            for source, command in zip(compiler.sources, compiler.commands):
                self.assertTrue(source.startswith(imports))
                self.assertEqual(command[:6],
                    ['opam', 'exec', '--switch='+candidate.SWITCH,
                     '--', 'rocq', 'compile'])
                self.assertIn(candidate.WARNINGS, command)
                self.assertEqual(command[-4], '-Q')
                self.assertEqual(command[-2], 'FedererAuditScratch')

    def test_all_serial_failure_checks_apply_per_shard(self):
        cases = [
            ('compiler failure', CLOSED+'\n', 1, 'compile failed'),
            ('warning', 'Warning: suspicious\n'+CLOSED+'\n', 0,
             'warning or error'),
            ('error', 'Error: suspicious\n'+CLOSED+'\n', 0,
             'warning or error'),
            ('missing result', '', 0, 'result count mismatch'),
            ('extra result', CLOSED+'\n'+CLOSED+'\n', 0,
             'result count mismatch'),
            ('unknown assumption', 'Axioms:\nunsafe.fake : Prop\n', 0,
             'unexpected assumptions: unsafe.fake'),
        ]
        for name, text, returncode, expected in cases:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as f:
                compiler = FakeCompiler(lambda _: text, returncode)
                result = self.run_shards(compiler, queries=[
                    'Print Assumptions Federer.A.first.'],
                    workers=1, build=f)
                self.assertTrue(any(expected in e for e in result['errors']))
                record = json.loads((Path(result['run_directory']) /
                                     'status.json').read_text())
                self.assertEqual(record['status'], 'failed')

    def test_exactly_three_permitted_assumptions_remain_accepted(self):
        self.assertEqual(candidate.ALLOWED, {
            'boolp.propositional_extensionality',
            'boolp.functional_extensionality_dep',
            'boolp.constructive_indefinite_description'})
        for name in sorted(candidate.ALLOWED):
            text = 'Axioms:\n'+name+' : Type\n'
            results, found, errors = parallel.validate_output(
                text, 0, 1, candidate.split_results, candidate.ALLOWED)
            self.assertEqual(results, [text.rstrip('\n')])
            self.assertEqual(found, {name})
            self.assertEqual(errors, [])

    def test_only_owned_generated_objects_are_removed(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            source = root/'Shard0000.v'
            source.write_text('unit-test source fixture\n')
            generated = [source.with_suffix(suffix) for suffix in
                         ('.vo', '.vos', '.vok', '.glob')]
            generated.append(root/'.Shard0000.aux')
            foreign = root/'Other.vo'
            for path in generated+[foreign]:
                path.write_text('unit-test artifact fixture\n')
            parallel._remove_objects(source)
            self.assertTrue(source.exists())
            self.assertTrue(foreign.exists())
            self.assertTrue(all(not path.exists() for path in generated))

    def test_invocations_never_share_scratch_or_serial_logs(self):
        compiler = FakeCompiler(lambda _: CLOSED+'\n')
        with tempfile.TemporaryDirectory() as folder:
            build = Path(folder)
            (build/'tests').mkdir()
            sentinel = build/'tests'/'DependencyAuditScratch.log'
            sentinel.write_text('active serial audit\n')
            query = ['Print Assumptions Federer.A.first.']
            first = self.run_shards(compiler, query, 1, build=build)
            second = self.run_shards(compiler, query, 1, build=build)
            self.assertNotEqual(first['run_directory'],
                                second['run_directory'])
            self.assertEqual(sentinel.read_text(), 'active serial audit\n')
            for result in [first, second]:
                scratch = Path(result['run_directory'])
                self.assertTrue((scratch/'Shard0000.v').exists())
                self.assertTrue((scratch/'Shard0000.log').exists())
                self.assertEqual(list(scratch.glob('*.vo')), [])

    def test_policy_transition_stops_only_owned_process_groups(self):
        compiler = FakeCompiler(lambda _: CLOSED+'\n', delay={0: 10, 1: 10})
        ceiling = Mock(side_effect=[None, None, 1])
        with tempfile.TemporaryDirectory() as folder, \
             patch.object(parallel.os, 'killpg') as kill:
            result = self.run_shards(compiler, queries=[
                'Print Assumptions Federer.A.first.',
                'Print Assumptions Federer.B.second.'],
                ceiling=ceiling, build=folder)
        self.assertTrue(any('resource profile changed' in e
                            for e in result['errors']))
        self.assertEqual({call.args[0] for call in kill.call_args_list},
                         {process.pid for process in compiler.processes})
        self.assertTrue(all(call.args[1] == signal.SIGTERM
                            for call in kill.call_args_list))

    def test_launch_failure_cannot_publish_partial_results(self):
        with tempfile.TemporaryDirectory() as folder, \
             patch.object(parallel.subprocess, 'Popen',
                          side_effect=OSError('test launch failure')):
            result = parallel.run_parallel_audit(
                ['Print Assumptions Federer.A.first.'],
                ['From Federer Require Import A.'], 1, folder,
                ['never-run'], candidate.split_results, candidate.ALLOWED)
            self.assertTrue(any('OSError: test launch failure' in e
                                for e in result['errors']))
            self.assertEqual(result['results'], [None])

    def test_empty_selection_launches_nothing(self):
        with tempfile.TemporaryDirectory() as folder, \
             patch.object(parallel.subprocess, 'Popen') as launch:
            result = parallel.run_parallel_audit(
                [], [], 0, folder, [], candidate.split_results,
                candidate.ALLOWED)
        launch.assert_not_called()
        self.assertEqual(result['results'], [])
        self.assertEqual(result['errors'], [])

    def test_admission_uses_existing_day_night_and_memory_limits(self):
        policy = guard.read_policy()
        for stamp, expected in [
                ('2026-11-18T12:00:00+01:00', 1),
                ('2026-11-18T19:00:00+01:00', 3),
                ('2026-11-21T12:00:00+01:00', 3)]:
            with self.subTest(stamp=stamp):
                from datetime import datetime
                profile = guard.profile_at(policy,
                    datetime.fromisoformat(stamp))
                fake = SimpleNamespace(
                    read_policy=lambda: policy,
                    profile_at=lambda _: profile,
                    worker_limit=guard.worker_limit,
                    available_mib=lambda: 10000,
                    cpu_count=lambda: 14)
                self.assertEqual(parallel.admitted_workers(
                    14, list(range(20)), fake), expected)
        fake.available_mib = lambda: 1000
        with self.assertRaisesRegex(ValueError, 'admits no'):
            parallel.admitted_workers(4, ['query'], fake)
        self.assertEqual(parallel.admitted_workers(4, [], fake), 0)


class IntegratedAuditTests(unittest.TestCase):
    old = (
        'From Federer Require Import A B Z.\n'
        'Goal True. idtac "=== original ===". exact I. Qed.\n'
        'Print Assumptions Federer.A.first.\n'
        'Print Assumptions Federer.B.second.\n'
        'Print Assumptions Federer.A.first.\n'
        'Print Assumptions Federer.Z.unchanged.\n')
    new = (old + '\nFrom Federer Require Import C.\n'
           'Print Assumptions Federer.C.third.\n'
           'Print Assumptions Federer.A.first.\n')
    result_by_name = {'Federer.A.first': CLOSED,
                      'Federer.B.second': FUNCTIONAL,
                      'Federer.Z.unchanged': CLOSED,
                      'Federer.C.third': PROPOSITIONAL}

    def test_serial_oracle_is_the_immutable_original(self):
        origin = json.loads((STAGED/'fixtures'/
                             'dependency_audit_serial_oracle.json').read_text())
        self.assertEqual(hashlib.sha256(ORACLE_PATH.read_bytes()).hexdigest(),
                         origin['sha256'])
        self.assertEqual(candidate.SWITCH, oracle.SWITCH)
        self.assertEqual(candidate.WARNINGS, oracle.WARNINGS)
        self.assertEqual(candidate.ALLOWED, oracle.ALLOWED)

    def output(self, source, replacement=None):
        results = dict(self.result_by_name)
        results.update(replacement or {})
        return '\n'.join(results[line[len('Print Assumptions '):-1]]
                         for line in source.splitlines()
                         if line.startswith('Print Assumptions ')) + '\n'

    def execute(self, audit, options, replacement=None, compiler_stderr=''):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root/'tests').mkdir()
            (root/'docs').mkdir()
            build = root/'build'
            (build/'tests').mkdir(parents=True)
            (root/'tests'/'Assumptions.v').write_text(self.new)
            log = root/'docs'/'assumptions.log'
            original_log = '=== retained ===\n'+self.output(self.old)
            log.write_text(original_log)
            compiler = FakeCompiler(
                lambda s: self.output(s, replacement),
                stderr=compiler_stderr, delay={0: 3})

            # The serial oracle predates the move into federer1969/; the
            # candidate reads the subproject's paths and renames.
            def git(*arguments, quiet=False):
                if arguments in {('show', 'BASE:tests/Assumptions.v'),
                                 ('show', 'BASE:./tests/Assumptions.v')}:
                    return self.old
                if arguments in {('show', 'BASE:docs/assumptions.log'),
                                 ('show', 'BASE:./docs/assumptions.log')}:
                    return original_log
                if arguments == ('rev-parse', '--show-prefix'):
                    return 'federer1969/\n'
                if arguments[:2] == ('diff', '--name-only'):
                    return 'theories/A.v\ntheories/C.v\n'
                if arguments[:2] == ('diff', '--name-status'):
                    return ('M\tfederer1969/theories/A.v\n'
                            'R100\tfederer1969/theories/B.v\tfederer1969/theories/B.v\n'
                            'R100\ttheories/Z.v\tfederer1969/theories/Z.v\n'
                            'R090\ttheories/C.v\tfederer1969/theories/C.v\n')
                if arguments[:1] == ('ls-files',):
                    return ''
                raise AssertionError(arguments)

            output = io.StringIO()
            with ExitStack() as stack:
                stack.enter_context(patch.object(audit, 'ROOT', root))
                stack.enter_context(patch.object(audit, 'BUILD', build))
                stack.enter_context(patch.object(audit, 'check_owner'))
                stack.enter_context(patch.object(audit, 'git',
                                                side_effect=git))
                stack.enter_context(patch.object(audit, 'module_graph',
                    return_value={'theories/A': set(),
                                  'theories/B': {'theories/A'},
                                  'theories/C': set(),
                                  'theories/Z': set()}))
                stack.enter_context(patch.object(audit, 'glob_names',
                                                return_value={}))
                stack.enter_context(patch.object(audit.subprocess, 'run',
                                                side_effect=compiler.run))
                stack.enter_context(patch.object(parallel.subprocess, 'Popen',
                                                side_effect=compiler.popen))
                stack.enter_context(patch.object(parallel,
                    'admitted_workers', side_effect=lambda n, q, g: min(n, len(q))))
                stack.enter_context(patch.object(parallel,
                    'current_worker_ceiling', return_value=None))
                stack.enter_context(patch.object(parallel.time, 'sleep'))
                stack.enter_context(patch.object(sys, 'argv',
                    ['dependency_audit.py', 'BASE']+options))
                stack.enter_context(redirect_stdout(output))
                with self.assertRaises(SystemExit) as exit_status:
                    audit.main()
            return (exit_status.exception.code, json.loads(output.getvalue()),
                    log.read_text(), compiler.sources, original_log)

    def test_default_full_import_path_matches_the_original_serial_oracle(self):
        old = self.execute(oracle, [])
        new = self.execute(candidate, [])
        self.assertEqual(old[:4], new[:4])
        self.assertEqual(new[0], 0)
        self.assertIn('From Federer Require Import A B Z.', new[3][0])
        self.assertEqual(candidate.split_results(new[2])[3], CLOSED)
        self.assertNotIn('Print Assumptions Federer.Z.unchanged.',
                         new[3][0])

    def test_parallel_targeted_merge_matches_serial_oracle_and_retains_old(self):
        serial = self.execute(oracle, ['--targeted-imports'])
        multi = self.execute(candidate,
            ['--targeted-imports', '--workers', '2'])
        self.assertEqual(serial[0], 0)
        self.assertEqual(multi[0], 0)
        self.assertEqual(serial[2], multi[2])
        self.assertEqual(serial[1]['entries'], multi[1]['entries'])
        self.assertEqual(serial[1]['audited_old'], 3)
        self.assertEqual(multi[1]['audited_old'], 3)
        self.assertEqual(multi[1]['audited_new'], 2)
        self.assertEqual(len(candidate.split_results(multi[2])), 6)
        self.assertEqual(multi[1]['workers'], 2)

    def test_parallel_summary_exposes_its_unique_merged_log(self):
        code, summary, _, _, _ = self.execute(candidate,
            ['--targeted-imports', '--workers', '2'])
        self.assertEqual(code, 0)
        self.assertEqual(Path(summary['parallel_merged_log']),
            Path(summary['parallel_run_directory'])/'merged.log')
        self.assertNotIn('DependencyAuditScratch',
                         summary['parallel_merged_log'])

    def test_changed_old_assumption_set_fails_without_writing_complete_log(self):
        for options in [[], ['--targeted-imports', '--workers', '2']]:
            with self.subTest(options=options):
                code, summary, log, _, before = self.execute(
                    candidate, options,
                    replacement={'Federer.A.first': PROPOSITIONAL})
                self.assertEqual(code, 1)
                self.assertIn('2 existing entries changed their assumptions',
                              summary['errors'])
                self.assertEqual(log, before)

    def test_warning_or_forbidden_assumption_never_rewrites_log(self):
        cases = [
            ({'Federer.C.third': 'Axioms:\nunsafe.fake : Prop'}, ''),
            ({}, 'Warning: test warning\n'),
        ]
        for replacement, stderr in cases:
            with self.subTest(replacement=replacement, stderr=stderr):
                code, summary, log, _, before = self.execute(
                    candidate, ['--targeted-imports', '--workers', '2'],
                    replacement=replacement, compiler_stderr=stderr)
                self.assertEqual(code, 1)
                self.assertTrue(summary['errors'])
                self.assertEqual(log, before)

    def test_cli_requires_positive_workers_and_targeted_imports(self):
        self.assertEqual(candidate.parse_options(['BASE']).workers, 1)
        for options in [['BASE', '--workers', '0'],
                        ['BASE', '--workers', '-1'],
                        ['BASE', '--workers', '2'],
                        ['BASE', '--workers', 'x', '--targeted-imports']]:
            with self.subTest(options=options), redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit):
                    candidate.parse_options(options)

    def test_targeted_import_resolution_fails_closed(self):
        for name, modules in [
                ('plain_name', {'theories/A'}),
                ('A.first', {'theories/A'}),
                ('Federer.A.first', None),
                ('Federer.A.first', {'theories/A', 'theories/B'}),
                ('Federer.A.first', {'tests/A'}),
                ('FedererTests.A.first', {'theories/A'})]:
            with self.subTest(name=name, modules=modules):
                with self.assertRaises(ValueError):
                    candidate.qualified_query_import(name, modules)
        self.assertEqual(candidate.qualified_query_import(
            'Federer.A.Inner.first', {'theories/A'}),
            'From Federer Require Import A.')


if __name__ == '__main__':
    unittest.main()
