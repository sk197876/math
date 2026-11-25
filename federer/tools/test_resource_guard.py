"""Check profile boundaries, memory admission and whole-job resource limits."""
from datetime import datetime
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

import resource_guard as guard


class ResourcePolicyTests(unittest.TestCase):
    def setUp(self):
        self.policy = guard.read_policy()

    def profile(self, timestamp):
        return guard.profile_at(self.policy, datetime.fromisoformat(timestamp))

    def test_winter_boundaries(self):
        self.assertEqual(self.profile('2026-11-18T05:59:59+00:00')['name'], 'night')
        self.assertEqual(self.profile('2026-11-18T06:00:00+00:00')['name'], 'day')
        self.assertEqual(self.profile('2026-11-18T15:59:59+00:00')['name'], 'day')
        self.assertEqual(self.profile('2026-11-18T16:00:00+00:00')['name'], 'night')

    def test_summer_boundaries(self):
        self.assertEqual(self.profile('2026-07-17T04:59:59+00:00')['name'], 'night')
        self.assertEqual(self.profile('2026-07-17T05:00:00+00:00')['name'], 'day')
        self.assertEqual(self.profile('2026-07-17T14:59:59+00:00')['name'], 'day')
        self.assertEqual(self.profile('2026-07-17T15:00:00+00:00')['name'], 'night')

    def test_daylight_saving_changes_preserve_local_hours(self):
        for stamp in ['2026-03-30T07:00:00+02:00', '2026-10-26T07:00:00+01:00']:
            self.assertEqual(self.profile(stamp)['name'], 'day')
        for stamp in ['2026-03-30T17:00:00+02:00', '2026-10-26T17:00:00+01:00']:
            self.assertEqual(self.profile(stamp)['name'], 'night')

    def test_weekend_is_unrestricted_until_monday_morning(self):
        for friday, monday, offset in [('2026-11-20', '2026-11-23', '+01:00'),
                                        ('2026-07-17', '2026-07-20', '+02:00')]:
            with self.subTest(friday=friday):
                self.assertEqual(self.profile(friday+'T16:59:59'+offset)['name'], 'day')
                self.assertEqual(self.profile(friday+'T17:00:00'+offset)['name'], 'night')
                self.assertEqual(self.profile(monday+'T06:59:59'+offset)['name'], 'night')
                self.assertEqual(self.profile(monday+'T07:00:00'+offset)['name'], 'day')
        for day in ['2026-11-21', '2026-11-22', '2026-07-18', '2026-07-19']:
            for hour in [0, 7, 12, 16, 17, 23]:
                with self.subTest(day=day, hour=hour):
                    profile = self.profile(f'{day}T{hour:02}:00:00+00:00')
                    self.assertEqual(profile['name'], 'night')
                    props = guard.properties(profile, 2048)
                    self.assertEqual(props['CPUQuota'], '')
                    self.assertEqual(props['MemoryMax'], 'infinity')
                    self.assertEqual(profile['reserve_mib'], 0)
                    self.assertIsNone(profile['max_workers'])
                    self.assertEqual(guard.worker_limit(profile, 1024, 15000, 14), 14)

    def test_daylight_saving_sundays_remain_unrestricted(self):
        for stamp in ['2026-03-29T01:59:59+01:00', '2026-03-29T03:00:00+02:00',
                      '2026-03-29T07:00:00+02:00', '2026-03-29T17:00:00+02:00',
                      '2026-10-25T02:59:59+02:00', '2026-10-25T02:00:00+01:00',
                      '2026-10-25T07:00:00+01:00', '2026-10-25T17:00:00+01:00']:
            with self.subTest(stamp=stamp):
                self.assertEqual(self.profile(stamp)['name'], 'night')

    def test_older_policy_snapshots_keep_their_recorded_schedule(self):
        older = {k: v for k, v in self.policy.items() if k != 'unrestricted_weekdays'}
        saturday = datetime.fromisoformat('2026-11-21T12:00:00+01:00')
        self.assertEqual(guard.profile_at(older, saturday)['name'], 'day')

    def test_day_admission_reserves_ram_and_growth_margin(self):
        day = self.profile('2026-11-18T12:00:00+01:00')
        required = 5 * 1024
        self.assertFalse(guard.admitted(day, 2048, required - 1))
        self.assertTrue(guard.admitted(day, 2048, required))
        self.assertEqual(guard.worker_limit(day, 2048, 15000, 14), 2)
        self.assertEqual(guard.worker_limit(day, 2048, 6000, 14), 1)
        self.assertEqual(guard.worker_limit(day, 2048, 3000, 14), 0)

    def test_night_uses_available_memory_and_detected_cpus(self):
        night = self.profile('2026-11-18T19:00:00+01:00')
        self.assertEqual(guard.worker_limit(night, 1024, 15000, 14), 14)
        self.assertEqual(guard.worker_limit(night, 2048, 6000, 14), 2)
        self.assertEqual(guard.worker_limit(night, 2048, 1000, 14), 0)
        self.assertTrue(guard.admitted(night, 2048, 2048))

    def test_day_properties_limit_whole_job(self):
        props = guard.properties(self.profile('2026-11-18T12:00:00+01:00'), 2048)
        self.assertEqual(props['CPUQuota'], '200%')
        self.assertEqual(props['CPUWeight'], '10')
        self.assertEqual(props['MemoryHigh'], '2048M')
        self.assertEqual(props['MemoryMax'], '2560M')

    def test_night_properties_remove_artificial_caps(self):
        props = guard.properties(self.profile('2026-11-18T19:00:00+01:00'), 2048)
        self.assertEqual(props['CPUQuota'], '')
        self.assertEqual(props['MemoryHigh'], 'infinity')
        self.assertEqual(props['MemoryMax'], 'infinity')

    def test_running_command_changes_both_profiles(self):
        day = self.profile('2026-11-18T12:00:00+01:00')
        night = self.profile('2026-11-18T19:00:00+01:00')
        process = Mock(pid=123, returncode=0)
        process.poll.side_effect = [None, None, 0]
        with tempfile.TemporaryDirectory() as folder:
            report = Path(folder) / 'resources.json'
            with patch.object(guard.grp, 'getgrnam', return_value=SimpleNamespace(gr_gid=guard.os.getgid())), \
                 patch.object(guard, 'profile_at', side_effect=[day, night, day]), \
                 patch.object(guard, 'available_mib', return_value=8000), \
                 patch.object(guard, 'run_control') as control, \
                 patch.object(guard.subprocess, 'Popen', return_value=process) as launch, \
                 patch.object(guard.subprocess, 'run', return_value=SimpleNamespace(returncode=0, stdout='')), \
                 patch.object(guard.time, 'sleep'):
                self.assertEqual(guard.run_guarded(['example-command'], report, 2048), 0)
            data = json.loads(report.read_text())
            self.assertEqual([t['profile']['name'] for t in data['transitions']], ['night', 'day'])
            self.assertIn('--property=CPUQuota=200%', launch.call_args.args[0])
            updates = [call.args for call in control.call_args_list if call.args[0] == 'set-property']
            self.assertIn('CPUQuota=', updates[0])
            self.assertIn('MemoryMax=infinity', updates[0])
            self.assertIn('CPUQuota=200%', updates[1])
            self.assertIn('MemoryMax=2560M', updates[1])
            self.assertEqual(data['status'], 'passed')

    def test_morning_memory_pressure_stops_only_own_scope(self):
        night = self.profile('2026-11-18T06:59:59+01:00')
        day = self.profile('2026-11-18T07:00:00+01:00')
        process = Mock(pid=123, returncode=-15)
        process.poll.return_value = None
        with tempfile.TemporaryDirectory() as folder:
            report = Path(folder) / 'resources.json'
            with patch.object(guard.grp, 'getgrnam', return_value=SimpleNamespace(gr_gid=guard.os.getgid())), \
                 patch.object(guard, 'profile_at', side_effect=[night, day]), \
                 patch.object(guard, 'available_mib', return_value=2048), \
                 patch.object(guard, 'run_control'), \
                 patch.object(guard.subprocess, 'Popen', return_value=process), \
                 patch.object(guard, 'stop_scope') as stop:
                self.assertEqual(guard.run_guarded(['example-command'], report, 2048), 75)
            data = json.loads(report.read_text())
            stop.assert_called_once_with(data['unit'], process)
            self.assertEqual(data['status'], 'interrupted')
            self.assertEqual(data['active_profile']['name'], 'day')

    def test_prior_report_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as folder:
            report = Path(folder) / 'resources.json'
            report.write_text('earlier attempt\n')
            with patch.object(guard.grp, 'getgrnam', return_value=SimpleNamespace(gr_gid=guard.os.getgid())), \
                 self.assertRaisesRegex(RuntimeError, 'Refusing to overwrite'):
                guard.run_guarded(['example-command'], report, 2048)
            self.assertEqual(report.read_text(), 'earlier attempt\n')


if __name__ == '__main__':
    unittest.main()
