"""Apply the project's weekday, overnight and weekend resource policy.

CPU quotas cover the whole command tree. Daytime memory admission leaves
room for interactive applications; a live reserve check and a cgroup memory
limit protect against unexpected growth. Interrupted checks return 75 and
retain their report. The clock uses Europe/Warsaw, including DST changes.
Only processes started in this command's own scope are stopped.
"""
import argparse
from datetime import datetime
import grp
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid
from zoneinfo import ZoneInfo

POLICY_PATH = Path(__file__).with_name('resource-policy.json')
TEMPORARY_FAILURE = 75


def read_policy():
    return json.loads(POLICY_PATH.read_text())


def locate_user_manager():
    """Point systemctl and systemd-run at the user's own manager.

    Noninteractive shells may lack XDG_RUNTIME_DIR; the standard runtime
    directory /run/user/UID is used only when it exists and is owned by
    the current user.
    """
    if os.environ.get('XDG_RUNTIME_DIR'):
        return
    runtime = Path('/run/user') / str(os.getuid())
    try:
        if runtime.is_dir() and runtime.stat().st_uid == os.getuid():
            os.environ['XDG_RUNTIME_DIR'] = str(runtime)
    except OSError:
        pass


def profile_at(policy, when=None):
    now = (when or datetime.now(ZoneInfo(policy['timezone']))).astimezone(
        ZoneInfo(policy['timezone']))
    unrestricted = now.weekday() in policy.get('unrestricted_weekdays', [])
    name = ('day' if not unrestricted and policy['day_start_hour'] <= now.hour <
            policy['night_start_hour'] else 'night')
    return {'name': name, **policy[name]}


def available_mib():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) / 1024
    raise RuntimeError('MemAvailable is unavailable')


def cpu_count():
    return len(os.sched_getaffinity(0))


def memory_budget_mib(profile, estimate):
    factor = profile['memory_limit_factor']
    return math.ceil(estimate * factor) if factor else estimate


def admitted(profile, estimate, available):
    return available >= profile['reserve_mib'] + memory_budget_mib(profile, estimate)


def worker_limit(profile, estimate, available, cpus):
    by_memory = max(0, int((available - profile['reserve_mib']) //
                           memory_budget_mib(profile, estimate)))
    return min(cpus, profile['max_workers'] or cpus, by_memory)


def properties(profile, estimate):
    quota = profile['cpu_quota_percent']
    limited = profile['memory_limit_factor'] is not None
    return {
        'CPUAccounting': 'yes',
        'MemoryAccounting': 'yes',
        # systemd resets CPUQuota with an empty assignment, not "infinity".
        'CPUQuota': f'{quota}%' if quota is not None else '',
        'CPUWeight': str(profile['cpu_weight']),
        'IOWeight': str(profile['io_weight']),
        'MemoryHigh': f'{math.ceil(estimate)}M' if limited else 'infinity',
        'MemoryMax': f'{memory_budget_mib(profile, estimate)}M' if limited else 'infinity',
    }


def run_control(*args):
    return subprocess.run(['systemctl', '--user', *args], check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)


def stop_scope(unit, process):
    # The unique unit and new process group belong only to this invocation.
    subprocess.run(['systemctl', '--user', 'kill', '--kill-whom=all',
                    '--signal=SIGTERM', unit], stdout=subprocess.DEVNULL,
                   stderr=subprocess.DEVNULL)
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        subprocess.run(['systemctl', '--user', 'kill', '--kill-whom=all',
                        '--signal=SIGKILL', unit], stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL)
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait(timeout=5)


def run_guarded(command, report_path, estimate):
    if os.getgid() != grp.getgrnam('llm').gr_gid:
        raise RuntimeError('Run project computation with group llm, for example through sg llm.')
    policy = read_policy()
    os.umask(0o002)
    report_path = Path(report_path)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    if report_path.exists():
        raise RuntimeError('Refusing to overwrite an earlier resource report: ' + str(report_path))
    record = {'status': 'waiting', 'command': command, 'policy': policy,
              'estimated_memory_mib': estimate, 'logical_cpus': cpu_count(),
              'created': datetime.now().astimezone().isoformat(), 'transitions': []}

    def save():
        temporary = report_path.with_name(report_path.name + '.tmp')
        temporary.write_text(json.dumps(record, indent=2) + '\n')
        temporary.replace(report_path)

    save()
    waiting_profile = None
    waiting_signal = None

    def cancel_wait(signum, frame):
        nonlocal waiting_signal
        waiting_signal = signum

    waiting_handlers = {sig: signal.signal(sig, cancel_wait)
                        for sig in (signal.SIGINT, signal.SIGTERM)}
    try:
        while True:
            if waiting_signal is not None:
                record.update(status='interrupted', interruption='signal during memory admission',
                              signal=waiting_signal, finished=datetime.now().astimezone().isoformat())
                save()
                return TEMPORARY_FAILURE
            profile = profile_at(policy)
            if profile['name'] != waiting_profile:
                waiting_profile = profile['name']
                record['waiting_profile'] = profile
                record['available_mib'] = round(available_mib(), 3)
                save()
            if admitted(profile, estimate, available_mib()):
                break
            time.sleep(1)
    finally:
        for sig, handler in waiting_handlers.items():
            signal.signal(sig, handler)

    # Fail closed if the user manager cannot enforce the requested limits.
    try:
        run_control('show-environment')
    except subprocess.CalledProcessError as error:
        record.update(status='failed', controller_error=error.stderr,
                      finished=datetime.now().astimezone().isoformat())
        save()
        raise
    unit = 'federer-compute-' + uuid.uuid4().hex + '.scope'
    props = properties(profile, estimate)
    launch = ['systemd-run', '--user', '--scope', '--quiet', '--collect', '--unit=' + unit]
    launch += ['--property=' + k + '=' + v for k, v in props.items()]
    launch += ['--', *command]
    record.update(status='running', started=datetime.now().astimezone().isoformat(),
                  unit=unit, admission_available_mib=round(available_mib(), 3),
                  active_profile=profile, enforced_properties=props)
    save()

    def lower_priority():
        os.setpriority(os.PRIO_PROCESS, 0, max(policy['nice'], os.getpriority(os.PRIO_PROCESS, 0)))

    process = subprocess.Popen(launch, start_new_session=True, preexec_fn=lower_priority)
    interrupted = None
    started = time.monotonic()
    minimum = available_mib()
    peak = 0
    cgroup = None

    def cancel(signum, frame):
        nonlocal interrupted
        interrupted = 'guard received signal ' + str(signum)

    old_handlers = {sig: signal.signal(sig, cancel) for sig in (signal.SIGINT, signal.SIGTERM)}
    try:
        while process.poll() is None:
            current = profile_at(policy)
            memory = available_mib()
            minimum = min(minimum, memory)
            if current['name'] != profile['name']:
                props = properties(current, estimate)
                run_control('set-property', '--runtime', unit,
                            *[k + '=' + v for k, v in props.items()])
                record['transitions'].append({'time': datetime.now().astimezone().isoformat(),
                                              'profile': current, 'properties': props})
                profile = current
                record['active_profile'] = current
                record['enforced_properties'] = props
                save()
            if profile['reserve_mib'] and memory < profile['reserve_mib']:
                interrupted = 'daytime available-memory reserve reached'
            if interrupted:
                stop_scope(unit, process)
                break
            if cgroup is None:
                result = subprocess.run(['systemctl', '--user', 'show', unit,
                                         '--property=ControlGroup', '--value'],
                                        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
                if result.returncode == 0 and result.stdout.strip():
                    cgroup = Path('/sys/fs/cgroup') / result.stdout.strip().lstrip('/')
            if cgroup is not None:
                try:
                    peak = max(peak, int((cgroup / 'memory.peak').read_text()))
                except (FileNotFoundError, ValueError):
                    pass
            time.sleep(policy['poll_seconds'])
    except BaseException as error:
        interrupted = 'resource controller failed: ' + str(error)
        stop_scope(unit, process)
        raise
    finally:
        for sig, handler in old_handlers.items():
            signal.signal(sig, handler)
        record.update(finished=datetime.now().astimezone().isoformat(),
                      seconds=round(time.monotonic() - started, 3),
                      minimum_available_mib=round(minimum, 3),
                      peak_scope_memory_mib=round(peak / 1024**2, 3),
                      command_returncode=process.returncode, interruption=interrupted,
                      status='interrupted' if interrupted else
                      ('passed' if process.returncode == 0 else 'failed'))
        save()
    return TEMPORARY_FAILURE if interrupted else process.returncode


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    show = sub.add_parser('show', help='Show the current profile and a memory-aware worker limit.')
    show.add_argument('--estimated-memory-mib', type=int, default=2048)
    run = sub.add_parser('run', help='Wait for headroom, then supervise one computation tree.')
    run.add_argument('--estimated-memory-mib', type=int, required=True)
    run.add_argument('--report', required=True)
    run.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.estimated_memory_mib <= 0:
        parser.error('The memory estimate must be positive.')
    if args.action == 'show':
        profile = profile_at(read_policy())
        memory = available_mib()
        print(json.dumps({'profile': profile, 'logical_cpus': cpu_count(),
                          'available_mib': round(memory, 3),
                          'admission_required_mib': profile['reserve_mib'] +
                          memory_budget_mib(profile, args.estimated_memory_mib),
                          'workers': worker_limit(profile, args.estimated_memory_mib, memory, cpu_count())},
                         indent=2))
        return 0
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        parser.error('A command is required after --.')
    locate_user_manager()
    return run_guarded(command, args.report, args.estimated_memory_mib)


if __name__ == '__main__':
    sys.exit(main())
