# Build resources

[Documentation](toc.md) · [Validation](validation.md) · [Maintenance](maintenance.md)

## Current machine and profiles

The current laptop has an Intel Core i7-8550U with 4 physical cores and
8 logical CPUs, about 15.5 GiB of RAM and 17 GiB of swap. Detect available
CPUs and RAM before choosing workers; the previous laptop's 14 logical CPUs
do not describe this machine. Compiler admission uses available RAM,
without adding swap capacity. The daytime limit of two compilers on two
cores is retained on this machine at the user's request.

The policy uses Europe/Warsaw time, including daylight-saving changes.

| Time | CPU use | RAM | Workers |
| --- | --- | --- | --- |
| Monday–Friday, 07:00–17:00 | At most two CPU cores for the whole computation tree, one core per compiler. | Leave at least 2.5 GiB available for interactive applications. | At most two compilers. |
| Weekday nights, 17:00–07:00 | No project CPU quota. | No fixed project reserve or memory cap; use the available RAM. | Use as many independent workers as available CPUs and RAM support. |
| Friday 17:00–Monday 07:00 | No project CPU quota throughout the weekend. | No fixed project reserve or memory cap; use the available RAM. | Use as many independent workers as available CPUs and RAM support. |

Both profiles retain nice 10, the required opam switch, umask 0002,
group `llm`, group read/write access and separate build artifacts under
`/opt/rocq/federer-build`. A worker limit does not permit overlapping builds
in the same artifact tree. Registered compilation, recursive kernel
checking and the assumptions audit still run in order. Private compilers
must not overlap a registered build or recursive kernel check.

## Running computation

Use [resource_guard.py](../tools/resource_guard.py) for Rocq compilation,
kernel checks, audits and other substantial computations on this laptop.
The settings are in [resource-policy.json](../tools/resource-policy.json).
The guard requires the host's systemd user manager and cgroup v2 controls;
it fails before starting computation if those controls are unavailable.
When a noninteractive shell lacks `XDG_RUNTIME_DIR`, the guard uses the
user's own runtime directory `/run/user/UID` to reach that manager.

Inspect the current profile and a memory-aware worker recommendation:

```sh
python3 -B tools/resource_guard.py show --estimated-memory-mib 2048
```

The estimate is the peak memory of one worker. A recommendation of zero
means that computation must wait. The daytime admission test adds a 25%
growth allowance to that estimate, then adds the 2.5 GiB reserve. Thus a
2 GiB focused check waits until at least 5 GiB is available. Overnight and
throughout the weekend,
admission requires the estimate alone, without a fixed reserve or growth
allowance. Estimates and worker counts should follow measured peaks.

For a command, give the estimated peak of its **whole process tree** and
a report path in the build tree. For example, a sequential ordinary build
can be run with:

```sh
sg llm -c 'umask 0002; python3 -B tools/resource_guard.py run \
  --estimated-memory-mib 2048 \
  --report /opt/rocq/federer-build/resources/build.json \
  -- opam exec --switch=RP.2026.02.0~9.1~2026.01 -- make -j1'
```

Use a fresh report path for each validation attempt. For an unrestricted
parallel build, sum the expected peaks of concurrent compilers and choose
workers from the available RAM and detected CPUs. The full-import audit
has previously needed about 8 GiB; a small compiler estimate is unsuitable
for that audit. Targeted dependency audits have their own measured peaks.

## Live safeguards and interruptions

The guard supervises the whole command in its own cgroup. During the day,
the CPU quota applies to that entire group, and a memory ceiling contains
unexpected growth. If available RAM falls below the reserve, the guard
terminates only its own computation, retains the report and returns exit
status 75. A memory ceiling or another unsuccessful command also leaves
an unsuccessful attempt; none certifies a proof or release. Recheck the
affected source normally when resources permit.

A running command changes profiles automatically at 17:00 and 07:00 on
weekdays. The unrestricted profile continues from Friday 17:00 through
Monday 07:00, including both daylight-saving transitions. At Monday
07:00 the daytime safeguards apply even to a job started during the weekend.
Each guard reads its code and policy at startup; a change to these files
requires a new guard invocation. Preserve the old report when replacing a
running guard, and change only the computation's own scope.
Do not close, signal or reconfigure the user's browser, editor, LaTeX
processes or other applications to make room for a build.

The policy tests cover weekday and weekend boundaries, summer and winter
offsets, daylight-saving weekends, RAM admission, worker recommendations
and the scope properties. Run them with:

```sh
python3 -B -m unittest discover -s tools -p test_resource_guard.py -v
```

The host controls have also been checked on a small diagnostic process:
the half-core quota was enforced, and live transitions removed and
restored the CPU and memory limits. These are resource-control tests,
not mathematical validation.
