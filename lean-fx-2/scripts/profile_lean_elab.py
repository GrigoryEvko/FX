#!/usr/bin/env python3
"""Profile Lean elaboration hot spots across LeanFX2 source files.

Runs Lean's profiler (``-Dprofiler=true -Dtrace.profiler=true``) per source
file and turns the raw trace into *line-level* hot-spot reports: every slow
declaration is anchored to ``file:line`` and broken down by the tactic / phase
that actually cost the time (``simp``, ``exact``, ``type checking``, ...).

Why this design (lessons from the previous version):

* ``trace.profiler=true`` is what makes the trace name each declaration via
  ``[Elab.definition.value] [secs] <FQN>``.  Without it you only get anonymous
  per-command phase blocks and cannot point at a line.  But it also echoes the
  full elaborated terms (~1300 lines for one heavy theorem), so the child
  process is read **streaming, line-filtered** — never buffered whole — or a
  project-wide sweep exhausts memory.
* The previous version oversubscribed (``workers * lean-jobs`` threads) and
  killed every heavy file at a fixed timeout, so the slowest — most
  interesting — files reported *no* data (exit 124, empty events).  Here the
  default is **no timeout** and ``--lean-jobs 1`` (with ``Elab.async=false``
  each ``lean`` is ~1 core, so parallelism comes from ``--workers``).
* ``lean`` is invoked directly with a resolved ``LEAN_PATH`` (no per-file
  ``lake`` fork), inside its own process group, so a watchdog can kill the
  whole group cleanly if a ceiling is set.
"""

from __future__ import annotations

import argparse
import collections
import concurrent.futures
import dataclasses
import os
import pathlib
import re
import signal
import subprocess
import sys
import threading
import time
from typing import Iterable


ROOT_DEFAULT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT_DEFAULT = pathlib.Path("/tmp/leanfx2-elab-profile")

# `[Elab.definition.value] [0.422317] <emoji> LeanFX2.Term.foo`
DEF_VALUE_RE = re.compile(
    r"\[Elab\.definition\.value\]\s+\[([0-9.]+)\]\s+\S+\s+(\S+)"
)
DEF_HEADER_RE = re.compile(
    r"\[Elab\.definition\.header\]\s+\[([0-9.]+)\]\s+\S+\s+(\S+)"
)
# `[Elab.command] [0.18] <emoji> <leading command text...>`
COMMAND_RE = re.compile(r"\[Elab\.command\]\s+\[([0-9.]+)\]\s+(.*)$")
# `tactic execution of Lean.Parser.Tactic.exact took 173ms`
TACTIC_RE = re.compile(r"^tactic execution of (\S+) took ([0-9.]+)(ms|s)\b")
# Generic `<phase words> took 90.5ms` (simp / type checking / elaboration / ...)
PHASE_RE = re.compile(r"^([A-Za-z][A-Za-z .]*?) took ([0-9.]+)(ms|s)\b")
# Any line worth keeping in the per-file filtered log.
KEEP_RE = re.compile(
    r"(took |\[Elab\.command\]|\[Elab\.definition\.(value|header)\]"
    r"|error:|warning:|uncaught exception)"
)
# Declaration headers in source, to map FQN-final-segment -> source line.
DECL_HEADER_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|opaque|inductive|structure|class)\s+"
    # Lean identifiers admit `?`, `!`, and `'` suffixes (decision procedures,
    # impure-flavoured helpers, primed variants) — omitting them stranded ~248
    # declarations at line 0 (e.g. `strengthenTyped?_rename_eq_*`).
    r"([A-Za-z_][A-Za-z0-9_'?!.]*)"
)


def to_milliseconds(value_text: str, unit_text: str = "s") -> float:
    value = float(value_text)
    return value * 1000.0 if unit_text == "s" else value


def final_segment(fully_qualified: str) -> str:
    return fully_qualified.rsplit(".", 1)[-1]


@dataclasses.dataclass
class DeclarationTiming:
    """Per-declaration elaboration cost with its phase breakdown."""

    declaration: str
    file_path: str
    source_line: int
    value_ms: float = 0.0
    header_ms: float = 0.0
    phase_ms: dict[str, float] = dataclasses.field(default_factory=dict)
    phase_count: dict[str, int] = dataclasses.field(default_factory=dict)

    @property
    def total_ms(self) -> float:
        return self.value_ms + self.header_ms

    def add_phase(self, phase: str, milliseconds: float) -> None:
        self.phase_ms[phase] = self.phase_ms.get(phase, 0.0) + milliseconds
        self.phase_count[phase] = self.phase_count.get(phase, 0) + 1

    def dominant_phase(self) -> tuple[str, float]:
        if not self.phase_ms:
            return ("-", 0.0)
        phase = max(self.phase_ms, key=lambda key: self.phase_ms[key])
        return (phase, self.phase_ms[phase])


@dataclasses.dataclass
class FileResult:
    file_path: str
    wall_seconds: float
    return_code: int
    declarations: list[DeclarationTiming]
    error_tail: str


def build_decl_line_index(source_text: str) -> dict[str, list[int]]:
    """Map every declared short name to the source line(s) of its header.

    The profiler reports fully-qualified names (``LeanFX2.Term.foo``) while the
    source writes the short name (``foo``) under a ``namespace`` block, so the
    final segment is the lookup key.  Multiple matches (rare) are kept in source
    order and consumed front-to-back during attribution.
    """

    index: dict[str, list[int]] = collections.defaultdict(list)
    for line_number, raw_line in enumerate(source_text.splitlines(), start=1):
        match = DECL_HEADER_RE.match(raw_line)
        if match:
            index[final_segment(match.group(2))].append(line_number)
    return index


def resolve_source_line(
    decl_line_index: dict[str, list[int]],
    consumed_lines: dict[str, int],
    fully_qualified: str,
) -> int:
    candidates = decl_line_index.get(final_segment(fully_qualified))
    if not candidates:
        return 0
    used = consumed_lines.get(fully_qualified, 0)
    chosen = candidates[min(used, len(candidates) - 1)]
    consumed_lines[fully_qualified] = used + 1
    return chosen


def parse_profile_lines(
    file_path: str,
    profile_lines: Iterable[str],
    decl_line_index: dict[str, list[int]],
) -> list[DeclarationTiming]:
    """Single forward pass: attribute phase blocks to the active declaration."""

    declarations: dict[str, DeclarationTiming] = {}
    consumed_lines: dict[str, int] = {}
    active: DeclarationTiming | None = None

    def declaration_for(fully_qualified: str) -> DeclarationTiming:
        existing = declarations.get(fully_qualified)
        if existing is not None:
            return existing
        timing = DeclarationTiming(
            declaration=fully_qualified,
            file_path=file_path,
            source_line=resolve_source_line(
                decl_line_index, consumed_lines, fully_qualified
            ),
        )
        declarations[fully_qualified] = timing
        return timing

    for raw_line in profile_lines:
        line = raw_line.rstrip("\n")

        value_match = DEF_VALUE_RE.search(line)
        if value_match:
            active = declaration_for(value_match.group(2))
            active.value_ms += to_milliseconds(value_match.group(1))
            continue

        header_match = DEF_HEADER_RE.search(line)
        if header_match:
            timing = declaration_for(header_match.group(2))
            timing.header_ms += to_milliseconds(header_match.group(1))
            active = timing
            continue

        # Phase blocks have no leading bracket; ignore trace-tree node lines.
        stripped = line.lstrip()
        if stripped.startswith("["):
            continue

        tactic_match = TACTIC_RE.match(stripped)
        if tactic_match:
            if active is not None:
                active.add_phase(
                    "tac:" + final_segment(tactic_match.group(1)),
                    to_milliseconds(tactic_match.group(2), tactic_match.group(3)),
                )
            continue

        phase_match = PHASE_RE.match(stripped)
        if phase_match and active is not None:
            active.add_phase(
                phase_match.group(1).strip(),
                to_milliseconds(phase_match.group(2), phase_match.group(3)),
            )

    return list(declarations.values())


def profile_one(
    lean_binary: str,
    lean_env: dict[str, str],
    root: pathlib.Path,
    file_path: pathlib.Path,
    threshold_ms: int,
    timeout_seconds: int,
    lean_jobs: int,
    logs_dir: pathlib.Path,
) -> FileResult:
    command = [
        lean_binary,
        f"-j{lean_jobs}",
        "-DautoImplicit=false",
        "-DrelaxedAutoImplicit=false",
        "-DmaxHeartbeats=0",
        "-DElab.async=false",
        "-Dprofiler=true",
        "-Dtrace.profiler=true",
        f"-Dprofiler.threshold={threshold_ms}",
        str(file_path),
    ]

    decl_line_index = build_decl_line_index(
        (root / file_path).read_text(encoding="utf-8", errors="replace")
    )

    started_at = time.perf_counter()
    process = subprocess.Popen(
        command,
        cwd=root,
        env=lean_env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        bufsize=1,
        start_new_session=True,
    )

    timed_out = threading.Event()

    def kill_group() -> None:
        timed_out.set()
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass

    watchdog = (
        threading.Timer(timeout_seconds, kill_group)
        if timeout_seconds and timeout_seconds > 0
        else None
    )
    if watchdog is not None:
        watchdog.start()

    kept_lines: list[str] = []
    error_lines: list[str] = []
    try:
        assert process.stdout is not None
        for raw_line in process.stdout:
            if KEEP_RE.search(raw_line):
                kept_lines.append(raw_line.rstrip("\n"))
                if "error:" in raw_line or "uncaught exception" in raw_line:
                    error_lines.append(raw_line.rstrip("\n"))
    finally:
        return_code = process.wait()
        if watchdog is not None:
            watchdog.cancel()

    wall_seconds = time.perf_counter() - started_at
    if timed_out.is_set():
        return_code = 124

    log_path = logs_dir / (str(file_path).replace("/", "__") + ".log")
    log_path.write_text("\n".join(kept_lines) + "\n", encoding="utf-8")

    declarations = parse_profile_lines(str(file_path), kept_lines, decl_line_index)
    return FileResult(
        file_path=str(file_path),
        wall_seconds=wall_seconds,
        return_code=return_code,
        declarations=declarations,
        error_tail="\n".join(error_lines[-12:]),
    )


def should_skip(path: pathlib.Path, include_audit: bool) -> bool:
    parts = path.parts
    if include_audit:
        return False
    skipped_roots = {("LeanFX2", "Tools"), ("LeanFX2", "Smoke"), ("LeanFX2", "Sketch")}
    return len(parts) >= 2 and parts[0:2] in skipped_roots


def collect_files(root: pathlib.Path, include_audit: bool) -> list[pathlib.Path]:
    source_root = root / "LeanFX2"
    return [
        path.relative_to(root)
        for path in sorted(source_root.rglob("*.lean"))
        if not should_skip(path.relative_to(root), include_audit)
    ]


def resolve_lean_env(root: pathlib.Path) -> tuple[str, dict[str, str]]:
    """Get the `lean` binary path + LEAN_PATH once, so we skip per-file `lake`."""

    lean_binary = subprocess.run(
        ["lake", "env", "bash", "-c", "command -v lean"],
        cwd=root,
        text=True,
        capture_output=True,
        check=True,
    ).stdout.strip()
    lean_path = subprocess.run(
        ["lake", "env", "bash", "-c", "printf %s \"$LEAN_PATH\""],
        cwd=root,
        text=True,
        capture_output=True,
        check=True,
    ).stdout.strip()
    lean_env = dict(os.environ)
    lean_env["LEAN_PATH"] = lean_path
    return lean_binary, lean_env


def write_declarations_tsv(path: pathlib.Path, decls: list[DeclarationTiming]) -> None:
    with path.open("w", encoding="utf-8") as output:
        output.write("total_ms\tvalue_ms\theader_ms\tfile:line\tdeclaration\tdominant_phase\n")
        for decl in decls:
            phase, phase_ms = decl.dominant_phase()
            share = f"{phase}({phase_ms / decl.total_ms * 100:.0f}%)" if decl.total_ms else phase
            output.write(
                f"{decl.total_ms:.1f}\t{decl.value_ms:.1f}\t{decl.header_ms:.1f}\t"
                f"{decl.file_path}:{decl.source_line}\t{decl.declaration}\t{share}\n"
            )


def write_decl_phase_tsv(path: pathlib.Path, decls: list[DeclarationTiming]) -> None:
    rows: list[tuple[float, int, str, int, str, str]] = []
    for decl in decls:
        for phase, milliseconds in decl.phase_ms.items():
            rows.append(
                (milliseconds, decl.phase_count[phase], decl.file_path,
                 decl.source_line, decl.declaration, phase)
            )
    rows.sort(key=lambda row: row[0], reverse=True)
    with path.open("w", encoding="utf-8") as output:
        output.write("total_ms\tcount\tfile:line\tdeclaration\tphase\n")
        for milliseconds, count, file_path, line, declaration, phase in rows:
            output.write(
                f"{milliseconds:.1f}\t{count}\t{file_path}:{line}\t{declaration}\t{phase}\n"
            )


def write_phase_totals(
    path: pathlib.Path, decls: list[DeclarationTiming], per_file: bool
) -> None:
    totals: dict[tuple, list[float]] = collections.defaultdict(lambda: [0.0, 0])
    for decl in decls:
        for phase, milliseconds in decl.phase_ms.items():
            key = (decl.file_path, phase) if per_file else (phase,)
            totals[key][0] += milliseconds
            totals[key][1] += decl.phase_count[phase]
    ordered = sorted(totals.items(), key=lambda item: item[1][0], reverse=True)
    with path.open("w", encoding="utf-8") as output:
        header = "total_ms\tcount\tfile\tphase\n" if per_file else "total_ms\tcount\tphase\n"
        output.write(header)
        for key, (milliseconds, count) in ordered:
            output.write(f"{milliseconds:.1f}\t{int(count)}\t" + "\t".join(key) + "\n")


def write_file_times(path: pathlib.Path, results: list[FileResult]) -> None:
    # Columns: total wall, kernel-recheck (= wall - elab), elab-self.  The
    # trace only attributes ELAB-self time per decl; the kernel `addDecl`
    # re-typecheck of the produced term is NOT in any trace node, so it shows
    # up only as (wall - elab).  Ranking by elab alone systematically
    # under-ranks kernel-recheck-dominated files (e.g. big `decide`/match
    # tables), so this table sorts by total wall.
    with path.open("w", encoding="utf-8") as output:
        output.write("wall_s\trecheck_s\telab_s\treturn_code\tfile\n")
        for result in sorted(results, key=lambda item: item.wall_seconds, reverse=True):
            elab_s = sum(decl.total_ms for decl in result.declarations) / 1000.0
            recheck_s = max(0.0, result.wall_seconds - elab_s)
            output.write(
                f"{result.wall_seconds:.3f}\t{recheck_s:.3f}\t{elab_s:.3f}\t"
                f"{result.return_code}\t{result.file_path}\n"
            )


def write_failures(path: pathlib.Path, results: list[FileResult]) -> None:
    with path.open("w", encoding="utf-8") as output:
        for result in results:
            if result.return_code != 0:
                output.write(f"## {result.file_path} exit={result.return_code}\n")
                output.write(result.error_tail + "\n\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=pathlib.Path, default=ROOT_DEFAULT)
    parser.add_argument("--output", type=pathlib.Path, default=OUTPUT_DEFAULT)
    parser.add_argument("--threshold-ms", type=int, default=50)
    parser.add_argument("--workers", type=int, default=12)
    parser.add_argument(
        "--timeout-seconds", type=int, default=0,
        help="Per-file ceiling; 0 (default) means no timeout.",
    )
    parser.add_argument("--lean-jobs", type=int, default=1)
    parser.add_argument("--top", type=int, default=60)
    parser.add_argument("--include-audit", action="store_true")
    parser.add_argument("--max-files", type=int, default=0)
    parser.add_argument("files", nargs="*")
    args = parser.parse_args()

    root = args.root.resolve()
    output_dir = args.output.resolve()
    logs_dir = output_dir / "logs"
    logs_dir.mkdir(parents=True, exist_ok=True)

    lean_binary, lean_env = resolve_lean_env(root)

    if args.files:
        files = [pathlib.Path(name) for name in args.files]
    else:
        files = collect_files(root, args.include_audit)
    if args.max_files > 0:
        files = files[: args.max_files]

    timeout_label = "none" if args.timeout_seconds <= 0 else f"{args.timeout_seconds}s"
    print(
        f"profiling {len(files)} files threshold={args.threshold_ms}ms "
        f"workers={args.workers} lean-jobs={args.lean_jobs} timeout={timeout_label}\n"
        f"lean={lean_binary}\noutput={output_dir}",
        flush=True,
    )

    results: list[FileResult] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as executor:
        future_map = {
            executor.submit(
                profile_one, lean_binary, lean_env, root, file_path,
                args.threshold_ms, args.timeout_seconds, args.lean_jobs, logs_dir,
            ): file_path
            for file_path in files
        }
        for index, future in enumerate(
            concurrent.futures.as_completed(future_map), start=1
        ):
            results.append(future.result())
            if index % 10 == 0 or index == len(files):
                print(f"finished {index}/{len(files)}", flush=True)

    all_decls = [decl for result in results for decl in result.declarations]
    all_decls.sort(key=lambda decl: decl.total_ms, reverse=True)

    write_declarations_tsv(output_dir / "declarations.tsv", all_decls[: max(args.top, 1) * 20])
    write_decl_phase_tsv(output_dir / "decl_phase_breakdown.tsv", all_decls)
    write_phase_totals(output_dir / "phase_totals_global.tsv", all_decls, per_file=False)
    write_phase_totals(output_dir / "phase_totals_by_file.tsv", all_decls, per_file=True)
    write_file_times(output_dir / "file_times.tsv", results)
    write_failures(output_dir / "failures.txt", results)

    failed = [result for result in results if result.return_code != 0]
    print(f"\nwrote {output_dir}")
    print(f"files={len(results)} failed={len(failed)} declarations={len(all_decls)}")
    files_by_wall = sorted(results, key=lambda item: item.wall_seconds, reverse=True)
    print(
        f"\ntop {min(args.top, len(results))} files by wall time "
        f"(total | kernel-recheck | elab), seconds:"
    )
    print(f"  {'total':>8} {'recheck':>8} {'elab':>8}  file")
    for result in files_by_wall[: args.top]:
        elab_s = sum(decl.total_ms for decl in result.declarations) / 1000.0
        recheck_s = max(0.0, result.wall_seconds - elab_s)
        print(
            f"  {result.wall_seconds:8.1f} {recheck_s:8.1f} {elab_s:8.1f}  "
            f"{result.file_path}"
        )
    print(f"\ntop {min(args.top, len(all_decls))} declarations by elaboration time:")
    for decl in all_decls[: args.top]:
        phase, phase_ms = decl.dominant_phase()
        share = f"{phase} {phase_ms / decl.total_ms * 100:.0f}%" if decl.total_ms else phase
        print(
            f"{decl.total_ms:9.1f}ms  {decl.file_path}:{decl.source_line}  "
            f"{final_segment(decl.declaration)}  [{share}]"
        )
    if failed:
        print(f"\nfailed/timed-out files (see failures.txt):")
        for result in failed:
            print(f"  exit={result.return_code}  {result.file_path}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
