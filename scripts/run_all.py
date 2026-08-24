#!/usr/bin/env python3
"""Run every executable experiment and collect reproducibility logs."""

from __future__ import annotations

import argparse
import csv
import os
import platform
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


PROJECTS = (
    "GFS-4F",
    "NEW_II",
    "NEW_III",
    "NEW_IV",
    "NEW_IV_ENC",
    "Type-1 GFS",
)


def executable_scripts(root: Path) -> list[tuple[str, Path]]:
    scripts: list[tuple[str, Path]] = []
    marker = re.compile(r"if\s+__name__\s*==\s*['\"]__main__['\"]")
    for project in PROJECTS:
        project_dir = root / project
        for path in sorted(project_dir.glob("*.py")):
            source = path.read_text(encoding="utf-8", errors="replace")
            if marker.search(source):
                scripts.append((project, path))
    return scripts


def package_version() -> str:
    try:
        import cvc5  # type: ignore

        return getattr(cvc5, "__version__", "installed (version unavailable)")
    except Exception as exc:  # pragma: no cover - diagnostic path
        return f"unavailable: {exc}"


def write_markdown_summary(
    path: Path,
    rows: list[dict[str, str]],
    started_at: str,
    timeout_seconds: int,
) -> None:
    passed = sum(row["status"] == "PASS" for row in rows)
    failed = sum(row["status"] == "FAIL" for row in rows)
    timed_out = sum(row["status"] == "TIMEOUT" for row in rows)
    lines = [
        "# Reproduction summary",
        "",
        f"- Started (UTC): `{started_at}`",
        f"- Platform: `{platform.platform()}`",
        f"- Python: `{platform.python_version()}`",
        f"- cvc5: `{package_version()}`",
        f"- Per-script timeout: `{timeout_seconds} s`",
        f"- Totals: `{passed} passed`, `{failed} failed`, `{timed_out} timed out`",
        "",
        "| Project | Script | Status | Exit code | Duration (s) | Log |",
        "|---|---|---:|---:|---:|---|",
    ]
    for row in rows:
        lines.append(
            "| {project} | `{script}` | {status} | {exit_code} | {duration_seconds} | "
            "[{log}]({log}) |".format(**row)
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--timeout",
        type=int,
        default=180,
        help="maximum seconds allowed for each script (default: 180)",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    results_dir = root / "results"
    raw_dir = results_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)
    started_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["PYTHONUNBUFFERED"] = "1"
    rows: list[dict[str, str]] = []

    scripts = executable_scripts(root)
    print(f"Discovered {len(scripts)} executable scripts.", flush=True)
    for index, (project, script) in enumerate(scripts, start=1):
        project_log_dir = raw_dir / project.replace(" ", "_")
        project_log_dir.mkdir(parents=True, exist_ok=True)
        log_path = project_log_dir / f"{script.stem}.log"
        print(f"[{index}/{len(scripts)}] {project}/{script.name}", flush=True)
        started = datetime.now(timezone.utc)
        exit_code = ""
        status = "FAIL"
        try:
            proc = subprocess.run(
                [sys.executable, script.name],
                cwd=script.parent,
                env=env,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=args.timeout,
                check=False,
            )
            status = "PASS" if proc.returncode == 0 else "FAIL"
            exit_code = str(proc.returncode)
            stdout = proc.stdout
            stderr = proc.stderr
        except subprocess.TimeoutExpired as exc:
            status = "TIMEOUT"
            exit_code = "timeout"
            stdout = exc.stdout or ""
            stderr = exc.stderr or ""
            if isinstance(stdout, bytes):
                stdout = stdout.decode("utf-8", errors="replace")
            if isinstance(stderr, bytes):
                stderr = stderr.decode("utf-8", errors="replace")
        ended = datetime.now(timezone.utc)
        duration = (ended - started).total_seconds()
        stdout = stdout.rstrip("\r\n") or "(no stdout)"
        stderr = stderr.rstrip("\r\n") or "(no stderr)"
        log_text = (
            f"project: {project}\n"
            f"script: {script.name}\n"
            f"command: {sys.executable} {script.name}\n"
            f"started_utc: {started.isoformat(timespec='seconds')}\n"
            f"duration_seconds: {duration:.6f}\n"
            f"status: {status}\n"
            f"exit_code: {exit_code}\n\n"
            "===== STDOUT =====\n"
            f"{stdout}\n"
            "===== STDERR =====\n"
            f"{stderr}\n"
        )
        log_path.write_text(log_text, encoding="utf-8")
        relative_log = log_path.relative_to(results_dir).as_posix()
        rows.append(
            {
                "project": project,
                "script": script.name,
                "status": status,
                "exit_code": exit_code,
                "duration_seconds": f"{duration:.6f}",
                "log": relative_log,
            }
        )

    results_dir.mkdir(parents=True, exist_ok=True)
    with (results_dir / "summary.csv").open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=(
                "project",
                "script",
                "status",
                "exit_code",
                "duration_seconds",
                "log",
            ),
        )
        writer.writeheader()
        writer.writerows(rows)
    write_markdown_summary(results_dir / "SUMMARY.md", rows, started_at, args.timeout)
    failures = sum(row["status"] != "PASS" for row in rows)
    print(f"Completed: {len(rows) - failures} passed, {failures} not passed.", flush=True)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
