"""
Run the complete call-role classification pipeline for a Java source tree.

Input: a Java source directory and the project's root package/namespace.
Output: calls.csv, calls_context.csv and classified_calls.json.
"""

from __future__ import annotations

import argparse
import csv
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source-path",
        required=True,
        type=Path,
        help="Java source directory or project/module directory to analyze",
    )
    parser.add_argument(
        "--project-root",
        help="root Java package used to identify project-internal types, e.g. com.fsck.k9",
    )
    parser.add_argument(
        "--project-name",
        help="name stored in classified_calls.json metadata; defaults to source directory name",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=Path("classified_calls.json"),
        help="classified call-site JSON output path",
    )
    parser.add_argument(
        "--calls-csv",
        type=Path,
        default=Path("calls.csv"),
        help="feature CSV produced by the extractor",
    )
    parser.add_argument(
        "--context-csv",
        type=Path,
        default=Path("calls_context.csv"),
        help="context CSV produced by the extractor",
    )
    parser.add_argument(
        "--skip-extraction",
        action="store_true",
        help="reuse existing calls.csv/calls_context.csv and only regenerate classified JSON",
    )
    return parser.parse_args()


def call_extractor_dir() -> Path:
    return Path(__file__).resolve().parents[1]


def count_csv_rows(path: Path) -> int:
    with path.open(newline="", encoding="utf-8") as f:
        return sum(1 for _ in csv.DictReader(f))


def infer_project_root(source_path: Path) -> str:
    package_pattern = re.compile(r"^\s*package\s+([A-Za-z_][A-Za-z0-9_.]*)\s*;")
    packages = []

    for java_file in source_path.rglob("*.java"):
        try:
            for line in java_file.read_text(encoding="utf-8", errors="ignore").splitlines()[:80]:
                match = package_pattern.match(line)
                if match:
                    packages.append(match.group(1))
                    break
        except OSError:
            continue

    if not packages:
        raise SystemExit(
            "could not infer --project-root because no Java package declarations were found"
        )

    total = len(packages)
    prefix_counts: Counter[str] = Counter()
    for package_name in packages:
        parts = package_name.split(".")
        for length in range(2, len(parts) + 1):
            prefix_counts[".".join(parts[:length])] += 1

    candidates = [
        (prefix, count)
        for prefix, count in prefix_counts.items()
        if count / total >= 0.60
    ]
    if candidates:
        candidates.sort(key=lambda item: (item[1] / total, len(item[0].split(".")), item[1]), reverse=True)
        return candidates[0][0]

    return prefix_counts.most_common(1)[0][0]


def run(cmd: list[str], cwd: Path) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def main() -> None:
    args = parse_args()
    extractor_dir = call_extractor_dir()

    source_path = args.source_path.expanduser().resolve()
    if not source_path.exists():
        raise SystemExit(f"source path does not exist: {source_path}")

    project_root = args.project_root or infer_project_root(source_path)
    project_name = args.project_name or source_path.name
    calls_csv = args.calls_csv if args.calls_csv.is_absolute() else extractor_dir / args.calls_csv
    context_csv = args.context_csv if args.context_csv.is_absolute() else extractor_dir / args.context_csv
    output_json = args.output_json if args.output_json.is_absolute() else extractor_dir / args.output_json

    if not args.skip_extraction:
        if args.project_root:
            print(f"Using project root package: {project_root}", flush=True)
        else:
            print(f"Inferred project root package: {project_root}", flush=True)
        run([
            "mvn",
            "-q",
            "exec:java",
            "-Dexec.mainClass=analysis.CallExtractorRevised",
            f"-DcallExtractor.projectRoot={project_root}",
            f"-DcallExtractor.inputResource={source_path}",
        ], cwd=extractor_dir)

    for path in (calls_csv, context_csv):
        if not path.exists():
            raise SystemExit(f"expected extractor output is missing: {path}")

    call_rows = count_csv_rows(calls_csv)
    context_rows = count_csv_rows(context_csv)
    if call_rows != context_rows:
        raise SystemExit(
            f"row count mismatch: {calls_csv.name} has {call_rows} rows, "
            f"{context_csv.name} has {context_rows} rows"
        )
    if call_rows == 0:
        raise SystemExit("extractor produced 0 call sites; check --source-path and --project-root")

    classifier_script = Path(__file__).resolve().parent / "classify_calls_with_jrip.py"
    run([
        sys.executable,
        str(classifier_script),
        "--calls-csv",
        str(calls_csv),
        "--context-csv",
        str(context_csv),
        "--output-json",
        str(output_json),
        "--project-name",
        project_name,
    ], cwd=extractor_dir)

    print()
    print(f"Pipeline completed for {project_name}")
    print(f"Call sites classified: {call_rows}")
    print(f"Feature CSV: {calls_csv}")
    print(f"Context CSV: {context_csv}")
    print(f"Classified JSON: {output_json}")


if __name__ == "__main__":
    main()
