#!/usr/bin/env python3
"""Build the root library and reject unexpected public-audit axioms."""
import argparse
from pathlib import Path
import re
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path("/tmp/ramanujan-weil-verification"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    with (output / "build.log").open("w") as log:
        result = subprocess.run(
            ["lake", "--log-level=error", "build", "RamanujanWeil", "RamanujanWeil.Axioms"],
            cwd=root, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f"Build failed; see {output / 'build.log'}")
    print(f"Root build passed; log: {output / 'build.log'}", flush=True)
    source = root / "scripts/audit/public.lean"
    expected = len(re.findall(r"^#print axioms ", source.read_text(), re.M))
    result = subprocess.run(["lake", "env", "lean", str(source)], cwd=root,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    path = output / "public.axioms.txt"
    path.write_text(result.stdout)
    reports = re.findall(r"depends on axioms: \[([^]]*)\]", result.stdout)
    reports += [""] * len(re.findall(r"does not depend on any axioms", result.stdout))
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    unexpected = {a.strip() for report in reports for a in report.split(",") if a.strip()} - allowed
    if result.returncode or not reports or len(reports) != expected or unexpected:
        raise SystemExit(f"Audit failed ({len(reports)}/{expected} declarations, "
                         f"unexpected axioms: {sorted(unexpected)}); see {path}")
    print(f"Public audit: {len(reports)} declarations, standard axioms only; {path}", flush=True)


if __name__ == "__main__":
    main()
