#!/usr/bin/env python3
"""Build the Lean development and audit its axioms.

Run from this directory after `lake exe cache get`. The script
1. scans the sources for forbidden tokens,
2. runs `lake build` (warnings are errors, see lakefile.toml),
3. runs `AxiomAudit.lean` and checks that every listed theorem depends only on
   `propext`, `Classical.choice`, and `Quot.sound`.
It writes the results to lean-verification.json.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [r"\bsorry\b", r"\badmit\b", r"^\s*axiom\b", r"\bnative_decide\b",
             r"\bimplemented_by\b", r"^\s*unsafe\b", r"@\[extern"]


def scan() -> list[str]:
    hits = []
    for path in sorted((ROOT / "GaussianSGD").rglob("*.lean")) + [ROOT / "GaussianSGD.lean"]:
        text = path.read_text()
        text = re.sub(r"/-.*?-/", "", text, flags=re.S)
        for lineno, line in enumerate(text.splitlines(), 1):
            code = line.split("--", 1)[0]
            for pattern in FORBIDDEN:
                if re.search(pattern, code):
                    hits.append(f"{path.relative_to(ROOT)}:{lineno}: {line.strip()}")
    return hits


def run(cmd: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)


def audit(output: str) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    pattern = re.compile(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", re.S)
    for name, axioms in pattern.findall(output):
        result[name] = sorted(a.strip() for a in axioms.split(",") if a.strip())
    return result


def main() -> int:
    hits = scan()
    build = run(["lake", "build"])
    audit_run = run(["lake", "env", "lean", "AxiomAudit.lean"])
    axioms = audit(audit_run.stdout)
    listed = len(re.findall(r"^#print axioms", (ROOT / "AxiomAudit.lean").read_text(), re.M))
    bad = {k: v for k, v in axioms.items() if not set(v) <= ALLOWED}
    ok = (not hits and build.returncode == 0 and audit_run.returncode == 0
          and len(axioms) == listed and not bad)
    report = {
        "status": "passed" if ok else "failed",
        "forbidden_tokens": hits,
        "build_returncode": build.returncode,
        "build_tail": build.stdout.strip().splitlines()[-3:],
        "audited_theorems": len(axioms),
        "listed_theorems": listed,
        "axioms": axioms,
        "non_standard": bad,
    }
    (ROOT / "lean-verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "audited_theorems", "listed_theorems",
                                              "forbidden_tokens", "non_standard")}, indent=2))
    if build.returncode != 0:
        print(build.stdout[-4000:], file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
