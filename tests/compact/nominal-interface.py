from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


def main():
    if len(sys.argv) > 2:
        raise SystemExit("usage: python3 nominal-interface.py [compactc]")
    compiler = sys.argv[1] if len(sys.argv) == 2 else "compactc"
    version = subprocess.check_output([compiler, "--version"], text=True).strip()
    if not version.startswith("0.36.1 (7fa3a117c "):
        raise SystemExit(f"expected pinned Compact 0.36.1, got {version}")

    fixture = Path(__file__).resolve().with_name("NominalInterface.compact")
    source = fixture.read_text()
    experiments = fixture.parents[2] / "build/experiments"
    experiments.mkdir(parents=True, exist_ok=True)
    mutations = [
        (
            "export circuit update(amount: Amount): Amount {\n  saved = disclose(amount);\n  return saved;\n}",
            "export circuit update(amount: Count): Amount {\n  saved = disclose(amount as Amount);\n  return saved;\n}",
            "implementation arguments must retain their nominal identity",
        ),
        (
            "export circuit update(amount: Amount): Amount {\n  saved = disclose(amount);\n  return saved;\n}",
            "export circuit update(amount: Amount): Count {\n  saved = disclose(amount);\n  return saved as Count;\n}",
            "implementation results must retain their nominal identity",
        ),
        (
            "service.update(disclose(amount))",
            "service.update(disclose(amount as Count))",
            "call arguments must match the declared nominal identity",
        ),
        (
            "export circuit forward(amount: Amount): Amount {",
            "export circuit forward(amount: Amount): Count {",
            "call results must match the declared nominal identity",
        ),
    ]

    with TemporaryDirectory(prefix="nominal-interface-", dir=experiments) as scratch_name:
        scratch = Path(scratch_name)
        positive = scratch / "positive"
        subprocess.run([compiler, "--skip-zk", fixture, positive], check=True)
        entries = {path.name for path in (positive / "zkir").glob("*.zkir")}
        if entries != {"update.zkir", "forward.zkir"}:
            raise SystemExit(f"expected update and forward entries, got {sorted(entries)}")

        for index, (original, replacement, description) in enumerate(mutations, start=1):
            if source.count(original) != 1:
                raise SystemExit(f"mutation {index} does not select one source fragment")
            candidate = scratch / f"negative-{index}.compact"
            candidate.write_text(source.replace(original, replacement))
            result = subprocess.run(
                [compiler, "--skip-zk", candidate, scratch / f"negative-output-{index}"],
                capture_output=True,
                text=True,
            )
            if result.returncode == 0:
                raise SystemExit(f"Compact accepted invalid case: {description}")
            diagnostic = result.stdout + result.stderr
            if not all(word in diagnostic for word in ("type", "Amount", "Count")):
                raise SystemExit(f"unexpected Compact error for {description}: {diagnostic}")

    print(f"Compact {version} accepted nominal interface calls and rejected {len(mutations)} alias mismatches")


if __name__ == "__main__":
    main()
