"""Replay the published evidence using the pinned pequalnp-proofs Lean checkout."""
import argparse
import hashlib
import json
import os
import subprocess
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
REVISION = "81b4fafd7a831eef210ad183d6864e5f167ec1d9"
EDGES = ((0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
         (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
         (6, 7), (6, 10), (7, 9), (8, 9))


def check_truth_tables():
    # Use a seven-center cover calculated directly from the public graph.
    cover = next(candidate for candidate in combinations(range(11), 7)
                 if all(a in candidate or b in candidate for a, b in EDGES))
    stars = {c: [] for c in cover}
    for a, b in EDGES:
        center, neighbor = (a, b) if a in stars else (b, a)
        stars[center].append(neighbor)
    if any(not neighbors for neighbors in stars.values()):
        raise ValueError("a star is empty")
    leaf_count = sum(1 + len(neighbors) for neighbors in stars.values())
    witness = json.loads((HERE / "g11" / "charge-23.json").read_text())
    gates, pairs = witness["gates"], witness["pairs"]
    if leaf_count != 23 or len(gates) + 2 * len(pairs) != 23:
        raise ValueError("unexpected formula or circuit size")
    for mask in range(1 << 11):
        raw = [bool(mask & (1 << v)) for v in range(11)]
        expected = any(raw[a] and raw[b] for a, b in EDGES)
        formula = any(raw[c] and any(raw[v] for v in neighbors)
                      for c, neighbors in stars.items())
        wires = raw.copy()
        for op, a, b in gates:
            if not (0 <= a < len(wires) and 0 <= b < len(wires)) or op not in ("and", "or"):
                raise ValueError("invalid gate")
            wires.append((wires[a] and wires[b]) if op == "and" else (wires[a] or wires[b]))
        circuit = any(wires[a] and wires[b] for a, b in pairs)
        if formula != expected or circuit != expected:
            raise ValueError(f"wrong output on input {mask}")
    print("G11: both constructions agree on all 2,048 assignments", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="local pequalnp-proofs checkout")
    args = parser.parse_args()
    repo = args.checkout.resolve()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    if revision != REVISION:
        print(f"Running with {revision}. The recorded verification used {REVISION}.", flush=True)
    for line in (HERE / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        if hashlib.sha256((HERE / name).read_bytes()).hexdigest() != digest:
            raise ValueError(f"checksum mismatch for {name}")
    check_truth_tables()
    with TemporaryDirectory() as tmp:
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join(filter(None, [tmp, env.get("LEAN_PATH")]))
        def lean(*args):
            subprocess.run(["lake", "env", "lean", *args], cwd=repo / "lean", env=env, check=True)
        def compile_module(group, module):
            src = HERE / group
            lean(f"--root={src}", "-o", Path(tmp) / (module + ".olean"), src / (module + ".lean"))
        compile_module("fano", "L_meta_11463")
        for name in ("FormulaRectPartition", "RectangleCNFBridge", "SingleSharedFormula", "CoverAt23"):
            compile_module("g11", name)
        evidence = HERE / "certificates"
        lean("--run", HERE / "g11/ReplayRectangleCNF.lean", evidence / "g11.cnf",
             evidence / "g11.lrat", evidence / "annotations.json")
        for name in ("GateSize", "RepairEdges", "Involution", "Graph", "Circuit", "MinimumCover",
                     "Normalize", "AmplifyGraph", "AmplifyCircuit", "AmplifiedNormalization",
                     "R_meta_3491_627"):
            compile_module("incidence", name)
    print("Verification complete.", flush=True)


if __name__ == "__main__":
    main()
