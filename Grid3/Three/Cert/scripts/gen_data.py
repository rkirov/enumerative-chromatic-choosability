#!/usr/bin/env python3
"""Emit Grid3/Three/Cert/Data/CNNNN.lean from generated record files.

Input: files of lines `fmt mL mR M ne blob` (the generator's `pack_record` output, one record per
valid maximal seam key, all 43,736 of them). Only one record per row-reflection orbit is kept:
the key `(mL, mR, M)` with `(mL, mR, M) <= (rtype mL, rtype mR, rM M)` as tuples, where `rtype`
and `rM` are the packed reflections of `Cert/Mirror.lean`. Records are ordered by type index and
key and written `PER` to a module; every record is a `decide +kernel` theorem.

    gen_data.py chunk_000.txt chunk_001.txt ...
"""
import re, sys
from pathlib import Path
sys.set_int_max_str_digits(0)
sys.path.insert(0, str(Path(__file__).resolve().parent))
from enum_replica import mult
from mirror import rtype, rM

ROOT = Path(__file__).resolve().parents[4]
DATA = ROOT / "Grid3/Three/Cert/Data"
PER = 40

checker = (ROOT / "Grid3/Three/Cert/Checker.lean").read_text()
TYPETABLE = int(re.search(r"def TYPETABLE : Nat := (\d+)", checker).group(1))
def typeIndex(m): return (TYPETABLE // 100 ** m) % 100

recs = {}
for f in sys.argv[1:]:
    for line in open(f):
        fmt, mL, mR, M, ne, blob = (int(x) for x in line.split())
        assert (mL, mR, M) not in recs
        recs[(mL, mR, M)] = (fmt, ne, blob)
assert len(recs) == 43736, len(recs)
canon = sorted((k for k in recs if k <= (rtype(k[0]), rtype(k[1]), rM(k[2]))),
               key=lambda k: (typeIndex(k[0]), typeIndex(k[1]), k[2]))
for k in recs:
    r = (rtype(k[0]), rtype(k[1]), rM(k[2]))
    assert r in recs, ("orbit not closed", k)
    assert (k in canon) or (r in canon)
print(f"records {len(recs)}, canonical {len(canon)}, self-symmetric {sum(1 for k in canon if k == (rtype(k[0]), rtype(k[1]), rM(k[2])))}")

DATA.mkdir(exist_ok=True)
for old in DATA.glob("C*.lean"): old.unlink()
mods = 0
for start in range(0, len(canon), PER):
    block = canon[start:start + PER]
    n = start // PER
    name = f"c{n:04d}"
    lines = ["import Grid3.Three.Cert.Checker", "", "set_option maxHeartbeats 0",
             "set_option maxRecDepth 100000", "namespace Grid3.Three.Cert", ""]
    for i, k in enumerate(block):
        fmt, ne, blob = recs[k]
        lines.append(f"def {name}_b{i} : Nat := {blob}")
    lines.append("")
    for i, k in enumerate(block):
        fmt, ne, blob = recs[k]
        lines.append(f"theorem {name}_ok{i} : checkRecord {fmt} {k[0]} {k[1]} {k[2]} {ne} {name}_b{i} = true := by decide +kernel")
    lines += ["", "end Grid3.Three.Cert", ""]
    (DATA / f"C{n:04d}.lean").write_text("\n".join(lines))
    mods += 1
print(f"wrote {mods} modules of up to {PER} records to {DATA}")
