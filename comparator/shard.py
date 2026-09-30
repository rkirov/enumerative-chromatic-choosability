#!/usr/bin/env python3
"""Write comparator/config.<shard>.json: config.json restricted to one shard of its claims.

The comparator exports and kernel-replays the closure of `theorem_names` only, and consults
`definition_names` only for constants that closure reaches, so running it once per shard checks
exactly what one run over config.json checks. Shards run as parallel CI jobs; the two heavy ones
isolate the two kernel-decided certificates, whose replay dominates the running time:

* grid3-three: the k = 3 height-three grid theorem (22,157 records in Grid3/Three/Cert/Data/);
* k2n: the K_{2,n} results at list sizes 3, 4, 5 (the AM-GM certificates in TwoDegenerate/K2n/);
* rest: every other claim, including any claim added to config.json later.

config.json stays the single source of truth; `rest` is its complement, so the union of the
shards is always all of config.json.

Usage: python3 comparator/shard.py SHARD   (run from the repository root or from comparator/)
"""
import json
import os
import sys

SHARDS = {
    "grid3-three": [
        "ListColoring.ecc_boxProd_pathG_two_of_three",
    ],
    "k2n": [
        "SimpleGraph.TwoDegenerate.K2_26.not_eccAt_four",
        "SimpleGraph.TwoDegenerate.K2_25.eccAt_four",
        "SimpleGraph.TwoDegenerate.completeBipartite_two_eccAt_three_iff",
        "SimpleGraph.TwoDegenerate.completeBipartite_two_eccAt_four_iff",
        "SimpleGraph.TwoDegenerate.completeBipartite_two_eccAt_five_iff",
    ],
}
ALL_SHARDS = list(SHARDS) + ["rest"]


def main() -> None:
    if len(sys.argv) != 2 or sys.argv[1] not in ALL_SHARDS:
        sys.exit(f"usage: shard.py {{{','.join(ALL_SHARDS)}}}")
    shard = sys.argv[1]
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "config.json")) as f:
        config = json.load(f)
    names = config["theorem_names"]
    for s, members in SHARDS.items():
        missing = [n for n in members if n not in names]
        if missing:
            sys.exit(f"shard {s}: not claimed in config.json: {missing}")
    if shard == "rest":
        taken = {n for members in SHARDS.values() for n in members}
        selected = [n for n in names if n not in taken]
    else:
        selected = [n for n in names if n in SHARDS[shard]]
    config["theorem_names"] = selected
    out = os.path.join(here, f"config.{shard}.json")
    with open(out, "w") as f:
        json.dump(config, f, indent=2)
        f.write("\n")
    print(f"{out}: {len(selected)} of {len(names)} claims")


if __name__ == "__main__":
    main()
