"""The packed row reflections of Grid3/Three/Cert/Mirror.lean, in Python."""
from enum_replica import mult
def revPat(p): return (p % 2) * 4 + ((p // 2) % 2) * 2 + p // 4
def rp(p): return revPat(p + 1) - 1
def rtype(m): return sum(mult(m, rp(p)) * 4 ** p for p in range(7))
def mcount(M, p, q): return (M // 4 ** (7 * p + q)) % 4
def rM(M): return sum(mcount(M, rp(p), rp(q)) * 4 ** (7 * p + q) for p in range(7) for q in range(7))
def rsig(s): return ((rp(s // 2 % 7) * 7 + rp(s // 14 % 7)) * 7 + rp(s // 98 % 7)) * 2 + s % 2
