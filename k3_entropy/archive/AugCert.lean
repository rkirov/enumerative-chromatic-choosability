import Mathlib

set_option maxRecDepth 4000

/-!
# Augmented certificate checker (rowOK + colOK + entryOK + boundOK).

Format per seam: `nr nc cA(nr) cB(nc) nent (s t v k)*`.  Adds `colOK` (right marginal = cB) to the
StringCert checker, so the certificate now discharges `hstep` as well.
-/
namespace Grid3.Three.AugCert

abbrev Entry := ℕ × ℕ × ℕ × ℕ
def Dc : ℕ := 108000
def Ec : ℕ := 1000000
def SC : ℕ := 1000

structure Seam where
  nr : ℕ
  nc : ℕ
  cA : Array ℕ
  cB : Array ℕ
  sup : Array Entry

def rowOK (d : Seam) : Bool :=
  (List.range d.nr).all (fun s =>
    (d.sup.foldl (fun a e => if e.1 = s then a + e.2.2.1 else a) 0) == d.cA[s]! * SC)
def colOK (d : Seam) : Bool :=
  (List.range d.nc).all (fun t =>
    (d.sup.foldl (fun a e => if e.2.1 = t then a + e.2.2.1 else a) 0) == d.cB[t]! * SC)
def entryOK (d : Seam) : Bool :=
  d.sup.all (fun e => e.2.2.2 ^ 4 * (Dc * d.cA[e.1]!) ≥ e.2.2.1 * 108 * (Ec ^ 4))
def boundOK (d : Seam) : Bool :=
  let NR := d.sup.foldl (fun a e => a + e.2.2.1 * e.2.2.2) 0
  let Dr := Dc * Ec
  (5 * NR ^ 4 < 2 * Dr ^ 4) && (17 * NR ^ 8 < (2 * Dr ^ 4 - 5 * NR ^ 4) ^ 2)
def checkSeam (d : Seam) : Bool := rowOK d && colOK d && entryOK d && boundOK d

def parseSeam (toks : Array ℕ) : Seam := Id.run do
  let nr := toks[0]!
  let nc := toks[1]!
  let cA := (Array.range nr).map (fun i => toks[2 + i]!)
  let cB := (Array.range nc).map (fun i => toks[2 + nr + i]!)
  let base := 2 + nr + nc
  let nent := toks[base]!
  let mut sup : Array Entry := Array.mkEmpty nent
  for i in [0:nent] do
    let o := base + 1 + 4 * i
    sup := sup.push (toks[o]!, toks[o+1]!, toks[o+2]!, toks[o+3]!)
  return { nr, nc, cA, cB, sup }

def parseNats (s : String) : Array ℕ :=
  (s.splitOn " ").foldl (fun acc w => match w.toNat? with | some n => acc.push n | none => acc) #[]

def checkBlob (blob : String) : Bool :=
  (blob.splitOn " ; ").all (fun rec => checkSeam (parseSeam (parseNats rec)))

def blob : String := include_str "aug_test.txt"

theorem aug_blob_ok : checkBlob blob = true := by native_decide

end Grid3.Three.AugCert
