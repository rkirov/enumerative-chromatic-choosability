import Mathlib

set_option maxRecDepth 4000

/-!
# Scaling test: flat-string certificate (codex route D).
`include_str` embeds the certificate as ONE flat string (O(1) elaboration — no per-entry syntax
nodes), a computable parser decodes it, and `native_decide` runs the integer checker over 300 REAL
seams. This is the encoding that scales to 43,736 where the Array literal blew `maxRecDepth`.
-/

namespace Grid3.Three.StringCert

abbrev Entry := ℕ × ℕ × ℕ × ℕ
def Dc : ℕ := 108000
def Ec : ℕ := 1000000
def SC : ℕ := 1000

def rowOK (cA : Array ℕ) (nr : ℕ) (sup : Array Entry) : Bool :=
  (List.range nr).all (fun s =>
    (sup.foldl (fun acc e => if e.1 = s then acc + e.2.2.1 else acc) 0) == cA[s]! * SC)
def entryOK (cA : Array ℕ) (sup : Array Entry) : Bool :=
  sup.all (fun e => e.2.2.2 ^ 4 * (Dc * cA[e.1]!) ≥ e.2.2.1 * 108 * (Ec ^ 4))
def boundOK (sup : Array Entry) : Bool :=
  let NR := sup.foldl (fun acc e => acc + e.2.2.1 * e.2.2.2) 0
  let Dr := Dc * Ec
  (5 * NR ^ 4 < 2 * Dr ^ 4) && (17 * NR ^ 8 < (2 * Dr ^ 4 - 5 * NR ^ 4) ^ 2)
def checkSeam (cA : Array ℕ) (nr : ℕ) (sup : Array Entry) : Bool :=
  rowOK cA nr sup && entryOK cA sup && boundOK sup

/-- Parse a flat token stream `nr ncA cA... nent (s t v k)...` into a seam. -/
def parseSeam (toks : Array ℕ) : Array ℕ × ℕ × Array Entry := Id.run do
  let nr := toks[0]!
  let ncA := toks[1]!
  let cA := (Array.range ncA).map (fun i => toks[2 + i]!)
  let base := 2 + ncA
  let nent := toks[base]!
  let mut sup : Array Entry := Array.mkEmpty nent
  for i in [0:nent] do
    let o := base + 1 + 4 * i
    sup := sup.push (toks[o]!, toks[o+1]!, toks[o+2]!, toks[o+3]!)
  return (cA, nr, sup)

def parseNats (s : String) : Array ℕ :=
  (s.splitOn " ").foldl (fun acc w => match w.toNat? with | some n => acc.push n | none => acc) #[]

def checkBlob (blob : String) : Bool :=
  (blob.splitOn " ; ").all (fun rec =>
    let (cA, nr, sup) := parseSeam (parseNats rec)
    checkSeam cA nr sup)

/-- The certificate blob (300 real seams) embedded as one flat string. -/
def blob : String := include_str "blob300.txt"

/-- **All 300 real seams pass the exact checker, decoded from a flat string** (compiled). -/
theorem blob_ok : checkBlob blob = true := by native_decide

end Grid3.Three.StringCert
