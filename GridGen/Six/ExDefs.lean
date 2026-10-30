/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.ExAcc
import GridGen.Six.Pins

/-!
# Height six at `k = 6`: the exact-certificate checker

The three single-mismatch classes `μ = (0,0,1,0,0)`, `(0,0,0,1,0)`, `(0,0,0,0,1)` of
`ai_research_notes/H6_K6_REVIEW_2026-10-29.md` are closed by exact certificates over column
types, as in `GridGen/Five/K5/ExactDefs.lean`. The shape `j ∈ {3, 4, 5}`: rows `r < j` carry a
`6`-list `U`, rows `r ≥ j` a `6`-list `V`, `|U ∩ V| = 5`; write `W = U ∩ V`, `U = W ∪ {a}`,
`V = W ∪ {b}`.

**Types.** A proper column `s` has a pattern `p = canon s` and a *kind* per row (`κ`): `0` if its
colour lies in `W`, `5` if it is `a` on a row of `U`, `6` if it is `b` on a row of `V`, `7` if it
is outside the row's list. Relabelling `W` onto `{0, …, 4}` (the colours of the `W` rows by the
rank of their pattern value, `lab`), `a ↦ 5` and `b ↦ 6`, the weighted successor count `GB` of
the column is that of the masks `em (bmJ j r) l_r` (`63 = {0..5}`, `95 = {0..4, 6}`, label `l_r`
erased), computed by `GridGen/Six/ExCount.lean`.

**The leaf test** (`leafX`): with the pins compiled for the pattern (`compileX`, `penC`) and
`e = D + K - pen`, the cone test `e · Ψ_d + D · Φ⁻_d ≤ D · Φ⁺_d` (`okc6`) for the five rays
(`d < 5`) and, on `Q`, for `Σ uⱼ qUⱼ` against `Σ cₒ qLₒ` (`d = 5`; sound since all counts are
nonnegative). `Φ±` are the six functionals of the orbit counts, read from one accumulation over
the set partitions (`accG`); `Ψ` and the compiled pins are per pattern data (`patS`).

**The enumeration** (`patK`): for one pattern and one kind of the first row, all kind vectors of
the other rows, with the admissibility `admK` and the bound on the common pattern values that
every actual column satisfies. Soundness: `GridGen/Six/ExShape.lean` (`seam_shape`).
-/

namespace GridGen.Six

open Finset

/-! ### Shapes and labels -/

/-- The mask of the list of row `r` in shape `j`. -/
def bmJ (j r : ℕ) : ℕ := bif Nat.blt r j then 63 else 95

/-- The kinds available on row `r` of shape `j`: common, the row's special colour, outside. -/
def spJ (j r : ℕ) : ℕ := bif Nat.blt r j then 5 else 6

/-- Erase label `l` from a mask. -/
def em (m l : ℕ) : ℕ := Nat.land m (Nat.sub 255 (Nat.pow 2 l))

/-- The pattern values of the common rows, as a mask. -/
def wbit (pr k : ℕ) : ℕ := bif Nat.beq k 0 then Nat.pow 2 pr else 0

def wmask (p : T6) (k0 k1 k2 k3 k4 k5 : ℕ) : ℕ :=
  Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (wbit (r1 p) k0) (wbit (r2 p) k1)) (wbit (r3 p) k2))
    (wbit (r4 p) k3)) (wbit (r5 p) k4)) (wbit (r6 p) k5)

/-- The rank of a pattern value among those of the common rows. -/
def rk (wm x : ℕ) : ℕ := popc (Nat.land wm (Nat.sub (Nat.pow 2 x) 1))

/-- The label of a row: the rank for a common row, else the kind. -/
def lab (wm pr k : ℕ) : ℕ := bif Nat.beq k 0 then rk wm pr else k

/-! ### Pins on types -/

/-- A peel of an exact pin: row `r` in an atom set `S` (bits `0` = `W`, `5` = `a`, `6` = `b`), or
rows `r` and `i` equal. -/
inductive XF
  | mem (r S : ℕ)
  | eq (r i : ℕ)

/-- An exact pin: a block of consecutive rows from `r0` with atom sets `bs`, peels, and the
multiplier. -/
structure XP where
  r0 : ℕ
  bs : List ℕ
  peels : List XF
  lam : ℕ

instance : Inhabited XP := ⟨⟨0, [], [], 0⟩⟩

/-- A label lies in an atom set. -/
def labIn (S x : ℕ) : Bool := Nat.blt x 7 && (bif Nat.blt x 5 then S.testBit 0 else S.testBit x)

/-! ### Well-formed pins and their bounds -/

/-- The number of colours of an atom set. -/
def asz (S : ℕ) : ℕ :=
  5 * (bif S.testBit 0 then 1 else 0) + (bif S.testBit 5 then 1 else 0) + (bif S.testBit 6 then 1 else 0)

/-- The peeled row of a peel, and the rows it reads. -/
def XF.row : XF → ℕ
  | mem r _ => r
  | eq r _ => r

def XF.reads : XF → ℕ → Bool
  | mem r _, i => decide (r = i)
  | eq r j, i => decide (r = i) || decide (j = i)

def XF.okb : XF → Bool
  | mem r _ => decide (r < 6)
  | eq r j => decide (r < 6 ∧ j < 6 ∧ j ≠ r)

/-- The block reads row `i`. -/
def blkReads (r0 : ℕ) (bs : List ℕ) (i : ℕ) : Bool := decide (r0 ≤ i ∧ i < r0 + bs.length)

/-- The peel order. -/
def xpeelOK (r0 : ℕ) (bs : List ℕ) : List XF → Bool
  | [] => true
  | f :: fs => !(blkReads r0 bs f.row) && fs.all (fun g => !(g.reads f.row)) && f.okb &&
      xpeelOK r0 bs fs

/-- A pin is well formed. -/
def XP.okb (q : XP) : Bool :=
  decide (q.bs.length ≤ 3 ∧ q.r0 + q.bs.length ≤ 6) && xpeelOK q.r0 q.bs q.peels

/-- The bound of a peel. -/
def XF.bnd : XF → ℚ
  | mem r S => min (qX r * asz S) 1
  | eq r _ => qX r

/-- The bound of a block. -/
def blkBnd (r0 : ℕ) : List ℕ → ℚ
  | [S] => βQ6 (asz S) 5 (fsd r0 * fsd (5 - r0))
  | [S, S'] => βQ6 (asz S * asz S') 20 (fsd r0 * fsd (4 - r0))
  | [S, S', S''] => βQ6 (asz S * asz S' * asz S'') 80 (fsd r0 * fsd (3 - r0))
  | _ => 1

/-- The bound of a pin. -/
def xbnd (q : XP) : ℚ := (q.peels.map XF.bnd).prod * blkBnd q.r0 q.bs

/-- **The scalar conditions of a certificate.** -/
def certOK (D K : ℕ) (P : List XP) : Bool :=
  Nat.blt 0 D && P.all XP.okb && decide ((P.map fun q => (q.lam : ℚ) * xbnd q).sum ≤ K)

/-! ### Primitive versions of the counting -/

/-- `pk 8` of `2^r` ones. -/
def ones8 : ℕ → ℕ
  | 0 => 1
  | 1 => 257
  | 2 => 16843009
  | 3 => 72340172838076673
  | 4 => 1334440654591915542993625911497130241
  | _ => 454086624460063511464984254936031011189294057512315937409637584344757371137

theorem ones8_eq : ∀ r < 6, ones8 r = pk 8 (List.replicate (2 ^ r) 1) := by decide +kernel

/-- One doubling step, primitive. -/
def dblF (T m r : ℕ) : ℕ :=
  Nat.add T (Nat.mul (Nat.pow 2 (Nat.mul 8 (Nat.pow 2 r))) (Nat.land T (Nat.mul m (ones8 r))))

theorem dblF_eq {r : ℕ} (hr : r < 6) (T m : ℕ) : dblF T m r = dblT T m r := by
  unfold dblF dblT; rw [ones8_eq r hr]

/-- Byte `i`. -/
def lane8 (x i : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 8 i)) 255

theorem lane8_eq (x i : ℕ) : lane8 x i = lane 8 x i := by
  unfold lane8 lane
  rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num]
  rw [show Nat.land (Nat.shiftRight x (Nat.mul 8 i)) (2 ^ 8 - 1)
      = (x >>> (8 * i)) &&& (2 ^ 8 - 1) from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

/-- The packed sizes from the packed intersections, in Horner form from byte `S`. -/
def horF (T : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | S, n + 1 => Nat.add (lane4 PT (lane8 T S)) (Nat.mul 16 (horF T (S + 1) n))

theorem horF_eq (T : ℕ) : ∀ n S, horF T S n = pkF 4 (fun i => lane 4 PT (lane 8 T (S + i))) n
  | 0, _ => rfl
  | n + 1, S => by
    rw [horF, pkF, horF_eq T n (S + 1), lane4_eq, lane8_eq]
    simp only [Nat.add_zero, show (2 : ℕ) ^ 4 = 16 by norm_num]
    congr 2
    exact pkF_congr fun i _ => by rw [show S + 1 + i = S + (i + 1) by ring]

/-- The packed intersections of six masks. -/
def tabF (m0 m1 m2 m3 m4 m5 : ℕ) (k : ℕ → Bool) : Bool :=
  xN (dblF 255 m0 0) fun t1 => xN (dblF t1 m1 1) fun t2 => xN (dblF t2 m2 2) fun t3 =>
  xN (dblF t3 m3 3) fun t4 => xN (dblF t4 m4 4) fun t5 => xN (dblF t5 m5 5) fun t6 => k t6

/-- A lane of `96` bits. -/
def lane96 (x i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight x (Nat.mul 96 i)) 79228162514264337593543950335

theorem lane96_eq (x i : ℕ) : lane96 x i = lane 96 x i := by
  unfold lane96 lane
  rw [show (79228162514264337593543950335 : ℕ) = 2 ^ 96 - 1 by norm_num]
  rw [show Nat.land (Nat.shiftRight x (Nat.mul 96 i)) (2 ^ 96 - 1)
      = (x >>> (96 * i)) &&& (2 ^ 96 - 1) from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

/-! ### Compiled pins -/

/-- The block conditions from row `r`. -/
def blkConds : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | r, S :: Ss => (r, S) :: blkConds (r + 1) Ss

/-- The membership conditions of the peels. -/
def memConds : List XF → List (ℕ × ℕ)
  | [] => []
  | XF.mem r S :: ps => (r, S) :: memConds ps
  | XF.eq _ _ :: ps => memConds ps

/-- The equalities of the peels hold on a pattern. -/
def eqsOK (p : T6) : List XF → Bool
  | [] => true
  | XF.eq r i :: ps => Nat.beq (rowAt r p) (rowAt i p) && eqsOK p ps
  | XF.mem _ _ :: ps => eqsOK p ps

/-- A pin compiled for a pattern: its row conditions and multiplier, if its equalities hold. -/
def compileOne (p : T6) (q : XP) : Option (List (ℕ × ℕ) × ℕ) :=
  bif eqsOK p q.peels then some (blkConds q.r0 q.bs ++ memConds q.peels, q.lam) else none

def compileX (p : T6) (P : List XP) : List (List (ℕ × ℕ) × ℕ) := P.filterMap (compileOne p)

/-- The penalty of a type from compiled pins. -/
def penC (cps : List (List (ℕ × ℕ) × ℕ)) (l : List ℕ) : ℕ :=
  cps.foldr (fun cp acc => Nat.add (bif cp.1.all (fun rs => labIn rs.2 (l.getD rs.1 7)) then cp.2
    else 0) acc) 0

/-- The values `Ψ` of a pattern, from the lists. -/
def psiL (p : T6) : List ℕ :=
  (FL.take 5).map (dotZ (VL.getD (orb p) [])) ++ [dotZ (VL.getD (orb p) []) qUL]

/-! ### The leaf and the enumeration -/

/-- The six cone tests of a type: `e · Ψ_d + D · Φ⁻_d ≤ D · Φ⁺_d`. -/
def okc6 (D e S : ℕ) (psi : List ℕ) : Bool :=
  Nat.ble (Nat.add (Nat.mul e (psi.getD 0 0)) (Nat.mul D (lane96 S 6))) (Nat.mul D (lane96 S 0)) &&
  Nat.ble (Nat.add (Nat.mul e (psi.getD 1 0)) (Nat.mul D (lane96 S 7))) (Nat.mul D (lane96 S 1)) &&
  Nat.ble (Nat.add (Nat.mul e (psi.getD 2 0)) (Nat.mul D (lane96 S 8))) (Nat.mul D (lane96 S 2)) &&
  Nat.ble (Nat.add (Nat.mul e (psi.getD 3 0)) (Nat.mul D (lane96 S 9))) (Nat.mul D (lane96 S 3)) &&
  Nat.ble (Nat.add (Nat.mul e (psi.getD 4 0)) (Nat.mul D (lane96 S 10))) (Nat.mul D (lane96 S 4)) &&
  Nat.ble (Nat.add (Nat.mul e (psi.getD 5 0)) (Nat.mul D (lane96 S 11))) (Nat.mul D (lane96 S 5))

/-- **The test of one column type** `(κ, p)` in shape `j`, with the pins compiled for `p`. -/
def leafX (D K j : ℕ) (cps : List (List (ℕ × ℕ) × ℕ)) (psi : List ℕ) (p : T6)
    (k0 k1 k2 k3 k4 k5 : ℕ) : Bool :=
  xN (wmask p k0 k1 k2 k3 k4 k5) fun wm =>
  xN (lab wm (r1 p) k0) fun l0 => xN (lab wm (r2 p) k1) fun l1 => xN (lab wm (r3 p) k2) fun l2 =>
  xN (lab wm (r4 p) k3) fun l3 => xN (lab wm (r5 p) k4) fun l4 => xN (lab wm (r6 p) k5) fun l5 =>
  xN (em (bmJ j 0) l0) fun m0 => xN (em (bmJ j 1) l1) fun m1 => xN (em (bmJ j 2) l2) fun m2 =>
  xN (em (bmJ j 3) l3) fun m3 => xN (em (bmJ j 4) l4) fun m4 => xN (em (bmJ j 5) l5) fun m5 =>
  tabF m0 m1 m2 m3 m4 m5 fun T => xN (horF T 0 64) fun I => xN (accG I) fun S =>
  xN (penC cps [l0, l1, l2, l3, l4, l5]) fun pe => xN (Nat.sub (Nat.add D K) pe) fun e =>
  okc6 D e S psi

/-- Two rows of a column type are compatible: equal pattern values force compatible kinds, and
different values exclude the same special colour. -/
def pairK (pa pb ka kb : ℕ) : Bool :=
  bif Nat.beq pa pb then
    (Nat.beq ka 0 == Nat.beq kb 0) && !(Nat.beq ka 5 && Nat.beq kb 6) && !(Nat.beq ka 6 && Nat.beq kb 5)
  else !(Nat.beq ka 5 && Nat.beq kb 5) && !(Nat.beq ka 6 && Nat.beq kb 6)

/-- The admissibility of a kind vector for a pattern. -/
def admK (p : T6) (k0 k1 k2 k3 k4 k5 : ℕ) : Bool :=
  pairK (r1 p) (r2 p) k0 k1 && pairK (r1 p) (r3 p) k0 k2 && pairK (r1 p) (r4 p) k0 k3 &&
  pairK (r1 p) (r5 p) k0 k4 && pairK (r1 p) (r6 p) k0 k5 && pairK (r2 p) (r3 p) k1 k2 &&
  pairK (r2 p) (r4 p) k1 k3 && pairK (r2 p) (r5 p) k1 k4 && pairK (r2 p) (r6 p) k1 k5 &&
  pairK (r3 p) (r4 p) k2 k3 && pairK (r3 p) (r5 p) k2 k4 && pairK (r3 p) (r6 p) k2 k5 &&
  pairK (r4 p) (r5 p) k3 k4 && pairK (r4 p) (r6 p) k3 k5 && pairK (r5 p) (r6 p) k4 k5

/-- The kinds of row `r`. -/
def kopts (j r : ℕ) : List ℕ := [0, spJ j r, 7]

/-- **The check of one pattern and one kind of the first row**: every admissible kind vector
passes. -/
def patK (D K j : ℕ) (cps : List (List (ℕ × ℕ) × ℕ)) (psi : List ℕ) (p : T6) (k0 : ℕ) : Bool :=
  (kopts j 1).all fun k1 => (kopts j 2).all fun k2 =>
  (kopts j 3).all fun k3 => (kopts j 4).all fun k4 => (kopts j 5).all fun k5 =>
    !(admK p k0 k1 k2 k3 k4 k5 && Nat.ble (popc (wmask p k0 k1 k2 k3 k4 k5)) 5) ||
      leafX D K j cps psi p k0 k1 k2 k3 k4 k5

/-- The data of one pattern are right: its values `Ψ` and its compiled pins. -/
def patS (P : List XP) (cps : List (List (ℕ × ℕ) × ℕ)) (psi : List ℕ) (p : T6) : Bool :=
  decide (psiL p = psi) && decide (compileX p P = cps)

end GridGen.Six
