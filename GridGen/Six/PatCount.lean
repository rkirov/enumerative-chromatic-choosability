/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.PartData

/-!
# Height six: counting proper colourings by pattern orbit

For lists `A₁, …, A₆` of colours below `8`, given as bit masks (`setOf`), the number of proper
colourings in each pattern orbit is an integer combination of the numbers `N_q` of colourings
(proper or not) constant on the blocks of a set partition `q` of the rows; `N_q` is the product,
over the blocks, of the sizes of the intersections of the lists in the block (`card_const_eq`,
from the general `card_piFinset_const`). The combination is Möbius inversion on the partition
lattice; its coefficients `MOB` are data, and the inversion identity is checked by the kernel
once (`idOK_all`), so that `card_orb_setOf` holds for all lists.

The bookkeeping goes through the *first-occurrence string* `foT t` of a column (each row
replaced by the first row of its colour): it is one of the 203 partitions `PART`
(`foT_mem_PART`), it has the equalities of `t` (`foT_rows`), and a column is constant on the
blocks of `q` iff `foT t` is coarser than `q` (`constB`).

This replaces the quotient-graph counts of `GridGen/Five/Small5/Count.lean`; it serves the
uniform transfer (`GridGen/Six/Uniform.lean`) and the exact certificates.
-/

namespace GridGen.Six

open Finset

/-! ### Rows by index and first occurrences -/

/-- Row `r` of a column (rows numbered from `0`). -/
def rowAt (r : ℕ) (t : T6) : ℕ :=
  match r with
  | 0 => r1 t
  | 1 => r2 t
  | 2 => r3 t
  | 3 => r4 t
  | 4 => r5 t
  | _ => r6 t

/-- The first row with the colour of row `k`. -/
def fo (t : T6) (k : ℕ) : ℕ :=
  if rowAt 0 t = rowAt k t then 0 else if rowAt 1 t = rowAt k t then 1
  else if rowAt 2 t = rowAt k t then 2 else if rowAt 3 t = rowAt k t then 3
  else if rowAt 4 t = rowAt k t then 4 else 5

theorem fo_row (t : T6) {k : ℕ} (hk : k < 6) : rowAt (fo t k) t = rowAt k t := by
  unfold fo
  interval_cases k <;> split_ifs <;> first | assumption | rfl | simp_all

theorem fo_le (t : T6) {k : ℕ} (hk : k < 6) : fo t k ≤ k := by
  unfold fo
  interval_cases k <;> split_ifs <;> simp_all

theorem fo_eq_iff (t : T6) {i j : ℕ} (hi : i < 6) (hj : j < 6) :
    fo t i = fo t j ↔ rowAt i t = rowAt j t :=
  ⟨fun h => by rw [← fo_row t hi, ← fo_row t hj, h], fun h => by unfold fo; rw [h]⟩

/-- The first-occurrence string of a column. -/
def foT (t : T6) : T6 := (fo t 0, fo t 1, fo t 2, fo t 3, fo t 4, fo t 5)

theorem rowAt_foT (t : T6) {k : ℕ} (hk : k < 6) : rowAt k (foT t) = fo t k := by
  interval_cases k <;> rfl

theorem foT_rows (t : T6) {i j : ℕ} (hi : i < 6) (hj : j < 6) :
    rowAt i (foT t) = rowAt j (foT t) ↔ rowAt i t = rowAt j t := by
  rw [rowAt_foT t hi, rowAt_foT t hj, fo_eq_iff t hi hj]

/-- The first-occurrence string reads only the equalities. -/
theorem foT_congr {s t : T6}
    (h : ∀ i < 6, ∀ j < 6, (rowAt i s = rowAt j s ↔ rowAt i t = rowAt j t)) : foT s = foT t := by
  have e : ∀ k < 6, fo s k = fo t k := by
    intro k hk
    simp only [fo, h 0 (by norm_num) k hk, h 1 (by norm_num) k hk, h 2 (by norm_num) k hk,
      h 3 (by norm_num) k hk, h 4 (by norm_num) k hk]
  simp only [foT, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num),
    e 4 (by norm_num), e 5 (by norm_num)]

theorem foT_idem (t : T6) : foT (foT t) = foT t :=
  foT_congr (fun _ hi _ hj => foT_rows t hi hj)

/-! ### The partitions -/

/-- All strings with entry `k` at most `k` (and entry `0` zero). -/
def all720 : List T6 :=
  (List.range 2).flatMap fun b => (List.range 3).flatMap fun c => (List.range 4).flatMap fun d =>
    (List.range 5).flatMap fun e => (List.range 6).map fun f => (0, b, c, d, e, f)

theorem foT_mem_all (t : T6) : foT t ∈ all720 := by
  have h0 : fo t 0 = 0 := by unfold fo; simp
  have h1 := fo_le t (k := 1) (by norm_num)
  have h2 := fo_le t (k := 2) (by norm_num)
  have h3 := fo_le t (k := 3) (by norm_num)
  have h4 := fo_le t (k := 4) (by norm_num)
  have h5 := fo_le t (k := 5) (by norm_num)
  simp only [all720, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨fo t 1, by omega, fo t 2, by omega, fo t 3, by omega, fo t 4, by omega, fo t 5, by omega,
    by rw [foT, h0]⟩

theorem PART_eq : PART = all720.filter (fun r => foT r == r) := by decide +kernel

/-- A code of a column with entries below `6`. -/
def code6 (t : T6) : ℕ := ((((r1 t * 6 + r2 t) * 6 + r3 t) * 6 + r4 t) * 6 + r5 t) * 6 + r6 t

theorem PART_sorted : (PART.map code6).Pairwise (· < ·) := by decide +kernel

theorem PART_nodup : PART.Nodup :=
  List.Nodup.of_map code6 (PART_sorted.imp (fun h => ne_of_lt h))

theorem PART_length : PART.length = 203 := by decide +kernel

theorem foT_mem_PART (t : T6) : foT t ∈ PART := by
  rw [PART_eq, List.mem_filter]
  exact ⟨foT_mem_all t, by simp [foT_idem]⟩

theorem foT_of_mem_PART {q : T6} (hq : q ∈ PART) : foT q = q := by
  rw [PART_eq, List.mem_filter] at hq
  simpa using hq.2

/-- The index of a column's partition. -/
def pidx (t : T6) : ℕ := PART.idxOf (foT t)

theorem pidx_lt (t : T6) : pidx t < 203 := by
  rw [← PART_length]; exact List.idxOf_lt_length_of_mem (foT_mem_PART t)

theorem getD_pidx (t : T6) : PART.getD (pidx t) (0, 0, 0, 0, 0, 0) = foT t := by
  rw [List.getD_eq_getElem _ _ (by rw [PART_length]; exact pidx_lt t)]
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem (foT_mem_PART t))

theorem pidx_eq_iff (t : T6) {ri : ℕ} (hri : ri < 203) :
    pidx t = ri ↔ foT t = PART.getD ri (0, 0, 0, 0, 0, 0) := by
  constructor
  · rintro rfl; exact (getD_pidx t).symm
  · intro h
    rw [List.getD_eq_getElem _ _ (by rw [PART_length]; exact hri)] at h
    unfold pidx
    rw [h]
    exact PART_nodup.idxOf_getElem ri _

/-- **Fibres over the partitions**: a sum of a function of the partition of a column. -/
theorem sum_by_part (S : Finset T6) (g : T6 → ℤ) :
    ∑ t ∈ S, g (foT t) = ∑ ri ∈ range 203, g (PART.getD ri (0, 0, 0, 0, 0, 0)) *
      ((S.filter (fun t => foT t = PART.getD ri (0, 0, 0, 0, 0, 0))).card : ℤ) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := pidx) (t := range 203)
    (fun t _ => mem_range.mpr (pidx_lt t))]
  refine Finset.sum_congr rfl fun ri hri => ?_
  have hri' := mem_range.mp hri
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
  have e : S.filter (fun t => pidx t = ri) = S.filter (fun t => foT t = PART.getD ri (0, 0, 0, 0, 0, 0)) :=
    Finset.filter_congr (fun t _ => pidx_eq_iff t hri')
  rw [e]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [(Finset.mem_filter.mp ht).2]
  simp

/-! ### Pair equalities and coarsening -/

/-- The fifteen pair equalities of a column. -/
def peq (t : T6) : List Bool :=
  [rowAt 0 t == rowAt 1 t, rowAt 0 t == rowAt 2 t, rowAt 0 t == rowAt 3 t, rowAt 0 t == rowAt 4 t,
    rowAt 0 t == rowAt 5 t, rowAt 1 t == rowAt 2 t, rowAt 1 t == rowAt 3 t, rowAt 1 t == rowAt 4 t,
    rowAt 1 t == rowAt 5 t, rowAt 2 t == rowAt 3 t, rowAt 2 t == rowAt 4 t, rowAt 2 t == rowAt 5 t,
    rowAt 3 t == rowAt 4 t, rowAt 3 t == rowAt 5 t, rowAt 4 t == rowAt 5 t]

/-- Entrywise implication of two lists of booleans. -/
def subB : List Bool → List Bool → Bool
  | a :: as, b :: bs => (!a || b) && subB as bs
  | _, _ => true

/-- `t` is constant on the blocks of `q`. -/
def constB (q t : T6) : Bool := subB (peq q) (peq t)

/-- The index of the pair `i < j` in `peq`. -/
def pairIdx (i j : ℕ) : ℕ := i * (11 - i) / 2 + (j - i - 1)

theorem peq_getD (t : T6) {i j : ℕ} (hij : i < j) (hj : j < 6) :
    (peq t).getD (pairIdx i j) false = (rowAt i t == rowAt j t) := by
  have hi : i < 5 := by omega
  interval_cases i <;> interval_cases j <;> rfl

theorem subB_iff : ∀ a b : List Bool, a.length = b.length →
    (subB a b = true ↔ ∀ n, a.getD n false = true → b.getD n false = true)
  | [], [], _ => by simp [subB]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)
  | x :: a, y :: b, h => by
    simp only [List.length_cons, add_left_inj] at h
    simp only [subB, Bool.and_eq_true, subB_iff a b h]
    constructor
    · rintro ⟨h1, h2⟩ n hn
      cases n with
      | zero => cases x <;> cases y <;> simp_all
      | succ n => exact h2 n hn
    · intro hh
      refine ⟨?_, fun n hn => hh (n + 1) hn⟩
      have := hh 0
      cases x <;> cases y <;> simp_all

theorem peq_length (t : T6) : (peq t).length = 15 := rfl

theorem constB_iff (q t : T6) : constB q t = true ↔
    ∀ i < 6, ∀ j < 6, rowAt i q = rowAt j q → rowAt i t = rowAt j t := by
  rw [constB, subB_iff _ _ (by rw [peq_length, peq_length])]
  constructor
  · intro h
    have key : ∀ i < 6, ∀ j < 6, i < j → rowAt i q = rowAt j q → rowAt i t = rowAt j t := by
      intro i hi j hj hij hq
      have := h (pairIdx i j)
      rw [peq_getD q hij hj, peq_getD t hij hj, beq_iff_eq, beq_iff_eq] at this
      exact this hq
    intro i hi j hj hq
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact key i hi j hj hij hq
    · rfl
    · exact (key j hj i hi hij hq.symm).symm
  · intro h n hn
    have hn15 : n < 15 := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by rw [peq_length]; omega)] at hn
      exact absurd hn (by decide)
    have e : ∃ i j, i < j ∧ j < 6 ∧ pairIdx i j = n := by
      interval_cases n
      exacts [⟨0, 1, by decide⟩, ⟨0, 2, by decide⟩, ⟨0, 3, by decide⟩, ⟨0, 4, by decide⟩,
        ⟨0, 5, by decide⟩, ⟨1, 2, by decide⟩, ⟨1, 3, by decide⟩, ⟨1, 4, by decide⟩,
        ⟨1, 5, by decide⟩, ⟨2, 3, by decide⟩, ⟨2, 4, by decide⟩, ⟨2, 5, by decide⟩,
        ⟨3, 4, by decide⟩, ⟨3, 5, by decide⟩, ⟨4, 5, by decide⟩]
    obtain ⟨i, j, hij, hj, rfl⟩ := e
    rw [peq_getD q hij hj, beq_iff_eq] at hn
    rw [peq_getD t hij hj, beq_iff_eq]
    exact h i (by omega) j hj hn

theorem peq_foT (t : T6) : peq (foT t) = peq t := by
  have e : ∀ i < 6, ∀ j < 6, (rowAt i (foT t) == rowAt j (foT t)) = (rowAt i t == rowAt j t) := by
    intro i hi j hj
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact foT_rows t hi hj
  simp only [peq, e 0 (by norm_num) 1 (by norm_num), e 0 (by norm_num) 2 (by norm_num),
    e 0 (by norm_num) 3 (by norm_num), e 0 (by norm_num) 4 (by norm_num),
    e 0 (by norm_num) 5 (by norm_num), e 1 (by norm_num) 2 (by norm_num),
    e 1 (by norm_num) 3 (by norm_num), e 1 (by norm_num) 4 (by norm_num),
    e 1 (by norm_num) 5 (by norm_num), e 2 (by norm_num) 3 (by norm_num),
    e 2 (by norm_num) 4 (by norm_num), e 2 (by norm_num) 5 (by norm_num),
    e 3 (by norm_num) 4 (by norm_num), e 3 (by norm_num) 5 (by norm_num),
    e 4 (by norm_num) 5 (by norm_num)]

theorem PEL_eq : PEL = PART.map peq := by decide +kernel

theorem PEL_getD {ri : ℕ} (hri : ri < 203) :
    PEL.getD ri [] = peq (PART.getD ri (0, 0, 0, 0, 0, 0)) := by
  rw [PEL_eq, List.getD_eq_getElem _ _ (by simp [PART_length, hri]),
    List.getD_eq_getElem _ _ (by simp [PART_length, hri])]
  simp

/-! ### The orbits of the partitions -/

/-- A column is proper, as a boolean. -/
def properB (t : T6) : Bool :=
  !(rowAt 0 t == rowAt 1 t) && !(rowAt 1 t == rowAt 2 t) && !(rowAt 2 t == rowAt 3 t) &&
    !(rowAt 3 t == rowAt 4 t) && !(rowAt 4 t == rowAt 5 t)

theorem properB_iff (t : T6) : properB t = true ↔ Proper t := by
  simp [properB, Proper, rowAt, and_assoc]

theorem samePat_foT (t : T6) : SamePat (foT t) t := by
  have e := fun i hi j hj => foT_rows t (i := i) (j := j) hi hj
  exact ⟨e 0 (by norm_num) 2 (by norm_num), e 1 (by norm_num) 3 (by norm_num),
    e 2 (by norm_num) 4 (by norm_num), e 3 (by norm_num) 5 (by norm_num),
    e 0 (by norm_num) 3 (by norm_num), e 1 (by norm_num) 4 (by norm_num),
    e 2 (by norm_num) 5 (by norm_num), e 0 (by norm_num) 4 (by norm_num),
    e 1 (by norm_num) 5 (by norm_num), e 0 (by norm_num) 5 (by norm_num)⟩

theorem proper_foT_iff (t : T6) : Proper (foT t) ↔ Proper t := by
  have e := fun i hi j hj => foT_rows t (i := i) (j := j) hi hj
  have e01 := e 0 (by norm_num) 1 (by norm_num)
  have e12 := e 1 (by norm_num) 2 (by norm_num)
  have e23 := e 2 (by norm_num) 3 (by norm_num)
  have e34 := e 3 (by norm_num) 4 (by norm_num)
  have e45 := e 4 (by norm_num) 5 (by norm_num)
  simp only [rowAt] at e01 e12 e23 e34 e45
  simp only [Proper, ne_eq, e01, e12, e23, e34, e45]

/-! ### The Möbius identity -/

/-- The inversion identity at orbit `o`: for every partition `r`, the coefficients of the
partitions finer than `r` sum to `1` if `r` is a proper pattern in orbit `o`, else to `0`. -/
def idOK (o : ℕ) : Bool :=
  (PART.zip PEL).all fun rp =>
    decide (((MOBT.getD o []).map fun x => if subB x.2.1 rp.2 then x.2.2 else 0).sum
      = if properB rp.1 && ((orb rp.1 : ℕ) == o) then 1 else 0)

/-- The Möbius entries are partitions with their pair equalities. -/
def mobtOK : Bool :=
  (List.range 32).all fun o => (MOBT.getD o []).all fun x => foT x.1 == x.1 && peq x.1 == x.2.1

theorem mobtOK_true : mobtOK = true := by decide +kernel

theorem MOBT_ok : ∀ o < 32, ∀ x ∈ MOBT.getD o [], foT x.1 = x.1 ∧ peq x.1 = x.2.1 := by
  intro o ho x hx
  have h := List.all_eq_true.mp (List.all_eq_true.mp mobtOK_true o (List.mem_range.mpr ho)) x hx
  simpa using h

theorem PEL_length : PEL.length = 203 := by decide +kernel

/-! ### The Möbius identity, checked fast

The kernel checks `idOK` through `idOKF`: the pair equalities as bit masks (`bmB`, `subB_bmB`)
and the coefficients split into positive and negative parts (`MOBM`, `PELM`, `sPB`, `sNB`). -/

/-- A list of booleans as a bit mask, the head lowest. -/
def bmB : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (bmB bs)

theorem subB_bmB : ∀ a b : List Bool, a.length = b.length →
    subB a b = (Nat.land (bmB a) (bmB b) == bmB a)
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)
  | x :: a, y :: b, h => by
    have ih := subB_bmB a b (by simpa using h)
    have e : Nat.land (bmB (x :: a)) (bmB (y :: b)) = Nat.bit (x && y) (Nat.land (bmB a) (bmB b)) :=
      Nat.land_bit x (bmB a) y (bmB b)
    rw [e]
    show ((!x || y) && subB a b) = (Nat.bit (x && y) (Nat.land (bmB a) (bmB b)) == Nat.bit x (bmB a))
    rw [ih]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, Nat.bit_val]
    cases x <;> cases y <;> simp <;> omega

/-- The packed form of a Möbius entry: the mask of its pair equalities, the positive and
negative parts of its coefficient. -/
def mobM (x : T6 × List Bool × ℤ) : ℕ × ℕ × ℕ := (bmB x.2.1, x.2.2.toNat, (-x.2.2).toNat)

/-- The Möbius table in packed form. -/
def MOBM : List (List (ℕ × ℕ × ℕ)) := data% "[[(32767,0,1),(9546,1,0)],[(32767,4,0),(5871,0,1),(9557,0,1),(19546,0,1),(9546,0,2),(1098,1,0),(32736,0,1),(9536,1,0)],[(32767,4,0),(11127,0,1),(9557,0,1),(32286,0,1),(19546,0,1),(6354,0,1),(2130,1,0),(9396,0,1),(9236,1,0)],[(32767,4,0),(11127,0,1),(9387,0,1),(32286,0,1),(9546,0,2),(29122,0,1),(8514,1,0),(9226,1,0)],[(32767,0,12),(5871,2,0),(11127,2,0),(16999,1,0),(615,0,1),(9387,2,0),(9557,2,0),(32257,1,0),(9217,0,1),(32286,2,0),(19546,2,0),(9546,2,0),(1098,0,1),(6354,1,0),(29122,2,0),(4290,0,1),(2130,0,1),(8514,0,1),(16450,0,1),(66,1,0),(9226,0,1),(9396,1,0),(32736,2,0),(9376,0,1),(9236,0,1),(9536,0,1),(32256,0,1),(9216,1,0)],[(32767,4,0),(19899,0,1),(29149,0,1),(5902,0,1),(9546,0,2),(1290,1,0),(11112,0,1),(8520,1,0)],[(32767,0,12),(5871,2,0),(11127,2,0),(19899,2,0),(9387,1,0),(1195,0,1),(29149,2,0),(9557,1,0),(8533,0,1),(32286,2,0),(5902,1,0),(5646,0,1),(19546,1,0),(9546,4,0),(1098,0,1),(29122,1,0),(8514,0,1),(19482,0,1),(1290,0,1),(9226,0,1),(1034,1,0),(11112,1,0),(32736,2,0),(11104,0,1),(8520,0,1),(29120,0,1),(9536,0,1),(8512,1,0)],[(32767,4,0),(19899,0,1),(29149,0,1),(10902,0,2),(6354,0,1),(2194,1,0),(9396,0,1),(8340,1,0)],[(32767,2,0),(9387,0,1),(10902,0,1),(29122,0,1),(8322,1,0)],[(32767,0,12),(5871,2,0),(19899,2,0),(9387,3,0),(1195,0,1),(29149,2,0),(10889,1,0),(8329,0,1),(10902,4,0),(17286,1,0),(646,0,1),(6354,1,0),(29122,3,0),(4290,0,1),(2194,0,1),(16770,0,1),(8322,0,2),(130,1,0),(9396,1,0),(32736,2,0),(9376,0,1),(8340,0,1),(29120,0,1),(10880,0,1),(8320,1,0)],[(32767,0,12),(11127,4,0),(19899,2,0),(6451,1,0),(2355,0,1),(29149,2,0),(9557,1,0),(8533,0,1),(32286,4,0),(10902,2,0),(10774,0,2),(19546,1,0),(6354,2,0),(2130,0,1),(19482,0,1),(2194,0,1),(6162,0,1),(2066,1,0),(28732,1,0),(9396,2,0),(8244,0,1),(28700,0,1),(8340,0,1),(9236,0,1),(8212,1,0)],[(32767,0,12),(11127,2,0),(19899,2,0),(9387,2,0),(6451,1,0),(2355,0,1),(29149,2,0),(10889,1,0),(8329,0,1),(32286,2,0),(5902,2,0),(17286,1,0),(774,0,1),(9546,2,0),(29122,2,0),(8514,0,1),(1290,0,1),(9226,0,1),(16770,0,1),(4354,0,1),(258,1,0),(28732,1,0),(11112,2,0),(8232,0,1),(28700,0,1),(8520,0,1),(10760,0,1),(8200,1,0)],[(32767,0,6),(11127,2,0),(9387,2,0),(28707,1,0),(8227,0,1),(32286,2,0),(10902,1,0),(10774,0,1),(9546,1,0),(29122,2,0),(8514,0,1),(9226,0,1),(8322,0,1),(28674,0,1),(8194,1,0)],[(32767,48,0),(5871,0,6),(11127,0,12),(16999,0,2),(615,2,0),(19899,0,6),(9387,0,8),(1195,2,0),(6451,0,2),(28707,0,4),(4131,1,0),(2355,2,0),(8227,3,0),(16419,1,0),(35,0,1),(29149,0,6),(9557,0,2),(8533,2,0),(10889,0,2),(32257,0,2),(10753,1,0),(8329,2,0),(9217,1,0),(28673,1,0),(8193,0,1),(32286,0,12),(5902,0,2),(5646,2,0),(10902,0,4),(17286,0,2),(646,1,0),(10774,4,0),(774,1,0),(16902,1,0),(518,0,1),(19546,0,2),(9546,0,4),(1098,1,0),(6354,0,2),(29122,0,8),(4290,2,0),(2130,1,0),(8514,3,0),(16450,1,0),(66,0,1),(19482,2,0),(1290,1,0),(9226,3,0),(1034,0,1),(2194,1,0),(16770,2,0),(8322,2,0),(130,0,1),(6162,1,0),(4354,1,0),(28674,3,0),(4098,0,1),(2066,0,1),(258,0,1),(8194,0,2),(16386,0,1),(2,1,0),(28732,0,2),(9396,0,2),(8244,1,0),(11112,0,2),(32736,0,6),(11104,2,0),(8232,1,0),(9376,2,0),(28704,1,0),(8224,0,1),(28700,2,0),(8340,1,0),(9236,1,0),(8212,0,1),(8520,1,0),(29120,2,0),(9536,1,0),(8512,0,1),(10760,1,0),(10880,1,0),(32256,2,0),(10752,0,1),(8200,0,1),(8320,0,1),(9216,0,1),(28672,0,1),(8192,1,0)],[(32767,2,0),(6349,0,1),(10902,0,1),(19876,0,1),(2180,1,0)],[(32767,0,12),(5871,2,0),(19899,2,0),(29149,2,0),(6349,3,0),(4301,0,1),(10889,1,0),(2185,0,1),(10902,4,0),(17286,1,0),(646,0,1),(6354,1,0),(2194,0,1),(9396,1,0),(19876,3,0),(1188,0,1),(32736,2,0),(19872,0,1),(8340,0,1),(16772,0,1),(2180,0,2),(132,1,0),(6336,0,1),(10880,0,1),(2176,1,0)],[(32767,4,0),(6349,0,1),(9557,0,1),(5902,0,1),(19546,0,1),(19876,0,1),(11112,0,1),(1284,1,0),(2120,1,0)],[(32767,0,12),(5871,2,0),(11127,2,0),(6349,2,0),(9557,2,0),(19525,2,0),(1093,0,1),(2117,0,1),(32286,2,0),(5902,1,0),(5646,0,1),(19546,2,0),(6354,1,0),(2130,0,1),(9396,1,0),(19876,2,0),(1188,0,1),(11112,1,0),(32736,2,0),(11104,0,1),(9236,0,1),(1284,0,1),(19460,0,1),(1028,1,0),(2120,0,1),(6336,0,1),(19520,0,1),(2112,1,0)],[(32767,0,12),(11127,2,0),(19899,2,0),(29149,2,0),(6349,2,0),(9557,1,0),(8533,0,1),(10889,1,0),(2185,0,1),(32286,2,0),(5902,2,0),(17286,1,0),(774,0,1),(19546,1,0),(19482,0,1),(6444,2,0),(19876,2,0),(2340,0,1),(11112,2,0),(2344,0,1),(4364,0,1),(6156,0,1),(16772,0,1),(1284,0,1),(260,1,0),(2120,0,1),(10760,0,1),(2056,1,0)],[(32767,0,6),(11127,2,0),(6349,2,0),(19525,1,0),(2117,0,1),(32286,2,0),(10902,1,0),(10774,0,1),(6444,1,0),(19876,2,0),(2340,0,1),(6156,0,1),(2180,0,1),(19460,0,1),(2052,1,0)],[(32767,48,0),(5871,0,6),(11127,0,12),(16999,0,2),(615,2,0),(19899,0,6),(6451,0,2),(2355,2,0),(29149,0,6),(6349,0,8),(4301,2,0),(9557,0,2),(19525,0,4),(1093,1,0),(8533,2,0),(2117,3,0),(16453,1,0),(69,0,1),(10889,0,2),(32257,0,2),(10753,1,0),(2185,2,0),(19457,1,0),(6145,1,0),(2049,0,1),(32286,0,12),(5902,0,2),(5646,2,0),(10902,0,4),(17286,0,2),(646,1,0),(10774,4,0),(774,1,0),(16902,1,0),(518,0,1),(19546,0,2),(6354,0,2),(2130,1,0),(19482,2,0),(2194,1,0),(6162,1,0),(2066,0,1),(28732,0,2),(6444,0,4),(4140,1,0),(9396,0,2),(19876,0,8),(1188,2,0),(8244,1,0),(2340,3,0),(16420,1,0),(36,0,1),(11112,0,2),(32736,0,6),(11104,2,0),(2344,1,0),(19872,2,0),(6432,1,0),(2336,0,1),(28700,2,0),(4364,1,0),(6156,3,0),(4108,0,1),(8340,1,0),(16772,2,0),(2180,2,0),(132,0,1),(9236,1,0),(1284,1,0),(19460,3,0),(1028,0,1),(8212,0,1),(260,0,1),(2052,0,2),(16388,0,1),(4,1,0),(2120,1,0),(6336,2,0),(19520,1,0),(2112,0,1),(10760,1,0),(10880,1,0),(32256,2,0),(10752,0,1),(2056,0,1),(2176,0,1),(19456,0,1),(6144,0,1),(2048,1,0)],[(32767,0,12),(5871,2,0),(19899,2,0),(29149,2,0),(6349,1,0),(4301,0,1),(9557,2,0),(5905,1,0),(1297,0,1),(5902,2,0),(19546,2,0),(9546,2,0),(1098,0,1),(1290,0,1),(19876,1,0),(17016,1,0),(11112,2,0),(616,0,1),(32736,2,0),(19872,0,1),(1284,0,1),(16472,0,1),(8520,0,1),(2120,0,1),(72,1,0),(9536,0,1),(5888,0,1),(1280,1,0)],[(32767,2,0),(9557,0,1),(19546,0,1),(5872,0,1),(1104,1,0)],[(32767,0,6),(5871,2,0),(9557,2,0),(19525,1,0),(1093,0,1),(19546,2,0),(9546,1,0),(1098,0,1),(5872,1,0),(32736,2,0),(5856,0,1),(1104,0,1),(9536,0,1),(19520,0,1),(1088,1,0)],[(32767,0,12),(11127,2,0),(19899,2,0),(29149,2,0),(9557,3,0),(8533,0,1),(5905,1,0),(1297,0,1),(32286,2,0),(19546,3,0),(6354,1,0),(2130,0,1),(19482,0,1),(9396,1,0),(17016,1,0),(5872,4,0),(624,0,1),(1200,0,1),(9236,0,1),(16472,0,1),(4304,0,1),(1104,0,2),(80,1,0),(5648,0,1),(1040,1,0)],[(32767,48,0),(5871,0,12),(11127,0,6),(16999,0,2),(615,2,0),(19899,0,6),(9387,0,2),(1195,2,0),(29149,0,6),(6349,0,2),(4301,2,0),(9557,0,8),(19525,0,4),(1093,3,0),(8533,2,0),(2117,1,0),(16453,1,0),(69,0,1),(5905,0,2),(32257,0,2),(5633,1,0),(1297,2,0),(19457,1,0),(9217,1,0),(1025,0,1),(32286,0,6),(5902,0,2),(5646,2,0),(19546,0,8),(9546,0,4),(1098,3,0),(6354,0,2),(29122,0,2),(4290,1,0),(2130,2,0),(8514,1,0),(16450,1,0),(66,0,1),(19482,2,0),(1290,1,0),(9226,1,0),(1034,0,1),(9396,0,2),(19876,0,2),(1188,1,0),(17016,0,2),(11112,0,2),(616,1,0),(5872,0,4),(32736,0,12),(5856,4,0),(624,1,0),(11104,2,0),(16992,1,0),(608,0,1),(1200,1,0),(19872,2,0),(9376,1,0),(1184,0,1),(9236,2,0),(1284,1,0),(19460,1,0),(1028,0,1),(16472,2,0),(8520,1,0),(2120,1,0),(72,0,1),(4304,1,0),(29120,2,0),(6336,1,0),(4288,0,1),(1104,2,0),(9536,3,0),(19520,3,0),(1088,0,2),(80,0,1),(8512,0,1),(2112,0,1),(16448,0,1),(64,1,0),(5648,1,0),(5888,1,0),(32256,2,0),(5632,0,1),(1040,0,1),(1280,0,1),(19456,0,1),(9216,0,1),(1024,1,0)],[(32767,0,6),(19899,2,0),(29149,2,0),(17305,1,0),(16793,0,1),(5902,2,0),(9546,1,0),(1290,0,1),(6444,1,0),(11112,2,0),(2344,0,1),(4364,0,1),(8520,0,1),(776,0,1),(264,1,0)],[(32767,48,0),(5871,0,6),(11127,0,6),(19899,0,12),(9387,0,2),(1195,2,0),(6451,0,2),(2355,2,0),(29149,0,12),(6349,0,2),(4301,2,0),(9557,0,2),(8533,2,0),(17305,0,4),(10889,0,2),(649,1,0),(5905,0,2),(785,1,0),(16793,4,0),(2185,1,0),(8329,1,0),(137,0,1),(1297,1,0),(4369,1,0),(273,0,1),(32286,0,6),(5902,0,8),(5646,2,0),(17286,0,2),(774,2,0),(19546,0,2),(9546,0,4),(1098,1,0),(29122,0,2),(8514,1,0),(19482,2,0),(1290,3,0),(9226,1,0),(1034,0,1),(16770,1,0),(4354,1,0),(258,0,1),(28732,0,2),(6444,0,4),(4140,1,0),(19876,0,2),(2340,1,0),(17016,0,2),(11112,0,8),(616,2,0),(32736,0,6),(11104,2,0),(16440,1,0),(2344,3,0),(8232,1,0),(40,0,1),(19872,2,0),(6432,1,0),(2336,0,1),(28700,2,0),(4364,3,0),(6156,1,0),(4108,0,1),(16772,1,0),(1284,1,0),(260,0,1),(16472,1,0),(8520,3,0),(2120,1,0),(72,0,1),(29120,2,0),(9536,1,0),(8512,0,1),(16920,1,0),(776,2,0),(10760,2,0),(520,0,1),(17280,1,0),(5888,2,0),(768,0,1),(16408,0,1),(264,0,2),(2056,0,1),(8200,0,1),(8,1,0),(16768,0,1),(1280,0,1),(4352,0,1),(256,1,0)],[(32767,0,6),(19899,2,0),(29149,2,0),(17305,1,0),(16793,0,1),(10902,2,0),(6354,1,0),(2194,0,1),(9396,1,0),(5872,2,0),(1200,0,1),(8340,0,1),(4304,0,1),(656,0,1),(144,1,0)],[(32767,24,0),(5871,0,6),(19899,0,6),(9387,0,2),(1195,2,0),(29149,0,6),(6349,0,2),(4301,2,0),(17305,0,2),(10889,0,2),(649,1,0),(16793,2,0),(2185,1,0),(8329,1,0),(137,0,1),(10902,0,6),(17286,0,2),(646,2,0),(6354,0,2),(29122,0,2),(4290,1,0),(2194,2,0),(16770,1,0),(8322,1,0),(130,0,1),(9396,0,2),(19876,0,2),(1188,1,0),(5872,0,2),(32736,0,6),(5856,2,0),(1200,1,0),(19872,2,0),(9376,1,0),(1184,0,1),(8340,2,0),(16772,1,0),(2180,1,0),(132,0,1),(4304,1,0),(29120,2,0),(6336,1,0),(4288,0,1),(656,1,0),(17280,1,0),(10880,2,0),(640,0,1),(144,0,1),(16768,0,1),(2176,0,1),(8320,0,1),(128,1,0)],[(32767,24,0),(11127,0,6),(19899,0,6),(6451,0,2),(2355,2,0),(29149,0,6),(9557,0,2),(8533,2,0),(17305,0,2),(5905,0,2),(785,1,0),(16793,2,0),(1297,1,0),(4369,1,0),(273,0,1),(32286,0,6),(10902,0,2),(10774,2,0),(19546,0,2),(6354,0,2),(2130,1,0),(19482,2,0),(2194,1,0),(6162,1,0),(2066,0,1),(28732,0,2),(9396,0,2),(8244,1,0),(17016,0,2),(5872,0,6),(624,2,0),(16440,1,0),(1200,2,0),(4144,1,0),(48,0,1),(28700,2,0),(8340,1,0),(9236,1,0),(8212,0,1),(16472,1,0),(4304,2,0),(1104,1,0),(80,0,1),(16920,1,0),(656,1,0),(5648,2,0),(528,0,1),(16408,0,1),(144,0,1),(1040,0,1),(4112,0,1),(16,1,0)],[(32767,0,120),(5871,24,0),(11127,24,0),(16999,6,0),(615,0,6),(19899,24,0),(9387,6,0),(1195,0,6),(6451,6,0),(28707,4,0),(4131,0,2),(2355,0,6),(8227,0,2),(16419,0,2),(35,2,0),(29149,24,0),(6349,6,0),(4301,0,6),(9557,6,0),(19525,4,0),(1093,0,2),(8533,0,6),(2117,0,2),(16453,0,2),(69,2,0),(17305,6,0),(10889,4,0),(649,0,2),(5905,4,0),(32257,6,0),(5633,0,2),(785,0,2),(10753,0,2),(16897,0,1),(513,1,0),(16793,0,6),(2185,0,2),(8329,0,2),(137,2,0),(1297,0,2),(19457,0,2),(9217,0,1),(1025,1,0),(4369,0,2),(6145,0,1),(28673,0,2),(4097,1,0),(273,2,0),(2049,1,0),(8193,1,0),(16385,1,0),(1,0,1),(32286,24,0),(5902,6,0),(5646,0,6),(10902,6,0),(17286,4,0),(646,0,2),(10774,0,6),(774,0,2),(16902,0,2),(518,2,0),(19546,6,0),(9546,4,0),(1098,0,2),(6354,4,0),(29122,6,0),(4290,0,2),(2130,0,2),(8514,0,2),(16450,0,1),(66,1,0),(19482,0,6),(1290,0,2),(9226,0,2),(1034,2,0),(2194,0,2),(16770,0,2),(8322,0,1),(130,1,0),(6162,0,2),(4354,0,1),(28674,0,2),(4098,1,0),(2066,2,0),(258,1,0),(8194,1,0),(16386,1,0),(2,0,1),(28732,6,0),(6444,4,0),(4140,0,2),(9396,4,0),(19876,6,0),(1188,0,2),(8244,0,2),(2340,0,2),(16420,0,1),(36,1,0),(17016,4,0),(11112,6,0),(616,0,2),(5872,6,0),(32736,24,0),(5856,0,6),(624,0,2),(11104,0,6),(16992,0,2),(608,2,0),(16440,0,2),(2344,0,2),(8232,0,1),(40,1,0),(1200,0,2),(19872,0,6),(9376,0,2),(1184,2,0),(4144,0,1),(6432,0,2),(28704,0,2),(4128,1,0),(48,1,0),(2336,2,0),(8224,1,0),(16416,1,0),(32,0,1),(28700,0,6),(4364,0,2),(6156,0,2),(4108,2,0),(8340,0,2),(16772,0,2),(2180,0,1),(132,1,0),(9236,0,2),(1284,0,1),(19460,0,2),(1028,1,0),(8212,2,0),(260,1,0),(2052,1,0),(16388,1,0),(4,0,1),(16472,0,2),(8520,0,2),(2120,0,1),(72,1,0),(4304,0,2),(29120,0,6),(6336,0,2),(4288,2,0),(1104,0,1),(9536,0,2),(19520,0,2),(1088,1,0),(80,1,0),(8512,2,0),(2112,1,0),(16448,1,0),(64,0,1),(16920,0,2),(776,0,1),(10760,0,2),(520,1,0),(656,0,1),(17280,0,2),(10880,0,2),(640,1,0),(5648,0,2),(5888,0,2),(32256,0,6),(5632,2,0),(528,1,0),(768,1,0),(10752,2,0),(16896,1,0),(512,0,1),(16408,2,0),(264,1,0),(2056,1,0),(8200,1,0),(8,0,1),(144,1,0),(16768,2,0),(2176,1,0),(8320,1,0),(128,0,1),(1040,1,0),(1280,1,0),(19456,2,0),(9216,1,0),(1024,0,1),(4112,1,0),(4352,1,0),(6144,1,0),(28672,2,0),(4096,0,1),(16,0,1),(256,0,1),(2048,0,1),(8192,0,1),(16384,0,1),(0,1,0)]]"

theorem MOBM_eq : MOBM = MOBT.map (List.map mobM) := by decide +kernel

/-- The pair equalities of the partitions as masks. -/
def PELM : List ℕ := data% "[32767,5871,11127,16999,615,19899,9387,1195,6451,28707,4131,2355,8227,16419,35,29149,6349,4301,9557,19525,1093,8533,2117,16453,69,17305,10889,649,5905,32257,5633,785,10753,16897,513,16793,2185,8329,137,1297,19457,9217,1025,4369,6145,28673,4097,273,2049,8193,16385,1,32286,5902,5646,10902,17286,646,10774,774,16902,518,19546,9546,1098,6354,29122,4290,2130,8514,16450,66,19482,1290,9226,1034,2194,16770,8322,130,6162,4354,28674,4098,2066,258,8194,16386,2,28732,6444,4140,9396,19876,1188,8244,2340,16420,36,17016,11112,616,5872,32736,5856,624,11104,16992,608,16440,2344,8232,40,1200,19872,9376,1184,4144,6432,28704,4128,48,2336,8224,16416,32,28700,4364,6156,4108,8340,16772,2180,132,9236,1284,19460,1028,8212,260,2052,16388,4,16472,8520,2120,72,4304,29120,6336,4288,1104,9536,19520,1088,80,8512,2112,16448,64,16920,776,10760,520,656,17280,10880,640,5648,5888,32256,5632,528,768,10752,16896,512,16408,264,2056,8200,8,144,16768,2176,8320,128,1040,1280,19456,9216,1024,4112,4352,6144,28672,4096,16,256,2048,8192,16384,0]"

theorem PELM_eq : PELM = PEL.map bmB := by decide +kernel

/-- The positive part of the coefficients of the entries finer than `m`. -/
def sPB (m : ℕ) (L : List (ℕ × ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun x _ acc => Nat.add (cond (Nat.beq (Nat.land x.1 m) x.1) x.2.1 0) acc) L

/-- The negative part of the coefficients of the entries finer than `m`. -/
def sNB (m : ℕ) (L : List (ℕ × ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun x _ acc => Nat.add (cond (Nat.beq (Nat.land x.1 m) x.1) x.2.2 0) acc) L

/-- **The Möbius identity at orbit `o`, fast.** -/
def idOKF (o : ℕ) : Bool :=
  (PART.zip PELM).all fun rp =>
    Nat.beq (sPB rp.2 (MOBM.getD o []))
      (Nat.add (sNB rp.2 (MOBM.getD o [])) (cond (properB rp.1 && ((orb rp.1 : ℕ) == o)) 1 0))

theorem idOKF_0 : ((List.range 16).all idOKF) = true := by decide +kernel
theorem idOKF_1 : (((List.range 16).map (· + 16)).all idOKF) = true := by decide +kernel

theorem sPN_eq (b : List Bool) : ∀ L : List (T6 × List Bool × ℤ),
    (∀ x ∈ L, x.2.1.length = b.length) →
    ((sPB (bmB b) (L.map mobM) : ℕ) : ℤ) - (sNB (bmB b) (L.map mobM) : ℕ)
      = (L.map fun x => if subB x.2.1 b then x.2.2 else 0).sum
  | [], _ => by simp [sPB, sNB]
  | x :: L, hl => by
    have ih := sPN_eq b L (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    have hs := subB_bmB x.2.1 b (hl x List.mem_cons_self)
    show ((Nat.add (cond (Nat.beq (Nat.land (mobM x).1 (bmB b)) (mobM x).1) (mobM x).2.1 0)
        (sPB (bmB b) (L.map mobM)) : ℕ) : ℤ)
      - ((Nat.add (cond (Nat.beq (Nat.land (mobM x).1 (bmB b)) (mobM x).1) (mobM x).2.2 0)
        (sNB (bmB b) (L.map mobM)) : ℕ) : ℤ) = _
    rw [List.map_cons, List.sum_cons, ← ih]
    have hc : ((x.2.2.toNat : ℕ) : ℤ) - ((-x.2.2).toNat : ℕ) = x.2.2 := Int.toNat_sub_toNat_neg _
    have hb : Nat.beq (Nat.land (mobM x).1 (bmB b)) (mobM x).1 = subB x.2.1 b := by
      rw [hs]; rfl
    rw [hb]
    cases subB x.2.1 b
    · simp only [Nat.add_eq, Bool.cond_false, Bool.false_eq_true, ite_false]; push_cast; ring
    · simp only [mobM, Nat.add_eq, Bool.cond_true, ite_true]; push_cast; linear_combination hc

theorem idOK_of_F {o : ℕ} (ho : o < 32) (h : idOKF o = true) : idOK o = true := by
  unfold idOKF at h
  rw [PELM_eq, List.zip_map_right, List.all_map, List.all_eq_true] at h
  unfold idOK
  rw [List.all_eq_true]
  intro rp hrp
  have k := h rp hrp
  simp only [Function.comp, Prod.map, id] at k
  rw [Nat.beq_eq] at k
  have hm : MOBM.getD o [] = (MOBT.getD o []).map mobM := by
    rw [MOBM_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases MOBT[o]? <;> rfl
  rw [hm] at k
  have hlen : rp.2.length = 15 := by
    have h2 := (List.of_mem_zip hrp).2
    rw [PEL_eq] at h2
    obtain ⟨q, -, hq⟩ := List.mem_map.mp h2
    rw [← hq]; rfl
  have hl : ∀ x ∈ MOBT.getD o [], x.2.1.length = rp.2.length := by
    intro x hx
    rw [hlen, ← (MOBT_ok o ho x hx).2]
    rfl
  rw [decide_eq_true_eq, ← sPN_eq rp.2 _ hl, k]
  cases properB rp.1 && ((orb rp.1 : ℕ) == o) <;> simp

theorem idOK_all (o : Fin 32) : idOK o = true := by
  apply idOK_of_F o.2
  rcases Nat.lt_or_ge o 16 with h | h
  · exact List.all_eq_true.mp idOKF_0 o (List.mem_range.mpr h)
  · exact List.all_eq_true.mp idOKF_1 o (List.mem_map.mpr ⟨o - 16, List.mem_range.mpr (by omega),
      by omega⟩)

theorem mem_zip_getD {ri : ℕ} (hri : ri < 203) :
    (PART.getD ri (0, 0, 0, 0, 0, 0), PEL.getD ri []) ∈ PART.zip PEL := by
  rw [List.getD_eq_getElem _ _ (by rw [PART_length]; exact hri),
    List.getD_eq_getElem _ _ (by rw [PEL_length]; exact hri)]
  have h : ri < (PART.zip PEL).length := by simp [PART_length, PEL_length, hri]
  have := List.getElem_mem h
  rwa [List.getElem_zip] at this

/-! ### Colourings constant on blocks -/

/-- The colours below `8` of a mask. -/
def setOf (m : ℕ) : Finset ℕ := (range 8).filter (fun x => m.testBit x)

instance (t : T6) : Decidable (Proper t) := by unfold Proper; infer_instance

/-- The product of six lists. -/
def prodS (A B C D E F : Finset ℕ) : Finset T6 := A ×ˢ (B ×ˢ (C ×ˢ (D ×ˢ (E ×ˢ F))))

theorem mem_prodS {A B C D E F : Finset ℕ} {t : T6} :
    t ∈ prodS A B C D E F ↔ r1 t ∈ A ∧ r2 t ∈ B ∧ r3 t ∈ C ∧ r4 t ∈ D ∧ r5 t ∈ E ∧ r6 t ∈ F := by
  simp [prodS]

theorem sts_eq_filter (A B C D E F : Finset ℕ) :
    sts A B C D E F = (prodS A B C D E F).filter (fun t => Proper t) := by
  ext t; rw [Finset.mem_filter, mem_sts, mem_prodS]; simp only [Proper]; tauto

/-- **The general block count**: functions constant on the fibres of an idempotent map. -/
theorem card_piFinset_const {n : ℕ} (L : Fin n → Finset ℕ) (Q : Fin n → Fin n)
    (hQ : ∀ i, Q (Q i) = Q i) :
    ((Fintype.piFinset L).filter (fun f => ∀ i, f i = f (Q i))).card
      = ∏ k ∈ univ.filter (fun k => Q k = k),
          ((L k).filter (fun x => ∀ i, Q i = k → x ∈ L i)).card := by
  classical
  let C : {k : Fin n // Q k = k} → Finset ℕ :=
    fun k => (L k.1).filter (fun x => ∀ i, Q i = k.1 → x ∈ L i)
  have h1 : ((Fintype.piFinset L).filter (fun f => ∀ i, f i = f (Q i))).card
      = (Fintype.piFinset C).card := by
    refine Finset.card_nbij' (fun f k => f k.1) (fun g i => g ⟨Q i, hQ i⟩) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset] at hf
      simp only [Finset.mem_coe, Fintype.mem_piFinset]
      intro k
      simp only [C, Finset.mem_filter]
      refine ⟨hf.1 k.1, fun i hi => ?_⟩
      have := hf.2 i
      rw [hi] at this
      rw [← this]; exact hf.1 i
    · intro g hg
      simp only [Finset.mem_coe, Fintype.mem_piFinset] at hg
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset]
      refine ⟨fun i => ((Finset.mem_filter.mp (hg ⟨Q i, hQ i⟩)).2 i rfl), fun i => ?_⟩
      congr 1
      exact Subtype.ext (hQ i).symm
    · intro f hf
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hf
      funext i
      exact (hf.2 i).symm
    · intro g _
      funext k
      exact congrArg g (Subtype.ext k.2)
  rw [h1, Fintype.card_piFinset]
  exact (Finset.prod_subtype (univ.filter fun k => Q k = k) (by simp)
    (fun k => ((L k).filter (fun x => ∀ i, Q i = k → x ∈ L i)).card)).symm

/-- A column as a function on the rows. -/
def toF (t : T6) : Fin 6 → ℕ := fun i => rowAt i t

/-- A function on the rows as a column. -/
def ofF (f : Fin 6 → ℕ) : T6 := (f 0, f 1, f 2, f 3, f 4, f 5)

theorem toF_ofF (f : Fin 6 → ℕ) : toF (ofF f) = f := by
  funext i; fin_cases i <;> rfl

/-- The six lists as a family. -/
def LL (A B C D E F : Finset ℕ) : Fin 6 → Finset ℕ := ![A, B, C, D, E, F]

theorem card_prodS_filter (A B C D E F : Finset ℕ) (P : (Fin 6 → ℕ) → Prop) [DecidablePred P] :
    ((prodS A B C D E F).filter (fun t => P (toF t))).card
      = ((Fintype.piFinset (LL A B C D E F)).filter P).card := by
  refine Finset.card_nbij' toF ofF ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_prodS] at ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ht.2⟩
    fin_cases i
    exacts [ht.1.1, ht.1.2.1, ht.1.2.2.1, ht.1.2.2.2.1, ht.1.2.2.2.2.1, ht.1.2.2.2.2.2]
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset] at hf
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_prodS, toF_ofF]
    exact ⟨⟨hf.1 0, hf.1 1, hf.1 2, hf.1 3, hf.1 4, hf.1 5⟩, hf.2⟩
  · intro t _; rfl
  · intro f _; exact toF_ofF f

/-! ### The block count from masks -/

/-- The number of set bits below `8`. -/
def popc (a : ℕ) : ℕ :=
  (cond (a.testBit 0) 1 0) + (cond (a.testBit 1) 1 0) + (cond (a.testBit 2) 1 0) +
    (cond (a.testBit 3) 1 0) + (cond (a.testBit 4) 1 0) + (cond (a.testBit 5) 1 0) +
    (cond (a.testBit 6) 1 0) + (cond (a.testBit 7) 1 0)

theorem card_setOf (a : ℕ) : (setOf a).card = popc a := by
  rw [setOf, Finset.card_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, popc]
  cases a.testBit 0 <;> cases a.testBit 1 <;> cases a.testBit 2 <;> cases a.testBit 3 <;>
    cases a.testBit 4 <;> cases a.testBit 5 <;> cases a.testBit 6 <;> cases a.testBit 7 <;> rfl

/-- The intersection of the masks of the rows in block `k` of `q`. -/
def blk (q : T6) (ms : List ℕ) (k : ℕ) : ℕ :=
  (List.range 6).foldr (fun i acc => if rowAt i q = k then (ms.getD i 0) &&& acc else acc) 255

theorem testBit_blk (q : T6) (ms : List ℕ) (k x : ℕ) (hx : x < 8) :
    (blk q ms k).testBit x = (List.range 6).all (fun i => !(rowAt i q == k) || (ms.getD i 0).testBit x) := by
  unfold blk
  generalize List.range 6 = L
  induction L with
  | nil =>
    simp only [List.foldr_nil, List.all_nil]
    interval_cases x <;> decide
  | cons i L ih =>
    simp only [List.foldr_cons, List.all_cons]
    split_ifs with h
    · rw [Nat.testBit_and, ih]; simp [h]
    · rw [ih]; simp [h]

/-- **`N_q` from the masks**: the product over the blocks of `q` of the sizes of the
intersections. -/
def Nq (q : T6) (ms : List ℕ) : ℕ :=
  (if rowAt 0 q = 0 then popc (blk q ms 0) else 1) * (if rowAt 1 q = 1 then popc (blk q ms 1) else 1) *
    (if rowAt 2 q = 2 then popc (blk q ms 2) else 1) * (if rowAt 3 q = 3 then popc (blk q ms 3) else 1) *
    (if rowAt 4 q = 4 then popc (blk q ms 4) else 1) * (if rowAt 5 q = 5 then popc (blk q ms 5) else 1)

/-- The lists of the masks. -/
def LS (ms : List ℕ) : Fin 6 → Finset ℕ := fun i => setOf (ms.getD i 0)

theorem LL_LS (ms : List ℕ) :
    LL (setOf (ms.getD 0 0)) (setOf (ms.getD 1 0)) (setOf (ms.getD 2 0)) (setOf (ms.getD 3 0))
      (setOf (ms.getD 4 0)) (setOf (ms.getD 5 0)) = LS ms := by
  funext i; fin_cases i <;> rfl

/-- The partition `q` (a first-occurrence string) as an idempotent map of the rows. -/
def Qm (q : T6) (hq : foT q = q) : Fin 6 → Fin 6 := fun i =>
  ⟨rowAt i q, by
    have h := fo_le q (k := i) i.2
    rw [← rowAt_foT q i.2, hq] at h
    omega⟩

theorem Qm_val {q : T6} (hq : foT q = q) (i : Fin 6) : (Qm q hq i : ℕ) = rowAt i q := rfl

theorem rowAt_rowAt {q : T6} (hq : foT q = q) {i : ℕ} (hi : i < 6) :
    rowAt (rowAt i q) q = rowAt i q := by
  have h := fo_row q hi
  rw [← rowAt_foT q hi, hq] at h
  exact h

theorem Qm_idem {q : T6} (hq : foT q = q) (i : Fin 6) : Qm q hq (Qm q hq i) = Qm q hq i :=
  Fin.ext (rowAt_rowAt hq i.2)

theorem constB_iff_Qm {q : T6} (hq : foT q = q) (t : T6) :
    constB q t = true ↔ ∀ i : Fin 6, toF t i = toF t (Qm q hq i) := by
  rw [constB_iff]
  constructor
  · intro h i
    have hlt : rowAt i q < 6 := (Qm q hq i).2
    exact h i i.2 _ hlt (rowAt_rowAt hq i.2).symm
  · intro h i hi j hj hij
    have e1 := h ⟨i, hi⟩
    have e2 := h ⟨j, hj⟩
    simp only [toF, Qm_val] at e1 e2
    rw [e1, e2, hij]

theorem filter_blk {q : T6} (hq : foT q = q) (ms : List ℕ) (k : Fin 6) (hk : rowAt k q = k) :
    (LS ms k).filter (fun x => ∀ i, Qm q hq i = k → x ∈ LS ms i) = setOf (blk q ms k) := by
  ext x
  simp only [LS, setOf, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hx, hkx⟩, h⟩
    refine ⟨hx, ?_⟩
    rw [testBit_blk q ms k x hx, List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.mp hi
    by_cases hik : rowAt i q = k
    · have := (h ⟨i, hi'⟩ (Fin.ext hik)).2
      rw [Bool.or_eq_true]; exact Or.inr this
    · simp [hik]
  · rintro ⟨hx, hb⟩
    rw [testBit_blk q ms k x hx, List.all_eq_true] at hb
    have hall : ∀ i < 6, rowAt i q = k → (ms.getD i 0).testBit x = true := by
      intro i hi hik
      have := hb i (List.mem_range.mpr hi)
      simpa [hik] using this
    refine ⟨⟨hx, hall k k.2 hk⟩, fun i hi => ⟨hx, hall i i.2 ?_⟩⟩
    have := congrArg Fin.val hi
    simpa [Qm_val] using this

/-- **The block count.** -/
theorem card_const_eq {q : T6} (hq : foT q = q) (ms : List ℕ) :
    ((prodS (setOf (ms.getD 0 0)) (setOf (ms.getD 1 0)) (setOf (ms.getD 2 0)) (setOf (ms.getD 3 0))
      (setOf (ms.getD 4 0)) (setOf (ms.getD 5 0))).filter (fun t => constB q t = true)).card
      = Nq q ms := by
  have e : (prodS (setOf (ms.getD 0 0)) (setOf (ms.getD 1 0)) (setOf (ms.getD 2 0))
      (setOf (ms.getD 3 0)) (setOf (ms.getD 4 0)) (setOf (ms.getD 5 0))).filter
        (fun t => constB q t = true)
      = (prodS (setOf (ms.getD 0 0)) (setOf (ms.getD 1 0)) (setOf (ms.getD 2 0))
      (setOf (ms.getD 3 0)) (setOf (ms.getD 4 0)) (setOf (ms.getD 5 0))).filter
        (fun t => (fun f => ∀ i : Fin 6, f i = f (Qm q hq i)) (toF t)) :=
    Finset.filter_congr (fun t _ => constB_iff_Qm hq t)
  rw [e, card_prodS_filter _ _ _ _ _ _ (fun f => ∀ i : Fin 6, f i = f (Qm q hq i)), LL_LS, card_piFinset_const _ _ (Qm_idem hq), Finset.prod_filter,
    Fin.prod_univ_six]
  have fac : ∀ k : Fin 6, (if Qm q hq k = k then
      ((LS ms k).filter (fun x => ∀ i, Qm q hq i = k → x ∈ LS ms i)).card else 1)
      = if rowAt k q = k then popc (blk q ms k) else 1 := by
    intro k
    by_cases hk : rowAt k q = k
    · have hk' : Qm q hq k = k := Fin.ext hk
      rw [ite_eq_left hk', ite_eq_left hk, filter_blk hq ms k hk, card_setOf]
    · have hk' : ¬ Qm q hq k = k := fun h => hk (congrArg Fin.val h)
      rw [ite_eq_right hk', ite_eq_right hk]
  rw [fac 0, fac 1, fac 2, fac 3, fac 4, fac 5]
  rfl

/-! ### The orbit counts -/

/-- The orbit count from the masks: `Σ c · N_q` over the Möbius entries. -/
def cntO (o : ℕ) (ms : List ℕ) : ℤ :=
  ((MOBT.getD o []).map fun x => x.2.2 * (Nq x.1 ms : ℤ)).sum

theorem list_sum_finset {α : Type*} (L : List α) (S : Finset ℕ) (f : α → ℕ → ℤ) :
    (L.map fun x => ∑ r ∈ S, f x r).sum = ∑ r ∈ S, (L.map fun x => f x r).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- **Proper colourings by pattern orbit**, for lists given by masks. -/
theorem card_orb_setOf (ms : List ℕ) (o : Fin 32) :
    (((sts (setOf (ms.getD 0 0)) (setOf (ms.getD 1 0)) (setOf (ms.getD 2 0)) (setOf (ms.getD 3 0))
      (setOf (ms.getD 4 0)) (setOf (ms.getD 5 0))).filter (fun t => orb t = o)).card : ℤ)
      = cntO o ms := by
  set S := prodS (setOf (ms.getD 0 0)) (setOf (ms.getD 1 0)) (setOf (ms.getD 2 0))
    (setOf (ms.getD 3 0)) (setOf (ms.getD 4 0)) (setOf (ms.getD 5 0)) with hS
  set E : ℕ → ℤ := fun ri => ((S.filter (fun t => foT t = PART.getD ri (0, 0, 0, 0, 0, 0))).card : ℤ)
    with hE
  -- the left side by partitions
  have hL : (((sts (setOf (ms.getD 0 0)) (setOf (ms.getD 1 0)) (setOf (ms.getD 2 0))
      (setOf (ms.getD 3 0)) (setOf (ms.getD 4 0)) (setOf (ms.getD 5 0))).filter
        (fun t => orb t = o)).card : ℤ)
      = ∑ ri ∈ range 203, (if (properB (PART.getD ri (0, 0, 0, 0, 0, 0)) &&
          ((orb (PART.getD ri (0, 0, 0, 0, 0, 0)) : ℕ) == (o : ℕ))) = true then 1 else 0) * E ri := by
    rw [sts_eq_filter, ← hS, Finset.filter_filter, Finset.card_filter, Nat.cast_sum]
    have h1 : ∀ t ∈ S, (((if Proper t ∧ orb t = o then 1 else 0 : ℕ)) : ℤ)
        = (fun r => if (properB r && ((orb r : ℕ) == (o : ℕ))) = true then (1 : ℤ) else 0)
          (foT t) := by
      intro t _
      simp only
      rw [orb_congr (samePat_foT t)]
      by_cases hpr : Proper t
      · have hb : properB (foT t) = true := (properB_iff _).mpr ((proper_foT_iff t).mpr hpr)
        by_cases ho : orb t = o
        · simp [hpr, ho, hb]
        · have : ¬ ((orb t : ℕ) = (o : ℕ)) := fun h => ho (Fin.ext h)
          simp [hpr, ho, this]
      · have hb : properB (foT t) = false := by
          rw [Bool.eq_false_iff]; intro h
          exact hpr ((proper_foT_iff t).mp ((properB_iff _).mp h))
        simp [hpr, hb]
    rw [Finset.sum_congr rfl h1,
      sum_by_part S (fun r => if (properB r && ((orb r : ℕ) == (o : ℕ))) = true then (1 : ℤ) else 0)]
  -- each `N_q` by partitions
  have hN : ∀ x ∈ MOBT.getD o [], (Nq x.1 ms : ℤ)
      = ∑ ri ∈ range 203, (if subB x.2.1 (PEL.getD ri []) = true then 1 else 0) * E ri := by
    intro x hx
    obtain ⟨hfo, hpe⟩ := MOBT_ok o o.2 x hx
    rw [← card_const_eq hfo ms, ← hS, Finset.card_filter, Nat.cast_sum]
    have h1 : ∀ t ∈ S, (((if constB x.1 t = true then 1 else 0 : ℕ)) : ℤ)
        = (fun r => if subB x.2.1 (peq r) = true then (1 : ℤ) else 0) (foT t) := by
      intro t _
      simp only [constB, hpe, peq_foT]
      split_ifs <;> simp_all
    rw [Finset.sum_congr rfl h1,
      sum_by_part S (fun r => if subB x.2.1 (peq r) = true then (1 : ℤ) else 0)]
    refine Finset.sum_congr rfl fun ri hri => ?_
    rw [PEL_getD (mem_range.mp hri)]
  rw [hL, cntO]
  have hM : ∀ x ∈ MOBT.getD o [], x.2.2 * (Nq x.1 ms : ℤ)
      = ∑ ri ∈ range 203, x.2.2 * ((if subB x.2.1 (PEL.getD ri []) = true then 1 else 0) * E ri) := by
    intro x hx
    rw [hN x hx, Finset.mul_sum]
  rw [List.map_congr_left hM, list_sum_finset]
  refine Finset.sum_congr rfl fun ri hri => ?_
  have hid := List.all_eq_true.mp (idOK_all o) _ (mem_zip_getD (mem_range.mp hri))
  rw [decide_eq_true_eq] at hid
  simp only at hid
  have : ∀ L : List (T6 × List Bool × ℤ), (L.map fun x => x.2.2 * ((if subB x.2.1 (PEL.getD ri []) = true
      then 1 else 0) * E ri)).sum
      = (L.map fun x => if subB x.2.1 (PEL.getD ri []) then x.2.2 else 0).sum * E ri := by
    intro L
    induction L with
    | nil => simp
    | cons x L ih =>
      simp only [List.map_cons, List.sum_cons, ih, add_mul]
      split_ifs <;> ring
  rw [this, hid]

end GridGen.Six
