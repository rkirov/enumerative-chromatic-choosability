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

theorem idOK_0 : (idOK 0 && idOK 1 && idOK 2 && idOK 3) = true := by decide +kernel
theorem idOK_4 : (idOK 4 && idOK 5 && idOK 6 && idOK 7) = true := by decide +kernel
theorem idOK_8 : (idOK 8 && idOK 9 && idOK 10 && idOK 11) = true := by decide +kernel
theorem idOK_12 : (idOK 12 && idOK 13 && idOK 14 && idOK 15) = true := by decide +kernel
theorem idOK_16 : (idOK 16 && idOK 17 && idOK 18 && idOK 19) = true := by decide +kernel
theorem idOK_20 : (idOK 20 && idOK 21 && idOK 22 && idOK 23) = true := by decide +kernel
theorem idOK_24 : (idOK 24 && idOK 25 && idOK 26 && idOK 27) = true := by decide +kernel
theorem idOK_28 : (idOK 28 && idOK 29 && idOK 30 && idOK 31) = true := by decide +kernel

theorem idOK_all (o : Fin 32) : idOK o = true := by
  have h0 := idOK_0; have h1 := idOK_4; have h2 := idOK_8; have h3 := idOK_12
  have h4 := idOK_16; have h5 := idOK_20; have h6 := idOK_24; have h7 := idOK_28
  simp only [Bool.and_eq_true] at h0 h1 h2 h3 h4 h5 h6 h7
  fin_cases o <;> simp_all

/-- The Möbius entries are partitions with their pair equalities. -/
def mobtOK : Bool :=
  (List.range 32).all fun o => (MOBT.getD o []).all fun x => foT x.1 == x.1 && peq x.1 == x.2.1

theorem mobtOK_true : mobtOK = true := by decide +kernel

theorem MOBT_ok : ∀ o < 32, ∀ x ∈ MOBT.getD o [], foT x.1 = x.1 ∧ peq x.1 = x.2.1 := by
  intro o ho x hx
  have h := List.all_eq_true.mp (List.all_eq_true.mp mobtOK_true o (List.mem_range.mpr ho)) x hx
  simpa using h

theorem PEL_length : PEL.length = 203 := by decide +kernel

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
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hf
      simp only [Finset.mem_coe, Fintype.mem_piFinset]
      intro k
      simp only [C, Finset.mem_filter]
      refine ⟨hf.1 k.1, fun i hi => ?_⟩
      have := hf.2 i
      rw [hi] at this
      rw [← this]; exact hf.1 i
    · intro g hg
      simp only [Finset.mem_coe, Fintype.mem_piFinset] at hg
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset]
      refine ⟨fun i => ((Finset.mem_filter.mp (hg ⟨Q i, hQ i⟩)).2 i rfl), fun i => ?_⟩
      congr 1
      exact Subtype.ext (hQ i).symm
    · intro f hf
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hf
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
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_prodS] at ht
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ht.2⟩
    fin_cases i
    exacts [ht.1.1, ht.1.2.1, ht.1.2.2.1, ht.1.2.2.2.1, ht.1.2.2.2.2.1, ht.1.2.2.2.2.2]
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_prodS, toF_ofF]
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
      rw [if_pos hk', if_pos hk, filter_blk hq ms k hk, card_setOf]
    · have hk' : ¬ Qm q hq k = k := fun h => hk (congrArg Fin.val h)
      rw [if_neg hk', if_neg hk]
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
