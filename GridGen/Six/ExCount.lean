/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.Cone
import GridGen.Six.Pack

/-!
# Height six at `k = 6`: orbit counts for the exact certificates

The exact layer (`GridGen/Six/ExDefs.lean`) needs, at every column type, the orbit counts of
the proper colourings of six lists given by bit masks (`cntO`, `card_orb_setOf`). The kernel
computes them as follows (the packing is in `GridGen/Six/Pack.lean`):

* the intersections of the masks over all `63` sets of rows, by doubling (`atL`: the list for
  rows `< r + 1` is the list for rows `< r` followed by its intersections with mask `r`);
* their sizes, packed four bits each into one natural (`pk`, `lane`, `PT` for the sizes of
  bytes);
* for each of the `203` set partitions `q`, `N_q` as the product of the packed sizes of its
  blocks (`nvq`, `nvq_eq`), times its Möbius coefficients folded into the six cone functionals
  (the five rays and the lower edge of `Q`), positive and negative parts packed `96` bits each
  (`MQ6`); the accumulation `accS` holds all twelve lanes (`lanes_fun`).

The intersections are also computed by doubling on one packed natural (`dblT_eq`, `tabF`), which
is what the kernel runs (`GridGen/Six/ExDefs.lean`).

The data (`MQ6`, `MQC`) are tied to the Möbius table `MOBT` of `GridGen/Six/PartData.lean` by
kernel checks (`el_ok`, `lane_bound`, `mqc_ok`).
-/

namespace GridGen.Six

open Finset

/-! ### The Möbius data -/

/-- The coefficient of orbit `o` at an entry. -/
def mqc (o : ℕ) (c : List ℕ × List ℕ) : ℤ := (c.1.getD o 0 : ℤ) - c.2.getD o 0

/-- The six cone functionals: the five rays and the lower edge of `Q`. -/
def FUN : List (List ℕ) := FL.take 5 ++ [qLL]

/-- `Σₒ aₒ bₒ`. -/
def dotZ (a b : List ℕ) : ℕ := (List.zipWith (· * ·) a b).sum

/-- The twelve lanes of an entry: positive, then negative parts of the six functionals of its
coefficients. -/
def lanesOf (c : List ℕ × List ℕ) : List ℕ :=
  FUN.map (fun F => dotZ c.1 F - dotZ c.2 F) ++ FUN.map (fun F => dotZ c.2 F - dotZ c.1 F)

/-- The partitions with their coefficients and packed data. -/
def EL : List ((T6 × List Bool) × ((List ℕ × List ℕ) × (List ℕ × ℕ))) :=
  (PART.zip PEL).zip (MQC.zip MQ6)

/-- An entry is consistent: its blocks, the lengths, and its packed lanes. -/
def entOK (e : (T6 × List Bool) × ((List ℕ × List ℕ) × (List ℕ × ℕ))) : Bool :=
  decide (e.2.2.1 = bms e.1.1 ∧ e.2.1.1.length = 32 ∧ e.2.1.2.length = 32 ∧
    e.2.2.2 = pk 96 (lanesOf e.2.1))

theorem el_ok : EL.map (fun e => e.2.2) = MQ6 ∧ EL.all entOK = true := by decide +kernel

/-- The lane sums stay below `2⁹⁶` for counts at most `8⁶`. -/
theorem lane_bound : ∀ i < 12, ((EL.map fun e => (lanesOf e.2.1).getD i 0).sum) * 262144
    < 2 ^ 96 := by decide +kernel

theorem fun_len : FUN.length = 6 ∧ ∀ F ∈ FUN, F.length = 32 := by decide +kernel

/-- The Möbius table from the coefficients. -/
def mobOf (o : ℕ) : List (T6 × List Bool × ℤ) :=
  EL.filterMap fun e => if mqc o e.2.1 = 0 then none else some (e.1.1, e.1.2, mqc o e.2.1)

/-- A Möbius entry with its column written as a list. -/
def entL (x : T6 × List Bool × ℤ) : List ℕ × List Bool × ℤ :=
  ([x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1, x.1.2.2.2.2.1, x.1.2.2.2.2.2], x.2.1, x.2.2)

theorem entL_inj : Function.Injective entL := by
  rintro ⟨⟨a1, a2, a3, a4, a5, a6⟩, b, c⟩ ⟨⟨a1', a2', a3', a4', a5', a6'⟩, b', c'⟩ h
  simp only [entL, Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩ := h
  rfl

theorem mqc_ok0 : (List.range 16).all
    (fun o => decide ((MOBT.getD o []).map entL = (mobOf o).map entL)) = true := by
  decide +kernel

theorem mqc_ok1 : ((List.range 16).map (· + 16)).all
    (fun o => decide ((MOBT.getD o []).map entL = (mobOf o).map entL)) = true := by
  decide +kernel

theorem mqc_ok {o : ℕ} (ho : o < 32) : MOBT.getD o [] = mobOf o := by
  apply List.map_injective_iff.mpr entL_inj
  rcases Nat.lt_or_ge o 16 with h | h
  · have := List.all_eq_true.mp mqc_ok0 o (List.mem_range.mpr h)
    simpa using this
  · have := List.all_eq_true.mp mqc_ok1 o (List.mem_map.mpr ⟨o - 16, List.mem_range.mpr (by omega),
      by omega⟩)
    simpa using this

theorem sum_filterMap_mob (o : ℕ) (ms : List ℕ) :
    ∀ E : List ((T6 × List Bool) × ((List ℕ × List ℕ) × (List ℕ × ℕ))),
    ((E.filterMap fun e => if mqc o e.2.1 = 0 then none else some (e.1.1, e.1.2, mqc o e.2.1)).map
        fun x => x.2.2 * (Nq x.1 ms : ℤ)).sum
      = (E.map fun e => mqc o e.2.1 * (Nq e.1.1 ms : ℤ)).sum
  | [] => rfl
  | e :: E => by
    rw [List.filterMap_cons, List.map_cons, List.sum_cons, ← sum_filterMap_mob o ms E]
    split_ifs with h
    · simp [h]
    · simp

/-- **The orbit counts from the coefficients.** -/
theorem cntO_eq_mqc (ms : List ℕ) {o : ℕ} (ho : o < 32) :
    cntO o ms = (EL.map fun e => mqc o e.2.1 * (Nq e.1.1 ms : ℤ)).sum := by
  rw [cntO, mqc_ok ho, mobOf, sum_filterMap_mob]

theorem sum_map_sub_int {α : Type*} (f g : α → ℤ) : ∀ L : List α,
    (L.map f).sum - (L.map g).sum = (L.map fun x => f x - g x).sum
  | [] => by simp
  | x :: L => by
    simp only [List.map_cons, List.sum_cons, ← sum_map_sub_int f g L]
    ring

theorem card_prodS_le (A B C D E F : ℕ) :
    (prodS (setOf A) (setOf B) (setOf C) (setOf D) (setOf E) (setOf F)).card ≤ 262144 := by
  have h8 : ∀ m, (setOf m).card ≤ 8 := fun m => by
    unfold setOf; exact (Finset.card_filter_le _ _).trans (by simp)
  simp only [prodS, Finset.card_product]
  have := Nat.mul_le_mul (h8 A) (Nat.mul_le_mul (h8 B) (Nat.mul_le_mul (h8 C)
    (Nat.mul_le_mul (h8 D) (Nat.mul_le_mul (h8 E) (h8 F)))))
  simpa using this

theorem Nq_le (ms : List ℕ) {q : T6} (hq : foT q = q) : Nq q ms ≤ 262144 := by
  rw [← card_const_eq hq]
  exact (Finset.card_filter_le _ _).trans (card_prodS_le _ _ _ _ _ _)

theorem foT_EL : ∀ e ∈ EL, foT e.1.1 = e.1.1 := by
  intro e he
  have h1 : e.1 ∈ PART.zip PEL := (List.of_mem_zip he).1
  exact foT_of_mem_PART (List.of_mem_zip h1).1

theorem dotZ_eq : ∀ (a b : List ℕ), a.length = 32 → b.length = 32 →
    dotZ a b = ∑ o : Fin 32, a.getD o 0 * b.getD o 0 := by
  intro a b ha hb
  rw [Fin.sum_univ_eq_sum_range (fun o => a.getD o 0 * b.getD o 0)]
  unfold dotZ
  have key : ∀ (a b : List ℕ) (n : ℕ), a.length = n → b.length = n →
      (List.zipWith (· * ·) a b).sum = ∑ o ∈ Finset.range n, a.getD o 0 * b.getD o 0 := by
    intro a b n
    induction a generalizing b n with
    | nil => intro h _; subst h; simp
    | cons x a ih =>
      intro h1 h2
      cases b with
      | nil => simp at h1 h2; omega
      | cons y b =>
        cases n with
        | zero => simp at h1
        | succ n =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
          rw [List.zipWith_cons_cons, List.sum_cons, ih b n h1 h2, Finset.sum_range_succ']
          simp [add_comm]
  exact key a b 32 ha hb

/-- **The six functionals of the orbit counts in lanes.** For `d < 6`, lane `d` minus lane
`6 + d` of `accS (itab ms) MQ6` is `Σₒ cntO o ms · Fₒ` for the functional `F = FUN[d]`. -/
theorem lanes_fun (ms : List ℕ) {d : ℕ} (hd : d < 6) :
    ((lane 96 (accS (itab ms) MQ6) d : ℕ) : ℤ) - (lane 96 (accS (itab ms) MQ6) (6 + d) : ℕ)
      = ∑ o : Fin 32, cntO o ms * ((FUN.getD d []).getD o 0 : ℕ) := by
  obtain ⟨hE, hok⟩ := el_ok
  have hok' : ∀ e ∈ EL, entOK e = true := List.all_eq_true.mp hok
  have hent : ∀ e ∈ EL, e.2.2.1 = bms e.1.1 ∧ e.2.1.1.length = 32 ∧ e.2.1.2.length = 32 ∧
      e.2.2.2 = pk 96 (lanesOf e.2.1) := fun e he => by
    have := hok' e he; simpa only [entOK, decide_eq_true_eq] using this
  have hlen : ∀ e ∈ EL, (lanesOf e.2.1).length = 12 := fun e _ => by
    simp [lanesOf, fun_len.1]
  -- the accumulation as packed lane sums
  have hacc : accS (itab ms) MQ6
      = pkF 96 (fun i => (EL.map fun e => Nq e.1.1 ms * (lanesOf e.2.1).getD i 0).sum) 12 := by
    rw [← hE]
    have : ∀ E : List ((T6 × List Bool) × ((List ℕ × List ℕ) × (List ℕ × ℕ))),
        (∀ e ∈ E, e ∈ EL) → accS (itab ms) (E.map fun e => e.2.2)
          = pkF 96 (fun i => (E.map fun e => Nq e.1.1 ms * (lanesOf e.2.1).getD i 0).sum) 12 := by
      intro E hEL
      induction E with
      | nil => simp [accS, pkF_zero]
      | cons e E ih =>
        have he := hent e (hEL e (by simp))
        rw [List.map_cons, accS, ih (fun x hx => hEL x (by simp [hx])), he.2.2.2, nvqF_eq, he.1,
          nvq_eq, pk_eq_pkF, hlen e (hEL e (by simp))]
        show Nq e.1.1 ms * pkF 96 _ 12 + _ = _
        rw [pkF_mul, pkF_add]
        simp
    exact this EL (fun e he => he)
  -- the lanes
  have hlane : ∀ i < 12, lane 96 (accS (itab ms) MQ6) i
      = (EL.map fun e => Nq e.1.1 ms * (lanesOf e.2.1).getD i 0).sum := by
    intro i hi
    rw [hacc, lane_pkF _ hi]
    intro k hk
    calc (EL.map fun e => Nq e.1.1 ms * (lanesOf e.2.1).getD k 0).sum
        ≤ (EL.map fun e => 262144 * (lanesOf e.2.1).getD k 0).sum := by
          apply List.sum_le_sum
          intro e he
          exact Nat.mul_le_mul_right _ (Nq_le ms (foT_EL e he))
      _ = (EL.map fun e => (lanesOf e.2.1).getD k 0).sum * 262144 := by
          rw [mul_comm, List.sum_map_mul_left]
      _ < 2 ^ 96 := lane_bound k hk
  rw [hlane d (by omega), hlane (6 + d) (by omega)]
  -- the functional of the counts, partition by partition
  have hF : (FUN.getD d []).length = 32 := by
    rw [List.getD_eq_getElem _ _ (by rw [fun_len.1]; exact hd)]; exact fun_len.2 _ (List.getElem_mem _)
  rw [Finset.sum_congr rfl (fun o _ => by rw [cntO_eq_mqc ms o.2]), ]
  simp only [Nat.cast_list_sum, List.map_map]
  rw [sum_map_sub_int]
  simp only [Function.comp_apply]
  have : ∀ e ∈ EL, ((Nq e.1.1 ms * (lanesOf e.2.1).getD d 0 : ℕ) : ℤ)
      - ((Nq e.1.1 ms * (lanesOf e.2.1).getD (6 + d) 0 : ℕ) : ℤ)
      = ∑ o : Fin 32, mqc o e.2.1 * (Nq e.1.1 ms : ℤ) * ((FUN.getD d []).getD o 0 : ℕ) := by
    intro e he
    have h1 := (hent e he).2.1
    have h2 := (hent e he).2.2.1
    have g1 : (lanesOf e.2.1).getD d 0 = dotZ e.2.1.1 (FUN.getD d []) - dotZ e.2.1.2 (FUN.getD d []) := by
      unfold lanesOf
      rw [List.getD_append _ _ _ _ (by simp [fun_len.1]; exact hd), List.getD_eq_getElem _ _
        (by simp [fun_len.1]; exact hd), List.getElem_map, List.getD_eq_getElem _ _
        (by rw [fun_len.1]; exact hd)]
    have g2 : (lanesOf e.2.1).getD (6 + d) 0 = dotZ e.2.1.2 (FUN.getD d []) - dotZ e.2.1.1 (FUN.getD d []) := by
      unfold lanesOf
      rw [List.getD_append_right _ _ _ _ (by simp [fun_len.1]), List.getD_eq_getElem _ _
        (by simp [fun_len.1]; omega)]
      simp only [List.getElem_map, List.length_map, fun_len.1, show 6 + d - 6 = d by omega]
      rw [List.getD_eq_getElem _ _ (by rw [fun_len.1]; exact hd)]
    rw [g1, g2]
    have e1 : (((dotZ e.2.1.1 (FUN.getD d []) - dotZ e.2.1.2 (FUN.getD d []) : ℕ) : ℤ)
        - ((dotZ e.2.1.2 (FUN.getD d []) - dotZ e.2.1.1 (FUN.getD d []) : ℕ) : ℤ))
        = (dotZ e.2.1.1 (FUN.getD d []) : ℤ) - dotZ e.2.1.2 (FUN.getD d []) := by omega
    push_cast [Nat.cast_mul]
    rw [← mul_sub, e1, dotZ_eq _ _ h1 hF, dotZ_eq _ _ h2 hF]
    push_cast
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    unfold mqc
    ring
  rw [List.map_congr_left (fun e he => this e he)]
  -- swap the sums
  have swap : ∀ E : List ((T6 × List Bool) × ((List ℕ × List ℕ) × (List ℕ × ℕ))),
      (E.map fun e => ∑ o : Fin 32, mqc o e.2.1 * (Nq e.1.1 ms : ℤ) * ((FUN.getD d []).getD o 0 : ℕ)).sum
        = ∑ o : Fin 32, (E.map fun e => mqc o e.2.1 * (Nq e.1.1 ms : ℤ)).sum
          * ((FUN.getD d []).getD o 0 : ℕ) := by
    intro E
    induction E with
    | nil => simp
    | cons e E ih =>
      rw [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun o _ => ?_
      simp only [List.map_cons, List.sum_cons]
      ring
  exact swap EL

end GridGen.Six
