/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred

/-!
# The twisted full cover of a cycle: counting

Helper material for `Outerplanar/WitnessFour.lean`, which is Step 4 of the outerplanar proof draft
(`ai_research_notes/OUTERPLANAR_PROOF_DRAFT_2026-11-09.md`). The draft is a result of this
repository's 2026-11 AI research collaboration; nothing here is taken from the literature.

Colours are `Fin (r + 2)`, so `k = r + 2`, `q = r + 1`. The *twisted cover* of the cycle on `Fin n`
has the identity matching on every edge `i → i + 1`, `i ≠ n - 1`, and the shift `x ↦ x + 1` on the
closing edge `n - 1 → 0`; `twist n r` is the set of its colourings.

* `wab`, `card_walks`: the number of proper walks with given ends over a set of `r + 2` colours
  (the transfer count), with the closed form `wab_closed`.
* `card_twist`, `card_twist_both`, `card_twist_nozero`, `card_twist_fiber`: the number of
  colourings of the twisted cover, of those vanishing at both `0` and `n - 1`, of those vanishing
  nowhere, and the fact that every colour is used at a vertex equally often.
* `part n r A`: the colourings that are nonzero exactly on `A`, with only the edges inside `A`
  constrained. `peel` removes leaves of the path forest `A` one at a time and compares the count
  with the forest bound `phi`; `peel_both`, `peel_zero`, `peel_last`, `peel_none` are the four
  cases of the comparison in Step 4, and `phi_compl_eq`, `phi_compl_mul` identify `phi` with
  `arcW`.
-/

namespace Outerplanar

open Finset

/-! ### Cyclic arithmetic in `Fin n` -/

section FinArith

variable {n : ℕ} [NeZero n]

theorem fin_val_neg_one : ((-1 : Fin n) : ℕ) = n - 1 := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp [Fin.coe_neg_one]

theorem fin_ne_neg_one_iff {i : Fin n} : i ≠ -1 ↔ (i : ℕ) + 1 < n := by
  rw [Ne, Fin.ext_iff, fin_val_neg_one]
  have := i.isLt
  omega

theorem fin_val_add_one {i : Fin n} (h : i ≠ -1) : ((i + 1 : Fin n) : ℕ) = i + 1 := by
  rw [fin_ne_neg_one_iff] at h
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact Fin.val_add_one_of_lt (Fin.lt_def.2 (by simpa using h))

theorem fin_val_sub_one {i : Fin n} (h : i ≠ 0) : ((i - 1 : Fin n) : ℕ) + 1 = i := by
  have h0 : (i : ℕ) ≠ 0 := fun h' => h (Fin.ext (by simpa using h'))
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [Fin.coe_sub_one, ite_eq_right h]
  omega

end FinArith

/-! ### Proper walks with prescribed ends -/

section Walks

/-- The numbers of proper walks with `j` steps over `r + 2` colours: closed ones first, then
those between two given distinct colours. -/
def wab (r : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | j + 1 => ((r + 1) * (wab r j).2, (wab r j).1 + r * (wab r j).2)

theorem wab_closed (r j : ℕ) :
    ((r : ℝ) + 2) * (wab r j).1 = ((r : ℝ) + 1) ^ j + (-1) ^ j * ((r : ℝ) + 1) ∧
      ((r : ℝ) + 2) * (wab r j).2 = ((r : ℝ) + 1) ^ j - (-1) ^ j := by
  induction j with
  | zero => simp [wab]; ring
  | succ j ih =>
    obtain ⟨ha, hb⟩ := ih
    simp only [wab, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    constructor
    · linear_combination ((r : ℝ) + 1) * hb
    · linear_combination ha + (r : ℝ) * hb

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The walks `g 0, …, g j` in `S` from `c` to `d` whose consecutive entries differ. -/
def walks (S : Finset α) (j : ℕ) (c d : α) : Finset (Fin (j + 1) → α) :=
  univ.filter fun g => (∀ i, g i ∈ S) ∧ (∀ i : Fin j, g i.castSucc ≠ g i.succ) ∧
    g 0 = c ∧ g (Fin.last j) = d

theorem mem_walks {S : Finset α} {j : ℕ} {c d : α} {g : Fin (j + 1) → α} :
    g ∈ walks S j c d ↔ (∀ i, g i ∈ S) ∧ (∀ i : Fin j, g i.castSucc ≠ g i.succ) ∧
      g 0 = c ∧ g (Fin.last j) = d := by
  simp [walks]

theorem card_walks_succ (S : Finset α) (j : ℕ) (c : α) {d : α} (hd : d ∈ S) :
    #(walks S (j + 1) c d) = ∑ e ∈ S.erase d, #(walks S j c e) := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun g : Fin (j + 1 + 1) → α => g (Fin.last j).castSucc) (t := S.erase d)]
  · refine Finset.sum_congr rfl fun e he => ?_
    rw [mem_erase] at he
    refine Finset.card_bij' (fun g _ => Fin.init g) (fun g _ => Fin.snoc g d) ?_ ?_ ?_ ?_
    · intro g hg
      rw [mem_filter, mem_walks] at hg
      obtain ⟨⟨hS, hp, h0, hl⟩, he'⟩ := hg
      rw [mem_walks]
      refine ⟨fun i => hS _, fun i => ?_, h0, he'⟩
      have := hp i.castSucc
      rwa [Fin.succ_castSucc] at this
    · intro g hg
      rw [mem_walks] at hg
      obtain ⟨hS, hp, h0, hl⟩ := hg
      rw [mem_filter, mem_walks]
      refine ⟨⟨fun i => ?_, fun i => ?_, ?_, ?_⟩, ?_⟩
      · induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact hd
        | cast i => rw [Fin.snoc_castSucc]; exact hS i
      · induction i using Fin.lastCases with
        | last =>
          rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hl]; exact he.1
        | cast i =>
          rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]; exact hp i
      · rw [← Fin.castSucc_zero, Fin.snoc_castSucc]; exact h0
      · rw [Fin.snoc_last]
      · show (Fin.snoc g d : Fin (j + 1 + 1) → α) (Fin.last j).castSucc = e
        rw [Fin.snoc_castSucc]; exact hl
    · intro g hg
      rw [mem_filter, mem_walks] at hg
      obtain ⟨⟨hS, hp, h0, hl⟩, he'⟩ := hg
      show (Fin.snoc (Fin.init g) d : Fin (j + 1 + 1) → α) = g
      rw [← hl]; exact Fin.snoc_init_self g
    · intro g hg
      exact Fin.init_snoc _ _
  · intro g hg
    rw [mem_coe, mem_walks] at hg
    obtain ⟨hS, hp, h0, hl⟩ := hg
    rw [mem_coe, mem_erase]
    refine ⟨?_, hS _⟩
    have := hp (Fin.last j)
    rwa [Fin.succ_last, hl] at this

theorem card_walks (S : Finset α) (r : ℕ) (hS : #S = r + 2) (j : ℕ) {c d : α} (hc : c ∈ S)
    (hd : d ∈ S) : #(walks S j c d) = if c = d then (wab r j).1 else (wab r j).2 := by
  induction j generalizing d with
  | zero =>
    by_cases h : c = d
    · subst h
      rw [ite_eq_left rfl]
      show _ = 1
      rw [Finset.card_eq_one]
      refine ⟨fun _ => c, ?_⟩
      ext g
      rw [mem_walks, mem_singleton]
      constructor
      · rintro ⟨_, _, h0, _⟩
        funext i
        rw [Fin.fin_one_eq_zero i]; exact h0
      · rintro rfl; exact ⟨fun _ => hc, fun i => i.elim0, rfl, rfl⟩
    · rw [ite_eq_right h]
      show _ = 0
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro g hg
      rw [mem_walks] at hg
      exact h (hg.2.2.1.symm.trans hg.2.2.2)
  | succ j ih =>
    rw [card_walks_succ S j c hd]
    have hcard : #(S.erase d) = r + 1 := by rw [card_erase_of_mem hd, hS]; rfl
    by_cases h : c = d
    · subst h
      rw [ite_eq_left rfl]
      rw [Finset.sum_congr rfl (g := fun _ => (wab r j).2)]
      · rw [sum_const, hcard, smul_eq_mul]; rfl
      · intro e he
        rw [mem_erase] at he
        rw [ih he.2, ite_eq_right he.1.symm]
    · rw [ite_eq_right h]
      have hc' : c ∈ S.erase d := mem_erase.2 ⟨h, hc⟩
      rw [← Finset.add_sum_erase _ _ hc', ih hc, ite_eq_left rfl]
      rw [Finset.sum_congr rfl (g := fun _ => (wab r j).2)]
      · rw [sum_const, card_erase_of_mem hc', hcard, smul_eq_mul]; rfl
      · intro e he
        rw [mem_erase, mem_erase] at he
        rw [ih he.2.2, ite_eq_right he.1.symm]

end Walks

section Cyc

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem walks_eq_empty_left {S : Finset α} {j : ℕ} {c d : α} (hc : c ∉ S) :
    walks S j c d = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro g hg
  rw [mem_walks] at hg
  exact hc (hg.2.2.1 ▸ hg.1 0)

theorem walks_eq_empty_right {S : Finset α} {j : ℕ} {c d : α} (hd : d ∉ S) :
    walks S j c d = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro g hg
  rw [mem_walks] at hg
  exact hd (hg.2.2.2 ▸ hg.1 _)

/-- Colourings of the path `0, …, n - 1` in `S` with a condition on the pair of end colours,
counted through the walks. -/
theorem card_cyc {n : ℕ} [NeZero n] (S : Finset α) (R : α → α → Prop) [DecidableRel R] (j : ℕ)
    (hn : n = j + 1) :
    #{f : Fin n → α | (∀ i, f i ∈ S) ∧ (∀ i, i ≠ -1 → f i ≠ f (i + 1)) ∧ R (f 0) (f (-1))} =
      ∑ c, ∑ d, if R c d then #(walks S j c d) else 0 := by
  subst hn
  have hlast : (-1 : Fin (j + 1)) = Fin.last j := Fin.ext (by rw [fin_val_neg_one]; simp)
  have hpath : ∀ f : Fin (j + 1) → α,
      (∀ i, i ≠ -1 → f i ≠ f (i + 1)) ↔ ∀ i : Fin j, f i.castSucc ≠ f i.succ := by
    intro f
    constructor
    · intro h i
      have hi : i.castSucc ≠ -1 := fin_ne_neg_one_iff.2 (by simp)
      have : i.castSucc + 1 = i.succ := Fin.ext (by rw [fin_val_add_one hi]; simp)
      rw [← this]; exact h _ hi
    · intro h i hi
      have hi' := fin_ne_neg_one_iff.1 hi
      have h1 := h ⟨i, by omega⟩
      have e1 : (⟨i, by omega⟩ : Fin j).castSucc = i := Fin.ext rfl
      have e2 : (⟨i, by omega⟩ : Fin j).succ = i + 1 :=
        Fin.ext (by rw [fin_val_add_one hi]; rfl)
      rwa [e1, e2] at h1
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f : Fin (j + 1) → α => (f 0, f (-1)))
    (t := univ) (fun _ _ => mem_coe.2 (mem_univ _)), Fintype.sum_prod_type]
  refine sum_congr rfl fun c _ => sum_congr rfl fun d _ => ?_
  split_ifs with hR
  · congr 1
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_walks, Prod.mk.injEq, hpath]
    rw [hlast]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩; exact ⟨h1, h2, h4, h5⟩
    · rintro ⟨h1, h2, h4, h5⟩; exact ⟨⟨h1, h2, by rw [h4, h5]; exact hR⟩, h4, h5⟩
  · rw [card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro f hf
    simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq] at hf
    obtain ⟨⟨_, _, h3⟩, h4, h5⟩ := hf
    rw [h4, h5] at h3
    exact hR h3

end Cyc

/-! ### The twisted full cover -/

section Twist

variable {n : ℕ} [NeZero n] {r : ℕ}

/-- The colourings of the full `(r + 2)`-fold cover of the cycle on `Fin n` whose matchings are
the identity on every edge except `n - 1 → 0`, where it is the shift by one. -/
def twist (n r : ℕ) [NeZero n] : Finset (Fin n → Fin (r + 2)) :=
  univ.filter fun f => (∀ i, i ≠ -1 → f i ≠ f (i + 1)) ∧ f 0 ≠ f (-1) + 1

theorem mem_twist {f : Fin n → Fin (r + 2)} :
    f ∈ twist n r ↔ (∀ i, i ≠ -1 → f i ≠ f (i + 1)) ∧ f 0 ≠ f (-1) + 1 := by
  simp [twist]

theorem fin_ne_sub_one (c : Fin (r + 2)) : c ≠ c - 1 := by
  intro h
  exact absurd (Fin.one_eq_zero_iff.1 (sub_eq_self.1 h.symm)) (by omega)

theorem filter_ne_add_one (S : Finset (Fin (r + 2))) (c : Fin (r + 2)) :
    S.filter (fun d => c ≠ d + 1) = S.erase (c - 1) := by
  ext d
  rw [mem_filter, mem_erase, and_comm, ne_eq, ne_eq, eq_sub_iff_add_eq, eq_comm]

theorem sum_twist_inner (a b : ℕ) (c : Fin (r + 2)) :
    (∑ d : Fin (r + 2), if c ≠ d + 1 then (if c = d then a else b) else 0) = a + r * b := by
  rw [← Finset.sum_filter, filter_ne_add_one]
  have hc : c ∈ (univ : Finset (Fin (r + 2))).erase (c - 1) :=
    mem_erase.2 ⟨fin_ne_sub_one c, mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ hc, ite_eq_left rfl]
  rw [Finset.sum_congr rfl (g := fun _ => b)]
  · rw [sum_const, card_erase_of_mem hc, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin, smul_eq_mul]
    rfl
  · intro e he
    rw [mem_erase] at he
    rw [ite_eq_right he.1.symm]

theorem card_walks_univ (j : ℕ) (c d : Fin (r + 2)) :
    #(walks (univ : Finset (Fin (r + 2))) j c d) = if c = d then (wab r j).1 else (wab r j).2 :=
  card_walks univ r (by rw [card_univ, Fintype.card_fin]) j (mem_univ _) (mem_univ _)

theorem card_twist {j : ℕ} (hn : n = j + 1) :
    #(twist n r) = (r + 2) * ((wab r j).1 + r * (wab r j).2) := by
  have h : twist n r = univ.filter fun f : Fin n → Fin (r + 2) =>
      (∀ i, f i ∈ (univ : Finset (Fin (r + 2)))) ∧ (∀ i, i ≠ -1 → f i ≠ f (i + 1)) ∧
        (fun c d => c ≠ d + 1) (f 0) (f (-1)) := by
    ext f; simp [twist]
  rw [h]
  refine (card_cyc univ (fun c d => c ≠ d + 1) j hn).trans ?_
  simp only [card_walks_univ, sum_twist_inner, sum_const,
    card_univ, Fintype.card_fin, smul_eq_mul]

theorem card_twist_both {j : ℕ} (hn : n = j + 1) :
    #{f ∈ twist n r | f 0 = 0 ∧ f (-1) = 0} = (wab r j).1 := by
  have h : {f ∈ twist n r | f 0 = 0 ∧ f (-1) = 0} = univ.filter fun f : Fin n → Fin (r + 2) =>
      (∀ i, f i ∈ (univ : Finset (Fin (r + 2)))) ∧ (∀ i, i ≠ -1 → f i ≠ f (i + 1)) ∧
        (fun c d => c = 0 ∧ d = 0) (f 0) (f (-1)) := by
    ext f
    simp only [mem_filter, mem_twist, mem_univ, true_and, implies_true]
    constructor
    · rintro ⟨⟨hp, -⟩, h0⟩; exact ⟨hp, h0⟩
    · rintro ⟨hp, h0, h1⟩
      refine ⟨⟨hp, ?_⟩, h0, h1⟩
      rw [h0, h1, zero_add]; exact zero_ne_one
  rw [h]
  refine (card_cyc univ (fun c d => c = 0 ∧ d = 0) j hn).trans ?_
  rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0]
  · rw [ite_eq_left ⟨rfl, rfl⟩, card_walks_univ,
      ite_eq_left rfl]
  · intro d _ hd; rw [ite_eq_right]; exact fun h => hd h.2
  · intro h; exact absurd (mem_univ _) h
  · intro c _ hc
    exact Finset.sum_eq_zero fun d _ => by rw [ite_eq_right]; exact fun h => hc h.1
  · intro h; exact absurd (mem_univ _) h

theorem card_twist_fiber (i : Fin n) : (r + 2) * #{f ∈ twist n r | f i = 0} = #(twist n r) := by
  have hfib : ∀ c : Fin (r + 2), #{f ∈ twist n r | f i = c} = #{f ∈ twist n r | f i = 0} := by
    intro c
    refine Finset.card_bij' (fun f _ => fun x => f x - c) (fun f _ => fun x => f x + c)
      ?_ ?_ ?_ ?_
    · intro f hf
      rw [mem_filter, mem_twist] at hf ⊢
      obtain ⟨⟨hp, hc⟩, hi⟩ := hf
      refine ⟨⟨fun x hx h => hp x hx (sub_left_injective h), fun h => hc ?_⟩, ?_⟩
      · rw [sub_add_eq_add_sub] at h; exact sub_left_injective h
      · show f i - c = 0
        rw [hi, sub_self]
    · intro f hf
      rw [mem_filter, mem_twist] at hf ⊢
      obtain ⟨⟨hp, hc⟩, hi⟩ := hf
      refine ⟨⟨fun x hx h => hp x hx (add_left_injective _ h), fun h => hc ?_⟩, ?_⟩
      · rw [add_right_comm] at h; exact add_left_injective _ h
      · show f i + c = c
        rw [hi, zero_add]
    · intro f _; funext x; exact sub_add_cancel _ _
    · intro f _; funext x; exact add_sub_cancel_right _ _
  rw [Finset.card_eq_sum_card_fiberwise (s := twist n r) (f := fun f => f i) (t := univ)
    (fun _ _ => mem_coe.2 (mem_univ _))]
  simp only [hfib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

theorem sum_nozero_inner (s a b : ℕ) {c : Fin (s + 1 + 2)} (hc : c ≠ 0) :
    (∑ d ∈ (univ : Finset (Fin (s + 1 + 2))).erase 0,
      if c ≠ d + 1 then (if c = d then a else b) else 0) =
      (a + s * b) + if c = 1 then b else 0 := by
  rw [← Finset.sum_filter, filter_ne_add_one]
  have hc' : c ∈ ((univ : Finset (Fin (s + 1 + 2))).erase 0).erase (c - 1) :=
    mem_erase.2 ⟨fin_ne_sub_one c, mem_erase.2 ⟨hc, mem_univ _⟩⟩
  rw [← Finset.add_sum_erase _ _ hc', ite_eq_left rfl]
  rw [Finset.sum_congr rfl (g := fun _ => b)]
  · rw [sum_const, card_erase_of_mem hc', smul_eq_mul]
    by_cases h1 : c = 1
    · have h0 : c - 1 ∉ (univ : Finset (Fin (s + 1 + 2))).erase 0 := by
        rw [h1, sub_self]; exact notMem_erase _ _
      rw [erase_eq_of_notMem h0, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
        ite_eq_left h1]
      show a + (s + 1) * b = a + s * b + b
      ring
    · have h0 : c - 1 ∈ (univ : Finset (Fin (s + 1 + 2))).erase 0 :=
        mem_erase.2 ⟨fun h => h1 (sub_eq_zero.1 h), mem_univ _⟩
      rw [card_erase_of_mem h0, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
        ite_eq_right h1]
      rfl
  · intro e he
    rw [mem_erase] at he
    rw [ite_eq_right he.1.symm]

theorem card_twist_nozero {j : ℕ} (hn : n = j + 1) (s : ℕ) :
    #{f ∈ twist n (s + 1) | ∀ i, f i ≠ 0} =
      (s + 2) * ((wab s j).1 + s * (wab s j).2) + (wab s j).2 := by
  have h : {f ∈ twist n (s + 1) | ∀ i, f i ≠ 0} = univ.filter fun f : Fin n → Fin (s + 1 + 2) =>
      (∀ i, f i ∈ (univ : Finset (Fin (s + 1 + 2))).erase 0) ∧
        (∀ i, i ≠ -1 → f i ≠ f (i + 1)) ∧ (fun c d => c ≠ d + 1) (f 0) (f (-1)) := by
    ext f
    simp only [mem_filter, mem_twist, mem_univ, true_and, mem_erase, and_true]
    tauto
  have hS : #((univ : Finset (Fin (s + 1 + 2))).erase 0) = s + 2 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; rfl
  rw [h]
  refine (card_cyc _ (fun c d => c ≠ d + 1) j hn).trans ?_
  rw [← Finset.sum_erase univ (a := 0)]
  · rw [Finset.sum_congr rfl (g := fun c => ((wab s j).1 + s * (wab s j).2) +
      if c = 1 then (wab s j).2 else 0)]
    · rw [sum_add_distrib, sum_const, hS, smul_eq_mul, Finset.sum_ite_eq',
        ite_eq_left (mem_erase.2
          ⟨fun h => absurd (Fin.one_eq_zero_iff.1 h) (by omega), mem_univ _⟩)]
    · intro c hc
      rw [← Finset.sum_erase univ (a := 0)]
      · rw [← sum_nozero_inner s _ _ (mem_erase.1 hc).1]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [card_walks _ s hS j hc hd]
      · rw [walks_eq_empty_right (notMem_erase _ _), card_empty, ite_self]
  · exact Finset.sum_eq_zero fun d _ => by
      rw [walks_eq_empty_left (notMem_erase _ _), card_empty, ite_self]

end Twist

section Peel

variable {n : ℕ} [NeZero n] {r : ℕ}

/-- The colourings of the twisted cover restricted to the active set `A`: nonzero on `A`, zero
off it, and only the path edges inside `A` and the closing edge are constrained. -/
def part (n r : ℕ) [NeZero n] (A : Finset (Fin n)) : Finset (Fin n → Fin (r + 2)) :=
  univ.filter fun f => (∀ i, i ∉ A → f i = 0) ∧ (∀ i, i ∈ A → f i ≠ 0) ∧
    (∀ i, i ≠ -1 → i ∈ A → i + 1 ∈ A → f i ≠ f (i + 1)) ∧ f 0 ≠ f (-1) + 1

theorem mem_part {A : Finset (Fin n)} {f : Fin n → Fin (r + 2)} :
    f ∈ part n r A ↔ (∀ i, i ∉ A → f i = 0) ∧ (∀ i, i ∈ A → f i ≠ 0) ∧
      (∀ i, i ≠ -1 → i ∈ A → i + 1 ∈ A → f i ≠ f (i + 1)) ∧ f 0 ≠ f (-1) + 1 := by
  simp [part]

/-- The bound for a forest of paths: `r + 1` for the first vertex of a path, `r` for the others.
The closing edge does not count. -/
def phi (r : ℕ) (A : Finset (Fin n)) : ℕ := ∏ i ∈ A, if i ≠ 0 ∧ i - 1 ∈ A then r else r + 1

theorem fin_sub_one_ne {i : Fin n} (h0 : i ≠ 0) : i - 1 ≠ i := by
  intro h
  have := fin_val_sub_one h0
  rw [h] at this
  omega

theorem fin_add_one_ne {i : Fin n} (h1 : i ≠ -1) : i + 1 ≠ i := by
  intro h
  have := fin_val_add_one h1
  rw [h] at this
  omega

theorem fin_add_one_ne_zero {i : Fin n} (h1 : i ≠ -1) : i + 1 ≠ 0 := by
  intro h
  have := fin_val_add_one h1
  rw [h] at this
  simp at this

theorem card_part_le_aux {A : Finset (Fin n)} {i : Fin n} (h0 : i ≠ 0) (h1 : i ≠ -1) (c : ℕ)
    (T : (Fin n → Fin (r + 2)) → Finset (Fin (r + 2)))
    (hT : ∀ f ∈ part n r (A.erase i), #(T f) ≤ c)
    (hmem : ∀ g ∈ part n r A, g i ∈ T (Function.update g i 0)) :
    #(part n r A) ≤ c * #(part n r (A.erase i)) := by
  refine Finset.card_le_mul_card_image_of_maps_to (f := fun g => Function.update g i 0) ?_ c ?_
  · intro g hg
    rw [mem_part] at hg ⊢
    obtain ⟨hz, hnz, hp, hc⟩ := hg
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx1 hx hx' => ?_, ?_⟩
    · by_cases hxi : x = i
      · rw [hxi, Function.update_self]
      · rw [Function.update_of_ne hxi]
        exact hz x fun hxA => hx (mem_erase.2 ⟨hxi, hxA⟩)
    · rw [mem_erase] at hx
      rw [Function.update_of_ne hx.1]; exact hnz x hx.2
    · rw [mem_erase] at hx hx'
      rw [Function.update_of_ne hx.1, Function.update_of_ne hx'.1]
      exact hp x hx1 hx.2 hx'.2
    · rw [Function.update_of_ne (Ne.symm h0), Function.update_of_ne (Ne.symm h1)]
      exact hc
  · intro f hf
    refine Finset.card_le_card_of_injOn (fun g => g i) ?_ ?_ |>.trans (hT f hf)
    · intro g hg
      rw [mem_coe, mem_filter] at hg
      rw [mem_coe, ← hg.2]
      exact hmem g hg.1
    · intro g₁ hg₁ g₂ hg₂ h
      rw [mem_coe, mem_filter] at hg₁ hg₂
      funext x
      by_cases hxi : x = i
      · rw [hxi]; exact h
      · have := congrFun (hg₁.2.trans hg₂.2.symm) x
        rwa [Function.update_of_ne hxi, Function.update_of_ne hxi] at this

theorem card_erase_zero_erase {x : Fin (r + 2)} (hx : x ≠ 0) :
    #(((univ : Finset (Fin (r + 2))).erase 0).erase x) = r := by
  rw [card_erase_of_mem (mem_erase.2 ⟨hx, mem_univ _⟩), card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fin]
  rfl

theorem card_part_le_free {A : Finset (Fin n)} {i : Fin n} (hi : i ∈ A) (h0 : i ≠ 0)
    (h1 : i ≠ -1) : #(part n r A) ≤ (r + 1) * #(part n r (A.erase i)) := by
  refine card_part_le_aux h0 h1 _ (fun _ => (univ : Finset (Fin (r + 2))).erase 0) ?_ ?_
  · intro f _
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; rfl
  · intro g hg
    exact mem_erase.2 ⟨(mem_part.1 hg).2.1 i hi, mem_univ _⟩

theorem card_part_le_pred {A : Finset (Fin n)} {i : Fin n} (hi : i ∈ A) (h0 : i ≠ 0)
    (h1 : i ≠ -1) (hp : i - 1 ∈ A) : #(part n r A) ≤ r * #(part n r (A.erase i)) := by
  refine card_part_le_aux h0 h1 _
    (fun f => ((univ : Finset (Fin (r + 2))).erase 0).erase (f (i - 1))) ?_ ?_
  · intro f hf
    exact (card_erase_zero_erase ((mem_part.1 hf).2.1 _
      (mem_erase.2 ⟨fin_sub_one_ne h0, hp⟩))).le
  · intro g hg
    have hg' := mem_part.1 hg
    have hne : i - 1 ≠ -1 := fun h => h0 (by rw [← sub_add_cancel i 1, h]; simp)
    have := hg'.2.2.1 (i - 1) hne hp (by rw [sub_add_cancel]; exact hi)
    rw [sub_add_cancel] at this
    rw [Function.update_of_ne (fin_sub_one_ne h0)]
    exact mem_erase.2 ⟨this.symm, mem_erase.2 ⟨hg'.2.1 i hi, mem_univ _⟩⟩

theorem card_part_le_succ {A : Finset (Fin n)} {i : Fin n} (hi : i ∈ A) (h0 : i ≠ 0)
    (h1 : i ≠ -1) (hs : i + 1 ∈ A) : #(part n r A) ≤ r * #(part n r (A.erase i)) := by
  refine card_part_le_aux h0 h1 _
    (fun f => ((univ : Finset (Fin (r + 2))).erase 0).erase (f (i + 1))) ?_ ?_
  · intro f hf
    exact (card_erase_zero_erase ((mem_part.1 hf).2.1 _
      (mem_erase.2 ⟨fin_add_one_ne h1, hs⟩))).le
  · intro g hg
    have hg' := mem_part.1 hg
    have := hg'.2.2.1 i h1 hi hs
    rw [Function.update_of_ne (fin_add_one_ne h1)]
    exact mem_erase.2 ⟨this, mem_erase.2 ⟨hg'.2.1 i hi, mem_univ _⟩⟩

theorem phi_erase {A : Finset (Fin n)} {i : Fin n} (hi : i ∈ A) (h1 : i ≠ -1)
    (hleaf : ¬(i - 1 ∈ A ∧ i + 1 ∈ A)) :
    phi r A = (if i ≠ 0 ∧ i - 1 ∈ A ∨ i + 1 ∈ A then r else r + 1) * phi r (A.erase i) := by
  unfold phi
  rw [← Finset.mul_prod_erase A _ hi]
  by_cases hs : i + 1 ∈ A
  · have hp : i - 1 ∉ A := fun hp => hleaf ⟨hp, hs⟩
    have hs' : i + 1 ∈ A.erase i := mem_erase.2 ⟨fin_add_one_ne h1, hs⟩
    rw [← Finset.mul_prod_erase (A.erase i) _ hs', ← Finset.mul_prod_erase (A.erase i) _ hs']
    have hP : ∏ x ∈ (A.erase i).erase (i + 1), (if x ≠ 0 ∧ x - 1 ∈ A then r else r + 1) =
        ∏ x ∈ (A.erase i).erase (i + 1), (if x ≠ 0 ∧ x - 1 ∈ A.erase i then r else r + 1) := by
      refine Finset.prod_congr rfl fun x hx => ?_
      have hx1 : x - 1 ≠ i := fun h => (mem_erase.1 hx).1 (by rw [← h, sub_add_cancel])
      simp only [mem_erase, hx1, ne_eq, not_false_eq_true, true_and]
    rw [hP, ite_eq_right (fun h => hp h.2), ite_eq_left (Or.inr hs),
      ite_eq_left ⟨fin_add_one_ne_zero h1, by rw [add_sub_cancel_right]; exact hi⟩,
      ite_eq_right (fun h => by
        rw [add_sub_cancel_right] at h; exact notMem_erase _ _ h.2)]
    ring
  · have hP : ∏ x ∈ A.erase i, (if x ≠ 0 ∧ x - 1 ∈ A then r else r + 1) =
        ∏ x ∈ A.erase i, (if x ≠ 0 ∧ x - 1 ∈ A.erase i then r else r + 1) := by
      refine Finset.prod_congr rfl fun x hx => ?_
      have hx1 : x - 1 ≠ i := fun h => hs (by rw [← h, sub_add_cancel]; exact (mem_erase.1 hx).2)
      simp only [mem_erase, hx1, ne_eq, not_false_eq_true, true_and]
    rw [hP]
    simp only [hs, or_false]

/-- Peeling leaves: if every set between `K` and `A` other than `K` has a leaf outside `K`
(not `0` or `-1`), then the ratio of the count to the forest bound only grows towards `K`. -/
theorem peel (K : Finset (Fin n)) (A : Finset (Fin n)) (hKA : K ⊆ A)
    (hleaf : ∀ B, K ⊆ B → B ⊆ A → B ≠ K →
      ∃ i ∈ B, i ∉ K ∧ i ≠ 0 ∧ i ≠ -1 ∧ ¬(i - 1 ∈ B ∧ i + 1 ∈ B)) :
    #(part n r A) * phi r K ≤ #(part n r K) * phi r A := by
  induction A using Finset.strongInduction with
  | H A ih =>
    by_cases hAK : A = K
    · rw [hAK]
    obtain ⟨i, hiA, hiK, h0, h1, hl⟩ := hleaf A hKA subset_rfl hAK
    have hIH := ih (A.erase i) (erase_ssubset hiA) (subset_erase.2 ⟨hKA, hiK⟩)
      (fun B hKB hBA => hleaf B hKB (hBA.trans (erase_subset _ _)))
    have hphi := phi_erase (r := r) hiA h1 hl
    have hcard : #(part n r A) ≤
        (if i ≠ 0 ∧ i - 1 ∈ A ∨ i + 1 ∈ A then r else r + 1) * #(part n r (A.erase i)) := by
      by_cases hp : i - 1 ∈ A
      · rw [ite_eq_left (Or.inl ⟨h0, hp⟩)]; exact card_part_le_pred hiA h0 h1 hp
      · by_cases hs : i + 1 ∈ A
        · rw [ite_eq_left (Or.inr hs)]; exact card_part_le_succ hiA h0 h1 hs
        · rw [ite_eq_right (fun h => h.elim (fun h => hp h.2) hs)]
          exact card_part_le_free hiA h0 h1
    rw [hphi]
    calc #(part n r A) * phi r K
        ≤ (if i ≠ 0 ∧ i - 1 ∈ A ∨ i + 1 ∈ A then r else r + 1) * #(part n r (A.erase i)) *
            phi r K := Nat.mul_le_mul_right _ hcard
      _ = (if i ≠ 0 ∧ i - 1 ∈ A ∨ i + 1 ∈ A then r else r + 1) *
            (#(part n r (A.erase i)) * phi r K) := by ring
      _ ≤ (if i ≠ 0 ∧ i - 1 ∈ A ∨ i + 1 ∈ A then r else r + 1) *
            (#(part n r K) * phi r (A.erase i)) := Nat.mul_le_mul_left _ hIH
      _ = _ := by ring

end Peel

section Bounds

variable {n : ℕ} [NeZero n] {r : ℕ}

theorem fin_neg_one_ne_zero (hn : 2 ≤ n) : (-1 : Fin n) ≠ 0 := by
  intro h
  have := fin_val_neg_one (n := n)
  rw [h] at this
  simp at this
  omega

theorem fin_lt_add_one {i : Fin n} (h1 : i ≠ -1) : i < i + 1 := by
  rw [Fin.lt_def, fin_val_add_one h1]; omega

theorem fin_sub_one_lt {i : Fin n} (h0 : i ≠ 0) : i - 1 < i := by
  rw [Fin.lt_def]; have := fin_val_sub_one h0; omega

theorem fin_le_neg_one (i : Fin n) : i ≤ -1 := by
  rw [Fin.le_def, fin_val_neg_one]; have := i.isLt; omega

theorem card_part_empty : #(part n r ∅) ≤ 1 := by
  rw [Finset.card_le_one]
  intro f hf g hg
  funext x
  rw [(mem_part.1 hf).1 x (notMem_empty _), (mem_part.1 hg).1 x (notMem_empty _)]

theorem card_part_zero (hn : 2 ≤ n) : #(part n r ({0} : Finset (Fin n))) ≤ r := by
  have h10 : (1 : Fin (r + 2)) ≠ 0 := fun h => absurd (Fin.one_eq_zero_iff.1 h) (by omega)
  refine (Finset.card_le_card_of_injOn (fun g => g 0) ?_ ?_).trans_eq (card_erase_zero_erase h10)
  · intro g hg
    have hg' := mem_part.1 hg
    have hl : g (-1) = 0 := hg'.1 _ (by rw [mem_singleton]; exact fin_neg_one_ne_zero hn)
    have hc := hg'.2.2.2
    rw [hl, zero_add] at hc
    exact mem_coe.2 (mem_erase.2 ⟨hc, mem_erase.2 ⟨hg'.2.1 0 (mem_singleton_self _), mem_univ _⟩⟩)
  · intro g₁ hg₁ g₂ hg₂ h
    funext x
    by_cases hx : x = 0
    · rw [hx]; exact h
    · rw [(mem_part.1 hg₁).1 x (by rwa [mem_singleton]),
        (mem_part.1 hg₂).1 x (by rwa [mem_singleton])]

theorem card_part_last (hn : 2 ≤ n) : #(part n r ({-1} : Finset (Fin n))) ≤ r := by
  have h10 : (-1 : Fin (r + 2)) ≠ 0 :=
    neg_ne_zero.2 fun h => absurd (Fin.one_eq_zero_iff.1 h) (by omega)
  refine (Finset.card_le_card_of_injOn (fun g => g (-1)) ?_ ?_).trans_eq
    (card_erase_zero_erase h10)
  · intro g hg
    have hg' := mem_part.1 hg
    have hl : g 0 = 0 :=
      hg'.1 _ (by rw [mem_singleton]; exact (fin_neg_one_ne_zero hn).symm)
    have hc := hg'.2.2.2
    rw [hl] at hc
    refine mem_coe.2 (mem_erase.2 ⟨fun (h : g (-1) = -1) => hc ?_, mem_erase.2
      ⟨hg'.2.1 _ (mem_singleton_self _), mem_univ _⟩⟩)
    rw [h, neg_add_cancel]
  · intro g₁ hg₁ g₂ hg₂ h
    funext x
    by_cases hx : x = -1
    · rw [hx]; exact h
    · rw [(mem_part.1 hg₁).1 x (by rwa [mem_singleton]),
        (mem_part.1 hg₂).1 x (by rwa [mem_singleton])]

theorem card_part_pair : #(part n r ({0, -1} : Finset (Fin n))) ≤ r * (r + 1) + 1 := by
  have h10 : (-1 : Fin (r + 2)) ≠ 0 :=
    neg_ne_zero.2 fun h => absurd (Fin.one_eq_zero_iff.1 h) (by omega)
  set S : Finset (Fin (r + 2)) := univ.erase 0 with hS
  set R : Finset (Fin (r + 2) × Fin (r + 2)) := (S.erase (-1)).image fun x => (x, x + 1) with hR
  have hRS : R ⊆ S ×ˢ S := by
    intro y hy
    rw [hR, mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_erase, hS, mem_erase] at hx
    rw [mem_product]
    exact ⟨mem_erase.2 ⟨hx.2.1, mem_univ _⟩,
      mem_erase.2 ⟨fun h => hx.1 (eq_neg_of_add_eq_zero_left h), mem_univ _⟩⟩
  have hcR : #R = r := by
    rw [hR, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1), hS,
      card_erase_zero_erase h10]
  have hcS : #(S ×ˢ S) = (r + 1) * (r + 1) := by
    rw [card_product, hS, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; rfl
  have hsd : #((S ×ˢ S) \ R) + r = (r + 1) * (r + 1) := by
    have := card_sdiff_add_card_eq_card hRS
    rwa [hcR, hcS] at this
  have hle : #(part n r ({0, -1} : Finset (Fin n))) ≤ #((S ×ˢ S) \ R) := by
    refine Finset.card_le_card_of_injOn (fun g => (g (-1), g 0)) ?_ ?_
    · intro g hg
      have hg' := mem_part.1 hg
      rw [mem_coe, mem_sdiff, mem_product]
      refine ⟨⟨mem_erase.2 ⟨hg'.2.1 _ (by simp), mem_univ _⟩,
        mem_erase.2 ⟨hg'.2.1 _ (by simp), mem_univ _⟩⟩, fun h => ?_⟩
      rw [hR, mem_image] at h
      obtain ⟨x, -, hx⟩ := h
      rw [Prod.mk.injEq] at hx
      exact hg'.2.2.2 (by rw [← hx.1, hx.2])
    · intro g₁ hg₁ g₂ hg₂ h
      rw [Prod.mk.injEq] at h
      funext x
      by_cases hx : x = 0
      · rw [hx]; exact h.2
      · by_cases hx' : x = -1
        · rw [hx']; exact h.1
        · rw [(mem_part.1 hg₁).1 x (by simp [hx, hx']), (mem_part.1 hg₂).1 x (by simp [hx, hx'])]
  have e : (r + 1) * (r + 1) = r * (r + 1) + 1 + r := by ring
  omega

theorem phi_empty : phi r (∅ : Finset (Fin n)) = 1 := by simp [phi]

theorem phi_zero : phi r ({0} : Finset (Fin n)) = r + 1 := by simp [phi]

theorem phi_last (hn : 2 ≤ n) : phi r ({-1} : Finset (Fin n)) = r + 1 := by
  rw [phi, prod_singleton, ite_eq_right]
  intro h
  exact fin_sub_one_ne (fin_neg_one_ne_zero hn) (mem_singleton.1 h.2)

theorem phi_pair (hn : 3 ≤ n) : phi r ({0, -1} : Finset (Fin n)) = (r + 1) * (r + 1) := by
  have h10 := fin_neg_one_ne_zero (n := n) (by omega)
  rw [phi, prod_pair h10.symm, ite_eq_right (fun h => h.1 rfl), ite_eq_right]
  intro h
  have hv := fin_val_sub_one h10
  rw [fin_val_neg_one] at hv
  rcases mem_insert.1 h.2 with h' | h'
  · rw [h'] at hv; simp at hv; omega
  · exact fin_sub_one_ne h10 (mem_singleton.1 h')

variable {J : Finset (Fin n)}

theorem peel_both (h0 : 0 ∈ J) (h1 : -1 ∈ J) : #(part n r Jᶜ) ≤ phi r Jᶜ := by
  have h := peel (r := r) ∅ Jᶜ (empty_subset _) (by
    intro B _ hBJ hB
    have hne : B.Nonempty := nonempty_iff_ne_empty.2 hB
    have hi := B.max'_mem hne
    have hi1 : B.max' hne ≠ -1 := fun h => mem_compl.1 (hBJ hi) (h ▸ h1)
    refine ⟨B.max' hne, hi, notMem_empty _, fun h => mem_compl.1 (hBJ hi) (h ▸ h0), hi1,
      fun h => ?_⟩
    exact absurd (B.le_max' _ h.2) (not_le.2 (fin_lt_add_one hi1)))
  rw [phi_empty, mul_one] at h
  exact h.trans ((Nat.mul_le_mul_right _ card_part_empty).trans_eq (one_mul _))

theorem peel_zero (hn : 2 ≤ n) (h0 : 0 ∉ J) (h1 : -1 ∈ J) :
    #(part n r Jᶜ) * (r + 1) ≤ r * phi r Jᶜ := by
  have h := peel (r := r) {0} Jᶜ (by rw [singleton_subset_iff, mem_compl]; exact h0) (by
    intro B hKB hBJ hB
    have h0B : (0 : Fin n) ∈ B := singleton_subset_iff.1 hKB
    have hne : B.Nonempty := ⟨0, h0B⟩
    have hi := B.max'_mem hne
    have hi1 : B.max' hne ≠ -1 := fun h => mem_compl.1 (hBJ hi) (h ▸ h1)
    have hi0 : B.max' hne ≠ 0 := by
      intro h
      apply hB
      refine Subset.antisymm (fun x hx => ?_) hKB
      have := B.le_max' x hx
      rw [h, Fin.le_def] at this
      rw [mem_singleton]
      exact Fin.ext (by simpa using this)
    refine ⟨B.max' hne, hi, by rwa [mem_singleton], hi0, hi1, fun h => ?_⟩
    exact absurd (B.le_max' _ h.2) (not_le.2 (fin_lt_add_one hi1)))
  rw [phi_zero] at h
  exact h.trans (Nat.mul_le_mul_right _ (card_part_zero hn))

theorem peel_last (hn : 2 ≤ n) (h0 : 0 ∈ J) (h1 : -1 ∉ J) :
    #(part n r Jᶜ) * (r + 1) ≤ r * phi r Jᶜ := by
  have h := peel (r := r) {-1} Jᶜ (by rw [singleton_subset_iff, mem_compl]; exact h1) (by
    intro B hKB hBJ hB
    have h1B : (-1 : Fin n) ∈ B := singleton_subset_iff.1 hKB
    have hne : B.Nonempty := ⟨-1, h1B⟩
    have hi := B.min'_mem hne
    have hi0 : B.min' hne ≠ 0 := fun h => mem_compl.1 (hBJ hi) (h ▸ h0)
    have hi1 : B.min' hne ≠ -1 := by
      intro h
      apply hB
      refine Subset.antisymm (fun x hx => ?_) hKB
      have := B.min'_le x hx
      rw [h] at this
      rw [mem_singleton]
      exact le_antisymm (fin_le_neg_one x) this
    refine ⟨B.min' hne, hi, by rwa [mem_singleton], hi0, hi1, fun h => ?_⟩
    exact absurd (B.min'_le _ h.1) (not_le.2 (fin_sub_one_lt hi0)))
  rw [phi_last hn] at h
  exact h.trans (Nat.mul_le_mul_right _ (card_part_last hn))

theorem peel_none (hn : 3 ≤ n) (h0 : 0 ∉ J) (h1 : -1 ∉ J) {j : Fin n} (hj : j ∈ J) :
    #(part n r Jᶜ) * ((r + 1) * (r + 1)) ≤ (r * (r + 1) + 1) * phi r Jᶜ := by
  have hK : ({0, -1} : Finset (Fin n)) ⊆ Jᶜ := by
    intro x hx
    rw [mem_insert, mem_singleton] at hx
    rw [mem_compl]
    rcases hx with rfl | rfl
    · exact h0
    · exact h1
  have h := peel (r := r) {0, -1} Jᶜ hK (by
    intro B hKB hBJ hB
    obtain ⟨x, hxB, hxK⟩ := Finset.exists_of_ssubset (hKB.ssubset_of_ne (Ne.symm hB))
    rw [mem_insert, mem_singleton, not_or] at hxK
    have hxj : x ≠ j := fun h => mem_compl.1 (hBJ hxB) (h ▸ hj)
    have hjl := fin_le_neg_one j
    rcases lt_or_gt_of_ne hxj with hlt | hgt
    · have hne : (B.filter (· < j)).Nonempty := ⟨x, mem_filter.2 ⟨hxB, hlt⟩⟩
      have hi := mem_filter.1 ((B.filter (· < j)).max'_mem hne)
      have hxi := (B.filter (· < j)).le_max' x (mem_filter.2 ⟨hxB, hlt⟩)
      set i := (B.filter (· < j)).max' hne with hidef
      have hi0 : i ≠ 0 := by
        intro h
        rw [h, Fin.le_def] at hxi
        exact hxK.1 (Fin.ext (by simpa using hxi))
      have hi1 : i ≠ -1 := fun h => absurd (h ▸ hi.2) (not_lt.2 hjl)
      refine ⟨i, hi.1, ?_, hi0, hi1, fun h => ?_⟩
      · rw [mem_insert, mem_singleton, not_or]; exact ⟨hi0, hi1⟩
      · have hv := fin_val_add_one hi1
        have hij := Fin.lt_def.1 hi.2
        by_cases he : i + 1 = j
        · exact mem_compl.1 (hBJ h.2) (he ▸ hj)
        · have hlt' : i + 1 < j := by
            rw [Fin.lt_def]
            have : ((i + 1 : Fin n) : ℕ) ≠ j := fun h' => he (Fin.ext h')
            omega
          have := (B.filter (· < j)).le_max' _ (mem_filter.2 ⟨h.2, hlt'⟩)
          exact absurd this (not_le.2 (fin_lt_add_one hi1))
    · have hne : (B.filter (fun y => j < y ∧ y ≠ -1)).Nonempty :=
        ⟨x, mem_filter.2 ⟨hxB, hgt, hxK.2⟩⟩
      have hi := mem_filter.1 ((B.filter (fun y => j < y ∧ y ≠ -1)).min'_mem hne)
      set i := (B.filter (fun y => j < y ∧ y ≠ -1)).min' hne with hidef
      have hi0 : i ≠ 0 := by
        intro h
        have := hi.2.1
        rw [h, Fin.lt_def] at this
        simp at this
      have hi1 : i ≠ -1 := hi.2.2
      refine ⟨i, hi.1, ?_, hi0, hi1, fun h => ?_⟩
      · rw [mem_insert, mem_singleton, not_or]; exact ⟨hi0, hi1⟩
      · have hv := fin_val_sub_one hi0
        have hij := Fin.lt_def.1 hi.2.1
        by_cases he : i - 1 = j
        · exact mem_compl.1 (hBJ h.1) (he ▸ hj)
        · have hlt' : j < i - 1 := by
            rw [Fin.lt_def]
            have : ((i - 1 : Fin n) : ℕ) ≠ j := fun h' => he (Fin.ext h')
            omega
          have hne1 : i - 1 ≠ -1 := by
            rw [fin_ne_neg_one_iff]
            have := i.isLt
            omega
          have := (B.filter (fun y => j < y ∧ y ≠ -1)).min'_le _
            (mem_filter.2 ⟨h.1, hlt', hne1⟩)
          exact absurd this (not_le.2 (fin_sub_one_lt hi0)))
  rw [phi_pair hn] at h
  exact h.trans (Nat.mul_le_mul_right _ card_part_pair)

/-! ### Comparison with `arcW` -/

theorem phi_compl_eq (h : 0 ∈ J ∨ -1 ∈ J) : (phi r Jᶜ : ℝ) = arcW (r + 1) J := by
  rw [phi, arcW, Nat.cast_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [mem_compl] at hi
  by_cases hp : i - 1 ∈ J
  · rw [ite_eq_right (fun h' => mem_compl.1 h'.2 hp), ite_eq_left hp]
  · have hi0 : i ≠ 0 := by
      rintro rfl
      rw [zero_sub] at hp
      exact h.elim hi hp
    rw [ite_eq_left ⟨hi0, mem_compl.2 hp⟩, ite_eq_right hp]
    push_cast; ring

theorem phi_compl_mul (h0 : 0 ∉ J) (h1 : -1 ∉ J) :
    (phi r Jᶜ : ℝ) * r = arcW (r + 1) J * (r + 1) := by
  have h0' : (0 : Fin n) ∈ Jᶜ := mem_compl.2 h0
  rw [phi, arcW, Nat.cast_prod, ← Finset.mul_prod_erase _ _ h0', ← Finset.mul_prod_erase _ _ h0',
    ite_eq_right (fun h' => h'.1 rfl), ite_eq_right (by rw [zero_sub]; exact h1)]
  have hP : ∏ i ∈ Jᶜ.erase 0, ((if i ≠ 0 ∧ i - 1 ∈ Jᶜ then r else r + 1 : ℕ) : ℝ) =
      ∏ i ∈ Jᶜ.erase 0, if i - 1 ∈ J then ((r + 1 : ℕ) : ℝ) else ((r + 1 : ℕ) : ℝ) - 1 := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [mem_erase] at hi
    by_cases hp : i - 1 ∈ J
    · rw [ite_eq_right (fun h' => mem_compl.1 h'.2 hp), ite_eq_left hp]
    · rw [ite_eq_left ⟨hi.1, mem_compl.2 hp⟩, ite_eq_right hp]
      push_cast; ring
  rw [hP]
  push_cast
  ring

end Bounds

end Outerplanar
