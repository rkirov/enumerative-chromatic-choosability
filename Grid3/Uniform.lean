/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Grid3.Transfer

/-!
# Counting in a column, and the uniform column

The cardinality identities behind `Grid3.Transfer`: the number of states of a column as a sum
over the middle colour, the successors of a state as the states of the punctured next column, and
for the uniform column `U = ([k], [k], [k])` the exact counts `ene k + [eq]` and
`gam k + del k · [eq]` that define the pattern transfer. These are what identify the abstract
sequence `Fpat` with the actual uniform colouring counts.
-/

open Finset

namespace Grid3

/-! ### Fibrewise counting -/

/-- The states with a prescribed middle colour, as an image of a product. -/
theorem filter_mid_eq_image (T M B : Finset ℕ) {b : ℕ} (hb : b ∈ M) :
    (states T M B).filter (fun s => s.2.1 = b)
      = ((T.erase b) ×ˢ (B.erase b)).image (fun p : ℕ × ℕ => (p.1, b, p.2)) := by
  ext s
  obtain ⟨a, b', c⟩ := s
  simp only [Finset.mem_filter, mem_states, Finset.mem_image, Finset.mem_product,
    Finset.mem_erase, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨ha, hb', hc, hab, hbc⟩, rfl⟩
    exact ⟨(a, c), ⟨⟨hab, ha⟩, ⟨Ne.symm hbc, hc⟩⟩, rfl, rfl, rfl⟩
  · rintro ⟨⟨a', c'⟩, ⟨⟨ha', ha⟩, ⟨hc', hc⟩⟩, rfl, rfl, rfl⟩
    exact ⟨⟨ha, hb, hc, ha', Ne.symm hc'⟩, rfl⟩

/-- The number of states of a column, summed over the middle colour. -/
theorem card_states (T M B : Finset ℕ) :
    (states T M B).card = ∑ b ∈ M, (T.erase b).card * (B.erase b).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun s : State => s.2.1) (t := M)
    (fun s hs => (mem_states.mp hs).2.1)]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [filter_mid_eq_image T M B hb, Finset.card_image_of_injective, Finset.card_product]
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 h.2.2

/-- The `eq` states with a prescribed middle colour. -/
theorem filter_eq_mid_eq_image (T M B : Finset ℕ) {b : ℕ} (hb : b ∈ M) :
    ((states T M B).filter IsEq).filter (fun s => s.2.1 = b)
      = ((T ∩ B).erase b).image (fun a : ℕ => (a, b, a)) := by
  ext s
  obtain ⟨a, b', c⟩ := s
  simp only [Finset.mem_filter, mem_states, Finset.mem_image, Finset.mem_erase, Finset.mem_inter,
    Prod.mk.injEq, IsEq]
  constructor
  · rintro ⟨⟨⟨ha, hb', hc, hab, hbc⟩, hac⟩, rfl⟩
    subst hac
    exact ⟨a, ⟨hab, ha, hc⟩, rfl, rfl, rfl⟩
  · rintro ⟨a', ⟨ha', ha, hc⟩, rfl, rfl, rfl⟩
    exact ⟨⟨⟨ha, hb, hc, ha', Ne.symm ha'⟩, rfl⟩, rfl⟩

/-- The number of `eq` states, summed over the middle colour. -/
theorem card_eq_states (T M B : Finset ℕ) :
    ((states T M B).filter IsEq).card = ∑ b ∈ M, ((T ∩ B).erase b).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun s : State => s.2.1) (t := M)
    (fun s hs => (mem_states.mp (Finset.mem_filter.mp hs).1).2.1)]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [filter_eq_mid_eq_image T M B hb, Finset.card_image_of_injective]
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact h.1

/-- The successors of `s` are the states of the punctured column. -/
theorem filter_compat_eq_states (T M B : Finset ℕ) (s : State) :
    (states T M B).filter (Compat s) = states (T.erase s.1) (M.erase s.2.1) (B.erase s.2.2) := by
  ext t
  simp only [Finset.mem_filter, mem_states, Compat, Finset.mem_erase]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5⟩, c1, c2, c3⟩
    exact ⟨⟨Ne.symm c1, h1⟩, ⟨Ne.symm c2, h2⟩, ⟨Ne.symm c3, h3⟩, h4, h5⟩
  · rintro ⟨⟨c1, h1⟩, ⟨c2, h2⟩, ⟨c3, h3⟩, h4, h5⟩
    exact ⟨⟨h1, h2, h3, h4, h5⟩, Ne.symm c1, Ne.symm c2, Ne.symm c3⟩

theorem succ_eq_card (T M B : Finset ℕ) (s : State) :
    succ T M B s = (states (T.erase s.1) (M.erase s.2.1) (B.erase s.2.2)).card := by
  rw [succ, filter_compat_eq_states]

/-- The `eq` successors of `s`: the `eq` states of the punctured column. -/
theorem eqSucc_eq_card (T M B : Finset ℕ) (s : State) :
    eqSucc T M B s
      = ((states (T.erase s.1) (M.erase s.2.1) (B.erase s.2.2)).filter IsEq).card := by
  rw [eqSucc, ← filter_compat_eq_states, Finset.filter_filter]


/-- The `eq` states, fibred over the common top-and-bottom colour. -/
theorem filter_eq_top_eq_image (T M B : Finset ℕ) {a : ℕ} (ha : a ∈ T ∩ B) :
    ((states T M B).filter IsEq).filter (fun s => s.1 = a)
      = (M.erase a).image (fun b : ℕ => (a, b, a)) := by
  ext s
  obtain ⟨a', b, c⟩ := s
  simp only [Finset.mem_filter, mem_states, Finset.mem_image, Finset.mem_erase, IsEq,
    Prod.mk.injEq]
  rw [Finset.mem_inter] at ha
  constructor
  · rintro ⟨⟨⟨ha', hb, hc, hab, hbc⟩, hac⟩, rfl⟩
    subst hac
    exact ⟨b, ⟨Ne.symm hab, hb⟩, rfl, rfl, rfl⟩
  · rintro ⟨b', ⟨hb', hb⟩, rfl, rfl, rfl⟩
    exact ⟨⟨⟨ha.1, hb, ha.2, Ne.symm hb', hb'⟩, rfl⟩, rfl⟩

/-- The number of `eq` states, summed over the common colour. -/
theorem card_eq_states' (T M B : Finset ℕ) :
    ((states T M B).filter IsEq).card = ∑ a ∈ T ∩ B, (M.erase a).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun s : State => s.1) (t := T ∩ B) (fun s hs => by
    obtain ⟨hs, hac⟩ := Finset.mem_filter.mp hs
    obtain ⟨h1, _, h3, _, _⟩ := mem_states.mp hs
    have hac' : s.1 = s.2.2 := hac
    exact Finset.mem_inter.mpr ⟨h1, by show s.1 ∈ B; rw [hac']; exact h3⟩)]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [filter_eq_top_eq_image T M B ha, Finset.card_image_of_injective]
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact h.2.1

/-! ### The uniform column -/

/-- Erasing one element of `[k]` leaves `k - 1`. -/
theorem card_erase_range {k a : ℕ} (ha : a ∈ Finset.range k) :
    ((Finset.range k).erase a).card = k - 1 := by
  rw [Finset.card_erase_of_mem ha, Finset.card_range]

/-- Erasing two elements of `[k]` leaves `k - 2`, or `k - 1` if they coincide. -/
theorem card_erase_erase_range {k a y : ℕ} (hk : 2 ≤ k) (ha : a ∈ Finset.range k)
    (hy : y ∈ Finset.range k) :
    (((Finset.range k).erase a).erase y).card = k - 2 + (if y = a then 1 else 0) := by
  by_cases h : y = a
  · subst h
    rw [Finset.erase_eq_of_notMem (Finset.notMem_erase _ _), card_erase_range ha, if_pos rfl]
    omega
  · rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h, hy⟩), card_erase_range ha, if_neg h]
    omega

/-- **Uniform successors.** A uniform state has `ene k + [eq]` successors in a uniform column. -/
theorem succ_uniform {k : ℕ} (hk : 2 ≤ k) {s : State}
    (hs : s ∈ states (Finset.range k) (Finset.range k) (Finset.range k)) :
    succ (Finset.range k) (Finset.range k) (Finset.range k) s = ene k + eqInd s := by
  obtain ⟨a, b, c⟩ := s
  obtain ⟨ha, hb, hc, hab, hbc⟩ := mem_states.mp hs
  simp only at ha hb hc hab hbc
  rw [succ_eq_card, card_states]
  simp only
  have hpt : ∀ y ∈ (Finset.range k).erase b,
      (((Finset.range k).erase a).erase y).card * (((Finset.range k).erase c).erase y).card
        = (k - 2) * (k - 2) + (k - 2) * (if y = a then 1 else 0)
          + (k - 2) * (if y = c then 1 else 0) + (if y = a then (if y = c then 1 else 0) else 0) := by
    intro y hy
    have hy' : y ∈ Finset.range k := (Finset.mem_erase.mp hy).2
    rw [card_erase_erase_range hk ha hy', card_erase_erase_range hk hc hy']
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hpt]
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum,
    Finset.sum_ite_eq', card_erase_range hb]
  have hab' : a ∈ (Finset.range k).erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
  have hcb' : c ∈ (Finset.range k).erase b := Finset.mem_erase.mpr ⟨Ne.symm hbc, hc⟩
  rw [if_pos hab', if_pos hcb', if_pos hab']
  unfold ene eqInd IsEq
  simp only
  by_cases hac : a = c
  · subst hac; simp; ring
  · simp [hac]; ring

/-- **Uniform `eq` successors.** A uniform state has `gam k + del k · [eq]` `eq` successors. -/
theorem eqSucc_uniform {k : ℕ} (hk : 2 ≤ k) {s : State}
    (hs : s ∈ states (Finset.range k) (Finset.range k) (Finset.range k)) :
    eqSucc (Finset.range k) (Finset.range k) (Finset.range k) s = gam k + del k * eqInd s := by
  obtain ⟨a, b, c⟩ := s
  obtain ⟨ha, hb, hc, hab, hbc⟩ := mem_states.mp hs
  simp only at ha hb hc hab hbc
  rw [eqSucc_eq_card, card_eq_states']
  simp only
  have hint : (Finset.range k).erase a ∩ (Finset.range k).erase c
      = ((Finset.range k).erase a).erase c := by
    ext x; simp only [Finset.mem_inter, Finset.mem_erase]; tauto
  rw [hint]
  have hpt : ∀ x ∈ ((Finset.range k).erase a).erase c,
      (((Finset.range k).erase b).erase x).card = k - 2 + (if x = b then 1 else 0) := by
    intro x hx
    have hx' : x ∈ Finset.range k := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
    exact card_erase_erase_range hk hb hx'
  rw [Finset.sum_congr rfl hpt]
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_ite_eq']
  rw [card_erase_erase_range hk ha hc]
  have hb' : b ∈ ((Finset.range k).erase a).erase c :=
    Finset.mem_erase.mpr ⟨hbc, Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩⟩
  rw [if_pos hb']
  unfold gam del eqInd IsEq
  simp only
  by_cases hac : a = c
  · subst hac; simp; ring
  · simp [hac, Ne.symm hac]; ring

/-- The uniform column has `k(k-1)²` states. -/
theorem card_states_uniform (k : ℕ) :
    (states (Finset.range k) (Finset.range k) (Finset.range k)).card = k * (k - 1) ^ 2 := by
  rw [card_states]
  rw [Finset.sum_congr rfl fun b hb => by rw [card_erase_range hb]]
  simp [pow_two]

/-- The uniform column has `k(k-1)` `eq` states. -/
theorem card_eq_states_uniform (k : ℕ) :
    ((states (Finset.range k) (Finset.range k) (Finset.range k)).filter IsEq).card
      = k * (k - 1) := by
  rw [card_eq_states', Finset.inter_self]
  rw [Finset.sum_congr rfl fun b hb => by rw [card_erase_range hb]]
  simp

/-! ### The initial column -/

/-- Any column of `k`-lists has at least `k(k-1)²` states. -/
theorem card_states_ge {k : ℕ} {T M B : Finset ℕ} (hT : T.card = k) (hM : M.card = k)
    (hB : B.card = k) : k * (k - 1) ^ 2 ≤ (states T M B).card := by
  rw [card_states]
  have h : ∀ b ∈ M, (k - 1) * (k - 1) ≤ (T.erase b).card * (B.erase b).card := by
    intro b _
    have h1 : k - 1 ≤ (T.erase b).card := by
      have := Finset.pred_card_le_card_erase (s := T) (a := b); omega
    have h2 : k - 1 ≤ (B.erase b).card := by
      have := Finset.pred_card_le_card_erase (s := B) (a := b); omega
    exact Nat.mul_le_mul h1 h2
  calc k * (k - 1) ^ 2 = ∑ _b ∈ M, (k - 1) * (k - 1) := by
        rw [Finset.sum_const, smul_eq_mul, hM]; ring
    _ ≤ _ := Finset.sum_le_sum h

/-- The number of states, minus `k(k-1)²`, is at least `(k-1)` times the number of middle
colours missing from the top list plus those missing from the bottom list. -/
theorem card_states_ge' {k : ℕ} {T M B : Finset ℕ} (hk : 1 ≤ k) (hT : T.card = k) (hM : M.card = k)
    (hB : B.card = k) :
    k * (k - 1) ^ 2 + (k - 1) * ((M.filter (· ∉ T)).card + (M.filter (· ∉ B)).card)
      ≤ (states T M B).card := by
  rw [card_states]
  have hpt : ∀ b ∈ M, (k - 1) * (k - 1) + (k - 1) * ((if b ∉ T then 1 else 0) + (if b ∉ B then 1 else 0))
      ≤ (T.erase b).card * (B.erase b).card := by
    intro b _
    have h1 : (T.erase b).card = k - 1 + (if b ∉ T then 1 else 0) := by
      by_cases h : b ∈ T
      · rw [Finset.card_erase_of_mem h, hT, if_neg (not_not.mpr h)]; omega
      · rw [Finset.erase_eq_of_notMem h, hT, if_pos h]; omega
    have h2 : (B.erase b).card = k - 1 + (if b ∉ B then 1 else 0) := by
      by_cases h : b ∈ B
      · rw [Finset.card_erase_of_mem h, hB, if_neg (not_not.mpr h)]; omega
      · rw [Finset.erase_eq_of_notMem h, hB, if_pos h]; omega
    rw [h1, h2]
    split_ifs <;> nlinarith
  calc k * (k - 1) ^ 2 + (k - 1) * ((M.filter (· ∉ T)).card + (M.filter (· ∉ B)).card)
      = ∑ b ∈ M, ((k - 1) * (k - 1)
          + (k - 1) * ((if b ∉ T then 1 else 0) + (if b ∉ B then 1 else 0))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hM, ← Finset.mul_sum,
          Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
        (try push_cast)
        ring
    _ ≤ _ := Finset.sum_le_sum hpt

/-- The `eq` states are at least `(k-1)` per common top-and-bottom colour. -/
theorem card_eq_states_ge {k : ℕ} {T M B : Finset ℕ} (hM : M.card = k) :
    (k - 1) * (T ∩ B).card ≤ ((states T M B).filter IsEq).card := by
  rw [card_eq_states']
  calc (k - 1) * (T ∩ B).card = ∑ _a ∈ T ∩ B, (k - 1) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun a _ => by
        have := Finset.pred_card_le_card_erase (s := M) (a := a); omega

/-- The middle colours missing from the top or from the bottom list cover all but `T ∩ B`. -/
theorem card_missing_ge {k : ℕ} {T M B : Finset ℕ} (hM : M.card = k) :
    k ≤ (M.filter (· ∉ T)).card + (M.filter (· ∉ B)).card + (T ∩ B).card := by
  have hsub : M ⊆ M.filter (· ∉ T) ∪ M.filter (· ∉ B) ∪ (T ∩ B) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_inter]
    by_cases hT : x ∈ T <;> by_cases hB : x ∈ B <;> tauto
  calc k = M.card := hM.symm
    _ ≤ (M.filter (· ∉ T) ∪ M.filter (· ∉ B) ∪ (T ∩ B)).card := Finset.card_le_card hsub
    _ ≤ (M.filter (· ∉ T) ∪ M.filter (· ∉ B)).card + (T ∩ B).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _

/-- **The initial condition.** For a column of `k`-lists, `cc · #states + #eq` is at least its
uniform value `cc · k(k-1)² + k(k-1)`. -/
theorem init_cond {k : ℕ} (hk : 3 ≤ k) {T M B : Finset ℕ} (hT : T.card = k) (hM : M.card = k)
    (hB : B.card = k) :
    cc k * (k * (k - 1) ^ 2) + k * (k - 1)
      ≤ cc k * (states T M B).card + ((states T M B).filter IsEq).card := by
  have h1 := card_states_ge' (by omega) hT hM hB
  have h2 := card_eq_states_ge (T := T) (B := B) hM
  have h3 := card_missing_ge (T := T) (B := B) hM
  have hi : (T ∩ B).card ≤ k := by rw [← hT]; exact Finset.card_le_card Finset.inter_subset_left
  have hcc : 1 ≤ cc k := by
    unfold cc
    have h2 : 1 ≤ (k - 1) * (k - 2) + 1 := Nat.le_add_left 1 _
    have h1' : 1 ≤ k - 2 := by omega
    calc 1 = 1 * 1 := rfl
      _ ≤ (k - 2) * ((k - 1) * (k - 2) + 1) := Nat.mul_le_mul h1' h2
  set m := (M.filter (· ∉ T)).card + (M.filter (· ∉ B)).card
  set i := (T ∩ B).card
  set st := (states T M B).card
  set eq := ((states T M B).filter IsEq).card
  have hm : m + i ≤ cc k * m + i :=
    Nat.add_le_add_right (Nat.le_mul_of_pos_left m (by omega)) _
  calc cc k * (k * (k - 1) ^ 2) + k * (k - 1)
      = cc k * (k * (k - 1) ^ 2) + (k - 1) * k := by ring
    _ ≤ cc k * (k * (k - 1) ^ 2) + (k - 1) * (m + i) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ h3) _
    _ ≤ cc k * (k * (k - 1) ^ 2) + (k - 1) * (cc k * m + i) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hm) _
    _ = cc k * (k * (k - 1) ^ 2 + (k - 1) * m) + (k - 1) * i := by ring
    _ ≤ cc k * st + eq := Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2

end Grid3
