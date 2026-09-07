import Grid3.Three.Glue
import Grid3.Three.Cert.KeyExt

/-!
# The slots of a canonical colour list

`Cert.colours mL mR M` lists the canonical colours of a seam with key `(mL, mR, M)`: first the
matched pairs `(p+1, q+1)` (`mcount M p q` of each), then the left-only colours `(p+1, 0)` and
the right-only colours `(0, q+1)`. This file counts the slots of each kind.
-/

open Finset

namespace Grid3.Three.Slots

open Cert Glue

theorem list_range_sum (g : ℕ → ℕ) : ∀ n, ((List.range n).map g).sum = ∑ i ∈ range n, g i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ,
      list_range_sum g n]
    simp

theorem count_flatMap {α β : Type*} [BEq β] (f : α → List β) (b : β) :
    ∀ l : List α, (l.flatMap f).count b = (l.map fun a => (f a).count b).sum
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.count_append, List.map_cons, List.sum_cons, count_flatMap f b l]

/-- the count of a replicate, as a `Prop`-valued `if` -/
theorem count_replicate' {β : Type*} [BEq β] [LawfulBEq β] [DecidableEq β] (n : ℕ) (x b : β) :
    (List.replicate n x).count b = if x = b then n else 0 := by
  rw [List.count_replicate]
  by_cases h : x = b
  · subst h; simp
  · simp [h]

/-- the three blocks of the canonical list -/
theorem colours_eq (mL mR M : ℕ) : colours mL mR M =
    ((List.range 7).flatMap fun p => (List.range 7).flatMap fun q =>
        List.replicate (mcount M p q) (p + 1, q + 1))
    ++ ((List.range 7).flatMap fun p => List.replicate (mult mL p - sumRow M p) (p + 1, 0))
    ++ ((List.range 7).flatMap fun q => List.replicate (mult mR q - sumCol M q) (0, q + 1)) := rfl

theorem count_pair (mL mR M p q : ℕ) (hp : p < 7) (hq : q < 7) :
    (colours mL mR M).count (p + 1, q + 1) = mcount M p q := by
  rw [colours_eq, List.count_append, List.count_append]
  have hA : (((List.range 7).flatMap fun p' => (List.range 7).flatMap fun q' =>
      List.replicate (mcount M p' q') (p' + 1, q' + 1)).count (p + 1, q + 1)) = mcount M p q := by
    rw [count_flatMap, list_range_sum]
    simp only [count_flatMap, list_range_sum, count_replicate', Prod.mk.injEq,
      Nat.add_right_cancel_iff]
    rw [Finset.sum_eq_single p]
    · rw [Finset.sum_eq_single q]
      · simp
      · intro q' _ hq'; simp [hq']
      · intro h; exact absurd (Finset.mem_range.2 hq) h
    · intro p' _ hp'
      apply Finset.sum_eq_zero
      intro q' _; simp [hp']
    · intro h; exact absurd (Finset.mem_range.2 hp) h
  have hB : (((List.range 7).flatMap fun p' =>
      List.replicate (mult mL p' - sumRow M p') (p' + 1, 0)).count (p + 1, q + 1)) = 0 := by
    rw [count_flatMap, list_range_sum]
    apply Finset.sum_eq_zero
    intro p' _
    rw [count_replicate', if_neg]
    simp
  have hC : (((List.range 7).flatMap fun q' =>
      List.replicate (mult mR q' - sumCol M q') (0, q' + 1)).count (p + 1, q + 1)) = 0 := by
    rw [count_flatMap, list_range_sum]
    apply Finset.sum_eq_zero
    intro q' _
    rw [count_replicate', if_neg]
    simp
  simp only [hA, hB, hC, Nat.add_zero, Nat.zero_add]

theorem count_left (mL mR M p : ℕ) (hp : p < 7) :
    (colours mL mR M).count (p + 1, 0) = mult mL p - sumRow M p := by
  rw [colours_eq, List.count_append, List.count_append]
  have hA : (((List.range 7).flatMap fun p' => (List.range 7).flatMap fun q' =>
      List.replicate (mcount M p' q') (p' + 1, q' + 1)).count (p + 1, 0)) = 0 := by
    rw [count_flatMap, list_range_sum]
    apply Finset.sum_eq_zero
    intro p' _
    rw [count_flatMap, list_range_sum]
    apply Finset.sum_eq_zero
    intro q' _
    rw [count_replicate', if_neg]
    simp
  have hB : (((List.range 7).flatMap fun p' =>
      List.replicate (mult mL p' - sumRow M p') (p' + 1, 0)).count (p + 1, 0))
      = mult mL p - sumRow M p := by
    rw [count_flatMap, list_range_sum]
    simp only [count_replicate', Prod.mk.injEq, Nat.add_right_cancel_iff, and_true]
    rw [Finset.sum_eq_single p]
    · simp
    · intro p' _ hp'; simp [hp']
    · intro h; exact absurd (Finset.mem_range.2 hp) h
  have hC : (((List.range 7).flatMap fun q' =>
      List.replicate (mult mR q' - sumCol M q') (0, q' + 1)).count (p + 1, 0)) = 0 := by
    rw [count_flatMap, list_range_sum]
    apply Finset.sum_eq_zero
    intro q' _
    rw [count_replicate', if_neg]
    simp
  simp only [hA, hB, hC, Nat.add_zero, Nat.zero_add]

theorem count_right (mL mR M q : ℕ) (hq : q < 7) :
    (colours mL mR M).count (0, q + 1) = mult mR q - sumCol M q := by
  rw [colours_eq, List.count_append, List.count_append]
  have hA : (((List.range 7).flatMap fun p' => (List.range 7).flatMap fun q' =>
      List.replicate (mcount M p' q') (p' + 1, q' + 1)).count (0, q + 1)) = 0 := by
    rw [count_flatMap, list_range_sum]
    apply Finset.sum_eq_zero
    intro p' _
    rw [count_flatMap, list_range_sum]
    apply Finset.sum_eq_zero
    intro q' _
    rw [count_replicate', if_neg]
    simp
  have hB : (((List.range 7).flatMap fun p' =>
      List.replicate (mult mL p' - sumRow M p') (p' + 1, 0)).count (0, q + 1)) = 0 := by
    rw [count_flatMap, list_range_sum]
    apply Finset.sum_eq_zero
    intro p' _
    rw [count_replicate', if_neg]
    simp
  have hC : (((List.range 7).flatMap fun q' =>
      List.replicate (mult mR q' - sumCol M q') (0, q' + 1)).count (0, q + 1))
      = mult mR q - sumCol M q := by
    rw [count_flatMap, list_range_sum]
    simp only [count_replicate', Prod.mk.injEq, Nat.add_right_cancel_iff, true_and]
    rw [Finset.sum_eq_single q]
    · simp
    · intro q' _ hq'; simp [hq']
    · intro h; exact absurd (Finset.mem_range.2 hq) h
  simp only [hA, hB, hC, Nat.add_zero, Nat.zero_add]

/-- every slot is one of the three kinds -/
theorem mem_colours_kinds (mL mR M : ℕ) (x : ℕ × ℕ) (hx : x ∈ colours mL mR M) :
    (∃ p < 7, ∃ q < 7, x = (p + 1, q + 1)) ∨ (∃ p < 7, x = (p + 1, 0)) ∨ (∃ q < 7, x = (0, q + 1)) := by
  rw [colours_eq, List.mem_append, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · rw [List.mem_flatMap] at hx
    obtain ⟨p, hp, hx⟩ := hx
    rw [List.mem_flatMap] at hx
    obtain ⟨q, hq, hx⟩ := hx
    rw [List.mem_replicate] at hx
    exact Or.inl ⟨p, List.mem_range.1 hp, q, List.mem_range.1 hq, hx.2⟩
  · rw [List.mem_flatMap] at hx
    obtain ⟨p, hp, hx⟩ := hx
    rw [List.mem_replicate] at hx
    exact Or.inr (Or.inl ⟨p, List.mem_range.1 hp, hx.2⟩)
  · rw [List.mem_flatMap] at hx
    obtain ⟨q, hq, hx⟩ := hx
    rw [List.mem_replicate] at hx
    exact Or.inr (Or.inr ⟨q, List.mem_range.1 hq, hx.2⟩)

/-- the slots of one kind -/
def slot (cols : List (ℕ × ℕ)) (x : ℕ × ℕ) : Finset (Fin cols.length) :=
  Finset.univ.filter fun i => cols[i] = x

theorem card_slot (cols : List (ℕ × ℕ)) (x : ℕ × ℕ) : (slot cols x).card = cols.count x :=
  count_eq_fiber cols x

theorem mem_slot (cols : List (ℕ × ℕ)) (x : ℕ × ℕ) (i : Fin cols.length) :
    i ∈ slot cols x ↔ cols[i] = x := by
  unfold slot; simp

end Grid3.Three.Slots
