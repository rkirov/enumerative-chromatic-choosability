/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Region

/-!
# Height four at `k = 4`: the minimum-over-lists recurrence, at the level of colours

Codex's (OpenAI) recurrence (`ai_research_notes/cx/h4k4b/NOTE.md`, "The lower-bound recurrence")
bounds a sum over a list `Y` of three or four colours by the smallest such sums. We use it in the
**`t`-bound** form: for every threshold `t`,

  `∑_{x ∈ Y} h x ≥ 3t + min(0, t) + ∑_{x ∈ Y} min(0, h x - t)`        (`tbound`)

since `h x ≥ t + min(0, h x - t)` and `|Y| t ≥ 3t + min(0, t)` for `|Y| ∈ {3, 4}`. The last sum
only gets smaller when terms are added, so it is bounded below by grouping the colours into
classes with known lower bounds and **upper bounds on the class sizes** (`sum_classes`): a class
of value `v` and at most `μ` members contributes at least `μ · min(0, v - t)`, and a class with
`v ≥ t` contributes nothing. With `t` the third smallest value (or the fourth when that is
negative) this is exactly the sum of the three smallest values plus the negative part of the
fourth; any `t` is sound. Overcounting a class is sound too, which makes merging and capacity
relaxations free.

`sumP_split`: the sum over the product of four lists is a sum over one list of the sums with that
list replaced by a singleton.
-/

namespace GridGen.Four.K4

open Finset

/-! ### Rows of a column -/

/-- A list of a column, by index. -/
def rowC (Y : Col) : ℕ → Finset ℕ
  | 0 => Y.1
  | 1 => Y.2.1
  | 2 => Y.2.2.1
  | _ => Y.2.2.2

/-- Replace a list of a column. -/
def setC (Y : Col) (i : ℕ) (X : Finset ℕ) : Col :=
  match i with
  | 0 => (X, Y.2.1, Y.2.2.1, Y.2.2.2)
  | 1 => (Y.1, X, Y.2.2.1, Y.2.2.2)
  | 2 => (Y.1, Y.2.1, X, Y.2.2.2)
  | _ => (Y.1, Y.2.1, Y.2.2.1, X)

/-- **Elimination of one row.** -/
theorem sumP_split (g : T4 → ℤ) (Y : Col) (i : ℕ) (hi : i < 4) :
    sumP g Y = ∑ x ∈ rowC Y i, sumP g (setC Y i {x}) := by
  obtain ⟨Y1, Y2, Y3, Y4⟩ := Y
  unfold sumP
  interval_cases i
  · simp [rowC, setC]
  · simp only [rowC, setC, Finset.sum_singleton]
    exact Finset.sum_comm
  · simp only [rowC, setC, Finset.sum_singleton]
    calc _ = ∑ a ∈ Y1, ∑ c ∈ Y3, ∑ b ∈ Y2, ∑ d ∈ Y4, g (a, b, c, d) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  · simp only [rowC, setC, Finset.sum_singleton]
    calc _ = ∑ a ∈ Y1, ∑ b ∈ Y2, ∑ d ∈ Y4, ∑ c ∈ Y3, g (a, b, c, d) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ a ∈ Y1, ∑ d ∈ Y4, ∑ b ∈ Y2, ∑ c ∈ Y3, g (a, b, c, d) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_comm

/-! ### The `t`-bound -/

/-- **The threshold bound.** -/
theorem tbound {Y : Finset ℕ} (hY : 3 ≤ Y.card ∧ Y.card ≤ 4) (h : ℕ → ℤ) (t : ℤ) :
    3 * t + min 0 t + ∑ x ∈ Y, min 0 (h x - t) ≤ ∑ x ∈ Y, h x := by
  have e : ∑ x ∈ Y, h x = ∑ x ∈ Y, (t + (h x - t)) := by
    refine Finset.sum_congr rfl fun x _ => ?_; ring
  have hle : ∑ x ∈ Y, (t + min 0 (h x - t)) ≤ ∑ x ∈ Y, (t + (h x - t)) :=
    Finset.sum_le_sum fun x _ => by linarith [min_le_right 0 (h x - t)]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hle
  rw [e]
  refine le_trans ?_ hle
  have hc : 3 * t + min 0 t ≤ (Y.card : ℤ) * t := by
    have h3 : (3 : ℤ) ≤ Y.card := by exact_mod_cast hY.1
    have h4 : (Y.card : ℤ) ≤ 4 := by exact_mod_cast hY.2
    rcases le_total 0 t with ht | ht
    · rw [min_eq_left ht]; nlinarith
    · rw [min_eq_right ht]; nlinarith
  linarith

/-- A class of colours: a predicate, a value, and a bound on the number of members. -/
abbrev Cls := (ℕ → Bool) × ℤ × ℕ

/-- **Grouping by classes.** If every colour of `Y` lies in a listed class or has `φ x = 0`, and
each class of value `v` has at most `μ` members in `Y` and `φ ≥ min(0, v - t)` on it, then
`∑_{x ∈ Y} φ x ≥ ∑_classes μ · min(0, v - t)`. -/
theorem sum_classes (t : ℤ) (φ : ℕ → ℤ) (hφ : ∀ x, φ x ≤ 0) :
    ∀ (L : List Cls) (Y : Finset ℕ),
      (∀ x ∈ Y, (∃ c ∈ L, c.1 x = true) ∨ φ x = 0) →
      (∀ c ∈ L, ∀ x, c.1 x = true → min 0 (c.2.1 - t) ≤ φ x) →
      (∀ c ∈ L, (Y.filter fun x => c.1 x = true).card ≤ c.2.2) →
      (L.map fun c => (c.2.2 : ℤ) * min 0 (c.2.1 - t)).sum ≤ ∑ x ∈ Y, φ x
  | [], Y, hcov, _, _ => by
    simp only [List.map_nil, List.sum_nil]
    refine le_of_eq (Finset.sum_eq_zero fun x hx => ?_).symm
    rcases hcov x hx with ⟨c, hc, -⟩ | h
    · simp at hc
    · exact h
  | c :: L, Y, hcov, hval, hcnt => by
    simp only [List.map_cons, List.sum_cons]
    rw [← Finset.sum_filter_add_sum_filter_not Y (fun x => c.1 x = true)]
    have h1 : (c.2.2 : ℤ) * min 0 (c.2.1 - t) ≤ ∑ x ∈ Y.filter (fun x => c.1 x = true), φ x := by
      have hm : min 0 (c.2.1 - t) ≤ 0 := min_le_left _ _
      have hcard : ((Y.filter fun x => c.1 x = true).card : ℤ) ≤ c.2.2 := by
        exact_mod_cast hcnt c List.mem_cons_self
      calc (c.2.2 : ℤ) * min 0 (c.2.1 - t)
          ≤ ((Y.filter fun x => c.1 x = true).card : ℤ) * min 0 (c.2.1 - t) :=
            mul_le_mul_of_nonpos_right hcard hm
        _ = ∑ x ∈ Y.filter (fun x => c.1 x = true), min 0 (c.2.1 - t) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ Y.filter (fun x => c.1 x = true), φ x :=
            Finset.sum_le_sum fun x hx =>
              hval c List.mem_cons_self x (Finset.mem_filter.mp hx).2
    have h2 := sum_classes t φ hφ L (Y.filter fun x => ¬ c.1 x = true)
      (fun x hx => by
        obtain ⟨hxY, hxc⟩ := Finset.mem_filter.mp hx
        rcases hcov x hxY with ⟨c', hc', hx'⟩ | h
        · rcases List.mem_cons.mp hc' with rfl | hc'
          · exact absurd hx' hxc
          · exact Or.inl ⟨c', hc', hx'⟩
        · exact Or.inr h)
      (fun c' hc' => hval c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => le_trans (Finset.card_le_card (by
          intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1.1, hx.2⟩)) (hcnt c' (List.mem_cons_of_mem _ hc')))
    linarith

end GridGen.Four.K4
