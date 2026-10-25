/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Exact6

/-!
# Height four: the shapes of the exact mismatch triples, for any list size

The exact certificates of `k = 6` (`Small6/`) and `k = 5` (`Small5k/`) are indexed by list shape:
the sizes of the fifteen nonempty atoms of the Venn diagram of `B₁, …, B₄`. For four `k`-lists
with consecutive mismatches `(μ₂, μ₃, μ₄)` (`μᵢ = k - |Bᵢ₋₁ ∩ Bᵢ|`) the atom sizes satisfy seven
linear equations (`venn_lin`). `dispatchCheck k M E hit` enumerates their solutions for the
triples below `M` accepted by `E`, pruning on partial sums, and asks `hit` of each; an instance
checks it by kernel evaluation, and `dispatch_of_check` turns that into the statement that the
lists' atom sizes are accepted by `hit`. With `hit = hitIn table atoms`, a table entry has exactly
those atom sizes (`hitIn_atoms`).
-/

namespace GridGen.Four

/-- `f 0 && f 1 && … && f (n - 1)`. -/
def allLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => allLt n f && f n

theorem allLt_spec {n : ℕ} {f : ℕ → Bool} (h : allLt n f = true) (x : ℕ) (hx : x < n) :
    f x = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [allLt, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
    · exact ih h.1 hx
    · exact h.2

theorem imp_spec {a b : Bool} (h : (!a || b) = true) (ha : a = true) : b = true := by
  subst ha; simpa using h

/-- The enumeration of the atom sizes of four `k`-lists with mismatches `(m2, m3, m4)`, each below
`M` and accepted by `E`: every solution of the Venn equations is accepted by `hit`. -/
def dispatchCheck (k M : ℕ) (E : ℕ → ℕ → ℕ → Bool) (hit : List ℕ → Bool) : Bool :=
  allLt M fun m2 => allLt M fun m3 => allLt M fun m4 => !E m2 m3 m4 ||
    allLt (k + 1) fun x5 => !(decide (x5 ≤ m2) &&
      decide (x5 ≤ m3) &&
      decide (x5 ≤ m4)) ||
    allLt (k + 1) fun x10 => !(decide (x10 ≤ m2) &&
      decide (x10 ≤ m3) &&
      decide (x10 ≤ m4) &&
      decide (x10 ≤ k)) ||
    allLt (k + 1) fun x2 => !(decide (x2 + x10 ≤ m3) && decide (x2 + x10 ≤ m4)) ||
    allLt (k + 1) fun x4 => !(decide (x4 + x5 ≤ m2) && decide (x4 + x5 ≤ m3)) ||
    allLt (k + 1) fun x6 => !(decide (x4 + x5 + x6 ≤ m2) && decide (x2 + x6 + x10 ≤ m4)) ||
    allLt (k + 1) fun x9 => !(decide (x9 + x10 ≤ m2) &&
      decide (x5 + x9 ≤ m4) &&
      decide (x9 + x10 ≤ k)) ||
    allLt (k + 1) fun x11 => !(decide (x9 + x10 + x11 ≤ m2) &&
      decide (x2 + x10 + x11 ≤ m3) &&
      decide (x9 + x10 + x11 ≤ k)) ||
    allLt (k + 1) fun x13 => !(decide (x4 + x5 + x13 ≤ m3) &&
      decide (x5 + x9 + x13 ≤ m4) &&
      decide (x9 + x10 + x11 + x13 ≤ k)) ||
    allLt (k + 1) fun x1 => !(decide (x1 + x5 + x9 + x13 = m4)) ||
    allLt (k + 1) fun x3 => !(decide (x2 + x3 + x10 + x11 = m3)) ||
    allLt (k + 1) fun x7 => !(decide (x4 + x5 + x6 + x7 = m2)) ||
    allLt (k + 1) fun x8 => !(decide (x8 + x9 + x10 + x11 = m2) &&
        decide (x8 + x9 + x10 + x11 + x13 ≤ k)) ||
    allLt (k + 1) fun x12 => !(decide (x4 + x5 + x12 + x13 = m3) &&
        decide (x8 + x9 + x10 + x11 + x12 + x13 ≤ k)) ||
    allLt (k + 1) fun x14 => !(decide (x2 + x6 + x10 + x14 = m4) &&
        decide (x8 + x9 + x10 + x11 + x12 + x13 + x14 ≤ k)) ||
    allLt (k + 1) fun x15 => !(decide (x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 = k)) ||
    hit [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15]

/-- A table of certificates accepts the atom sizes of its entries. -/
def hitIn {α : Type*} (table : List α) (atoms : α → List (Mem × ℕ)) (xs : List ℕ) : Bool :=
  table.any fun sp => decide (memList.tail.map (asz (atoms sp)) = xs)

/-- The list sizes and consecutive intersections by atom sizes. -/
theorem venn_lin (B₁ B₂ B₃ B₄ : Finset ℕ) :
    (B₁.card : ℤ) =
      ((atomSet B₁ B₂ B₃ B₄ (true, false, false, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, false, false, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, false, true, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, false, true, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, false, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, false, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, true, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, true, true)).card : ℤ) ∧
    (B₂.card : ℤ) =
      ((atomSet B₁ B₂ B₃ B₄ (false, true, false, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (false, true, false, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (false, true, true, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (false, true, true, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, false, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, false, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, true, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, true, true)).card : ℤ) ∧
    (B₃.card : ℤ) =
      ((atomSet B₁ B₂ B₃ B₄ (false, false, true, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (false, false, true, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (false, true, true, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (false, true, true, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, false, true, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, false, true, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, true, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, true, true)).card : ℤ) ∧
    (B₄.card : ℤ) =
      ((atomSet B₁ B₂ B₃ B₄ (false, false, false, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (false, false, true, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (false, true, false, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (false, true, true, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, false, false, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, false, true, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, false, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, true, true)).card : ℤ) ∧
    ((B₁ ∩ B₂).card : ℤ) =
      ((atomSet B₁ B₂ B₃ B₄ (true, true, false, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, false, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, true, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, true, true)).card : ℤ) ∧
    ((B₂ ∩ B₃).card : ℤ) =
      ((atomSet B₁ B₂ B₃ B₄ (false, true, true, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (false, true, true, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, true, false)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, true, true)).card : ℤ) ∧
    ((B₃ ∩ B₄).card : ℤ) =
      ((atomSet B₁ B₂ B₃ B₄ (false, false, true, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (false, true, true, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, false, true, true)).card : ℤ)
      + ((atomSet B₁ B₂ B₃ B₄ (true, true, true, true)).card : ℤ) := by
  have h := vennOf_eq B₁ B₂ B₃ B₄
  simp only [vennOf, vennFn, Venn.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h12, h23, h34, -⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]; simp [vsum, memList]; ring
  · rw [h2]; simp [vsum, memList]; ring
  · rw [h3]; simp [vsum, memList]; ring
  · rw [h4]; simp [vsum, memList]; ring
  · rw [h12]; simp [vsum, memList]; ring
  · rw [h23]; simp [vsum, memList]; ring
  · rw [h34]; simp [vsum, memList]; ring

theorem hitIn_atoms {α : Type*} {table : List α} {atoms : α → List (Mem × ℕ)}
    {B₁ B₂ B₃ B₄ : Finset ℕ}
    (h : hitIn table atoms (memList.tail.map fun m => (atomSet B₁ B₂ B₃ B₄ m).card) = true) :
    ∃ sp ∈ table, ∀ m : Mem, m ≠ mem0 → (atomSet B₁ B₂ B₃ B₄ m).card = asz (atoms sp) m := by
  obtain ⟨sp, hsp, he⟩ := List.any_eq_true.mp h
  refine ⟨sp, hsp, ?_⟩
  have he' := of_decide_eq_true he
  simp only [memList, List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    at he'
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := he'
  intro m hm
  rcases m with ⟨_ | _, _ | _, _ | _, _ | _⟩
  all_goals first
    | exact absurd rfl hm | exact e1.symm | exact e2.symm | exact e3.symm | exact e4.symm
    | exact e5.symm | exact e6.symm | exact e7.symm | exact e8.symm | exact e9.symm
    | exact e10.symm | exact e11.symm | exact e12.symm | exact e13.symm | exact e14.symm
    | exact e15.symm

/-- **The shapes of the exact mismatch triples**: a checked enumeration accepts the atom sizes of
any four `k`-lists whose mismatch triple it covers. -/
theorem dispatch_of_check {k M : ℕ} {E : ℕ → ℕ → ℕ → Bool} {hit : List ℕ → Bool}
    (hc : dispatchCheck k M E hit = true) {B₁ B₂ B₃ B₄ : Finset ℕ} {m2 m3 m4 : ℕ}
    (hM : m2 < M ∧ m3 < M ∧ m4 < M) (hE : E m2 m3 m4 = true)
    (hB₁ : B₁.card = k) (hB₂ : B₂.card = k) (hB₃ : B₃.card = k) (hB₄ : B₄.card = k)
    (h12 : (B₁ ∩ B₂).card + m2 = k) (h23 : (B₂ ∩ B₃).card + m3 = k)
    (h34 : (B₃ ∩ B₄).card + m4 = k) :
    hit (memList.tail.map fun m => (atomSet B₁ B₂ B₃ B₄ m).card) = true := by
  obtain ⟨l1, l2, l3, l4, l12, l23, l34⟩ := venn_lin B₁ B₂ B₃ B₄
  obtain ⟨u2, u3, u4⟩ := hM
  have h := allLt_spec hc m2 (by omega)
  have h := allLt_spec h m3 (by omega)
  have h := allLt_spec h m4 (by omega)
  have h := imp_spec h hE
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (false, true, false, true)).card (by omega)
  have h := imp_spec h (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (true, false, true, false)).card (by omega)
  have h := imp_spec h (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (false, false, true, false)).card (by omega)
  have h := imp_spec h (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (false, true, false, false)).card (by omega)
  have h := imp_spec h (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (false, true, true, false)).card (by omega)
  have h := imp_spec h (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (true, false, false, true)).card (by omega)
  have h := imp_spec h (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (true, false, true, true)).card (by omega)
  have h := imp_spec h (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (true, true, false, true)).card (by omega)
  have h := imp_spec h (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (false, false, false, true)).card (by omega)
  have h := imp_spec h (by simp only [decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (false, false, true, true)).card (by omega)
  have h := imp_spec h (by simp only [decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (false, true, true, true)).card (by omega)
  have h := imp_spec h (by simp only [decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (true, false, false, false)).card (by omega)
  have h := imp_spec h (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (true, true, false, false)).card (by omega)
  have h := imp_spec h (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (true, true, true, false)).card (by omega)
  have h := imp_spec h (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
  have h := allLt_spec h (atomSet B₁ B₂ B₃ B₄ (true, true, true, true)).card (by omega)
  have h := imp_spec h (by simp only [decide_eq_true_eq]; omega)
  exact h

end GridGen.Four
