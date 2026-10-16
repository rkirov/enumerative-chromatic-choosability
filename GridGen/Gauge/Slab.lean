/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Uniform
import GridGen.Gauge.CSP

/-!
# The slab: one past column, the seam column, and the future

At a seam the telescoped quantity is a count of DP-colourings of a slab of the grid. The slab
has `m` rows and `c + 2` columns:

* column `0` — the past column. It is coloured from lists `P` (the actual lists with the colour
  of the column before removed);
* column `1` — the seam column, coloured from the `k`-lists `A`;
* columns `2, …, c + 1` — the future, coloured with labels `0, …, k-1`.

Vertical edges and horizontal edges are equality constraints, except the seam edge between
columns `1` and `2` in row `v`. There colour `a` at `(1, v)` clashes with label `b` at `(2, v)`
exactly when `M v a = b`. A *key* `M v a ≥ k` therefore means that `a` is unpaired (a "star").

`card_Ω_eq` identifies the number of slab solutions with
`∑_p ∑_{s ∼ p} F (c) (M ∘ s)`, the quantity the gauge telescope needs.
-/

open Finset SimpleGraph
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

/-- The row graph: the path on `Fin m`, with explicit adjacency. -/
def rowG (m : ℕ) : SimpleGraph (Fin m) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun _ h => by rcases h with h | h <;> omega⟩

instance (m : ℕ) : DecidableRel (rowG m).Adj := fun u v =>
  inferInstanceAs (Decidable (u.val + 1 = v.val ∨ v.val + 1 = u.val))

theorem rowG_adj {m : ℕ} {u v : Fin m} : (rowG m).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val :=
  Iff.rfl

/-- A slab cell: column, row. -/
abbrev Cell (c m : ℕ) := Fin (c + 2) × Fin m

/-- Slab adjacency: same column and consecutive rows, or same row and consecutive columns. -/
def slabAdj {c m : ℕ} (x y : Cell c m) : Prop :=
  (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
    (x.2 = y.2 ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val))

/-- The slab constraint system. -/
def slab (c m k : ℕ) (P A : Fin m → Finset ℕ) (M : Fin m → ℕ → ℕ) : CSP (Cell c m) where
  adj := slabAdj
  D x := if x.1.val = 0 then P x.2 else if x.1.val = 1 then A x.2 else range k
  conf x y a b :=
    if x.1.val = 1 ∧ y.1.val = 2 then M x.2 a = b
    else if x.1.val = 2 ∧ y.1.val = 1 then a = M y.2 b
    else a = b

variable {c m k : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

/-! ### Columns of a slab assignment -/

/-- Column `j` of an assignment (as a state of the row graph). -/
def colOf (f : Cell c m → ℕ) (j : Fin (c + 2)) : State (Fin m) := fun v => f (j, v)

/-- The future columns, `0`-indexed. -/
def futOf (f : Cell c m → ℕ) : Fin c → State (Fin m) := fun t v => f (⟨t.val + 2, by omega⟩, v)

/-- Valid future sequences after a seam state `q`: labels below `k`, proper columns, the first
column compatible with `q`, consecutive columns compatible. -/
def FutValid (k : ℕ) (q : State (Fin m)) (ψ : Fin c → State (Fin m)) : Prop :=
  (∀ t, ψ t ∈ states (rowG m) (unif k)) ∧ (∀ t : Fin c, t.val = 0 → Compat q (ψ t)) ∧
    ∀ t t' : Fin c, t.val + 1 = t'.val → Compat (ψ t) (ψ t')

/-- The finset of valid futures. -/
noncomputable def futs (c k : ℕ) (q : State (Fin m)) : Finset (Fin c → State (Fin m)) :=
  (Fintype.piFinset fun _ : Fin c => states (rowG m) (unif k)).filter (FutValid k q)

theorem mem_futs {q : State (Fin m)} {ψ : Fin c → State (Fin m)} :
    ψ ∈ futs c k q ↔ FutValid k q ψ := by
  unfold futs
  rw [mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- **The futures count `F`.** -/
theorem card_futs (k : ℕ) : ∀ (c : ℕ) (q : State (Fin m)), (futs c k q).card = F (rowG m) k c q := by
  intro c
  induction c with
  | zero =>
      intro q
      rw [F_zero]
      refine card_eq_one.mpr ⟨fun t => Fin.elim0 t, ?_⟩
      ext ψ
      simp only [mem_singleton, mem_futs]
      constructor
      · intro _; funext t; exact Fin.elim0 t
      · intro _; exact ⟨fun t => Fin.elim0 t, fun t => Fin.elim0 t, fun t => Fin.elim0 t⟩
  | succ c ih =>
      intro q
      rw [F_succ, ← sum_congr rfl fun t _ => ih t]
      -- split a future by its first column
      rw [card_eq_sum_card_fiberwise (f := fun ψ : Fin (c + 1) → State (Fin m) => ψ 0)
        (t := (states (rowG m) (unif k)).filter (Compat q))]
      · refine sum_congr rfl fun t ht => ?_
        rw [mem_filter] at ht
        refine card_bij (fun ψ _ => Fin.tail ψ) ?_ ?_ ?_
        · intro ψ hψ
          rw [mem_filter, mem_futs] at hψ
          rw [mem_futs]
          refine ⟨fun s => hψ.1.1 s.succ, fun s hs => ?_, fun s s' hss => ?_⟩
          · have := hψ.1.2.2 0 s.succ (by simp [hs])
            rw [hψ.2] at this
            exact this
          · exact hψ.1.2.2 s.succ s'.succ (by simp [hss])
        · intro ψ hψ ψ' hψ' he
          rw [mem_filter] at hψ hψ'
          funext s
          refine Fin.cases ?_ (fun s => ?_) s
          · rw [hψ.2, hψ'.2]
          · exact congrFun he s
        · intro χ hχ
          rw [mem_futs] at hχ
          refine ⟨Fin.cons t χ, ?_, by simp⟩
          rw [mem_filter, mem_futs]
          refine ⟨⟨fun s => ?_, fun s hs => ?_, fun s s' hss => ?_⟩, by simp⟩
          · refine Fin.cases ?_ (fun s => ?_) s
            · simpa using ht.1
            · simpa using hχ.1 s
          · have : s = 0 := Fin.ext hs
            subst this; simpa using ht.2
          · obtain ⟨σ', rfl⟩ : ∃ σ' : Fin c, s' = σ'.succ :=
              ⟨⟨s'.val - 1, by omega⟩, by ext; simp; omega⟩
            by_cases h0 : s.val = 0
            · have : s = 0 := Fin.ext h0
              subst this
              simpa using hχ.2.1 σ' (by simp at hss; omega)
            · obtain ⟨σ, rfl⟩ : ∃ σ : Fin c, s = σ.succ :=
                ⟨⟨s.val - 1, by omega⟩, by ext; simp; omega⟩
              simpa using hχ.2.2 σ σ' (by simp at hss; omega)
      · intro ψ hψ
        rw [Finset.mem_coe, mem_futs] at hψ
        rw [Finset.mem_coe, mem_filter]
        exact ⟨hψ.1 0, hψ.2.1 0 rfl⟩

/-! ### Slab solutions are (past state, seam state, future) -/

/-- The seam state seen through the keys: row `v` presents `M v (s v)` to the future. -/
def keyed (M : Fin m → ℕ → ℕ) (s : State (Fin m)) : State (Fin m) := fun v => M v (s v)

theorem slab_D_zero {x : Cell c m} (h : x.1.val = 0) : (slab c m k P A M).D x = P x.2 := by
  simp only [slab]; rw [ite_eq_left h]

theorem slab_D_one {x : Cell c m} (h : x.1.val = 1) : (slab c m k P A M).D x = A x.2 := by
  simp only [slab]; rw [ite_eq_right (by omega), ite_eq_left h]

theorem slab_D_fut {x : Cell c m} (h : 2 ≤ x.1.val) : (slab c m k P A M).D x = range k := by
  simp only [slab]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem slab_conf_seam {x y : Cell c m} (hx : x.1.val = 1) (hy : y.1.val = 2) {a b : ℕ} :
    (slab c m k P A M).conf x y a b ↔ M x.2 a = b := by
  simp only [slab]; rw [ite_eq_left ⟨hx, hy⟩]

theorem slab_conf_seam' {x y : Cell c m} (hx : x.1.val = 2) (hy : y.1.val = 1) {a b : ℕ} :
    (slab c m k P A M).conf x y a b ↔ a = M y.2 b := by
  simp only [slab]; rw [ite_eq_right (by omega), ite_eq_left ⟨hx, hy⟩]

theorem slab_conf_eq {x y : Cell c m} (h1 : ¬ (x.1.val = 1 ∧ y.1.val = 2))
    (h2 : ¬ (x.1.val = 2 ∧ y.1.val = 1)) {a b : ℕ} :
    (slab c m k P A M).conf x y a b ↔ a = b := by
  simp only [slab]
  rw [ite_eq_right h1, ite_eq_right h2]

/-- Glue a past state, a seam state and a future into a slab assignment. -/
def glue (p s : State (Fin m)) (ψ : Fin c → State (Fin m)) : Cell c m → ℕ := fun x =>
  if h0 : x.1.val = 0 then p x.2 else if h1 : x.1.val = 1 then s x.2
  else ψ ⟨x.1.val - 2, by have := x.1.isLt; omega⟩ x.2

theorem glue_zero (p s : State (Fin m)) (ψ : Fin c → State (Fin m)) (v : Fin m) :
    glue p s ψ (0, v) = p v := by simp [glue]

theorem glue_one (p s : State (Fin m)) (ψ : Fin c → State (Fin m)) (v : Fin m) :
    glue p s ψ (1, v) = s v := by simp [glue]

theorem glue_fut (p s : State (Fin m)) (ψ : Fin c → State (Fin m)) (t : Fin c) (v : Fin m) :
    glue p s ψ (⟨t.val + 2, by omega⟩, v) = ψ t v := by
  simp [glue]

theorem colOf_zero_eq (f : Cell c m → ℕ) (v : Fin m) : colOf f 0 v = f (0, v) := rfl

/-- **Slab validity, column by column.** -/
theorem valid_iff (f : Cell c m → ℕ) :
    (slab c m k P A M).Valid f ↔
      colOf f 0 ∈ states (rowG m) P ∧ colOf f 1 ∈ states (rowG m) A ∧
        Compat (colOf f 0) (colOf f 1) ∧ FutValid k (keyed M (colOf f 1)) (futOf f) := by
  constructor
  · rintro ⟨hD, hC⟩
    -- vertical edges in any column are equality constraints
    have hvert : ∀ (j : Fin (c + 2)) (u v : Fin m), (rowG m).Adj u v → f (j, u) ≠ f (j, v) := by
      intro j u v huv
      have hadj : (slab c m k P A M).adj (j, u) (j, v) := Or.inl ⟨rfl, huv⟩
      have := hC _ _ hadj
      rwa [slab_conf_eq (show ¬ (j.val = 1 ∧ j.val = 2) by omega)
        (show ¬ (j.val = 2 ∧ j.val = 1) by omega)] at this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_states]
      refine ⟨fun v => ?_, fun u v huv => hvert 0 u v huv⟩
      have := hD (0, v); rwa [slab_D_zero (show (0 : Fin (c + 2)).val = 0 from rfl)] at this
    · rw [mem_states]
      refine ⟨fun v => ?_, fun u v huv => hvert 1 u v huv⟩
      have := hD (1, v)
      rwa [slab_D_one (x := ((1 : Fin (c + 2)), v)) (Fin.val_one _)] at this
    · intro v
      have hadj : (slab c m k P A M).adj (0, v) (1, v) :=
        Or.inr ⟨rfl, Or.inl (show (0 : Fin (c + 2)).val + 1 = (1 : Fin (c + 2)).val by
          rw [Fin.val_one]; rfl)⟩
      have := hC _ _ hadj
      rwa [slab_conf_eq (show ¬ ((0 : Fin (c + 2)).val = 1 ∧ (1 : Fin (c + 2)).val = 2) by
        simp) (show ¬ ((0 : Fin (c + 2)).val = 2 ∧ (1 : Fin (c + 2)).val = 1) by simp)] at this
    · intro t
      rw [mem_states]
      refine ⟨fun v => ?_, fun u v huv => hvert _ u v huv⟩
      have := hD (⟨t.val + 2, by omega⟩, v)
      rwa [slab_D_fut (show 2 ≤ t.val + 2 by omega)] at this
    · intro t ht v
      have h1 : (1 : Fin (c + 2)).val = 1 := Fin.val_one _
      have hadj : (slab c m k P A M).adj (1, v) (⟨t.val + 2, by omega⟩, v) :=
        Or.inr ⟨rfl, Or.inl (show (1 : Fin (c + 2)).val + 1 = t.val + 2 by omega)⟩
      have := hC _ _ hadj
      rw [slab_conf_seam (show (1 : Fin (c + 2)).val = 1 from h1)
        (show t.val + 2 = 2 by omega)] at this
      exact this
    · intro t t' htt v
      have hadj : (slab c m k P A M).adj (⟨t.val + 2, by omega⟩, v) (⟨t'.val + 2, by omega⟩, v) :=
        Or.inr ⟨rfl, Or.inl (show t.val + 2 + 1 = t'.val + 2 by omega)⟩
      have := hC _ _ hadj
      rwa [slab_conf_eq (show ¬ (t.val + 2 = 1 ∧ t'.val + 2 = 2) by omega)
        (show ¬ (t.val + 2 = 2 ∧ t'.val + 2 = 1) by omega)] at this
  · rintro ⟨h0, h1, h01, hψ⟩
    rw [mem_states] at h0 h1
    refine ⟨fun x => ?_, fun x y hxy => ?_⟩
    · obtain ⟨j, v⟩ := x
      by_cases hj0 : j.val = 0
      · rw [slab_D_zero hj0]
        have : j = 0 := Fin.ext hj0
        subst this; exact h0.1 v
      by_cases hj1 : j.val = 1
      · rw [slab_D_one hj1]
        have : j = 1 := Fin.ext (by rw [Fin.val_one]; exact hj1)
        subst this; exact h1.1 v
      · rw [slab_D_fut (show 2 ≤ j.val by omega)]
        have := ((mem_states (rowG m)).mp (hψ.1 ⟨j.val - 2, by omega⟩)).1 v
        simp only [unif] at this
        convert this using 2
        simp only [futOf]; congr 2; ext; simp; omega
    · obtain ⟨j, v⟩ := x
      obtain ⟨j', v'⟩ := y
      rcases hxy with ⟨hjj, hvv⟩ | ⟨hvv, hjj⟩
      · -- vertical edge
        simp only at hjj hvv
        subst hjj
        rw [slab_conf_eq (show ¬ (j.val = 1 ∧ j.val = 2) by omega)
          (show ¬ (j.val = 2 ∧ j.val = 1) by omega)]
        by_cases hj0 : j.val = 0
        · have : j = 0 := Fin.ext hj0
          subst this; exact h0.2 hvv
        by_cases hj1 : j.val = 1
        · have : j = 1 := Fin.ext (by rw [Fin.val_one]; exact hj1)
          subst this; exact h1.2 hvv
        · have := ((mem_states (rowG m)).mp (hψ.1 ⟨j.val - 2, by omega⟩)).2 hvv
          have e : ∀ w, futOf f ⟨j.val - 2, by omega⟩ w = f (j, w) := by
            intro w; simp only [futOf]; congr 2; ext; simp; omega
          rwa [e, e] at this
      · -- horizontal edge
        simp only at hjj hvv
        subst hvv
        rcases hjj with hjj | hjj
        · -- j' = j + 1
          by_cases hj0 : j.val = 0
          · rw [slab_conf_eq (show ¬ (j.val = 1 ∧ j'.val = 2) by omega)
              (show ¬ (j.val = 2 ∧ j'.val = 1) by omega)]
            have e0 : j = 0 := Fin.ext hj0
            have e1 : j' = 1 := Fin.ext (by rw [Fin.val_one]; omega)
            subst e0; subst e1; exact h01 v
          by_cases hj1 : j.val = 1
          · rw [slab_conf_seam (show j.val = 1 from hj1) (show j'.val = 2 by omega)]
            have e1 : j = 1 := Fin.ext (by rw [Fin.val_one]; exact hj1)
            subst e1
            have := hψ.2.1 ⟨0, by omega⟩ rfl v
            have e : futOf f ⟨0, by omega⟩ v = f (j', v) := by
              simp only [futOf]; congr 2; ext; simp; omega
            rw [e] at this; exact this
          · rw [slab_conf_eq (show ¬ (j.val = 1 ∧ j'.val = 2) by omega)
              (show ¬ (j.val = 2 ∧ j'.val = 1) by omega)]
            have := hψ.2.2 ⟨j.val - 2, by omega⟩ ⟨j'.val - 2, by omega⟩ (show j.val - 2 + 1 = j'.val - 2 by omega) v
            have e : ∀ (i : Fin (c + 2)) (hi : 2 ≤ i.val), futOf f ⟨i.val - 2, by omega⟩ v = f (i, v) := by
              intro i hi; simp only [futOf]; congr 2; ext; simp; omega
            rwa [e j (by omega), e j' (by omega)] at this
        · -- j = j' + 1
          by_cases hj0 : j'.val = 0
          · rw [slab_conf_eq (show ¬ (j.val = 1 ∧ j'.val = 2) by omega)
              (show ¬ (j.val = 2 ∧ j'.val = 1) by omega)]
            have e0 : j' = 0 := Fin.ext hj0
            have e1 : j = 1 := Fin.ext (by rw [Fin.val_one]; omega)
            subst e0; subst e1; exact fun h => h01 v h.symm
          by_cases hj1 : j'.val = 1
          · rw [slab_conf_seam' (show j.val = 2 by omega) (show j'.val = 1 from hj1)]
            have e1 : j' = 1 := Fin.ext (by rw [Fin.val_one]; exact hj1)
            subst e1
            have := hψ.2.1 ⟨0, by omega⟩ rfl v
            have e : futOf f ⟨0, by omega⟩ v = f (j, v) := by
              simp only [futOf]; congr 2; ext; simp; omega
            rw [e] at this; exact fun h => this h.symm
          · rw [slab_conf_eq (show ¬ (j.val = 1 ∧ j'.val = 2) by omega)
              (show ¬ (j.val = 2 ∧ j'.val = 1) by omega)]
            have := hψ.2.2 ⟨j'.val - 2, by omega⟩ ⟨j.val - 2, by omega⟩ (show j'.val - 2 + 1 = j.val - 2 by omega) v
            have e : ∀ (i : Fin (c + 2)) (hi : 2 ≤ i.val), futOf f ⟨i.val - 2, by omega⟩ v = f (i, v) := by
              intro i hi; simp only [futOf]; congr 2; ext; simp; omega
            rw [e j' (by omega), e j (by omega)] at this
            exact fun h => this h.symm

theorem colOf_glue_zero (p s : State (Fin m)) (ψ : Fin c → State (Fin m)) :
    colOf (glue p s ψ) 0 = p := by
  funext v; simp [colOf, glue]

theorem colOf_glue_one (p s : State (Fin m)) (ψ : Fin c → State (Fin m)) :
    colOf (glue p s ψ) 1 = s := by
  funext v; simp [colOf, glue]

theorem futOf_glue (p s : State (Fin m)) (ψ : Fin c → State (Fin m)) :
    futOf (glue p s ψ) = ψ := by
  funext t v; simp only [futOf, glue]
  rw [dite_eq_right (by simp), dite_eq_right (by simp)]
  congr 1

theorem glue_cols (f : Cell c m → ℕ) : glue (colOf f 0) (colOf f 1) (futOf f) = f := by
  funext x
  obtain ⟨j, v⟩ := x
  simp only [glue, colOf, futOf]
  by_cases h0 : j.val = 0
  · rw [dite_eq_left h0]; congr; exact (Fin.ext h0).symm
  rw [dite_eq_right h0]
  by_cases h1 : j.val = 1
  · rw [dite_eq_left h1]; congr; exact (Fin.ext (by rw [Fin.val_one]; exact h1)).symm
  rw [dite_eq_right h1]
  exact congrArg f (Prod.ext (Fin.ext (show j.val - 2 + 2 = j.val by omega)) rfl)

/-- **The slab count.** The number of slab solutions is the past–seam pairs weighted by the
futures of their keyed seam states. -/
theorem card_Ω_eq :
    (slab c m k P A M).Ω.card = ∑ p ∈ states (rowG m) P,
      ∑ s ∈ (states (rowG m) A).filter (Compat p), F (rowG m) k c (keyed M s) := by
  set T := (states (rowG m) P ×ˢ states (rowG m) A).filter
    (fun ps : State (Fin m) × State (Fin m) => Compat ps.1 ps.2)
  rw [card_eq_sum_card_fiberwise (f := fun f => (colOf f 0, colOf f 1)) (t := T)]
  · rw [Finset.sum_filter, Finset.sum_product]
    refine sum_congr rfl fun p _ => ?_
    rw [Finset.sum_filter]
    refine sum_congr rfl fun s _ => ?_
    split_ifs with hps
    · rw [← card_futs]
      refine card_bij (fun f _ => futOf f) ?_ ?_ ?_
      · intro f hf
        rw [mem_filter, CSP.mem_Ω, valid_iff] at hf
        obtain ⟨⟨_, _, _, hψ⟩, he⟩ := hf
        simp only [Prod.mk.injEq] at he
        rw [mem_futs, ← he.2]; exact hψ
      · intro f hf f' hf' hff
        rw [mem_filter] at hf hf'
        simp only [Prod.mk.injEq] at hf hf'
        rw [← glue_cols f, ← glue_cols f', hf.2.1, hf.2.2, hf'.2.1, hf'.2.2, hff]
      · intro ψ hψ
        refine ⟨glue p s ψ, ?_, futOf_glue _ _ _⟩
        rw [mem_filter, CSP.mem_Ω, valid_iff, colOf_glue_zero, colOf_glue_one, futOf_glue]
        rw [mem_futs] at hψ
        refine ⟨⟨by assumption, by assumption, hps, hψ⟩, rfl⟩
    · rfl
  · intro f hf
    rw [Finset.mem_coe, CSP.mem_Ω, valid_iff] at hf
    rw [Finset.mem_coe, mem_filter, mem_product]
    exact ⟨⟨hf.1, hf.2.1⟩, hf.2.2.1⟩

end GridGen.Gauge
