/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Seven.Swap7
import GridGen.Gauge.Box

/-!
# Swapping the seam cell of a row

At `k = 7`, let `z = (1, r)` be a seam cell and `a₀` an unpaired colour of row `r`. Its list
neighbours `(0, r)`, `(1, r - 1)`, `(1, r + 1)` are pairwise non-adjacent, and each keeps at least
four available colours once the rest is fixed. So in every event read off these four cells, any
value of `z` is at most `(4/3)³ = 64/27` times as frequent as `a₀` (`swap_seam`).
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {c m : ℕ} {P A : Fin m → Finset ℕ} {M : Fin m → ℕ → ℕ}

/-- The list neighbours of the seam cell of row `r`. -/
noncomputable def nbS (r : Fin m) : Finset (Cell c m) :=
  univ.filter (fun w => (w.1.val = 0 ∧ w.2 = r) ∨
    (w.1.val = 1 ∧ (w.2.val + 1 = r.val ∨ w.2.val = r.val + 1)))

/-- The seam cell of row `r` with its list neighbours. -/
noncomputable def boxS (r : Fin m) : Finset (Cell c m) := insert ((1 : Fin (c + 2)), r) (nbS r)

theorem mem_nbS {r : Fin m} {w : Cell c m} : w ∈ nbS r ↔ (w.1.val = 0 ∧ w.2 = r) ∨
    (w.1.val = 1 ∧ (w.2.val + 1 = r.val ∨ w.2.val = r.val + 1)) := by
  unfold nbS; simp

theorem one_val : ((1 : Fin (c + 2))).val = 1 := Fin.val_one _

theorem seam_notMem_nbS (r : Fin m) : ((1 : Fin (c + 2)), r) ∉ nbS r := by
  rw [mem_nbS]; simp only [one_val]; omega

theorem nbS_nonadj (r : Fin m) :
    ∀ n ∈ nbS (c := c) r, ∀ n' ∈ nbS r, ¬ (slab c m 7 P A M).adj n n' := by
  intro n hn n' hn' hadj
  rw [mem_nbS] at hn hn'
  have h : slabAdj n n' := hadj
  unfold slabAdj at h
  have e1 : ∀ w : Cell c m, w.2 = r → w.2.val = r.val := fun w h => by rw [h]
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hn' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · have := e1 n h2; have := e1 n' h2'; omega
  · have := e1 n h2; omega
  · have := e1 n' h2'; omega
  · omega

theorem card_nbS_le (r : Fin m) : (nbS (c := c) r).card ≤ 3 := by
  refine card_le_of_coords _ [(0, r.val), (1, r.val - 1), (1, r.val + 1)] fun w hw => ?_
  rw [mem_nbS] at hw
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h1, by rw [h2]⟩
  · right; omega

/-- **The swap at a seam cell.** -/
theorem swap_seam (hK : KeyInj 7 A M) (hA : ∀ v, (A v).card = 7)
    (hP : ∀ v a, a ∈ A v → 6 ≤ (P v).card ∨ a ∉ P v) (r : Fin m) {a₀ a : ℕ} (ha₀ : a₀ ∈ A r)
    (h7 : 7 ≤ M r a₀) (R : (Cell c m → ℕ) → Prop) [DecidablePred R]
    (hR : CSP.OffU (boxS r) R) :
    (((slab c m 7 P A M).Ω.filter R).filter (fun f => f ((1 : Fin (c + 2)), r) = a)).card * 27 ≤
      (((slab c m 7 P A M).Ω.filter R).filter (fun f => f ((1 : Fin (c + 2)), r) = a₀)).card * 64 := by
  set C := slab c m 7 P A M
  set z : Cell c m := ((1 : Fin (c + 2)), r)
  have hM := slab_match (c := c) (P := P) hK
  have hI : (C : CSP (Cell c m)).Irrefl := slab_irrefl
  refine C.fibre_cmp_rel (boxS r) _ _ R hR 27 64 fun g hg _ => ?_
  have hgv := (C.mem_Ω).mp hg
  have hgU : C.ValidOff (boxS r) g := C.validOff_of_valid hgv
  -- the neighbours of `z` off the box: only `(2, r)`
  have hz_out : ∀ y, y ∉ boxS (c := c) r → (C.adj z y ∨ C.adj y z) → y.1.val = 2 ∧ y.2 = r := by
    intro y hy hadj
    have hc := adj_coords hadj
    simp only [z, one_val] at hc
    unfold boxS at hy
    rw [mem_insert, mem_nbS, not_or] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hne : y ≠ z := hy1
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; apply hy2; right; exact ⟨h1, by omega⟩
    · rcases h2 with h2 | h2
      · exfalso; apply hy2; left; exact ⟨by omega, Fin.ext h1⟩
      · exact ⟨by omega, Fin.ext h1⟩
  have ha₀z : a₀ ∈ C.avail (boxS r) g z := by
    rw [CSP.mem_avail]
    refine ⟨by rw [slab_D_one one_val]; exact ha₀, fun y hy => ⟨fun hadj => ?_, fun hadj => ?_⟩⟩
    · obtain ⟨h1, h2⟩ := hz_out y hy (Or.inl hadj)
      rw [slab_conf_seam one_val h1]
      have hlt : g y < 7 := by
        have := hgv.1 y; rw [slab_D_fut (by omega), mem_range] at this; exact this
      show ¬ M r a₀ = g y
      omega
    · obtain ⟨h1, h2⟩ := hz_out y hy (Or.inr hadj)
      rw [slab_conf_seam' h1 one_val]
      have hlt : g y < 7 := by
        have := hgv.1 y; rw [slab_D_fut (by omega), mem_range] at this; exact this
      show ¬ g y = M r a₀
      omega
  have hup := CSP.card_cls_val_le (C := C) (seam_notMem_nbS (c := c) r) g a
  have hlo := CSP.card_cls_val_ge (C := C) (seam_notMem_nbS (c := c) r) (nbS_nonadj r) hI hgU ha₀z
  -- per neighbour: `3 |avail| ≤ 4 |compat|`
  have hper : ∀ n ∈ nbS (c := c) r, 3 * (C.avail (boxS r) g n).card ≤
      4 * (C.compat (boxS r) g z n a₀).card := by
    intro n hn
    have hnU : n ∈ boxS (c := c) r := mem_insert_of_mem hn
    -- `compat` contains the available values other than `a₀`
    have hsub : (C.avail (boxS r) g n).erase a₀ ⊆ C.compat (boxS r) g z n a₀ := by
      intro b hb
      rw [mem_erase] at hb
      unfold CSP.compat
      rw [mem_filter]
      have hn' := (mem_nbS.mp hn)
      have hnot1 : ¬ (z.1.val = 1 ∧ n.1.val = 2) := by simp only [z, one_val]; omega
      have hnot2 : ¬ (z.1.val = 2 ∧ n.1.val = 1) := by simp only [z, one_val]; omega
      have hnot3 : ¬ (n.1.val = 1 ∧ z.1.val = 2) := by simp only [z, one_val]; omega
      have hnot4 : ¬ (n.1.val = 2 ∧ z.1.val = 1) := by simp only [z, one_val]; omega
      refine ⟨hb.2, fun _ => ?_, fun _ => ?_⟩
      · rw [slab_conf_eq hnot1 hnot2]; exact fun e => hb.1 e.symm
      · rw [slab_conf_eq hnot3 hnot4]; exact hb.1
    by_cases hin : a₀ ∈ C.avail (boxS r) g n
    · -- at least four available colours
      have hge : 4 ≤ (C.avail (boxS r) g n).card := by
        have hav := C.card_avail_ge hM hI hnU (fun y _ => hgv.1 y)
        rcases mem_nbS.mp hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hP6 : 6 ≤ (P r).card := by
            have hD := (C.mem_avail.mp hin).1
            rw [slab_D_zero h1, h2] at hD
            exact (hP r a₀ ha₀).resolve_right (not_not.mpr hD)
          have hout : (C.nbrsOut n (boxS r)).card ≤ 2 := by
            refine card_le_of_coords _ [(0, r.val - 1), (0, r.val + 1)] fun w hw => ?_
            rw [CSP.mem_nbrsOut] at hw
            have hc := adj_coords hw.1
            have hB := hw.2
            unfold boxS at hB
            rw [mem_insert, mem_nbS, not_or] at hB
            have hn2 : n.2.val = r.val := by rw [h2]
            rw [h1, hn2] at hc
            simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
            have hw1 : w ≠ z := hB.1
            have hw2 := hB.2
            rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · omega
            · exfalso
              rcases e2 with e2 | e2
              · omega
              · apply hw1; exact cell_eq (by simp [z]; omega) (by simp [z]; omega)
          rw [slab_D_zero h1, h2] at hav
          omega
        · have hout : (C.nbrsOut n (boxS r)).card ≤ 3 := by
            refine card_le_of_coords _ [(0, n.2.val), (1, n.2.val + n.2.val - r.val), (2, n.2.val)]
              fun w hw => ?_
            rw [CSP.mem_nbrsOut] at hw
            have hc := adj_coords hw.1
            have hB := hw.2
            unfold boxS at hB
            rw [mem_insert, mem_nbS, not_or] at hB
            rw [h1] at hc
            simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
            have hw1 : w ≠ z := hB.1
            rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · -- vertical neighbour in the seam column: not `z`
              right; left
              refine ⟨e1, ?_⟩
              rcases e2 with e2 | e2 <;> rcases h2 with h2 | h2
              · omega
              · exfalso; apply hw1; exact cell_eq (by simp [z]; omega) (by simp [z]; omega)
              · exfalso; apply hw1; exact cell_eq (by simp [z]; omega) (by simp [z]; omega)
              · omega
            · rcases e2 with e2 | e2
              · left; exact ⟨by omega, e1⟩
              · right; right; exact ⟨by omega, e1⟩
          rw [slab_D_one h1, hA] at hav
          omega
      have := card_le_card hsub
      rw [card_erase_of_mem hin] at this
      omega
    · rw [erase_eq_of_notMem hin] at hsub
      have := card_le_card hsub
      omega
  -- the products
  have hprod : 3 ^ (nbS (c := c) r).card * ∏ n ∈ nbS r, (C.avail (boxS r) g n).card ≤
      4 ^ (nbS (c := c) r).card * ∏ n ∈ nbS r, (C.compat (boxS r) g z n a₀).card := by
    rw [← prod_const, ← prod_const, ← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_le_prod fun n hn => hper n hn
  have hN := card_nbS_le (c := c) r
  have h27 : 27 * ∏ n ∈ nbS (c := c) r, (C.avail (boxS r) g n).card ≤
      64 * ∏ n ∈ nbS r, (C.compat (boxS r) g z n a₀).card := by
    set p := ∏ n ∈ nbS (c := c) r, (C.avail (boxS r) g n).card
    set q := ∏ n ∈ nbS (c := c) r, (C.compat (boxS r) g z n a₀).card
    interval_cases h : (nbS (c := c) r).card <;> norm_num at hprod <;> nlinarith
  calc ((C.cls (boxS r) g).filter (fun f => f z = a)).card * 27
      ≤ (∏ n ∈ nbS r, (C.avail (boxS r) g n).card) * 27 := Nat.mul_le_mul_right _ hup
    _ ≤ (∏ n ∈ nbS r, (C.compat (boxS r) g z n a₀).card) * 64 := by linarith
    _ ≤ ((C.cls (boxS r) g).filter (fun f => f z = a₀)).card * 64 := Nat.mul_le_mul_right _ hlo

end GridGen.Gauge
