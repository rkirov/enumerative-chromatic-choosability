/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.K4.Assemble

/-!
# Height four at `k = 4`: nodes with explicit lists (layer B3)

For seventeen next-column shapes even the exact minimum-over-lists recurrence is negative, and
Codex's (OpenAI) proof (`ai_research_notes/cx/h4k4b/NOTE.md`, "branch on actual lists") fixes the
actual lists of some rows, sums the seam over them, and bounds the remaining rows by the
recurrence of the summed function; the configurations that stay negative when every list is
fixed are the bad patterns.

A **general node** has a table of colour masks (`cols`, colour ids `0, …, len - 1`) and, for each
row, nothing (free) or a list of colour ids: one id for a row placed by the recurrence, three or
four for an explicit list. A realization sends the ids to distinct colours with these masks
(`GNode.Real`); filling the free rows with lists `Y` gives a column (`gfill`).
-/

namespace GridGen.Four.K4

open Finset

/-- A general node. -/
structure GNode where
  cols : List ℕ
  r0 : Option (List ℕ)
  r1 : Option (List ℕ)
  r2 : Option (List ℕ)
  r3 : Option (List ℕ)

/-- A row of a general node. -/
def GNode.get (nd : GNode) : ℕ → Option (List ℕ)
  | 0 => nd.r0
  | 1 => nd.r1
  | 2 => nd.r2
  | _ => nd.r3

/-- Set a row of a general node. -/
def GNode.set (nd : GNode) (i : ℕ) (p : Option (List ℕ)) : GNode :=
  match i with
  | 0 => ⟨nd.cols, p, nd.r1, nd.r2, nd.r3⟩
  | 1 => ⟨nd.cols, nd.r0, p, nd.r2, nd.r3⟩
  | 2 => ⟨nd.cols, nd.r0, nd.r1, p, nd.r3⟩
  | _ => ⟨nd.cols, nd.r0, nd.r1, nd.r2, p⟩

/-- Add colours to the table. -/
def GNode.addCols (nd : GNode) (ms : List ℕ) : GNode := ⟨nd.cols ++ ms, nd.r0, nd.r1, nd.r2, nd.r3⟩

/-- The empty general node. -/
def GNode.root : GNode := ⟨[], none, none, none, none⟩

theorem GNode.get_set_same (nd : GNode) {i : ℕ} (hi : i < 4) (p : Option (List ℕ)) :
    (nd.set i p).get i = p := by
  interval_cases i <;> rfl

theorem GNode.get_set_ne (nd : GNode) {i j : ℕ} (hi : i < 4) (hj : j < 4) (h : j ≠ i)
    (p : Option (List ℕ)) : (nd.set i p).get j = nd.get j := by
  interval_cases i <;> interval_cases j <;> first | rfl | exact absurd rfl h

theorem GNode.cols_set (nd : GNode) (i : ℕ) (p : Option (List ℕ)) : (nd.set i p).cols = nd.cols := by
  unfold GNode.set; split <;> rfl

theorem GNode.get_addCols (nd : GNode) (ms : List ℕ) (j : ℕ) : (nd.addCols ms).get j = nd.get j := by
  unfold GNode.addCols GNode.get; split <;> rfl

/-- **A realization** of a general node: ids to distinct colours with the right masks; the rows
list distinct ids of the table. -/
def GNode.Real (B : Col) (nd : GNode) (ρ : ℕ → ℕ) : Prop :=
  (∀ t < nd.cols.length, mv B (ρ t) = nd.cols.getD t 0) ∧
  (∀ t < nd.cols.length, ∀ t' < nd.cols.length, ρ t = ρ t' → t = t') ∧
  (∀ j < 4, ∀ L, nd.get j = some L → (∀ t ∈ L, t < nd.cols.length) ∧ L.Nodup)

theorem GNode.real_root (B : Col) (ρ : ℕ → ℕ) : GNode.root.Real B ρ := by
  refine ⟨fun t ht => by simp [GNode.root] at ht, fun t ht => by simp [GNode.root] at ht, ?_⟩
  intro j hj L h
  interval_cases j <;> simp [GNode.root, GNode.get] at h

/-- Fill a row. -/
def gfr (p : Option (List ℕ)) (ρ : ℕ → ℕ) (Y : Finset ℕ) : Finset ℕ :=
  match p with
  | some L => (L.map ρ).toFinset
  | none => Y

/-- **The column of a general node**, its free rows filled from `Y`. -/
def gfill (nd : GNode) (ρ : ℕ → ℕ) (Y : Col) : Col :=
  (gfr nd.r0 ρ Y.1, gfr nd.r1 ρ Y.2.1, gfr nd.r2 ρ Y.2.2.1, gfr nd.r3 ρ Y.2.2.2)

theorem rowC_gfill (nd : GNode) (ρ : ℕ → ℕ) (Y : Col) {i : ℕ} (hi : i < 4) :
    rowC (gfill nd ρ Y) i = gfr (nd.get i) ρ (rowC Y i) := by
  interval_cases i <;> rfl

/-- **A good value** of a general node. -/
def GGood (B : Col) (nd : GNode) (v : V5) : Prop :=
  ∀ ρ, nd.Real B ρ → ∀ Y : Col, CardsIn 3 4 Y →
    ∀ k : Fin 5, ∀ w ∈ famW k, (v.get k).val ≤ sumP (gw B w) (gfill nd ρ Y)

/-! ### Colours of the table -/

/-- The number of table colours of mask `m`. -/
def gcnt : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: L, m => cond (Nat.beq a m) (Nat.succ (gcnt L m)) (gcnt L m)

theorem gcnt_cons (a : ℕ) (L : List ℕ) (m : ℕ) :
    gcnt (a :: L) m = gcnt L m + if a = m then 1 else 0 := by
  show cond (Nat.beq a m) (Nat.succ (gcnt L m)) (gcnt L m) = _
  cases h : Nat.beq a m
  · have : a ≠ m := fun e => by rw [e, Nat.beq_refl] at h; exact absurd h (by decide)
    simp [this]
  · rw [Nat.beq_eq] at h
    simp [h]

theorem gcnt_eq (L : List ℕ) (m : ℕ) :
    gcnt L m = ((Finset.range L.length).filter fun t => L.getD t 0 = m).card := by
  rw [Finset.card_filter]
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.length_cons, Finset.sum_range_succ', gcnt_cons, ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]

/-- The table colours. -/
def gcolSet (nd : GNode) (ρ : ℕ → ℕ) : Finset ℕ := (Finset.range nd.cols.length).image ρ

/-- **Capacity** for general nodes: a colour of mask `m ≠ 0` outside the table shows that the
table has fewer than `n_m` colours of mask `m`; with the fresh colours of a list counted too. -/
theorem gfresh_count {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : GNode} {ρ : ℕ → ℕ}
    (hρ : nd.Real B ρ) (Y : Finset ℕ) {m : ℕ} (h0 : 0 < m) (h16 : m < 16) :
    (Y.filter fun x => mv B x = m ∧ x ∉ gcolSet nd ρ).card + gcnt nd.cols m ≤ sh.na m := by
  rw [← hB.2.2 m h0 h16, gcnt_eq]
  set F := (Finset.range nd.cols.length).filter fun t => nd.cols.getD t 0 = m
  have hinj : Set.InjOn ρ ↑F := by
    intro t ht t' ht' e
    simp only [F, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ht ht'
    exact hρ.2.1 t ht.1 t' ht'.1 e
  rw [← Finset.card_image_of_injOn hinj, ← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact mem_atomN (by omega) (Finset.mem_filter.mp hc).2.1
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
      simp only [F, Finset.mem_filter, Finset.mem_range] at ht
      exact mem_atomN (by omega) ((hρ.1 t ht.1).trans ht.2)
  · rw [Finset.disjoint_left]
    intro c hc hc'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc'
    simp only [F, Finset.mem_filter, Finset.mem_range] at ht
    exact (Finset.mem_filter.mp hc).2.2 (Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht.1, rfl⟩)

theorem gused_lt {B : Col} {sh : Sh} (hB : ShapeOf B sh) {nd : GNode} {ρ : ℕ → ℕ}
    (hρ : nd.Real B ρ) {x m : ℕ} (hx : x ∉ gcolSet nd ρ) (hm : mv B x = m) (h0 : m ≠ 0) :
    gcnt nd.cols m < sh.na m := by
  have h16 : m < 16 := hm ▸ mv_lt B x
  have := gfresh_count hB hρ {x} (Nat.pos_of_ne_zero h0) h16
  have hc : ({x} : Finset ℕ).filter (fun x => mv B x = m ∧ x ∉ gcolSet nd ρ) = {x} := by
    rw [Finset.filter_eq_self]; intro y hy; rw [Finset.mem_singleton] at hy; subst hy; exact ⟨hm, hx⟩
  rw [hc, Finset.card_singleton] at this
  omega

end GridGen.Four.K4
