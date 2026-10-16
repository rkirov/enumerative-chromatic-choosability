/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Gauge.Bad

/-!
# Counting crossing paths

A crossing path is encoded by its *shape*: the start offset `d = v₁ - w ≥ 1` and the list of step
directions (up, down, right, left). The shape walk starts at `(0, d)`, never enters `x < 0`, never
reverses a step, and ends on `x = 0` at height `≤ 0` (`WOK`). The encoding is injective. Every
valid shape is produced by the pruned enumerator `enum` (`mem_enum`). So the number of crossing
paths with `L` cells is at most `∑_{d<L} |enum 0 d none (L-1)|`. That sum is `1, 2, 4, 10, 31, 76`
for `L = 2, …, 7` (by `decide`) and at most `(L-1)·3^(L-1)` in general.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

/-! ### Shape walks -/

/-- The `x`-step of a direction: `0` up, `1` down, `2` right, `3` left. -/
def dx : Fin 4 → ℤ
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => -1

/-- The `y`-step of a direction. -/
def dy : Fin 4 → ℤ
  | 0 => -1 | 1 => 1 | 2 => 0 | 3 => 0

/-- The reverse direction. -/
def opp : Fin 4 → Fin 4
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2

/-- A valid shape walk from `(x, y)` after the step `prev`. -/
def WOK : ℤ → ℤ → Option (Fin 4) → List (Fin 4) → Prop
  | x, y, _, [] => x = 0 ∧ y ≤ 0
  | x, y, prev, d :: ds => prev ≠ some (opp d) ∧ 0 ≤ x + dx d ∧ WOK (x + dx d) (y + dy d) (some d) ds

/-- The pruned enumerator of valid shape walks with `n` steps. -/
def enum : ℤ → ℤ → Option (Fin 4) → ℕ → List (List (Fin 4))
  | x, y, _, 0 => if x = 0 ∧ y ≤ 0 then [[]] else []
  | x, y, prev, n + 1 =>
      if (n + 1 : ℤ) < x + max y 0 then []
      else ([0, 1, 2, 3] : List (Fin 4)).flatMap fun d =>
        if prev ≠ some (opp d) ∧ 0 ≤ x + dx d then
          (enum (x + dx d) (y + dy d) (some d) n).map (d :: ·)
        else []

theorem dx_dy_le (d : Fin 4) : |dx d| + |dy d| = 1 := by
  fin_cases d <;> simp [dx, dy]

/-- A valid walk can return: `x + max y 0` is at most the number of steps. -/
theorem reach_of_WOK : ∀ (ds : List (Fin 4)) (x y : ℤ) (prev : Option (Fin 4)),
    WOK x y prev ds → x + max y 0 ≤ ds.length := by
  intro ds
  induction ds with
  | nil => intro x y _ h; simp only [WOK] at h; simp [h.1, h.2]
  | cons d ds ih =>
      intro x y prev h
      simp only [WOK] at h
      have := ih _ _ _ h.2.2
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      fin_cases d <;> simp only [dx, dy] at this h ⊢ <;> omega

/-- **Completeness of the enumerator.** -/
theorem mem_enum : ∀ (ds : List (Fin 4)) (x y : ℤ) (prev : Option (Fin 4)),
    WOK x y prev ds → ds ∈ enum x y prev ds.length := by
  intro ds
  induction ds with
  | nil => intro x y _ h; simp only [WOK] at h; simp [enum, h.1, h.2]
  | cons d ds ih =>
      intro x y prev h
      have hr := reach_of_WOK _ _ _ _ h
      simp only [WOK] at h
      simp only [List.length_cons, enum]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hr
      rw [if_neg (by omega)]
      rw [List.mem_flatMap]
      refine ⟨d, by fin_cases d <;> simp, ?_⟩
      rw [if_pos ⟨h.1, h.2.1⟩]
      exact List.mem_map.mpr ⟨ds, ih _ _ _ h.2.2, rfl⟩

/-- The enumerator branches at most three ways after a step or on the axis. -/
theorem length_enum_le : ∀ (n : ℕ) (x y : ℤ) (prev : Option (Fin 4)),
    (prev.isSome ∨ x = 0) → (enum x y prev n).length ≤ 3 ^ n := by
  intro n
  induction n with
  | zero => intro x y _ _; simp only [enum]; split_ifs <;> simp
  | succ n ih =>
      intro x y prev hp
      simp only [enum]
      split_ifs
      · simp
      · rw [List.length_flatMap]
        -- each branch has at most `3^n` walks, and one of the four branches is closed
        have hb : ∀ d : Fin 4, (if prev ≠ some (opp d) ∧ 0 ≤ x + dx d then
            (enum (x + dx d) (y + dy d) (some d) n).map (d :: ·) else []).length ≤ 3 ^ n := by
          intro d; split_ifs
          · rw [List.length_map]; exact ih _ _ _ (Or.inl rfl)
          · simp
        have hclosed : ∃ d₀ : Fin 4, (if prev ≠ some (opp d₀) ∧ 0 ≤ x + dx d₀ then
            (enum (x + dx d₀) (y + dy d₀) (some d₀) n).map (d₀ :: ·) else []).length = 0 := by
          rcases hp with hp | hp
          · obtain ⟨p, rfl⟩ := Option.isSome_iff_exists.mp hp
            refine ⟨opp p, ?_⟩
            rw [if_neg]; · simp
            intro h; apply h.1; fin_cases p <;> rfl
          · refine ⟨3, ?_⟩
            rw [if_neg]; · simp
            intro h; have := h.2; simp [dx, hp] at this
        obtain ⟨d₀, hd₀⟩ := hclosed
        set e : Fin 4 → ℕ := fun d => (if prev ≠ some (opp d) ∧ 0 ≤ x + dx d then
          (enum (x + dx d) (y + dy d) (some d) n).map (d :: ·) else []).length with he
        have hlist : (([0, 1, 2, 3] : List (Fin 4)).map e).sum = ∑ d : Fin 4, e d := by
          rw [Fin.sum_univ_four]; simp only [List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil]; ring
        have hfin : ∑ d : Fin 4, e d ≤ 3 * 3 ^ n := by
          rw [← sum_erase_add _ _ (mem_univ d₀)]
          have : ∑ d ∈ univ.erase d₀, e d ≤ (univ.erase d₀).card * 3 ^ n :=
            sum_le_card_nsmul _ _ _ fun d _ => hb d
          rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at this
          have h0 : e d₀ = 0 := hd₀
          omega
        rw [pow_succ, mul_comm]
        exact (le_of_eq hlist).trans hfin

/-! ### From crossing paths to shapes -/

variable {c m : ℕ}

/-- The direction of the step `a → b`. -/
def dirOf (a b : Cell c m) : Fin 4 :=
  if b.2.val + 1 = a.2.val then 0 else if b.2.val = a.2.val + 1 then 1
  else if b.1.val = a.1.val + 1 then 2 else 3

/-- The step directions of a list of cells. -/
def dirsOf : List (Cell c m) → List (Fin 4)
  | a :: b :: rest => dirOf a b :: dirsOf (b :: rest)
  | _ => []

theorem length_dirsOf : ∀ l : List (Cell c m), (dirsOf l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      simp only [dirsOf, List.length_cons, length_dirsOf (b :: rest)]
      omega

theorem move {a b : Cell c m} (h : slabAdj a b) :
    (b.1.val : ℤ) = a.1.val + dx (dirOf a b) ∧ (b.2.val : ℤ) = a.2.val + dy (dirOf a b) := by
  unfold slabAdj at h
  unfold dirOf
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : b.1.val = a.1.val := by rw [h1]
    rcases h2 with h2 | h2
    · rw [if_neg (by omega), if_pos h2.symm]; simp only [dx, dy]; omega
    · rw [if_pos h2]; simp only [dx, dy]; omega
  · have e2 : b.2.val = a.2.val := by rw [h1]
    rcases h2 with h2 | h2
    · rw [if_neg (by omega), if_neg (by omega), if_pos h2.symm]; simp only [dx, dy]; omega
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp only [dx, dy]; omega

theorem eq_of_dirOf {a b b' : Cell c m} (h : slabAdj a b) (h' : slabAdj a b')
    (hd : dirOf a b = dirOf a b') : b = b' := by
  have m1 := move h
  have m2 := move h'
  rw [hd] at m1
  exact cell_eq (by omega) (by omega)

theorem dirOf_symm {a b : Cell c m} (h : slabAdj a b) : dirOf b a = opp (dirOf a b) := by
  have m1 := move h
  have m2 := move (slabAdj_symm h)
  generalize hd : dirOf a b = d at m1
  generalize hd' : dirOf b a = d' at m2
  fin_cases d <;> fin_cases d' <;> simp only [dx, dy] at m1 m2 <;> first | rfl | omega

theorem opp_injective : Function.Injective opp := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [opp]

/-- **Paths give valid shape walks.** -/
theorem wok_dirsOf (w : ℕ) :
    ∀ l : List (Cell c m), l.IsChain slabAdj → l.Nodup → (∀ z ∈ l, 2 ≤ z.1.val) →
      ∀ a ∈ l.head?, (∀ z ∈ l.getLast?, z.1.val = 2 ∧ z.2.val ≤ w) →
        ∀ p : Option (Cell c m), (∀ b ∈ p, slabAdj b a ∧ b ∉ l) →
          WOK ((a.1.val : ℤ) - 2) ((a.2.val : ℤ) - w) (p.map (dirOf · a)) (dirsOf l) := by
  intro l
  induction l with
  | nil => intro _ _ _ a ha; simp at ha
  | cons a' rest ih =>
      intro hch hnd hfut a ha hl p hp
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      subst ha
      cases rest with
      | nil =>
          simp only [dirsOf, WOK]
          have := hl a' (by simp)
          omega
      | cons b rest' =>
          rw [List.isChain_cons_cons] at hch
          rw [List.nodup_cons] at hnd
          simp only [dirsOf, WOK]
          have hm := move hch.1
          refine ⟨?_, ?_, ?_⟩
          · intro e
            obtain ⟨c', rfl⟩ : ∃ c', p = some c' := by
              cases p with
              | none => simp at e
              | some c' => exact ⟨c', rfl⟩
            simp only [Option.map_some, Option.some.injEq] at e
            have hc' := hp c' rfl
            rw [dirOf_symm (slabAdj_symm hc'.1)] at e
            have := eq_of_dirOf (slabAdj_symm hc'.1) hch.1 (opp_injective e)
            exact hc'.2 (by rw [this]; simp)
          · have := hfut b (by simp); omega
          · have e1 : (a'.1.val : ℤ) - 2 + dx (dirOf a' b) = (b.1.val : ℤ) - 2 := by omega
            have e2 : (a'.2.val : ℤ) - w + dy (dirOf a' b) = (b.2.val : ℤ) - w := by omega
            rw [e1, e2]
            have := ih hch.2 hnd.2 (fun z hz => hfut z (by simp [hz])) b (by simp)
              (fun z hz => hl z (by simpa [List.getLast?_cons_cons] using hz)) (some a')
              (fun b' hb' => by
                simp only [Option.mem_def, Option.some.injEq] at hb'
                subst hb'; exact ⟨hch.1, hnd.1⟩)
            simpa using this

/-- **The encoding is injective.** -/
theorem eq_of_dirsOf : ∀ l l' : List (Cell c m), l.IsChain slabAdj → l'.IsChain slabAdj →
    l.head? = l'.head? → dirsOf l = dirsOf l' → l = l' := by
  intro l
  induction l with
  | nil => intro l' _ _ h _; cases l' <;> simp_all
  | cons a rest ih =>
      intro l' hch hch' hh hd
      cases l' with
      | nil => simp at hh
      | cons a' rest' =>
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          cases rest with
          | nil =>
              cases rest' with
              | nil => rfl
              | cons b' r' => simp [dirsOf] at hd
          | cons b r =>
              cases rest' with
              | nil => simp [dirsOf] at hd
              | cons b' r' =>
                  rw [List.isChain_cons_cons] at hch hch'
                  simp only [dirsOf, List.cons.injEq] at hd
                  have hb := eq_of_dirOf hch.1 hch'.1 hd.1
                  subst hb
                  rw [ih (b :: r') hch.2 hch'.2 rfl hd.2]

/-! ### Counting -/

/-- The enumerated shapes with `L` cells and start offset at least `1`. -/
def shapeCount (L : ℕ) : ℕ :=
  ((List.range (L - 1)).map fun d : ℕ => (enum 0 ((d : ℤ) + 1) none (L - 1)).length).sum

theorem sum_range_eq_list (n : ℕ) (f : ℕ → ℕ) :
    ∑ d ∈ range n, f d = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem shapeCount_eq (L : ℕ) :
    shapeCount L = ∑ d ∈ range (L - 1), (enum 0 ((d : ℤ) + 1) none (L - 1)).length := by
  rw [sum_range_eq_list]; rfl

theorem shapeCount_le (L : ℕ) : shapeCount L ≤ (L - 1) * 3 ^ (L - 1) := by
  rw [shapeCount_eq]
  calc ∑ d ∈ range (L - 1), (enum 0 ((d : ℤ) + 1) none (L - 1)).length
      ≤ ∑ _d ∈ range (L - 1), 3 ^ (L - 1) :=
        sum_le_sum fun d _ => length_enum_le _ _ _ _ (Or.inr rfl)
    _ = (L - 1) * 3 ^ (L - 1) := by simp

theorem shapeCount_small :
    shapeCount 0 = 0 ∧ shapeCount 1 = 0 ∧ shapeCount 2 = 1 ∧ shapeCount 3 = 2 ∧
      shapeCount 4 = 4 ∧ shapeCount 5 = 10 ∧ shapeCount 6 = 31 ∧ shapeCount 7 = 76 := by
  unfold shapeCount; decide +kernel

/-- **Crossing paths with `L` cells are at most the shapes.** -/
theorem card_crossPaths_len_le (hc : 1 ≤ c) (w L : ℕ) :
    ((crossPaths (m := m) hc w).filter (fun l => l.length = L)).card ≤ shapeCount L := by
  set S : Finset (ℕ × List (Fin 4)) := (range (L - 1)).biUnion fun d : ℕ =>
    (enum 0 ((d : ℤ) + 1) none (L - 1)).toFinset.image fun ds => (d, ds)
  have hS : S.card ≤ shapeCount L := by
    calc S.card ≤ ∑ d ∈ range (L - 1),
          ((enum 0 (d + 1) none (L - 1)).toFinset.image fun ds => (d, ds)).card := card_biUnion_le
      _ ≤ ∑ d ∈ range (L - 1), (enum 0 ((d : ℤ) + 1) none (L - 1)).length := by
          refine sum_le_sum fun d _ => le_trans card_image_le (List.toFinset_card_le _)
      _ = shapeCount L := (shapeCount_eq L).symm
  refine le_trans (card_le_card_of_injOn (fun l => ((l.head?.map fun z => z.2.val).getD 0 - w - 1,
    dirsOf l)) ?_ ?_) hS
  · intro l hl
    rw [mem_coe, mem_filter] at hl
    obtain ⟨hl, hlen⟩ := hl
    have hcp : CrossPath hc w l := (mem_filter.mp hl).2
    obtain ⟨hnd, hch, hfut, ⟨v₁, hw₁, h1⟩, ⟨v₂, hw₂, h2⟩⟩ := hcp
    have hwok := wok_dirsOf w l hch hnd hfut (fut0 hc, v₁) (by rw [h1]; rfl)
      (fun z hz => by rw [h2] at hz; simp at hz; subst hz; exact ⟨rfl, hw₂⟩) none (by simp)
    simp only [fut0, Option.map_none] at hwok
    have e : ((v₁.val : ℤ) - w) = ((v₁.val - w - 1 + 1 : ℕ) : ℤ) := by push_cast; omega
    rw [show ((2 : ℕ) : ℤ) - 2 = 0 by norm_num, e] at hwok
    have hr := reach_of_WOK _ _ _ _ hwok
    rw [length_dirsOf, hlen] at hr
    have hmem := mem_enum _ _ _ _ hwok
    rw [length_dirsOf, hlen] at hmem
    rw [mem_coe, mem_biUnion]
    refine ⟨v₁.val - w - 1, mem_range.mpr ?_, ?_⟩
    · simp only [max_def] at hr; split_ifs at hr <;> omega
    · dsimp only
      rw [h1]
      simp only [Option.map_some, Option.getD_some]
      exact mem_image.mpr ⟨_, List.mem_toFinset.mpr hmem, rfl⟩
  · intro l hl l' hl' he
    rw [mem_coe, mem_filter] at hl hl'
    have hcp := (mem_filter.mp hl.1).2
    have hcp' := (mem_filter.mp hl'.1).2
    obtain ⟨_, hch, _, ⟨v₁, hw₁, h1⟩, _⟩ := hcp
    obtain ⟨_, hch', _, ⟨v₁', hw₁', h1'⟩, _⟩ := hcp'
    simp only [Prod.mk.injEq, h1, h1', Option.map_some, Option.getD_some] at he
    have hv : v₁ = v₁' := Fin.ext (by omega)
    subst hv
    exact eq_of_dirsOf l l' hch hch' (by rw [h1, h1']) he.2

/-- **The weighted path sum.** -/
theorem sum_crossPaths_le (hc : 1 ≤ c) (w : ℕ) (g : ℕ → ℚ) (hg : ∀ L, 0 ≤ g L) :
    ∑ l ∈ crossPaths (m := m) hc w, g l.length ≤
      ∑ L ∈ range (Fintype.card (Cell c m) + 1), (shapeCount L : ℚ) * g L := by
  rw [← sum_fiberwise_of_maps_to (g := List.length) (t := range (Fintype.card (Cell c m) + 1))]
  · refine sum_le_sum fun L _ => ?_
    rw [sum_congr rfl fun l hl => by rw [(mem_filter.mp hl).2], sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_crossPaths_len_le hc w L) (hg L)
  · intro l hl
    have hnd := ((mem_filter.mp hl).2).1
    exact mem_range.mpr (Nat.lt_succ_of_le hnd.length_le_card)

/-! ### The series -/

theorem geom_sum_le {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x < 1) (a : ℕ) :
    ∀ N, a ≤ N → ∑ n ∈ Ico a N, (n : ℚ) * x ^ n ≤ x ^ a * (a - (a - 1) * x) / (1 - x) ^ 2 := by
  have key : ∀ N, a ≤ N → (∑ n ∈ Ico a N, (n : ℚ) * x ^ n) * (1 - x) ^ 2 =
      x ^ a * (a - (a - 1) * x) - x ^ N * (N - (N - 1) * x) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
        rw [sum_Ico_succ_top hN, add_mul, ih]
        push_cast; ring
  intro N hN
  have hpos : 0 < (1 - x) ^ 2 := by have : 0 < 1 - x := by linarith
                                    positivity
  rw [le_div_iff₀ hpos, key N hN]
  have : 0 ≤ x ^ N * (N - (N - 1) * x) := by
    apply mul_nonneg (pow_nonneg hx0 _)
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp; linarith
    · have h1 : (1 : ℚ) ≤ N := by exact_mod_cast h
      nlinarith
  linarith

end GridGen.Gauge
