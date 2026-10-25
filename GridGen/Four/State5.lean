/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.Block5

/-!
# Height four, `k = 5`: the bound for one state

For a previous column `s` and next lists `B₁, …, B₄` of five colours, the successors are the
proper colourings from `Aᵢ = Bᵢ.erase sᵢ` (`|Aᵢ| ≥ 4`).

* **The uniform side** (`GU_urow5`): `GU 5 w s` is an explicit affine function of `w` by pattern,
  with `nu5 = 142, 139, 135, 136` uniform successors (`ℓ = 3`).
* **The pattern lemma** (`pattern5k`): the average pattern weight of the actual successors is at
  least `cpat5` times the uniform one. With lists of at least four colours, a free end row has at
  least three values, so the shares of `s₁ = s₃`, `s₂ = s₄`, `s₁ = s₄` are at most `1/3` and that of
  `0101` at most `1/9` (`pat_counts5`); the resulting linear programme is checked at the eight
  corners of the box with the rounded optimum (`ai_research_notes/H4_K5_REVIEW_2026-10-24.md` §3).
* **The count** (`card_ge_N4g`): the four-row count is at least its value at the greedy profile
  of the interval relaxation (triple intersections at their lower bounds, the fourfold at the
  smaller of them), a function `N4g` of the sizes `nᵢ = |Aᵢ|` and `eⱼ = |Aⱼ ∩ Aⱼ₊₁|`.
* **Row codes** (`rowCode5`): `nᵢ = 4 + [sᵢ ∉ Bᵢ]` and `eⱼ = 3 - μⱼ + …` from the membership of the
  state colours in the next lists (`card_inter_code5`).
* `state_bound5k`: `cpat5 · N4g(codes) · GU ≤ nu5 · GB`.
-/

namespace GridGen.Four

open Finset GridGen.Lookback

/-! ### The uniform side -/

/-- The uniform class coefficients at `k = 5` (`ℓ = 3`), by pattern. -/
def urow5 (e13 e24 e14 : Bool) : ℤ × ℤ × ℤ × ℤ :=
  if e13 && e24 then (13, 60, 21, 48)
  else if e13 || e24 then (10, 56, 23, 50)
  else if e14 then (7, 46, 32, 50)
  else (8, 50, 25, 53)

/-- The number of uniform successors, by pattern. -/
def nu5 (e13 e24 e14 : Bool) : ℤ :=
  if e13 && e24 then 142 else if e13 || e24 then 139 else if e14 then 135 else 136

/-- The pattern constants (rounded down at `10⁻⁷`). -/
def cpat5 (e13 e24 e14 : Bool) : ℚ :=
  if e13 && e24 then 9622143 / 10000000 else if e13 || e24 then 9634067 / 10000000
  else if e14 then 9639939 / 10000000 else 9650610 / 10000000

/-- The pattern bits of a column. -/
abbrev pbits (s : T4) : Bool × Bool × Bool :=
  (decide (r1 s = r3 s), decide (r2 s = r4 s), decide (r1 s = r4 s))

/-- **The uniform side at `k = 5`, by pattern.** -/
theorem GU_urow5 (w : Wt) {s : T4} (hs : Proper s) :
    GU 5 w s = ((urow5 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).1 : ℝ)
      + ((urow5 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2.1 : ℝ)
          * w.a
      + ((urow5 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2.2.1 : ℝ)
          * w.b
      + ((urow5 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))).2.2.2 : ℝ)
          * w.c := by
  have hs' := hs
  obtain ⟨p12, p23, p34⟩ := hs'
  rcases canon_cases hs with h | h | h | h | h
  · rw [GU_eq_of_canon w h (by decide), GU_0101 (by norm_num) w]
    have b : r3 s = r1 s ∧ r4 s = r2 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    simp [urow5, b.1.symm, b.2.symm, vA, aff]; norm_num
  · rw [GU_eq_of_canon w h (by decide), GU_0102 (by norm_num) w]
    have b : r3 s = r1 s ∧ r4 s ≠ r2 s ∧ r4 s ≠ r1 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    have b2 : r2 s ≠ r4 s := fun e => b.2.1 e.symm
    have b3 : r1 s ≠ r4 s := fun e => b.2.2 e.symm
    simp [urow5, b.1.symm, b2, vB, aff]; norm_num
  · rw [GU_eq_of_canon w h (by decide), GU_0121 (by norm_num) w]
    have b : r3 s ≠ r1 s ∧ r4 s = r2 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    have b1 : r1 s ≠ r3 s := fun e => b.1 e.symm
    have b3 : r1 s ≠ r4 s := fun e => p12 (e.trans b.2)
    simp [urow5, b1, b.2.symm, vB, aff]; norm_num
  · rw [GU_eq_of_canon w h (by decide), GU_0120 (by norm_num) w]
    have b : r3 s ≠ r1 s ∧ r4 s ≠ r2 s ∧ r4 s = r1 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    have b1 : r1 s ≠ r3 s := fun e => b.1 e.symm
    have b2 : r2 s ≠ r4 s := fun e => b.2.1 e.symm
    simp [urow5, b1, b2, b.2.2.symm, Ne.symm p34, vC, aff]; norm_num
  · rw [GU_eq_of_canon w h (by decide), GU_0123 (by norm_num) w]
    have b : r3 s ≠ r1 s ∧ r4 s ≠ r2 s ∧ r4 s ≠ r1 s := by
      unfold canon at h; simp only [Prod.mk.injEq] at h; split_ifs at h <;> simp_all
    have b1 : r1 s ≠ r3 s := fun e => b.1 e.symm
    have b2 : r2 s ≠ r4 s := fun e => b.2.1 e.symm
    have b3 : r1 s ≠ r4 s := fun e => b.2.2 e.symm
    simp [urow5, b1, b2, b3, vD, aff]; norm_num

theorem nu5_eq (e13 e24 e14 : Bool) :
    nu5 e13 e24 e14 = (urow5 e13 e24 e14).1 + (urow5 e13 e24 e14).2.1 + (urow5 e13 e24 e14).2.2.1
      + (urow5 e13 e24 e14).2.2.2 := by
  cases e13 <;> cases e24 <;> cases e14 <;> rfl

/-! ### The pattern lemma -/

/-- The counts of a column system with lists of at least four colours. -/
theorem pat_counts5 {A₁ A₂ A₃ A₄ : Finset ℕ} (h₁ : 4 ≤ A₁.card) (h₂ : 4 ≤ A₂.card)
    (h₃ : 4 ≤ A₃.card) (h₄ : 4 ≤ A₄.card) :
    let Ω := sts A₁ A₂ A₃ A₄
    3 * ((Ω.filter (fun t => r1 t = r3 t)).card : ℝ) ≤ Ω.card ∧
    3 * ((Ω.filter (fun t => r2 t = r4 t)).card : ℝ) ≤ Ω.card ∧
    3 * ((Ω.filter (fun t => r1 t = r4 t)).card : ℝ) ≤ Ω.card ∧
    9 * ((Ω.filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℝ) ≤ Ω.card ∧
    ((Ω.filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℝ)
      ≤ (Ω.filter (fun t => r1 t = r3 t)).card ∧
    ((Ω.filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card : ℝ)
      ≤ (Ω.filter (fun t => r2 t = r4 t)).card ∧
    ((Ω.filter (fun t => r1 t = r3 t)).card : ℝ) + (Ω.filter (fun t => r2 t = r4 t)).card
      - (Ω.filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card
      + (Ω.filter (fun t => r1 t = r4 t)).card ≤ Ω.card := by
  intro Ω
  have hR : ∀ t ∈ Ω, ∀ t' ∈ Ω, (fun _ : T4 => (1 : ℝ)) t ≤ 1 * (fun _ : T4 => (1 : ℝ)) t' :=
    fun _ _ _ _ => by norm_num
  have one : ∀ (P : T4 → Prop) [DecidablePred P], ∑ t ∈ Ω.filter P, (fun _ : T4 => (1 : ℝ)) t
      = ((Ω.filter P).card : ℝ) := fun P _ => by simp
  have m3 : ((mrow 0 : ℕ) : ℝ) = 3 := by norm_num [mrow]
  have m3' : ((mrow 3 : ℕ) : ℝ) = 3 := by norm_num [mrow]
  have f13 := fib_event (X₁ := A₁) (X₂ := A₂) (X₃ := A₃) (X₄ := A₄) (fun _ => (1 : ℝ))
    (fun _ => zero_le_one) one_pos hR h₁ h₂ h₃ h₄ 0 (fun _ => true) (fun _ _ => rfl) (rowfun 2)
    (fun t x => rowfun_setRow_ne (by decide) t x)
  have f24 := fib_event (X₁ := A₁) (X₂ := A₂) (X₃ := A₃) (X₄ := A₄) (fun _ => (1 : ℝ))
    (fun _ => zero_le_one) one_pos hR h₁ h₂ h₃ h₄ 3 (fun _ => true) (fun _ _ => rfl) (rowfun 1)
    (fun t x => rowfun_setRow_ne (by decide) t x)
  have f14 := fib_event (X₁ := A₁) (X₂ := A₂) (X₃ := A₃) (X₄ := A₄) (fun _ => (1 : ℝ))
    (fun _ => zero_le_one) one_pos hR h₁ h₂ h₃ h₄ 0 (fun _ => true) (fun _ _ => rfl) (rowfun 3)
    (fun t x => rowfun_setRow_ne (by decide) t x)
  have fm := fib_event (X₁ := A₁) (X₂ := A₂) (X₃ := A₃) (X₄ := A₄) (fun _ => (1 : ℝ))
    (fun _ => zero_le_one) one_pos hR h₁ h₂ h₃ h₄ 0 (fun t => decide (r2 t = r4 t))
    (fun _ _ => rfl) (rowfun 2) (fun t x => rowfun_setRow_ne (by decide) t x)
  rw [m3, one, one] at f13 f14 fm
  rw [m3', one, one] at f24
  have e13 : Ω.filter (fun t => rowfun 0 t = rowfun 2 t ∧ (fun _ => true) t = true)
      = Ω.filter (fun t => r1 t = r3 t) := Finset.filter_congr (fun t _ => by simp [rowfun])
  have e24 : Ω.filter (fun t => rowfun 3 t = rowfun 1 t ∧ (fun _ => true) t = true)
      = Ω.filter (fun t => r2 t = r4 t) :=
    Finset.filter_congr (fun t _ => by simp [rowfun]; exact eq_comm)
  have e14 : Ω.filter (fun t => rowfun 0 t = rowfun 3 t ∧ (fun _ => true) t = true)
      = Ω.filter (fun t => r1 t = r4 t) := Finset.filter_congr (fun t _ => by simp [rowfun])
  have em : Ω.filter (fun t => rowfun 0 t = rowfun 2 t ∧ (fun t => decide (r2 t = r4 t)) t = true)
      = Ω.filter (fun t => r1 t = r3 t ∧ r2 t = r4 t) :=
    Finset.filter_congr (fun t _ => by simp [rowfun])
  have eΩ : Ω.filter (fun t => (fun _ => true) t = true) = Ω :=
    Finset.filter_true_of_mem (fun _ _ => rfl)
  have em' : Ω.filter (fun t => (fun t => decide (r2 t = r4 t)) t = true)
      = Ω.filter (fun t => r2 t = r4 t) := Finset.filter_congr (fun t _ => by simp)
  rw [e13, eΩ] at f13
  rw [e24, eΩ] at f24
  rw [e14, eΩ] at f14
  rw [em, em'] at fm
  norm_num at f13 f24 f14 fm
  refine ⟨f13, f24, f14, by linarith, ?_, ?_, ?_⟩
  · exact_mod_cast Finset.card_le_card (fun t ht => by
      simp only [Finset.mem_filter] at ht ⊢; exact ⟨ht.1, ht.2.1⟩)
  · exact_mod_cast Finset.card_le_card (fun t ht => by
      simp only [Finset.mem_filter] at ht ⊢; exact ⟨ht.1, ht.2.2⟩)
  · have hu : (Ω.filter (fun t => r1 t = r3 t)).card + (Ω.filter (fun t => r2 t = r4 t)).card
        = (Ω.filter (fun t => r1 t = r3 t ∨ r2 t = r4 t)).card
          + (Ω.filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card := by
      rw [← Finset.card_union_add_card_inter, ← Finset.filter_or, ← Finset.filter_and]
    have hd : Disjoint (Ω.filter (fun t => r1 t = r3 t ∨ r2 t = r4 t))
        (Ω.filter (fun t => r1 t = r4 t)) := by
      rw [Finset.disjoint_filter]
      intro t ht h1 h2
      obtain ⟨-, -, -, -, p12, p23, p34⟩ := mem_sts.mp ht
      rcases h1 with h1 | h1
      · exact p34 (h1.symm.trans h2)
      · exact p12 (h2.trans h1.symm)
    have hsub : Ω.filter (fun t => r1 t = r3 t ∨ r2 t = r4 t) ∪ Ω.filter (fun t => r1 t = r4 t)
        ⊆ Ω := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd] at hc
    have : ((Ω.filter (fun t => r1 t = r3 t)).card : ℝ) + (Ω.filter (fun t => r2 t = r4 t)).card
        = ((Ω.filter (fun t => r1 t = r3 t ∨ r2 t = r4 t)).card : ℝ)
          + (Ω.filter (fun t => r1 t = r3 t ∧ r2 t = r4 t)).card := by exact_mod_cast hu
    have hc' : ((Ω.filter (fun t => r1 t = r3 t ∨ r2 t = r4 t)).card : ℝ)
        + (Ω.filter (fun t => r1 t = r4 t)).card ≤ Ω.card := by exact_mod_cast hc
    linarith

/-- The corner reduction of the pattern lemma, for one uniform row `aff c₀ c₁ c₂ c₃`. -/
theorem pat_corner5 {c0 c1 c2 c3 cp N n13 n24 m n14 : ℝ} {w : Wt} (hw : BoxR (118 / 125) w)
    (hN : 0 ≤ N) (h13 : 3 * n13 ≤ N) (h24 : 3 * n24 ≤ N) (h14 : 3 * n14 ≤ N) (hm9 : 9 * m ≤ N)
    (hm0 : 0 ≤ m) (hm13 : m ≤ n13) (hm24 : m ≤ n24) (h140 : 0 ≤ n14)
    (hcov : n13 + n24 - m + n14 ≤ N)
    (hc : ∀ x y z : ℝ, (x = 118 / 125 ∨ x = 1) → (y = 118 / 125 ∨ y = 1) →
      (z = 118 / 125 ∨ z = 1) → ∀ N n13 n24 m n14 : ℝ, 0 ≤ N → 3 * n13 ≤ N → 3 * n24 ≤ N →
        3 * n14 ≤ N → 9 * m ≤ N → 0 ≤ m → m ≤ n13 → m ≤ n24 → 0 ≤ n14 →
        n13 + n24 - m + n14 ≤ N →
        cp * aff c0 c1 c2 c3 ⟨x, y, z⟩ * N
          ≤ (z * N + (x - z) * (n13 + n24) + (1 - 2 * x + z) * m + (y - z) * n14)
            * (c0 + c1 + c2 + c3)) :
    cp * aff c0 c1 c2 c3 w * N
      ≤ (w.c * N + (w.a - w.c) * (n13 + n24) + (1 - 2 * w.a + w.c) * m + (w.b - w.c) * n14)
        * (c0 + c1 + c2 + c3) := by
  obtain ⟨ha, ha', hb, hb', hcc, hcc'⟩ := hw
  rw [← sub_nonneg]
  have e : (w.c * N + (w.a - w.c) * (n13 + n24) + (1 - 2 * w.a + w.c) * m + (w.b - w.c) * n14)
        * (c0 + c1 + c2 + c3) - cp * aff c0 c1 c2 c3 w * N
      = aff (-cp * c0 * N + m * (c0 + c1 + c2 + c3))
          ((n13 + n24 - 2 * m) * (c0 + c1 + c2 + c3) - cp * c1 * N)
          (n14 * (c0 + c1 + c2 + c3) - cp * c2 * N)
          ((N - n13 - n24 + m - n14) * (c0 + c1 + c2 + c3) - cp * c3 * N) w := by
    unfold aff; ring
  rw [e]
  refine aff_nonneg ha ha' hb hb' hcc hcc' (fun x y z hx hy hz => ?_)
  have := hc x y z hx hy hz N n13 n24 m n14 hN h13 h24 h14 hm9 hm0 hm13 hm24 h140 hcov
  have e' : (z * N + (x - z) * (n13 + n24) + (1 - 2 * x + z) * m + (y - z) * n14)
        * (c0 + c1 + c2 + c3) - cp * aff c0 c1 c2 c3 ⟨x, y, z⟩ * N
      = aff (-cp * c0 * N + m * (c0 + c1 + c2 + c3))
          ((n13 + n24 - 2 * m) * (c0 + c1 + c2 + c3) - cp * c1 * N)
          (n14 * (c0 + c1 + c2 + c3) - cp * c2 * N)
          ((N - n13 - n24 + m - n14) * (c0 + c1 + c2 + c3) - cp * c3 * N)
          ⟨x, y, z⟩ := by
    unfold aff; ring
  linarith

/-- The corner inequalities for the four uniform rows at `ℓ = 3`. -/
theorem pat_rows5 (c0 c1 c2 c3 cp : ℝ)
    (h : (c0, c1, c2, c3, cp) = (13, 60, 21, 48, 9622143 / 10000000) ∨
      (c0, c1, c2, c3, cp) = (10, 56, 23, 50, 9634067 / 10000000) ∨
      (c0, c1, c2, c3, cp) = (7, 46, 32, 50, 9639939 / 10000000) ∨
      (c0, c1, c2, c3, cp) = (8, 50, 25, 53, 9650610 / 10000000)) :
    ∀ x y z : ℝ, (x = 118 / 125 ∨ x = 1) → (y = 118 / 125 ∨ y = 1) →
      (z = 118 / 125 ∨ z = 1) → ∀ N n13 n24 m n14 : ℝ, 0 ≤ N → 3 * n13 ≤ N → 3 * n24 ≤ N →
        3 * n14 ≤ N → 9 * m ≤ N → 0 ≤ m → m ≤ n13 → m ≤ n24 → 0 ≤ n14 →
        n13 + n24 - m + n14 ≤ N →
        cp * aff c0 c1 c2 c3 ⟨x, y, z⟩ * N
          ≤ (z * N + (x - z) * (n13 + n24) + (1 - 2 * x + z) * m + (y - z) * n14)
            * (c0 + c1 + c2 + c3) := by
  rcases h with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h <;>
  · rintro x y z (rfl | rfl) (rfl | rfl) (rfl | rfl) N n13 n24 m n14 hN h13 h24 h14 hm9 hm0 hm13
      hm24 h140 hcov <;>
    · simp only [aff]; linarith

theorem urow5_cases (e13 e24 e14 : Bool) : ∃ c0 c1 c2 c3 cp : ℝ,
    ((c0, c1, c2, c3, cp) = (13, 60, 21, 48, 9622143 / 10000000) ∨
      (c0, c1, c2, c3, cp) = (10, 56, 23, 50, 9634067 / 10000000) ∨
      (c0, c1, c2, c3, cp) = (7, 46, 32, 50, 9639939 / 10000000) ∨
      (c0, c1, c2, c3, cp) = (8, 50, 25, 53, 9650610 / 10000000)) ∧
    ((urow5 e13 e24 e14).1 : ℝ) = c0 ∧ ((urow5 e13 e24 e14).2.1 : ℝ) = c1 ∧
    ((urow5 e13 e24 e14).2.2.1 : ℝ) = c2 ∧ ((urow5 e13 e24 e14).2.2.2 : ℝ) = c3 ∧
    ((cpat5 e13 e24 e14 : ℚ) : ℝ) = cp := by
  refine ⟨_, _, _, _, _, ?_, rfl, rfl, rfl, rfl, rfl⟩
  cases e13 <;> cases e24 <;> cases e14 <;> norm_num [urow5, cpat5]

/-- **The pattern lemma at `k = 5`.** -/
theorem pattern5k {w : Wt} (hw : InBox 5 w) {s : T4} (hs : Proper s)
    {A₁ A₂ A₃ A₄ : Finset ℕ} (h₁ : 4 ≤ A₁.card) (h₂ : 4 ≤ A₂.card) (h₃ : 4 ≤ A₃.card)
    (h₄ : 4 ≤ A₄.card) :
    ((cpat5 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℚ) : ℝ)
        * GU 5 w s * (sts A₁ A₂ A₃ A₄).card
      ≤ ((nu5 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℤ) : ℝ)
        * G w A₁ A₂ A₃ A₄ := by
  have hb : BoxR (118 / 125) w := by rw [← rho_five]; exact hw
  obtain ⟨c13, c24, c14, c9, m13, m24, cov⟩ := pat_counts5 h₁ h₂ h₃ h₄
  have hsplit := G_split w A₁ A₂ A₃ A₄
  simp only [Int.cast_natCast] at hsplit
  rw [hsplit, GU_urow5 w hs, nu5_eq]
  obtain ⟨c0, c1, c2, c3, cp, hrow, e0, e1, e2, e3, ecp⟩ :=
    urow5_cases (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s))
  push_cast
  rw [e0, e1, e2, e3, ecp]
  have := pat_corner5 (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (cp := cp) hb
    (Nat.cast_nonneg _) c13 c24 c14 c9 (Nat.cast_nonneg _) m13 m24 (Nat.cast_nonneg _) cov
    (pat_rows5 c0 c1 c2 c3 cp hrow)
  unfold aff at this
  linarith

/-! ### The count -/

/-- The four-row count at the greedy profile. -/
def N4g (n1 n2 n3 n4 e12 e23 e34 : ℤ) : ℤ :=
  n1 * n2 * n3 * n4 - e12 * n3 * n4 - n1 * e23 * n4 - n1 * n2 * e34
    + max 0 (e12 + e23 - n2) * n4 + n1 * max 0 (e23 + e34 - n3) + e12 * e34
    - min (max 0 (e12 + e23 - n2)) (max 0 (e23 + e34 - n3))

theorem greedy4 {n1 n2 n3 n4 e12 e23 e34 t1 t2 q : ℤ} (hn1 : 1 ≤ n1) (hn4 : 1 ≤ n4)
    (ht1 : 0 ≤ t1) (ht1' : e12 + e23 - n2 ≤ t1) (ht2 : 0 ≤ t2) (ht2' : e23 + e34 - n3 ≤ t2)
    (hq1 : q ≤ t1) (hq2 : q ≤ t2) :
    N4g n1 n2 n3 n4 e12 e23 e34
      ≤ n1 * n2 * n3 * n4 - e12 * n3 * n4 - n1 * e23 * n4 - n1 * n2 * e34
        + t1 * n4 + n1 * t2 + e12 * e34 - q := by
  unfold N4g
  set T1 := max 0 (e12 + e23 - n2) with hT1
  set T2 := max 0 (e23 + e34 - n3) with hT2
  have D1 : T1 ≤ t1 := max_le ht1 ht1'
  have D2 : T2 ≤ t2 := max_le ht2 ht2'
  have g : q - min T1 T2 ≤ (t1 - T1) + (t2 - T2) := by
    rcases le_total T1 T2 with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have s1 : 0 ≤ (n4 - 1) * (t1 - T1) := mul_nonneg (by linarith) (by linarith)
  have s2 : 0 ≤ (n1 - 1) * (t2 - T2) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- **The count is at least its greedy value.** -/
theorem card_ge_N4g (A₁ A₂ A₃ A₄ : Finset ℕ) (h₁ : 1 ≤ A₁.card) (h₄ : 1 ≤ A₄.card) :
    N4g A₁.card A₂.card A₃.card A₄.card (A₁ ∩ A₂).card (A₂ ∩ A₃).card (A₃ ∩ A₄).card
      ≤ ((sts A₁ A₂ A₃ A₄).card : ℤ) := by
  rw [card_sts_formula]
  have t1 := triple_ge A₁ A₂ A₃
  have t2 := triple_ge A₂ A₃ A₄
  have t1' : ((A₁ ∩ A₂).card : ℤ) + (A₂ ∩ A₃).card - A₂.card ≤ (A₁ ∩ A₂ ∩ A₃).card := by
    exact_mod_cast t1
  have t2' : ((A₂ ∩ A₃).card : ℤ) + (A₃ ∩ A₄).card - A₃.card ≤ (A₂ ∩ A₃ ∩ A₄).card := by
    exact_mod_cast t2
  have q1 : ((A₁ ∩ A₂ ∩ A₃ ∩ A₄).card : ℤ) ≤ (A₁ ∩ A₂ ∩ A₃).card := by
    exact_mod_cast card_le_card inter_subset_left
  have q2 : ((A₁ ∩ A₂ ∩ A₃ ∩ A₄).card : ℤ) ≤ (A₂ ∩ A₃ ∩ A₄).card := by
    exact_mod_cast card_le_card (fun x hx => by
      simp only [mem_inter] at hx ⊢; exact ⟨⟨hx.1.1.2, hx.1.2⟩, hx.2⟩)
  have e : ((A₁ ∩ A₂ ∩ A₃ ∩ A₄).card : ℤ) = (A₁ ∩ A₂ ∩ A₃ ∩ A₄).card := rfl
  exact greedy4 (by exact_mod_cast h₁) (by exact_mod_cast h₄) (Nat.cast_nonneg _) t1'
    (Nat.cast_nonneg _) t2' q1 q2

/-! ### Row codes -/

/-- The code of a colour in the list `Bi` (previous `Bp`, next `Bn`): `0` if it misses `Bi`,
else `1` (in both neighbours), `2` (only missing `Bp`), `3` (only missing `Bn`), `4` (missing
both). -/
def rowCode5 (Bp Bi Bn : Finset ℕ) (x : ℕ) : ℕ :=
  if x ∈ Bi then (if x ∈ Bp then (if x ∈ Bn then 1 else 3) else (if x ∈ Bn then 2 else 4))
  else 0

def cH5 (c : ℕ) : ℕ := if c = 0 then 1 else 0
def cM5 (c : ℕ) : ℕ := if c = 2 ∨ c = 4 then 1 else 0
def cX5 (c : ℕ) : ℕ := if c = 3 ∨ c = 4 then 1 else 0

section codes
variable (Bp Bi Bn : Finset ℕ) (x : ℕ)

theorem cH5_code : cH5 (rowCode5 Bp Bi Bn x) = if x ∈ Bi then 0 else 1 := by
  unfold cH5 rowCode5; split_ifs <;> simp_all

theorem cM5_code : cM5 (rowCode5 Bp Bi Bn x) = if x ∈ Bi \ Bp then 1 else 0 := by
  unfold cM5 rowCode5; simp only [mem_sdiff]; split_ifs <;> simp_all

theorem cX5_code : cX5 (rowCode5 Bp Bi Bn x) = if x ∈ Bi \ Bn then 1 else 0 := by
  unfold cX5 rowCode5; simp only [mem_sdiff]; split_ifs <;> simp_all

theorem rowCode5_le : rowCode5 Bp Bi Bn x ≤ 4 := by
  unfold rowCode5; split_ifs <;> norm_num

end codes

theorem card_erase_code5 {B : Finset ℕ} (hB : B.card = 5) (Bp Bn : Finset ℕ) (x : ℕ) :
    (B.erase x).card = 4 + cH5 (rowCode5 Bp B Bn x) := by
  rw [cH5_code]
  by_cases h : x ∈ B
  · rw [Finset.card_erase_of_mem h, hB]; simp [h]
  · rw [Finset.erase_eq_of_notMem h, hB]; simp [h]

/-- **The consecutive intersection from the codes.** -/
theorem card_inter_code5 {B C : Finset ℕ} (hB : B.card = 5) (hC : C.card = 5) {m : ℕ}
    (hm : (B ∩ C).card + m = 5) (Bp Cn : Finset ℕ) {x y : ℕ} (hxy : x ≠ y) :
    ((B.erase x) ∩ (C.erase y)).card + m
      = 3 + cH5 (rowCode5 Bp B C x) + cX5 (rowCode5 Bp B C x) + cH5 (rowCode5 B C Cn y)
        + cM5 (rowCode5 B C Cn y) := by
  have h := card_inter_erase hB hC hxy
  have hmu : mu 5 B C = (m : ℝ) := by
    unfold mu
    have : ((B ∩ C).card : ℝ) + m = 5 := by exact_mod_cast hm
    push_cast; linarith
  rw [hmu] at h
  have e1 : hb B x = (cH5 (rowCode5 Bp B C x) : ℝ) := by
    rw [cH5_code]; unfold hb; split_ifs <;> simp
  have e2 : hb C y = (cH5 (rowCode5 B C Cn y) : ℝ) := by
    rw [cH5_code]; unfold hb; split_ifs <;> simp
  have e3 : zz B C x y = (cX5 (rowCode5 Bp B C x) : ℝ) + (cM5 (rowCode5 B C Cn y) : ℝ) := by
    rw [cX5_code, cM5_code, zz_eq]; split_ifs <;> simp
  rw [e1, e2, e3] at h
  push_cast at h
  have : (((B.erase x) ∩ (C.erase y)).card : ℝ) + m
      = ((3 + cH5 (rowCode5 Bp B C x) + cX5 (rowCode5 Bp B C x) + cH5 (rowCode5 B C Cn y)
        + cM5 (rowCode5 B C Cn y) : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

/-- The consecutive intersection of a code pair, as an integer. -/
def nE5 (m cp ci : ℕ) : ℤ := 3 - (m : ℤ) + cH5 cp + cX5 cp + cH5 ci + cM5 ci

/-- The greedy count of a code vector. -/
def Nst5 (m2 m3 m4 c1 c2 c3 c4 : ℕ) : ℤ :=
  N4g (4 + cH5 c1 : ℕ) (4 + cH5 c2 : ℕ) (4 + cH5 c3 : ℕ) (4 + cH5 c4 : ℕ) (nE5 m2 c1 c2)
    (nE5 m3 c2 c3) (nE5 m4 c3 c4)

/-- The codes of a state. -/
def codes5 (B₁ B₂ B₃ B₄ : Finset ℕ) (s : T4) : ℕ × ℕ × ℕ × ℕ :=
  (rowCode5 B₁ B₁ B₂ (r1 s), rowCode5 B₁ B₂ B₃ (r2 s), rowCode5 B₂ B₃ B₄ (r3 s),
    rowCode5 B₃ B₄ B₄ (r4 s))

/-- **The bound for one state**: `cpat5 · N4g(codes) · GU ≤ nu5 · GB`. -/
theorem state_bound5k {w : Wt} (hw : InBox 5 w) {B₁ B₂ B₃ B₄ : Finset ℕ} (hB₁ : B₁.card = 5)
    (hB₂ : B₂.card = 5) (hB₃ : B₃.card = 5) (hB₄ : B₄.card = 5) {m2 m3 m4 : ℕ}
    (c2 : (B₁ ∩ B₂).card + m2 = 5) (c3 : (B₂ ∩ B₃).card + m3 = 5)
    (c4 : (B₃ ∩ B₄).card + m4 = 5) {s : T4} (hs : Proper s) :
    ((cpat5 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℚ) : ℝ)
        * ((Nst5 m2 m3 m4 (codes5 B₁ B₂ B₃ B₄ s).1 (codes5 B₁ B₂ B₃ B₄ s).2.1
          (codes5 B₁ B₂ B₃ B₄ s).2.2.1 (codes5 B₁ B₂ B₃ B₄ s).2.2.2 : ℤ) : ℝ) * GU 5 w s
      ≤ ((nu5 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℤ) : ℝ)
        * GB w B₁ B₂ B₃ B₄ s := by
  obtain ⟨p12, p23, p34⟩ := hs
  have n1 := card_erase_code5 hB₁ B₁ B₂ (r1 s)
  have n2 := card_erase_code5 hB₂ B₁ B₃ (r2 s)
  have n3 := card_erase_code5 hB₃ B₂ B₄ (r3 s)
  have n4 := card_erase_code5 hB₄ B₃ B₄ (r4 s)
  have i2 := card_inter_code5 hB₁ hB₂ c2 B₁ B₃ p12
  have i3 := card_inter_code5 hB₂ hB₃ c3 B₁ B₄ p23
  have i4 := card_inter_code5 hB₃ hB₄ c4 B₂ B₄ p34
  have hcount := card_ge_N4g (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s))
    (B₄.erase (r4 s)) (by omega) (by omega)
  have hN : Nst5 m2 m3 m4 (codes5 B₁ B₂ B₃ B₄ s).1 (codes5 B₁ B₂ B₃ B₄ s).2.1
      (codes5 B₁ B₂ B₃ B₄ s).2.2.1 (codes5 B₁ B₂ B₃ B₄ s).2.2.2
      ≤ ((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))).card : ℤ) := by
    refine le_of_eq_of_le ?_ hcount
    simp only [Nst5, codes5, nE5]
    rw [n1, n2, n3, n4]
    congr 1
    · omega
    · omega
    · omega
  have hp := pattern5k hw ⟨p12, p23, p34⟩ (A₁ := B₁.erase (r1 s)) (A₂ := B₂.erase (r2 s))
    (A₃ := B₃.erase (r3 s)) (A₄ := B₄.erase (r4 s)) (by omega) (by omega) (by omega) (by omega)
  have hcp : (0 : ℝ) ≤ ((cpat5 (decide (r1 s = r3 s)) (decide (r2 s = r4 s))
      (decide (r1 s = r4 s)) : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ cpat5 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) := by
      unfold cpat5; split_ifs <;> norm_num
    exact_mod_cast this
  have hU := GU_nonneg (by norm_num) hw s
  have hNR : ((Nst5 m2 m3 m4 (codes5 B₁ B₂ B₃ B₄ s).1 (codes5 B₁ B₂ B₃ B₄ s).2.1
      (codes5 B₁ B₂ B₃ B₄ s).2.2.1 (codes5 B₁ B₂ B₃ B₄ s).2.2.2 : ℤ) : ℝ)
      ≤ ((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))).card : ℝ) := by
    exact_mod_cast hN
  unfold GB
  calc _ = ((cpat5 (decide (r1 s = r3 s)) (decide (r2 s = r4 s)) (decide (r1 s = r4 s)) : ℚ) : ℝ)
        * GU 5 w s * ((Nst5 m2 m3 m4 (codes5 B₁ B₂ B₃ B₄ s).1 (codes5 B₁ B₂ B₃ B₄ s).2.1
          (codes5 B₁ B₂ B₃ B₄ s).2.2.1 (codes5 B₁ B₂ B₃ B₄ s).2.2.2 : ℤ) : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hNR (mul_nonneg hcp hU)
    _ ≤ _ := hp

end GridGen.Four
