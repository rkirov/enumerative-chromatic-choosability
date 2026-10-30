/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Six.BitDP

/-!
# Height six at `k = 6`: the seam from the state-bit checks

The bridge from the kernel checks of `GridGen/Six/BitFast.lean` and `GridGen/Six/BitDP.lean` to
the seam inequality.

* **The codes of an actual state** (`codes_facts`): for a proper column `s` and `6`-lists
  `B₁, …, B₆` with mismatches `m`, the codes `kcodes B s` are admissible, the successor lists have
  `5 + h` colours and their consecutive intersections are `eR`.
* **One state** (`state_of_leaf`): a passed leaf inequality with a denominator at least
  `NU · R(n, o(s))` gives `GU · (D + K - fired) ≤ D · GB` (from `state66`).
* **The three kinds of classes**: a compact certificate (pins without equalities, the
  denominator `NM = max_o NU_o R(n, o)`, `seam_compact`), a pattern-aware certificate (one check
  per canonical pattern with its own denominator, `seam_pattern`), and a pointwise class (the
  `64` worst states, by `N6g_anti`, `seam_point`).
-/

namespace GridGen.Six

open Finset

/-! ### Tables -/

/-- The uniform successor counts by orbit. -/
def NUL : List ℕ := [6765, 6693, 6608, 6697, 6625, 6629, 6625, 6524, 6613, 6541, 6540, 6561, 6629, 6557, 6436, 6453, 6541, 6537, 6473, 6452, 6469, 6558, 6621, 6622, 6553, 6554, 6494, 6490, 6469, 6470, 6485, 6486]

theorem NUL_eq : ∀ o : Fin 32, NUL.getD o 0 = NUo o := by decide +kernel

/-- The largest `NU · R` by size vector. -/
def NML : List ℕ := [6847882717926525, 6846794893350390, 6846288615295140, 6845201297086020, 6847882717926525, 6846794893350390, 6846288615295140, 6845201297086020, 6847882717926525, 6846794893350390, 6846288615295140, 6845201297086020, 6847882717926525, 6846794893350390, 6846288615295140, 6845201297086020, 6846288615295140, 6845201297086020, 6846288615295140, 6845201297086020, 6846288615295140, 6845201297086020, 6846288615295140, 6845201297086020, 6846288615295140, 6845201297086020, 6846288615295140, 6845201297086020, 6846288615295140, 6845201297086020, 6846288615295140, 6845201297086020, 6846794893350390, 6845780702971485, 6845201297086020, 6844187578721460, 6846794893350390, 6845780702971485, 6845201297086020, 6844187578721460, 6846794893350390, 6845780702971485, 6845201297086020, 6844187578721460, 6846794893350390, 6845780702971485, 6845201297086020, 6844187578721460, 6845201297086020, 6844187578721460, 6845201297086020, 6844187578721460, 6845201297086020, 6844187578721460, 6845201297086020, 6844187578721460, 6845201297086020, 6844187578721460, 6845201297086020, 6844187578721460, 6845201297086020, 6844187578721460, 6845201297086020, 6844187578721460]

theorem NML_ok : ∀ i < 64, ∀ o < 32,
    NUL.getD o 0 * (patCerts.getD i default).R.getD o 0 ≤ NML.getD i 0 := by decide +kernel

/-- The ratio bounds are positive. -/
theorem R_pos : ∀ i < 64, ∀ o < 32, 0 < (patCerts.getD i default).R.getD o 0 := by
  decide +kernel

/-- The denominators of orbit `o` by size vector. -/
def DRL (o : ℕ) : List ℕ :=
  (List.range 64).map fun i => NUL.getD o 0 * (patCerts.getD i default).R.getD o 0

theorem DRL_getD {o i : ℕ} (hi : i < 64) :
    (DRL o).getD i 0 = NUL.getD o 0 * (patCerts.getD i default).R.getD o 0 := by
  unfold DRL
  rw [List.getD_eq_getElem _ _ (by simp [hi])]
  simp

/-! ### The codes of an actual state -/

theorem nidx_lt {a b c d e f : ℕ} (ha : a = 5 ∨ a = 6) (hb : b = 5 ∨ b = 6) (hc : c = 5 ∨ c = 6)
    (hd : d = 5 ∨ d = 6) (he : e = 5 ∨ e = 6) (hf : f = 5 ∨ f = 6) : nidx a b c d e f < 64 := by
  unfold nidx; omega

theorem kH56 (c : ℕ) : 5 + kH c = 5 ∨ 5 + kH c = 6 := by unfold kH; split_ifs <;> simp

theorem kH_le (c : ℕ) : kH c ≤ 1 := by unfold kH; split_ifs <;> simp

theorem sdiff_pos6 {B C : Finset ℕ} (hB : B.card = 6) {m : ℕ} (hm : (C ∩ B).card + m = 6) {x : ℕ}
    (hx : x ∈ B \ C) : 0 < m := by
  have h1 := Finset.card_sdiff_add_card_inter B C
  rw [Finset.inter_comm] at h1
  have h2 : 0 < (B \ C).card := Finset.card_pos.mpr ⟨x, hx⟩
  omega

theorem capR_eq (cp ci : ℕ) : capR cp ci = 4 + kH cp + kX cp + kH ci + kM ci := by
  simp only [capR, kHr_eq, kXr_eq, kMr_eq, Nat.add_eq]

theorem pairR_iff (m cp ci : ℕ) : pairR m cp ci = true ↔
    (kM ci = 0 ∨ 0 < m) ∧ (kX cp = 0 ∨ 0 < m) ∧ m ≤ 4 + kH cp + kX cp + kH ci + kM ci := by
  simp only [pairR, Bool.and_eq_true, Bool.or_eq_true, beq_eq_decide, blt_eq_decide,
    ble_eq_decide, decide_eq_true_eq, kMr_eq, kXr_eq, capR_eq]
  tauto

theorem rcode_lt (Bp Bi Bn : Finset ℕ) (x : ℕ) : rcode Bp Bi Bn x < 5 := by
  have := rcode_le Bp Bi Bn x; omega

/-- **The codes of an actual state.** -/
theorem codes_facts {B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ} (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6)
    (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6)
    {m1 m2 m3 m4 m5 : ℕ} (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ [m1, m2, m3, m4, m5]) {s : T6}
    (hs : Proper s) :
    codes5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) ∧ bvalid6 m1 m2 m3 m4 m5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) ∧
    ((B₁.erase (r1 s)).card = 5 + kH (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) ∧
     (B₂.erase (r2 s)).card = 5 + kH (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) ∧
     (B₃.erase (r3 s)).card = 5 + kH (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) ∧
     (B₄.erase (r4 s)).card = 5 + kH (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) ∧
     (B₅.erase (r5 s)).card = 5 + kH (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) ∧
     (B₆.erase (r6 s)).card = 5 + kH (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) ∧
    (((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card
        = eR m1 (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) ∧
     ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card
        = eR m2 (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) ∧
     ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card
        = eR m3 (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) ∧
     ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card
        = eR m4 (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) ∧
     ((B₅.erase (r5 s)) ∩ (B₆.erase (r6 s))).card
        = eR m5 (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) := by
  obtain ⟨c2, c3, c4, c5, c6⟩ := hm
  simp only [List.getD_cons_zero, List.getD_cons_succ] at c2 c3 c4 c5 c6
  have e1 : r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) = rcode B₁ B₁ B₂ (r1 s) := rfl
  have e2 : r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) = rcode B₁ B₂ B₃ (r2 s) := rfl
  have e3 : r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) = rcode B₂ B₃ B₄ (r3 s) := rfl
  have e4 : r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) = rcode B₃ B₄ B₅ (r4 s) := rfl
  have e5 : r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) = rcode B₄ B₅ B₆ (r5 s) := rfl
  have e6 : r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s) = rcode B₅ B₆ B₆ (r6 s) := rfl
  simp only [codes5, bvalid6, e1, e2, e3, e4, e5, e6]
  obtain ⟨p12, p23, p34, p45, p56⟩ := hs
  have i2 := card_inter_rcode hB₁ hB₂ c2 B₁ B₃ p12
  have i3 := card_inter_rcode hB₂ hB₃ c3 B₁ B₄ p23
  have i4 := card_inter_rcode hB₃ hB₄ c4 B₂ B₅ p34
  have i5 := card_inter_rcode hB₄ hB₅ c5 B₃ B₆ p45
  have i6 := card_inter_rcode hB₅ hB₆ c6 B₄ B₆ p56
  have pm : ∀ {Bp Bi Bn : Finset ℕ} {x m : ℕ}, Bi.card = 6 → (Bp ∩ Bi).card + m = 6 →
      (kM (rcode Bp Bi Bn x) = 0 ∨ 0 < m) := by
    intro Bp Bi Bn x m hBi hm
    rw [kM_code]
    split_ifs with h
    · right; exact sdiff_pos6 hBi hm h
    · left; rfl
  have px : ∀ {Bp Bi Bn : Finset ℕ} {x m : ℕ}, Bi.card = 6 → (Bi ∩ Bn).card + m = 6 →
      (kX (rcode Bp Bi Bn x) = 0 ∨ 0 < m) := by
    intro Bp Bi Bn x m hBi hm
    rw [kX_code]
    split_ifs with h
    · right; rw [Finset.inter_comm] at hm; exact sdiff_pos6 hBi hm h
    · left; rfl
  have z1 : kM (rcode B₁ B₁ B₂ (r1 s)) = 0 := by rw [kM_code]; simp
  have z6 : kX (rcode B₅ B₆ B₆ (r6 s)) = 0 := by rw [kX_code]; simp
  refine ⟨⟨rcode_lt _ _ _ _, rcode_lt _ _ _ _, rcode_lt _ _ _ _, rcode_lt _ _ _ _,
    rcode_lt _ _ _ _, rcode_lt _ _ _ _⟩, ⟨z1, z6, ?_, ?_, ?_, ?_, ?_⟩, ⟨card_erase_rcode hB₁ _ _ _,
    card_erase_rcode hB₂ _ _ _, card_erase_rcode hB₃ _ _ _, card_erase_rcode hB₄ _ _ _,
    card_erase_rcode hB₅ _ _ _, card_erase_rcode hB₆ _ _ _⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pairR_iff]; exact ⟨pm hB₂ c2, px hB₁ c2, by omega⟩
  · rw [pairR_iff]; exact ⟨pm hB₃ c3, px hB₂ c3, by omega⟩
  · rw [pairR_iff]; exact ⟨pm hB₄ c4, px hB₃ c4, by omega⟩
  · rw [pairR_iff]; exact ⟨pm hB₅ c5, px hB₄ c5, by omega⟩
  · rw [pairR_iff]; exact ⟨pm hB₆ c6, px hB₅ c6, by omega⟩
  all_goals simp only [eR, capR_eq, Nat.sub_eq]; omega

/-! ### One state -/

theorem NUo_pos : ∀ o : Fin 32, 0 < NUo o := by
  intro o; rw [← NUL_eq]; revert o; decide +kernel

/-- The arithmetic of one state. -/
theorem state_arith {U Gb : ℝ} {D K F den NU R P M : ℕ} (hU : 0 ≤ U) (hG : 0 ≤ Gb) (hR : 0 < R)
    (hNU : 0 < NU) (hden : NU * R ≤ den)
    (hleaf : (D + K - F) * den + D * 1000000000000 * M ≤ D * 1000000000000 * P)
    (hst : (1000000000000 : ℝ) * ((P : ℝ) - M) * U ≤ (R : ℝ) * NU * Gb) :
    U * ((D : ℝ) + K - F) ≤ D * Gb := by
  rcases le_or_gt (D + K) F with h | h
  · have : (D : ℝ) + K - F ≤ 0 := by
      have : ((D + K : ℕ) : ℝ) ≤ F := by exact_mod_cast h
      push_cast at this; linarith
    have h1 : U * ((D : ℝ) + K - F) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hU this
    have h2 : (0 : ℝ) ≤ D * Gb := mul_nonneg (Nat.cast_nonneg _) hG
    linarith
  · have ha : ((D + K - F : ℕ) : ℝ) = (D : ℝ) + K - F := by
      rw [Nat.cast_sub h.le]; push_cast; ring
    have hleafR : ((D + K - F : ℕ) : ℝ) * den + D * 1000000000000 * M
        ≤ D * 1000000000000 * P := by exact_mod_cast hleaf
    rw [ha] at hleafR
    have hdenR : (NU : ℝ) * R ≤ den := by exact_mod_cast hden
    have ha0 : (0 : ℝ) ≤ (D : ℝ) + K - F := by rw [← ha]; exact Nat.cast_nonneg _
    have k1 : ((D : ℝ) + K - F) * (NU * R) ≤ ((D : ℝ) + K - F) * den :=
      mul_le_mul_of_nonneg_left hdenR ha0
    have k2 : ((D : ℝ) + K - F) * (NU * R) ≤ D * 1000000000000 * ((P : ℝ) - M) := by linarith
    have k3 := mul_le_mul_of_nonneg_right k2 hU
    have k4 := mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    have hpos : (0 : ℝ) < NU * R := by
      have : (0 : ℝ) < NU := by exact_mod_cast hNU
      have : (0 : ℝ) < R := by exact_mod_cast hR
      positivity
    have key : U * ((D : ℝ) + K - F) * (NU * R) ≤ D * Gb * (NU * R) := by nlinarith
    exact le_of_mul_le_mul_right key hpos

/-- **One state from a passed leaf**: with `den ≥ NU · R(n, o(s))`. -/
theorem state_of_leaf {w : Wt6} (hw : InCone6 w) {B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ}
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6) {s : T6} (hs : Proper s) {D K F den : ℕ}
    (hden : NUo (orb s) * Rof (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card
        (B₃.erase (r3 s)).card (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card
        (B₆.erase (r6 s)).card (orb s) ≤ den)
    (hR : 0 < Rof (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card
        (B₃.erase (r3 s)).card (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card
        (B₆.erase (r6 s)).card (orb s))
    (hleaf : (D + K - F) * den + D * 1000000000000 * N6gM (B₁.erase (r1 s)).card
        (B₂.erase (r2 s)).card (B₃.erase (r3 s)).card (B₄.erase (r4 s)).card
        (B₅.erase (r5 s)).card (B₆.erase (r6 s)).card
        ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card
        ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card
        ((B₅.erase (r5 s)) ∩ (B₆.erase (r6 s))).card
      ≤ D * 1000000000000 * N6gP (B₁.erase (r1 s)).card
        (B₂.erase (r2 s)).card (B₃.erase (r3 s)).card (B₄.erase (r4 s)).card
        (B₅.erase (r5 s)).card (B₆.erase (r6 s)).card
        ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card
        ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card
        ((B₅.erase (r5 s)) ∩ (B₆.erase (r6 s))).card) :
    GU 6 w s * ((D : ℝ) + K - F) ≤ D * GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by
  have hst := state66 hw hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hs
  rw [← N6gPM_eq] at hst
  have hU : 0 ≤ GU 6 w s := GU_nonneg hw s
  have hG : 0 ≤ GB w B₁ B₂ B₃ B₄ B₅ B₆ s := GB_nonneg hw _ _ _ _ _ _ s
  generalize N6gP (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card (B₃.erase (r3 s)).card
    (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card (B₆.erase (r6 s)).card
    ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card
    ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card
    ((B₅.erase (r5 s)) ∩ (B₆.erase (r6 s))).card = P at hst hleaf
  generalize N6gM (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card (B₃.erase (r3 s)).card
    (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card (B₆.erase (r6 s)).card
    ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card
    ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card
    ((B₅.erase (r5 s)) ∩ (B₆.erase (r6 s))).card = M at hst hleaf
  generalize Rof (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card (B₃.erase (r3 s)).card
    (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card (B₆.erase (r6 s)).card (orb s) = R
    at hst hden hR
  generalize hNU0 : NUo (orb s) = NU at hst hden
  generalize GU 6 w s = U at hst hU ⊢
  generalize GB w B₁ B₂ B₃ B₄ B₅ B₆ s = Gb at hst hG ⊢
  push_cast at hst
  exact state_arith hU hG hR (by rw [← hNU0]; exact NUo_pos _) hden hleaf hst

/-! ### Pointwise classes -/

theorem kHX_le (c : ℕ) : kH c + kX c ≤ 1 ∧ kH c + kM c ≤ 1 := by
  unfold kH kX kM; constructor <;> split_ifs <;> omega

theorem eR_le_emax {m c c' : ℕ} (hp : pairR m c c' = true) : eR m c c' ≤ emax m (kH c) (kH c') := by
  rw [pairR_iff] at hp
  have h1 := kHX_le c
  have h2 := kHX_le c'
  unfold eR emax
  rw [capR_eq]
  split_ifs with hm
  · simp only [Nat.sub_eq]; omega
  · have hm0 : m = 0 := by omega
    subst hm0
    have hX : kX c = 0 := by rcases hp.2.1 with h | h <;> omega
    have hM : kM c' = 0 := by rcases hp.1 with h | h <;> omega
    simp only [Nat.sub_eq]; omega

theorem emax_le {m h h' : ℕ} (hh : h ≤ 1) (hh' : h' ≤ 1) :
    emax m h h' ≤ 5 + h ∧ emax m h h' ≤ 5 + h' := by
  unfold emax; split_ifs <;> omega

/-- The arithmetic of a pointwise state. -/
theorem point_arith {U Gb : ℝ} {R NU Nm P M P' M' : ℕ} (hU : 0 ≤ U) (hR : 0 < R) (hNU : 0 < NU)
    (hNM : NU * R ≤ Nm) (hpt : Nm + 1000000000000 * M' ≤ 1000000000000 * P')
    (hanti : ((P' : ℤ) - M') ≤ (P : ℤ) - M)
    (hst : (1000000000000 : ℝ) * ((P : ℝ) - M) * U ≤ (R : ℝ) * NU * Gb) : U ≤ Gb := by
  have h1 : ((NU * R : ℕ) : ℝ) ≤ 1000000000000 * ((P' : ℝ) - M') := by
    have : ((Nm + 1000000000000 * M' : ℕ) : ℝ) ≤ ((1000000000000 * P' : ℕ) : ℝ) := by
      exact_mod_cast hpt
    have h2 : ((NU * R : ℕ) : ℝ) ≤ Nm := by exact_mod_cast hNM
    push_cast at this; linarith
  have h3 : ((P' : ℝ) - M') ≤ (P : ℝ) - M := by exact_mod_cast hanti
  push_cast at h1
  have hpos : (0 : ℝ) < NU * R := by
    have : (0 : ℝ) < NU := by exact_mod_cast hNU
    have : (0 : ℝ) < R := by exact_mod_cast hR
    positivity
  have k1 : (NU : ℝ) * R * U ≤ 1000000000000 * ((P : ℝ) - M) * U :=
    mul_le_mul_of_nonneg_right (by linarith) hU
  have key : U * (NU * R) ≤ Gb * (NU * R) := by nlinarith
  exact le_of_mul_le_mul_right key hpos

/-- A mismatch `a` dominates `m`: the same support and `a ≤ m`. -/
def domR (a m : ℕ) : Bool := (Nat.beq a 0 && Nat.beq m 0) || (Nat.blt 0 a && Nat.ble a m)

theorem emax_dom {a m : ℕ} (h : domR a m = true) (hh hh' : ℕ) : emax m hh hh' ≤ emax a hh hh' := by
  unfold domR at h
  rw [beq_eq_decide, beq_eq_decide, blt_eq_decide, ble_eq_decide] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold emax
  rcases h with ⟨rfl, rfl⟩ | ⟨h0, hle⟩
  · exact le_refl _
  · split_ifs <;> omega

/-- **The seam inequality for a pointwise class**, checked at a dominating class `a` (by
`N6g_anti`, the check at `a` covers `m`). -/
theorem seam_point {w : Wt6} (hw : InCone6 w) {X₁ X₂ X₃ X₄ X₅ X₆ B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ}
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6) {m1 m2 m3 m4 m5 a1 a2 a3 a4 a5 : ℕ}
    (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ [m1, m2, m3, m4, m5]) (hC : ptChk NML a1 a2 a3 a4 a5 = true)
    (d1 : domR a1 m1 = true) (d2 : domR a2 m2 = true) (d3 : domR a3 m3 = true)
    (d4 : domR a4 m4 = true) (d5 : domR a5 m5 = true) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by
  refine Finset.sum_le_sum fun s hs' => ?_
  have hs := proper_of_mem_sts hs'
  obtain ⟨hc5, hv, ⟨n1, n2, n3, n4, n5, n6⟩, ⟨i1, i2, i3, i4, i5⟩⟩ :=
    codes_facts hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm hs
  obtain ⟨-, -, p1, p2, p3, p4, p5⟩ := hv
  set c := kcodes B₁ B₂ B₃ B₄ B₅ B₆ s
  have hst := state66 hw hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hs
  rw [n1, n2, n3, n4, n5, n6, i1, i2, i3, i4, i5] at hst
  have l1 := kH_le (r1 c); have l2 := kH_le (r2 c); have l3 := kH_le (r3 c)
  have l4 := kH_le (r4 c); have l5 := kH_le (r5 c); have l6 := kH_le (r6 c)
  have hpt := ptChk_spec hC (h1 := kH (r1 c)) (h2 := kH (r2 c)) (h3 := kH (r3 c))
    (h4 := kH (r4 c)) (h5 := kH (r5 c)) (h6 := kH (r6 c)) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  -- the worst state of the bonuses
  have ea1 := (eR_le_emax p1).trans (emax_dom d1 _ _)
  have ea2 := (eR_le_emax p2).trans (emax_dom d2 _ _)
  have ea3 := (eR_le_emax p3).trans (emax_dom d3 _ _)
  have ea4 := (eR_le_emax p4).trans (emax_dom d4 _ _)
  have ea5 := (eR_le_emax p5).trans (emax_dom d5 _ _)
  have b1 := emax_le (m := a1) l1 l2; have b2 := emax_le (m := a2) l2 l3
  have b3 := emax_le (m := a3) l3 l4; have b4 := emax_le (m := a4) l4 l5
  have b5 := emax_le (m := a5) l5 l6
  have hanti := N6g_anti (n1 := ((5 + kH (r1 c) : ℕ) : ℤ)) (n2 := ((5 + kH (r2 c) : ℕ) : ℤ))
    (n3 := ((5 + kH (r3 c) : ℕ) : ℤ)) (n4 := ((5 + kH (r4 c) : ℕ) : ℤ))
    (n5 := ((5 + kH (r5 c) : ℕ) : ℤ)) (n6 := ((5 + kH (r6 c) : ℕ) : ℤ))
    (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
    (by push_cast; omega) (by push_cast; omega)
    (e1 := (eR m1 (r1 c) (r2 c) : ℤ)) (e1' := (emax a1 (kH (r1 c)) (kH (r2 c)) : ℤ))
    (e2 := (eR m2 (r2 c) (r3 c) : ℤ)) (e2' := (emax a2 (kH (r2 c)) (kH (r3 c)) : ℤ))
    (e3 := (eR m3 (r3 c) (r4 c) : ℤ)) (e3' := (emax a3 (kH (r3 c)) (kH (r4 c)) : ℤ))
    (e4 := (eR m4 (r4 c) (r5 c) : ℤ)) (e4' := (emax a4 (kH (r4 c)) (kH (r5 c)) : ℤ))
    (e5 := (eR m5 (r5 c) (r6 c) : ℤ)) (e5' := (emax a5 (kH (r5 c)) (kH (r6 c)) : ℤ))
    (by exact_mod_cast ea1) (by exact_mod_cast ea2) (by exact_mod_cast ea3) (by exact_mod_cast ea4)
    (by exact_mod_cast ea5) (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
    (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
    (by push_cast; omega)
  rw [← N6gPM_eq, ← N6gPM_eq] at hanti
  rw [← N6gPM_eq] at hst
  have hidx := nidx_lt (kH56 (r1 c)) (kH56 (r2 c)) (kH56 (r3 c)) (kH56 (r4 c)) (kH56 (r5 c))
    (kH56 (r6 c))
  have hNM := NML_ok _ hidx (orb s) (orb s).2
  rw [NUL_eq] at hNM
  have hR := R_pos _ hidx (orb s) (orb s).2
  have hRof : Rof (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c)) (5 + kH (r4 c)) (5 + kH (r5 c))
      (5 + kH (r6 c)) (orb s) = (patCerts.getD (nidx (5 + kH (r1 c)) (5 + kH (r2 c))
        (5 + kH (r3 c)) (5 + kH (r4 c)) (5 + kH (r5 c)) (5 + kH (r6 c))) default).R.getD (orb s) 0 :=
    rfl
  rw [hRof] at hst
  generalize (patCerts.getD (nidx (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c)) (5 + kH (r4 c))
    (5 + kH (r5 c)) (5 + kH (r6 c))) default).R.getD (orb s) 0 = R at hst hNM hR
  generalize NML.getD (nidx (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c)) (5 + kH (r4 c))
    (5 + kH (r5 c)) (5 + kH (r6 c))) 0 = Nm at hpt hNM
  generalize N6gP (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c)) (5 + kH (r4 c)) (5 + kH (r5 c))
    (5 + kH (r6 c)) (eR m1 (r1 c) (r2 c)) (eR m2 (r2 c) (r3 c)) (eR m3 (r3 c) (r4 c))
    (eR m4 (r4 c) (r5 c)) (eR m5 (r5 c) (r6 c)) = P at hst hanti
  generalize N6gM (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c)) (5 + kH (r4 c)) (5 + kH (r5 c))
    (5 + kH (r6 c)) (eR m1 (r1 c) (r2 c)) (eR m2 (r2 c) (r3 c)) (eR m3 (r3 c) (r4 c))
    (eR m4 (r4 c) (r5 c)) (eR m5 (r5 c) (r6 c)) = M at hst hanti
  generalize N6gP (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c)) (5 + kH (r4 c)) (5 + kH (r5 c))
    (5 + kH (r6 c)) (emax a1 (kH (r1 c)) (kH (r2 c))) (emax a2 (kH (r2 c)) (kH (r3 c)))
    (emax a3 (kH (r3 c)) (kH (r4 c))) (emax a4 (kH (r4 c)) (kH (r5 c)))
    (emax a5 (kH (r5 c)) (kH (r6 c))) = P' at hpt hanti
  generalize N6gM (5 + kH (r1 c)) (5 + kH (r2 c)) (5 + kH (r3 c)) (5 + kH (r4 c)) (5 + kH (r5 c))
    (5 + kH (r6 c)) (emax a1 (kH (r1 c)) (kH (r2 c))) (emax a2 (kH (r2 c)) (kH (r3 c)))
    (emax a3 (kH (r3 c)) (kH (r4 c))) (emax a4 (kH (r4 c)) (kH (r5 c)))
    (emax a5 (kH (r5 c)) (kH (r6 c))) = M' at hpt hanti
  generalize hNU0 : NUo (orb s) = NU at hst hNM
  have hNU : 0 < NU := by rw [← hNU0]; exact NUo_pos _
  exact point_arith (GU_nonneg hw s) hR hNU hNM hpt hanti (by push_cast at hst ⊢; linarith)

/-! ### Certificate classes -/

/-- The leaf inequality at the codes of an actual state gives its state inequality. -/
theorem state_of_codes {w : Wt6} (hw : InCone6 w) {B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ}
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6) {m1 m2 m3 m4 m5 : ℕ}
    (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ [m1, m2, m3, m4, m5]) {s : T6} (hs : Proper s) {D K F : ℕ}
    {den : List ℕ}
    (hden : NUo (orb s) * (patCerts.getD (nidx (5 + kH (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (5 + kH (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (5 + kH (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))) default).R.getD (orb s) 0
      ≤ den.getD (nidx (5 + kH (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (5 + kH (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (5 + kH (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))) 0)
    (hleaf : (D + K - F) * den.getD (nidx (5 + kH (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (5 + kH (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (5 + kH (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))) 0
      + D * 1000000000000 * N6gM (5 + kH (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (5 + kH (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (5 + kH (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (eR m1 (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (eR m2 (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (eR m3 (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (eR m4 (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (eR m5 (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
      ≤ D * 1000000000000 * N6gP (5 + kH (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (5 + kH (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (5 + kH (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (eR m1 (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (eR m2 (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (eR m3 (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (eR m4 (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (eR m5 (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)) (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))) :
    GU 6 w s * ((D : ℝ) + K - F) ≤ D * GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by
  obtain ⟨-, -, ⟨n1, n2, n3, n4, n5, n6⟩, ⟨i1, i2, i3, i4, i5⟩⟩ :=
    codes_facts hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm hs
  have hidx := nidx_lt (kH56 (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
    (kH56 (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (kH56 (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
    (kH56 (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (kH56 (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
    (kH56 (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
  have hR := R_pos _ hidx (orb s) (orb s).2
  refine state_of_leaf hw hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hs (F := F)
    (den := den.getD (nidx (5 + kH (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (5 + kH (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (5 + kH (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
        (5 + kH (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))) 0) ?_ ?_ ?_
  · rw [n1, n2, n3, n4, n5, n6]; exact hden
  · rw [n1, n2, n3, n4, n5, n6]; exact hR
  · rw [n1, n2, n3, n4, n5, n6, i1, i2, i3, i4, i5]; exact hleaf

/-- Pins without equalities. -/
def eqFree (P : List BPin6) : Bool := P.all fun q => (peelEqs q.peels).isEmpty

theorem fired_eqFree {P : List BPin6} (hP : eqFree P = true) (c p p' : T6) :
    fired P c p = fired P c p' := by
  unfold fired
  congr 1
  apply List.map_congr_left
  intro q hq
  have h := List.all_eq_true.mp hP q hq
  have e : ∀ p, eqOKp q p = true := by
    intro p
    unfold eqOKp
    rw [List.isEmpty_iff] at h
    rw [h]; rfl
  rw [evc_split, evc_split, e p, e p']

/-- **The seam inequality for a compact certificate.** -/
theorem seam_compact {w : Wt6} (hw : InCone6 w) {X₁ X₂ X₃ X₄ X₅ X₆ B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ}
    (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card) (h₄ : 5 ≤ X₄.card)
    (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card)
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6) {m1 m2 m3 m4 m5 : ℕ}
    (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ [m1, m2, m3, m4, m5]) {P : List BPin6} {D K : ℕ} (hD : 0 < D)
    (hP : P.all BPin6.okb = true) (hE : eqFree P = true) (hL : lamBnd P [m1, m2, m3, m4, m5] ≤ K)
    {t : D6} (ht : treeOK t NML = true)
    (hC : chkW m1 m2 m3 m4 m5 D K t (rowTable P) (lastLists P)
      (maskOf (fun q => eqOKp q (0, 1, 0, 1, 0, 1)) P) = true) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by
  refine seam_of_states hw h₁ h₂ h₃ h₄ h₅ h₆ hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm hD hP hL fun s hs' => ?_
  have hs := proper_of_mem_sts hs'
  obtain ⟨hc5, hv, -, -⟩ := codes_facts hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm hs
  have hk := chkW_spec hP ht hC hc5 hv
  rw [fired_eqFree hE _ (0, 1, 0, 1, 0, 1) (canon s)] at hk
  refine state_of_codes hw hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm hs ?_ hk
  have hidx := nidx_lt (kH56 (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
    (kH56 (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (kH56 (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
    (kH56 (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (kH56 (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
    (kH56 (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
  have := NML_ok _ hidx (orb s) (orb s).2
  rwa [NUL_eq] at this

theorem canon_index {s : T6} (hs : Proper s) :
    ∃ i < 52, canons.getD i (0, 0, 0, 0, 0, 0) = canon s := by
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem (canon_mem hs)
  have hl : canons.length = 52 := by decide +kernel
  refine ⟨i, by rw [← hl]; exact hi, ?_⟩
  rw [List.getD_eq_getElem _ _ hi, e]

/-- **The seam inequality for a pattern-aware certificate.** -/
theorem seam_pattern {w : Wt6} (hw : InCone6 w) {X₁ X₂ X₃ X₄ X₅ X₆ B₁ B₂ B₃ B₄ B₅ B₆ : Finset ℕ}
    (h₁ : 5 ≤ X₁.card) (h₂ : 5 ≤ X₂.card) (h₃ : 5 ≤ X₃.card) (h₄ : 5 ≤ X₄.card)
    (h₅ : 5 ≤ X₅.card) (h₆ : 5 ≤ X₆.card)
    (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6)
    (hB₅ : B₅.card = 6) (hB₆ : B₆.card = 6) {m1 m2 m3 m4 m5 : ℕ}
    (hm : MOK B₁ B₂ B₃ B₄ B₅ B₆ [m1, m2, m3, m4, m5]) {P : List BPin6} {D K : ℕ} (hD : 0 < D)
    (hP : P.all BPin6.okb = true) (hL : lamBnd P [m1, m2, m3, m4, m5] ≤ K)
    {T : List D6} (hT : ∀ o < 32, treeOK (T.getD o default) (DRL o) = true)
    (hC : ∀ i < 52, chkW m1 m2 m3 m4 m5 D K (T.getD (orb (canons.getD i (0, 0, 0, 0, 0, 0))) default)
      (rowTable P) (lastLists P)
      (maskOf (fun q => eqOKp q (canons.getD i (0, 0, 0, 0, 0, 0))) P) = true) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GU 6 w s
      ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅ X₆, GB w B₁ B₂ B₃ B₄ B₅ B₆ s := by
  refine seam_of_states hw h₁ h₂ h₃ h₄ h₅ h₆ hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm hD hP hL fun s hs' => ?_
  have hs := proper_of_mem_sts hs'
  obtain ⟨hc5, hv, -, -⟩ := codes_facts hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm hs
  obtain ⟨i, hi, hci⟩ := canon_index hs
  have hk := chkW_spec hP (hT _ (orb (canons.getD i (0, 0, 0, 0, 0, 0))).2) (hC i hi) hc5 hv
  rw [hci] at hk
  have ho : orb (canon s) = orb s := (orb_congr (samePat_canon hs)).symm
  rw [ho] at hk
  refine state_of_codes hw hB₁ hB₂ hB₃ hB₄ hB₅ hB₆ hm hs ?_ hk
  have hidx := nidx_lt (kH56 (r1 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
    (kH56 (r2 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (kH56 (r3 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
    (kH56 (r4 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s))) (kH56 (r5 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
    (kH56 (r6 (kcodes B₁ B₂ B₃ B₄ B₅ B₆ s)))
  rw [DRL_getD hidx, NUL_eq]

end GridGen.Six
