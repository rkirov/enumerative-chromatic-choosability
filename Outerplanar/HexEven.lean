/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.LongDesign6
import Outerplanar.HexWalks

/-!
# The hexagon bound through even faces of length at least six

**`hexEvenSix`**: an even face of length at least six maps the hexagon bound (`Hex`) on all its
path edges to the hexagon bound on its root edge, with the factor `56/59 = 1/K`. This is the
"centre law" of the research notes `ai_research_notes/OUTERPLANAR_ELEVEN_AND_CENTRAL_SQUARE_2026-11-23.md`
("Two distinguished edges on an even face", `L ≥ 6`) and
`ai_research_notes/OUTERPLANAR_THIRTEEN_AND_GAUGE_OBSTRUCTION_2026-11-23.md` (Steps 2 and 3): the
balanced designs of the ball proofs make every step uniform on a matched family, and their centre
entropy is at least `log α - log K`.

* Length six: the six designs of `Outerplanar/LongDesign6.lean` (`hexCert_*`) give the cell
  constants `num_k / 2^32`; their product is at least `(11 · 56/59)^6` (`hexNum_*_ok`, the
  tightest being the rotations, log margin `2.8 · 10⁻⁴`). No weight is moved, so only the hub and
  the balance of the certificates are used.
* Length at least eight: the uniform-midpoint design of `Outerplanar/LongDesign8.lean`
  (`cell_hub`, `cells_bal`) with the numbers `(56/59 d_n)³ ≤ 27 s_r d_r² s_{r+1} d_{r+1}²`
  (`hexLong_numbers`; a polynomial with positive coefficients in `x - 8`, `x = 2^r`).

Formalized by Claude (milestone M3 of `ai_research_notes/OUTERPLANAR_13_15_LEAN_PLAN.md`).
-/

namespace Outerplanar

open Finset

/-! ### Assembly -/

/-- Six cells with constants `N k` and walk products `Γ k` whose total is `U ^ e`. -/
theorem hex_assembly_gen {e : ℕ} (he : 0 < e) {N p Γ : Fin 6 → ℝ} {U B : ℝ}
    (hN : ∀ k, 0 ≤ N k) (hp : ∀ k, 0 ≤ p k) (hΓ : ∀ k, 0 ≤ Γ k)
    (hub : ∀ k, N k ^ e * Γ k ≤ p k ^ e) (hprod : ∏ k, Γ k = U ^ e) (hB : 0 ≤ B) (hU : B ≤ U) :
    (∏ k, N k) * B ≤ ∏ k, p k := by
  have hN0 : 0 ≤ ∏ k, N k := prod_nonneg fun k _ => hN k
  have h1 : ∏ k, (N k ^ e * Γ k) ≤ ∏ k, p k ^ e :=
    Finset.prod_le_prod₀ (fun k _ => mul_nonneg (pow_nonneg (hN k) _) (hΓ k)) fun k _ => hub k
  rw [Finset.prod_mul_distrib, hprod, Finset.prod_pow, Finset.prod_pow] at h1
  have h2 : ((∏ k, N k) * B) ^ e ≤ (∏ k, p k) ^ e := by
    calc ((∏ k, N k) * B) ^ e = (∏ k, N k) ^ e * B ^ e := mul_pow _ _ _
      _ ≤ (∏ k, N k) ^ e * U ^ e :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hU _) (pow_nonneg hN0 _)
      _ ≤ _ := h1
  exact (pow_le_pow_iff_left₀ (mul_nonneg hN0 hB) (prod_nonneg fun k _ => hp k) he.ne').mp h2

/-! ### Length six -/

/-- The cell constants of a certificate pay for the hexagon target at the scale `56/59`. -/
def HexNumOK (num : Fin 6 → ℕ) : Prop := 616 ^ 6 * hexD ^ 6 ≤ 59 ^ 6 * ∏ k, num k

instance (num : Fin 6 → ℕ) : Decidable (HexNumOK num) := by unfold HexNumOK; infer_instance

theorem hexNum_id_ok : HexNumOK hexNum_id := by decide +kernel

theorem hexNum_p1_ok : HexNumOK hexNum_p1 := by decide +kernel

theorem hexNum_p2_ok : HexNumOK hexNum_p2 := by decide +kernel

theorem hexNum_t0_ok : HexNumOK hexNum_t0 := by decide +kernel

theorem hexNum_t1_ok : HexNumOK hexNum_t1 := by decide +kernel

theorem hexNum_t2_ok : HexNumOK hexNum_t2 := by decide +kernel

theorem hex_designs_K (σ : Fin 3 → Fin 3) (hσ : Function.Injective σ) :
    ∃ (ns : Fin 6 → List ℕ) (num : Fin 6 → ℕ), HexCert σ ns num ∧ HexNumOK num := by
  rcases inj_cases σ hσ with rfl | rfl | rfl | ⟨a, rfl⟩
  · exact ⟨_, _, hexCert_id, hexNum_id_ok⟩
  · exact ⟨_, _, hexCert_p1, hexNum_p1_ok⟩
  · exact ⟨_, _, hexCert_p2, hexNum_p2_ok⟩
  · fin_cases a
    · exact ⟨_, _, hexCert_t0, hexNum_t0_ok⟩
    · exact ⟨_, _, hexCert_t1, hexNum_t1_ok⟩
    · exact ⟨_, _, hexCert_t2, hexNum_t2_ok⟩

/-- **The hexagon inequality of a five-step path**, for every bijection `σ`, with the constant
`616/59 = (56/59) · 11`. -/
theorem walks_hex_six (Ms : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (hlen : Ms.length = 5)
    (hM : ∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hhex : List.Forall₂ OffHex Ms As) (σ : Fin 3 → Fin 3) (hσ : Function.Injective σ) :
    ((616 / 59 : ℝ) * As.prod) ^ 6 ≤ ∏ k, pw Ms (offPair k).1 (σ (offPair k).2) := by
  obtain ⟨ns, num, ⟨hlenc, hsum, hbal, hhub, -⟩, hok⟩ := hex_designs_K σ hσ
  have hp := pw_nonneg Ms hM
  have hD : (0 : ℝ) < hexD := by unfold hexD; positivity
  have hw0 := wpr_nonneg Ms hM
  have hΓ0 : ∀ k, 0 ≤ dΓ Ms σ ns k := fun k => zipWith_pow_nonneg _ _ _ fun w _ => hw0 _ w
  have hcell : ∀ k, ((num k : ℝ) / hexD) ^ 360 * dΓ Ms σ ns k
      ≤ pw Ms (offPair k).1 (σ (offPair k).2) ^ 360 := fun k => by
    set l := cw Ms.length (offPair k).1 (σ (offPair k).2)
    have key := amgm_list (l.map (wpr Ms (offPair k).1)) (ns k)
      (by rw [List.length_map]; simp only [l, hlen]; exact hlenc k)
      fun x hx => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
        exact hw0 _ w
    rw [List.zipWith_map_left, hsum k, ← pw_eq_cw] at key
    set Q := ((ns k).map fun c : ℕ => (c : ℝ) ^ c).prod
    have hQ : 0 ≤ Q := prod_pow_self_nonneg _
    have hh : ((num k : ℝ) / hexD) ^ 360 * Q ≤ (360 : ℝ) ^ 360 := by
      have := hhub k
      have hcast : ((((ns k).map fun c => c ^ c).prod : ℕ) : ℝ) = Q := cast_prod_pow _
      have h' : (num k : ℝ) ^ 360 * Q ≤ (360 : ℝ) ^ 360 * (hexD : ℝ) ^ 360 := by
        rw [← hcast]; exact_mod_cast this
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hD 360)]
      exact h'
    have hee : (0 : ℝ) < (360 : ℝ) ^ 360 := by positivity
    have key' : ((360 : ℕ) : ℝ) ^ 360 * dΓ Ms σ ns k
        ≤ Q * pw Ms (offPair k).1 (σ (offPair k).2) ^ 360 := key
    push_cast at key'
    refine le_of_mul_le_mul_left ?_ hee
    calc (360 : ℝ) ^ 360 * (((num k : ℝ) / hexD) ^ 360 * dΓ Ms σ ns k)
        = ((num k : ℝ) / hexD) ^ 360 * ((360 : ℝ) ^ 360 * dΓ Ms σ ns k) := by ring
      _ ≤ ((num k : ℝ) / hexD) ^ 360 * (Q * pw Ms (offPair k).1 (σ (offPair k).2) ^ 360) :=
          mul_le_mul_of_nonneg_left key' (by positivity)
      _ = (((num k : ℝ) / hexD) ^ 360 * Q) * pw Ms (offPair k).1 (σ (offPair k).2) ^ 360 := by
          ring
      _ ≤ (360 : ℝ) ^ 360 * pw Ms (offPair k).1 (σ (offPair k).2) ^ 360 :=
          mul_le_mul_of_nonneg_right hh (pow_nonneg (hp _ _) _)
  have hbal' : ∏ k, dΓ Ms σ ns k = up Ms 1 ^ 360 := by
    rw [← famProd_dfam, famProd_up 360 Ms _ (famOK_dfam _ σ ns) (by rw [hlen]; exact hbal),
      ← up_mul, one_mul]
  have hU := up_one_ge hhex hM fun A hA' => (hA A hA').le
  have key := hex_assembly_gen (e := 360) (by norm_num) (N := fun k => (num k : ℝ) / hexD)
    (fun k => by positivity) (fun k => hp _ _) hΓ0 hcell hbal'
    (pow_nonneg (List.prod_nonneg fun A hA' => (hA A hA').le) _) hU
  refine le_trans ?_ key
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (List.prod_nonneg fun A hA' =>
    (hA A hA').le) _)
  have hok' : (616 : ℝ) ^ 6 * (hexD : ℝ) ^ 6 ≤ 59 ^ 6 * ∏ k, (num k : ℝ) := by
    have := hok
    unfold HexNumOK at this
    exact_mod_cast this
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    le_div_iff₀ (pow_pos hD 6), div_pow]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
  linarith

/-! ### Length at least eight -/

/-- **The hexagon inequality of a path `L₁ ++ L₂` with a uniform midpoint**, for every bijection
`σ`, with any constant `N` whose cube is at most the effective count. -/
theorem walks_hex_mid' (L₁ L₂ : List (Fin 3 → Fin 3 → ℝ)) (As : List ℝ) (hl₁ : 2 ≤ L₁.length)
    (hl₂ : 2 ≤ L₂.length) (hM : ∀ M ∈ L₁ ++ L₂, ∀ a b, 0 ≤ M a b) (hA : ∀ A ∈ As, 0 < A)
    (hhex : List.Forall₂ OffHex (L₁ ++ L₂) As) {N : ℝ} (hN : 0 ≤ N)
    (hN3 : N ^ 3 ≤ 27 * ((sN L₁.length : ℝ) * (dN L₁.length : ℝ) ^ 2)
        * ((sN L₂.length : ℝ) * (dN L₂.length : ℝ) ^ 2))
    (σ : Fin 3 → Fin 3) (hσ : Function.Injective σ) :
    (N * As.prod) ^ 6 ≤ ∏ k, pw (L₁ ++ L₂) (offPair k).1 (σ (offPair k).2) := by
  have h₁ : ∀ M ∈ L₁, ∀ a b, 0 ≤ M a b := fun M hM' => hM M (List.mem_append_left _ hM')
  have h₂ : ∀ M ∈ L₂, ∀ a b, 0 ≤ M a b := fun M hM' => hM M (List.mem_append_right _ hM')
  set s₁ := sN L₁.length
  set d₁ := dN L₁.length
  set s₂ := sN L₂.length
  set d₂ := dN L₂.length
  set S := s₁ * d₁ * s₂ * d₂ with hS
  have dvs₁ : s₁ ∣ S := ((dvd_mul_right s₁ d₁).mul_right s₂).mul_right d₂
  have dvd₁ : d₁ ∣ S := ((dvd_mul_left d₁ s₁).mul_right s₂).mul_right d₂
  have dvs₂ : s₂ ∣ S := (dvd_mul_left s₂ (s₁ * d₁)).mul_right d₂
  have dvd₂ : d₂ ∣ S := dvd_mul_left d₂ _
  have hc₁ : ∀ a z, cnt L₁.length a z ∣ S := fun a z => by
    unfold cnt; split_ifs
    · exact dvs₁
    · exact dvd₁
  have hc₂ : ∀ z b, cnt L₂.length z b ∣ S := fun z b => by
    unfold cnt; split_ifs
    · exact dvs₂
    · exact dvd₂
  have hS2 : 2 ∣ S := (((two_dvd_sN _ (by omega)).mul_right d₁).mul_right s₂).mul_right d₂
  have hSpos : 0 < S := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (sN_pos_two _ hl₁)
    (dN_pos_one _ (by omega))) (sN_pos_two _ hl₂)) (dN_pos_one _ (by omega))
  have hne₁ : L₁ ≠ [] := fun h => by rw [h] at hl₁; simp at hl₁
  have hne₂ : L₂ ≠ [] := fun h => by rw [h] at hl₂; simp at hl₂
  have hp := pw_nonneg (L₁ ++ L₂) hM
  set X : ℝ := 27 * ((s₁ : ℝ) * (d₁ : ℝ) ^ 2) * ((s₂ : ℝ) * (d₂ : ℝ) ^ 2) with hX
  have hX0 : 0 ≤ X := by positivity
  have hbal : ∏ k : Fin 6, midΓ L₁ L₂ S (offPair k).1 (σ (offPair k).2)
      = up (L₁ ++ L₂) 1 ^ (3 * S) := by
    rw [cells_bal L₁ L₂ hne₁ hne₂ S dvd₁ dvs₁ dvd₂ dvs₂ hS2 hσ, ← up_mul, one_mul]
  have hU := up_one_ge hhex hM fun A hA' => (hA A hA').le
  have key := hex_assembly_gen (e := 3 * S) (by omega) (N := fun _ => X ^ ((1 : ℝ) / 3))
    (p := fun k => pw (L₁ ++ L₂) (offPair k).1 (σ (offPair k).2))
    (Γ := fun k => midΓ L₁ L₂ S (offPair k).1 (σ (offPair k).2))
    (fun _ => Real.rpow_nonneg hX0 _) (fun k => hp _ _)
    (fun k => midΓ_nonneg L₁ L₂ h₁ h₂ S _ _) (fun k => ?_) hbal
    (pow_nonneg (List.prod_nonneg fun A hA' => (hA A hA').le) _) hU
  · have hc3 : (X ^ ((1 : ℝ) / 3)) ^ 3 = X := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]; norm_num
    have hN' : N ≤ X ^ ((1 : ℝ) / 3) :=
      (pow_le_pow_iff_left₀ hN (Real.rpow_nonneg hX0 _) (by norm_num : (3 : ℕ) ≠ 0)).mp
        (by rw [hc3]; exact hN3)
    refine le_trans ?_ key
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (List.prod_nonneg fun A hA' =>
      (hA A hA').le) _)
    exact pow_le_pow_left₀ hN hN' 6
  · have kh := cell_hub L₁ L₂ h₁ h₂ S hc₁ hc₂ (offPair k).1 (σ (offPair k).2)
    have hc3 : (X ^ ((1 : ℝ) / 3)) ^ (3 * S) = X ^ S := by
      rw [pow_mul, show (X ^ ((1 : ℝ) / 3)) ^ 3 = X by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]; norm_num]
    show (X ^ ((1 : ℝ) / 3)) ^ (3 * S) * _ ≤ _
    rw [hc3]
    exact kh

/-- The polynomial inequality behind `hexLong_numbers`, for both signs. -/
theorem hexLong_poly (x : ℝ) (hx : 8 ≤ x) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    (56 / 59 * ((2 * x ^ 2 + 1) / 3)) ^ 3
      ≤ 27 * ((x + 2 * ε) / 3 * ((x - ε) / 3) ^ 2) * ((2 * x - 2 * ε) / 3 * ((2 * x + ε) / 3) ^ 2) := by
  obtain ⟨y, hy, rfl⟩ : ∃ y, 0 ≤ y ∧ x = y + 8 := ⟨x - 8, by linarith, by ring⟩
  rcases hε with rfl | rfl
  · have e : 27 * ((y + 8 + 2 * 1) / 3 * ((y + 8 - 1) / 3) ^ 2)
          * ((2 * (y + 8) - 2 * 1) / 3 * ((2 * (y + 8) + 1) / 3) ^ 2)
        - (56 / 59 * ((2 * (y + 8) ^ 2 + 1) / 3)) ^ 3
        = (238104 * y ^ 6 + 11428992 * y ^ 5 + 220311078 * y ^ 4 + 2176459882 * y ^ 3
          + 11525555622 * y ^ 2 + 30471843150 * y + 30179147236) / 5545233 := by ring
    have : 0 ≤ (238104 * y ^ 6 + 11428992 * y ^ 5 + 220311078 * y ^ 4 + 2176459882 * y ^ 3
          + 11525555622 * y ^ 2 + 30471843150 * y + 30179147236) / 5545233 := by positivity
    linarith
  · have e : 27 * ((y + 8 + 2 * -1) / 3 * ((y + 8 - -1) / 3) ^ 2)
          * ((2 * (y + 8) - 2 * -1) / 3 * ((2 * (y + 8) + -1) / 3) ^ 2)
        - (56 / 59 * ((2 * (y + 8) ^ 2 + 1) / 3)) ^ 3
        = (238104 * y ^ 6 + 11428992 * y ^ 5 + 220311078 * y ^ 4 + 2170709270 * y ^ 3
          + 11387540934 * y ^ 2 + 29370190194 * y + 27254550276) / 5545233 := by ring
    have : 0 ≤ (238104 * y ^ 6 + 11428992 * y ^ 5 + 220311078 * y ^ 4 + 2170709270 * y ^ 3
          + 11387540934 * y ^ 2 + 29370190194 * y + 27254550276) / 5545233 := by positivity
    linarith

/-- **The numbers of the long face at the scale `56/59`**: `n = 2 r + 1` steps, `r ≥ 3`. -/
theorem hexLong_numbers (r : ℕ) (hr : 3 ≤ r) :
    (56 / 59 * (dN (2 * r + 1) : ℝ)) ^ 3
      ≤ 27 * ((sN r : ℝ) * (dN r : ℝ) ^ 2) * ((sN (r + 1) : ℝ) * (dN (r + 1) : ℝ) ^ 2) := by
  have hx : (8 : ℝ) ≤ 2 ^ r := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
  have tn : ((2 ^ (2 * r + 1) : ℕ) : ℝ) = 2 * dN (2 * r + 1) + sN (2 * r + 1) := by
    exact_mod_cast two_pow_eq (2 * r + 1)
  have pn : (dN (2 * r + 1) : ℝ) = sN (2 * r + 1) + 1 := by
    exact_mod_cast (sN_dN_parity (2 * r + 1)).2 ⟨r, rfl⟩
  push_cast at tn
  have e2 : (2 : ℝ) ^ (2 * r + 1) = 2 * ((2 : ℝ) ^ r) ^ 2 := by ring
  rw [e2] at tn
  have hdn : (dN (2 * r + 1) : ℝ) = (2 * ((2 : ℝ) ^ r) ^ 2 + 1) / 3 := by linarith
  obtain ⟨ε, hε, h1, h2, h3, h4⟩ := counts_closed r
  rw [hdn, h1, h2, h3, h4]
  exact hexLong_poly _ hx ε hε

/-! ### The faces -/

/-- The index form shared by the face lemmas: frames along the path. -/
theorem hexEven_frames {m : ℕ} (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d)
    (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 < A j)
    (hE : ∀ j, Hex (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j))
    (α β : Fin 3 → ℕ) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hαm : ∀ a, α a ∈ Lu) (hβm : ∀ b, β b ∈ Lv) :
    ∃ (Ms : List (Fin 3 → Fin 3 → ℝ)) (σ : Fin 3 → Fin 3), Ms.length = m + 1 ∧
      (∀ M ∈ Ms, ∀ a b, 0 ≤ M a b) ∧ List.Forall₂ OffHex Ms (List.ofFn A) ∧
      Function.Injective σ ∧
      ∀ a b : Fin 3, pw Ms a (σ b) ≤ faceSum Li (fun _ _ => 1) E (α a) (β b) := by
  set Vs := List.ofFn Li ++ [Lv] with hVs
  have hVcard : ∀ L ∈ Vs, L.card = 3 := by
    intro L hL
    rcases List.mem_append.mp hL with h | h
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp h
      exact hLi i
    · rw [List.mem_singleton.mp h]
      exact hLv
  have hEs0 : ∀ E' ∈ List.ofFn E, ∀ c d, 0 ≤ E' c d := by
    intro E' hE' c d
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hE'
    exact hE0 i c d
  obtain ⟨ζs, hζs, hOff, hMnn⟩ := framesHex Vs (List.ofFn E) (List.ofFn A) Lu α hα hαm hVcard
    hEs0 (chainHex_of_fin Lu Lv Li E A hE)
  have hlenV : Vs.length = m + 1 := by simp [hVs]
  have hlenE : (List.ofFn E).length = m + 1 := List.length_ofFn
  have hlenζ : ζs.length = m + 1 := by rw [hζs.length_eq, hlenV]
  set Ms := mkMs α ζs (List.ofFn E) with hMs
  have hlenM : Ms.length = m + 1 := by
    rw [hMs, mkMs_length _ _ _ (by rw [hlenζ, hlenE]), hlenE]
  have hend : Function.Injective (ζs.getLastD α) ∧ ∀ a, (ζs.getLastD α) a ∈ Lv := by
    have h := forall₂_getLastD (P := fun ζ L => Function.Injective ζ ∧ ∀ a, ζ a ∈ L) ζs Vs α Lu
      hζs ⟨hα, hαm⟩
    have e : Vs.getLastD Lu = Lv := by
      rw [hVs, getLastD_append]
      rfl
    rwa [e] at h
  have himg : ∀ b, ∃ x, (ζs.getLastD α) x = β b := fun b => by
    have hb : β b ∈ univ.image (ζs.getLastD α) := by
      rw [image_enum hLv hend.1 hend.2]
      exact hβm b
    obtain ⟨x, -, hx⟩ := mem_image.mp hb
    exact ⟨x, hx⟩
  choose σ hσ using himg
  have hσinj : Function.Injective σ := fun b b' e => hβ (by rw [← hσ b, ← hσ b', e])
  refine ⟨Ms, σ, hlenM, hMnn, hOff, hσinj, fun a b => ?_⟩
  rw [faceSum_eq_psum Li Lv E (α a) (β b) (hβm b), ← hσ b]
  exact pw_le_psum Vs (List.ofFn E) ζs α (by rw [hlenE, hlenV]) hζs hEs0 a (σ b)

/-- **An even face of length at least six maps the hexagon bound on all its path edges to the
hexagon bound on its root edge**, with the factor `56/59`. -/
theorem hexEvenSix (m : ℕ) (hev : Even m) (h4 : 4 ≤ m) (Lu Lv : Finset ℕ)
    (Li : Fin m → Finset ℕ) (hLv : Lv.card = 3) (hLi : ∀ j, (Li j).card = 3)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ)
    (hA : ∀ j, 0 < A j)
    (hE : ∀ j, Hex (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    Hex Lu Lv (faceSum Li (fun _ _ => 1) E) (56 / 59 * faceConst3 m * ∏ j, A j) := by
  refine hex_of_idx fun α β hα hβ hαm hβm _ => ?_
  obtain ⟨Ms, σ, hlenM, hMnn, hOff, hσinj, hcell⟩ :=
    hexEven_frames Lu Lv Li hLv hLi E hE0 A hA hE α β hα hβ hαm hβm
  have hAs : ∀ A' ∈ List.ofFn A, 0 < A' := by
    intro A' hA'
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hA'
    exact hA i
  have hp := pw_nonneg Ms hMnn
  have key : ((56 / 59 : ℝ) * (dN (m + 1) : ℝ) * (List.ofFn A).prod) ^ 6
      ≤ ∏ k, pw Ms (offPair k).1 (σ (offPair k).2) := by
    rcases Nat.lt_or_ge m 6 with h | h
    · obtain rfl : m = 4 := by obtain ⟨k, hk⟩ := hev; omega
      have h11 : (dN (4 + 1) : ℝ) = 11 := by
        rw [show dN (4 + 1) = 11 by decide]; norm_num
      rw [h11, show (56 / 59 : ℝ) * 11 = 616 / 59 by norm_num]
      exact walks_hex_six Ms (List.ofFn A) hlenM hMnn hAs hOff σ hσinj
    · obtain ⟨r, hr⟩ := hev
      have hr3 : 3 ≤ r := by omega
      have hlen' : Ms.length = 2 * r + 1 := by rw [hlenM]; omega
      have e : Ms.take r ++ Ms.drop r = Ms := List.take_append_drop r Ms
      have hl₁ : (Ms.take r).length = r := by simp; omega
      have hl₂ : (Ms.drop r).length = r + 1 := by simp; omega
      have hN3 := hexLong_numbers r hr3
      have k := walks_hex_mid' (Ms.take r) (Ms.drop r) (List.ofFn A) (by omega) (by omega)
        (by rw [e]; exact hMnn) hAs (by rw [e]; exact hOff)
        (N := 56 / 59 * (dN (2 * r + 1) : ℝ)) (by positivity)
        (by rw [hl₁, hl₂]; exact hN3) σ hσinj
      rw [e] at k
      have e' : dN (m + 1) = dN (2 * r + 1) := by congr 1; omega
      rw [e']
      exact k
  calc (56 / 59 * faceConst3 m * ∏ j, A j) ^ 6
      = ((56 / 59 : ℝ) * (dN (m + 1) : ℝ) * (List.ofFn A).prod) ^ 6 := by
        rw [faceConst3_eq_dN, List.prod_ofFn]
    _ ≤ ∏ k, pw Ms (offPair k).1 (σ (offPair k).2) := key
    _ ≤ _ := Finset.prod_le_prod₀ (fun k _ => hp _ _) fun k _ => hcell _ _

end Outerplanar
