/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Five.CertF5

/-!
# Height five, `k = 6`: dual certificates over the state bits

`ai_research_notes/H5_K6_ANALYTIC_2026-10-23.md` §3.3. For the quads of `bitQuads5`, the count
part of a state is kept exactly as a function of its state bits instead of the universal
constant `κ`.

**State bits.** Row `i` of a previous column `s` has a code (`rowCode`): `0` if `sᵢ ∉ Bᵢ`
(`h = 1`), and otherwise records whether `sᵢ ∈ Bᵢ ∖ Bᵢ₋₁` (`xm`) and whether `sᵢ ∈ Bᵢ ∖ Bᵢ₊₁`
(`xp`) (`B₀ := B₁`, `B₆ := B₅`). The list sizes are `nᵢ = 5 + h`, and the consecutive
intersections `eⱼ = 4 - μⱼ + hⱼ₋₁ + xpⱼ₋₁ + hⱼ + xmⱼ` (`card_inter_code`), so by greedy
minimality `|sts A| ≥ N5(greedy)(n, e)`, a function of the codes.

**The certificate.** For a quad, rationals `C = Cn/Cd` and `ρₖ = aₖ/dₖ ∈ (0, 1]`, one for each of
the eleven pins `xm₂ … xm₅`, `xp₁ … xp₄`, `xm ∨ xp` on rows `2 … 4` (`piv`), with
`N5(greedy)(n, e) ≥ C ∏ₖ ρₖ^{πₖ}` for every admissible code vector (`bitOK`, by `decide`). Then
`log |sts A| ≥ log C + Σₖ πₖ log ρₖ` (`count_bits`), and with the pattern lemma
`GB ≥ GU · (1 + Kr (o(s)) + log γ + Σₖ πₖ log ρₖ)`, `γ = C/(κ · 5t⁴)`. Each pin holds on at most
`min (q|D|, 1)` of the uniform weight (`D` its set of colours, `|D| ≤` the relevant mismatches),
so the averaged gain is at least `K̄ + log γ + Σₖ bₖ log ρₖ` (`seam_of_bit`).
-/

namespace GridGen.Five

open Finset Real

/-! ### Row codes -/

/-- The code of one row: `0` if the colour misses the list, else `1 + [∉ previous] + 2[∉ next]`
in the order `1` (both in), `2` (only `xm`), `3` (only `xp`), `4` (both). -/
def rowCode (Bp Bi Bn : Finset ℕ) (x : ℕ) : ℕ :=
  if x ∈ Bi then (if x ∈ Bp then (if x ∈ Bn then 1 else 3) else (if x ∈ Bn then 2 else 4))
  else 0

def cH (c : ℕ) : ℕ := if c = 0 then 1 else 0
def cM (c : ℕ) : ℕ := if c = 2 ∨ c = 4 then 1 else 0
def cX (c : ℕ) : ℕ := if c = 3 ∨ c = 4 then 1 else 0
def cU (c : ℕ) : ℕ := if c = 2 ∨ c = 3 ∨ c = 4 then 1 else 0

section codes
variable (Bp Bi Bn : Finset ℕ) (x : ℕ)

theorem cH_code : cH (rowCode Bp Bi Bn x) = if x ∈ Bi then 0 else 1 := by
  unfold cH rowCode; split_ifs <;> simp_all

theorem cM_code : cM (rowCode Bp Bi Bn x) = if x ∈ Bi \ Bp then 1 else 0 := by
  unfold cM rowCode; simp only [mem_sdiff]; split_ifs <;> simp_all

theorem cX_code : cX (rowCode Bp Bi Bn x) = if x ∈ Bi \ Bn then 1 else 0 := by
  unfold cX rowCode; simp only [mem_sdiff]; split_ifs <;> simp_all

theorem cU_code : cU (rowCode Bp Bi Bn x) = if x ∈ (Bi \ Bp) ∪ (Bi \ Bn) then 1 else 0 := by
  unfold cU rowCode; simp only [mem_union, mem_sdiff]; split_ifs <;> simp_all

theorem rowCode_le : rowCode Bp Bi Bn x ≤ 4 := by
  unfold rowCode; split_ifs <;> norm_num

end codes

/-! ### The Boolean check -/

/-- The eleven pins of a code vector. -/
def piv (k c1 c2 c3 c4 c5 : ℕ) : ℕ :=
  match k with
  | 0 => cM c2
  | 1 => cM c3
  | 2 => cM c4
  | 3 => cM c5
  | 4 => cX c1
  | 5 => cX c2
  | 6 => cX c3
  | 7 => cX c4
  | 8 => cU c2
  | 9 => cU c3
  | 10 => cU c4
  | _ => 0

theorem cM_01 (c : ℕ) : cM c = 0 ∨ cM c = 1 := by unfold cM; split_ifs <;> simp
theorem cX_01 (c : ℕ) : cX c = 0 ∨ cX c = 1 := by unfold cX; split_ifs <;> simp
theorem cU_01 (c : ℕ) : cU c = 0 ∨ cU c = 1 := by unfold cU; split_ifs <;> simp

theorem piv_01 (k c1 c2 c3 c4 c5 : ℕ) :
    piv k c1 c2 c3 c4 c5 = 0 ∨ piv k c1 c2 c3 c4 c5 = 1 := by
  unfold piv
  split <;> first | exact cM_01 _ | exact cX_01 _ | exact cU_01 _ | exact Or.inl rfl

/-- A product over `k < n`. -/
def pprod (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => pprod f n * f n

theorem pprod_eq (f : ℕ → ℕ) (n : ℕ) : pprod f n = ∏ k ∈ range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pprod, ih, Finset.prod_range_succ]

/-- The numerator and denominator of `ρₖ`. -/
def rhoN (rho : List (ℕ × ℕ)) (k : ℕ) : ℕ := (rho.getD k (1, 1)).1
def rhoD (rho : List (ℕ × ℕ)) (k : ℕ) : ℕ := (rho.getD k (1, 1)).2

/-- The consecutive intersection of a code pair. -/
def nE (m cp ci : ℕ) : ℕ := 4 + cH cp + cX cp + cH ci + cM ci - m

/-- The admissible code vectors of a quad. -/
def bvalid (m2 m3 m4 m5 c1 c2 c3 c4 c5 : ℕ) : Bool :=
  cM c1 == 0 && cX c5 == 0 &&
  (cM c2 == 0 || 0 < m2) && (cM c3 == 0 || 0 < m3) && (cM c4 == 0 || 0 < m4) &&
  (cM c5 == 0 || 0 < m5) && (cX c1 == 0 || 0 < m2) && (cX c2 == 0 || 0 < m3) &&
  (cX c3 == 0 || 0 < m4) && (cX c4 == 0 || 0 < m5) &&
  decide (m2 ≤ 4 + cH c1 + cX c1 + cH c2 + cM c2) &&
  decide (m3 ≤ 4 + cH c2 + cX c2 + cH c3 + cM c3) &&
  decide (m4 ≤ 4 + cH c3 + cX c3 + cH c4 + cM c4) &&
  decide (m5 ≤ 4 + cH c4 + cX c4 + cH c5 + cM c5)

/-- The check at one code vector. -/
def bitAt (m2 m3 m4 m5 Cn Cd : ℕ) (rho : List (ℕ × ℕ)) (c1 c2 c3 c4 c5 : ℕ) : Bool :=
  !(bvalid m2 m3 m4 m5 c1 c2 c3 c4 c5) ||
    decide (Cn * pprod (fun k => if piv k c1 c2 c3 c4 c5 = 1 then rhoN rho k else 1) 11
        + kapM (5 + cH c1) (5 + cH c2) (5 + cH c3) (5 + cH c4) (5 + cH c5) (nE m2 c1 c2)
            (nE m3 c2 c3) (nE m4 c3 c4) (nE m5 c4 c5)
          * (Cd * pprod (fun k => if piv k c1 c2 c3 c4 c5 = 1 then rhoD rho k else 1) 11)
      ≤ kapP (5 + cH c1) (5 + cH c2) (5 + cH c3) (5 + cH c4) (5 + cH c5) (nE m2 c1 c2)
            (nE m3 c2 c3) (nE m4 c3 c4) (nE m5 c4 c5)
          * (Cd * pprod (fun k => if piv k c1 c2 c3 c4 c5 = 1 then rhoD rho k else 1) 11))

/-- The check over all code vectors. -/
def bitOK (m2 m3 m4 m5 Cn Cd : ℕ) (rho : List (ℕ × ℕ)) : Bool :=
  allUpTo (fun c1 => allUpTo (fun c2 => allUpTo (fun c3 => allUpTo (fun c4 => allUpTo
    (fun c5 => bitAt m2 m3 m4 m5 Cn Cd rho c1 c2 c3 c4 c5) 4) 4) 4) 4) 4

/-! ### The count of one state from its codes -/

theorem card_erase_code {B : Finset ℕ} (hB : B.card = 6) (Bp Bn : Finset ℕ) (x : ℕ) :
    (B.erase x).card = 5 + cH (rowCode Bp B Bn x) := by
  rw [cH_code]
  by_cases h : x ∈ B
  · rw [Finset.card_erase_of_mem h, hB]; simp [h]
  · rw [Finset.erase_eq_of_notMem h, hB]; simp [h]

/-- **The consecutive intersection from the codes.** -/
theorem card_inter_code {B C : Finset ℕ} (hB : B.card = 6) (hC : C.card = 6) {m : ℕ}
    (hm : (B ∩ C).card + m = 6) (Bp Cn : Finset ℕ) {x y : ℕ} (hxy : x ≠ y) :
    ((B.erase x) ∩ (C.erase y)).card + m
      = 4 + cH (rowCode Bp B C x) + cX (rowCode Bp B C x) + cH (rowCode B C Cn y)
        + cM (rowCode B C Cn y) := by
  have h := Four.card_inter_erase hB hC hxy
  rw [mu_eq_of hm] at h
  have e1 : Four.hb B x = (cH (rowCode Bp B C x) : ℝ) := by
    rw [cH_code]; unfold Four.hb; split_ifs <;> simp
  have e2 : Four.hb C y = (cH (rowCode B C Cn y) : ℝ) := by
    rw [cH_code]; unfold Four.hb; split_ifs <;> simp
  have e3 : Four.zz B C x y = (cX (rowCode Bp B C x) : ℝ) + (cM (rowCode B C Cn y) : ℝ) := by
    rw [cX_code, cM_code, Four.zz_eq]; split_ifs <;> simp
  rw [e1, e2, e3] at h
  push_cast at h
  have : (((B.erase x) ∩ (C.erase y)).card : ℝ) + m
      = ((4 + cH (rowCode Bp B C x) + cX (rowCode Bp B C x) + cH (rowCode B C Cn y)
        + cM (rowCode B C Cn y) : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

/-- The codes of a state. -/
def codes (B₁ B₂ B₃ B₄ B₅ : Finset ℕ) (s : T5) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (rowCode B₁ B₁ B₂ (r1 s), rowCode B₁ B₂ B₃ (r2 s), rowCode B₂ B₃ B₄ (r3 s),
    rowCode B₃ B₄ B₅ (r4 s), rowCode B₄ B₅ B₅ (r5 s))

theorem sdiff_pos {B C : Finset ℕ} (hB : B.card = 6) {m : ℕ} (hm : (C ∩ B).card + m = 6) {x : ℕ}
    (hx : x ∈ B \ C) : 0 < m := by
  have h1 := Finset.card_sdiff_add_card_inter B C
  rw [Finset.inter_comm] at h1
  have h2 : 0 < (B \ C).card := Finset.card_pos.mpr ⟨x, hx⟩
  omega

/-- The pin multipliers of a state, as a product. -/
noncomputable def pinLog (rho : List (ℕ × ℕ)) (c : ℕ × ℕ × ℕ × ℕ × ℕ) : ℝ :=
  ∑ k ∈ range 11, (piv k c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 : ℝ)
    * log ((rhoN rho k : ℝ) / rhoD rho k)

/-- **The count of one state from its codes**:
`log (|sts A| / 5t⁴) ≥ log (C / 5t⁴) + Σₖ πₖ log ρₖ`. -/
theorem count_bits {B₁ B₂ B₃ B₄ B₅ : Finset ℕ} (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6)
    (hB₃ : B₃.card = 6) (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) {m2 m3 m4 m5 : ℕ}
    (c2 : (B₁ ∩ B₂).card + m2 = 6) (c3 : (B₂ ∩ B₃).card + m3 = 6)
    (c4 : (B₃ ∩ B₄).card + m4 = 6) (c5 : (B₄ ∩ B₅).card + m5 = 6)
    {Cn Cd : ℕ} {rho : List (ℕ × ℕ)} (hCn : 0 < Cn) (hCd : 0 < Cd)
    (hρ : ∀ k < 11, 0 < rhoN rho k ∧ 0 < rhoD rho k)
    (hok : bitOK m2 m3 m4 m5 Cn Cd rho = true) {s : T5} (hs : Proper s) :
    0 < ((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
        (B₅.erase (r5 s))).card : ℝ) ∧
    log ((Cn : ℝ) / Cd / (194481 / 125)) + pinLog rho (codes B₁ B₂ B₃ B₄ B₅ s)
      ≤ log (((sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
        (B₅.erase (r5 s))).card : ℝ) / (194481 / 125)) := by
  obtain ⟨p12, p23, p34, p45⟩ := hs
  set k1 := rowCode B₁ B₁ B₂ (r1 s) with hk1
  set k2 := rowCode B₁ B₂ B₃ (r2 s) with hk2
  set k3 := rowCode B₂ B₃ B₄ (r3 s) with hk3
  set k4 := rowCode B₃ B₄ B₅ (r4 s) with hk4
  set k5 := rowCode B₄ B₅ B₅ (r5 s) with hk5
  -- sizes and intersections
  have n1 := card_erase_code hB₁ B₁ B₂ (r1 s)
  have n2 := card_erase_code hB₂ B₁ B₃ (r2 s)
  have n3 := card_erase_code hB₃ B₂ B₄ (r3 s)
  have n4 := card_erase_code hB₄ B₃ B₅ (r4 s)
  have n5 := card_erase_code hB₅ B₄ B₅ (r5 s)
  have i2 := card_inter_code hB₁ hB₂ c2 B₁ B₃ p12
  have i3 := card_inter_code hB₂ hB₃ c3 B₁ B₄ p23
  have i4 := card_inter_code hB₃ hB₄ c4 B₂ B₅ p34
  have i5 := card_inter_code hB₄ hB₅ c5 B₃ B₅ p45
  rw [← hk1, ← hk2] at i2
  rw [← hk2, ← hk3] at i3
  rw [← hk3, ← hk4] at i4
  rw [← hk4, ← hk5] at i5
  rw [← hk1] at n1; rw [← hk2] at n2; rw [← hk3] at n3; rw [← hk4] at n4; rw [← hk5] at n5
  -- validity of the codes
  have hv : bvalid m2 m3 m4 m5 k1 k2 k3 k4 k5 = true := by
    have z1 : cM k1 = 0 := by rw [hk1, cM_code]; simp
    have z5 : cX k5 = 0 := by rw [hk5, cX_code]; simp
    have pm : ∀ {Bp Bi Bn : Finset ℕ} {x m : ℕ}, Bi.card = 6 → (Bp ∩ Bi).card + m = 6 →
        (cM (rowCode Bp Bi Bn x) == 0 || 0 < m) = true := by
      intro Bp Bi Bn x m hBi hm
      rw [cM_code]
      split_ifs with h
      · simp [sdiff_pos hBi hm h]
      · simp
    have px : ∀ {Bp Bi Bn : Finset ℕ} {x m : ℕ}, Bi.card = 6 → (Bi ∩ Bn).card + m = 6 →
        (cX (rowCode Bp Bi Bn x) == 0 || 0 < m) = true := by
      intro Bp Bi Bn x m hBi hm
      rw [cX_code]
      split_ifs with h
      · rw [Finset.inter_comm] at hm; simp [sdiff_pos hBi hm h]
      · simp
    simp only [bvalid, Bool.and_eq_true, decide_eq_true_eq, z1, z5, beq_self_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨trivial, trivial⟩, pm hB₂ c2⟩, pm hB₃ c3⟩, pm hB₄ c4⟩, pm hB₅ c5⟩,
      px hB₁ c2⟩, px hB₂ c3⟩, px hB₃ c4⟩, px hB₄ c5⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩
  have h1 := allUpTo_spec hok k1 (rowCode_le _ _ _ _)
  have h2 := allUpTo_spec h1 k2 (rowCode_le _ _ _ _)
  have h3 := allUpTo_spec h2 k3 (rowCode_le _ _ _ _)
  have h4 := allUpTo_spec h3 k4 (rowCode_le _ _ _ _)
  have h5 := allUpTo_spec h4 k5 (rowCode_le _ _ _ _)
  simp only [bitAt, hv, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h5
  -- the greedy bound for the actual lists
  have hg := N5g_le_card (A₁ := B₁.erase (r1 s)) (A₂ := B₂.erase (r2 s)) (A₃ := B₃.erase (r3 s))
    (A₄ := B₄.erase (r4 s)) (A₅ := B₅.erase (r5 s)) (by omega) (by omega) (by omega) (by omega)
  have e2 : nE m2 k1 k2 = ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card := by unfold nE; omega
  have e3 : nE m3 k2 k3 = ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card := by unfold nE; omega
  have e4 : nE m4 k3 k4 = ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card := by unfold nE; omega
  have e5 : nE m5 k4 k5 = ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card := by unfold nE; omega
  rw [e2, e3, e4, e5, ← n1, ← n2, ← n3, ← n4, ← n5] at h5
  rw [← kapP_kapM] at hg
  set N := (sts (B₁.erase (r1 s)) (B₂.erase (r2 s)) (B₃.erase (r3 s)) (B₄.erase (r4 s))
    (B₅.erase (r5 s))).card with hN
  set P := kapP (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card (B₃.erase (r3 s)).card
    (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card
    ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card
    ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card with hP
  set M := kapM (B₁.erase (r1 s)).card (B₂.erase (r2 s)).card (B₃.erase (r3 s)).card
    (B₄.erase (r4 s)).card (B₅.erase (r5 s)).card ((B₁.erase (r1 s)) ∩ (B₂.erase (r2 s))).card
    ((B₂.erase (r2 s)) ∩ (B₃.erase (r3 s))).card ((B₃.erase (r3 s)) ∩ (B₄.erase (r4 s))).card
    ((B₄.erase (r4 s)) ∩ (B₅.erase (r5 s))).card with hM
  set fN : ℕ → ℕ := fun k => if piv k k1 k2 k3 k4 k5 = 1 then rhoN rho k else 1 with hfN
  set fD : ℕ → ℕ := fun k => if piv k k1 k2 k3 k4 k5 = 1 then rhoD rho k else 1 with hfD
  have hpN : 0 < pprod fN 11 := by
    rw [pprod_eq]; exact Finset.prod_pos fun k hk => by
      simp only [hfN]; split_ifs
      · exact (hρ k (Finset.mem_range.mp hk)).1
      · norm_num
  have hpD : 0 < pprod fD 11 := by
    rw [pprod_eq]; exact Finset.prod_pos fun k hk => by
      simp only [hfD]; split_ifs
      · exact (hρ k (Finset.mem_range.mp hk)).2
      · norm_num
  -- in the reals: `N ≥ (Cn/Cd) · numerator/denominator`
  have h5R : (Cn : ℝ) * pprod fN 11 + M * (Cd * pprod fD 11) ≤ P * (Cd * pprod fD 11) := by
    exact_mod_cast h5
  have hgR : (P : ℝ) - M ≤ N := by exact_mod_cast hg
  have hCnR : (0 : ℝ) < Cn := by exact_mod_cast hCn
  have hCdR : (0 : ℝ) < Cd := by exact_mod_cast hCd
  have hpNR : (0 : ℝ) < pprod fN 11 := by exact_mod_cast hpN
  have hpDR : (0 : ℝ) < pprod fD 11 := by exact_mod_cast hpD
  have hD : (0 : ℝ) < Cd * pprod fD 11 := mul_pos hCdR hpDR
  have hNlow : (Cn : ℝ) / Cd * (pprod fN 11 / pprod fD 11) ≤ N := by
    have : (Cn : ℝ) * pprod fN 11 ≤ ((P : ℝ) - M) * (Cd * pprod fD 11) := by
      linarith only [h5R]
    have h' : (Cn : ℝ) * pprod fN 11 ≤ (N : ℝ) * (Cd * pprod fD 11) :=
      le_trans this (mul_le_mul_of_nonneg_right hgR hD.le)
    rw [div_mul_div_comm, div_le_iff₀ hD]
    linarith only [h']
  have hlow0 : (0 : ℝ) < (Cn : ℝ) / Cd * (pprod fN 11 / pprod fD 11) :=
    mul_pos (div_pos hCnR hCdR) (div_pos hpNR hpDR)
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hlow0 hNlow
  refine ⟨hN0, ?_⟩
  have hl := Real.log_le_log (div_pos hlow0 (by norm_num))
    (div_le_div_of_nonneg_right hNlow (by norm_num : (0 : ℝ) ≤ 194481 / 125))
  -- the log of the product
  have hprod : log ((pprod fN 11 : ℝ) / pprod fD 11) = pinLog rho (k1, k2, k3, k4, k5) := by
    rw [Real.log_div hpNR.ne' hpDR.ne', pprod_eq, pprod_eq]
    push_cast
    rw [Real.log_prod (fun k hk => by
        simp only [hfN]; split_ifs
        · exact_mod_cast (hρ k (Finset.mem_range.mp hk)).1.ne'
        · norm_num),
      Real.log_prod (fun k hk => by
        simp only [hfD]; split_ifs
        · exact_mod_cast (hρ k (Finset.mem_range.mp hk)).2.ne'
        · norm_num),
      ← Finset.sum_sub_distrib]
    unfold pinLog
    refine Finset.sum_congr rfl fun k hk => ?_
    have hpk := piv_01 k k1 k2 k3 k4 k5
    simp only [hfN, hfD]
    rcases hpk with h | h
    · simp [h]
    · simp only [h, ↓reduceIte, Nat.cast_one, one_mul]
      rw [Real.log_div (by exact_mod_cast (hρ k (Finset.mem_range.mp hk)).1.ne')
        (by exact_mod_cast (hρ k (Finset.mem_range.mp hk)).2.ne')]
  have esplit : (Cn : ℝ) / Cd * (pprod fN 11 / pprod fD 11) / (194481 / 125)
      = (Cn : ℝ) / Cd / (194481 / 125) * (pprod fN 11 / pprod fD 11) := by ring
  rw [esplit, Real.log_mul (div_pos (div_pos hCnR hCdR) (by norm_num)).ne'
    (div_pos hpNR hpDR).ne', hprod] at hl
  exact hl


/-! ### The averaged gain -/

/-- The pin bounds of a quad: each pin holds on at most `min (q · |D|, 1)` of the uniform
weight. -/
noncomputable def bnd (m2 m3 m4 m5 : ℕ) (k : ℕ) : ℝ :=
  match k with
  | 0 => min (qm5 * (m2 : ℝ)) 1
  | 1 => min (qm5 * (m3 : ℝ)) 1
  | 2 => min (qm5 * (m4 : ℝ)) 1
  | 3 => min (qe5 * (m5 : ℝ)) 1
  | 4 => min (qe5 * (m2 : ℝ)) 1
  | 5 => min (qm5 * (m3 : ℝ)) 1
  | 6 => min (qm5 * (m4 : ℝ)) 1
  | 7 => min (qm5 * (m5 : ℝ)) 1
  | 8 => min (qm5 * ((m2 : ℝ) + m3)) 1
  | 9 => min (qm5 * ((m3 : ℝ) + m4)) 1
  | 10 => min (qm5 * ((m4 : ℝ) + m5)) 1
  | _ => 0

theorem pin_set {Ω : Finset T5} (u : T5 → ℝ) (hu0 : ∀ t, 0 ≤ u t) (g : T5 → ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hc : ∀ c, ∑ t ∈ Ω.filter (fun t => g t = c), u t ≤ q * ∑ t ∈ Ω, u t)
    (D : Finset ℕ) {M : ℝ} (hD : (D.card : ℝ) ≤ M) :
    ∑ t ∈ Ω, u t * (if g t ∈ D then 1 else 0) ≤ min (q * M) 1 * ∑ t ∈ Ω, u t := by
  have h := pin_min5 u hu0 g hc D
  have hW : 0 ≤ ∑ t ∈ Ω, u t := Finset.sum_nonneg fun t _ => hu0 t
  refine h.trans (mul_le_mul_of_nonneg_right (min_le_min (mul_le_mul_of_nonneg_left hD hq0)
    le_rfl) hW)

theorem card_sdiff_eq {B C : Finset ℕ} (hB : B.card = 6) {m : ℕ} (hm : (C ∩ B).card + m = 6) :
    ((B \ C).card : ℝ) = m := by
  have h1 := Finset.card_sdiff_add_card_inter B C
  rw [Finset.inter_comm] at h1
  have : (B \ C).card = m := by omega
  rw [this]

theorem card_union_le' (D E : Finset ℕ) : (((D ∪ E).card : ℕ) : ℝ) ≤ (D.card : ℝ) + E.card := by
  exact_mod_cast Finset.card_union_le D E

/-- **The seam inequality from a dual certificate over the state bits.** -/
theorem seam_of_bit {w : Wt5} (hw : InBox5 w) {X₁ X₂ X₃ X₄ X₅ B₁ B₂ B₃ B₄ B₅ : Finset ℕ}
    (hX₁ : 5 ≤ X₁.card) (hX₂ : 5 ≤ X₂.card) (hX₃ : 5 ≤ X₃.card) (hX₄ : 5 ≤ X₄.card)
    (hX₅ : 5 ≤ X₅.card) (hB₁ : B₁.card = 6) (hB₂ : B₂.card = 6) (hB₃ : B₃.card = 6)
    (hB₄ : B₄.card = 6) (hB₅ : B₅.card = 6) {m2 m3 m4 m5 : ℕ}
    (c2 : (B₁ ∩ B₂).card + m2 = 6) (c3 : (B₂ ∩ B₃).card + m3 = 6)
    (c4 : (B₃ ∩ B₄).card + m4 = 6) (c5 : (B₄ ∩ B₅).card + m5 = 6)
    {Cn Cd : ℕ} {rho : List (ℕ × ℕ)} (hCn : 0 < Cn) (hCd : 0 < Cd)
    (hρ : ∀ k < 11, 0 < rhoN rho k ∧ 0 < rhoD rho k ∧ rhoN rho k ≤ rhoD rho k)
    (hok : bitOK m2 m3 m4 m5 Cn Cd rho = true)
    (hfin : 0 ≤ Kbar + log ((Cn : ℝ) / Cd / (123125 / 128018 * (194481 / 125)))
      + ∑ k ∈ range 11, bnd m2 m3 m4 m5 k * log ((rhoN rho k : ℝ) / rhoD rho k)) :
    ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GU 6 w s ≤ ∑ s ∈ sts X₁ X₂ X₃ X₄ X₅, GB w B₁ B₂ B₃ B₄ B₅ s := by
  set Ω := sts X₁ X₂ X₃ X₄ X₅ with hΩ
  set W := ∑ t ∈ Ω, GU 6 w t with hW
  have hu0 : ∀ t, 0 ≤ GU 6 w t := GU_nonneg5 hw
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun t _ => hu0 t
  have hCnR : (0 : ℝ) < Cn := by exact_mod_cast hCn
  have hCdR : (0 : ℝ) < Cd := by exact_mod_cast hCd
  set γ : ℝ := (Cn : ℝ) / Cd / (123125 / 128018 * (194481 / 125)) with hγ
  -- the state bound
  have hstate : ∀ s ∈ Ω, GU 6 w s * (1 + (Kr (orb s) + (log γ
      + pinLog rho (codes B₁ B₂ B₃ B₄ B₅ s)))) ≤ GB w B₁ B₂ B₃ B₄ B₅ s := by
    intro s hs
    have hp := proper_of_mem_sts hs
    obtain ⟨hN, hc⟩ := count_bits hB₁ hB₂ hB₃ hB₄ hB₅ c2 c3 c4 c5 hCn hCd
      (fun k hk => ⟨(hρ k hk).1, (hρ k hk).2.1⟩) hok hp
    refine state_bound_of_count hw hB₁ hB₂ hB₃ hB₄ hB₅ hp hN ?_
    have e : log (123125 / 128018) + log γ = log ((Cn : ℝ) / Cd / (194481 / 125)) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      congr 1
      rw [hγ]; field_simp
    linarith
  have hsum : ∑ s ∈ Ω, GU 6 w s * (1 + (Kr (orb s) + (log γ
      + pinLog rho (codes B₁ B₂ B₃ B₄ B₅ s)))) ≤ ∑ s ∈ Ω, GB w B₁ B₂ B₃ B₄ B₅ s :=
    Finset.sum_le_sum hstate
  -- the single-colour pins
  have f1 : ∀ c, ∑ t ∈ Ω.filter (fun t => r1 t = c), GU 6 w t ≤ qe5 * W := fun c =>
    pin_row1 hw hX₁ _ (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
  have f2 : ∀ c, ∑ t ∈ Ω.filter (fun t => r2 t = c), GU 6 w t ≤ qm5 * W := fun c =>
    pin_row2 hw hX₂ _ (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
  have f3 : ∀ c, ∑ t ∈ Ω.filter (fun t => r3 t = c), GU 6 w t ≤ qm5 * W := fun c =>
    pin_row3 hw hX₃ _ (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
  have f4 : ∀ c, ∑ t ∈ Ω.filter (fun t => r4 t = c), GU 6 w t ≤ qm5 * W := fun c =>
    pin_row4 hw hX₄ _ (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
  have f5 : ∀ c, ∑ t ∈ Ω.filter (fun t => r5 t = c), GU 6 w t ≤ qe5 * W := fun c =>
    pin_row5 hw hX₅ _ (fun _ => c) (fun _ _ => rfl) (fun _ h => h)
  have qe0 : (0 : ℝ) ≤ qe5 := by unfold qe5; norm_num
  have qm0 : (0 : ℝ) ≤ qm5 := by unfold qm5; norm_num
  have s21 := card_sdiff_eq hB₂ c2
  have s32 := card_sdiff_eq hB₃ c3
  have s43 := card_sdiff_eq hB₄ c4
  have s54 := card_sdiff_eq hB₅ c5
  have s12 := card_sdiff_eq hB₁ (show (B₂ ∩ B₁).card + m2 = 6 by rw [Finset.inter_comm]; exact c2)
  have s23 := card_sdiff_eq hB₂ (show (B₃ ∩ B₂).card + m3 = 6 by rw [Finset.inter_comm]; exact c3)
  have s34 := card_sdiff_eq hB₃ (show (B₄ ∩ B₃).card + m4 = 6 by rw [Finset.inter_comm]; exact c4)
  have s45 := card_sdiff_eq hB₄ (show (B₅ ∩ B₄).card + m5 = 6 by rw [Finset.inter_comm]; exact c5)
  -- each pin, as an indicator of a row colour in a set
  have hpin : ∀ k < 11, ∑ t ∈ Ω, GU 6 w t * (piv k (codes B₁ B₂ B₃ B₄ B₅ t).1
      (codes B₁ B₂ B₃ B₄ B₅ t).2.1 (codes B₁ B₂ B₃ B₄ B₅ t).2.2.1
      (codes B₁ B₂ B₃ B₄ B₅ t).2.2.2.1 (codes B₁ B₂ B₃ B₄ B₅ t).2.2.2.2 : ℝ)
      ≤ bnd m2 m3 m4 m5 k * W := by
    intro k hk
    interval_cases k
    · simp only [piv, codes, cM_code, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact pin_set (GU 6 w) hu0 r2 qm0 f2 (B₂ \ B₁) (le_of_eq s21)
    · simp only [piv, codes, cM_code, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact pin_set (GU 6 w) hu0 r3 qm0 f3 (B₃ \ B₂) (le_of_eq s32)
    · simp only [piv, codes, cM_code, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact pin_set (GU 6 w) hu0 r4 qm0 f4 (B₄ \ B₃) (le_of_eq s43)
    · simp only [piv, codes, cM_code, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact pin_set (GU 6 w) hu0 r5 qe0 f5 (B₅ \ B₄) (le_of_eq s54)
    · simp only [piv, codes, cX_code, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact pin_set (GU 6 w) hu0 r1 qe0 f1 (B₁ \ B₂) (le_of_eq s12)
    · simp only [piv, codes, cX_code, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact pin_set (GU 6 w) hu0 r2 qm0 f2 (B₂ \ B₃) (le_of_eq s23)
    · simp only [piv, codes, cX_code, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact pin_set (GU 6 w) hu0 r3 qm0 f3 (B₃ \ B₄) (le_of_eq s34)
    · simp only [piv, codes, cX_code, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact pin_set (GU 6 w) hu0 r4 qm0 f4 (B₄ \ B₅) (le_of_eq s45)
    · simp only [piv, codes, cU_code, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact pin_set (GU 6 w) hu0 r2 qm0 f2 ((B₂ \ B₁) ∪ (B₂ \ B₃))
        ((card_union_le' _ _).trans (by rw [s21, s23]))
    · simp only [piv, codes, cU_code, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact pin_set (GU 6 w) hu0 r3 qm0 f3 ((B₃ \ B₂) ∪ (B₃ \ B₄))
        ((card_union_le' _ _).trans (by rw [s32, s34]))
    · simp only [piv, codes, cU_code, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact pin_set (GU 6 w) hu0 r4 qm0 f4 ((B₄ \ B₃) ∪ (B₄ \ B₅))
        ((card_union_le' _ _).trans (by rw [s43, s45]))
  have hlogρ : ∀ k < 11, log ((rhoN rho k : ℝ) / rhoD rho k) ≤ 0 := fun k hk => by
    obtain ⟨a, b, c⟩ := hρ k hk
    apply Real.log_nonpos (by positivity)
    rw [div_le_one (by exact_mod_cast b)]; exact_mod_cast c
  have hpinsum : ∑ k ∈ range 11, bnd m2 m3 m4 m5 k * log ((rhoN rho k : ℝ) / rhoD rho k) * W
      ≤ ∑ t ∈ Ω, GU 6 w t * pinLog rho (codes B₁ B₂ B₃ B₄ B₅ t) := by
    unfold pinLog
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have e : ∑ t ∈ Ω, GU 6 w t * ((piv k (codes B₁ B₂ B₃ B₄ B₅ t).1
        (codes B₁ B₂ B₃ B₄ B₅ t).2.1 (codes B₁ B₂ B₃ B₄ B₅ t).2.2.1
        (codes B₁ B₂ B₃ B₄ B₅ t).2.2.2.1 (codes B₁ B₂ B₃ B₄ B₅ t).2.2.2.2 : ℝ)
          * log ((rhoN rho k : ℝ) / rhoD rho k))
        = log ((rhoN rho k : ℝ) / rhoD rho k) * ∑ t ∈ Ω, GU 6 w t * (piv k
          (codes B₁ B₂ B₃ B₄ B₅ t).1 (codes B₁ B₂ B₃ B₄ B₅ t).2.1 (codes B₁ B₂ B₃ B₄ B₅ t).2.2.1
          (codes B₁ B₂ B₃ B₄ B₅ t).2.2.2.1 (codes B₁ B₂ B₃ B₄ B₅ t).2.2.2.2 : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring
    rw [e]
    have := mul_le_mul_of_nonpos_left (hpin k hk') (hlogρ k hk')
    linarith
  have lk := sum_Kr hw hX₁ hX₂ hX₃ hX₄ hX₅
  have e : ∑ s ∈ Ω, GU 6 w s * (1 + (Kr (orb s) + (log γ + pinLog rho (codes B₁ B₂ B₃ B₄ B₅ s))))
      = W + (∑ t ∈ Ω, GU 6 w t * Kr (orb t) + log γ * W
        + ∑ t ∈ Ω, GU 6 w t * pinLog rho (codes B₁ B₂ B₃ B₄ B₅ t)) := by
    rw [hW, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have hFW := mul_nonneg hfin hW0
  have e2 : (Kbar + log γ + ∑ k ∈ range 11, bnd m2 m3 m4 m5 k * log ((rhoN rho k : ℝ) / rhoD rho k))
      * W = Kbar * W + log γ * W
        + ∑ k ∈ range 11, bnd m2 m3 m4 m5 k * log ((rhoN rho k : ℝ) / rhoD rho k) * W := by
    rw [add_mul, add_mul, Finset.sum_mul]
  rw [e2] at hFW
  linarith

end GridGen.Five
