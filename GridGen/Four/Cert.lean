/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import GridGen.Four.State

/-!
# Height four: the averaged certificate

After averaging, the per-state gain becomes a function of the three list mismatches alone:
`Fval k μ₂ μ₃ μ₄`. With `log (1 + x) ≥ x - x²/2` it is bounded below by the polynomial `Fg`, which
on each region where the mismatch indicators are constant is a concave quadratic in each variable
separately; so it is nonnegative on a box once it is nonnegative at the box's eight vertices.
Three boxes cover the nonzero integer mismatches, fourteen distinct vertices in all, checked for
each `k = 8, …, 15` by `norm_num`.
-/

namespace GridGen.Four

open Real

/-- The averaged fibre ratio `q = 1/(ρ(k-3))`. -/
noncomputable def qk (k : ℕ) : ℝ := 1 / (rho k * ((k - 3 : ℕ) : ℝ))

/-- The averaged gain. -/
noncomputable def Fval (k : ℕ) (μ2 μ3 μ4 : ℝ) : ℝ :=
  log (1 + μ2 / kA ((k : ℝ) - 1)) + log (1 + μ3 / kA ((k : ℝ) - 1))
    + log (1 + μ4 / kA ((k : ℝ) - 1))
    - 2 * qk k * (μ2 + μ3 + μ4) / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1))
    - J3 μ2 μ3 * ((μ2 + 1) * (μ3 + 1) / (((k : ℝ) - 1) ^ 2 * ((k : ℝ) - 1 - 1) ^ 2)
        + ku3 ((k : ℝ) - 1) * qk k)
    - J4 μ2 μ3 μ4 * ((μ3 + 2) * (μ4 + 1) / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1) ^ 3)
        + ku4e ((k : ℝ) - 1) * qk k + ku4b ((k : ℝ) - 1))
    - eta k * (1 + 4 * qk k) * (μ2 + 2 * μ3 + μ4)

/-- The averaged gain with the pattern term capped at `(1-ρ)/ρ`. -/
noncomputable def Fcap (k : ℕ) (μ2 μ3 μ4 : ℝ) : ℝ :=
  log (1 + μ2 / kA ((k : ℝ) - 1)) + log (1 + μ3 / kA ((k : ℝ) - 1))
    + log (1 + μ4 / kA ((k : ℝ) - 1))
    - 2 * qk k * (μ2 + μ3 + μ4) / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1))
    - J3 μ2 μ3 * ((μ2 + 1) * (μ3 + 1) / (((k : ℝ) - 1) ^ 2 * ((k : ℝ) - 1 - 1) ^ 2)
        + ku3 ((k : ℝ) - 1) * qk k)
    - J4 μ2 μ3 μ4 * ((μ3 + 2) * (μ4 + 1) / (((k : ℝ) - 1) * ((k : ℝ) - 1 - 1) ^ 3)
        + ku4e ((k : ℝ) - 1) * qk k + ku4b ((k : ℝ) - 1))
    - (1 - rho k) / rho k

/-- The polynomial lower bound, with the indicators as parameters. -/
noncomputable def Fg (A n q η u3 u4e u4b j3 j4 a b c : ℝ) : ℝ :=
  (a / A - a ^ 2 / (2 * A ^ 2)) + (b / A - b ^ 2 / (2 * A ^ 2)) + (c / A - c ^ 2 / (2 * A ^ 2))
    - 2 * q * (a + b + c) / (n * (n - 1))
    - j3 * ((a + 1) * (b + 1) / (n ^ 2 * (n - 1) ^ 2) + u3 * q)
    - j4 * ((b + 2) * (c + 1) / (n * (n - 1) ^ 3) + u4e * q + u4b)
    - η * (1 + 4 * q) * (a + 2 * b + c)

/-- A function with a concave quadratic secant identity, nonnegative at both ends of an
interval, is nonnegative on it. -/
theorem secant_nonneg {f : ℝ → ℝ} {lo hi s : ℝ} (hlh : lo ≤ hi) (hs : 0 ≤ s)
    (hf : ∀ x, f x * (hi - lo) = (hi - x) * f lo + (x - lo) * f hi + s * (x - lo) * (hi - x) * (hi - lo))
    (h0 : 0 ≤ f lo) (h1 : 0 ≤ f hi) {x : ℝ} (hx : lo ≤ x) (hx' : x ≤ hi) : 0 ≤ f x := by
  rcases hlh.lt_or_eq with hlt | heq
  · have hd : 0 < hi - lo := by linarith
    have := hf x
    have : 0 ≤ f x * (hi - lo) := by
      rw [this]
      have a1 : 0 ≤ (hi - x) * f lo := mul_nonneg (by linarith) h0
      have a2 : 0 ≤ (x - lo) * f hi := mul_nonneg (by linarith) h1
      have a3 : 0 ≤ s * (x - lo) * (hi - x) * (hi - lo) :=
        mul_nonneg (mul_nonneg (mul_nonneg hs (by linarith)) (by linarith)) hd.le
      linarith
    exact nonneg_of_mul_nonneg_left this hd
  · have : x = lo := by linarith
    rw [this]; exact h0

/-- **Vertices suffice.** -/
theorem Fg_box {A n q η u3 u4e u4b j3 j4 : ℝ} (hA : 0 < A)
    {la ha lb hb lc hc : ℝ} (hla : la ≤ ha) (hlb : lb ≤ hb) (hlc : lc ≤ hc)
    (hv : ∀ a ∈ ({la, ha} : Set ℝ), ∀ b ∈ ({lb, hb} : Set ℝ), ∀ c ∈ ({lc, hc} : Set ℝ),
      0 ≤ Fg A n q η u3 u4e u4b j3 j4 a b c)
    {a b c : ℝ} (ha1 : la ≤ a) (ha2 : a ≤ ha) (hb1 : lb ≤ b) (hb2 : b ≤ hb) (hc1 : lc ≤ c)
    (hc2 : c ≤ hc) : 0 ≤ Fg A n q η u3 u4e u4b j3 j4 a b c := by
  have hs : 0 ≤ 1 / (2 * A ^ 2) := by positivity
  have hAne : A ≠ 0 := hA.ne'
  -- in `c`
  have stepc : ∀ a b, 0 ≤ Fg A n q η u3 u4e u4b j3 j4 a b lc →
      0 ≤ Fg A n q η u3 u4e u4b j3 j4 a b hc → 0 ≤ Fg A n q η u3 u4e u4b j3 j4 a b c := by
    intro a b h0 h1
    refine secant_nonneg (f := fun c => Fg A n q η u3 u4e u4b j3 j4 a b c) hlc hs ?_ h0 h1 hc1 hc2
    intro x; simp only [Fg]; field_simp; ring
  have stepb : ∀ a c, 0 ≤ Fg A n q η u3 u4e u4b j3 j4 a lb c →
      0 ≤ Fg A n q η u3 u4e u4b j3 j4 a hb c → ∀ b, lb ≤ b → b ≤ hb →
      0 ≤ Fg A n q η u3 u4e u4b j3 j4 a b c := by
    intro a c h0 h1 b hb1 hb2
    refine secant_nonneg (f := fun b => Fg A n q η u3 u4e u4b j3 j4 a b c) hlb hs ?_ h0 h1 hb1 hb2
    intro x; simp only [Fg]; field_simp; ring
  have stepa : ∀ b c, 0 ≤ Fg A n q η u3 u4e u4b j3 j4 la b c →
      0 ≤ Fg A n q η u3 u4e u4b j3 j4 ha b c → ∀ a, la ≤ a → a ≤ ha →
      0 ≤ Fg A n q η u3 u4e u4b j3 j4 a b c := by
    intro b c h0 h1 a ha1 ha2
    refine secant_nonneg (f := fun a => Fg A n q η u3 u4e u4b j3 j4 a b c) hla hs ?_ h0 h1 ha1 ha2
    intro x; simp only [Fg]; field_simp; ring
  have vb : ∀ a ∈ ({la, ha} : Set ℝ), ∀ c ∈ ({lc, hc} : Set ℝ),
      0 ≤ Fg A n q η u3 u4e u4b j3 j4 a b c := fun a' ha' c' hc' =>
    stepb a' c' (hv a' ha' lb (by simp) c' hc') (hv a' ha' hb (by simp) c' hc') b hb1 hb2
  have vc : ∀ a ∈ ({la, ha} : Set ℝ), 0 ≤ Fg A n q η u3 u4e u4b j3 j4 a b c := fun a' ha' =>
    stepc a' b (vb a' ha' lc (by simp)) (vb a' ha' hc (by simp))
  exact stepa b c (vc la (by simp)) (vc ha (by simp)) a ha1 ha2

/-- A vertex value. -/
noncomputable def Vx (k : ℕ) (j3 a b c : ℝ) : ℝ :=
  Fg (kA ((k : ℝ) - 1)) ((k : ℝ) - 1) (qk k) (eta k) (ku3 ((k : ℝ) - 1)) (ku4e ((k : ℝ) - 1))
    (ku4b ((k : ℝ) - 1)) j3 1 a b c

/-! The vertex values, one `k` at a time. -/

set_option maxHeartbeats 2000000 in
theorem vertices_8 :
    (0 ≤ Vx 8 1 1 0 0 ∧ 0 ≤ Vx 8 1 1 0 8 ∧ 0 ≤ Vx 8 1 1 8 0 ∧ 0 ≤ Vx 8 1 1 8 8 ∧
      0 ≤ Vx 8 1 8 0 0 ∧ 0 ≤ Vx 8 1 8 0 8 ∧ 0 ≤ Vx 8 1 8 8 0 ∧ 0 ≤ Vx 8 1 8 8 8) ∧
    (0 ≤ Vx 8 1 0 1 0 ∧ 0 ≤ Vx 8 1 0 1 8 ∧ 0 ≤ Vx 8 1 0 8 0 ∧ 0 ≤ Vx 8 1 0 8 8) ∧
    (0 ≤ Vx 8 0 0 0 1 ∧ 0 ≤ Vx 8 0 0 0 8) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [Vx, Fg, kA, kt, ku3, ku4e, ku4b, qk, eta, rho]

set_option maxHeartbeats 2000000 in
theorem vertices_9 :
    (0 ≤ Vx 9 1 1 0 0 ∧ 0 ≤ Vx 9 1 1 0 9 ∧ 0 ≤ Vx 9 1 1 9 0 ∧ 0 ≤ Vx 9 1 1 9 9 ∧
      0 ≤ Vx 9 1 9 0 0 ∧ 0 ≤ Vx 9 1 9 0 9 ∧ 0 ≤ Vx 9 1 9 9 0 ∧ 0 ≤ Vx 9 1 9 9 9) ∧
    (0 ≤ Vx 9 1 0 1 0 ∧ 0 ≤ Vx 9 1 0 1 9 ∧ 0 ≤ Vx 9 1 0 9 0 ∧ 0 ≤ Vx 9 1 0 9 9) ∧
    (0 ≤ Vx 9 0 0 0 1 ∧ 0 ≤ Vx 9 0 0 0 9) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [Vx, Fg, kA, kt, ku3, ku4e, ku4b, qk, eta, rho]

set_option maxHeartbeats 2000000 in
theorem vertices_10 :
    (0 ≤ Vx 10 1 1 0 0 ∧ 0 ≤ Vx 10 1 1 0 10 ∧ 0 ≤ Vx 10 1 1 10 0 ∧ 0 ≤ Vx 10 1 1 10 10 ∧
      0 ≤ Vx 10 1 10 0 0 ∧ 0 ≤ Vx 10 1 10 0 10 ∧ 0 ≤ Vx 10 1 10 10 0 ∧ 0 ≤ Vx 10 1 10 10 10) ∧
    (0 ≤ Vx 10 1 0 1 0 ∧ 0 ≤ Vx 10 1 0 1 10 ∧ 0 ≤ Vx 10 1 0 10 0 ∧ 0 ≤ Vx 10 1 0 10 10) ∧
    (0 ≤ Vx 10 0 0 0 1 ∧ 0 ≤ Vx 10 0 0 0 10) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [Vx, Fg, kA, kt, ku3, ku4e, ku4b, qk, eta, rho]

set_option maxHeartbeats 2000000 in
theorem vertices_11 :
    (0 ≤ Vx 11 1 1 0 0 ∧ 0 ≤ Vx 11 1 1 0 11 ∧ 0 ≤ Vx 11 1 1 11 0 ∧ 0 ≤ Vx 11 1 1 11 11 ∧
      0 ≤ Vx 11 1 11 0 0 ∧ 0 ≤ Vx 11 1 11 0 11 ∧ 0 ≤ Vx 11 1 11 11 0 ∧ 0 ≤ Vx 11 1 11 11 11) ∧
    (0 ≤ Vx 11 1 0 1 0 ∧ 0 ≤ Vx 11 1 0 1 11 ∧ 0 ≤ Vx 11 1 0 11 0 ∧ 0 ≤ Vx 11 1 0 11 11) ∧
    (0 ≤ Vx 11 0 0 0 1 ∧ 0 ≤ Vx 11 0 0 0 11) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [Vx, Fg, kA, kt, ku3, ku4e, ku4b, qk, eta, rho]

set_option maxHeartbeats 2000000 in
theorem vertices_12 :
    (0 ≤ Vx 12 1 1 0 0 ∧ 0 ≤ Vx 12 1 1 0 12 ∧ 0 ≤ Vx 12 1 1 12 0 ∧ 0 ≤ Vx 12 1 1 12 12 ∧
      0 ≤ Vx 12 1 12 0 0 ∧ 0 ≤ Vx 12 1 12 0 12 ∧ 0 ≤ Vx 12 1 12 12 0 ∧ 0 ≤ Vx 12 1 12 12 12) ∧
    (0 ≤ Vx 12 1 0 1 0 ∧ 0 ≤ Vx 12 1 0 1 12 ∧ 0 ≤ Vx 12 1 0 12 0 ∧ 0 ≤ Vx 12 1 0 12 12) ∧
    (0 ≤ Vx 12 0 0 0 1 ∧ 0 ≤ Vx 12 0 0 0 12) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [Vx, Fg, kA, kt, ku3, ku4e, ku4b, qk, eta, rho]

set_option maxHeartbeats 2000000 in
theorem vertices_13 :
    (0 ≤ Vx 13 1 1 0 0 ∧ 0 ≤ Vx 13 1 1 0 13 ∧ 0 ≤ Vx 13 1 1 13 0 ∧ 0 ≤ Vx 13 1 1 13 13 ∧
      0 ≤ Vx 13 1 13 0 0 ∧ 0 ≤ Vx 13 1 13 0 13 ∧ 0 ≤ Vx 13 1 13 13 0 ∧ 0 ≤ Vx 13 1 13 13 13) ∧
    (0 ≤ Vx 13 1 0 1 0 ∧ 0 ≤ Vx 13 1 0 1 13 ∧ 0 ≤ Vx 13 1 0 13 0 ∧ 0 ≤ Vx 13 1 0 13 13) ∧
    (0 ≤ Vx 13 0 0 0 1 ∧ 0 ≤ Vx 13 0 0 0 13) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [Vx, Fg, kA, kt, ku3, ku4e, ku4b, qk, eta, rho]

set_option maxHeartbeats 2000000 in
theorem vertices_14 :
    (0 ≤ Vx 14 1 1 0 0 ∧ 0 ≤ Vx 14 1 1 0 14 ∧ 0 ≤ Vx 14 1 1 14 0 ∧ 0 ≤ Vx 14 1 1 14 14 ∧
      0 ≤ Vx 14 1 14 0 0 ∧ 0 ≤ Vx 14 1 14 0 14 ∧ 0 ≤ Vx 14 1 14 14 0 ∧ 0 ≤ Vx 14 1 14 14 14) ∧
    (0 ≤ Vx 14 1 0 1 0 ∧ 0 ≤ Vx 14 1 0 1 14 ∧ 0 ≤ Vx 14 1 0 14 0 ∧ 0 ≤ Vx 14 1 0 14 14) ∧
    (0 ≤ Vx 14 0 0 0 1 ∧ 0 ≤ Vx 14 0 0 0 14) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [Vx, Fg, kA, kt, ku3, ku4e, ku4b, qk, eta, rho]

set_option maxHeartbeats 2000000 in
theorem vertices_15 :
    (0 ≤ Vx 15 1 1 0 0 ∧ 0 ≤ Vx 15 1 1 0 15 ∧ 0 ≤ Vx 15 1 1 15 0 ∧ 0 ≤ Vx 15 1 1 15 15 ∧
      0 ≤ Vx 15 1 15 0 0 ∧ 0 ≤ Vx 15 1 15 0 15 ∧ 0 ≤ Vx 15 1 15 15 0 ∧ 0 ≤ Vx 15 1 15 15 15) ∧
    (0 ≤ Vx 15 1 0 1 0 ∧ 0 ≤ Vx 15 1 0 1 15 ∧ 0 ≤ Vx 15 1 0 15 0 ∧ 0 ≤ Vx 15 1 0 15 15) ∧
    (0 ≤ Vx 15 0 0 0 1 ∧ 0 ≤ Vx 15 0 0 0 15) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [Vx, Fg, kA, kt, ku3, ku4e, ku4b, qk, eta, rho]

/-- **The fourteen vertices**, for each `k = 8, …, 15`. -/
theorem vertices {k : ℕ} (hk8 : 8 ≤ k) (hk15 : k ≤ 15) :
    (0 ≤ Vx k 1 1 0 0 ∧ 0 ≤ Vx k 1 1 0 k ∧ 0 ≤ Vx k 1 1 k 0 ∧ 0 ≤ Vx k 1 1 k k ∧
      0 ≤ Vx k 1 k 0 0 ∧ 0 ≤ Vx k 1 k 0 k ∧ 0 ≤ Vx k 1 k k 0 ∧ 0 ≤ Vx k 1 k k k) ∧
    (0 ≤ Vx k 1 0 1 0 ∧ 0 ≤ Vx k 1 0 1 k ∧ 0 ≤ Vx k 1 0 k 0 ∧ 0 ≤ Vx k 1 0 k k) ∧
    (0 ≤ Vx k 0 0 0 1 ∧ 0 ≤ Vx k 0 0 0 k) := by
  interval_cases k
  · exact_mod_cast vertices_8
  · exact_mod_cast vertices_9
  · exact_mod_cast vertices_10
  · exact_mod_cast vertices_11
  · exact_mod_cast vertices_12
  · exact_mod_cast vertices_13
  · exact_mod_cast vertices_14
  · exact_mod_cast vertices_15

/-- The mismatches are integers: zero or at least one. -/
theorem mu_cases {k : ℕ} {B C : Finset ℕ} (hB : B.card = k) : mu k B C = 0 ∨ 1 ≤ mu k B C := by
  unfold mu
  have h : (B ∩ C).card ≤ k := hB ▸ Finset.card_le_card Finset.inter_subset_left
  rcases (show (B ∩ C).card = k ∨ (B ∩ C).card + 1 ≤ k by omega) with h1 | h1
  · left; rw [h1]; ring
  · right
    have : (((B ∩ C).card + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast h1
    push_cast at this; linarith

/-- `log (1 + x/A) ≥ x/A - x²/(2A²)`. -/
theorem log_quad {x A : ℝ} (hx : 0 ≤ x) (hA : 0 < A) :
    x / A - x ^ 2 / (2 * A ^ 2) ≤ log (1 + x / A) := by
  have := log_one_add_ge (div_nonneg hx hA.le)
  have e : x / A - (x / A) ^ 2 / 2 = x / A - x ^ 2 / (2 * A ^ 2) := by field_simp
  linarith

/-- **The certificate**: the averaged gain is nonnegative for every list system. -/
theorem Fval_nonneg {k : ℕ} (hk8 : 8 ≤ k) (hk15 : k ≤ 15) {μ2 μ3 μ4 : ℝ}
    (h2 : μ2 = 0 ∨ 1 ≤ μ2) (h3 : μ3 = 0 ∨ 1 ≤ μ3) (h4 : μ4 = 0 ∨ 1 ≤ μ4)
    (h2k : μ2 ≤ k) (h3k : μ3 ≤ k) (h4k : μ4 ≤ k) : 0 ≤ Fval k μ2 μ3 μ4 := by
  have hk8' : (8 : ℝ) ≤ k := by exact_mod_cast hk8
  have hA : 0 < kA ((k : ℝ) - 1) := by unfold kA; nlinarith
  have hn2 : (k : ℝ) - 1 - 1 = (k : ℝ) - 1 - 1 := rfl
  have p2 : 0 ≤ μ2 := by rcases h2 with h | h <;> linarith
  have p3 : 0 ≤ μ3 := by rcases h3 with h | h <;> linarith
  have p4 : 0 ≤ μ4 := by rcases h4 with h | h <;> linarith
  have l2 := log_quad p2 hA
  have l3 := log_quad p3 hA
  have l4 := log_quad p4 hA
  obtain ⟨V1, V2, V3⟩ := vertices hk8 hk15
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have h1k : (1 : ℝ) ≤ k := by linarith
  -- `Fval ≥ Fg` with the indicators of the region
  have key : ∀ j3 j4 : ℝ, J3 μ2 μ3 = j3 → J4 μ2 μ3 μ4 = j4 →
      Fg (kA ((k : ℝ) - 1)) ((k : ℝ) - 1) (qk k) (eta k) (ku3 ((k : ℝ) - 1)) (ku4e ((k : ℝ) - 1))
        (ku4b ((k : ℝ) - 1)) j3 j4 μ2 μ3 μ4 ≤ Fval k μ2 μ3 μ4 := by
    intro j3 j4 e3 e4
    unfold Fval Fg; rw [e3, e4]
    have : (k : ℝ) - 1 - 1 = (k : ℝ) - 1 - 1 := rfl
    linarith
  by_cases z23 : μ2 + μ3 = 0
  · have e2 : μ2 = 0 := by linarith
    have e3 : μ3 = 0 := by linarith
    rcases h4 with e4 | h4
    · subst e2 e3 e4
      unfold Fval J3 J4; norm_num
    · refine le_trans ?_ (key 0 1 (by simp [J3, z23]) (by simp [J4, z23]; linarith))
      rw [e2, e3]
      obtain ⟨w1, w2⟩ := V3
      refine Fg_box hA le_rfl le_rfl h1k ?_ le_rfl le_rfl le_rfl le_rfl h4 h4k
      intro a ha b hb c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self] at ha hb hc
      subst ha hb
      rcases hc with rfl | rfl
      · exact w1
      · exact w2
  · have j3 : J3 μ2 μ3 = 1 := by simp [J3, z23]
    have j4 : J4 μ2 μ3 μ4 = 1 := by
      have : μ2 + μ3 + μ4 ≠ 0 := by intro h; apply z23; linarith
      simp [J4, this]
    refine le_trans ?_ (key 1 1 j3 j4)
    rcases h2 with e2 | h2
    · have h3' : 1 ≤ μ3 := by
        rcases h3 with e3 | h3
        · exfalso; apply z23; rw [e2, e3]; ring
        · exact h3
      rw [e2]
      obtain ⟨w1, w2, w3, w4⟩ := V2
      refine Fg_box hA le_rfl h1k (by linarith) ?_ le_rfl le_rfl h3' h3k p4 h4k
      intro a ha b hb c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self] at ha hb hc
      subst ha
      rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> assumption
    · obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := V1
      refine Fg_box hA h1k (by linarith) (by linarith) ?_ h2 h2k p3 h3k p4 h4k
      intro a ha b hb c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
        assumption

end GridGen.Four
