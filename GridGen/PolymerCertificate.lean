import GridGen.PolymerParityMonotonicity
import ListColoring.Rename

/-!
# ECC from a parity certificate

`CertifiedAt D k` packages the whole polymer argument's hypotheses with its numbers
abstracted: a `ParityCert D x₀ e o r` and an activity `x = q⁻¹ ≤ x₀` whose root penalty
`k x r` fits inside the singleton surplus `k x - 1`. The finite interpolation between
`P(G,k)` and `P(G,L)` is then positive, monotone under vertex deletion, and has derivative at
least `(1 - 2eo)` times its positive edge terms. Hence, for every graph of maximum degree at
most `D`:

* `colConst_le_col_of_certifiedAt`: `P(G,k) ≤ P(G,L)`, i.e. ECC at `k`;
* `colConst_lt_col_of_certifiedAt_of_adj`: strict inequality when two adjacent lists differ;
* `col_eq_colConst_iff_of_certifiedAt`: on a connected graph, equality holds exactly for the
  constant assignments.

`certifiedAt_of_parityCert` is the scaled form every concrete threshold uses: a certificate
at activity `s / k₀` with `s r ≤ s - 1` covers every list size `k ≥ k₀`. The strictness and
equality statements were first proved at the uniform threshold in `PolymerStability.lean`.
-/

namespace GridGen.Polymer

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem partitionSum_graphActivity_eq (L : ListAssignment V) (k : ℕ)
    (q t : ℝ) (U : Finset V) :
    partitionSum (fun S => graphActivity G L k q⁻¹ S t) U =
      interpolatedSum (blockCoefficient G) (listDeficiency L k) k t U / q ^ U.card := by
  have hw : (fun S => graphActivity G L k q⁻¹ S t) =
      (fun S => blockCoefficient G S * ((k : ℝ) - t * listDeficiency L k S) / q ^ S.card) := by
    funext S
    simp only [graphActivity, div_eq_mul_inv, inv_pow]
  rw [hw, partitionSum_normalized]
  rfl

/-- The hypotheses of the polymer argument at list size `k` for maximum degree `D`: a
normalization `q`, a certificate valid at activity `q⁻¹`, and the root budget. -/
def CertifiedAt (D k : ℕ) : Prop :=
  ∃ q x₀ e o r : ℝ, 0 < q ∧ ParityCert D x₀ e o r ∧ q⁻¹ ≤ x₀ ∧
    (k : ℝ) * q⁻¹ * r ≤ (k : ℝ) * q⁻¹ - 1

/-- A certificate at activity `s / k₀` with `s r ≤ s - 1` covers every `k ≥ k₀`:
take `q = k / s`, so that the activity `s / k` is at most `s / k₀` and `k q⁻¹ = s`. -/
theorem certifiedAt_of_parityCert {D k₀ : ℕ} {s e o r : ℝ}
    (hc : ParityCert D (s / k₀) e o r) (hs : 0 < s) (hsr : s * r ≤ s - 1)
    (hk₀ : 0 < k₀) {k : ℕ} (hk : k₀ ≤ k) : CertifiedAt D k := by
  have hk₀' : (0 : ℝ) < k₀ := by exact_mod_cast hk₀
  have hkk : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  have hk' : (0 : ℝ) < k := hk₀'.trans_le hkk
  have hks : (k : ℝ) * (k / s)⁻¹ = s := by rw [inv_div]; field_simp
  refine ⟨k / s, _, e, o, r, div_pos hk' hs, hc, ?_, by rw [hks]; exact hsr⟩
  rw [inv_div]
  gcongr

/-- `P(G,k) ≤ P(G,L)`, with a strict inequality as soon as one edge has unequal lists. -/
theorem colConst_le_col_of_certifiedAt {D k : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    (hcert : CertifiedAt D k) {L : ListAssignment V} (hL : IsNListAssignment L k) :
    G.colConst k ≤ G.col L := by
  obtain ⟨q, x₀, e, o, r, hq, hc, hqx, hbudget⟩ := hcert
  have hx : 0 ≤ q⁻¹ := (inv_pos.mpr hq).le
  have hh := partitionSum_endpoints_le (Finset.univ : Finset V)
    (graphActivity G L k q⁻¹)
    (fun S _t => graphActivityDeriv G L k q⁻¹ S)
    (fun t S _ => hasDerivAt_graphActivity G L k _ t S)
    (fun t ht =>
      graphActivity_cert_derivative_sum_nonneg G hdeg hc hL hx hqx hbudget ht Finset.univ)
  rw [partitionSum_graphActivity_eq, partitionSum_graphActivity_eq,
    interpolatedSum_zero, interpolatedSum_one] at hh
  have hqn := pow_pos hq (Finset.univ : Finset V).card
  have hcol : (G.colConst k : ℝ) ≤ (G.col L : ℝ) := (div_le_div_iff_of_pos_right hqn).mp hh
  exact_mod_cast hcol

theorem eccAt_of_certifiedAt {D k : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    (hcert : CertifiedAt D k) : G.ECCAt k :=
  fun _ hL => colConst_le_col_of_certifiedAt G hdeg hcert hL

/-- An edge whose lists differ keeps the derivative strictly positive, because the charge
consumes only a fraction `2eo < 1` of that edge's own term. -/
theorem colConst_lt_col_of_certifiedAt {D k : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    (hcert : CertifiedAt D k) {L : ListAssignment V} (hL : IsNListAssignment L k)
    {f : Sym2 V} (hf : f ∈ G.edgeFinset) (hd : 0 < edgeDef L k f) :
    G.colConst k < G.col L := by
  classical
  obtain ⟨q, x₀, e, o, r, hq, hc, hqx, hbudget⟩ := hcert
  have hx : 0 < q⁻¹ := inv_pos.mpr hq
  have hh := partitionSum_endpoints_lt (Finset.univ : Finset V)
    (graphActivity G L k q⁻¹)
    (fun S _t => graphActivityDeriv G L k q⁻¹ S)
    (fun t S _ => hasDerivAt_graphActivity G L k _ t S) ?_
  · rw [partitionSum_graphActivity_eq, partitionSum_graphActivity_eq,
      interpolatedSum_zero, interpolatedSum_one] at hh
    have hqn := pow_pos hq (Finset.univ : Finset V).card
    have hcol : (G.colConst k : ℝ) < (G.col L : ℝ) := (div_lt_div_iff_of_pos_right hqn).mp hh
    exact_mod_cast hcol
  intro t ht
  have hp := graphActivity_cert_positive_mono G hdeg hc hL hx.le hqx hbudget ht
  have hfU : f ∈ edgesWithin G.edgeFinset Finset.univ :=
    mem_edgesWithin.mpr ⟨hf, fun _ _ => Finset.mem_univ _⟩
  have hd' : (0 : ℝ) < edgeDef L k f := by exact_mod_cast hd
  have hs : 0 < ∑ f ∈ edgesWithin G.edgeFinset Finset.univ,
      (edgeDef L k f : ℝ) * q⁻¹ ^ 2 *
        partitionSum (fun T => graphActivity G L k q⁻¹ T t) (Finset.univ \ f.toFinset) := by
    apply Finset.sum_pos'
    · intro g _
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (hp _).1.le
    · exact ⟨f, hfU, mul_pos (mul_pos hd' (pow_pos hx 2)) (hp _).1⟩
  exact lt_of_lt_of_le (mul_pos (by linarith [hc.edge]) hs)
    (graphActivity_cert_derivative_sum_lower_bound G hdeg hc hL hx.le hqx hbudget ht _)

/-- Adjacent vertices with different lists force strictly more list colourings. -/
theorem colConst_lt_col_of_certifiedAt_of_adj {D k : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    (hcert : CertifiedAt D k) {L : ListAssignment V} (hL : IsNListAssignment L k)
    {u v : V} (huv : G.Adj u v) (hne : L u ≠ L v) : G.colConst k < G.col L := by
  have hlt : (L u ∩ L v).card < k := by
    by_contra h
    have hle : k ≤ (L u ∩ L v).card := by omega
    have hu : L u ∩ L v = L u := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [hL u]; exact hle)
    have hv : L u ∩ L v = L v := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      (by rw [hL v]; exact hle)
    exact hne (hu.symm.trans hv)
  exact colConst_lt_col_of_certifiedAt G hdeg hcert hL (f := s(u, v))
    (G.mem_edgeFinset.mpr huv) (by simpa only [edgeDef_mk] using Nat.sub_pos_of_lt hlt)

/-- On a connected graph, the constant assignments are exactly the minimizers. -/
theorem col_eq_colConst_iff_of_certifiedAt {D k : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    (hcert : CertifiedAt D k) (hG : G.Connected) {L : ListAssignment V}
    (hL : IsNListAssignment L k) :
    G.col L = G.colConst k ↔ ∃ s : Finset ℕ, ∀ v, L v = s := by
  constructor
  · intro heq
    have hedge : ∀ u v, G.Adj u v → L u = L v := by
      intro u v huv
      by_contra hne
      have hlt := colConst_lt_col_of_certifiedAt_of_adj G hdeg hcert hL huv hne
      omega
    obtain ⟨r⟩ := hG.nonempty
    refine ⟨L r, fun v => ?_⟩
    obtain ⟨p⟩ := hG.preconnected v r
    induction p with
    | nil => rfl
    | cons hadj _ ih => exact (hedge _ _ hadj).trans ih
  · rintro ⟨s, hs⟩
    obtain ⟨r⟩ := hG.nonempty
    have hcard : s.card = k := by rw [← hs r]; exact hL r
    have heq : L = fun _ => s := funext hs
    rw [heq]
    exact col_const_eq_colConst hcard

/-- The scaled form every concrete threshold uses. -/
theorem eccAt_of_parityCert {D k₀ : ℕ} (hdeg : ∀ v, G.degree v ≤ D)
    {s e o r : ℝ} (hc : ParityCert D (s / k₀) e o r) (hs : 0 < s) (hsr : s * r ≤ s - 1)
    (hk₀ : 0 < k₀) {k : ℕ} (hk : k₀ ≤ k) : G.ECCAt k :=
  eccAt_of_certifiedAt G hdeg (certifiedAt_of_parityCert hc hs hsr hk₀ hk)

end GridGen.Polymer
