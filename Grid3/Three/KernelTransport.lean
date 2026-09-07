import Mathlib

/-!
# Transport of a finite seam along two independent injections

The left and right canonical colour labels need not be sent to actual colours by the same
map. After maximal extension, only the respective column laws and the implication from
canonical compatibility to actual compatibility must be preserved.

`liftLaw` extends a law by zero along an injection. `liftKernel` extends each target row by
zero and supplies an arbitrary stochastic fallback outside the source image. The fallback
is invisible to the joint law and its entropy. No certificate arithmetic is repeated.

This lemma does not construct the pattern-respecting injections: that remains a separate
combinatorial obligation. It permits different finite source/target types and different
injections on the two sides of a seam.
-/

namespace Grid3.Three.Transport

open Finset Function

variable {A B S T : Type*} [Fintype A] [Fintype B] [Fintype S] [Fintype T]

noncomputable def liftLaw (f : A → S) (law : A → ℝ) : S → ℝ :=
  Function.extend f law (fun _ => 0)

omit [Fintype A] [Fintype S] in
theorem liftLaw_apply (f : A → S) (hf : Injective f) (law : A → ℝ) (a : A) :
    liftLaw f law (f a) = law a := hf.extend_apply law (fun _ => 0) a

omit [Fintype A] [Fintype S] in
theorem liftLaw_off (f : A → S) (law : A → ℝ) (s : S) (hs : s ∉ Set.range f) :
    liftLaw f law s = 0 := Function.extend_apply' law (fun _ => 0) s hs

omit [Fintype A] [Fintype S] in
theorem liftLaw_nonneg (f : A → S) (hf : Injective f) (law : A → ℝ)
    (hlaw : ∀ a, 0 ≤ law a) (s : S) : 0 ≤ liftLaw f law s := by
  by_cases hs : s ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hs
    rw [liftLaw_apply f hf]; exact hlaw a
  · rw [liftLaw_off f law s hs]

/-- Any zero-preserving statistic sums over the small source type, not the padded type. -/
theorem sum_liftLaw_map (f : A → S) (hf : Injective f) (law : A → ℝ)
    (φ : ℝ → ℝ) (hφ : φ 0 = 0) :
    ∑ s, φ (liftLaw f law s) = ∑ a, φ (law a) := by
  symm
  apply Fintype.sum_of_injective f hf
  · intro s hs; rw [liftLaw_off f law s hs, hφ]
  · intro a; rw [liftLaw_apply f hf]

theorem sum_liftLaw (f : A → S) (hf : Injective f) (law : A → ℝ) :
    ∑ s, liftLaw f law s = ∑ a, law a := sum_liftLaw_map f hf law id rfl

theorem sum_liftLaw_mul (f : A → S) (hf : Injective f) (law : A → ℝ) (g : S → ℝ) :
    ∑ s, liftLaw f law s * g s = ∑ a, law a * g (f a) := by
  symm
  apply Fintype.sum_of_injective f hf
  · intro s hs; rw [liftLaw_off f law s hs, zero_mul]
  · intro a; rw [liftLaw_apply f hf]

theorem entropy_liftLaw (f : A → S) (hf : Injective f) (law : A → ℝ) :
    ∑ s, Real.negMulLog (liftLaw f law s) = ∑ a, Real.negMulLog (law a) :=
  sum_liftLaw_map f hf law Real.negMulLog Real.negMulLog_zero

noncomputable def liftKernel (f : A → S) (g : B → T) (K : A → B → ℝ)
    (fallback : T → ℝ) : S → T → ℝ :=
  Function.extend f (fun a => liftLaw g (K a)) (fun _ => fallback)

omit [Fintype A] [Fintype B] [Fintype S] [Fintype T] in
theorem liftKernel_row (f : A → S) (hf : Injective f) (g : B → T)
    (K : A → B → ℝ) (fallback : T → ℝ) (a : A) :
    liftKernel f g K fallback (f a) = liftLaw g (K a) :=
  hf.extend_apply (fun a => liftLaw g (K a)) (fun _ => fallback) a

omit [Fintype A] [Fintype B] [Fintype S] [Fintype T] in
theorem liftKernel_apply (f : A → S) (hf : Injective f) (g : B → T) (hg : Injective g)
    (K : A → B → ℝ) (fallback : T → ℝ) (a : A) (b : B) :
    liftKernel f g K fallback (f a) (g b) = K a b := by
  rw [liftKernel_row f hf, liftLaw_apply g hg]

omit [Fintype A] [Fintype B] [Fintype S] [Fintype T] in
theorem liftKernel_off (f : A → S) (g : B → T) (K : A → B → ℝ)
    (fallback : T → ℝ) (s : S) (hs : s ∉ Set.range f) :
    liftKernel f g K fallback s = fallback :=
  Function.extend_apply' (fun a => liftLaw g (K a)) (fun _ => fallback) s hs

omit [Fintype A] [Fintype B] [Fintype S] [Fintype T] in
theorem liftKernel_nonneg (f : A → S) (hf : Injective f) (g : B → T) (hg : Injective g)
    (K : A → B → ℝ) (fallback : T → ℝ)
    (hK : ∀ a b, 0 ≤ K a b) (hfall : ∀ t, 0 ≤ fallback t) (s : S) (t : T) :
    0 ≤ liftKernel f g K fallback s t := by
  by_cases hs : s ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hs
    rw [liftKernel_row f hf]; exact liftLaw_nonneg g hg (K a) (hK a) t
  · rw [liftKernel_off f g K fallback s hs]; exact hfall t

omit [Fintype S] in
theorem liftKernel_rowsum (f : A → S) (hf : Injective f) (g : B → T) (hg : Injective g)
    (K : A → B → ℝ) (fallback : T → ℝ)
    (hK : ∀ a, ∑ b, K a b = 1) (hfall : ∑ t, fallback t = 1) (s : S) :
    ∑ t, liftKernel f g K fallback s t = 1 := by
  by_cases hs : s ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hs
    simp_rw [liftKernel_row f hf]
    rw [sum_liftLaw g hg]; exact hK a
  · simp_rw [liftKernel_off f g K fallback s hs]; exact hfall

omit [Fintype T] in
/-- The transported column laws are still exactly the marginals of the transported kernel. -/
theorem liftKernel_step (f : A → S) (hf : Injective f) (g : B → T) (hg : Injective g)
    (left : A → ℝ) (right : B → ℝ) (K : A → B → ℝ) (fallback : T → ℝ)
    (hstep : ∀ b, ∑ a, left a * K a b = right b) (t : T) :
    ∑ s, liftLaw f left s * liftKernel f g K fallback s t = liftLaw g right t := by
  rw [sum_liftLaw_mul f hf]
  by_cases ht : t ∈ Set.range g
  · obtain ⟨b, rfl⟩ := ht
    simp_rw [liftKernel_apply f hf g hg, liftLaw_apply g hg]
    exact hstep b
  · simp_rw [liftKernel_row f hf, liftLaw_off g _ t ht, mul_zero, Finset.sum_const_zero]

/-- Every zero-preserving row statistic, including collision and Shannon entropy, transports
exactly. This also avoids summing over padded states in subsequent analytic proofs. -/
theorem liftKernel_statistic (f : A → S) (hf : Injective f) (g : B → T) (hg : Injective g)
    (left : A → ℝ) (K : A → B → ℝ) (fallback : T → ℝ)
    (φ : ℝ → ℝ) (hφ : φ 0 = 0) :
    (∑ s, liftLaw f left s * ∑ t, φ (liftKernel f g K fallback s t))
      = ∑ a, left a * ∑ b, φ (K a b) := by
  rw [sum_liftLaw_mul f hf]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [liftKernel_row f hf]
  rw [sum_liftLaw_map g hg (K a) φ hφ]

theorem liftKernel_entropy (f : A → S) (hf : Injective f) (g : B → T) (hg : Injective g)
    (left : A → ℝ) (K : A → B → ℝ) (fallback : T → ℝ) :
    (∑ s, liftLaw f left s * ∑ t,
      liftKernel f g K fallback s t * (-Real.log (liftKernel f g K fallback s t)))
      = ∑ a, left a * ∑ b, K a b * (-Real.log (K a b)) :=
  liftKernel_statistic f hf g hg left K fallback (fun x => x * (-Real.log x)) (by simp)

omit [Fintype A] [Fintype B] [Fintype S] [Fintype T] in
/-- Only compatibility on positive-mass canonical transitions needs to be transported. -/
theorem liftKernel_support (f : A → S) (hf : Injective f) (g : B → T) (hg : Injective g)
    (left : A → ℝ) (K : A → B → ℝ) (fallback : T → ℝ) (R : S → T → Prop)
    (hsupp : ∀ a b, 0 < left a → 0 < K a b → R (f a) (g b))
    (s : S) (t : T) (hs : 0 < liftLaw f left s)
    (hK : 0 < liftKernel f g K fallback s t) : R s t := by
  have hsf : s ∈ Set.range f := by
    by_contra h
    rw [liftLaw_off f left s h] at hs
    exact (lt_irrefl 0) hs
  obtain ⟨a, rfl⟩ := hsf
  rw [liftLaw_apply f hf] at hs
  rw [liftKernel_row f hf] at hK
  have htg : t ∈ Set.range g := by
    by_contra h
    rw [liftLaw_off g (K a) t h] at hK
    exact (lt_irrefl 0) hK
  obtain ⟨b, rfl⟩ := htg
  rw [liftLaw_apply g hg] at hK
  exact hsupp a b hs hK

end Grid3.Three.Transport
