/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Finite constraint systems, fibres, and the chain bound

A *constraint system* on a finite vertex type `X` gives each vertex a finite domain `D x ⊆ ℕ`, an
adjacency `adj`, and for adjacent vertices a conflict relation `conf x y a b` ("colour `a` at `x`
clashes with colour `b` at `y`"). Its solutions `Ω` are the assignments that respect the domains
and avoid every conflict on every edge. DP-colourings of a cover are the case where every
`conf x y a ·` has at most one solution.

For a set `U` of vertices and an assignment `g`, the *fibre* `cls U g` is the set of solutions
that agree with `g` off `U`. Counting inequalities that hold in every fibre hold for `Ω`
(`fibre_sum_le`, `fibre_sum_ge`). Two fibre estimates are proved here.

* **Chain lower bound** (`chainProd_le_card_cls`). Colour a duplicate-free list of vertices one
  at a time. The vertex `c i` keeps at least `|D (c i)|` minus the number of its neighbours that
  are not later in the list, provided each neighbour excludes at most one colour (`Match`).
* **Prescribed values** (`card_cls_prescribed_le_one`). Inside one fibre over `U`, at most one
  solution takes prescribed single values on `U`.

Together they give `card_prescribed_mul_le`: prescribing the values on a chain costs a factor of
at least the chain product. This is the counting form of "the probability that a given chain
carries given colours is at most `Π 1/(k − 4 + later_i)`".

Nothing here is decidable. Everything is `noncomputable` and classical.
-/

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace GridGen.Gauge

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A finite constraint system. -/
structure CSP (X : Type*) where
  /-- The adjacency. -/
  adj : X → X → Prop
  /-- The domains. -/
  D : X → Finset ℕ
  /-- `conf x y a b`: colour `a` at `x` conflicts with colour `b` at the neighbour `y`. -/
  conf : X → X → ℕ → ℕ → Prop

namespace CSP

variable (C : CSP X)

/-- A solution: domains respected, no edge in conflict. -/
def Valid (f : X → ℕ) : Prop :=
  (∀ x, f x ∈ C.D x) ∧ ∀ x y, C.adj x y → ¬ C.conf x y (f x) (f y)

/-- The solutions. -/
noncomputable def Ω : Finset (X → ℕ) :=
  (Fintype.piFinset C.D).filter C.Valid

theorem mem_Ω {f : X → ℕ} : f ∈ C.Ω ↔ C.Valid f := by
  classical
  unfold Ω
  simp only [mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- `g` is a solution away from `U`: domains off `U`, and no conflict on an edge with both ends
off `U`. -/
def ValidOff (U : Finset X) (g : X → ℕ) : Prop :=
  (∀ x, x ∉ U → g x ∈ C.D x) ∧
    ∀ x y, x ∉ U → y ∉ U → C.adj x y → ¬ C.conf x y (g x) (g y)

theorem validOff_of_valid {U : Finset X} {g : X → ℕ} (h : C.Valid g) : C.ValidOff U g :=
  ⟨fun x _ => h.1 x, fun x y _ _ hxy => h.2 x y hxy⟩

theorem valid_of_validOff_empty {g : X → ℕ} (h : C.ValidOff ∅ g) : C.Valid g :=
  ⟨fun x => h.1 x (Finset.notMem_empty x),
    fun x y hxy => h.2 x y (Finset.notMem_empty x) (Finset.notMem_empty y) hxy⟩

/-- The fibre over `U` through `g`: the solutions agreeing with `g` off `U`. -/
noncomputable def cls (U : Finset X) (g : X → ℕ) : Finset (X → ℕ) :=
  C.Ω.filter (fun f => ∀ x, x ∉ U → f x = g x)

theorem mem_cls {U : Finset X} {g f : X → ℕ} :
    f ∈ C.cls U g ↔ C.Valid f ∧ ∀ x, x ∉ U → f x = g x := by
  classical
  unfold cls
  rw [mem_filter, mem_Ω]

/-! ### Summing over fibres -/

/-- The restriction to the complement of `U`, as a total function (zero on `U`). -/
def restr (U : Finset X) (f : X → ℕ) : X → ℕ := fun x => if x ∈ U then 0 else f x

theorem restr_eq_iff {U : Finset X} {f g : X → ℕ} :
    restr U f = restr U g ↔ ∀ x, x ∉ U → f x = g x := by
  constructor
  · intro h x hx
    have := congrFun h x
    simpa [restr, hx] using this
  · intro h
    funext x
    by_cases hx : x ∈ U
    · simp [restr, hx]
    · simp [restr, hx, h x hx]

theorem cls_eq_filter (U : Finset X) (g : X → ℕ) :
    C.cls U g = C.Ω.filter (fun f => restr U f = restr U g) := by
  classical
  ext f
  simp only [cls, mem_filter, restr_eq_iff]

/-- **Fibre sums, upper form.** If in every fibre over `U` the predicate `Q` is rarer by the
factor `c`, it is rarer by `c` in `Ω`. -/
theorem fibre_sum_le (U : Finset X) (Q : (X → ℕ) → Prop) [DecidablePred Q] (c : ℕ)
    (h : ∀ g ∈ C.Ω, ((C.cls U g).filter Q).card * c ≤ (C.cls U g).card) :
    (C.Ω.filter Q).card * c ≤ C.Ω.card := by
  classical
  set T := C.Ω.image (restr U)
  have hΩ : C.Ω.card = ∑ ω ∈ T, (C.Ω.filter (fun f => restr U f = ω)).card :=
    card_eq_sum_card_fiberwise (fun f hf => mem_image_of_mem _ hf)
  have hQ : (C.Ω.filter Q).card = ∑ ω ∈ T, ((C.Ω.filter Q).filter (fun f => restr U f = ω)).card :=
    card_eq_sum_card_fiberwise (fun f hf => mem_image_of_mem _ (mem_filter.mp hf).1)
  rw [hΩ, hQ, sum_mul]
  refine sum_le_sum fun ω hω => ?_
  obtain ⟨g, hg, rfl⟩ := mem_image.mp hω
  have h1 := h g hg
  rw [cls_eq_filter] at h1
  have he : (C.Ω.filter Q).filter (fun f => restr U f = restr U g)
      = (C.Ω.filter (fun f => restr U f = restr U g)).filter Q := by
    ext f; simp only [mem_filter]; tauto
  rw [he]
  convert h1 using 3

/-- **Fibre sums, lower form.** If in every fibre the predicate `Q` has density at least `a/b`,
it has density at least `a/b` in `Ω`. -/
theorem fibre_sum_ge (U : Finset X) (Q : (X → ℕ) → Prop) [DecidablePred Q] (a b : ℕ)
    (h : ∀ g ∈ C.Ω, (C.cls U g).card * a ≤ ((C.cls U g).filter Q).card * b) :
    C.Ω.card * a ≤ (C.Ω.filter Q).card * b := by
  classical
  set T := C.Ω.image (restr U)
  have hΩ : C.Ω.card = ∑ ω ∈ T, (C.Ω.filter (fun f => restr U f = ω)).card :=
    card_eq_sum_card_fiberwise (fun f hf => mem_image_of_mem _ hf)
  have hQ : (C.Ω.filter Q).card = ∑ ω ∈ T, ((C.Ω.filter Q).filter (fun f => restr U f = ω)).card :=
    card_eq_sum_card_fiberwise (fun f hf => mem_image_of_mem _ (mem_filter.mp hf).1)
  rw [hΩ, hQ, sum_mul, sum_mul]
  refine sum_le_sum fun ω hω => ?_
  obtain ⟨g, hg, rfl⟩ := mem_image.mp hω
  have h1 := h g hg
  rw [cls_eq_filter] at h1
  have he : (C.Ω.filter Q).filter (fun f => restr U f = restr U g)
      = (C.Ω.filter (fun f => restr U f = restr U g)).filter Q := by
    ext f; simp only [mem_filter]; tauto
  rw [he]
  convert h1 using 3

/-! ### Membership in a fibre -/

/-- The colours available at `u` given `g` on the vertices off `U`. -/
noncomputable def avail (U : Finset X) (g : X → ℕ) (u : X) : Finset ℕ :=
  (C.D u).filter (fun a => ∀ y, y ∉ U →
    (C.adj u y → ¬ C.conf u y a (g y)) ∧ (C.adj y u → ¬ C.conf y u (g y) a))

theorem mem_avail {U : Finset X} {g : X → ℕ} {u : X} {a : ℕ} :
    a ∈ C.avail U g u ↔ a ∈ C.D u ∧ ∀ y, y ∉ U →
      (C.adj u y → ¬ C.conf u y a (g y)) ∧ (C.adj y u → ¬ C.conf y u (g y) a) := by
  classical
  unfold avail
  rw [mem_filter]

/-- A solution in the fibre takes available values on `U`. -/
theorem mem_avail_of_mem_cls {U : Finset X} {g f : X → ℕ} (hf : f ∈ C.cls U g) {u : X}
    (_hu : u ∈ U) : f u ∈ C.avail U g u := by
  rw [mem_cls] at hf
  rw [mem_avail]
  refine ⟨hf.1.1 u, fun y hy => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [← hf.2 y hy]; exact hf.1.2 u y h
  · rw [← hf.2 y hy]; exact hf.1.2 y u h

/-- **The fibre, described.** An assignment that agrees with `g` off `U`, takes available
values on `U` and has no conflict inside `U` is a solution (when `g` is valid off `U`). -/
theorem mem_cls_of {U : Finset X} {g f : X → ℕ} (hg : C.ValidOff U g)
    (hoff : ∀ x, x ∉ U → f x = g x) (hon : ∀ u, u ∈ U → f u ∈ C.avail U g u)
    (hin : ∀ u u', u ∈ U → u' ∈ U → C.adj u u' → ¬ C.conf u u' (f u) (f u')) :
    f ∈ C.cls U g := by
  rw [mem_cls]
  refine ⟨⟨fun x => ?_, fun x y hxy => ?_⟩, hoff⟩
  · by_cases hx : x ∈ U
    · exact (C.mem_avail.mp (hon x hx)).1
    · rw [hoff x hx]; exact hg.1 x hx
  · by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
    · exact hin x y hx hy hxy
    · rw [hoff y hy]; exact ((C.mem_avail.mp (hon x hx)).2 y hy).1 hxy
    · rw [hoff x hx]; exact ((C.mem_avail.mp (hon y hy)).2 x hx).2 hxy
    · rw [hoff x hx, hoff y hy]; exact hg.2 x y hx hy hxy

/-! ### The chain bound -/

/-- The neighbours (either direction) of `x`. -/
noncomputable def nbrs (x : X) : Finset X :=
  Finset.univ.filter (fun y => C.adj x y ∨ C.adj y x)

theorem mem_nbrs {x y : X} : y ∈ C.nbrs x ↔ C.adj x y ∨ C.adj y x := by
  classical
  unfold nbrs
  simp

/-- The neighbours of `x` that are not in `S`. -/
noncomputable def nbrsOut (x : X) (S : Finset X) : Finset X :=
  (C.nbrs x).filter (fun y => y ∉ S)

/-- The chain product: vertex by vertex, the domain size less the neighbours not later in the
list. -/
noncomputable def chainProd : List X → ℕ
  | [] => 1
  | x :: rest => ((C.D x).card - (C.nbrsOut x rest.toFinset).card) * chainProd rest

/-- Every neighbour excludes at most one colour (DP-cover condition). -/
def Match : Prop :=
  ∀ x y b, b ∈ C.D y → ∀ a a', a ∈ C.D x → a' ∈ C.D x →
    (C.conf x y a b ∨ C.conf y x b a) → (C.conf x y a' b ∨ C.conf y x b a') → a = a'

/-- No vertex is its own neighbour. -/
def Irrefl : Prop := ∀ x, ¬ C.adj x x

/-- The values left at `x` by the neighbours off `S`, under `g`. -/
noncomputable def good (S : Finset X) (g : X → ℕ) (x : X) : Finset ℕ :=
  (C.D x).filter (fun a => ∀ y, y ∉ S → y ≠ x →
    (C.adj x y → ¬ C.conf x y a (g y)) ∧ (C.adj y x → ¬ C.conf y x (g y) a))

theorem mem_good {S : Finset X} {g : X → ℕ} {x : X} {a : ℕ} :
    a ∈ C.good S g x ↔ a ∈ C.D x ∧ ∀ y, y ∉ S → y ≠ x →
      (C.adj x y → ¬ C.conf x y a (g y)) ∧ (C.adj y x → ¬ C.conf y x (g y) a) := by
  unfold good; rw [mem_filter]

/-- Each neighbour off `S` removes at most one colour. -/
theorem card_good_ge (hM : C.Match) (hI : C.Irrefl) (S : Finset X) (g : X → ℕ) (x : X)
    (hg : ∀ y, y ∉ S → y ≠ x → g y ∈ C.D y) :
    (C.D x).card - (C.nbrsOut x S).card ≤ (C.good S g x).card := by
  set B := (C.nbrsOut x S).biUnion (fun y => (C.D x).filter (fun a =>
    C.conf x y a (g y) ∨ C.conf y x (g y) a)) with hBdef
  have hB : B.card ≤ (C.nbrsOut x S).card := by
    refine le_trans card_biUnion_le ?_
    calc ∑ y ∈ C.nbrsOut x S, ((C.D x).filter (fun a =>
            C.conf x y a (g y) ∨ C.conf y x (g y) a)).card
          ≤ ∑ _y ∈ C.nbrsOut x S, 1 := by
          refine sum_le_sum fun y hy => ?_
          unfold nbrsOut at hy
          rw [mem_filter, mem_nbrs] at hy
          have hyx : y ≠ x := by
            rintro rfl
            rcases hy.1 with h | h <;> exact hI _ h
          refine card_le_one.mpr fun a ha a' ha' => ?_
          rw [mem_filter] at ha ha'
          exact hM x y (g y) (hg y hy.2 hyx) a a' ha.1 ha'.1 ha.2 ha'.2
      _ = _ := by simp
  have hsub : C.D x \ B ⊆ C.good S g x := by
    intro a ha
    rw [mem_sdiff] at ha
    rw [mem_good]
    refine ⟨ha.1, fun y hy hyx => ?_⟩
    have hnot : ¬ (C.conf x y a (g y) ∨ C.conf y x (g y) a) → (C.adj x y → ¬ C.conf x y a (g y)) ∧
        (C.adj y x → ¬ C.conf y x (g y) a) := fun h => ⟨fun _ h' => h (Or.inl h'),
          fun _ h' => h (Or.inr h')⟩
    by_cases hadj : C.adj x y ∨ C.adj y x
    · refine hnot fun hc => ha.2 ?_
      rw [hBdef, mem_biUnion]
      refine ⟨y, ?_, mem_filter.mpr ⟨ha.1, hc⟩⟩
      unfold nbrsOut
      rw [mem_filter, mem_nbrs]
      exact ⟨hadj, hy⟩
    · exact ⟨fun h => absurd (Or.inl h) hadj, fun h => absurd (Or.inr h) hadj⟩
  calc (C.D x).card - (C.nbrsOut x S).card ≤ (C.D x).card - B.card := Nat.sub_le_sub_left hB _
    _ ≤ (C.D x \ B).card := le_card_sdiff _ _
    _ ≤ _ := card_le_card hsub

/-- **The chain lower bound.** A fibre over the vertices of a duplicate-free list has at least
the chain product of solutions. -/
theorem chainProd_le_card_cls (hM : C.Match) (hI : C.Irrefl) :
    ∀ (c : List X) (g : X → ℕ), c.Nodup → C.ValidOff c.toFinset g →
      C.chainProd c ≤ (C.cls c.toFinset g).card := by
  intro c
  induction c with
  | nil =>
      intro g _ hg
      have hv : C.Valid g := C.valid_of_validOff_empty (by simpa using hg)
      have : g ∈ C.cls ([] : List X).toFinset g := by
        rw [mem_cls]; exact ⟨hv, fun _ _ => rfl⟩
      simpa [chainProd] using card_pos.mpr ⟨g, this⟩
  | cons x rest ih =>
      intro g hnd hg
      rw [List.nodup_cons] at hnd
      have hxr : x ∉ rest.toFinset := by simpa using hnd.1
      have hU : (x :: rest).toFinset = insert x rest.toFinset := by simp
      rw [hU] at hg ⊢
      -- each available colour at `x` opens a disjoint subfibre
      have hval : ∀ a ∈ C.good rest.toFinset g x,
          C.ValidOff rest.toFinset (Function.update g x a) := by
        intro a ha
        rw [mem_good] at ha
        refine ⟨fun y hy => ?_, fun y z hy hz hyz => ?_⟩
        · by_cases hyx : y = x
          · subst hyx; simpa using ha.1
          · rw [Function.update_of_ne hyx]
            exact hg.1 y (by simp [hy, hyx])
        · by_cases hyx : y = x <;> by_cases hzx : z = x
          · subst hyx; subst hzx; exact absurd hyz (hI _)
          · subst hyx
            rw [Function.update_self, Function.update_of_ne hzx]
            exact (ha.2 z hz hzx).1 hyz
          · subst hzx
            rw [Function.update_self, Function.update_of_ne hyx]
            exact (ha.2 y hy hyx).2 hyz
          · rw [Function.update_of_ne hyx, Function.update_of_ne hzx]
            exact hg.2 y z (by simp [hy, hyx]) (by simp [hz, hzx]) hyz
      have hsub : (C.good rest.toFinset g x).biUnion
          (fun a => C.cls rest.toFinset (Function.update g x a))
            ⊆ C.cls (insert x rest.toFinset) g := by
        intro f hf
        rw [mem_biUnion] at hf
        obtain ⟨a, _, hf⟩ := hf
        rw [mem_cls] at hf ⊢
        refine ⟨hf.1, fun y hy => ?_⟩
        have hyx : y ≠ x := fun h => hy (by simp [h])
        rw [hf.2 y (fun h => hy (mem_insert_of_mem h)), Function.update_of_ne hyx]
      have hdisj : (C.good rest.toFinset g x : Set ℕ).PairwiseDisjoint
          (fun a => C.cls rest.toFinset (Function.update g x a)) := by
        intro a _ b _ hab
        refine Finset.disjoint_left.mpr fun f hfa hfb => hab ?_
        rw [mem_cls] at hfa hfb
        have h1 := hfa.2 x hxr
        have h2 := hfb.2 x hxr
        rw [Function.update_self] at h1 h2
        rw [← h1, ← h2]
      have hcard := card_le_card hsub
      rw [card_biUnion hdisj] at hcard
      have hgx : ∀ y, y ∉ rest.toFinset → y ≠ x → g y ∈ C.D y :=
        fun y hy hyx => hg.1 y (by simp [hy, hyx])
      calc C.chainProd (x :: rest)
          = ((C.D x).card - (C.nbrsOut x rest.toFinset).card) * C.chainProd rest := rfl
        _ ≤ (C.good rest.toFinset g x).card * C.chainProd rest :=
            Nat.mul_le_mul_right _ (C.card_good_ge hM hI _ g x hgx)
        _ = ∑ _a ∈ C.good rest.toFinset g x, C.chainProd rest := by rw [sum_const, smul_eq_mul]
        _ ≤ ∑ a ∈ C.good rest.toFinset g x,
              (C.cls rest.toFinset (Function.update g x a)).card :=
            sum_le_sum fun a ha => ih _ hnd.2 (hval a ha)
        _ ≤ _ := hcard

/-- **Prescribed values.** In a fibre over `U`, at most one solution takes prescribed values from
sets of size at most one on `U`. -/
theorem card_cls_prescribed_le_one (U : Finset X) (g : X → ℕ) (S : X → Finset ℕ)
    (hS : ∀ x ∈ U, (S x).card ≤ 1) :
    ((C.cls U g).filter (fun f => ∀ x ∈ U, f x ∈ S x)).card ≤ 1 := by
  refine card_le_one.mpr fun f hf f' hf' => ?_
  rw [mem_filter, mem_cls] at hf hf'
  funext x
  by_cases hx : x ∈ U
  · exact card_le_one.mp (hS x hx) _ (hf.2 x hx) _ (hf'.2 x hx)
  · rw [hf.1.2 x hx, hf'.1.2 x hx]

/-- **The chain bound.** Prescribing the values on a chain (sets of size at most one) costs at
least the chain product. -/
theorem card_prescribed_mul_le (hM : C.Match) (hI : C.Irrefl) (c : List X) (hc : c.Nodup)
    (S : X → Finset ℕ) (hS : ∀ x ∈ c, (S x).card ≤ 1) :
    (C.Ω.filter (fun f => ∀ x ∈ c, f x ∈ S x)).card * C.chainProd c ≤ C.Ω.card := by
  have hQ : C.Ω.filter (fun f : X → ℕ => ∀ x ∈ c, f x ∈ S x)
      = C.Ω.filter (fun f => ∀ x ∈ c.toFinset, f x ∈ S x) := by
    ext f; simp
  rw [hQ]
  refine C.fibre_sum_le c.toFinset _ _ fun g hg => ?_
  have h1 := C.card_cls_prescribed_le_one c.toFinset g S (fun x hx => hS x (by simpa using hx))
  have h2 := C.chainProd_le_card_cls hM hI c g hc (C.validOff_of_valid ((C.mem_Ω).mp hg))
  calc _ ≤ 1 * C.chainProd c := Nat.mul_le_mul_right _ h1
    _ ≤ _ := by rw [one_mul]; exact h2

/-- On a vertex of `U`, the available colours are the colours left by the neighbours off `U`. -/
theorem avail_eq_good {U : Finset X} {g : X → ℕ} {u : X} (hu : u ∈ U) :
    C.avail U g u = C.good U g u := by
  ext a
  rw [mem_avail, mem_good]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun y hy _ => h2 y hy⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun y hy => h2 y hy (fun h => hy (h ▸ hu))⟩

/-- **Available colours.** Each neighbour off `U` removes at most one colour. -/
theorem card_avail_ge (hM : C.Match) (hI : C.Irrefl) {U : Finset X} {g : X → ℕ} {u : X}
    (hu : u ∈ U) (hg : ∀ y, y ∉ U → g y ∈ C.D y) :
    (C.D u).card - (C.nbrsOut u U).card ≤ (C.avail U g u).card := by
  rw [C.avail_eq_good hu]
  exact C.card_good_ge hM hI U g u fun y hy _ => hg y hy

theorem mem_nbrsOut {x y : X} {S : Finset X} :
    y ∈ C.nbrsOut x S ↔ (C.adj x y ∨ C.adj y x) ∧ y ∉ S := by
  unfold nbrsOut; rw [mem_filter, mem_nbrs]

end CSP

end GridGen.Gauge
