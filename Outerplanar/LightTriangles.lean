/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.SixEvenBuild

/-!
# Light triangles: any number of even faces

**`ecc_three_of_lightTriangles`**: a polygon dissection in which every triangular face has at
most two even faces outside its heaviest branch is 3-ECC, whatever the number of even faces
(Claude's extension of the six-even-face theorem, research note
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`, "Extension: arbitrarily many even faces",
Corollary 2).

The three *branches* of a triangle are the parts of the polygon beyond its three sides; `br G u v`
counts the even faces in the arc from `u` up to `v`, the branch beyond the side `(u, v)`. The
count is invariant under rotations, so the condition `LightTriangles` is too.

The proof builds the graph by ears (`exists_build`) with the tags of the six-even-face theorem on
intervals with at most two even faces, the matching bound alone (`tMB`) on intervals without a
heavy triangle (one with three or more even faces inside), and the hexagon bound alone (`tHex`)
elsewhere. This works when no heavy triangle lies inside an even face (`CondL`). The base edge is a
narrowest chord with more than half of the even faces inside, if any: its root face is a centroid,
and then every triangle other than that face has its heaviest branch on the side of the base, so it
is not heavy (`light_le_two`).
-/

namespace Outerplanar

open Finset

variable {n : ℕ}

/-! ### Branches -/

/-- `w` is in the closed arc from `u` up to `v`. -/
def InArc (u v w : Fin n) : Prop := (w - u).val ≤ (v - u).val

open Classical in
/-- The even faces in the arc from `u` up to `v`. -/
noncomputable def br (G : SimpleGraph (Fin n)) (u v : Fin n) : ℕ :=
  (univ.filter fun F : Finset (Fin n) => IsFace G F ∧ Even F.card ∧ ∀ w ∈ F, InArc u v w).card

/-- **Light triangles**: every triangular face has at most two even faces outside its heaviest
branch. -/
def LightTriangles (G : SimpleGraph (Fin n)) : Prop :=
  ∀ x y z : Fin n, IsFace G {x, y, z} → x ≠ y → y ≠ z → x ≠ z →
    CycNext {x, y, z} x y → CycNext {x, y, z} y z → CycNext {x, y, z} z x →
    br G x y + br G y z + br G z x ≤ 2 + max (br G x y) (max (br G y z) (br G z x))

theorem inArc_lt {u v w : Fin n} (huv : u < v) : InArc u v w ↔ u ≤ w ∧ w ≤ v := by
  unfold InArc
  rw [sub_val_le huv.le]
  have hw := w.isLt
  have hv := v.isLt
  by_cases h : u ≤ w
  · rw [sub_val_le h]
    have : u.val ≤ w.val := h
    constructor
    · intro h'; exact ⟨h, by show w.val ≤ v.val; omega⟩
    · rintro ⟨-, h'⟩; have : w.val ≤ v.val := h'; omega
  · rw [sub_val_lt (not_le.mp h)]
    have : w.val < u.val := not_le.mp h
    constructor
    · intro h'; omega
    · rintro ⟨h', -⟩; exact absurd h' h

theorem inArc_gt {x z w : Fin n} (hxz : x < z) : InArc z x w ↔ ¬ (x < w ∧ w < z) :=
  sub_le_iff hxz

section Branches

variable {G : SimpleGraph (Fin n)}

open Classical in
theorem br_lt {u v : Fin n} (huv : u < v) : br G u v = marks G u v := by
  unfold br marks facesIn
  congr 1
  ext F
  simp only [mem_filter, mem_univ, true_and, inArc_lt huv, subset_iff, mem_Icc]
  tauto

open Classical in
/-- The faces off the chord `(a, b)` have no vertex strictly inside it. -/
theorem numEven_split (hG : IsDissection G) {a b : Fin n} (hab : a < b) (hadj : G.Adj a b) :
    numEvenFaces G = marks G a b + br G b a := by
  unfold numEvenFaces br
  set E := univ.filter fun F : Finset (Fin n) => IsFace G F ∧ Even F.card with hE
  have hA : marks G a b = (E.filter fun F => F ⊆ Icc a b).card := by
    unfold marks facesIn
    congr 1
    ext F
    simp only [hE, mem_filter, mem_univ, true_and]
    tauto
  have hout : ∀ F, IsFace G F → (¬ F ⊆ Icc a b ↔ ∀ x ∈ F, ¬ (a < x ∧ x < b)) := by
    intro F hF
    constructor
    · intro h x hx ⟨h1, h2⟩
      exact h fun y hy => mem_Icc.mpr (face_sep hG hF hab hadj hx h1 h2 y hy)
    · intro h hsub
      have := card_le_two_of_gap hsub h
      have := hF.1
      omega
  have hB : (univ.filter fun F : Finset (Fin n) => IsFace G F ∧ Even F.card ∧
      ∀ w ∈ F, InArc b a w) = E.filter fun F => ¬ F ⊆ Icc a b := by
    ext F
    simp only [hE, mem_filter, mem_univ, true_and, inArc_gt hab]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, (hout F h1).mpr h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, (hout F h1).mp h3⟩
  rw [hA, hB, Finset.card_filter_add_card_filter_not]

variable [NeZero n]

theorem inArc_rot (r u v w : Fin n) : InArc (u + r) (v + r) (w + r) ↔ InArc u v w := by
  unfold InArc
  simp only [add_sub_add_right_eq_sub]

open Classical in
/-- Branches are invariant under rotation. -/
theorem br_rot (r u v : Fin n) : br (G.comap (rot r)) u v = br G (u + r) (v + r) := by
  unfold br
  rw [← card_image_of_injective _ (image_injective (rot_injective r))]
  congr 1
  ext F'
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨F, ⟨hF, hev, harc⟩, rfl⟩
    refine ⟨(isFace_rot G r F).mp hF, by rwa [card_image_of_injective _ (rot_injective r)], ?_⟩
    intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_image.mp hw
    exact (inArc_rot r u v w').mpr (harc w' hw')
  · rintro ⟨hF', hev, harc⟩
    refine ⟨F'.image (rot (-r)), ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [isFace_rot, image_image]
      convert hF'
      ext y; simp [rot]
    · rwa [card_image_of_injective _ (rot_injective _)]
    · intro w hw
      obtain ⟨w', hw', rfl⟩ := mem_image.mp hw
      have := harc w' hw'
      rw [← inArc_rot r]
      simpa [rot] using this
    · rw [image_image]
      ext y; simp [rot]

open Classical in
theorem numEvenFaces_rot (r : Fin n) : numEvenFaces (G.comap (rot r)) = numEvenFaces G := by
  unfold numEvenFaces
  rw [← card_image_of_injective _ (image_injective (rot_injective r))]
  congr 1
  ext F'
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨F, ⟨hF, hev⟩, rfl⟩
    exact ⟨(isFace_rot G r F).mp hF, by rwa [card_image_of_injective _ (rot_injective r)]⟩
  · rintro ⟨hF', hev⟩
    refine ⟨F'.image (rot (-r)), ⟨?_, ?_⟩, ?_⟩
    · rw [isFace_rot, image_image]
      convert hF'
      ext y; simp [rot]
    · rwa [card_image_of_injective _ (rot_injective _)]
    · rw [image_image]
      ext y; simp [rot]

/-- **Light triangles are invariant under rotation.** -/
theorem lightTriangles_rot (h : LightTriangles G) (r : Fin n) :
    LightTriangles (G.comap (rot r)) := by
  intro x y z hF hxy hyz hxz h1 h2 h3
  have himg : ({x, y, z} : Finset (Fin n)).image (rot r) = {x + r, y + r, z + r} := by
    simp [image_insert, rot]
  rw [isFace_rot, himg] at hF
  have c1 := (cycNext_rot r {x, y, z} x y).mpr h1
  have c2 := (cycNext_rot r {x, y, z} y z).mpr h2
  have c3 := (cycNext_rot r {x, y, z} z x).mpr h3
  rw [himg] at c1 c2 c3
  simp only [rot] at c1 c2 c3
  rw [br_rot, br_rot, br_rot]
  exact h _ _ _ hF (fun e => hxy (add_right_cancel e)) (fun e => hyz (add_right_cancel e))
    (fun e => hxz (add_right_cancel e)) c1 c2 c3

end Branches

/-! ### A triangle inside at most half of the even faces is not heavy -/

section Light

variable {H : SimpleGraph (Fin n)}

/-- A face in `[a, b]` through `a` and `b` is the root face. -/
theorem face_eq_root (hH : IsDissection H) {a b : Fin n} (hab : a < b) (hadj : H.Adj a b)
    {F : Finset (Fin n)} (hF : F ∈ facesIn H a b) (ha : a ∈ F) (hb : b ∈ F) :
    F = rootFace H a b := by
  have h2 : a.val + 2 ≤ b.val := by
    by_contra h
    rw [facesIn_edge (by omega)] at hF
    simp at hF
  obtain ⟨m, r, he⟩ := exists_rootEnum hH hadj h2
  rcases he.cover hH hadj hab hF with h | ⟨i, hi⟩
  · exact h
  · obtain ⟨-, hsub⟩ := mem_facesIn.mp hi
    obtain ⟨h1, -⟩ := mem_Icc.mp (hsub ha)
    obtain ⟨-, h3⟩ := mem_Icc.mp (hsub hb)
    have e1 : r i.castSucc = a := le_antisymm h1 (he.ge _)
    have e2 : r i.succ = b := le_antisymm (he.le _) h3
    have := he.width i
    rw [e1, e2] at this
    omega

/-- The three vertices of a triangle with given least and greatest vertices. -/
theorem triangle_mid {Δ : Finset (Fin n)} (h3 : Δ.card = 3) {x z : Fin n} (hx : x ∈ Δ)
    (hz : z ∈ Δ) (hext : ∀ w ∈ Δ, x ≤ w ∧ w ≤ z) : ∃ y, x < y ∧ y < z ∧ Δ = {x, y, z} := by
  have hxz : x ≠ z := by
    intro e
    have : Δ ⊆ {x} := fun w hw => by
      rw [mem_singleton]; exact le_antisymm (e ▸ (hext w hw).2) (hext w hw).1
    have := card_le_card this
    simp at this; omega
  have hc : ((Δ.erase x).erase z).card = 1 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hxz, hz⟩), card_erase_of_mem hx, h3]
  obtain ⟨y, hy⟩ := card_eq_one.mp hc
  have hyΔ : y ∈ (Δ.erase x).erase z := by rw [hy]; exact mem_singleton_self y
  obtain ⟨hyz, hy'⟩ := mem_erase.mp hyΔ
  obtain ⟨hyx, hyΔ'⟩ := mem_erase.mp hy'
  refine ⟨y, lt_of_le_of_ne (hext y hyΔ').1 (Ne.symm hyx),
    lt_of_le_of_ne (hext y hyΔ').2 hyz, ?_⟩
  ext w
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hw
    by_cases h1 : w = x
    · exact Or.inl h1
    · by_cases h2 : w = z
      · exact Or.inr (Or.inr h2)
      · have : w ∈ (Δ.erase x).erase z := mem_erase.mpr ⟨h2, mem_erase.mpr ⟨h1, hw⟩⟩
        rw [hy, mem_singleton] at this
        exact Or.inr (Or.inl this)
  · rintro (rfl | rfl | rfl) <;> assumption

/-- **The key estimate**: a triangle whose inside holds at most half of the even faces has at
most two even faces inside. -/
theorem light_le_two (hH : IsDissection H) (hL : LightTriangles H) {x y z : Fin n} (hxy : x < y)
    (hyz : y < z) (hF : IsFace H {x, y, z}) (hhalf : 2 * marks H x z ≤ numEvenFaces H) :
    marks H x z ≤ 2 := by
  have hxz := hxy.trans hyz
  have hxF : x ∈ ({x, y, z} : Finset (Fin n)) := by simp
  have hyF : y ∈ ({x, y, z} : Finset (Fin n)) := by simp
  have hzF : z ∈ ({x, y, z} : Finset (Fin n)) := by simp
  have hmem : ∀ w ∈ ({x, y, z} : Finset (Fin n)), w = x ∨ w = y ∨ w = z := by
    intro w hw; simpa using hw
  -- the cyclic order of the triangle
  have c1 : CycNext {x, y, z} x y := (cycNext_lt hxy).mpr fun w hw ⟨h1, h2⟩ => by
    rcases hmem w hw with rfl | rfl | rfl
    · exact lt_irrefl _ h1
    · exact lt_irrefl _ h2
    · exact absurd (h2.trans hyz) (lt_irrefl _)
  have c2 : CycNext {x, y, z} y z := (cycNext_lt hyz).mpr fun w hw ⟨h1, h2⟩ => by
    rcases hmem w hw with rfl | rfl | rfl
    · exact absurd (hxy.trans h1) (lt_irrefl _)
    · exact lt_irrefl _ h1
    · exact lt_irrefl _ h2
  have c3 : CycNext {x, y, z} z x := (cycNext_gt hxz).mpr fun w hw h1 h2 => by
    rcases hmem w hw with rfl | rfl | rfl
    · exact absurd rfl h1
    · exact ⟨hxy, hyz⟩
    · exact absurd rfl h2
  have hL' := hL x y z hF (ne_of_lt hxy) (ne_of_lt hyz) (ne_of_lt hxz) c1 c2 c3
  -- the branches in linear form
  have hadj : H.Adj x z := (hF.2 x hxF z hzF (ne_of_lt hxz)).mpr (Or.inr c3)
  rw [br_lt hxy, br_lt hyz] at hL'
  have hsplit := numEven_split hH hxz hadj
  -- the inside of the triangle: its two other branches
  have hroot : rootFace H x z = {x, y, z} :=
    (face_eq_root hH hxz hadj (mem_facesIn.mpr ⟨hF, fun w hw => by
      rcases hmem w hw with rfl | rfl | rfl
      · exact mem_Icc.mpr ⟨le_rfl, hxz.le⟩
      · exact mem_Icc.mpr ⟨hxy.le, hyz.le⟩
      · exact mem_Icc.mpr ⟨hxz.le, le_rfl⟩⟩) hxF hzF).symm
  have h2 : x.val + 2 ≤ z.val := by
    have : x.val < y.val := hxy; have : y.val < z.val := hyz; omega
  obtain ⟨m, r, he⟩ := exists_rootEnum hH hadj h2
  have hm : m = 1 := by
    have := he.card
    rw [hroot, card_insert_of_notMem (by simp [ne_of_lt hxy, ne_of_lt hxz]),
      card_pair (ne_of_lt hyz)] at this
    omega
  subst hm
  have hr1 : r 1 = y := by
    have h1 := he.mem 1
    rw [hroot] at h1
    rcases hmem _ h1 with h | h | h
    · have := he.mono (show (0 : Fin 3) < 1 by decide)
      rw [he.first] at this
      exact absurd h (ne_of_gt this)
    · exact h
    · have := he.mono (show (1 : Fin 3) < 2 by decide)
      rw [show (2 : Fin 3) = Fin.last 2 from rfl, he.last] at this
      exact absurd h (ne_of_lt this)
  have hdec := he.marks_eq hH hadj hxz
  rw [Fin.sum_univ_two] at hdec
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one, Fin.succ_one_eq_two,
    he.first, hr1] at hdec
  rw [show (2 : Fin 3) = Fin.last 2 from rfl, he.last] at hdec
  have hodd : ¬ Even (1 + 2) := by decide
  simp only [hodd, ↓reduceIte, zero_add] at hdec
  omega

end Light

/-! ### The tags and the rule -/

section Rule

variable {H : SimpleGraph (Fin n)}

/-- No heavy triangle in `[u, v]`. -/
def NoHeavy (H : SimpleGraph (Fin n)) (u v : Fin n) : Prop :=
  ∀ Δ ∈ facesIn H u v, Δ.card = 3 → ∀ x ∈ Δ, ∀ z ∈ Δ, (∀ w ∈ Δ, x ≤ w ∧ w ≤ z) →
    marks H x z ≤ 2

/-- No heavy triangle inside an even face of `[a, b]`. -/
def CondL (H : SimpleGraph (Fin n)) (a b : Fin n) : Prop :=
  ∀ F ∈ facesIn H a b, Even F.card → ∀ u ∈ F, ∀ v ∈ F, (∀ w ∈ F, u ≤ w ∧ w ≤ v) → NoHeavy H u v

theorem NoHeavy.mono {u v u' v' : Fin n} (h : NoHeavy H u v) (h1 : u ≤ u') (h2 : v' ≤ v) :
    NoHeavy H u' v' := fun Δ hΔ => h Δ (facesIn_mono h1 h2 hΔ)

theorem CondL.mono {a b a' b' : Fin n} (h : CondL H a b) (h1 : a ≤ a') (h2 : b' ≤ b) :
    CondL H a' b' := fun F hF => h F (facesIn_mono h1 h2 hF)

open Classical in
theorem marks_mono {a b a' b' : Fin n} (h1 : a ≤ a') (h2 : b' ≤ b) :
    marks H a' b' ≤ marks H a b := by
  unfold marks
  exact card_le_card fun F hF => mem_filter.mpr ⟨facesIn_mono h1 h2 (mem_filter.mp hF).1,
    (mem_filter.mp hF).2⟩

open Classical in
/-- The tag of `[a, b]`: as for six even faces with at most two marks, otherwise the matching
bound without a heavy triangle, and the hexagon bound with one. -/
noncomputable def tagL (H : SimpleGraph (Fin n)) (a b : Fin n) : NTag :=
  if marks H a b ≤ 2 then tagOf H a b else if NoHeavy H a b then tMB else tHex

/-- **The face rule for light triangles.** -/
theorem ruleL (hH : IsDissection H) {a b : Fin n} (hadj : H.Adj a b) {m : ℕ}
    {r : Fin (m + 2) → Fin n} (he : RootEnum H a b m r) (hab : a < b) (hg : CondL H a b) :
    numRule (tagL H a b) m (fun i => tagL H (r i.castSucc) (r i.succ)) := by
  classical
  have hchild : ∀ i : Fin (m + 1), marks H (r i.castSucc) (r i.succ) ≤ marks H a b :=
    fun i => marks_mono (he.ge _) (he.le _)
  by_cases h2 : marks H a b ≤ 2
  · have e1 : tagL H a b = tagOf H a b := by unfold tagL; simp [h2]
    have e2 : (fun i : Fin (m + 1) => tagL H (r i.castSucc) (r i.succ))
        = fun i => tagOf H (r i.castSucc) (r i.succ) := by
      funext i; unfold tagL; simp [(hchild i).trans h2]
    rw [e1, e2]
    exact rule_of_enum hH hadj he hab (goodP_of_marks_le (by omega))
  · by_cases hnh : NoHeavy H a b
    · have e1 : tagL H a b = tMB := by unfold tagL; simp [h2, hnh]
      rw [e1]
      have hm2 : 2 ≤ m := by
        by_contra hlt
        have hm1 : m = 1 := by have := he.one_le; omega
        subst hm1
        have h2' : a.val + 2 ≤ b.val := by
          have := he.card
          by_contra h
          have := card_le_two_of_gap (rootFace_sub (H := H) (a := a) (b := b)) fun z _ ⟨h1, h2⟩ => by
            have : a.val < z.val := h1
            have : z.val < b.val := h2
            omega
          omega
        have := hnh (rootFace H a b) (mem_facesIn.mpr ⟨rootFace_isFace hH hadj h2', rootFace_sub⟩)
          he.card a (left_mem_rootFace hab.le) b (right_mem_rootFace hab.le) fun w hw =>
            ⟨(mem_rootFace.mp hw).1, (mem_rootFace.mp hw).2.1⟩
        exact h2 this
      refine numRule_mb hm2 fun i => ?_
      unfold tagL
      by_cases hc : marks H (r i.castSucc) (r i.succ) ≤ 2
      · simp only [hc, ↓reduceIte]; exact tagOf_mb hc
      · simp only [hc, ↓reduceIte, hnh.mono (he.ge _) (he.le _)]; rfl
    · have e1 : tagL H a b = tHex := by unfold tagL; simp [h2, hnh]
      rw [e1]
      rcases Nat.even_or_odd m with hev | hodd
      · -- an even root face has no heavy triangle inside: excluded
        exfalso
        have h2' : a.val + 2 ≤ b.val := by
          have := he.card
          have := he.one_le
          by_contra h
          have := card_le_two_of_gap (rootFace_sub (H := H) (a := a) (b := b)) fun z _ ⟨h1, h2⟩ => by
            have : a.val < z.val := h1
            have : z.val < b.val := h2
            omega
          omega
        refine hnh (hg (rootFace H a b) (mem_facesIn.mpr ⟨rootFace_isFace hH hadj h2',
          rootFace_sub⟩) ?_ a (left_mem_rootFace hab.le) b (right_mem_rootFace hab.le)
          fun w hw => ⟨(mem_rootFace.mp hw).1, (mem_rootFace.mp hw).2.1⟩)
        rw [he.card]; obtain ⟨k, hk⟩ := hev; exact ⟨k + 1, by omega⟩
      · exact numRule_hex_odd hodd

end Rule

/-! ### The theorem -/

variable {H : SimpleGraph (Fin n)}

/-- `CondL` from the half bound on every triangle off the top. -/
theorem condL_of_half (hH : IsDissection H) (hL : LightTriangles H) {a b : Fin n}
    (hhalf : ∀ Δ ∈ facesIn H a b, Δ.card = 3 → ∀ x ∈ Δ, ∀ z ∈ Δ,
      (∀ w ∈ Δ, x ≤ w ∧ w ≤ z) → ¬ (x = a ∧ z = b) → 2 * marks H x z ≤ numEvenFaces H) :
    CondL H a b := by
  intro F hF hev u hu v hv hext Δ hΔ h3 x hx z hz hextΔ
  obtain ⟨hΔf, hsubΔ⟩ := mem_facesIn.mp hΔ
  obtain ⟨hFf, hsubF⟩ := mem_facesIn.mp hF
  have hΔab : Δ ∈ facesIn H a b := mem_facesIn.mpr ⟨hΔf, fun w hw => by
    obtain ⟨h1, h2⟩ := mem_Icc.mp (hsubΔ hw)
    obtain ⟨h3, -⟩ := mem_Icc.mp (hsubF hu)
    obtain ⟨-, h4⟩ := mem_Icc.mp (hsubF hv)
    exact mem_Icc.mpr ⟨h3.trans h1, h2.trans h4⟩⟩
  obtain ⟨y, hxy, hyz, rfl⟩ := triangle_mid h3 hx hz hextΔ
  refine light_le_two hH hL hxy hyz hΔf (hhalf _ hΔab h3 x hx z hz hextΔ ?_)
  -- the triangle is not the root face: then it would be `F`, which is even
  intro hends
  obtain ⟨hxa, hzb⟩ := hends
  subst hxa hzb
  have hxz := hxy.trans hyz
  have hadj : H.Adj x z := (hΔf.2 x hx z hz (ne_of_lt hxz)).mpr (Or.inr ((cycNext_gt hxz).mpr
    fun w hw h1 h2 => ⟨lt_of_le_of_ne (hextΔ w hw).1 (Ne.symm h1),
      lt_of_le_of_ne (hextΔ w hw).2 h2⟩))
  have hux : u = x := le_antisymm (mem_Icc.mp (hsubΔ hx)).1 (mem_Icc.mp (hsubF hu)).1
  have hvz : v = z := le_antisymm (mem_Icc.mp (hsubF hv)).2 (mem_Icc.mp (hsubΔ hz)).2
  subst hux hvz
  have e1 := face_eq_root hH hxz hadj hF hu hv
  have e2 := face_eq_root hH hxz hadj hΔab hx hz
  rw [e1, ← e2, h3] at hev
  exact absurd hev (by decide)

/-- The least and greatest vertices of a triangular face are adjacent. -/
theorem tri_ends {Δ : Finset (Fin n)} (hΔ : IsFace H Δ) (h3 : Δ.card = 3) {x z : Fin n}
    (hx : x ∈ Δ) (hz : z ∈ Δ) (hext : ∀ w ∈ Δ, x ≤ w ∧ w ≤ z) : x < z ∧ H.Adj x z := by
  obtain ⟨y, hxy, hyz, -⟩ := triangle_mid h3 hx hz hext
  have hxz := hxy.trans hyz
  refine ⟨hxz, (hΔ.2 x hx z hz (ne_of_lt hxz)).mpr (Or.inr ((cycNext_gt hxz).mpr
    fun w hw h1 h2 => ⟨lt_of_le_of_ne (hext w hw).1 (Ne.symm h1),
      lt_of_le_of_ne (hext w hw).2 h2⟩))⟩

/-- **A polygon dissection with light triangles is 3-ECC**: if every triangular face has at most
two even faces outside its heaviest branch, then every assignment of lists of three colours has at
least as many proper colourings as there are `3`-colourings — with any number of even faces. -/
theorem ecc_three_of_lightTriangles {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : IsDissection G) (hn : 3 ≤ n) (hL : LightTriangles G) : G.ECCAt 3 := by
  have : NeZero n := ⟨by omega⟩
  suffices h : ∃ tg, TagBuilt G numSys numRule (fun _ _ => True) univ tg by
    obtain ⟨tg, h⟩ := h
    exact ecc_three_of_numBuilt G h
  have hbuild := exists_build (R := numSys) (rule := numRule) G hG (fun H => tagL H)
    (fun H => CondL H)
    (fun H hH _ _ _ _ hadj hab he hg => ruleL hH hadj he hab hg)
    (fun _ _ _ _ _ he hg _ => hg.mono (he.ge _) (he.le _))
  by_cases hbig : ∃ a b : Fin n, a < b ∧ G.Adj a b ∧ numEvenFaces G < 2 * marks G a b
  · -- a narrowest chord with more than half of the even faces inside
    have hex : ∃ d, ∃ a b : Fin n, a < b ∧ G.Adj a b ∧ numEvenFaces G < 2 * marks G a b ∧
        b.val - a.val = d := by
      obtain ⟨a, b, h1, h2, h3⟩ := hbig
      exact ⟨_, a, b, h1, h2, h3, rfl⟩
    obtain ⟨a, b, hab, hadj, hbig', hd⟩ := Nat.find_spec hex
    have hmin : ∀ a' b' : Fin n, a' < b' → G.Adj a' b' → b'.val - a'.val < b.val - a.val →
        2 * marks G a' b' ≤ numEvenFaces G := by
      intro a' b' h1 h2 hw
      by_contra h
      exact Nat.find_min hex (hd ▸ hw) ⟨a', b', h1, h2, by omega, rfl⟩
    have hg₁ : CondL G a b := condL_of_half hG hL fun Δ hΔ h3 x hx z hz hext hne => by
      obtain ⟨hΔf, hsub⟩ := mem_facesIn.mp hΔ
      obtain ⟨hxz, hadj'⟩ := tri_ends hΔf h3 hx hz hext
      refine hmin x z hxz hadj' ?_
      obtain ⟨h1, -⟩ := mem_Icc.mp (hsub hx)
      obtain ⟨-, h2⟩ := mem_Icc.mp (hsub hz)
      have : a.val ≤ x.val := h1
      have : z.val ≤ b.val := h2
      have : x.val < z.val := hxz
      by_cases e1 : x = a
      · have : z ≠ b := fun e => hne ⟨e1, e⟩
        have : z.val ≠ b.val := fun e => this (Fin.ext e)
        rw [e1]; omega
      · have : x.val ≠ a.val := fun e => e1 (Fin.ext e)
        omega
    have hside := marks_add_rot hG hab hadj
    have hg₂ : CondL (G.comap (rot b)) 0 (a - b) :=
      condL_of_half (isDissection_rot hG b) (lightTriangles_rot hL b)
        fun Δ hΔ h3 x hx z hz hext _ => by
          obtain ⟨-, hsub⟩ := mem_facesIn.mp hΔ
          have hle := marks_mono (H := G.comap (rot b)) (mem_Icc.mp (hsub hx)).1
            (mem_Icc.mp (hsub hz)).2
          rw [numEvenFaces_rot]
          omega
    exact hbuild a b hab hadj hg₁ hg₂
  · -- otherwise from the outer edge `(0, n - 1)`
    push Not at hbig
    obtain ⟨l, h0l, hadj, -, hl1⟩ := outer_edge (by omega) hG
    have hg₁ : CondL G 0 l := condL_of_half hG hL fun Δ hΔ h3 x hx z hz hext _ => by
      obtain ⟨hΔf, -⟩ := mem_facesIn.mp hΔ
      obtain ⟨hxz, hadj'⟩ := tri_ends hΔf h3 hx hz hext
      exact hbig x z hxz hadj'
    refine hbuild 0 l h0l hadj hg₁ fun F hF => ?_
    rw [facesIn_edge (by rw [hl1]; simp)] at hF
    simp at hF

end Outerplanar
