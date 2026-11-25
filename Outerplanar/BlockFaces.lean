/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.BranchBuild

/-!
# The faces of the regions of a block decomposition

For a graph with a block decomposition (`Outerplanar/BlockModel.lean`), the faces of all blocks
(`allFaces`, a face being a pair of a block and a face of its dissection) and the faces lying in
a vertex region `U` (`facesR U`), with the count of the even ones (`marksR U`) and the flag
"a square lies in `U`" (`sqR U`). These are the contents a tag system may read off a region
(`Outerplanar/BranchBuild.lean`); nothing here depends on the face rules.

* `Sep X Y` — every face of `X ∪ Y` lies in `X` or in `Y`, and none in both; then the faces,
  marks and squares add up (`facesR_union`, `marksR_union`, `sqR_union`).
* `sep_brR` — a branch is separated from what it is attached to.
* `facesR_side`, `marksR_side`, `sqR_side_root`, `sqR_side_child` — the faces of a side of a
  block are its root face and the faces of the children (`childR`), what hangs at the interior
  vertices of the root face included.
* `half_shift` — the half of a side `[a, b]` read from `c` is the half `halfR` of the edge
  `(c + a, c + b)`.
* `sep_halves`, `halves_union`, `marks_halves` — the two halves of an edge are separated and make
  up its connected component (`compR`); `marksR_comp` — the marks of a component are the even
  faces of its blocks.

Part of the formalization of the seven-even-face theorem with cut vertices (research note
`ai_research_notes/OUTERPLANAR_SEVEN_AND_CUTS_2026-11-23.md`); formalized by Claude.
-/

namespace Outerplanar

open Finset BlockDecomp

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {ι : Type} [Fintype ι] [DecidableEq ι] (D : BlockDecomp G ι)

namespace BlockDecomp

/-- A face of a block: the block and the face, in the block's coordinates. -/
abbrev FaceOcc := Σ j : ι, Finset (Fin (D.n j))

open Classical in
/-- All faces of all blocks. -/
noncomputable def allFaces : Finset D.FaceOcc := univ.filter fun f => IsFace (D.H f.1) f.2

/-- The vertices of a face in `G`. -/
def fimg (f : D.FaceOcc) : Finset V := f.2.image (D.ψ f.1)

open Classical in
/-- The faces lying in a region. -/
noncomputable def facesR (U : Finset V) : Finset D.FaceOcc :=
  D.allFaces.filter fun f => D.fimg f ⊆ U

open Classical in
/-- **The marks of a region**: the even faces of the blocks lying in it. -/
noncomputable def marksR (U : Finset V) : ℕ := ((D.facesR U).filter fun f => Even f.2.card).card

/-- A square face lies in the region. -/
def sqR (U : Finset V) : Prop := ∃ f ∈ D.facesR U, f.2.card = 4


variable {D}

theorem mem_allFaces {f : D.FaceOcc} : f ∈ D.allFaces ↔ IsFace (D.H f.1) f.2 := by
  unfold allFaces; simp only [mem_filter, mem_univ, true_and]

theorem mem_facesR {U : Finset V} {f : D.FaceOcc} :
    f ∈ D.facesR U ↔ IsFace (D.H f.1) f.2 ∧ D.fimg f ⊆ U := by
  unfold facesR; simp only [mem_filter, mem_allFaces]

theorem card_fimg (f : D.FaceOcc) : (D.fimg f).card = f.2.card :=
  card_image_of_injective _ (D.inj f.1)

theorem three_le_fimg {f : D.FaceOcc} (hf : IsFace (D.H f.1) f.2) : 3 ≤ (D.fimg f).card := by
  rw [card_fimg]; exact hf.1

theorem mem_fimg {f : D.FaceOcc} {v : V} : v ∈ D.fimg f ↔ ∃ a ∈ f.2, D.ψ f.1 a = v := by
  unfold fimg; simp only [mem_image]

theorem facesR_mono {U U' : Finset V} (h : U ⊆ U') : D.facesR U ⊆ D.facesR U' := fun f hf => by
  rw [mem_facesR] at hf ⊢; exact ⟨hf.1, hf.2.trans h⟩

theorem marksR_mono {U U' : Finset V} (h : U ⊆ U') : D.marksR U ≤ D.marksR U' := by
  classical
  unfold marksR
  exact card_le_card (filter_subset_filter _ (facesR_mono h))

theorem marksR_pos_of_sqR {U : Finset V} (h : D.sqR U) : 1 ≤ D.marksR U := by
  classical
  obtain ⟨f, hf, h4⟩ := h
  unfold marksR
  exact card_pos.mpr ⟨f, mem_filter.mpr ⟨hf, by rw [h4]; decide⟩⟩

/-- Faces lying in a small set: none. -/
theorem not_fimg_sub_of_card {f : D.FaceOcc} (hf : IsFace (D.H f.1) f.2) {U : Finset V}
    (hU : U.card ≤ 2) : ¬ D.fimg f ⊆ U := fun h => by
  have := card_le_card h
  have := three_le_fimg hf
  omega

/-! ### Separated regions -/

/-- Every face in `X ∪ Y` lies in `X` or in `Y`, and none in both. -/
def Sep (X Y : Finset V) : Prop :=
  (∀ f : D.FaceOcc, IsFace (D.H f.1) f.2 → D.fimg f ⊆ X ∪ Y → D.fimg f ⊆ X ∨ D.fimg f ⊆ Y) ∧
    ∀ f : D.FaceOcc, IsFace (D.H f.1) f.2 → D.fimg f ⊆ X → D.fimg f ⊆ Y → False

theorem facesR_union {X Y : Finset V} (h : D.Sep X Y) :
    D.facesR (X ∪ Y) = D.facesR X ∪ D.facesR Y := by
  ext f
  simp only [mem_union, mem_facesR]
  constructor
  · rintro ⟨hf, hs⟩
    rcases h.1 f hf hs with h' | h'
    · exact Or.inl ⟨hf, h'⟩
    · exact Or.inr ⟨hf, h'⟩
  · rintro (⟨hf, hs⟩ | ⟨hf, hs⟩)
    · exact ⟨hf, hs.trans subset_union_left⟩
    · exact ⟨hf, hs.trans subset_union_right⟩

theorem facesR_disj {X Y : Finset V} (h : D.Sep X Y) : Disjoint (D.facesR X) (D.facesR Y) := by
  rw [disjoint_left]
  intro f hX hY
  rw [mem_facesR] at hX hY
  exact h.2 f hX.1 hX.2 hY.2

theorem marksR_union {X Y : Finset V} (h : D.Sep X Y) :
    D.marksR (X ∪ Y) = D.marksR X + D.marksR Y := by
  classical
  unfold marksR
  rw [facesR_union h, filter_union, card_union_of_disjoint
    (disjoint_filter_filter (facesR_disj h))]

theorem sqR_union {X Y : Finset V} (h : D.Sep X Y) : D.sqR (X ∪ Y) ↔ D.sqR X ∨ D.sqR Y := by
  unfold sqR
  rw [facesR_union h]
  simp only [mem_union]
  constructor
  · rintro ⟨f, hf | hf, h4⟩
    · exact Or.inl ⟨f, hf, h4⟩
    · exact Or.inr ⟨f, hf, h4⟩
  · rintro (⟨f, hf, h4⟩ | ⟨f, hf, h4⟩)
    · exact ⟨f, Or.inl hf, h4⟩
    · exact ⟨f, Or.inr hf, h4⟩

/-- **A branch is closed**: a face meeting it outside its root lies in it. -/
theorem fimg_sub_brR {j : ι} {z₀ : Fin (D.n j)} {f : D.FaceOcc} {v : V} (hv : v ∈ D.fimg f)
    (hvB : v ∈ D.brR j z₀) (hvx : v ≠ D.ψ j z₀) : D.fimg f ⊆ D.brR j z₀ := by
  obtain ⟨a, -, rfl⟩ := mem_fimg.mp hv
  rcases mem_brR.mp hvB with h | ⟨z, hz, h⟩
  · exact absurd h hvx
  intro w hw
  obtain ⟨b, -, rfl⟩ := mem_fimg.mp hw
  by_cases hk : f.1 = j
  · obtain ⟨k, F⟩ := f
    simp only at hk
    subst hk
    by_cases hb : b = z₀
    · rw [hb]; exact mem_brR.mpr (Or.inl rfl)
    · exact mem_brR.mpr (Or.inr ⟨b, hb, D.hang_self _ b⟩)
  · exact mem_brR.mpr (Or.inr ⟨z, hz, D.block_mem_hang hk h b⟩)

/-- **A branch is separated from what it is attached to.** -/
theorem sep_brR {j : ι} {z₀ : Fin (D.n j)} {X : Finset V} (hx : D.ψ j z₀ ∈ X)
    (hX : ∀ v ∈ X, v ∈ D.brR j z₀ → v = D.ψ j z₀) : D.Sep X (D.brR j z₀) := by
  refine ⟨fun f hf hs => ?_, fun f hf h1 h2 => ?_⟩
  · by_cases hm : ∃ v ∈ D.fimg f, v ∈ D.brR j z₀ ∧ v ≠ D.ψ j z₀
    · obtain ⟨v, hv, hvB, hvx⟩ := hm
      exact Or.inr (fimg_sub_brR hv hvB hvx)
    · push Not at hm
      left
      intro v hv
      rcases mem_union.mp (hs hv) with h | h
      · exact h
      · rw [hm v hv h]; exact hx
  · refine not_fimg_sub_of_card hf (U := {D.ψ j z₀}) (by simp) fun v hv => ?_
    exact mem_singleton.mpr (hX v (h1 hv) (h2 hv))

end BlockDecomp

/-! ### The marks of a side -/

namespace BlockDecomp

variable {D} {j : ι} {c : Fin (D.n j)}

theorem sideR_mono {a b a' b' : Fin (D.n j)} (h1 : a ≤ a') (h2 : b' ≤ b) (h3 : a' < b') :
    sideR (D.vψ j c) (D.vhang j c) a' b' ⊆ sideR (D.vψ j c) (D.vhang j c) a b := by
  intro v hv
  have hok := D.view_hangOK j c
  rcases mem_sideR.mp hv with rfl | rfl | ⟨z, hz1, hz2, hz⟩
  · rcases h1.lt_or_eq with h1 | rfl
    · exact mem_sideR.mpr (Or.inr (Or.inr ⟨a', h1, h3.trans_le h2, hok.self a'⟩))
    · exact mem_sideR.mpr (Or.inl rfl)
  · rcases h2.lt_or_eq with h2 | rfl
    · exact mem_sideR.mpr (Or.inr (Or.inr ⟨b', h1.trans_lt h3, h2, hok.self b'⟩))
    · exact mem_sideR.mpr (Or.inr (Or.inl rfl))
  · exact mem_sideR.mpr (Or.inr (Or.inr ⟨z, h1.trans_lt hz1, hz2.trans_le h2, hz⟩))

/-- Where the vertices of a side are: each hangs at a vertex of the side, and at an end only
as the end itself. -/
theorem anchor_sideR {a b : Fin (D.n j)} {v : V} (hv : v ∈ sideR (D.vψ j c) (D.vhang j c) a b)
    (hab : a < b) :
    ∃ z, a ≤ z ∧ z ≤ b ∧ v ∈ D.vhang j c z ∧ (z = a → v = D.vψ j c a) ∧
      (z = b → v = D.vψ j c b) := by
  have hok := D.view_hangOK j c
  rcases mem_sideR.mp hv with rfl | rfl | ⟨z, hz1, hz2, hz⟩
  · exact ⟨a, le_rfl, hab.le, hok.self a, fun _ => rfl, fun h => absurd h (ne_of_lt hab)⟩
  · exact ⟨b, hab.le, le_rfl, hok.self b, fun h => absurd h (ne_of_gt hab), fun _ => rfl⟩
  · exact ⟨z, hz1.le, hz2.le, hz, fun h => absurd h (ne_of_gt hz1),
      fun h => absurd h (ne_of_lt hz2)⟩

variable {m : ℕ} {r : Fin (m + 2) → Fin (D.n j)}

theorem anchor_childR {a b : Fin (D.n j)} (he : RootEnum (D.vH j c) a b m r) (i : Fin (m + 1))
    {v : V} (hv : v ∈ childR (D.vψ j c) (D.vhang j c) r i) :
    ∃ z, r i.castSucc ≤ z ∧ z ≤ r i.succ ∧ v ∈ D.vhang j c z ∧
      (z = r i.succ → v = D.vψ j c (r i.succ)) := by
  unfold childR at hv
  split_ifs at hv with h0
  · obtain ⟨z, h1, h2, h3, -, h5⟩ := anchor_sideR hv (he.lt i)
    exact ⟨z, h1, h2, h3, h5⟩
  · rcases mem_union.mp hv with hv | hv
    · obtain ⟨z, h1, h2, h3, -, h5⟩ := anchor_sideR hv (he.lt i)
      exact ⟨z, h1, h2, h3, h5⟩
    · exact ⟨_, le_rfl, (he.lt i).le, hv, fun h => absurd h (ne_of_lt (he.lt i))⟩

/-- A vertex of the block in a region located by anchors: its view index is the anchor. -/
theorem vψ_mem_vhang {z y : Fin (D.n j)} (h : D.ψ j y ∈ D.vhang j c z) : y - c = z := by
  rw [vhang_apply] at h
  exact (rot_eq_iff.mp (BlockDecomp.hang_idx h).symm).symm

/-- Two children of a root face share at most a vertex. -/
theorem childR_inter {a b : Fin (D.n j)} (he : RootEnum (D.vH j c) a b m r) {i i' : Fin (m + 1)}
    (hii : i < i') {v : V} (hv : v ∈ childR (D.vψ j c) (D.vhang j c) r i)
    (hv' : v ∈ childR (D.vψ j c) (D.vhang j c) r i') : v = D.vψ j c (r i.succ) := by
  obtain ⟨z, h1, h2, h3, h4⟩ := anchor_childR he i hv
  obtain ⟨z', h1', -, h3', -⟩ := anchor_childR he i' hv'
  have e : z = z' := rot_injective c (D.hang_disj h3 h3')
  subst e
  have : r i.succ ≤ r i'.castSucc := he.mono.monotone (by
    show i.val + 1 ≤ i'.val; exact hii)
  exact h4 (le_antisymm h2 (this.trans h1'))

theorem childR_sub {a b : Fin (D.n j)} (he : RootEnum (D.vH j c) a b m r) (i : Fin (m + 1)) :
    childR (D.vψ j c) (D.vhang j c) r i ⊆ sideR (D.vψ j c) (D.vhang j c) a b := by
  have hs := sideR_mono (c := c) (he.ge i.castSucc) (he.le i.succ) (he.lt i)
  unfold childR
  split_ifs with h0
  · exact hs
  · refine union_subset hs fun v hv => mem_sideR.mpr (Or.inr (Or.inr ⟨_, ?_, ?_, hv⟩))
    · rw [← he.first]; exact he.mono (show (0 : ℕ) < i.val by omega)
    · exact (he.lt i).trans_le (he.le _)

/-- The root face of a side, as a face of the block. -/
noncomputable def rootOcc (j : ι) (c a b : Fin (D.n j)) : D.FaceOcc :=
  ⟨j, (rootFace (D.vH j c) a b).image (rot c)⟩

theorem fimg_rootOcc (a b : Fin (D.n j)) :
    D.fimg (rootOcc j c a b) = (rootFace (D.vH j c) a b).image (D.vψ j c) := by
  unfold fimg rootOcc
  rw [image_image]
  rfl

theorem card_rootOcc {a b : Fin (D.n j)} (he : RootEnum (D.vH j c) a b m r) :
    (rootOcc j c a b).2.card = m + 2 := by
  show ((rootFace (D.vH j c) a b).image (rot c)).card = m + 2
  rw [card_image_of_injective _ (rot_injective c), he.card]

theorem two_le_of_enum {a b : Fin (D.n j)} (he : RootEnum (D.vH j c) a b m r) :
    a.val + 2 ≤ b.val := by
  have := he.card; have := he.one_le
  by_contra h
  have := card_le_two_of_gap (rootFace_sub (H := D.vH j c) (a := a) (b := b))
    fun z _ ⟨h1, h2⟩ => by
      have : a.val < z.val := h1
      have : z.val < b.val := h2
      omega
  omega

/-- A face of the block `j`, read in the view. -/
theorem view_face {F : Finset (Fin (D.n j))} (hF : IsFace (D.H j) F) :
    IsFace (D.vH j c) (F.image (· - c)) ∧ (F.image (· - c)).image (rot c) = F := by
  have e : (F.image (· - c)).image (rot c) = F := by
    rw [image_image]
    conv_rhs => rw [← image_id (s := F)]
    exact image_congr fun z _ => rot_sub' c z
  refine ⟨?_, e⟩
  unfold vH
  rw [isFace_rot, e]
  exact hF

theorem view_face_sub {F : Finset (Fin (D.n j))} {a b : Fin (D.n j)} (hab : a < b)
    (h : D.fimg ⟨j, F⟩ ⊆ sideR (D.vψ j c) (D.vhang j c) a b) : F.image (· - c) ⊆ Icc a b := by
  intro k hk
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hk
  obtain ⟨z, h1, h2, h3, -, -⟩ := anchor_sideR (h (mem_fimg.mpr ⟨y, hy, rfl⟩)) hab
  rw [vψ_mem_vhang h3]
  exact mem_Icc.mpr ⟨h1, h2⟩

theorem view_face_childR {F : Finset (Fin (D.n j))} {a b : Fin (D.n j)}
    (he : RootEnum (D.vH j c) a b m r) (i : Fin (m + 1))
    (h : D.fimg ⟨j, F⟩ ⊆ childR (D.vψ j c) (D.vhang j c) r i) :
    F.image (· - c) ⊆ Icc (r i.castSucc) (r i.succ) := by
  intro k hk
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hk
  obtain ⟨z, h1, h2, h3, -⟩ := anchor_childR he i (h (mem_fimg.mpr ⟨y, hy, rfl⟩))
  rw [vψ_mem_vhang h3]
  exact mem_Icc.mpr ⟨h1, h2⟩

theorem fimg_view_sub {F' : Finset (Fin (D.n j))} {a b : Fin (D.n j)} (hab : a < b)
    (h : F' ⊆ Icc a b) :
    D.fimg ⟨j, F'.image (rot c)⟩ ⊆ sideR (D.vψ j c) (D.vhang j c) a b := by
  intro v hv
  obtain ⟨y, hy, rfl⟩ := mem_fimg.mp hv
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hy
  obtain ⟨h1, h2⟩ := mem_Icc.mp (h hk)
  rcases h1.lt_or_eq with h1 | rfl
  · rcases h2.lt_or_eq with h2 | rfl
    · exact mem_sideR.mpr (Or.inr (Or.inr ⟨k, h1, h2, D.hang_self j _⟩))
    · exact mem_sideR.mpr (Or.inr (Or.inl rfl))
  · exact mem_sideR.mpr (Or.inl rfl)

/-- A face of another block in a side hangs at an interior vertex. -/
theorem other_face_sideR {k : ι} (hk : k ≠ j) {F : Finset (Fin (D.n k))} (hF : IsFace (D.H k) F)
    {a b : Fin (D.n j)} (hab : a < b)
    (h : D.fimg ⟨k, F⟩ ⊆ sideR (D.vψ j c) (D.vhang j c) a b) :
    ∃ z, a < z ∧ z < b ∧ D.fimg ⟨k, F⟩ ⊆ D.vhang j c z := by
  have hc := three_le_fimg (f := ⟨k, F⟩) hF
  obtain ⟨v, hv, hvn⟩ : ∃ v ∈ D.fimg ⟨k, F⟩, v ∉ ({D.vψ j c a, D.vψ j c b} : Finset V) := by
    by_contra hall
    push Not at hall
    have := card_le_card hall
    have := card_le_two (a := D.vψ j c a) (b := D.vψ j c b)
    omega
  simp only [mem_insert, mem_singleton, not_or] at hvn
  rcases mem_sideR.mp (h hv) with e | e | ⟨z, hz1, hz2, hz⟩
  · exact absurd e hvn.1
  · exact absurd e hvn.2
  refine ⟨z, hz1, hz2, fun w hw => ?_⟩
  obtain ⟨a₁, -, rfl⟩ := mem_fimg.mp hv
  obtain ⟨b₁, -, rfl⟩ := mem_fimg.mp hw
  rw [vhang_apply] at hz ⊢
  exact D.block_mem_hang hk hz b₁

/-- **The faces of a side**: its root face and the faces of the children. -/
theorem facesR_side {a b : Fin (D.n j)} (hadj : (D.vH j c).Adj a b) (hab : a < b)
    (he : RootEnum (D.vH j c) a b m r) :
    D.facesR (sideR (D.vψ j c) (D.vhang j c) a b) =
      insert (rootOcc j c a b) (univ.biUnion fun i => D.facesR (childR (D.vψ j c) (D.vhang j c) r i)) := by
  have hH := D.view_diss j c
  have h2 := two_le_of_enum he
  ext ⟨k, F⟩
  rw [mem_insert, mem_biUnion]
  constructor
  · intro hf
    obtain ⟨hF, hs⟩ := mem_facesR.mp hf
    by_cases hk : k = j
    · subst hk
      obtain ⟨hF', e⟩ := view_face (c := c) hF
      have hmem : F.image (· - c) ∈ facesIn (D.vH k c) a b :=
        mem_facesIn.mpr ⟨hF', view_face_sub hab hs⟩
      rcases he.cover hH hadj hab hmem with h | ⟨i, hi⟩
      · left
        unfold rootOcc
        rw [← h, e]
      · right
        refine ⟨i, mem_univ _, mem_facesR.mpr ⟨hF, ?_⟩⟩
        have := fimg_view_sub (c := c) (he.lt i) (mem_facesIn.mp hi).2
        rw [e] at this
        exact this.trans (by
          unfold childR; split_ifs
          · exact subset_rfl
          · exact subset_union_left)
    · obtain ⟨z, hz1, hz2, hz⟩ := other_face_sideR hk hF hab hs
      right
      obtain ⟨i, hi1, hi2⟩ := he.cover_Icc hz1.le hz2.le
      rcases hi1.lt_or_eq with hi1 | hi1
      · rcases hi2.lt_or_eq with hi2 | hi2
        · refine ⟨i, mem_univ _, mem_facesR.mpr ⟨hF, hz.trans fun v hv => ?_⟩⟩
          have : v ∈ sideR (D.vψ j c) (D.vhang j c) (r i.castSucc) (r i.succ) :=
            mem_sideR.mpr (Or.inr (Or.inr ⟨z, hi1, hi2, hv⟩))
          unfold childR; split_ifs
          · exact this
          · exact mem_union_left _ this
        · have hil : i.val + 1 < m + 1 := by
            by_contra hc
            have : i.succ = Fin.last (m + 1) := Fin.ext (by simp; omega)
            rw [hi2, this, he.last] at hz2
            exact lt_irrefl _ hz2
          set i' : Fin (m + 1) := ⟨i.val + 1, hil⟩
          refine ⟨i', mem_univ _, mem_facesR.mpr ⟨hF, hz.trans fun v hv => ?_⟩⟩
          unfold childR
          rw [ite_eq_right (by simp [i'])]
          have : i'.castSucc = i.succ := Fin.ext (by simp [i'])
          rw [this, ← hi2]
          exact mem_union_right _ hv
      · have hi0 : i.val ≠ 0 := by
          intro h0
          have : i.castSucc = 0 := Fin.ext (by simp [h0])
          rw [this, he.first] at hi1
          rw [hi1] at hz1
          exact lt_irrefl _ hz1
        refine ⟨i, mem_univ _, mem_facesR.mpr ⟨hF, hz.trans fun v hv => ?_⟩⟩
        unfold childR
        rw [ite_eq_right hi0, hi1]
        exact mem_union_right _ hv
  · rintro (h | ⟨i, -, hi⟩)
    · rw [h]
      refine mem_facesR.mpr ⟨?_, ?_⟩
      · show IsFace (D.H j) ((rootFace (D.vH j c) a b).image (rot c))
        rw [← isFace_rot]
        exact rootFace_isFace hH hadj h2
      · exact fimg_view_sub hab rootFace_sub
    · exact facesR_mono (childR_sub he i) hi

theorem rootOcc_notMem {a b : Fin (D.n j)} (hadj : (D.vH j c).Adj a b)
    (he : RootEnum (D.vH j c) a b m r) (i : Fin (m + 1)) :
    rootOcc j c a b ∉ D.facesR (childR (D.vψ j c) (D.vhang j c) r i) := by
  intro h
  obtain ⟨hF, hs⟩ := mem_facesR.mp h
  have hsub := view_face_childR he i hs
  have e : ((rootFace (D.vH j c) a b).image (rot c)).image (· - c) = rootFace (D.vH j c) a b := by
    rw [image_image]
    conv_rhs => rw [← image_id (s := rootFace (D.vH j c) a b)]
    exact image_congr fun z _ => by simp [rot]
  unfold rootOcc at hsub
  rw [e] at hsub
  exact he.root_not_child i (mem_facesIn.mpr ⟨rootFace_isFace (D.view_diss j c)
    hadj (two_le_of_enum he), hsub⟩)

/-- **The marks of a side**: the root face, if even, and the marks of the children. -/
theorem marksR_side {a b : Fin (D.n j)} (hadj : (D.vH j c).Adj a b) (hab : a < b)
    (he : RootEnum (D.vH j c) a b m r) :
    D.marksR (sideR (D.vψ j c) (D.vhang j c) a b) = (if Even (m + 2) then 1 else 0)
      + ∑ i, D.marksR (childR (D.vψ j c) (D.vhang j c) r i) := by
  classical
  unfold marksR
  rw [facesR_side hadj hab he, filter_insert, filter_biUnion]
  have hdisj : ((univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))).PairwiseDisjoint fun i =>
      (D.facesR (childR (D.vψ j c) (D.vhang j c) r i)).filter fun f => Even f.2.card := by
    intro i _ i' _ hii
    refine disjoint_filter_filter ?_
    rw [disjoint_left]
    intro f hf hf'
    obtain ⟨hF, hs⟩ := mem_facesR.mp hf
    obtain ⟨-, hs'⟩ := mem_facesR.mp hf'
    rcases lt_or_gt_of_ne hii with h | h
    · exact not_fimg_sub_of_card hF (U := {D.vψ j c (r i.succ)}) (by simp) fun v hv =>
        mem_singleton.mpr (childR_inter he h (hs hv) (hs' hv))
    · exact not_fimg_sub_of_card hF (U := {D.vψ j c (r i'.succ)}) (by simp) fun v hv =>
        mem_singleton.mpr (childR_inter he h (hs' hv) (hs hv))
  have hnot : rootOcc j c a b ∉ univ.biUnion fun i =>
      (D.facesR (childR (D.vψ j c) (D.vhang j c) r i)).filter fun f => Even f.2.card := by
    simp only [mem_biUnion, mem_univ, true_and, mem_filter, not_exists, not_and]
    exact fun i h _ => rootOcc_notMem hadj he i h
  rw [card_rootOcc he]
  by_cases hev : Even (m + 2)
  · simp only [hev, ↓reduceIte]
    rw [card_insert_of_notMem hnot, card_biUnion hdisj]
    ring
  · simp only [hev, ↓reduceIte]
    rw [card_biUnion hdisj, zero_add]

theorem sqR_side_root {a b : Fin (D.n j)} (hadj : (D.vH j c).Adj a b) (hab : a < b)
    (he : RootEnum (D.vH j c) a b m r)
    (h0 : ∀ i, D.marksR (childR (D.vψ j c) (D.vhang j c) r i) = 0) :
    D.sqR (sideR (D.vψ j c) (D.vhang j c) a b) ↔ m = 2 := by
  unfold sqR
  rw [facesR_side hadj hab he]
  constructor
  · rintro ⟨f, hf, h4⟩
    rcases mem_insert.mp hf with rfl | hf
    · rw [card_rootOcc he] at h4; omega
    · obtain ⟨i, -, hi⟩ := mem_biUnion.mp hf
      have := marksR_pos_of_sqR ⟨f, hi, h4⟩
      rw [h0 i] at this
      omega
  · intro hm
    exact ⟨_, mem_insert_self _ _, by rw [card_rootOcc he, hm]⟩

theorem sqR_side_child {a b : Fin (D.n j)} (hadj : (D.vH j c).Adj a b) (hab : a < b)
    (he : RootEnum (D.vH j c) a b m r) (hodd : ¬ Even (m + 2)) (i₀ : Fin (m + 1))
    (h0 : ∀ i, i ≠ i₀ → D.marksR (childR (D.vψ j c) (D.vhang j c) r i) = 0) :
    D.sqR (sideR (D.vψ j c) (D.vhang j c) a b) ↔
      D.sqR (childR (D.vψ j c) (D.vhang j c) r i₀) := by
  unfold sqR
  rw [facesR_side hadj hab he]
  constructor
  · rintro ⟨f, hf, h4⟩
    rcases mem_insert.mp hf with rfl | hf
    · rw [card_rootOcc he] at h4
      exact absurd (show Even (m + 2) by rw [h4]; decide) hodd
    · obtain ⟨i, -, hi⟩ := mem_biUnion.mp hf
      by_cases hii : i = i₀
      · exact ⟨f, hii ▸ hi, h4⟩
      · have := marksR_pos_of_sqR ⟨f, hi, h4⟩
        rw [h0 i hii] at this
        omega
  · rintro ⟨f, hf, h4⟩
    exact ⟨f, mem_insert_of_mem (mem_biUnion.mpr ⟨i₀, mem_univ _, hf⟩), h4⟩

/-! ### Halves -/

/-- The half of a side read from the start of the side. -/
theorem half_shift {a b : Fin (D.n j)} (hab : a < b) :
    sideR (D.vψ j c) (D.vhang j c) a b ∪ D.vhang j c a = D.halfR j (rot c a) (rot c b) := by
  unfold halfR
  have hqp : rot c b - rot c a = b - a := add_sub_add_right_eq_sub b a c
  rw [hqp]
  have hav : a.val < b.val := hab
  have hba : (b - a).val = b.val - a.val := sub_val_le hab.le
  congr 1
  · ext v
    simp only [mem_sideR]
    have e0 : D.vψ j (rot c a) 0 = D.vψ j c a := by rw [vψ_apply, rot_zero']; rfl
    have e1 : D.vψ j (rot c a) (b - a) = D.vψ j c b := by
      rw [vψ_apply, vψ_apply]; congr 1; simp only [rot]; rw [← add_assoc, sub_add_cancel]
    rw [e0, e1]
    refine or_congr Iff.rfl (or_congr Iff.rfl ⟨?_, ?_⟩)
    · rintro ⟨z, h1, h2, hz⟩
      refine ⟨z - a, ?_, ?_, ?_⟩
      · exact Fin.pos_iff_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt h1))
      · rw [Fin.lt_def, hba, sub_val_le h1.le]
        have : z.val < b.val := h2
        have : a.val < z.val := h1
        omega
      · have : rot (rot c a) (z - a) = rot c z := by
          simp only [rot]; rw [← add_assoc, sub_add_cancel]
        show v ∈ D.hang j (rot (rot c a) (z - a))
        rw [this]; exact hz
    · rintro ⟨k, h1, h2, hk⟩
      have hk1 : 0 < k.val := h1
      have hk2 : k.val < b.val - a.val := by rw [← hba]; exact h2
      have hka : (k + a).val = k.val + a.val := by
        rw [Fin.val_add]; exact Nat.mod_eq_of_lt (by have := b.isLt; omega)
      refine ⟨k + a, ?_, ?_, ?_⟩
      · rw [Fin.lt_def, hka]; omega
      · rw [Fin.lt_def, hka]; omega
      · have : rot c (k + a) = rot (rot c a) k := by simp only [rot]; rw [add_assoc]
        show v ∈ D.hang j (rot c (k + a))
        rw [this]; exact hk

theorem anchor_halfR {i : ι} {p q : Fin (D.n i)} (hpq : p ≠ q) {v : V}
    (hv : v ∈ D.halfR i p q) :
    ∃ z, v ∈ D.hang i z ∧ (z = p ∨ (z = q ∧ v = D.ψ i q) ∨
      (0 < (z - p).val ∧ (z - p).val < (q - p).val)) := by
  unfold halfR at hv
  rcases mem_union.mp hv with hv | hv
  · have hq0 : (0 : Fin (D.n i)) < q - p :=
      Fin.pos_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hpq))
    obtain ⟨z, h1, h2, h3, h4, h5⟩ := anchor_sideR hv hq0
    refine ⟨rot p z, h3, ?_⟩
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · right; right
        rw [show rot p z - p = z by simp [rot]]
        exact ⟨h1, h2⟩
      · right; left
        refine ⟨by rw [h2]; exact rot_sub' p q, ?_⟩
        rw [h5 h2, vψ_apply, rot_sub']
    · left; rw [← h1]; exact rot_zero' p
  · exact ⟨p, hv, Or.inl rfl⟩

/-- The two halves of an edge meet in its ends. -/
theorem halfR_inter {i : ι} {p q : Fin (D.n i)} (hpq : p ≠ q) {v : V}
    (h1 : v ∈ D.halfR i p q) (h2 : v ∈ D.halfR i q p) : v = D.ψ i p ∨ v = D.ψ i q := by
  obtain ⟨z, hz, hc⟩ := anchor_halfR hpq h1
  obtain ⟨z', hz', hc'⟩ := anchor_halfR (Ne.symm hpq) h2
  have e : z = z' := D.hang_disj hz hz'
  subst e
  rcases hc with h | ⟨-, hv⟩ | ⟨a1, a2⟩
  · rcases hc' with h' | ⟨-, hv'⟩ | ⟨-, b2⟩
    · exact absurd (h.symm.trans h') hpq
    · exact Or.inl hv'
    · rw [h] at b2; exact absurd b2 (lt_irrefl _)
  · exact Or.inr hv
  · rcases hc' with h' | ⟨h', -⟩ | ⟨b1, b2⟩
    · rw [h'] at a2; exact absurd a2 (lt_irrefl _)
    · rw [h', sub_self] at a1; simp at a1
    · exact absurd ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ (arc_disj p q z)

/-- The vertices of the arc from `q` to `p` other than `p` and `q` lie in the half on the side
of `q`. -/
theorem mem_halfR_of_arc {i : ι} {p q z : Fin (D.n i)} (hpq : p ≠ q)
    (h : z = p ∨ z = q ∨ (0 < (z - p).val ∧ (z - p).val < (q - p).val)) :
    D.ψ i z ∈ D.halfR i p q := by
  unfold halfR
  rcases h with rfl | rfl | ⟨h1, h2⟩
  · exact mem_union_right _ (D.hang_self _ _)
  · refine mem_union_left _ (mem_sideR.mpr (Or.inr (Or.inl ?_)))
    rw [vψ_apply, rot_sub']
  · refine mem_union_left _ (mem_sideR.mpr (Or.inr (Or.inr ⟨z - p, Fin.lt_def.mpr (by simpa using h1),
      Fin.lt_def.mpr h2, ?_⟩)))
    rw [vhang_apply, rot_sub']; exact D.hang_self _ _

theorem hang_sub_halfR {i : ι} {p q z : Fin (D.n i)}
    (h : z = p ∨ (0 < (z - p).val ∧ (z - p).val < (q - p).val)) :
    D.hang i z ⊆ D.halfR i p q := by
  unfold halfR
  rcases h with rfl | ⟨h1, h2⟩
  · exact subset_union_right
  · intro v hv
    refine mem_union_left _ (mem_sideR.mpr (Or.inr (Or.inr ⟨z - p, Fin.lt_def.mpr (by simpa using h1),
      Fin.lt_def.mpr h2, ?_⟩)))
    rw [vhang_apply, rot_sub']; exact hv

/-- **The two halves of an edge are separated.** -/
theorem sep_halves {i : ι} {p q : Fin (D.n i)} (hpq : (D.H i).Adj p q) :
    D.Sep (D.halfR i p q) (D.halfR i q p) := by
  have hne : p ≠ q := hpq.ne
  refine ⟨fun ⟨k, F⟩ hF hs => ?_, fun f hf h1 h2 => ?_⟩
  · by_cases hk : k = i
    · subst hk
      obtain ⟨hF', e⟩ := view_face (c := p) hF
      have hq0 : (0 : Fin (D.n k)) < q - p :=
        Fin.pos_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hne))
      have hadj : (D.vH k p).Adj 0 (q - p) := by
        show (D.H k).Adj (rot p 0) (rot p (q - p))
        rw [rot_zero', rot_sub']; exact hpq
      by_cases hin : ∃ x ∈ F.image (· - p), 0 < x ∧ x < q - p
      · obtain ⟨x, hx, h1, h2⟩ := hin
        have hsub := face_sep (D.view_diss k p) hF' hq0 hadj hx h1 h2
        left
        have := fimg_view_sub (c := p) hq0 (F' := F.image (· - p)) fun y hy =>
          mem_Icc.mpr (hsub y hy)
        rw [e] at this
        exact this.trans subset_union_left
      · push Not at hin
        right
        intro v hv
        obtain ⟨z, hz, rfl⟩ := mem_fimg.mp hv
        have hz' := hin (z - p) (mem_image_of_mem _ hz)
        apply mem_halfR_of_arc (Ne.symm hne)
        rcases arc_cases p q z hne with h | h | ⟨h1, h2⟩ | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact absurd (hz' (Fin.lt_def.mpr (by simpa using h1))) (not_le.mpr (Fin.lt_def.mpr h2))
        · exact Or.inr (Or.inr h)
    · obtain ⟨a₀, ha₀⟩ : F.Nonempty := card_pos.mp (by have h3 : 3 ≤ F.card := hF.1; omega)
      obtain ⟨z, hz⟩ : ∃ z, D.ψ k a₀ ∈ D.hang i z := by
        rcases mem_union.mp (hs (mem_fimg.mpr ⟨a₀, ha₀, rfl⟩)) with h | h
        · obtain ⟨z, hz, -⟩ := anchor_halfR hne h; exact ⟨z, hz⟩
        · obtain ⟨z, hz, -⟩ := anchor_halfR (Ne.symm hne) h; exact ⟨z, hz⟩
      have hsub : D.fimg ⟨k, F⟩ ⊆ D.hang i z := fun v hv => by
        obtain ⟨b, -, rfl⟩ := mem_fimg.mp hv
        exact D.block_mem_hang hk hz b
      rcases arc_cases p q z hne with h | h | h | h
      · exact Or.inl (hsub.trans (hang_sub_halfR (Or.inl h)))
      · exact Or.inr (hsub.trans (hang_sub_halfR (Or.inl h)))
      · exact Or.inl (hsub.trans (hang_sub_halfR (Or.inr h)))
      · exact Or.inr (hsub.trans (hang_sub_halfR (Or.inr h)))
  · refine not_fimg_sub_of_card hf (U := {D.ψ i p, D.ψ i q}) (card_le_two) fun v hv => ?_
    rcases halfR_inter hne (h1 hv) (h2 hv) with h | h <;> simp [h]

variable (G) in
open Classical in
/-- The vertices reachable from `v₀`: its connected component. -/
noncomputable def compR (v₀ : V) : Finset V := univ.filter fun v => G.Reachable v₀ v

theorem mem_compR {v₀ v : V} : v ∈ compR G v₀ ↔ G.Reachable v₀ v := by
  unfold compR; simp only [mem_filter, mem_univ, true_and]

theorem compR_eq {v₀ w : V} (h : G.Reachable v₀ w) : compR G w = compR G v₀ := by
  ext v
  rw [mem_compR, mem_compR]
  exact ⟨fun h' => h.trans h', fun h' => h.symm.trans h'⟩

theorem block_reachable {i : ι} (a b : Fin (D.n i)) : G.Reachable (D.ψ i a) (D.ψ i b) := by
  have := D.block_reach (E := ∅) (k := i) (fun _ _ _ => Set.notMem_empty _) a b
  rwa [SimpleGraph.deleteEdges_empty] at this

theorem hang_reachable {i : ι} {y z : Fin (D.n i)} {v : V} (hv : v ∈ D.hang i z) :
    G.Reachable (D.ψ i y) v :=
  (block_reachable y z).trans
    (SimpleGraph.Reachable.mono (SimpleGraph.deleteEdges_le _) (mem_hang.mp hv))

/-- The hanging sets of a block cover its component. -/
theorem hang_cover' {i : ι} {y₀ : Fin (D.n i)} {v : V} (hv : G.Reachable (D.ψ i y₀) v) :
    ∃ y, v ∈ D.hang i y := by
  refine reach_closed (G' := G) (s := D.ψ i y₀) (P := fun v => ∃ y, v ∈ D.hang i y)
    ⟨_, D.hang_self i _⟩ ?_ hv
  rintro u w - huw ⟨y, hu⟩
  rcases D.hang_closed hu huw with h | ⟨-, b, rfl⟩
  · exact ⟨y, h⟩
  · exact ⟨b, D.hang_self i b⟩

/-- **The two halves of an edge make up its component.** -/
theorem halves_union {i : ι} {p q : Fin (D.n i)} (hpq : p ≠ q) :
    D.halfR i p q ∪ D.halfR i q p = compR G (D.ψ i p) := by
  ext v
  rw [mem_compR]
  constructor
  · intro hv
    rcases mem_union.mp hv with h | h
    · obtain ⟨z, hz, -⟩ := anchor_halfR hpq h; exact hang_reachable hz
    · obtain ⟨z, hz, -⟩ := anchor_halfR (Ne.symm hpq) h; exact hang_reachable hz
  · intro hv
    obtain ⟨z, hz⟩ := hang_cover' hv
    rcases arc_cases p q z hpq with h | h | h | h
    · exact mem_union_left _ (hang_sub_halfR (Or.inl h) hz)
    · exact mem_union_right _ (hang_sub_halfR (Or.inl h) hz)
    · exact mem_union_left _ (hang_sub_halfR (Or.inr h) hz)
    · exact mem_union_right _ (hang_sub_halfR (Or.inr h) hz)

/-- **The marks of the two halves of an edge add up to those of its component.** -/
theorem marks_halves {i : ι} {p q : Fin (D.n i)} (hpq : (D.H i).Adj p q) :
    D.marksR (D.halfR i p q) + D.marksR (D.halfR i q p) = D.marksR (compR G (D.ψ i p)) := by
  rw [← marksR_union (sep_halves hpq), halves_union hpq.ne]

variable (D) in
/-- **The marks of a component** are the even faces of its blocks. -/
theorem marksR_comp (v₀ : V) :
    D.marksR (compR G v₀) = ∑ i ∈ univ.filter (fun i => G.Reachable v₀ (D.ψ i 0)),
      numEvenFaces (D.H i) := by
  classical
  have h : (D.facesR (compR G v₀)).filter (fun f => Even f.2.card) =
      (univ.filter (fun i => G.Reachable v₀ (D.ψ i 0))).sigma fun i =>
        univ.filter fun F : Finset (Fin (D.n i)) => IsFace (D.H i) F ∧ Even F.card := by
    ext ⟨i, F⟩
    simp only [mem_filter, mem_facesR, mem_sigma, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hF, hs⟩, hev⟩
      obtain ⟨a₀, ha₀⟩ : F.Nonempty := card_pos.mp (by have h3 : 3 ≤ F.card := hF.1; omega)
      have := mem_compR.mp (hs (mem_fimg.mpr ⟨a₀, ha₀, rfl⟩))
      exact ⟨this.trans (block_reachable a₀ 0), hF, hev⟩
    · rintro ⟨hr, hF, hev⟩
      refine ⟨⟨hF, fun v hv => ?_⟩, hev⟩
      obtain ⟨a, -, rfl⟩ := mem_fimg.mp hv
      exact mem_compR.mpr (hr.trans (block_reachable 0 a))
  unfold marksR
  rw [h, card_sigma]
  unfold numEvenFaces
  rfl

end BlockDecomp

end Outerplanar
