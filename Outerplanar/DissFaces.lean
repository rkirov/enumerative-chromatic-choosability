/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Dissection

/-!
# Faces of a polygon dissection

For a polygon dissection `H` on `Fin n` (`IsDissection`, `Outerplanar/Dissection.lean`), the
bounded faces are the vertex sets `F` of at least three vertices in which two vertices are
adjacent exactly when one of the two arcs of the polygon between them contains no other vertex
of `F` (`IsFace`). The definition only uses differences in `Fin n`, so it is invariant under
rotations of the polygon (`isFace_rot`), as is `IsDissection` (`isDissection_rot`).

* `face_sep` — a face with a vertex strictly inside a chord lies on that side of the chord.
* `face_eq_of_subset` — a face contained in a face is equal to it.
* `rootFace` — the face of the sub-polygon `[a, b]` on the chord `(a, b)`: the vertices of
  `[a, b]` not strictly inside a shorter chord. `rootFace_isFace`, and the faces in `[a, b]` are
  the root face and the faces in the intervals between consecutive vertices of the root face
  (`faces_decomp`).
* `marks H a b` — the number of even faces in `[a, b]`; `marks_decomp`.

Part of the formalization of the six-even-face theorem (research note
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`).
-/

namespace Outerplanar

open Finset

variable {n : ℕ}

/-! ### Faces -/

/-- Going up from `x`, the next vertex of `F` is `y`. -/
def CycNext (F : Finset (Fin n)) (x y : Fin n) : Prop :=
  ∀ z ∈ F, z ≠ x → z ≠ y → (y - x).val ≤ (z - x).val

/-- **A face** of a polygon dissection: at least three vertices, two of which are adjacent
exactly when one of the two arcs between them contains no other vertex of the set. -/
def IsFace (H : SimpleGraph (Fin n)) (F : Finset (Fin n)) : Prop :=
  3 ≤ F.card ∧ ∀ x ∈ F, ∀ y ∈ F, x ≠ y → (H.Adj x y ↔ CycNext F x y ∨ CycNext F y x)

theorem sub_val_le {a b : Fin n} (h : b ≤ a) : (a - b).val = a.val - b.val :=
  Fin.coe_sub_iff_le.mpr h

theorem sub_val_lt {a b : Fin n} (h : a < b) : (a - b).val = n + a.val - b.val :=
  Fin.coe_sub_iff_lt.mpr h

/-- The linear form of `CycNext` for `x < y`: nothing of `F` strictly between. -/
theorem cycNext_lt {F : Finset (Fin n)} {x y : Fin n} (hxy : x < y) :
    CycNext F x y ↔ ∀ z ∈ F, ¬ (x < z ∧ z < y) := by
  have hxy' : x.val < y.val := hxy
  constructor
  · intro h z hz ⟨h1, h2⟩
    have h1' : x.val < z.val := h1
    have h2' : z.val < y.val := h2
    have := h z hz (ne_of_gt h1) (ne_of_lt h2)
    rw [sub_val_le hxy.le, sub_val_le h1.le] at this
    omega
  · intro h z hz hzx hzy
    rw [sub_val_le hxy.le]
    have hz' := z.isLt
    by_cases hle : x ≤ z
    · rw [sub_val_le hle]
      have hle' : x.val ≤ z.val := hle
      have hne : x.val ≠ z.val := fun e => hzx (Fin.ext e.symm)
      have : ¬ (z.val < y.val) := fun h' =>
        h z hz ⟨Fin.lt_def.mpr (lt_of_le_of_ne hle' hne), h'⟩
      omega
    · rw [sub_val_lt (not_le.mp hle)]
      omega

/-- The linear form of `CycNext` for `x < y`, going round: everything of `F` is between. -/
theorem cycNext_gt {F : Finset (Fin n)} {x y : Fin n} (hxy : x < y) :
    CycNext F y x ↔ ∀ z ∈ F, z ≠ x → z ≠ y → x < z ∧ z < y := by
  have hxy' : x.val < y.val := hxy
  constructor
  · intro h z hz hzx hzy
    have := h z hz hzy hzx
    rw [sub_val_lt hxy] at this
    have hz' := z.isLt
    have hne1 : z.val ≠ x.val := fun e => hzx (Fin.ext e)
    by_cases hle : y ≤ z
    · rw [sub_val_le hle] at this
      have : y.val ≤ z.val := hle
      omega
    · rw [sub_val_lt (not_le.mp hle)] at this
      have : z.val < y.val := not_le.mp hle
      exact ⟨by show x.val < z.val; omega, not_le.mp hle⟩
  · intro h z hz hzy hzx
    obtain ⟨h1, h2⟩ := h z hz hzx hzy
    have h1' : x.val < z.val := h1
    have h2' : z.val < y.val := h2
    rw [sub_val_lt hxy, sub_val_lt h2]
    omega

/-- The linear form of the face condition. -/
theorem IsFace.adj_iff {H : SimpleGraph (Fin n)} {F : Finset (Fin n)} (hF : IsFace H F)
    {x y : Fin n} (hx : x ∈ F) (hy : y ∈ F) (hxy : x < y) :
    H.Adj x y ↔ (∀ z ∈ F, ¬ (x < z ∧ z < y)) ∨ (∀ z ∈ F, x ≤ z ∧ z ≤ y) := by
  rw [hF.2 x hx y hy (ne_of_lt hxy), cycNext_lt hxy, cycNext_gt hxy]
  refine or_congr Iff.rfl ⟨fun h z hz => ?_, fun h z hz hzx hzy => ?_⟩
  · by_cases h1 : z = x
    · rw [h1]; exact ⟨le_rfl, hxy.le⟩
    · by_cases h2 : z = y
      · rw [h2]; exact ⟨hxy.le, le_rfl⟩
      · exact ⟨(h z hz h1 h2).1.le, (h z hz h1 h2).2.le⟩
  · obtain ⟨h1, h2⟩ := h z hz
    exact ⟨lt_of_le_of_ne h1 (Ne.symm hzx), lt_of_le_of_ne h2 hzy⟩

/-! ### Rotations -/

section Rot

variable [NeZero n]

/-- The rotation of the polygon by `r`. -/
def rot (r : Fin n) : Fin n → Fin n := fun i => i + r

omit [NeZero n] in
theorem rot_injective (r : Fin n) : Function.Injective (rot r) := add_left_injective r

theorem cycNext_rot (r : Fin n) (F : Finset (Fin n)) (x y : Fin n) :
    CycNext (F.image (rot r)) (rot r x) (rot r y) ↔ CycNext F x y := by
  unfold CycNext rot
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp only [add_sub_add_right_eq_sub]
  refine forall₂_congr fun z _ => ?_
  constructor
  · intro h hzx hzy
    exact h (fun e => hzx (add_right_cancel e)) fun e => hzy (add_right_cancel e)
  · intro h hzx hzy
    exact h (fun e => hzx (by rw [e])) fun e => hzy (by rw [e])

/-- **Faces are invariant under rotation.** -/
theorem isFace_rot (G : SimpleGraph (Fin n)) (r : Fin n) (F : Finset (Fin n)) :
    IsFace (G.comap (rot r)) F ↔ IsFace G (F.image (rot r)) := by
  unfold IsFace
  rw [card_image_of_injective _ (rot_injective r)]
  refine and_congr Iff.rfl ⟨fun h x hx y hy hxy => ?_, fun h x hx y hy hxy => ?_⟩
  · obtain ⟨x', hx', rfl⟩ := mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_image.mp hy
    have hne : x' ≠ y' := fun e => hxy (by rw [e])
    rw [cycNext_rot, cycNext_rot]
    exact h x' hx' y' hy' hne
  · have := h (rot r x) (mem_image_of_mem _ hx) (rot r y) (mem_image_of_mem _ hy)
      (fun e => hxy (rot_injective r e))
    rw [cycNext_rot, cycNext_rot] at this
    exact this

omit [NeZero n] in
/-- **Rotations of a polygon dissection are polygon dissections.** -/
theorem isDissection_rot {G : SimpleGraph (Fin n)} (hG : IsDissection G) (r : Fin n) :
    IsDissection (G.comap (rot r)) := by
  obtain ⟨hcyc, hwrap, hcross⟩ := hG
  have hr := r.isLt
  -- the vertices `i` and `i + 1` around the cycle are adjacent
  have hstep : ∀ i j : Fin n, i ≠ j → (j.val = i.val + 1 ∨ (i.val + 1 = n ∧ j.val = 0)) →
      G.Adj i j := by
    intro i j hne h
    rcases h with h | ⟨h1, h2⟩
    · exact hcyc i j h.symm
    · exact (hwrap j i h2 h1 (Ne.symm hne)).symm
  refine ⟨fun i j hij => ?_, fun i j hi hj hne => ?_, fun a b c d hab hbc hcd hac hbd => ?_⟩
  · show G.Adj (i + r) (j + r)
    have hne : i + r ≠ j + r := fun e => by
      have := congrArg Fin.val (add_right_cancel e); omega
    apply hstep _ _ hne
    rw [Fin.val_add_eq_ite, Fin.val_add_eq_ite]
    split_ifs <;> omega
  · show G.Adj (i + r) (j + r)
    have hne' : j + r ≠ i + r := fun e => hne (add_right_cancel e).symm
    refine SimpleGraph.Adj.symm ?_
    apply hstep _ _ hne'
    rw [Fin.val_add_eq_ite, Fin.val_add_eq_ite]
    split_ifs <;> omega
  · change G.Adj (a + r) (c + r) at hac
    change G.Adj (b + r) (d + r) at hbd
    have hab' : a.val < b.val := hab
    have hbc' : b.val < c.val := hbc
    have hcd' : c.val < d.val := hcd
    have hlt : ∀ x y : Fin n, x.val < y.val → x < y := fun x y h => h
    have ea := Fin.val_add_eq_ite a r
    have eb := Fin.val_add_eq_ite b r
    have ec := Fin.val_add_eq_ite c r
    have ed := Fin.val_add_eq_ite d r
    by_cases hd : n ≤ d.val + r.val
    · by_cases hc : n ≤ c.val + r.val
      · by_cases hb : n ≤ b.val + r.val
        · by_cases ha : n ≤ a.val + r.val
          · simp only [ha, ↓reduceIte] at ea; simp only [hb, ↓reduceIte] at eb; simp only [hc, ↓reduceIte] at ec
            simp only [hd, ↓reduceIte] at ed
            exact hcross _ _ _ _ (hlt _ _ (by omega)) (hlt _ _ (by omega)) (hlt _ _ (by omega))
              hac hbd
          · simp only [ha, ↓reduceIte] at ea; simp only [hb, ↓reduceIte] at eb; simp only [hc, ↓reduceIte] at ec
            simp only [hd, ↓reduceIte] at ed
            exact hcross _ _ _ _ (hlt (b + r) (c + r) (by omega)) (hlt _ (d + r) (by omega))
              (hlt _ (a + r) (by omega)) hbd hac.symm
        · simp only [show ¬ n ≤ a.val + r.val by omega, ↓reduceIte] at ea; simp only [hb, ↓reduceIte] at eb
          simp only [hc, ↓reduceIte] at ec; simp only [hd, ↓reduceIte] at ed
          exact hcross _ _ _ _ (hlt (c + r) (d + r) (by omega)) (hlt _ (a + r) (by omega))
            (hlt _ (b + r) (by omega)) hac.symm hbd.symm
      · simp only [show ¬ n ≤ a.val + r.val by omega, ↓reduceIte] at ea
        simp only [show ¬ n ≤ b.val + r.val by omega, ↓reduceIte] at eb
        simp only [hc, ↓reduceIte] at ec; simp only [hd, ↓reduceIte] at ed
        exact hcross _ _ _ _ (hlt (d + r) (a + r) (by omega)) (hlt _ (b + r) (by omega))
          (hlt _ (c + r) (by omega)) hbd.symm hac
    · simp only [show ¬ n ≤ a.val + r.val by omega, ↓reduceIte] at ea
      simp only [show ¬ n ≤ b.val + r.val by omega, ↓reduceIte] at eb
      simp only [show ¬ n ≤ c.val + r.val by omega, ↓reduceIte] at ec; simp only [hd, ↓reduceIte] at ed
      exact hcross _ _ _ _ (hlt _ _ (by omega)) (hlt _ _ (by omega)) (hlt _ _ (by omega)) hac
        hbd

end Rot

/-! ### Chords -/

section Chords

variable {H : SimpleGraph (Fin n)}

/-- An edge from strictly inside a chord stays on its side. -/
theorem nc_inside (hH : IsDissection H) {a b x y : Fin n} (hxa : a < x) (hxb : x < b)
    (hab : H.Adj a b) (hxy : H.Adj x y) : a ≤ y ∧ y ≤ b := by
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hH.2.2 y a x b (not_le.mp h) hxa hxb hxy.symm hab
  · by_contra h
    exact hH.2.2 a x b y hxa hxb (not_le.mp h) hab hxy

end Chords

/-- A face from its linear form. -/
theorem isFace_of_linear {H : SimpleGraph (Fin n)} {F : Finset (Fin n)} (h3 : 3 ≤ F.card)
    (h : ∀ x ∈ F, ∀ y ∈ F, x < y →
      (H.Adj x y ↔ (∀ z ∈ F, ¬ (x < z ∧ z < y)) ∨ (∀ z ∈ F, x ≤ z ∧ z ≤ y))) : IsFace H F := by
  have key : ∀ x ∈ F, ∀ y ∈ F, x < y → (H.Adj x y ↔ CycNext F x y ∨ CycNext F y x) := by
    intro x hx y hy hxy
    rw [h x hx y hy hxy, cycNext_lt hxy, cycNext_gt hxy]
    refine or_congr Iff.rfl ⟨fun h' z hz hzx hzy => ?_, fun h' z hz => ?_⟩
    · obtain ⟨h1, h2⟩ := h' z hz
      exact ⟨lt_of_le_of_ne h1 (Ne.symm hzx), lt_of_le_of_ne h2 hzy⟩
    · by_cases h1 : z = x
      · rw [h1]; exact ⟨le_rfl, hxy.le⟩
      · by_cases h2 : z = y
        · rw [h2]; exact ⟨hxy.le, le_rfl⟩
        · exact ⟨(h' z hz h1 h2).1.le, (h' z hz h1 h2).2.le⟩
  refine ⟨h3, fun x hx y hy hxy => ?_⟩
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact key x hx y hy hlt
  · rw [H.adj_comm, or_comm]
    exact key y hy x hx hgt

/-- A set of at least three elements has one strictly between its least and greatest. -/
theorem exists_mid {F : Finset (Fin n)} (h3 : 3 ≤ F.card) :
    ∃ w ∈ F, F.min' (card_pos.mp (by omega)) < w ∧ w < F.max' (card_pos.mp (by omega)) := by
  set hne := card_pos.mp (by omega : 0 < F.card)
  have hm := F.min'_mem hne
  have hM := F.max'_mem hne
  have hmM : F.max' hne ≠ F.min' hne := by
    intro e
    have := Finset.card_le_one.mpr fun x hx y hy => by
      have h1 := F.min'_le x hx
      have h2 := F.le_max' x hx
      have h3 := F.min'_le y hy
      have h4 := F.le_max' y hy
      rw [e] at h2 h4
      exact le_antisymm (h2.trans h3) (h4.trans h1)
    omega
  have hc : 1 ≤ ((F.erase (F.min' hne)).erase (F.max' hne)).card := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨hmM, hM⟩), card_erase_of_mem hm]
    omega
  obtain ⟨w, hw⟩ := card_pos.mp hc
  obtain ⟨hw1, hw2⟩ := mem_erase.mp hw
  obtain ⟨hw3, hw4⟩ := mem_erase.mp hw2
  exact ⟨w, hw4, lt_of_le_of_ne (F.min'_le w hw4) (Ne.symm hw3),
    lt_of_le_of_ne (F.le_max' w hw4) hw1⟩

section Faces

variable {H : SimpleGraph (Fin n)}

/-- **A face with a vertex strictly inside a chord lies on that side of the chord.** -/
theorem face_sep (hH : IsDissection H) {F : Finset (Fin n)} (hF : IsFace H F) {c d : Fin n}
    (hcd : c < d) (hadj : H.Adj c d) {x : Fin n} (hx : x ∈ F) (hcx : c < x) (hxd : x < d) :
    ∀ y ∈ F, c ≤ y ∧ y ≤ d := by
  classical
  set I := F.filter fun z => c < z ∧ z < d with hI
  have hIne : I.Nonempty := ⟨x, mem_filter.mpr ⟨hx, hcx, hxd⟩⟩
  have hpI := mem_filter.mp (I.min'_mem hIne)
  have hqI := mem_filter.mp (I.max'_mem hIne)
  set p := I.min' hIne
  set q := I.max' hIne
  -- below the least vertex inside: the chord's end `c`
  have step1 : (∃ z ∈ F, z < p) → c ∈ F := by
    rintro ⟨z₀, hz₀, hz₀p⟩
    set L := F.filter fun z => z < p
    have hLne : L.Nonempty := ⟨z₀, mem_filter.mpr ⟨hz₀, hz₀p⟩⟩
    have hp' := mem_filter.mp (L.max'_mem hLne)
    have hcons : ∀ w ∈ F, ¬ (L.max' hLne < w ∧ w < p) := fun w hw ⟨h1, h2⟩ =>
      not_lt.mpr (L.le_max' w (mem_filter.mpr ⟨hw, h2⟩)) h1
    have hadj' := (hF.adj_iff hp'.1 hpI.1 hp'.2).mpr (Or.inl hcons)
    obtain ⟨h1, h2⟩ := nc_inside hH hpI.2.1 hpI.2.2 hadj hadj'.symm
    rcases h1.lt_or_eq with h | h
    · exact absurd (I.min'_le _ (mem_filter.mpr ⟨hp'.1, h, hp'.2.trans hpI.2.2⟩))
        (not_le.mpr hp'.2)
    · rw [h]; exact hp'.1
  have step2 : (∃ z ∈ F, q < z) → d ∈ F := by
    rintro ⟨z₀, hz₀, hz₀q⟩
    set U := F.filter fun z => q < z
    have hUne : U.Nonempty := ⟨z₀, mem_filter.mpr ⟨hz₀, hz₀q⟩⟩
    have hq' := mem_filter.mp (U.min'_mem hUne)
    have hcons : ∀ w ∈ F, ¬ (q < w ∧ w < U.min' hUne) := fun w hw ⟨h1, h2⟩ =>
      not_lt.mpr (U.min'_le w (mem_filter.mpr ⟨hw, h1⟩)) h2
    have hadj' := (hF.adj_iff hqI.1 hq'.1 hq'.2).mpr (Or.inl hcons)
    obtain ⟨h1, h2⟩ := nc_inside hH hqI.2.1 hqI.2.2 hadj hadj'
    rcases h2.lt_or_eq with h | h
    · exact absurd (I.le_max' _ (mem_filter.mpr ⟨hq'.1, hqI.2.1.trans hq'.2, h⟩))
        (not_le.mpr hq'.2)
    · rw [← h]; exact hq'.1
  -- both ends in the face contradict the face condition
  have both : c ∈ F → d ∈ F → (∃ y ∈ F, y < c ∨ d < y) → False := by
    rintro hc hd ⟨y, hy, hy'⟩
    rcases (hF.adj_iff hc hd hcd).mp hadj with h | h
    · exact h x hx ⟨hcx, hxd⟩
    · rcases hy' with h' | h'
      · exact not_le.mpr h' (h y hy).1
      · exact not_le.mpr h' (h y hy).2
  intro y hy
  by_contra hbad
  have hy' : y < c ∨ d < y := by
    by_contra h
    push Not at h
    exact hbad h
  have hFne : F.Nonempty := ⟨x, hx⟩
  rcases hy' with hyc | hdy
  · have hc := step1 ⟨y, hy, hyc.trans hpI.2.1⟩
    by_cases hup : ∃ z ∈ F, q < z
    · exact both hc (step2 hup) ⟨y, hy, Or.inl hyc⟩
    · -- `q` is the greatest vertex: the wrap edge from the least one
      push Not at hup
      have hqmax : F.max' hFne = q := le_antisymm (F.max'_le _ _ hup) (F.le_max' _ hqI.1)
      have hmin_lt : F.min' hFne < q := (F.min'_le y hy).trans_lt (hyc.trans hqI.2.1)
      have hadj' := (hF.adj_iff (F.min'_mem hFne) hqI.1 hmin_lt).mpr (Or.inr fun z hz =>
        ⟨F.min'_le z hz, hup z hz⟩)
      have := (nc_inside hH hqI.2.1 hqI.2.2 hadj hadj'.symm).1
      exact not_le.mpr ((F.min'_le y hy).trans_lt hyc) this
  · have hd := step2 ⟨y, hy, hqI.2.2.trans hdy⟩
    by_cases hdown : ∃ z ∈ F, z < p
    · exact both (step1 hdown) hd ⟨y, hy, Or.inr hdy⟩
    · push Not at hdown
      have hlt : p < F.max' hFne := hpI.2.2.trans (hdy.trans_le (F.le_max' y hy))
      have hadj' := (hF.adj_iff hpI.1 (F.max'_mem hFne) hlt).mpr (Or.inr fun z hz =>
        ⟨hdown z hz, F.le_max' z hz⟩)
      have := (nc_inside hH hpI.2.1 hpI.2.2 hadj hadj').2
      exact not_le.mpr (hdy.trans_le (F.le_max' y hy)) this

/-- **A face contained in a face is equal to it.** -/
theorem face_eq_of_subset {F F' : Finset (Fin n)} (hF : IsFace H F) (hF' : IsFace H F')
    (hsub : F ⊆ F') : F = F' := by
  classical
  by_contra hne
  obtain ⟨z, hz', hzF⟩ : ∃ z ∈ F', z ∉ F := by
    by_contra h
    push Not at h
    exact hne (Finset.Subset.antisymm hsub h)
  have hFne : F.Nonempty := card_pos.mp (by have := hF.1; omega)
  by_cases hdown : ∃ w ∈ F, w < z
  · by_cases hup : ∃ w ∈ F, z < w
    · set L := F.filter fun w => w < z
      set U := F.filter fun w => z < w
      have hLne : L.Nonempty := by obtain ⟨w, hw, h⟩ := hdown; exact ⟨w, mem_filter.mpr ⟨hw, h⟩⟩
      have hUne : U.Nonempty := by obtain ⟨w, hw, h⟩ := hup; exact ⟨w, mem_filter.mpr ⟨hw, h⟩⟩
      have hx := mem_filter.mp (L.max'_mem hLne)
      have hy := mem_filter.mp (U.min'_mem hUne)
      have hgap : ∀ w ∈ F, ¬ (L.max' hLne < w ∧ w < U.min' hUne) := by
        rintro w hw ⟨h1, h2⟩
        rcases lt_trichotomy w z with h | h | h
        · exact not_le.mpr h1 (L.le_max' w (mem_filter.mpr ⟨hw, h⟩))
        · exact hzF (h ▸ hw)
        · exact not_le.mpr h2 (U.min'_le w (mem_filter.mpr ⟨hw, h⟩))
      have hxy := hx.2.trans hy.2
      have hadj := (hF.adj_iff hx.1 hy.1 hxy).mpr (Or.inl hgap)
      rcases (hF'.adj_iff (hsub hx.1) (hsub hy.1) hxy).mp hadj with h | h
      · exact h z hz' ⟨hx.2, hy.2⟩
      · -- then `F` lies in `[x, y]` with nothing strictly inside: at most two vertices
        have hsub2 : F ⊆ {L.max' hLne, U.min' hUne} := by
          intro w hw
          obtain ⟨h1, h2⟩ := h w (hsub hw)
          rcases h1.lt_or_eq with h1 | h1
          · rcases h2.lt_or_eq with h2 | h2
            · exact absurd ⟨h1, h2⟩ (hgap w hw)
            · rw [h2]; simp
          · rw [← h1]; simp
        have := card_le_card hsub2
        have := card_insert_le (L.max' hLne) {U.min' hUne}
        simp at this
        have := hF.1
        omega
    · push Not at hup
      obtain ⟨w, hw, hw1, hw2⟩ := exists_mid hF.1
      have hlt := hw1.trans hw2
      have hadj := (hF.adj_iff (F.min'_mem hFne) (F.max'_mem hFne) hlt).mpr
        (Or.inr fun v hv => ⟨F.min'_le v hv, F.le_max' v hv⟩)
      rcases (hF'.adj_iff (hsub (F.min'_mem hFne)) (hsub (F.max'_mem hFne)) hlt).mp hadj with
        h | h
      · exact h w (hsub hw) ⟨hw1, hw2⟩
      · have hzmax : F.max' hFne < z := lt_of_le_of_ne (hup _ (F.max'_mem hFne))
          fun e => hzF (e ▸ F.max'_mem hFne)
        exact not_le.mpr hzmax (h z hz').2
  · push Not at hdown
    obtain ⟨w, hw, hw1, hw2⟩ := exists_mid hF.1
    have hlt := hw1.trans hw2
    have hadj := (hF.adj_iff (F.min'_mem hFne) (F.max'_mem hFne) hlt).mpr
      (Or.inr fun v hv => ⟨F.min'_le v hv, F.le_max' v hv⟩)
    rcases (hF'.adj_iff (hsub (F.min'_mem hFne)) (hsub (F.max'_mem hFne)) hlt).mp hadj with
      h | h
    · exact h w (hsub hw) ⟨hw1, hw2⟩
    · have hzmin : z < F.min' hFne := lt_of_le_of_ne (hdown _ (F.min'_mem hFne))
        fun e => hzF (e.symm ▸ F.min'_mem hFne)
      exact not_le.mpr hzmin (h z hz').1

end Faces

/-! ### The root face of an interval -/

section Root

variable {H : SimpleGraph (Fin n)}

/-- `x` is not strictly inside a chord of `[a, b]` other than `(a, b)` itself. -/
def Vis (H : SimpleGraph (Fin n)) (a b x : Fin n) : Prop :=
  ∀ y z, a ≤ y → y < x → x < z → z ≤ b → H.Adj y z → y = a ∧ z = b

open Classical in
/-- **The root face** of the sub-polygon `[a, b]` on the chord `(a, b)`. -/
noncomputable def rootFace (H : SimpleGraph (Fin n)) (a b : Fin n) : Finset (Fin n) :=
  univ.filter fun x => a ≤ x ∧ x ≤ b ∧ Vis H a b x

theorem mem_rootFace {a b x : Fin n} : x ∈ rootFace H a b ↔ a ≤ x ∧ x ≤ b ∧ Vis H a b x := by
  classical
  unfold rootFace
  simp only [mem_filter, mem_univ, true_and]

theorem left_mem_rootFace {a b : Fin n} (hab : a ≤ b) : a ∈ rootFace H a b :=
  mem_rootFace.mpr ⟨le_rfl, hab, fun _ _ hay hya _ _ _ => absurd hya (not_lt.mpr hay)⟩

theorem right_mem_rootFace {a b : Fin n} (hab : a ≤ b) : b ∈ rootFace H a b :=
  mem_rootFace.mpr ⟨hab, le_rfl, fun _ _ _ _ hbz hzb _ => absurd hbz (not_lt.mpr hzb)⟩

theorem rootFace_sub {a b : Fin n} : rootFace H a b ⊆ Icc a b := fun x hx => by
  obtain ⟨h1, h2, -⟩ := mem_rootFace.mp hx
  exact mem_Icc.mpr ⟨h1, h2⟩

/-- **The next vertex of the root face** is adjacent, with nothing of the root face between. -/
theorem rootFace_next (hH : IsDissection H) {a b : Fin n} (hadj : H.Adj a b) {x : Fin n}
    (hx : x ∈ rootFace H a b) (hxb : x < b) :
    ∃ x' ∈ rootFace H a b, x < x' ∧ H.Adj x x' ∧ (∀ w ∈ rootFace H a b, ¬ (x < w ∧ w < x')) ∧
      (x = a → x' = b → b.val = a.val + 1) := by
  classical
  obtain ⟨hax, hxb', hvis⟩ := mem_rootFace.mp hx
  set C := univ.filter fun z => x < z ∧ z ≤ b ∧ H.Adj x z ∧ ¬ (x = a ∧ z = b) with hC
  by_cases hCne : C.Nonempty
  · have hm := mem_filter.mp (C.max'_mem hCne)
    obtain ⟨-, h1, h2, h3, h4⟩ := hm
    set x' := C.max' hCne
    have hmem : x' ∈ rootFace H a b := by
      refine mem_rootFace.mpr ⟨hax.trans h1.le, h2, fun y z hay hyx' hx'z hzb hyz => ?_⟩
      rcases lt_trichotomy y x with hyx | rfl | hxy
      · exact hvis y z hay hyx (h1.trans hx'z) hzb hyz
      · by_contra hne
        exact not_le.mpr hx'z (C.le_max' z (mem_filter.mpr ⟨mem_univ _, h1.trans hx'z, hzb,
          hyz, hne⟩))
      · exact absurd hyz (hH.2.2 x y x' z hxy hyx' hx'z h3)
    refine ⟨x', hmem, h1, h3, fun w hw ⟨hw1, hw2⟩ => ?_, fun ha hb => absurd ⟨ha, hb⟩ h4⟩
    obtain ⟨-, -, hvw⟩ := mem_rootFace.mp hw
    exact h4 (hvw x x' hax hw1 hw2 h2 h3)
  · -- no chord from `x` inside: then `x = a` and `b = a + 1`
    have hb := b.isLt
    have hxb2 : x.val + 1 < n := by have : x.val < b.val := hxb; omega
    set y : Fin n := ⟨x.val + 1, hxb2⟩
    have hy : H.Adj x y := hH.1 x y rfl
    have hyb : y ≤ b := by show x.val + 1 ≤ b.val; have : x.val < b.val := hxb; omega
    have hxy : x < y := by show x.val < x.val + 1; omega
    have hab' : x = a ∧ y = b := by
      by_contra h
      exact hCne ⟨y, mem_filter.mpr ⟨mem_univ _, hxy, hyb, hy, h⟩⟩
    obtain ⟨rfl, rfl⟩ := hab'
    refine ⟨y, right_mem_rootFace hxy.le, hxy, hy, fun w _ ⟨hw1, hw2⟩ => ?_, fun _ _ => rfl⟩
    have h1 : x.val < w.val := hw1
    have h2 : w.val < x.val + 1 := hw2
    omega

theorem rootFace_card (hH : IsDissection H) {a b : Fin n} (hadj : H.Adj a b)
    (h2 : a.val + 2 ≤ b.val) : 3 ≤ (rootFace H a b).card := by
  have hab : a < b := by show a.val < b.val; omega
  obtain ⟨x', hx', hax', -, -, hne⟩ := rootFace_next hH hadj (left_mem_rootFace hab.le) hab
  have hx'b : x' ≠ b := fun e => by have := hne rfl e; omega
  have hsub : ({a, x', b} : Finset (Fin n)) ⊆ rootFace H a b := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact left_mem_rootFace hab.le
    · exact hx'
    · exact right_mem_rootFace hab.le
  have hcard : ({a, x', b} : Finset (Fin n)).card = 3 := by
    rw [card_insert_of_notMem (by simp [ne_of_lt hax', ne_of_lt hab]), card_pair hx'b]
  exact hcard ▸ card_le_card hsub

/-- The adjacency on the root face, in linear form. -/
theorem rootFace_adj (hH : IsDissection H) {a b : Fin n} (hab : a < b) (hadj : H.Adj a b)
    {x y : Fin n} (hx : x ∈ rootFace H a b) (hy : y ∈ rootFace H a b) (hxy : x < y) :
    H.Adj x y ↔ (∀ z ∈ rootFace H a b, ¬ (x < z ∧ z < y)) ∨
      (∀ z ∈ rootFace H a b, x ≤ z ∧ z ≤ y) := by
  obtain ⟨hax, -, -⟩ := mem_rootFace.mp hx
  obtain ⟨-, hyb, -⟩ := mem_rootFace.mp hy
  constructor
  · intro h
    by_cases hend : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := hend
      exact Or.inr fun z hz => ⟨(mem_rootFace.mp hz).1, (mem_rootFace.mp hz).2.1⟩
    · exact Or.inl fun w hw ⟨h1, h2⟩ => hend ((mem_rootFace.mp hw).2.2 x y hax h1 h2 hyb h)
  · rintro (h | h)
    · obtain ⟨x', hx', hxx', hadj', hgap, -⟩ := rootFace_next hH hadj hx (hxy.trans_le hyb)
      have e : x' = y := by
        rcases lt_trichotomy x' y with h1 | h1 | h1
        · exact absurd ⟨hxx', h1⟩ (h x' hx')
        · exact h1
        · exact absurd ⟨hxy, h1⟩ (hgap y hy)
      exact e ▸ hadj'
    · have e1 : x = a := le_antisymm (h a (left_mem_rootFace hab.le)).1 hax
      have e2 : y = b := le_antisymm hyb (h b (right_mem_rootFace hab.le)).2
      rw [e1, e2]; exact hadj

/-- **The root face is a face.** -/
theorem rootFace_isFace (hH : IsDissection H) {a b : Fin n} (hadj : H.Adj a b)
    (h2 : a.val + 2 ≤ b.val) : IsFace H (rootFace H a b) := by
  have hab : a < b := by show a.val < b.val; omega
  exact isFace_of_linear (rootFace_card hH hadj h2) fun x hx y hy hxy =>
    rootFace_adj hH hab hadj hx hy hxy

/-- **Every other vertex of `[a, b]` is strictly inside a chord between two consecutive vertices
of the root face.** -/
theorem rootFace_cover (hH : IsDissection H) {a b : Fin n} (hab : a < b) (hadj : H.Adj a b)
    {w : Fin n} (haw : a ≤ w) (hwb : w ≤ b) (hw : w ∉ rootFace H a b) :
    ∃ f ∈ rootFace H a b, ∃ f' ∈ rootFace H a b, f < w ∧ w < f' ∧
      (∀ z ∈ rootFace H a b, ¬ (f < z ∧ z < f')) ∧ H.Adj f f' := by
  classical
  set R := rootFace H a b
  have haw' : a < w := lt_of_le_of_ne haw fun e => hw (e ▸ left_mem_rootFace hab.le)
  have hwb' : w < b := lt_of_le_of_ne hwb fun e => hw (e.symm ▸ right_mem_rootFace hab.le)
  set L := R.filter fun z => z < w
  set U := R.filter fun z => w < z
  have hLne : L.Nonempty := ⟨a, mem_filter.mpr ⟨left_mem_rootFace hab.le, haw'⟩⟩
  have hUne : U.Nonempty := ⟨b, mem_filter.mpr ⟨right_mem_rootFace hab.le, hwb'⟩⟩
  have hf := mem_filter.mp (L.max'_mem hLne)
  have hf' := mem_filter.mp (U.min'_mem hUne)
  have hgap : ∀ z ∈ R, ¬ (L.max' hLne < z ∧ z < U.min' hUne) := by
    rintro z hz ⟨h1, h2⟩
    rcases lt_trichotomy z w with h | h | h
    · exact not_le.mpr h1 (L.le_max' z (mem_filter.mpr ⟨hz, h⟩))
    · exact hw (h ▸ hz)
    · exact not_le.mpr h2 (U.min'_le z (mem_filter.mpr ⟨hz, h⟩))
  exact ⟨_, hf.1, _, hf'.1, hf.2, hf'.2, hgap,
    (rootFace_adj hH hab hadj hf.1 hf'.1 (hf.2.trans hf'.2)).mpr (Or.inl hgap)⟩

/-- The root face in increasing order. -/
theorem rootFace_enum (hH : IsDissection H) {a b : Fin n} (hadj : H.Adj a b)
    (h2 : a.val + 2 ≤ b.val) :
    ∃ m : ℕ, ∃ r : Fin (m + 2) → Fin n, 1 ≤ m ∧ (rootFace H a b).card = m + 2 ∧ StrictMono r ∧
      (∀ i, r i ∈ rootFace H a b) ∧ (∀ x ∈ rootFace H a b, ∃ i, r i = x) ∧ r 0 = a ∧
      r (Fin.last (m + 1)) = b := by
  have hab : a < b := by show a.val < b.val; omega
  have hc := rootFace_card hH hadj h2
  obtain ⟨m, hm⟩ : ∃ m, (rootFace H a b).card = m + 2 := ⟨(rootFace H a b).card - 2, by omega⟩
  set e := (rootFace H a b).orderEmbOfFin hm
  have hmem : ∀ i, e i ∈ rootFace H a b := fun i => (rootFace H a b).orderEmbOfFin_mem hm i
  have hsurj : ∀ x ∈ rootFace H a b, ∃ i, e i = x := fun x hx => by
    have h : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin (rootFace H a b) hm]; exact hx
    exact h
  have hmono : StrictMono e := e.strictMono
  have h0 : e 0 = a := by
    obtain ⟨i, hi⟩ := hsurj a (left_mem_rootFace hab.le)
    refine le_antisymm ?_ (mem_rootFace.mp (hmem 0)).1
    rw [← hi]; exact hmono.monotone (Fin.zero_le i)
  have hl : e (Fin.last (m + 1)) = b := by
    obtain ⟨i, hi⟩ := hsurj b (right_mem_rootFace hab.le)
    refine le_antisymm (mem_rootFace.mp (hmem _)).2.1 ?_
    rw [← hi]; exact hmono.monotone (Fin.le_last i)
  exact ⟨m, e, by omega, hm, hmono, hmem, hsurj, h0, hl⟩

end Root

/-! ### Faces in an interval, and the marks -/

section Marks

variable {H : SimpleGraph (Fin n)}

open Classical in
/-- The faces inside `[a, b]`. -/
noncomputable def facesIn (H : SimpleGraph (Fin n)) (a b : Fin n) : Finset (Finset (Fin n)) :=
  univ.filter fun F => IsFace H F ∧ F ⊆ Icc a b

theorem mem_facesIn {a b : Fin n} {F : Finset (Fin n)} :
    F ∈ facesIn H a b ↔ IsFace H F ∧ F ⊆ Icc a b := by
  classical
  unfold facesIn
  simp only [mem_filter, mem_univ, true_and]

open Classical in
/-- **The marks of `[a, b]`**: the number of even faces inside. -/
noncomputable def marks (H : SimpleGraph (Fin n)) (a b : Fin n) : ℕ :=
  ((facesIn H a b).filter fun F => Even F.card).card

/-- A square inside `[a, b]`. -/
def sqIn (H : SimpleGraph (Fin n)) (a b : Fin n) : Prop := ∃ F ∈ facesIn H a b, F.card = 4

theorem facesIn_mono {a b a' b' : Fin n} (h1 : a ≤ a') (h2 : b' ≤ b) :
    facesIn H a' b' ⊆ facesIn H a b := fun F hF => by
  obtain ⟨hF, hsub⟩ := mem_facesIn.mp hF
  refine mem_facesIn.mpr ⟨hF, fun x hx => ?_⟩
  obtain ⟨h3, h4⟩ := mem_Icc.mp (hsub hx)
  exact mem_Icc.mpr ⟨h1.trans h3, h4.trans h2⟩

/-- A set inside an interval with nothing strictly between its ends has at most two elements. -/
theorem card_le_two_of_gap {F : Finset (Fin n)} {a b : Fin n} (hsub : F ⊆ Icc a b)
    (hgap : ∀ z ∈ F, ¬ (a < z ∧ z < b)) : F.card ≤ 2 := by
  have : F ⊆ {a, b} := by
    intro z hz
    obtain ⟨h1, h2⟩ := mem_Icc.mp (hsub hz)
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact absurd ⟨h1, h2⟩ (hgap z hz)
      · rw [h2]; simp
    · rw [← h1]; simp
  exact (card_le_card this).trans (card_insert_le _ _)

theorem facesIn_edge {a b : Fin n} (h : b.val ≤ a.val + 1) : facesIn H a b = ∅ := by
  ext F
  simp only [Finset.notMem_empty, iff_false]
  intro hF
  obtain ⟨hF, hsub⟩ := mem_facesIn.mp hF
  have := card_le_two_of_gap hsub fun z _ ⟨h1, h2⟩ => by
    have : a.val < z.val := h1
    have : z.val < b.val := h2
    omega
  have := hF.1
  omega

theorem marks_edge {a b : Fin n} (h : b.val ≤ a.val + 1) : marks H a b = 0 := by
  classical
  unfold marks
  rw [facesIn_edge h]
  rfl

/-- The facts on the consecutive vertices of the root face that are used below. -/
structure RootEnum (H : SimpleGraph (Fin n)) (a b : Fin n) (m : ℕ) (r : Fin (m + 2) → Fin n) :
    Prop where
  one_le : 1 ≤ m
  card : (rootFace H a b).card = m + 2
  mono : StrictMono r
  mem : ∀ i, r i ∈ rootFace H a b
  surj : ∀ x ∈ rootFace H a b, ∃ i, r i = x
  first : r 0 = a
  last : r (Fin.last (m + 1)) = b

theorem exists_rootEnum (hH : IsDissection H) {a b : Fin n} (hadj : H.Adj a b)
    (h2 : a.val + 2 ≤ b.val) : ∃ m r, RootEnum H a b m r := by
  obtain ⟨m, r, h1, h2', h3, h4, h5, h6, h7⟩ := rootFace_enum hH hadj h2
  exact ⟨m, r, ⟨h1, h2', h3, h4, h5, h6, h7⟩⟩

section Enum

variable {a b : Fin n} {m : ℕ} {r : Fin (m + 2) → Fin n}

theorem RootEnum.gap (he : RootEnum H a b m r) (i : Fin (m + 1)) :
    ∀ z ∈ rootFace H a b, ¬ (r i.castSucc < z ∧ z < r i.succ) := by
  rintro z hz ⟨h1, h2⟩
  obtain ⟨j, rfl⟩ := he.surj z hz
  have h1' := he.mono.lt_iff_lt.mp h1
  have h2' := he.mono.lt_iff_lt.mp h2
  have : i.val < j.val := h1'
  have : j.val < i.val + 1 := h2'
  omega

theorem RootEnum.lt (he : RootEnum H a b m r) (i : Fin (m + 1)) : r i.castSucc < r i.succ :=
  he.mono Fin.castSucc_lt_succ

theorem RootEnum.adj (hH : IsDissection H) (hadj : H.Adj a b) (he : RootEnum H a b m r)
    (hab : a < b) (i : Fin (m + 1)) : H.Adj (r i.castSucc) (r i.succ) :=
  (rootFace_adj hH hab hadj (he.mem _) (he.mem _) (he.lt i)).mpr (Or.inl (he.gap i))

theorem RootEnum.ge (he : RootEnum H a b m r) (i : Fin (m + 2)) : a ≤ r i :=
  he.first ▸ he.mono.monotone (Fin.zero_le i)

theorem RootEnum.le (he : RootEnum H a b m r) (i : Fin (m + 2)) : r i ≤ b :=
  he.last ▸ he.mono.monotone (Fin.le_last i)

/-- The children are shorter than the parent. -/
theorem RootEnum.width (he : RootEnum H a b m r) (i : Fin (m + 1)) :
    (r i.succ).val - (r i.castSucc).val < b.val - a.val := by
  have h1 : a.val ≤ (r i.castSucc).val := he.ge _
  have h2 : (r i.succ).val ≤ b.val := he.le _
  have h3 : (r i.castSucc).val < (r i.succ).val := he.lt i
  have hm := he.one_le
  by_contra h
  have e1 : (r i.castSucc).val = a.val := by omega
  have e2 : (r i.succ).val = b.val := by omega
  have i0 : i.castSucc = 0 := he.mono.injective (Fin.ext (by rw [e1, he.first]))
  have i1 : i.succ = Fin.last (m + 1) := he.mono.injective (Fin.ext (by rw [e2, he.last]))
  have v0 : i.val = 0 := by have := congrArg Fin.val i0; simpa using this
  have v1 : i.val + 1 = m + 1 := by have := congrArg Fin.val i1; simpa using this
  omega

/-- A pair of consecutive vertices of the root face is a pair of the enumeration. -/
theorem RootEnum.consec (he : RootEnum H a b m r) {f f' : Fin n} (hf : f ∈ rootFace H a b)
    (hf' : f' ∈ rootFace H a b) (hff : f < f') (hgap : ∀ z ∈ rootFace H a b, ¬ (f < z ∧ z < f')) :
    ∃ i : Fin (m + 1), r i.castSucc = f ∧ r i.succ = f' := by
  obtain ⟨k, rfl⟩ := he.surj f hf
  obtain ⟨l, rfl⟩ := he.surj f' hf'
  have hkl : k < l := he.mono.lt_iff_lt.mp hff
  have hl : l.val = k.val + 1 := by
    by_contra h
    have hk1 : k.val + 1 < m + 2 := by have := l.isLt; have : k.val < l.val := hkl; omega
    have hlt1 : k < ⟨k.val + 1, hk1⟩ := by show k.val < k.val + 1; omega
    have hlt2 : (⟨k.val + 1, hk1⟩ : Fin (m + 2)) < l := by
      show k.val + 1 < l.val; have : k.val < l.val := hkl; omega
    exact hgap _ (he.mem _) ⟨he.mono hlt1, he.mono hlt2⟩
  have hk : k.val < m + 1 := by have := l.isLt; omega
  exact ⟨⟨k.val, hk⟩, congrArg r (Fin.ext rfl), congrArg r (Fin.ext (by simp [hl]))⟩

/-- **The faces in `[a, b]` are the root face and the faces in the children.** -/
theorem RootEnum.cover (hH : IsDissection H) (hadj : H.Adj a b) (he : RootEnum H a b m r)
    (hab : a < b) {F : Finset (Fin n)} (hF : F ∈ facesIn H a b) :
    F = rootFace H a b ∨ ∃ i : Fin (m + 1), F ∈ facesIn H (r i.castSucc) (r i.succ) := by
  obtain ⟨hF, hsub⟩ := mem_facesIn.mp hF
  have h2 : a.val + 2 ≤ b.val := by
    have := he.card; have := he.one_le
    by_contra h
    have := card_le_two_of_gap (rootFace_sub (H := H) (a := a) (b := b)) fun z _ ⟨h1, h2⟩ => by
      have : a.val < z.val := h1
      have : z.val < b.val := h2
      omega
    omega
  by_cases hall : F ⊆ rootFace H a b
  · exact Or.inl (face_eq_of_subset hF (rootFace_isFace hH hadj h2) hall)
  · right
    obtain ⟨w, hwF, hwR⟩ := not_subset.mp hall
    obtain ⟨haw, hwb⟩ := mem_Icc.mp (hsub hwF)
    obtain ⟨f, hf, f', hf', hfw, hwf', hgap, hadj'⟩ := rootFace_cover hH hab hadj haw hwb hwR
    obtain ⟨i, rfl, rfl⟩ := he.consec hf hf' (hfw.trans hwf') hgap
    exact ⟨i, mem_facesIn.mpr ⟨hF, fun y hy => mem_Icc.mpr
      (face_sep hH hF (hfw.trans hwf') hadj' hwF hfw hwf' y hy)⟩⟩

theorem RootEnum.child_sub (he : RootEnum H a b m r) (i : Fin (m + 1)) :
    facesIn H (r i.castSucc) (r i.succ) ⊆ facesIn H a b :=
  facesIn_mono (he.ge _) (he.le _)

theorem RootEnum.root_not_child (he : RootEnum H a b m r) (i : Fin (m + 1)) :
    rootFace H a b ∉ facesIn H (r i.castSucc) (r i.succ) := by
  intro h
  obtain ⟨hF, hsub⟩ := mem_facesIn.mp h
  have := card_le_two_of_gap hsub (he.gap i)
  rw [he.card] at this
  have := he.one_le
  omega

theorem RootEnum.disj (he : RootEnum H a b m r) {i j : Fin (m + 1)} (hij : i ≠ j) :
    Disjoint (facesIn H (r i.castSucc) (r i.succ)) (facesIn H (r j.castSucc) (r j.succ)) := by
  rw [Finset.disjoint_left]
  intro F hFi hFj
  obtain ⟨hF, hsi⟩ := mem_facesIn.mp hFi
  obtain ⟨-, hsj⟩ := mem_facesIn.mp hFj
  -- wlog `i < j`: then the two intervals meet in at most one point
  have key : ∀ i j : Fin (m + 1), i < j → F ⊆ Icc (r i.castSucc) (r i.succ) →
      F ⊆ Icc (r j.castSucc) (r j.succ) → False := by
    intro i j hlt hi hj
    have hle : r i.succ ≤ r j.castSucc := he.mono.monotone (by
      show i.val + 1 ≤ j.val; have : i.val < j.val := hlt; omega)
    have hsub : F ⊆ {r i.succ} := by
      intro z hz
      obtain ⟨-, h1⟩ := mem_Icc.mp (hi hz)
      obtain ⟨h2, -⟩ := mem_Icc.mp (hj hz)
      rw [mem_singleton]
      exact le_antisymm h1 (hle.trans h2)
    have := card_le_card hsub
    have := hF.1
    simp at *
    omega
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hsi hsj
  · exact key j i h hsj hsi

/-- **The marks of `[a, b]`**: the root face, if even, and the marks of the children. -/
theorem RootEnum.marks_eq (hH : IsDissection H) (hadj : H.Adj a b) (he : RootEnum H a b m r)
    (hab : a < b) :
    marks H a b = (if Even (m + 2) then 1 else 0)
      + ∑ i : Fin (m + 1), marks H (r i.castSucc) (r i.succ) := by
  classical
  have h2 : a.val + 2 ≤ b.val := by
    have := he.card; have := he.one_le
    by_contra h
    have := card_le_two_of_gap (rootFace_sub (H := H) (a := a) (b := b)) fun z _ ⟨h1, h2⟩ => by
      have : a.val < z.val := h1
      have : z.val < b.val := h2
      omega
    omega
  have hset : facesIn H a b = insert (rootFace H a b)
      (univ.biUnion fun i : Fin (m + 1) => facesIn H (r i.castSucc) (r i.succ)) := by
    ext F
    simp only [mem_insert, mem_biUnion, mem_univ, true_and]
    constructor
    · intro hF; exact he.cover hH hadj hab hF
    · rintro (rfl | ⟨i, hi⟩)
      · exact mem_facesIn.mpr ⟨rootFace_isFace hH hadj h2, rootFace_sub⟩
      · exact he.child_sub i hi
  have hnot : rootFace H a b ∉ univ.biUnion fun i : Fin (m + 1) =>
      facesIn H (r i.castSucc) (r i.succ) := by
    simp only [mem_biUnion, mem_univ, true_and, not_exists]
    exact he.root_not_child
  unfold marks
  rw [hset, filter_insert, filter_biUnion]
  have hcardR : (rootFace H a b).card = m + 2 := he.card
  have hdisj : ((univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))).PairwiseDisjoint fun i =>
      (facesIn H (r i.castSucc) (r i.succ)).filter fun F => Even F.card := by
    intro i _ j _ hij
    exact Finset.disjoint_filter_filter (he.disj hij)
  simp only [hcardR]
  by_cases hev : Even (m + 2)
  · simp only [hev, ↓reduceIte]
    rw [card_insert_of_notMem (fun h => hnot (by
      simp only [mem_biUnion, mem_filter] at h ⊢; obtain ⟨i, hi, hi', -⟩ := h; exact ⟨i, hi, hi'⟩)),
      card_biUnion hdisj]
    ring
  · simp only [hev, ↓reduceIte]
    rw [card_biUnion hdisj, zero_add]

end Enum

/-- **The good property**: every even face of `[a, b]` has at most two marks in each of the
intervals between its consecutive vertices. -/
def GoodP (H : SimpleGraph (Fin n)) (a b : Fin n) : Prop :=
  ∀ F ∈ facesIn H a b, Even F.card → ∀ f ∈ F, ∀ f' ∈ F, f < f' →
    (∀ z ∈ F, ¬ (f < z ∧ z < f')) → marks H f f' ≤ 2

theorem GoodP.mono {a b a' b' : Fin n} (h : GoodP H a b) (h1 : a ≤ a') (h2 : b' ≤ b) :
    GoodP H a' b' := fun F hF => h F (facesIn_mono h1 h2 hF)

/-- **At most three marks make an interval good.** -/
theorem goodP_of_marks_le {a b : Fin n} (h : marks H a b ≤ 3) : GoodP H a b := by
  classical
  intro F hF hev f hf f' hf' hff hgap
  obtain ⟨hFf, hsub⟩ := mem_facesIn.mp hF
  have hsub' : Icc f f' ⊆ Icc a b := fun x hx => by
    obtain ⟨h1, h2⟩ := mem_Icc.mp hx
    obtain ⟨h3, -⟩ := mem_Icc.mp (hsub hf)
    obtain ⟨-, h4⟩ := mem_Icc.mp (hsub hf')
    exact mem_Icc.mpr ⟨h3.trans h1, h2.trans h4⟩
  have hnot : F ∉ facesIn H f f' := fun h' => by
    have := card_le_two_of_gap (mem_facesIn.mp h').2 hgap
    have := hFf.1
    omega
  have hle : insert F ((facesIn H f f').filter fun G => Even G.card) ⊆
      (facesIn H a b).filter fun G => Even G.card := by
    intro G hG
    rcases mem_insert.mp hG with rfl | hG
    · exact mem_filter.mpr ⟨hF, hev⟩
    · obtain ⟨hG1, hG2⟩ := mem_filter.mp hG
      obtain ⟨h1, h2⟩ := mem_facesIn.mp hG1
      exact mem_filter.mpr ⟨mem_facesIn.mpr ⟨h1, h2.trans hsub'⟩, hG2⟩
  have := card_le_card hle
  rw [card_insert_of_notMem (fun h' => hnot (mem_filter.mp h').1)] at this
  unfold marks at h ⊢
  omega

end Marks

end Outerplanar
