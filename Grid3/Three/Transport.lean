import Grid3.Three.ColourMaps
import k3_entropy.KernelTransport

/-!
# From colour maps to state maps

Given the colour maps of a seam (`ColourMaps`), each packed canonical state `st : Fin SB` (three
labels below `32`) is sent to the actual state `fL st : Fin 3 → Fin C` whose rows carry the
actual colours of the labels; inactive labels get fresh colours `B + i` above every actual
colour, so the map is injective on all of `Fin SB` and `Transport.liftLaw`/`liftKernel` apply.

* `liftLaw_fL`: the canonical law of the left column transports exactly to the concrete law
  `lawC Lc` (and symmetrically on the right), because `fL` restricts to a bijection between the
  canonical states `stsOf pL` and the proper concrete states, preserving signatures.
* `compat_fL_fR`: canonical compatibility of a positive transition implies actual compatibility
  (the rows differ), because a colour shared by both columns in a common row is in `commonI` and
  was sent to the same slot by both colour maps.
-/

open Finset

namespace Grid3.Three.Seam

open Cert Col

/-! ### Labels of a packed state -/

/-- the label of row `r` in a packed state -/
def lab (r : Fin 3) (st : ℕ) : ℕ :=
  if r.val = 0 then st / 1024 else if r.val = 1 then st / 32 % 32 else st % 32

theorem lab_lt (r : Fin 3) (st : ℕ) (hst : st < SB) : lab r st < 32 := by
  have hst' : st < 32768 := hst
  unfold lab; split_ifs <;> omega

theorem lab_zero (st : ℕ) : lab 0 st = st / 1024 := rfl
theorem lab_one (st : ℕ) : lab 1 st = st / 32 % 32 := rfl
theorem lab_two (st : ℕ) : lab 2 st = st % 32 := rfl

theorem pack_lab (st : ℕ) (hst : st < SB) : lab 0 st * 1024 + lab 1 st * 32 + lab 2 st = st := by
  have hst' : st < 32768 := hst
  rw [lab_zero, lab_one, lab_two]; omega

theorem lab_pack (i0 i1 i2 : ℕ) (h0 : i0 < 32) (h1 : i1 < 32) (h2 : i2 < 32) :
    lab 0 (i0 * 1024 + i1 * 32 + i2) = i0 ∧ lab 1 (i0 * 1024 + i1 * 32 + i2) = i1
      ∧ lab 2 (i0 * 1024 + i1 * 32 + i2) = i2 := by
  rw [lab_zero, lab_one, lab_two]; omega

theorem compat_iff (st st' : ℕ) :
    compat st st' = true ↔ ∀ r : Fin 3, lab r st ≠ lab r st' := by
  unfold compat
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩ r
    fin_cases r
    · exact h0
    · exact h1
    · exact h2
  · intro h
    exact ⟨⟨h 0, h 1⟩, h 2⟩

/-- the row lists of the canonical column, via the pattern of a slot -/
theorem mem_rowList_map (cs : List (ℕ × ℕ)) (r i : ℕ) :
    i ∈ rowList (cs.map Prod.fst) r ↔ i < cs.length ∧ ((cs.getD i (0, 0)).1).testBit r = true := by
  rw [mem_rowList, List.length_map]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simpa using h
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
    simpa using h

theorem mem_rowList_map' (cs : List (ℕ × ℕ)) (r i : ℕ) :
    i ∈ rowList (cs.map Prod.snd) r ↔ i < cs.length ∧ ((cs.getD i (0, 0)).2).testBit r = true := by
  rw [mem_rowList, List.length_map]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simpa using h
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
    simpa using h

theorem getD_map_fst (cs : List (ℕ × ℕ)) (i : ℕ) (hi : i < cs.length) :
    (cs.map Prod.fst).getD i 0 = (cs.getD i (0, 0)).1 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi]; rfl

theorem getD_map_snd (cs : List (ℕ × ℕ)) (i : ℕ) (hi : i < cs.length) :
    (cs.map Prod.snd).getD i 0 = (cs.getD i (0, 0)).2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi]; rfl

/-- a pattern with a set bit is nonzero -/
theorem ne_zero_of_testBit (x r : ℕ) (h : x.testBit r = true) : x ≠ 0 := by
  intro hx; rw [hx, Nat.zero_testBit] at h; exact absurd h (by decide)

/-! ### The state maps -/

variable (Lc Lc' : Fin 3 → Finset ℕ) (M : ℕ) (cm : ColourMaps Lc Lc' M) (B C : ℕ)

/-- label → actual colour on the left: the colour of an active slot, a fresh colour otherwise -/
def colL (i : ℕ) : ℕ :=
  if i < (cols Lc Lc' M).length ∧ ((cols Lc Lc' M).getD i (0, 0)).1 ≠ 0 then cm.ψL i else B + i

def colR (i : ℕ) : ℕ :=
  if i < (cols Lc Lc' M).length ∧ ((cols Lc Lc' M).getD i (0, 0)).2 ≠ 0 then cm.ψR i else B + i

section

variable (hB : ∀ c ∈ colours Lc, c < B) (hB' : ∀ c ∈ colours Lc', c < B) (hBC : B + 32 ≤ C)
  (h32 : (cols Lc Lc' M).length ≤ 32)

include hB hBC in
theorem colL_lt (i : ℕ) (hi : i < 32) : colL Lc Lc' M cm B i < C := by
  unfold colL
  split_ifs with h
  · exact lt_of_lt_of_le (hB _ (cm.φL_ψL i h.1 h.2).1) (by omega)
  · omega

include hB' hBC in
theorem colR_lt (i : ℕ) (hi : i < 32) : colR Lc Lc' M cm B i < C := by
  unfold colR
  split_ifs with h
  · exact lt_of_lt_of_le (hB' _ (cm.φR_ψR i h.1 h.2).1) (by omega)
  · omega

/-- the left state map -/
noncomputable def fL (st : Fin SB) : Fin 3 → Fin C := fun r =>
  ⟨colL Lc Lc' M cm B (lab r st.val), colL_lt Lc Lc' M cm B C hB hBC _ (lab_lt r st.val st.isLt)⟩

noncomputable def fR (st : Fin SB) : Fin 3 → Fin C := fun r =>
  ⟨colR Lc Lc' M cm B (lab r st.val), colR_lt Lc Lc' M cm B C hB' hBC _ (lab_lt r st.val st.isLt)⟩

include hB in
theorem colL_inj (i j : ℕ) (hi : i < 32) (hj : j < 32)
    (h : colL Lc Lc' M cm B i = colL Lc Lc' M cm B j) : i = j := by
  unfold colL at h
  split_ifs at h with hi' hj' hj'
  · have := cm.φL_ψL i hi'.1 hi'.2
    have := cm.φL_ψL j hj'.1 hj'.2
    calc i = cm.φL (cm.ψL i) := (cm.φL_ψL i hi'.1 hi'.2).2.symm
      _ = cm.φL (cm.ψL j) := by rw [h]
      _ = j := (cm.φL_ψL j hj'.1 hj'.2).2
  · have := hB _ (cm.φL_ψL i hi'.1 hi'.2).1; omega
  · have := hB _ (cm.φL_ψL j hj'.1 hj'.2).1; omega
  · omega

include hB' in
theorem colR_inj (i j : ℕ) (hi : i < 32) (hj : j < 32)
    (h : colR Lc Lc' M cm B i = colR Lc Lc' M cm B j) : i = j := by
  unfold colR at h
  split_ifs at h with hi' hj' hj'
  · calc i = cm.φR (cm.ψR i) := (cm.φR_ψR i hi'.1 hi'.2).2.symm
      _ = cm.φR (cm.ψR j) := by rw [h]
      _ = j := (cm.φR_ψR j hj'.1 hj'.2).2
  · have := hB' _ (cm.φR_ψR i hi'.1 hi'.2).1; omega
  · have := hB' _ (cm.φR_ψR j hj'.1 hj'.2).1; omega
  · omega

theorem fL_injective : Function.Injective (fL Lc Lc' M cm B C hB hBC) := by
  intro st st' h
  have hr : ∀ r : Fin 3, lab r st.val = lab r st'.val := fun r =>
    colL_inj Lc Lc' M cm B hB _ _ (lab_lt r _ st.isLt) (lab_lt r _ st'.isLt)
      (congrArg Fin.val (congrFun h r))
  apply Fin.ext
  rw [← pack_lab st.val st.isLt, ← pack_lab st'.val st'.isLt, hr 0, hr 1, hr 2]

theorem fR_injective : Function.Injective (fR Lc Lc' M cm B C hB' hBC) := by
  intro st st' h
  have hr : ∀ r : Fin 3, lab r st.val = lab r st'.val := fun r =>
    colR_inj Lc Lc' M cm B hB' _ _ (lab_lt r _ st.isLt) (lab_lt r _ st'.isLt)
      (congrArg Fin.val (congrFun h r))
  apply Fin.ext
  rw [← pack_lab st.val st.isLt, ← pack_lab st'.val st'.isLt, hr 0, hr 1, hr 2]

/-! ### Canonical states correspond to proper concrete states -/

/-- the canonical left patterns -/
abbrev pL : List ℕ := (cols Lc Lc' M).map Prod.fst
abbrev pR : List ℕ := (cols Lc Lc' M).map Prod.snd

/-- an active left label with bit `r` carries a colour of row `r` -/
theorem colL_active (i : ℕ) (r : Fin 3) (hi : i < (cols Lc Lc' M).length)
    (hr : (((cols Lc Lc' M).getD i (0, 0)).1).testBit r.val = true) :
    colL Lc Lc' M cm B i = cm.ψL i ∧ cm.ψL i ∈ Lc r ∧ cm.φL (cm.ψL i) = i := by
  have hne := ne_zero_of_testBit _ _ hr
  have hψ := cm.φL_ψL i hi hne
  refine ⟨by unfold colL; rw [if_pos ⟨hi, hne⟩], ?_, hψ.2⟩
  rw [← patOf_testBit Lc _ r, ← cm.φL_pat _ hψ.1, hψ.2]
  exact hr

theorem colR_active (i : ℕ) (r : Fin 3) (hi : i < (cols Lc Lc' M).length)
    (hr : (((cols Lc Lc' M).getD i (0, 0)).2).testBit r.val = true) :
    colR Lc Lc' M cm B i = cm.ψR i ∧ cm.ψR i ∈ Lc' r ∧ cm.φR (cm.ψR i) = i := by
  have hne := ne_zero_of_testBit _ _ hr
  have hψ := cm.φR_ψR i hi hne
  refine ⟨by unfold colR; rw [if_pos ⟨hi, hne⟩], ?_, hψ.2⟩
  rw [← patOf_testBit Lc' _ r, ← cm.φR_pat _ hψ.1, hψ.2]
  exact hr

include hB in
/-- a label whose colour lies in row `r` is active with bit `r` -/
theorem colL_mem (i : ℕ) (r : Fin 3) (hi : i < 32) (h : colL Lc Lc' M cm B i ∈ Lc r) :
    i < (cols Lc Lc' M).length ∧ (((cols Lc Lc' M).getD i (0, 0)).1).testBit r.val = true := by
  unfold colL at h
  split_ifs at h with hact
  · have hψ := cm.φL_ψL i hact.1 hact.2
    refine ⟨hact.1, ?_⟩
    rw [← hψ.2, cm.φL_pat _ hψ.1, patOf_testBit]
    exact h
  · have := hB _ ((mem_colours Lc _).2 ⟨r, h⟩); omega

include hB' in
theorem colR_mem (i : ℕ) (r : Fin 3) (hi : i < 32) (h : colR Lc Lc' M cm B i ∈ Lc' r) :
    i < (cols Lc Lc' M).length ∧ (((cols Lc Lc' M).getD i (0, 0)).2).testBit r.val = true := by
  unfold colR at h
  split_ifs at h with hact
  · have hψ := cm.φR_ψR i hact.1 hact.2
    refine ⟨hact.1, ?_⟩
    rw [← hψ.2, cm.φR_pat _ hψ.1, patOf_testBit]
    exact h
  · have := hB' _ ((mem_colours Lc' _).2 ⟨r, h⟩); omega

include h32 in
/-- the labels of a state in `stsOf pL` -/
theorem labels_of_mem (st : ℕ) (hst : st ∈ stsOf (pL Lc Lc' M)) :
    ∀ r : Fin 3, lab r st < (cols Lc Lc' M).length
      ∧ (((cols Lc Lc' M).getD (lab r st) (0, 0)).1).testBit r.val = true := by
  have h32' : (pL Lc Lc' M).length ≤ 32 := by rw [List.length_map]; exact h32
  obtain ⟨h0, h1, h2, -, -⟩ := stsOf_digits _ h32' st hst
  intro r
  fin_cases r
  · exact (mem_rowList_map _ _ _).1 h0
  · exact (mem_rowList_map _ _ _).1 h1
  · exact (mem_rowList_map _ _ _).1 h2

include h32 in
theorem labels_of_mem' (st : ℕ) (hst : st ∈ stsOf (pR Lc Lc' M)) :
    ∀ r : Fin 3, lab r st < (cols Lc Lc' M).length
      ∧ (((cols Lc Lc' M).getD (lab r st) (0, 0)).2).testBit r.val = true := by
  have h32' : (pR Lc Lc' M).length ≤ 32 := by rw [List.length_map]; exact h32
  obtain ⟨h0, h1, h2, -, -⟩ := stsOf_digits _ h32' st hst
  intro r
  fin_cases r
  · exact (mem_rowList_map' _ _ _).1 h0
  · exact (mem_rowList_map' _ _ _).1 h1
  · exact (mem_rowList_map' _ _ _).1 h2

include h32 in
theorem labels_ne_of_mem (st : ℕ) (hst : st ∈ stsOf (pL Lc Lc' M)) :
    lab 0 st ≠ lab 1 st ∧ lab 1 st ≠ lab 2 st := by
  have h32' : (pL Lc Lc' M).length ≤ 32 := by rw [List.length_map]; exact h32
  obtain ⟨-, -, -, h01, h12⟩ := stsOf_digits _ h32' st hst
  exact ⟨h01, h12⟩

include h32 in
theorem labels_ne_of_mem' (st : ℕ) (hst : st ∈ stsOf (pR Lc Lc' M)) :
    lab 0 st ≠ lab 1 st ∧ lab 1 st ≠ lab 2 st := by
  have h32' : (pR Lc Lc' M).length ≤ 32 := by rw [List.length_map]; exact h32
  obtain ⟨-, -, -, h01, h12⟩ := stsOf_digits _ h32' st hst
  exact ⟨h01, h12⟩

include h32 in
/-- a canonical state is sent to a proper concrete state -/
theorem isCol_fL (st : Fin SB) (hst : st.val ∈ stsOf (pL Lc Lc' M)) :
    IsCol Lc (fL Lc Lc' M cm B C hB hBC st) := by
  have hl := labels_of_mem Lc Lc' M h32 st.val hst
  have hne := labels_ne_of_mem Lc Lc' M h32 st.val hst
  refine ⟨fun r => ?_, ?_, ?_⟩
  · show colL Lc Lc' M cm B (lab r st.val) ∈ Lc r
    obtain ⟨he, hm, -⟩ := colL_active Lc Lc' M cm B _ r (hl r).1 (hl r).2
    rw [he]; exact hm
  · intro h
    exact hne.1 (colL_inj Lc Lc' M cm B hB _ _ (lab_lt 0 _ st.isLt) (lab_lt 1 _ st.isLt)
      (congrArg Fin.val h))
  · intro h
    exact hne.2 (colL_inj Lc Lc' M cm B hB _ _ (lab_lt 1 _ st.isLt) (lab_lt 2 _ st.isLt)
      (congrArg Fin.val h))

include h32 in
theorem isCol_fR (st : Fin SB) (hst : st.val ∈ stsOf (pR Lc Lc' M)) :
    IsCol Lc' (fR Lc Lc' M cm B C hB' hBC st) := by
  have hl := labels_of_mem' Lc Lc' M h32 st.val hst
  have hne := labels_ne_of_mem' Lc Lc' M h32 st.val hst
  refine ⟨fun r => ?_, ?_, ?_⟩
  · show colR Lc Lc' M cm B (lab r st.val) ∈ Lc' r
    obtain ⟨he, hm, -⟩ := colR_active Lc Lc' M cm B _ r (hl r).1 (hl r).2
    rw [he]; exact hm
  · intro h
    exact hne.1 (colR_inj Lc Lc' M cm B hB' _ _ (lab_lt 0 _ st.isLt) (lab_lt 1 _ st.isLt)
      (congrArg Fin.val h))
  · intro h
    exact hne.2 (colR_inj Lc Lc' M cm B hB' _ _ (lab_lt 1 _ st.isLt) (lab_lt 2 _ st.isLt)
      (congrArg Fin.val h))

/-- conversely, a packed state with a proper image is canonical -/
theorem mem_of_isCol_fL (st : Fin SB) (h : IsCol Lc (fL Lc Lc' M cm B C hB hBC st)) :
    st.val ∈ stsOf (pL Lc Lc' M) := by
  obtain ⟨hmem, h01, h12⟩ := h
  have hact : ∀ r : Fin 3, lab r st.val ∈ rowList (pL Lc Lc' M) r.val := fun r => by
    rw [mem_rowList_map]
    exact colL_mem Lc Lc' M cm B hB _ r (lab_lt r _ st.isLt) (hmem r)
  have hne01 : lab 0 st.val ≠ lab 1 st.val := fun e => h01 (Fin.ext (by
    show colL Lc Lc' M cm B (lab 0 st.val) = colL Lc Lc' M cm B (lab 1 st.val); rw [e]))
  have hne12 : lab 1 st.val ≠ lab 2 st.val := fun e => h12 (Fin.ext (by
    show colL Lc Lc' M cm B (lab 1 st.val) = colL Lc Lc' M cm B (lab 2 st.val); rw [e]))
  have := mem_stsOf_of_labels (pL Lc Lc' M) _ _ _ (hact 0) (hact 1) (hact 2) hne01 hne12
  rwa [pack_lab st.val st.isLt] at this

theorem mem_of_isCol_fR (st : Fin SB) (h : IsCol Lc' (fR Lc Lc' M cm B C hB' hBC st)) :
    st.val ∈ stsOf (pR Lc Lc' M) := by
  obtain ⟨hmem, h01, h12⟩ := h
  have hact : ∀ r : Fin 3, lab r st.val ∈ rowList (pR Lc Lc' M) r.val := fun r => by
    rw [mem_rowList_map']
    exact colR_mem Lc Lc' M cm B hB' _ r (lab_lt r _ st.isLt) (hmem r)
  have hne01 : lab 0 st.val ≠ lab 1 st.val := fun e => h01 (Fin.ext (by
    show colR Lc Lc' M cm B (lab 0 st.val) = colR Lc Lc' M cm B (lab 1 st.val); rw [e]))
  have hne12 : lab 1 st.val ≠ lab 2 st.val := fun e => h12 (Fin.ext (by
    show colR Lc Lc' M cm B (lab 1 st.val) = colR Lc Lc' M cm B (lab 2 st.val); rw [e]))
  have := mem_stsOf_of_labels (pR Lc Lc' M) _ _ _ (hact 0) (hact 1) (hact 2) hne01 hne12
  rwa [pack_lab st.val st.isLt] at this

include h32 in
/-- every proper concrete state is the image of a canonical one -/
theorem exists_fL (s : Fin 3 → Fin C) (hs : IsCol Lc s) :
    ∃ st : Fin SB, st.val ∈ stsOf (pL Lc Lc' M) ∧ fL Lc Lc' M cm B C hB hBC st = s := by
  obtain ⟨hmem, h01, h12⟩ := hs
  have hcol : ∀ r : Fin 3, (s r).val ∈ colours Lc := fun r => (mem_colours Lc _).2 ⟨r, hmem r⟩
  have hlt : ∀ r : Fin 3, cm.φL (s r).val < (cols Lc Lc' M).length := fun r =>
    cm.φL_lt _ (hcol r)
  have hbit : ∀ r : Fin 3, (((cols Lc Lc' M).getD (cm.φL (s r).val) (0, 0)).1).testBit r.val = true :=
    fun r => by rw [cm.φL_pat _ (hcol r), patOf_testBit]; exact hmem r
  have h32' : ∀ r : Fin 3, cm.φL (s r).val < 32 := fun r => lt_of_lt_of_le (hlt r) h32
  have hstlt : cm.φL (s 0).val * 1024 + cm.φL (s 1).val * 32 + cm.φL (s 2).val < SB := by
    show _ < 32768; have := h32' 0; have := h32' 1; have := h32' 2; omega
  obtain ⟨e0, e1, e2⟩ := lab_pack _ _ _ (h32' 0) (h32' 1) (h32' 2)
  have hcolL : ∀ r : Fin 3, colL Lc Lc' M cm B (cm.φL (s r).val) = (s r).val := fun r => by
    obtain ⟨he, -, -⟩ := colL_active Lc Lc' M cm B _ r (hlt r) (hbit r)
    rw [he, cm.ψL_φL _ (hcol r)]
  refine ⟨⟨_, hstlt⟩, ?_, ?_⟩
  · have hne01 : cm.φL (s 0).val ≠ cm.φL (s 1).val := fun e => h01 (Fin.ext (by
      rw [← cm.ψL_φL _ (hcol 0), ← cm.ψL_φL _ (hcol 1), e]))
    have hne12 : cm.φL (s 1).val ≠ cm.φL (s 2).val := fun e => h12 (Fin.ext (by
      rw [← cm.ψL_φL _ (hcol 1), ← cm.ψL_φL _ (hcol 2), e]))
    exact mem_stsOf_of_labels (pL Lc Lc' M) _ _ _
      ((mem_rowList_map _ _ _).2 ⟨hlt 0, hbit 0⟩) ((mem_rowList_map _ _ _).2 ⟨hlt 1, hbit 1⟩)
      ((mem_rowList_map _ _ _).2 ⟨hlt 2, hbit 2⟩) hne01 hne12
  · funext r
    apply Fin.ext
    rcases r with ⟨r, hr⟩
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
    · show colL Lc Lc' M cm B (lab 0 _) = (s 0).val; rw [e0]; exact hcolL 0
    · show colL Lc Lc' M cm B (lab 1 _) = (s 1).val; rw [e1]; exact hcolL 1
    · show colL Lc Lc' M cm B (lab 2 _) = (s 2).val; rw [e2]; exact hcolL 2

include h32 in
theorem exists_fR (s : Fin 3 → Fin C) (hs : IsCol Lc' s) :
    ∃ st : Fin SB, st.val ∈ stsOf (pR Lc Lc' M) ∧ fR Lc Lc' M cm B C hB' hBC st = s := by
  obtain ⟨hmem, h01, h12⟩ := hs
  have hcol : ∀ r : Fin 3, (s r).val ∈ colours Lc' := fun r => (mem_colours Lc' _).2 ⟨r, hmem r⟩
  have hlt : ∀ r : Fin 3, cm.φR (s r).val < (cols Lc Lc' M).length := fun r =>
    cm.φR_lt _ (hcol r)
  have hbit : ∀ r : Fin 3, (((cols Lc Lc' M).getD (cm.φR (s r).val) (0, 0)).2).testBit r.val = true :=
    fun r => by rw [cm.φR_pat _ (hcol r), patOf_testBit]; exact hmem r
  have h32' : ∀ r : Fin 3, cm.φR (s r).val < 32 := fun r => lt_of_lt_of_le (hlt r) h32
  have hstlt : cm.φR (s 0).val * 1024 + cm.φR (s 1).val * 32 + cm.φR (s 2).val < SB := by
    show _ < 32768; have := h32' 0; have := h32' 1; have := h32' 2; omega
  obtain ⟨e0, e1, e2⟩ := lab_pack _ _ _ (h32' 0) (h32' 1) (h32' 2)
  have hcolR : ∀ r : Fin 3, colR Lc Lc' M cm B (cm.φR (s r).val) = (s r).val := fun r => by
    obtain ⟨he, -, -⟩ := colR_active Lc Lc' M cm B _ r (hlt r) (hbit r)
    rw [he, cm.ψR_φR _ (hcol r)]
  refine ⟨⟨_, hstlt⟩, ?_, ?_⟩
  · have hne01 : cm.φR (s 0).val ≠ cm.φR (s 1).val := fun e => h01 (Fin.ext (by
      rw [← cm.ψR_φR _ (hcol 0), ← cm.ψR_φR _ (hcol 1), e]))
    have hne12 : cm.φR (s 1).val ≠ cm.φR (s 2).val := fun e => h12 (Fin.ext (by
      rw [← cm.ψR_φR _ (hcol 1), ← cm.ψR_φR _ (hcol 2), e]))
    exact mem_stsOf_of_labels (pR Lc Lc' M) _ _ _
      ((mem_rowList_map' _ _ _).2 ⟨hlt 0, hbit 0⟩) ((mem_rowList_map' _ _ _).2 ⟨hlt 1, hbit 1⟩)
      ((mem_rowList_map' _ _ _).2 ⟨hlt 2, hbit 2⟩) hne01 hne12
  · funext r
    apply Fin.ext
    rcases r with ⟨r, hr⟩
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
    · show colR Lc Lc' M cm B (lab 0 _) = (s 0).val; rw [e0]; exact hcolR 0
    · show colR Lc Lc' M cm B (lab 1 _) = (s 1).val; rw [e1]; exact hcolR 1
    · show colR Lc Lc' M cm B (lab 2 _) = (s 2).val; rw [e2]; exact hcolR 2

/-! ### Signatures -/

include h32 in
theorem sigOf_fL (st : Fin SB) (hst : st.val ∈ stsOf (pL Lc Lc' M)) :
    sigOf (pL Lc Lc' M) st.val = sigC Lc (fL Lc Lc' M cm B C hB hBC st) := by
  have hl := labels_of_mem Lc Lc' M h32 st.val hst
  have hpat : ∀ r : Fin 3, (pL Lc Lc' M).getD (lab r st.val) 0
      = patOf Lc (colL Lc Lc' M cm B (lab r st.val)) := fun r => by
    obtain ⟨he, hm, hφ⟩ := colL_active Lc Lc' M cm B _ r (hl r).1 (hl r).2
    rw [he, getD_map_fst _ _ (hl r).1, ← hφ, cm.φL_pat _ ((mem_colours Lc _).2 ⟨r, hm⟩), hφ]
  have hABA : isABA st.val = true ↔ fL Lc Lc' M cm B C hB hBC st 0 = fL Lc Lc' M cm B C hB hBC st 2 := by
    unfold isABA
    rw [beq_iff_eq]
    constructor
    · intro h
      apply Fin.ext
      show colL Lc Lc' M cm B (lab 0 st.val) = colL Lc Lc' M cm B (lab 2 st.val)
      rw [lab_zero, lab_two, h]
    · intro h
      have := colL_inj Lc Lc' M cm B hB _ _ (lab_lt 0 _ st.isLt) (lab_lt 2 _ st.isLt)
        (congrArg Fin.val h)
      rw [lab_zero, lab_two] at this
      exact this
  unfold sigOf sigC
  have e0 := hpat 0; have e1 := hpat 1; have e2 := hpat 2
  rw [lab_zero] at e0; rw [lab_one] at e1; rw [lab_two] at e2
  simp only [e0, e1, e2]
  show (((patOf Lc (colL Lc Lc' M cm B (st.val / 1024)) - 1) * 7
      + (patOf Lc (colL Lc Lc' M cm B (st.val / 32 % 32)) - 1)) * 7
      + (patOf Lc (colL Lc Lc' M cm B (st.val % 32)) - 1)) * 2 + (if isABA st.val = true then 1 else 0)
    = (((patOf Lc (colL Lc Lc' M cm B (lab 0 st.val)) - 1) * 7
      + (patOf Lc (colL Lc Lc' M cm B (lab 1 st.val)) - 1)) * 7
      + (patOf Lc (colL Lc Lc' M cm B (lab 2 st.val)) - 1)) * 2
      + (if fL Lc Lc' M cm B C hB hBC st 0 = fL Lc Lc' M cm B C hB hBC st 2 then 1 else 0)
  rw [lab_zero, lab_one, lab_two]
  congr 1
  by_cases h : isABA st.val = true
  · rw [if_pos h, if_pos (hABA.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hABA.2 h'))]

include h32 in
theorem sigOf_fR (st : Fin SB) (hst : st.val ∈ stsOf (pR Lc Lc' M)) :
    sigOf (pR Lc Lc' M) st.val = sigC Lc' (fR Lc Lc' M cm B C hB' hBC st) := by
  have hl := labels_of_mem' Lc Lc' M h32 st.val hst
  have hpat : ∀ r : Fin 3, (pR Lc Lc' M).getD (lab r st.val) 0
      = patOf Lc' (colR Lc Lc' M cm B (lab r st.val)) := fun r => by
    obtain ⟨he, hm, hφ⟩ := colR_active Lc Lc' M cm B _ r (hl r).1 (hl r).2
    rw [he, getD_map_snd _ _ (hl r).1, ← hφ, cm.φR_pat _ ((mem_colours Lc' _).2 ⟨r, hm⟩), hφ]
  have hABA : isABA st.val = true ↔ fR Lc Lc' M cm B C hB' hBC st 0 = fR Lc Lc' M cm B C hB' hBC st 2 := by
    unfold isABA
    rw [beq_iff_eq]
    constructor
    · intro h
      apply Fin.ext
      show colR Lc Lc' M cm B (lab 0 st.val) = colR Lc Lc' M cm B (lab 2 st.val)
      rw [lab_zero, lab_two, h]
    · intro h
      have := colR_inj Lc Lc' M cm B hB' _ _ (lab_lt 0 _ st.isLt) (lab_lt 2 _ st.isLt)
        (congrArg Fin.val h)
      rw [lab_zero, lab_two] at this
      exact this
  unfold sigOf sigC
  have e0 := hpat 0; have e1 := hpat 1; have e2 := hpat 2
  rw [lab_zero] at e0; rw [lab_one] at e1; rw [lab_two] at e2
  simp only [e0, e1, e2]
  show (((patOf Lc' (colR Lc Lc' M cm B (st.val / 1024)) - 1) * 7
      + (patOf Lc' (colR Lc Lc' M cm B (st.val / 32 % 32)) - 1)) * 7
      + (patOf Lc' (colR Lc Lc' M cm B (st.val % 32)) - 1)) * 2 + (if isABA st.val = true then 1 else 0)
    = (((patOf Lc' (colR Lc Lc' M cm B (lab 0 st.val)) - 1) * 7
      + (patOf Lc' (colR Lc Lc' M cm B (lab 1 st.val)) - 1)) * 7
      + (patOf Lc' (colR Lc Lc' M cm B (lab 2 st.val)) - 1)) * 2
      + (if fR Lc Lc' M cm B C hB' hBC st 0 = fR Lc Lc' M cm B C hB' hBC st 2 then 1 else 0)
  rw [lab_zero, lab_one, lab_two]
  congr 1
  by_cases h : isABA st.val = true
  · rw [if_pos h, if_pos (hABA.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hABA.2 h'))]

/-! ### The law transports exactly -/

open Transport in
include h32 in
theorem liftLaw_fL :
    liftLaw (fL Lc Lc' M cm B C hB hBC) (lawR (packType Lc) (pL Lc Lc' M)) = lawC Lc := by
  funext s
  by_cases hs : s ∈ Set.range (fL Lc Lc' M cm B C hB hBC)
  · obtain ⟨st, rfl⟩ := hs
    rw [liftLaw_apply _ (fL_injective Lc Lc' M cm B C hB hBC), lawR_eq_lawSig]
    unfold lawC
    by_cases hst : st.val ∈ stsOf (pL Lc Lc' M)
    · rw [if_pos hst, if_pos (isCol_fL Lc Lc' M cm B C hB hBC h32 st hst),
        sigOf_fL Lc Lc' M cm B C hB hBC h32 st hst]
    · rw [if_neg hst, if_neg (fun h => hst (mem_of_isCol_fL Lc Lc' M cm B C hB hBC st h))]
  · rw [liftLaw_off _ _ _ hs]
    unfold lawC
    rw [if_neg]
    intro hcol
    obtain ⟨st, -, hst⟩ := exists_fL Lc Lc' M cm B C hB hBC h32 s hcol
    exact hs ⟨st, hst⟩

open Transport in
include h32 in
theorem liftLaw_fR :
    liftLaw (fR Lc Lc' M cm B C hB' hBC) (lawR (packType Lc') (pR Lc Lc' M)) = lawC Lc' := by
  funext s
  by_cases hs : s ∈ Set.range (fR Lc Lc' M cm B C hB' hBC)
  · obtain ⟨st, rfl⟩ := hs
    rw [liftLaw_apply _ (fR_injective Lc Lc' M cm B C hB' hBC), lawR_eq_lawSig]
    unfold lawC
    by_cases hst : st.val ∈ stsOf (pR Lc Lc' M)
    · rw [if_pos hst, if_pos (isCol_fR Lc Lc' M cm B C hB' hBC h32 st hst),
        sigOf_fR Lc Lc' M cm B C hB' hBC h32 st hst]
    · rw [if_neg hst, if_neg (fun h => hst (mem_of_isCol_fR Lc Lc' M cm B C hB' hBC st h))]
  · rw [liftLaw_off _ _ _ hs]
    unfold lawC
    rw [if_neg]
    intro hcol
    obtain ⟨st, -, hst⟩ := exists_fR Lc Lc' M cm B C hB' hBC h32 s hcol
    exact hs ⟨st, hst⟩

/-! ### Canonical compatibility implies actual compatibility -/

theorem land_ne_zero_of_testBit (a b r : ℕ) (ha : a.testBit r = true) (hb : b.testBit r = true) :
    a &&& b ≠ 0 := by
  intro h
  have := congrArg (fun x => x.testBit r) h
  simp only [Nat.testBit_and, ha, hb, Nat.zero_testBit] at this
  exact absurd this (by decide)

include h32 in
theorem compat_fL_fR (st st' : Fin SB) (hst : st.val ∈ stsOf (pL Lc Lc' M))
    (hst' : st'.val ∈ stsOf (pR Lc Lc' M)) (hc : compat st.val st'.val = true) :
    ∀ r : Fin 3, fL Lc Lc' M cm B C hB hBC st r ≠ fR Lc Lc' M cm B C hB' hBC st' r := by
  intro r h
  have hlab := (compat_iff _ _).1 hc r
  have hl := labels_of_mem Lc Lc' M h32 st.val hst r
  have hr := labels_of_mem' Lc Lc' M h32 st'.val hst' r
  obtain ⟨heL, hmL, hφL⟩ := colL_active Lc Lc' M cm B _ r hl.1 hl.2
  obtain ⟨heR, hmR, hφR⟩ := colR_active Lc Lc' M cm B _ r hr.1 hr.2
  have hx : colL Lc Lc' M cm B (lab r st.val) = colR Lc Lc' M cm B (lab r st'.val) :=
    congrArg Fin.val h
  rw [heL, heR] at hx
  -- the shared colour lies in row `r` of both columns, so it is in `commonI`
  have hcom : cm.ψL (lab r st.val) ∈ commonI Lc Lc' := by
    rw [mem_commonI]
    refine ⟨(mem_colours Lc _).2 ⟨r, hmL⟩, (mem_colours Lc' _).2 ⟨r, by rw [hx]; exact hmR⟩, ?_⟩
    apply land_ne_zero_of_testBit _ _ r.val
    · exact (patOf_testBit Lc _ r).2 hmL
    · exact (patOf_testBit Lc' _ r).2 (by rw [hx]; exact hmR)
  apply hlab
  calc lab r st.val = cm.φL (cm.ψL (lab r st.val)) := hφL.symm
    _ = cm.φR (cm.ψL (lab r st.val)) := cm.common _ hcom
    _ = cm.φR (cm.ψR (lab r st'.val)) := by rw [hx]
    _ = lab r st'.val := hφR

end

end Grid3.Three.Seam
