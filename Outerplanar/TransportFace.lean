/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.Transport

/-!
# Transport of the four-cell bound through a face with one loaded edge

**`tb_transport`**: a face with `m` interior vertices whose path edge `j₀` has the four-cell
bound `TB` with constant `τ`, all other path edges `Dominant`, has the four-cell bound on its
root edge with constant `τ · (dd / α)³`. Here `α = faceConst3 m` and
`dd = dd j₀ (m - j₀)` is `α` for odd `m` and `α - 1` for even `m`. So faces of odd length carry
the bound without loss.

The lists are enumerated along the path so that consecutive enumerations are aligned
(`framesFin`). The good colourings are then walks on three indices (`pw_le_faceSum`), and the
index form is `walks_tb_transport` of `Outerplanar/Transport.lean`. The constants of the side
edges are first normalised to one (`faceSum_div`).

This is the transport lemma of the research note
`ai_research_notes/OUTERPLANAR_SIX_EVEN_2026-11-23.md`.
-/

namespace Outerplanar

open Finset

/-- Two enumerations are aligned: equal colours have equal indices. -/
def Aligned (ζ ξ : Fin 3 → ℕ) : Prop := ∀ a b, ζ a = ξ b → a = b

/-! ### Enumerations along a path -/

theorem pathList_zero {m : ℕ} (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) :
    pathList Lu Lv Li 0 = Lu := consSnoc_zero _ _ _ _ rfl

theorem framesFin : ∀ (m : ℕ) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ), Lv.card = 3 →
    (∀ j, (Li j).card = 3) → ∀ α : Fin 3 → ℕ, Function.Injective α → (∀ a, α a ∈ Lu) →
    ∃ ζ : Fin (m + 2) → Fin 3 → ℕ, ζ 0 = α ∧
      (∀ i, Function.Injective (ζ i) ∧ ∀ a, ζ i a ∈ pathList Lu Lv Li i) ∧
      ∀ j : Fin (m + 1), Aligned (ζ j.castSucc) (ζ j.succ)
  | 0, Lu, Lv, Li, hv, _, α, hα, hαm => by
    obtain ⟨γ, hγ, hγm, hal⟩ := exists_aligned hv hα
    refine ⟨Fin.cons α fun _ => γ, rfl, fun i => ?_, fun j => ?_⟩
    · refine Fin.cases ⟨hα, fun a => by rw [Fin.cons_zero, pathList_zero]; exact hαm a⟩
        (fun i => ⟨hγ, fun a => ?_⟩) i
      have : pathList Lu Lv Li i.succ = Lv :=
        consSnoc_last _ _ _ _ (by have := i.isLt; simp only [Fin.val_succ]; omega)
      rw [Fin.cons_succ, this]
      exact hγm a
    · have hj : j = 0 := Fin.fin_one_eq_zero j
      subst hj
      intro a b e
      exact (hal b a e.symm)
  | m + 1, Lu, Lv, Li, hv, hLi, α, hα, hαm => by
    obtain ⟨ξ, hξ, hξm, hal⟩ := exists_aligned (hLi 0) hα
    obtain ⟨ζ', h0, hmem, hchain⟩ := framesFin m (Li 0) Lv (Fin.tail Li) hv
      (fun j => hLi _) ξ hξ hξm
    refine ⟨Fin.cons α ζ', rfl, fun i => ?_, fun j => ?_⟩
    · refine Fin.cases ⟨hα, fun a => by rw [Fin.cons_zero, pathList_zero]; exact hαm a⟩
        (fun i => ?_) i
      rw [Fin.cons_succ, pathList_tail]
      exact hmem i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro a b e
        have e' : α a = ξ b := by
          have h1 : (Fin.cons α ζ' : Fin (m + 3) → Fin 3 → ℕ) (Fin.castSucc 0) = α := rfl
          have h2 : (Fin.cons α ζ' : Fin (m + 3) → Fin 3 → ℕ) (Fin.succ 0) = ξ := by
            rw [Fin.cons_succ, h0]
          rw [h1, h2] at e
          exact e
        exact (hal b a e'.symm)
      · have e1 : (j.succ : Fin (m + 2)).castSucc = (j.castSucc).succ := rfl
        rw [e1, Fin.cons_succ, Fin.cons_succ]
        exact hchain j

/-! ### From the chain to the face sum -/

theorem mkMs_ofFn : ∀ (n : ℕ) (ζ : Fin (n + 2) → Fin 3 → ℕ) (E : Fin (n + 1) → ℕ → ℕ → ℝ),
    mkMs (ζ 0) (List.ofFn fun i : Fin (n + 1) => ζ i.succ) (List.ofFn E)
      = List.ofFn fun j => idxM (E j) (ζ j.castSucc) (ζ j.succ)
  | 0, ζ, E => by
    simp [List.ofFn_succ, mkMs]
  | n + 1, ζ, E => by
    have ih := mkMs_ofFn n (fun i => ζ i.succ) (fun j => E j.succ)
    rw [List.ofFn_succ (f := fun i : Fin (n + 2) => ζ i.succ), List.ofFn_succ (f := E), mkMs,
      List.ofFn_succ (f := fun j : Fin (n + 2) => idxM (E j) (ζ j.castSucc) (ζ j.succ))]
    congr 1

theorem forall₂_ofFn {α β : Type*} {R : α → β → Prop} : ∀ {n : ℕ} (f : Fin n → α)
    (g : Fin n → β), (∀ i, R (f i) (g i)) → List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (forall₂_ofFn _ _ fun i => h i.succ)

theorem ofFn_pathList_succ {m : ℕ} (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) :
    List.ofFn (fun i : Fin (m + 1) => pathList Lu Lv Li i.succ) = List.ofFn Li ++ [Lv] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  congr 1
  · congr 1
    funext i
    exact consSnoc_mid _ _ _ _ i (by simp)
  · congr 1
    exact consSnoc_last _ _ _ _ (by simp)

theorem getLastD_ofFn {α : Type*} : ∀ {n : ℕ} (f : Fin (n + 1) → α) (x : α),
    (List.ofFn f).getLastD x = f (Fin.last n)
  | 0, f, x => by simp [List.ofFn_succ]
  | n + 1, f, x => by
    rw [List.ofFn_succ, getLastD_cons, getLastD_ofFn (fun i => f i.succ)]
    rfl

/-- The tables of a path, read through an aligned chain of enumerations. -/
def pathTabs {m : ℕ} (ζ : Fin (m + 2) → Fin 3 → ℕ) (E : Fin (m + 1) → ℕ → ℕ → ℝ) :
    List (Fin 3 → Fin 3 → ℝ) :=
  List.ofFn fun j => idxM (E j) (ζ j.castSucc) (ζ j.succ)

theorem pw_le_faceSum {m : ℕ} {Lu Lv : Finset ℕ} {Li : Fin m → Finset ℕ}
    {ζ : Fin (m + 2) → Fin 3 → ℕ}
    (hζ : ∀ i, Function.Injective (ζ i) ∧ ∀ a, ζ i a ∈ pathList Lu Lv Li i)
    (E : Fin (m + 1) → ℕ → ℕ → ℝ) (hE0 : ∀ j c d, 0 ≤ E j c d) (a b : Fin 3) :
    pw (pathTabs ζ E) a b ≤ faceSum Li (fun _ _ => 1) E (ζ 0 a) (ζ (Fin.last (m + 1)) b) := by
  have hb : ζ (Fin.last (m + 1)) b ∈ Lv := by
    have := (hζ (Fin.last (m + 1))).2 b
    rwa [show pathList Lu Lv Li (Fin.last (m + 1)) = Lv from consSnoc_last _ _ _ _ (by simp)]
      at this
  rw [faceSum_eq_psum Li Lv E _ _ hb, pathTabs, ← mkMs_ofFn]
  have hF : List.Forall₂ (fun (ζ' : Fin 3 → ℕ) (L : Finset ℕ) => Function.Injective ζ' ∧
      ∀ a, ζ' a ∈ L) (List.ofFn fun i : Fin (m + 1) => ζ i.succ) (List.ofFn Li ++ [Lv]) := by
    rw [← ofFn_pathList_succ]
    exact forall₂_ofFn _ _ fun i => hζ i.succ
  have key := pw_le_psum (List.ofFn Li ++ [Lv]) (List.ofFn E) _ (ζ 0) (by simp) hF
    (fun E' hE' c d => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hE'
      exact hE0 i c d) a b
  rwa [getLastD_ofFn] at key

/-! ### Normalising the constants -/

theorem faceSum_div {m : ℕ} (Li : Fin m → Finset ℕ) (E : Fin (m + 1) → ℕ → ℕ → ℝ)
    (A : Fin (m + 1) → ℝ) (c d : ℕ) :
    faceSum Li (fun _ _ => 1) (fun j c d => E j c d / A j) c d
      = faceSum Li (fun _ _ => 1) E c d / ∏ j, A j := by
  unfold faceSum
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.prod_div_distrib, mul_div_assoc]

theorem TB.div {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A τ : ℝ} (h : TB S T W A τ) (hA : 0 < A) :
    TB S T (fun c d => W c d / A) 1 τ := by
  intro p q hm hpq i j k l hij hik hil hjk hjl hkl
  have := h p q hm hpq i j k l hij hik hil hjk hjl hkl
  have hA6 : (0 : ℝ) < A ^ 6 := pow_pos hA 6
  calc τ ^ 2 * 1 ^ 6 = τ ^ 2 * A ^ 6 / A ^ 6 := by field_simp
    _ ≤ (W (p i) (q i) ^ 2 * W (p j) (q j) ^ 2 * W (p k) (q k) * W (p l) (q l)) / A ^ 6 :=
        div_le_div_of_nonneg_right this hA6.le
    _ = _ := by field_simp

theorem TB.of_div {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A τ C : ℝ} (hA : 0 < A)
    (h : TB S T (fun c d => W c d / A) C τ) : TB S T W (C * A) τ := by
  intro p q hm hpq i j k l hij hik hil hjk hjl hkl
  have := h p q hm hpq i j k l hij hik hil hjk hjl hkl
  have hA6 : (0 : ℝ) < A ^ 6 := pow_pos hA 6
  have e : (W (p i) (q i) / A) ^ 2 * (W (p j) (q j) / A) ^ 2 * (W (p k) (q k) / A)
      * (W (p l) (q l) / A)
      = (W (p i) (q i) ^ 2 * W (p j) (q j) ^ 2 * W (p k) (q k) * W (p l) (q l)) / A ^ 6 := by
    field_simp
  rw [e, le_div_iff₀ hA6] at this
  calc τ ^ 2 * (C * A) ^ 6 = τ ^ 2 * C ^ 6 * A ^ 6 := by ring
    _ ≤ _ := this

theorem Dominant.div {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A : ℝ} (h : Dominant S T W A)
    (hA : 0 < A) : Dominant S T (fun c d => W c d / A) 1 := fun c hc d hd hcd => by
  rw [le_div_iff₀ hA, one_mul]
  exact h c hc d hd hcd

/-! ### Tables -/

theorem one_le_mn_of_dom {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} (h : Dominant S T W 1)
    {ζ ξ : Fin 3 → ℕ} (hζm : ∀ a, ζ a ∈ S) (hξm : ∀ b, ξ b ∈ T) (hal : Aligned ζ ξ) :
    1 ≤ mn (idxM W ζ ξ) := by
  unfold mn
  rw [Finset.le_inf'_iff]
  intro k _
  exact h _ (hζm _) _ (hξm _) fun e => offPair_ne k (hal _ _ e)

theorem one_le_mnP : ∀ (L : List (Fin 3 → Fin 3 → ℝ)), (∀ M ∈ L, 1 ≤ mn M) → 1 ≤ mnP L
  | [], _ => by simp [mnP]
  | M :: L, h => by
    rw [mnP_cons]
    exact one_le_mul_of_one_le_of_one_le (h M List.mem_cons_self)
      (one_le_mnP L fun M' h' => h M' (List.mem_cons_of_mem _ h'))

theorem TB.idx {S T : Finset ℕ} {W : ℕ → ℕ → ℝ} {A τ : ℝ} (h : TB S T W A τ)
    {ζ ξ : Fin 3 → ℕ} (hζ : Function.Injective ζ) (hξ : Function.Injective ξ)
    (hζm : ∀ a, ζ a ∈ S) (hξm : ∀ b, ξ b ∈ T) (hal : Aligned ζ ξ) :
    ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      τ ^ 2 * A ^ 6 ≤ idxM W ζ ξ (offPair i).1 (offPair i).2 ^ 2
        * idxM W ζ ξ (offPair j).1 (offPair j).2 ^ 2
        * idxM W ζ ξ (offPair k).1 (offPair k).2 * idxM W ζ ξ (offPair l).1 (offPair l).2 :=
  h _ _ (matched_of_enum hζ hξ hζm hξm) fun i e => offPair_ne i (hal _ _ e)

/-- The four-cell class at a root edge from its index form. -/
theorem tb_of_idx {Lu Lv : Finset ℕ} {F : ℕ → ℕ → ℝ} {A τ : ℝ}
    (h : ∀ α β : Fin 3 → ℕ, Function.Injective α → Function.Injective β → (∀ a, α a ∈ Lu) →
      (∀ b, β b ∈ Lv) → (∀ a b, α a = β b → a = b) →
      ∀ i j k l : Fin 6, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
        τ ^ 2 * A ^ 6 ≤ F (α (offPair i).1) (β (offPair i).2) ^ 2
          * F (α (offPair j).1) (β (offPair j).2) ^ 2
          * F (α (offPair k).1) (β (offPair k).2) * F (α (offPair l).1) (β (offPair l).2)) :
    TB Lu Lv F A τ := by
  intro p q hm hpq i j k l hij hik hil hjk hjl hkl
  obtain ⟨α, β, hα, hβ, hαm, hβm, hab⟩ := hm
  have hal : ∀ a b, α a = β b → a = b := by
    intro a b e
    by_contra hne
    obtain ⟨r, hr1, hr2⟩ := hab a b hne
    exact hpq r (by rw [hr1, hr2, e])
  obtain ⟨κ, hκb, hκ⟩ := matched_reindex hα hβ hab
  obtain ⟨i', rfl⟩ := hκb.2 i
  obtain ⟨j', rfl⟩ := hκb.2 j
  obtain ⟨k', rfl⟩ := hκb.2 k
  obtain ⟨l', rfl⟩ := hκb.2 l
  have key := h α β hα hβ hαm hβm hal i' j' k' l' (fun e => hij (by rw [e]))
    (fun e => hik (by rw [e])) (fun e => hil (by rw [e])) (fun e => hjk (by rw [e]))
    (fun e => hjl (by rw [e])) (fun e => hkl (by rw [e]))
  rw [(hκ i').1, (hκ i').2, (hκ j').1, (hκ j').2, (hκ k').1, (hκ k').2, (hκ l').1, (hκ l').2]
  exact key

/-! ### The theorem -/

/-- The normalised form: all constants one. -/
theorem tb_transport_one (m : ℕ) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (j₀ : Fin (m + 1)) (E : Fin (m + 1) → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) {τ : ℝ}
    (hT : TB (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) 1 τ)
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) 1) :
    TB Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m)
      (τ * (dd j₀ (m - j₀) / faceConst3 m) ^ 3) := by
  have hα : 0 < faceConst3 m := faceConst3_pos m
  refine tb_of_idx fun α β hα' hβ hαm hβm _ => ?_
  obtain ⟨ζ, h0, hζ, hchain⟩ := framesFin m Lu Lv Li hLv hLi α hα' hαm
  -- the last enumeration and the monodromy
  have hlast : ∀ b, ζ (Fin.last (m + 1)) b ∈ Lv := fun b => by
    have := (hζ (Fin.last (m + 1))).2 b
    rwa [show pathList Lu Lv Li (Fin.last (m + 1)) = Lv from consSnoc_last _ _ _ _ (by simp)]
      at this
  have himg : ∀ b, ∃ x, ζ (Fin.last (m + 1)) x = β b := fun b => by
    have hb : β b ∈ univ.image (ζ (Fin.last (m + 1))) := by
      rw [image_enum hLv (hζ _).1 hlast]
      exact hβm b
    obtain ⟨x, -, hx⟩ := mem_image.mp hb
    exact ⟨x, hx⟩
  choose σ hσ using himg
  have hσinj : Function.Injective σ := fun b b' e => hβ (by rw [← hσ b, ← hσ b', e])
  -- the tables, split at the loaded edge
  set T := pathTabs ζ E with hTdef
  set Mst := idxM (E j₀) (ζ j₀.castSucc) (ζ j₀.succ) with hMst
  have hlenT : T.length = m + 1 := by simp [hTdef, pathTabs]
  have hj₀ : j₀.val < T.length := by rw [hlenT]; exact j₀.isLt
  have hsplit : T = T.take j₀ ++ Mst :: T.drop (j₀ + 1) := by
    conv_lhs => rw [← List.take_append_drop j₀.val T]
    congr 1
    rw [List.drop_eq_getElem_cons hj₀]
    congr 1
    simp only [hTdef, pathTabs, List.getElem_ofFn, hMst, Fin.eta]
  have hTnn : ∀ M ∈ T, ∀ a b, 0 ≤ M a b := by
    intro M hM a b
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hM
    exact hE0 _ _ _
  have hdomT : ∀ j : Fin (m + 1), j ≠ j₀ → 1 ≤ mn (idxM (E j) (ζ j.castSucc) (ζ j.succ)) :=
    fun j hj => one_le_mn_of_dom (hD j hj) (hζ _).2 (hζ _).2 (hchain j)
  have hL₁ : ∀ M ∈ T.take j₀, 1 ≤ mn M := by
    intro M hM
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hM
    have hi' : i < j₀.val := by simp at hi; omega
    rw [List.getElem_take]
    simp only [hTdef, pathTabs, List.getElem_ofFn]
    exact hdomT ⟨i, by omega⟩ fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
  have hL₂ : ∀ M ∈ T.drop (j₀ + 1), 1 ≤ mn M := by
    intro M hM
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hM
    rw [List.getElem_drop]
    simp only [hTdef, pathTabs, List.getElem_ofFn]
    exact hdomT ⟨j₀ + 1 + i, by simp at hi; omega⟩ fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
  have hlen₁ : (T.take j₀).length = j₀.val := by
    rw [List.length_take, hlenT]; omega
  have hlen₂ : (T.drop (j₀ + 1)).length = m - j₀.val := by
    rw [List.length_drop, hlenT]; omega
  have hTidx := hT.idx (hζ _).1 (hζ _).1 (hζ _).2 (hζ _).2 (hchain j₀)
  rw [one_pow, mul_one] at hTidx
  have hτ2 : 0 ≤ τ ^ 2 := sq_nonneg τ
  have key := walks_tb_transport (T.take j₀) (T.drop (j₀ + 1))
    (fun M hM => hTnn M (List.mem_of_mem_take hM)) (fun M hM => hTnn M (List.mem_of_mem_drop hM))
    Mst (fun a b => hE0 _ _ _) zero_le_one zero_le_one (one_le_mnP _ hL₁) (one_le_mnP _ hL₂)
    hτ2 hTidx hσinj
  rw [← hsplit, hlen₁, hlen₂, one_mul, one_mul] at key
  intro i j k l hij hik hil hjk hjl hkl
  have hcell : ∀ r : Fin 6, pw T (offPair r).1 (σ (offPair r).2)
      ≤ faceSum Li (fun _ _ => 1) E (α (offPair r).1) (β (offPair r).2) := fun r => by
    have := pw_le_faceSum hζ E hE0 (offPair r).1 (σ (offPair r).2)
    rwa [h0, hσ] at this
  have hp := pw_nonneg T hTnn
  calc (τ * (dd j₀ (m - j₀) / faceConst3 m) ^ 3) ^ 2 * faceConst3 m ^ 6
      = dd j₀ (m - j₀) ^ 6 * τ ^ 2 := by field_simp
    _ ≤ _ := key i j k l hij hik hil hjk hjl hkl
    _ ≤ _ := four_le (hp _ _) (hp _ _) (hp _ _) (hp _ _) (hcell i) (hcell j) (hcell k) (hcell l)

/-- **Transport through a face with one loaded edge.** -/
theorem tb_transport (m : ℕ) (Lu Lv : Finset ℕ) (Li : Fin m → Finset ℕ) (hLv : Lv.card = 3)
    (hLi : ∀ j, (Li j).card = 3) (j₀ : Fin (m + 1)) (E : Fin (m + 1) → ℕ → ℕ → ℝ)
    (hE0 : ∀ j c d, 0 ≤ E j c d) (A : Fin (m + 1) → ℝ) (hA : ∀ j, 0 < A j) {τ : ℝ}
    (hT : TB (pathList Lu Lv Li j₀.castSucc) (pathList Lu Lv Li j₀.succ) (E j₀) (A j₀) τ)
    (hD : ∀ j, j ≠ j₀ →
      Dominant (pathList Lu Lv Li j.castSucc) (pathList Lu Lv Li j.succ) (E j) (A j)) :
    TB Lu Lv (faceSum Li (fun _ _ => 1) E) (faceConst3 m * ∏ j, A j)
      (τ * (dd j₀ (m - j₀) / faceConst3 m) ^ 3) := by
  have hP : 0 < ∏ j, A j := Finset.prod_pos fun j _ => hA j
  have key := tb_transport_one m Lu Lv Li hLv hLi j₀ (fun j c d => E j c d / A j)
    (fun j c d => div_nonneg (hE0 j c d) (hA j).le) (hT.div (hA j₀))
    (fun j hj => (hD j hj).div (hA j))
  refine TB.of_div hP ?_
  have e : (fun c d => faceSum Li (fun _ _ => 1) E c d / ∏ j, A j)
      = faceSum Li (fun _ _ => 1) (fun j c d => E j c d / A j) := by
    funext c d
    rw [faceSum_div]
  rw [e]
  exact key

end Outerplanar
