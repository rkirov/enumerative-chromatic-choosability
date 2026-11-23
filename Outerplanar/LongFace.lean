/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.LongData
import Outerplanar.SquareThm
import Outerplanar.OddBall

/-!
# Every face with one loaded edge preserves the ball class

`faceOK_all`: for every face with one loaded edge, in the two-arm form of
`Outerplanar/Arms.lean`, the profile is in the ball class with the constant of the face. The
proof is by strong induction on the number `m` of interior vertices.

* `m ≤ 2`: the edge itself, triangles (`ballTriClosed`) and squares (`ballFaceBare_two`).
* `m ≥ 3`: carry aligned enumerations outwards along both arms. If the codes of an arm have a
  reducible window, one of the rules `faceOK_cut`, `faceOK_sh1`, `faceOK_sh0` applies, the last
  two with the induction hypothesis for `m - 2` (`faceOK_of_red`). Otherwise both arms have at
  most four edges (`LongData.red5`), one of them has at least two, and the open-arm rule applies
  to it (`faceOK_open`, with `LongData.cov2`, `cov3`, `cov4` and the certificates `open*`).

`ballFaceBare_all` translates this back to the face sum of `Outerplanar/FaceDefs.lean`, and
`ecc_three_of_oneLoadBuilt` is the resulting theorem on graphs: **a graph built from an edge
by ears on edges, in which every ear of two or more vertices sits on an active edge and makes at
most one of its new edges active, is `3`-ECC.**

This is a result of this repository's 2026-11 AI research collaboration (research log
`ai_research_notes/OUTERPLANAR_K3_TRIANGLES_2026-11-10.md`, sections "Twelfth pass" and "Long
faces").
-/

namespace Outerplanar

open Finset

/-! ### Reducible windows -/

/-- Splitting a chain along a splitting of its codes. -/
theorem Chain.split_codes {ζ' : Fin 3 → ℕ} {dB : List (Fin 3 → Bool)} :
    ∀ (dA : List (Fin 3 → Bool)) {U : List (Finset ℕ)} {ζ : Fin 3 → ℕ}
      {ds : List (Fin 3 → Bool)}, Chain ζ U ds ζ' → ds = dA ++ dB →
      ∃ A B ζm, U = A ++ B ∧ Chain ζ A dA ζm ∧ Chain ζm B dB ζ'
  | [], U, ζ, ds, h, heq => ⟨[], U, ζ, rfl, Chain.nil ζ, by rw [heq] at h; exact h⟩
  | d :: dA, U, ζ, ds, h, heq => by
    cases h with
    | nil => cases heq
    | cons hL hinj hmem hal h' =>
      injection heq with h1 h2
      obtain ⟨A, B, ζm, rfl, hA, hB⟩ := Chain.split_codes dA h' h2
      refine ⟨_ :: A, B, ζm, rfl, ?_, hB⟩
      rw [← h1]
      exact Chain.cons hL hinj hmem hal hA

theorem sh1Code_length {ds : List (Fin 3 → Bool)} (h : sh1Code ds = true) : ds.length = 3 := by
  rcases ds with _ | ⟨d₁, _ | ⟨d₂, _ | ⟨d₃, _ | ⟨d₄, ds⟩⟩⟩⟩ <;> first | rfl | simp [sh1Code] at h

theorem sh0Code_length {ds : List (Fin 3 → Bool)} (h : sh0Code ds = true) : ds.length = 2 := by
  rcases ds with _ | ⟨d₁, _ | ⟨d₂, _ | ⟨d₃, ds⟩⟩⟩ <;> first | rfl | simp [sh0Code] at h

/-- **A reducible window on the second arm.** -/
theorem faceOK_of_red {S T : Finset ℕ} {U₁ U₂ : List (Finset ℕ)} (hS : S.card = 3)
    (hT : T.card = 3) (hU₁ : ∀ L ∈ U₁, L.card = 3)
    (ih : ∀ U₂' : List (Finset ℕ), U₂'.length + 2 = U₂.length → (∀ L ∈ U₂', L.card = 3) →
      FaceOK S U₁ T U₂')
    {η β₀ : Fin 3 → ℕ} {ds₂ : List (Fin 3 → Bool)} (hη : Function.Injective η)
    (hηm : ∀ i, η i ∈ T) (hc : Chain η U₂ ds₂ β₀) (hred : HasRed ds₂) : FaceOK S U₁ T U₂ := by
  obtain ⟨dP, dS, dR, hds, hr⟩ := hred
  obtain ⟨P, B, ζ₁, rfl, hcP, hcB⟩ :=
    Chain.split_codes (dB := dS ++ dR) dP hc (by rw [hds, List.append_assoc])
  obtain ⟨Sub, R, ζ₂, rfl, hcS, hcR⟩ := Chain.split_codes dS hcB rfl
  have hP := hcP.cards
  have hSub := hcS.cards
  have hR := hcR.cards
  have hX : (P.getLastD T).card = 3 := card_getLastD hT hP
  have hζ₁ := hcP.injective hη
  have hζ₁m : ∀ i, ζ₁ i ∈ P.getLastD T := hcP.mem hηm
  rw [redCode, Bool.or_eq_true, Bool.or_eq_true] at hr
  rcases hr with (hcut | hsh1) | hsh0
  · obtain ⟨b, hb, hcutC⟩ := hcS.cut hX hζ₁ hζ₁m hcut
    exact faceOK_cut hS hU₁ hT hP hSub hR b hcutC hb
  · have hlen : Sub.length = 3 := by rw [← hcS.length]; exact sh1Code_length hsh1
    obtain ⟨Y₁, Y₂, Z, rfl⟩ := List.length_eq_three.mp hlen
    have hZ : Z.card = 3 := hSub Z (by simp)
    have hcond := hcS.sh1 hX hζ₁ hζ₁m hsh1
    have hlenU : (P ++ Z :: R).length + 2 = (P ++ ([Y₁, Y₂, Z] ++ R)).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have ih' := ih (P ++ Z :: R) hlenU fun L hL => by
      rcases List.mem_append.mp hL with h | h
      · exact hP L h
      · rcases List.mem_cons.mp h with rfl | h'
        · exact hZ
        · exact hR L h'
    exact faceOK_sh1 hS hU₁ hT hP hR hZ ih' hcond
  · have hlen : Sub.length = 2 := by rw [← hcS.length]; exact sh0Code_length hsh0
    obtain ⟨Y, Z, rfl⟩ := List.length_eq_two.mp hlen
    have hZ : Z.card = 3 := hSub Z (by simp)
    obtain ⟨hXZ, hcond⟩ := hcS.sh0 hX hζ₁ hζ₁m hsh0
    have hlenU : (P ++ R).length + 2 = (P ++ ([Y, Z] ++ R)).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have ih' := ih (P ++ R) hlenU fun L hL => by
      rcases List.mem_append.mp hL with h | h
      · exact hP L h
      · exact hR L h
    exact faceOK_sh0 hS hU₁ hT hP hR hZ ih' hXZ hcond

/-! ### The tables -/

theorem hasRed5 (ds : List (Fin 3 → Bool)) (h : 5 ≤ ds.length) : HasRed ds :=
  hasRed_of_five LongData.red5 ds h

theorem open_helper {cs : List ℕ} {α dc s : ℕ} {L : List Inst}
    (hd : ∀ t b : Fin 3, dig 8 dc (3 * t.val + b.val) = dMat s t b)
    (h : cs.all (fun c => checkCase α (openCase c dc) L) = true) :
    ∀ c ∈ cs, GenOK (fun a y : Fin 3 => dig 8 c (3 * a.val + y.val)) idPat (dMat s) noPat α :=
  fun c hc => genOK_of_open hd (List.all_eq_true.mp h c hc)

/-- An arm without reducible window, of two to four edges, is fine against any second arm of
at most four edges. -/
theorem openOK_table (ds : List (Fin 3 → Bool)) (hr : ¬ HasRed ds) (h2 : 2 ≤ ds.length) (s : ℕ)
    (hs : s ≤ 4) (h3 : 3 ≤ ds.length + s) : OpenOK ds s := by
  have h4 : ds.length ≤ 4 := by
    by_contra h
    exact hr (hasRed5 ds (by omega))
  have key : ∀ (cs : List ℕ) (n : ℕ), ds.length = n → allOpen cs n [] = true →
      Covered cs ds := fun cs n hn hall => by
    rcases allOpen_sound cs n [] hall ds hn with h | h
    · exact absurd (by simpa using h) hr
    · simpa using h
  obtain hn | hn | hn : ds.length = 2 ∨ ds.length = 3 ∨ ds.length = 4 := by omega
  · refine openOK_of_covered (key LongData.cs2 2 hn LongData.cov2) ?_
    interval_cases s
    · exfalso
      omega
    · rw [show ds.length + 1 = 3 from by omega]
      exact open_helper LongData.dc1_ok LongData.open2_1
    · rw [show ds.length + 2 = 4 from by omega]
      exact open_helper LongData.dc2_ok LongData.open2_2
    · rw [show ds.length + 3 = 5 from by omega]
      exact open_helper LongData.dc3_ok LongData.open2_3
    · rw [show ds.length + 4 = 6 from by omega]
      exact open_helper LongData.dc4_ok LongData.open2_4
  · refine openOK_of_covered (key LongData.cs3 3 hn LongData.cov3) ?_
    interval_cases s
    · rw [show ds.length + 0 = 3 from by omega]
      exact open_helper LongData.dc0_ok LongData.open3_0
    · rw [show ds.length + 1 = 4 from by omega]
      exact open_helper LongData.dc1_ok LongData.open3_1
    · rw [show ds.length + 2 = 5 from by omega]
      exact open_helper LongData.dc2_ok LongData.open3_2
    · rw [show ds.length + 3 = 6 from by omega]
      exact open_helper LongData.dc3_ok LongData.open3_3
    · rw [show ds.length + 4 = 7 from by omega]
      exact open_helper LongData.dc4_ok LongData.open3_4
  · refine openOK_of_covered (key LongData.cs4 4 hn LongData.cov4) ?_
    interval_cases s
    · rw [show ds.length + 0 = 4 from by omega]
      exact open_helper LongData.dc0_ok LongData.open4_0
    · rw [show ds.length + 1 = 5 from by omega]
      exact open_helper LongData.dc1_ok LongData.open4_1
    · rw [show ds.length + 2 = 6 from by omega]
      exact open_helper LongData.dc2_ok LongData.open4_2
    · rw [show ds.length + 3 = 7 from by omega]
      exact open_helper LongData.dc3_ok LongData.open4_3
    · rw [show ds.length + 4 = 8 from by omega]
      exact open_helper LongData.dc4_ok LongData.open4_4

/-! ### Small faces -/

theorem armF_nil_left (S T : Finset ℕ) (U₂ : List (Finset ℕ)) (W : ℕ → ℕ → ℝ) {c : ℕ}
    (hc : c ∈ S) (d : ℕ) :
    armF S [] T U₂ W c d = ∑ t ∈ T, W c t * psum U₂ (nes U₂.length) t d := by
  unfold armF
  simp only [psum_nil]
  rw [Finset.sum_eq_single c (fun s _ hs => Finset.sum_eq_zero fun t _ => by
    rw [ite_eq_right hs, zero_mul, zero_mul]) (fun h => absurd hc h)]
  exact Finset.sum_congr rfl fun t _ => by rw [ite_eq_left rfl, one_mul]

/-- The loaded edge itself. -/
theorem faceOK_zero (S T : Finset ℕ) : FaceOK S [] T [] := by
  intro W hW A hA hin
  have h1 : faceConst3 (([] : List (Finset ℕ)).length + ([] : List (Finset ℕ)).length) = 1 := by
    norm_num [faceConst3]
  rw [h1, one_mul]
  refine hin.mono hW fun c hc d hd _ => le_of_eq ?_
  rw [armF_nil_left S T [] W hc d]
  simp only [psum_nil]
  rw [Finset.sum_eq_single d (fun t _ ht => by rw [ite_eq_right ht, mul_zero])
    (fun h => absurd hd h), ite_eq_left rfl, mul_one]

/-- A triangle. -/
theorem faceOK_tri {S T Lv : Finset ℕ} (hS : S.card = 3) (hT : T.card = 3) (hLv : Lv.card = 3) :
    FaceOK S [] T [Lv] := by
  intro W hW A hA hin
  obtain ⟨l0, l1, l2, l3⟩ := pathList_tri S Lv fun _ => T
  have key := ballTriClosed S Lv (fun _ => T) hS hLv (fun _ => hT)
    (fun j => if j = 0 then W else neP)
    (fun j c d => by split_ifs <;> [exact hW c d; exact neP_nonneg c d])
    (fun j => if j = 0 then A else 1) (fun j => by split_ifs <;> [exact hA; exact one_pos])
    (fun j => by
      fin_cases j
      · show InBall (pathList S Lv (fun _ => T) (Fin.castSucc 0))
          (pathList S Lv (fun _ => T) (Fin.succ 0)) W A
        rw [l0, l1]
        exact hin
      · show InBall (pathList S Lv (fun _ => T) (Fin.castSucc 1))
          (pathList S Lv (fun _ => T) (Fin.succ 1)) neP 1
        rw [l2, l3]
        exact inBall_ne T Lv)
  have hprod : (∏ j : Fin 2, if j = 0 then A else (1 : ℝ)) = A := by
    rw [Fin.prod_univ_two]
    simp
  have h1 : faceConst3 (([] : List (Finset ℕ)).length + [Lv].length) = 1 := faceConst3_one
  rw [hprod] at key
  rw [h1, one_mul]
  refine key.mono (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) fun j c d => by
    split_ifs <;> [exact hW c d; exact neP_nonneg c d]) fun c hc d hd _ => le_of_eq ?_
  rw [faceSum_eq_psum (fun _ => T) Lv _ c d hd, armF_nil_left S T [Lv] W hc d]
  show psum [T, Lv] [W, neP] c d = ∑ t ∈ T, W c t * psum [Lv] [neP] t d
  rfl

/-- A square with the loaded edge at the root end. -/
theorem faceOK_sq02 {S T Y Lv : Finset ℕ} (hS : S.card = 3) (hT : T.card = 3) (hY : Y.card = 3)
    (hLv : Lv.card = 3) : FaceOK S [] T [Y, Lv] := by
  intro W hW A hA hin
  obtain ⟨l0, l1, -, -, -, -⟩ := pathList_two S Lv ![T, Y]
  have key := ballFaceBare_two S Lv ![T, Y] hS hLv (fun j => by fin_cases j <;> assumption)
    0 W hW A hA (by rw [l0, l1]; exact hin)
  refine key.mono (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) fun j c d => by
    split_ifs <;> [exact hW c d; exact neP_nonneg c d]) fun c hc d hd _ => le_of_eq ?_
  rw [faceSum_two, armF_nil_left S T [Y, Lv] W hc d]
  refine Finset.sum_congr rfl fun t _ => ?_
  show _ = W c t * psum [Y, Lv] [neP, neP] t d
  rw [psum_cons, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [psum_single Lv neP y d hd]
  simp [neP]

/-- A square with the loaded edge in the middle. -/
theorem faceOK_sq11 {S T Lu Lv : Finset ℕ} (hS : S.card = 3) (hT : T.card = 3)
    (hLu : Lu.card = 3) (hLv : Lv.card = 3) : FaceOK S [Lu] T [Lv] := by
  intro W hW A hA hin
  obtain ⟨-, -, l2, l3, -, -⟩ := pathList_two Lu Lv ![S, T]
  have key := ballFaceBare_two Lu Lv ![S, T] hLu hLv (fun j => by fin_cases j <;> assumption)
    1 W hW A hA (by rw [l2, l3]; exact hin)
  refine key.mono (faceSum_nonneg _ _ _ (fun _ _ _ => zero_le_one) fun j c d => by
    split_ifs <;> [exact hW c d; exact neP_nonneg c d]) fun c hc d hd _ => le_of_eq ?_
  rw [faceSum_two]
  unfold armF
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  show _ = psum [Lu] [neP] s c * W s t * psum [Lv] [neP] t d
  rw [psum_single Lu neP s c hc, psum_single Lv neP t d hd, neP_comm s c]
  simp [neP]

/-! ### All faces -/

/-- **Every face with one loaded edge preserves the ball class.** -/
theorem faceOK_all : ∀ (m : ℕ) (S : Finset ℕ) (U₁ : List (Finset ℕ)) (T : Finset ℕ)
    (U₂ : List (Finset ℕ)), U₁.length + U₂.length = m → S.card = 3 → T.card = 3 →
    (∀ L ∈ U₁, L.card = 3) → (∀ L ∈ U₂, L.card = 3) → FaceOK S U₁ T U₂ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S U₁ T U₂ hm hS hT hU₁ hU₂
    by_cases h3 : 3 ≤ m
    · obtain ⟨ξ, hξ, hξm⟩ := exists_enum hS
      obtain ⟨ds₁, α₀, hc₁⟩ := exists_chain U₁ hU₁ ξ hξ
      obtain ⟨η, hη, hηm⟩ := exists_enum hT
      obtain ⟨ds₂, β₀, hc₂⟩ := exists_chain U₂ hU₂ η hη
      by_cases hr₂ : HasRed ds₂
      · exact faceOK_of_red hS hT hU₁ (fun U₂' hlen hU₂' =>
          ih (U₁.length + U₂'.length) (by omega) S U₁ T U₂' rfl hS hT hU₁ hU₂') hη hηm hc₂ hr₂
      by_cases hr₁ : HasRed ds₁
      · exact (faceOK_of_red hT hS hU₂ (fun U₁' hlen hU₁' =>
          ih (U₂.length + U₁'.length) (by omega) T U₂ S U₁' rfl hT hS hU₂ hU₁') hξ hξm hc₁
            hr₁).swap
      have hl₁ : U₁.length ≤ 4 := by
        by_contra h
        exact hr₁ (hasRed5 ds₁ (by rw [hc₁.length]; omega))
      have hl₂ : U₂.length ≤ 4 := by
        by_contra h
        exact hr₂ (hasRed5 ds₂ (by rw [hc₂.length]; omega))
      by_cases h2 : 2 ≤ U₁.length
      · exact faceOK_open hS hT hU₂ hξ hξm hc₁
          (openOK_table ds₁ hr₁ (by rw [hc₁.length]; exact h2) U₂.length hl₂
            (by rw [hc₁.length]; omega))
      · exact (faceOK_open hT hS hU₁ hη hηm hc₂
          (openOK_table ds₂ hr₂ (by rw [hc₂.length]; omega) U₁.length hl₁
            (by rw [hc₂.length]; omega))).swap
    · -- at most two interior vertices
      rcases U₁ with _ | ⟨a₁, _ | ⟨a₂, U₁⟩⟩
      · rcases U₂ with _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, U₂⟩⟩⟩
        · exact faceOK_zero S T
        · exact faceOK_tri hS hT (hU₂ b₁ (by simp))
        · exact faceOK_sq02 hS hT (hU₂ b₁ (by simp)) (hU₂ b₂ (by simp))
        · exfalso
          simp only [List.length_cons, List.length_nil] at hm
          omega
      · rcases U₂ with _ | ⟨b₁, _ | ⟨b₂, U₂⟩⟩
        · exact (faceOK_tri hT hS (hU₁ a₁ (by simp))).swap
        · exact faceOK_sq11 hS hT (hU₁ a₁ (by simp)) (hU₂ b₁ (by simp))
        · exfalso
          simp only [List.length_cons, List.length_nil] at hm
          omega
      · rcases U₁ with _ | ⟨a₃, U₁⟩
        · rcases U₂ with _ | ⟨b₁, U₂⟩
          · exact (faceOK_sq02 hT hS (hU₁ a₁ (by simp)) (hU₁ a₂ (by simp))).swap
          · exfalso
            simp only [List.length_cons, List.length_nil] at hm
            omega
        · exfalso
          simp only [List.length_cons] at hm
          omega

/-! ### Back to the face sum -/

theorem nes_reverse_map (n : ℕ) : ((nes n).reverse.map fun E a b => E b a) = nes n := by
  unfold nes
  rw [List.reverse_replicate, List.map_replicate]
  congr 1
  funext a b
  exact neP_comm b a

/-- A path sum with one loaded edge, in the two-arm form. -/
theorem psum_eq_armF (Lu : Finset ℕ) (V₁ : List (Finset ℕ)) (T : Finset ℕ)
    (U₂ : List (Finset ℕ)) (W : ℕ → ℕ → ℝ) {c : ℕ} (hc : c ∈ Lu) (d : ℕ) :
    psum (V₁ ++ T :: U₂) (nes V₁.length ++ W :: nes U₂.length) c d
      = armF (V₁.getLastD Lu) (Lu :: V₁).reverse.tail T U₂ W c d := by
  rcases eq_nil_or_snoc V₁ with rfl | ⟨A, S, rfl⟩
  · show psum (T :: U₂) (W :: nes U₂.length) c d = armF Lu [] T U₂ W c d
    rw [armF_nil_left Lu T U₂ W hc d]
    rfl
  · have hlast : (A ++ [S]).getLastD Lu = S := by rw [getLastD_append]; rfl
    have hrev : (Lu :: (A ++ [S])).reverse.tail = A.reverse ++ [Lu] := by simp
    rw [hlast, hrev, List.append_assoc]
    show psum (A ++ S :: (T :: U₂)) (nes (A ++ [S]).length ++ W :: nes U₂.length) c d = _
    rw [psum_append A S (T :: U₂) _ _ (by simp [nes])]
    unfold armF
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [psum_cons, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e := psum_reverse A (nes (A ++ [S]).length) Lu S (by simp [nes]) c hc s hs
    rw [nes_reverse_map] at e
    rw [e]
    have hl : (A.reverse ++ [Lu]).length = (A ++ [S]).length := by simp
    rw [hl]
    ring

theorem pathList_succ_tail {m : ℕ} (Lu Lv : Finset ℕ) (Li : Fin (m + 1) → Finset ℕ)
    (i : Fin (m + 2)) : pathList Lu Lv Li i.succ = pathList (Li 0) Lv (Fin.tail Li) i := by
  unfold pathList
  rw [Fin.cons_succ]
  have e : (Fin.snoc Li Lv : Fin (m + 2) → Finset ℕ)
      = Fin.cons (Li 0) (Fin.snoc (Fin.tail Li) Lv) := by
    rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
  rw [e]

/-- The lists of a face, split at its loaded edge. -/
theorem face_pos : ∀ (m : ℕ) (Li : Fin m → Finset ℕ) (Lu Lv : Finset ℕ) (j₀ : Fin (m + 1)),
    ∃ V₁ T U₂, List.ofFn Li ++ [Lv] = V₁ ++ T :: U₂ ∧ V₁.length = j₀.val ∧
      V₁.length + U₂.length = m ∧ V₁.getLastD Lu = pathList Lu Lv Li j₀.castSucc ∧
      T = pathList Lu Lv Li j₀.succ ∧ U₂.getLastD T = Lv
  | 0, Li, Lu, Lv, j₀ => by
    obtain rfl : j₀ = 0 := Fin.ext (by have := j₀.isLt; omega)
    refine ⟨[], Lv, [], by simp, rfl, rfl, ?_, ?_, rfl⟩
    · exact (consSnoc_zero _ _ _ _ (by simp)).symm
    · exact (consSnoc_last _ _ _ _ (by simp)).symm
  | m + 1, Li, Lu, Lv, j₀ => by
    refine Fin.cases ?_ (fun j' => ?_) j₀
    · refine ⟨[], Li 0, List.ofFn (Fin.tail Li) ++ [Lv], ?_, rfl, ?_, ?_, ?_, ?_⟩
      · rw [List.ofFn_succ]
        rfl
      · simp
      · exact (consSnoc_zero _ _ _ _ (by simp)).symm
      · exact (consSnoc_mid _ _ _ _ (0 : Fin (m + 1)) (by simp)).symm
      · rw [getLastD_append]
        rfl
    · obtain ⟨V₁, T, U₂, hl, hlen, hsum, hS, hT, hlast⟩ := face_pos m (Fin.tail Li) (Li 0) Lv j'
      refine ⟨Li 0 :: V₁, T, U₂, ?_, ?_, ?_, ?_, ?_, hlast⟩
      · rw [List.ofFn_succ, List.cons_append]
        exact congrArg (Li 0 :: ·) hl
      · simp [hlen]
      · simp only [List.length_cons]
        omega
      · rw [getLastD_cons, hS]
        exact (pathList_succ_tail Lu Lv Li j'.castSucc).symm
      · rw [hT]
        exact (pathList_succ_tail Lu Lv Li j'.succ).symm

theorem ofFn_faceEs : ∀ (m : ℕ) (j₀ : Fin (m + 1)) (W : ℕ → ℕ → ℝ),
    List.ofFn (fun j : Fin (m + 1) => if j = j₀ then W else fun c d => if c ≠ d then 1 else 0)
      = nes j₀.val ++ W :: nes (m - j₀.val)
  | 0, j₀, W => by
    obtain rfl : j₀ = 0 := Fin.ext (by have := j₀.isLt; omega)
    rfl
  | m + 1, j₀, W => by
    refine Fin.cases ?_ (fun j' => ?_) j₀
    · rw [List.ofFn_succ]
      have e : (fun i : Fin (m + 1) => if i.succ = (0 : Fin (m + 2)) then W
          else fun c d => if c ≠ d then (1 : ℝ) else 0) = fun _ => neP := by
        funext i
        rw [ite_eq_right (Fin.succ_ne_zero i)]
        rfl
      rw [e, List.ofFn_const]
      rfl
    · rw [List.ofFn_succ]
      have e : (fun i : Fin (m + 1) => if i.succ = j'.succ then W
          else fun c d => if c ≠ d then (1 : ℝ) else 0)
          = fun i : Fin (m + 1) => if i = j' then W else fun c d => if c ≠ d then 1 else 0 := by
        funext i
        simp only [Fin.succ_inj]
      rw [e, ofFn_faceEs m j' W, ite_eq_right (Fin.succ_ne_zero j').symm]
      simp only [Fin.val_succ, Nat.add_sub_add_right]
      rfl

/-- **Every face with one loaded edge preserves the ball class**, for the face sum. -/
theorem ballFaceBare_all (m : ℕ) : BallFaceBare m := by
  intro Lu Lv Li hLu hLv hLi j₀ W hW A hA hin
  obtain ⟨V₁, T, U₂, hl, hlen, hsum, hS, hT, hlast⟩ := face_pos m Li Lu Lv j₀
  have hmem : ∀ L ∈ V₁ ++ T :: U₂, L.card = 3 := by
    rw [← hl]
    intro L hL
    rcases List.mem_append.mp hL with h | h
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp h
      exact hLi i
    · rw [List.mem_singleton.mp h]
      exact hLv
  have hV₁ : ∀ L ∈ V₁, L.card = 3 := fun L hL => hmem L (List.mem_append_left _ hL)
  have hTc : T.card = 3 := hmem T (List.mem_append_right _ List.mem_cons_self)
  have hU₂ : ∀ L ∈ U₂, L.card = 3 := fun L hL =>
    hmem L (List.mem_append_right _ (List.mem_cons_of_mem _ hL))
  have hSc : (V₁.getLastD Lu).card = 3 := card_getLastD hLu hV₁
  have hU₁ : ∀ L ∈ (Lu :: V₁).reverse.tail, L.card = 3 := fun L hL => by
    have h1 : L ∈ (Lu :: V₁).reverse := List.mem_of_mem_tail hL
    rcases List.mem_cons.mp (List.mem_reverse.mp h1) with rfl | h'
    · exact hLu
    · exact hV₁ L h'
  have hlen₁ : ((Lu :: V₁).reverse.tail).length = V₁.length := by simp
  have hlastU : ((Lu :: V₁).reverse.tail).getLastD (V₁.getLastD Lu) = Lu := by
    rcases eq_nil_or_snoc V₁ with rfl | ⟨A, S, rfl⟩
    · rfl
    · have hrev : (Lu :: (A ++ [S])).reverse.tail = A.reverse ++ [Lu] := by simp
      rw [hrev, getLastD_append]
      rfl
  have hin' : InBall (V₁.getLastD Lu) T W A := by
    rw [hS, hT]
    exact hin
  have key := faceOK_all m (V₁.getLastD Lu) (Lu :: V₁).reverse.tail T U₂ (by rw [hlen₁]; exact hsum)
    hSc hTc hU₁ hU₂ W hW A hA hin'
  rw [hlastU, hlast, hlen₁, hsum] at key
  refine key.mono (armF_nonneg hW) fun c hc d hd _ => le_of_eq ?_
  rw [faceSum_eq_psum Li Lv _ c d hd, ofFn_faceEs m j₀ W, hl, ← psum_eq_armF Lu V₁ T U₂ W hc d,
    hlen]
  have hq : m - j₀.val = U₂.length := by omega
  rw [hq]

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Three colours when every even face has at most one loaded edge.** A graph built from an
edge by ears on edges is `3`-ECC if an ear with an even number of vertices on an active edge
makes at most one of its new edges active, and an ear on a tame edge has an odd number of
vertices and makes none active; an ear with an odd number of vertices on an active edge may make
any of its new edges active. So below every face of even length at most one edge may lead to
another face of even length, and faces of odd length are unrestricted. -/
theorem ecc_three_of_oneLoadBuilt {act : Finset (V × V)} (h : OneLoadBuilt G Finset.univ act) :
    G.ECCAt 3 :=
  ecc_three_of_oneLoadBuilt_of_bare G (fun m _ => ballFaceBare_all m) domFaceClosed_odd
    (fun m hodd h3 => ballOddClosed m hodd h3) h

/-- `OddEarBuilt G S`: the induced subgraph on `S` is built from an edge by ears on edges, each
with an odd number of new vertices. Every bounded face then has odd length, wherever the
triangles are. -/
inductive OddEarBuilt : Finset V → Prop
  | edge (u v : V) (huv : G.Adj u v) : OddEarBuilt {u, v}
  | face (S : Finset V) (m : ℕ) (u v : V) (x : Fin m → V) (he : IsEar G S u v x) (hodd : Odd m)
      (hS : OddEarBuilt S) : OddEarBuilt (S ∪ Finset.univ.image x)

omit [Fintype V] [DecidableRel G.Adj] in
variable {G} in
/-- Odd ears never load an edge. -/
theorem OddEarBuilt.oneLoadBuilt {S : Finset V} (h : OddEarBuilt G S) :
    ∃ act, OneLoadBuilt G S act := by
  induction h with
  | edge u v huv => exact ⟨_, OneLoadBuilt.edge u v huv⟩
  | face S m u v x he hodd _ ih =>
    obtain ⟨act, hact⟩ := ih
    exact ⟨_, OneLoadBuilt.face S act m u v x he ∅ (fun h => absurd h Finset.not_nonempty_empty)
      (fun _ _ => Or.inl (by simp)) (fun _ => hodd) hact⟩

/-- **All bounded faces odd.** A graph built from an edge by ears with an odd number of vertices
is `3`-ECC. -/
theorem ecc_three_of_oddEarBuilt (h : OddEarBuilt G Finset.univ) : G.ECCAt 3 := by
  obtain ⟨act, hact⟩ := h.oneLoadBuilt
  exact ecc_three_of_oneLoadBuilt G hact

end Outerplanar
