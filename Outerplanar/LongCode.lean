/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.OpenArm

/-!
# Faces of length at least five: the finite checks on codes

The codes of an arm (`Outerplanar/Chain.lean`) either contain a *reducible window* — a stretch to
which one of the three rules of `Outerplanar/Arms.lean` applies (`HasRed`) — or the arm is short
and its chain matrix dominates one of a few minimal matrices, for which the open-arm rule holds
by a certificate (`Covered`).

Both alternatives are decided by exhaustive searches over lists of codes that stop at a
reducible window ending at the last code:

* `allRed n ds` — every extension of `ds` by `n` codes has a reducible window;
* `allOpen cs n ds` — every extension of `ds` by `n` codes has a reducible window or is covered
  by the list `cs` of matrices.

The searches are evaluated by the kernel in `Outerplanar/LongData.lean`.
-/

namespace Outerplanar

/-- One of the three rules applies to the stretch with codes `ds`. -/
def redCode (ds : List (Fin 3 → Bool)) : Bool := cutCode ds || sh1Code ds || sh0Code ds

/-- Some window of `ds` is reducible. -/
def HasRed (ds : List (Fin 3 → Bool)) : Prop :=
  ∃ dP dS dR, ds = dP ++ dS ++ dR ∧ redCode dS = true

theorem HasRed.append_right {ds : List (Fin 3 → Bool)} (h : HasRed ds)
    (e : List (Fin 3 → Bool)) : HasRed (ds ++ e) := by
  obtain ⟨dP, dS, dR, rfl, hr⟩ := h
  exact ⟨dP, dS, dR ++ e, by simp [List.append_assoc], hr⟩

/-- Some window ending at the last code is reducible. -/
def sufRed (ds : List (Fin 3 → Bool)) : Bool :=
  (List.range ds.length).any fun i => redCode (ds.drop i)

theorem hasRed_of_sufRed {ds : List (Fin 3 → Bool)} (h : sufRed ds = true) : HasRed ds := by
  obtain ⟨i, -, hi⟩ := List.any_eq_true.mp h
  exact ⟨ds.take i, ds.drop i, [], by simp, hi⟩

/-- Every extension of `ds` by `n` codes has a reducible window. -/
def allRed : ℕ → List (Fin 3 → Bool) → Bool
  | 0, ds => sufRed ds
  | n + 1, ds => sufRed ds || all8 fun k => allRed n (ds ++ [bitsOf k])

theorem allRed_sound : ∀ (n : ℕ) (ds : List (Fin 3 → Bool)), allRed n ds = true →
    ∀ e : List (Fin 3 → Bool), e.length = n → HasRed (ds ++ e)
  | 0, ds, h, e, he => by
    obtain rfl : e = [] := List.eq_nil_of_length_eq_zero he
    rw [List.append_nil]
    exact hasRed_of_sufRed h
  | n + 1, ds, h, e, he => by
    rw [allRed] at h
    rcases Bool.or_eq_true_iff.mp h with h1 | h1
    · exact (hasRed_of_sufRed h1).append_right e
    · obtain ⟨d, e', rfl⟩ : ∃ d e', e = d :: e' := by
        cases e with
        | nil => simp at he
        | cons d e' => exact ⟨d, e', rfl⟩
      obtain ⟨k, hk, rfl⟩ := exists_bits d
      have h2 := allRed_sound n (ds ++ [bitsOf k]) (all8_lt h1 hk) e' (by simpa using he)
      rwa [List.append_assoc] at h2

/-- An arm of five or more edges has a reducible window. -/
theorem hasRed_of_five (h5 : allRed 5 [] = true) (ds : List (Fin 3 → Bool))
    (hlen : 5 ≤ ds.length) : HasRed ds := by
  have h1 := allRed_sound 5 [] h5 (ds.take 5) (by rw [List.length_take]; omega)
  have h2 := h1.append_right (ds.drop 5)
  simpa using h2

/-! ### Coverage by a list of matrices -/

/-- The chain matrix, packed with 8 bits per entry. -/
def packM (ds : List (Fin 3 → Bool)) : ℕ :=
  chainM ds 0 0 + 256 * chainM ds 0 1 + 256 ^ 2 * chainM ds 0 2 + 256 ^ 3 * chainM ds 1 0
    + 256 ^ 4 * chainM ds 1 1 + 256 ^ 5 * chainM ds 1 2 + 256 ^ 6 * chainM ds 2 0
    + 256 ^ 7 * chainM ds 2 1 + 256 ^ 8 * chainM ds 2 2

/-- `p 0 || … || p 5`. -/
def any6 (p : ℕ → Bool) : Bool := p 0 || p 1 || p 2 || p 3 || p 4 || p 5

theorem any6_exists {p : ℕ → Bool} (h : any6 p = true) : ∃ t, t < 6 ∧ p t = true := by
  simp only [any6, Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  exacts [⟨0, by norm_num, h⟩, ⟨1, by norm_num, h⟩, ⟨2, by norm_num, h⟩, ⟨3, by norm_num, h⟩,
    ⟨4, by norm_num, h⟩, ⟨5, by norm_num, h⟩]

/-- For every mismatch `ρ` of the frames, some renumbering `τ` makes the chain matrix dominate a
matrix of the list `cs` (given by codes, 8 bits per entry). -/
def Covered (cs : List ℕ) (ds : List (Fin 3 → Bool)) : Prop :=
  ∀ ρ : Fin 3 → Fin 3, Function.Bijective ρ → ∃ τ : Fin 3 → Fin 3, Function.Bijective τ ∧
    ∃ c ∈ cs, ∀ a y : Fin 3, dig 8 c (3 * a.val + y.val) ≤ chainM ds (τ y) (ρ (τ a))

/-- The check of `Covered`. -/
def covered (cs : List ℕ) (ds : List (Fin 3 → Bool)) : Bool :=
  (all3F2 fun x y => dig 8 (packM ds) (3 * x.val + y.val) == chainM ds x y) &&
  all6 fun r => any6 fun t => cs.any fun c => all3F2 fun a y =>
    decide (dig 8 c (3 * a.val + y.val)
      ≤ dig 8 (packM ds) (3 * (perm6 t y).val + (perm6 r (perm6 t a)).val))

theorem covered_sound {cs : List ℕ} {ds : List (Fin 3 → Bool)} (h : covered cs ds = true) :
    Covered cs ds := by
  rw [covered, Bool.and_eq_true] at h
  obtain ⟨hpack, hall⟩ := h
  intro ρ hρ
  obtain ⟨r, rfl⟩ := exists_perm6 ρ hρ.1
  obtain ⟨t, ht, h1⟩ := any6_exists (all6_lt hall r.isLt)
  obtain ⟨c, hc, h2⟩ := List.any_eq_true.mp h1
  refine ⟨perm6 t, perm6_bij ⟨t, ht⟩, c, hc, fun a y => ?_⟩
  have h3 := of_decide_eq_true (all3F2_apply h2 a y)
  have h4 := all3F2_apply hpack (perm6 t y) (perm6 r.val (perm6 t a))
  rw [beq_iff_eq] at h4
  rw [h4] at h3
  exact h3

/-- Every extension of `ds` by `n` codes has a reducible window or is covered by `cs`. -/
def allOpen (cs : List ℕ) : ℕ → List (Fin 3 → Bool) → Bool
  | 0, ds => sufRed ds || covered cs ds
  | n + 1, ds => sufRed ds || all8 fun k => allOpen cs n (ds ++ [bitsOf k])

theorem allOpen_sound (cs : List ℕ) : ∀ (n : ℕ) (ds : List (Fin 3 → Bool)),
    allOpen cs n ds = true → ∀ e : List (Fin 3 → Bool), e.length = n →
      HasRed (ds ++ e) ∨ Covered cs (ds ++ e)
  | 0, ds, h, e, he => by
    obtain rfl : e = [] := List.eq_nil_of_length_eq_zero he
    rw [List.append_nil]
    rw [allOpen] at h
    rcases Bool.or_eq_true_iff.mp h with h1 | h1
    · exact Or.inl (hasRed_of_sufRed h1)
    · exact Or.inr (covered_sound h1)
  | n + 1, ds, h, e, he => by
    rw [allOpen] at h
    rcases Bool.or_eq_true_iff.mp h with h1 | h1
    · exact Or.inl ((hasRed_of_sufRed h1).append_right e)
    · obtain ⟨d, e', rfl⟩ : ∃ d e', e = d :: e' := by
        cases e with
        | nil => simp at he
        | cons d e' => exact ⟨d, e', rfl⟩
      obtain ⟨k, hk, rfl⟩ := exists_bits d
      have h2 := allOpen_sound cs n (ds ++ [bitsOf k]) (all8_lt h1 hk) e' (by simpa using he)
      rwa [List.append_assoc] at h2

/-! ### From certificates to the open-arm rule -/

/-- The face of the open-arm rule as numbers: first arm matrix `c`, the diagonal pattern on the
loaded edge, walks `dc` on the second arm, no equal colours at the root. -/
def openCase (c dc : ℕ) : GCase := ⟨c, 0x111, dc, 0⟩

theorem bitAt_id : ∀ s t : Fin 3, bitAt 0x111 (3 * s.val + t.val) = decide (s = t) := by
  decide +kernel

theorem bitAt_zero : ∀ s t : Fin 3, bitAt 0 (3 * s.val + t.val) = false := by decide +kernel

theorem openCase_El (c dc : ℕ) : (openCase c dc).El = idPat :=
  funext fun s => funext fun t => bitAt_id s t

theorem openCase_Er (c dc : ℕ) : (openCase c dc).Er = noPat :=
  funext fun s => funext fun t => bitAt_zero s t

theorem genOK_of_open {α c dc s : ℕ} {L : List Inst}
    (hd : ∀ t b : Fin 3, dig 8 dc (3 * t.val + b.val) = dMat s t b)
    (h : checkCase α (openCase c dc) L = true) :
    GenOK (fun a y : Fin 3 => dig 8 c (3 * a.val + y.val)) idPat (dMat s) noPat α := by
  have h1 := checkCase_sound h
  rw [openCase_El, openCase_Er] at h1
  have e2 : (openCase c dc).B₂ = dMat s := funext fun t => funext fun b => hd t b
  rw [e2] at h1
  exact h1

theorem openOK_of_covered {cs : List ℕ} {ds : List (Fin 3 → Bool)} {s : ℕ}
    (hcov : Covered cs ds)
    (hcs : ∀ c ∈ cs, GenOK (fun a y : Fin 3 => dig 8 c (3 * a.val + y.val)) idPat (dMat s) noPat
      (faceN (ds.length + s))) : OpenOK ds s := fun ρ hρ => by
  obtain ⟨τ, hτ, c, hc, hle⟩ := hcov ρ hρ
  exact ⟨τ, hτ, _, hcs c hc, hle⟩

end Outerplanar
