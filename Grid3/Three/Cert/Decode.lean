import Grid3.Three.Cert.Checker
import Grid3.Three.Cert.Digits

/-!
# Reflection, part 1: the packed pass as a fold over an explicit entry list

`passR`/`passQ` decode entries from a packed literal on the fly. Here we define the decoded entry
lists and show that the passes are `List.foldl` over them; then the accumulator fields are explicit
sums over the entries, and `ok = true` gives the per-entry facts and strict monotonicity.
No Mathlib: everything is `Nat`/`Int`/`List` arithmetic.
-/

namespace Grid3.Three.Cert

/-- decoded rational entry `(s, t, v0, k)` -/
abbrev EntR := Nat × Nat × Nat × Nat
/-- decoded `ℚ(√17)` entry `(s, t, v0, v1, k)` -/
abbrev EntQ := Nat × Nat × Nat × Int × Nat

def entriesR (fr : Bool) : Nat → Nat → List EntR
  | 0, _ => []
  | n + 1, x =>
    if fr then
      let e := x % 100000000000000000
      (e / 1000000000000000, (e / 10000000000000) % 100, e % 1000000, (e / 1000000) % 10000000)
        :: entriesR fr n (x / 100000000000000000)
    else
      let e := x % 10000000000
      (e / 100000000, (e / 1000000) % 100, e % 1000000, 0) :: entriesR fr n (x / 10000000000)

def entriesQ (fr : Bool) : Nat → Nat → List EntQ
  | 0, _ => []
  | n + 1, x =>
    if fr then
      let e := x % 100000000000000000000000
      (e / 1000000000000000000000, (e / 10000000000000000000) % 100, e % 1000000,
        (((e / 1000000) % 1000000 : Nat) - (OFF : Nat) : Int), (e / 1000000000000) % 10000000)
        :: entriesQ fr n (x / 100000000000000000000000)
    else
      let e := x % 10000000000000000
      (e / 100000000000000, (e / 1000000000000) % 100, e % 1000000,
        (((e / 1000000) % 1000000 : Nat) - (OFF : Nat) : Int), 0)
        :: entriesQ fr n (x / 10000000000000000)

def stepR' (fr : Bool) (L R : Col) (a : AccR) (e : EntR) : AccR :=
  stepR fr L R a e.1 e.2.1 e.2.2.1 e.2.2.2
def stepQ' (fr : Bool) (L R : Col) (a : AccQ) (e : EntQ) : AccQ :=
  stepQ fr L R a e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2

theorem passR_eq_foldl (fr : Bool) (L R : Col) :
    ∀ n x a, passR fr L R n x a = (entriesR fr n x).foldl (stepR' fr L R) a := by
  intro n
  induction n with
  | zero => intro x a; rfl
  | succ n ih =>
    intro x a
    cases fr <;> simp only [passR, entriesR, List.foldl, stepR', ih, Bool.false_eq_true, ↓reduceIte]

theorem passQ_eq_foldl (fr : Bool) (L R : Col) :
    ∀ n x a, passQ fr L R n x a = (entriesQ fr n x).foldl (stepQ' fr L R) a := by
  intro n
  induction n with
  | zero => intro x a; rfl
  | succ n ih =>
    intro x a
    cases fr <;> simp only [passQ, entriesQ, List.foldl, stepQ', ih, Bool.false_eq_true, ↓reduceIte]

/-! ### Accumulator fields as sums -/

def sumR (f : EntR → Nat) : List EntR → Nat
  | [] => 0
  | e :: es => f e + sumR f es

theorem foldl_stepR_r0 (fr : Bool) (L R : Col) :
    ∀ (es : List EntR) (a : AccR),
      (es.foldl (stepR' fr L R) a).r0 = a.r0 + sumR (fun e => e.2.2.1 * B ^ e.1) es := by
  intro es
  induction es with
  | nil => intro a; simp [sumR]
  | cons e es ih =>
    intro a
    simp only [List.foldl, ih, stepR', stepR, sumR]
    omega

theorem foldl_stepR_c0 (fr : Bool) (L R : Col) :
    ∀ (es : List EntR) (a : AccR),
      (es.foldl (stepR' fr L R) a).c0 = a.c0 + sumR (fun e => e.2.2.1 * B ^ e.2.1) es := by
  intro es
  induction es with
  | nil => intro a; simp [sumR]
  | cons e es ih =>
    intro a
    simp only [List.foldl, ih, stepR', stepR, sumR]
    omega

theorem foldl_stepR_q (fr : Bool) (L R : Col) :
    ∀ (es : List EntR) (a : AccR),
      (es.foldl (stepR' fr L R) a).q
        = a.q + sumR (fun e => 108 * (L.lcm / ((L.CV / 100 ^ e.1) % 100)) * (289 * e.2.2.1 * e.2.2.1)) es := by
  intro es
  induction es with
  | nil => intro a; simp [sumR]
  | cons e es ih =>
    intro a
    simp only [List.foldl, ih, stepR', stepR, sumR]
    omega

theorem foldl_stepR_nr (fr : Bool) (L R : Col) :
    ∀ (es : List EntR) (a : AccR),
      (es.foldl (stepR' fr L R) a).nr = a.nr + sumR (fun e => e.2.2.1 * e.2.2.2) es := by
  intro es
  induction es with
  | nil => intro a; simp [sumR]
  | cons e es ih =>
    intro a
    simp only [List.foldl, ih, stepR', stepR, sumR]
    omega

/-- the per-entry condition recorded in `ok` -/
def entOKR (fr : Bool) (L R : Col) (prev : Nat) (e : EntR) : Bool :=
  prev < e.1 * 100 + e.2.1 + 1 && e.1 < L.n && e.2.1 < R.n
    && compat (stateAt L.P e.1) (stateAt R.P e.2.1)
    && (!fr || LD * E ^ 4 * e.2.2.1 ≤ e.2.2.2 ^ 4 * ((L.CV / 100 ^ e.1) % 100) * XD)

/-- packed `(s, t)` index of an entry -/
def idxR (e : EntR) : Nat := e.1 * 100 + e.2.1

/-- every entry satisfies its condition against the previous packed index -/
def chainR (fr : Bool) (L R : Col) : Nat → List EntR → Prop
  | _, [] => True
  | prev, e :: es => entOKR fr L R prev e = true ∧ chainR fr L R (idxR e + 1) es

theorem foldl_stepR_prev' (fr : Bool) (L R : Col) (a : AccR) (e : EntR) :
    (stepR' fr L R a e).prev = idxR e + 1 := rfl

theorem foldl_stepR_ok (fr : Bool) (L R : Col) :
    ∀ (es : List EntR) (a : AccR), (es.foldl (stepR' fr L R) a).ok = true →
      a.ok = true ∧ chainR fr L R a.prev es := by
  intro es
  induction es with
  | nil => intro a h; exact ⟨h, trivial⟩
  | cons e es ih =>
    intro a h
    simp only [List.foldl] at h
    obtain ⟨hok, hrest⟩ := ih _ h
    have hprev : (stepR' fr L R a e).prev = idxR e + 1 := rfl
    rw [hprev] at hrest
    simp only [stepR', stepR] at hok
    refine ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).1, ?_, hrest⟩
    simp only [entOKR, Bool.and_eq_true_iff]
    have h1 := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).2
    have h2 := (Bool.and_eq_true_iff.mp hok).2
    simp only [Bool.and_eq_true_iff] at h1
    exact ⟨h1, h2⟩

/-- the packed indices along a chain are strictly increasing, and every entry satisfies the
non-`prev` part of its condition -/
theorem chainR_mem (fr : Bool) (L R : Col) :
    ∀ (es : List EntR) (prev : Nat), chainR fr L R prev es →
      ∀ e ∈ es, prev < idxR e + 1 ∧ e.1 < L.n ∧ e.2.1 < R.n
        ∧ compat (stateAt L.P e.1) (stateAt R.P e.2.1) = true
        ∧ (fr = true → LD * E ^ 4 * e.2.2.1 ≤ e.2.2.2 ^ 4 * ((L.CV / 100 ^ e.1) % 100) * XD) := by
  intro es
  induction es with
  | nil => intro prev _ e he; exact absurd he List.not_mem_nil
  | cons e es ih =>
    intro prev hc e' he'
    obtain ⟨hok, hrest⟩ := hc
    rcases List.mem_cons.mp he' with rfl | hmem
    · simp only [entOKR, Bool.and_eq_true_iff, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hok
      refine ⟨h1, h2, h3, h4, fun hfr => ?_⟩
      rcases h5 with h5 | h5
      · rw [hfr] at h5; exact absurd h5 (by decide)
      · exact h5
    · have := ih _ hrest e' hmem
      refine ⟨?_, this.2⟩
      have hlt : prev < idxR e + 1 := by
        simp only [entOKR, Bool.and_eq_true_iff, decide_eq_true_eq] at hok
        exact hok.1.1.1.1
      omega

/-- along a chain, two distinct positions have distinct packed indices -/
theorem chainR_nodup_idx (fr : Bool) (L R : Col) :
    ∀ (es : List EntR) (prev : Nat), chainR fr L R prev es → (es.map idxR).Nodup := by
  intro es
  induction es with
  | nil => intro _ _; exact List.nodup_nil
  | cons e es ih =>
    intro prev hc
    obtain ⟨_, hrest⟩ := hc
    refine List.nodup_cons.mpr ⟨?_, ih _ hrest⟩
    intro hmem
    obtain ⟨e', he', heq⟩ := List.mem_map.mp hmem
    have := (chainR_mem fr L R es _ hrest e' he').1
    omega

/-! ### Row and column sums -/

/-- the `v0`-sum of the entries in row `s` -/
def rowSumR (es : List EntR) (s : Nat) : Nat := sumR (fun e => if e.1 = s then e.2.2.1 else 0) es
/-- the `v0`-sum of the entries in column `t` -/
def colSumR (es : List EntR) (t : Nat) : Nat := sumR (fun e => if e.2.1 = t then e.2.2.1 else 0) es

theorem sumR_add (f g : EntR → Nat) : ∀ es, sumR (fun e => f e + g e) es = sumR f es + sumR g es := by
  intro es; induction es with
  | nil => rfl
  | cons e es ih => simp only [sumR, ih]; omega

theorem pkList_range_sumR (key f : EntR → Nat) :
    ∀ (es : List EntR) (n : Nat), pkList B (fun s => sumR (fun e => if key e = s then f e else 0) es) (List.range n) 0
      = sumR (fun e => if key e < n then f e * B ^ key e else 0) es := by
  intro es
  induction es with
  | nil =>
    intro n
    simp only [sumR]
    exact pkList_zero_of B _ (List.range n) 0 (fun _ _ => rfl)
  | cons e es ih =>
    intro n
    have hsplit : (fun s => sumR (fun e' => if key e' = s then f e' else 0) (e :: es))
        = fun s => (if key e = s then f e else 0) + sumR (fun e' => if key e' = s then f e' else 0) es := by
      funext s; rfl
    rw [hsplit, pkList_add, ih]
    simp only [sumR]
    congr 1
    by_cases h : key e < n
    · have hnd : (List.range n).Nodup := List.nodup_range
      have hmem : key e < (List.range n).length := by simpa using h
      have hget : (List.range n)[key e]'hmem = key e := by simp
      have := pkList_single B (f e) (List.range n) 0 (key e) hmem hnd
      rw [Nat.zero_add] at this
      rw [if_pos h, ← this]
      congr 1; funext s
      rw [hget]
      by_cases hs : key e = s
      · subst hs; simp
      · simp [hs, Ne.symm hs]
    · rw [if_neg h]
      exact pkList_zero_of B _ (List.range n) 0 (fun s hs => by
        rw [List.mem_range] at hs; rw [if_neg]; omega)

def sumNat : List Nat → Nat
  | [] => 0
  | x :: l => x + sumNat l

/-! ### The column structure -/

def countsList (sub : Nat) (pats : List Nat) (sts : List Nat) : List Nat := sts.map (countOf sub pats)

theorem countOf_lt (sub : Nat) (pats : List Nat) (st : Nat) : countOf sub pats st < 100 :=
  Nat.mod_lt _ (by decide)

/-- `colFold` on a non-uniform column, with explicit start fields (`n = i`) -/
theorem colFold_false_spec (sub : Nat) (pats : List Nat) :
    ∀ (sts : List Nat) (i P CV e0 aba abc l sc sc2 : Nat) (u : Bool),
      let c' := colFold false sub pats sts i ⟨i, P, CV, u, e0, aba, abc, l, sc, sc2⟩
      c'.n = i + sts.length ∧ c'.P = P ∧ c'.isU = u
        ∧ c'.CV = CV + pkList 100 (countOf sub pats) sts i
        ∧ c'.exp0 = e0 + pkList B (fun st => 1000 * countOf sub pats st) sts i
        ∧ c'.lcm = sts.foldl (fun l st => Nat.lcm l (countOf sub pats st)) l
        ∧ c'.sumC = sc + sumNat (countsList sub pats sts)
        ∧ c'.sumC2 = sc2 + sumNat ((countsList sub pats sts).map fun k => k * k)
        ∧ c'.abaMask = aba ∧ c'.abcMask = abc := by
  intro sts
  induction sts with
  | nil => intro i P CV e0 aba abc l sc sc2 u; simp [colFold, pkList, countsList, sumNat]
  | cons st sts ih =>
    intro i P CV e0 aba abc l sc sc2 u
    simp only [colFold, Bool.false_eq_true, ↓reduceIte]
    have := ih (i + 1) P (CV + countOf sub pats st * 100 ^ i) (e0 + 1000 * countOf sub pats st * B ^ i)
      aba abc (Nat.lcm l (countOf sub pats st)) (sc + countOf sub pats st)
      (sc2 + countOf sub pats st * countOf sub pats st) u
    simp only [pkList, countsList, List.map, sumNat, List.foldl, List.length] at this ⊢
    refine ⟨by omega, this.2.1, this.2.2.1, by rw [this.2.2.2.1]; omega, by rw [this.2.2.2.2.1]; omega,
      this.2.2.2.2.2.1, by rw [this.2.2.2.2.2.2.1]; omega, by rw [this.2.2.2.2.2.2.2.1]; omega,
      this.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2⟩

/-- `colFold` on the uniform column -/
theorem colFold_true_spec (sub : Nat) (pats : List Nat) :
    ∀ (sts : List Nat) (i P CV e0 aba abc l sc sc2 : Nat) (u : Bool),
      let c' := colFold true sub pats sts i ⟨i, P, CV, u, e0, aba, abc, l, sc, sc2⟩
      c'.n = i + sts.length ∧ c'.P = P ∧ c'.isU = u ∧ c'.CV = CV ∧ c'.lcm = l
        ∧ c'.exp0 = e0 + pkList B (fun _ => 9000) sts i
        ∧ c'.abaMask = aba + pkList B (fun st => if isABA st then 1 else 0) sts i
        ∧ c'.abcMask = abc + pkList B (fun st => if isABA st then 0 else 1) sts i := by
  intro sts
  induction sts with
  | nil => intro i P CV e0 aba abc l sc sc2 u; simp [colFold, pkList]
  | cons st sts ih =>
    intro i P CV e0 aba abc l sc sc2 u
    simp only [colFold, ↓reduceIte]
    have := ih (i + 1) P CV (e0 + 9000 * B ^ i) (if isABA st then aba + B ^ i else aba)
      (if isABA st then abc else abc + B ^ i) l sc sc2 u
    simp only [pkList, List.length] at this ⊢
    refine ⟨by omega, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
      by rw [this.2.2.2.2.2.1]; omega, ?_, ?_⟩
    · rw [this.2.2.2.2.2.2.1]; split <;> simp <;> omega
    · rw [this.2.2.2.2.2.2.2]; split <;> simp <;> omega

theorem packStates_eq (sts : List Nat) : packStates sts = pkList SB id sts 0 := by
  induction sts with
  | nil => rfl
  | cons st sts ih =>
    rw [pkList_cons_zero, ← ih]
    show st + packStates sts * SB = st + SB * packStates sts
    rw [Nat.mul_comm]

theorem stateAt_packStates (sts : List Nat) (hlt : ∀ st ∈ sts, st < SB) (s : Nat) (hs : s < sts.length) :
    stateAt (packStates sts) s = sts[s] := by
  rw [stateAt, packStates_eq]
  exact pkList_digit SB (by decide) id sts s hs hlt

/-! ### Regrouping a row sum by column, and the digit bound -/

def sumRange (m : Nat) (g : Nat → Nat) : Nat := sumNat ((List.range m).map g)

theorem sumNat_map_add (g h : Nat → Nat) : ∀ l : List Nat,
    sumNat (l.map fun t => g t + h t) = sumNat (l.map g) + sumNat (l.map h) := by
  intro l; induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map, sumNat, ih]; omega

theorem sumNat_map_zero (l : List Nat) (g : Nat → Nat) (h : ∀ x ∈ l, g x = 0) : sumNat (l.map g) = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map, sumNat, h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- a single hit in a range sum -/
theorem sumRange_single (m t v : Nat) (ht : t < m) :
    sumRange m (fun t' => if t' = t then v else 0) = v := by
  unfold sumRange
  induction m with
  | zero => exact absurd ht (Nat.not_lt_zero _)
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    have hsum : ∀ (l1 l2 : List Nat), sumNat (l1 ++ l2) = sumNat l1 + sumNat l2 := by
      intro l1 l2; induction l1 with
      | nil => simp only [List.nil_append, sumNat, Nat.zero_add]
      | cons x l1 ih1 => simp only [List.cons_append, sumNat, ih1]; omega
    rw [hsum]
    by_cases hm : t = m
    · subst hm
      rw [sumNat_map_zero _ _ (fun x hx => by rw [List.mem_range] at hx; rw [if_neg]; omega)]
      simp [sumNat]
    · rw [ih (by omega)]
      simp [sumNat, Ne.symm hm]

theorem sumRange_zero_of (m : Nat) (g : Nat → Nat) (h : ∀ t < m, g t = 0) : sumRange m g = 0 :=
  sumNat_map_zero _ _ (fun t ht => h t (List.mem_range.mp ht))

/-- the row-`s` sum regrouped over the columns `t < m` -/
theorem rowSum_regroup (k1 k2 : EntR → Nat) (f : EntR → Nat) (s m : Nat) :
    ∀ es : List EntR, (∀ e ∈ es, k2 e < m) →
      sumRange m (fun t => sumR (fun e => if k1 e = s ∧ k2 e = t then f e else 0) es)
        = sumR (fun e => if k1 e = s then f e else 0) es := by
  intro es
  induction es with
  | nil => intro _; simp only [sumR]; exact sumRange_zero_of m _ (fun _ _ => rfl)
  | cons e es ih =>
    intro hb
    have hsplit : (fun t => sumR (fun e' => if k1 e' = s ∧ k2 e' = t then f e' else 0) (e :: es))
        = fun t => (if k1 e = s ∧ k2 e = t then f e else 0)
            + sumR (fun e' => if k1 e' = s ∧ k2 e' = t then f e' else 0) es := by
      funext t; rfl
    rw [hsplit]
    unfold sumRange
    rw [sumNat_map_add]
    have ih' := ih (fun e' he' => hb e' (List.mem_cons_of_mem e he'))
    unfold sumRange at ih'
    rw [ih']
    simp only [sumR]
    congr 1
    by_cases hs : k1 e = s
    · rw [if_pos hs]
      have hfun : (fun t => if k1 e = s ∧ k2 e = t then f e else 0)
          = fun t => if t = k2 e then f e else 0 := by
        funext t
        by_cases ht : t = k2 e
        · subst ht; simp [hs]
        · simp [ht, Ne.symm ht]
      rw [hfun]
      have := sumRange_single m (k2 e) (f e) (hb e (List.mem_cons_self ..))
      unfold sumRange at this
      exact this
    · rw [if_neg hs]
      exact sumNat_map_zero _ _ (fun t _ => by simp [hs])

theorem sumR_idx_zero_of_not_mem (i : Nat) (f : EntR → Nat) :
    ∀ es : List EntR, i ∉ es.map idxR → sumR (fun e => if idxR e = i then f e else 0) es = 0 := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    intro h
    have hne : idxR e ≠ i := fun heq => h (List.mem_map.mpr ⟨e, List.mem_cons_self .., heq⟩)
    simp only [sumR, if_neg hne, Nat.zero_add]
    exact ih (fun hm => h (List.mem_cons_of_mem _ hm))

/-- a cell sum along a chain with distinct indices is a single entry -/
theorem cell_lt_gen (f : EntR → Nat) (bound : Nat) : ∀ (es : List EntR) (i : Nat), (es.map idxR).Nodup →
    (∀ e ∈ es, f e < bound) → 0 < bound →
    sumR (fun e => if idxR e = i then f e else 0) es < bound := by
  intro es
  induction es with
  | nil => intro i _ _ hb; simp [sumR]; exact hb
  | cons e es ih =>
    intro i hnd hb hpos
    have hnd' := (List.nodup_cons.mp hnd).2
    have hnot := (List.nodup_cons.mp hnd).1
    simp only [sumR]
    by_cases hi : idxR e = i
    · rw [if_pos hi, sumR_idx_zero_of_not_mem i _ es (hi ▸ hnot), Nat.add_zero]
      exact hb e (List.mem_cons_self ..)
    · rw [if_neg hi, Nat.zero_add]
      exact ih i hnd' (fun x hx => hb x (List.mem_cons_of_mem e hx)) hpos

theorem cell_lt (bound : Nat) (es : List EntR) (i : Nat) (hnd : (es.map idxR).Nodup)
    (hb : ∀ e ∈ es, e.2.2.1 < bound) (hpos : 0 < bound) :
    sumR (fun e => if idxR e = i then e.2.2.1 else 0) es < bound :=
  cell_lt_gen (fun e => e.2.2.1) bound es i hnd hb hpos

/-! ### Remaining helpers -/

theorem sumR_congr (f g : EntR → Nat) : ∀ es : List EntR, (∀ e ∈ es, f e = g e) → sumR f es = sumR g es := by
  intro es; induction es with
  | nil => intro _; rfl
  | cons e es ih => intro h; simp only [sumR, h e (List.mem_cons_self ..)]; rw [ih (fun x hx => h x (List.mem_cons_of_mem e hx))]

theorem sumRange_le (m bound : Nat) (g : Nat → Nat) (h : ∀ t < m, g t < bound) : sumRange m g ≤ m * bound := by
  unfold sumRange
  induction m with
  | zero => simp [sumNat]
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    have hsum : ∀ (l1 l2 : List Nat), sumNat (l1 ++ l2) = sumNat l1 + sumNat l2 := by
      intro l1 l2; induction l1 with
      | nil => simp only [List.nil_append, sumNat, Nat.zero_add]
      | cons x l1 ih1 => simp only [List.cons_append, sumNat, ih1]; omega
    rw [hsum]
    have := ih (fun t ht => h t (by omega))
    have hm := h m (by omega)
    simp only [sumNat, Nat.succ_mul]
    omega

theorem entriesR_bounds (fr : Bool) : ∀ (n x : Nat), ∀ e ∈ entriesR fr n x,
    e.1 < 100 ∧ e.2.1 < 100 ∧ e.2.2.1 < 1000000 ∧ e.2.2.2 < 10000000 ∧ (fr = false → e.2.2.2 = 0) := by
  intro n
  induction n with
  | zero => intro x e he; exact absurd he List.not_mem_nil
  | succ n ih =>
    intro x e he
    cases fr with
    | false =>
      simp only [entriesR, Bool.false_eq_true, ↓reduceIte] at he
      rcases List.mem_cons.mp he with rfl | hmem
      · refine ⟨?_, Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), by simp, fun _ => rfl⟩
        have : x % 10000000000 < 10000000000 := Nat.mod_lt _ (by decide)
        omega
      · exact ih _ e hmem
    | true =>
      simp only [entriesR, ↓reduceIte] at he
      rcases List.mem_cons.mp he with rfl | hmem
      · refine ⟨?_, Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), fun h => absurd h (by decide)⟩
        have : x % 100000000000000000 < 100000000000000000 := Nat.mod_lt _ (by decide)
        omega
      · exact ih _ e hmem

theorem rowList_lt (pats : List Nat) (r : Nat) : ∀ c ∈ rowList pats r, c < pats.length := by
  intro c hc
  unfold rowList at hc
  have := List.mem_range.mp (List.mem_filter.mp hc).1
  exact this

theorem states_lt (L0 L1 L2 : List Nat) (h0 : ∀ c ∈ L0, c < 32) (h1 : ∀ c ∈ L1, c < 32) (h2 : ∀ c ∈ L2, c < 32) :
    ∀ st ∈ states L0 L1 L2, st < SB := by
  intro st hst
  unfold states at hst
  obtain ⟨c0, hc0, hst⟩ := List.mem_flatMap.mp hst
  obtain ⟨c1, hc1, hst⟩ := List.mem_flatMap.mp hst
  split at hst
  · exact absurd hst List.not_mem_nil
  · obtain ⟨c2, hc2, hst⟩ := List.mem_flatMap.mp hst
    split at hst
    · exact absurd hst List.not_mem_nil
    · rcases List.mem_singleton.mp hst with rfl
      have := h0 c0 hc0; have := h1 c1 hc1; have := h2 c2 hc2
      unfold SB; omega

theorem dvd_foldl_lcm (cnt : Nat → Nat) : ∀ (sts : List Nat) (init : Nat),
    init ∣ sts.foldl (fun l st => Nat.lcm l (cnt st)) init := by
  intro sts
  induction sts with
  | nil => intro init; exact Nat.dvd_refl _
  | cons st sts ih =>
    intro init
    simp only [List.foldl]
    exact Nat.dvd_trans (Nat.dvd_lcm_left init (cnt st)) (ih _)

theorem mem_dvd_foldl_lcm (cnt : Nat → Nat) : ∀ (sts : List Nat) (init : Nat), ∀ st ∈ sts,
    cnt st ∣ sts.foldl (fun l st => Nat.lcm l (cnt st)) init := by
  intro sts
  induction sts with
  | nil => intro init st hst; exact absurd hst List.not_mem_nil
  | cons st' sts ih =>
    intro init st hst
    simp only [List.foldl]
    rcases List.mem_cons.mp hst with rfl | hmem
    · exact Nat.dvd_trans (Nat.dvd_lcm_right init (cnt st)) (dvd_foldl_lcm cnt sts _)
    · exact ih _ st hmem

/-- the states of a column, from its patterns -/
def stsOf (pats : List Nat) : List Nat := states (rowList pats 0) (rowList pats 1) (rowList pats 2)
/-- the law counts of a non-uniform column of packed type `m` -/
def cntOf (m : Nat) (pats : List Nat) : Nat → Nat := countOf (subTable (typeIndex m)) pats

/-- `mkCol` on a non-uniform column -/
theorem mkCol_spec_nonU (m : Nat) (pats : List Nat) (hU : (m == UTYPE) = false) :
    (mkCol m pats).n = (stsOf pats).length ∧ (mkCol m pats).P = packStates (stsOf pats)
      ∧ (mkCol m pats).isU = false
      ∧ (mkCol m pats).CV = pkList 100 (cntOf m pats) (stsOf pats) 0
      ∧ (mkCol m pats).exp0 = pkList B (fun st => 1000 * cntOf m pats st) (stsOf pats) 0
      ∧ (mkCol m pats).lcm = (stsOf pats).foldl (fun l st => Nat.lcm l (cntOf m pats st)) 1
      ∧ (mkCol m pats).sumC = sumNat ((stsOf pats).map (cntOf m pats))
      ∧ (mkCol m pats).sumC2 = sumNat (((stsOf pats).map (cntOf m pats)).map fun k => k * k) := by
  have h := colFold_false_spec (subTable (typeIndex m)) pats (stsOf pats) 0 (packStates (stsOf pats)) 0 0 0 0 1 0 0 false
  simp only [Nat.zero_add, countsList] at h
  have hc : mkCol m pats = colFold false (subTable (typeIndex m)) pats (stsOf pats) 0
      ⟨0, packStates (stsOf pats), 0, false, 0, 0, 0, 1, 0, 0⟩ := by
    unfold mkCol
    simp only [hU, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hc]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

/-! ### The main integer-level theorem, rational collision format -/

/-! ### The main theorem for the rational collision format (`fmt = 0`) -/

/-- the `v0`-sum of the entries at packed index `i` -/
def cellSum (es : List EntR) (i : Nat) : Nat := sumR (fun e => if idxR e = i then e.2.2.1 else 0) es

theorem rowSumR_lt_B (es : List EntR) (m : Nat) (hm : m ≤ 27) (hnd : (es.map idxR).Nodup)
    (hb : ∀ e ∈ es, e.2.1 < m ∧ e.2.2.1 < 1000000) (s : Nat) : rowSumR es s < B := by
  have hre := rowSum_regroup (fun e => e.1) (fun e => e.2.1) (fun e => e.2.2.1) s m es (fun e he => (hb e he).1)
  unfold rowSumR
  rw [← hre]
  have hcell : ∀ t < m, sumR (fun e => if e.1 = s ∧ e.2.1 = t then e.2.2.1 else 0) es < 1000000 := by
    intro t ht
    have := cell_lt 1000000 es (s * 100 + t) hnd (fun e he => (hb e he).2) (by decide)
    rw [sumR_congr _ (fun e => if idxR e = s * 100 + t then e.2.2.1 else 0) es]
    · exact this
    · intro e he
      have h2 := (hb e he).1
      by_cases h1 : e.1 = s ∧ e.2.1 = t
      · rw [if_pos h1, if_pos]; unfold idxR; omega
      · rw [if_neg h1, if_neg]; unfold idxR; omega
  have := sumRange_le m 1000000 _ hcell
  unfold B; omega

/-- the column version: sums over `t` of a column are bounded the same way -/
theorem colSumR_lt_B (es : List EntR) (m : Nat) (hm : m ≤ 27) (hnd : (es.map idxR).Nodup)
    (hb : ∀ e ∈ es, e.1 < m ∧ e.2.1 < 100 ∧ e.2.2.1 < 1000000) (t : Nat) (ht : t < 100) :
    colSumR es t < B := by
  have hre := rowSum_regroup (fun e => e.2.1) (fun e => e.1) (fun e => e.2.2.1) t m es (fun e he => (hb e he).1)
  unfold colSumR
  rw [← hre]
  have hcell : ∀ s < m, sumR (fun e => if e.2.1 = t ∧ e.1 = s then e.2.2.1 else 0) es < 1000000 := by
    intro s hs
    have := cell_lt 1000000 es (s * 100 + t) hnd (fun e he => (hb e he).2.2) (by decide)
    rw [sumR_congr _ (fun e => if idxR e = s * 100 + t then e.2.2.1 else 0) es]
    · exact this
    · intro e he
      have h2 := (hb e he).2.1
      by_cases h1 : e.2.1 = t ∧ e.1 = s
      · rw [if_pos h1, if_pos]; unfold idxR; omega
      · rw [if_neg h1, if_neg]; unfold idxR; omega
  have := sumRange_le m 1000000 _ hcell
  unfold B; omega

/-! ### The main theorem for the rational collision format (`fmt = 0`) -/

theorem colFold_isU (u : Bool) (sub : Nat) (pats : List Nat) :
    ∀ (sts : List Nat) (i : Nat) (c : Col), (colFold u sub pats sts i c).isU = c.isU := by
  intro sts
  induction sts with
  | nil => intro i c; rfl
  | cons st sts ih => intro i c; cases u <;> simp only [colFold, Bool.false_eq_true, ↓reduceIte] <;> rw [ih]

theorem mkCol_isU (m : Nat) (pats : List Nat) : (mkCol m pats).isU = (m == UTYPE) := by
  unfold mkCol; rw [colFold_isU]

theorem getD_of_lt {l : List Nat} {i d : Nat} (hi : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

/-- `checkRecord` at format `0`, unfolded -/
theorem checkRecord_zero_eq (mL mR M ne blob : Nat) :
    checkRecord 0 mL mR M ne blob =
      (let cols := colours mL mR M
       let L := mkCol mL (cols.map Prod.fst)
       let R := mkCol mR (cols.map Prod.snd)
       let a := passR false L R ne blob ⟨0, 0, 0, 0, 0, true⟩
       (validType mL && validType mR && decide (cols.length ≤ 32) && decide (L.n ≤ 27) && decide (R.n ≤ 27)
         && colOK L && colOK R && (L.isU || decide (typeIndex mL ≥ 1)) && (R.isU || decide (typeIndex mR ≥ 1)))
         && !L.isU && !R.isU && a.ok && (a.r0 == L.exp0) && (a.c0 == R.exp0) && finalR false L a) := rfl

theorem states_lt_of_cols (pats : List Nat) (h32 : pats.length ≤ 32) : ∀ st ∈ stsOf pats, st < SB := by
  apply states_lt
  all_goals intro c hc; have := rowList_lt pats _ c hc; omega

/-- the `CV` digit of a state is its law count (clean context) -/
theorem cvDigit_eq (m : Nat) (pats : List Nat) (e1 : Nat) (h1 : e1 < (stsOf pats).length) :
    pkList 100 (cntOf m pats) (stsOf pats) 0 / 100 ^ e1 % 100 = cntOf m pats ((stsOf pats).getD e1 0) := by
  rw [pkList_digit 100 (by decide) (cntOf m pats) (stsOf pats) e1 h1
    (fun st _ => countOf_lt (subTable (typeIndex m)) pats st), getD_of_lt h1]

set_option maxHeartbeats 1000000 in
theorem checkRecord_zero_spec (mL mR M ne blob : Nat) (h : checkRecord 0 mL mR M ne blob = true) :
    let cols := colours mL mR M
    let pL := cols.map Prod.fst
    let pR := cols.map Prod.snd
    let es := entriesR false ne blob
    let lc := (stsOf pL).foldl (fun l st => Nat.lcm l (cntOf mL pL st)) 1
    validType mL = true ∧ validType mR = true ∧ cols.length ≤ 32
      ∧ (stsOf pL).length ≤ 27 ∧ (stsOf pR).length ≤ 27
      ∧ (mL == UTYPE) = false ∧ (mR == UTYPE) = false ∧ 1 ≤ typeIndex mL ∧ 1 ≤ typeIndex mR
      ∧ (es.map idxR).Nodup
      ∧ (∀ e ∈ es, e.1 < (stsOf pL).length ∧ e.2.1 < (stsOf pR).length ∧ e.2.2.1 < 1000000
          ∧ compat ((stsOf pL).getD e.1 0) ((stsOf pR).getD e.2.1 0) = true)
      ∧ (∀ s (hs : s < (stsOf pL).length), rowSumR es s = 1000 * cntOf mL pL (stsOf pL)[s])
      ∧ (∀ t (ht : t < (stsOf pR).length), colSumR es t = 1000 * cntOf mR pR (stsOf pR)[t])
      ∧ sumNat ((stsOf pL).map (cntOf mL pL)) = 108
      ∧ sumNat (((stsOf pL).map (cntOf mL pL)).map fun k => k * k) ≤ 972
      ∧ sumNat ((stsOf pR).map (cntOf mR pR)) = 108
      ∧ sumNat (((stsOf pR).map (cntOf mR pR)).map fun k => k * k) ≤ 972
      ∧ (∀ st ∈ stsOf pL, cntOf mL pL st ∣ lc) ∧ 0 < lc
      ∧ (let q := sumR (fun e => 108 * (lc / cntOf mL pL ((stsOf pL).getD e.1 0)) * (289 * e.2.2.1 * e.2.2.1)) es
         5 * q < 2 * (lc * XD * XD)
           ∧ 17 * q * q < (2 * (lc * XD * XD) - 5 * q) * (2 * (lc * XD * XD) - 5 * q)) := by
  intro cols pL pR es lc
  rw [checkRecord_zero_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hvL, hvR⟩, h32⟩, hLn⟩, hRn⟩, hcL⟩, hcR⟩, htL⟩, htR⟩, hLU⟩, hRU⟩, hok⟩, hr0⟩, hc0⟩, hfin⟩ := h
  -- the two columns
  have hLU' : (mL == UTYPE) = false := by rw [← mkCol_isU mL pL]; exact hLU
  have hRU' : (mR == UTYPE) = false := by rw [← mkCol_isU mR pR]; exact hRU
  have hL := mkCol_spec_nonU mL pL hLU'
  have hR := mkCol_spec_nonU mR pR hRU'
  obtain ⟨hLn', hLP, -, hLCV, hLexp, hLlcm, hLsc, hLsc2⟩ := hL
  obtain ⟨hRn', hRP, -, hRCV, hRexp, hRlcm, hRsc, hRsc2⟩ := hR
  have htL' : 1 ≤ typeIndex mL := by
    rcases htL with h | h
    · rw [hLU] at h; exact absurd h (by decide)
    · exact h
  have htR' : 1 ≤ typeIndex mR := by
    rcases htR with h | h
    · rw [hRU] at h; exact absurd h (by decide)
    · exact h
  have hLn27 : (stsOf pL).length ≤ 27 := by rw [← hLn']; exact hLn
  have hRn27 : (stsOf pR).length ≤ 27 := by rw [← hRn']; exact hRn
  have hcL' : (mkCol mL pL).sumC = 108 ∧ (mkCol mL pL).sumC2 ≤ 972 ∧ 0 < (mkCol mL pL).lcm := by
    unfold colOK at hcL; rw [hLU] at hcL
    simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcL
    exact ⟨hcL.1.1, hcL.1.2, hcL.2⟩
  have hcR' : (mkCol mR pR).sumC = 108 ∧ (mkCol mR pR).sumC2 ≤ 972 := by
    unfold colOK at hcR; rw [hRU] at hcR
    simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcR
    exact ⟨hcR.1.1, hcR.1.2⟩
  have hpL32 : pL.length ≤ 32 := by simpa [pL] using h32
  have hpR32 : pR.length ≤ 32 := by simpa [pR] using h32
  have hSBL := states_lt_of_cols pL hpL32
  have hSBR := states_lt_of_cols pR hpR32
  -- the pass as a fold
  rw [passR_eq_foldl] at hok hr0 hc0 hfin
  obtain ⟨-, hchain⟩ := foldl_stepR_ok false _ _ es _ hok
  have hnd := chainR_nodup_idx false _ _ es 0 hchain
  have hmem := chainR_mem false _ _ es 0 hchain
  have hbnd := entriesR_bounds false ne blob
  have hent : ∀ e ∈ es, e.1 < (stsOf pL).length ∧ e.2.1 < (stsOf pR).length ∧ e.2.2.1 < 1000000
      ∧ compat ((stsOf pL).getD e.1 0) ((stsOf pR).getD e.2.1 0) = true := by
    intro e he
    obtain ⟨-, h1, h2, h3, -⟩ := hmem e he
    rw [hLn'] at h1; rw [hRn'] at h2
    refine ⟨h1, h2, (hbnd e he).2.2.1, ?_⟩
    rw [hLP, hRP, stateAt_packStates _ hSBL _ h1, stateAt_packStates _ hSBR _ h2] at h3
    rw [getD_of_lt h1, getD_of_lt h2]; exact h3
  -- row sums
  have hrow : ∀ s (hs : s < (stsOf pL).length), rowSumR es s = 1000 * cntOf mL pL (stsOf pL)[s] := by
    rw [foldl_stepR_r0, hLexp] at hr0
    simp only [Nat.zero_add] at hr0
    have hsplit := pkList_range_sumR (fun e => e.1) (fun e => e.2.2.1) es (stsOf pL).length
    rw [sumR_congr _ (fun e => e.2.2.1 * B ^ e.1) es (fun e he => by rw [if_pos (hent e he).1])] at hsplit
    rw [← hsplit] at hr0
    intro s hs
    have := pkList_inj B (by decide) (fun s => sumR (fun e => if e.1 = s then e.2.2.1 else 0) es)
      (fun st => 1000 * cntOf mL pL st) (List.range (stsOf pL).length) (stsOf pL) (by simp)
      (fun s _ => rowSumR_lt_B es (stsOf pR).length hRn27 hnd (fun e he => ⟨(hent e he).2.1, (hent e he).2.2.1⟩) s)
      (fun st _ => by
        have := countOf_lt (subTable (typeIndex mL)) pL st
        show 1000 * countOf (subTable (typeIndex mL)) pL st < 100000000
        omega)
      hr0 s (by simpa using hs) hs
    unfold rowSumR; simpa using this
  have hcol : ∀ t (ht : t < (stsOf pR).length), colSumR es t = 1000 * cntOf mR pR (stsOf pR)[t] := by
    rw [foldl_stepR_c0, hRexp] at hc0
    simp only [Nat.zero_add] at hc0
    have hsplit := pkList_range_sumR (fun e => e.2.1) (fun e => e.2.2.1) es (stsOf pR).length
    rw [sumR_congr _ (fun e => e.2.2.1 * B ^ e.2.1) es (fun e he => by rw [if_pos (hent e he).2.1])] at hsplit
    rw [← hsplit] at hc0
    intro t ht
    have := pkList_inj B (by decide) (fun t => sumR (fun e => if e.2.1 = t then e.2.2.1 else 0) es)
      (fun st => 1000 * cntOf mR pR st) (List.range (stsOf pR).length) (stsOf pR) (by simp)
      (fun t ht' => colSumR_lt_B es (stsOf pL).length hLn27 hnd
        (fun e he => ⟨(hent e he).1, (hbnd e he).2.1, (hent e he).2.2.1⟩) t
        (by have := List.mem_range.mp ht'; omega))
      (fun st _ => by
        have := countOf_lt (subTable (typeIndex mR)) pR st
        show 1000 * countOf (subTable (typeIndex mR)) pR st < 100000000
        omega)
      hc0 t (by simpa using ht) ht
    unfold colSumR; simpa using this
  -- the collision inequality
  have hq : (5 * ((es.foldl (stepR' false (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, true⟩).q)
      < 2 * ((mkCol mL pL).lcm * XD * XD))
      ∧ 17 * ((es.foldl (stepR' false (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, true⟩).q)
        * ((es.foldl (stepR' false (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, true⟩).q)
      < (2 * ((mkCol mL pL).lcm * XD * XD) - 5 * ((es.foldl (stepR' false (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, true⟩).q))
        * (2 * ((mkCol mL pL).lcm * XD * XD) - 5 * ((es.foldl (stepR' false (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, true⟩).q)) := by
    unfold finalR at hfin
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hfin
    exact hfin
  rw [foldl_stepR_q, Nat.zero_add, hLlcm] at hq
  have hqeq : sumR (fun e => 108 * ((stsOf pL).foldl (fun l st => Nat.lcm l (cntOf mL pL st)) 1
        / ((mkCol mL pL).CV / 100 ^ e.1 % 100)) * (289 * e.2.2.1 * e.2.2.1)) es
      = sumR (fun e => 108 * (lc / cntOf mL pL ((stsOf pL).getD e.1 0)) * (289 * e.2.2.1 * e.2.2.1)) es := by
    apply sumR_congr
    intro e he
    have h1 := (hent e he).1
    rw [hLCV]
    exact congrArg (fun x => 108 * (lc / x) * (289 * e.2.2.1 * e.2.2.1)) (cvDigit_eq mL pL e.1 h1)
  rw [hqeq] at hq
  refine ⟨hvL, hvR, h32, hLn27, hRn27, hLU', hRU', htL', htR', hnd, hent, hrow, hcol,
    by rw [← hLsc]; exact hcL'.1, by rw [← hLsc2]; exact hcL'.2.1, by rw [← hRsc]; exact hcR'.1, by rw [← hRsc2]; exact hcR'.2,
    fun st hst => mem_dvd_foldl_lcm _ _ _ st hst,
    (by show 0 < (stsOf pL).foldl (fun l st => Nat.lcm l (cntOf mL pL st)) 1; rw [← hLlcm]; exact hcL'.2.2), hq⟩

/-! ### The `ℚ(√17)` formats: projections to rational entry lists -/

/-- the `v0` projection of a `ℚ(√17)` entry -/
def toR (e : EntQ) : EntR := (e.1, e.2.1, e.2.2.1, e.2.2.2.2)
/-- the `v1 + OFF` projection (a natural number by the decoding bounds) -/
def toR1 (e : EntQ) : EntR := (e.1, e.2.1, Int.toNat (e.2.2.2.1 + OFF), e.2.2.2.2)

def idxQ (e : EntQ) : Nat := e.1 * 100 + e.2.1
theorem idxR_toR (e : EntQ) : idxR (toR e) = idxQ e := rfl
theorem idxR_toR1 (e : EntQ) : idxR (toR1 e) = idxQ e := rfl

theorem entriesQ_bounds (fr : Bool) : ∀ (n x : Nat), ∀ e ∈ entriesQ fr n x,
    e.1 < 100 ∧ e.2.1 < 100 ∧ e.2.2.1 < 1000000 ∧ (-(OFF : Int) ≤ e.2.2.2.1 ∧ e.2.2.2.1 + OFF < 1000000)
      ∧ e.2.2.2.2 < 10000000 ∧ (fr = false → e.2.2.2.2 = 0) := by
  intro n
  induction n with
  | zero => intro x e he; exact absurd he List.not_mem_nil
  | succ n ih =>
    intro x e he
    cases fr with
    | false =>
      simp only [entriesQ, Bool.false_eq_true, ↓reduceIte] at he
      rcases List.mem_cons.mp he with rfl | hmem
      · refine ⟨?_, Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), ⟨by dsimp only; omega, ?_⟩, by simp, fun _ => rfl⟩
        · have : x % 10000000000000000 < 10000000000000000 := Nat.mod_lt _ (by decide)
          omega
        · have : x % 10000000000000000 / 1000000 % 1000000 < 1000000 := Nat.mod_lt _ (by decide)
          simp only [OFF]; omega
      · exact ih _ e hmem
    | true =>
      simp only [entriesQ, ↓reduceIte] at he
      rcases List.mem_cons.mp he with rfl | hmem
      · refine ⟨?_, Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), ⟨by dsimp only; omega, ?_⟩,
          Nat.mod_lt _ (by decide), fun h => absurd h (by decide)⟩
        · have : x % 100000000000000000000000 < 100000000000000000000000 := Nat.mod_lt _ (by decide)
          omega
        · have : x % 100000000000000000000000 / 1000000 % 1000000 < 1000000 := Nat.mod_lt _ (by decide)
          simp only [OFF]; omega
      · exact ih _ e hmem

/-- the per-entry condition recorded in `ok` for the `ℚ(√17)` formats -/
def entOKQ (fr : Bool) (L R : Col) (prev : Nat) (e : EntQ) : Bool :=
  prev < e.1 * 100 + e.2.1 + 1 && e.1 < L.n && e.2.1 < R.n
    && compat (stateAt L.P e.1) (stateAt R.P e.2.1)
    && nonnegQ17 (17 * e.2.2.1) (9 * e.2.2.2.1)
    && (!fr || nonnegQ17 ((e.2.2.2.2 ^ 4 * (if L.isU then 12 else (L.CV / 100 ^ e.1) % 100) * XD : Nat)
          - (LD * E ^ 4 * e.2.2.1 : Nat) : Int) (-(972 * E ^ 4 : Nat) * e.2.2.2.1))

def chainQ (fr : Bool) (L R : Col) : Nat → List EntQ → Prop
  | _, [] => True
  | prev, e :: es => entOKQ fr L R prev e = true ∧ chainQ fr L R (idxQ e + 1) es

/-- the `q0`/`q1` increments of an entry (collision formats only) -/
def dq (L : Col) (e : EntQ) : Int × Int :=
  let stL := stateAt L.P e.1
  let cnt := if L.isU then 12 else (L.CV / 100 ^ e.1) % 100
  let a17 : Int := 17 * e.2.2.1
  let b9 : Int := 9 * e.2.2.2.1
  let A := a17 * a17 + 17 * b9 * b9
  let Bq := 2 * a17 * b9
  if L.isU then
    if isABA stL then (153 * A - 153 * Bq, 153 * Bq - 9 * A) else (153 * A + 153 * Bq, 153 * Bq + 9 * A)
  else
    let f : Int := 108 * (L.lcm / cnt)
    (f * A, f * Bq)

def sumInt (f : EntQ → Int) : List EntQ → Int
  | [] => 0
  | e :: es => f e + sumInt f es

theorem foldl_stepQ_fields (fr : Bool) (L R : Col) :
    ∀ (es : List EntQ) (a : AccQ),
      let a' := es.foldl (stepQ' fr L R) a
      a'.r0 = a.r0 + sumR (fun e => e.2.2.1 * B ^ e.1) (es.map toR)
      ∧ a'.r1 = a.r1 + sumR (fun e => e.2.2.1 * B ^ e.1) (es.map toR1)
      ∧ a'.c0 = a.c0 + sumR (fun e => e.2.2.1 * B ^ e.2.1) (es.map toR)
      ∧ a'.c1 = a.c1 + sumR (fun e => e.2.2.1 * B ^ e.2.1) (es.map toR1)
      ∧ a'.rc = a.rc + sumR (fun e => B ^ e.1) (es.map toR)
      ∧ a'.cc = a.cc + sumR (fun e => B ^ e.2.1) (es.map toR)
      ∧ a'.q0 = a.q0 + (if fr then 0 else sumInt (fun e => (dq L e).1) es)
      ∧ a'.q1 = a.q1 + (if fr then 0 else sumInt (fun e => (dq L e).2) es)
      ∧ a'.nr = a.nr + sumR (fun e => e.2.2.1 * e.2.2.2) (es.map toR)
      ∧ a'.nr1 = a.nr1 + sumInt (fun e => e.2.2.2.1 * e.2.2.2.2) es := by
  intro es
  induction es with
  | nil => intro a; simp [sumR, sumInt]
  | cons e es ih =>
    intro a
    have h := ih (stepQ' fr L R a e)
    simp only [List.foldl, List.map, sumR, sumInt] at h ⊢
    simp only [stepQ', stepQ, dq, toR, toR1] at h ⊢
    refine ⟨by rw [h.1]; omega, by rw [h.2.1]; omega, by rw [h.2.2.1]; omega, by rw [h.2.2.2.1]; omega,
      by rw [h.2.2.2.2.1]; omega, by rw [h.2.2.2.2.2.1]; omega, ?_, ?_, by rw [h.2.2.2.2.2.2.2.2.1]; omega,
      by rw [h.2.2.2.2.2.2.2.2.2]; omega⟩
    · rw [h.2.2.2.2.2.2.1]; cases fr <;> simp <;> omega
    · rw [h.2.2.2.2.2.2.2.1]; cases fr <;> simp <;> omega

theorem foldl_stepQ_ok (fr : Bool) (L R : Col) :
    ∀ (es : List EntQ) (a : AccQ), (es.foldl (stepQ' fr L R) a).ok = true →
      a.ok = true ∧ chainQ fr L R a.prev es := by
  intro es
  induction es with
  | nil => intro a h; exact ⟨h, trivial⟩
  | cons e es ih =>
    intro a h
    simp only [List.foldl] at h
    obtain ⟨hok, hrest⟩ := ih _ h
    have hprev : (stepQ' fr L R a e).prev = idxQ e + 1 := rfl
    rw [hprev] at hrest
    simp only [stepQ', stepQ] at hok
    refine ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).1, ?_, hrest⟩
    simp only [entOKQ, Bool.and_eq_true_iff]
    have h1 := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).2
    have h2 := (Bool.and_eq_true_iff.mp hok).2
    simp only [Bool.and_eq_true_iff] at h1
    exact ⟨h1, h2⟩

theorem chainQ_mem (fr : Bool) (L R : Col) :
    ∀ (es : List EntQ) (prev : Nat), chainQ fr L R prev es →
      ∀ e ∈ es, prev < idxQ e + 1 ∧ e.1 < L.n ∧ e.2.1 < R.n
        ∧ compat (stateAt L.P e.1) (stateAt R.P e.2.1) = true
        ∧ nonnegQ17 (17 * e.2.2.1) (9 * e.2.2.2.1) = true
        ∧ (fr = true → nonnegQ17 ((e.2.2.2.2 ^ 4 * (if L.isU then 12 else (L.CV / 100 ^ e.1) % 100) * XD : Nat)
              - (LD * E ^ 4 * e.2.2.1 : Nat) : Int) (-(972 * E ^ 4 : Nat) * e.2.2.2.1) = true) := by
  intro es
  induction es with
  | nil => intro prev _ e he; exact absurd he List.not_mem_nil
  | cons e es ih =>
    intro prev hc e' he'
    obtain ⟨hok, hrest⟩ := hc
    rcases List.mem_cons.mp he' with rfl | hmem
    · simp only [entOKQ, Bool.and_eq_true_iff, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok
      refine ⟨h1, h2, h3, h4, h5, fun hfr => ?_⟩
      rcases h6 with h6 | h6
      · rw [hfr] at h6; exact absurd h6 (by decide)
      · exact h6
    · have := ih _ hrest e' hmem
      refine ⟨?_, this.2⟩
      have hlt : prev < idxQ e + 1 := by
        simp only [entOKQ, Bool.and_eq_true_iff, decide_eq_true_eq] at hok
        exact hok.1.1.1.1.1
      omega

theorem chainQ_nodup_idx (fr : Bool) (L R : Col) :
    ∀ (es : List EntQ) (prev : Nat), chainQ fr L R prev es → (es.map idxQ).Nodup := by
  intro es
  induction es with
  | nil => intro _ _; exact List.nodup_nil
  | cons e es ih =>
    intro prev hc
    obtain ⟨_, hrest⟩ := hc
    refine List.nodup_cons.mpr ⟨?_, ih _ hrest⟩
    intro hmem
    obtain ⟨e', he', heq⟩ := List.mem_map.mp hmem
    have := (chainQ_mem fr L R es _ hrest e' he').1
    omega

theorem map_idxR_toR (es : List EntQ) : (es.map toR).map idxR = es.map idxQ := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map, ih]; rfl
theorem map_idxR_toR1 (es : List EntQ) : (es.map toR1).map idxR = es.map idxQ := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map, ih]; rfl

/-- `mkCol` on the uniform column -/
theorem mkCol_spec_U (m : Nat) (pats : List Nat) (hU : (m == UTYPE) = true) :
    (mkCol m pats).n = (stsOf pats).length ∧ (mkCol m pats).P = packStates (stsOf pats)
      ∧ (mkCol m pats).isU = true ∧ (mkCol m pats).CV = 0 ∧ (mkCol m pats).lcm = 1
      ∧ (mkCol m pats).exp0 = pkList B (fun _ => 9000) (stsOf pats) 0
      ∧ (mkCol m pats).abaMask = pkList B (fun st => if isABA st then 1 else 0) (stsOf pats) 0
      ∧ (mkCol m pats).abcMask = pkList B (fun st => if isABA st then 0 else 1) (stsOf pats) 0 := by
  have h := colFold_true_spec 0 pats (stsOf pats) 0 (packStates (stsOf pats)) 0 0 0 0 1 0 0 true
  simp only [Nat.zero_add] at h
  have hc : mkCol m pats = colFold true 0 pats (stsOf pats) 0
      ⟨0, packStates (stsOf pats), 0, true, 0, 0, 0, 1, 0, 0⟩ := by
    unfold mkCol
    simp only [hU, ↓reduceIte]
    rfl
  rw [hc]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-! ### `exp1Of` as a packed vector -/

theorem pkList_append {α : Type} (b : Nat) (g : α → Nat) :
    ∀ (l1 l2 : List α) (i : Nat), pkList b g (l1 ++ l2) i = pkList b g l1 i + pkList b g l2 (i + l1.length) := by
  intro l1
  induction l1 with
  | nil => intro l2 i; simp [pkList]
  | cons x l1 ih =>
    intro l2 i
    simp only [List.cons_append, pkList, ih, List.length_cons]
    rw [show i + (l1.length + 1) = i + 1 + l1.length from by omega]
    omega

theorem foldl_range_pkList (g : Nat → Nat) :
    ∀ (n a : Nat), (List.range n).foldl (fun acc s => acc + g s * B ^ s) a = a + pkList B g (List.range n) 0 := by
  intro n
  induction n with
  | zero => intro a; simp [pkList]
  | succ n ih =>
    intro a
    rw [List.range_succ, List.foldl_append, ih, pkList_append]
    simp only [List.foldl, pkList, List.length_range, Nat.zero_add, Nat.add_zero]
    omega

theorem pkList_mul {α : Type} (b c : Nat) (g : α → Nat) :
    ∀ (l : List α) (i : Nat), c * pkList b g l i = pkList b (fun x => c * g x) l i := by
  intro l
  induction l with
  | nil => intro i; simp [pkList]
  | cons x l ih => intro i; simp only [pkList, Nat.mul_add, ← ih, Nat.mul_assoc]

theorem exp1Of_nonU (c : Col) (hU : c.isU = false) (cnt : Nat) : exp1Of c cnt = OFF * cnt := by
  unfold exp1Of; rw [hU]; rfl

theorem exp1Of_U (c : Col) (hU : c.isU = true) (cnt : Nat) :
    exp1Of c cnt = pkList B (fun s => if (c.abaMask / B ^ s) % B == 1 then (cnt / B ^ s) % B * OFF + 1000
      else (cnt / B ^ s) % B * OFF - 1000) (List.range c.n) 0 := by
  unfold exp1Of; rw [hU]
  simp only [↓reduceIte]
  rw [foldl_range_pkList]
  simp

/-! ### Entry counts and the `v1` marginals -/

/-- number of entries with key value `s` -/
def keyCnt (key : EntR → Nat) (es : List EntR) (s : Nat) : Nat := sumR (fun e => if key e = s then 1 else 0) es

theorem sumR_zero_fn : ∀ l : List EntR, sumR (fun _ => 0) l = 0 := by
  intro l; induction l with
  | nil => rfl
  | cons _ _ ih => simp [sumR, ih]

/-- entry counts per key value are at most `2·m ≤ 54` (rows: `swap = false`; columns: `swap = true`) -/
theorem keyCnt_le (key key' : EntR → Nat) (swap : Bool) (es : List EntR) (m : Nat) (hm : m ≤ 27)
    (hnd : (es.map idxR).Nodup)
    (hkey : ∀ e, idxR e = if swap then key' e * 100 + key e else key e * 100 + key' e)
    (hb : ∀ e ∈ es, key' e < m) (hb' : ∀ e ∈ es, key' e < 100) (hb'' : ∀ e ∈ es, key e < 100)
    (s : Nat) : keyCnt key es s ≤ 54 := by
  by_cases hs : s < 100
  · have hre := rowSum_regroup key key' (fun _ => 1) s m es hb
    unfold keyCnt
    rw [← hre]
    have hcell : ∀ t < m, sumR (fun e => if key e = s ∧ key' e = t then 1 else 0) es < 2 := by
      intro t ht
      have := cell_lt_gen (fun _ => 1) 2 es (if swap then t * 100 + s else s * 100 + t) hnd
        (fun _ _ => by decide) (by decide)
      rw [sumR_congr _ (fun e => if idxR e = (if swap then t * 100 + s else s * 100 + t) then 1 else 0) es]
      · exact this
      · intro e he
        have h2 := hb' e he
        have h3 := hb'' e he
        have hk := hkey e
        cases swap <;> simp only [Bool.false_eq_true, ↓reduceIte] at hk ⊢ <;>
        · by_cases h1 : key e = s ∧ key' e = t
          · rw [if_pos h1, if_pos]; omega
          · rw [if_neg h1, if_neg]; omega
    have := sumRange_le m 2 _ hcell
    omega
  · unfold keyCnt
    rw [sumR_congr _ (fun _ => 0) es (fun e he => by rw [if_neg]; have := hb'' e he; omega), sumR_zero_fn]
    decide

theorem keySum_pow (key : EntR → Nat) (es : List EntR) (n : Nat) (hb : ∀ e ∈ es, key e < n) :
    sumR (fun e => B ^ key e) es = pkList B (keyCnt key es) (List.range n) 0 := by
  unfold keyCnt
  rw [pkList_range_sumR key (fun _ => 1) es n]
  apply sumR_congr
  intro e he
  rw [if_pos (hb e he), Nat.one_mul]

/-- `sumInt` of the `v1` field over a key class, in terms of the `toR1` projection -/
theorem v1_key_sum (keyQ : EntQ → Nat) (key : EntR → Nat) (hk1 : ∀ e, key (toR1 e) = keyQ e)
    (hk0 : ∀ e, key (toR e) = keyQ e) :
    ∀ (es : List EntQ) (s : Nat), (∀ e ∈ es, -(OFF : Int) ≤ e.2.2.2.1) →
      sumInt (fun e => if keyQ e = s then e.2.2.2.1 else 0) es + OFF * keyCnt key (es.map toR) s
        = (sumR (fun e => if key e = s then e.2.2.1 else 0) (es.map toR1) : Int) := by
  intro es
  induction es with
  | nil => intro s _; simp [sumInt, keyCnt, sumR]
  | cons e es ih =>
    intro s hb
    have ih' := ih s (fun x hx => hb x (List.mem_cons_of_mem e hx))
    simp only [sumInt, List.map, keyCnt, sumR, hk0, hk1] at ih' ⊢
    have hnn := hb e (List.mem_cons_self ..)
    have htn : ((Int.toNat (e.2.2.2.1 + OFF) : Nat) : Int) = e.2.2.2.1 + OFF := by
      rw [Int.toNat_of_nonneg (by omega)]
    by_cases hs : keyQ e = s
    · simp only [hs, if_true, toR1]
      push_cast
      rw [htn]
      unfold OFF at ih' ⊢
      omega
    · simp only [hs, if_false, toR1]
      push_cast
      unfold OFF at ih' ⊢
      omega

/-- the semantic law digits -/
def lawE0 (m : Nat) (pats : List Nat) (st : Nat) : Nat := if m == UTYPE then 9000 else 1000 * cntOf m pats st
def lawE1 (m : Nat) (st : Nat) : Int := if m == UTYPE then (if isABA st then 1000 else -1000) else 0

theorem keyCnt_pos (key : EntR → Nat) (f : EntR → Nat) :
    ∀ (es : List EntR) (s : Nat), 0 < sumR (fun e => if key e = s then f e else 0) es → 1 ≤ keyCnt key es s := by
  intro es
  induction es with
  | nil => intro s h; simp [sumR] at h
  | cons e es ih =>
    intro s h
    unfold keyCnt; simp only [sumR] at h ⊢
    by_cases hs : key e = s
    · rw [if_pos hs]; omega
    · rw [if_neg hs] at h ⊢; rw [Nat.zero_add] at h ⊢; exact ih s h

/-- the semantic collision increments of an entry -/
def dqSem (m : Nat) (pats : List Nat) (lc : Nat) (e : EntQ) : Int × Int :=
  let st := (stsOf pats).getD e.1 0
  let a17 : Int := 17 * e.2.2.1
  let b9 : Int := 9 * e.2.2.2.1
  let A := a17 * a17 + 17 * b9 * b9
  let Bq := 2 * a17 * b9
  if m == UTYPE then
    if isABA st then (153 * A - 153 * Bq, 153 * Bq - 9 * A) else (153 * A + 153 * Bq, 153 * Bq + 9 * A)
  else
    let f : Int := 108 * (lc / cntOf m pats st)
    (f * A, f * Bq)

/-- `checkRecord` at format `1`, unfolded -/
theorem checkRecord_one_eq (mL mR M ne blob : Nat) :
    checkRecord 1 mL mR M ne blob =
      (let cols := colours mL mR M
       let L := mkCol mL (cols.map Prod.fst)
       let R := mkCol mR (cols.map Prod.snd)
       let a := passQ false L R ne blob ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, true⟩
       (validType mL && validType mR && decide (cols.length ≤ 32) && decide (L.n ≤ 27) && decide (R.n ≤ 27)
         && colOK L && colOK R && (L.isU || decide (typeIndex mL ≥ 1)) && (R.isU || decide (typeIndex mR ≥ 1)))
         && (!false || !L.isU) && a.ok && (a.r0 == L.exp0) && (a.c0 == R.exp0)
         && (a.r1 == exp1Of L a.rc) && (a.c1 == exp1Of R a.cc) && finalQ false L a) := rfl

/-- unified column facts -/
theorem mkCol_facts (m : Nat) (pats : List Nat) :
    (mkCol m pats).n = (stsOf pats).length ∧ (mkCol m pats).P = packStates (stsOf pats)
      ∧ (mkCol m pats).isU = (m == UTYPE)
      ∧ (mkCol m pats).exp0 = pkList B (lawE0 m pats) (stsOf pats) 0
      ∧ ((m == UTYPE) = true → (mkCol m pats).CV = 0 ∧ (mkCol m pats).lcm = 1
          ∧ (mkCol m pats).abaMask = pkList B (fun st => if isABA st then 1 else 0) (stsOf pats) 0)
      ∧ ((m == UTYPE) = false → (mkCol m pats).CV = pkList 100 (cntOf m pats) (stsOf pats) 0
          ∧ (mkCol m pats).lcm = (stsOf pats).foldl (fun l st => Nat.lcm l (cntOf m pats st)) 1
          ∧ (mkCol m pats).sumC = sumNat ((stsOf pats).map (cntOf m pats))
          ∧ (mkCol m pats).sumC2 = sumNat (((stsOf pats).map (cntOf m pats)).map fun k => k * k)) := by
  by_cases hU : (m == UTYPE) = true
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := mkCol_spec_U m pats hU
    refine ⟨h1, h2, by rw [h3, hU], ?_, fun _ => ⟨h4, h5, h7⟩, fun h => absurd hU (by rw [h]; decide)⟩
    rw [h6]; unfold lawE0; rw [hU]; rfl
  · have hU' : (m == UTYPE) = false := by simpa using hU
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := mkCol_spec_nonU m pats hU'
    refine ⟨h1, h2, by rw [h3, hU'], ?_, fun h => absurd h hU, fun _ => ⟨h4, h6, h7, h8⟩⟩
    rw [h5]; unfold lawE0; rw [hU']; rfl

/-- digit `s` of the packed `abaMask` -/
theorem abaMask_digit (sts : List Nat) (s : Nat) (hs : s < sts.length) :
    pkList B (fun st => if isABA st then 1 else 0) sts 0 / B ^ s % B = if isABA sts[s] then 1 else 0 :=
  pkList_digit B (by decide) _ sts s hs (fun st _ => by split <;> decide)

/-- the expected `v1 + OFF` digit vector -/
def exp1Digit (m : Nat) (sts : List Nat) (cnt : Nat → Nat) (s : Nat) : Nat :=
  if m == UTYPE then (if isABA (sts.getD s 0) then cnt s * OFF + 1000 else cnt s * OFF - 1000) else OFF * cnt s

theorem pkList_congr {α : Type} (b : Nat) (f g : α → Nat) :
    ∀ (l : List α) (i : Nat), (∀ x ∈ l, f x = g x) → pkList b f l i = pkList b g l i := by
  intro l
  induction l with
  | nil => intro i _; rfl
  | cons x l ih => intro i h; simp only [pkList, h x (List.mem_cons_self ..)]; rw [ih (i + 1) (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- `exp1Of` of a column against the packed entry counts is the packed expected digit vector -/
theorem exp1Of_eq (m : Nat) (pats : List Nat) (cnt : Nat → Nat) (hc : ∀ s, cnt s ≤ 54) :
    exp1Of (mkCol m pats) (pkList B cnt (List.range (stsOf pats).length) 0)
      = pkList B (exp1Digit m (stsOf pats) cnt) (List.range (stsOf pats).length) 0 := by
  obtain ⟨hn, -, hU, -, hUf, -⟩ := mkCol_facts m pats
  by_cases hu : (m == UTYPE) = true
  · obtain ⟨-, -, haba⟩ := hUf hu
    rw [exp1Of_U _ (by rw [hU, hu]), hn]
    apply pkList_congr
    intro s hs
    have hs' : s < (stsOf pats).length := List.mem_range.mp hs
    unfold exp1Digit; rw [hu]; simp only [↓reduceIte]
    have hd := pkList_digit B (by decide) cnt (List.range (stsOf pats).length) s (by simpa using hs')
      (fun t _ => by have := hc t; unfold B; omega)
    simp only [List.getElem_range] at hd
    rw [hd, haba, abaMask_digit _ s hs', getD_of_lt hs']
    split <;> simp
  · have hu' : (m == UTYPE) = false := by simpa using hu
    rw [exp1Of_nonU _ (by rw [hU, hu']), pkList_mul]
    apply pkList_congr
    intro s _; unfold exp1Digit; rw [hu']; rfl

theorem sumInt_congr (f g : EntQ → Int) : ∀ es : List EntQ, (∀ e ∈ es, f e = g e) → sumInt f es = sumInt g es := by
  intro es; induction es with
  | nil => intro _; rfl
  | cons e es ih => intro h; simp only [sumInt, h e (List.mem_cons_self ..)]; rw [ih (fun x hx => h x (List.mem_cons_of_mem e hx))]

set_option maxHeartbeats 2000000 in
theorem checkRecord_one_spec (mL mR M ne blob : Nat) (h : checkRecord 1 mL mR M ne blob = true) :
    let cols := colours mL mR M
    let pL := cols.map Prod.fst
    let pR := cols.map Prod.snd
    let es := entriesQ false ne blob
    let lc := (stsOf pL).foldl (fun l st => Nat.lcm l (cntOf mL pL st)) 1
    validType mL = true ∧ validType mR = true ∧ cols.length ≤ 32
      ∧ (stsOf pL).length ≤ 27 ∧ (stsOf pR).length ≤ 27
      ∧ ((mL == UTYPE) = false → 1 ≤ typeIndex mL) ∧ ((mR == UTYPE) = false → 1 ≤ typeIndex mR)
      ∧ (es.map idxQ).Nodup
      ∧ (∀ e ∈ es, e.1 < (stsOf pL).length ∧ e.2.1 < (stsOf pR).length ∧ e.2.2.1 < 1000000
          ∧ (-(OFF : Int) ≤ e.2.2.2.1 ∧ e.2.2.2.1 + OFF < 1000000)
          ∧ compat ((stsOf pL).getD e.1 0) ((stsOf pR).getD e.2.1 0) = true
          ∧ nonnegQ17 (17 * e.2.2.1) (9 * e.2.2.2.1) = true)
      ∧ (∀ s (hs : s < (stsOf pL).length), rowSumR (es.map toR) s = lawE0 mL pL (stsOf pL)[s])
      ∧ (∀ s (hs : s < (stsOf pL).length),
          sumInt (fun e => if e.1 = s then e.2.2.2.1 else 0) es = lawE1 mL (stsOf pL)[s])
      ∧ (∀ t (ht : t < (stsOf pR).length), colSumR (es.map toR) t = lawE0 mR pR (stsOf pR)[t])
      ∧ (∀ t (ht : t < (stsOf pR).length),
          sumInt (fun e => if e.2.1 = t then e.2.2.2.1 else 0) es = lawE1 mR (stsOf pR)[t])
      ∧ ((mL == UTYPE) = false → sumNat ((stsOf pL).map (cntOf mL pL)) = 108
          ∧ sumNat (((stsOf pL).map (cntOf mL pL)).map fun k => k * k) ≤ 972
          ∧ (∀ st ∈ stsOf pL, cntOf mL pL st ∣ lc) ∧ 0 < lc)
      ∧ ((mR == UTYPE) = false → sumNat ((stsOf pR).map (cntOf mR pR)) = 108
          ∧ sumNat (((stsOf pR).map (cntOf mR pR)).map fun k => k * k) ≤ 972)
      ∧ (let den : Int := (if mL == UTYPE then 12 else lc) * XD * XD
         let q0 := sumInt (fun e => (dqSem mL pL lc e).1) es
         let q1 := sumInt (fun e => (dqSem mL pL lc e).2) es
         negQ17 (5 * q0 + 17 * q1 - 2 * den) (q0 + 5 * q1) = true
           ∧ ((mL == UTYPE) = true → negQ17 (18 * (5 * q0 + 17 * q1) - 34 * den) (18 * (q0 + 5 * q1)) = true)) := by
  intro cols pL pR es lc
  rw [checkRecord_one_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
    Bool.not_false, Bool.true_or, true_and, and_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hvL, hvR⟩, h32⟩, hLn⟩, hRn⟩, hcL⟩, hcR⟩, htL⟩, htR⟩, hok⟩, hr0⟩, hc0⟩, hr1⟩, hc1⟩, hfin⟩ := h
  obtain ⟨hLn', hLP, hLU, hLexp, hLUf, hLnUf⟩ := mkCol_facts mL pL
  obtain ⟨hRn', hRP, hRU, hRexp, hRUf, hRnUf⟩ := mkCol_facts mR pR
  have hLn27 : (stsOf pL).length ≤ 27 := by rw [← hLn']; exact hLn
  have hRn27 : (stsOf pR).length ≤ 27 := by rw [← hRn']; exact hRn
  have hpL32 : pL.length ≤ 32 := by simpa [pL] using h32
  have hpR32 : pR.length ≤ 32 := by simpa [pR] using h32
  have hSBL := states_lt_of_cols pL hpL32
  have hSBR := states_lt_of_cols pR hpR32
  have htL' : (mL == UTYPE) = false → 1 ≤ typeIndex mL := by
    intro hu; rcases htL with h | h
    · rw [hLU, hu] at h; exact absurd h (by decide)
    · exact h
  have htR' : (mR == UTYPE) = false → 1 ≤ typeIndex mR := by
    intro hu; rcases htR with h | h
    · rw [hRU, hu] at h; exact absurd h (by decide)
    · exact h
  -- the pass as a fold
  rw [passQ_eq_foldl] at hok hr0 hc0 hr1 hc1 hfin
  obtain ⟨-, hchain⟩ := foldl_stepQ_ok false _ _ es _ hok
  have hnd := chainQ_nodup_idx false _ _ es 0 hchain
  have hmem := chainQ_mem false _ _ es 0 hchain
  have hbnd := entriesQ_bounds false ne blob
  have hent : ∀ e ∈ es, e.1 < (stsOf pL).length ∧ e.2.1 < (stsOf pR).length ∧ e.2.2.1 < 1000000
      ∧ (-(OFF : Int) ≤ e.2.2.2.1 ∧ e.2.2.2.1 + OFF < 1000000)
      ∧ compat ((stsOf pL).getD e.1 0) ((stsOf pR).getD e.2.1 0) = true
      ∧ nonnegQ17 (17 * e.2.2.1) (9 * e.2.2.2.1) = true := by
    intro e he
    obtain ⟨-, h1, h2, h3, h4, -⟩ := hmem e he
    rw [hLn'] at h1; rw [hRn'] at h2
    refine ⟨h1, h2, (hbnd e he).2.2.1, (hbnd e he).2.2.2.1, ?_, h4⟩
    rw [hLP, hRP, stateAt_packStates _ hSBL _ h1, stateAt_packStates _ hSBR _ h2] at h3
    rw [getD_of_lt h1, getD_of_lt h2]; exact h3
  have hfields := foldl_stepQ_fields false (mkCol mL pL) (mkCol mR pR) es ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, true⟩
  simp only [Nat.zero_add, Int.zero_add, Bool.false_eq_true, ↓reduceIte] at hfields
  obtain ⟨hf0, hf1, hfc0, hfc1, hfrc, hfcc, hfq0, hfq1, -, -⟩ := hfields
  have hndR : ((es.map toR).map idxR).Nodup := by rw [map_idxR_toR]; exact hnd
  have hndR1 : ((es.map toR1).map idxR).Nodup := by rw [map_idxR_toR1]; exact hnd
  have hmemR : ∀ e ∈ es.map toR, e.1 < (stsOf pL).length ∧ e.2.1 < (stsOf pR).length ∧ e.2.2.1 < 1000000 := by
    intro e he; obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact ⟨(hent e' he').1, (hent e' he').2.1, (hent e' he').2.2.1⟩
  have hmemR1 : ∀ e ∈ es.map toR1, e.1 < (stsOf pL).length ∧ e.2.1 < (stsOf pR).length ∧ e.2.2.1 < 1000000 := by
    intro e he; obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    refine ⟨(hent e' he').1, (hent e' he').2.1, ?_⟩
    have := (hent e' he').2.2.2.1; unfold toR1; simp only; omega
  -- v0 row and column sums
  have hrow0 : ∀ s (hs : s < (stsOf pL).length), rowSumR (es.map toR) s = lawE0 mL pL (stsOf pL)[s] := by
    rw [hf0, hLexp] at hr0
    have hsplit := pkList_range_sumR (fun e => e.1) (fun e => e.2.2.1) (es.map toR) (stsOf pL).length
    rw [sumR_congr _ (fun e => e.2.2.1 * B ^ e.1) _ (fun e he => by rw [if_pos (hmemR e he).1])] at hsplit
    rw [← hsplit] at hr0
    intro s hs
    have := pkList_inj B (by decide) (fun s => sumR (fun e => if e.1 = s then e.2.2.1 else 0) (es.map toR))
      (lawE0 mL pL) (List.range (stsOf pL).length) (stsOf pL) (by simp)
      (fun s _ => rowSumR_lt_B _ (stsOf pR).length hRn27 hndR (fun e he => ⟨(hmemR e he).2.1, (hmemR e he).2.2⟩) s)
      (fun st _ => by
        unfold lawE0; split
        · decide
        · have := countOf_lt (subTable (typeIndex mL)) pL st
          show 1000 * countOf (subTable (typeIndex mL)) pL st < 100000000
          omega)
      hr0 s (by simpa using hs) hs
    unfold rowSumR; simpa using this
  have hcol0 : ∀ t (ht : t < (stsOf pR).length), colSumR (es.map toR) t = lawE0 mR pR (stsOf pR)[t] := by
    rw [hfc0, hRexp] at hc0
    have hsplit := pkList_range_sumR (fun e => e.2.1) (fun e => e.2.2.1) (es.map toR) (stsOf pR).length
    rw [sumR_congr _ (fun e => e.2.2.1 * B ^ e.2.1) _ (fun e he => by rw [if_pos (hmemR e he).2.1])] at hsplit
    rw [← hsplit] at hc0
    intro t ht
    have := pkList_inj B (by decide) (fun t => sumR (fun e => if e.2.1 = t then e.2.2.1 else 0) (es.map toR))
      (lawE0 mR pR) (List.range (stsOf pR).length) (stsOf pR) (by simp)
      (fun t ht' => colSumR_lt_B _ (stsOf pL).length hLn27 hndR
        (fun e he => ⟨(hmemR e he).1, by have := (hmemR e he).2.1; omega, (hmemR e he).2.2⟩) t
        (by have := List.mem_range.mp ht'; omega))
      (fun st _ => by
        unfold lawE0; split
        · decide
        · have := countOf_lt (subTable (typeIndex mR)) pR st
          show 1000 * countOf (subTable (typeIndex mR)) pR st < 100000000
          omega)
      hc0 t (by simpa using ht) ht
    unfold colSumR; simpa using this
  -- entry counts per row and column (from `rc`, `cc`)
  have hrc : (es.foldl (stepQ' false (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, true⟩).rc
      = pkList B (keyCnt (fun e => e.1) (es.map toR)) (List.range (stsOf pL).length) 0 := by
    rw [hfrc]; exact keySum_pow (fun e => e.1) (es.map toR) _ (fun e he => (hmemR e he).1)
  have hcc : (es.foldl (stepQ' false (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, true⟩).cc
      = pkList B (keyCnt (fun e => e.2.1) (es.map toR)) (List.range (stsOf pR).length) 0 := by
    rw [hfcc]; exact keySum_pow (fun e => e.2.1) (es.map toR) _ (fun e he => (hmemR e he).2.1)
  have hcntL : ∀ s, keyCnt (fun e => e.1) (es.map toR) s ≤ 54 := fun s =>
    keyCnt_le (fun e => e.1) (fun e => e.2.1) false (es.map toR) (stsOf pR).length hRn27 hndR (fun _ => rfl)
      (fun e he => (hmemR e he).2.1) (fun e he => by have := (hmemR e he).2.1; omega)
      (fun e he => by have := (hmemR e he).1; omega) s
  have hcntR : ∀ t, keyCnt (fun e => e.2.1) (es.map toR) t ≤ 54 := fun t =>
    keyCnt_le (fun e => e.2.1) (fun e => e.1) true (es.map toR) (stsOf pL).length hLn27 hndR (fun _ => rfl)
      (fun e he => (hmemR e he).1) (fun e he => by have := (hmemR e he).1; omega)
      (fun e he => by have := (hmemR e he).2.1; omega) t
  -- v1 row sums
  have hrow1 : ∀ s (hs : s < (stsOf pL).length),
      sumInt (fun e => if e.1 = s then e.2.2.2.1 else 0) es = lawE1 mL (stsOf pL)[s] := by
    rw [hf1, hrc, exp1Of_eq mL pL _ hcntL] at hr1
    have hsplit := pkList_range_sumR (fun e => e.1) (fun e => e.2.2.1) (es.map toR1) (stsOf pL).length
    rw [sumR_congr _ (fun e => e.2.2.1 * B ^ e.1) _ (fun e he => by rw [if_pos (hmemR1 e he).1])] at hsplit
    rw [← hsplit] at hr1
    intro s hs
    have hdig := pkList_inj B (by decide) (fun s => sumR (fun e => if e.1 = s then e.2.2.1 else 0) (es.map toR1))
      (exp1Digit mL (stsOf pL) (keyCnt (fun e => e.1) (es.map toR))) (List.range (stsOf pL).length)
      (List.range (stsOf pL).length) rfl
      (fun s _ => rowSumR_lt_B _ (stsOf pR).length hRn27 hndR1 (fun e he => ⟨(hmemR1 e he).2.1, (hmemR1 e he).2.2⟩) s)
      (fun s _ => by
        unfold exp1Digit; have := hcntL s; unfold B OFF
        split <;> (try split) <;> omega)
      hr1 s (by simpa using hs) (by simpa using hs)
    simp only [List.getElem_range] at hdig
    have hv := v1_key_sum (fun e => e.1) (fun e => e.1) (fun _ => rfl) (fun _ => rfl) es s
      (fun e he => (hent e he).2.2.2.1.1)
    rw [hdig] at hv
    have hg := getD_of_lt (l := stsOf pL) (d := 0) hs
    unfold exp1Digit at hv
    unfold lawE1
    by_cases hu : (mL == UTYPE) = true
    · simp only [hu, eq_self_iff_true, if_true, ↓reduceIte] at hv ⊢
      have hpos : 1 ≤ keyCnt (fun e => e.1) (es.map toR) s := by
        apply keyCnt_pos (fun e => e.1) (fun e => e.2.2.1)
        have := hrow0 s hs; unfold rowSumR at this; rw [this]; unfold lawE0; rw [hu]; simp
      rw [hg] at hv
      by_cases ha : isABA (stsOf pL)[s]
      · rw [if_pos ha] at hv ⊢; unfold OFF at hv; omega
      · rw [if_neg ha] at hv ⊢; unfold OFF at hv; omega
    · have hu' : (mL == UTYPE) = false := by simpa using hu
      simp only [hu', Bool.false_eq_true, ↓reduceIte] at hv ⊢
      unfold OFF at hv; omega
  -- v1 column sums
  have hcol1 : ∀ t (ht : t < (stsOf pR).length),
      sumInt (fun e => if e.2.1 = t then e.2.2.2.1 else 0) es = lawE1 mR (stsOf pR)[t] := by
    rw [hfc1, hcc, exp1Of_eq mR pR _ hcntR] at hc1
    have hsplit := pkList_range_sumR (fun e => e.2.1) (fun e => e.2.2.1) (es.map toR1) (stsOf pR).length
    rw [sumR_congr _ (fun e => e.2.2.1 * B ^ e.2.1) _ (fun e he => by rw [if_pos (hmemR1 e he).2.1])] at hsplit
    rw [← hsplit] at hc1
    intro t ht
    have hdig := pkList_inj B (by decide) (fun t => sumR (fun e => if e.2.1 = t then e.2.2.1 else 0) (es.map toR1))
      (exp1Digit mR (stsOf pR) (keyCnt (fun e => e.2.1) (es.map toR))) (List.range (stsOf pR).length)
      (List.range (stsOf pR).length) rfl
      (fun t ht' => colSumR_lt_B _ (stsOf pL).length hLn27 hndR1
        (fun e he => ⟨(hmemR1 e he).1, by have := (hmemR1 e he).2.1; omega, (hmemR1 e he).2.2⟩) t
        (by have := List.mem_range.mp ht'; omega))
      (fun t _ => by
        unfold exp1Digit; have := hcntR t; unfold B OFF
        split <;> (try split) <;> omega)
      hc1 t (by simpa using ht) (by simpa using ht)
    simp only [List.getElem_range] at hdig
    have hv := v1_key_sum (fun e => e.2.1) (fun e => e.2.1) (fun _ => rfl) (fun _ => rfl) es t
      (fun e he => (hent e he).2.2.2.1.1)
    rw [hdig] at hv
    have hg := getD_of_lt (l := stsOf pR) (d := 0) ht
    unfold exp1Digit at hv
    unfold lawE1
    by_cases hu : (mR == UTYPE) = true
    · simp only [hu, eq_self_iff_true, if_true, ↓reduceIte] at hv ⊢
      have hpos : 1 ≤ keyCnt (fun e => e.2.1) (es.map toR) t := by
        apply keyCnt_pos (fun e => e.2.1) (fun e => e.2.2.1)
        have := hcol0 t ht; unfold colSumR at this; rw [this]; unfold lawE0; rw [hu]; simp
      rw [hg] at hv
      by_cases ha : isABA (stsOf pR)[t]
      · rw [if_pos ha] at hv ⊢; unfold OFF at hv; omega
      · rw [if_neg ha] at hv ⊢; unfold OFF at hv; omega
    · have hu' : (mR == UTYPE) = false := by simpa using hu
      simp only [hu', Bool.false_eq_true, ↓reduceIte] at hv ⊢
      unfold OFF at hv; omega
  -- column facts for non-uniform columns
  have hcLf : (mL == UTYPE) = false → sumNat ((stsOf pL).map (cntOf mL pL)) = 108
      ∧ sumNat (((stsOf pL).map (cntOf mL pL)).map fun k => k * k) ≤ 972
      ∧ (∀ st ∈ stsOf pL, cntOf mL pL st ∣ lc) ∧ 0 < lc := by
    intro hu
    obtain ⟨-, hlcm, hsc, hsc2⟩ := hLnUf hu
    unfold colOK at hcL; rw [hLU, hu] at hcL
    simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcL
    refine ⟨by rw [← hsc]; exact hcL.1.1, by rw [← hsc2]; exact hcL.1.2,
      fun st hst => mem_dvd_foldl_lcm _ _ _ st hst, ?_⟩
    show 0 < (stsOf pL).foldl (fun l st => Nat.lcm l (cntOf mL pL st)) 1
    rw [← hlcm]; exact hcL.2
  have hcRf : (mR == UTYPE) = false → sumNat ((stsOf pR).map (cntOf mR pR)) = 108
      ∧ sumNat (((stsOf pR).map (cntOf mR pR)).map fun k => k * k) ≤ 972 := by
    intro hu
    obtain ⟨-, -, hsc, hsc2⟩ := hRnUf hu
    unfold colOK at hcR; rw [hRU, hu] at hcR
    simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcR
    exact ⟨by rw [← hsc]; exact hcR.1.1, by rw [← hsc2]; exact hcR.1.2⟩
  -- the collision inequality
  have hdq : ∀ e ∈ es, dq (mkCol mL pL) e = dqSem mL pL lc e := by
    intro e he
    have h1 := (hent e he).1
    unfold dq dqSem
    rw [hLP, stateAt_packStates _ hSBL _ h1, ← getD_of_lt (l := stsOf pL) (d := 0) h1, hLU]
    by_cases hu : (mL == UTYPE) = true
    · simp only [hu, eq_self_iff_true, if_true, ↓reduceIte]
    · have hu' : (mL == UTYPE) = false := by simpa using hu
      obtain ⟨hCV, hlcm, -, -⟩ := hLnUf hu'
      simp only [hu', Bool.false_eq_true, ↓reduceIte]
      rw [hCV, cvDigit_eq mL pL e.1 h1, hlcm]
  have hq0 : (es.foldl (stepQ' false (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, true⟩).q0
      = sumInt (fun e => (dqSem mL pL lc e).1) es := by
    rw [hfq0]; exact sumInt_congr _ _ es (fun e he => by rw [hdq e he])
  have hq1 : (es.foldl (stepQ' false (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, true⟩).q1
      = sumInt (fun e => (dqSem mL pL lc e).2) es := by
    rw [hfq1]; exact sumInt_congr _ _ es (fun e he => by rw [hdq e he])
  have hfin' : negQ17 (5 * sumInt (fun e => (dqSem mL pL lc e).1) es + 17 * sumInt (fun e => (dqSem mL pL lc e).2) es
        - 2 * ((if mL == UTYPE then 12 else lc) * XD * XD))
        (sumInt (fun e => (dqSem mL pL lc e).1) es + 5 * sumInt (fun e => (dqSem mL pL lc e).2) es) = true
      ∧ ((mL == UTYPE) = true → negQ17 (18 * (5 * sumInt (fun e => (dqSem mL pL lc e).1) es
          + 17 * sumInt (fun e => (dqSem mL pL lc e).2) es) - 34 * ((if mL == UTYPE then 12 else lc) * XD * XD))
        (18 * (sumInt (fun e => (dqSem mL pL lc e).1) es + 5 * sumInt (fun e => (dqSem mL pL lc e).2) es)) = true) := by
    unfold finalQ at hfin
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hfin
    rw [hq0, hq1, hLU] at hfin
    by_cases hu : (mL == UTYPE) = true
    · simp only [hu, eq_self_iff_true, if_true, ↓reduceIte] at hfin ⊢
      rcases hfin with ⟨hb, hs | hs⟩
      · exact absurd hs (by decide)
      · exact ⟨hb, fun _ => hs⟩
    · have hu' : (mL == UTYPE) = false := by simpa using hu
      obtain ⟨-, hlcm, -, -⟩ := hLnUf hu'
      simp only [hu', Bool.false_eq_true, ↓reduceIte] at hfin ⊢
      rw [hlcm] at hfin
      exact ⟨hfin.1, fun h => absurd h (by decide)⟩
  exact ⟨hvL, hvR, h32, hLn27, hRn27, htL', htR', hnd, hent, hrow0, hrow1, hcol0, hcol1, hcLf, hcRf, hfin'⟩

/-! ### Format `2` (rational fourth-root) -/

/-- `checkRecord` at format `2`, unfolded -/
theorem checkRecord_two_eq (mL mR M ne blob : Nat) :
    checkRecord 2 mL mR M ne blob =
      (let cols := colours mL mR M
       let L := mkCol mL (cols.map Prod.fst)
       let R := mkCol mR (cols.map Prod.snd)
       let a := passR true L R ne blob ⟨0, 0, 0, 0, 0, true⟩
       (validType mL && validType mR && decide (cols.length ≤ 32) && decide (L.n ≤ 27) && decide (R.n ≤ 27)
         && colOK L && colOK R && (L.isU || decide (typeIndex mL ≥ 1)) && (R.isU || decide (typeIndex mR ≥ 1)))
         && !L.isU && !R.isU && a.ok && (a.r0 == L.exp0) && (a.c0 == R.exp0) && finalR true L a) := rfl

theorem checkRecord_two_spec (mL mR M ne blob : Nat) (h : checkRecord 2 mL mR M ne blob = true) :
    let cols := colours mL mR M
    let pL := cols.map Prod.fst
    let pR := cols.map Prod.snd
    let es := entriesR true ne blob
    let lc := (stsOf pL).foldl (fun l st => Nat.lcm l (cntOf mL pL st)) 1
    validType mL = true ∧ validType mR = true ∧ cols.length ≤ 32
      ∧ (stsOf pL).length ≤ 27 ∧ (stsOf pR).length ≤ 27
      ∧ (mL == UTYPE) = false ∧ (mR == UTYPE) = false ∧ 1 ≤ typeIndex mL ∧ 1 ≤ typeIndex mR
      ∧ (es.map idxR).Nodup
      ∧ (∀ e ∈ es, e.1 < (stsOf pL).length ∧ e.2.1 < (stsOf pR).length ∧ e.2.2.1 < 1000000
          ∧ compat ((stsOf pL).getD e.1 0) ((stsOf pR).getD e.2.1 0) = true)
      ∧ (∀ s (hs : s < (stsOf pL).length), rowSumR es s = 1000 * cntOf mL pL (stsOf pL)[s])
      ∧ (∀ t (ht : t < (stsOf pR).length), colSumR es t = 1000 * cntOf mR pR (stsOf pR)[t])
      ∧ sumNat ((stsOf pL).map (cntOf mL pL)) = 108
      ∧ sumNat (((stsOf pL).map (cntOf mL pL)).map fun k => k * k) ≤ 972
      ∧ sumNat ((stsOf pR).map (cntOf mR pR)) = 108
      ∧ sumNat (((stsOf pR).map (cntOf mR pR)).map fun k => k * k) ≤ 972
      ∧ (∀ st ∈ stsOf pL, cntOf mL pL st ∣ lc) ∧ 0 < lc
      ∧ (∀ e ∈ es, e.2.2.2 < 10000000
          ∧ LD * E ^ 4 * e.2.2.1 ≤ e.2.2.2 ^ 4 * cntOf mL pL ((stsOf pL).getD e.1 0) * XD)
      ∧ (let NR := sumR (fun e => e.2.2.1 * e.2.2.2) es
         5 * NR ^ 4 < 2 * (D0 * E) ^ 4 ∧ 17 * NR ^ 8 < (2 * (D0 * E) ^ 4 - 5 * NR ^ 4) ^ 2) := by
  intro cols pL pR es lc
  rw [checkRecord_two_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hvL, hvR⟩, h32⟩, hLn⟩, hRn⟩, hcL⟩, hcR⟩, htL⟩, htR⟩, hLU⟩, hRU⟩, hok⟩, hr0⟩, hc0⟩, hfin⟩ := h
  -- the two columns
  have hLU' : (mL == UTYPE) = false := by rw [← mkCol_isU mL pL]; exact hLU
  have hRU' : (mR == UTYPE) = false := by rw [← mkCol_isU mR pR]; exact hRU
  have hL := mkCol_spec_nonU mL pL hLU'
  have hR := mkCol_spec_nonU mR pR hRU'
  obtain ⟨hLn', hLP, -, hLCV, hLexp, hLlcm, hLsc, hLsc2⟩ := hL
  obtain ⟨hRn', hRP, -, hRCV, hRexp, hRlcm, hRsc, hRsc2⟩ := hR
  have htL' : 1 ≤ typeIndex mL := by
    rcases htL with h | h
    · rw [hLU] at h; exact absurd h (by decide)
    · exact h
  have htR' : 1 ≤ typeIndex mR := by
    rcases htR with h | h
    · rw [hRU] at h; exact absurd h (by decide)
    · exact h
  have hLn27 : (stsOf pL).length ≤ 27 := by rw [← hLn']; exact hLn
  have hRn27 : (stsOf pR).length ≤ 27 := by rw [← hRn']; exact hRn
  have hcL' : (mkCol mL pL).sumC = 108 ∧ (mkCol mL pL).sumC2 ≤ 972 ∧ 0 < (mkCol mL pL).lcm := by
    unfold colOK at hcL; rw [hLU] at hcL
    simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcL
    exact ⟨hcL.1.1, hcL.1.2, hcL.2⟩
  have hcR' : (mkCol mR pR).sumC = 108 ∧ (mkCol mR pR).sumC2 ≤ 972 := by
    unfold colOK at hcR; rw [hRU] at hcR
    simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcR
    exact ⟨hcR.1.1, hcR.1.2⟩
  have hpL32 : pL.length ≤ 32 := by simpa [pL] using h32
  have hpR32 : pR.length ≤ 32 := by simpa [pR] using h32
  have hSBL := states_lt_of_cols pL hpL32
  have hSBR := states_lt_of_cols pR hpR32
  -- the pass as a fold
  rw [passR_eq_foldl] at hok hr0 hc0 hfin
  obtain ⟨-, hchain⟩ := foldl_stepR_ok true _ _ es _ hok
  have hnd := chainR_nodup_idx true _ _ es 0 hchain
  have hmem := chainR_mem true _ _ es 0 hchain
  have hbnd := entriesR_bounds true ne blob
  have hent : ∀ e ∈ es, e.1 < (stsOf pL).length ∧ e.2.1 < (stsOf pR).length ∧ e.2.2.1 < 1000000
      ∧ compat ((stsOf pL).getD e.1 0) ((stsOf pR).getD e.2.1 0) = true := by
    intro e he
    obtain ⟨-, h1, h2, h3, -⟩ := hmem e he
    rw [hLn'] at h1; rw [hRn'] at h2
    refine ⟨h1, h2, (hbnd e he).2.2.1, ?_⟩
    rw [hLP, hRP, stateAt_packStates _ hSBL _ h1, stateAt_packStates _ hSBR _ h2] at h3
    rw [getD_of_lt h1, getD_of_lt h2]; exact h3
  -- row sums
  have hrow : ∀ s (hs : s < (stsOf pL).length), rowSumR es s = 1000 * cntOf mL pL (stsOf pL)[s] := by
    rw [foldl_stepR_r0, hLexp] at hr0
    simp only [Nat.zero_add] at hr0
    have hsplit := pkList_range_sumR (fun e => e.1) (fun e => e.2.2.1) es (stsOf pL).length
    rw [sumR_congr _ (fun e => e.2.2.1 * B ^ e.1) es (fun e he => by rw [if_pos (hent e he).1])] at hsplit
    rw [← hsplit] at hr0
    intro s hs
    have := pkList_inj B (by decide) (fun s => sumR (fun e => if e.1 = s then e.2.2.1 else 0) es)
      (fun st => 1000 * cntOf mL pL st) (List.range (stsOf pL).length) (stsOf pL) (by simp)
      (fun s _ => rowSumR_lt_B es (stsOf pR).length hRn27 hnd (fun e he => ⟨(hent e he).2.1, (hent e he).2.2.1⟩) s)
      (fun st _ => by
        have := countOf_lt (subTable (typeIndex mL)) pL st
        show 1000 * countOf (subTable (typeIndex mL)) pL st < 100000000
        omega)
      hr0 s (by simpa using hs) hs
    unfold rowSumR; simpa using this
  have hcol : ∀ t (ht : t < (stsOf pR).length), colSumR es t = 1000 * cntOf mR pR (stsOf pR)[t] := by
    rw [foldl_stepR_c0, hRexp] at hc0
    simp only [Nat.zero_add] at hc0
    have hsplit := pkList_range_sumR (fun e => e.2.1) (fun e => e.2.2.1) es (stsOf pR).length
    rw [sumR_congr _ (fun e => e.2.2.1 * B ^ e.2.1) es (fun e he => by rw [if_pos (hent e he).2.1])] at hsplit
    rw [← hsplit] at hc0
    intro t ht
    have := pkList_inj B (by decide) (fun t => sumR (fun e => if e.2.1 = t then e.2.2.1 else 0) es)
      (fun st => 1000 * cntOf mR pR st) (List.range (stsOf pR).length) (stsOf pR) (by simp)
      (fun t ht' => colSumR_lt_B es (stsOf pL).length hLn27 hnd
        (fun e he => ⟨(hent e he).1, (hbnd e he).2.1, (hent e he).2.2.1⟩) t
        (by have := List.mem_range.mp ht'; omega))
      (fun st _ => by
        have := countOf_lt (subTable (typeIndex mR)) pR st
        show 1000 * countOf (subTable (typeIndex mR)) pR st < 100000000
        omega)
      hc0 t (by simpa using ht) ht
    unfold colSumR; simpa using this
  -- the fourth-root witnesses and bound
  have hwit : ∀ e ∈ es, e.2.2.2 < 10000000
      ∧ LD * E ^ 4 * e.2.2.1 ≤ e.2.2.2 ^ 4 * cntOf mL pL ((stsOf pL).getD e.1 0) * XD := by
    intro e he
    obtain ⟨-, h1, -, -, hw⟩ := hmem e he
    rw [hLn'] at h1
    have hw' := hw rfl
    rw [hLCV, cvDigit_eq mL pL e.1 h1] at hw'
    exact ⟨(hbnd e he).2.2.2.1, hw'⟩
  have hq : (5 * ((es.foldl (stepR' true (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, true⟩).nr) ^ 4
        < 2 * (D0 * E) ^ 4)
      ∧ 17 * ((es.foldl (stepR' true (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, true⟩).nr) ^ 8
        < (2 * (D0 * E) ^ 4 - 5 * ((es.foldl (stepR' true (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, true⟩).nr) ^ 4) ^ 2 := by
    unfold finalR at hfin
    simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hfin
    exact hfin
  rw [foldl_stepR_nr, Nat.zero_add] at hq
  refine ⟨hvL, hvR, h32, hLn27, hRn27, hLU', hRU', htL', htR', hnd, hent, hrow, hcol,
    by rw [← hLsc]; exact hcL'.1, by rw [← hLsc2]; exact hcL'.2.1, by rw [← hRsc]; exact hcR'.1, by rw [← hRsc2]; exact hcR'.2,
    fun st hst => mem_dvd_foldl_lcm _ _ _ st hst,
    (by show 0 < (stsOf pL).foldl (fun l st => Nat.lcm l (cntOf mL pL st)) 1; rw [← hLlcm]; exact hcL'.2.2), hwit, hq⟩


/-! ### Format `3` (`ℚ(√17)` fourth-root) -/

/-- `checkRecord` at format `3`, unfolded -/
theorem checkRecord_three_eq (mL mR M ne blob : Nat) :
    checkRecord 3 mL mR M ne blob =
      (let cols := colours mL mR M
       let L := mkCol mL (cols.map Prod.fst)
       let R := mkCol mR (cols.map Prod.snd)
       let a := passQ true L R ne blob ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, true⟩
       (validType mL && validType mR && decide (cols.length ≤ 32) && decide (L.n ≤ 27) && decide (R.n ≤ 27)
         && colOK L && colOK R && (L.isU || decide (typeIndex mL ≥ 1)) && (R.isU || decide (typeIndex mR ≥ 1)))
         && (!true || !L.isU) && a.ok && (a.r0 == L.exp0) && (a.c0 == R.exp0)
         && (a.r1 == exp1Of L a.rc) && (a.c1 == exp1Of R a.cc) && finalQ true L a) := rfl

set_option maxHeartbeats 2000000 in
theorem checkRecord_three_spec (mL mR M ne blob : Nat) (h : checkRecord 3 mL mR M ne blob = true) :
    let cols := colours mL mR M
    let pL := cols.map Prod.fst
    let pR := cols.map Prod.snd
    let es := entriesQ true ne blob
    let lc := (stsOf pL).foldl (fun l st => Nat.lcm l (cntOf mL pL st)) 1
    validType mL = true ∧ validType mR = true ∧ cols.length ≤ 32
      ∧ (stsOf pL).length ≤ 27 ∧ (stsOf pR).length ≤ 27
      ∧ ((mL == UTYPE) = false → 1 ≤ typeIndex mL) ∧ ((mR == UTYPE) = false → 1 ≤ typeIndex mR)
      ∧ (es.map idxQ).Nodup
      ∧ (∀ e ∈ es, e.1 < (stsOf pL).length ∧ e.2.1 < (stsOf pR).length ∧ e.2.2.1 < 1000000
          ∧ (-(OFF : Int) ≤ e.2.2.2.1 ∧ e.2.2.2.1 + OFF < 1000000)
          ∧ compat ((stsOf pL).getD e.1 0) ((stsOf pR).getD e.2.1 0) = true
          ∧ nonnegQ17 (17 * e.2.2.1) (9 * e.2.2.2.1) = true)
      ∧ (∀ s (hs : s < (stsOf pL).length), rowSumR (es.map toR) s = lawE0 mL pL (stsOf pL)[s])
      ∧ (∀ s (hs : s < (stsOf pL).length),
          sumInt (fun e => if e.1 = s then e.2.2.2.1 else 0) es = lawE1 mL (stsOf pL)[s])
      ∧ (∀ t (ht : t < (stsOf pR).length), colSumR (es.map toR) t = lawE0 mR pR (stsOf pR)[t])
      ∧ (∀ t (ht : t < (stsOf pR).length),
          sumInt (fun e => if e.2.1 = t then e.2.2.2.1 else 0) es = lawE1 mR (stsOf pR)[t])
      ∧ ((mL == UTYPE) = false → sumNat ((stsOf pL).map (cntOf mL pL)) = 108
          ∧ sumNat (((stsOf pL).map (cntOf mL pL)).map fun k => k * k) ≤ 972
          ∧ (∀ st ∈ stsOf pL, cntOf mL pL st ∣ lc) ∧ 0 < lc)
      ∧ ((mR == UTYPE) = false → sumNat ((stsOf pR).map (cntOf mR pR)) = 108
          ∧ sumNat (((stsOf pR).map (cntOf mR pR)).map fun k => k * k) ≤ 972)
      ∧ (mL == UTYPE) = false
      ∧ (∀ e ∈ es, e.2.2.2.2 < 10000000
          ∧ nonnegQ17 ((e.2.2.2.2 ^ 4 * cntOf mL pL ((stsOf pL).getD e.1 0) * XD : Nat)
              - (LD * E ^ 4 * e.2.2.1 : Nat) : Int) (-(972 * E ^ 4 : Nat) * e.2.2.2.1) = true)
      ∧ (let R0 : Int := 17 * sumR (fun e => e.2.2.1 * e.2.2.2) (es.map toR)
         let R1 : Int := 9 * sumInt (fun e => e.2.2.2.1 * e.2.2.2.2) es
         let S0 := R0 * R0 + 17 * R1 * R1
         let S1 := 2 * R0 * R1
         let T0 := S0 * S0 + 17 * S1 * S1
         let T1 := 2 * S0 * S1
         negQ17 (5 * T0 + 17 * T1 - 2 * ((XD * E : Nat) : Int) ^ 4) (T0 + 5 * T1) = true) := by
  intro cols pL pR es lc
  rw [checkRecord_three_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
    Bool.not_true, Bool.false_or] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hvL, hvR⟩, h32⟩, hLn⟩, hRn⟩, hcL⟩, hcR⟩, htL⟩, htR⟩, hLUf0⟩, hok⟩, hr0⟩, hc0⟩, hr1⟩, hc1⟩, hfin⟩ := h
  obtain ⟨hLn', hLP, hLU, hLexp, hLUf, hLnUf⟩ := mkCol_facts mL pL
  obtain ⟨hRn', hRP, hRU, hRexp, hRUf, hRnUf⟩ := mkCol_facts mR pR
  have hLn27 : (stsOf pL).length ≤ 27 := by rw [← hLn']; exact hLn
  have hRn27 : (stsOf pR).length ≤ 27 := by rw [← hRn']; exact hRn
  have hpL32 : pL.length ≤ 32 := by simpa [pL] using h32
  have hpR32 : pR.length ≤ 32 := by simpa [pR] using h32
  have hSBL := states_lt_of_cols pL hpL32
  have hSBR := states_lt_of_cols pR hpR32
  have htL' : (mL == UTYPE) = false → 1 ≤ typeIndex mL := by
    intro hu; rcases htL with h | h
    · rw [hLU, hu] at h; exact absurd h (by decide)
    · exact h
  have htR' : (mR == UTYPE) = false → 1 ≤ typeIndex mR := by
    intro hu; rcases htR with h | h
    · rw [hRU, hu] at h; exact absurd h (by decide)
    · exact h
  -- the pass as a fold
  rw [passQ_eq_foldl] at hok hr0 hc0 hr1 hc1 hfin
  obtain ⟨-, hchain⟩ := foldl_stepQ_ok true _ _ es _ hok
  have hnd := chainQ_nodup_idx true _ _ es 0 hchain
  have hmem := chainQ_mem true _ _ es 0 hchain
  have hbnd := entriesQ_bounds true ne blob
  have hent : ∀ e ∈ es, e.1 < (stsOf pL).length ∧ e.2.1 < (stsOf pR).length ∧ e.2.2.1 < 1000000
      ∧ (-(OFF : Int) ≤ e.2.2.2.1 ∧ e.2.2.2.1 + OFF < 1000000)
      ∧ compat ((stsOf pL).getD e.1 0) ((stsOf pR).getD e.2.1 0) = true
      ∧ nonnegQ17 (17 * e.2.2.1) (9 * e.2.2.2.1) = true := by
    intro e he
    obtain ⟨-, h1, h2, h3, h4, -⟩ := hmem e he
    rw [hLn'] at h1; rw [hRn'] at h2
    refine ⟨h1, h2, (hbnd e he).2.2.1, (hbnd e he).2.2.2.1, ?_, h4⟩
    rw [hLP, hRP, stateAt_packStates _ hSBL _ h1, stateAt_packStates _ hSBR _ h2] at h3
    rw [getD_of_lt h1, getD_of_lt h2]; exact h3
  have hfields := foldl_stepQ_fields true (mkCol mL pL) (mkCol mR pR) es ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, true⟩
  simp only [Nat.zero_add, Int.zero_add, Bool.false_eq_true, ↓reduceIte] at hfields
  obtain ⟨hf0, hf1, hfc0, hfc1, hfrc, hfcc, hfq0, hfq1, -, -⟩ := hfields
  have hndR : ((es.map toR).map idxR).Nodup := by rw [map_idxR_toR]; exact hnd
  have hndR1 : ((es.map toR1).map idxR).Nodup := by rw [map_idxR_toR1]; exact hnd
  have hmemR : ∀ e ∈ es.map toR, e.1 < (stsOf pL).length ∧ e.2.1 < (stsOf pR).length ∧ e.2.2.1 < 1000000 := by
    intro e he; obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact ⟨(hent e' he').1, (hent e' he').2.1, (hent e' he').2.2.1⟩
  have hmemR1 : ∀ e ∈ es.map toR1, e.1 < (stsOf pL).length ∧ e.2.1 < (stsOf pR).length ∧ e.2.2.1 < 1000000 := by
    intro e he; obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    refine ⟨(hent e' he').1, (hent e' he').2.1, ?_⟩
    have := (hent e' he').2.2.2.1; unfold toR1; simp only; omega
  -- v0 row and column sums
  have hrow0 : ∀ s (hs : s < (stsOf pL).length), rowSumR (es.map toR) s = lawE0 mL pL (stsOf pL)[s] := by
    rw [hf0, hLexp] at hr0
    have hsplit := pkList_range_sumR (fun e => e.1) (fun e => e.2.2.1) (es.map toR) (stsOf pL).length
    rw [sumR_congr _ (fun e => e.2.2.1 * B ^ e.1) _ (fun e he => by rw [if_pos (hmemR e he).1])] at hsplit
    rw [← hsplit] at hr0
    intro s hs
    have := pkList_inj B (by decide) (fun s => sumR (fun e => if e.1 = s then e.2.2.1 else 0) (es.map toR))
      (lawE0 mL pL) (List.range (stsOf pL).length) (stsOf pL) (by simp)
      (fun s _ => rowSumR_lt_B _ (stsOf pR).length hRn27 hndR (fun e he => ⟨(hmemR e he).2.1, (hmemR e he).2.2⟩) s)
      (fun st _ => by
        unfold lawE0; split
        · decide
        · have := countOf_lt (subTable (typeIndex mL)) pL st
          show 1000 * countOf (subTable (typeIndex mL)) pL st < 100000000
          omega)
      hr0 s (by simpa using hs) hs
    unfold rowSumR; simpa using this
  have hcol0 : ∀ t (ht : t < (stsOf pR).length), colSumR (es.map toR) t = lawE0 mR pR (stsOf pR)[t] := by
    rw [hfc0, hRexp] at hc0
    have hsplit := pkList_range_sumR (fun e => e.2.1) (fun e => e.2.2.1) (es.map toR) (stsOf pR).length
    rw [sumR_congr _ (fun e => e.2.2.1 * B ^ e.2.1) _ (fun e he => by rw [if_pos (hmemR e he).2.1])] at hsplit
    rw [← hsplit] at hc0
    intro t ht
    have := pkList_inj B (by decide) (fun t => sumR (fun e => if e.2.1 = t then e.2.2.1 else 0) (es.map toR))
      (lawE0 mR pR) (List.range (stsOf pR).length) (stsOf pR) (by simp)
      (fun t ht' => colSumR_lt_B _ (stsOf pL).length hLn27 hndR
        (fun e he => ⟨(hmemR e he).1, by have := (hmemR e he).2.1; omega, (hmemR e he).2.2⟩) t
        (by have := List.mem_range.mp ht'; omega))
      (fun st _ => by
        unfold lawE0; split
        · decide
        · have := countOf_lt (subTable (typeIndex mR)) pR st
          show 1000 * countOf (subTable (typeIndex mR)) pR st < 100000000
          omega)
      hc0 t (by simpa using ht) ht
    unfold colSumR; simpa using this
  -- entry counts per row and column (from `rc`, `cc`)
  have hrc : (es.foldl (stepQ' true (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, true⟩).rc
      = pkList B (keyCnt (fun e => e.1) (es.map toR)) (List.range (stsOf pL).length) 0 := by
    rw [hfrc]; exact keySum_pow (fun e => e.1) (es.map toR) _ (fun e he => (hmemR e he).1)
  have hcc : (es.foldl (stepQ' true (mkCol mL pL) (mkCol mR pR)) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, true⟩).cc
      = pkList B (keyCnt (fun e => e.2.1) (es.map toR)) (List.range (stsOf pR).length) 0 := by
    rw [hfcc]; exact keySum_pow (fun e => e.2.1) (es.map toR) _ (fun e he => (hmemR e he).2.1)
  have hcntL : ∀ s, keyCnt (fun e => e.1) (es.map toR) s ≤ 54 := fun s =>
    keyCnt_le (fun e => e.1) (fun e => e.2.1) false (es.map toR) (stsOf pR).length hRn27 hndR (fun _ => rfl)
      (fun e he => (hmemR e he).2.1) (fun e he => by have := (hmemR e he).2.1; omega)
      (fun e he => by have := (hmemR e he).1; omega) s
  have hcntR : ∀ t, keyCnt (fun e => e.2.1) (es.map toR) t ≤ 54 := fun t =>
    keyCnt_le (fun e => e.2.1) (fun e => e.1) true (es.map toR) (stsOf pL).length hLn27 hndR (fun _ => rfl)
      (fun e he => (hmemR e he).1) (fun e he => by have := (hmemR e he).1; omega)
      (fun e he => by have := (hmemR e he).2.1; omega) t
  -- v1 row sums
  have hrow1 : ∀ s (hs : s < (stsOf pL).length),
      sumInt (fun e => if e.1 = s then e.2.2.2.1 else 0) es = lawE1 mL (stsOf pL)[s] := by
    rw [hf1, hrc, exp1Of_eq mL pL _ hcntL] at hr1
    have hsplit := pkList_range_sumR (fun e => e.1) (fun e => e.2.2.1) (es.map toR1) (stsOf pL).length
    rw [sumR_congr _ (fun e => e.2.2.1 * B ^ e.1) _ (fun e he => by rw [if_pos (hmemR1 e he).1])] at hsplit
    rw [← hsplit] at hr1
    intro s hs
    have hdig := pkList_inj B (by decide) (fun s => sumR (fun e => if e.1 = s then e.2.2.1 else 0) (es.map toR1))
      (exp1Digit mL (stsOf pL) (keyCnt (fun e => e.1) (es.map toR))) (List.range (stsOf pL).length)
      (List.range (stsOf pL).length) rfl
      (fun s _ => rowSumR_lt_B _ (stsOf pR).length hRn27 hndR1 (fun e he => ⟨(hmemR1 e he).2.1, (hmemR1 e he).2.2⟩) s)
      (fun s _ => by
        unfold exp1Digit; have := hcntL s; unfold B OFF
        split <;> (try split) <;> omega)
      hr1 s (by simpa using hs) (by simpa using hs)
    simp only [List.getElem_range] at hdig
    have hv := v1_key_sum (fun e => e.1) (fun e => e.1) (fun _ => rfl) (fun _ => rfl) es s
      (fun e he => (hent e he).2.2.2.1.1)
    rw [hdig] at hv
    have hg := getD_of_lt (l := stsOf pL) (d := 0) hs
    unfold exp1Digit at hv
    unfold lawE1
    by_cases hu : (mL == UTYPE) = true
    · simp only [hu, eq_self_iff_true, if_true, ↓reduceIte] at hv ⊢
      have hpos : 1 ≤ keyCnt (fun e => e.1) (es.map toR) s := by
        apply keyCnt_pos (fun e => e.1) (fun e => e.2.2.1)
        have := hrow0 s hs; unfold rowSumR at this; rw [this]; unfold lawE0; rw [hu]; simp
      rw [hg] at hv
      by_cases ha : isABA (stsOf pL)[s]
      · rw [if_pos ha] at hv ⊢; unfold OFF at hv; omega
      · rw [if_neg ha] at hv ⊢; unfold OFF at hv; omega
    · have hu' : (mL == UTYPE) = false := by simpa using hu
      simp only [hu', Bool.false_eq_true, ↓reduceIte] at hv ⊢
      unfold OFF at hv; omega
  -- v1 column sums
  have hcol1 : ∀ t (ht : t < (stsOf pR).length),
      sumInt (fun e => if e.2.1 = t then e.2.2.2.1 else 0) es = lawE1 mR (stsOf pR)[t] := by
    rw [hfc1, hcc, exp1Of_eq mR pR _ hcntR] at hc1
    have hsplit := pkList_range_sumR (fun e => e.2.1) (fun e => e.2.2.1) (es.map toR1) (stsOf pR).length
    rw [sumR_congr _ (fun e => e.2.2.1 * B ^ e.2.1) _ (fun e he => by rw [if_pos (hmemR1 e he).2.1])] at hsplit
    rw [← hsplit] at hc1
    intro t ht
    have hdig := pkList_inj B (by decide) (fun t => sumR (fun e => if e.2.1 = t then e.2.2.1 else 0) (es.map toR1))
      (exp1Digit mR (stsOf pR) (keyCnt (fun e => e.2.1) (es.map toR))) (List.range (stsOf pR).length)
      (List.range (stsOf pR).length) rfl
      (fun t ht' => colSumR_lt_B _ (stsOf pL).length hLn27 hndR1
        (fun e he => ⟨(hmemR1 e he).1, by have := (hmemR1 e he).2.1; omega, (hmemR1 e he).2.2⟩) t
        (by have := List.mem_range.mp ht'; omega))
      (fun t _ => by
        unfold exp1Digit; have := hcntR t; unfold B OFF
        split <;> (try split) <;> omega)
      hc1 t (by simpa using ht) (by simpa using ht)
    simp only [List.getElem_range] at hdig
    have hv := v1_key_sum (fun e => e.2.1) (fun e => e.2.1) (fun _ => rfl) (fun _ => rfl) es t
      (fun e he => (hent e he).2.2.2.1.1)
    rw [hdig] at hv
    have hg := getD_of_lt (l := stsOf pR) (d := 0) ht
    unfold exp1Digit at hv
    unfold lawE1
    by_cases hu : (mR == UTYPE) = true
    · simp only [hu, eq_self_iff_true, if_true, ↓reduceIte] at hv ⊢
      have hpos : 1 ≤ keyCnt (fun e => e.2.1) (es.map toR) t := by
        apply keyCnt_pos (fun e => e.2.1) (fun e => e.2.2.1)
        have := hcol0 t ht; unfold colSumR at this; rw [this]; unfold lawE0; rw [hu]; simp
      rw [hg] at hv
      by_cases ha : isABA (stsOf pR)[t]
      · rw [if_pos ha] at hv ⊢; unfold OFF at hv; omega
      · rw [if_neg ha] at hv ⊢; unfold OFF at hv; omega
    · have hu' : (mR == UTYPE) = false := by simpa using hu
      simp only [hu', Bool.false_eq_true, ↓reduceIte] at hv ⊢
      unfold OFF at hv; omega
  -- column facts for non-uniform columns
  have hcLf : (mL == UTYPE) = false → sumNat ((stsOf pL).map (cntOf mL pL)) = 108
      ∧ sumNat (((stsOf pL).map (cntOf mL pL)).map fun k => k * k) ≤ 972
      ∧ (∀ st ∈ stsOf pL, cntOf mL pL st ∣ lc) ∧ 0 < lc := by
    intro hu
    obtain ⟨-, hlcm, hsc, hsc2⟩ := hLnUf hu
    unfold colOK at hcL; rw [hLU, hu] at hcL
    simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcL
    refine ⟨by rw [← hsc]; exact hcL.1.1, by rw [← hsc2]; exact hcL.1.2,
      fun st hst => mem_dvd_foldl_lcm _ _ _ st hst, ?_⟩
    show 0 < (stsOf pL).foldl (fun l st => Nat.lcm l (cntOf mL pL st)) 1
    rw [← hlcm]; exact hcL.2
  have hcRf : (mR == UTYPE) = false → sumNat ((stsOf pR).map (cntOf mR pR)) = 108
      ∧ sumNat (((stsOf pR).map (cntOf mR pR)).map fun k => k * k) ≤ 972 := by
    intro hu
    obtain ⟨-, -, hsc, hsc2⟩ := hRnUf hu
    unfold colOK at hcR; rw [hRU, hu] at hcR
    simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcR
    exact ⟨by rw [← hsc]; exact hcR.1.1, by rw [← hsc2]; exact hcR.1.2⟩
  -- the left column is non-uniform
  have hLU0 : (mL == UTYPE) = false := by rw [← hLU]; exact hLUf0
  -- witnesses and the fourth-root bound
  have hwit : ∀ e ∈ es, e.2.2.2.2 < 10000000
      ∧ nonnegQ17 ((e.2.2.2.2 ^ 4 * cntOf mL pL ((stsOf pL).getD e.1 0) * XD : Nat)
          - (LD * E ^ 4 * e.2.2.1 : Nat) : Int) (-(972 * E ^ 4 : Nat) * e.2.2.2.1) = true := by
    intro e he
    obtain ⟨-, h1, -, -, -, hw⟩ := hmem e he
    rw [hLn'] at h1
    have hw' := hw rfl
    obtain ⟨hCV, -, -, -⟩ := hLnUf hLU0
    rw [hLU, hLU0] at hw'
    simp only [Bool.false_eq_true, ↓reduceIte] at hw'
    rw [hCV, cvDigit_eq mL pL e.1 h1] at hw'
    exact ⟨(hbnd e he).2.2.2.2.1, hw'⟩
  have hfields' := foldl_stepQ_fields true (mkCol mL pL) (mkCol mR pR) es ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, true⟩
  simp only [Nat.zero_add, Int.zero_add] at hfields'
  obtain ⟨-, -, -, -, -, -, -, -, hfnr, hfnr1⟩ := hfields'
  have hfin' : (let R0 : Int := 17 * sumR (fun e => e.2.2.1 * e.2.2.2) (es.map toR)
         let R1 : Int := 9 * sumInt (fun e => e.2.2.2.1 * e.2.2.2.2) es
         let S0 := R0 * R0 + 17 * R1 * R1
         let S1 := 2 * R0 * R1
         let T0 := S0 * S0 + 17 * S1 * S1
         let T1 := 2 * S0 * S1
         negQ17 (5 * T0 + 17 * T1 - 2 * ((XD * E : Nat) : Int) ^ 4) (T0 + 5 * T1) = true) := by
    unfold finalQ at hfin
    simp only [↓reduceIte] at hfin
    rw [hfnr, hfnr1] at hfin
    exact hfin
  exact ⟨hvL, hvR, h32, hLn27, hRn27, htL', htR', hnd, hent, hrow0, hrow1, hcol0, hcol1, hcLf, hcRf, hLU0, hwit, hfin'⟩


end Grid3.Three.Cert