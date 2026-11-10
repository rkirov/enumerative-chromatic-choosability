/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Outerplanar.GraphDefs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Order.Fin.Basic

/-!
# Polygon dissections are built by pendant vertices and ears on edges

This file connects the abstract class `EarBuilt` of `Outerplanar/GraphDefs.lean` to outerplanar
graphs with a Hamiltonian cycle. A *polygon dissection* (`IsDissection`) is a graph on `Fin n`
that contains the cycle `0, 1, …, n - 1` and has no two crossing edges; for `n ≥ 3` these are the
2-connected outerplanar graphs, drawn with the Hamiltonian cycle as the outer face.

* `earBuilt_of_isDissection`: every polygon dissection is `EarBuilt` with ears of at least one
  vertex.
* `earBuilt_two_of_isDissection`: a triangle-free polygon dissection is `EarBuilt` with ears of
  at least two vertices.

Both follow from `earBuilt_of_gapClosed`, proved by strong induction on a vertex set `S` that is
*gap-closed* (`GapClosed`): consecutive elements of `S` are adjacent, and so are its two extreme
elements. If some chord of `S` has an element of `S` strictly inside it, a chord with the fewest
such elements cuts off an ear; otherwise the largest element of `S` is a pendant vertex.

The general outerplanar case (graphs that are not 2-connected, whose blocks are polygon
dissections or single edges glued at cut vertices) is not formalised here.
-/

namespace Outerplanar

open Finset

/-- A *polygon dissection*: a graph on `Fin n` containing the Hamiltonian cycle
`0, 1, …, n - 1` and whose edges do not cross. These are the outerplanar graphs with a
Hamiltonian cycle, i.e. (for `n ≥ 3`) the 2-connected outerplanar graphs. -/
def IsDissection {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (∀ i j : Fin n, i.val + 1 = j.val → G.Adj i j) ∧
  (∀ i j : Fin n, i.val = 0 → j.val + 1 = n → i ≠ j → G.Adj i j) ∧
  ∀ a b c d : Fin n, a < b → b < c → c < d → G.Adj a c → ¬ G.Adj b d

/-- A vertex set is *gap-closed* if any two of its elements with no element of the set strictly
between them are adjacent, and its least and greatest elements (if distinct) are adjacent. -/
def GapClosed {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬ (a < x ∧ x < b)) → G.Adj a b) ∧
  (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, a ≤ x ∧ x ≤ b) → G.Adj a b)

/-- A finite set of a linear order is enumerated increasingly by `Fin` of its cardinality. -/
theorem exists_increasing_enum {n : ℕ} (T : Finset (Fin n)) :
    ∃ x : Fin T.card → Fin n, Function.Injective x ∧ (∀ j, x j ∈ T) ∧
      (∀ i j, x i < x j ↔ i < j) ∧ ∀ t ∈ T, ∃ j, x j = t := by
  refine ⟨fun j => T.orderEmbOfFin rfl j, (T.orderEmbOfFin rfl).injective,
    fun j => Finset.orderEmbOfFin_mem T rfl j, fun i j => (T.orderEmbOfFin rfl).lt_iff_lt,
    fun t ht => ?_⟩
  have h : t ∈ Set.range (T.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin T rfl]; exact ht
  exact h

/-- A gap-closed vertex set of a graph without crossing edges is built by pendant vertices and
ears on edges; without triangles the ears have at least two vertices. -/
theorem earBuilt_of_gapClosed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (m₀ : ℕ)
    (hcross : ∀ a b c d : Fin n, a < b → b < c → c < d → G.Adj a c → ¬ G.Adj b d)
    (hm₀ : m₀ ≤ 1 ∨ (m₀ ≤ 2 ∧ ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj a c))
    (S : Finset (Fin n)) (hS : GapClosed G S) : EarBuilt G m₀ S := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
  obtain ⟨hgap, hend⟩ := hS
  by_cases hc : ∃ a ∈ S, ∃ b ∈ S, a < b ∧ G.Adj a b ∧ ∃ x ∈ S, a < x ∧ x < b
  · -- an ear: take a chord with the fewest elements of `S` strictly inside
    obtain ⟨a₀, ha₀, b₀, hb₀, hab₀, hadj₀, hx₀⟩ := hc
    obtain ⟨⟨a, b⟩, hp, hmin'⟩ := Finset.exists_min_image
      ((S ×ˢ S).filter fun p => p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ ∃ x ∈ S, p.1 < x ∧ x < p.2)
      (fun p => (S.filter fun x => p.1 < x ∧ x < p.2).card)
      ⟨(a₀, b₀), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha₀, hb₀⟩, hab₀, hadj₀, hx₀⟩⟩
    obtain ⟨hab', hab, hadj, x₀, hx₀, hx₀'⟩ := Finset.mem_filter.1 hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hab'
    simp only at ha hb hab hadj hx₀' hmin'
    -- minimality: a shorter chord inside `[a, b]` has nothing strictly inside
    have hmin : ∀ a' ∈ S, ∀ b' ∈ S, a ≤ a' → b' ≤ b → a' < b' → (a < a' ∨ b' < b) →
        G.Adj a' b' → ∀ x ∈ S, ¬ (a' < x ∧ x < b') := by
      intro a' ha' b' hb' h1 h2 h3 h4 h5 x hx hx'
      have hle := hmin' (a', b')
        (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha', hb'⟩, h3, h5, x, hx, hx'⟩)
      have hsub : (S.filter fun x => a' < x ∧ x < b') ⊆ S.filter fun x => a < x ∧ x < b := by
        intro y hy
        obtain ⟨hy, hy1, hy2⟩ := Finset.mem_filter.1 hy
        exact Finset.mem_filter.2 ⟨hy, lt_of_le_of_lt h1 hy1, lt_of_lt_of_le hy2 h2⟩
      refine absurd (Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ?_)) (not_lt.2 hle)
      rcases h4 with h4 | h4
      · exact ⟨a', Finset.mem_filter.2 ⟨ha', h4, lt_of_lt_of_le h3 h2⟩,
          fun h => lt_irrefl _ (Finset.mem_filter.1 h).2.1⟩
      · exact ⟨b', Finset.mem_filter.2 ⟨hb', lt_of_le_of_lt h1 h3, h4⟩,
          fun h => lt_irrefl _ (Finset.mem_filter.1 h).2.2⟩
    -- the ear `T` and the rest `S'`
    obtain ⟨T, hT⟩ : ∃ T : Finset (Fin n), ∀ t, t ∈ T ↔ t ∈ S ∧ a < t ∧ t < b :=
      ⟨S.filter fun t => a < t ∧ t < b, fun t => by simp⟩
    obtain ⟨S', hS'⟩ : ∃ S' : Finset (Fin n), ∀ y, y ∈ S' ↔ y ∈ S ∧ ¬ (a < y ∧ y < b) :=
      ⟨S.filter fun t => ¬ (a < t ∧ t < b), fun t => by simp⟩
    have haS' : a ∈ S' := (hS' a).2 ⟨ha, fun h => lt_irrefl _ h.1⟩
    have hbS' : b ∈ S' := (hS' b).2 ⟨hb, fun h => lt_irrefl _ h.2⟩
    have hss : S' ⊂ S := (Finset.ssubset_iff_of_subset (fun y hy => ((hS' y).1 hy).1)).2
      ⟨x₀, hx₀, fun h => ((hS' _).1 h).2 hx₀'⟩
    have hclosed : GapClosed G S' := by
      refine ⟨?_, ?_⟩
      · intro p hp q hq hpq hno
        obtain ⟨hpS, hp'⟩ := (hS' p).1 hp
        obtain ⟨hqS, hq'⟩ := (hS' q).1 hq
        by_cases hex : ∃ z ∈ S, p < z ∧ z < q
        · obtain ⟨z, hz, hpz, hzq⟩ := hex
          have hzT : a < z ∧ z < b := by
            by_contra h; exact hno z ((hS' z).2 ⟨hz, h⟩) ⟨hpz, hzq⟩
          have hpa : p ≤ a := by
            by_contra h; exact hp' ⟨not_le.1 h, hpz.trans hzT.2⟩
          have hbq : b ≤ q := by
            by_contra h; exact hq' ⟨hzT.1.trans hzq, not_le.1 h⟩
          have hpa' : p = a := by
            by_contra h; exact hno a haS' ⟨lt_of_le_of_ne hpa h, hzT.1.trans hzq⟩
          have hqb : q = b := by
            by_contra h; exact hno b hbS' ⟨hpz.trans hzT.2, lt_of_le_of_ne hbq (Ne.symm h)⟩
          rw [hpa', hqb]; exact hadj
        · exact hgap p hpS q hqS hpq fun z hz hz' => hex ⟨z, hz, hz'⟩
      · intro p hp q hq hpq hall
        refine hend p ((hS' p).1 hp).1 q ((hS' q).1 hq).1 hpq fun z hz => ?_
        by_cases h : a < z ∧ z < b
        · exact ⟨(hall a haS').1.trans h.1.le, h.2.le.trans (hall b hbS').2⟩
        · exact hall z ((hS' z).2 ⟨hz, h⟩)
    have hrec : EarBuilt G m₀ S' := ih S' hss hclosed
    -- enumerate the ear increasingly
    obtain ⟨m, x, hm, hinj, hxT, hxmono, hxsurj⟩ : ∃ m : ℕ, ∃ x : Fin m → Fin n, 1 ≤ m ∧
        Function.Injective x ∧ (∀ j, x j ∈ T) ∧ (∀ i j, x i < x j ↔ i < j) ∧
        ∀ t ∈ T, ∃ j, x j = t := by
      obtain ⟨x, hx⟩ := exists_increasing_enum T
      exact ⟨T.card, x, Finset.card_pos.2 ⟨x₀, (hT x₀).2 ⟨hx₀, hx₀'⟩⟩, hx⟩
    have hold : ∀ j : Fin m, ∀ y ∈ S',
        G.Adj (x j) y ↔ (j.val = 0 ∧ y = a) ∨ (j.val + 1 = m ∧ y = b) := by
      intro j y hy
      obtain ⟨hyS, hy'⟩ := (hS' y).1 hy
      obtain ⟨htS, hat, htb⟩ := (hT _).1 (hxT j)
      constructor
      · intro hadj'
        rcases lt_trichotomy y a with h1 | h1 | h1
        · exact absurd hadj (hcross y a (x j) b h1 hat htb hadj'.symm)
        · left
          refine ⟨?_, h1⟩
          by_contra h0
          have hlt : x ⟨0, by omega⟩ < x j := (hxmono _ _).2 (by rw [Fin.lt_def]; simp; omega)
          obtain ⟨h0S, h0a, -⟩ := (hT _).1 (hxT ⟨0, by omega⟩)
          rw [h1] at hadj'
          exact hmin a ha (x j) htS le_rfl htb.le hat (Or.inr htb) hadj'.symm _ h0S ⟨h0a, hlt⟩
        · rcases lt_trichotomy y b with h2 | h2 | h2
          · exact absurd ⟨h1, h2⟩ hy'
          · right
            refine ⟨?_, h2⟩
            by_contra h0
            have hlt : x j < x ⟨m - 1, by omega⟩ :=
              (hxmono _ _).2 (by rw [Fin.lt_def]; have := j.2; simp; omega)
            obtain ⟨h0S, -, h0b⟩ := (hT _).1 (hxT ⟨m - 1, by omega⟩)
            rw [h2] at hadj'
            exact hmin (x j) htS b hb hat.le le_rfl htb (Or.inl hat) hadj' _ h0S ⟨hlt, h0b⟩
          · exact absurd hadj' (hcross a (x j) b y hat htb h2 hadj)
      · rintro (⟨h0, hya⟩ | ⟨h0, hyb⟩)
        · rw [hya]
          refine (hgap a ha (x j) htS hat fun z hz hz' => ?_).symm
          obtain ⟨i, rfl⟩ := hxsurj z ((hT z).2 ⟨hz, hz'.1, hz'.2.trans htb⟩)
          have := (hxmono _ _).1 hz'.2
          rw [Fin.lt_def] at this
          omega
        · rw [hyb]
          refine hgap (x j) htS b hb htb fun z hz hz' => ?_
          obtain ⟨i, rfl⟩ := hxsurj z ((hT z).2 ⟨hz, hat.trans hz'.1, hz'.2⟩)
          have := (hxmono _ _).1 hz'.1
          have := i.2
          rw [Fin.lt_def] at *
          omega
    have hnew1 : ∀ j j' : Fin m, j < j' → (G.Adj (x j) (x j') ↔ j.val + 1 = j'.val) := by
      intro j j' hjj
      obtain ⟨htS, hat, htb⟩ := (hT _).1 (hxT j)
      obtain ⟨htS', hat', htb'⟩ := (hT _).1 (hxT j')
      have hlt := (hxmono j j').2 hjj
      rw [Fin.lt_def] at hjj
      constructor
      · intro hadj'
        by_contra hne
        have hj1 : j.val + 1 < m := by have := j'.2; omega
        obtain ⟨hmS, -, -⟩ := (hT _).1 (hxT ⟨j.val + 1, hj1⟩)
        exact hmin _ htS _ htS' hat.le htb'.le hlt (Or.inl hat) hadj' _ hmS
          ⟨(hxmono _ _).2 (by rw [Fin.lt_def]; simp),
            (hxmono _ _).2 (by rw [Fin.lt_def]; simp; omega)⟩
      · intro h1
        refine hgap _ htS _ htS' hlt fun z hz hz' => ?_
        obtain ⟨i, rfl⟩ := hxsurj z ((hT z).2 ⟨hz, hat.trans hz'.1, hz'.2.trans htb'⟩)
        have h2 := (hxmono _ _).1 hz'.1
        have h3 := (hxmono _ _).1 hz'.2
        rw [Fin.lt_def] at h2 h3
        omega
    have hnew : ∀ j j' : Fin m,
        G.Adj (x j) (x j') ↔ j.val + 1 = j'.val ∨ j'.val + 1 = j.val := by
      intro j j'
      rcases lt_trichotomy j j' with h | h | h
      · rw [hnew1 j j' h]; rw [Fin.lt_def] at h; omega
      · subst h; simp
      · rw [G.adj_comm, hnew1 j' j h]; rw [Fin.lt_def] at h; omega
    have hm₀' : m₀ ≤ m := by
      rcases hm₀ with h | ⟨h, htri⟩
      · omega
      · by_contra hlt
        have h1 := (hold ⟨0, hm⟩ a haS').2 (Or.inl ⟨rfl, rfl⟩)
        have h2 := (hold ⟨0, hm⟩ b hbS').2 (Or.inr ⟨by simp; omega, rfl⟩)
        exact htri a _ b h1.symm h2 hadj
    have hSeq : S = S' ∪ univ.image x := by
      ext y
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, hS']
      constructor
      · intro hy
        by_cases h : a < y ∧ y < b
        · exact Or.inr (hxsurj y ((hT y).2 ⟨hy, h⟩))
        · exact Or.inl ⟨hy, h⟩
      · rintro (h | ⟨j, rfl⟩)
        · exact h.1
        · exact ((hT _).1 (hxT j)).1
    rw [hSeq]
    exact EarBuilt.ear S' m hm hm₀' a b haS' hbS' hadj x hinj
      (fun j h => ((hS' _).1 h).2 ((hT _).1 (hxT j)).2) hrec hold hnew
  · -- no chord has anything inside: the largest element is a pendant vertex
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact EarBuilt.empty
    obtain ⟨z, hz, hle⟩ : ∃ z ∈ S, ∀ x ∈ S, x ≤ z :=
      ⟨S.max' hne, S.max'_mem hne, fun x hx => S.le_max' x hx⟩
    rw [← Finset.insert_erase hz]
    refine EarBuilt.pendant _ z (Finset.notMem_erase z S)
      (ih _ (Finset.erase_ssubset hz) ⟨?_, ?_⟩) ?_
    · intro a ha b hb hab hx
      have ha' := Finset.mem_of_mem_erase ha
      have hb' := Finset.mem_of_mem_erase hb
      refine hgap a ha' b hb' hab fun x hxS hx' => hx x (Finset.mem_erase.2 ⟨?_, hxS⟩) hx'
      intro h
      rw [h] at hx'
      exact absurd (hle b hb') (not_le.2 hx'.2)
    · intro a ha b hb hab hall
      have ha' := Finset.mem_of_mem_erase ha
      have hb' := Finset.mem_of_mem_erase hb
      have hbz : b < z := lt_of_le_of_ne (hle b hb') (Finset.ne_of_mem_erase hb)
      refine absurd ⟨a, ha', z, hz, hab.trans hbz, hend a ha' z hz (hab.trans hbz) fun x hx => ?_,
        b, hb', hab, hbz⟩ hc
      by_cases hxz : x = z
      · rw [hxz]; exact ⟨(hab.trans hbz).le, le_rfl⟩
      · exact ⟨(hall x (Finset.mem_erase.2 ⟨hxz, hx⟩)).1, hle x hx⟩
    · have key : ∀ y ∈ S, ∀ y' ∈ S, y < y' → y' < z → G.Adj z y → False :=
        fun y hy y' hy' h1 h2 h3 => hc ⟨y, hy, z, hz, h1.trans h2, h3.symm, y', hy', h1, h2⟩
      refine Finset.card_le_one.2 fun y hy y' hy' => ?_
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
      obtain ⟨hy1', hy2'⟩ := Finset.mem_filter.1 hy'
      have hyz : y < z :=
        lt_of_le_of_ne (hle y (Finset.mem_of_mem_erase hy1)) (Finset.ne_of_mem_erase hy1)
      have hyz' : y' < z :=
        lt_of_le_of_ne (hle y' (Finset.mem_of_mem_erase hy1')) (Finset.ne_of_mem_erase hy1')
      rcases lt_trichotomy y y' with h | h | h
      · exact (key y (Finset.mem_of_mem_erase hy1) y' (Finset.mem_of_mem_erase hy1') h hyz'
          hy2).elim
      · exact h
      · exact (key y' (Finset.mem_of_mem_erase hy1') y (Finset.mem_of_mem_erase hy1) h hyz
          hy2').elim

/-- The whole vertex set of a polygon dissection is gap-closed. -/
theorem gapClosed_univ_of_isDissection {n : ℕ} (G : SimpleGraph (Fin n))
    (h : IsDissection G) : GapClosed G univ := by
  refine ⟨?_, ?_⟩
  · intro a _ b _ hab hno
    refine h.1 a b ?_
    by_contra hne
    rw [Fin.lt_def] at hab
    have hb := b.2
    exact hno ⟨a.val + 1, by omega⟩ (Finset.mem_univ _)
      ⟨by rw [Fin.lt_def]; simp, by rw [Fin.lt_def]; simp; omega⟩
  · intro a _ b _ hab hall
    have hb := b.2
    have h0 := (hall ⟨0, by omega⟩ (Finset.mem_univ _)).1
    have h1 := (hall ⟨n - 1, by omega⟩ (Finset.mem_univ _)).2
    rw [Fin.le_def] at h0 h1
    simp only at h0 h1
    exact h.2.1 a b (by omega) (by omega) (ne_of_lt hab)

/-- Every polygon dissection is built by pendant vertices and ears on edges. -/
theorem earBuilt_of_isDissection {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : IsDissection G) : EarBuilt G 1 univ :=
  earBuilt_of_gapClosed G 1 h.2.2 (Or.inl le_rfl) univ (gapClosed_univ_of_isDissection G h)

/-- A triangle-free polygon dissection is built by ears of at least two vertices. -/
theorem earBuilt_two_of_isDissection {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : IsDissection G) (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj a c) :
    EarBuilt G 2 univ :=
  earBuilt_of_gapClosed G 2 h.2.2 (Or.inr ⟨le_rfl, htri⟩) univ
    (gapClosed_univ_of_isDissection G h)

end Outerplanar
