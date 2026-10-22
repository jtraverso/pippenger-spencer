/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.PippengerSpencer.Basic

/-! # The colour hypergraph

For a hypergraph `H` on `V` and a number `C` of colours, the *colour hypergraph* lives on
`Finset V ⊕ (V × Fin C)`; its edges are `{e} ∪ {(v, c) : v ∈ e}` for `e ∈ H` and `c < C`.
A matching of the colour hypergraph is the same as a partial proper edge colouring of `H`
with `C` colours.
-/

@[expose] public section

namespace Pseudorandom.PS

open Finset

variable {V : Type*} [DecidableEq V] {C : ℕ}

/-- The edge `{e} ∪ {(v,c) : v ∈ e}` of the colour hypergraph. -/
def cedge (C : ℕ) (e : Finset V) (c : Fin C) : Finset (Finset V ⊕ (V × Fin C)) :=
  insert (Sum.inl e) (e.map ⟨fun v => Sum.inr (v, c), fun a b h => by simpa using h⟩)

theorem mem_cedge_inl {e e' : Finset V} {c : Fin C} :
    (Sum.inl e' : Finset V ⊕ (V × Fin C)) ∈ cedge C e c ↔ e' = e := by
  simp [cedge]

theorem mem_cedge_inr {e : Finset V} {c c' : Fin C} {v : V} :
    (Sum.inr (v, c') : Finset V ⊕ (V × Fin C)) ∈ cedge C e c ↔ v ∈ e ∧ c' = c := by
  simp only [cedge, mem_insert, reduceCtorEq, false_or, mem_map]
  constructor
  · rintro ⟨u, hu, h⟩
    have h' : Sum.inr (u, c) = (Sum.inr (v, c') : Finset V ⊕ (V × Fin C)) := h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨hu, rfl⟩
  · rintro ⟨hv, rfl⟩; exact ⟨v, hv, rfl⟩

theorem card_cedge (e : Finset V) (c : Fin C) : (cedge C e c).card = e.card + 1 := by
  unfold cedge
  rw [card_insert_of_notMem (by simp), card_map]

theorem cedge_inj {e e' : Finset V} {c c' : Fin C} (he : e.Nonempty)
    (h : cedge C e c = cedge C e' c') : e = e' ∧ c = c' := by
  have h1 : e = e' := by
    have : (Sum.inl e : Finset V ⊕ (V × Fin C)) ∈ cedge C e' c' := by
      rw [← h]; exact mem_cedge_inl.mpr rfl
    exact mem_cedge_inl.mp this
  subst h1
  obtain ⟨v, hv⟩ := he
  have : (Sum.inr (v, c) : Finset V ⊕ (V × Fin C)) ∈ cedge C e c' := by
    rw [← h]; exact mem_cedge_inr.mpr ⟨hv, rfl⟩
  exact ⟨rfl, (mem_cedge_inr.mp this).2⟩

/-- The colour hypergraph. -/
def colourHyp (H : Finset (Finset V)) (C : ℕ) : Finset (Finset (Finset V ⊕ (V × Fin C))) :=
  (H ×ˢ (univ : Finset (Fin C))).image (fun p => cedge C p.1 p.2)

theorem colourHyp_uniform {H : Finset (Finset V)} {r : ℕ} (huni : IsUniform H r) :
    IsUniform (colourHyp H C) (r + 1) := by
  intro x hx
  simp only [colourHyp, mem_image, mem_product] at hx
  obtain ⟨⟨e, c⟩, ⟨he, -⟩, rfl⟩ := hx
  rw [card_cedge, huni e he]

theorem card_colourHyp_le (H : Finset (Finset V)) : (colourHyp H C).card ≤ H.card * C := by
  unfold colourHyp
  refine card_image_le.trans ?_
  simp

/-- Degrees and codegrees of the colour hypergraph are bounded by counting the pairs `(e,c)`. -/
theorem card_filter_colourHyp_le (H : Finset (Finset V)) (q : Finset (Finset V ⊕ (V × Fin C)) → Prop)
    [DecidablePred q] :
    ((colourHyp H C).filter q).card ≤
      ((H ×ˢ (univ : Finset (Fin C))).filter (fun p => q (cedge C p.1 p.2))).card := by
  unfold colourHyp
  rw [filter_image]
  exact card_image_le

theorem degree_colourHyp_inl (H : Finset (Finset V)) (e : Finset V) :
    degree (colourHyp H C) (Sum.inl e) ≤ C := by
  unfold degree
  refine (card_filter_colourHyp_le H _).trans ?_
  calc _ ≤ (({e} : Finset (Finset V)) ×ˢ (univ : Finset (Fin C))).card := by
        apply card_le_card
        intro p hp
        simp only [mem_filter, mem_product] at hp
        have := mem_cedge_inl.mp hp.2
        exact mem_product.mpr ⟨mem_singleton.mpr this.symm, mem_univ _⟩
    _ = C := by simp

theorem degree_colourHyp_inr (H : Finset (Finset V)) (v : V) (c : Fin C) :
    degree (colourHyp H C) (Sum.inr (v, c)) ≤ degree H v := by
  unfold degree
  refine (card_filter_colourHyp_le H _).trans ?_
  calc _ ≤ ((H.filter (fun e => v ∈ e)) ×ˢ ({c} : Finset (Fin C))).card := by
        apply card_le_card
        intro p hp
        simp only [mem_filter, mem_product] at hp
        have := mem_cedge_inr.mp hp.2
        exact mem_product.mpr ⟨mem_filter.mpr ⟨hp.1.1, this.1⟩, mem_singleton.mpr this.2.symm⟩
    _ = _ := by simp

theorem codegree_colourHyp_le (H : Finset (Finset V)) (y z : Finset V ⊕ (V × Fin C))
    (hyz : y ≠ z) :
    codegree (colourHyp H C) y z ≤ 1 ∨
      ∃ u v, u ≠ v ∧ codegree (colourHyp H C) y z ≤ codegree H u v := by
  unfold codegree
  have key := card_filter_colourHyp_le (C := C) H (fun x => y ∈ x ∧ z ∈ x)
  rcases y with e | ⟨u, c⟩ <;> rcases z with e' | ⟨v, c'⟩
  · left
    refine key.trans (le_of_eq_of_le ?_ zero_le_one)
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro p - ⟨h1, h2⟩
    exact hyz (by rw [mem_cedge_inl.mp h1, mem_cedge_inl.mp h2])
  · left
    refine key.trans ((card_le_card (s := _) (t := {(e, c')}) ?_).trans (by simp))
    intro p hp
    simp only [mem_filter] at hp
    have h1 := mem_cedge_inl.mp hp.2.1
    have h2 := mem_cedge_inr.mp hp.2.2
    exact mem_singleton.mpr (Prod.ext h1.symm h2.2.symm)
  · left
    refine key.trans ((card_le_card (s := _) (t := {(e', c)}) ?_).trans (by simp))
    intro p hp
    simp only [mem_filter] at hp
    have h1 := mem_cedge_inl.mp hp.2.2
    have h2 := mem_cedge_inr.mp hp.2.1
    exact mem_singleton.mpr (Prod.ext h1.symm h2.2.symm)
  · by_cases huv : u = v
    · subst huv
      left
      refine key.trans (le_of_eq_of_le ?_ zero_le_one)
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro p - ⟨h1, h2⟩
      have := (mem_cedge_inr.mp h1).2
      have := (mem_cedge_inr.mp h2).2
      exact hyz (by subst_vars; rfl)
    · right
      refine ⟨u, v, huv, key.trans ?_⟩
      calc _ ≤ ((H.filter (fun e => u ∈ e ∧ v ∈ e)) ×ˢ ({c} : Finset (Fin C))).card := by
            apply card_le_card
            intro p hp
            simp only [mem_filter, mem_product] at hp
            have h1 := mem_cedge_inr.mp hp.2.1
            have h2 := mem_cedge_inr.mp hp.2.2
            exact mem_product.mpr ⟨mem_filter.mpr ⟨hp.1.1, h1.1, h2.1⟩,
              mem_singleton.mpr h1.2.symm⟩
        _ = _ := by simp

/-! ## Matchings of the colour hypergraph are partial colourings -/

/-- The weight function counting the colour-vertices `(v, ·)` of an edge. -/
def wv (v : V) (x : Finset (Finset V ⊕ (V × Fin C))) : ℝ :=
  ((x.filter (fun y => ∃ c, y = Sum.inr (v, c))).card : ℝ)

theorem wv_nonneg (v : V) (x : Finset (Finset V ⊕ (V × Fin C))) : 0 ≤ wv v x :=
  Nat.cast_nonneg _

theorem wv_cedge (v : V) (e : Finset V) (c : Fin C) :
    wv v (cedge C e c) = if v ∈ e then 1 else 0 := by
  unfold wv
  have : (cedge C e c).filter (fun y => ∃ c', y = Sum.inr (v, c')) =
      if v ∈ e then {Sum.inr (v, c)} else ∅ := by
    ext y
    rcases y with e' | ⟨u, c'⟩
    · simp only [mem_filter, reduceCtorEq, exists_false, and_false, false_iff]
      split_ifs <;> simp
    · simp only [mem_filter, mem_cedge_inr, Sum.inr.injEq, Prod.mk.injEq, exists_and_left,
        exists_eq', and_true]
      split_ifs with hv
      · simp only [mem_singleton, Sum.inr.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨-, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
        · rintro ⟨rfl, rfl⟩; exact ⟨⟨hv, rfl⟩, rfl⟩
      · simp only [notMem_empty, iff_false, not_and]
        rintro ⟨hu, -⟩ rfl
        exact hv hu
  rw [this]
  split_ifs <;> simp

theorem wv_le_one {H : Finset (Finset V)} {x : Finset (Finset V ⊕ (V × Fin C))}
    (hx : x ∈ colourHyp H C) (v : V) : wv v x ≤ 1 := by
  simp only [colourHyp, mem_image] at hx
  obtain ⟨p, -, rfl⟩ := hx
  rw [wv_cedge]; split_ifs <;> norm_num

theorem weight_image {H : Finset (Finset V)} (hne : ∀ e ∈ H, e.Nonempty)
    (S : Finset (Finset V × Fin C)) (hS : S ⊆ H ×ˢ univ) (v : V) :
    weight (wv v) (S.image (fun p => cedge C p.1 p.2)) =
      ((S.filter (fun p => v ∈ p.1)).card : ℝ) := by
  unfold weight
  rw [sum_image]
  · simp_rw [wv_cedge]
    rw [sum_boole]
  · intro p hp q _ hpq
    have hpH : p.1 ∈ H := (mem_product.mp (hS hp)).1
    obtain ⟨h1, h2⟩ := cedge_inj (hne _ hpH) hpq
    exact Prod.ext h1 h2

theorem weight_colourHyp {H : Finset (Finset V)} (hne : ∀ e ∈ H, e.Nonempty) (v : V) :
    weight (wv v) (colourHyp H C) = (degree H v : ℝ) * C := by
  unfold colourHyp
  rw [weight_image hne _ (subset_refl _)]
  have : (H ×ˢ (univ : Finset (Fin C))).filter (fun p => v ∈ p.1) =
      (H.filter (fun e => v ∈ e)) ×ˢ univ := by
    ext p; simp [and_assoc]
  rw [this, card_product, card_univ, Fintype.card_fin]
  unfold degree
  push_cast; ring

/-- The edges of `H` coloured by a matching `M` of the colour hypergraph. -/
def col (H : Finset (Finset V)) (M : Finset (Finset (Finset V ⊕ (V × Fin C)))) :
    Finset (Finset V) :=
  H.filter (fun e => ∃ c, cedge C e c ∈ M)

theorem col_subset (H : Finset (Finset V)) (M : Finset (Finset (Finset V ⊕ (V × Fin C)))) :
    col H M ⊆ H := filter_subset _ _

theorem weight_matching {H : Finset (Finset V)} (hne : ∀ e ∈ H, e.Nonempty)
    {M : Finset (Finset (Finset V ⊕ (V × Fin C)))} (hMH : M ⊆ colourHyp H C)
    (hM : IsMatching M) (v : V) :
    weight (wv v) M = (((col H M).filter (fun e => v ∈ e)).card : ℝ) := by
  set S := (H ×ˢ (univ : Finset (Fin C))).filter (fun p => cedge C p.1 p.2 ∈ M) with hSdef
  have hMS : M = S.image (fun p => cedge C p.1 p.2) := by
    ext x
    constructor
    · intro hx
      have := hMH hx
      simp only [colourHyp, mem_image] at this
      obtain ⟨p, hp, rfl⟩ := this
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hx⟩, rfl⟩
    · intro hx
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hp).2
  have hw := weight_image (C := C) hne S (filter_subset _ _) v
  rw [← hMS] at hw
  rw [hw]
  congr 1
  have himg : (S.filter (fun p => v ∈ p.1)).image Prod.fst = (col H M).filter (fun e => v ∈ e) := by
    ext e
    simp only [mem_image, mem_filter, hSdef, mem_product, mem_univ, and_true, col]
    constructor
    · rintro ⟨p, ⟨⟨hp1, hp2⟩, hv⟩, rfl⟩
      exact ⟨⟨hp1, p.2, hp2⟩, hv⟩
    · rintro ⟨⟨he, c, hc⟩, hv⟩
      exact ⟨(e, c), ⟨⟨he, hc⟩, hv⟩, rfl⟩
  rw [← himg, card_image_of_injOn]
  intro p hp q hq hpq
  simp only [coe_filter, Set.mem_ofPred_eq, hSdef, mem_filter, mem_product] at hp hq
  have hpq' : p.1 = q.1 := hpq
  by_contra hne'
  have hc : p.2 ≠ q.2 := fun h => hne' (Prod.ext hpq' h)
  have hdiff : cedge C p.1 p.2 ≠ cedge C q.1 q.2 := by
    intro h
    exact hc (cedge_inj (hne _ hp.1.1.1) h).2
  have hd := hM _ hp.1.2 _ hq.1.2 hdiff
  have h1 : (Sum.inl p.1 : Finset V ⊕ (V × Fin C)) ∈ cedge C p.1 p.2 := mem_cedge_inl.mpr rfl
  have h2 : (Sum.inl p.1 : Finset V ⊕ (V × Fin C)) ∈ cedge C q.1 q.2 :=
    mem_cedge_inl.mpr hpq'
  exact Finset.disjoint_left.mp hd h1 h2

/-- The leftover degree: `deg_{H \ col}(v) = deg_H(v) - #(coloured edges at v)`. -/
theorem degree_sdiff_col (H : Finset (Finset V)) (M : Finset (Finset (Finset V ⊕ (V × Fin C))))
    (v : V) :
    degree (H \ col H M) v + ((col H M).filter (fun e => v ∈ e)).card = degree H v := by
  unfold degree
  have : (H \ col H M).filter (fun e => v ∈ e) =
      H.filter (fun e => v ∈ e) \ (col H M).filter (fun e => v ∈ e) := by
    ext e; simp only [mem_filter, mem_sdiff]; tauto
  rw [this, card_sdiff_add_card_eq_card]
  exact filter_subset_filter _ (col_subset H M)

open Classical in
/-- The colouring of the coloured edges given by a matching of the colour hypergraph. -/
noncomputable def colOf (M : Finset (Finset (Finset V ⊕ (V × Fin C)))) (hC : 0 < C) :
    Finset V → Fin C :=
  fun e => if h : ∃ c, cedge C e c ∈ M then h.choose else ⟨0, hC⟩

theorem colOf_proper (H : Finset (Finset V)) {M : Finset (Finset (Finset V ⊕ (V × Fin C)))}
    (hM : IsMatching M) (hC : 0 < C) : IsProperEdgeColouring (col H M) C (colOf M hC) := by
  intro e he f hf hef hcol
  have he' := (mem_filter.mp he).2
  have hf' := (mem_filter.mp hf).2
  have hce : cedge C e (colOf M hC e) ∈ M := by
    have := he'.choose_spec; simpa [colOf, he'] using this
  have hcf : cedge C f (colOf M hC e) ∈ M := by
    rw [hcol]; have := hf'.choose_spec; simpa [colOf, hf'] using this
  have hdiff : cedge C e (colOf M hC e) ≠ cedge C f (colOf M hC e) := by
    intro h
    have : (Sum.inl e : Finset V ⊕ (V × Fin C)) ∈ cedge C f (colOf M hC e) := by
      rw [← h]; exact mem_cedge_inl.mpr rfl
    exact hef (mem_cedge_inl.mp this)
  have hd := hM _ hce _ hcf hdiff
  rw [Finset.disjoint_left]
  intro v hve hvf
  exact Finset.disjoint_left.mp hd (mem_cedge_inr.mpr ⟨hve, rfl⟩) (mem_cedge_inr.mpr ⟨hvf, rfl⟩)

end Pseudorandom.PS
