/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.PippengerSpencer.LocalNibble

/-! # Locality of the realised nibble

Balls in a hypergraph, and the fact that after `t` rounds of the realised nibble, the state
restricted to the edges meeting the ball of radius `k` around `v` only depends on the coins
of the edges meeting, and the vertices in, the ball of radius `k + 2t`.
-/

@[expose] public section

namespace Pseudorandom.PS

open Finset Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Balls -/

section Balls

variable (H : Finset (Finset V))

/-- The vertices at distance at most `k` from `v`. -/
def ball : ℕ → V → Finset V
  | 0, v => {v}
  | k + 1, v => ball k v ∪ (H.filter (fun e => ¬ Disjoint e (ball k v))).biUnion id

/-- The edges meeting the ball of radius `k` around `v`. -/
def eball (k : ℕ) (v : V) : Finset (Finset V) := H.filter (fun e => ¬ Disjoint e (ball H k v))

variable {H}

theorem mem_ball_zero {v w : V} : w ∈ ball H 0 v ↔ w = v := by simp [ball]

theorem mem_ball_succ {k : ℕ} {v w : V} :
    w ∈ ball H (k + 1) v ↔ w ∈ ball H k v ∨ ∃ e ∈ H, ¬ Disjoint e (ball H k v) ∧ w ∈ e := by
  simp only [ball, mem_union, mem_biUnion, mem_filter, id]
  constructor
  · rintro (h | ⟨e, ⟨he, hd⟩, hw⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, he, hd, hw⟩
  · rintro (h | ⟨e, he, hd, hw⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, ⟨he, hd⟩, hw⟩

theorem mem_eball {k : ℕ} {v : V} {e : Finset V} :
    e ∈ eball H k v ↔ e ∈ H ∧ ∃ u ∈ e, u ∈ ball H k v := by
  simp only [eball, mem_filter, Finset.not_disjoint_iff]

theorem self_mem_ball (k : ℕ) (v : V) : v ∈ ball H k v := by
  induction k with
  | zero => exact mem_ball_zero.mpr rfl
  | succ k ih => exact mem_ball_succ.mpr (Or.inl ih)

theorem ball_subset_succ (k : ℕ) (v : V) : ball H k v ⊆ ball H (k + 1) v :=
  fun _ h => mem_ball_succ.mpr (Or.inl h)

theorem ball_mono {k m : ℕ} (h : k ≤ m) (v : V) : ball H k v ⊆ ball H m v := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
    rcases Nat.lt_or_ge m k with h' | h'
    · rw [show k = m + 1 by omega]
    · exact (ih h').trans (ball_subset_succ m v)

theorem eball_mono {k m : ℕ} (h : k ≤ m) (v : V) : eball H k v ⊆ eball H m v := by
  intro e he
  obtain ⟨heH, u, hu, hub⟩ := mem_eball.mp he
  exact mem_eball.mpr ⟨heH, u, hu, ball_mono h v hub⟩

theorem mem_eball_of {k : ℕ} {v u : V} {e : Finset V} (he : e ∈ H) (hu : u ∈ e)
    (hub : u ∈ ball H k v) : e ∈ eball H k v := mem_eball.mpr ⟨he, u, hu, hub⟩

theorem subset_ball_of_mem_eball {k : ℕ} {v : V} {e : Finset V} (he : e ∈ eball H k v) :
    e ⊆ ball H (k + 1) v := by
  intro w hw
  rw [eball, mem_filter] at he
  exact mem_ball_succ.mpr (Or.inr ⟨e, he.1, he.2, hw⟩)

theorem mem_eball_succ_of_meet {k : ℕ} {v : V} {e f : Finset V} (he : e ∈ eball H k v)
    (hf : f ∈ H) (hfe : ¬ Disjoint f e) : f ∈ eball H (k + 1) v := by
  obtain ⟨u, huf, hue⟩ := Finset.not_disjoint_iff.mp hfe
  exact mem_eball_of hf huf (subset_ball_of_mem_eball he hue)

/-- Adjacent vertices are in each other's ball of radius one. -/
theorem mem_ball_one_of_adj {u w : V} {e : Finset V} (he : e ∈ H) (hu : u ∈ e) (hw : w ∈ e) :
    w ∈ ball H 1 u :=
  mem_ball_succ.mpr (Or.inr ⟨e, he, Finset.not_disjoint_iff.mpr ⟨u, hu, mem_ball_zero.mpr rfl⟩,
    hw⟩)

/-- The triangle inequality for balls. -/
theorem ball_trans {a b : ℕ} {v u w : V} (hu : u ∈ ball H a v) (hw : w ∈ ball H b u) :
    w ∈ ball H (a + b) v := by
  induction b generalizing w with
  | zero => rw [mem_ball_zero.mp hw]; exact hu
  | succ b ih =>
    rcases mem_ball_succ.mp hw with h | ⟨e, he, hd, hwe⟩
    · exact ball_subset_succ _ _ (ih h)
    · obtain ⟨u', hu'e, hu'b⟩ := Finset.not_disjoint_iff.mp hd
      exact mem_ball_succ.mpr (Or.inr ⟨e, he,
        Finset.not_disjoint_iff.mpr ⟨u', hu'e, ih hu'b⟩, hwe⟩)

/-- Symmetry of balls. -/
theorem ball_symm {k : ℕ} {v w : V} (h : w ∈ ball H k v) : v ∈ ball H k w := by
  induction k generalizing w with
  | zero => rw [mem_ball_zero.mp h]; exact mem_ball_zero.mpr rfl
  | succ k ih =>
    rcases mem_ball_succ.mp h with h' | ⟨e, he, hd, hwe⟩
    · exact ball_subset_succ _ _ (ih h')
    · obtain ⟨u, hue, hub⟩ := Finset.not_disjoint_iff.mp hd
      have h1 : u ∈ ball H 1 w := mem_ball_one_of_adj he hwe hue
      have := ball_trans h1 (ih hub)
      rwa [add_comm] at this

/-- The size of balls. -/
theorem card_ball_le {r Δ : ℕ} (huni : IsUniform H r) (hdeg : ∀ u, degree H u ≤ Δ) :
    ∀ (k : ℕ) (v : V), (ball H k v).card ≤ (1 + r * Δ) ^ k := by
  intro k v
  induction k with
  | zero => simp [ball]
  | succ k ih =>
    have h1 : (eball H k v).card ≤ ∑ u ∈ ball H k v, degree H u := by
      have hsub : eball H k v ⊆ (ball H k v).biUnion (fun u => H.filter (fun e => u ∈ e)) := by
        intro e he
        obtain ⟨heH, u, hue, hub⟩ := mem_eball.mp he
        exact mem_biUnion.mpr ⟨u, hub, mem_filter.mpr ⟨heH, hue⟩⟩
      exact (card_le_card hsub).trans card_biUnion_le
    have h2 : ∑ u ∈ ball H k v, degree H u ≤ (ball H k v).card * Δ := by
      rw [← smul_eq_mul, ← sum_const]; exact sum_le_sum fun u _ => hdeg u
    have h3 : ((eball H k v).biUnion id).card ≤ (eball H k v).card * r := by
      refine card_biUnion_le.trans ?_
      rw [← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun e he => le_of_eq (huni e (mem_filter.mp he).1)
    have h4 : (ball H (k + 1) v).card ≤ (ball H k v).card + ((eball H k v).biUnion id).card :=
      card_union_le _ _
    calc (ball H (k + 1) v).card ≤ (ball H k v).card + (ball H k v).card * Δ * r := by
          have := Nat.mul_le_mul_right r (h1.trans h2); omega
      _ = (ball H k v).card * (1 + r * Δ) := by ring
      _ ≤ (1 + r * Δ) ^ k * (1 + r * Δ) := Nat.mul_le_mul_right _ ih
      _ = (1 + r * Δ) ^ (k + 1) := by ring

end Balls

/-! ## One round is local -/

/-- Two states agree on a set of edges. -/
def AgreeOn (E : Finset (Finset V)) (S S' : State V) : Prop :=
  ∀ e ∈ E, (e ∈ S.1 ↔ e ∈ S'.1) ∧ (e ∈ S.2 ↔ e ∈ S'.2)

theorem AgreeOn.mono {E F : Finset (Finset V)} {S S' : State V} (h : AgreeOn F S S')
    (hEF : E ⊆ F) : AgreeOn E S S' := fun e he => h e (hEF he)

theorem nextT_local {H : Finset (Finset V)} (N : ℕ) (D' : ℝ) {S S' : State V} (hS : S.1 ⊆ H)
    (hS' : S'.1 ⊆ H) (k : ℕ) (v : V) {y y' : Coin V → Fin (N + 2)}
    (hag : AgreeOn (eball H (k + 2) v) S S')
    (hy : ∀ e ∈ eball H (k + 2) v, y (Sum.inl e) = y' (Sum.inl e))
    (hy' : ∀ u ∈ ball H (k + 2) v, y (Sum.inr u) = y' (Sum.inr u)) :
    AgreeOn (eball H k v) (nextT D' S (fun c => decode N S.1 c (y c)))
      (nextT D' S' (fun c => decode N S'.1 c (y' c))) := by
  set A := S.1
  set A' := S'.1
  set ω : Coin V → Bool := fun c => decode N A c (y c) with hω
  set ω' : Coin V → Bool := fun c => decode N A' c (y' c) with hω'
  -- (i) membership and edge coins agree on `eball (k+2)`
  have hmem : ∀ f ∈ eball H (k + 2) v, (f ∈ A ↔ f ∈ A') := fun f hf => (hag f hf).1
  have hcoinE : ∀ f ∈ eball H (k + 2) v, ω (Sum.inl f) = ω' (Sum.inl f) := by
    intro f hf
    simp only [hω, hω', decode, hy f hf, hmem f hf]
  -- (ii) degrees and vertex coins agree on `ball (k+2)`
  have hdeg : ∀ u ∈ ball H (k + 2) v, degree A u = degree A' u := by
    intro u hu
    unfold degree
    congr 1
    ext f
    simp only [mem_filter]
    constructor
    · rintro ⟨hfA, huf⟩
      exact ⟨(hmem f (mem_eball_of (hS hfA) huf hu)).mp hfA, huf⟩
    · rintro ⟨hfA, huf⟩
      exact ⟨(hmem f (mem_eball_of (hS' hfA) huf hu)).mpr hfA, huf⟩
  have hcoinV : ∀ u ∈ ball H (k + 2) v, ω (Sum.inr u) = ω' (Sum.inr u) := by
    intro u hu
    simp only [hω, hω', decode, hy' u hu, hdeg u hu]
  -- (iii) deaths agree on `ball (k+2)`
  have hdead : ∀ u ∈ ball H (k + 2) v, (Dead A ω u ↔ Dead A' ω' u) := by
    intro u hu
    unfold Dead
    rw [hcoinV u hu]
    apply or_congr_left
    constructor
    · rintro ⟨f, hfA, huf, hf⟩
      have hfe := mem_eball_of (hS hfA) huf hu
      exact ⟨f, (hmem f hfe).mp hfA, huf, (hcoinE f hfe) ▸ hf⟩
    · rintro ⟨f, hfA, huf, hf⟩
      have hfe := mem_eball_of (hS' hfA) huf hu
      exact ⟨f, (hmem f hfe).mpr hfA, huf, (hcoinE f hfe).symm ▸ hf⟩
  -- (iv) survival agrees on `eball (k+1)`
  have halive : ∀ e ∈ eball H (k + 1) v, (e ∈ alive A ω ↔ e ∈ alive A' ω') := by
    intro e he
    have he2 := eball_mono (by omega : k + 1 ≤ k + 2) v he
    have hsub := subset_ball_of_mem_eball he
    simp only [alive, mem_filter]
    rw [hmem e he2]
    apply and_congr_right
    intro _
    exact forall₂_congr fun u hu => not_congr (hdead u (hsub hu))
  -- (v) degrees of the alive hypergraphs agree on `ball (k+1)`
  have hdegA : ∀ u ∈ ball H (k + 1) v, degree (alive A ω) u = degree (alive A' ω') u := by
    intro u hu
    unfold degree
    congr 1
    ext f
    simp only [mem_filter]
    constructor
    · rintro ⟨hf, huf⟩
      have hfH : f ∈ H := hS (alive_subset _ _ hf)
      exact ⟨(halive f (mem_eball_of hfH huf hu)).mp hf, huf⟩
    · rintro ⟨hf, huf⟩
      have hfH : f ∈ H := hS' (alive_subset _ _ hf)
      exact ⟨(halive f (mem_eball_of hfH huf hu)).mpr hf, huf⟩
  intro e he
  have he1 := eball_mono (by omega : k ≤ k + 1) v he
  have he2 := eball_mono (by omega : k ≤ k + 2) v he
  have hsub := subset_ball_of_mem_eball he
  constructor
  · -- (vi) the trimmed alive edges
    simp only [nextT, trim, mem_filter]
    rw [halive e he1]
    apply and_congr_right
    intro _
    exact forall₂_congr fun u hu => by rw [hdegA u (hsub hu)]
  · -- (vii)-(viii) the matching
    simp only [nextT, mem_union]
    apply or_congr (hag e he2).2
    simp only [acc, mem_filter]
    rw [hmem e he2, hcoinE e he2]
    apply and_congr_right
    intro heA'
    apply and_congr_right
    intro _
    constructor
    · intro h f hf hfe hd
      have hfH : f ∈ H := hS' hf
      have hf2 := eball_mono (by omega : k + 1 ≤ k + 2) v (mem_eball_succ_of_meet he hfH hd)
      rw [← hcoinE f hf2]
      exact h f ((hmem f hf2).mpr hf) hfe hd
    · intro h f hf hfe hd
      have hfH : f ∈ H := hS hf
      have hf2 := eball_mono (by omega : k + 1 ≤ k + 2) v (mem_eball_succ_of_meet he hfH hd)
      rw [hcoinE f hf2]
      exact h f ((hmem f hf2).mp hf) hfe hd

/-! ## Many rounds are local -/

/-- Whether a coin is relevant within radius `m` of `v`. -/
def coinIn (H : Finset (Finset V)) (m : ℕ) (v : V) : Coin V → Bool
  | Sum.inl e => decide (e ∈ eball H m v)
  | Sum.inr u => decide (u ∈ ball H m v)

/-- The coins of all rounds that are relevant within radius `m` of `v`. -/
def coordSet (H : Finset (Finset V)) (T m : ℕ) (v : V) : Finset (Fin T × Coin V) :=
  univ.filter (fun i => coinIn H m v i.2 = true)

theorem mem_coordSet_inl {H : Finset (Finset V)} {T m : ℕ} {v : V} {t : Fin T} {e : Finset V} :
    (t, Sum.inl e) ∈ coordSet H T m v ↔ e ∈ eball H m v := by
  rw [coordSet, mem_filter]
  simp only [mem_univ, true_and]
  show decide (e ∈ eball H m v) = true ↔ _
  exact decide_eq_true_iff

theorem mem_coordSet_inr {H : Finset (Finset V)} {T m : ℕ} {v : V} {t : Fin T} {u : V} :
    (t, Sum.inr u) ∈ coordSet H T m v ↔ u ∈ ball H m v := by
  rw [coordSet, mem_filter]
  simp only [mem_univ, true_and]
  show decide (u ∈ ball H m v) = true ↔ _
  exact decide_eq_true_iff

theorem coordSet_mono {H : Finset (Finset V)} {T m m' : ℕ} (h : m ≤ m') (v : V) :
    coordSet H T m v ⊆ coordSet H T m' v := by
  intro i hi
  rcases i with ⟨t, e | u⟩
  · exact mem_coordSet_inl.mpr (eball_mono h v (mem_coordSet_inl.mp hi))
  · exact mem_coordSet_inr.mpr (ball_mono h v (mem_coordSet_inr.mp hi))

theorem stateAt_local {N : ℕ} {H : Finset (Finset V)} {Ds : ℕ → ℝ} {T : ℕ} (v : V)
    {ω ω' : Fin T × Coin V → Fin (N + 2)} :
    ∀ t k, (∀ i ∈ coordSet H T (k + 2 * t) v, ω i = ω' i) →
      AgreeOn (eball H k v) (stateAt N H Ds T ω t) (stateAt N H Ds T ω' t)
  | 0, k, _ => fun e _ => ⟨Iff.rfl, Iff.rfl⟩
  | t + 1, k, h => by
    have ih := stateAt_local (Ds := Ds) v t (k + 2) (fun i hi => h i (by
      have : k + 2 + 2 * t = k + 2 * (t + 1) := by ring
      rw [this] at hi; exact hi))
    simp only [stateAt]
    split_ifs with ht
    · refine nextT_local N (Ds (t + 1)) (stateAt_inv ω t).1 (stateAt_inv ω' t).1 k v ih ?_ ?_
      · intro e he
        exact h (⟨t, ht⟩, Sum.inl e) (mem_coordSet_inl.mpr (eball_mono (by omega) v he))
      · intro u hu
        exact h (⟨t, ht⟩, Sum.inr u) (mem_coordSet_inr.mpr (ball_mono (by omega) v hu))
    · exact ih.mono (eball_mono (by omega) v)

/-- **Locality of the output.** Whether an edge at `v` is in the output matching only depends on
the coins in `coordSet H T (2T) v`. -/
theorem outM_local {N : ℕ} {H : Finset (Finset V)} {Ds : ℕ → ℝ} {T : ℕ} (v : V)
    {ω ω' : Fin T × Coin V → Fin (N + 2)} (h : ∀ i ∈ coordSet H T (2 * T) v, ω i = ω' i)
    {e : Finset V} (he : e ∈ H) (hv : v ∈ e) :
    e ∈ outM N H Ds T ω ↔ e ∈ outM N H Ds T ω' := by
  have := stateAt_local (Ds := Ds) v T 0 (by simpa using h)
  exact (this e (mem_eball_of he hv (self_mem_ball 0 v))).2

/-- Coordinate sets of far apart vertices are disjoint. -/
theorem mem_ball_of_not_disjoint_coordSet {H : Finset (Finset V)} {T m : ℕ} {v w : V}
    (h : ¬ Disjoint (coordSet H T m v) (coordSet H T m w)) : w ∈ ball H (2 * m + 1) v := by
  obtain ⟨i, hiv, hiw⟩ := Finset.not_disjoint_iff.mp h
  rcases i with ⟨t, e | u⟩
  · obtain ⟨heH, u1, hu1e, hu1⟩ := mem_eball.mp (mem_coordSet_inl.mp hiv)
    obtain ⟨-, u2, hu2e, hu2⟩ := mem_eball.mp (mem_coordSet_inl.mp hiw)
    have h1 : u2 ∈ ball H (m + 1) v := ball_trans hu1 (mem_ball_one_of_adj heH hu1e hu2e)
    have h2 := ball_trans h1 (ball_symm hu2)
    rwa [show m + 1 + m = 2 * m + 1 by ring] at h2
  · have h2 := ball_trans (mem_coordSet_inr.mp hiv) (ball_symm (mem_coordSet_inr.mp hiw))
    exact ball_mono (by omega) v h2

end Pseudorandom.PS
