/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.PippengerSpencer.BatchCoarse
public import PseudorandomLib.PippengerSpencer.LLL
public import PseudorandomLib.PippengerSpencer.Basic

/-! # One batch of colours

Run `K` independent copies of the realised nibble on `G` and give the edges of the `i`-th
matching colour `i` (an edge in several matchings gets the smallest such colour). With the
Lovász Local Lemma we find an outcome in which every vertex of large degree (degree
`> Db - K λ`) loses at least `K λ` edges. Hence the uncoloured edges form a hypergraph of
maximum degree `≤ Db - K λ`.
-/

@[expose] public section

namespace Pseudorandom.PS

open Finset Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {N : ℕ} {G : Finset (Finset V)} {as Ds : ℕ → ℝ} {T K : ℕ}

open Classical in
/-- **The failure probability at a vertex of large degree.** -/
theorem pProb_bad_le (has : ∀ t, 0 ≤ as t) (hDs : ∀ t, 0 ≤ Ds t) (hdeg : Good (Ds 0) G)
    (hN : G.card ≤ N) {p : ℝ} (hp : 0 ≤ p)
    (hmarg : ∀ e ∈ G, p ≤ ∑ M, outMT G as Ds T M * (if e ∈ M then 1 else 0)) (v : V)
    {lam t q : ℝ} {m : ℕ} (ht : 0 < t)
    (htm : t ≤ K * ((degree G v : ℝ) * p) - K * lam - m)
    (hq : 1 - ((degree G v : ℝ) - K) * p ≤ q) (hq0 : 0 ≤ q) (hm : Real.exp 2 * K * q ≤ m) :
    pProb (sampleQ N as Ds T K) (fun y =>
        (((colSet N G Ds T y).filter (fun e => v ∈ e)).card : ℝ) < K * lam) ≤
      Real.exp (-(t ^ 2 / (2 * (K + t)))) + Real.exp (-m) := by
  have hQ := sampleQ_isPMF (V := V) (N := N) (Ds := Ds) (T := T) (K := K) has
  have hcov := pProb_cov_ge (G := G) (N := N) (T := T) has hDs hdeg hN hmarg v
  have hhit : ∀ U : Finset (Finset V), U.card ≤ K → (∀ e ∈ U, v ∈ e) →
      pProb (procQ N as Ds T) (fun y => ∃ e ∈ outM N G Ds T y, e ∈ U) ≤ q := by
    intro U hU hUv
    refine (pProb_hit_le has hDs hdeg hN hp hmarg v U hUv).trans ?_
    have : ((degree G v : ℝ) - K) * p ≤ ((degree G v : ℝ) - U.card) * p := by
      apply mul_le_mul_of_nonneg_right _ hp
      have : (U.card : ℝ) ≤ K := by exact_mod_cast hU
      linarith
    linarith
  have hA := pProb_cov_lower (K := K) has v ht hcov
  have hB := pProb_rep_ge has v hq0 hhit m hm
  refine le_trans (pProb_mono hQ fun y hy => ?_) ((pProb_or_le hQ _ _).trans (add_le_add hA hB))
  have hc := card_cov_sub_card_rep_le (G := G) (Ds := Ds) v y
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  linarith

/-- The colour of an edge: the first sample containing it. -/
noncomputable def firstColour (hK : 0 < K) (M : Fin K → Finset (Finset V)) (e : Finset V) :
    Fin K := by
  classical
  exact if h : (univ.filter (fun i => e ∈ M i)).Nonempty then
    (univ.filter (fun i => e ∈ M i)).min' h else ⟨0, hK⟩

theorem firstColour_mem (hK : 0 < K) (M : Fin K → Finset (Finset V)) {e : Finset V}
    (he : ∃ i, e ∈ M i) : e ∈ M (firstColour hK M e) := by
  classical
  have hne : (univ.filter (fun i => e ∈ M i)).Nonempty := by
    obtain ⟨i, hi⟩ := he; exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have := min'_mem _ hne
  unfold firstColour
  rw [dif_pos hne]
  exact (mem_filter.mp this).2

theorem firstColour_proper (hK : 0 < K) (M : Fin K → Finset (Finset V))
    (hM : ∀ i, IsMatching (M i)) :
    IsProperEdgeColouring (univ.biUnion M) K (firstColour hK M) := by
  intro e he f hf hef hc
  obtain ⟨i, -, hi⟩ := mem_biUnion.mp he
  obtain ⟨j, -, hj⟩ := mem_biUnion.mp hf
  have h1 := firstColour_mem hK M ⟨i, hi⟩
  have h2 := firstColour_mem hK M ⟨j, hj⟩
  rw [← hc] at h2
  exact hM _ e h1 f h2 hef

/-- **One batch of colours.** -/
theorem batch_colouring {r : ℕ} (huni : IsUniform G r) (hN : G.card ≤ N)
    (has : ∀ t, 0 ≤ as t) (hDs : ∀ t, 0 ≤ Ds t) {Db : ℝ} (hDs0 : Ds 0 = Db)
    (hdeg : ∀ v, (degree G v : ℝ) ≤ Db) {p : ℝ} (hp : 0 ≤ p)
    (hmarg : ∀ e ∈ G, p ≤ ∑ M, outMT G as Ds T M * (if e ∈ M then 1 else 0))
    (hK : 0 < K) {lam t : ℝ} {m Δ : ℕ} (hΔ : ∀ v, degree G v ≤ Δ) (hlam : lam ≤ 1)
    (ht : 0 < t) (htm : t ≤ K * ((Db - K) * p) - K * lam - m)
    (hq0 : 0 ≤ 1 - (Db - 2 * K) * p) (hm : Real.exp 2 * K * (1 - (Db - 2 * K) * p) ≤ m)
    (hLLL : Real.exp 1 * (Real.exp (-(t ^ 2 / (2 * (K + t)))) + Real.exp (-m)) *
      (((1 + r * Δ) ^ (4 * T + 1) : ℕ) + 1) ≤ 1) :
    ∃ (Col : Finset (Finset V)) (c : Finset V → Fin K), Col ⊆ G ∧
      IsProperEdgeColouring Col K c ∧ ∀ v, (degree (G \ Col) v : ℝ) ≤ Db - K * lam := by
  classical
  have hgood : Good (Ds 0) G := fun v => hDs0 ▸ hdeg v
  -- the fine product space
  set P : Fin K × (Fin T × Coin V) → Fin (N + 2) → ℝ := fun i => procQ N as Ds T i.2 with hPdef
  have hP : IsPMF P := ⟨fun i a => (procQ_isPMF has).1 i.2 a, fun i => (procQ_isPMF has).2 i.2⟩
  set sam : (Fin K × (Fin T × Coin V) → Fin (N + 2)) → Fin K → (Fin T × Coin V → Fin (N + 2)) :=
    fun ω i j => ω (i, j) with hsam
  set Bad : V → (Fin K × (Fin T × Coin V) → Fin (N + 2)) → Prop := fun v ω =>
    (((colSet N G Ds T (sam ω)).filter (fun e => v ∈ e)).card : ℝ) < K * lam with hBad
  set S : V → Finset (Fin K × (Fin T × Coin V)) := fun v => univ ×ˢ coordSet G T (2 * T) v
    with hS
  set U : Finset V := univ.filter (fun v => Db - K * lam < degree G v) with hU
  set p' : ℝ := Real.exp (-(t ^ 2 / (2 * (K + t)))) + Real.exp (-m) with hp'
  -- locality of the bad events
  have hloc : ∀ v, EvDepOn (Bad v) (S v) := by
    intro v ω ω' hωω'
    have hset : (colSet N G Ds T (sam ω)).filter (fun e => v ∈ e) =
        (colSet N G Ds T (sam ω')).filter (fun e => v ∈ e) := by
      ext e
      simp only [colSet, mem_filter, mem_biUnion, mem_univ, true_and]
      constructor
      · rintro ⟨⟨i, hi⟩, hv⟩
        have heG := (outM_isMatching (N := N) (H := G) (Ds := Ds) (T := T) _).2 hi
        refine ⟨⟨i, (outM_local v (fun j hj => hωω' (i, j) (mem_product.mpr ⟨mem_univ _, hj⟩))
          heG hv).mp hi⟩, hv⟩
      · rintro ⟨⟨i, hi⟩, hv⟩
        have heG := (outM_isMatching (N := N) (H := G) (Ds := Ds) (T := T) _).2 hi
        refine ⟨⟨i, (outM_local v (fun j hj => hωω' (i, j) (mem_product.mpr ⟨mem_univ _, hj⟩))
          heG hv).mpr hi⟩, hv⟩
    simp only [hBad, hset]
  -- the probability of each bad event
  have hprob : ∀ v ∈ U, pProb P (Bad v) ≤ p' := by
    intro v hv
    have hv' : Db - K * lam < degree G v := (mem_filter.mp hv).2
    rw [pProb_curry]
    have hdv : Db - K ≤ (degree G v : ℝ) := by
      have : (K : ℝ) * lam ≤ K := mul_le_of_le_one_right (Nat.cast_nonneg _) hlam
      linarith
    refine pProb_bad_le (m := m) has hDs hgood hN hp hmarg v ht ?_ ?_ hq0 hm
    · have : K * ((Db - K) * p) ≤ K * ((degree G v : ℝ) * p) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdv hp) (Nat.cast_nonneg _)
      linarith
    · have : (Db - 2 * K) * p ≤ ((degree G v : ℝ) - K) * p :=
        mul_le_mul_of_nonneg_right (by linarith) hp
      linarith
  -- the dependency degree
  have hdep : ∀ v ∈ U, (U.filter (fun w => w ≠ v ∧ ¬ Disjoint (S v) (S w))).card ≤
      (1 + r * Δ) ^ (4 * T + 1) := by
    intro v _
    refine le_trans (card_le_card ?_) (card_ball_le huni hΔ (4 * T + 1) v)
    intro w hw
    have hd := (mem_filter.mp hw).2.2
    obtain ⟨⟨i, j⟩, h1, h2⟩ := Finset.not_disjoint_iff.mp hd
    have h1' := (mem_product.mp h1).2
    have h2' := (mem_product.mp h2).2
    have := mem_ball_of_not_disjoint_coordSet (Finset.not_disjoint_iff.mpr ⟨j, h1', h2'⟩)
    rwa [show 2 * (2 * T) + 1 = 4 * T + 1 by ring] at this
  obtain ⟨ω, hω⟩ := lovasz_local_lemma hP Bad S hloc U p' _ hprob hdep (by
    have : ((1 + r * Δ) ^ (4 * T + 1) : ℕ) = (((1 + r * Δ) ^ (4 * T + 1) : ℕ) : ℝ) := rfl
    simpa [hp'] using hLLL)
  -- the colouring
  set M : Fin K → Finset (Finset V) := fun i => outM N G Ds T (sam ω i) with hM
  refine ⟨univ.biUnion M, firstColour hK M, ?_, firstColour_proper hK M
    (fun i => (outM_isMatching (N := N) (H := G) (Ds := Ds) (T := T) _).1), ?_⟩
  · intro e he
    obtain ⟨i, -, hi⟩ := mem_biUnion.mp he
    exact (outM_isMatching (N := N) (H := G) (Ds := Ds) (T := T) _).2 hi
  · intro v
    have hsplit : degree (G \ univ.biUnion M) v +
        ((univ.biUnion M).filter (fun e => v ∈ e)).card = degree G v := by
      unfold degree
      have hsub : (univ.biUnion M).filter (fun e => v ∈ e) ⊆ G.filter (fun e => v ∈ e) := by
        intro e he
        rw [mem_filter] at he ⊢
        obtain ⟨i, -, hi⟩ := mem_biUnion.mp he.1
        exact ⟨(outM_isMatching (N := N) (H := G) (Ds := Ds) (T := T) _).2 hi, he.2⟩
      have : (G \ univ.biUnion M).filter (fun e => v ∈ e) =
          G.filter (fun e => v ∈ e) \ (univ.biUnion M).filter (fun e => v ∈ e) := by
        ext e; simp only [mem_filter, mem_sdiff]; tauto
      rw [this, card_sdiff_add_card_eq_card hsub]
    have hsplitR : (degree (G \ univ.biUnion M) v : ℝ) =
        degree G v - (((univ.biUnion M).filter (fun e => v ∈ e)).card : ℝ) := by
      rw [← hsplit]; push_cast; ring
    rw [hsplitR]
    by_cases hv : v ∈ U
    · have := hω v hv
      simp only [hBad, not_lt] at this
      have hcol : colSet N G Ds T (sam ω) = univ.biUnion M := rfl
      rw [hcol] at this
      linarith [hdeg v]
    · have : (degree G v : ℝ) ≤ Db - K * lam := by
        simp only [hU, mem_filter, mem_univ, true_and, not_lt] at hv
        exact hv
      have h0 : (0 : ℝ) ≤ (((univ.biUnion M).filter (fun e => v ∈ e)).card : ℝ) :=
        Nat.cast_nonneg _
      linarith

end Pseudorandom.PS
