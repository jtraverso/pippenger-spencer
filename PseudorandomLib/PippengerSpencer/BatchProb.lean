/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.PippengerSpencer.Locality

/-! # A batch of independent nibbles: the probability estimates at one vertex

We run `K` independent copies of the realised nibble on a hypergraph `G`, giving matchings
`M_0, …, M_{K-1}`. Fix a vertex `v` of large degree. Let `X_i` be the event that `M_i` covers `v`
and `Z_i` the event that the edge of `M_i` at `v` already lies in an earlier `M_j`. Then
* the number of edges at `v` lying in some `M_i` is at least `#{i : X_i} - #{i : Z_i}`;
* `#{i : X_i}` is a sum of independent indicators, each of probability `≥ (Db - K)(1-ε)/Db`
  (Bernstein's inequality gives the lower tail);
* whatever happened before, `Z_i` has conditional probability at most
  `q = 1 - (Db - 2K)(1-ε)/Db`, so `P(#{i : Z_i} ≥ m) ≤ C(K, m) q^m ≤ e^{-m}` once `m ≥ e² K q`.
-/

@[expose] public section

namespace Pseudorandom.PS

open Finset Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

section Sample

variable {N : ℕ} {G : Finset (Finset V)} {as Ds : ℕ → ℝ} {T : ℕ}

/-- A matching has at most one edge at `v`. -/
theorem card_filter_mem_le_one {M : Finset (Finset V)} (hM : IsMatching M) (v : V) :
    (M.filter (fun e => v ∈ e)).card ≤ 1 := by
  rw [card_le_one]
  intro e he f hf
  by_contra hef
  have := hM e (mem_filter.mp he).1 f (mem_filter.mp hf).1 hef
  exact Finset.disjoint_left.mp this (mem_filter.mp he).2 (mem_filter.mp hf).2

/-- The event that the sample covers `v`. -/
def Cov (N : ℕ) (G : Finset (Finset V)) (Ds : ℕ → ℝ) (T : ℕ) (v : V)
    (y : Fin T × Coin V → Fin (N + 2)) : Prop :=
  ∃ e ∈ outM N G Ds T y, v ∈ e

/-- The probability that some edge of `U` lies in the sample. -/
theorem pProb_hit_eq (has : ∀ t, 0 ≤ as t) (U : Finset (Finset V)) (v : V)
    (hU : ∀ e ∈ U, v ∈ e) :
    pProb (procQ N as Ds T) (fun y => ∃ e ∈ outM N G Ds T y, e ∈ U) =
      ∑ e ∈ U, pProb (procQ N as Ds T) (fun y => e ∈ outM N G Ds T y) := by
  classical
  have hQ := procQ_isPMF (V := V) (N := N) (Ds := Ds) (T := T) has
  rw [pProb_eq_pE _ (fun y => (((outM N G Ds T y).filter (fun e => e ∈ U)).card : ℝ))]
  · have : (fun y => (((outM N G Ds T y).filter (fun e => e ∈ U)).card : ℝ)) =
        fun y => ∑ e ∈ U, (if e ∈ outM N G Ds T y then (1 : ℝ) else 0) := by
      funext y
      rw [sum_boole]
      congr 2
      ext e; simp [and_comm]
    rw [this, pE_sum]
    refine sum_congr rfl fun e _ => ?_
    rw [pProb_eq_pE _ (fun y => if e ∈ outM N G Ds T y then (1 : ℝ) else 0)
      (fun y h => by simp [h]) (fun y h => by simp [h])]
  · intro y ⟨e, he, heU⟩
    have h1 : 1 ≤ ((outM N G Ds T y).filter (fun e => e ∈ U)).card :=
      card_pos.mpr ⟨e, mem_filter.mpr ⟨he, heU⟩⟩
    have h2 : ((outM N G Ds T y).filter (fun e => e ∈ U)).card ≤ 1 := by
      refine le_trans (card_le_card ?_) (card_filter_mem_le_one (outM_isMatching (N := N) (H := G) (Ds := Ds) (T := T) y).1 v)
      intro f hf
      rw [mem_filter] at hf ⊢
      exact ⟨hf.1, hU f hf.2⟩
    have : ((outM N G Ds T y).filter (fun e => e ∈ U)).card = 1 := le_antisymm h2 h1
    rw [this]; norm_num
  · intro y h
    push Not at h
    have : (outM N G Ds T y).filter (fun e => e ∈ U) = ∅ := by
      rw [filter_eq_empty_iff]; exact fun e he heU => h e he heU
    rw [this]; simp

/-- Hitting the edges of `G` at `v` is covering `v`. -/
theorem pProb_cov_eq (has : ∀ t, 0 ≤ as t) (v : V) :
    pProb (procQ N as Ds T) (Cov N G Ds T v) =
      ∑ e ∈ G.filter (fun e => v ∈ e), pProb (procQ N as Ds T)
        (fun y => e ∈ outM N G Ds T y) := by
  rw [← pProb_hit_eq has _ v (fun e he => (mem_filter.mp he).2)]
  refine pProb_congr fun y => ?_
  constructor
  · rintro ⟨e, he, hv⟩
    exact ⟨e, he, mem_filter.mpr ⟨(outM_isMatching (N := N) (H := G) (Ds := Ds) (T := T) y).2 he, hv⟩⟩
  · rintro ⟨e, he, heU⟩
    exact ⟨e, he, (mem_filter.mp heU).2⟩

/-- The marginal bound transferred to the realised process. -/
theorem pProb_mem_outM_ge (has : ∀ t, 0 ≤ as t) (hDs : ∀ t, 0 ≤ Ds t)
    (hdeg : Good (Ds 0) G) (hN : G.card ≤ N) {p : ℝ}
    (hmarg : ∀ e ∈ G, p ≤ ∑ M, outMT G as Ds T M * (if e ∈ M then 1 else 0))
    {e : Finset V} (he : e ∈ G) :
    p ≤ pProb (procQ N as Ds T) (fun y => e ∈ outM N G Ds T y) := by
  rw [outM_marginal has hDs hdeg hN e]; exact hmarg e he

/-- Lower bound for the probability of covering `v`. -/
theorem pProb_cov_ge (has : ∀ t, 0 ≤ as t) (hDs : ∀ t, 0 ≤ Ds t)
    (hdeg : Good (Ds 0) G) (hN : G.card ≤ N) {p : ℝ}
    (hmarg : ∀ e ∈ G, p ≤ ∑ M, outMT G as Ds T M * (if e ∈ M then 1 else 0)) (v : V) :
    (degree G v : ℝ) * p ≤ pProb (procQ N as Ds T) (Cov N G Ds T v) := by
  rw [pProb_cov_eq has v]
  have := sum_le_sum fun e (he : e ∈ G.filter (fun e => v ∈ e)) =>
    pProb_mem_outM_ge (T := T) (N := N) has hDs hdeg hN hmarg (mem_filter.mp he).1
  rw [sum_const, nsmul_eq_mul] at this
  unfold degree
  exact this

/-- Upper bound for the probability of hitting a set `U` of edges at `v`. -/
theorem pProb_hit_le (has : ∀ t, 0 ≤ as t) (hDs : ∀ t, 0 ≤ Ds t)
    (hdeg : Good (Ds 0) G) (hN : G.card ≤ N) {p : ℝ} (hp : 0 ≤ p)
    (hmarg : ∀ e ∈ G, p ≤ ∑ M, outMT G as Ds T M * (if e ∈ M then 1 else 0)) (v : V)
    (U : Finset (Finset V)) (hU : ∀ e ∈ U, v ∈ e) :
    pProb (procQ N as Ds T) (fun y => ∃ e ∈ outM N G Ds T y, e ∈ U) ≤
      1 - ((degree G v : ℝ) - U.card) * p := by
  have hQ := procQ_isPMF (V := V) (N := N) (Ds := Ds) (T := T) has
  set star := G.filter (fun e => v ∈ e)
  -- split the sum over the star
  have hcov := pProb_cov_eq (G := G) (N := N) (Ds := Ds) (T := T) has v
  have hle1 := pProb_le_one hQ (Cov N G Ds T v)
  have hsplit := sum_filter_add_sum_filter_not star (fun e => e ∈ U)
    (fun e => pProb (procQ N as Ds T) (fun y => e ∈ outM N G Ds T y))
  have hrest : ((star.filter (fun e => ¬ e ∈ U)).card : ℝ) * p ≤
      ∑ e ∈ star.filter (fun e => ¬ e ∈ U),
        pProb (procQ N as Ds T) (fun y => e ∈ outM N G Ds T y) := by
    have := sum_le_sum fun e (he : e ∈ star.filter (fun e => ¬ e ∈ U)) =>
      pProb_mem_outM_ge (T := T) (N := N) has hDs hdeg hN hmarg
        (mem_filter.mp (mem_filter.mp he).1).1
    rwa [sum_const, nsmul_eq_mul] at this
  have hcard : (degree G v : ℝ) - U.card ≤ ((star.filter (fun e => ¬ e ∈ U)).card : ℝ) := by
    have h1 := card_filter_add_card_filter_not (s := star) (fun e => e ∈ U)
    have h2 : (star.filter (fun e => e ∈ U)).card ≤ U.card :=
      card_le_card (fun e he => (mem_filter.mp he).2)
    have h3 : degree G v = star.card := rfl
    have : (degree G v : ℝ) = (star.filter (fun e => e ∈ U)).card +
        (star.filter (fun e => ¬ e ∈ U)).card := by rw [h3]; exact_mod_cast h1.symm
    have h2' : ((star.filter (fun e => e ∈ U)).card : ℝ) ≤ U.card := by exact_mod_cast h2
    linarith
  have hhit : pProb (procQ N as Ds T) (fun y => ∃ e ∈ outM N G Ds T y, e ∈ U) ≤
      ∑ e ∈ star.filter (fun e => e ∈ U),
        pProb (procQ N as Ds T) (fun y => e ∈ outM N G Ds T y) := by
    rw [← pProb_hit_eq has _ v (fun e he => (mem_filter.mp (mem_filter.mp he).1).2)]
    refine pProb_mono hQ fun y ⟨e, he, heU⟩ => ⟨e, he, mem_filter.mpr ⟨mem_filter.mpr
      ⟨(outM_isMatching (N := N) (H := G) (Ds := Ds) (T := T) y).2 he, hU e heU⟩, heU⟩⟩
  have := mul_le_mul_of_nonneg_right hcard hp
  linarith

end Sample

end Pseudorandom.PS
