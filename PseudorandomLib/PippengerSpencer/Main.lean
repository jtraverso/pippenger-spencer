/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.PippengerSpencer.Step
public import PseudorandomLib.PippengerSpencer.Iterate
public import PseudorandomLib.PippengerSpencer.Numerics

/-! # The Pippenger–Spencer theorem

**Theorem** (Pippenger–Spencer 1989). For `r ≥ 2` and `ε > 0` there are `μ > 0` and `D₀` such
that every `r`-uniform hypergraph with all degrees in `[(1 - μ) D, D]` and all codegrees
`≤ μ D` has chromatic index at most `(1 + ε) D`, whenever `D ≥ D₀`.

Proof: colour in batches of `K ≈ ε₁ τ D` colours. In each batch `K` independent copies of the
(trimmed, local) Rödl nibble are run on the uncoloured hypergraph; by the Local Lemma there is an
outcome lowering the maximum degree by `K (1 - 28 ε₁)`. After about `(1 - τ) D / K` batches
the maximum degree is `≤ 2 τ D` and the rest is coloured greedily with `≤ 2 r τ D + 1` colours.
The lower bound on the degrees is not needed.
-/

@[expose] public section

namespace Pseudorandom

open Finset Filter PS

theorem codegree_mono' {V : Type*} [DecidableEq V] {A B : Finset (Finset V)} (h : A ⊆ B)
    (u w : V) : codegree A u w ≤ codegree B u w :=
  card_le_card (filter_subset_filter _ h)

/-- **The Pippenger–Spencer theorem.** A nearly regular `r`-uniform hypergraph with small
codegrees has chromatic index at most `(1 + ε) D`.

The lower bound `(1 - μ) D ≤ deg(v)` is part of the requested statement but is not used by the
proof: the conclusion holds for every hypergraph of maximum degree `≤ D`. -/
theorem pippenger_spencer (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ D₀ : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V))
      (D : ℝ), D₀ ≤ D → IsUniform H r →
      (∀ v, (1 - μ) * D ≤ degree H v ∧ (degree H v : ℝ) ≤ D) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ μ * D) →
      ∃ (m : ℕ) (c : Finset V → Fin m), (m : ℝ) ≤ (1 + ε) * D ∧ IsProperEdgeColouring H m c := by
  -- parameters
  set ε' : ℝ := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  set ε₁ : ℝ := ε' / 200 with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₁s : ε₁ ≤ 1 / 56 := by rw [hε₁]; linarith
  set τ : ℝ := ε' / (6 * r) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτr : 2 * r * τ = ε' / 3 := by rw [hτ]; field_simp; ring
  have hτ1 : τ ≤ 1 := by
    rw [hτ, div_le_one (by positivity)]; linarith
  obtain ⟨μ₀, hμ₀, T, hT⟩ := Nibble.pippenger_process r hr hε₁0
  have hproc : ∀ D : ℝ, 1 ≤ μ₀ * D →
      ∃ as Ds : ℕ → ℝ, (∀ t, 0 ≤ as t) ∧ (∀ t, 0 ≤ Ds t) ∧ Ds 0 = D ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)),
        IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
        (∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ μ₀ * D) →
        ∀ e ∈ H, (1 - ε₁) / D ≤ ∑ M, Nibble.outMT H as Ds T M * (if e ∈ M then 1 else 0) := by
    intro D hD
    obtain ⟨as, Ds, h1, h2, h3, h4⟩ := hT D hD
    exact ⟨as, Ds, h1, h2, h3, fun V _ _ H => h4 V H⟩
  set a : ℝ := ε₁ * τ with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp
    (eventually_numerics hε₁0 ha0 hμ₀ hτ0 hε'0 r T)
  refine ⟨μ₀ * τ, by positivity, D₀, ?_⟩
  intro V _ _ H D hD huni hdeg hcod
  obtain ⟨hD1, hμD, hK1, hεD, hLLL⟩ := hD₀ D hD
  have hD0 : 0 < D := by linarith
  set K : ℕ := ⌊a * D⌋₊ with hK
  have hKle : (K : ℝ) ≤ a * D := Nat.floor_le (by positivity)
  have hKpos : (0 : ℝ) < K := by
    by_contra h; push Not at h; nlinarith
  set lam : ℝ := 1 - 28 * ε₁ with hlam
  have hlam0 : 1 / 2 ≤ lam := by rw [hlam]; linarith
  have hlam1 : lam ≤ 1 := by rw [hlam]; linarith
  have hdegH : ∀ v, (degree H v : ℝ) ≤ D := fun v => (hdeg v).2
  -- one batch
  have hstep : ∀ G ⊆ H, ∀ Db : ℝ, τ * D ≤ Db → (∀ v, (degree G v : ℝ) ≤ Db) →
      ∃ (Col : Finset (Finset V)) (c : Finset V → Fin K), Col ⊆ G ∧
        IsProperEdgeColouring Col K c ∧ ∀ v, (degree (G \ Col) v : ℝ) ≤ Db - K * lam := by
    intro G hG Db hDb hdegG
    have hμDb : μ₀ * τ * D ≤ μ₀ * Db := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hDb hμ₀.le
    refine batch_step hε₁0 hε₁s hproc G (fun e he => huni e (hG he)) (by linarith) hdegG
      (fun u w huw => ?_) (Δ := ⌊D⌋₊) (fun v => ?_) hK1 ?_ hLLL
    · have := codegree_mono' hG u w
      have : (codegree G u w : ℝ) ≤ codegree H u w := by exact_mod_cast this
      linarith [hcod u w huw]
    · exact Nat.le_floor ((Nat.cast_le.mpr (degree_mono' hG v)).trans (hdegH v))
    · have : a * D ≤ ε₁ * Db := by
        rw [ha, mul_assoc]; exact mul_le_mul_of_nonneg_left hDb hε₁0.le
      linarith
  -- the number of batches
  have hKlam : 0 < (K : ℝ) * lam := by nlinarith
  set B : ℕ := ⌊(1 - τ) * D / (K * lam)⌋₊ with hB
  have hBle : (B : ℝ) * (K * lam) ≤ (1 - τ) * D := by
    have := Nat.floor_le (by
      have : 0 ≤ (1 - τ) * D := mul_nonneg (by linarith) hD0.le
      positivity : 0 ≤ (1 - τ) * D / (K * lam))
    rwa [← hB, le_div_iff₀ hKlam] at this
  have hBgt : (1 - τ) * D < (B + 1) * (K * lam) := by
    have := Nat.lt_floor_add_one ((1 - τ) * D / (K * lam))
    rwa [← hB, div_lt_iff₀ hKlam] at this
  obtain ⟨Col, c, hCol, hc, hdegC⟩ := iterate_batches H hstep hdegH B (by
    intro j hj
    have : (j : ℝ) * (K * lam) ≤ B * (K * lam) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj.le) hKlam.le
    linarith)
  -- the leftover is coloured greedily
  set DB : ℝ := D - B * (K * lam) with hDB
  have hDB0 : 0 ≤ DB := by
    have : 0 ≤ τ * D := by positivity
    rw [hDB]; linarith
  set Δ' : ℕ := ⌊DB⌋₊ with hΔ'
  obtain ⟨c', hc'⟩ := exists_greedy_colouring r Δ' (H \ Col)
    (fun e he => huni e (mem_sdiff.mp he).1) (fun v => Nat.le_floor (hdegC v))
  have hglue := hc.glue hc'
  rw [union_sdiff_of_subset hCol] at hglue
  refine ⟨B * K + 1 + (r * Δ' + 1), _, ?_, hglue⟩
  -- counting colours
  have hΔ'le : (Δ' : ℝ) ≤ DB := Nat.floor_le hDB0
  have hDBle : DB ≤ 2 * τ * D := by
    have h1 : (K : ℝ) * lam ≤ K := mul_le_of_le_one_right hKpos.le hlam1
    have h2 : a * D ≤ τ * D := by
      rw [ha]; apply mul_le_mul_of_nonneg_right _ hD0.le; nlinarith
    rw [hDB]; nlinarith
  have hBK : (B : ℝ) * K ≤ D * (1 + 56 * ε₁) := by
    have h1 : (B : ℝ) * K ≤ (B * (K * lam)) * (1 + 56 * ε₁) := by
      have : 1 ≤ lam * (1 + 56 * ε₁) := by rw [hlam]; nlinarith
      have h0 : (0 : ℝ) ≤ B * K := by positivity
      calc (B : ℝ) * K = (B * K) * 1 := by ring
        _ ≤ (B * K) * (lam * (1 + 56 * ε₁)) := mul_le_mul_of_nonneg_left this h0
        _ = (B * (K * lam)) * (1 + 56 * ε₁) := by ring
    have h2 : (B : ℝ) * (K * lam) ≤ D := by
      have : 0 ≤ τ * D := by positivity
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 1 + 56 * ε₁)
    linarith
  have hrΔ : (r : ℝ) * Δ' ≤ ε' / 3 * D := by
    have : (r : ℝ) * Δ' ≤ r * (2 * τ * D) :=
      mul_le_mul_of_nonneg_left (hΔ'le.trans hDBle) (Nat.cast_nonneg r)
    rw [← hτr]; linarith
  push_cast
  have : ε' * D ≤ ε * D := mul_le_mul_of_nonneg_right hε'ε hD0.le
  have : ε₁ * D = ε' * D / 200 := by rw [hε₁]; ring
  have : D * (1 + 56 * ε₁) = D + 56 * (ε₁ * D) := by ring
  have : (1 + ε) * D = D + ε * D := by ring
  linarith

end Pseudorandom
