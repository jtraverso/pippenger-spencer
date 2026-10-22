/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import PseudorandomLib.PippengerSpencer.Main
public import PseudorandomLib.PippengerSpencer.Polynomial

/-!
# Proofs of the statements in `Challenge.lean`

The definitions are copied verbatim from `Challenge.lean`; each theorem is closed by the
corresponding theorem of `PseudorandomLib` (namespace `Pseudorandom`), whose definitions are
literally the same.
-/

@[expose] public section

namespace PippengerSpencer

open Finset

section Hypergraphs

variable {V : Type*} [DecidableEq V]

/-- `H` is `r`-uniform: every edge has exactly `r` vertices. -/
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- The degree `deg_H(v)`: the number of edges containing `v`. -/
def degree (H : Finset (Finset V)) (v : V) : ℕ := (H.filter (fun e => v ∈ e)).card

/-- The codegree `deg_H(uv)`: the number of edges containing both `u` and `v`. -/
def codegree (H : Finset (Finset V)) (u v : V) : ℕ :=
  (H.filter (fun e => u ∈ e ∧ v ∈ e)).card

/-- A proper edge colouring of `H` with `m` colours: edges of the same colour are disjoint. -/
def IsProperEdgeColouring (H : Finset (Finset V)) (m : ℕ) (c : Finset V → Fin m) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → c e = c f → Disjoint e f

end Hypergraphs

/-- **The Pippenger–Spencer theorem.** For `r ≥ 2` and `ε > 0` there are `μ > 0` and `D₀`
such that every `r`-uniform hypergraph whose degrees lie in `[(1 - μ) D, D]` and whose codegrees
are at most `μ D`, with `D ≥ D₀`, has a proper edge colouring with at most `(1 + ε) D` colours. -/
theorem pippenger_spencer (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ D₀ : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V))
      (D : ℝ), D₀ ≤ D → IsUniform H r →
      (∀ v, (1 - μ) * D ≤ degree H v ∧ (degree H v : ℝ) ≤ D) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ μ * D) →
      ∃ (m : ℕ) (c : Finset V → Fin m), (m : ℝ) ≤ (1 + ε) * D ∧ IsProperEdgeColouring H m c :=
  Pseudorandom.pippenger_spencer r hr ε hε

/-- **Chromatic index under polynomial codegrees.** For `r ≥ 2` and `0 < δ < 1` there are
`γ > 0` and `D₀` such that every `r`-uniform hypergraph with maximum degree at most `D ≥ D₀`,
codegrees at most `D^{1-δ}` and at most `exp(D^γ)` edges has a proper edge colouring with at
most `D + D^{1-γ}` colours. -/
theorem chromatic_index_polynomial (r : ℕ) (hr : 2 ≤ r) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ D₀ : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V))
      (D : ℝ), D₀ ≤ D → IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ D ^ (1 - δ)) →
      (H.card : ℝ) ≤ Real.exp (D ^ γ) →
      ∃ (m : ℕ) (c : Finset V → Fin m), (m : ℝ) ≤ D + D ^ (1 - γ) ∧
        IsProperEdgeColouring H m c :=
  Pseudorandom.chromatic_index_polynomial r hr δ hδ0 hδ1

end PippengerSpencer
