/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-! # Hypergraphs, matchings and weights

Basic vocabulary for the formalization of Ehard–Glock–Joos, *Pseudorandom hypergraph
matchings* (arXiv:1907.09946).

A hypergraph on a finite vertex type `V` is a finite set `H : Finset (Finset V)` of edges.
It is `r`-uniform if every edge has exactly `r` vertices. A weight function is a function
`ω : Finset V → ℝ`; only its values on the edges of `H` matter.
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {V : Type*} [DecidableEq V]

/-- `H` is `r`-uniform: every edge has exactly `r` vertices. -/
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- The degree `deg_H(v)`: the number of edges containing `v`. -/
def degree (H : Finset (Finset V)) (v : V) : ℕ := (H.filter (fun e => v ∈ e)).card

/-- The codegree `deg_H(uv)`: the number of edges containing both `u` and `v`. -/
def codegree (H : Finset (Finset V)) (u v : V) : ℕ :=
  (H.filter (fun e => u ∈ e ∧ v ∈ e)).card

/-- A matching: a set of pairwise disjoint edges. -/
def IsMatching (M : Finset (Finset V)) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

/-- The weight `ω(X) = ∑_{e ∈ X} ω(e)` of a set of edges. -/
def weight (ω : Finset V → ℝ) (X : Finset (Finset V)) : ℝ := ∑ e ∈ X, ω e

end Pseudorandom
