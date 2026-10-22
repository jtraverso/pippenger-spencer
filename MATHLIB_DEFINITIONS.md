# Mathlib definitions used in Challenge.lean (Pippenger–Spencer)

Verbatim excerpts of the Mathlib definitions used by the statements in `Challenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib.

## Finset.card

`Mathlib/Data/Finset/Card.lean`, line 47:

```lean
/-- `s.card` is the number of elements of `s`, aka its cardinality.

The notation `#s` can be accessed in the `Finset` locale. -/
def card (s : Finset α) : ℕ :=
  Multiset.card s.1
```

## Finset.filter

`Mathlib/Data/Finset/Filter.lean`, line 52:

```lean
/-- `Finset.filter p s` is the set of elements of `s` that satisfy `p`.

For example, one can use `s.filter (· ∈ t)` to get the intersection of `s` with `t : Set α`
as a `Finset α` (when a `DecidablePred (· ∈ t)` instance is available). -/
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩
```

## Disjoint

`Mathlib/Order/Disjoint.lean`, line 48:

```lean
def Disjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥
```

## Real.exp

`Mathlib/Analysis/Complex/Exponential.lean`, line 80:

```lean
/-- The real exponential function, defined as the real part of the complex exponential -/
@[pp_nodot, wikidata Q168698]
nonrec def exp (x : ℝ) : ℝ :=
  (exp x).re
```

## Real.rpow

`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`, line 35:

```lean
/-- The real power function `x ^ y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`, one sets `0 ^ 0=1` and `0 ^ y=0` for
`y ≠ 0`. For `x < 0`, the definition is somewhat arbitrary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (π y)`. -/
noncomputable def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re
```
