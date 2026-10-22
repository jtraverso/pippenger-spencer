# The Pippenger–Spencer theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of the theorem of N. Pippenger and J. Spencer, *Asymptotic
behavior of the chromatic index for hypergraphs* (J. Combin. Theory Ser. A 51 (1989) 24–42):
a nearly regular uniform hypergraph with small codegrees has chromatic index `(1 + o(1))`
times its degree. A second theorem gives an explicit polynomial error term when the codegrees
are polynomially small. All statements are in the namespace `PippengerSpencer` of
`Challenge.lean`.

## Definitions

Hypergraphs are finite sets of finite subsets of a finite vertex type `V`.

* `IsUniform H r`: every edge has exactly `r` vertices.
* `degree H v`, `codegree H u v`: the number of edges containing `v`, resp. both `u` and `v`.
* `IsProperEdgeColouring H m c`: `c : Finset V → Fin m` gives distinct edges of the same colour
  disjoint vertex sets. A colouring with `m` colours bounds the chromatic index by `m`.

## Results

| Lean | Statement |
|---|---|
| `pippenger_spencer` | For `r ≥ 2` and `ε > 0` there are `μ > 0` and `D₀` such that every `r`-uniform hypergraph with all degrees in `[(1 − μ) D, D]` and all codegrees `≤ μ D`, `D ≥ D₀`, has a proper edge colouring with at most `(1 + ε) D` colours |
| `chromatic_index_polynomial` | For `r ≥ 2` and `0 < δ < 1` there are `γ > 0` and `D₀` such that every `r`-uniform hypergraph with maximum degree `≤ D`, codegrees `≤ D^{1−δ}` and at most `exp(D^γ)` edges, `D ≥ D₀`, has a proper edge colouring with at most `D + D^{1−γ}` colours |

The lower bound `(1 − μ) D ≤ deg(v)` in `pippenger_spencer` is part of the classical statement
but is not used by the proof, so the bound holds for every hypergraph of maximum degree at most
`D` with codegrees at most `μ D`. The trivial lower bound `χ'(H) ≥ Δ(H)` is not restated.

## Proofs

The proofs (in `PseudorandomLib/PippengerSpencer/`) build on the author's formalization of
Ehard–Glock–Joos, *Pseudorandom hypergraph matchings* (Palomar PALOMAR-2026-10-17-000004,
[jtraverso/pseudorandom-hypergraph-matchings](https://github.com/jtraverso/pseudorandom-hypergraph-matchings)).
This repository contains only the part of that library they need (36 modules, all unchanged).

* `pippenger_spencer` colours in batches:
  * each batch runs independent copies of the library's trimmed Rödl nibble, written as a
    function of independent per-vertex coins whose effect at a vertex depends only on a bounded
    neighbourhood;
  * the Lovász Local Lemma, proved in `LLL.lean`, selects an outcome that lowers the maximum
    degree of the uncoloured hypergraph by almost the batch size;
  * when the maximum degree is at most `2τD`, the rest is coloured greedily.
* `chromatic_index_polynomial` applies Theorem 1.2 of Ehard–Glock–Joos to the auxiliary
  `(r + 1)`-uniform hypergraph whose edges are `{e} ∪ {(v, c) : v ∈ e}` for an edge `e` and a
  colour `c < ⌊D⌋`:
  * a matching of the auxiliary hypergraph is a partial proper colouring;
  * one weight function per vertex makes it colour almost all edges at every vertex;
  * the leftover, of small maximum degree, is coloured greedily.

No `sorry` and no `native_decide` is used; the only axioms are `propext`, `Classical.choice`
and `Quot.sound`.

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the audited statements. It imports
  only Mathlib.
- [`Solution.lean`](Solution.lean) and [`PseudorandomLib/`](PseudorandomLib): the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## Sources

* N. Pippenger, J. Spencer, *Asymptotic behavior of the chromatic index for hypergraphs*,
  J. Combin. Theory Ser. A 51 (1989) 24–42, doi:10.1016/0097-3165(89)90074-5.
* S. Ehard, S. Glock, F. Joos, *Pseudorandom hypergraph matchings*, Combin. Probab. Comput. 29
  (2020) 868–885, doi:10.1017/S0963548320000280.

## Authorship and use of AI

The author chose the result and directed the work. The proofs were produced by Harmonic's
Aristotle from formal statements and a suggested proof route, on top of the author's
Ehard–Glock–Joos library. Claude (Claude Code) wrote the statements, audited the return,
built it locally and prepared this package. Lean checks everything mechanically. See
`formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
