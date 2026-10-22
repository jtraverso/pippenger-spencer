/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Cylinder
public import PseudorandomLib.Counting

/-! # Step 1: a random vertex partition

Colour every vertex uniformly at random with one of `p` colours and let `H_i` be the set of
edges all of whose vertices have colour `i`. With positive probability
* every vertex has degree at most `(1 + ξ) Δ / p^{r-1}` in every `H_i`, and
* every relevant weight function satisfies `ω(H_i) = (1 ± ξ) ω(H) / p^r` for every `i`.
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `H` all of whose vertices have colour `i`. -/
def part {p : ℕ} (H : Finset (Finset V)) (τ : V → Fin p) (i : Fin p) : Finset (Finset V) :=
  H.filter (fun e => ∀ v ∈ e, τ v = i)

theorem part_subset {p : ℕ} (H : Finset (Finset V)) (τ : V → Fin p) (i : Fin p) :
    part H τ i ⊆ H := filter_subset _ _

/-! ## Degrees -/

/-- Number of edges at `x` whose other vertices all have colour `i`. -/
noncomputable def degCyl {p : ℕ} (H : Finset (Finset V)) (x : V) (i : Fin p) (τ : V → Fin p) :
    ℝ :=
  cyl (H.filter (fun e => x ∈ e)) (fun _ => 1) (fun e => e.erase x) i τ

theorem degree_part_le_degCyl {p : ℕ} (H : Finset (Finset V)) (x : V) (i : Fin p)
    (τ : V → Fin p) : (degree (part H τ i) x : ℝ) ≤ degCyl H x i τ := by
  classical
  unfold degree part degCyl cyl
  rw [filter_filter]
  have : ((H.filter (fun e => (∀ v ∈ e, τ v = i) ∧ x ∈ e)).card : ℝ) =
      ∑ e ∈ H.filter (fun e => x ∈ e), (if ∀ v ∈ e, τ v = i then (1 : ℝ) else 0) := by
    rw [← sum_boole, sum_filter]
    refine sum_congr rfl fun e _ => ?_
    by_cases hx : x ∈ e <;> simp [hx]
  rw [this]
  refine sum_le_sum fun e _ => ?_
  rw [one_mul]
  split_ifs with h1 h2 h2 <;> try norm_num
  exact absurd (fun v hv => h1 v (mem_of_mem_erase hv)) h2

theorem pE_degCyl {p : ℕ} (hp : 0 < p) (H : Finset (Finset V)) (r : ℕ) (huni : IsUniform H r)
    (x : V) (i : Fin p) :
    pE (unif V p) (degCyl H x i) = degree H x * (1 / (p : ℝ)) ^ (r - 1) := by
  unfold degCyl
  rw [cyl_pE hp]
  have : ∀ e ∈ H.filter (fun e => x ∈ e), (1 : ℝ) * (1 / (p : ℝ)) ^ (e.erase x).card =
      (1 / (p : ℝ)) ^ (r - 1) := by
    intro e he
    rw [mem_filter] at he
    rw [card_erase_of_mem he.2, huni e he.1, one_mul]
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul]
  rfl

omit [Fintype V] in
theorem degCyl_gap_le (H : Finset (Finset V)) (x : V) (C : ℝ) (hC : 0 ≤ C)
    (hcod : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ C) (v : V) :
    cylGap (ι := V) (H.filter (fun e => x ∈ e)) (fun _ => (1 : ℝ)) (fun e => e.erase x) v ≤ C := by
  classical
  unfold cylGap
  rw [sum_const, nsmul_eq_mul, mul_one]
  by_cases hv : v = x
  · subst hv
    have : (H.filter (fun e => v ∈ e)).filter (fun e => v ∈ e.erase v) = ∅ := by
      ext e; simp
    rw [this]; simpa using hC
  · refine le_trans ?_ (hcod x v (Ne.symm hv))
    have hsub : (H.filter (fun e => x ∈ e)).filter (fun e => v ∈ e.erase x) ⊆
        H.filter (fun e => x ∈ e ∧ v ∈ e) := by
      intro e he
      simp only [mem_filter, mem_erase] at he ⊢
      exact ⟨he.1.1, he.1.2, he.2.2⟩
    unfold codegree
    exact_mod_cast card_le_card hsub

/-- Tail bound for the degrees. -/
theorem degCyl_tail {p : ℕ} (hp : 0 < p) (H : Finset (Finset V)) (r : ℕ) (hr : 1 ≤ r)
    (huni : IsUniform H r) (Δ C ξ : ℝ) (hΔ : 0 < Δ) (hC : 0 < C) (hξ : 0 < ξ)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) (hcod : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ C)
    (x : V) (i : Fin p) :
    pProb (unif V p) (fun τ => ξ * Δ / (p : ℝ) ^ (r - 1) ≤
        degCyl H x i τ - pE (unif V p) (degCyl H x i)) ≤
      Real.exp (-(ξ ^ 2 * Δ / (2 * C * (r * ((p : ℝ) ^ (r - 1)) ^ 2 / p + ξ * (p : ℝ) ^ (r - 1))))) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hP : (0 : ℝ) < (p : ℝ) ^ (r - 1) := by positivity
  have hWt : ∑ e ∈ H.filter (fun e => x ∈ e), (1 : ℝ) * (e.erase x).card ≤ r * Δ := by
    have : ∀ e ∈ H.filter (fun e => x ∈ e), (1 : ℝ) * (e.erase x).card ≤ r := by
      intro e he
      rw [mem_filter] at he
      rw [card_erase_of_mem he.2, huni e he.1, one_mul]
      exact_mod_cast Nat.sub_le r 1
    refine (sum_le_sum this).trans ?_
    rw [sum_const, nsmul_eq_mul, mul_comm]
    have : ((H.filter (fun e => x ∈ e)).card : ℝ) ≤ Δ := hdeg x
    have : (0 : ℝ) ≤ r := by positivity
    nlinarith
  have h := cyl_upper (ι := V) hp (H.filter (fun e => x ∈ e)) (fun _ => (1 : ℝ))
    (fun _ _ => zero_le_one) (fun e => e.erase x) i C (r * Δ) hC
    (degCyl_gap_le H x C hC.le hcod) hWt (ξ * Δ / (p : ℝ) ^ (r - 1)) (by positivity)
  refine h.trans (le_of_eq ?_)
  congr 2
  field_simp

/-! ## Weights -/

theorem weight_part_eq_cyl {p : ℕ} (H : Finset (Finset V)) (w : Finset V → ℝ) (i : Fin p)
    (τ : V → Fin p) : weight w (part H τ i) = cyl H w id i τ := by
  classical
  unfold weight part cyl
  rw [sum_filter]
  refine sum_congr rfl fun e _ => ?_
  simp only [id]
  split_ifs <;> simp

theorem pE_weight_cyl {p : ℕ} (hp : 0 < p) (H : Finset (Finset V)) (r : ℕ)
    (huni : IsUniform H r) (w : Finset V → ℝ) (i : Fin p) :
    pE (unif V p) (cyl H w id i) = weight w H * (1 / (p : ℝ)) ^ r := by
  rw [cyl_pE hp, weight, sum_mul]
  refine sum_congr rfl fun e he => ?_
  simp [huni e he]

omit [Fintype V] in
theorem weight_gap_le (H : Finset (Finset V)) (Δ : ℝ)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) (w : Finset V → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hw : ∀ e ∈ H, w e ≤ m) (v : V) : cylGap (ι := V) H w id v ≤ Δ * m := by
  unfold cylGap
  calc ∑ e ∈ H.filter (fun e => v ∈ id e), w e ≤ ∑ e ∈ H.filter (fun e => v ∈ id e), m :=
        sum_le_sum fun e he => hw e (mem_filter.mp he).1
    _ = (degree H v : ℝ) * m := by rw [sum_const, nsmul_eq_mul]; rfl
    _ ≤ Δ * m := mul_le_mul_of_nonneg_right (hdeg v) hm

/-- Tail bounds for the weights (both directions at once). -/
theorem weight_cyl_tail {p : ℕ} (hp : 0 < p) (H : Finset (Finset V)) (r : ℕ)
    (huni : IsUniform H r) (Δ η ξ : ℝ) (hΔ : 0 < Δ) (hη : 0 < η) (hξ : 0 < ξ)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) (w : Finset V → ℝ) (hw0 : ∀ e ∈ H, 0 ≤ w e)
    (hwpos : 0 < weight w H) (hwmax : ∀ e ∈ H, w e ≤ η * weight w H) (i : Fin p) :
    pProb (unif V p) (fun τ => ξ * (weight w H / (p : ℝ) ^ r) ≤
        cyl H w id i τ - pE (unif V p) (cyl H w id i)) ≤
      Real.exp (-(ξ ^ 2 / (2 * Δ * η * (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r)))) ∧
    pProb (unif V p) (fun τ => ξ * (weight w H / (p : ℝ) ^ r) ≤
        pE (unif V p) (cyl H w id i) - cyl H w id i τ) ≤
      Real.exp (-(ξ ^ 2 / (2 * Δ * η * (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r)))) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  set ω := weight w H with hω
  have hL0 : 0 < Δ * (η * ω) := by positivity
  have hWt : ∑ e ∈ H, w e * (id e).card ≤ r * ω := by
    rw [hω, weight, mul_sum]
    exact le_of_eq (sum_congr rfl fun e he => by simp [huni e he, mul_comm])
  have hgap := weight_gap_le H Δ hdeg w (η * ω) (by positivity) hwmax
  have ht : 0 < ξ * (ω / (p : ℝ) ^ r) := by positivity
  have heq : (ξ * (ω / (p : ℝ) ^ r)) ^ 2 / (2 * (Δ * (η * ω) * (r * ω) / p +
      Δ * (η * ω) * (ξ * (ω / (p : ℝ) ^ r)))) =
      ξ ^ 2 / (2 * Δ * η * (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r)) := by
    field_simp
  constructor
  · have h := cyl_upper (ι := V) hp H w hw0 id i (Δ * (η * ω)) (r * ω) hL0 hgap hWt _ ht
    rwa [heq] at h
  · have h := cyl_lower (ι := V) hp H w hw0 id i (Δ * (η * ω)) (r * ω) hL0 hgap hWt _ ht
    rwa [heq] at h

/-! ## Existence of a good vertex partition -/

omit [Fintype V] in
theorem degree_eq_zero_of_not_mem_biUnion (A H : Finset (Finset V)) (hA : A ⊆ H) {x : V}
    (hx : x ∉ H.biUnion id) : degree A x = 0 := by
  unfold degree
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hxe
  exact hx (mem_biUnion.mpr ⟨e, hA he, hxe⟩)

/-- **Step 1.** A random vertex partition is good with positive probability; an additional bad
event `Bad` of probability at most `πB` can be avoided at the same time. -/
theorem vertex_partition_ext {p : ℕ} (hp : 0 < p) (H : Finset (Finset V)) (r : ℕ) (hr : 1 ≤ r)
    (huni : IsUniform H r) (Δ C η ξ : ℝ) (hΔ : 0 < Δ) (hC : 0 < C) (hη : 0 < η) (hξ : 0 < ξ)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) (hcod : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ C)
    {ι : Type*} (W : ι → Finset V → ℝ) (K : Finset ι)
    (hW0 : ∀ k ∈ K, ∀ e ∈ H, 0 ≤ W k e) (hWpos : ∀ k ∈ K, 0 < weight (W k) H)
    (hWmax : ∀ k ∈ K, ∀ e ∈ H, W k e ≤ η * weight (W k) H)
    (Bad : (V → Fin p) → Prop) (πB : ℝ) (hBad : pProb (unif V p) Bad ≤ πB)
    (hfail : ((H.biUnion id).card * p : ℝ) * Real.exp (-(ξ ^ 2 * Δ /
        (2 * C * (r * ((p : ℝ) ^ (r - 1)) ^ 2 / p + ξ * (p : ℝ) ^ (r - 1))))) +
      (2 * K.card * p : ℝ) * Real.exp (-(ξ ^ 2 /
        (2 * Δ * η * (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r)))) + πB < 1) :
    ∃ τ : V → Fin p, (∀ x i, (degree (part H τ i) x : ℝ) ≤ (1 + ξ) * Δ / (p : ℝ) ^ (r - 1)) ∧
      (∀ k ∈ K, ∀ i, |weight (W k) (part H τ i) - weight (W k) H / (p : ℝ) ^ r| ≤
        ξ * (weight (W k) H / (p : ℝ) ^ r)) ∧ ¬ Bad τ := by
  classical
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hP := unif_isPMF (ι := V) p hp
  set U := H.biUnion id with hU
  set E2 := ξ ^ 2 * Δ / (2 * C * (r * ((p : ℝ) ^ (r - 1)) ^ 2 / p + ξ * (p : ℝ) ^ (r - 1)))
  set E1 := ξ ^ 2 / (2 * Δ * η * (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r))
  set bad1 : (V → Fin p) → Prop := fun τ => ∃ xi ∈ U ×ˢ (univ : Finset (Fin p)),
    ξ * Δ / (p : ℝ) ^ (r - 1) ≤ degCyl H xi.1 xi.2 τ - pE (unif V p) (degCyl H xi.1 xi.2)
  set bad2 : (V → Fin p) → Prop := fun τ => ∃ ki ∈ K ×ˢ (univ : Finset (Fin p)),
    ξ * (weight (W ki.1) H / (p : ℝ) ^ r) ≤
      cyl H (W ki.1) id ki.2 τ - pE (unif V p) (cyl H (W ki.1) id ki.2)
  set bad3 : (V → Fin p) → Prop := fun τ => ∃ ki ∈ K ×ˢ (univ : Finset (Fin p)),
    ξ * (weight (W ki.1) H / (p : ℝ) ^ r) ≤
      pE (unif V p) (cyl H (W ki.1) id ki.2) - cyl H (W ki.1) id ki.2 τ
  have h1 : pProb (unif V p) bad1 ≤ (U.card * p : ℝ) * Real.exp (-E2) := by
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum fun xi _ => degCyl_tail hp H r hr huni Δ C ξ hΔ hC hξ hdeg hcod
      xi.1 xi.2).trans (le_of_eq ?_)
    rw [sum_const, card_product, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have h2 : pProb (unif V p) bad2 ≤ (K.card * p : ℝ) * Real.exp (-E1) := by
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum fun ki hki => (weight_cyl_tail hp H r huni Δ η ξ hΔ hη hξ hdeg (W ki.1)
      (hW0 _ (mem_product.mp hki).1) (hWpos _ (mem_product.mp hki).1)
      (hWmax _ (mem_product.mp hki).1) ki.2).1).trans (le_of_eq ?_)
    rw [sum_const, card_product, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have h3 : pProb (unif V p) bad3 ≤ (K.card * p : ℝ) * Real.exp (-E1) := by
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum fun ki hki => (weight_cyl_tail hp H r huni Δ η ξ hΔ hη hξ hdeg (W ki.1)
      (hW0 _ (mem_product.mp hki).1) (hWpos _ (mem_product.mp hki).1)
      (hWmax _ (mem_product.mp hki).1) ki.2).2).trans (le_of_eq ?_)
    rw [sum_const, card_product, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hall : pProb (unif V p) (fun τ => bad1 τ ∨ bad2 τ ∨ bad3 τ ∨ Bad τ) < 1 := by
    have := pProb_or_le hP bad1 (fun τ => bad2 τ ∨ bad3 τ ∨ Bad τ)
    have := pProb_or_le hP bad2 (fun τ => bad3 τ ∨ Bad τ)
    have := pProb_or_le hP bad3 Bad
    linarith
  obtain ⟨τ, _, hτ⟩ := exists_of_pProb_lt_one hP hall
  simp only [not_or] at hτ
  obtain ⟨n1, n2, n3, n4⟩ := hτ
  refine ⟨τ, fun x i => ?_, fun k hk i => ?_, n4⟩
  · have hrhs : 0 ≤ (1 + ξ) * Δ / (p : ℝ) ^ (r - 1) := by positivity
    by_cases hx : x ∈ U
    · have hn : ¬ (ξ * Δ / (p : ℝ) ^ (r - 1) ≤
          degCyl H x i τ - pE (unif V p) (degCyl H x i)) :=
        fun h => n1 ⟨(x, i), mem_product.mpr ⟨hx, mem_univ _⟩, h⟩
      push_neg at hn
      rw [pE_degCyl hp H r huni x i, one_div_pow] at hn
      have hd := degree_part_le_degCyl H x i τ
      have : (degree H x : ℝ) * (1 / (p : ℝ) ^ (r - 1)) ≤ Δ * (1 / (p : ℝ) ^ (r - 1)) :=
        mul_le_mul_of_nonneg_right (hdeg x) (by positivity)
      have e : (1 + ξ) * Δ / (p : ℝ) ^ (r - 1) =
          Δ * (1 / (p : ℝ) ^ (r - 1)) + ξ * Δ / (p : ℝ) ^ (r - 1) := by ring
      rw [e]; linarith
    · rw [degree_eq_zero_of_not_mem_biUnion _ H (part_subset H τ i) hx]
      simpa using hrhs
  · have hn2 : ¬ (ξ * (weight (W k) H / (p : ℝ) ^ r) ≤
        cyl H (W k) id i τ - pE (unif V p) (cyl H (W k) id i)) :=
      fun h => n2 ⟨(k, i), mem_product.mpr ⟨hk, mem_univ _⟩, h⟩
    have hn3 : ¬ (ξ * (weight (W k) H / (p : ℝ) ^ r) ≤
        pE (unif V p) (cyl H (W k) id i) - cyl H (W k) id i τ) :=
      fun h => n3 ⟨(k, i), mem_product.mpr ⟨hk, mem_univ _⟩, h⟩
    push_neg at hn2 hn3
    rw [pE_weight_cyl hp H r huni, one_div_pow, ← div_eq_mul_one_div] at hn2 hn3
    rw [weight_part_eq_cyl, abs_le]
    constructor <;> linarith

/-- **Step 1.** A random vertex partition is good with positive probability. -/
theorem vertex_partition {p : ℕ} (hp : 0 < p) (H : Finset (Finset V)) (r : ℕ) (hr : 1 ≤ r)
    (huni : IsUniform H r) (Δ C η ξ : ℝ) (hΔ : 0 < Δ) (hC : 0 < C) (hη : 0 < η) (hξ : 0 < ξ)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) (hcod : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ C)
    {ι : Type*} (W : ι → Finset V → ℝ) (K : Finset ι)
    (hW0 : ∀ k ∈ K, ∀ e ∈ H, 0 ≤ W k e) (hWpos : ∀ k ∈ K, 0 < weight (W k) H)
    (hWmax : ∀ k ∈ K, ∀ e ∈ H, W k e ≤ η * weight (W k) H)
    (hfail : ((H.biUnion id).card * p : ℝ) * Real.exp (-(ξ ^ 2 * Δ /
        (2 * C * (r * ((p : ℝ) ^ (r - 1)) ^ 2 / p + ξ * (p : ℝ) ^ (r - 1))))) +
      (2 * K.card * p : ℝ) * Real.exp (-(ξ ^ 2 /
        (2 * Δ * η * (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r)))) < 1) :
    ∃ τ : V → Fin p, (∀ x i, (degree (part H τ i) x : ℝ) ≤ (1 + ξ) * Δ / (p : ℝ) ^ (r - 1)) ∧
      ∀ k ∈ K, ∀ i, |weight (W k) (part H τ i) - weight (W k) H / (p : ℝ) ^ r| ≤
        ξ * (weight (W k) H / (p : ℝ) ^ r) := by
  classical
  obtain ⟨τ, h1, h2, -⟩ := vertex_partition_ext hp H r hr huni Δ C η ξ hΔ hC hη hξ hdeg hcod W K
    hW0 hWpos hWmax (fun _ => False) 0 (by unfold pProb pE; simp) (by linarith)
  exact ⟨τ, h1, h2⟩

end Pseudorandom
