/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.FiniteProb

/-! # A Bernstein-type bounded-differences inequality on finite product spaces

Let `f` be a function of independent coordinates. Suppose that changing coordinate `i`
changes `f` by at most `c i ≤ L`, and that coordinate `i` only matters through a set `R i`
of "rare" values: changing coordinate `i` between two values outside `R i` does not change
`f`. If `R i` has probability at most `q i`, then with `V = ∑ i, q i * c i ^ 2`

  `P(f - E f ≥ t) ≤ exp(-t² / (2 (V + L t)))`.

Taking `R i = univ`, `q i = 1` gives a McDiarmid-type inequality; taking two-point
coordinates gives a Chernoff-type inequality. Everything is proved from scratch: the
one-coordinate exponential bound comes from the exponential series, and it is iterated along
the coordinates (an exposure martingale written as a recursion).
-/

@[expose] public section

namespace Pseudorandom

open Finset

open Nat in
/-- `e^x ≤ 1 + x + x²/(2(1-r))` whenever `|x| ≤ r < 1`. -/
theorem exp_le_one_add_add_sq_div (x r : ℝ) (hx : |x| ≤ r) (hr : r < 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - r)) := by
  have hE : HasSum (fun n : ℕ => x ^ n / (n ! : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  set a := |x| with ha
  have ha0 : 0 ≤ a := abs_nonneg x
  have ha1 : a < 1 := lt_of_le_of_lt hx hr
  have hG : HasSum (fun n : ℕ => a ^ n) (1 - a)⁻¹ := hasSum_geometric_of_lt_one ha0 ha1
  have hG2 : HasSum (fun n : ℕ => a ^ (n + 2) / 2) (a ^ 2 * (1 - a)⁻¹ / 2) := by
    have := (hG.mul_left (a ^ 2)).div_const 2
    simpa [pow_add, mul_comm] using this
  have hE2 : HasSum (fun n : ℕ => x ^ (n + 2) / ((n + 2) ! : ℝ))
      (Real.exp x - ∑ i ∈ Finset.range 2, x ^ i / (i ! : ℝ)) :=
    (hasSum_nat_add_iff' 2).mpr hE
  have hle := hasSum_le (fun n => ?_) hE2 hG2
  · simp [Finset.sum_range_succ] at hle
    have h1 : a ^ 2 = x ^ 2 := by rw [ha, sq_abs]
    have h2 : a ^ 2 * (1 - a)⁻¹ / 2 ≤ x ^ 2 / (2 * (1 - r)) := by
      rw [h1, div_le_div_iff₀ (by norm_num) (by linarith), ← div_eq_mul_inv]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg x]
    linarith
  · have hf : (2 : ℝ) ≤ ((n + 2) ! : ℝ) := by
      have : 2 ≤ (n + 2) ! := by
        calc 2 = (2 : ℕ) ! := rfl
          _ ≤ (n + 2) ! := Nat.factorial_le (by omega)
      exact_mod_cast this
    have hxa : x ^ (n + 2) ≤ a ^ (n + 2) := by
      rw [ha, ← abs_pow]; exact le_abs_self _
    calc x ^ (n + 2) / ((n + 2) ! : ℝ) ≤ a ^ (n + 2) / ((n + 2) ! : ℝ) := by
          gcongr
      _ ≤ a ^ (n + 2) / 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hf

/-- One-coordinate exponential bound. -/
theorem coord_exp_bound {α : Type*} [Fintype α] (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (M : α → ℝ) (c L lam q : ℝ) (R : Finset α)
    (hgap : ∀ a b, |M a - M b| ≤ c) (hR : ∀ a b, a ∉ R → b ∉ R → M a = M b)
    (hq : ∑ a ∈ R, p a ≤ q) (hcL : c ≤ L) (hlam : 0 ≤ lam) (hlamL : lam * L < 1) :
    ∑ a, p a * Real.exp (lam * (M a - ∑ b, p b * M b)) ≤
      Real.exp (lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L))) := by
  classical
  set m := ∑ b, p b * M b with hm
  have hne : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hp1
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hgap (Classical.arbitrary _) (Classical.arbitrary _))
  have hY : ∀ a, |M a - m| ≤ c := by
    intro a
    have : M a - m = ∑ b, p b * (M a - M b) := by
      rw [hm]; simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hp1, one_mul]
    rw [this]
    calc |∑ b, p b * (M a - M b)| ≤ ∑ b, |p b * (M a - M b)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ b, p b * c := sum_le_sum fun b _ => by
          rw [abs_mul, abs_of_nonneg (hp0 b)]
          exact mul_le_mul_of_nonneg_left (hgap a b) (hp0 b)
      _ = c := by rw [← sum_mul, hp1, one_mul]
  have hK : 0 < 1 - lam * L := by linarith
  -- variance bound
  have hvar : ∑ a, p a * (M a - m) ^ 2 ≤ q * c ^ 2 := by
    have hdecomp : ∀ x : ℝ, ∑ a, p a * (M a - x) ^ 2 =
        ∑ a, p a * (M a - m) ^ 2 + (m - x) ^ 2 := by
      intro x
      have h0 : ∑ a, p a * (M a - m) = 0 := by
        simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hp1, one_mul, hm]; ring
      have : ∀ a, p a * (M a - x) ^ 2 =
          p a * (M a - m) ^ 2 + 2 * (m - x) * (p a * (M a - m)) + (m - x) ^ 2 * p a := by
        intro a; ring
      simp_rw [this]
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, h0, ← mul_sum, hp1]; ring
    by_cases hex : ∃ b0, b0 ∉ R
    · obtain ⟨b0, hb0⟩ := hex
      have := hdecomp (M b0)
      calc ∑ a, p a * (M a - m) ^ 2 ≤ ∑ a, p a * (M a - M b0) ^ 2 := by
            rw [this]; nlinarith [sq_nonneg (m - M b0)]
        _ ≤ ∑ a, if a ∈ R then p a * c ^ 2 else 0 := by
            refine sum_le_sum fun a _ => ?_
            split_ifs with ha
            · apply mul_le_mul_of_nonneg_left _ (hp0 a)
              have := hgap a b0
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
            · rw [hR a b0 ha hb0]; simp
        _ = (∑ a ∈ R, p a) * c ^ 2 := by
            rw [← sum_filter, sum_mul]; simp
        _ ≤ q * c ^ 2 := mul_le_mul_of_nonneg_right hq (sq_nonneg c)
    · push_neg at hex
      have hR1 : ∑ a ∈ R, p a = 1 := by
        rw [← hp1]; congr 1; ext a; simp [hex a]
      calc ∑ a, p a * (M a - m) ^ 2 ≤ ∑ a, p a * c ^ 2 := sum_le_sum fun a _ => by
            apply mul_le_mul_of_nonneg_left _ (hp0 a)
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hY a) 2
        _ = c ^ 2 := by rw [← sum_mul, hp1, one_mul]
        _ ≤ q * c ^ 2 := by
            have : 1 ≤ q := hR1 ▸ hq
            nlinarith [sq_nonneg c]
  have hpt : ∀ a, Real.exp (lam * (M a - m)) ≤
      1 + lam * (M a - m) + (lam * (M a - m)) ^ 2 / (2 * (1 - lam * L)) := by
    intro a
    apply exp_le_one_add_add_sq_div _ _ _ hlamL
    rw [abs_mul, abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_left ((hY a).trans hcL) hlam
  calc ∑ a, p a * Real.exp (lam * (M a - m))
      ≤ ∑ a, p a * (1 + lam * (M a - m) + (lam * (M a - m)) ^ 2 / (2 * (1 - lam * L))) :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpt a) (hp0 a)
    _ = 1 + lam * ∑ a, p a * (M a - m) +
          lam ^ 2 / (2 * (1 - lam * L)) * ∑ a, p a * (M a - m) ^ 2 := by
        have : ∀ a, p a * (1 + lam * (M a - m) + (lam * (M a - m)) ^ 2 / (2 * (1 - lam * L)))
            = p a + lam * (p a * (M a - m)) +
              lam ^ 2 / (2 * (1 - lam * L)) * (p a * (M a - m) ^ 2) := by
          intro a; ring
        simp_rw [this]
        rw [sum_add_distrib, sum_add_distrib, hp1, ← mul_sum, ← mul_sum]
    _ = 1 + lam ^ 2 / (2 * (1 - lam * L)) * ∑ a, p a * (M a - m) ^ 2 := by
        have h0 : ∑ a, p a * (M a - m) = 0 := by
          simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hp1, one_mul, hm]; ring
        rw [h0]; ring
    _ ≤ 1 + lam ^ 2 / (2 * (1 - lam * L)) * (q * c ^ 2) := by
        gcongr
    _ ≤ Real.exp (lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L))) := by
        have := Real.add_one_le_exp (lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L)))
        rw [div_mul_eq_mul_div] at *
        linarith

section Coord

variable {α : Type*}

/-- Bounded differences on coordinate `i`. -/
def CoordGap {ι : Type*} [DecidableEq ι] (f : (ι → α) → ℝ) (c : ι → ℝ) : Prop :=
  ∀ i ω a b, |f (Function.update ω i a) - f (Function.update ω i b)| ≤ c i

/-- Coordinate `i` only matters through the values in `R i`. -/
def CoordRare {ι : Type*} [DecidableEq ι] (f : (ι → α) → ℝ) (R : ι → Finset α) : Prop :=
  ∀ i ω a b, a ∉ R i → b ∉ R i → f (Function.update ω i a) = f (Function.update ω i b)

theorem CoordGap.tail {n : ℕ} {f : (Fin (n + 1) → α) → ℝ} {c : Fin (n + 1) → ℝ}
    (h : CoordGap f c) (b : α) :
    CoordGap (fun ω => f (Fin.cons b ω)) (fun i => c i.succ) := by
  intro i ω a a'
  have := h i.succ (Fin.cons b ω) a a'
  simpa [← Fin.cons_update] using this

theorem CoordRare.tail {n : ℕ} {f : (Fin (n + 1) → α) → ℝ} {R : Fin (n + 1) → Finset α}
    (h : CoordRare f R) (b : α) :
    CoordRare (fun ω => f (Fin.cons b ω)) (fun i => R i.succ) := by
  intro i ω a a' ha ha'
  have := h i.succ (Fin.cons b ω) a a' ha ha'
  simpa [← Fin.cons_update] using this

theorem CoordGap.neg {ι : Type*} [DecidableEq ι] {f : (ι → α) → ℝ} {c : ι → ℝ}
    (h : CoordGap f c) : CoordGap (fun ω => -f ω) c := by
  intro i ω a b
  have := h i ω a b
  rw [← abs_neg]; convert this using 2; ring

theorem CoordRare.neg {ι : Type*} [DecidableEq ι] {f : (ι → α) → ℝ} {R : ι → Finset α}
    (h : CoordRare f R) : CoordRare (fun ω => -f ω) R := by
  intro i ω a b ha hb
  simp [h i ω a b ha hb]

end Coord

/-! ## The recursive (exposure) form of the product expectation -/

section Rec

variable {α : Type*} [Fintype α]

/-- The product expectation computed coordinate by coordinate. -/
def rmean : {n : ℕ} → (Fin n → α → ℝ) → ((Fin n → α) → ℝ) → ℝ
  | 0, _, f => f Fin.elim0
  | _ + 1, P, f => ∑ a, P 0 a * rmean (fun i => P i.succ) (fun ω => f (Fin.cons a ω))

theorem rmean_eq_pE : ∀ {n : ℕ} (P : Fin n → α → ℝ) (f : (Fin n → α) → ℝ),
    rmean P f = pE P f
  | 0, P, f => by
    simp only [rmean, pE, pw, univ_eq_empty, prod_empty, one_mul]
    rw [Fintype.sum_unique]
    congr 1
  | n + 1, P, f => by
    simp only [rmean]
    simp_rw [rmean_eq_pE]
    unfold pE
    rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => α) (fun x => pw P (Fin.cons x.1 x.2) *
      f (Fin.cons x.1 x.2)) _ (fun x => rfl)]
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun ω _ => ?_
    simp only [pw, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    ring

theorem IsPMF.tail {n : ℕ} {P : Fin (n + 1) → α → ℝ} (hP : IsPMF P) :
    IsPMF (fun i : Fin n => P i.succ) :=
  ⟨fun _ a => hP.1 _ a, fun _ => hP.2 _⟩

/-- Exponential moment bound for the centered function. -/
theorem rmean_mgf_le : ∀ {n : ℕ} (P : Fin n → α → ℝ) (_hP : IsPMF P)
    (f : (Fin n → α) → ℝ) (c q : Fin n → ℝ) (R : Fin n → Finset α) (L lam : ℝ)
    (_hcL : ∀ i, c i ≤ L) (_hf : CoordGap f c) (_hfR : CoordRare f R)
    (_hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (_hlam : 0 ≤ lam) (_hlamL : lam * L < 1),
    rmean P (fun ω => Real.exp (lam * (f ω - rmean P f))) ≤
      Real.exp (lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L)))
  | 0, P, _, f, c, q, R, L, lam, _, _, _, _, _, _ => by
    simp [rmean]
  | n + 1, P, hP, f, c, q, R, L, lam, hcL, hf, hfR, hq, hlam, hlamL => by
    set P' : Fin n → α → ℝ := fun i => P i.succ
    set M : α → ℝ := fun b => rmean P' (fun ω => f (Fin.cons b ω)) with hM
    have hmean : rmean P f = ∑ a, P 0 a * M a := rfl
    set K := 2 * (1 - lam * L)
    set V' := ∑ i : Fin n, q i.succ * (c i.succ) ^ 2
    have hstep : ∀ b, rmean P' (fun ω => Real.exp (lam * (f (Fin.cons b ω) -
        rmean P f))) ≤ Real.exp (lam * (M b - rmean P f)) *
          Real.exp (lam ^ 2 * V' / K) := by
      intro b
      have hsplit : (fun ω => Real.exp (lam * (f (Fin.cons b ω) - rmean P f))) =
          fun ω => Real.exp (lam * (M b - rmean P f)) *
            Real.exp (lam * (f (Fin.cons b ω) - M b)) := by
        funext ω
        rw [← Real.exp_add]
        ring_nf
      rw [hsplit, rmean_eq_pE, pE_const_mul, ← rmean_eq_pE]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact rmean_mgf_le P' hP.tail _ (fun i => c i.succ) (fun i => q i.succ)
        (fun i => R i.succ) L lam (fun i => hcL i.succ) (hf.tail b) (hfR.tail b)
        (fun i => hq i.succ) hlam hlamL
    have hgap : ∀ a b, |M a - M b| ≤ c 0 := by
      intro a b
      simp only [hM]
      rw [rmean_eq_pE, rmean_eq_pE, ← pE_sub]
      have hb : ∀ ω, |f (Fin.cons a ω) - f (Fin.cons b ω)| ≤ c 0 := by
        intro ω
        have := hf 0 (Fin.cons a ω) a b
        simpa [Fin.update_cons_zero] using this
      rw [abs_le]
      constructor
      · have := pE_mono hP.tail (f := fun _ => -c 0)
          (g := fun ω => f (Fin.cons a ω) - f (Fin.cons b ω))
          (fun ω => (abs_le.mp (hb ω)).1)
        rwa [pE_const hP.tail] at this
      · have := pE_mono hP.tail (g := fun _ => c 0)
          (f := fun ω => f (Fin.cons a ω) - f (Fin.cons b ω))
          (fun ω => (abs_le.mp (hb ω)).2)
        rwa [pE_const hP.tail] at this
    have hRM : ∀ a b, a ∉ R 0 → b ∉ R 0 → M a = M b := by
      intro a b ha hb
      simp only [hM]
      congr 1; funext ω
      have := hfR 0 (Fin.cons a ω) a b ha hb
      simpa [Fin.update_cons_zero] using this
    calc rmean P (fun ω => Real.exp (lam * (f ω - rmean P f)))
        = ∑ a, P 0 a * rmean P' (fun ω => Real.exp (lam *
            (f (Fin.cons a ω) - rmean P f))) := rfl
      _ ≤ ∑ a, P 0 a * (Real.exp (lam * (M a - rmean P f)) *
            Real.exp (lam ^ 2 * V' / K)) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hstep a) (hP.1 0 a)
      _ = (∑ a, P 0 a * Real.exp (lam * (M a - ∑ b, P 0 b * M b))) *
            Real.exp (lam ^ 2 * V' / K) := by
          rw [sum_mul, hmean]; congr 1; funext a; ring
      _ ≤ Real.exp (lam ^ 2 * (q 0 * c 0 ^ 2) / K) * Real.exp (lam ^ 2 * V' / K) := by
          gcongr
          exact coord_exp_bound (P 0) (hP.1 0) (hP.2 0) M (c 0) L lam (q 0) (R 0) hgap hRM
            (hq 0) (hcL 0) hlam hlamL
      _ = _ := by
          rw [← Real.exp_add, Fin.sum_univ_succ]
          congr 1
          simp only [K, V']
          ring

end Rec

/-! ## The tail bounds -/

section Tail

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem pE_tail_le_of_lam_fin {n : ℕ} (P : Fin n → α → ℝ) (hP : IsPMF P)
    (f : (Fin n → α) → ℝ) (c q : Fin n → ℝ) (R : Fin n → Finset α) (L lam t : ℝ)
    (hcL : ∀ i, c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (hlam : 0 ≤ lam) (hlamL : lam * L < 1) :
    pProb P (fun ω => t ≤ f ω - pE P f) ≤
      Real.exp (-(lam * t) + lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L))) := by
  classical
  have hind : ∀ ω, (if t ≤ f ω - pE P f then (1 : ℝ) else 0) ≤
      Real.exp (-(lam * t)) * Real.exp (lam * (f ω - pE P f)) := by
    intro ω
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp
      nlinarith
    · exact (Real.exp_pos _).le
  unfold pProb
  calc _ ≤ pE P (fun ω => Real.exp (-(lam * t)) *
        Real.exp (lam * (f ω - pE P f))) := pE_mono hP hind
    _ = Real.exp (-(lam * t)) * pE P (fun ω => Real.exp (lam * (f ω - pE P f))) :=
        pE_const_mul _ _
    _ ≤ Real.exp (-(lam * t)) *
          Real.exp (lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L))) := by
        gcongr
        have := rmean_mgf_le P hP f c q R L lam hcL hf hfR hq hlam hlamL
        simp only [rmean_eq_pE] at this
        exact this
    _ = _ := (Real.exp_add _ _).symm

theorem pE_upper_tail_fin {n : ℕ} (P : Fin n → α → ℝ) (hP : IsPMF P)
    (f : (Fin n → α) → ℝ) (c q : Fin n → ℝ) (R : Fin n → Finset α) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ f ω - pE P f) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by
  set V := ∑ i, q i * c i ^ 2 with hVdef
  have hq0 : ∀ i, 0 ≤ q i := fun i => (sum_nonneg fun a _ => hP.1 i a).trans (hq i)
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun i _ => mul_nonneg (hq0 i) (sq_nonneg _)
  have hcL : ∀ i, c i ≤ L := fun i => (hc i).2
  rcases hV0.lt_or_eq with hV | hV
  · have hD : 0 < V + L * t := by positivity
    set lam := t / (V + L * t)
    have hlam : 0 ≤ lam := by positivity
    have hlamL : lam * L < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hD]; nlinarith
    refine (pE_tail_le_of_lam_fin P hP f c q R L lam t hcL hf hfR hq hlam hlamL).trans
      (le_of_eq (congrArg Real.exp ?_))
    have h1 : 1 - lam * L = V / (V + L * t) := by
      simp only [lam]; field_simp; ring
    rw [h1]
    simp only [lam]
    field_simp
    ring
  · have hlamL : 1 / (2 * L) * L < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
    refine (pE_tail_le_of_lam_fin P hP f c q R L (1 / (2 * L)) t hcL hf hfR hq
      (by positivity) hlamL).trans (le_of_eq (congrArg Real.exp ?_))
    rw [← hVdef, ← hV]
    field_simp
    ring

/-- **Bernstein-type bounded differences, upper tail**, on a product space over any
finite index type. -/
theorem pE_upper_tail (P : ι → α → ℝ) (hP : IsPMF P)
    (f : (ι → α) → ℝ) (c q : ι → ℝ) (R : ι → Finset α) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ f ω - pE P f) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by
  set e := Fintype.equivFin ι
  rw [pProb_equiv e, pE_equiv e]
  have hP' : IsPMF (fun j => P (e.symm j)) := ⟨fun j a => hP.1 _ a, fun j => hP.2 _⟩
  have hV : ∑ i, q i * c i ^ 2 = ∑ j, q (e.symm j) * c (e.symm j) ^ 2 :=
    (Fintype.sum_equiv e.symm _ _ (fun j => rfl)).symm
  rw [hV]
  apply pE_upper_tail_fin _ hP' (fun ω' => f (ω' ∘ e)) (fun j => c (e.symm j))
    (fun j => q (e.symm j)) (fun j => R (e.symm j)) L hL (fun j => hc _) _ _
    (fun j => hq _) t ht
  · intro j ω' a b
    have := hf (e.symm j) (ω' ∘ e) a b
    simpa [Function.update_comp_equiv] using this
  · intro j ω' a b ha hb
    have := hfR (e.symm j) (ω' ∘ e) a b ha hb
    simpa [Function.update_comp_equiv] using this

/-- **Bernstein-type bounded differences, lower tail.** -/
theorem pE_lower_tail (P : ι → α → ℝ) (hP : IsPMF P)
    (f : (ι → α) → ℝ) (c q : ι → ℝ) (R : ι → Finset α) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ pE P f - f ω) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by
  have h := pE_upper_tail P hP (fun ω => -f ω) c q R L hL hc hf.neg hfR.neg hq t ht
  rw [pE_neg] at h
  convert h using 3
  constructor <;> intro h' <;> linarith

end Tail

end Pseudorandom
