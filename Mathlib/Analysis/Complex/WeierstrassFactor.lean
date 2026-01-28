/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Power bound for Weierstrass elementary factors

This file defines the Weierstrass elementary factors
`E_m(z) = (1 - z) * exp (∑_{k=1}^m z^k / k)` (implemented as `Complex.weierstrassFactor`) and proves
quantitative bounds used in Hadamard/Weierstrass factorization.

The key estimate is a fixed-constant, sequence-friendly bound:

`‖E_m(z) - 1‖ ≤ 4 * ‖z‖^(m+1)` for `‖z‖ ≤ 1 / 2`.

## Main definitions

- `Complex.partialLogSum m z`: the partial sum `∑_{k=1}^m z^k / k`
- `Complex.logTail m z`: the tail `∑_{k>m} z^k / k` (as a `tsum` starting at `m+1`)
- `Complex.weierstrassFactor m z`: the elementary factor
  `E_m(z) = (1 - z) * exp (partialLogSum m z)`

## Main results

- `Complex.weierstrassFactor_sub_one_pow_bound`: the power bound `‖E_m(z) - 1‖ ≤ 4‖z‖^(m+1)` for
  `‖z‖ ≤ 1 / 2`
- `Complex.weierstrassFactor_eq_exp_neg_tail`: representation of `E_m` as `exp (- logTail m z)` on
  `‖z‖ < 1`

On the domain `‖z‖ < 1`, we use the principal branch `Complex.log` via the standard Taylor series
lemma for `-log (1 - z)`.
-/

noncomputable section

@[expose] public section

open Real Set Filter Topology
open scoped BigOperators Topology

namespace Complex

/-! ## Partial logarithm series -/

/-- The partial sum `∑_{k=1}^m z^k / k` (written with a `Finset.range` index shift). -/
def partialLogSum (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1)

/-- `partialLogSum 0 z = 0`. -/
@[simp]
lemma partialLogSum_zero (z : ℂ) : partialLogSum 0 z = 0 := by
  simp [partialLogSum]

/-- The first partial sum is `partialLogSum 1 z = z`. -/
@[simp]
lemma partialLogSum_one (z : ℂ) : partialLogSum 1 z = z := by
  simp [partialLogSum]

/-- A recursion for `partialLogSum`. -/
lemma partialLogSum_succ (m : ℕ) (z : ℂ) :
    partialLogSum (m + 1) z = partialLogSum m z + z ^ (m + 1) / (m + 1) := by
  simp [partialLogSum, Finset.sum_range_succ]

/-- The tail `∑_{k>m} z^k / k`, written as `∑' k, z^(m+1+k)/(m+1+k)`. -/
def logTail (m : ℕ) (z : ℂ) : ℂ :=
  ∑' k, z ^ (m + 1 + k) / ((m + 1 + k : ℕ) : ℂ)

/-- For `‖z‖ < 1`, the power series for `-log (1 - z)`. -/
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' k : ℕ, z ^ (k + 1) / (k + 1) := by
  have h := hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]

/-- A convenient inequality: `-‖w‖ ≤ w.re`. -/
lemma neg_norm_le_re (w : ℂ) : (-‖w‖ : ℝ) ≤ w.re := by
  have habs : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  simpa using (neg_le_of_abs_le habs)

private lemma one_le_norm_natCast_add_one_add (m k : ℕ) :
    (1 : ℝ) ≤ ‖((m + 1 + k : ℕ) : ℂ)‖ := by
  have h1 : (1 : ℝ) ≤ (m + 1 + k : ℝ) := by
    have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
    nlinarith
  have hn : ‖((m + 1 + k : ℕ) : ℂ)‖ = (m + 1 + k : ℝ) := by
    simpa using (Complex.norm_natCast (m + 1 + k))
  rw [hn]
  exact h1

-- Small helper: dropping the nat denominator only increases the norm.
private lemma norm_pow_succ_div_le (z : ℂ) (k : ℕ) :
    ‖z ^ (k + 1) / (k + 1)‖ ≤ ‖z‖ ^ (k + 1) := by
  rw [norm_div, norm_pow]
  refine div_le_self (pow_nonneg (norm_nonneg z) _) ?_
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (one_le_norm_natCast_add_one_add 0 k)

/-- A crude bound on `‖partialLogSum m z‖` used in minimum-modulus arguments. -/
lemma norm_partialLogSum_le (m : ℕ) (z : ℂ) :
    ‖partialLogSum m z‖ ≤ (m : ℝ) * max 1 (‖z‖ ^ m) := by
  refine
      (show ‖partialLogSum m z‖ ≤ ∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ from by
        simpa [partialLogSum] using
          (norm_sum_le (Finset.range m) (fun k => z ^ (k + 1) / (k + 1)))).trans ?_
  calc
    (∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖)
        ≤ ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hk_le : k + 1 ≤ m := Nat.succ_le_iff.2 (Finset.mem_range.1 hk)
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          by_cases hz1 : ‖z‖ ≤ (1 : ℝ)
          · refine (norm_pow_succ_div_le z k).trans ?_
            exact (pow_le_one₀ hz0 hz1).trans (le_max_left _ _)
          · have hz1' : (1 : ℝ) ≤ ‖z‖ := le_of_not_ge hz1
            refine (norm_pow_succ_div_le z k).trans ?_
            exact (pow_le_pow_right₀ hz1' hk_le).trans (le_max_right _ _)
    _ = (m : ℝ) * max 1 (‖z‖ ^ m) := by
          simp [Finset.sum_const]

/-- The series defining `logTail m z` is summable for `‖z‖ < 1`. -/
lemma summable_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k : ℕ) : ℂ)) := by
  refine Summable.of_norm_bounded
      (g := fun k : ℕ => ‖z‖ ^ k)
      (summable_geometric_of_lt_one (norm_nonneg z) hz) ?_
  intro k
  rw [norm_div, norm_pow]
  calc
    ‖z‖ ^ (m + 1 + k) / ‖((m + 1 + k : ℕ) : ℂ)‖
        ≤ ‖z‖ ^ (m + 1 + k) := by
              exact div_le_self (pow_nonneg (norm_nonneg z) _)
                (one_le_norm_natCast_add_one_add m k)
    _ = ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) k)
          exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k := one_mul _

/-! A head/tail decomposition for `logTail` on `‖z‖ < 1`. -/
lemma logTail_eq_add_logTail_succ {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    logTail m z = z ^ (m + 1) / (m + 1) + logTail (m + 1) z := by
  let g : ℕ → ℂ := fun k => z ^ (m + 1 + k) / ((m + 1 + k : ℕ) : ℂ)
  have hg : Summable g := by
    simpa [g, div_eq_mul_inv] using (summable_logTail (z := z) hz m)
  have hsplit : logTail m z = (Finset.range 1).sum g + ∑' k : ℕ, g (k + 1) := by
    simpa [logTail, g] using (hg.sum_add_tsum_nat_add 1).symm
  have hsum : (Finset.range 1).sum g = z ^ (m + 1) / (m + 1) := by
    simp [g, Finset.range_one, Nat.add_comm, Nat.add_left_comm]
  have htail : (∑' k : ℕ, g (k + 1)) = logTail (m + 1) z := by
    unfold logTail g
    simp [Nat.cast_add, add_left_comm, add_comm]
  calc
    logTail m z
        = (Finset.range 1).sum g + ∑' k : ℕ, g (k + 1) := hsplit
    _ = z ^ (m + 1) / (m + 1) + logTail (m + 1) z := by
          simp_rw [hsum, htail]

/-- Decompose the full logarithm series into the partial sum plus `logTail`. -/
lemma tsum_pow_succ_div_eq_partialLogSum_add_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    (∑' k : ℕ, z ^ (k + 1) / (k + 1)) = partialLogSum m z + logTail m z := by
  have hf : Summable (fun k : ℕ => z ^ (k + 1) / (k + 1)) := by
    simpa [logTail, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
      (summable_logTail (z := z) hz 0)
  simpa [partialLogSum, logTail, Nat.cast_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    add_assoc, add_left_comm, add_comm] using
    (hf.sum_add_tsum_nat_add m).symm

/-- A geometric-series bound on the tail `logTail m z`. -/
lemma norm_logTail_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  unfold logTail
  have h_summable := summable_logTail hz m
  calc
    ‖∑' k, z ^ (m + 1 + k) / ((m + 1 + k : ℕ) : ℂ)‖
        ≤ ∑' k, ‖z ^ (m + 1 + k) / ((m + 1 + k : ℕ) : ℂ)‖ :=
          norm_tsum_le_tsum_norm h_summable.norm
    _ ≤ ∑' k, ‖z‖ ^ (m + 1 + k) := by
          have h_rhs_summable : Summable (fun k => ‖z‖ ^ (m + 1 + k)) := by
            simpa [pow_add] using
              (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ (m + 1))
          refine h_summable.norm.tsum_le_tsum ?_ h_rhs_summable
          intro k
          rw [norm_div, norm_pow]
          exact div_le_self (pow_nonneg (norm_nonneg z) _) (one_le_norm_natCast_add_one_add m k)
    _ = ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
          have h_eq : (fun k => ‖z‖ ^ (m + 1 + k)) = (fun k => ‖z‖ ^ (m + 1) * ‖z‖ ^ k) := by
            ext k; rw [pow_add]
          rw [h_eq, tsum_mul_left]
          have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) hz
          rw [h_geom.tsum_eq, div_eq_mul_inv]

/-- For `‖z‖ ≤ 1 / 2`: `‖z‖^{m+1}/(1-‖z‖) ≤ 2‖z‖^{m+1}`. -/
lemma norm_pow_div_one_sub_le_two {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) (m : ℕ) :
    ‖z‖ ^ (m + 1) / (1 - ‖z‖) ≤ 2 * ‖z‖ ^ (m + 1) := by
  have h1mr_pos : 0 < 1 - ‖z‖ := by linarith [norm_nonneg z]
  rw [div_le_iff₀ h1mr_pos]
  calc
    ‖z‖ ^ (m + 1) = 1 * ‖z‖ ^ (m + 1) := by ring
    _ ≤ 2 * (1 - ‖z‖) * ‖z‖ ^ (m + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) _)
          nlinarith
    _ = 2 * ‖z‖ ^ (m + 1) * (1 - ‖z‖) := by ring

/-! ## The Weierstrass factor representation -/

/-- The Weierstrass elementary factor. -/
def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum m z)

/-- The elementary factor `E₀(z) = 1 - z`. -/
@[simp] lemma weierstrassFactor_zero (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor]

/-- The elementary factor `E₁(z) = (1 - z) * exp z`. -/
@[simp] lemma weierstrassFactor_one (z : ℂ) : weierstrassFactor 1 z = (1 - z) * exp z := by
  simp [weierstrassFactor]

/-- The elementary factor at `z = 0` equals `1`. -/
@[simp] lemma weierstrassFactor_at_zero (m : ℕ) : weierstrassFactor m 0 = 1 := by
  simp [weierstrassFactor, partialLogSum]

/-- The elementary factor vanishes at `z = 1`. -/
@[simp] lemma weierstrassFactor_at_one (m : ℕ) : weierstrassFactor m 1 = 0 := by
  simp [weierstrassFactor]

/-- The Weierstrass factor vanishes exactly at `z = 1`. -/
lemma weierstrassFactor_eq_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z = 0 ↔ z = 1 := by
  constructor
  · intro hz
    have hmul : (1 - z) = 0 ∨ exp (partialLogSum m z) = 0 := by
      exact mul_eq_zero.mp (by simpa [weierstrassFactor] using hz)
    have : (1 - z) = 0 := hmul.resolve_right (exp_ne_zero _)
    exact (sub_eq_zero.mp this).symm
  · rintro rfl
    simp [weierstrassFactor]

lemma weierstrassFactor_ne_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z ≠ 0 ↔ z ≠ 1 := by
  simpa using (not_congr (weierstrassFactor_eq_zero_iff m z))

/-- `E_m(z) = exp(-logTail m z)` for `‖z‖ < 1`. -/
lemma weierstrassFactor_eq_exp_neg_tail (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    weierstrassFactor m z = exp (-logTail m z) := by
  unfold weierstrassFactor
  have hz1 : z ≠ (1 : ℂ) := by
    intro hz1
    subst hz1
    simp at hz
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have h_log : log (1 - z) = -∑' k : ℕ, z ^ (k + 1) / (k + 1) := by
    exact (neg_eq_iff_eq_neg).1 (neg_log_one_sub_eq_tsum (z := z) hz)
  have h_decomp :
      (∑' k : ℕ, z ^ (k + 1) / (k + 1)) = partialLogSum m z + logTail m z :=
    tsum_pow_succ_div_eq_partialLogSum_add_logTail (z := z) hz m
  rw [← exp_log hz_ne_1]
  rw [← Complex.exp_add]
  congr 1
  calc
    log (1 - z) + partialLogSum m z
        = (-(∑' k : ℕ, z ^ (k + 1) / (k + 1))) + partialLogSum m z := by
              simp [h_log]
    _ = (-(partialLogSum m z + logTail m z)) + partialLogSum m z := by
              simp [h_decomp]
    _ = -logTail m z := by
          simp

/-! ## The power bound -/

/-- For `‖z‖ ≤ 1 / 2`, `‖E_m(z) - 1‖ ≤ 4‖z‖^{m+1}`. -/
theorem weierstrassFactor_sub_one_pow_bound {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · subst hm
    simp [weierstrassFactor, partialLogSum]
    nlinarith [norm_nonneg z]
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    have h_eq : weierstrassFactor m z = exp (-logTail m z) :=
      weierstrassFactor_eq_exp_neg_tail m hz_lt
    rw [h_eq]
    have h_tail_bound : ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) :=
      (norm_logTail_le hz_lt m).trans (norm_pow_div_one_sub_le_two hz m)
    have hw_le_one : ‖-logTail m z‖ ≤ 1 := by
      have hlogTail_le_one : ‖logTail m z‖ ≤ 1 := by
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := Nat.succ_le_succ (Nat.succ_le_iff.2 hm_pos)
        have hz1' : ‖z‖ ≤ 1 := by nlinarith [hz]
        have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
        calc
          ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) := h_tail_bound
          _ ≤ 2 * ‖z‖ ^ 2 := by
                refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
                exact pow_le_pow_of_le_one hz0 hz1' h2
          _ ≤ 1 := by
                have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
                nlinarith
      simpa [norm_neg] using hlogTail_le_one
    have h_exp_sub_one : ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖-logTail m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc
      ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖logTail m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring

/-!
## Lower bounds for `Real.log ‖weierstrassFactor m z‖`

These are auxiliary inequalities used in minimum-modulus / Cartan-type arguments in Hadamard
factorization: one “near” estimate (small `‖z‖`) and one general lower bound expressed in terms of
`log ‖1 - z‖` and a crude bound on `partialLogSum`.
-/

lemma log_norm_weierstrassFactor_ge_neg_two_pow {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    (-2 : ℝ) * ‖z‖ ^ (m + 1) ≤ Real.log ‖weierstrassFactor m z‖ := by
  have hz_lt : ‖z‖ < (1 : ℝ) := lt_of_le_of_lt hz (by norm_num)
  have hEq : weierstrassFactor m z = Complex.exp (-logTail m z) :=
    weierstrassFactor_eq_exp_neg_tail m hz_lt
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = (-logTail m z).re := by
    simp [hEq, Complex.norm_exp, Real.log_exp]
  have hre : (-logTail m z).re ≥ -‖logTail m z‖ := by
    -- `-‖-w‖ ≤ (-w).re`
    simpa [norm_neg, ge_iff_le] using (neg_norm_le_re (-logTail m z))
  have htail : ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) :=
    (norm_logTail_le hz_lt m).trans (norm_pow_div_one_sub_le_two hz m)
  have : (-logTail m z).re ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
    calc
      (-logTail m z).re ≥ -‖logTail m z‖ := hre
      _ ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
            nlinarith [htail]
  simpa [hlog, mul_assoc, mul_left_comm, mul_comm] using this

/-!
## A general lower bound for `Real.log ‖weierstrassFactor m z‖`
-/

/-- A crude lower bound on `Real.log ‖weierstrassFactor m z‖`, expressed in terms of
`Real.log ‖1 - z‖` and a bound for `partialLogSum`. -/
lemma log_norm_weierstrassFactor_ge_log_norm_one_sub_sub
    (m : ℕ) (z : ℂ) :
    Real.log ‖1 - z‖ - (m : ℝ) * max 1 (‖z‖ ^ m) ≤ Real.log ‖weierstrassFactor m z‖ := by
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    simp [weierstrassFactor]
  set S : ℂ := partialLogSum m z
  have hS : weierstrassFactor m z = (1 - z) * Complex.exp S := by
    simp [weierstrassFactor, S]
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = Real.log ‖1 - z‖ + S.re := by
    have hne : ‖(1 : ℂ) - z‖ ≠ 0 := ne_of_gt hnorm_pos
    calc
      Real.log ‖weierstrassFactor m z‖
          = Real.log (‖(1 : ℂ) - z‖ * ‖Complex.exp S‖) := by
                simp [hS]
      _ = Real.log ‖(1 : ℂ) - z‖ + Real.log ‖Complex.exp S‖ := by
            simpa using Real.log_mul hne ((norm_ne_zero_iff).2 (Complex.exp_ne_zero S))
      _ = Real.log ‖(1 : ℂ) - z‖ + S.re := by
            simp [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖1 - z‖ + S.re := by simp [sub_eq_add_neg, add_comm]
  have hre : S.re ≥ -‖S‖ := by
    simpa [ge_iff_le] using (neg_norm_le_re S)
  have hnormS : ‖S‖ ≤ (m : ℝ) * max 1 (‖z‖ ^ m) := by
    simpa [S] using norm_partialLogSum_le m z
  have : Real.log ‖weierstrassFactor m z‖ ≥ Real.log ‖1 - z‖ - ‖S‖ := by
    linarith [hlog, hre]
  linarith [this, hnormS]

end Complex
