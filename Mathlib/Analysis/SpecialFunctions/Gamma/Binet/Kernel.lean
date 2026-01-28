/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
# Binet kernel estimates

This file studies the kernel
`K(t) = 1 / (exp t - 1) - 1 / t + 1 / 2`
that appears in Binet's integral representation of `log Γ`, together with the normalized kernel
`Ktilde t = K t / t`.

## Main results

- `Binet.continuousOn_Ktilde_Ioi`: continuity of `Ktilde` on `(0, ∞)`.
- `Binet.K_nonneg`: `0 ≤ K t` for `t > 0`.
- `Binet.Ktilde_nonneg`: `0 ≤ Ktilde t` for `t ≥ 0`.
- `Binet.Ktilde_le`: `Ktilde t ≤ 1 / 12` for `t ≥ 0`.
- `Binet.Ktilde_lt`: `Ktilde t < 1 / 12` for `t > 0`.

## Mathematical background

Formally, the Laurent expansion
\[
\frac{1}{e^t - 1} = \frac{1}{t} - \frac{1}{2} + \frac{t}{12} - \frac{t^3}{720} + \cdots
\]
suggests `K t → 0` and `Ktilde t → 1 / 12` as `t → 0⁺`.

## Implementation notes

We define `K` and `Ktilde` on all of `ℝ` by assigning convenient values on `(-∞, 0]`.
The analytic content is on `(0, ∞)`. The upper bound `Ktilde t ≤ 1/12` is proved via a
Taylor/series argument using `Real.sum_le_exp_of_nonneg` (positivity of the exponential series),
rather than a bespoke derivative chain.

## References

See the DLMF entry on the Gamma function, especially the discussion around Binet-type formulas:
<https://dlmf.nist.gov/5.9>
<https://dlmf.nist.gov/5.11>.

## Tags

gamma, binet, kernel, exponential, bounds

-/

noncomputable section

open Real Set Filter
open scoped Topology

namespace Binet

/-! ### Basic definitions and elementary properties -/

/-- The (unnormalized) Binet kernel.

We define `K : ℝ → ℝ` on all of `ℝ` by setting `K t = 0` for `t ≤ 0`, and using
`K(t) = 1/(exp t - 1) - 1/t + 1/2` for `t > 0`.
This total definition is convenient for global boundedness/continuity statements; the analytic
content is on `(0, ∞)`. -/
def K (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else 1/(exp t - 1) - 1/t + 1/2

/-- The normalized Binet kernel.

We define `Ktilde : ℝ → ℝ` by setting `Ktilde t = 1/12` for `t ≤ 0`, and
`Ktilde(t) = (1/(exp t - 1) - 1/t + 1/2) / t` for `t > 0`.
The value `1/12` is the right-limit as `t → 0⁺`. -/
def Ktilde (t : ℝ) : ℝ :=
  if t ≤ 0 then 1/12 else (1/(exp t - 1) - 1/t + 1/2) / t

/-- For t > 0, K has the explicit formula. -/
lemma K_pos {t : ℝ} (ht : 0 < t) : K t = 1/(exp t - 1) - 1/t + 1/2 := by
  simp [K, not_le.mpr ht]

/-- For t > 0, K̃ has the explicit formula. -/
lemma Ktilde_pos {t : ℝ} (ht : 0 < t) :
    Ktilde t = (1/(exp t - 1) - 1/t + 1/2) / t := by
  simp [Ktilde, not_le.mpr ht]

/-- K̃(0) = 1/12 by definition (the limit value). -/
lemma Ktilde_zero : Ktilde 0 = 1/12 := by simp [Ktilde]

/-! ### The main identity for the kernel -/

namespace Internal

/-- For `t > 0`, we have `0 < exp t - 1`. -/
lemma exp_sub_one_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp t - 1 :=
  sub_pos.2 (Real.one_lt_exp_iff.2 ht)

/-- The function `kernelNum(t) = exp t * (t - 2) + t + 2` that appears in the kernel numerator. -/
def kernelNum (t : ℝ) : ℝ := exp t * (t - 2) + t + 2

lemma kernelNum_zero : kernelNum 0 = 0 := by simp [kernelNum]

end Internal

open Internal

/-- K̃ is continuous on (0, ∞). -/
lemma continuousOn_Ktilde_Ioi : ContinuousOn Ktilde (Ioi 0) := by
  intro t ht
  have ht0 : 0 < t := mem_Ioi.mp ht
  have hne_exp : exp t - 1 ≠ 0 := (exp_sub_one_pos ht0).ne'
  have h1 : ContinuousAt (fun x => 1 / (exp x - 1)) t :=
    continuousAt_const.div (continuous_exp.continuousAt.sub continuousAt_const) hne_exp
  have h2 : ContinuousAt (fun x => 1 / x) t := continuousAt_const.div continuousAt_id ht0.ne'
  have h3 : ContinuousAt (fun x => (1 / (exp x - 1) - 1 / x + 1 / 2) / x) t :=
    ((h1.sub h2).add continuousAt_const).div continuousAt_id ht0.ne'
  exact h3.continuousWithinAt.congr
    (fun y hy => by simp only [Ktilde, not_le.mpr (mem_Ioi.mp hy), ↓reduceIte])
    (by simp only [Ktilde, not_le.mpr ht0, ↓reduceIte])

/-- Key algebraic identity for `K` when `t > 0`. -/
private lemma K_eq_kernelNum_div {t : ℝ} (ht : 0 < t) :
    K t = kernelNum t / (2 * t * (exp t - 1)) := by
  have hexp : exp t - 1 ≠ 0 := ne_of_gt (exp_sub_one_pos ht)
  have ht' : t ≠ 0 := ne_of_gt ht
  rw [K_pos ht, kernelNum]
  field_simp [hexp, ht']
  ring

/-! ### Sign analysis -/

/-- The derivative of kernelNum(t) = e^t(t-2) + t + 2 is kernelNum'(t) = e^t(t-1) + 1. -/
private lemma kernelNum_deriv (t : ℝ) : HasDerivAt kernelNum (exp t * (t - 1) + 1) t := by
  unfold kernelNum
  have h1 : HasDerivAt (fun x => exp x * (x - 2)) (exp t * (t - 2) + exp t * 1) t :=
    (Real.hasDerivAt_exp t).mul ((hasDerivAt_id t).sub_const 2)
  have h2 : HasDerivAt (fun x => exp x * (x - 2) + x) (exp t * (t - 2) + exp t * 1 + 1) t :=
    h1.add (hasDerivAt_id t)
  have h3 : HasDerivAt (fun x => exp x * (x - 2) + x + 2) (exp t * (t - 2) + exp t * 1 + 1) t :=
    h2.add_const 2
  convert h3 using 1
  ring

/-- kernelNum'(t) > 0 for t > 0. -/
private lemma kernelNum_deriv_pos {t : ℝ} (ht : 0 < t) : 0 < deriv kernelNum t := by
  rw [(kernelNum_deriv t).deriv]
  have h : exp t * (1 - t) < 1 := by
    by_cases h : 1 ≤ t
    · exact (mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (sub_nonpos.2 h)).trans_lt zero_lt_one
    · push_neg at h
      rw [mul_comm, ← lt_div_iff₀ (exp_pos _)]
      calc 1 - t < exp (-t) := one_sub_lt_exp_neg ht.ne'
        _ = 1 / exp t := by rw [exp_neg, inv_eq_one_div]
  linarith

/-- `kernelNum` is strictly increasing on `[0, ∞)`. -/
private lemma strictMonoOn_kernelNum_Ici : StrictMonoOn kernelNum (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ fun x hx =>
    kernelNum_deriv_pos (by rwa [interior_Ici] at hx)
  exact ((continuous_exp.mul (continuous_id.sub continuous_const)).add continuous_id).add
    continuous_const |>.continuousOn.congr fun _ _ => rfl

/-- kernelNum(t) ≥ 0 for all t ≥ 0. -/
private lemma kernelNum_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ kernelNum t := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp [kernelNum_zero]
  · simpa [kernelNum_zero] using (strictMonoOn_kernelNum_Ici (by simp) ht'.le ht').le

/-- The Binet kernel K(t) is nonnegative for t > 0. -/
theorem K_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ K t := by
  rw [K_eq_kernelNum_div ht]
  have hexp : 0 < exp t - 1 := exp_sub_one_pos ht
  exact div_nonneg (kernelNum_nonneg ht.le) (by positivity)

/-- The normalized kernel K̃(t) is nonnegative for t ≥ 0. -/
theorem Ktilde_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Ktilde t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · simp [Ktilde_zero]
  · rw [Ktilde_pos hpos]
    exact div_nonneg (by rw [← K_pos hpos]; exact K_nonneg hpos) hpos.le

/-! ### Upper bound -/

/-! ### Auxiliary function g for the Ktilde bound -/

/-- The auxiliary function g(t) = (t² - 6t + 12)e^t - (t² + 6t + 12).
We show g(t) ≥ 0 for t ≥ 0, which implies the bound Ktilde t ≤ 1/12. -/
private def gAux (t : ℝ) : ℝ :=
  (t ^ 2 - 6 * t + 12) * exp t - (t ^ 2 + 6 * t + 12)

/-! #### Taylor/series route: a polynomial lower bound for `gAux` -/

private lemma exp_poly5_le_exp {t : ℝ} (ht : 0 ≤ t) :
    1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + t ^ 5 / 120 ≤ exp t := by
  simpa [Finset.sum_range_succ, Nat.factorial, div_eq_mul_inv] using
    (Real.sum_le_exp_of_nonneg ht 6)

private lemma gAux_lower_bound_poly {t : ℝ} (ht : 0 ≤ t) :
    t ^ 5 * (t ^ 2 - t + 2) / 120 ≤ gAux t := by
  have hA : 0 ≤ t ^ 2 - 6 * t + 12 := by
    -- `(t - 3)^2 + 3 ≥ 0`.
    have : t ^ 2 - 6 * t + 12 = (t - 3) ^ 2 + 3 := by ring
    nlinarith [sq_nonneg (t - 3)]
  have hexp := (mul_le_mul_of_nonneg_left (exp_poly5_le_exp ht) hA)
  unfold gAux
  linarith

private lemma gAux_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gAux t := by
  have hquad : 0 ≤ t ^ 2 - t + 2 := by
    have : t ^ 2 - t + 2 = (t - (1 / 2)) ^ 2 + (7 / 4) := by ring
    nlinarith [sq_nonneg (t - (1 / 2))]
  have h : 0 ≤ t ^ 5 * (t ^ 2 - t + 2) / 120 := by positivity
  exact h.trans (gAux_lower_bound_poly ht)

private lemma gAux_pos {t : ℝ} (ht : 0 < t) : 0 < gAux t := by
  have hquad : 0 < t ^ 2 - t + 2 := by
    have : t ^ 2 - t + 2 = (t - (1 / 2)) ^ 2 + (7 / 4) := by ring
    nlinarith [sq_nonneg (t - (1 / 2))]
  have h : 0 < t ^ 5 * (t ^ 2 - t + 2) / 120 := by positivity
  exact h.trans_le (gAux_lower_bound_poly ht.le)

namespace Internal

/-- A convenient closed form for `Ktilde` when `t > 0`. -/
lemma Ktilde_eq_kernelNum_div {t : ℝ} (ht : 0 < t) :
    Ktilde t = kernelNum t / (2 * t ^ 2 * (exp t - 1)) := by
  calc
    Ktilde t = (1 / (exp t - 1) - 1 / t + 1 / 2) / t := Ktilde_pos ht
    _ = K t / t := by
        simp [K_pos ht]
    _ = (kernelNum t / (2 * t * (exp t - 1))) / t := by
        simp [K_eq_kernelNum_div ht]
    _ = kernelNum t / (2 * t ^ 2 * (exp t - 1)) := by
        field_simp

lemma denom_pos {t : ℝ} (ht : 0 < t) : (0 : ℝ) < 2 * t ^ 2 * (exp t - 1) := by
  have := exp_sub_one_pos ht
  positivity

end Internal

/-- Upper bound for `Ktilde` on `[0, ∞)`. -/
theorem Ktilde_le {t : ℝ} (ht : 0 ≤ t) : Ktilde t ≤ 1/12 := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [Ktilde_zero]
  · have hD : (0 : ℝ) < 2 * t ^ 2 * (exp t - 1) := denom_pos hpos
    have h12 : (0 : ℝ) < (12 : ℝ) := by norm_num
    rw [Ktilde_eq_kernelNum_div hpos, div_le_div_iff₀ hD h12]
    have hgoal : 0 ≤ 2 * gAux t := by nlinarith [gAux_nonneg (t := t) hpos.le]
    unfold gAux at hgoal
    unfold kernelNum
    linarith [hgoal, exp_pos t, sq_nonneg t]

/-- Strict upper bound for `Ktilde` on `(0, ∞)`. -/
theorem Ktilde_lt {t : ℝ} (ht : 0 < t) : Ktilde t < 1 / 12 := by
  have hD : (0 : ℝ) < 2 * t ^ 2 * (exp t - 1) := denom_pos ht
  have h12 : (0 : ℝ) < (12 : ℝ) := by norm_num
  rw [Ktilde_eq_kernelNum_div ht, div_lt_div_iff₀ hD h12]
  have hpos : 0 < 2 * gAux t := by nlinarith [gAux_pos (t := t) ht]
  unfold gAux at hpos
  unfold kernelNum
  linarith [hpos, exp_pos t, sq_nonneg t]

end Binet
