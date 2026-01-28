/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
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
<https://dlmf.nist.gov/5.9>.

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
  if t ≤ 0 then 0 else 1 / (exp t - 1) - 1 / t + 1 / 2

/-- The normalized Binet kernel.

We define `Ktilde : ℝ → ℝ` by setting `Ktilde t = 1/12` for `t ≤ 0`, and
`Ktilde(t) = (1/(exp t - 1) - 1/t + 1/2) / t` for `t > 0`.
The value `1/12` is the right-limit as `t → 0⁺`. -/
def Ktilde (t : ℝ) : ℝ :=
  if t ≤ 0 then 1 / 12 else (1 / (exp t - 1) - 1 / t + 1 / 2) / t

/-- For `t ≤ 0`, `K t = 0` by definition. -/
@[simp]
lemma K_of_nonpos {t : ℝ} (ht : t ≤ 0) : K t = 0 := by
  simp [K, ht]

/-- For `t > 0`, `K` has the explicit formula. -/
lemma K_of_pos {t : ℝ} (ht : 0 < t) : K t = 1 / (exp t - 1) - 1 / t + 1 / 2 := by
  simp [K, not_le.mpr ht]

/-- For `t ≤ 0`, `Ktilde t = 1/12` by definition. -/
@[simp]
lemma Ktilde_of_nonpos {t : ℝ} (ht : t ≤ 0) : Ktilde t = 1 / 12 := by
  simp [Ktilde, ht]

/-- For `t > 0`, `Ktilde` has the explicit formula. -/
lemma Ktilde_of_pos {t : ℝ} (ht : 0 < t) :
    Ktilde t = (1 / (exp t - 1) - 1 / t + 1 / 2) / t := by
  simp [Ktilde, not_le.mpr ht]

/-- K̃(0) = 1/12 by definition (the limit value). -/
@[simp]
lemma Ktilde_zero : Ktilde 0 = 1 / 12 := by simp [Ktilde]


/-! ### The main identity for the kernel -/

namespace Aux

/-- For `t > 0`, we have `0 < exp t - 1`. -/
lemma exp_sub_one_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp t - 1 :=
  sub_pos.2 (Real.one_lt_exp_iff.2 ht)

/-- The function `kernelNum(t) = exp t * (t - 2) + t + 2` that appears in the kernel numerator. -/
def kernelNum (t : ℝ) : ℝ := exp t * (t - 2) + t + 2

lemma kernelNum_zero : kernelNum 0 = 0 := by simp [kernelNum]

end Aux

open Aux

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
  refine h3.continuousWithinAt.congr (fun x hx => ?_) ?_
  · simpa using (Ktilde_of_pos (mem_Ioi.mp hx))
  · simpa using (Ktilde_of_pos ht0)

/-- Key algebraic identity for `K` when `t > 0`. -/
private lemma K_eq_kernelNum_div {t : ℝ} (ht : 0 < t) :
    K t = kernelNum t / (2 * t * (exp t - 1)) := by
  have hexp : exp t - 1 ≠ 0 := ne_of_gt (exp_sub_one_pos ht)
  have ht' : t ≠ 0 := ne_of_gt ht
  rw [K_of_pos ht, kernelNum]
  field_simp [hexp, ht']
  ring

/-! ### Sign analysis -/

/-- The derivative of `kernelNum t = exp t * (t - 2) + t + 2` is `exp t * (t - 1) + 1`. -/
private lemma kernelNum_deriv (t : ℝ) : HasDerivAt kernelNum (exp t * (t - 1) + 1) t := by
  unfold kernelNum
  have h1 : HasDerivAt (fun x => exp x * (x - 2)) (exp t * (t - 2) + exp t * 1) t :=
    (Real.hasDerivAt_exp t).mul ((hasDerivAt_id t).sub_const 2)
  have h2 :
      HasDerivAt (fun x => exp x * (x - 2) + x) (exp t * (t - 2) + exp t * 1 + 1) t :=
    h1.add (hasDerivAt_id t)
  have h3 :
      HasDerivAt (fun x => exp x * (x - 2) + x + 2) (exp t * (t - 2) + exp t * 1 + 1) t :=
    h2.add_const 2
  convert h3 using 1
  ring

/-- kernelNum'(t) > 0 for t > 0. -/
private lemma kernelNum_deriv_pos {t : ℝ} (ht : 0 < t) : 0 < deriv kernelNum t := by
  rw [(kernelNum_deriv t).deriv]
  have h : exp t * (1 - t) < 1 := by
    simpa [mul_comm, exp_neg, mul_inv_cancel₀ (exp_pos t).ne'] using
      (mul_lt_mul_of_pos_left (one_sub_lt_exp_neg ht.ne') (exp_pos t))
  have hrew : exp t * (t - 1) + 1 = 1 - exp t * (1 - t) := by ring
  simpa [hrew] using (sub_pos.2 h)

/-- `kernelNum` is strictly increasing on `[0, ∞)`. -/
private lemma strictMonoOn_kernelNum_Ici : StrictMonoOn kernelNum (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ fun x hx =>
    kernelNum_deriv_pos (by rwa [interior_Ici] at hx)
  simpa [kernelNum] using
    (((continuous_exp.mul (continuous_id.sub continuous_const)).add continuous_id).add
          continuous_const).continuousOn

/-- kernelNum(t) ≥ 0 for all t ≥ 0. -/
private lemma kernelNum_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ kernelNum t := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp [kernelNum_zero]
  · exact le_of_lt <| by
      simpa [kernelNum_zero] using strictMonoOn_kernelNum_Ici (by simp) ht ht'

/-- The Binet kernel K(t) is nonnegative for t > 0. -/
theorem K_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ K t := by
  rw [K_eq_kernelNum_div ht]
  exact div_nonneg (kernelNum_nonneg ht.le) (by positivity [exp_sub_one_pos ht, ht.le])

/-- The normalized kernel K̃(t) is nonnegative for t ≥ 0. -/
theorem Ktilde_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Ktilde t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · simp
  · simpa [Ktilde_of_pos hpos, K_of_pos hpos] using div_nonneg (K_nonneg hpos) hpos.le

/-! ### Upper bound -/

/-! ### Auxiliary function g for the Ktilde bound -/

/-- The auxiliary function g(t) = (t² - 6t + 12)e^t - (t² + 6t + 12).
We show g(t) ≥ 0 for t ≥ 0, which implies the bound Ktilde t ≤ 1/12. -/
private def gAux (t : ℝ) : ℝ :=
  (t ^ 2 - 6 * t + 12) * exp t - (t ^ 2 + 6 * t + 12)

private lemma quad_pos (t : ℝ) : 0 < t ^ 2 - t + 2 := by
  have : t ^ 2 - t + 2 = (t - (1 / 2)) ^ 2 + (7 / 4) := by ring
  nlinarith [sq_nonneg (t - (1 / 2))]

private lemma sub_mul_kernelNum_eq_two_mul_gAux (t : ℝ) :
    2 * t ^ 2 * (exp t - 1) - 12 * kernelNum t = 2 * gAux t := by
  unfold gAux kernelNum
  ring

private lemma kernelNum_mul12_le_iff_gAux_nonneg (t : ℝ) :
    kernelNum t * 12 ≤ 2 * t ^ 2 * (exp t - 1) ↔ 0 ≤ gAux t := by
  constructor <;> intro h
  · have : 0 ≤ 2 * gAux t := by
      have : 0 ≤ 2 * t ^ 2 * (exp t - 1) - 12 * kernelNum t := by linarith
      simpa [sub_mul_kernelNum_eq_two_mul_gAux t] using this
    nlinarith
  · have : 0 ≤ 2 * t ^ 2 * (exp t - 1) - 12 * kernelNum t := by
      have : 0 ≤ 2 * gAux t := by nlinarith
      simpa [sub_mul_kernelNum_eq_two_mul_gAux t] using this
    linarith

private lemma kernelNum_mul12_lt_iff_gAux_pos (t : ℝ) :
    kernelNum t * 12 < 2 * t ^ 2 * (exp t - 1) ↔ 0 < gAux t := by
  constructor <;> intro h
  · have : 0 < 2 * gAux t := by
      have : 0 < 2 * t ^ 2 * (exp t - 1) - 12 * kernelNum t := by linarith
      simpa [sub_mul_kernelNum_eq_two_mul_gAux t] using this
    nlinarith
  · have : 0 < 2 * t ^ 2 * (exp t - 1) - 12 * kernelNum t := by
      have : 0 < 2 * gAux t := by nlinarith
      simpa [sub_mul_kernelNum_eq_two_mul_gAux t] using this
    linarith

/-! #### Taylor/series route: a polynomial lower bound for `gAux` -/

private lemma exp_poly5_le_exp {t : ℝ} (ht : 0 ≤ t) :
    1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + t ^ 5 / 120 ≤ exp t := by
  simpa [Finset.sum_range_succ, Nat.factorial, div_eq_mul_inv] using
    (Real.sum_le_exp_of_nonneg ht 6)

private lemma gAux_lower_bound_poly {t : ℝ} (ht : 0 ≤ t) :
    t ^ 5 * (t ^ 2 - t + 2) / 120 ≤ gAux t := by
  have hA : 0 ≤ t ^ 2 - 6 * t + 12 := by
    have : t ^ 2 - 6 * t + 12 = (t - 3) ^ 2 + 3 := by ring
    nlinarith [sq_nonneg (t - 3)]
  have h := mul_le_mul_of_nonneg_left (exp_poly5_le_exp ht) hA
  unfold gAux
  linarith

private lemma gAux_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gAux t := by
  have h : 0 ≤ t ^ 5 * (t ^ 2 - t + 2) / 120 := by
    have : 0 ≤ t ^ 2 - t + 2 := (quad_pos t).le
    positivity
  exact h.trans (gAux_lower_bound_poly ht)

private lemma gAux_pos {t : ℝ} (ht : 0 < t) : 0 < gAux t := by
  have h : 0 < t ^ 5 * (t ^ 2 - t + 2) / 120 := by
    have : 0 < t ^ 2 - t + 2 := quad_pos t
    positivity
  exact h.trans_le (gAux_lower_bound_poly ht.le)

namespace Aux

/-- A convenient closed form for `Ktilde` when `t > 0`. -/
lemma Ktilde_eq_kernelNum_div {t : ℝ} (ht : 0 < t) :
    Ktilde t = kernelNum t / (2 * t ^ 2 * (exp t - 1)) := by
  calc
    Ktilde t = (1 / (exp t - 1) - 1 / t + 1 / 2) / t := Ktilde_of_pos ht
    _ = K t / t := by simp [K_of_pos ht]
    _ = (kernelNum t / (2 * t * (exp t - 1))) / t := by simp [K_eq_kernelNum_div ht]
    _ = kernelNum t / (2 * t ^ 2 * (exp t - 1)) := by
          field_simp

lemma denom_pos {t : ℝ} (ht : 0 < t) : (0 : ℝ) < 2 * t ^ 2 * (exp t - 1) := by
  positivity [exp_sub_one_pos ht]

end Aux

open Aux

/-- Upper bound for `Ktilde` on `[0, ∞)`. -/
theorem Ktilde_le {t : ℝ} (ht : 0 ≤ t) : Ktilde t ≤ 1 / 12 := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · simp
  · have hD : (0 : ℝ) < 2 * t ^ 2 * (exp t - 1) := denom_pos hpos
    have h12 : (0 : ℝ) < (12 : ℝ) := by norm_num
    rw [Ktilde_eq_kernelNum_div hpos, div_le_div_iff₀ hD h12]
    have : 0 ≤ gAux t := gAux_nonneg (t := t) hpos.le
    simpa [one_mul] using (kernelNum_mul12_le_iff_gAux_nonneg t).2 this

/-- Strict upper bound for `Ktilde` on `(0, ∞)`. -/
theorem Ktilde_lt {t : ℝ} (ht : 0 < t) : Ktilde t < 1 / 12 := by
  have hD : (0 : ℝ) < 2 * t ^ 2 * (exp t - 1) := denom_pos ht
  have h12 : (0 : ℝ) < (12 : ℝ) := by norm_num
  rw [Ktilde_eq_kernelNum_div ht, div_lt_div_iff₀ hD h12]
  have : 0 < gAux t := gAux_pos (t := t) ht
  simpa [one_mul] using (kernelNum_mul12_lt_iff_gAux_pos t).2 this

end Binet
