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
  if t ≤ 0 then 0 else 1/(Real.exp t - 1) - 1/t + 1/2

/-- The normalized Binet kernel.

We define `Ktilde : ℝ → ℝ` by setting `Ktilde t = 1/12` for `t ≤ 0`, and
`Ktilde(t) = (1/(exp t - 1) - 1/t + 1/2) / t` for `t > 0`.
The value `1/12` is the right-limit as `t → 0⁺`. -/
def Ktilde (t : ℝ) : ℝ :=
  if t ≤ 0 then 1/12 else (1/(Real.exp t - 1) - 1/t + 1/2) / t

/-- For t > 0, K has the explicit formula. -/
lemma K_pos {t : ℝ} (ht : 0 < t) : K t = 1/(Real.exp t - 1) - 1/t + 1/2 := by
  simp [K, not_le.mpr ht]

/-- For t > 0, K̃ has the explicit formula. -/
lemma Ktilde_pos {t : ℝ} (ht : 0 < t) :
    Ktilde t = (1/(Real.exp t - 1) - 1/t + 1/2) / t := by
  simp [Ktilde, not_le.mpr ht]

/-- K̃(0) = 1/12 by definition (the limit value). -/
lemma Ktilde_zero : Ktilde 0 = 1/12 := by simp [Ktilde]

/-! ### The key identity for the kernel -/

/-- For t > 0, e^t > 1, so e^t - 1 > 0. -/
private lemma exp_sub_one_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp t - 1 := by
  exact sub_pos.2 (Real.one_lt_exp_iff.2 ht)

/-- K̃ is continuous on (0, ∞). -/
lemma continuousOn_Ktilde_Ioi : ContinuousOn Ktilde (Set.Ioi 0) := by
  intro t ht
  have ht0 : 0 < t := by simpa [Set.mem_Ioi] using ht
  have hne_t : t ≠ 0 := ne_of_gt ht0
  have hne_exp : Real.exp t - 1 ≠ 0 := ne_of_gt (exp_sub_one_pos ht0)
  have h1 : ContinuousAt (fun x => 1 / (Real.exp x - 1)) t :=
    continuousAt_const.div (Real.continuous_exp.continuousAt.sub continuousAt_const) hne_exp
  have h2 : ContinuousAt (fun x => 1 / x) t := continuousAt_const.div continuousAt_id hne_t
  have h3 : ContinuousAt (fun x => 1 / (Real.exp x - 1) - 1 / x + 1 / 2) t :=
    (h1.sub h2).add continuousAt_const
  have h4 : ContinuousAt (fun x => (1 / (Real.exp x - 1) - 1 / x + 1 / 2) / x) t :=
    h3.div continuousAt_id hne_t
  apply h4.continuousWithinAt.congr
  · intro y hy
    have hy0 : 0 < y := by simpa [Set.mem_Ioi] using hy
    simp [Ktilde, not_le.mpr hy0]
  · simp [Ktilde, not_le.mpr ht0]

/-- The function f(t) = e^t(t-2) + t + 2 that appears in the numerator. -/
private def f (t : ℝ) : ℝ := Real.exp t * (t - 2) + t + 2

private lemma f_zero : f 0 = 0 := by simp [f]

/-- Key algebraic identity for `K` when `t > 0`. -/
private lemma K_eq_f_div {t : ℝ} (ht : 0 < t) :
    K t = f t / (2 * t * (Real.exp t - 1)) := by
  rw [K_pos ht]
  have hexp : Real.exp t - 1 ≠ 0 := ne_of_gt (exp_sub_one_pos ht)
  have ht_ne : t ≠ 0 := ne_of_gt ht
  dsimp [f]
  field_simp [hexp, ht_ne]
  ring

/-! ### Sign analysis -/

/-- The derivative of f(t) = e^t(t-2) + t + 2 is f'(t) = e^t(t-1) + 1. -/
private lemma f_deriv (t : ℝ) : HasDerivAt f (Real.exp t * (t - 1) + 1) t := by
  have hmul :
      HasDerivAt (fun x => Real.exp x * (x - 2)) (Real.exp t * (t - 2) + Real.exp t) t :=
    by
      simpa [one_mul] using
        (Real.hasDerivAt_exp t).mul ((hasDerivAt_id t).sub_const 2)
  have hadd1 :
      HasDerivAt (fun x => Real.exp x * (x - 2) + x) (Real.exp t * (t - 2) + Real.exp t + 1) t :=
    hmul.add (hasDerivAt_id t)
  have hadd :
      HasDerivAt (fun x => Real.exp x * (x - 2) + x + 2)
        (Real.exp t * (t - 2) + Real.exp t + 1) t :=
    hadd1.add_const 2
  have hderiv :
      Real.exp t * (t - 2) + Real.exp t + 1 = Real.exp t * (t - 1) + 1 := by ring
  have h0 : HasDerivAt f (Real.exp t * (t - 2) + Real.exp t + 1) t := by
    dsimp [f]
    exact hadd
  simpa [hderiv] using h0

/-- f'(t) > 0 for t > 0. -/
private lemma f_deriv_pos {t : ℝ} (ht : 0 < t) : 0 < deriv f t := by
  rw [(f_deriv t).deriv]
  have h : Real.exp t * (1 - t) < 1 := by
    have ht0 : (-t : ℝ) ≠ 0 := by simpa using (neg_ne_zero.2 (ne_of_gt ht))
    have hlt : 1 - t < Real.exp (-t) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (add_one_lt_exp (x := -t) ht0)
    have hexp_pos : 0 < Real.exp t := Real.exp_pos t
    have hmul : Real.exp t * (1 - t) < Real.exp t * Real.exp (-t) :=
      (mul_lt_mul_of_pos_left hlt hexp_pos)
    have hmul' : Real.exp t * Real.exp (-t) = 1 := by
      calc
        Real.exp t * Real.exp (-t) = Real.exp t * (Real.exp t)⁻¹ := by simp [Real.exp_neg]
        _ = 1 := by simp
    exact lt_of_lt_of_eq hmul hmul'
  have : Real.exp t * (t - 1) = -(Real.exp t * (1 - t)) := by ring
  linarith

/-- `f` is strictly increasing on `[0, ∞)`. -/
private lemma strictMonoOn_f_Ici : StrictMonoOn f (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · have hcont :
        Continuous fun t : ℝ => Real.exp t * (t - 2) + t + 2 :=
      ((Real.continuous_exp.mul (continuous_id.sub continuous_const)).add continuous_id).add
        continuous_const
    simpa [f] using hcont.continuousOn
  · intro x hx
    have hx' : 0 < x := by simpa [interior_Ici] using hx
    exact f_deriv_pos hx'

/-- f(t) ≥ 0 for all t ≥ 0. -/
private lemma f_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [f_zero]
  · have h0 : (0 : ℝ) ∈ Set.Ici 0 := by simp
    have ht' : t ∈ Set.Ici 0 := by exact le_of_lt ht
    have hlt : f 0 < f t := strictMonoOn_f_Ici h0 ht' ht
    simpa [f_zero] using (le_of_lt hlt)

/-- The Binet kernel K(t) is nonnegative for t > 0. -/
theorem K_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ K t := by
  rw [K_eq_f_div ht]
  have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos ht
  have hdenom : 0 < 2 * t * (Real.exp t - 1) := by positivity
  apply div_nonneg _ hdenom.le
  exact f_nonneg (le_of_lt ht)

/-- The normalized kernel K̃(t) is nonnegative for t ≥ 0. -/
theorem Ktilde_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Ktilde t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [Ktilde_zero]; norm_num
  · rw [Ktilde_pos hpos]
    have hK : 0 ≤ K t := K_nonneg hpos
    rw [K_pos hpos] at hK
    exact div_nonneg hK (le_of_lt hpos)

/-! ### Upper bound -/

/-! ### Auxiliary function g for the Ktilde bound -/

/-- The auxiliary function g(t) = (t² - 6t + 12)e^t - (t² + 6t + 12).
We show g(t) ≥ 0 for t ≥ 0, which implies the bound Ktilde t ≤ 1/12. -/
private def gAux (t : ℝ) : ℝ :=
  (t ^ 2 - 6 * t + 12) * Real.exp t - (t ^ 2 + 6 * t + 12)

/-! #### Taylor/series route: a polynomial lower bound for `gAux` -/

private lemma exp_poly5_le_exp {t : ℝ} (ht : 0 ≤ t) :
    1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + t ^ 5 / 120 ≤ Real.exp t := by
  simpa [Finset.sum_range_succ, Nat.factorial, div_eq_mul_inv] using
    (Real.sum_le_exp_of_nonneg ht 6)

private lemma gAux_lower_bound_poly {t : ℝ} (ht : 0 ≤ t) :
    t ^ 5 * (t ^ 2 - t + 2) / 120 ≤ gAux t := by
  have hA : 0 ≤ t ^ 2 - 6 * t + 12 := by
    -- `(t - 3)^2 + 3 ≥ 0`.
    have : t ^ 2 - 6 * t + 12 = (t - 3) ^ 2 + 3 := by ring
    nlinarith [sq_nonneg (t - 3)]
  have hexp :=
    (mul_le_mul_of_nonneg_left (exp_poly5_le_exp ht) hA)
  have hexp' :
      (t ^ 2 - 6 * t + 12) *
            (1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + t ^ 5 / 120) -
          (t ^ 2 + 6 * t + 12)
        ≤ gAux t := by
    simpa [gAux, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using
      sub_le_sub_right hexp (t ^ 2 + 6 * t + 12)
  have hpoly :
      (t ^ 2 - 6 * t + 12) *
            (1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + t ^ 5 / 120) -
          (t ^ 2 + 6 * t + 12)
        = t ^ 5 * (t ^ 2 - t + 2) / 120 := by
    ring
  simpa [hpoly] using hexp'

private lemma gAux_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gAux t := by
  have hquad : 0 ≤ t ^ 2 - t + 2 := by
    have : t ^ 2 - t + 2 = (t - (1 / 2)) ^ 2 + (7 / 4) := by ring
    nlinarith [sq_nonneg (t - (1 / 2))]
  have hpow : 0 ≤ t ^ 5 := pow_nonneg ht 5
  have h : 0 ≤ t ^ 5 * (t ^ 2 - t + 2) / 120 := by
    have : 0 ≤ t ^ 5 * (t ^ 2 - t + 2) := mul_nonneg hpow hquad
    exact div_nonneg this (by norm_num)
  exact h.trans (gAux_lower_bound_poly ht)

private lemma gAux_pos {t : ℝ} (ht : 0 < t) : 0 < gAux t := by
  have hquad : 0 < t ^ 2 - t + 2 := by
    have : t ^ 2 - t + 2 = (t - (1 / 2)) ^ 2 + (7 / 4) := by ring
    nlinarith [sq_nonneg (t - (1 / 2))]
  have hpow : 0 < t ^ 5 := pow_pos ht 5
  have h : 0 < t ^ 5 * (t ^ 2 - t + 2) / 120 := by
    have : 0 < t ^ 5 * (t ^ 2 - t + 2) := mul_pos hpow hquad
    exact div_pos this (by norm_num)
  exact h.trans_le (gAux_lower_bound_poly ht.le)

/-- A convenient closed form for `Ktilde` when `t > 0`. -/
private lemma Ktilde_eq_f_div {t : ℝ} (ht : 0 < t) :
    Ktilde t = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
  calc
    Ktilde t = (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := Ktilde_pos ht
    _ = K t / t := by
        simp [K_pos ht]
    _ = (f t / (2 * t * (Real.exp t - 1))) / t := by
        simp [K_eq_f_div ht]
    _ = f t / (2 * t ^ 2 * (Real.exp t - 1)) := by
        field_simp

private lemma denom_pos {t : ℝ} (ht : 0 < t) : (0 : ℝ) < 2 * t ^ 2 * (Real.exp t - 1) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
  have hexp : 0 < Real.exp t - 1 := exp_sub_one_pos ht
  nlinarith

/-- Upper bound for `Ktilde` on `[0, ∞)`. -/
theorem Ktilde_le {t : ℝ} (ht : 0 ≤ t) : Ktilde t ≤ 1/12 := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [Ktilde_zero]
  · have hD : (0 : ℝ) < 2 * t ^ 2 * (Real.exp t - 1) := denom_pos hpos
    have h12 : (0 : ℝ) < (12 : ℝ) := by norm_num
    rw [Ktilde_eq_f_div hpos, div_le_div_iff₀ hD h12]
    have h_nonneg : 0 ≤ gAux t := gAux_nonneg hpos.le
    have hgoal : 0 ≤ 2 * gAux t := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h_nonneg
    unfold gAux at hgoal
    unfold f
    linarith [hgoal, Real.exp_pos t, sq_nonneg t]

/-- Strict upper bound for `Ktilde` on `(0, ∞)`. -/
theorem Ktilde_lt {t : ℝ} (ht : 0 < t) : Ktilde t < 1 / 12 := by
  have hD : (0 : ℝ) < 2 * t ^ 2 * (Real.exp t - 1) := denom_pos ht
  have h12 : (0 : ℝ) < (12 : ℝ) := by norm_num
  rw [Ktilde_eq_f_div ht, div_lt_div_iff₀ hD h12]
  have hpos_g : 0 < gAux t := gAux_pos ht
  have hpos : 0 < 2 * gAux t := mul_pos (by norm_num) hpos_g
  unfold gAux at hpos
  unfold f
  linarith [hpos, Real.exp_pos t, sq_nonneg t]

end Binet
