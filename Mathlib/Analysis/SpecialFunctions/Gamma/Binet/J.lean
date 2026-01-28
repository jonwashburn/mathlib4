/- 
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.Integrability

/-!
# The Binet integral `J`

This file defines the Binet integral term `Binet.J` (for `0 < z.re`) and proves the fundamental
bound `‖J z‖ ≤ 1 / (12 * z.re)`.
-/

noncomputable section

open Real Complex Set MeasureTheory Filter Topology

namespace Binet

/-! ## The Binet integral `J(z)` -/

/-- The Binet integral term in Binet's formula (defined for `0 < z.re`). -/
def J (z : ℂ) : ℂ :=
  if 0 < z.re then
    ∫ t in Set.Ioi (0 : ℝ), (Ktilde t : ℂ) * Complex.exp (-t * z)
  else 0

/-- J(z) is well-defined for `0 < z.re` (the integral converges). -/
lemma J_well_defined {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun t : ℝ => (Ktilde t : ℂ) * Complex.exp (-t * z))
      (Measure.restrict volume (Set.Ioi 0)) :=
  integrable_Ktilde_exp_complex hz

/-- For `0 < z.re`, `J z` equals the defining integral. -/
lemma J_eq_integral {z : ℂ} (hz : 0 < z.re) :
    J z = ∫ t in Set.Ioi (0 : ℝ), (Ktilde t : ℂ) * Complex.exp (-t * z) := by
  simp [J, hz]

lemma norm_Ktilde_mul_exp {z : ℂ} (t : ℝ) (ht : 0 < t) :
    ‖(Ktilde t : ℂ) * Complex.exp (-t * z)‖ = Ktilde t * Real.exp (-t * z.re) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Ktilde_nonneg (le_of_lt ht)), Complex.norm_exp]
  congr 1
  have : ((-↑t * z).re) = -t * z.re := by
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [this]

lemma integrable_const_mul_exp {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => (1 / 12 : ℝ) * Real.exp (-t * x)) (Set.Ioi 0) := by
  apply Integrable.const_mul
  have h := integrableOn_exp_mul_Ioi (neg_neg_of_pos hx) 0
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _
  ring_nf

lemma Ktilde_mul_exp_le {x : ℝ} (t : ℝ) (ht : 0 < t) :
    Ktilde t * Real.exp (-t * x) ≤ (1 / 12 : ℝ) * Real.exp (-t * x) :=
  mul_le_mul_of_nonneg_right (Ktilde_le (le_of_lt ht)) (Real.exp_nonneg _)

lemma integral_exp_neg_mul_Ioi {x : ℝ} (hx : 0 < x) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) = 1 / x := by
  have h := integral_exp_mul_Ioi (neg_neg_of_pos hx) 0
  simp only [mul_zero, Real.exp_zero] at h
  have heq : (fun t => Real.exp (-t * x)) = fun t => Real.exp (-x * t) := by
    ext t; ring_nf
  rw [heq, h]
  field_simp

/-- The fundamental bound `‖J z‖ ≤ 1 / (12 * z.re)` for `0 < z.re`. -/
theorem J_norm_le_re {z : ℂ} (hz : 0 < z.re) : ‖J z‖ ≤ 1 / (12 * z.re) := by
  rw [J_eq_integral hz]
  calc ‖∫ t in Set.Ioi (0 : ℝ), (Ktilde t : ℂ) * Complex.exp (-t * z)‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖(Ktilde t : ℂ) * Complex.exp (-t * z)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), Ktilde t * Real.exp (-t * z.re) := by
        apply MeasureTheory.setIntegral_mono_on
        · exact (J_well_defined hz).norm
        · exact integrable_Ktilde_exp (x := z.re) hz
        · exact measurableSet_Ioi
        · intro t ht
          rw [norm_Ktilde_mul_exp t ht]
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), (1 / 12 : ℝ) * Real.exp (-t * z.re) := by
        apply MeasureTheory.setIntegral_mono_on
        · exact integrable_Ktilde_exp (x := z.re) hz
        · exact integrable_const_mul_exp hz
        · exact measurableSet_Ioi
        · intro t ht
          exact Ktilde_mul_exp_le t ht
    _ = (1 / 12 : ℝ) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * z.re) := by
        rw [← MeasureTheory.integral_const_mul]
    _ = (1 / 12 : ℝ) * (1 / z.re) := by
        rw [integral_exp_neg_mul_Ioi hz]
    _ = 1 / (12 * z.re) := by ring

/-- For real `x > 0`, `‖J (x : ℂ)‖ ≤ 1 / (12 * x)`. -/
theorem J_norm_le_real {x : ℝ} (hx : 0 < x) : ‖J (x : ℂ)‖ ≤ 1 / (12 * x) := by
  have hre : (0 : ℝ) < (x : ℂ).re := by simp [hx]
  have h := J_norm_le_re hre
  simpa using h

lemma tendsto_re_J_atTop : Tendsto (fun y : ℝ => (Binet.J (y : ℂ)).re) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨(1 / (12 * ε) : ℝ) + 1, ?_⟩
  intro y hy
  have hy_pos : 0 < y := by
    have : 0 < (1 / (12 * ε) : ℝ) + 1 := by
      have : 0 < (1 / (12 * ε) : ℝ) := by positivity
      linarith
    exact this.trans_le hy
  have hbound : |(Binet.J (y : ℂ)).re| ≤ 1 / (12 * y) := by
    exact (Complex.abs_re_le_norm (Binet.J (y : ℂ))).trans (J_norm_le_real (x := y) hy_pos)
  have h1 : 1 / (12 * y) < ε := by
    have hy' : 0 < 12 * y := by positivity
    have hy_gt : (1 / (12 * ε) : ℝ) < y := by linarith
    have hpos : 0 < (12 * ε : ℝ) := by positivity
    have htmp : (12 * ε : ℝ) * (1 / (12 * ε : ℝ)) < (12 * ε : ℝ) * y :=
      mul_lt_mul_of_pos_left hy_gt hpos
    have hleft : (12 * ε : ℝ) * (ε⁻¹ * 12⁻¹) = 1 := by
      field_simp [ne_of_gt hε]
    have hbig1 : (1 : ℝ) < (12 * ε : ℝ) * y := by
      -- `simp` has normalized `12*ε*(1/(12*ε))` as `12*ε*(ε⁻¹*12⁻¹)`
      simpa [mul_assoc, hleft] using htmp
    have hbig : (1 : ℝ) < ε * (12 * y) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbig1
    have : (1 : ℝ) / (12 * y) < ε := (div_lt_iff₀ hy').2 (by simpa [mul_assoc] using hbig)
    simpa using this
  have : |(Binet.J (y : ℂ)).re - 0| < ε := by
    simpa using lt_of_le_of_lt hbound h1
  simpa [Real.dist_eq] using this

end Binet

