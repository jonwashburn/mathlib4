/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Auxiliary bounds for the Gamma function

This file collects a few standalone bounds on `Real.Gamma` and `Complex.Gamma` used in the Binet /
Stirling development.
-/

noncomputable section

open Real Complex Set MeasureTheory

namespace Binet

/-- For `x ∈ [1, 2]`, we have `Γ(x) ≤ 1` since `Γ(1) = Γ(2) = 1` and `Γ` is convex. -/
theorem Gamma_le_one_of_mem_Icc {x : ℝ} (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    Real.Gamma x ≤ 1 := by
  have h_convex := Real.convexOn_Gamma
  have h1 : Real.Gamma 1 = 1 := Real.Gamma_one
  have h2 : Real.Gamma 2 = 1 := Real.Gamma_two
  let t := 2 - x
  have ht_nonneg : 0 ≤ t := by linarith
  have hx_conv : x = t * 1 + (1 - t) * 2 := by field_simp [t]; ring
  have := h_convex.2 (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)
    ht_nonneg (by linarith : 0 ≤ 1 - t) (by ring : t + (1 - t) = 1)
  rw [smul_eq_mul, smul_eq_mul] at this
  calc Real.Gamma x
      = Real.Gamma (t * 1 + (1 - t) * 2) := by rw [hx_conv]
    _ ≤ t * Real.Gamma 1 + (1 - t) * Real.Gamma 2 := this
    _ = t * 1 + (1 - t) * 1 := by rw [h1, h2]
    _ = 1 := by ring

/-- The integral representation gives the bound `‖Complex.Gamma z‖ ≤ Real.Gamma z.re`
for `0 < z.re`. -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  have h_norm_eq : ∀ t ∈ Set.Ioi (0 : ℝ),
      ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ = Real.exp (-t) * t ^ (z.re - 1) := by
    intro t ht
    have hcpow : ‖(t : ℂ) ^ (z - 1)‖ = t ^ (z.re - 1) := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos ht (z - 1)
    simp [Complex.norm_exp, hcpow]
  calc ‖Complex.GammaIntegral z‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ := by
        unfold Complex.GammaIntegral
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (z.re - 1) := by
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_norm_eq

/-- For `z.re ∈ [1,2]`, we have `‖Complex.Gamma z‖ ≤ 1`. -/
theorem norm_Gamma_le_one {z : ℂ} (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2) :
    ‖Complex.Gamma z‖ ≤ 1 := by
  have hz_pos : 0 < z.re := by linarith
  calc ‖Complex.Gamma z‖
      ≤ Real.Gamma z.re := norm_Gamma_le_Gamma_re hz_pos
    _ ≤ 1 := Gamma_le_one_of_mem_Icc hlo hhi

end Binet
