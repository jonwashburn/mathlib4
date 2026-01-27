/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.Integral
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Limit and continuity for the Binet kernel

This file proves the right-limit at zero for the normalized Binet kernel `Binet.Ktilde`, and
derives global continuity of `Ktilde` on `ℝ`.

## Tags

gamma, binet, kernel, exponential, limit, continuity
-/

noncomputable section

open Real Set Filter
open scoped Topology

namespace Binet

/-! ## Auxiliary limits -/

open Internal

/-- Auxiliary: \((\exp t - 1)/t \to 1\) as \(t \to 0^+\). -/
private lemma tendsto_exp_sub_one_div :
    Tendsto (fun t => (exp t - 1) / t) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
  have h := Real.hasDerivAt_exp 0
  rw [exp_zero] at h
  simpa [inv_mul_eq_div, zero_add, smul_eq_mul] using h.tendsto_slope_zero_right

/-- The Taylor remainder \(h(t) = \exp(t) - 1 - t - t^2/2\) satisfies \(h(t)/t^3 \to 1/6\)
as \(t \to 0^+\). -/
private lemma tendsto_exp_taylor3_div_cube :
    Tendsto (fun t => (exp t - 1 - t - t ^ 2 / 2) / t ^ 3) (𝓝[>] 0) (𝓝 (1 / 6 : ℝ)) := by
  have h_taylor : (fun x =>
          exp x - ∑ i ∈ Finset.range 4, x ^ i / Nat.factorial i) =o[𝓝 0] (· ^ 3) :=
    exp_sub_sum_range_succ_isLittleO_pow 3
  have h_sum :
      ∀ x : ℝ, ∑ i ∈ Finset.range 4, x ^ i / Nat.factorial i = 1 + x + x ^ 2 / 2 + x ^ 3 / 6 := by
    intro x; simp [Finset.sum_range_succ, Nat.factorial]
  have h_decomp : ∀ t : ℝ, exp t - 1 - t - t ^ 2 / 2 =
          (exp t - ∑ i ∈ Finset.range 4, t ^ i / Nat.factorial i) + t ^ 3 / 6 := by
    intro t; rw [h_sum]; ring
  have h_zero : Tendsto (fun t =>
          (exp t - ∑ i ∈ Finset.range 4, t ^ i / Nat.factorial i) / t ^ 3) (𝓝[>] 0) (𝓝 0) := by
    have := h_taylor.tendsto_div_nhds_zero
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have h_add : Tendsto (fun t =>
          (exp t - ∑ i ∈ Finset.range 4, t ^ i / Nat.factorial i) / t ^ 3 + (1 / 6 : ℝ))
        (𝓝[>] 0) (𝓝 (0 + (1 / 6 : ℝ))) :=
    h_zero.add tendsto_const_nhds
  simp only [zero_add] at h_add
  refine h_add.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ 0 := ne_of_gt ht
  rw [h_decomp]; field_simp [hne]

/-! ## Limit of `Ktilde` at zero -/

private lemma tendsto_kernelNum_div_cube :
    Tendsto (fun t => kernelNum t / t ^ 3) (𝓝[>] 0) (𝓝 (1 / 6 : ℝ)) := by
  have h1 :
      Tendsto (fun t => (exp t - 1 - t - t ^ 2 / 2) / t ^ 3 * (t - 2)) (𝓝[>] 0)
        (𝓝 ((1 / 6 : ℝ) * (-2))) := by
    refine (tendsto_exp_taylor3_div_cube.mul ?_)
    have : Tendsto (fun x : ℝ => x - 2) (𝓝 0) (𝓝 (-2)) := by
      simpa using ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 (0 : ℝ))).sub tendsto_const_nhds)
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have h2 : Tendsto (fun t => (1 / 2 : ℝ) + (exp t - 1 - t - t ^ 2 / 2) / t ^ 3 * (t - 2))
        (𝓝[>] 0) (𝓝 ((1 / 2 : ℝ) + (1 / 6 : ℝ) * (-2))) :=
    tendsto_const_nhds.add h1
  have heq : ((1 / 2 : ℝ) + (1 / 6 : ℝ) * (-2)) = (1 / 6 : ℝ) := by norm_num
  rw [← heq]
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ 0 := ne_of_gt ht
  have hdecomp : kernelNum t = t ^ 3 / 2 + (exp t - 1 - t - t ^ 2 / 2) * (t - 2) := by
    dsimp [kernelNum]; ring
  rw [hdecomp]; field_simp [hne]

/-- The kernel `Ktilde(t)` tends to `1/12` as `t → 0⁺`. -/
theorem tendsto_Ktilde_zero : Tendsto Ktilde (𝓝[>] 0) (𝓝 (1 / 12 : ℝ)) := by
  have hK : ∀ᶠ t in 𝓝[>] 0, Ktilde t = kernelNum t / (2 * t ^ 2 * (exp t - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Ktilde_eq_kernelNum_div ht
  rw [tendsto_congr' hK]
  have h4 : ∀ᶠ t in 𝓝[>] 0, kernelNum t / (2 * t ^ 2 * (exp t - 1)) =
          (kernelNum t / t ^ 3) / (2 * ((exp t - 1) / t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hne : t ≠ 0 := ne_of_gt ht
    have hexp' : exp t - 1 ≠ 0 := ne_of_gt (exp_sub_one_pos ht)
    field_simp [hne, hexp']
  rw [tendsto_congr' h4]
  have hlim_num : Tendsto (fun t => kernelNum t / t ^ 3)
    (𝓝[>] 0) (𝓝 (1 / 6 : ℝ)) := tendsto_kernelNum_div_cube
  have hlim_den : Tendsto (fun t => 2 * ((exp t - 1) / t)) (𝓝[>] 0) (𝓝 (2 * (1 : ℝ))) :=
    (tendsto_exp_sub_one_div.const_mul 2)
  have hne : (2 * (1 : ℝ)) ≠ 0 := by norm_num
  convert hlim_num.div hlim_den hne using 1
  norm_num

/-! ## Global continuity -/

/-- The normalized kernel `Ktilde` is continuous on `ℝ`. -/
lemma continuous_Ktilde : Continuous Ktilde := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : 0 < x
  · exact continuousOn_Ktilde_Ioi.continuousAt (Ioi_mem_nhds hx)
  · push_neg at hx
    by_cases hx0 : x < 0
    · have hev : ∀ᶠ y in 𝓝 x, Ktilde y = 1 / 12 := by
        filter_upwards [Iio_mem_nhds hx0] with y hy
        have hy0 : y < 0 := by simpa [mem_Iio] using hy
        simp [Ktilde, le_of_lt hy0]
      have hval : Ktilde x = 1 / 12 := by simp [Ktilde, le_of_lt hx0]
      simpa [ContinuousAt, hval] using (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))
    · have hx_eq : x = 0 := le_antisymm hx (not_lt.mp hx0)
      subst hx_eq
      rw [continuousAt_iff_continuous_left'_right']
      constructor
      · rw [ContinuousWithinAt, Ktilde_zero]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy0 : y < 0 := by simpa [mem_Iio] using hy
        simp [Ktilde, le_of_lt hy0]
      · simpa [ContinuousWithinAt, Ktilde_zero] using tendsto_Ktilde_zero

end Binet
