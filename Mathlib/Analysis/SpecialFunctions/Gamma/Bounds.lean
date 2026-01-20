/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

open Real Set MeasureTheory Filter Asymptotics
open scoped Real Topology

namespace Real.Gamma

/-- For `a ∈ [1 / 2, 1]`, we have `Gamma a ≤ Gamma (1 / 2) = √π`.
This uses convexity of Gamma and the fact that `Γ(1) = 1 < √π = Γ(1 / 2)`. -/
lemma Gamma_le_Gamma_one_half {a : ℝ} (ha_low : 1 / 2 ≤ a) (ha_high : a ≤ 1) :
    Real.Gamma a ≤ Real.Gamma (1 / 2) := by
  have h_convex := Real.convexOn_Gamma
  have h1 : Real.Gamma 1 = 1 := Real.Gamma_one
  have h_half : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  -- √π > 1
  have h_sqrt_pi_gt_one : 1 < Real.sqrt Real.pi := by
    have hpi : (1 : ℝ) < Real.pi := by
      have h13 : (1 : ℝ) < 3 := by norm_num
      exact h13.trans Real.pi_gt_three
    have : Real.sqrt (1 : ℝ) < Real.sqrt Real.pi := Real.sqrt_lt_sqrt (by norm_num) hpi
    simpa using this
  have h_one_le_half : (1 : ℝ) ≤ Real.Gamma (1 / 2) := by
    rw [h_half]
    have : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    exact (Real.one_le_sqrt).2 this
  let t := 2 - 2*a
  have ht_nonneg : 0 ≤ t := by linarith
  have ht_le_one : t ≤ 1 := by linarith
  have ha_conv : a = t * (1 / 2) + (1 - t) * 1 := by
    field_simp [t]
    ring
  have := h_convex.2 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1)
    ht_nonneg (by linarith : 0 ≤ 1-t) (by linarith : t + (1-t) = 1)
  rw [smul_eq_mul, smul_eq_mul] at this
  calc Real.Gamma a
      = Real.Gamma (t * (1 / 2) + (1 - t) * 1) := by rw [ha_conv]
    _ ≤ t * Real.Gamma (1 / 2) + (1 - t) * Real.Gamma 1 := this
    _ = t * Real.Gamma (1 / 2) + (1 - t) * 1 := by rw [h1]
    _ ≤ t * Real.Gamma (1 / 2) + (1 - t) * Real.Gamma (1 / 2) := by
        have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht_le_one
        have hmul : (1 - t) * 1 ≤ (1 - t) * Real.Gamma (1 / 2) := by
          simpa [one_mul] using mul_le_mul_of_nonneg_left h_one_le_half h1t
        -- `add_le_add_right` produces the terms in the opposite order; normalize via commutativity.
        have h' :=
          add_le_add_right hmul (t * Real.Gamma (1 / 2))
        simpa [add_comm, add_left_comm, add_assoc] using h'
    _ = Real.Gamma (1 / 2) := by ring

end Gamma
end Real
open Gamma Real

/-- For `a ∈ [1 / 2, 1]` we have `∫₁^∞ e^{-t} t^{a-1} ≤ √π`. -/
lemma integral_exp_neg_rpow_Ioi_one_le {a : ℝ}
    (ha_low : (1 / 2 : ℝ) ≤ a) (ha_high : a ≤ 1) :
    ∫ t in Ioi 1, Real.exp (-t) * t ^ (a - 1) ≤ Real.sqrt Real.pi := by
  have h_split :
      (∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1) ∂volume) =
        (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1) ∂volume) +
        (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1) ∂volume) := by
    have h_int_Ioc :
        IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (a - 1)) (Ioc 0 1) :=
      (Real.GammaIntegral_convergent (by linarith : 0 < a)).mono_set Ioc_subset_Ioi_self
    have h_int_Ioi :
        IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (a - 1)) (Ioi 1) :=
      (Real.GammaIntegral_convergent (by linarith : 0 < a)).mono_set (by
        intro x hx
        exact (lt_trans (by norm_num : (0 : ℝ) < 1) hx))
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using
      (MeasureTheory.setIntegral_union
          (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1))
          measurableSet_Ioi h_int_Ioc h_int_Ioi)
  have h_nonneg :
      (0 : ℝ) ≤ ∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1) := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc ?_
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht.1) _)
  have h_step₁ :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1))
        ≤ (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) +
          (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1)) := by
    simpa using
      (le_add_of_nonneg_right
          (a := ∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1))
          h_nonneg)
  have h_step₂ :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) +
        (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1)) =
        ∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1) := by
    simpa [add_comm] using h_split.symm
  have h_step₃ :
      (∫ x in Ioi 0, Real.exp (-x) * x ^ (a - 1)) = Real.Gamma a := by
    simpa using (Real.Gamma_eq_integral (by linarith : 0 < a)).symm
  have h_le_Gamma :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) ≤ Real.Gamma a := by
    have : (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1))
        ≤ (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1)) +
          (∫ x in Ioc 0 1, Real.exp (-x) * x ^ (a - 1)) := h_step₁
    simpa [h_step₂, h_step₃] using this
  have :
      (∫ x in Ioi 1, Real.exp (-x) * x ^ (a - 1))
        ≤ Real.Gamma (1 / 2) :=
    h_le_Gamma.trans (Gamma_le_Gamma_one_half ha_low ha_high)
  have hGammaHalf : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have hGammaInv : Real.Gamma (2⁻¹) = Real.sqrt Real.pi := by
    simp_rw [inv_eq_one_div]
    aesop
  simpa [hGammaHalf, hGammaInv] using this

@[simp] lemma Complex.re_neg_eq_neg_re (z : ℂ) : (-z).re = -z.re := by
  simp

-- Unit-interval power integral: ∫_{0}^{1} x^s dx = 1 / (s + 1), for s > -1
lemma intervalIntegral.integral_rpow_unit (s : ℝ) (hs : -1 < s) :
    ∫ x in (0 : ℝ)..1, x ^ s = 1 / (s + 1) := by
  have h := (integral_rpow (a := (0 : ℝ)) (b := (1 : ℝ)) (h := Or.inl hs))
  have hne : s + 1 ≠ 0 := by linarith
  simpa [one_rpow, zero_rpow hne] using h

lemma integral_rpow_Ioc_zero_one {s : ℝ} (hs : 0 < s) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (s - 1) = 1 / s := by
  have h_eq : ∫ t in Ioc (0 : ℝ) 1, t ^ (s - 1) = ∫ t in (0)..(1), t ^ (s - 1) := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp
  rw [h_eq]
  have hne : s - 1 ≠ -1 := by linarith
  have hlt : -1 < s - 1 := by linarith
  have h := (integral_rpow (a := (0 : ℝ)) (b := (1 : ℝ)) (h := Or.inl hlt))
  simp [one_rpow, zero_rpow hs.ne'] at h
  simp only [one_div, h]

namespace Complex.Gammaℝ

/- Bound on the norm of `Complex.Gamma` for points with real part in `[1 / 2, 1]`. -/

/-- A uniform bound on `‖Γ(w)‖` when `Re w ∈ [a,1] ⊆ [1 / 2, 1]`. -/
lemma norm_Complex_Gamma_le_of_re_ge' {w : ℂ} {a : ℝ}
    (ha_low : (1 / 2 : ℝ) ≤ a) (_ : a ≤ 1)
    (hw : a ≤ w.re) (hw_ub : w.re ≤ 1) :
    ‖Complex.Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi := by
  have hw_pos : 0 < w.re := by
    have : (0 : ℝ) < (1 / 2) := by norm_num
    exact this.trans_le (ha_low.trans hw)
  have ha_pos : 0 < a := (lt_of_lt_of_le (by norm_num) ha_low)
  have hΓ : Complex.Gamma w =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-t) * t ^ (w - 1) := by
    simpa [Complex.GammaIntegral] using (Complex.Gamma_eq_integral hw_pos)
  have h_norm :
      ‖Complex.Gamma w‖ =
        ‖∫ t in Ioi (0 : ℝ), Complex.exp (-t) * t ^ (w - 1)‖ := by
    rw [hΓ]
  have h_le_int :
      ‖∫ t in Ioi (0 : ℝ), Complex.exp (-t) * t ^ (w - 1)‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖Complex.exp (-t) * t ^ (w - 1)‖ := by
    exact MeasureTheory.norm_integral_le_integral_norm _
  have h_int_real :
      ∫ t in Ioi (0 : ℝ), ‖Complex.exp (-t) * t ^ (w - 1)‖
        = ∫ t in Ioi (0 : ℝ),
            Real.exp (-t) * t ^ (w.re - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have hcpow : ‖(t : ℂ) ^ (w - 1)‖ = t ^ (w.re - 1) := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos ht (w - 1)
    simp [Complex.norm_exp, hcpow]
  have h_split :
      (∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (w.re - 1))
        = (∫ t in Ioc 0 1, Real.exp (-t) * t ^ (w.re - 1))
        + (∫ t in Ioi 1,   Real.exp (-t) * t ^ (w.re - 1)) := by
    have hIoc : IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (w.re - 1))
                              (Ioc 0 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
    have hIoi : IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (w.re - 1))
                              (Ioi 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set
        (fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one ht))
    -- use additivity of the set integral
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using
      (MeasureTheory.setIntegral_union
          (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := 1))
          measurableSet_Ioi hIoc hIoi)
  have h_ae :
      (fun t : ℝ ↦ Real.exp (-t) * t ^ (w.re - 1))
        ≤ᵐ[volume.restrict (Ioc 0 1)]
      (fun t : ℝ ↦                 t ^ (w.re - 1)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
    intro t ht
    -- here `ht : t ∈ Ioc 0 1`, i.e. `0 < t ∧ t ≤ 1`
    have h_exp : Real.exp (-t) ≤ 1 := by
      have : (-t : ℝ) ≤ 0 := by linarith [ht.1]
      exact exp_le_one_iff.mpr this
    have h_nonneg : (0 : ℝ) ≤ t ^ (w.re - 1) :=
      Real.rpow_nonneg (le_of_lt ht.1) _
    simpa using mul_le_of_le_one_left h_nonneg h_exp
  have hIoc₁ :
      IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (w.re - 1)) (Ioc 0 1) :=
    (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
  have hIoc₂ :
      IntegrableOn (fun t : ℝ ↦ t ^ (w.re - 1)) (Ioc 0 1) := by
    have hInt :
        IntervalIntegrable (fun t : ℝ ↦ t ^ (w.re - 1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < w.re - 1)
    simpa using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
          (μ := volume) (a := 0) (b := 1) zero_le_one).1 hInt
  have h_drop_exp :
      (∫ t in Ioc 0 1, Real.exp (-t) * t ^ (w.re - 1))
        ≤ ∫ t in Ioc 0 1, t ^ (w.re - 1) := MeasureTheory.setIntegral_mono_ae_restrict hIoc₁ hIoc₂ h_ae
  have h_Ioc_exact :
      ∫ t in Ioc 0 1, t ^ (w.re - 1) = 1 / w.re :=
    integral_rpow_Ioc_zero_one hw_pos
  have h_Ioi_bound :
      ∫ t in Ioi 1, Real.exp (-t) * t ^ (w.re - 1)
        ≤ Real.sqrt Real.pi := by
    have h_low : (1 / 2 : ℝ) ≤ w.re := ha_low.trans hw
    exact integral_exp_neg_rpow_Ioi_one_le h_low hw_ub
  have h_big :
      ‖Complex.Gamma w‖
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1))
          + (∫ t in Ioi 1, Real.exp (-t) * t ^ (w.re - 1)) := by
    have H :
        ‖∫ t in Ioi (0 : ℝ), Complex.exp (-t) * t ^ (w - 1)‖
          ≤ (∫ t in Ioc 0 1, Real.exp (-t) * t ^ (w.re - 1))
            + (∫ t in Ioi 1, Real.exp (-t) * t ^ (w.re - 1)) := by
      calc
        _ ≤ ∫ t in Ioi (0 : ℝ), ‖Complex.exp (-t) * t ^ (w - 1)‖ := h_le_int
        _ = ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (w.re - 1) := by
              simp_rw [h_int_real]
        _ = (∫ t in Ioc 0 1, Real.exp (-t) * t ^ (w.re - 1))
              + (∫ t in Ioi 1, Real.exp (-t) * t ^ (w.re - 1)) := h_split
    have :
        ‖∫ t in Ioi (0 : ℝ), Complex.exp (-t) * t ^ (w - 1)‖
          ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1))
            + (∫ t in Ioi 1, Real.exp (-t) * t ^ (w.re - 1)) :=
      H.trans (add_le_add_left h_drop_exp _)
    simpa [h_norm] using this
  have h_big' :
      ‖Complex.Gamma w‖ ≤ 1 / w.re + Real.sqrt Real.pi := by
    have : (∫ t in Ioc 0 1, t ^ (w.re - 1))
            + (∫ t in Ioi 1, Real.exp (-t) * t ^ (w.re - 1))
          ≤ 1 / w.re + Real.sqrt Real.pi := by
      simpa [h_Ioc_exact]
        using h_Ioi_bound
    exact h_big.trans this
  have h_one_div : 1 / w.re ≤ 1 / a :=
    one_div_le_one_div_of_le ha_pos hw
  have : 1 / w.re + Real.sqrt Real.pi ≤ 1 / a + Real.sqrt Real.pi :=
    add_le_add_left h_one_div _
  exact h_big'.trans this

/-- Bound on the norm of `Complex.Gamma` when `0 < a ≤ re w ≤ 1`. -/
lemma norm_Complex_Gamma_le_of_re_ge {w : ℂ} {a : ℝ}
    (ha_pos : 0 < a) (hw : a ≤ w.re) (hw_ub : w.re ≤ 1) :
    ‖Complex.Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi := by
  set f : ℝ → ℂ := fun t ↦ Complex.exp (-t) * t ^ (w - 1)
  set g : ℝ → ℝ := fun t ↦ Real.exp (-t) * t ^ (w.re - 1)
  have hw_pos : 0 < w.re := ha_pos.trans_le hw
  have hΓ : Complex.Gamma w = ∫ t in Ioi (0 : ℝ), f t := by
    rw [Complex.Gamma_eq_integral hw_pos]
    simp [Complex.GammaIntegral, f]  -- Changed from rfl to simp
  have h_norm :
      ‖Complex.Gamma w‖ =
        ‖∫ t in Ioi (0 : ℝ), f t‖ := by
    simp [hΓ]
  have h_le_int :
      ‖∫ t in Ioi (0 : ℝ), f t‖
        ≤ ∫ t in Ioi (0 : ℝ), ‖f t‖ := by
    exact MeasureTheory.norm_integral_le_integral_norm _
  have h_int_real :
      ∫ t in Ioi (0 : ℝ), ‖f t‖
        = ∫ t in Ioi (0 : ℝ), g t := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    simp [f, g, Complex.norm_exp,
          Complex.norm_cpow_eq_rpow_re_of_pos ht (w - 1)]
  have h_split :
      (∫ t in Ioi (0 : ℝ), g t)
        = (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t) := by
    have hIoc : IntegrableOn g (Ioc 0 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
    have hIoi : IntegrableOn g (Ioi 1) :=
      (Real.GammaIntegral_convergent hw_pos).mono_set
        (fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht)))  -- Fixed
    simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using
      (MeasureTheory.setIntegral_union
          (Ioc_disjoint_Ioi_same (a := 0) (b := 1))
          measurableSet_Ioi hIoc hIoi)
  have h_ae_drop :
      (fun t : ℝ ↦ g t)
        ≤ᵐ[volume.restrict (Ioc 0 1)]
      (fun t : ℝ ↦ t ^ (w.re - 1)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall ?_)
    intro t ht
    have h_exp : Real.exp (-t) ≤ 1 := by
      have : (-t : ℝ) ≤ 0 := by linarith [ht.1]
      exact exp_le_one_iff.mpr this
    have h_nonneg : (0 : ℝ) ≤ t ^ (w.re - 1) :=
      Real.rpow_nonneg (le_of_lt ht.1) _
    simpa [g] using mul_le_of_le_one_left h_nonneg h_exp
  have hIoc₁ : IntegrableOn g (Ioc 0 1) :=
    (Real.GammaIntegral_convergent hw_pos).mono_set Ioc_subset_Ioi_self
  have hIoc₂ : IntegrableOn (fun t : ℝ ↦ t ^ (w.re - 1)) (Ioc 0 1) := by
    have hInt :
        IntervalIntegrable (fun t : ℝ ↦ t ^ (w.re - 1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < w.re - 1)
    simpa using
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
          (a := 0) (b := 1) zero_le_one).1 hInt
  have h_drop_exp :
      (∫ t in Ioc 0 1, g t)
        ≤ ∫ t in Ioc 0 1, t ^ (w.re - 1) :=
    MeasureTheory.setIntegral_mono_ae_restrict hIoc₁ hIoc₂ h_ae_drop
  have h_big :
      ‖Complex.Gamma w‖
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1))
          + (∫ t in Ioi 1, g t) := by
    have step1 : ‖∫ t in Ioi (0 : ℝ), f t‖
        ≤ (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t) := by
      simpa [h_int_real, h_split] using h_le_int
    have step2 : (∫ t in Ioc 0 1, g t) + (∫ t in Ioi 1, g t)
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1))
          + (∫ t in Ioi 1, g t) := by
      exact add_le_add_left h_drop_exp _
    simpa [h_norm] using (le_trans step1 step2)
  have h_Ioc_exact :
      ∫ t in Ioc 0 1, t ^ (w.re - 1) = 1 / w.re :=
    integral_rpow_Ioc_zero_one hw_pos
  have h_tail :
      ∫ t in Ioi 1, g t ≤ Real.sqrt Real.pi := by
    by_cases hhalf : (1 / 2 : ℝ) ≤ w.re
    · have := integral_exp_neg_rpow_Ioi_one_le hhalf hw_ub
      simpa [g] using this
    · have h_ae :
          (fun t : ℝ ↦ g t)
            ≤ᵐ[volume.restrict (Ioi 1)]
          (fun t : ℝ ↦ Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)) := by
        refine (ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall ?_)
        intro t ht
        have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
        have hpow : t ^ (w.re - 1) ≤ t ^ ((1 / 2 : ℝ) - 1) := by
          have : w.re - 1 ≤ (1 / 2 : ℝ) - 1 := by linarith [hhalf]
          exact Real.rpow_le_rpow_of_exponent_le ht1 this
        have hnonneg : (0 : ℝ) ≤ Real.exp (-t) := (Real.exp_pos _).le
        simpa [g] using mul_le_mul_of_nonneg_left hpow hnonneg
      have hIntL : IntegrableOn g (Ioi 1) :=
        (Real.GammaIntegral_convergent hw_pos).mono_set
          (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hx)))  -- Fixed
      have hIntR : IntegrableOn
            (fun t : ℝ ↦ Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)) (Ioi 1) :=
        (Real.GammaIntegral_convergent (by norm_num : 0 < (1 / 2 : ℝ))).mono_set
          (fun x hx => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hx)))  -- Fixed
      have h_le : ∫ t in Ioi 1, g t
            ≤ ∫ t in Ioi 1, Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1) :=
        MeasureTheory.setIntegral_mono_ae_restrict hIntL hIntR h_ae
      have h_upper :
          ∫ t in Ioi 1, Real.exp (-t) * t ^ ((1 / 2 : ℝ) - 1)
            ≤ Real.sqrt Real.pi := by
        have := integral_exp_neg_rpow_Ioi_one_le
                  (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
                  (by norm_num : (1 / 2 : ℝ) ≤ (1 : ℝ))
        simpa using this
      exact h_le.trans h_upper
  have h_main :
      ‖Complex.Gamma w‖ ≤ 1 / w.re + Real.sqrt Real.pi := by
    calc ‖Complex.Gamma w‖
        ≤ (∫ t in Ioc 0 1, t ^ (w.re - 1)) + (∫ t in Ioi 1, g t) := h_big
      _ = 1 / w.re + (∫ t in Ioi 1, g t) := by rw [h_Ioc_exact]
      _ ≤ 1 / w.re + Real.sqrt Real.pi := by
          exact add_le_add_right h_tail _
  have h_one_div : (1 / w.re : ℝ) ≤ 1 / a :=
    one_div_le_one_div_of_le ha_pos hw
  have : 1 / w.re + Real.sqrt Real.pi ≤ 1 / a + Real.sqrt Real.pi :=
    add_le_add_left h_one_div _
  exact h_main.trans this

/-!
# Gamma function bounds via integral splitting

This file provides explicit bounds for the complex Gamma function `Γ(s)` in the
strip `0 < a ≤ Re(s) ≤ b` by splitting the Euler integral at `t = 1`.

## Main results

* `Gammaℝ.norm_Complex_Gamma_le_of_re_ge`: For `0 < a ≤ Re(w) ≤ 1`,
  we have `‖Γ(w)‖ ≤ 1/a + √π`.

## Mathematical background

The Euler integral `Γ(s) = ∫₀^∞ t^{s-1} e^{-t} dt` converges for `Re(s) > 0`.
For `0 < a ≤ Re(s) ≤ 1`, we split at `t = 1`:

1. **Integral on `[0,1]`**:
   Since `|t^{s-1}| = t^{Re(s)-1} ≤ t^{a-1}` for `t ∈ [0,1]` and `a ≤ Re(s)`,
   and `e^{-t} ≤ 1`, we have
   `∫₀¹ |t^{s-1} e^{-t}| dt ≤ ∫₀¹ t^{a-1} dt = 1/a`.

2. **Integral on `[1,∞)`**:
   Since `Re(s) ≤ 1`, we have `|t^{s-1}| = t^{Re(s)-1} ≤ 1` for `t ≥ 1`.
   Thus `∫₁^∞ |t^{s-1} e^{-t}| dt ≤ ∫₁^∞ e^{-t} dt = e^{-1} < √π`.

Combining: `|Γ(s)| ≤ 1/a + e^{-1} < 1/a + √π`.

A tighter bound uses Gaussian decay estimates, which we import from the
standard Mathlib analysis of Gaussian integrals.
-/

noncomputable section

open Complex Real Set MeasureTheory Filter Topology
open scoped Real Topology BigOperators


/-! ## Auxiliary integral bounds -/

/-- The integral `∫₀¹ t^(a-1) dt = 1/a` for `a > 0`. -/
lemma integral_rpow_zero_one_eq {a : ℝ} (ha : 0 < a) :
    ∫ t in (0 : ℝ)..1, t ^ (a - 1) = 1 / a := by
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < a - 1))]
  simp only [sub_add_cancel]
  simp only [Real.one_rpow, Real.zero_rpow (by linarith : a ≠ 0)]
  ring

/-- The integral `∫₁^∞ e^{-t} dt = e^{-1}`. -/
lemma integral_exp_neg_Ioi_one :
    ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) = Real.exp (-1) := by
  have h_int : IntegrableOn (fun t => Real.exp (-t)) (Set.Ioi 1) := integrableOn_exp_neg_Ioi 1
  -- Use the antiderivative -exp(-t)
  have h_cont : ContinuousWithinAt (fun x => -Real.exp (-x)) (Set.Ici 1) 1 := by
    apply ContinuousAt.continuousWithinAt
    exact (Real.continuous_exp.comp continuous_neg).neg.continuousAt
  have h_deriv : ∀ t ∈ Set.Ioi (1 : ℝ), HasDerivAt (fun x => -Real.exp (-x)) (Real.exp (-t)) t := by
    intro t _ht
    have h1 : HasDerivAt (fun x => -x) (-1) t := hasDerivAt_neg t
    have h2 : HasDerivAt Real.exp (Real.exp (-t)) (-t) := Real.hasDerivAt_exp (-t)
    have h3 : HasDerivAt (fun x => Real.exp (-x)) (Real.exp (-t) * (-1)) t := h2.comp t h1
    have h4 : HasDerivAt (fun x => -Real.exp (-x)) (-(Real.exp (-t) * (-1))) t := h3.neg
    convert h4 using 1
    ring
  have h_tendsto : Tendsto (fun t => -Real.exp (-t)) atTop (𝓝 0) := by
    have : Tendsto (fun t => Real.exp (-t)) atTop (𝓝 0) := tendsto_exp_neg_atTop_nhds_zero
    simpa using this.neg
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto h_cont h_deriv h_int h_tendsto]
  simp [Real.exp_neg]

/-- `e^{-1} < √π`. -/
lemma exp_neg_one_lt_sqrt_pi : Real.exp (-1) < Real.sqrt Real.pi := by
  -- e^{-1} ≈ 0.368, √π ≈ 1.772
  -- We'll show e^{-1} < 1 < √π
  have h1 : Real.exp (-1) < 1 := by
    have : Real.exp 0 = 1 := Real.exp_zero
    have hlt : (-1 : ℝ) < 0 := by norm_num
    calc Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.mpr hlt
      _ = 1 := this
  have h2 : 1 < Real.sqrt Real.pi := by
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hone_lt_pi : 1 < Real.pi := by
      have : (3 : ℝ) < Real.pi := Real.pi_gt_three
      linarith
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hone_lt_pi
  linarith


/-! ## Corollaries -/

/-- Bound when `a = 1 / 2`: `‖Γ(w)‖ ≤ 4` for `1 / 2 ≤ Re(w) ≤ 1`. -/
lemma norm_Gamma_le_four_half_strip {w : ℂ}
    (hw_lo : (1 / 2 : ℝ) ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Complex.Gamma w‖ ≤ 4 := by
  have h := norm_Complex_Gamma_le_of_re_ge (by norm_num : (0 : ℝ) < 1 / 2) hw_lo hw_hi
  have hsqrt : Real.sqrt Real.pi < 2 := by
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have : Real.sqrt Real.pi < Real.sqrt 4 := Real.sqrt_lt_sqrt (le_of_lt Real.pi_pos) hpi4
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (2 : ℝ) ≥ 0)]
    linarith
  calc ‖Complex.Gamma w‖
      ≤ 1 / (1 / 2 : ℝ) + Real.sqrt Real.pi := h
    _ = 2 + Real.sqrt Real.pi := by norm_num
    _ ≤ 2 + 2 := by linarith
    _ = 4 := by ring

/-- Bound when `a = 1 / 4`: `‖Γ(w)‖ ≤ 6` for `1 / 4 ≤ Re(w) ≤ 1`. -/
lemma norm_Gamma_le_six_quarter_strip {w : ℂ}
    (hw_lo : (1 / 4 : ℝ) ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Complex.Gamma w‖ ≤ 6 := by
  have h := norm_Complex_Gamma_le_of_re_ge (by norm_num : (0 : ℝ) < 1 / 4) hw_lo hw_hi
  have hsqrt : Real.sqrt Real.pi < 2 := by
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have : Real.sqrt Real.pi < Real.sqrt 4 := Real.sqrt_lt_sqrt (le_of_lt Real.pi_pos) hpi4
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (2 : ℝ) ≥ 0)]
    linarith
  calc ‖Complex.Gamma w‖
      ≤ 1 / (1 / 4 : ℝ) + Real.sqrt Real.pi := h
    _ = 4 + Real.sqrt Real.pi := by norm_num
    _ ≤ 4 + 2 := by linarith
    _ = 6 := by ring

open Complex Real Set Metric

/-! ### Analyticity of `Γ_ℝ` on the right half-plane -/

/-- `Γ_ℝ` is complex differentiable on the open half-plane `{s | 0 < re s}`. -/
lemma differentiableOn_halfplane :
    DifferentiableOn ℂ Gammaℝ {s : ℂ | 0 < s.re} := by
  intro s hs
  -- Factorization: Γ_ℝ(s) = Γ_ℝ(s') * ∏(s-k) where s' is in (0,1]
  have h_cpow : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) ^ (-z / 2)) s := by
    refine ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow ?_)
    exact Or.inl (ofReal_ne_zero.mpr pi_ne_zero)
  have h_gamma : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) s := by
    have hnot : ∀ m : ℕ, s / 2 ≠ -m := by
      intro m hsm
      have hre := congrArg Complex.re hsm
      have hdiv : s.re / 2 = -(m : ℝ) := by
        simpa [div_ofNat_re, Complex.ofReal_intCast] using hre
      have hsre_eq : s.re = -(2 * (m : ℝ)) := by
        have h' := congrArg (fun x : ℝ => x * 2) hdiv
        have hleft : (s.re / 2) * 2 = s.re := by
          have : s.re * (2 : ℝ) / 2 = s.re := by simp
          simp
        simpa [hleft, mul_comm, neg_mul] using h'
      have hle : s.re ≤ 0 := by
        have : 0 ≤ (2 : ℝ) * (m : ℝ) := by positivity
        simp [hsre_eq]
      exact (not_le.mpr hs) hle
    have hg : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
      (differentiableAt_id.div_const (2 : ℂ))
    exact (differentiableAt_Gamma (s := s / 2) hnot).comp s hg
  simpa [Gammaℝ, Gammaℝ_def] using (h_cpow.mul h_gamma).differentiableWithinAt

/-! ### A Cauchy–derivative bound on a circle (exact, no placeholders)

We derive the standard Cauchy inequality for the derivative at a center `s` from the
Cauchy integral formula for the derivative, and a uniform bound on `‖Gammaℝ‖` along a circle. -/

/-- If `0 < r`, `closedBall s r ⊆ {z | 0 < re z}`, and `‖Gammaℝ z‖ ≤ M` for all `z` on the circle
`sphere s r`, then `‖deriv Gammaℝ s‖ ≤ r⁻¹ * M`. -/
theorem deriv_bound_on_circle
    {s : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hBall : closedBall s r ⊆ {z : ℂ | 0 < z.re})
    (hM : ∀ z ∈ sphere s r, ‖Gammaℝ z‖ ≤ M) :
    ‖deriv Gammaℝ s‖ ≤ r⁻¹ * M := by
  have hUopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hUdiff : DifferentiableOn ℂ Gammaℝ {z : ℂ | 0 < z.re} := differentiableOn_halfplane
  have hsub : closedBall s r ⊆ {z : ℂ | 0 < z.re} := hBall
  have hs_ball : s ∈ ball s r := by
    simp [mem_ball, dist_self, hr]
  have hCauchy :
      ((2 * π * I : ℂ)⁻¹ • ∮ z in C(s, r), ((z - s) ^ 2)⁻¹ • Gammaℝ z)
        = deriv Gammaℝ s := by
    simpa using
      (two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
        (E := ℂ) hUopen (c := s) (w₀ := s) (R := r) (hc := hsub)
        (hf := hUdiff) (hw₀ := by simpa [mem_ball, dist_self] using hr))
  have hker : ∀ z ∈ sphere s r, ‖((z - s) ^ 2)⁻¹ • Gammaℝ z‖ ≤ (r ^ 2)⁻¹ * M := by
    intro z hz
    have hzR : ‖z - s‖ = r := by simpa [dist_eq_norm] using hz
    have : ‖(z - s) ^ 2‖ = ‖z - s‖ ^ 2 := by simp [norm_pow]
    have : ‖(z - s) ^ 2‖ = r ^ 2 := by simp [hzR]
    calc
      ‖((z - s) ^ 2)⁻¹ • Gammaℝ z‖
          = ‖(z - s) ^ 2‖⁻¹ * ‖Gammaℝ z‖ := by simp [norm_inv]
      _ ≤ (r ^ 2)⁻¹ * M := by
        have hHM : ‖Gammaℝ z‖ ≤ M := hM z hz
        have hnonneg : 0 ≤ ‖(z - s) ^ 2‖⁻¹ := by
          exact inv_nonneg.mpr (norm_nonneg _)
        have hnormpow : ‖(z - s) ^ 2‖ = ‖z - s‖ ^ 2 := by simp [norm_pow]
        have hnorm : ‖(z - s) ^ 2‖ = r ^ 2 := by simp [hzR]
        have hinv : ‖(z - s) ^ 2‖⁻¹ = (r ^ 2)⁻¹ := by simp [hnorm]
        have hmul : ‖(z - s) ^ 2‖⁻¹ * ‖Gammaℝ z‖ ≤ ‖(z - s) ^ 2‖⁻¹ * M :=
          mul_le_mul_of_nonneg_left hHM hnonneg
        simp_rw [hinv]; aesop
  have hbound :
      ‖(2 * π * I : ℂ)⁻¹ • ∮ z in C(s, r), ((z - s) ^ 2)⁻¹ • Gammaℝ z‖
        ≤ r * ((r ^ 2)⁻¹ * M) :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (c := s) (R := r) (hR := hr.le) (hf := hker)
  have hbound' : ‖deriv Gammaℝ s‖ ≤ r * ((r ^ 2)⁻¹ * M) :=
    calc
      ‖deriv Gammaℝ s‖
          = ‖(2 * π * I : ℂ)⁻¹ • ∮ z in C(s, r), ((z - s) ^ 2)⁻¹ • Gammaℝ z‖ := by
            simp_rw [hCauchy]
      _ ≤ r * ((r ^ 2)⁻¹ * M) := hbound
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hr
  have hrr : r * ((r ^ 2)⁻¹ * M) = M * r⁻¹ := by
    calc
      r * ((r ^ 2)⁻¹ * M) = (r * (r ^ 2)⁻¹) * M := by
        simp [mul_comm, mul_left_comm]
      _ = (r / r^2) * M := by simp [div_eq_mul_inv]
      _ = (1 / r) * M := by
        have : r / r^2 = 1 / r := by
          calc
            r / r^2 = r / (r * r) := by simp [pow_two]
            _ = (r / r) / r := by simp_rw [div_mul_eq_div_div]
            _ = 1 / r := by simp [hr0]
        simp [this]
      _ = M * r⁻¹ := by simp [one_div, mul_comm]
  have : ‖deriv Gammaℝ s‖ ≤ M * r⁻¹ := by simpa [hrr] using hbound'
  -- normalize the RHS into the stated `r⁻¹ * M` form
  simpa [mul_comm] using this

/-- If `s = σ + it` with `σ ≥ σ0 > 0` and `r = σ0/2`, then the entire closed ball `closedBall s r`
lies in the right half-plane `{z | 0 < re z}`. -/
lemma closedBall_subset_halfplane_of_re_ge
    {σ0 σ t : ℝ} (hσ0 : 0 < σ0) (hσ : σ0 ≤ σ) :
    closedBall (σ + t * I) (σ0 / 2) ⊆ {z : ℂ | 0 < z.re} := by
  intro z hz
  -- |Re(z - s)| ≤ ‖z - s‖ ≤ r ⇒ Re z ≥ Re s - r ≥ σ0 - σ0/2 = σ0/2 > 0
  have hz' : ‖z - (σ + t * I)‖ ≤ σ0 / 2 := by
    simpa [dist_eq_norm] using hz
  have hre : (z - (σ + t * I)).re ≥ -‖z - (σ + t * I)‖ := by
    -- |Re w| ≤ ‖w‖ ⇒ -‖w‖ ≤ Re w
    have := (abs_re_le_norm (z - (σ + t * I)))
    have : |(z - (σ + t * I)).re| ≤ ‖z - (σ + t * I)‖ := this
    exact neg_le_of_abs_le this
  have : z.re ≥ σ - σ0 / 2 := by
    -- z.re ≥ (σ+tI).re - ‖z-(σ+tI)‖
    have h1 : z.re ≥ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have := add_le_add_right hre ((σ + t * I).re)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    -- (σ+tI).re - σ0/2 ≤ (σ+tI).re - ‖z-(σ+tI)‖
    have h2 : (σ + t * I).re - (σ0 / 2) ≤ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have hneg := neg_le_neg hz'
      linarith
    -- combine
    have hzre_ge : (σ + t * I).re - (σ0 / 2) ≤ z.re := le_trans h2 (h1)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_zero] at hzre_ge
    linarith
  have : 0 < z.re := by
    have hσpos : 0 < σ - σ0 / 2 := by linarith
    exact lt_of_lt_of_le hσpos (by simpa [ge_iff_le] using this)
  simpa using this

/-! ### Explicit bounds for `Gammaℝ` on circles and strips -/

/-- A uniform circle bound for `Γ_ℝ(z) = π^{-z/2} Γ(z/2)` over the strip:
on each circle of radius `σ0/2` centered at `σ+it` with `σ ∈ [σ0,1]`, we have
`‖Gammaℝ z‖ ≤ π^{-(σ0/4)} * (4/σ0 + √π)`. -/
def circleBound (σ0 : ℝ) : ℝ := Real.rpow Real.pi (-(σ0 / 4)) * (4 / σ0 + Real.sqrt Real.pi)

lemma norm_H_on_sphere_le
    {σ0 σ t : ℝ} (hσ0 : (1 / 2 : ℝ) < σ0) (hlo : σ0 ≤ σ) (hhi : σ ≤ 1) :
    ∀ z ∈ sphere (σ + t * I) (σ0 / 2), ‖Gammaℝ z‖ ≤ circleBound σ0 := by
  intro z hz
  -- Re z ≥ σ - σ0/2 ≥ σ0/2
  have hz' : ‖z - (σ + t * I)‖ ≤ σ0 / 2 := by simpa [dist_eq_norm] using (mem_sphere.mp hz).le
  have h_re : (σ0 / 2) ≤ z.re := by
    -- z.re ≥ (σ+tI).re - ‖z-(σ+tI)‖ ≥ σ - σ0/2
    have hre : (z - (σ + t * I)).re ≥ -‖z - (σ + t * I)‖ := by
      have := (abs_re_le_norm (z - (σ + t * I)))
      exact (neg_le_of_abs_le this)
    have h1 : z.re ≥ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have := add_le_add_right hre ((σ + t * I).re)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h2 : (σ + t * I).re - σ0 / 2 ≤ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have := neg_le_neg hz'
      linarith
    have : (σ + t * I).re - σ0 / 2 ≤ z.re := le_trans h2 h1
    have : σ - σ0 / 2 ≤ z.re := by simpa [sub_eq_add_neg] using this
    exact (le_trans (by have := hlo; linarith) this)
  have hπ : ‖(π : ℂ) ^ (-(z / 2))‖ ≤ Real.rpow Real.pi (-(σ0 / 4)) := by
    have : Real.rpow Real.pi (-(z.re / 2)) ≤ Real.rpow Real.pi (-(σ0 / 4)) := by
      have : (σ0 / 2) ≤ z.re := h_re
      have h_exp : -(z.re / 2) ≤ -(σ0 / 4) := by
        have : σ0 / 4 ≤ z.re / 2 := by linarith [h_re]
        linarith
      have hpi : (1 : ℝ) < Real.pi := by
        have : (3 : ℝ) < Real.pi := Real.pi_gt_three
        linarith
      have hpow :
          Real.rpow Real.pi (-(z.re / 2)) ≤ Real.rpow Real.pi (-(σ0 / 4)) :=
        Real.rpow_le_rpow_of_exponent_le hpi.le h_exp
      exact hpow
    calc ‖(π : ℂ) ^ (-(z / 2))‖
        = Real.pi ^ (-(z / 2)).re := Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _
      _ = Real.pi ^ (-(z.re / 2)) := by simp [Complex.neg_re]
      _ ≤ Real.pi ^ (-(σ0 / 4)) := this
  let w := z / 2
  have hw_re : (σ0 / 4) ≤ w.re := by
    have : (σ0 / 2) ≤ z.re := h_re
    simpa [w, Complex.div_re] using
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)
  have hw_ub : w.re ≤ 1 := by
    have h_z_ub : z.re ≤ σ + σ0 / 2 := by
      have : |z.re - σ| ≤ σ0 / 2 := by
        have := (abs_re_le_norm (z - (σ + t * I))).trans hz'
        simpa [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
                Complex.mul_re, Complex.I_re, mul_zero, add_zero] using this
      linarith [(abs_sub_le_iff.mp this).left]
    have : z.re ≤ 3/2 := by
      calc z.re
          ≤ σ + σ0 / 2 := h_z_ub
        _ ≤ 1 + 1 / 2 := by linarith [hhi, hσ0]
        _ = 3 / 2 := by norm_num
    calc w.re
        = z.re / 2 := by simp [w]
      _ ≤ (3 / 2) / 2 := by
            exact div_le_div_of_nonneg_right this (by norm_num)
      _ = 3 / 4 := by norm_num
      _ ≤ 1 := by norm_num
  have hΓ : ‖Complex.Gamma w‖ ≤ 4 / σ0 + Real.sqrt Real.pi := by
    have ha : 0 < σ0 / 4 := by linarith [hσ0]
    calc ‖Complex.Gamma w‖
        ≤ 1 / (σ0 / 4) + Real.sqrt Real.pi :=
          norm_Complex_Gamma_le_of_re_ge ha hw_re hw_ub
      _ = 4 / σ0 + Real.sqrt Real.pi := by ring
  have : ‖Gammaℝ z‖ ≤ Real.rpow Real.pi (-(σ0 / 4)) * (4 / σ0 + Real.sqrt Real.pi) := by
    calc ‖Gammaℝ z‖
      _ = ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ := by rw [Complex.Gammaℝ_def]
      _ = ‖(π : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma (z / 2)‖ := Complex.norm_mul _ _
      _ = ‖(π : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma w‖ := by rw [show z / 2 = w from rfl]
      _ ≤ Real.rpow Real.pi (-(σ0 / 4)) * ‖Complex.Gamma w‖ := by
        have : (π : ℂ) ^ (-z / 2) = (π : ℂ) ^ (-(z / 2)) := by ring_nf
        rw [this]
        exact mul_le_mul_of_nonneg_right hπ (norm_nonneg _)
      _ ≤ Real.rpow Real.pi (-(σ0 / 4)) * (4 / σ0 + Real.sqrt Real.pi) :=
        mul_le_mul_of_nonneg_left hΓ (Real.rpow_nonneg Real.pi_pos.le _)
  simpa [circleBound] using this

end Gammaℝ
end Complex
end


end

end Complex.Gammaℝ
