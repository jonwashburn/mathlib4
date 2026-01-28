/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.J
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.Bounds

/-!
# Real-part identities for the Binet integral

This file contains the real-part integral expression for `re (J x)` and the key recurrence
`re (J x) - re (J (x+1)) = (x + 1/2) * log (1 + 1/x) - 1`.

These are used to relate Binet's integral representation to the real logarithm of `Γ`.
-/

noncomputable section

open Real Complex Set MeasureTheory Filter Topology
open scoped BigOperators

namespace Binet

/-- Real-part version of the Binet integral: for `x > 0`,
`re (J x) = ∫₀^∞ K̃(t) * exp(-t*x) dt`. -/
theorem re_J_eq_integral_Ktilde {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re = ∫ t in Set.Ioi (0 : ℝ), Ktilde t * Real.exp (-t * x) := by
  have hx' : 0 < (x : ℂ).re := by simpa using hx
  rw [Binet.J_eq_integral (z := (x : ℂ)) hx']
  have hInt :
      Integrable (fun t : ℝ => (Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Binet.J_well_defined (z := (x : ℂ)) hx'
  have hre :
      ∫ t in Set.Ioi (0 : ℝ),
          ((Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ))).re
        = (∫ t in Set.Ioi (0 : ℝ),
              (Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ))).re := by
    simpa using
      (integral_re (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (f := fun t : ℝ => (Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ))) hInt)
  rw [← hre]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro t _ht
  dsimp
  have hexp : Complex.exp (-t * (x : ℂ)) = (Real.exp (-t * x) : ℂ) := by
    have harg : (-t * (x : ℂ)) = ((-t * x : ℝ) : ℂ) := by simp
    calc
      Complex.exp (-t * (x : ℂ)) = Complex.exp ((-t * x : ℝ) : ℂ) := by simp [harg]
      _ = (Real.exp (-t * x) : ℂ) := by simp
  rw [hexp]
  simp [-Complex.ofReal_exp]

/-- Auxiliary identity: for `t > 0`,
`K̃(t) * (1 - exp(-t)) = ∫_{u∈[0,1]} (1/2 - u) * exp(-u*t) du`. -/
lemma Ktilde_mul_one_sub_exp_eq_integral {t : ℝ} (ht : 0 < t) :
    Ktilde t * (1 - Real.exp (-t)) =
      ∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hIcc :
      (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)) =
        ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-u * t) := by
    have hIccIoc :
        (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)) =
          ∫ u in Set.Ioc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) := by
      simpa using
        (MeasureTheory.integral_Icc_eq_integral_Ioc
          (μ := (volume : Measure ℝ)) (f := fun u : ℝ => (1 / 2 - u) * Real.exp (-u * t))
          (x := (0 : ℝ)) (y := (1 : ℝ)))
    have hIoc :
        ∫ u in Set.Ioc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) =
          ∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-u * t) := by
      simpa using
        (intervalIntegral.integral_of_le (μ := (volume : Measure ℝ))
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun u : ℝ => (1 / 2 - u) * Real.exp (-u * t)) (by norm_num : (0 : ℝ) ≤ 1)).symm
    exact hIccIoc.trans hIoc
  rw [hIcc]
  have hInt_exp : IntervalIntegrable (fun u : ℝ => Real.exp (-u * t)) volume (0 : ℝ) 1 := by
    have hcont : Continuous (fun u : ℝ => Real.exp (-u * t)) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := (volume : Measure ℝ)) (0 : ℝ) 1
  have hInt_u_exp :
      IntervalIntegrable (fun u : ℝ => u * Real.exp (-u * t)) volume (0 : ℝ) 1 := by
    have hcont : Continuous (fun u : ℝ => u * Real.exp (-u * t)) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := (volume : Measure ℝ)) (0 : ℝ) 1
  have h_split :
      (∫ u in (0 : ℝ)..1, (1 / 2 - u) * Real.exp (-u * t)) =
        (1 / 2 : ℝ) * (∫ u in (0 : ℝ)..1, Real.exp (-u * t)) -
          (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) := by
    have hlin :
        (fun u : ℝ => (1 / 2 - u) * Real.exp (-u * t)) =
          (fun u : ℝ => (1 / 2 : ℝ) * Real.exp (-u * t)) - fun u : ℝ => u * Real.exp (-u * t) := by
      funext u
      simp [sub_mul]
    rw [hlin]
    have hInt1 :
        IntervalIntegrable (fun u : ℝ => (1 / 2 : ℝ) * Real.exp (-u * t)) volume (0 : ℝ) 1 :=
      hInt_exp.const_mul (1 / 2 : ℝ)
    simpa [intervalIntegral.integral_const_mul] using
      (intervalIntegral.integral_sub (μ := (volume : Measure ℝ)) hInt1 hInt_u_exp)
  rw [h_split]
  have h_exp :
      (∫ u in (0 : ℝ)..1, Real.exp (-u * t)) = (1 - Real.exp (-t)) / t := by
    have ht0' : (-t) ≠ 0 := neg_ne_zero.2 ht0
    calc
      (∫ u in (0 : ℝ)..1, Real.exp (-u * t))
          = ∫ u in (0 : ℝ)..1, Real.exp (u * (-t)) := by
              simp
      _ = (-t)⁻¹ • ∫ x in (0 : ℝ) * (-t)..(1 : ℝ) * (-t), Real.exp x := by
            simpa using
              (intervalIntegral.integral_comp_mul_right (a := (0 : ℝ)) (b := (1 : ℝ))
                (f := fun x : ℝ => Real.exp x) (c := -t) ht0')
      _ = (-t)⁻¹ • (Real.exp (-t) - 1) := by
            simp [integral_exp]
      _ = (-t)⁻¹ * (Real.exp (-t) - 1) := by simp [smul_eq_mul]
      _ = (1 - Real.exp (-t)) / t := by
            field_simp [ht0]
            ring_nf
  have h_u_exp :
      (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) =
        (1 - Real.exp (-t) * (t + 1)) / (t ^ 2) := by
    -- integration by parts: take `u ↦ u`, `v' ↦ exp(-u*t)`, so `v ↦ -exp(-u*t)/t`.
    let ufun : ℝ → ℝ := fun u => u
    let vfun : ℝ → ℝ := fun u => -Real.exp (-u * t) / t
    have hu : ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt ufun 1 u := by
      intro u _hu
      simpa [ufun] using (hasDerivAt_id u)
    have hv :
        ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt vfun (Real.exp (-u * t)) u := by
      intro u _hu
      have h_inner : HasDerivAt (fun u : ℝ => -u * t) (-t) u := by
        simpa [mul_assoc] using ((hasDerivAt_id u).mul_const (-t))
      have h_exp' :
          HasDerivAt (fun u : ℝ => Real.exp (-u * t)) ((-t) * Real.exp (-u * t)) u := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          (Real.hasDerivAt_exp (-u * t)).comp u h_inner
      have hneg : HasDerivAt (fun u : ℝ => -Real.exp (-u * t)) (-(((-t) * Real.exp (-u * t)))) u :=
        h_exp'.neg
      have hdiv : HasDerivAt (fun u : ℝ => -Real.exp (-u * t) / t)
          (-(((-t) * Real.exp (-u * t))) / t) u := hneg.div_const t
      -- simplify the derivative
      simpa [vfun, ht0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    have hu' : IntervalIntegrable (fun _u : ℝ => (1 : ℝ)) volume (0 : ℝ) 1 := by
      simp
    have hv' : IntervalIntegrable (fun u : ℝ => Real.exp (-u * t)) volume (0 : ℝ) 1 :=
      hInt_exp
    have hparts :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := (1 : ℝ))
        (u := ufun) (u' := fun _ => (1 : ℝ)) (v := vfun) (v' := fun u => Real.exp (-u * t))
        hu hv hu' hv'
    -- solve for the target integral and simplify
    have hI :
        (∫ u in (0 : ℝ)..1, ufun u * Real.exp (-u * t)) =
          ufun 1 * vfun 1 - ufun 0 * vfun 0 - ∫ u in (0 : ℝ)..1, (1 : ℝ) * vfun u := by
      simpa using hparts
    have hI' :
        (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) =
          -Real.exp (-t) / t + (1 / t) * ∫ u in (0 : ℝ)..1, Real.exp (-u * t) := by
      -- turn the integration-by-parts identity into a clean formula
      -- and pull the constant `1/t` out of the remaining integral
      have hI1 :
          (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) =
            (1 : ℝ) * vfun 1 - (0 : ℝ) * vfun 0 - ∫ u in (0 : ℝ)..1, (1 : ℝ) * vfun u := by
        simpa [ufun] using hI
      have hv1 : vfun 1 = -Real.exp (-t) / t := by
        simp [vfun]
      have hv0 : vfun 0 = -(1 : ℝ) / t := by
        simp [vfun]
      have hInt_v :
          (∫ u in (0 : ℝ)..1, vfun u) =
            (-1 / t) * ∫ u in (0 : ℝ)..1, Real.exp (-(u * t)) := by
        -- `vfun u = (-1/t) * exp(-(u*t))`
        simp [vfun, div_eq_mul_inv, intervalIntegral.integral_const_mul, mul_comm]
      calc
        (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t))
            = (1 : ℝ) * vfun 1 - (0 : ℝ) * vfun 0 - ∫ u in (0 : ℝ)..1, (1 : ℝ) * vfun u := hI1
        _ = -Real.exp (-t) / t - ∫ u in (0 : ℝ)..1, vfun u := by
              simp [hv1, hv0]
        _ = -Real.exp (-t) / t - ((-1 / t) * ∫ u in (0 : ℝ)..1, Real.exp (-(u * t))) := by
              simp [hInt_v]
        _ = -Real.exp (-t) / t + (1 / t) * ∫ u in (0 : ℝ)..1, Real.exp (-u * t) := by
              -- rewrite `exp (-(u*t))` as `exp (-u*t)`
              have :
                  (∫ u in (0 : ℝ)..1, Real.exp (-(u * t))) =
                    ∫ u in (0 : ℝ)..1, Real.exp (-u * t) := by
                simp
              simp [this]
              ring
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    -- now substitute the closed form for `∫ exp(-u*t)` and normalize
    have hrew :
        (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) =
          (1 - Real.exp (-t) * (t + 1)) / (t ^ 2) := by
      -- `h_exp` was proved just above
      -- Normalize `exp (-u*t)` as `exp (-(t*u))` for robust algebra.
      have hI'' :
          (∫ u in (0 : ℝ)..1, u * Real.exp (-(t * u))) =
            -Real.exp (-t) / t + (1 / t) * ∫ u in (0 : ℝ)..1, Real.exp (-(t * u)) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hI'
      have h_exp'' :
          (∫ u in (0 : ℝ)..1, Real.exp (-(t * u))) = (1 - Real.exp (-t)) / t := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using h_exp
      have hnorm : (∫ u in (0 : ℝ)..1, u * Real.exp (-u * t)) =
          ∫ u in (0 : ℝ)..1, u * Real.exp (-(t * u)) := by
        have hfun :
            (fun u : ℝ => u * Real.exp (-(u * t))) = fun u => u * Real.exp (-(t * u)) := by
          funext u
          simp [mul_comm]
        simp [hfun]
      rw [hnorm]
      calc
        (∫ u in (0 : ℝ)..1, u * Real.exp (-(t * u)))
            = -Real.exp (-t) / t + (1 / t) * ∫ u in (0 : ℝ)..1, Real.exp (-(t * u)) := hI''
        _ = -Real.exp (-t) / t + (1 / t) * ((1 - Real.exp (-t)) / t) := by
              simp [h_exp'']
        _ = (1 - Real.exp (-t) * (t + 1)) / (t ^ 2) := by
              field_simp [ht0, ht2, pow_two]
              ring_nf
    simpa using hrew
  have hkernel : Ktilde t = (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := by
    simpa [one_div] using (Ktilde_pos (t := t) ht)
  rw [h_exp, h_u_exp, hkernel]
  have h_exp_ne : Real.exp t - 1 ≠ 0 := by
    have h1 : 1 < Real.exp t := (Real.one_lt_exp_iff).2 ht
    exact ne_of_gt (sub_pos.2 h1)
  field_simp [ht0, h_exp_ne, Real.exp_neg, pow_two]
  have h_exp_mul : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [h_exp_mul]

/-- Recurrence for the real part of the Binet integral. -/
theorem re_J_sub_re_J_add_one {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re - (Binet.J ((x : ℂ) + 1)).re =
      (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := by
  have hx1 : 0 < x + 1 := by linarith
  have hJx : (Binet.J (x : ℂ)).re =
      ∫ t in Set.Ioi (0 : ℝ), Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx
  have hJx1 : (Binet.J ((x : ℂ) + 1)).re =
      ∫ t in Set.Ioi (0 : ℝ), Ktilde t * Real.exp (-t * (x + 1)) := by
    simpa using (re_J_eq_integral_Ktilde (x := x + 1) hx1)
  rw [hJx, hJx1]
  have hInt_x :
      IntegrableOn (fun t : ℝ => Ktilde t * Real.exp (-t * x)) (Set.Ioi 0) :=
    integrable_Ktilde_exp (x := x) hx
  have hInt_x1 :
      IntegrableOn (fun t : ℝ => Ktilde t * Real.exp (-t * (x + 1))) (Set.Ioi 0) :=
    integrable_Ktilde_exp (x := x + 1) hx1
  have hsub :
      (∫ t in Set.Ioi (0 : ℝ), Ktilde t * Real.exp (-t * x)) -
        (∫ t in Set.Ioi (0 : ℝ), Ktilde t * Real.exp (-t * (x + 1))) =
        ∫ t in Set.Ioi (0 : ℝ),
          (Ktilde t * Real.exp (-t * x) - Ktilde t * Real.exp (-t * (x + 1))) := by
    simpa [sub_eq_add_neg] using
      (MeasureTheory.integral_sub (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (hf := hInt_x) (hg := hInt_x1)).symm
  rw [hsub]
  have hintegrand :
      (fun t : ℝ =>
          Ktilde t * Real.exp (-t * x) - Ktilde t * Real.exp (-t * (x + 1)))
        = fun t : ℝ => Ktilde t * Real.exp (-t * x) * (1 - Real.exp (-t)) := by
    funext t
    have : Real.exp (-t * (x + 1)) = Real.exp (-t * x) * Real.exp (-t) := by
      have : -t * (x + 1) = (-t * x) + (-t) := by ring
      simp [this, Real.exp_add, mul_comm]
    rw [this]
    ring
  rw [hintegrand]
  have hkernel :
      ∀ t ∈ Set.Ioi (0 : ℝ),
        Ktilde t * (1 - Real.exp (-t)) =
          ∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) := by
    intro t ht
    exact Ktilde_mul_one_sub_exp_eq_integral (t := t) ht
  have hswap1 :
      ∫ t in Set.Ioi (0 : ℝ), Ktilde t * Real.exp (-t * x) * (1 - Real.exp (-t)) =
        ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    dsimp
    have : Ktilde t * Real.exp (-t * x) * (1 - Real.exp (-t)) =
        Real.exp (-t * x) * (Ktilde t * (1 - Real.exp (-t))) := by ring
    rw [this, hkernel t ht]
  rw [hswap1]
  let F : ℝ → ℝ → ℝ := fun t u =>
    Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))
  have hF_int :
      Integrable (Function.uncurry F)
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have hmeas :
        AEStronglyMeasurable (Function.uncurry F)
          ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
      have hcont : Continuous (Function.uncurry F) := by
        simpa [F] using (by fun_prop)
      exact hcont.aestronglyMeasurable
    refine (MeasureTheory.integrable_prod_iff hmeas).2 ?_
    constructor
    · refine (MeasureTheory.ae_restrict_iff' (μ := volume)
        (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).2 ?_
      refine MeasureTheory.ae_of_all _ ?_
      intro t ht
      have ht0 : 0 < t := ht
      haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        have : (volume (Set.Icc (0 : ℝ) 1)) ≠ ⊤ := by simp
        exact (MeasureTheory.isFiniteMeasure_restrict).2 this
      refine (MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
        (hg := MeasureTheory.integrable_const (c := (Real.exp (-t * x) / 2 : ℝ))) ?_ ?_)
      · have : Continuous fun u : ℝ => F t u := by
          have : Continuous fun u : ℝ => (1 / 2 - u) * Real.exp (-u * t) := by
            fun_prop
          exact continuous_const.mul this
        exact this.aestronglyMeasurable
      · refine (MeasureTheory.ae_restrict_iff' (μ := volume)
          (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc).2 ?_
        refine MeasureTheory.ae_of_all _ ?_
        intro u hu
        have hu0 : 0 ≤ u := hu.1
        have hu1 : u ≤ 1 := hu.2
        have h_abs : |(1 / 2 - u) * Real.exp (-u * t)| ≤ (1 / 2 : ℝ) := by
          have h1 : |1 / 2 - u| ≤ (1 / 2 : ℝ) := by
            refine (abs_sub_le_iff).2 ?_
            constructor <;> linarith [hu0, hu1]
          have h2 : |Real.exp (-u * t)| ≤ (1 : ℝ) := by
            have : -u * t ≤ 0 := by
              have : 0 ≤ u * t := mul_nonneg hu0 (le_of_lt ht0)
              linarith
            have := Real.exp_le_one_iff.mpr this
            have hpos : 0 ≤ Real.exp (-u * t) := (Real.exp_pos _).le
            simpa [abs_of_nonneg hpos] using this
          calc
            |(1 / 2 - u) * Real.exp (-u * t)| = |1 / 2 - u| * |Real.exp (-u * t)| := by
                simp [abs_mul]
            _ ≤ (1 / 2 : ℝ) * 1 := by
                gcongr
            _ = (1 / 2 : ℝ) := by ring
        have h_exp_nonneg : 0 ≤ Real.exp (-t * x) := (Real.exp_pos _).le
        have :
            |F t u| ≤ Real.exp (-t * x) / 2 := by
          dsimp [F]
          have : |Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))|
              = |Real.exp (-t * x)| * |(1 / 2 - u) * Real.exp (-u * t)| := by
                simp [abs_mul]
          rw [this]
          have habs_exp : |Real.exp (-t * x)| = Real.exp (-t * x) := by simp
          rw [habs_exp]
          have := mul_le_mul_of_nonneg_left h_abs h_exp_nonneg
          simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
        simpa [Real.norm_eq_abs, abs_of_nonneg h_exp_nonneg] using this
    · haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        have : (volume (Set.Icc (0 : ℝ) 1)) ≠ ⊤ := by simp
        exact (MeasureTheory.isFiniteMeasure_restrict).2 this
      have hbound :
          ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
            (∫ u : ℝ, ‖(Function.uncurry F) (t, u)‖ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
              ≤ (Real.exp (-t * x) / 2 : ℝ) := by
        refine (MeasureTheory.ae_restrict_iff' (μ := volume)
          (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).2 ?_
        refine MeasureTheory.ae_of_all _ ?_
        intro t ht
        have ht0 : 0 < t := ht
        have h_point :
            ∀ u ∈ Set.Icc (0 : ℝ) 1,
              ‖F t u‖ ≤ (Real.exp (-t * x) / 2 : ℝ) := by
          intro u hu
          have hu0 : 0 ≤ u := hu.1
          have hu1 : u ≤ 1 := hu.2
          have h_abs : |(1 / 2 - u) * Real.exp (-u * t)| ≤ (1 / 2 : ℝ) := by
            have h1 : |1 / 2 - u| ≤ (1 / 2 : ℝ) := by
              have : |u - (1 / 2 : ℝ)| ≤ (1 / 2 : ℝ) := by
                refine (abs_sub_le_iff).2 ?_
                constructor <;> linarith [hu0, hu1]
              simpa [abs_sub_comm] using this
            have h2 : |Real.exp (-u * t)| ≤ (1 : ℝ) := by
              have : -u * t ≤ 0 := by
                have : 0 ≤ u * t := mul_nonneg hu0 (le_of_lt ht0)
                linarith
              have hexp : Real.exp (-u * t) ≤ (1 : ℝ) := Real.exp_le_one_iff.mpr this
              have hpos : 0 ≤ Real.exp (-u * t) := (Real.exp_pos _).le
              simpa [abs_of_nonneg hpos] using hexp
            calc
              |(1 / 2 - u) * Real.exp (-u * t)| = |1 / 2 - u| * |Real.exp (-u * t)| := by
                  simp [abs_mul]
              _ ≤ (1 / 2 : ℝ) * 1 := by
                  gcongr
              _ = (1 / 2 : ℝ) := by ring
          have h_exp_nonneg : 0 ≤ Real.exp (-t * x) := (Real.exp_pos _).le
          have :
              |F t u| ≤ Real.exp (-t * x) / 2 := by
            dsimp [F]
            calc
              |Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))|
                  = Real.exp (-t * x) * |(1 / 2 - u) * Real.exp (-u * t)| := by
                      simp [abs_mul]
              _ ≤ Real.exp (-t * x) * (1 / 2 : ℝ) := by
                      gcongr
              _ = Real.exp (-t * x) / 2 := by ring
          simpa [Real.norm_eq_abs] using this
        have hmono :
            (fun u : ℝ => ‖F t u‖) ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
              fun _u : ℝ => (Real.exp (-t * x) / 2 : ℝ) := by
          refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Icc (0 : ℝ) 1)
            measurableSet_Icc).2 ?_
          refine MeasureTheory.ae_of_all _ ?_
          intro u hu
          exact h_point u hu
        have hconst :
            (∫ u : ℝ, (Real.exp (-t * x) / 2 : ℝ) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
              = Real.exp (-t * x) / 2 := by
          simp
        have hF_integrable :
            Integrable (fun u : ℝ => F t u) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
          apply Continuous.integrableOn_Icc
          unfold F
          fun_prop
        have hconst_integrable : Integrable (fun _u : ℝ => (Real.exp (-t * x) / 2 : ℝ))
            (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) := by
          exact integrable_const _
        have habs_integrable : Integrable (fun u : ℝ => |F t u|)
            (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) := by
          exact hF_integrable.abs
        have hmono' :
            (fun u : ℝ => |F t u|) ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
              fun _u : ℝ => (Real.exp (-t * x) / 2 : ℝ) := by
          simp_rw [Real.norm_eq_abs] at hmono
          exact hmono
        have := MeasureTheory.integral_mono_ae habs_integrable hconst_integrable hmono'
        simpa [hconst] using this
      have hdom : Integrable (fun t : ℝ => (Real.exp (-t * x) / 2 : ℝ))
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
        have : IntegrableOn (fun t : ℝ => Real.exp (-t * x)) (Set.Ioi 0) := by
          have h := integrableOn_exp_mul_Ioi (a := -x) (c := (0:ℝ)) (by linarith : (-x : ℝ) < 0)
          simpa [mul_assoc, mul_comm, mul_left_comm] using h
        have h2 : IntegrableOn (fun t => Real.exp (-t * x) / 2) (Set.Ioi 0) := by
          simp only [div_eq_mul_inv]
          exact this.mul_const (2⁻¹)
        exact h2.integrable
      refine
        (MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Ioi (0 : ℝ))) (hg := hdom) ?_ ?_)
      · have hmeas' :
            AEStronglyMeasurable
              (fun t : ℝ =>
                ∫ u : ℝ, ‖(Function.uncurry F) (t, u)‖ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
              (volume.restrict (Set.Ioi (0 : ℝ))) := by
          have hF_meas' : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖Function.uncurry F p‖)
              ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
            exact AEStronglyMeasurable.norm hmeas
          exact AEStronglyMeasurable.integral_prod_right' hF_meas'
        exact hmeas'
      · filter_upwards [hbound] with t ht
        calc ‖∫ u : ℝ, ‖Function.uncurry F (t, u)‖ ∂volume.restrict (Icc 0 1)‖
            = ∫ u : ℝ, ‖Function.uncurry F (t, u)‖ ∂volume.restrict (Icc 0 1) := by
              apply Real.norm_of_nonneg
              apply MeasureTheory.integral_nonneg
              intro u
              exact norm_nonneg _
          _ ≤ rexp (-t * x) / 2 := ht
  have hswap :
      ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t))
        =
        ∫ u in Set.Icc (0 : ℝ) 1,
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)) := by
    have hswap0 :
        (∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1, F t u) =
          ∫ u in Set.Icc (0 : ℝ) 1, ∫ t in Set.Ioi (0 : ℝ), F t u := by
      simpa [Function.uncurry] using
      (MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (ν := volume.restrict (Set.Icc (0 : ℝ) 1)) (f := fun t u => F t u) hF_int)
    have hLHS :
        (∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1, F t u) =
          ∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioi (0 : ℝ))
        measurableSet_Ioi).2 ?_
      refine MeasureTheory.ae_of_all _ ?_
      intro t ht
      have :
          (∫ u in Set.Icc (0 : ℝ) 1, F t u) =
            Real.exp (-t * x) * ∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t) := by
        simp [F, MeasureTheory.integral_const_mul]
      simp [this]
    have hswap1 :
        (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t))) =
          ∫ u in Set.Icc (0 : ℝ) 1, ∫ t in Set.Ioi (0 : ℝ), F t u := by
      calc
        (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-t * x) * (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * Real.exp (-u * t)))
            =
            ∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Icc (0 : ℝ) 1, F t u := by
              simpa using hLHS.symm
        _ = ∫ u in Set.Icc (0 : ℝ) 1, ∫ t in Set.Ioi (0 : ℝ), F t u := hswap0
    simpa [F] using hswap1
  rw [hswap]
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h_inner :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)))
          = (1 / 2 - u) * (1 / (x + u)) := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have hxu : 0 < x + u := by linarith [hx, hu0]
    have hmul :
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))) =
          (1 / 2 - u) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * (x + u))) := by
      have hrew : (fun t : ℝ => Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))) =
          fun t : ℝ => (1 / 2 - u) * Real.exp (-(t * (x + u))) := by
        funext t
        have hexp :
            Real.exp (-t * x) * Real.exp (-u * t) = Real.exp ((-t * x) + (-u * t)) := by
          simpa using (Real.exp_add (-t * x) (-u * t)).symm
        have hadd : (-t * x) + (-u * t) = -(t * (x + u)) := by ring
        calc
          Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))
              = (1 / 2 - u) * (Real.exp (-t * x) * Real.exp (-u * t)) := by ring
          _ = (1 / 2 - u) * Real.exp ((-t * x) + (-u * t)) := by
                  simpa using congrArg (fun y => (1 / 2 - u) * y) hexp
          _ = (1 / 2 - u) * Real.exp (-(t * (x + u))) := by
                  simpa using congrArg (fun y => (1 / 2 - u) * Real.exp y) hadd
      have hrew_int :
          (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t))) =
            ∫ t in Set.Ioi (0 : ℝ), (1 / 2 - u) * Real.exp (-(t * (x + u))) := by
        simpa using congrArg (fun f : ℝ → ℝ => ∫ t in Set.Ioi (0 : ℝ), f t) hrew
      calc
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)))
            = ∫ t in Set.Ioi (0 : ℝ), (1 / 2 - u) * Real.exp (-(t * (x + u))) := hrew_int
        _ = (1 / 2 - u) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * (x + u))) := by
            simp [MeasureTheory.integral_const_mul]
    have hbase : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * (x + u)))) = 1 / (x + u) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using (integral_exp_neg_mul_Ioi (x := x + u) hxu)
    calc
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)))
          = (1 / 2 - u) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * (x + u))) := hmul
      _ = (1 / 2 - u) * (1 / (x + u)) := by simp [hbase]
  have h_inner_int :
      (∫ u in Set.Icc (0 : ℝ) 1,
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) * ((1 / 2 - u) * Real.exp (-u * t)))
        = ∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * (1 / (x + u)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro u hu
    exact h_inner u hu
  rw [h_inner_int]
  have hrew_u :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (1 / 2 - u) * (1 / (x + u)) = (x + 1 / 2) * (1 / (x + u)) - 1 := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have hx_u : x + u ≠ 0 := by
      have : 0 < x + u := by linarith [hx, hu0]
      exact ne_of_gt this
    field_simp [hx_u]
    ring_nf
  have hrew_u_int :
      (∫ u in Set.Icc (0 : ℝ) 1, (1 / 2 - u) * (1 / (x + u))) =
        ∫ u in Set.Icc (0 : ℝ) 1, ((x + 1 / 2) * (1 / (x + u)) - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro u hu
    simpa using hrew_u u hu
  rw [hrew_u_int]
  have hxpos : 0 < x := hx
  have h_shift :
      (∫ u in Set.Icc (0 : ℝ) 1, (1 / (x + u) : ℝ)) = Real.log (1 + 1 / x) := by
    have hIcc :
        (∫ u in Set.Icc (0 : ℝ) 1, (1 / (x + u) : ℝ)) = ∫ u in (0 : ℝ)..1, (1 / (x + u) : ℝ) := by
      have hIccIoc :
          (∫ u in Set.Icc (0 : ℝ) 1, (1 / (x + u) : ℝ)) =
            ∫ u in Set.Ioc (0 : ℝ) 1, (1 / (x + u) : ℝ) := by
        simpa using
          (MeasureTheory.integral_Icc_eq_integral_Ioc
            (μ := (volume : Measure ℝ)) (f := fun u : ℝ => (1 / (x + u) : ℝ))
            (x := (0 : ℝ)) (y := (1 : ℝ)))
      have hIoc :
          ∫ u in Set.Ioc (0 : ℝ) 1, (1 / (x + u) : ℝ) = ∫ u in (0 : ℝ)..1, (1 / (x + u) : ℝ) := by
        simpa using
          (intervalIntegral.integral_of_le (μ := (volume : Measure ℝ))
            (a := (0 : ℝ)) (b := (1 : ℝ)) (f := fun u : ℝ => (1 / (x + u) : ℝ))
            (by norm_num : (0 : ℝ) ≤ 1)).symm
      exact hIccIoc.trans hIoc
    rw [hIcc]
    have hshift' :
        (∫ u in (0 : ℝ)..1, (1 / (x + u) : ℝ)) = ∫ u in x..(x + 1), (1 / u : ℝ) := by
      simp
    rw [hshift']
    have hx0' : (0 : ℝ) ∉ Set.uIcc x (x + 1) := by
      intro hxmem
      have hxle : x ≤ x + 1 := by linarith
      have hxmem' : (0 : ℝ) ∈ Set.Icc x (x + 1) := by
        simpa [Set.uIcc, hxle, min_eq_left hxle, max_eq_right hxle] using hxmem
      have hx_le0 : x ≤ (0 : ℝ) := (Set.mem_Icc.1 hxmem').1
      linarith [hxpos, hx_le0]
    have hinv : (∫ u in x..(x + 1), (u : ℝ)⁻¹) = Real.log ((x + 1) / x) := by
      simpa [one_div] using (integral_inv (a := x) (b := x + 1) hx0')
    have hdiv : (x + 1) / x = 1 + 1 / x := by
      field_simp [hx0]
    simpa [one_div, hdiv] using hinv
  have hI1 : (∫ u in Set.Icc (0 : ℝ) 1, (1 : ℝ)) = 1 := by simp
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hInt_inv :
      Integrable (fun u : ℝ => (x + u)⁻¹) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    refine (MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
      (hg := MeasureTheory.integrable_const (c := ‖(x⁻¹ : ℝ)‖)) ?_ ?_)
    · exact (Measurable.inv ((measurable_const.add measurable_id))).aestronglyMeasurable
    · refine (MeasureTheory.ae_restrict_iff' (μ := volume)
        (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc).2 ?_
      refine MeasureTheory.ae_of_all _ ?_
      intro u hu
      have hu0 : 0 ≤ u := hu.1
      have hxle : x ≤ x + u := by linarith
      have hxpos' : 0 < x := hxpos
      have hxupos : 0 < x + u := lt_of_lt_of_le hxpos' hxle
      have : (x + u)⁻¹ ≤ x⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hxpos' hxle
      have hnorm1 : ‖(x + u)⁻¹‖ = (x + u)⁻¹ := by
        simp [Real.norm_eq_abs, abs_of_pos hxupos]
      have hnorm2 : ‖(x⁻¹ : ℝ)‖ = x⁻¹ := by
        simp [Real.norm_eq_abs, abs_of_pos hxpos']
      simpa [hnorm1, hnorm2] using this
  have hInt_mul :
      Integrable (fun u : ℝ => (x + (1 / 2 : ℝ)) * (x + u)⁻¹)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hInt_inv.const_mul (x + (1 / 2 : ℝ))
  have hInt_const :
      Integrable (fun _u : ℝ => (-1 : ℝ)) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    integrable_const _
  have hadd :
      (∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ) + (x + (1 / 2 : ℝ)) * (x + u)⁻¹) =
        (∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ)) +
          ∫ u in Set.Icc (0 : ℝ) 1, (x + (1 / 2 : ℝ)) * (x + u)⁻¹ := by
    simpa using
      (MeasureTheory.integral_add (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) hInt_const hInt_mul)
  have hmul_shift :
      (∫ u in Set.Icc (0 : ℝ) 1, (x + (1 / 2 : ℝ)) * (x + u)⁻¹)
        = (x + (1 / 2 : ℝ)) * Real.log (1 + 1 / x) := by
    calc
      (∫ u in Set.Icc (0 : ℝ) 1, (x + (1 / 2 : ℝ)) * (x + u)⁻¹)
          = (x + (1 / 2 : ℝ)) * ∫ u in Set.Icc (0 : ℝ) 1, (x + u)⁻¹ := by
              simp [MeasureTheory.integral_const_mul]
      _ = (x + (1 / 2 : ℝ)) * Real.log (1 + 1 / x) := by
              simpa [one_div] using congrArg (fun z => (x + (1 / 2 : ℝ)) * z) h_shift
  have hconst : (∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ)) = -1 := by simp
  have hrew_goal :
      (∫ u in Set.Icc (0 : ℝ) 1, (x + (1 / 2 : ℝ)) * (1 / (x + u)) - 1) =
        ∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ) + (x + (1 / 2 : ℝ)) * (x + u)⁻¹ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro u hu
    simp [one_div, sub_eq_add_neg, add_comm, mul_comm]
  rw [hrew_goal]
  calc
    ∫ u in Set.Icc (0 : ℝ) 1, (-1 : ℝ) + (x + (1 / 2 : ℝ)) * (x + u)⁻¹
        = (-1) + (x + (1 / 2 : ℝ)) * Real.log (1 + 1 / x) := by
            rw [hadd, hconst, hmul_shift]
    _ = (x + (1 / 2 : ℝ)) * Real.log (1 + 1 / x) - 1 := by ring

/-! ## Positivity and bounds for `re (J x)` -/

/-- Integrability of the real Binet integrand `K̃(t) * exp(-t*x)` on `(0,∞)` for `x > 0`. -/
theorem integrable_Ktilde_mul_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Ktilde t * Real.exp (-t * x)) (Set.Ioi 0) := by
  simpa [IntegrableOn] using (integrable_Ktilde_exp (x := x) hx)

/-- **Positivity of the Binet integral (real part).**

For `x > 0`, the Binet correction term satisfies `(Binet.J x).re > 0`. -/
theorem re_J_pos {x : ℝ} (hx : 0 < x) : 0 < (Binet.J (x : ℂ)).re := by
  have hJ : (Binet.J (x : ℂ)).re =
      ∫ t in Set.Ioi (0 : ℝ), Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx
  let f : ℝ → ℝ := fun t => Ktilde t * Real.exp (-t * x)
  have hf_int : IntegrableOn f (Set.Ioi (0 : ℝ)) volume := by
    simpa [f] using (integrable_Ktilde_mul_exp_neg_mul (x := x) hx)
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hK0 : 0 ≤ Ktilde t := Ktilde_nonneg (le_of_lt ht)
    exact mul_nonneg hK0 (Real.exp_nonneg _)
  have hμ_support : (0 : ENNReal) < volume (Function.support f ∩ Set.Ioi (0 : ℝ)) := by
    have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Function.support f ∩ Set.Ioi (0 : ℝ) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have hKpos : 0 < Ktilde t := by
        have hconst : 0 < (1 / 12 : ℝ) * Real.exp (-t / 12) := by
          have : (0 : ℝ) < (1 / 12 : ℝ) := by norm_num
          exact mul_pos this (Real.exp_pos _)
        exact lt_of_lt_of_le hconst (one_div_twelve_mul_exp_neg_div_twelve_le_Ktilde ht0)
      have hf_ne : f t ≠ 0 := ne_of_gt (mul_pos hKpos (Real.exp_pos _))
      have ht_support : t ∈ Function.support f := by
        simpa [Function.mem_support] using hf_ne
      exact ⟨ht_support, ht.1⟩
    have hvol_pos : (0 : ENNReal) < volume (Set.Ioc (0 : ℝ) 1) := by simp
    exact lt_of_lt_of_le hvol_pos (measure_mono hsub)
  have hf_pos : 0 < ∫ t in Set.Ioi (0 : ℝ), f t ∂volume := by
    refine
      (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
        (μ := volume) (s := Set.Ioi (0 : ℝ)) hf_nonneg hf_int).2 hμ_support
  simpa [hJ, f] using hf_pos

/-- **Upper bound for the Binet integral (real part).** For `x > 0`, we have
`(Binet.J (x : ℂ)).re ≤ 1 / (12 * x)`. -/
theorem re_J_le_one_div_twelve {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re ≤ 1 / (12 * x) := by
  have h₁ : (Binet.J (x : ℂ)).re ≤ |(Binet.J (x : ℂ)).re| := le_abs_self _
  have h₂ : |(Binet.J (x : ℂ)).re| ≤ 1 / (12 * x) :=
    (Complex.abs_re_le_norm (Binet.J (x : ℂ))).trans (Binet.J_norm_le_real (x := x) hx)
  exact h₁.trans h₂

/-- Compatibility alias: historical name for the strict upper bound on `re (J x)`. -/
theorem re_J_lt_one_div_twelve {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re < 1 / (12 * x) := by
  have hJ : (Binet.J (x : ℂ)).re =
      ∫ t in Set.Ioi (0 : ℝ), Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx
  let f : ℝ → ℝ := fun t => Ktilde t * Real.exp (-t * x)
  let g : ℝ → ℝ := fun t => (1 / 12 : ℝ) * Real.exp (-t * x)
  let h : ℝ → ℝ := fun t => g t - f t
  have hf_int : IntegrableOn f (Set.Ioi (0 : ℝ)) volume := by
    simpa [f] using (integrable_Ktilde_mul_exp_neg_mul (x := x) hx)
  have hg_int : IntegrableOn g (Set.Ioi (0 : ℝ)) volume := by
    simpa [g] using (Binet.integrable_const_mul_exp (x := x) hx)
  have hh_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] h := by
    have : ∀ᵐ t ∂volume, t ∈ Set.Ioi (0 : ℝ) → 0 ≤ h t := by
      refine MeasureTheory.ae_of_all _ ?_
      intro t ht
      have hK : Ktilde t ≤ (1 / 12 : ℝ) := Ktilde_le (le_of_lt ht)
      have hE : 0 ≤ Real.exp (-t * x) := Real.exp_nonneg _
      dsimp [h, f, g]
      refine sub_nonneg.2 ?_
      exact mul_le_mul_of_nonneg_right hK hE
    exact
      (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).2 this
  have hh_int : IntegrableOn h (Set.Ioi (0 : ℝ)) volume := by
    simpa [h] using (hg_int.sub hf_int)
  have hμ_support : (0 : ENNReal) < volume (Function.support h ∩ Set.Ioi (0 : ℝ)) := by
    have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Function.support h ∩ Set.Ioi (0 : ℝ) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htI : t ∈ Set.Ioi (0 : ℝ) := ht0
      have hK : Ktilde t < (1 / 12 : ℝ) := Ktilde_lt ht0
      have hE : 0 < Real.exp (-t * x) := Real.exp_pos _
      have : h t ≠ 0 := by
        have : 0 < h t := by
          dsimp [h, f, g]
          have hlt :
              Ktilde t * Real.exp (-t * x) < (1 / 12 : ℝ) * Real.exp (-t * x) := by
            exact mul_lt_mul_of_pos_right hK hE
          exact sub_pos.2 hlt
        exact ne_of_gt this
      have ht_support : t ∈ Function.support h := by
        simp [Function.mem_support, this]
      exact ⟨ht_support, htI⟩
    have hvol_pos : (0 : ENNReal) < volume (Set.Ioc (0 : ℝ) 1) := by simp
    exact lt_of_lt_of_le hvol_pos (measure_mono hsub)
  have hh_pos : 0 < ∫ t in Set.Ioi (0 : ℝ), h t := by
    have := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae (μ := volume)
      (s := Set.Ioi (0 : ℝ)) (f := h) hh_nonneg hh_int).2 hμ_support
    simpa using this
  have hsub_eq :
      (∫ t in Set.Ioi (0 : ℝ), h t) =
        (∫ t in Set.Ioi (0 : ℝ), g t) - (∫ t in Set.Ioi (0 : ℝ), f t) := by
    simpa [h, sub_eq_add_neg] using
      (MeasureTheory.integral_sub (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (hf := hg_int) (hg := hf_int))
  have hlt_fg : (∫ t in Set.Ioi (0 : ℝ), f t) < (∫ t in Set.Ioi (0 : ℝ), g t) := by
    have : 0 < (∫ t in Set.Ioi (0 : ℝ), g t) - (∫ t in Set.Ioi (0 : ℝ), f t) := by
      simpa [hsub_eq] using hh_pos
    exact (sub_pos.mp this)
  have hg_val : (∫ t in Set.Ioi (0 : ℝ), g t) = 1 / (12 * x) := by
    have hbase : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * x)) = 1 / x := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using (Binet.integral_exp_neg_mul_Ioi (x := x) hx)
    calc
      (∫ t in Set.Ioi (0 : ℝ), g t)
          = (1 / 12 : ℝ) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * x)) := by
              simp [g, MeasureTheory.integral_const_mul, mul_comm]
      _ = (1 / 12 : ℝ) * (1 / x) := by simp [hbase]
      _ = 1 / (12 * x) := by ring
  have : (Binet.J (x : ℂ)).re < 1 / (12 * x) := by
    have : (∫ t in Set.Ioi (0 : ℝ), f t) < 1 / (12 * x) := by
      have : (∫ t in Set.Ioi (0 : ℝ), f t) < (∫ t in Set.Ioi (0 : ℝ), g t) := hlt_fg
      exact lt_of_lt_of_eq this hg_val
    simpa [hJ, f] using this
  exact this

end Binet
