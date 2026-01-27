/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrability of the Binet kernel

This file proves basic boundedness and integrability statements for the normalized Binet kernel
`Binet.Ktilde`, used in Binet's integral representation of `log Γ`.

## Tags

gamma, binet, kernel, integrable
-/

noncomputable section

open Real Set MeasureTheory

namespace Binet

/-! ## Boundedness -/

/-- `Ktilde` is bounded on `[0, ∞)`. -/
lemma Ktilde_bdd : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖Ktilde t‖ ≤ C := by
  refine ⟨(1 / 12 : ℝ), ?_⟩
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (Ktilde_nonneg ht)]
  exact Ktilde_le ht

/-! ## Integrability -/

/-- The kernel \(t \mapsto K̃(t)\,e^{-tx}\) is integrable on \((0,∞)\) for \(x>0\). -/
theorem integrable_Ktilde_exp {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => Ktilde t * exp (-t * x))
      (Measure.restrict volume (Ioi 0)) := by
  have h_exp_int : IntegrableOn (fun t : ℝ => exp (-x * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hx) 0
  have h_exp_int' : IntegrableOn (fun t : ℝ => exp (-t * x)) (Ioi 0) :=
    h_exp_int.congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
  obtain ⟨C, hC⟩ := Ktilde_bdd
  have h_meas :
      AEStronglyMeasurable Ktilde (Measure.restrict volume (Ioi 0)) :=
    (continuousOn_Ktilde_Ioi.aestronglyMeasurable measurableSet_Ioi)
  have h_bdd_ae :
      ∀ᵐ t ∂(Measure.restrict volume (Ioi 0)), ‖Ktilde t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hC t (le_of_lt ht)
  exact h_exp_int'.integrable.bdd_mul h_meas h_bdd_ae

/-- The Binet integral \(\int_0^\infty K̃(t)e^{-tz}\,dt\) converges for \(\Re(z)>0\). -/
theorem integrable_Ktilde_exp_complex {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun t : ℝ => (Ktilde t : ℂ) * Complex.exp (-t * z))
      (Measure.restrict volume (Ioi 0)) := by
  have h_neg_re : (-z).re < 0 := by simp [hz]
  have h_exp_int : IntegrableOn (fun t : ℝ => Complex.exp ((-z) * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi h_neg_re 0
  have h_exp_int' : IntegrableOn (fun t : ℝ => Complex.exp (-t * z)) (Ioi 0) :=
    h_exp_int.congr_fun (fun t _ => by simp; ring_nf) measurableSet_Ioi
  obtain ⟨C, hC⟩ := Ktilde_bdd
  have h_meas :
      AEStronglyMeasurable (fun t : ℝ => (Ktilde t : ℂ))
        (Measure.restrict volume (Ioi 0)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (continuousOn_Ktilde_Ioi.aestronglyMeasurable measurableSet_Ioi)
  have h_bdd_ae :
      ∀ᵐ t ∂(Measure.restrict volume (Ioi 0)),
        ‖(Ktilde t : ℂ)‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa [Complex.norm_real] using hC t (le_of_lt ht)
  exact h_exp_int'.integrable.bdd_mul h_meas h_bdd_ae

end Binet
