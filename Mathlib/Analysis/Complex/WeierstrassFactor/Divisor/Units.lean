/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Complex.WeierstrassFactor.Divisor.Index
import Mathlib.Analysis.Complex.WeierstrassFactor.Lemmas

/-!
# Local nonvanishing and units for divisor-indexed Weierstrass factors

This file bundles local nonvanishing statements for the factors
`weierstrassFactor m (z / a)` indexed by `divisorZeroIndex₀`, on punctured balls that isolate a
single divisor-support point.

The main definition is `Complex.Hadamard.weierstrassFactorUnits`, which views these factors as
`Units ℂ` on such punctured balls.
-/

noncomputable section

open Set

namespace Complex.Hadamard

lemma divisorZeroIndex₀_val_eq_of_mem_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε) :
    divisorZeroIndex₀_val p = z₀ := by
  have hsupp : divisorZeroIndex₀_val p ∈ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support :=
    divisorZeroIndex₀_val_mem_support p
  have : divisorZeroIndex₀_val p ∈ ({z₀} : Set ℂ) := by
    simpa [hball] using show divisorZeroIndex₀_val p ∈
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support from ⟨hp, hsupp⟩
  simpa [Set.mem_singleton_iff] using this

lemma weierstrassFactor_div_ne_zero_on_ball_of_val_ne
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (hp : divisorZeroIndex₀_val p ≠ z₀) :
    ∀ z ∈ Metric.ball z₀ ε, weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
  intro z hzball h0
  have ha : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
  have hz_eq : z = divisorZeroIndex₀_val p := by
    have : z / divisorZeroIndex₀_val p = 1 := by
      simpa [weierstrassFactor_eq_zero_iff (m := m)] using h0
    exact (div_eq_one_iff_eq ha).1 this
  have hz0 : z = z₀ := by
    have hz_support : z ∈ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support := by
      simp [hz_eq, divisorZeroIndex₀_val_mem_support (p := p)]
    have : z ∈ ({z₀} : Set ℂ) := by
      simpa [hball] using
        (show z ∈ Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support from
          ⟨hzball, hz_support⟩)
    simpa [Set.mem_singleton_iff] using this
  have : divisorZeroIndex₀_val p = z₀ := hz_eq.symm.trans hz0
  exact hp this

lemma weierstrassFactor_div_ne_zero_on_ball_punctured
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀}) :
    ∀ z ∈ Metric.ball z₀ ε, z ≠ z₀ →
      ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
  intro z hz hz0 p
  by_cases hp : divisorZeroIndex₀_val p = z₀
  · have hz1 : z / divisorZeroIndex₀_val p ≠ (1 : ℂ) := by
      have ha : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
      simpa [hp] using (mt (div_eq_one_iff_eq ha).1 (by simpa [hp] using hz0))
    exact (weierstrassFactor_ne_zero_iff m (z / divisorZeroIndex₀_val p)).mpr hz1
  · exact weierstrassFactor_div_ne_zero_on_ball_of_val_ne (m := m) (f := f) (z₀ := z₀)
        (ε := ε) hball p (by simpa using hp) z hz

/-- View the Weierstrass factors `weierstrassFactor m (z / a)` as units on a punctured isolating
ball around `z₀`. -/
noncomputable def weierstrassFactorUnits
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ)
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (z : ℂ) (hz : z ∈ Metric.ball z₀ ε) (hz0 : z ≠ z₀) :
    divisorZeroIndex₀ f (Set.univ : Set ℂ) → Units ℂ :=
  fun p =>
    Units.mk0 (weierstrassFactor m (z / divisorZeroIndex₀_val p))
      (weierstrassFactor_div_ne_zero_on_ball_punctured (m := m) (f := f) (z₀ := z₀)
        (ε := ε) hball z hz hz0 p)

@[simp] lemma weierstrassFactorUnits_coe
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ)
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (z : ℂ) (hz : z ∈ Metric.ball z₀ ε) (hz0 : z ≠ z₀)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    ((weierstrassFactorUnits (m := m) (f := f) (z₀ := z₀) (ε := ε)
        hball z hz hz0 p : Units ℂ) : ℂ) =
      weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  simp [weierstrassFactorUnits]

end Complex.Hadamard
