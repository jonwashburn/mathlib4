/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Weierstrass elementary factors

This file defines the Weierstrass elementary factors
`E_m(z) = (1 - z) * exp (∑_{k=1}^m z^k / k)` (implemented as `Complex.weierstrassFactor`) together
with basic simp/recursion lemmas.

Quantitative bounds and analytic identities are proved in
`Mathlib.Analysis.Complex.WeierstrassFactor.Lemmas`.

## Main definitions

- `Complex.partialLogSum m z`: the partial sum `∑_{k=1}^m z^k / k`
- `Complex.logTail m z`: the tail `∑_{k>m} z^k / k` (as a `tsum` starting at `m+1`)
- `Complex.weierstrassFactor m z`: the elementary factor
  `E_m(z) = (1 - z) * exp (partialLogSum m z)`
-/

noncomputable section

@[expose] public section

open scoped BigOperators

namespace Complex

/-! ## Partial logarithm series -/

/-- The partial sum `∑_{k=1}^m z^k / k` (written with a `Finset.range` index shift). -/
def partialLogSum (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1)

/-- `partialLogSum 0 z = 0`. -/
@[simp]
lemma partialLogSum_zero (z : ℂ) : partialLogSum 0 z = 0 := by
  simp [partialLogSum]

/-- The first partial sum is `partialLogSum 1 z = z`. -/
@[simp]
lemma partialLogSum_one (z : ℂ) : partialLogSum 1 z = z := by
  simp [partialLogSum]

/-- A recursion for `partialLogSum`. -/
lemma partialLogSum_succ (m : ℕ) (z : ℂ) :
    partialLogSum (m + 1) z = partialLogSum m z + z ^ (m + 1) / (m + 1) := by
  simp [partialLogSum, Finset.sum_range_succ]

/-- The tail `∑_{k>m} z^k / k`, written as `∑' k, z^(m+1+k)/(m+1+k)`. -/
def logTail (m : ℕ) (z : ℂ) : ℂ :=
  ∑' k, z ^ (m + 1 + k) / ((m + 1 + k : ℕ) : ℂ)

/-! ## The Weierstrass factor -/

/-- The Weierstrass elementary factor. -/
def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum m z)

/-- The elementary factor `E₀(z) = 1 - z`. -/
@[simp] lemma weierstrassFactor_zero (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor]

/-- The elementary factor `E₁(z) = (1 - z) * exp z`. -/
@[simp] lemma weierstrassFactor_one (z : ℂ) : weierstrassFactor 1 z = (1 - z) * exp z := by
  simp [weierstrassFactor]

/-- The elementary factor at `z = 0` equals `1`. -/
@[simp] lemma weierstrassFactor_at_zero (m : ℕ) : weierstrassFactor m 0 = 1 := by
  simp [weierstrassFactor, partialLogSum]

/-- The elementary factor vanishes at `z = 1`. -/
@[simp] lemma weierstrassFactor_at_one (m : ℕ) : weierstrassFactor m 1 = 0 := by
  simp [weierstrassFactor]

/-- The Weierstrass factor vanishes exactly at `z = 1`. -/
lemma weierstrassFactor_eq_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z = 0 ↔ z = 1 := by
  constructor
  · intro hz
    have hmul : (1 - z) = 0 ∨ exp (partialLogSum m z) = 0 := by
      exact mul_eq_zero.mp (by simpa [weierstrassFactor] using hz)
    have : (1 - z) = 0 := hmul.resolve_right (exp_ne_zero _)
    exact (sub_eq_zero.mp this).symm
  · rintro rfl
    simp [weierstrassFactor]

lemma weierstrassFactor_ne_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z ≠ 0 ↔ z ≠ 1 := by
  simpa using (not_congr (weierstrassFactor_eq_zero_iff m z))

/-- The partial sum `partialLogSum m` is continuous. -/
lemma continuous_partialLogSum (m : ℕ) : Continuous fun z : ℂ => partialLogSum m z := by
  classical
  unfold partialLogSum
  simpa using
    (continuous_finset_sum (Finset.range m) fun k _ => by
      continuity)

/-- The Weierstrass factor is continuous. -/
lemma continuous_weierstrassFactor (m : ℕ) : Continuous fun z : ℂ => weierstrassFactor m z := by
  have hpartial : Continuous fun z : ℂ => partialLogSum m z := continuous_partialLogSum m
  simpa [weierstrassFactor] using
    (continuous_const.sub continuous_id).mul (Complex.continuous_exp.comp hpartial)

end Complex
