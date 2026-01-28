/- 
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.J

/-!
# Stirling series via the Binet integral

This file defines the (truncated) Stirling series and its remainder, expressed using `Binet.J`.
Only the basic `n = 0` remainder bounds are included here; sharper bounds belong in dedicated files.
-/

noncomputable section

open scoped BigOperators

namespace Binet

/-! ## Stirling series with Bernoulli numbers -/

/-- The Bernoulli number \(B_n\) as a real number. -/
def bernoulliReal (n : ℕ) : ℝ :=
  (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli n)).eval 0

/-- The k-th term of the Stirling series:
\(B_{2k} / (2k(2k-1) z^{2k-1})\). -/
def stirlingTerm (k : ℕ) (z : ℂ) : ℂ :=
  if k = 0 then 0 else
    (bernoulliReal (2 * k) : ℂ) / (2 * k * (2 * k - 1) * z ^ (2 * k - 1))

/-- The truncated Stirling series up to order `n`. -/
def stirlingSeries (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, stirlingTerm k z

/-- The remainder after `n` terms of the Stirling series. -/
def stirlingRemainder (n : ℕ) (z : ℂ) : ℂ :=
  J z - stirlingSeries n z

/-- The Binet integral equals the Stirling series plus its remainder. -/
theorem J_eq_stirlingSeries_add_remainder (z : ℂ) (n : ℕ) :
    J z = stirlingSeries n z + stirlingRemainder n z := by
  simp [stirlingRemainder, add_sub_cancel]

/-- Simplified bound for `n = 0`: `‖stirlingRemainder 0 z‖ ≤ 1 / (12 * z.re)` (for `0 < z.re`). -/
theorem stirlingRemainder_zero_bound {z : ℂ} (hz : 0 < z.re) :
    ‖stirlingRemainder 0 z‖ ≤ 1 / (12 * z.re) := by
  simpa [stirlingRemainder, stirlingSeries, one_div, mul_assoc, mul_left_comm, mul_comm] using
    (J_norm_le_re (z := z) hz)

/-- For real `x > 0`: `‖stirlingRemainder 0 (x : ℂ)‖ ≤ 1 / (12 * x)`. -/
theorem stirlingRemainder_zero_bound_real {x : ℝ} (hx : 0 < x) :
    ‖stirlingRemainder 0 (x : ℂ)‖ ≤ 1 / (12 * x) := by
  simpa [stirlingRemainder, stirlingSeries, one_div, mul_assoc, mul_left_comm, mul_comm] using
    (J_norm_le_real (x := x) hx)

end Binet

