/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

module

public import Mathlib.Analysis.Complex.WeierstrassFactor.Lemmas
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Canonical products

This file defines canonical products attached to a sequence `a : ℕ → ℂ` of points:

`canonicalProduct m a z := ∏' n, weierstrassFactor m (z / a n)`.

and proves uniform convergence on compact sets assuming the standard summability hypothesis
`Summable (fun n => ‖a n‖⁻¹ ^ (m+1))`.

## Implementation notes

The summability hypothesis implies `‖a n‖ → ∞`, so the product converges locally uniformly on `ℂ`.
We phrase the main theorem as a `TendstoUniformlyOn` statement for the finite partial products.

## Main definitions

- `Complex.canonicalProduct`: the infinite product `∏' n, E_m(z / a n)`

## Main results

- `Complex.canonicalProduct_converges_uniformOn_compact`: uniform convergence on compact sets under
  the standard summability hypothesis and `a n ≠ 0`

-/

noncomputable section

@[expose] public section

open Complex Real Set Filter Topology
open scoped BigOperators Topology

namespace Complex

/-! ## Canonical product definition -/

/-- The canonical product `∏' n, E_m(z/a_n)` for a sequence `a`. -/
def canonicalProduct (m : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor m (z / a n)

@[simp]
lemma canonicalProduct_at_zero (m : ℕ) (a : ℕ → ℂ) : canonicalProduct m a 0 = 1 := by
  simp [canonicalProduct]

lemma canonicalProduct_eq_tprod (m : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    canonicalProduct m a z = ∏' n : ℕ, weierstrassFactor m (z / a n) :=
  rfl

private lemma eventually_two_mul_le_norm_of_summable_inv_pow
    {p : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ p))
    (h_nonzero : ∀ n, a n ≠ 0)
    {R : ℝ} (hRpos : 0 < R) :
    ∀ᶠ n in atTop, (2 * R : ℝ) ≤ ‖a n‖ := by
  have hEv : ∀ᶠ n in atTop, ‖a n‖⁻¹ ^ p < (1 / (2 * R)) ^ p := by
    have hpos : 0 < (1 / (2 * R) : ℝ) := by
      have : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
      exact one_div_pos.mpr this
    have hpos' : 0 < (1 / (2 * R)) ^ p := pow_pos hpos p
    simpa [Nat.cofinite_eq_atTop] using
      (h_sum.tendsto_cofinite_zero).eventually (eventually_lt_nhds hpos')
  filter_upwards [hEv] with n hn
  by_contra h'
  have hle : ‖a n‖ ≤ 2 * R := le_of_not_ge h'
  have ha_pos : 0 < ‖a n‖ := norm_pos_iff.2 (h_nonzero n)
  have hinv : (1 / (2 * R : ℝ)) ≤ ‖a n‖⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le ha_pos hle)
  have hinv_pow : (1 / (2 * R : ℝ)) ^ p ≤ ‖a n‖⁻¹ ^ p :=
    pow_le_pow_left₀ (by positivity) hinv p
  exact (not_lt_of_ge hinv_pow) (by simpa [one_div] using hn)

/-! ## Uniform convergence on compact sets

We keep this statement minimal: it is purely a convergence+analyticity lemma for the canonical
product, parameterized by a sequence `a` and a genus `m`.
-/

/-- Under the standard summability hypothesis `Summable (fun n => ‖a n‖⁻¹ ^ (m + 1))` and
`a n ≠ 0`, the finite partial products of `weierstrassFactor m (z / a n)` converge uniformly on
compact sets to `canonicalProduct m a`. -/
theorem canonicalProduct_converges_uniformOn_compact
    {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn
        (fun s z => ∏ n ∈ s, weierstrassFactor m (z / a n))
        (canonicalProduct m a) atTop K := by
  intro K hK
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  set R : ℝ := max R0 1
  have hR1pos : 0 < R + 1 := by
    have : (1 : ℝ) ≤ R := le_max_right R0 1
    linarith
  let f : ℕ → ℂ → ℂ := fun n z => weierstrassFactor m (z / a n) - 1
  let u : ℕ → ℝ := fun n => (4 * (R + 1) ^ (m + 1)) * (‖a n‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * (R + 1) ^ (m + 1))
  have hLarge : ∀ᶠ n in atTop, (2 * (R + 1) : ℝ) ≤ ‖a n‖ := by
    simpa using
      eventually_two_mul_le_norm_of_summable_inv_pow (p := m + 1) (a := a) h_sum h_nonzero hR1pos
  have hBoundK : ∀ᶠ n in atTop, ∀ z ∈ K, ‖f n z‖ ≤ u n := by
    filter_upwards [hLarge] with n hn z hzK
    have hzle : ‖z‖ ≤ R + 1 := by
      have : ‖z‖ ≤ R := le_trans (hR0 z hzK) (le_max_left _ _)
      linarith
    have hW :
        ‖weierstrassFactor m (z / a n) - 1‖ ≤ 4 * ((R + 1) ^ (m + 1)) * (‖a n‖⁻¹ ^ (m + 1)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (norm_weierstrassFactor_div_sub_one_le
          (m := m) (R := R + 1) (z := z) (a := a n) hR1pos hzle hn)
    simpa [f, u, mul_assoc, mul_left_comm, mul_comm] using hW
  have hcts : ∀ n, ContinuousOn (f n) K := by
    intro n
    have hcont : Continuous fun z : ℂ => weierstrassFactor m (z / a n) :=
      (continuous_weierstrassFactor m).comp (by
        simpa [div_eq_mul_inv] using (continuous_id.mul continuous_const))
    simpa [f] using hcont.continuousOn.sub continuous_const.continuousOn
  have hprodK :
      HasProdUniformlyOn (fun n z ↦ 1 + f n z) (fun z ↦ ∏' n, (1 + f n z)) K := by
    simpa using Summable.hasProdUniformlyOn_nat_one_add (f := f) (K := K) hK hu hBoundK hcts
  have htendK :
      TendstoUniformlyOn
        (fun s z => ∏ n ∈ s, (1 + f n z))
        (fun z => ∏' n, (1 + f n z)) atTop K :=
    (hasProdUniformlyOn_iff_tendstoUniformlyOn).1 hprodK
  have htendK' :
      TendstoUniformlyOn
        (fun s z => ∏ n ∈ s, weierstrassFactor m (z / a n))
        (fun z => ∏' n, (1 + f n z)) atTop K :=
    htendK.congr <| Filter.Eventually.of_forall (fun s => by
      intro z hzK
      simp [f])
  refine htendK'.congr_right (fun z hzK => ?_)
  simp [f, canonicalProduct]

end Complex
