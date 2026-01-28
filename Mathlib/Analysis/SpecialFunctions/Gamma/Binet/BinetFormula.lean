/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.Integrability
import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.Limit
import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.J
import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.ReJ
import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.StirlingSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.GammaBounds

/-!
# Binet's Formula for log Γ and Stirling Series with Error Bounds

This file develops the Binet formula for the logarithm of the Gamma function
and derives sharp error bounds for the Stirling asymptotic series.

## Main Definitions

* `Binet.J`: the Binet integral (defined for `0 < z.re`)
* `Binet.R`: the real correction term in Stirling's formula
* `Binet.stirlingSeries`, `Binet.stirlingRemainder`: the Stirling series (via Bernoulli numbers) and
   its remainder

## Main Results

* `Binet.log_Gamma_real_eq`: Binet's formula for `Real.log (Real.Gamma x)` on `0 < x`
* `Binet.J_norm_le_re`: the main bound `‖J z‖ ≤ 1 / (12 * z.re)` for `0 < z.re`
* `Binet.J_norm_le_real`: the specialization `‖J x‖ ≤ 1 / (12 * x)` for `0 < x`

## References

* NIST DLMF 5.11: Asymptotic Expansions
* Robbins, H. "A Remark on Stirling's Formula." Amer. Math. Monthly 62 (1955): 26-29.
* Whittaker & Watson, "A Course of Modern Analysis", Chapter 12

## Implementation Notes

We use the normalized kernel `Binet.Ktilde`, which satisfies
`Binet.Ktilde t → 1 / 12` as `t → 0⁺` and `0 ≤ Binet.Ktilde t ≤ 1 / 12` for `0 ≤ t`.
-/

open Real Complex Set MeasureTheory Filter Topology
open scoped BigOperators Nat


private lemma one_div_cast_sub_le_two_div_cast (n : ℕ) (hn2 : 2 ≤ n) :
    (1 : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ (2 : ℝ) / (n : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn2))
  have hn1_pos : 0 < ((n - 1 : ℕ) : ℝ) := by
    have : 0 < n - 1 := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hn2)
    exact_mod_cast this
  refine (div_le_div_iff₀ hn1_pos hn_pos).2 ?_
  have hn1_ge1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ n - 1 := Nat.sub_le_sub_right hn2 1
    exact_mod_cast this
  have hn_nat_pos : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn2
  have hnat : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_nat_pos)
  have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hnat.symm
  nlinarith [hn1_ge1, hcast]
noncomputable section

namespace Binet

private lemma eq_of_tendsto_atTop_of_add_one {h : ℝ → ℝ} {x l : ℝ} (hx : 0 < x)
    (h_add_one : ∀ y, 0 < y → h y = h (y + 1)) (hlim : Tendsto h atTop (𝓝 l)) :
    h x = l := by
  have hxseq : Tendsto (fun n : ℕ => h (x + n)) atTop (𝓝 l) := by
    have hxadd : Tendsto (fun n : ℕ => (x + n : ℝ)) atTop atTop := by
      -- `x + n → ∞`
      have hnx : Tendsto (fun n : ℕ => ((n : ℝ) + x)) atTop atTop :=
        Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
      simpa [add_assoc, add_comm, add_left_comm] using hnx
    exact hlim.comp hxadd
  have hconst : (fun n : ℕ => h (x + n)) = fun _ => h x := by
    funext n
    induction n with
    | zero => simp
    | succ n ih =>
      have hxpos : 0 < x + n := by linarith [hx]
      have hstep : h (x + (n + 1)) = h (x + n) := by
        simpa [add_assoc, add_comm, add_left_comm] using (h_add_one (x + n) hxpos).symm
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm, ih] using hstep
  rw [hconst] at hxseq
  exact tendsto_const_nhds_iff.mp hxseq

/-! ## Binet's formula for log Γ -/

/-!
### About a complex `log Γ` statement

A statement of the form

`Complex.log (Complex.Gamma z) = (z - 1/2) * Complex.log z - z + log(2π)/2 + J z`

using the *principal* complex logarithm `Complex.log` is **not valid on all of** `{z | 0 < re z}`:
`Γ` crosses the negative real axis infinitely many times in the right half-plane, so the composite
`Complex.log ∘ Complex.Gamma` cannot be holomorphic there.

A principled complex formulation should instead use a holomorphic branch of `log Γ`
(often called `logGamma`) on a suitable simply-connected domain.
-/

/-- The Stirling main terms for real `x`. -/
def stirlingMainReal (x : ℝ) : ℝ :=
  (x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2

/-- The (real) Stirling correction term:
`R(x) := log Γ(x) - ((x - 1/2) log x - x + log(2π)/2)`. -/
def R (x : ℝ) : ℝ :=
  Real.log (Real.Gamma x) - stirlingMainReal x

lemma log_Gamma_real_eq_of_R_eq_re_J {x : ℝ} (hR : R x = (Binet.J (x : ℂ)).re) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + (J x).re := by
  have hR' := hR
  dsimp [R] at hR'
  have hmain : Real.log (Real.Gamma x) = stirlingMainReal x + (Binet.J (x : ℂ)).re := by
    linarith
  -- rewrite `stirlingMainReal`, and rewrite `(Binet.J (x : ℂ)).re` as `(J x).re`
  simpa [stirlingMainReal] using hmain

lemma stirlingMainReal_add_one_sub {x : ℝ} (hx : 0 < x) :
    stirlingMainReal (x + 1) - stirlingMainReal x =
      Real.log x + (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := by
  unfold stirlingMainReal
  have hx1 : 0 < x + 1 := by linarith
  have hlog_sum : Real.log (x + 1) = Real.log x + Real.log (1 + 1 / x) := by
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h1 : x + 1 = x * (1 + 1 / x) := by
      calc
        x + 1 = x + x * (1 / x) := by simp [hx0]
        _ = x * (1 + 1 / x) := by ring
    rw [h1, Real.log_mul hx0 (by
      have : 0 < (1 + 1 / x) := by
        have : 0 < (1 / x : ℝ) := by positivity
        linarith
      exact ne_of_gt this)]
  rw [hlog_sum]
  ring

lemma R_sub_R_add_one {x : ℝ} (hx : 0 < x) :
    R x - R (x + 1) = (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := by
  unfold R
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hΓ_diff :
      Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x) = Real.log x := by
    have hΓ : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one (s := x) hx0
    have hΓx_ne : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
    calc
      Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)
          = (Real.log x + Real.log (Real.Gamma x)) - Real.log (Real.Gamma x) := by
              simp [hΓ, Real.log_mul hx0 hΓx_ne]
      _ = Real.log x := by ring
  have hS := stirlingMainReal_add_one_sub (x := x) hx
  calc
    (Real.log (Real.Gamma x) - stirlingMainReal x) - (Real.log (Real.Gamma (x + 1)) -
      stirlingMainReal (x + 1))
        = (stirlingMainReal (x + 1) - stirlingMainReal x) -
            (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)) := by ring
    _ = (Real.log x + (x + 1 / 2) * Real.log (1 + 1 / x) - 1) - Real.log x := by
          simpa [hΓ_diff] using congrArg (fun t => t - Real.log x) hS
    _ = (x + 1 / 2) * Real.log (1 + 1 / x) - 1 := by ring

/-!
## Real-part identities for `J`

The real-part integral formula and the key recurrence for `re (J x)` live in
`Mathlib/Analysis/SpecialFunctions/Gamma/Binet/ReJ.lean`.
-/

-- Auxiliary limit: `R x → 0` as `x → ∞`.
private lemma tendsto_R_atTop : Tendsto R atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => R (n : ℝ)) atTop (𝓝 0) := by
    have hst : Tendsto Stirling.stirlingSeq atTop (𝓝 (Real.sqrt Real.pi)) :=
      Stirling.tendsto_stirlingSeq_sqrt_pi
    have hlogst : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n))
        atTop (𝓝 (Real.log (Real.sqrt Real.pi))) :=
      (Real.continuousAt_log (by
        have : (0 : ℝ) < Real.sqrt Real.pi := by
          have : (0 : ℝ) < Real.pi := Real.pi_pos
          simpa using Real.sqrt_pos.2 this
        exact ne_of_gt this)).tendsto.comp hst
    have hπ : Real.log (Real.sqrt Real.pi) = Real.log Real.pi / 2 := by
      simpa using (Real.log_sqrt (x := Real.pi) (by exact le_of_lt Real.pi_pos))
    have hR_eq :
        (fun n : ℕ => R (n : ℝ)) =ᶠ[atTop]
          fun n : ℕ => Real.log (Stirling.stirlingSeq n) - Real.log Real.pi / 2 := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hn)
      have hGamma_n :
          Real.Gamma (n : ℝ) = ((n - 1)! : ℝ) := by
        have hn' : 0 < n := hn
        have hn_succ : (n - 1).succ = n := Nat.succ_pred_eq_of_pos hn'
        have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
          have := congrArg (fun k : ℕ => (k : ℝ)) hn_succ
          simpa [Nat.cast_succ] using this
        have hGamma := Real.Gamma_nat_eq_factorial (n - 1)
        simpa [hcast, Nat.cast_add, Nat.cast_one, add_assoc] using hGamma
      have hlogGamma :
          Real.log (Real.Gamma (n : ℝ)) = Real.log (n ! : ℝ) - Real.log (n : ℝ) := by
        have hn_fact_ne : ((n ! : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.factorial_ne_zero n)
        have hpred_fact_ne : (((n - 1)! : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.factorial_ne_zero (n - 1))
        have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
        have hfac : (n ! : ℝ) = (n : ℝ) * ((n - 1)! : ℝ) := by
          have hn_succ : (n - 1).succ = n := Nat.succ_pred_eq_of_pos hn
          have : (n ! : ℝ) = (n : ℝ) * ((n - 1)! : ℝ) := by
            have hn_pos : 0 < n := hn
            have hn' : (n - 1 + 1) = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)
            have hnat : ((n - 1 + 1) ! : ℕ) = (n - 1 + 1) * (n - 1)! :=
              Nat.factorial_succ (n - 1)
            have := congrArg (fun k : ℕ => (k : ℝ)) hnat
            simpa [hn', Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc,
              mul_comm, mul_left_comm] using this
          exact this
        have hlog_mul : Real.log (n ! : ℝ) = Real.log (n : ℝ) + Real.log ((n - 1)! : ℝ) := by
          have h : Real.log ((n : ℝ) * ((n - 1)! : ℝ)) =
              Real.log (n : ℝ) + Real.log ((n - 1)! : ℝ) := by
            simpa using Real.log_mul (x := (n : ℝ)) (y := ((n - 1)! : ℝ)) hn_ne hpred_fact_ne
          simpa [hfac, mul_comm, add_comm, add_left_comm, add_assoc] using h
        have : Real.log ((n - 1)! : ℝ) = Real.log (n ! : ℝ) - Real.log (n : ℝ) := by
          linarith
        simp [hGamma_n, this]
      have hn' : n ≠ 0 := Nat.ne_of_gt hn
      have hlogst_formula := Stirling.log_stirlingSeq_formula n
      unfold R stirlingMainReal at *
      have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hlog_pi2 : Real.log (Real.pi * 2) = Real.log Real.pi + Real.log 2 := by
        simpa [mul_comm] using Real.log_mul (Real.pi_pos.ne') (by norm_num : (2 : ℝ) ≠ 0)
      have hlogst_formula' :
          Real.log (Stirling.stirlingSeq n) =
            Real.log (n ! : ℝ) - (1 / 2 : ℝ) * (Real.log 2 + Real.log (n : ℝ))
              - (n : ℝ) * (Real.log (n : ℝ) - 1) := by
        have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hn_ne : (n : ℝ) ≠ 0 := hn_pos_real.ne'
        have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
        have hlog_2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) := by
          simpa using Real.log_mul h2_ne hn_ne
        have hlog_div : Real.log ((n : ℝ) / Real.exp 1) = Real.log (n : ℝ) - 1 := by
          simpa [Real.log_exp, sub_eq_add_neg] using
            (Real.log_div hn_ne (Real.exp_pos 1).ne')
        have h0 := Stirling.log_stirlingSeq_formula n
        have h0' :
            Real.log (Stirling.stirlingSeq n) =
              Real.log (n ! : ℝ) - (1 / 2 : ℝ) * Real.log (2 * (n : ℝ))
                - (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) := by
          simpa [Stirling.stirlingSeq, sub_eq_add_neg, one_div, mul_assoc, mul_left_comm,
            mul_comm, add_assoc, add_left_comm, add_comm] using h0
        calc
          Real.log (Stirling.stirlingSeq n)
              = Real.log (n ! : ℝ) - (1 / 2 : ℝ) * Real.log (2 * (n : ℝ))
                  - (n : ℝ) * Real.log ((n : ℝ) / Real.exp 1) := h0'
          _ = Real.log (n ! : ℝ) - (1 / 2 : ℝ) * (Real.log 2 + Real.log (n : ℝ))
                - (n : ℝ) * (Real.log (n : ℝ) - 1) := by
              simp [hlog_2n, hlog_div]
      simp [hlogGamma, hlogst_formula', hlog_pi2, sub_eq_add_neg,
        mul_add, add_mul, mul_comm]
      ring_nf
    have h_tendsto :
        Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) -
          Real.log Real.pi / 2) atTop (𝓝 0) :=
      by
        simpa [hπ, sub_eq_add_neg, add_assoc] using hlogst.sub_const (Real.log Real.pi / 2)
    exact (tendsto_congr' hR_eq).2 h_tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hnat' := (Metric.tendsto_atTop).1 hnat (ε / 2) (by positivity)
  rcases hnat' with ⟨N1, hN1⟩
  have h_inv : Tendsto (fun n : ℕ => (3 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv, mul_assoc] using (this.const_mul (3 : ℝ))
  have h_inv' := (Metric.tendsto_atTop).1 h_inv (ε / 2) (by positivity)
  rcases h_inv' with ⟨N2, hN2⟩
  let N : ℕ := max (max N1 N2) 2
  refine ⟨(N : ℝ) + 1, ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  let n : ℕ := ⌊y⌋₊
  have hn_le : (n : ℝ) ≤ y := Nat.floor_le hy0
  have hy_lt : y < (n : ℝ) + 1 := Nat.lt_floor_add_one y
  have hn_ge : N ≤ n := by
    by_contra h
    have hn_lt : n < N := Nat.lt_of_not_ge h
    have : y < (N : ℝ) := (Nat.floor_lt hy0).1 hn_lt
    linarith
  have hn2 : 2 ≤ n := le_trans (by exact le_max_right _ _) hn_ge
  have hn_pos : 0 < (n : ℝ) := by
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact this.trans_le (by exact_mod_cast hn2)
  have hn1_pos : 0 < (n - 1 : ℕ) := by
    exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
  have ha0 : 0 ≤ y - n := sub_nonneg.2 hn_le
  have ha1 : y - n < 1 := by
    have : y < (n : ℝ) + 1 := hy_lt
    linarith
  have ha_le : y - n ≤ 1 := le_of_lt ha1
  -- Use the Bohr–Mollerup auxiliary lemmas (already in Mathlib) to control `log Γ` on a unit
  -- interval via convexity + `Γ(x+1)=xΓ(x)`.
  have hf_conv :
      ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun z : ℝ => Real.log (Real.Gamma z)) := by
    simpa [Function.comp] using
      (Real.convexOn_log_Gamma : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (Real.log ∘ Real.Gamma))
  have hf_feq :
      ∀ {z : ℝ}, 0 < z →
        (fun w : ℝ => Real.log (Real.Gamma w)) (z + 1) =
          (fun w : ℝ => Real.log (Real.Gamma w)) z + Real.log z := by
    intro z hz
    have hz0 : z ≠ 0 := hz.ne'
    have hΓ : Real.Gamma (z + 1) = z * Real.Gamma z := Real.Gamma_add_one (s := z) hz0
    calc
      Real.log (Real.Gamma (z + 1)) = Real.log (z * Real.Gamma z) := by simp [hΓ]
      _ = Real.log z + Real.log (Real.Gamma z) := by
            simp [Real.log_mul hz0 (Real.Gamma_pos_of_pos hz).ne']
      _ = Real.log (Real.Gamma z) + Real.log z := by ac_rfl
  have h_upper :
      Real.log (Real.Gamma y) ≤
        Real.log (Real.Gamma (n : ℝ)) + (y - n) * Real.log (n : ℝ) := by
    by_cases h0 : y - n = 0
    · have hy_eq : y = (n : ℝ) := sub_eq_zero.mp h0
      simp [hy_eq]
    · have ha_pos : 0 < y - n := lt_of_le_of_ne ha0 (Ne.symm h0)
      have hn0 : n ≠ 0 := by
        exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn2)
      have h :=
        Real.BohrMollerup.f_add_nat_le (f := fun z : ℝ => Real.log (Real.Gamma z))
          hf_conv (fun {z} hz => hf_feq hz) hn0 ha_pos ha_le
      have hy' : (n : ℝ) + (y - n) = y := by ring
      simpa [hy'] using h
  have h_lower :
      Real.log (Real.Gamma y) ≥
        Real.log (Real.Gamma (n : ℝ)) + (y - n) * Real.log ((n - 1 : ℕ) : ℝ) := by
    by_cases h0 : y - n = 0
    · have hy_eq : y = (n : ℝ) := sub_eq_zero.mp h0
      simp [hy_eq]
    · have ha_pos : 0 < y - n := lt_of_le_of_ne ha0 (Ne.symm h0)
      have h :=
        Real.BohrMollerup.f_add_nat_ge (f := fun z : ℝ => Real.log (Real.Gamma z))
          hf_conv (fun {z} hz => hf_feq hz) hn2 ha_pos
      have hy' : (n : ℝ) + (y - n) = y := by ring
      have hn1 : (1 : ℕ) ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) hn2
      have hcast : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
        -- `Nat.cast_sub hn1` gives `((n - 1) : ℝ) = (n : ℝ) - 1`.
        simpa [Nat.cast_one, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (Nat.cast_sub (R := ℝ) hn1).symm
      have :
          Real.log (Real.Gamma (n : ℝ)) + (y - n) * Real.log ((n - 1 : ℕ) : ℝ) ≤
            Real.log (Real.Gamma y) := by
        simpa [hy', hcast] using h
      exact this
  have hn0' : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hR_upper : R y ≤ R (n : ℝ) + 1 / (n : ℝ) := by
    have hy_pos : 0 < y := lt_of_lt_of_le hn_pos hn_le
    have hy_ne : y ≠ 0 := ne_of_gt hy_pos
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hlog_ge :
        (y - (n : ℝ)) / y ≤ Real.log y - Real.log (n : ℝ) := by
      have hx_pos : 0 < y / (n : ℝ) := div_pos hy_pos hn_pos
      have h0 : 1 - (y / (n : ℝ))⁻¹ ≤ Real.log (y / (n : ℝ)) :=
        Real.one_sub_inv_le_log_of_pos (x := y / (n : ℝ)) hx_pos
      have hL : 1 - (y / (n : ℝ))⁻¹ = (y - (n : ℝ)) / y := by
        field_simp [hy_ne, hn_ne]
      have hR : Real.log (y / (n : ℝ)) = Real.log y - Real.log (n : ℝ) := by
        simpa using (Real.log_div (x := y) (y := (n : ℝ)) hy_ne hn_ne)
      have h0' : (y - (n : ℝ)) / y ≤ Real.log y - Real.log (n : ℝ) := by
        have h0'' : (y - (n : ℝ)) / y ≤ Real.log (y / (n : ℝ)) := by
          have htmp := h0
          rw [hL] at htmp
          exact htmp
        simpa [hR] using h0''
      exact h0'
    have hΔ :
        stirlingMainReal (n : ℝ) + (y - (n : ℝ)) * Real.log (n : ℝ) - stirlingMainReal y ≤
          1 / (n : ℝ) := by
      have hΔ_eq :
          stirlingMainReal (n : ℝ) + (y - (n : ℝ)) * Real.log (n : ℝ) - stirlingMainReal y =
            (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * (Real.log y - Real.log (n : ℝ)) := by
        unfold stirlingMainReal
        ring
      have hy1 : 0 ≤ y - (1 / 2 : ℝ) := by linarith [hy]
      have hΔ_le :
          (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * (Real.log y - Real.log (n : ℝ)) ≤
            (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * ((y - (n : ℝ)) / y) := by
        have hmul := mul_le_mul_of_nonneg_left hlog_ge hy1
        linarith
      have hΔ_simp :
          (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * ((y - (n : ℝ)) / y) =
            (y - (n : ℝ)) / (2 * y) := by
        field_simp [hy_ne]
        ring
      have hΔ_bound : (y - (n : ℝ)) / (2 * y) ≤ 1 / (n : ℝ) := by
        have h2y_pos : 0 < 2 * y := by nlinarith [hy_pos]
        have h2n_pos : 0 < 2 * (n : ℝ) := by nlinarith [hn_pos]
        have hstep1 :
            (y - (n : ℝ)) / (2 * y) ≤ 1 / (2 * y) := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt h2y_pos)
          linarith [ha_le]
        have hstep2 :
            (1 : ℝ) / (2 * y) ≤ 1 / (2 * (n : ℝ)) := by
          have hle : 2 * (n : ℝ) ≤ 2 * y := by nlinarith [hn_le]
          exact one_div_le_one_div_of_le h2n_pos hle
        have hstep3 :
            (1 : ℝ) / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
          have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
          have hnonneg : 0 ≤ (1 / (n : ℝ) : ℝ) := one_div_nonneg.2 (le_of_lt hn_pos)
          have hrew : (1 : ℝ) / (2 * (n : ℝ)) = (1 / (n : ℝ)) / 2 := by
            field_simp [hn0]
          have : (1 / (n : ℝ)) / 2 ≤ (1 / (n : ℝ)) :=
            div_le_self hnonneg (by norm_num : (1 : ℝ) ≤ 2)
          rw [hrew]
          exact this
        exact le_trans hstep1 (le_trans hstep2 hstep3)
      calc
        stirlingMainReal (n : ℝ) + (y - (n : ℝ)) * Real.log (n : ℝ) - stirlingMainReal y
            = (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * (Real.log y - Real.log (n : ℝ)) := hΔ_eq
        _ ≤ (y - (n : ℝ)) - (y - (1 / 2 : ℝ)) * ((y - (n : ℝ)) / y) := hΔ_le
        _ = (y - (n : ℝ)) / (2 * y) := hΔ_simp
        _ ≤ 1 / (n : ℝ) := hΔ_bound
    have : Real.log (Real.Gamma y) - stirlingMainReal y ≤
        (Real.log (Real.Gamma (n : ℝ)) - stirlingMainReal (n : ℝ)) + 1 / (n : ℝ) :=
      by linarith [h_upper, hΔ]
    simpa [R, sub_eq_add_neg, add_assoc] using this
  have hR_lower : R y ≥ R (n : ℝ) - 3 / (n : ℝ) := by
    have hy_pos : 0 < y := lt_of_lt_of_le hn_pos hn_le
    have hy_ne : y ≠ 0 := ne_of_gt hy_pos
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hlogy_ub : Real.log y ≤ Real.log (n : ℝ) + (y - (n : ℝ)) / (n : ℝ) := by
      have hx_pos : 0 < y / (n : ℝ) := div_pos hy_pos hn_pos
      have hlog : Real.log (y / (n : ℝ)) ≤ y / (n : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (x := y / (n : ℝ)) hx_pos
      have hlog_div : Real.log (y / (n : ℝ)) = Real.log y - Real.log (n : ℝ) := by
        simpa using (Real.log_div (x := y) (y := (n : ℝ)) hy_ne hn_ne)
      have hrhs : y / (n : ℝ) - 1 = (y - (n : ℝ)) / (n : ℝ) := by
        field_simp [hn_ne]
      have : Real.log y - Real.log (n : ℝ) ≤ (y - (n : ℝ)) / (n : ℝ) := by
        simpa [hlog_div, hrhs] using hlog
      linarith
    have hlognm1 : Real.log ((n - 1 : ℕ) : ℝ) ≥ Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ) := by
      have hn_nat_pos : 0 < n := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2
      have hn1_pos_real : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hn1_pos
      have hn1_ne0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hn1_pos_real
      have hlognm1' : Real.log ((n - 1 : ℕ) : ℝ) ≥
          Real.log (n : ℝ) - 1 / ((n - 1 : ℕ) : ℝ) := by
        have hx_pos : 0 < (n : ℝ) / ((n - 1 : ℕ) : ℝ) := div_pos hn_pos hn1_pos_real
        have hlog : Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ (n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (x := (n : ℝ) / ((n - 1 : ℕ) : ℝ)) hx_pos
        have hlog' :
            Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) =
              Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) := by
          simpa using (Real.log_div (x := (n : ℝ)) (y := ((n - 1 : ℕ) : ℝ)) hn_ne hn1_ne0)
        have hrhs : (n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1 = 1 / ((n - 1 : ℕ) : ℝ) := by
          field_simp [hn1_ne0]
          have hnat : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_nat_pos)
          have hcast : ((n : ℝ) : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
            exact_mod_cast hnat.symm
          linarith [hcast]
        have : Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) ≤ 1 / ((n - 1 : ℕ) : ℝ) := by
          have htmp := hlog
          rw [hlog'] at htmp
          rw [hrhs] at htmp
          exact htmp
        have h1 :
            Real.log (n : ℝ) ≤ Real.log ((n - 1 : ℕ) : ℝ) + 1 / ((n - 1 : ℕ) : ℝ) := by
          have h1' : Real.log (n : ℝ) ≤ 1 / ((n - 1 : ℕ) : ℝ) + Real.log ((n - 1 : ℕ) : ℝ) :=
            (sub_le_iff_le_add).1 this
          have h1'' := h1'
          rw [add_comm] at h1''
          exact h1''
        exact (sub_le_iff_le_add).2 h1
      have hfrac : (1 : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ (2 : ℝ) / (n : ℝ) :=
        one_div_cast_sub_le_two_div_cast n hn2
      have hcomp :
          Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ) ≤ Real.log (n : ℝ) - 1 / ((n - 1 : ℕ) : ℝ) := by
        exact sub_le_sub_left hfrac (Real.log (n : ℝ))
      exact le_trans hcomp hlognm1'
    have hy_le' : y ≤ (n : ℝ) + 1 := le_of_lt hy_lt
    have hy1 : 0 ≤ y - (1 / 2 : ℝ) := by
      have hN2_nat : (2 : ℕ) ≤ N := le_max_right (max N1 N2) 2
      have hN2 : (2 : ℝ) ≤ (N : ℝ) := by
        have h : ((2 : ℕ) : ℝ) ≤ (N : ℝ) := (Nat.cast_le (α := ℝ)).2 hN2_nat
        exact h
      have hy3 : (3 : ℝ) ≤ y := by
        have h3' : (2 : ℝ) + 1 ≤ (N : ℝ) + 1 := add_le_add_left hN2 1
        have h3 : (3 : ℝ) ≤ (N : ℝ) + 1 := by
          have h21 : (2 : ℝ) + 1 = 3 := by norm_num
          have h3'' := h3'
          rw [h21] at h3''
          exact h3''
        have hy' : (N : ℝ) + 1 ≤ y := hy
        exact le_trans h3 hy'
      have : (1 / 2 : ℝ) ≤ y := by
        have hhalf : (1 / 2 : ℝ) ≤ 3 := by norm_num
        exact le_trans hhalf hy3
      exact sub_nonneg.2 this
    have ha_nonneg : 0 ≤ y - (n : ℝ) := ha0
    have hlogGamma_lb : Real.log (Real.Gamma y) ≥ Real.log (Real.Gamma (n : ℝ)) +
        (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ) := by
      exact h_lower
    have hmain :
        stirlingMainReal (n : ℝ) + (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ) -
          stirlingMainReal y ≥
          - (3 / (n : ℝ)) := by
      unfold stirlingMainReal
      have hlogy_mul :
          (y - (1 / 2 : ℝ)) * Real.log y ≤
            (y - (1 / 2 : ℝ)) * (Real.log (n : ℝ) + (y - (n : ℝ)) / (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hlogy_ub hy1
      have hlognm1_mul :
          (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ) ≥
            (y - (n : ℝ)) * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hlognm1 ha_nonneg
        exact h
      set a : ℝ := y - (n : ℝ) with ha
      have ha0 : 0 ≤ a := by simpa [a] using ha_nonneg
      have ha1 : a ≤ 1 := by simpa [a] using ha_le
      have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
      have hy_a : y = (n : ℝ) + a := by
        dsimp [a]
        ring
      have hrew0 :
          ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ) + Real.log (2 * π) / 2
            + (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ)
            - ((y - 1 / 2) * Real.log y - y + Real.log (2 * π) / 2)) =
            ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
              + a * Real.log ((n - 1 : ℕ) : ℝ)
              + (-( (y - 1 / 2) * Real.log y)) + y) := by
        ring
      have h1 :
          a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ)) ≤ a * Real.log ((n - 1 : ℕ) : ℝ) := by
        have : a * Real.log ((n - 1 : ℕ) : ℝ) ≥ a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ)) := by
          simpa [a] using hlognm1_mul
        simpa [ge_iff_le] using this
      have h2 :
          -((y - 1 / 2) * (Real.log (n : ℝ) + a / (n : ℝ))) ≤ -((y - 1 / 2) * Real.log y) := by
        have := neg_le_neg hlogy_mul
        simpa [a] using this
      have hmain_lower :
          ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
            + a * Real.log ((n - 1 : ℕ) : ℝ)
            + (-( (y - 1 / 2) * Real.log y)) + y)
            ≥
          ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
            + a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ))
            + (-( (y - 1 / 2) * (Real.log (n : ℝ) + a / (n : ℝ)))) + y) := by
        linarith [h1, h2]
      have hsimp :
          ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
            + a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ))
            + (-( (y - 1 / 2) * (Real.log (n : ℝ) + a / (n : ℝ)))) + y)
            =
          a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) := by
        rw [hy_a]
        field_simp [hn0]
        ring
      have hfinal : a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) ≥ - (3 / (n : ℝ)) := by
        have hnum : a * (1 / 2 - a) - 2 * a ≥ (-3 : ℝ) := by
          -- `a * (1/2 - a) - 2a = -a^2 - (3/2)a`, and on `0 ≤ a ≤ 1` this is ≥ `-5/2 ≥ -3`.
          have ha_sq_le : a ^ 2 ≤ a := by
            have ha0' : 0 ≤ a := ha0
            have ha1' : a ≤ 1 := ha1
            simpa [pow_two] using (mul_le_of_le_one_right ha0' ha1')
          calc
            a * (1 / 2 - a) - 2 * a
                = -(a ^ 2) - (3 / 2) * a := by ring
            _ ≥ -a - (3 / 2) * a := by
                  gcongr
            _ = -(5 / 2) * a := by ring
            _ ≥ -(5 / 2) := by
                  have ha' : a ≤ 1 := ha1
                  have hk : (-(5 / 2 : ℝ)) ≤ 0 := by norm_num
                  have hmul : (-(5 / 2 : ℝ)) * 1 ≤ (-(5 / 2 : ℝ)) * a :=
                    mul_le_mul_of_nonpos_left ha' hk
                  simpa using hmul
            _ ≥ (-3 : ℝ) := by norm_num
        have hdiv : (a * (1 / 2 - a) - 2 * a) / (n : ℝ) ≥ (-3 : ℝ) / (n : ℝ) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hn_pos)
        have hrew :
            a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) =
              (a * (1 / 2 - a) - 2 * a) / (n : ℝ) := by
          -- `x / n - y / n = (x - y) / n`.
          simpa [sub_eq_add_neg] using
            (sub_div (a * (1 / 2 - a)) (2 * a) (n : ℝ)).symm
        calc
          a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ)
              = (a * (1 / 2 - a) - 2 * a) / (n : ℝ) := hrew
          _ ≥ (-3 : ℝ) / (n : ℝ) := hdiv
          _ = - (3 / (n : ℝ)) := by simp [neg_div]
      calc
        ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ) + Real.log (2 * π) / 2
          + (y - (n : ℝ)) * Real.log ((n - 1 : ℕ) : ℝ)
          - ((y - 1 / 2) * Real.log y - y + Real.log (2 * π) / 2))
            =
            ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
              + a * Real.log ((n - 1 : ℕ) : ℝ)
              + (-( (y - 1 / 2) * Real.log y)) + y) := hrew0
        _ ≥
            ( (n - 1 / 2) * Real.log (n : ℝ) - (n : ℝ)
              + a * (Real.log (n : ℝ) - (2 : ℝ) / (n : ℝ))
              + (-( (y - 1 / 2) * (Real.log (n : ℝ) + a / (n : ℝ)))) + y) := hmain_lower
        _ = a * (1 / 2 - a) / (n : ℝ) - 2 * a / (n : ℝ) := hsimp
        _ ≥ - (3 / (n : ℝ)) := hfinal
    have : Real.log (Real.Gamma y) - stirlingMainReal y ≥
        (Real.log (Real.Gamma (n : ℝ)) - stirlingMainReal (n : ℝ)) - 3 / (n : ℝ) := by
      linarith [hlogGamma_lb, hmain]
    simpa [R] using this
  have hR_abs : |R y| ≤ |R (n : ℝ)| + 3 / (n : ℝ) := by
    have hlower : -(|R (n : ℝ)| + 3 / (n : ℝ)) ≤ R y := by
      have h1 : R (n : ℝ) - 3 / (n : ℝ) ≤ R y := hR_lower
      have h2 : -|R (n : ℝ)| - 3 / (n : ℝ) ≤ R (n : ℝ) - 3 / (n : ℝ) :=
        sub_le_sub_right (neg_abs_le (R (n : ℝ))) (3 / (n : ℝ))
      have h3 : -|R (n : ℝ)| - 3 / (n : ℝ) ≤ R y := le_trans h2 h1
      have hneg : -(|R (n : ℝ)| + 3 / (n : ℝ)) = -|R (n : ℝ)| - 3 / (n : ℝ) := by ring
      simpa [hneg] using h3
    have hupper : R y ≤ |R (n : ℝ)| + 3 / (n : ℝ) := by
      have hn_pos' : 0 < (n : ℝ) := hn_pos
      have hRn : R (n : ℝ) ≤ |R (n : ℝ)| := le_abs_self _
      have hdiv : (1 : ℝ) / (n : ℝ) ≤ (3 : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) (le_of_lt hn_pos')
      have hstep : R (n : ℝ) + (1 : ℝ) / (n : ℝ) ≤ |R (n : ℝ)| + (3 : ℝ) / (n : ℝ) := by
        exact add_le_add hRn hdiv
      exact le_trans hR_upper hstep
    exact abs_le.2 ⟨hlower, hupper⟩
  have hRn_small : |R (n : ℝ)| < ε / 2 := by
    have hN1_le_N : N1 ≤ N := by
      exact le_trans (le_max_left N1 N2) (le_max_left (max N1 N2) 2)
    have hn_ge1 : N1 ≤ n := le_trans hN1_le_N hn_ge
    have hdist : dist (R (n : ℝ)) 0 < ε / 2 := hN1 n hn_ge1
    simpa [Real.dist_eq] using hdist
  have h3n_small : 3 / (n : ℝ) < ε / 2 := by
    have hN2_le_N : N2 ≤ N := by
      exact le_trans (le_max_right N1 N2) (le_max_left (max N1 N2) 2)
    have hn_ge2 : N2 ≤ n := le_trans hN2_le_N hn_ge
    have hdist : dist ((3 : ℝ) / (n : ℝ)) 0 < ε / 2 := hN2 n hn_ge2
    simpa [Real.dist_eq] using hdist
  have : |R y| < ε := by
    have hsum : |R (n : ℝ)| + 3 / (n : ℝ) < ε := by
      have : |R (n : ℝ)| + 3 / (n : ℝ) < ε / 2 + ε / 2 := add_lt_add hRn_small h3n_small
      simpa [add_halves] using this
    exact lt_of_le_of_lt hR_abs hsum
  simpa [Real.dist_eq, abs_sub_comm] using this

/-- Binet's formula for real arguments. -/
theorem log_Gamma_real_eq {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1/2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + (J x).re := by
  have hR : R x = (Binet.J (x : ℂ)).re := by
    let h : ℝ → ℝ := fun y => R y - (Binet.J (y : ℂ)).re
    have h_periodic : ∀ y, 0 < y → h y = h (y + 1) := by
      intro y hy
      have hy1 : 0 < y + 1 := by linarith
      have hRrec := R_sub_R_add_one (x := y) hy
      have hJrec := re_J_sub_re_J_add_one (x := y) hy
      have hdiff : R y - R (y + 1) = (Binet.J (y : ℂ)).re - (Binet.J ((y : ℂ) + 1)).re := by
        calc
          R y - R (y + 1)
              = (y + 1 / 2) * Real.log (1 + 1 / y) - 1 := hRrec
          _ = (Binet.J (y : ℂ)).re - (Binet.J ((y : ℂ) + 1)).re := by
              simpa using hJrec.symm
      dsimp [h]
      have heq :
          R y - (Binet.J (y : ℂ)).re = R (y + 1) - (Binet.J ((y : ℂ) + 1)).re := by
        linarith [hdiff]
      simpa using heq
    have hRlim : Tendsto R atTop (𝓝 0) :=
      tendsto_R_atTop
    have hJlim : Tendsto (fun y : ℝ => (Binet.J (y : ℂ)).re) atTop (𝓝 0) :=
      tendsto_re_J_atTop
    have hlim : Tendsto h atTop (𝓝 0) := by
      simpa [h, sub_eq_add_neg] using hRlim.add (hJlim.neg)
    have hxseq : Tendsto (fun n : ℕ => h (x + n)) atTop (𝓝 0) := by
      have hxadd : Tendsto (fun n : ℕ => (x + n : ℝ)) atTop atTop := by
        have hnx : Tendsto (fun n : ℕ => ((n : ℝ) + x)) atTop atTop :=
          Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
        simpa [add_assoc, add_comm, add_left_comm] using hnx
      exact hlim.comp hxadd
    have hx0' : h x = 0 :=
      eq_of_tendsto_atTop_of_add_one (h := h) (x := x) (l := 0) hx h_periodic hlim
    dsimp [h] at hx0'
    linarith
  exact log_Gamma_real_eq_of_R_eq_re_J (x := x) hR

lemma R_eq_re_J {x : ℝ} (hx : 0 < x) : R x = (Binet.J (x : ℂ)).re := by
  have h := log_Gamma_real_eq (x := x) hx
  unfold R stirlingMainReal
  linarith [h]

/-!
## Positivity and bounds for `re (J x)`

These statements belong to the `ReJ` API and live in
`Mathlib/Analysis/SpecialFunctions/Gamma/Binet/ReJ.lean`.
-/

/-- Compatibility: real Binet formula for `Real.log (Real.Gamma x)` on `x > 0`. -/
theorem Real_log_Gamma_eq_Binet {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + (Binet.J x).re := by
  simpa using (Binet.log_Gamma_real_eq (x := x) hx)

end Binet
