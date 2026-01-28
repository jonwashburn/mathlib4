/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Binet.Kernel

/-!
# Robbins lower bound for the Binet kernel

This file proves the Robbins-type pointwise lower bound for the normalized Binet kernel
`Binet.Ktilde`:
\[
\frac{1}{12} e^{-t/12} \le K̃(t), \qquad t>0.
\]

The proof uses an explicit auxiliary function and a short Taylor lower bound for
`exp (t/12)` via `Real.quadratic_le_exp_of_nonneg`.

## References

Robbins' sharpened Stirling bounds (via Binet's integral representation).

## Tags

gamma, binet, kernel, robbins, exponential, bounds
-/

noncomputable section

open Real Set

namespace Binet

/-! ### General monotonicity and positivity lemmas -/

private lemma monotoneOn_of_deriv_nonneg_Ici {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Ici 0))
    (hderiv : ∀ x ∈ Ici 0, 0 ≤ deriv f x) :
    MonotoneOn f (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuousOn (hf.mono interior_subset)
  intro x hx
  rw [interior_Ici] at hx
  exact hderiv x (mem_Ici.mpr (le_of_lt hx))

private lemma nonneg_of_deriv_nonneg_Ici {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Ici 0))
    (hderiv : ∀ x ∈ Ici 0, 0 ≤ deriv f x) (h0 : f 0 = 0) :
    ∀ {x}, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  have hmono := monotoneOn_of_deriv_nonneg_Ici (f := f) hf hderiv
  have hx' : x ∈ Ici 0 := hx
  have h0' : (0 : ℝ) ∈ Ici 0 := by simp
  have hle := hmono h0' hx' hx
  simpa [h0] using hle

private lemma nonneg_of_hasDerivAt_nonneg_Ici {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hderiv_nonneg : ∀ x, 0 ≤ x → 0 ≤ f' x) (h0 : f 0 = 0) :
    ∀ {x}, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  have hf : DifferentiableOn ℝ f (Ici 0) := fun y _ =>
    (hderiv y).differentiableAt.differentiableWithinAt
  have hmain : ∀ y ∈ Ici 0, 0 ≤ deriv f y := by
    intro y hy
    have : deriv f y = f' y := by simpa using (hderiv y).deriv
    simpa [this] using hderiv_nonneg y hy
  exact nonneg_of_deriv_nonneg_Ici (f := f) hf hmain h0 hx

open Internal

/-!
### Positivity of the Robbins auxiliary function

Following the classical manipulation, the Robbins inequality reduces to `0 ≤ robbinsAux t` for
`t ≥ 0`, where `robbinsAux` is an explicit combination of `exp` and polynomials.

We show `robbinsAux'''' t ≥ 0` using a Taylor lower bound for `exp (t/12)`; then we integrate this
inequality four times on `[0,∞)` using `nonneg_of_deriv_nonneg_Ici`.
-/

private def robbinsAux (t : ℝ) : ℝ :=
  12 * exp (t * (13 / 12 : ℝ)) * (t - 2)
    + 12 * exp (t * (1 / 12 : ℝ)) * (t + 2)
    - 2 * t ^ 2 * exp t + 2 * t ^ 2

private def robbinsAux' (t : ℝ) : ℝ :=
  exp (t * (13 / 12 : ℝ)) * (13 * t - 14)
    + exp (t * (1 / 12 : ℝ)) * (t + 14)
    - 2 * exp t * (t * (t + 2)) + 4 * t

private def robbinsAux'' (t : ℝ) : ℝ :=
  exp (t * (13 / 12 : ℝ)) * ((169 * t - 26) / 12)
    + exp (t * (1 / 12 : ℝ)) * ((t + 26) / 12)
    - 2 * exp t * (t ^ 2 + 4 * t + 2) + 4

private def robbinsAux''' (t : ℝ) : ℝ :=
  exp (t * (13 / 12 : ℝ)) * ((2197 * t + 1690) / 144)
    + exp (t * (1 / 12 : ℝ)) * ((t + 38) / 144)
    - 2 * exp t * (t ^ 2 + 6 * t + 6)

private def robbinsAux'''' (t : ℝ) : ℝ :=
  exp (t * (13 / 12 : ℝ)) * ((28561 * t + 48334) / 1728)
    + exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728)
    - 2 * exp t * (t ^ 2 + 8 * t + 12)

private lemma robbinsAux_zero : robbinsAux 0 = 0 := by
  simp [robbinsAux]

private lemma robbinsAux'_zero : robbinsAux' 0 = 0 := by
  simp [robbinsAux']

private lemma robbinsAux''_zero : robbinsAux'' 0 = 0 := by
  simp [robbinsAux'']; norm_num

private lemma robbinsAux'''_zero : robbinsAux''' 0 = 0 := by
  simp [robbinsAux''']; norm_num

private lemma hasDerivAt_exp_mul_const (a t : ℝ) :
    HasDerivAt (fun x : ℝ => exp (x * a)) (exp (t * a) * a) t := by
  simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
    (Real.hasDerivAt_exp (t * a)).comp t ((hasDerivAt_id t).mul_const a)

private lemma hasDerivAt_sq (t : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
  simpa using (hasDerivAt_pow 2 t)

private lemma hasDerivAt_cube (t : ℝ) : HasDerivAt (fun x : ℝ => x ^ 3) ((3 : ℝ) * t ^ 2) t := by
  simpa using (hasDerivAt_pow 3 t)

private lemma hasDerivAt_exp_mul {a : ℝ} {p p' : ℝ → ℝ} {t : ℝ}
    (hp : HasDerivAt p (p' t) t) : HasDerivAt (fun x : ℝ => exp (x * a) * p x)
      (exp (t * a) * (a * p t + p' t)) t := by
  have hexp := hasDerivAt_exp_mul_const a t
  have h := hexp.mul hp
  convert h using 1; ring_nf

private lemma hasDerivAt_robbinsAux (t : ℝ) : HasDerivAt robbinsAux (robbinsAux' t) t := by
  have h1 : HasDerivAt (fun x : ℝ => 12 * exp (x * (13 / 12 : ℝ)) * (x - 2))
      (12 * (exp (t * (13 / 12 : ℝ)) * ((13 / 12 : ℝ) * (t - 2) + 1))) t := by
    simpa [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using (hasDerivAt_exp_mul (a := (13 / 12 : ℝ)) (p := fun x => x - 2)
      (p' := fun _ => 1) (hp := (hasDerivAt_id t).sub_const 2)).const_mul 12
  have h2 : HasDerivAt (fun x : ℝ => 12 * exp (x * (1 / 12 : ℝ)) * (x + 2))
        (12 * (exp (t * (1 / 12 : ℝ)) * ((1 / 12 : ℝ) * (t + 2) + 1))) t := by
    simpa [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using (hasDerivAt_exp_mul (a := (1 / 12 : ℝ)) (p := fun x => x + 2) (p' := fun _ => 1)
       (hp := (hasDerivAt_id t).add_const 2)).const_mul 12
  have h3 : HasDerivAt (fun x : ℝ => -2 * x ^ 2 * exp x)
        (-2 * (exp t * ((1 : ℝ) * (t ^ 2) + (2 : ℝ) * t))) t := by
    have h :=
      (hasDerivAt_exp_mul (a := (1 : ℝ)) (p := fun x => x ^ 2) (p' := fun x => (2 : ℝ) * x)
          (hp := hasDerivAt_sq t)).const_mul (-2)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have h4 :
      HasDerivAt (fun x : ℝ => 2 * x ^ 2) (4 * t) t := by
    exact ((hasDerivAt_sq t).const_mul (2 : ℝ)).congr_deriv (by ring)
  have H := (((h1.add h2).add h3).add h4)
  convert H using 1
  · funext x
    simp [robbinsAux, mul_assoc, mul_comm, sub_eq_add_neg]
  · simp [robbinsAux']
    ring_nf

private lemma hasDerivAt_robbinsAux' (t : ℝ) : HasDerivAt robbinsAux' (robbinsAux'' t) t := by
  -- Again: compute the derivative for a conveniently-arranged expression and normalize.
  have hp1 : HasDerivAt (fun x : ℝ => 13 * x - 14) (13 : ℝ) t := by
    simpa [id, mul_assoc] using ((hasDerivAt_id t).const_mul (13 : ℝ)).sub_const 14
  have hp2 : HasDerivAt (fun x : ℝ => x + 14) (1 : ℝ) t := by
    simpa [id] using (hasDerivAt_id t).add_const 14
  have hp3 : HasDerivAt (fun x : ℝ => x ^ 2 + 2 * x) ((2 : ℝ) * t + 2) t := by
    -- Avoid commutative rewriting: keep the normal form `x^2 + 2*x`.
    simpa [id, mul_assoc, add_assoc] using
      (hasDerivAt_sq t).add ((hasDerivAt_id t).const_mul (2 : ℝ))
  have h1 :=
    hasDerivAt_exp_mul (a := (13 / 12 : ℝ)) (p := fun x : ℝ => 13 * x - 14)
      (p' := fun _ => (13 : ℝ)) (hp := hp1)
  have h2 :=
    hasDerivAt_exp_mul (a := (1 / 12 : ℝ)) (p := fun x : ℝ => x + 14) (p' := fun _ => (1 : ℝ))
      (hp := hp2)
  have h3 :=
    (hasDerivAt_exp_mul (a := (1 : ℝ)) (p := fun x : ℝ => x ^ 2 + 2 * x)
      (p' := fun x => (2 : ℝ) * x + 2)  (hp := hp3)).const_mul (-2)
  have h4 := (hasDerivAt_id t).const_mul (4 : ℝ)
  have H := (((h1.add h2).add h3).add h4)
  convert H using 1
  · funext x
    simp [robbinsAux', mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
    ring_nf
  · simp [robbinsAux'']
    ring_nf

private lemma hasDerivAt_robbinsAux'' (t : ℝ) : HasDerivAt robbinsAux'' (robbinsAux''' t) t := by
  have hp1 : HasDerivAt (fun x : ℝ => (169 * x - 26) / 12) (169 / 12 : ℝ) t := by
    simpa [id, mul_assoc, div_eq_mul_inv] using
      ((((hasDerivAt_id t).const_mul (169 : ℝ)).sub_const 26).div_const 12)
  have hp2 : HasDerivAt (fun x : ℝ => (x + 26) / 12) (1 / 12 : ℝ) t := by
    simpa [id, div_eq_mul_inv] using ((hasDerivAt_id t).add_const 26).div_const 12
  have hp3 : HasDerivAt (fun x : ℝ => x ^ 2 + 4 * x + 2) ((2 : ℝ) * t + 4) t := by
    simpa [mul_assoc, two_mul, add_assoc, add_left_comm, add_comm] using
      (hasDerivAt_sq t).add (((hasDerivAt_id t).const_mul (4 : ℝ)).add_const 2)
  have h1 :=
    hasDerivAt_exp_mul (a := (13 / 12 : ℝ))
      (p := fun x : ℝ => (169 * x - 26) / 12) (p' := fun _ => (169 / 12 : ℝ)) (hp := hp1)
  have h2 :=
    hasDerivAt_exp_mul (a := (1 / 12 : ℝ)) (p := fun x : ℝ => (x + 26) / 12)
      (p' := fun _ => (1 / 12 : ℝ)) (hp := hp2)
  have h3 :=
    (hasDerivAt_exp_mul (a := (1 : ℝ)) (p := fun x : ℝ => x ^ 2 + 4 * x + 2)
      (p' := fun x => (2 : ℝ) * x + 4) (hp := hp3)).const_mul (-2)
  have h4 : HasDerivAt (fun _ => (4 : ℝ)) 0 t := hasDerivAt_const t 4
  have H := (((h1.add h2).add h3).add h4)
  convert H using 1
  · funext x
    simp [robbinsAux'', mul_left_comm, mul_comm, sub_eq_add_neg]
  · simp [robbinsAux''']
    ring_nf

private lemma hasDerivAt_robbinsAux''' (t : ℝ) :
    HasDerivAt robbinsAux''' (robbinsAux'''' t) t := by
  have hp1 : HasDerivAt (fun x : ℝ => (2197 * x + 1690) / 144) (2197 / 144 : ℝ) t := by
    simpa [id, mul_assoc, div_eq_mul_inv] using
      ((((hasDerivAt_id t).const_mul (2197 : ℝ)).add_const 1690).div_const 144)
  have hp2 : HasDerivAt (fun x : ℝ => (x + 38) / 144) (1 / 144 : ℝ) t := by
    simpa [id, div_eq_mul_inv] using ((hasDerivAt_id t).add_const 38).div_const 144
  have hp3 : HasDerivAt (fun x : ℝ => x ^ 2 + 6 * x + 6) ((2 : ℝ) * t + 6) t := by
    simpa [mul_assoc, two_mul, add_assoc, add_left_comm, add_comm] using
      (hasDerivAt_sq t).add (((hasDerivAt_id t).const_mul (6 : ℝ)).add_const 6)
  have h1 :=
    hasDerivAt_exp_mul (a := (13 / 12 : ℝ)) (p := fun x : ℝ => (2197 * x + 1690) / 144)
      (p' := fun _ => (2197 / 144 : ℝ)) (hp := hp1)
  have h2 :=
    hasDerivAt_exp_mul (a := (1 / 12 : ℝ)) (p := fun x : ℝ => (x + 38) / 144)
      (p' := fun _ => (1 / 144 : ℝ)) (hp := hp2)
  have h3 :=
    (hasDerivAt_exp_mul (a := (1 : ℝ)) (p := fun x : ℝ => x ^ 2 + 6 * x + 6)
      (p' := fun x => (2 : ℝ) * x + 6)  (hp := hp3)).const_mul (-2)
  have h4 : HasDerivAt (fun _ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
  have H := (((h1.add h2).add h3).add h4)
  convert H using 1
  · funext x
    simp [robbinsAux''', mul_left_comm, mul_comm, sub_eq_add_neg]
  · simp [robbinsAux'''']
    ring_nf

/-! ### Positivity of the fourth derivative -/

private noncomputable def robbinsPoly (t : ℝ) : ℝ :=
  (3431 / 864 : ℝ) + (29645 / 10368 : ℝ) * t - (130765 / 248832 : ℝ) * t ^ 2 +
    (28561 / 497664 : ℝ) * t ^ 3

private noncomputable def robbinsPoly' (t : ℝ) : ℝ :=
  (28561 / 165888 : ℝ) * t ^ 2 - (130765 / 124416 : ℝ) * t + (29645 / 10368 : ℝ)

private lemma hasDerivAt_robbinsPoly (t : ℝ) : HasDerivAt robbinsPoly (robbinsPoly' t) t := by
  unfold robbinsPoly robbinsPoly'
  have h0 : HasDerivAt (fun _x : ℝ => (3431 / 864 : ℝ)) 0 t := hasDerivAt_const t _
  have h1 : HasDerivAt (fun x : ℝ => (29645 / 10368 : ℝ) * x) (29645 / 10368 : ℝ) t := by
    simpa [mul_comm] using (hasDerivAt_id t).const_mul (29645 / 10368 : ℝ)
  have h2 :
      HasDerivAt (fun x : ℝ => -(130765 / 248832 : ℝ) * x ^ 2) (-(130765 / 124416 : ℝ) * t) t := by
    have h := (hasDerivAt_sq t).const_mul (-(130765 / 248832 : ℝ))
    convert h using 1
    · ring_nf
  have h3 :
      HasDerivAt (fun x : ℝ => (28561 / 497664 : ℝ) * x ^ 3) ((28561 / 165888 : ℝ) * t ^ 2) t := by
    have h := (hasDerivAt_cube t).const_mul (28561 / 497664 : ℝ)
    convert h using 1
    · ring_nf
  have h := (((h0.add h1).add h2).add h3)
  convert h using 1
  · funext x
    simp [Pi.add_apply]
    ring_nf
  · ring_nf

private lemma robbinsPoly'_pos (t : ℝ) : 0 < robbinsPoly' t := by
  have :
      robbinsPoly' t =
        (28561 / 165888 : ℝ) * (t - 261530 / 85683) ^ 2 + 13381385195 / 10660336128 := by
    unfold robbinsPoly'
    ring_nf
  rw [this]
  positivity

private lemma robbinsPoly_pos {t : ℝ} (_ht : 0 ≤ t) : 0 < robbinsPoly t := by
  have h0 : 0 < robbinsPoly 0 := by norm_num [robbinsPoly]
  have hmono : StrictMono robbinsPoly :=
    strictMono_of_hasDerivAt_pos hasDerivAt_robbinsPoly robbinsPoly'_pos
  exact lt_of_lt_of_le h0 (hmono.monotone _ht)

private lemma robbinsAux''''_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux'''' t := by
  have hexp13 :
      exp (t * (13 / 12 : ℝ)) = exp t * exp (t * (1 / 12 : ℝ)) := by
    have : t * (13 / 12 : ℝ) = t + t * (1 / 12 : ℝ) := by ring
    calc
      exp (t * (13 / 12 : ℝ)) = exp (t + t * (1 / 12 : ℝ)) := by simp [this]
      _ = exp t * exp (t * (1 / 12 : ℝ)) := by simp [exp_add]
  have htlin : 0 ≤ (28561 * t + 48334) / 1728 := by
    have : (0 : ℝ) ≤ 28561 * t + 48334 := by nlinarith [ht]
    nlinarith
  have hExpLower :
      robbinsPoly t ≤
        exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) - 2 * (t ^ 2 + 8 * t + 12) := by
    have hu : 0 ≤ t * (1 / 12 : ℝ) := by nlinarith [ht]
    have hexp_lb :
        1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2 ≤ exp (t * (1 / 12 : ℝ)) :=
      Real.quadratic_le_exp_of_nonneg hu
    have hmul :
        (1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2) * ((28561 * t + 48334) / 1728)
          ≤ exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) :=
      mul_le_mul_of_nonneg_right hexp_lb htlin
    have hsub :
        (1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2) * ((28561 * t + 48334) / 1728)
            - 2 * (t ^ 2 + 8 * t + 12)
          ≤
            exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) - 2 * (t ^ 2 + 8 * t + 12) :=
      sub_le_sub_right hmul _
    have :
        (1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2) * ((28561 * t + 48334) / 1728)
            - 2 * (t ^ 2 + 8 * t + 12)
          = robbinsPoly t := by
      unfold robbinsPoly
      ring
    calc
      robbinsPoly t =
          (1 + (t * (1 / 12 : ℝ)) + (t * (1 / 12 : ℝ)) ^ 2 / 2) * ((28561 * t + 48334) / 1728)
            - 2 * (t ^ 2 + 8 * t + 12) := by
              simpa using this.symm
      _ ≤ exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) - 2 * (t ^ 2 + 8 * t + 12) :=
        hsub
  have hpoly_pos : 0 < robbinsPoly t := robbinsPoly_pos (t := t) ht
  have hbracket :
      0 ≤ exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) - 2 * (t ^ 2 + 8 * t + 12) :=
    le_of_lt (lt_of_lt_of_le hpoly_pos hExpLower)
  have hterm2 : 0 ≤ exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728) := by
    have : 0 ≤ (t + 50) / 1728 := by nlinarith [ht]
    exact mul_nonneg (exp_pos _).le this
  have : robbinsAux'''' t =
      exp t *
          (exp (t * (1 / 12 : ℝ)) * ((28561 * t + 48334) / 1728) - 2 * (t ^ 2 + 8 * t + 12))
        + exp (t * (1 / 12 : ℝ)) * ((t + 50) / 1728) := by
    unfold robbinsAux''''
    simp [hexp13, mul_add, sub_eq_add_neg]
    ring
  rw [this]
  exact add_nonneg (mul_nonneg (exp_pos _).le hbracket) hterm2

private lemma robbinsAux'''_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux''' t := by
  exact nonneg_of_hasDerivAt_nonneg_Ici (f := robbinsAux''') (f' := robbinsAux'''')
    hasDerivAt_robbinsAux''' (fun x hx => robbinsAux''''_nonneg (t := x) hx) robbinsAux'''_zero ht

private lemma robbinsAux''_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux'' t := by
  exact nonneg_of_hasDerivAt_nonneg_Ici (f := robbinsAux'') (f' := robbinsAux''')
    hasDerivAt_robbinsAux'' (fun x hx => robbinsAux'''_nonneg (t := x) hx) robbinsAux''_zero ht

private lemma robbinsAux'_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux' t := by
  exact nonneg_of_hasDerivAt_nonneg_Ici (f := robbinsAux') (f' := robbinsAux'')
    hasDerivAt_robbinsAux' (fun x hx => robbinsAux''_nonneg (t := x) hx) robbinsAux'_zero ht

private lemma robbinsAux_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ robbinsAux t := by
  exact nonneg_of_hasDerivAt_nonneg_Ici (f := robbinsAux) (f' := robbinsAux')
    hasDerivAt_robbinsAux (fun x hx => robbinsAux'_nonneg (t := x) hx) robbinsAux_zero ht

/-! ### The Robbins lower bound -/

theorem one_div_twelve_mul_exp_neg_div_twelve_le_Ktilde {t : ℝ} (ht : 0 < t) :
    (1 / 12 : ℝ) * exp (-t / 12) ≤ Ktilde t := by
  rw [Ktilde_eq_kernelNum_div ht]
  have hdenom : 0 < 2 * t ^ 2 * (exp t - 1) := denom_pos ht
  have hmain : 2 * t ^ 2 * (exp t - 1) ≤ 12 * exp (t * (1 / 12 : ℝ)) * kernelNum t := by
    have h0 : 0 ≤ robbinsAux t := robbinsAux_nonneg (t := t) (le_of_lt ht)
    have hrobbins :
        robbinsAux t =
          12 * exp (t * (1 / 12 : ℝ)) * kernelNum t - 2 * t ^ 2 * (exp t - 1) := by
      unfold robbinsAux kernelNum
      have : t * (13 / 12 : ℝ) = t + t * (1 / 12 : ℝ) := by ring
      simp [this, exp_add, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
      ring
    exact sub_nonneg.1 (by simpa [hrobbins] using h0)
  have hExp : exp (-t / 12) * exp (t * (1 / 12 : ℝ)) = 1 := by
    have : (-t / 12 : ℝ) + (t * (1 / 12 : ℝ)) = 0 := by ring
    have := congrArg exp this
    simpa [exp_add, exp_zero] using this
  have hExp' : exp (-t / 12) * exp (t * (12⁻¹ : ℝ)) = 1 := by
    simpa [one_div] using hExp
  have hmul :
      ((1 / 12 : ℝ) * exp (-t / 12)) * (2 * t ^ 2 * (exp t - 1)) ≤ kernelNum t := by
    have h' :=
      mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ (1 / 12 : ℝ) * exp (-t / 12))
    refine h'.trans_eq ?_
    calc
      ((1 / 12 : ℝ) * exp (-t / 12)) * (12 * exp (t * (1 / 12 : ℝ)) * kernelNum t)
          = (exp (-t / 12) * exp (t * (1 / 12 : ℝ))) * kernelNum t := by ring
      _ = kernelNum t := by
            have := congrArg (fun z => z * kernelNum t) hExp'
            simpa [mul_assoc] using this
  exact (le_div_iff₀ hdenom).2 hmul

end Binet
