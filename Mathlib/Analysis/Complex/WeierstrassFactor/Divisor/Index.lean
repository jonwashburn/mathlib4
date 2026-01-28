/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Complex.WeierstrassFactor.Defs
import Mathlib.Analysis.Meromorphic.DivisorSupport

/-!
# Indexing zeros via the intrinsic divisor

This file defines index types that enumerate zeros of a meromorphic function (with multiplicity)
using `MeromorphicOn.divisor`.

The main use is in Hadamard/Weierstrass factorization, where these indices are used to build
canonical products.
-/

noncomputable section

@[expose] public section

open Set
open scoped BigOperators

namespace Complex.Hadamard

/-!
## Index types
-/

/-- Index type enumerating zeros (with multiplicity) via the divisor. -/
def divisorZeroIndex (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  Σ z : ℂ, Fin (Int.toNat (MeromorphicOn.divisor f U z))

/-- The nonzero part of `divisorZeroIndex`. -/
abbrev divisorZeroIndex₀ (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  {p : divisorZeroIndex f U // p.1 ≠ 0}

/-- The underlying point of a (nonzero) divisor index. -/
abbrev divisorZeroIndex₀_val {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) : ℂ :=
  p.1.1

@[simp] lemma divisorZeroIndex₀_val_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ≠ 0 := p.2

/-- A (nonzero) divisor index has nonzero divisor at its underlying point. -/
@[simp]
lemma divisorZeroIndex₀_val_divisor_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) :
    MeromorphicOn.divisor f U (divisorZeroIndex₀_val p) ≠ 0 := by
  classical
  set n : ℕ := Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p))
  have hn : n ≠ 0 := by
    intro hn0
    have : Fin 0 := by simpa [divisorZeroIndex₀_val, divisorZeroIndex, n, hn0] using p.1.2
    exact Fin.elim0 this
  intro hdiv
  have : n = 0 := by simp [n, hdiv]
  exact hn this

lemma divisorZeroIndex₀_val_mem_support {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ∈ (MeromorphicOn.divisor f U).support := by
  simp [Function.mem_support, divisorZeroIndex₀_val_divisor_ne_zero (p := p)]

lemma exists_ball_inter_divisor_support_eq_singleton_of_index
    {f : ℂ → ℂ} (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    ∃ ε > 0,
      Metric.ball (divisorZeroIndex₀_val p) ε ∩
          (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support =
        {divisorZeroIndex₀_val p} := by
  simpa using
    MeromorphicOn.exists_ball_inter_divisor_support_eq_singleton
      (f := f)
      (z₀ := divisorZeroIndex₀_val p)
      (hz₀ := divisorZeroIndex₀_val_mem_support (p := p))

/-- The canonical product attached to the (nonzero) divisor of `f` on `U`. -/
def divisorCanonicalProduct (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f U, weierstrassFactor m (z / divisorZeroIndex₀_val p)

@[simp] lemma divisorCanonicalProduct_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 = 1 := by
  classical
  simp [divisorCanonicalProduct]

lemma divisorCanonicalProduct_ne_zero_at_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 ≠ 0 := by
  simp [divisorCanonicalProduct_zero]

end Complex.Hadamard
