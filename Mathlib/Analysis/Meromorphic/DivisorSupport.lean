/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof

/-!
# Support of the divisor of a meromorphic function

This file contains topological properties of the support of `MeromorphicOn.divisor`.
In particular, the support is discrete, and in hereditarily Lindelöf spaces it is countable.
It is also locally finite within the domain, hence meets compact subsets of the domain in finitely
many points.
-/

@[expose] public section

open Filter Topology Set

namespace MeromorphicOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U K : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Discreteness and countability of the divisor support
-/

/-- The support of the divisor of a meromorphic function is a discrete subset. -/
lemma divisor_support_discrete (f : 𝕜 → E) (U : Set 𝕜) :
    IsDiscrete (divisor f U).support := by
  simpa using (Function.locallyFinsuppWithin.discreteSupport (D := divisor f U))

/-- In a hereditarily Lindelöf space, the support of the divisor of a meromorphic function
is countable. -/
lemma divisor_support_countable [HereditarilyLindelofSpace 𝕜] (f : 𝕜 → E) (U : Set 𝕜) :
    (divisor f U).support.Countable := by
  simpa using
    (HereditarilyLindelof_LindelofSets (s := (divisor f U).support)).countable_of_isDiscrete
      (divisor_support_discrete (f := f) (U := U))

/-!
## Finiteness of the divisor support on compact subsets of the domain
-/

/-- The divisor support meets compact subsets of the domain in finitely many points. -/
lemma divisor_support_inter_compact_finite (f : 𝕜 → E) {U K : Set 𝕜}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ (divisor f U).support).Finite := by
  classical
  set D : Function.locallyFinsuppWithin U ℤ := divisor f U
  have hloc : ∀ x ∈ K, ∃ V : Set 𝕜, V ∈ 𝓝 x ∧ Set.Finite (V ∩ D.support) := by
    intro x hxK
    simpa using D.supportLocallyFiniteWithinDomain x (hKU hxK)
  choose V hVnhds hVfin using hloc
  rcases hK.elim_nhds_subcover' (U := fun x hx => V x hx) (hU := fun x hx => hVnhds x hx) with
    ⟨t, ht⟩
  have hsub :
      K ∩ D.support ⊆ ⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyK, hyS⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : 𝕜) x.2 := ht hyK
    rcases Set.mem_iUnion.1 hycov with ⟨x, hycov'⟩
    rcases Set.mem_iUnion.1 hycov' with ⟨hxT, hyV⟩
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ?_⟩
    exact ⟨hxT, ⟨hyV, hyS⟩⟩
  have hfinU : Set.Finite (⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support)) := by
    refine (t.finite_toSet).biUnion ?_
    intro x hx
    simpa using (hVfin (x : 𝕜) x.2)
  exact hfinU.subset hsub

/-!
## Local singleton balls and enumerations of the divisor support
-/

/-- Around any point in the divisor support (for `U = univ`), there is a small metric ball whose
intersection with the support is exactly that singleton. -/
lemma exists_ball_inter_divisor_support_eq_singleton {f : 𝕜 → E} (z₀ : 𝕜)
    (hz₀ : z₀ ∈ (divisor f (Set.univ : Set 𝕜)).support) :
    ∃ ε > 0, Metric.ball z₀ ε ∩ (divisor f (Set.univ : Set 𝕜)).support = {z₀} := by
  simpa using
    Metric.exists_ball_inter_eq_singleton_of_mem_discrete
      (hs := divisor_support_discrete (f := f) (U := (Set.univ : Set 𝕜))) hz₀

/-- In a hereditarily Lindelöf space, a nonempty divisor support can be enumerated by a sequence. -/
lemma exists_seq_eq_range_divisor_support [HereditarilyLindelofSpace 𝕜] {f : 𝕜 → E} {U : Set 𝕜}
    (hne : (divisor f U).support.Nonempty) :
    ∃ a : ℕ → 𝕜, (divisor f U).support = Set.range a := by
  simpa using (divisor_support_countable (f := f) (U := U)).exists_eq_range hne

/-- In a hereditarily Lindelöf space, the divisor support away from `0` is contained in the range of
a nonzero sequence. -/
lemma exists_nonzero_seq_divisor_support_diff_zero [HereditarilyLindelofSpace 𝕜]
    {f : 𝕜 → E} {U : Set 𝕜} :
    ∃ a : ℕ → 𝕜,
      (∀ n, a n ≠ 0) ∧ (divisor f U).support \ {0} ⊆ Set.range a := by
  set s : Set 𝕜 := (divisor f U).support \ {0}
  by_cases hs : s.Nonempty
  · have hs_count : s.Countable := by
      have hsup : (divisor f U).support.Countable := divisor_support_countable (f := f) (U := U)
      refine hsup.mono ?_
      intro x hx
      exact hx.1
    rcases hs_count.exists_eq_range hs with ⟨a, ha⟩
    refine ⟨a, ?_, ?_⟩
    · intro n
      have han : a n ∈ s := by simp [ha]
      exact fun h0 => han.2 (by simpa [Set.mem_singleton_iff] using h0)
    · simp [s, ha]
  · refine ⟨fun _ => (1 : 𝕜), ?_, ?_⟩
    · intro _; simp
    · have : s = ∅ := Set.not_nonempty_iff_eq_empty.1 hs
      simp [this]

end MeromorphicOn
