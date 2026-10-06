/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Basic
public import Hironaka.Algebra.Local.TuningParam
public import Hironaka.Manifold.IdealSheaf.Tuning
import Hironaka.Algebra.Local.Regular
import Hironaka.Manifold.IdealSheaf.TuningLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 1 of Theorem 103: the tuned triple

Step 1 of the proof of [Kol07, Theorem 103] replaces `I` by an ideal `W(I) = W_s(I)` which is
D-balanced and MC-invariant and for which order reduction is equivalent to order reduction for `I`,
taking `s = m!` "to avoid further choices". The ideal
`W_s(I)` is the maximal coefficient ideal of [Kol07, Definition 98], and [Kol07, Corollary 101]
admits any `s = r · lcm(2, …, m)` with `r ≥ m − 1`. On manifolds the tuned ideal sheaf is
`𝓘.tuning m (tuningParam m)`, the maximal coefficient ideal sheaf of order `s = tuningParam m`,
where `tuningParam m = max (m − 1) 1 · lcm(2, …, m)` is the smallest admissible choice of `s` made
positive; this differs from Kollár's `m!`, which the argument does not need.

* `AnalyticTriple.tuned T m hm` — the triple `(M, W_s(𝓘), E)`: the tuned ideal sheaf with the same
  boundary; it is nonzero everywhere since `𝓘^s ⊆ W_s(𝓘)` and the stalks are domains.
* `AnalyticTriple.boClass_tuned`, `hasMaximalContact_tuned`, `localMCClass_tuned`,
  `isDBalanced_tuned`, `isMCInvariant_tuned` — the tuned triple of a triple of `BOClass m` lies in
  `BOClass s` (the order of `W_s(𝓘)` is at most `s` everywhere), a hypersurface of maximal contact
  for `(𝓘, m)` is one for `(W_s(𝓘), s)` (`MC(W_s(I)) = MC(I)`, [Kol07, Proposition 99 (4)]), and the
  tuned ideal sheaf is D-balanced and MC-invariant ([Kol07, Proposition 99 (5), (8)]). These need
  only `ord 𝓘 ≤ m` everywhere, so no case distinction on `max-ord I = m` is made: where the order
  is everywhere `< m` the order-reduction sequence is empty anyway, no centre of a sequence of order
  `≥ s` being nonempty.
* `AnalyticBlowUpSequenceAssignment.ofTunedClass` — the Step 1 wrapper: a functor on a class whose
  tuned triples lie in the domain of a functor `B` at the mark `s` is evaluated on the tuned triple.

The transfer of the order-reduction clauses between `(𝓘, m)` and `(W_s(𝓘), s)` is in
`TunedLemmas.lean`; the wrapper is applied to the local functor of Step 2 in `Assembly.lean`.
-/

@[expose] public section

noncomputable section

open Set Topology IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E}

namespace AnalyticTriple

/-- The tuned triple `(M, W_s(𝓘), E)` of Step 1 of the proof of [Kol07, Theorem 103], with
`s = tuningParam m`: the ideal sheaf replaced by its maximal coefficient ideal sheaf
`𝓘.tuning m (tuningParam m)` ([Kol07, Definition 98]), the boundary kept. The tuned ideal sheaf is
nonzero everywhere: it contains `𝓘^s` (`pow_le_tuning`) and the stalks are domains. -/
def tuned (T : AnalyticTriple ψ₀ M) (m : ℕ) (hm : 1 ≤ m) : AnalyticTriple ψ₀ M where
  I := T.I.tuning m (tuningParam m)
  isNonzeroEverywhere := by
    intro x hbot
    have hle : T.I ^ tuningParam m ≤ T.I.tuning m (tuningParam m) :=
      IdealSheaf.pow_le_tuning T.I m (tuningParam m) (Nat.le_mul_of_pos_left _ hm)
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (T.isNonzeroEverywhere x)
    have hmem : f ^ tuningParam m ∈ (T.I.tuning m (tuningParam m)).stalkIdeal x := by
      have h := IdealSheaf.le_def.mp hle x
      rw [IdealSheaf.stalkIdeal_pow] at h
      exact h (Ideal.pow_mem_pow hf _)
    rw [hbot] at hmem
    have hdom : IsDomain ((structureSheaf 𝕜 E M).presheaf.stalk x) := inferInstance
    exact pow_ne_zero _ hf0 ((Submodule.mem_bot _).mp hmem)
  F := T.F
  isSnc := T.isSnc

@[simp] theorem tuned_I (T : AnalyticTriple ψ₀ M) (m : ℕ) (hm : 1 ≤ m) :
    (T.tuned m hm).I = T.I.tuning m (tuningParam m) := rfl

@[simp] theorem tuned_F (T : AnalyticTriple ψ₀ M) (m : ℕ) (hm : 1 ≤ m) : (T.tuned m hm).F = T.F :=
  rfl

variable {T : AnalyticTriple ψ₀ M} {m : ℕ}

/-- For `ord 𝓘 ≤ m` everywhere, the tuned ideal sheaf has order at most `s = tuningParam m`
everywhere: exactly `s` where `ord 𝓘 = m`, less than `s` where `ord 𝓘 < m`. -/
theorem ord_tuned_le (hT : BOClass m T) (x : M) :
    (T.tuned m hT.1).I.ord x ≤ (tuningParam m : ℕ∞) := by
  rw [tuned_I]
  by_cases h : (m : ℕ∞) ≤ T.I.ord x
  · exact le_of_eq (IdealSheaf.ord_tuning T.I m (tuningParam m) hT.1 (le_antisymm (hT.2.1 x) h))
  · exact le_of_lt (not_le.mp fun h' =>
      h ((IdealSheaf.le_ord_tuning_iff T.I m (tuningParam m) hT.1 (one_le_tuningParam m) x).mp h'))

/-- The tuned triple of a triple of the class `BOClass m` lies in the class `BOClass s`,
`s = tuningParam m` (Step 1 of the proof of [Kol07, Theorem 103]). -/
theorem boClass_tuned (hT : BOClass m T) : BOClass (tuningParam m) (T.tuned m hT.1) :=
  ⟨one_le_tuningParam m, ord_tuned_le hT, hT.2.2⟩

/-- The tuned ideal sheaf is D-balanced at the mark `s = tuningParam m` (Step 1 of the proof of
[Kol07, Theorem 103]; [Kol07, Proposition 99 (8)]). -/
theorem isDBalanced_tuned (hT : BOClass m T) :
    (T.tuned m hT.1).I.IsDBalanced (tuningParam m) := by
  rw [tuned_I]
  exact IdealSheaf.isDBalanced_tuning_tuningParam T.I m hT.1 hT.2.1

/-- The tuned ideal sheaf is MC-invariant at the mark `s = tuningParam m` (Step 1 of the proof of
[Kol07, Theorem 103]; [Kol07, Proposition 99 (5)]). -/
theorem isMCInvariant_tuned (hT : BOClass m T) :
    (T.tuned m hT.1).I.IsMCInvariant (tuningParam m) := by
  rw [tuned_I]
  exact IdealSheaf.isMCInvariant_tuning_tuningParam T.I m hT.1 hT.2.1

/-- A hypersurface of maximal contact for `(𝓘, m)` is one for `(W_s(𝓘), s)`, since
`MC(W_s(I)) = MC(I)` ([Kol07, Proposition 99 (4)]): the class with a global hypersurface of maximal
contact is stable under tuning. -/
theorem hasMaximalContact_tuned (hT : BOClass m T) (h : HasMaximalContact m T) :
    HasMaximalContact (tuningParam m) (T.tuned m hT.1) := by
  obtain ⟨H, hH, hle⟩ := h
  refine ⟨H, hH, ?_⟩
  rw [tuned_I, IdealSheaf.iteratedDeriv_tuning T.I m (tuningParam m) hT.1 hT.2.1
    (one_le_tuningParam m)]
  exact hle

/-- The tuned triple of a triple of `LocalMCClass m` lies in `LocalMCClass s`, `s = tuningParam
m`. -/
theorem localMCClass_tuned (hT : LocalMCClass m T) :
    LocalMCClass (tuningParam m) (T.tuned m hT.1.1) :=
  ⟨boClass_tuned hT.1, hasMaximalContact_tuned hT.1 hT.2⟩

end AnalyticTriple

namespace AnalyticBlowUpSequenceAssignment

variable {C Dom' : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}

/-- The wrapper for Step 1 of the proof of [Kol07, Theorem 103] ("from now on we assume that `I` is
D-balanced and MC-invariant"): a blow-up sequence functor on the class `C` whose values are those
of the functor `B` (at the mark `s = tuningParam m`) on the tuned triples; the class `C` forces
`1 ≤ m` and its tuned triples lie in the domain of `B`. -/
def ofTunedClass (m : ℕ) (B : AnalyticBlowUpSequenceAssignment ψ₀ Dom')
    (hmC : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M), C T → 1 ≤ m)
    (hDom : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : C T),
      Dom' (T.tuned m (hmC T hT))) :
    AnalyticBlowUpSequenceAssignment ψ₀ C where
  seq T hT := B.seq (T.tuned m (hmC T hT)) (hDom T hT)
  noEmptyCenters _ _ := B.noEmptyCenters _ _

@[simp] theorem ofTunedClass_seq (m : ℕ) (B : AnalyticBlowUpSequenceAssignment ψ₀ Dom')
    (hmC : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M), C T → 1 ≤ m)
    (hDom : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : C T),
      Dom' (T.tuned m (hmC T hT)))
    (T : AnalyticTriple ψ₀ M) (hT : C T) :
    (ofTunedClass m B hmC hDom).seq T hT = B.seq (T.tuned m (hmC T hT)) (hDom T hT) := rfl

end AnalyticBlowUpSequenceAssignment

end Manifold

end
