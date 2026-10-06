/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BD
import Hironaka.Resolution.Analytic.OrderReduction.BDOf
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lemma 102: indifference to empty boundary members

The analytic functors are required to be indifferent to empty boundary members
(`AnalyticBlowUpSequenceAssignment.IndifferentToEmptyMembers`; the counterpart for
boundary members of the empty blow-up convention [Kol07, 32]): deleting empty members of the
boundary along an order
embedding of index sets does not change the value. For `BDan`, the analytic `BD_{n,m,·}` of
[Kol07, Lemma 102], the value at a kept member `e i` of `E` equals the value at the member `i` of
the smaller boundary `F'`.

The first centre and the transform of the member depend only on the hypersurface
`E^j = E^{e i} = F'^i` itself (`Zminus1_eq_of_hyp_eq`, `transformS_eq_transformSOf`, read through
the parametrized core of `BDOf.lean`); the two restricted triples differ only in the index set of
their boundary, and the indifference of the input functor absorbs the difference: the restriction
of `E - E^{e i}` to `S_0` embeds the restriction of `F' - F'^i` along `e`, with the members
matched and empty outside the range.

* `BDan.withBoundary` — the triple with its boundary replaced.
* `BDan.Zminus1_eq_of_hyp_eq`, `BDan.transformS_eq_transformSOf` — the data at `e i` and at `i`.
* `BDan.core_indifferentToEmptyMembers` — the clause for the core at the mark `s`.
* `BDan_indifferentToEmptyMembers` — the clause for `BDan`, tuning keeping the boundary.
-/

@[expose] public section

noncomputable section

open Set Topology IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace BDan

open _root_.Manifold

variable [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- The triple `T` with its boundary replaced by the family `F'` with simple normal crossings. -/
abbrev withBoundary (T : AnalyticTriple ψ₀ M) (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀) :
    AnalyticTriple ψ₀ M :=
  ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩

variable (T : AnalyticTriple ψ₀ M) (s : ℕ) (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀)
  (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i) (i : F'.ι)

omit [FiniteDimensional 𝕜 E] in
include he in
/-- The first centre at the member `e i` of `E` is the first centre at the member `i` of `F'`. -/
theorem Zminus1_eq_of_hyp_eq :
    BD.Zminus1 T.I s (T.F.hyp (e i)) =
      BD.Zminus1 (withBoundary T F' hsnc').I s
        ((withBoundary T F' hsnc').F.hyp i) := by
  change BD.Zminus1 T.I s (T.F.hyp (e i)) = BD.Zminus1 T.I s (F'.hyp i)
  rw [he i]

include he in
/-- The transform of the member `e i` of `E` is the transform of the member `i` of `F'` (over the
first centre at `e i`). -/
theorem transformS_eq_transformSOf :
    transformS T s (e i) =
      transformSOf (withBoundary T F' hsnc') i
        (BD.isClosedSubmanifold_Zminus1 T s (e i)) := by
  change ⇑(Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s (e i))) ⁻¹' T.F.hyp (e i) =
    ⇑(Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s (e i))) ⁻¹' F'.hyp i
  exact congrArg (Set.preimage ⇑(Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s (e i))))
      (he i)

include he in
/-- Indifference to empty boundary members for the core at the mark `s`: the core at the member
`e i` of `E` is the core at the member `i` of `F'`. The first centre and the transform of the
member agree, and the input functor is indifferent to the empty members of the restricted
boundary: the restriction of `E - E^{e i}` to `S_0` embeds that of `F' - F'^i` along `e`, with
matched members and empty members outside the range. -/
theorem core_indifferentToEmptyMembers (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    (inp : BMOanData 𝕜 (n - 1) s) (hT : BDClass s T)
    (hT₂ : BDClass s (withBoundary T F' hsnc')) :
    core T s (e i) inp hT = core (withBoundary T F' hsnc') s i inp hT₂ := by
  rw [core_eq_of_eq T s (e i) (BD.isClosedSubmanifold_Zminus1 T s (e i))
      (isClosedSubmanifold_transformS T s (e i)) inp hT rfl rfl,
    core_eq_of_eq (withBoundary T F' hsnc') s i (BD.isClosedSubmanifold_Zminus1 T s (e i))
      (isClosedSubmanifold_transformS T s (e i)) inp hT₂ (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
      (transformS_eq_transformSOf T s F' hsnc' e he i)]
  unfold coreOfListOf
  -- the restricted boundary of `E − E^{e i}` embeds that of `F' − F'^i` along `e`
  have hmatch : ∀ k, (restrictedTripleOf T s (e i) (BD.isClosedSubmanifold_Zminus1 T s (e i))
      (isClosedSubmanifold_transformS T s (e i)) hT rfl rfl).F.hyp (e k) =
      (restrictedTripleOf (withBoundary T F' hsnc') s i
        (BD.isClosedSubmanifold_Zminus1 T s (e i)) (isClosedSubmanifold_transformS T s (e i)) hT₂
        (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
        (transformS_eq_transformSOf T s F' hsnc' e he i)).F.hyp k := by
    intro k
    change (isClosedSubmanifold_transformS T s (e i)).preimageVal
        (⇑(Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s (e i))) ⁻¹'
          (T.F.emptyMember (e i)).hyp (e k)) =
      (isClosedSubmanifold_transformS T s (e i)).preimageVal
        (⇑(Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s (e i))) ⁻¹'
            (F'.emptyMember i).hyp k)
    congr 2
    by_cases hk : k = i
    · subst hk
      rw [HypersurfaceFamily.emptyMember_hyp_self, HypersurfaceFamily.emptyMember_hyp_self]
    · rw [HypersurfaceFamily.emptyMember_hyp_of_ne T.F fun h => hk (e.injective h),
        HypersurfaceFamily.emptyMember_hyp_of_ne F' hk, he k]
  have hout : ∀ b, b ∉ Set.range e →
      (restrictedTripleOf T s (e i) (BD.isClosedSubmanifold_Zminus1 T s (e i))
        (isClosedSubmanifold_transformS T s (e i)) hT rfl rfl).F.hyp b = ∅ := by
    intro b hb
    change (isClosedSubmanifold_transformS T s (e i)).preimageVal
        (⇑(Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s (e i))) ⁻¹'
          (T.F.emptyMember (e i)).hyp b) = ∅
    have hb0 : (T.F.emptyMember (e i)).hyp b = ∅ := by
      by_cases hbi : b = e i
      · subst hbi
        exact HypersurfaceFamily.emptyMember_hyp_self T.F (e i)
      · rw [HypersurfaceFamily.emptyMember_hyp_of_ne T.F hbi]
        exact he' b hb
    rw [hb0, Set.preimage_empty]
    exact Set.eq_empty_iff_forall_notMem.mpr fun p hp => hp
  have hX : inp.functor.seq
      (restrictedTripleOf T s (e i) (BD.isClosedSubmanifold_Zminus1 T s (e i))
        (isClosedSubmanifold_transformS T s (e i)) hT rfl rfl)
      (bmoClass_restrictedTripleOf T s (e i) (BD.isClosedSubmanifold_Zminus1 T s (e i))
        (isClosedSubmanifold_transformS T s (e i)) hT rfl rfl) =
    inp.functor.seq
      (restrictedTripleOf (withBoundary T F' hsnc') s i
        (BD.isClosedSubmanifold_Zminus1 T s (e i)) (isClosedSubmanifold_transformS T s (e i)) hT₂
        (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
        (transformS_eq_transformSOf T s F' hsnc' e he i))
      (bmoClass_restrictedTripleOf (withBoundary T F' hsnc')
        s i (BD.isClosedSubmanifold_Zminus1 T s (e i)) (isClosedSubmanifold_transformS T s (e i))
        hT₂ (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
        (transformS_eq_transformSOf T s F' hsnc' e he i)) :=
    inp.indifferentToEmptyMembers
      (restrictedTripleOf T s (e i) (BD.isClosedSubmanifold_Zminus1 T s (e i))
        (isClosedSubmanifold_transformS T s (e i)) hT rfl rfl)
      (restrictedTripleOf (withBoundary T F' hsnc') s i
        (BD.isClosedSubmanifold_Zminus1 T s (e i)) (isClosedSubmanifold_transformS T s (e i)) hT₂
        (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
        (transformS_eq_transformSOf T s F' hsnc' e he i)).F
      (restrictedTripleOf (withBoundary T F' hsnc') s i
        (BD.isClosedSubmanifold_Zminus1 T s (e i)) (isClosedSubmanifold_transformS T s (e i)) hT₂
        (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
        (transformS_eq_transformSOf T s F' hsnc' e he i)).isSnc
      e hmatch hout _ _
  rw [hX]

end BDan

section Assembly

variable [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {m : ℕ}

/-- **`BD_{n,m,·}` is indifferent to empty boundary members** (the counterpart for boundary
members of the empty blow-up convention [Kol07, 32]): for a boundary `F'` with simple normal
crossings embedding
order-preservingly into `E` along `e`, with the members matched and empty outside the range, the
value at the kept member `e i` equals the value at `i` for the triple with boundary `F'`. It is the
clause for the core at the tuned triple, tuning keeping the boundary. -/
theorem BDan_indifferentToEmptyMembers (inp : BMOanData 𝕜 (n - 1) (tuningParam m))
    (T : AnalyticTriple ψ₀ M) (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι)
    (he : ∀ i, T.F.hyp (e i) = F'.hyp i) (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    (hT : AnalyticTriple.BOClass m T)
    (hT' : AnalyticTriple.BOClass m
      (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M)) (i : F'.ι) :
    BDan m inp T hT (e i) = BDan m inp ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ hT' i := by
  unfold BDan
  exact BDan.core_indifferentToEmptyMembers (T.tuned m hT.1) (tuningParam m) F' hsnc' e he i he'
    inp _ ⟨AnalyticTriple.boClass_tuned hT', AnalyticTriple.isDBalanced_tuned hT'⟩

end Assembly

end Hironaka.Manifold

end
