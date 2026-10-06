/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.Assembly
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Resolution.Analytic.Principalization.ShrinkAppendLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The value of the principalization family restricts

The compatibility clause of the compatible-family form ([Wlo09, Theorem 2.0.3 (4)]; Kollár's
functoriality for smooth morphisms, [Kol07, 34.1], per open) for the value of `Assembly.lean` at
a fixed shrinking open `W`: for `U ≤ V` both relatively compact with closures in `W`, the value on
`U` computed with `W` is the value on `V` computed with `W`, pulled back along the open inclusion
`U → V` and with the empty rounds erased (`principalizationValueOn_restrict`). The proof is the
restriction law of the shrink-and-append step (`shrinkAppend_pullback_eraseEmpty`): the
disjoining list over `W` is the same on both sides, the open inclusions compose (`restrictLE`),
and the order-reduction values on the two reading opens are related by the input family's own
compatibility clause (the reading open over `U` lying in the reading open over `V`). The
independence of `W` is `Canonicity.lean`.
-/

public section

universe u

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- The open inclusions of the chain compose: `U → V → W` is `U → W`. -/
theorem restrictLE_comp_restrictLE {U V W : Opens M} (hUV : U ≤ V) (hVW : V ≤ W) :
    (M.restrictLE hVW).comp (M.restrictLE hUV) = M.restrictLE (hUV.trans hVW) :=
  ContMDiffMap.ext fun _ => Subtype.ext rfl

/-- **The value restricts at a fixed shrinking open** ([Wlo09, Theorem 2.0.3 (4)]; [Kol07, 34.1]
per open): for `U ≤ V` with closures in `W`, the value on `U` computed with `W` is the value on
`V` computed with `W`, pulled back along `U → V`, with the empty rounds erased. -/
theorem principalizationValueOn_restrict (bmo : BMOanFam.{u} 𝕜 n 1)
    (T : Manifold.AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) {U V W : Opens M}
    (hU : IsCompact (closure (U : Set M))) (hV : IsCompact (closure (V : Set M)))
    (hW : IsCompact (closure (W : Set M))) (hUW : closure (U : Set M) ⊆ (W : Set M))
    (hVW : closure (V : Set M) ⊆ (W : Set M)) (hUV : U ≤ V) :
    principalizationValueOn bmo T U hU W hW hUW =
      ((principalizationValueOn bmo T V hV W hW hVW).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  have hcomp : (M.restrictLE (subset_closure.trans hVW)).comp (M.restrictLE hUV) =
      M.restrictLE (subset_closure.trans hUW) :=
    ContMDiffMap.ext fun _ => Subtype.ext rfl
  have hle : (disjoinListOn T W hW).liftRange (M.restrictLE (subset_closure.trans hUW))
        (isLocalDiffeomorph_restrictLE (subset_closure.trans hUW)) ≤
      (disjoinListOn T W hW).liftRange (M.restrictLE (subset_closure.trans hVW))
        (isLocalDiffeomorph_restrictLE (subset_closure.trans hVW)) :=
    AnalyticManifold.BlowUpSequence.range_pullbackLiftLast_subset_of_comp
        (disjoinListOn T W hW) _ _ _
      (isLocalDiffeomorph_restrictLE hUV) _ _ hcomp
  unfold principalizationValueOn valueOf
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty]
  refine (AnalyticManifold.BlowUpSequence.shrinkAppend_pullback_eraseEmpty _ _ _ _ _ _ _ hcomp _ _
      hle ?_).symm
  rw [(bmo.functor.fam
    (disjoinedTriple (restrictTriple T W) (meetLocus_disjoinBound_eq_empty T W hW))
    (disjoinedTriple_bmoClass _ _)).compat _ _ _ _ hle]
  exact AnalyticManifold.BlowUpSequence.eraseEmpty_eraseEmpty _

end Hironaka.Manifold
