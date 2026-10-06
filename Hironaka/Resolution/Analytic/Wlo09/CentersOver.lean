/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Rounds
public import Hironaka.Resolution.Analytic.Principalization.Assembly
public import Hironaka.Resolution.Analytic.Principalization.IsoOff
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.Principalization.BoundaryConcat
import Hironaka.Resolution.Analytic.Principalization.ClauseThree
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The centres of the resolution rounds lie over the cosupport

For the value `resolveSeqOn bo T U hU` of the resolution family on a relatively compact open `U`
(the rounds `d_U, …, 1` of the order-reduction functors `bo d`,
`Hironaka/Resolution/Analytic/Wlo09/Rounds.lean`), the composite blow-down is an analytic
isomorphism over `U ∖ V(𝓘|_U)`: clause (3) of [Kol07, Theorem 35] and [Wlo09, Lemma 4.0.3], proved
from the fields of the functors `bo` alone.

* `centersOver_resolveFrom`, the invariant of the recursion `resolveFrom`: every centre of the
  rounds from `d` on the current triple `cur`, read on `N` along the local analytic isomorphism `ι`,
  lies over `ι⁻¹(V(cur.I))`. Round by round: the value of the round `bo (d + 1)` on `Ω d` is a
  sequence of order `≥ d + 1` for the restricted marked ideal ([Kol07, Definition 66 (4′)], the
  field `isOfOrderGe`), so its centres lie in the cosupport of the current marked transform, which
  lies over the cosupport of `cur.I` (`FiniteSuccession.CentersOver.of_isOfOrderGe`,
  `cosupport_markedTransformSeqAux_subset`); the pull-back along the corestriction of `ι` transports
  the invariant (`IdealSheaf.support_pullback`); the derived triple's ideal is the marked transform
  at mark `d + 1` (`AnalyticTriple.induced`; Hironaka's weak transform [Hir64, p. 142], see
  `Hironaka/Resolution/Analytic/Wlo09/HironakaClauses.lean`), whose cosupport lies over the previous
  one; the last-stage lift of `ι` lies over `ι` (`stageMap_last_pullbackLiftLast`);
  `centersOver_concat` splits the concatenation at the round's last stage.
* `isAnalyticIsoOver_stageMap_last_resolveSeqOn`: the composite blow-down of
  `resolveSeqOn bo T U hU` is an analytic isomorphism over `U ∖ V(𝓘|_U)`
  (`FiniteSuccession.isAnalyticIsoOver_stageMap` on the invariant along the canonical chain, the
  deletion of the empty rounds transporting the predicate,
  `isAnalyticIsoOver_stageMap_last_eraseEmpty`).

The glued form on the whole manifold is `isAnalyticIsoOver_resolveFamExt_map`
(`Hironaka/Resolution/Analytic/Wlo09/FamilyExt.lean`), by
`CompatibleFamily.isAnalyticIsoOver_limitBlowDown`
(`Hironaka/Resolution/Analytic/Functor/LimitGluing.lean`).
-/

public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)

/-- The invariant of the recursion `resolveFrom`: every centre of the rounds from `d` on the current
triple `cur`, read on `N` along `ι`, lies over the cosupport of `cur.I`. The round's centres lie in
the cosupport of the current marked transform (the order bound `isOfOrderGe`,
[Kol07, Definition 66 (4′)]), the cosupport of the marked transform lies over the previous one, and
the last-stage lift of `ι` lies over `ι`. -/
theorem centersOver_resolveFrom :
    ∀ (d : ℕ) {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
      (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
      (hord : ∀ x, cur.I.ord x ≤ (d : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅})
      (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
      (hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
      {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
      (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
      (hrange : Set.range ι ⊆ Ω 0),
      (resolveFrom bo d cur hord hfin Ω hΩ hΩsub ι hι hrange).toSuccession.CentersOver
        (⇑ι ⁻¹' cur.I.support)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => fun i => i.elim0
  | d + 1, X, cur, hord, hfin, Ω, hΩ, hΩsub, N, ι, hι, hrange => by
    -- the round at `Ω d`, pulled back along the corestriction of `ι`: order `≥ d + 1` for the
    -- restricted marked ideal, so the centres lie over its cosupport, which is `ι⁻¹(V(cur.I))`
    have hround : ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).pullback
          (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι
            (range_subset_chain hΩsub hrange))).toSuccession.CentersOver
        (⇑ι ⁻¹' cur.I.support) := by
      have hge := AnalyticTriple.isOfOrderGe_pullback _ (d + 1)
        (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self d)))
        ((bo (d + 1)).isOfOrderGe cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d)))
        (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
        (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))
      refine (FiniteSuccession.CentersOver.of_isOfOrderGe _ hge
        (Nat.succ_le_succ (Nat.zero_le d))).mono fun q hq => ?_
      change q ∈ ((cur.I.pullback _ (X.inclusion (Ω d)).contMDiff).pullback _
          (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange)).contMDiff).support
        at hq
      rw [IdealSheaf.support_pullback, Set.mem_preimage, IdealSheaf.support_pullback,
        Set.mem_preimage] at hq
      exact hq
    -- the later rounds, over the derived triple: the induction hypothesis, then the marked
    -- transform's cosupport lies over the previous cosupport and the lift lies over `ι`
    have hrest := centersOver_resolveFrom d
      (derivedTriple bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d)))
      (derivedTriple_ord_le bo cur _ (Ω d) _) (derivedTriple_finite bo cur _ (Ω d) _)
      (liftChain (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))) Ω)
      (liftChain_isCompact _ hΩ hΩsub rfl) (liftChain_closure_subset _ hΩsub)
      ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).pullbackLiftLast
        (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
        (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange)))
      (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
      (range_pullbackLiftLast_subset_liftOpens _ ι hι (Ω 0) hrange
        (range_subset_chain hΩsub hrange))
    refine BlowUpSequence.centersOver_concat _ _ _ hround (hrest.mono fun q hq => ?_)
    simp only [Set.mem_preimage] at hq ⊢
    have h1 := FiniteSuccession.cosupport_markedTransformSeqAux_subset
      (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).toSuccession
      (cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).I (d + 1)
      (Fin.last _).1 (Fin.last _).2 hq
    change (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
      (hΩ d (Nat.lt_succ_self d))).toSuccession.stageMap (Fin.last _)
        ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d))).pullbackLiftLast
          (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange)) q) ∈
        (cur.I.pullback _ (X.inclusion (Ω d)).contMDiff).support at h1
    rw [BlowUpSequence.stageMap_last_pullbackLiftLast, IdealSheaf.support_pullback,
      Set.mem_preimage] at h1
    exact h1

variable {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)

/-- The composite blow-down of the value `resolveSeqOn bo T U hU` is an analytic isomorphism over
`U ∖ V(𝓘|_U)` ([Kol07, Theorem 35 (3)]; [Wlo09, Lemma 4.0.3]): the centres of the rounds lie over
the cosupport (`centersOver_resolveFrom` along the canonical chain),
`FiniteSuccession.isAnalyticIsoOver_stageMap`, and the deletion of the empty rounds transports the
predicate (`isAnalyticIsoOver_stageMap_last_eraseEmpty`). -/
theorem isAnalyticIsoOver_stageMap_last_resolveSeqOn (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    ((resolveSeqOn bo T U hU).toSuccession.stageMap (Fin.last _)).IsIsoOver
      ((restrictTriple T U).I.support)ᶜ := by
  unfold resolveSeqOn resolveSeqOnAlong
  refine BlowUpSequence.isAnalyticIsoOver_stageMap_last_eraseEmpty _ ?_
  refine FiniteSuccession.isAnalyticIsoOver_stageMap
    ((centersOver_resolveFrom bo _ _ _ _ _ _ _ _ _ _).mono fun q hq => ?_) (Fin.last _)
  rw [Set.mem_preimage] at hq
  change _ ∈ (T.I.pullback _ (M.inclusion
    ((canonicalResolveChain T U hU).W (canonicalResolveChain T U hU).D)).contMDiff).support at hq
  rw [IdealSheaf.support_pullback, Set.mem_preimage] at hq
  change _ ∈ (T.I.pullback _ (M.inclusion U).contMDiff).support
  rw [IdealSheaf.support_pullback, Set.mem_preimage]
  exact hq

end Hironaka.Manifold

end
