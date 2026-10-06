/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.Assembly
public import Hironaka.Resolution.Analytic.Wlo09.Rounds
public import Hironaka.Resolution.Analytic.Principalization.MonomialTransport
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.Functor.EraseEmptyOrder
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.Principalization.MonomialSeqMark
import Hironaka.Resolution.Analytic.Principalization.NormalCrossingsOfMonomial
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The total transform of `𝓘|_U` along the resolution rounds is a normal-crossings divisor

For the value `resolveSeqOn bo T U hU` of the resolution family on a relatively compact open `U`
(the rounds `d_U, …, 1` of the order-reduction functors `bo d`,
`Hironaka/Resolution/Analytic/Wlo09/Rounds.lean`), the pull-back of `𝓘|_U` along the composite
blow-down is at every point a monomial in the final total transform of the boundary `E|_U`, and the
final boundary is a simple normal crossing family, so the pull-back is the ideal sheaf of a
normal-crossings divisor: clause (2) of [Kol07, Theorem 35], clause (3) of [Wlo09, Theorem 2.0.3],
[BM97, Theorem 1.10], proved from the fields of the functors `bo` alone. Round by round the
pull-back is Kollár's explicit formula [Kol07, 72] at the round's own mark
(`Principalization/MonomialSeqMark.lean`), with residual the derived triple's ideal; the residual
closes at the last round's mark `1`.

* `isOfOrderGe_zero_resolveFrom`: the invariant of the recursion for clause (3′) of
  [Kol07, Definition 66]: every centre of the rounds has only normal crossings with the boundary
  sequence from `E` read along `ι` (order `≥ 0` for the pulled-back triple). The round's
  `isOfOrderGe` weakened to mark `0`, `isOfOrderGe_concat` at mark `0`, the boundary at the
  junction identified through `isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt` and
  `totalTransformSeqFrom_last_pullbackLiftLast`.
* `pullbackIsMonomialAtLast_resolveFrom`: the total transform of the current ideal along the
  rounds, read on `N` along `ι`, is a boundary monomial at every point of the last stage. The
  residual identity at mark `d + 1` on the pulled-back round list, whose residual is the derived
  ideal along the last-stage lift (`markedTransformSeq_last_pullbackLiftLast`), the induction
  hypothesis on the derived triple, `pullbackIsMonomialAtLast_of_isBoundaryMonomialAt` and
  `pullbackIsMonomialAtLast_concat`; at `d = 0` the ideal is the unit ideal and the list is empty.
* `isOfOrderGe_zero_resolveSeqOn`: clause (3′) for the value (the invariant at the canonical
  chain, the deletion of the empty rounds by `isOfOrderGe_eraseEmpty`); the final boundary's
  normal crossings, in the family form and in the ideal-sheaf form, are each one line from it.
* `pullbackIsMonomialAtLast_resolveSeqOn`: Kollár's formula [Kol07, 72] for the value.
* `resolveSeqOn_comap_last_isNormalCrossingsDivisor`: the normal-crossings divisor.
* `cosupport_comap_last_resolveSeqOn_subset_boundary`: the cosupport of the pull-back lies in the
  final boundary grown from `E|_U`.

The glued form on the whole manifold is `resolveFamExt_comap_map_isNormalCrossingsDivisor`
(`Hironaka/Resolution/Analytic/BM97/JacobianAssembly.lean`), by
`CompatibleFamily.isNormalCrossingsDivisor_comap_limitBlowDown`
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

/-- The invariant of the recursion `resolveFrom` for clause (3′) of [Kol07, Definition 66]: every
centre of the rounds from `d` on the current triple `cur`, read on `N` along `ι`, has only normal
crossings with the boundary sequence from `E`, stated as order `≥ 0` for the pulled-back triple,
which is clause (3′) alone. -/
theorem isOfOrderGe_zero_resolveFrom :
    ∀ (d : ℕ) {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
      (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
      (hord : ∀ x, cur.I.ord x ≤ (d : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅})
      (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
      (hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
      {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
      (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
      (hrange : Set.range ι ⊆ Ω 0),
      (resolveFrom bo d cur hord hfin Ω hΩ hΩsub ι hι hrange).toSuccession.IsOfOrderGe
        (cur.pullback ι hι).I 0 (cur.pullback ι hι).F.idealSheaf
  | 0, _, _, _, _, _, _, _, _, _, _, _ => FiniteSuccession.isOfOrderGe_nil _ _ 0
  | d + 1, X, cur, hord, hfin, Ω, hΩ, hΩsub, N, ι, hι, hrange => by
    have hround := AnalyticTriple.isOfOrderGe_pullback _ (d + 1)
      (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self d)))
      ((bo (d + 1)).isOfOrderGe cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d)))
      (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
      (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))
    have hround0 : ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).pullback
          (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι
            (range_subset_chain hΩsub hrange))).toSuccession.IsOfOrderGe
        (cur.pullback ι hι).I 0 (cur.pullback ι hι).F.idealSheaf :=
      FiniteSuccession.isOfOrderGe_zero_of_isOfOrderGe _ hround
    have hrest := isOfOrderGe_zero_resolveFrom d
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
    have hE : ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).pullback
          (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι
            (range_subset_chain hΩsub hrange))).toSuccession.boundarySeq
          (cur.pullback ι hι).F.idealSheaf (Fin.last _) =
        ((derivedTriple bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d))).pullback
          ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
            (hΩ d (Nat.lt_succ_self d))).pullbackLiftLast
            (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
            (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange)))
          (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)).F.idealSheaf := by
      have h1 := (FiniteSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt
        (cur.pullback ι hι).isSnc (Fin.last _) fun i _ => (hround0 i).1).2
      have h2 := BlowUpSequence.totalTransformSeqFrom_last_pullbackLiftLast
        (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d)))
        (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
        (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))
        (cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).F
      rw [h1]
      exact congrArg HypersurfaceFamily.idealSheaf h2
    refine BlowUpSequence.isOfOrderGe_concat _ _ hround0 ?_
    rw [hE]
    exact FiniteSuccession.isOfOrderGe_zero_of_isOfOrderGe _ hrest

/-- Kollár's formula for the pull-back [Kol07, 72] along the rounds: the total transform of the
current ideal along the rounds from `d`, read on `N` along `ι`, is at every point of the last stage
a boundary monomial in the final total transform of the boundary. Round by round: the residual
identity at the round's mark `d + 1` on the pulled-back round list, whose residual at the last
stage is the derived triple's ideal pulled back along the last-stage lift; the induction
hypothesis on the derived triple; the multiplicativity and the concatenation of
`PullbackIsMonomialAtLast`. At `d = 0` the ideal has order `0` everywhere, so it is the unit ideal,
and the list is empty. The residual closes at the last round's mark `1` (`(bo 1).ord_lt` through
`derivedTriple_ord_le`). -/
theorem pullbackIsMonomialAtLast_resolveFrom :
    ∀ (d : ℕ) {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
      (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
      (hord : ∀ x, cur.I.ord x ≤ (d : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅})
      (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
      (hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
      {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
      (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
      (hrange : Set.range ι ⊆ Ω 0),
      (resolveFrom bo d cur hord hfin Ω hΩ hΩsub ι hι hrange).PullbackIsMonomialAtLast
        (cur.pullback ι hι).F (cur.pullback ι hι).I
  | 0, X, cur, hord, _, _, _, _, N, ι, hι, _ => fun x => by
    refine ⟨∅, fun _ => 0, fun j hj => absurd hj (Finset.notMem_empty j), ?_⟩
    rw [Finset.prod_empty]
    have h0 : cur.I.stalkIdeal (ι x) = ⊤ := by
      have h := hord (ι x)
      rw [Nat.cast_zero, nonpos_iff_eq_zero, IdealSheaf.ord_eq_zero_iff, IdealSheaf.mem_support,
        not_not] at h
      exact h
    change (IdealSheaf.pullback (𝕜 := 𝕜) (E' := Fin n → 𝕜) (id : N → N) contMDiff_id
      (cur.pullback ι hι).I).stalkIdeal x = 1
    rw [IdealSheaf.pullback_id_eq_self, Ideal.one_eq_top]
    exact (IdealSheaf.stalkIdeal_pullback (⇑ι) ι.contMDiff cur.I x).trans
      (by rw [h0, Ideal.map_top])
  | d + 1, X, cur, hord, hfin, Ω, hΩ, hΩsub, N, ι, hι, hrange => by
    have hgeA := AnalyticTriple.isOfOrderGe_pullback _ (d + 1)
      (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self d)))
      ((bo (d + 1)).isOfOrderGe cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d)))
      (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
      (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))
    have hI : ((cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).pullback
        (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
        (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))).I =
        (cur.pullback ι hι).I := by
      change (cur.I.pullback _ (X.inclusion (Ω d)).contMDiff).pullback _ (AnalyticMap.corestrict ι
          (Ω d) (range_subset_chain hΩsub hrange)).contMDiff = cur.I.pullback ι
            ι.contMDiff
      rw [IdealSheaf.pullback_comp]
      exact congrArg (fun f : AnalyticMap _ _ => cur.I.pullback f f.contMDiff)
          (ContMDiffMap.ext fun _ => rfl)
    have eF : ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).pullback
          (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι
            (range_subset_chain hΩsub hrange))).toSuccession.totalTransformSeqFrom
          (cur.pullback ι hι).F (Fin.last _) =
        ((derivedTriple bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d))).pullback
          ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
            (hΩ d (Nat.lt_succ_self d))).pullbackLiftLast
            (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
            (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange)))
          (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)).F :=
      BlowUpSequence.totalTransformSeqFrom_last_pullbackLiftLast
        (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d)))
        (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
        (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))
        (cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).F
    have eM : ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).pullback
          (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι
            (range_subset_chain hΩsub hrange))).toSuccession.markedTransformSeq
          ((cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).pullback
            (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
            (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))).I
          (d + 1) (Fin.last _) =
        ((derivedTriple bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d))).pullback
          ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
            (hΩ d (Nat.lt_succ_self d))).pullbackLiftLast
            (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
            (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange)))
          (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)).I :=
      BlowUpSequence.markedTransformSeq_last_pullbackLiftLast
        (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d)))
        (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
        (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))
        (cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).I
        (cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).F.idealSheaf
        (d + 1)
        ((bo (d + 1)).isOfOrderGe cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d)))
    have hmono : ∀ p, (((derivedTriple bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).pullback
          ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
            (hΩ d (Nat.lt_succ_self d))).pullbackLiftLast
            (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
            (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange)))
          (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)).F).IsBoundaryMonomialAt
        (Manifold.IdealSheaf.pullback _ (((roundList bo cur (boClass_succ_of_ord_le cur hord hfin)
            (Ω d)
            (hΩ d (Nat.lt_succ_self d))).pullback
              (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
              (isLocalDiffeomorph_corestrict ι (Ω d) hι
                (range_subset_chain hΩsub hrange))).toSuccession.stageMap (Fin.last _)).contMDiff
          (cur.pullback ι hι).I)
        ((derivedTriple bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d))).pullback
          ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
            (hΩ d (Nat.lt_succ_self d))).pullbackLiftLast
            (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
            (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange)))
          (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)).I p := fun p => by
      have h := FiniteSuccession.isBoundaryMonomialAt_stageMapAux_of_isOfOrderGe _
        ((cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).pullback
          (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))).isSnc
        hgeA _ (Nat.lt_succ_self _) p
      change (((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).pullback
          (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι
            (range_subset_chain hΩsub hrange))).toSuccession.totalTransformSeqFrom
          (cur.pullback ι hι).F (Fin.last _)).IsBoundaryMonomialAt
        (Manifold.IdealSheaf.pullback _ (((roundList bo cur (boClass_succ_of_ord_le cur hord hfin)
            (Ω d)
            (hΩ d (Nat.lt_succ_self d))).pullback
              (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
              (isLocalDiffeomorph_corestrict ι (Ω d) hι
                (range_subset_chain hΩsub hrange))).toSuccession.stageMap (Fin.last _)).contMDiff
          ((cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).pullback
            (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
            (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))).I)
        (((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d))).pullback
            (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
            (isLocalDiffeomorph_corestrict ι (Ω d) hι
              (range_subset_chain hΩsub hrange))).toSuccession.markedTransformSeq
          ((cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).pullback
            (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
            (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))).I
          (d + 1) (Fin.last _)) p at h
      rw [eF, eM, hI] at h
      exact h
    have hrest := pullbackIsMonomialAtLast_resolveFrom d
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
    have h3rest := isOfOrderGe_zero_resolveFrom bo d
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
    refine BlowUpSequence.pullbackIsMonomialAtLast_concat _ _ _ _ ?_
    rw [eF]
    exact BlowUpSequence.pullbackIsMonomialAtLast_of_isBoundaryMonomialAt _
      (AnalyticTriple.isSnc _) (fun i => (h3rest i).1) hmono hrest

variable {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)

/-- Clause (3′) of [Kol07, Definition 66] for the value `resolveSeqOn bo T U hU`: it is of order `≥
0` for `(𝓘|_U, 0, red E|_U)`, the invariant at the canonical chain
(`AnalyticTriple.pullback_inclusion_restrictLE`) and the deletion of the empty rounds
(`isOfOrderGe_eraseEmpty`, [Kol07, 34.1]). The final boundary's normal crossings, in the family form
`IsSnc` of the final total transform and in the ideal-sheaf form `HasOnlyNormalCrossings` of the
boundary sequence (clause (iv) of [Hir64, Main Theorem II′(N), p. 156]), are each one line from it
(`isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt`,
`hasOnlyNormalCrossings_idealSheaf`). -/
theorem isOfOrderGe_zero_resolveSeqOn (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (resolveSeqOn bo T U hU).toSuccession.IsOfOrderGe (restrictTriple T U).I 0
      (restrictTriple T U).F.idealSheaf := by
  unfold resolveSeqOn resolveSeqOnAlong
  refine BlowUpSequence.isOfOrderGe_eraseEmpty _ _ 0 (restrictTriple T U).isSnc ?_
  have h : (restrictTriple T
      ((canonicalResolveChain T U hU).W (canonicalResolveChain T U hU).D)).pullback
      (M.restrictLE (canonicalResolveChain T U hU).le_outerOpen)
      (isLocalDiffeomorph_restrictLE (canonicalResolveChain T U hU).le_outerOpen) =
      restrictTriple T U :=
    T.pullback_inclusion_restrictLE (canonicalResolveChain T U hU).le_outerOpen
  rw [← h]
  exact isOfOrderGe_zero_resolveFrom bo _ _ _ _ _ _ _ _ _ _

/-- Kollár's formula [Kol07, 72] for the value: the pull-back of `𝓘|_U` along the composite
blow-down of `resolveSeqOn bo T U hU` is at every point of the last stage a boundary monomial in the
final total transform of `E|_U` (`pullbackIsMonomialAtLast_resolveFrom` at the canonical chain, the
deletion of the empty rounds by `pullbackIsMonomialAtLast_eraseEmpty`). -/
theorem pullbackIsMonomialAtLast_resolveSeqOn (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (resolveSeqOn bo T U hU).PullbackIsMonomialAtLast (restrictTriple T U).F
      (restrictTriple T U).I := by
  unfold resolveSeqOn resolveSeqOnAlong
  refine BlowUpSequence.pullbackIsMonomialAtLast_eraseEmpty _
    (fun j => ((restrictTriple T U).isSnc.1 j).isClosed) _ ?_
  have h : (restrictTriple T
      ((canonicalResolveChain T U hU).W (canonicalResolveChain T U hU).D)).pullback
      (M.restrictLE (canonicalResolveChain T U hU).le_outerOpen)
      (isLocalDiffeomorph_restrictLE (canonicalResolveChain T U hU).le_outerOpen) =
      restrictTriple T U :=
    T.pullback_inclusion_restrictLE (canonicalResolveChain T U hU).le_outerOpen
  rw [← h]
  exact pullbackIsMonomialAtLast_resolveFrom bo _ _ _ _ _ _ _ _ _ _

/-- **The pull-back of `𝓘|_U` along the composite blow-down of `resolveSeqOn bo T U hU` is the ideal
sheaf of a normal-crossings divisor** ([Kol07, Theorem 35 (2)]; [Wlo09, Theorem 2.0.3 (3)];
[BM97, Theorem 1.10]): a boundary monomial at every point (`pullbackIsMonomialAtLast_resolveSeqOn`)
in the final total transform of `E|_U`, which is a simple normal crossing family (clause (3′) of
the value, at every step), hence `isNormalCrossingsDivisor_of_forall_monomial`. -/
theorem resolveSeqOn_comap_last_isNormalCrossingsDivisor (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    AnalyticManifold.IdealSheaf.IsNormalCrossingsDivisor ((restrictTriple T U).I.pullback _
      ((resolveSeqOn bo T U hU).toSuccession.stageMap (Fin.last _)).contMDiff) :=
  isNormalCrossingsDivisor_of_forall_monomial _
    (FiniteSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt
      (restrictTriple T U).isSnc (Fin.last _)
      fun i _ => (isOfOrderGe_zero_resolveSeqOn bo T U hU i).1).1
    _ (pullbackIsMonomialAtLast_resolveSeqOn bo T U hU)

/-- The cosupport of the pull-back of `𝓘|_U` along the composite blow-down of `resolveSeqOn bo T U
hU` lies in the final boundary grown from `E|_U`, `boundarySeq (E|_U) (Fin.last _)`: a point of the
cosupport lies on a member of the final total transform through which the monomial of
`pullbackIsMonomialAtLast_resolveSeqOn` has a factor (an empty product is the unit ideal). When `E ≠
∅` this is weaker than Włodarczyk's clause that the total transform is supported on the exceptional
divisors ([Wlo09, Theorem 2.0.3 (3)]); the two coincide when `E = ∅`, the case of the
principalization theorem with the Jacobian clause, whose boundary is empty. The
exceptional-divisor form would need the boundary monomial in the exceptional sub-family, that
is, the descent of clause (3′) to the empty boundary along the sequence; it is not proved in this
library. Not used elsewhere in the library. -/
theorem cosupport_comap_last_resolveSeqOn_subset_boundary (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    ((restrictTriple T U).I.pullback _ ((resolveSeqOn bo T U hU).toSuccession.stageMap (Fin.last
        _)).contMDiff).support ⊆
      ((resolveSeqOn bo T U hU).toSuccession.boundarySeq (restrictTriple T U).F.idealSheaf
        (Fin.last _)).support := by
  classical
  intro x hx
  obtain ⟨s, α, hs, hx'⟩ := pullbackIsMonomialAtLast_resolveSeqOn bo T U hU x
  have hE := FiniteSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt
    (restrictTriple T U).isSnc (Fin.last _)
    fun i _ => (isOfOrderGe_zero_resolveSeqOn bo T U hU i).1
  rw [hE.2, hE.1.cosupport_idealSheaf]
  by_contra hxs
  rw [IdealSheaf.mem_support] at hx
  apply hx
  rw [hx']
  have hs0 : s = ∅ := by
    by_contra hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact hxs (Set.mem_iUnion.mpr ⟨j, hs j hj⟩)
  rw [hs0, Finset.prod_empty]
  exact Ideal.one_eq_top

end Hironaka.Manifold

end
