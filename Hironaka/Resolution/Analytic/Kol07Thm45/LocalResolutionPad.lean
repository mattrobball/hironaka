/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
public import Hironaka.Resolution.Analytic.Kol07Thm45.StrictSubspacePushforward
public import Hironaka.Manifold.BlowUp.Transform.GermIso
public import Hironaka.Manifold.Snc.Proper
public import Hironaka.Resolution.Analytic.Kol07Thm45.ClosedSubspaceHom
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.AnalyticSpace.Manifold.Chart
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.ToSuccessionPushforward
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.GoingUp.StageIso
import Hironaka.Resolution.Analytic.Kol07Thm45.DimensionCast
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Hom
import Hironaka.Resolution.Analytic.Kol07Thm45.PushforwardBoundaryTrace
import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Hironaka.Resolution.Analytic.Restrict.BoundaryTrace
import Hironaka.Resolution.Analytic.Restrict.DiffeomorphTransport
import Hironaka.Resolution.Analytic.Restrict.StrictSubspaceSeqTransport
import Hironaka.Resolution.Analytic.TransportBase
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The padded local resolution is the local resolution of the slice preimage, over the piece

Kollár's weak commutation with closed embeddings, `j^* B(X, I_X, E) = B(Y, I_Y, E|_Y)`
[Kol07, 34.4], at the padding `E.padAlong σ` of a piece embedding: the field `bed.closedEmbedding`
of `BEDanFamStar` (the commutation with closed embeddings of ambient manifolds,
[Wlo09, Theorem 2.0.2(4)]) reads the padded sequence over a relatively compact open `U` of the
padded ambient as the restricted push-forward of the sequence of the coordinate slice
`S = {z_j = 0, j ∉ range σ}` over `S ∩ U`; the slice is the piece through the zero extension
`padExt` (the diffeomorphism `padExtDiffeomorph`, `PadSliceDiffeomorph.lean`), and the dimension
cast `BEDanFamStar.exists_diffeomorph_last_of_cast` (`DimensionCast.lean`, from the commutation
with local isomorphisms) carries the piece's own sequence over `s⁻¹ U` to the slice sequence.
`StrictSubspacePushforward.lean` identifies the final strict transform of the padded ideal,
restricted to the carried slice, with the final strict transform of the slice ideal
[Kol07, Definition 30.3], so the morphisms of closed subspaces along the last inclusion and along
the diffeomorphisms give the isomorphism of closed subspaces `Ỹ_E(s⁻¹ U) ≅ Ỹ_P(U)`, and the
squares of the composites its compatibility with the maps to the piece. This module provides:

* `AnalyticManifold.FiniteSuccession.stageMap_pushforwardIncl` (the inclusions `S_i ↪ X_i`
  commute with the composites) and `pushforwardIncl_eq_incl`;
* `PieceEmbedding.emb_comp_embInv_padAlong` (`E.emb ∘ P.emb⁻¹ = padSliceHom`);
* the core `PieceEmbedding.exists_closedSubmanifold_localResolution_padAlong`: a closed
  submanifold `S_r` of the padded last stage with `𝓘_{S_r} ≤ Ỹ_P`, a diffeomorphism
  `G : Ỹ_E`'s stage `≅ S_r` with `Ỹ_E = (Ỹ_P)|_{S_r}` transported along `G`, and the square of the
  composites over the zero extension;
* `PieceEmbedding.exists_isIso_localResolution_padAlong`: the isomorphism over the piece.

## The general forms

`exists_closedSubmanifold_last_pushforwardRestrict_boundary` and
`localResolutionToPiece_comp_homOfPullbackEq_padAlong` are the general forms of the core and of
the isomorphism's body; the statements above are their corollaries. The general forms expose the
last-stage boundary's trace identity along `j_r ∘ G`
(`exists_orderIso_totalTransformSeq_pushforward`, `PushforwardBoundaryTrace.lean`) under the
normal-crossings clause (3′) of [Kol07, Definition 66], and the compatibility
`Π_P ∘ (m_I ∘ m_G) = Π_E` for any carried slice; the padding identity of a datum at the coproduct
(`CoproductPadIdentity.lean`) uses the first.

Not in the sources beyond the commutation with closed embeddings; bookkeeping.
-/

public section

noncomputable section

open TopologicalSpace Set AnalyticManifold CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff Topology

universe u

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}
  (hS : IsClosedSubmanifold ψ S s) (T : FiniteSuccession hS.toAnalyticManifold)

/-- The inclusions `j_i : S_i ↪ X_i` commute with the composites `σ^i`, ℕ-indexed
([Kol07, Definition 30.3]): by induction on the stage with `pushforwardIncl_map`. Internal. -/
theorem stageMapAux_pushforwardIncl : ∀ (i : ℕ) (hi : i < T.length + 1) (p : T.stage ⟨i, hi⟩),
    (T.pushforward hS).stageMapAux i hi (T.pushforwardIncl hS ⟨i, hi⟩ p) =
      hS.inclusionMap (T.stageMapAux i hi p)
  | 0, _, _ => rfl
  | i + 1, hi, p => by
    have h := T.pushforwardIncl_map hS ⟨i, Nat.lt_of_succ_lt_succ hi⟩ p
    exact (congrArg ((T.pushforward hS).stageMapAux i (Nat.lt_of_succ_lt hi)) h.symm).trans
      (stageMapAux_pushforwardIncl i (Nat.lt_of_succ_lt hi)
        (T.map ⟨i, Nat.lt_of_succ_lt_succ hi⟩ p))

/-- The inclusions `j_i : S_i ↪ X_i` commute with the composites `σ^i : X_i → X_0`,
`σ^i ∘ j_i = j_0 ∘ σ^i_S`. -/
theorem stageMap_pushforwardIncl (i : Fin (T.length + 1)) (p : T.stage i) :
    (T.pushforward hS).stageMap i (T.pushforwardIncl hS i p) = hS.inclusionMap (T.stageMap i p) :=
  T.stageMapAux_pushforwardIncl hS i.1 i.2 p

/-- **The stage `T_i` is diffeomorphic to the carried slice `S_i`** (the identification
`e_i : T_i ≃ S_i` carried by the recursion of `pushforwardAux`), the inclusion `j_i` being the
inclusion of `S_i` after the diffeomorphism — the stage datum's `iso` read on the range of `j_i`
(`range_incl`, `diffeomorphOfEq`), case by case on the index. -/
theorem exists_diffeomorph_range_pushforwardIncl (i : Fin (T.length + 1)) :
    ∃ iso : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) (T.stage i)
        (T.isClosedSubmanifold_range_pushforwardIncl hS i).toAnalyticManifold ω,
      ∀ q, (T.isClosedSubmanifold_range_pushforwardIncl hS i).inclusionMap (iso q) =
        T.pushforwardIncl hS i q := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · exact ⟨(T.pushforwardAux hS 0 hi).iso.trans
      ((T.pushforwardAux hS 0 hi).isClosedSubmanifold.diffeomorphOfEq _
        (T.pushforwardAux hS 0 hi).range_incl.symm),
      fun q => IsClosedSubmanifold.diffeomorphOfEq_apply_val _ _ _ _⟩
  · exact ⟨(T.pushforwardAux hS (i + 1) hi).iso.trans
      ((T.pushforwardAux hS (i + 1) hi).isClosedSubmanifold.diffeomorphOfEq _
        (T.pushforwardAux hS (i + 1) hi).range_incl.symm),
      fun q => IsClosedSubmanifold.diffeomorphOfEq_apply_val _ _ _ _⟩

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold Manifold
open AnalyticSpace.KLocallyRingedSpace

variable {𝕜 : Type} [RCLike 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}
  (hS : IsClosedSubmanifold ψ S s) (U : Opens M)
  (L_S : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
    ((hS.toAnalyticManifold).restrict (hS.preimageOpens U)))
  (I : IdealSheaf M)

local macro "𝐞" : term => `(IsClosedSubmanifold.restrictBundleDiffeomorphOf hS U
  (IsClosedSubmanifold.preimageOpens hS U) rfl)
local macro "𝐓" : term => `(BlowUpSequence.toSuccession (BlowUpSequence.pullback L_S
  ⟨⇑(Diffeomorph.symm 𝐞), Diffeomorph.contMDiff (Diffeomorph.symm 𝐞)⟩
  (Diffeomorph.isLocalDiffeomorph (Diffeomorph.symm 𝐞))))
local macro "𝐉" : term => `(AnalyticManifold.IdealSheaf.restrict (Manifold.IdealSheaf.pullback
  (⇑(IsClosedSubmanifold.inclusionMap hS))
  (ContMDiffMap.contMDiff (IsClosedSubmanifold.inclusionMap hS)) I)
  (IsClosedSubmanifold.preimageOpens hS U))

/-- The GENERAL FORM of `exists_closedSubmanifold_last_pushforwardRestrict`, of which that theorem
is the corollary ([Kol07, Definitions 30.2–30.3]): its three clauses, and, UNDER clause (3′) of
`L_P` (the centres have only normal crossings with the boundary at every stage): the last-stage
boundary of `L_P` has simple normal crossings with the carried slice `S_r` properly, and an order
isomorphism `o` of the last-stage boundary index types with `(j_r ∘ G)⁻¹(H^P_{r, o j}) = H^S_{r, j}`
— `exists_orderIso_totalTransformSeq_pushforward` on the transported list `T`, read back on `L_S`
along the lift of the bundling bridge (`totalTransformSeqFrom_last_pullbackLiftLast`). -/
theorem exists_closedSubmanifold_last_pushforwardRestrict_boundary (hNE : L_S.NoEmptyCenters)
    (hSI : hS.idealSheaf ≤ I) (L_P : BlowUpSequence ψ (M.restrict U))
    (hL : L_P = pushforwardRestrict hS U L_S) :
    ∃ (S_r : Set (L_P.toSuccession.stage (Fin.last _))) (hS_r : IsClosedSubmanifold ψ S_r s)
      (G : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜)
        (L_S.toSuccession.stage (Fin.last _)) hS_r.toAnalyticManifold ω),
      hS_r.idealSheaf ≤
        L_P.toSuccession.strictTransformSubspaceSeq (I.restrict U) (Fin.last _) ∧
      L_S.toSuccession.strictTransformSubspaceSeq
          (IdealSheaf.restrict
            (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (hS.preimageOpens U))
          (Fin.last _) =
        (L_P.toSuccession.strictTransformSubspaceSeq (I.restrict U) (Fin.last _)).pullback
          (⇑hS_r.inclusionMap ∘ ⇑G) (hS_r.inclusionMap.contMDiff.comp G.contMDiff) ∧
      (∀ q, hS.inclusionMap ((hS.toAnalyticManifold).inclusion (hS.preimageOpens U)
          (L_S.toSuccession.composite q)) =
        M.inclusion U (L_P.toSuccession.composite (hS_r.inclusionMap (G q)))) ∧
      ((∀ i : Fin L_P.toSuccession.length, (L_P.toSuccession.boundarySeq (⊤)
          i.castSucc).HasOnlyNormalCrossingsWith (L_P.toSuccession.center i)) →
        (L_P.toSuccession.totalTransformSeq (Fin.last _)).HasSncWithProper ψ S_r s ∧
        ∃ o : (L_S.toSuccession.totalTransformSeq (Fin.last _)).ι ≃o
            (L_P.toSuccession.totalTransformSeq (Fin.last _)).ι,
          ∀ j, (⇑hS_r.inclusionMap ∘ ⇑G) ⁻¹'
              (L_P.toSuccession.totalTransformSeq (Fin.last _)).hyp (o j) =
            (L_S.toSuccession.totalTransformSeq (Fin.last _)).hyp j) := by
  subst hL
  have hNE' : (L_S.pullback ⟨(𝐞).symm, (𝐞).symm.contMDiff⟩
      (𝐞).symm.isLocalDiffeomorph).NoEmptyCenters :=
    noEmptyCenters_pullback_of_surjective _ _ _ (𝐞).symm.surjective hNE
  -- the restricted push-forward is the push-forward of the list transported along the bridge
  rw [show pushforwardRestrict hS U L_S = _ from
    pushforwardRestrictOf_eq hS U (hS.preimageOpens U) rfl L_S,
    toSuccession_pushforward (hS.restrictOpen U) _ hNE']
  -- the restricted ideal of `S ∩ U` lies in `I|U`
  have hI : (hS.restrictOpen U).idealSheaf ≤ I.restrict U := by
    have h1 : (hS.restrictOpen U).idealSheaf =
        hS.idealSheaf.pullback _ (M.inclusion U).contMDiff :=
      (comap_idealSheaf_of_isLocalDiffeomorph (ψ := ψ) (M.inclusion U)
        (isLocalDiffeomorph_inclusion M U) hS).symm
    rw [h1]
    exact IdealSheaf.le_def.mpr fun x => by
      dsimp only
          [IdealSheaf.restrict]
      rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback]
      exact Ideal.map_mono (IdealSheaf.le_def.mp hSI _)
  -- the containment and the restriction identity of `StrictSubspacePushforward.lean` at the last
  -- stage
  have h1a :=
    FiniteSuccession.idealSheaf_range_pushforwardIncl_le_strictTransformSubspaceSeq
      (hS.restrictOpen U) 𝐓 (I.restrict U) hI (Fin.last _)
  have h1b := FiniteSuccession.strictTransformSubspaceSeq_pushforward_pullback_incl
    (hS.restrictOpen U) 𝐓 (I.restrict U) hI (Fin.last _)
  -- the transported ideal and the lift of the bridge
  have hJ' : (I.restrict U).pullback ⇑(hS.restrictOpen U).inclusionMap
      (hS.restrictOpen U).inclusionMap.contMDiff =
      𝐉.pullback (𝐞).symm (𝐞).symm.contMDiff := by
    dsimp only [IdealSheaf.restrict]
    rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr _ _ _ (funext fun _ => rfl)
  have hpb : (𝐓).strictTransformSubspaceSeq ((I.restrict U).pullback
        ⇑(hS.restrictOpen U).inclusionMap (hS.restrictOpen U).inclusionMap.contMDiff) (Fin.last _) =
      (L_S.toSuccession.strictTransformSubspaceSeq 𝐉 (Fin.last _)).pullback
        ⇑(L_S.pullbackLiftLastDiffeomorph (𝐞).symm)
        (L_S.pullbackLiftLastDiffeomorph (𝐞).symm).contMDiff := by
    erw [hJ', strictTransformSubspaceSeq_last_pullbackLiftLast' L_S
      ⟨(𝐞).symm, (𝐞).symm.contMDiff⟩ (𝐞).symm.isLocalDiffeomorph 𝐉]
    rfl
  -- the carried slice at the last stage and its identification with the last stage of `T`
  have hex := FiniteSuccession.exists_diffeomorph_range_pushforwardIncl
    (hS.restrictOpen U) 𝐓 (Fin.last _)
  have hiso' := Classical.choose_spec hex
  have hfun : (⇑(FiniteSuccession.isClosedSubmanifold_range_pushforwardIncl
        (hS.restrictOpen U) 𝐓 (Fin.last _)).inclusionMap ∘
        ⇑((L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm.trans (Classical.choose hex))) =
      ⇑((𝐓).pushforwardIncl (hS.restrictOpen U) (Fin.last _)) ∘
        ⇑(L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm :=
    funext fun q => hiso' ((L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm q)
  refine ⟨_, FiniteSuccession.isClosedSubmanifold_range_pushforwardIncl
      (hS.restrictOpen U) 𝐓 (Fin.last _),
    (L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm.trans (Classical.choose hex), h1a, ?_, ?_,
    ?_⟩
  · -- the final strict transforms correspond: through `T`'s last stage along the lift of the bridge
    calc L_S.toSuccession.strictTransformSubspaceSeq 𝐉 (Fin.last _)
        = ((L_S.toSuccession.strictTransformSubspaceSeq 𝐉 (Fin.last _)).pullback
              ⇑(L_S.pullbackLiftLastDiffeomorph (𝐞).symm)
              (L_S.pullbackLiftLastDiffeomorph (𝐞).symm).contMDiff).pullback
            ⇑(L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm
            (L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm.contMDiff :=
          (IdealSheaf.pullback_pullback_symm (L_S.pullbackLiftLastDiffeomorph (𝐞).symm) _).symm
      _ = ((𝐓).strictTransformSubspaceSeq ((I.restrict U).pullback
              ⇑(hS.restrictOpen U).inclusionMap (hS.restrictOpen U).inclusionMap.contMDiff)
              (Fin.last _)).pullback
            ⇑(L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm
            (L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm.contMDiff :=
          congrArg (IdealSheaf.pullback ⇑(L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm
            (L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm.contMDiff) hpb.symm
      _ = ((((𝐓).pushforward (hS.restrictOpen U)).strictTransformSubspaceSeq (I.restrict U)
              (Fin.last _)).pullback ⇑((𝐓).pushforwardIncl (hS.restrictOpen U) (Fin.last _))
              ((𝐓).pushforwardIncl (hS.restrictOpen U) (Fin.last _)).contMDiff).pullback
            ⇑(L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm
            (L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm.contMDiff :=
          congrArg (IdealSheaf.pullback ⇑(L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm
            (L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm.contMDiff) h1b.symm
      _ = (((𝐓).pushforward (hS.restrictOpen U)).strictTransformSubspaceSeq (I.restrict U)
              (Fin.last _)).pullback
            (⇑((𝐓).pushforwardIncl (hS.restrictOpen U) (Fin.last _)) ∘
              ⇑(L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm)
            (((𝐓).pushforwardIncl (hS.restrictOpen U) (Fin.last _)).contMDiff.comp
              (L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm.contMDiff) :=
          IdealSheaf.pullback_pullback _ _ _ _ _
      _ = _ := IdealSheaf.pullback_congr _ _ _ hfun.symm
  · -- the square of the composites
    intro q
    have h2 : ((𝐓).pushforward (hS.restrictOpen U)).composite
        ((𝐓).pushforwardIncl (hS.restrictOpen U) (Fin.last _)
          ((L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm q)) =
        (hS.restrictOpen U).inclusionMap
          ((𝐓).composite ((L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm q)) :=
      FiniteSuccession.stageMap_pushforwardIncl (hS.restrictOpen U) 𝐓 (Fin.last _) _
    have h3 : (𝐓).composite ((L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm q) =
        (𝐞) (L_S.toSuccession.composite q) := by
      have h := stageMap_last_pullbackLiftLast L_S ⟨(𝐞).symm, (𝐞).symm.contMDiff⟩
        (𝐞).symm.isLocalDiffeomorph ((L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm q)
      have hx : L_S.pullbackLiftLast ⟨(𝐞).symm, (𝐞).symm.contMDiff⟩ (𝐞).symm.isLocalDiffeomorph
          ((L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm q) = q :=
        (L_S.pullbackLiftLastDiffeomorph (𝐞).symm).apply_symm_apply q
      rw [hx] at h
      exact ((congrArg (𝐞) h).trans ((𝐞).apply_symm_apply _)).symm
    change hS.inclusionMap ((hS.toAnalyticManifold).inclusion (hS.preimageOpens U)
        (L_S.toSuccession.composite q)) =
      M.inclusion U (((𝐓).pushforward (hS.restrictOpen U)).composite
        ((FiniteSuccession.isClosedSubmanifold_range_pushforwardIncl
          (hS.restrictOpen U) 𝐓 (Fin.last _)).inclusionMap
          (Classical.choose hex ((L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm q))))
    rw [hiso', h2, h3]
    rfl
  · -- the boundary clauses: the boundary of the push-forward has snc with the
    -- carried slice properly; the trace identity
    -- `exists_orderIso_totalTransformSeq_pushforward`
    -- on `T`, read back on `L_S` along the lift of the bridge
    -- (`totalTransformSeqFrom_last_pullbackLiftLast` at the empty start family)
    intro h3
    refine ⟨?_, ?_⟩
    · have h := ((𝐓).pushforward
          (hS.restrictOpen U)).hasSncWithProper_totalTransformSeq_strictTransformSeq_of_forall_lt
        (hS.restrictOpen U) ((𝐓).centersIn_pushforward (hS.restrictOpen U)) (Fin.last _)
        fun i _ => h3 i
      have e := (𝐓).range_pushforwardIncl (hS.restrictOpen U)
        (Fin.last ((𝐓).pushforward (hS.restrictOpen U)).length)
      exact e ▸ h
    · -- the last stage of the push-forward spelled through `T`'s length (definitionally the same
      -- `Fin.last`), so that every rewrite below is syntactic
      change ∃ o : (L_S.toSuccession.totalTransformSeq (Fin.last _)).ι ≃o
          (((𝐓).pushforward (hS.restrictOpen U)).totalTransformSeq (Fin.last (𝐓).length)).ι,
        ∀ j, (⇑(FiniteSuccession.isClosedSubmanifold_range_pushforwardIncl
              (hS.restrictOpen U) 𝐓 (Fin.last _)).inclusionMap ∘
            ⇑((L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm.trans (Classical.choose hex))) ⁻¹'
            (((𝐓).pushforward (hS.restrictOpen U)).totalTransformSeq
              (Fin.last (𝐓).length)).hyp (o j) =
          (L_S.toSuccession.totalTransformSeq (Fin.last _)).hyp j
      have h3' : ∀ i : Fin (𝐓).length,
          (((𝐓).pushforward (hS.restrictOpen U)).boundarySeq (⊤)
            i.castSucc).HasOnlyNormalCrossingsWith
            (((𝐓).pushforward (hS.restrictOpen U)).center i) :=
        fun i => h3 i
      have hh := FiniteSuccession.exists_orderIso_totalTransformSeq_pushforward
        (hS.restrictOpen U) (𝐓) h3' (Fin.last _)
      let o₁ := hh.choose
      have ho₁ := hh.choose_spec
      have hT : (𝐓).totalTransformSeq (Fin.last _) =
          (L_S.toSuccession.totalTransformSeq (Fin.last _)).comap
            ⇑(L_S.pullbackLiftLast ⟨(𝐞).symm, (𝐞).symm.contMDiff⟩
              (𝐞).symm.isLocalDiffeomorph) := by
        have h := totalTransformSeqFrom_last_pullbackLiftLast L_S
          ⟨(𝐞).symm, (𝐞).symm.contMDiff⟩ (𝐞).symm.isLocalDiffeomorph (HypersurfaceFamily.empty _)
        rwa [HypersurfaceFamily.empty_comap] at h
      have key : ∀ (G' : HypersurfaceFamily ((𝐓).stage (Fin.last _)))
          (hG : (𝐓).totalTransformSeq (Fin.last _) = G'),
          ∃ o : ((𝐓).totalTransformSeq (Fin.last _)).ι ≃o G'.ι,
            ∀ j, ((𝐓).totalTransformSeq (Fin.last _)).hyp j = G'.hyp (o j) := by
        intro G' hG
        subst hG
        exact ⟨OrderIso.refl _, fun _ => rfl⟩
      let o₂ := (key _ hT).choose
      have ho₂ := (key _ hT).choose_spec
      have hid : ∀ X : Set (L_S.toSuccession.stage (Fin.last _)),
          ⇑(L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm ⁻¹'
            (⇑(L_S.pullbackLiftLast ⟨(𝐞).symm, (𝐞).symm.contMDiff⟩
              (𝐞).symm.isLocalDiffeomorph) ⁻¹' X) = X := fun X => by
        ext q
        have hx : L_S.pullbackLiftLast ⟨(𝐞).symm, (𝐞).symm.contMDiff⟩
            (𝐞).symm.isLocalDiffeomorph ((L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm q) = q :=
          (L_S.pullbackLiftLastDiffeomorph (𝐞).symm).apply_symm_apply q
        change L_S.pullbackLiftLast ⟨(𝐞).symm, (𝐞).symm.contMDiff⟩ (𝐞).symm.isLocalDiffeomorph
          ((L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm q) ∈ X ↔ q ∈ X
        rw [hx]
      refine ⟨o₂.symm.trans o₁, fun j => ?_⟩
      -- the pointwise identity, in term mode (no rewriting inside the dependent types)
      have e1 := congrArg (fun f : _ → _ => f ⁻¹'
        (((𝐓).pushforward (hS.restrictOpen U)).totalTransformSeq
          (Fin.last (𝐓).length)).hyp ((o₂.symm.trans o₁) j)) hfun
      refine e1.trans ?_
      refine (Set.preimage_comp (f := ⇑(L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm)
        (g := ⇑((𝐓).pushforwardIncl (hS.restrictOpen U) (Fin.last _)))).trans ?_
      refine (congrArg (fun X => ⇑(L_S.pullbackLiftLastDiffeomorph (𝐞).symm).symm ⁻¹' X)
        ((ho₁ (o₂.symm j)).trans ((ho₂ (o₂.symm j)).trans
          (congrArg _ (o₂.apply_symm_apply j))))).trans ?_
      exact hid _

/-- **The final strict transform along a restricted push-forward, read on the carried slice**
([Kol07, Definition 30.3]): for a list `L_S` on the trace `S ∩ U` of the bundled `S` (no empty
centres) and a list `L_P` on `U` equal to its restricted push-forward, the final stage of `L_P`
carries a closed submanifold `S_r` whose ideal lies in the final strict transform `Ỹ_P` of `I|_U`, a
diffeomorphism `G` of the final stage of `L_S` onto `S_r` with `Ỹ_S = G^*(Ỹ_P|_{S_r})` for the final
strict transform `Ỹ_S` of `(I|_S)|_{S ∩ U}` along `L_S`, and the square of the composites. The
argument: `pushforwardRestrictOf_eq` and `toSuccession_pushforward` (the family value has no empty
centres) put `L_P`'s succession in the form `T.pushforward (S ∩ U)`; the containment and the
restriction identity of `StrictSubspacePushforward.lean` at the last stage; the bundling bridge's
lift (`pullbackLiftLastDiffeomorph`, `strictTransformSubspaceSeq_last_pullbackLiftLast'`) and the
stage datum's `iso` identify the last stages. -/
theorem exists_closedSubmanifold_last_pushforwardRestrict (hNE : L_S.NoEmptyCenters)
    (hSI : hS.idealSheaf ≤ I) (L_P : BlowUpSequence ψ (M.restrict U))
    (hL : L_P = pushforwardRestrict hS U L_S) :
    ∃ (S_r : Set (L_P.toSuccession.stage (Fin.last _))) (hS_r : IsClosedSubmanifold ψ S_r s)
      (G : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜)
        (L_S.toSuccession.stage (Fin.last _)) hS_r.toAnalyticManifold ω),
      hS_r.idealSheaf ≤
        L_P.toSuccession.strictTransformSubspaceSeq (I.restrict U) (Fin.last _) ∧
      L_S.toSuccession.strictTransformSubspaceSeq
          (IdealSheaf.restrict
            (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (hS.preimageOpens U))
          (Fin.last _) =
        (L_P.toSuccession.strictTransformSubspaceSeq (I.restrict U) (Fin.last _)).pullback
          (⇑hS_r.inclusionMap ∘ ⇑G) (hS_r.inclusionMap.contMDiff.comp G.contMDiff) ∧
      ∀ q, hS.inclusionMap ((hS.toAnalyticManifold).inclusion (hS.preimageOpens U)
          (L_S.toSuccession.composite q)) =
        M.inclusion U (L_P.toSuccession.composite (hS_r.inclusionMap (G q))) := by
  obtain ⟨S_r, hS_r, G, h1, h2, h3, -⟩ :=
    exists_closedSubmanifold_last_pushforwardRestrict_boundary hS U L_S I hNE hSI L_P hL
  exact ⟨S_r, hS_r, G, h1, h2, h3⟩

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open AnalyticSpace.KLocallyRingedSpace

variable {𝕜 : Type} [RCLike 𝕜]

local notation:80 g:81 " ⊚ " f:80 => CategoryTheory.CategoryStruct.comp (obj := AnalyticSpace _) f g

namespace PieceEmbedding

open _root_.Manifold

variable {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)
  {n' : ℕ} (σ : Fin n ↪ Fin n')

/-- The piece embedding followed by the inverse of the padded embedding is the slice morphism:
`E.emb ∘ (E.padAlong σ).emb⁻¹ = padSliceHom σ 𝓘` (`padAlong`'s `emb := padSliceIso.inv ∘ E.emb`). -/
theorem emb_comp_embInv_padAlong : E.emb ⊚ (E.padAlong σ).embInv = padSliceHom σ E.ideal := by
  have e1 : (E.padAlong σ).emb ⊚ (E.padAlong σ).embInv = 𝟙 _ :=
    (E.padAlong σ).emb_comp_embInv
  have e2 : padSliceHom σ E.ideal ⊚ (padSliceIso σ E.ideal).inv = 𝟙 _ :=
    (padSliceIso σ E.ideal).inv_hom_id
  -- `E.emb ∘ P.emb⁻¹ = (slice ∘ slice⁻¹) ∘ (E.emb ∘ P.emb⁻¹)`
  -- `= slice ∘ ((slice⁻¹ ∘ E.emb) ∘ P.emb⁻¹) = slice ∘ (P.emb ∘ P.emb⁻¹) = slice`
  exact (Category.comp_id _).symm.trans
    ((congrArg (fun k => k ⊚ (E.emb ⊚ (E.padAlong σ).embInv)) e2.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => padSliceHom σ E.ideal ⊚ k) (Category.assoc _ _ _)).trans
          ((congrArg (fun k => padSliceHom σ E.ideal ⊚ k) e1).trans (Category.id_comp _)))))

variable (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (U : Opens (pieceAmbient.{u} 𝕜 (padOpens σ E.G)))
  (hU : IsCompact (closure (U : Set (pieceAmbient 𝕜 (padOpens σ E.G)))))

local macro "𝐒" : term => `(isClosedSubmanifold_padSlice σ (PieceEmbedding.G E))
local macro "𝐠" : term => `(padExtDiffeomorph σ (PieceEmbedding.G E))
local macro "𝐔₀" : term => `(preimageOpens (padExt σ (PieceEmbedding.G E))
  (contMDiff_padExt σ (PieceEmbedding.G E)) U)
local macro "𝐡𝐔₀" : term => `(isCompact_closure_preimage_padExt σ (PieceEmbedding.G E) U hU)
local macro "𝐉" : term => `(Manifold.IdealSheaf.pullback
  (⇑(IsClosedSubmanifold.inclusionMap 𝐒))
  (ContMDiffMap.contMDiff (IsClosedSubmanifold.inclusionMap 𝐒))
  (padIdeal σ (PieceEmbedding.ideal E)))

include hbed in
/-- **The final strict transform of the piece over `s⁻¹ U` is the final strict transform of the
padding over `U` restricted to a carried slice** (the weak commutation with closed embeddings,
[Kol07, 34.4], at the padding; [Kol07, Definition 30.3]): a closed submanifold `S_r` of the padded
last stage whose ideal lies in `Ỹ_P`, a diffeomorphism `G` of the piece's last stage onto `S_r`,
`Ỹ_E = G^*(Ỹ_P|_{S_r})`, and the square of the composites over the zero extension. The argument: the
field `bed.closedEmbedding` rewrites the padded sequence as the restricted push-forward of the
slice sequence; `exists_closedSubmanifold_last_pushforwardRestrict` reads its final strict
transform on the carried slice; the slice sequence is the piece's sequence over `s⁻¹ U` through the
dimension cast (`exists_diffeomorph_last_of_cast` at `padExtDiffeomorph`, from the commutation
with local isomorphisms of `hbed`). -/
theorem exists_closedSubmanifold_localResolution_padAlong :
    ∃ (S_r : Set (((E.padAlong σ).localResolutionSeq bed U hU).toSuccession.stage (Fin.last _)))
      (hS_r : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜)) S_r (n' - n))
      (G : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin (n' - (n' - n)) → 𝕜)
        ((E.localResolutionSeq bed 𝐔₀ 𝐡𝐔₀).toSuccession.stage (Fin.last _))
        hS_r.toAnalyticManifold ω),
      hS_r.idealSheaf ≤
        ((E.padAlong σ).localResolutionSeq bed U hU).toSuccession.strictTransformSubspaceSeq
          ((E.padAlong σ).restrictedIdeal U) (Fin.last _) ∧
      (E.localResolutionSeq bed 𝐔₀ 𝐡𝐔₀).toSuccession.strictTransformSubspaceSeq
          (E.restrictedIdeal 𝐔₀) (Fin.last _) =
        (((E.padAlong σ).localResolutionSeq bed U hU).toSuccession.strictTransformSubspaceSeq
          ((E.padAlong σ).restrictedIdeal U) (Fin.last _)).pullback
          (⇑hS_r.inclusionMap ∘ ⇑G) (hS_r.inclusionMap.contMDiff.comp G.contMDiff) ∧
      ∀ p, padExt σ E.G ((pieceAmbient 𝕜 E.G).inclusion 𝐔₀
          ((E.localResolutionSeq bed 𝐔₀ 𝐡𝐔₀).toSuccession.composite p)) =
        (pieceAmbient 𝕜 (padOpens σ E.G)).inclusion U
          (((E.padAlong σ).localResolutionSeq bed U hU).toSuccession.composite
            (hS_r.inclusionMap (G p))) := by
  -- the slice triple: the padded ideal restricted to the slice is the piece's ideal transported
  have hJeq : 𝐉 = E.ideal.pullback ⇑(𝐠).symm (𝐠).symm.contMDiff :=
    pullback_inclusionMap_padIdeal σ E.G E.ideal
  have hJnz : (𝐉).IsNonzeroEverywhere := by
    rw [hJeq]
    exact IdealSheaf.isNonzeroEverywhere_pullback_diffeomorph (𝐠).symm E.isNonzeroEverywhere
  have hJred : IdealSheaf.IsReduced 𝐉 := by
    rw [hJeq]
    exact IdealSheaf.isReduced_pullback_diffeomorph (𝐠).symm E.isReduced
  have hT' : DomBEDan 𝕜 ⟨𝐉, hJnz, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩ :=
    ⟨⟨fun x => PEmpty.elim x⟩, hJred⟩
  -- the commutation with closed embeddings at the padding: the padded sequence is the restricted
  -- push-forward of the slice sequence
  have hA : (E.padAlong σ).localResolutionSeq bed U hU =
      BlowUpSequence.pushforwardRestrict (𝐒) U
        (((bed.fam (n' - (n' - n))).fam _ hT').seqOn ((𝐒).preimageOpens U)
          ((𝐒).isCompact_closure_preimageOpens U hU)) :=
    bed.closedEmbedding n' (n' - n) (𝐒) (padIdeal σ E.ideal) (E.padAlong σ).isNonzeroEverywhere _
      hJnz (idealSheaf_padSlice_le_padIdeal σ E.G E.ideal) rfl (E.padAlong σ).domBEDan_ambientTriple
      hT' U hU
  obtain ⟨S_r, hS_r, G₁, hle, hideal, hsq⟩ :=
    BlowUpSequence.exists_closedSubmanifold_last_pushforwardRestrict (𝐒) U _ (padIdeal σ E.ideal)
      (((bed.fam (n' - (n' - n))).fam _ hT').noEmptyCenters _ _)
      (idealSheaf_padSlice_le_padIdeal σ E.G E.ideal) _ hA
  -- the dimension cast: the piece's sequence over `s⁻¹ U` is the slice sequence over `S ∩ U`
  have hn : n ≤ n' := by simpa using Fintype.card_le_of_embedding σ
  obtain ⟨G₀, hG₀sq, hG₀ideal⟩ := bed.exists_diffeomorph_last_of_cast hbed.2
    (Nat.sub_sub_self hn) (𝐠) 𝐉 hJnz E.ideal E.isNonzeroEverywhere
    (by rw [hJeq]; exact (IdealSheaf.pullback_symm_pullback (𝐠) E.ideal).symm)
    hT' E.domBEDan_ambientTriple ((𝐒).preimageOpens U) ((𝐒).isCompact_closure_preimageOpens U hU)
    𝐔₀ 𝐡𝐔₀ rfl
  refine ⟨S_r, hS_r, G₀.trans G₁, hle, ?_, ?_⟩
  · exact hG₀ideal.trans ((congrArg (fun J => IdealSheaf.pullback ⇑G₀ G₀.contMDiff J) hideal).trans
      (IdealSheaf.pullback_pullback _ _ _ _ _))
  · intro p
    calc padExt σ E.G ((pieceAmbient 𝕜 E.G).inclusion 𝐔₀
          ((E.localResolutionSeq bed 𝐔₀ 𝐡𝐔₀).toSuccession.composite p))
        = (𝐒).inclusionMap ((𝐠) ((pieceAmbient 𝕜 E.G).inclusion 𝐔₀
            ((E.localResolutionSeq bed 𝐔₀ 𝐡𝐔₀).toSuccession.composite p))) := rfl
      _ = (𝐒).inclusionMap (((𝐒).toAnalyticManifold).inclusion ((𝐒).preimageOpens U)
            ((((bed.fam (n' - (n' - n))).fam _ hT').seqOn ((𝐒).preimageOpens U)
              ((𝐒).isCompact_closure_preimageOpens U hU)).toSuccession.composite (G₀ p))) :=
          congrArg (𝐒).inclusionMap (hG₀sq p).symm
      _ = (pieceAmbient 𝕜 (padOpens σ E.G)).inclusion U
            (((E.padAlong σ).localResolutionSeq bed U hU).toSuccession.composite
              (hS_r.inclusionMap (G₁ (G₀ p)))) := hsq (G₀ p)
      _ = _ := rfl

local macro "𝕊" : term => `(AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
local macro "𝕊'" : term => `(AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜)))
local macro "𝕊ₛ" : term => `(AnalyticSpace.toSpace
  (ContinuousLinearEquiv.refl 𝕜 (Fin (n' - (n' - n)) → 𝕜)))
local macro "𝐋ₚ" : term =>
  `(PieceEmbedding.localResolutionSeq (PieceEmbedding.padAlong E σ) bed U hU)
local macro "𝐋ₑ" : term => `(PieceEmbedding.localResolutionSeq E bed 𝐔₀ 𝐡𝐔₀)
local macro "𝐌ₚ" : term => `(FiniteSuccession.stage (BlowUpSequence.toSuccession 𝐋ₚ) (Fin.last _))
local macro "𝐌ₑ" : term => `(FiniteSuccession.stage (BlowUpSequence.toSuccession 𝐋ₑ) (Fin.last _))
local macro "𝐘ₚ" : term =>
  `(FiniteSuccession.strictTransformSubspaceSeq (BlowUpSequence.toSuccession 𝐋ₚ)
  (PieceEmbedding.restrictedIdeal (PieceEmbedding.padAlong E σ) U) (Fin.last _))
local macro "𝐘ₑ" : term =>
  `(FiniteSuccession.strictTransformSubspaceSeq (BlowUpSequence.toSuccession 𝐋ₑ)
  (PieceEmbedding.restrictedIdeal E 𝐔₀) (Fin.last _))

/-- The body of `exists_isIso_localResolution_padAlong`, in general form: **the compatibility over
the piece of the two quotient isomorphisms** — for ANY carried slice `S_r` with `G : M_E ≃ S_r`
satisfying the core's strict-transform identity and square, the morphism of closed subspaces along
the inclusion of `S_r` after the one along `G` is compatible with the maps to the piece,
`Π_P ∘ (m_I ∘ m_G) = Π_E`. Read through `emb_comp_embInv_padAlong`, the slice morphism's square,
`toAnalyticSpaceι_comp_restrictedIdealHom`, `localResolutionMap_comp_ι`, the two squares of the
closed-subspace morphisms and the core's square of the composites, closed by
`Hom.ext_of_comp_quotientι`. The isomorphism theorem obtains `S_r`, `G` from the core. -/
theorem localResolutionToPiece_comp_homOfPullbackEq_padAlong
    (S_r : Set (((E.padAlong σ).localResolutionSeq bed U hU).toSuccession.stage (Fin.last _)))
    (hS_r : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜)) S_r (n' - n))
    (G : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin (n' - (n' - n)) → 𝕜)
      ((E.localResolutionSeq bed 𝐔₀ 𝐡𝐔₀).toSuccession.stage (Fin.last _))
      hS_r.toAnalyticManifold ω)
    (hideal : 𝐘ₑ = (𝐘ₚ).pullback (⇑hS_r.inclusionMap ∘ ⇑G)
      (hS_r.inclusionMap.contMDiff.comp G.contMDiff))
    (hsq : ∀ p, padExt σ E.G ((pieceAmbient 𝕜 E.G).inclusion 𝐔₀
        ((E.localResolutionSeq bed 𝐔₀ 𝐡𝐔₀).toSuccession.composite p)) =
      (pieceAmbient 𝕜 (padOpens σ E.G)).inclusion U
        (((E.padAlong σ).localResolutionSeq bed U hU).toSuccession.composite
          (hS_r.inclusionMap (G p)))) :
    (IdealSheaf.homOfPullbackEq ⇑G G.contMDiff
        (hideal.trans
        (IdealSheaf.pullback_pullback _ _ _ _
        _).symm) ≫ IdealSheaf.homOfPullbackEq ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff
        (rfl : (𝐘ₚ).pullback ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff =
        _)) ≫ (E.padAlong σ).localResolutionToPiece bed U hU =
      E.localResolutionToPiece bed 𝐔₀ 𝐡𝐔₀ := by
  have hG : 𝐘ₑ = ((𝐘ₚ).pullback ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff).pullback ⇑G
      G.contMDiff :=
    hideal.trans (IdealSheaf.pullback_pullback _ _ _ _ _).symm
  -- the identities of the layer, on the raw terms
  have e1 : E.emb ⊚ (E.padAlong σ).embInv = padSliceHom σ E.ideal := E.emb_comp_embInv_padAlong σ
  have e2 : E.ideal.toAnalyticSpaceι ⊚ padSliceHom σ E.ideal =
      (show 𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (padCoordProj σ E.G) (contMDiff_padCoordProj σ E.G)) ⊚
      (padIdeal σ E.ideal).toAnalyticSpaceι :=
    quotientMap_comp_quotientι (ofManifoldHom (padCoordProj σ E.G) (contMDiff_padCoordProj σ E.G))
      (padIdeal σ E.ideal) E.ideal (compat_padCoordProj σ E.ideal)
  have e3 : (padIdeal σ E.ideal).toAnalyticSpaceι ⊚ (E.padAlong σ).restrictedIdealHom U =
      (show 𝕊' ((pieceAmbient.{u} 𝕜 (padOpens σ E.G)).restrict U) ⟶
          𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) from
        ofManifoldHom (AnalyticManifold.inclusion _ U)
          (AnalyticManifold.inclusion _ U).contMDiff) ⊚
      ((E.padAlong σ).restrictedIdeal U).toAnalyticSpaceι :=
    (E.padAlong σ).toAnalyticSpaceι_comp_restrictedIdealHom U
  have e4 : ((E.padAlong σ).restrictedIdeal U).toAnalyticSpaceι ⊚
        (E.padAlong σ).localResolutionMap bed U hU =
      AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜))
        (BlowUpSequence.toSuccession 𝐋ₚ).composite ⊚ (𝐘ₚ).toAnalyticSpaceι :=
    (E.padAlong σ).localResolutionMap_comp_ι bed U hU
  have e5 : (𝐘ₚ).toAnalyticSpaceι ⊚ IdealSheaf.homOfPullbackEq ⇑hS_r.inclusionMap
        hS_r.inclusionMap.contMDiff
        (rfl : (𝐘ₚ).pullback ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff = _) =
      (show 𝕊ₛ hS_r.toAnalyticManifold ⟶
          𝕊' ((BlowUpSequence.toSuccession 𝐋ₚ).stage (Fin.last _)) from
        ofManifoldHom ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff) ⊚
      IdealSheaf.toAnalyticSpaceι ((𝐘ₚ).pullback ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff) :=
    homOfPullbackEq_comp_toAnalyticSpaceι _ _ _
  have e6 : IdealSheaf.toAnalyticSpaceι
        ((𝐘ₚ).pullback ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff) ⊚
        IdealSheaf.homOfPullbackEq ⇑G G.contMDiff hG =
      (show 𝕊 ((BlowUpSequence.toSuccession 𝐋ₑ).stage (Fin.last _)) ⟶ 𝕊ₛ hS_r.toAnalyticManifold
          from ofManifoldHom ⇑G G.contMDiff) ⊚
      (𝐘ₑ).toAnalyticSpaceι :=
    homOfPullbackEq_comp_toAnalyticSpaceι _ _ _
  have e7 : E.ideal.toAnalyticSpaceι ⊚ E.restrictedIdealHom 𝐔₀ =
      (show 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict 𝐔₀) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (AnalyticManifold.inclusion _ 𝐔₀)
          (AnalyticManifold.inclusion _ 𝐔₀).contMDiff) ⊚
      (E.restrictedIdeal 𝐔₀).toAnalyticSpaceι :=
    E.toAnalyticSpaceι_comp_restrictedIdealHom 𝐔₀
  have e8 : (E.restrictedIdeal 𝐔₀).toAnalyticSpaceι ⊚ E.localResolutionMap bed 𝐔₀ 𝐡𝐔₀ =
      AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (BlowUpSequence.toSuccession 𝐋ₑ).composite ⊚ (𝐘ₑ).toAnalyticSpaceι :=
    E.localResolutionMap_comp_ι bed 𝐔₀ 𝐡𝐔₀
  have e9 : E.emb ⊚ E.embInv = 𝟙 _ := E.emb_comp_embInv
  -- the square of the ambient maps: `p ∘ incl U ∘ σ_P ∘ j ∘ G = incl (s⁻¹ U) ∘ σ_E`
  have hfun : padCoordProj σ E.G ∘ (⇑(AnalyticManifold.inclusion _ U) ∘
        (⇑(BlowUpSequence.toSuccession 𝐋ₚ).composite ∘ (⇑hS_r.inclusionMap ∘ ⇑G))) =
      ⇑(AnalyticManifold.inclusion _ 𝐔₀) ∘
          ⇑(BlowUpSequence.toSuccession 𝐋ₑ).composite :=
    funext fun p => (congrArg (padCoordProj σ E.G) (hsq p).symm).trans (padCoordProj_padExt σ E.G _)
    -- the `Sp`-level identity:
  -- `Sp(p) ∘ Sp(incl U) ∘ Sp(σ_P) ∘ Sp(j) ∘ Sp(G) = Sp(incl (s⁻¹ U)) ∘ Sp(σ_E)`
  have s1 : (show 𝕊ₛ hS_r.toAnalyticManifold ⟶ 𝕊' 𝐌ₚ from
        ofManifoldHom ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff) ⊚
      (show 𝕊 𝐌ₑ ⟶ 𝕊ₛ hS_r.toAnalyticManifold from
        ofManifoldHom ⇑G G.contMDiff) =
      (show 𝕊 𝐌ₑ ⟶ 𝕊' 𝐌ₚ from
        ofManifoldHom (⇑hS_r.inclusionMap ∘ ⇑G) (hS_r.inclusionMap.contMDiff.comp G.contMDiff)) :=
    (ofManifoldHom_comp _ _ _ _).symm
  have s2 : AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜))
        (BlowUpSequence.toSuccession 𝐋ₚ).composite ⊚
      (show 𝕊 𝐌ₑ ⟶ 𝕊' 𝐌ₚ from
        ofManifoldHom (⇑hS_r.inclusionMap ∘ ⇑G) (hS_r.inclusionMap.contMDiff.comp G.contMDiff)) =
      (show 𝕊 𝐌ₑ ⟶ 𝕊' ((pieceAmbient.{u} 𝕜 (padOpens σ E.G)).restrict U) from
        ofManifoldHom (⇑(BlowUpSequence.toSuccession 𝐋ₚ).composite ∘ (⇑hS_r.inclusionMap ∘ ⇑G))
          ((BlowUpSequence.toSuccession 𝐋ₚ).composite.contMDiff.comp
            (hS_r.inclusionMap.contMDiff.comp G.contMDiff))) :=
    (ofManifoldHom_comp _ _ _ _).symm
  have s3 : (show
      𝕊' ((pieceAmbient.{u} 𝕜 (padOpens σ E.G)).restrict U) ⟶
      𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) from
        ofManifoldHom (AnalyticManifold.inclusion _ U)
          (AnalyticManifold.inclusion _ U).contMDiff) ⊚
      (show 𝕊 𝐌ₑ ⟶ 𝕊' ((pieceAmbient.{u} 𝕜 (padOpens σ E.G)).restrict U) from
        ofManifoldHom (⇑(BlowUpSequence.toSuccession 𝐋ₚ).composite ∘ (⇑hS_r.inclusionMap ∘ ⇑G))
          ((BlowUpSequence.toSuccession 𝐋ₚ).composite.contMDiff.comp
            (hS_r.inclusionMap.contMDiff.comp G.contMDiff))) =
      (show 𝕊 𝐌ₑ ⟶ 𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) from
        ofManifoldHom (⇑(AnalyticManifold.inclusion _ U) ∘
            (⇑(BlowUpSequence.toSuccession 𝐋ₚ).composite ∘ (⇑hS_r.inclusionMap ∘ ⇑G)))
          ((AnalyticManifold.inclusion _ U).contMDiff.comp
            ((BlowUpSequence.toSuccession 𝐋ₚ).composite.contMDiff.comp
              (hS_r.inclusionMap.contMDiff.comp G.contMDiff)))) :=
    (ofManifoldHom_comp _ _ _ _).symm
  have s4 : (show 𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (padCoordProj σ E.G) (contMDiff_padCoordProj σ E.G)) ⊚
      (show 𝕊 𝐌ₑ ⟶ 𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) from
        ofManifoldHom (⇑(AnalyticManifold.inclusion _ U) ∘
            (⇑(BlowUpSequence.toSuccession 𝐋ₚ).composite ∘ (⇑hS_r.inclusionMap ∘ ⇑G)))
          ((AnalyticManifold.inclusion _ U).contMDiff.comp
            ((BlowUpSequence.toSuccession 𝐋ₚ).composite.contMDiff.comp
              (hS_r.inclusionMap.contMDiff.comp G.contMDiff)))) =
      (show 𝕊 𝐌ₑ ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom
            (padCoordProj σ E.G ∘ (⇑(AnalyticManifold.inclusion _ U) ∘
            (⇑(BlowUpSequence.toSuccession 𝐋ₚ).composite ∘ (⇑hS_r.inclusionMap ∘ ⇑G))))
          ((contMDiff_padCoordProj σ E.G).comp
            ((AnalyticManifold.inclusion _ U).contMDiff.comp
              ((BlowUpSequence.toSuccession 𝐋ₚ).composite.contMDiff.comp
                (hS_r.inclusionMap.contMDiff.comp G.contMDiff))))) :=
    (ofManifoldHom_comp _ _ _ _).symm
  have s5 : (show 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict 𝐔₀) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (AnalyticManifold.inclusion _ 𝐔₀)
          (AnalyticManifold.inclusion _ 𝐔₀).contMDiff) ⊚
      AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (BlowUpSequence.toSuccession 𝐋ₑ).composite =
      (show 𝕊 𝐌ₑ ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (⇑(AnalyticManifold.inclusion _ 𝐔₀) ∘
            ⇑(BlowUpSequence.toSuccession 𝐋ₑ).composite)
          ((AnalyticManifold.inclusion _ 𝐔₀).contMDiff.comp
            (BlowUpSequence.toSuccession 𝐋ₑ).composite.contMDiff)) :=
    (ofManifoldHom_comp _ _ _ _).symm
  have e10 := (congrArg
      (fun k => (show 𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G)
      from
        ofManifoldHom (padCoordProj σ E.G) (contMDiff_padCoordProj σ E.G)) ⊚
      ((show 𝕊' ((pieceAmbient.{u} 𝕜 (padOpens σ E.G)).restrict U) ⟶
          𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) from
        ofManifoldHom (AnalyticManifold.inclusion _ U)
          (AnalyticManifold.inclusion _ U).contMDiff) ⊚
        (AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜))
          (BlowUpSequence.toSuccession 𝐋ₚ).composite ⊚ k))) s1).trans
    ((congrArg (fun k =>
        (show 𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (padCoordProj σ E.G) (contMDiff_padCoordProj σ E.G)) ⊚
      ((show 𝕊' ((pieceAmbient.{u} 𝕜 (padOpens σ E.G)).restrict U) ⟶
          𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) from
        ofManifoldHom (AnalyticManifold.inclusion _ U)
          (AnalyticManifold.inclusion _ U).contMDiff) ⊚ k)) s2).trans
      ((congrArg (fun k =>
          (show 𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) from
          ofManifoldHom (padCoordProj σ E.G) (contMDiff_padCoordProj σ E.G)) ⊚ k) s3).trans
        (s4.trans ((ofManifoldHom_congr hfun _).trans s5.symm))))
  -- the abbreviations (plain `let`s, every type spelled with the two `localResolution`s so the
  -- `calc` steps share one `Eq` type; the identities re-read on them)
  let ιE :
      E.ideal.toAnalyticSpace ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) :=
    E.ideal.toAnalyticSpaceι
  let qP : (padIdeal σ E.ideal).toAnalyticSpace ⟶ 𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) :=
    (padIdeal σ E.ideal).toAnalyticSpaceι
  let qU :
      (((E.padAlong σ).restrictedIdeal U).toAnalyticSpace ⟶ 𝕊'
          ((pieceAmbient.{u} 𝕜 (padOpens σ E.G)).restrict U)) :=
    ((E.padAlong σ).restrictedIdeal U).toAnalyticSpaceι
  let ιYp :
      (E.padAlong σ).localResolution bed U hU ⟶ 𝕊' 𝐌ₚ :=
    (𝐘ₚ).toAnalyticSpaceι
  let ιpb : IdealSheaf.toAnalyticSpace ((𝐘ₚ).pullback ⇑hS_r.inclusionMap
      hS_r.inclusionMap.contMDiff) ⟶ 𝕊ₛ hS_r.toAnalyticManifold :=
    IdealSheaf.toAnalyticSpaceι ((𝐘ₚ).pullback ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff)
  let ιYe : E.localResolution bed 𝐔₀ 𝐡𝐔₀ ⟶ 𝕊 𝐌ₑ :=
    (𝐘ₑ).toAnalyticSpaceι
  let qE : (E.restrictedIdeal 𝐔₀).toAnalyticSpace ⟶ 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict 𝐔₀) :=
    (E.restrictedIdeal 𝐔₀).toAnalyticSpaceι
  let ρP :
      ((E.padAlong σ).restrictedIdeal U).toAnalyticSpace ⟶
          (padIdeal σ E.ideal).toAnalyticSpace :=
    (E.padAlong σ).restrictedIdealHom U
  let lP : (E.padAlong σ).localResolution bed U hU ⟶
      ((E.padAlong σ).restrictedIdeal U).toAnalyticSpace :=
    (E.padAlong σ).localResolutionMap bed U hU
  let ρE : (E.restrictedIdeal 𝐔₀).toAnalyticSpace ⟶ E.ideal.toAnalyticSpace :=
    E.restrictedIdealHom 𝐔₀
  let lE : E.localResolution bed 𝐔₀ 𝐡𝐔₀ ⟶ (E.restrictedIdeal 𝐔₀).toAnalyticSpace :=
    E.localResolutionMap bed 𝐔₀ 𝐡𝐔₀
  let SpP : 𝕊' (pieceAmbient.{u} 𝕜 (padOpens σ E.G)) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) :=
    ofManifoldHom (padCoordProj σ E.G) (contMDiff_padCoordProj σ E.G)
  let SpU :
      (𝕊' ((pieceAmbient.{u} 𝕜 (padOpens σ E.G)).restrict U) ⟶ 𝕊'
          (pieceAmbient.{u} 𝕜 (padOpens σ E.G))) :=
    ofManifoldHom (AnalyticManifold.inclusion _ U)
      (AnalyticManifold.inclusion _ U).contMDiff
  let SpC : 𝕊' 𝐌ₚ ⟶ 𝕊' ((pieceAmbient.{u} 𝕜 (padOpens σ E.G)).restrict U) :=
    AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜))
      (BlowUpSequence.toSuccession 𝐋ₚ).composite
  let SpI : 𝕊ₛ hS_r.toAnalyticManifold ⟶ 𝕊' 𝐌ₚ :=
    ofManifoldHom ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff
  let SpG : 𝕊 𝐌ₑ ⟶ 𝕊ₛ hS_r.toAnalyticManifold :=
    ofManifoldHom ⇑G G.contMDiff
  let Sp0 : 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict 𝐔₀) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) :=
    ofManifoldHom (AnalyticManifold.inclusion _ 𝐔₀)
      (AnalyticManifold.inclusion _ 𝐔₀).contMDiff
  let SpCE :
      𝕊 𝐌ₑ ⟶ 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict 𝐔₀) :=
    AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (BlowUpSequence.toSuccession 𝐋ₑ).composite
  let mI : IdealSheaf.toAnalyticSpace ((𝐘ₚ).pullback ⇑hS_r.inclusionMap
      hS_r.inclusionMap.contMDiff) ⟶ (E.padAlong σ).localResolution bed U hU :=
    IdealSheaf.homOfPullbackEq ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff
      (rfl : (𝐘ₚ).pullback ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff = _)
  let mG : E.localResolution bed 𝐔₀ 𝐡𝐔₀ ⟶ IdealSheaf.toAnalyticSpace ((𝐘ₚ).pullback
      ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff) :=
    IdealSheaf.homOfPullbackEq ⇑G G.contMDiff hG
  let φ : E.localResolution bed 𝐔₀ 𝐡𝐔₀ ⟶ (E.padAlong σ).localResolution bed U hU :=
    mI ⊚ mG
  -- the identities re-read on the abbreviations, and the category laws at `Hom`-typed arguments
  have e2' : ιE ⊚ padSliceHom σ E.ideal = SpP ⊚ qP := e2
  have e3' : qP ⊚ ρP = SpU ⊚ qU := e3
  have e4' : qU ⊚ lP = SpC ⊚ ιYp := e4
  have e5' : ιYp ⊚ mI = SpI ⊚ ιpb := e5
  have e6' : ιpb ⊚ mG = SpG ⊚ ιYe := e6
  have e7' : ιE ⊚ ρE = Sp0 ⊚ qE := e7
  have e8' : qE ⊚ lE = SpCE ⊚ ιYe := e8
  have e10' : SpP ⊚ (SpU ⊚ (SpC ⊚ (SpI ⊚ SpG))) = Sp0 ⊚ SpCE := e10
  have assoc' :
      ∀ {A B C D : AnalyticSpace.{u} 𝕜}
          (a : C ⟶ D)
      (b : B ⟶ C)
          (c : A ⟶ B),
      a ⊚ (b ⊚ c) = (a ⊚ b) ⊚ c := fun _ _ _ => Category.assoc _ _ _
  have comp_id' :
      ∀ {A B : AnalyticSpace.{u} 𝕜}
          (f : A ⟶ B),
      𝟙 B ⊚ f = f := fun _ => Category.comp_id _
  have id_comp' :
      ∀ {A B : AnalyticSpace.{u} 𝕜}
          (f : A ⟶ B),
      f ⊚ 𝟙 A = f := fun _ => Category.id_comp _
  -- the two composites into `Sp(G)/𝓘` agree after `ι`
  have key0 : ιE ⊚ (E.emb ⊚ (((E.padAlong σ).embInv ⊚ (ρP ⊚ lP)) ⊚ (mI ⊚ mG))) =
      ιE ⊚ (E.emb ⊚ (E.embInv ⊚ (ρE ⊚ lE))) :=
    calc ιE ⊚ (E.emb ⊚ (((E.padAlong σ).embInv ⊚ (ρP ⊚ lP)) ⊚ (mI ⊚ mG)))
        = ιE ⊚ ((E.emb ⊚ ((E.padAlong σ).embInv ⊚ (ρP ⊚ lP))) ⊚ (mI ⊚ mG)) :=
          congrArg (fun k => ιE ⊚ k) (assoc' _ _ _)
      _ = ιE ⊚ (((E.emb ⊚ (E.padAlong σ).embInv) ⊚ (ρP ⊚ lP)) ⊚ (mI ⊚ mG)) :=
          congrArg (fun k => ιE ⊚ (k ⊚ (mI ⊚ mG))) (assoc' _ _ _)
      _ = ιE ⊚ ((padSliceHom σ E.ideal ⊚ (ρP ⊚ lP)) ⊚ (mI ⊚ mG)) :=
          congrArg (fun k => ιE ⊚ ((k ⊚ (ρP ⊚ lP)) ⊚ (mI ⊚ mG))) e1
      _ = (ιE ⊚ (padSliceHom σ E.ideal ⊚ (ρP ⊚ lP))) ⊚ (mI ⊚ mG) := assoc' _ _ _
      _ = ((ιE ⊚ padSliceHom σ E.ideal) ⊚ (ρP ⊚ lP)) ⊚ (mI ⊚ mG) :=
          congrArg (fun k => k ⊚ (mI ⊚ mG)) (assoc' _ _ _)
      _ = ((SpP ⊚ qP) ⊚ (ρP ⊚ lP)) ⊚ (mI ⊚ mG) :=
          congrArg (fun k => (k ⊚ (ρP ⊚ lP)) ⊚ (mI ⊚ mG)) e2'
      _ = (SpP ⊚ (qP ⊚ (ρP ⊚ lP))) ⊚ (mI ⊚ mG) :=
          congrArg (fun k => k ⊚ (mI ⊚ mG)) (assoc' _ _ _).symm
      _ = (SpP ⊚ ((qP ⊚ ρP) ⊚ lP)) ⊚ (mI ⊚ mG) :=
          congrArg (fun k => (SpP ⊚ k) ⊚ (mI ⊚ mG)) (assoc' _ _ _)
      _ = (SpP ⊚ ((SpU ⊚ qU) ⊚ lP)) ⊚ (mI ⊚ mG) :=
          congrArg (fun k => (SpP ⊚ (k ⊚ lP)) ⊚ (mI ⊚ mG)) e3'
      _ = (SpP ⊚ (SpU ⊚ (qU ⊚ lP))) ⊚ (mI ⊚ mG) :=
          congrArg (fun k => (SpP ⊚ k) ⊚ (mI ⊚ mG)) (assoc' _ _ _).symm
      _ = (SpP ⊚ (SpU ⊚ (SpC ⊚ ιYp))) ⊚ (mI ⊚ mG) :=
          congrArg (fun k => (SpP ⊚ (SpU ⊚ k)) ⊚ (mI ⊚ mG)) e4'
      _ = SpP ⊚ ((SpU ⊚ (SpC ⊚ ιYp)) ⊚ (mI ⊚ mG)) := (assoc' _ _ _).symm
      _ = SpP ⊚ (SpU ⊚ ((SpC ⊚ ιYp) ⊚ (mI ⊚ mG))) :=
          congrArg (fun k => SpP ⊚ k) (assoc' _ _ _).symm
      _ = SpP ⊚ (SpU ⊚ (SpC ⊚ (ιYp ⊚ (mI ⊚ mG)))) :=
          congrArg (fun k => SpP ⊚ (SpU ⊚ k)) (assoc' _ _ _).symm
      _ = SpP ⊚ (SpU ⊚ (SpC ⊚ ((ιYp ⊚ mI) ⊚ mG))) :=
          congrArg (fun k => SpP ⊚ (SpU ⊚ (SpC ⊚ k))) (assoc' _ _ _)
      _ = SpP ⊚ (SpU ⊚ (SpC ⊚ ((SpI ⊚ ιpb) ⊚ mG))) :=
          congrArg (fun k => SpP ⊚ (SpU ⊚ (SpC ⊚ (k ⊚ mG)))) e5'
      _ = SpP ⊚ (SpU ⊚ (SpC ⊚ (SpI ⊚ (ιpb ⊚ mG)))) :=
          congrArg (fun k => SpP ⊚ (SpU ⊚ (SpC ⊚ k))) (assoc' _ _ _).symm
      _ = SpP ⊚ (SpU ⊚ (SpC ⊚ (SpI ⊚ (SpG ⊚ ιYe)))) :=
          congrArg (fun k => SpP ⊚ (SpU ⊚ (SpC ⊚ (SpI ⊚ k)))) e6'
      _ = SpP ⊚ (SpU ⊚ (SpC ⊚ ((SpI ⊚ SpG) ⊚ ιYe))) :=
          congrArg (fun k => SpP ⊚ (SpU ⊚ (SpC ⊚ k))) (assoc' _ _ _)
      _ = SpP ⊚ (SpU ⊚ ((SpC ⊚ (SpI ⊚ SpG)) ⊚ ιYe)) :=
          congrArg (fun k => SpP ⊚ (SpU ⊚ k)) (assoc' _ _ _)
      _ = SpP ⊚ ((SpU ⊚ (SpC ⊚ (SpI ⊚ SpG))) ⊚ ιYe) :=
          congrArg (fun k => SpP ⊚ k) (assoc' _ _ _)
      _ = (SpP ⊚ (SpU ⊚ (SpC ⊚ (SpI ⊚ SpG)))) ⊚ ιYe := assoc' _ _ _
      _ = (Sp0 ⊚ SpCE) ⊚ ιYe := congrArg (fun k => k ⊚ ιYe) e10'
      _ = Sp0 ⊚ (SpCE ⊚ ιYe) := (assoc' _ _ _).symm
      _ = Sp0 ⊚ (qE ⊚ lE) := congrArg (fun k => Sp0 ⊚ k) e8'.symm
      _ = (Sp0 ⊚ qE) ⊚ lE := assoc' _ _ _
      _ = (ιE ⊚ ρE) ⊚ lE := congrArg (fun k => k ⊚ lE) e7'.symm
      _ = ιE ⊚ (ρE ⊚ lE) := (assoc' _ _ _).symm
      _ = ιE ⊚ (𝟙 _ ⊚ (ρE ⊚ lE)) :=
          congrArg (fun k => ιE ⊚ k) (comp_id' _).symm
      _ = ιE ⊚ ((E.emb ⊚ E.embInv) ⊚ (ρE ⊚ lE)) :=
          congrArg (fun k => ιE ⊚ (k ⊚ (ρE ⊚ lE))) e9.symm
      _ = ιE ⊚ (E.emb ⊚ (E.embInv ⊚ (ρE ⊚ lE))) :=
          congrArg (fun k => ιE ⊚ k) (assoc' _ _ _).symm
  have key1 : E.emb ⊚ (((E.padAlong σ).embInv ⊚ (ρP ⊚ lP)) ⊚ (mI ⊚ mG)) =
      E.emb ⊚ (E.embInv ⊚ (ρE ⊚ lE)) :=
    Hom.ext_of_comp_quotientι (X := ofManifold 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 E.G)) E.ideal
      key0
  -- cancel the isomorphism `E.emb` (the class-based lemmas take the category `An/K` explicitly)
  have key : ((E.padAlong σ).embInv ⊚ (ρP ⊚ lP)) ⊚ φ = E.embInv ⊚ (ρE ⊚ lE) := by
    have hemb : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _ E.emb := E.emb_isIso
    exact (@Iso.cancel_iso_hom_right (AnalyticSpace.{u} 𝕜) _ _ _ _ _ _
      (@asIso (AnalyticSpace.{u} 𝕜) _ _ _ E.emb hemb)).mp key1
  exact key

include hbed in
/-- **The padded resolution is the resolution of the slice preimage, over the piece** (the weak
commutation with closed embeddings, [Kol07, 34.4], at the padding `E.padAlong σ`, with
[Kol07, Definition 30.3] and the dimension cast): for a relatively compact open `U` of the padded
ambient, the local resolution of `E.padAlong σ` over `U` is isomorphic over the piece to the local
resolution of `E` over `s⁻¹ U` — the morphism of closed subspaces along the inclusion of the
carried slice (`isIso_homOfPullbackEq_inclusionMap`, the core's `𝓘_{S_r} ≤ Ỹ_P`) and along the
core's diffeomorphism `G` (`isIso_homOfPullbackEq_of_diffeomorph`); the compatibility with the
maps to the piece through `emb_comp_embInv_padAlong`, the slice morphism's square,
`toAnalyticSpaceι_comp_restrictedIdealHom`, `localResolutionMap_comp_ι`, the two squares of the
closed-subspace morphisms and the core's square of the composites, closed by
`Hom.ext_of_comp_quotientι`. -/
theorem exists_isIso_localResolution_padAlong :
    ∃ ψ : (E.padAlong σ).localResolution bed U hU ⟶ E.localResolution bed (Manifold.preimageOpens
        (padExt σ E.G) (contMDiff_padExt σ E.G) U) (isCompact_closure_preimage_padExt σ E.G U hU),
      IsIso ψ ∧
      ψ ≫ E.localResolutionToPiece bed (Manifold.preimageOpens (padExt σ E.G)
          (contMDiff_padExt σ E.G) U) (isCompact_closure_preimage_padExt σ E.G U hU) =
        (E.padAlong σ).localResolutionToPiece bed U hU := by
  obtain ⟨S_r, hS_r, G, hle, hideal, hsq⟩ :=
    E.exists_closedSubmanifold_localResolution_padAlong σ bed hbed U hU
  have hG : 𝐘ₑ = ((𝐘ₚ).pullback ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff).pullback ⇑G
      G.contMDiff :=
    hideal.trans (IdealSheaf.pullback_pullback _ _ _ _ _).symm
  have hQ2 : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _
      (IdealSheaf.homOfPullbackEq ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff
        (rfl : (𝐘ₚ).pullback ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff = _)) :=
    isIso_homOfPullbackEq_inclusionMap hS_r hle rfl
  have hQ1 : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _
      (IdealSheaf.homOfPullbackEq ⇑G G.contMDiff hG) :=
    isIso_homOfPullbackEq_of_diffeomorph G hG
  have key := E.localResolutionToPiece_comp_homOfPullbackEq_padAlong σ bed U hU S_r hS_r G hideal
    hsq
  let mI : IdealSheaf.toAnalyticSpace ((𝐘ₚ).pullback ⇑hS_r.inclusionMap
      hS_r.inclusionMap.contMDiff) ⟶ (E.padAlong σ).localResolution bed U hU :=
    IdealSheaf.homOfPullbackEq ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff
      (rfl : (𝐘ₚ).pullback ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff = _)
  let mG : E.localResolution bed 𝐔₀ 𝐡𝐔₀ ⟶ IdealSheaf.toAnalyticSpace ((𝐘ₚ).pullback
      ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff) :=
    IdealSheaf.homOfPullbackEq ⇑G G.contMDiff hG
  let φ : E.localResolution bed 𝐔₀ 𝐡𝐔₀ ⟶ (E.padAlong σ).localResolution bed U hU :=
    mI ⊚ mG
  have hφiso : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _ φ :=
    @IsIso.comp_isIso (AnalyticSpace.{u} 𝕜) _ _ _ _ mG mI hQ1 hQ2
  refine ⟨@inv (AnalyticSpace.{u} 𝕜) _ _ _ φ hφiso,
    @IsIso.inv_isIso (AnalyticSpace.{u} 𝕜) _ _ _ φ hφiso, ?_⟩
  exact (@IsIso.inv_comp_eq (AnalyticSpace.{u} 𝕜) _ _ _ _ φ hφiso _ _).mpr
    key.symm

end PieceEmbedding

end Hironaka.Manifold

end
