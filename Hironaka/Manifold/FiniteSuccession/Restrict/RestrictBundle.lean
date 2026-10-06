/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Pushforward
public import Hironaka.Manifold.Germ.StalkMap
public import Mathlib.Analysis.InnerProductSpace.Basic
import Hironaka.Manifold.BlowUp.Restrict
import Hironaka.Manifold.FiniteSuccession.Functor.LocalCover
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PushforwardPullback
import Hironaka.Manifold.Submanifold.Charts
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The two bundlings of a restricted closed submanifold

A closed submanifold `S ⊆ M` read over an open `U ⊆ M` carries two analytic structures on the same
carrier `S ∩ U`: the open subset `U_S := inclusionMap ⁻¹' U` of the bundled `S`
(`(hS.toAnalyticManifold).restrict U_S`) and the bundling of `S ∩ U` as a closed submanifold of
`M.restrict U` (`(hS.restrictOpen U).toAnalyticManifold`, via `IsClosedSubmanifoldOn.restrict`).
They agree up to an analytic isomorphism over the identity of the carrier
(`restrictBundleDiffeomorph`); with it a list of centres on the first is pushed forward to
`M.restrict U` (`BlowUpSequence.pushforwardRestrict`, the `PushforwardStage` recursion of
`Pushforward.lean` with the isomorphism as its `iso` field), and the push-forward is the ordinary
one of the list transported along the isomorphism (`pushforwardRestrict_eq`). This is the
bookkeeping behind the push-forward `τ_* BMO_{n-1,1}(Y, J, 1, ∅)` from a hypersurface of maximal
contact in [Kol07, Theorem 103(3)], read over each open of a cover; the push-forward of a blow-up
sequence is [Kol07, Definition 30.3], its behaviour under open embeddings [Kol07, 34.1]. Not in
the sources; routine.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}

/-- The open `U_S := inclusionMap ⁻¹' U` of the bundled submanifold — the instance at the closed
embedding `inclusionMap` of the general `preimageOpens φ hφ U`, whose `mem_preimageOpens` reads
`p ∈ U_S ↔ (p : S).1 ∈ U`. -/
abbrev IsClosedSubmanifold.preimageOpens (hS : IsClosedSubmanifold ψ S s) (U : Opens M) :
    Opens hS.toAnalyticManifold :=
  Manifold.preimageOpens hS.inclusionMap hS.inclusionMap.contMDiff U

/-- `U_S` is relatively compact in `S` when `U` is relatively compact in `M` (`S` is closed). -/
theorem IsClosedSubmanifold.isCompact_closure_preimageOpens (hS : IsClosedSubmanifold ψ S s)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    IsCompact (closure (hS.preimageOpens U : Set hS.toAnalyticManifold)) := by
  have hemb : Topology.IsClosedEmbedding (Subtype.val : S → M) :=
    hS.isClosed.isClosedEmbedding_subtypeVal
  refine (hemb.isCompact_preimage hU).of_isClosed_subset isClosed_closure ?_
  refine closure_minimal (fun p hp => ?_) (isClosed_closure.preimage continuous_subtype_val)
  exact subset_closure hp

/-- `S ∩ U` as a closed submanifold of the open subset `U` (`IsClosedSubmanifoldOn.restrict` at
`isClosedSubmanifoldOn'`). -/
theorem IsClosedSubmanifold.restrictOpen (hS : IsClosedSubmanifold ψ S s) (U : Opens M) :
    IsClosedSubmanifold ψ (⇑(M.inclusion U) ⁻¹' S : Set (M.restrict U)) s :=
  (hS.isClosedSubmanifoldOn' U.2).restrict

/-- **The bundling bridge** (general form): for an open `V ⊆ M` and an open `W` of the bundled `S`
whose underlying set is `inclusionMap ⁻¹' V`, the identity of the carrier `S ∩ V` as an analytic
isomorphism from the open `W` of the bundled `S` to the bundled closed submanifold `S ∩ V` of
`M.restrict V` (Kollár's remark that for all practical purposes `Z_i^X = Z_i^S`,
[Kol07, Definition 30.3]). -/
def IsClosedSubmanifold.restrictBundleDiffeomorphOf (hS : IsClosedSubmanifold ψ S s) (V : Opens M)
    (W : Opens hS.toAnalyticManifold)
    (hW : (W : Set hS.toAnalyticManifold) = ⇑hS.inclusionMap ⁻¹' (V : Set M)) :
    Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜)
      ((hS.toAnalyticManifold).restrict W) ((hS.restrictOpen V).toAnalyticManifold) ω where
  toFun p := ⟨⟨p.1.1, by
      have h : p.1 ∈ (W : Set hS.toAnalyticManifold) := p.2
      rw [hW] at h
      exact h⟩, p.1.2⟩
  invFun r := ⟨⟨r.1.1, r.2⟩, by
      have h : (⟨r.1.1, r.2⟩ : hS.toAnalyticManifold) ∈ (W : Set hS.toAnalyticManifold) := by
        rw [hW]
        exact r.1.2
      exact h⟩
  left_inv p := rfl
  right_inv r := rfl
  contMDiff_toFun := by
    -- into `M.restrict V` (`contMDiff_codRestrict_opens`), then codomain-restricted to `S ∩ V`
    have hf : ContMDiff 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, E) ω
        (fun p : (hS.toAnalyticManifold).restrict W => (⟨p.1.1, by
          have h : p.1 ∈ (W : Set hS.toAnalyticManifold) := p.2
          rw [hW] at h
          exact h⟩ : M.restrict V)) :=
      contMDiff_codRestrict_opens hS.inclusionMap.contMDiff fun _ => rfl
    exact (hS.restrictOpen V).contMDiff_codRestrict hf fun p => p.1.2
  contMDiff_invFun := by
    -- `(hS.restrictOpen V).restrictMap hS (M.inclusion V) …` into the bundled `S`, then into the
    -- open `W` (`liftPropWithinAt_subtypeVal_comp_iff`)
    intro r
    have hval : ContMDiffAt 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω
        ((Subtype.val : (hS.toAnalyticManifold).restrict W → hS.toAnalyticManifold) ∘
          fun r : (hS.restrictOpen V).toAnalyticManifold =>
            (⟨⟨r.1.1, r.2⟩, by
              have h : (⟨r.1.1, r.2⟩ : hS.toAnalyticManifold) ∈
                  (W : Set hS.toAnalyticManifold) := by
                rw [hW]
                exact r.1.2
              exact h⟩ : (hS.toAnalyticManifold).restrict W)) r :=
      ((hS.restrictOpen V).restrictMap hS (M.inclusion V) (M.inclusion V).contMDiff
        fun _ hx => hx).contMDiff.contMDiffAt
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω) _ univ r).mp hval

/-- The bridge at the canonical open `U_S := hS.preimageOpens U` (`V := U`). -/
abbrev IsClosedSubmanifold.restrictBundleDiffeomorph (hS : IsClosedSubmanifold ψ S s)
    (U : Opens M) :
    Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜)
      ((hS.toAnalyticManifold).restrict (hS.preimageOpens U))
      ((hS.restrictOpen U).toAnalyticManifold) ω :=
  hS.restrictBundleDiffeomorphOf U (hS.preimageOpens U) rfl

/-- The push-forward stage of `S ∩ V ⊆ M.restrict V` read from the open `W` of the bundled `S` —
the bridge fills the stage's `iso` ([Kol07, Definition 30.3]). -/
def IsClosedSubmanifold.restrictStageOf (hS : IsClosedSubmanifold ψ S s) (V : Opens M)
    (W : Opens hS.toAnalyticManifold)
    (hW : (W : Set hS.toAnalyticManifold) = ⇑hS.inclusionMap ⁻¹' (V : Set M)) :
    PushforwardStage ψ s ((hS.toAnalyticManifold).restrict W) :=
  ⟨M.restrict V, ⇑(M.inclusion V) ⁻¹' S, hS.restrictOpen V, hS.restrictBundleDiffeomorphOf V W hW⟩

/-- The push-forward to `M.restrict V` of a list of centres on an open `W` of the bundled `S`
whose underlying set is `inclusionMap ⁻¹' V` (the trace of `V` on `S`; the image of `W` is then
closed in `V`, which a push-forward stage requires): [Kol07, Definition 30.3] over one open. -/
def _root_.AnalyticManifold.BlowUpSequence.pushforwardRestrictOf (hS : IsClosedSubmanifold ψ S s)
    (V : Opens M)
    (W : Opens hS.toAnalyticManifold)
    (hW : (W : Set hS.toAnalyticManifold) = ⇑hS.inclusionMap ⁻¹' (V : Set M))
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((hS.toAnalyticManifold).restrict W)) :
    AnalyticManifold.BlowUpSequence ψ (M.restrict V) :=
  AnalyticManifold.BlowUpSequence.pushforwardAux (hS.restrictStageOf V W hW) L

/-- The push-forward over one open at the canonical open `U_S := hS.preimageOpens U`
([Kol07, Definition 30.3]). -/
abbrev _root_.AnalyticManifold.BlowUpSequence.pushforwardRestrict (hS : IsClosedSubmanifold ψ S s)
    (U : Opens M)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((hS.toAnalyticManifold).restrict (hS.preimageOpens U))) :
    AnalyticManifold.BlowUpSequence ψ (M.restrict U) :=
  AnalyticManifold.BlowUpSequence.pushforwardRestrictOf hS U (hS.preimageOpens U) rfl L

/-- The per-open push-forward is the ordinary push-forward (`BlowUpSequence.pushforward`) of the
list transported along the bridge. -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforwardRestrictOf_eq
    (hS : IsClosedSubmanifold ψ S s) (V : Opens M)
    (W : Opens hS.toAnalyticManifold)
    (hW : (W : Set hS.toAnalyticManifold) = ⇑hS.inclusionMap ⁻¹' (V : Set M))
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((hS.toAnalyticManifold).restrict W)) :
    AnalyticManifold.BlowUpSequence.pushforwardRestrictOf hS V W hW L =
      (L.pullback ⟨(hS.restrictBundleDiffeomorphOf V W hW).symm,
          (hS.restrictBundleDiffeomorphOf V W hW).symm.contMDiff⟩
        (hS.restrictBundleDiffeomorphOf V W hW).symm.isLocalDiffeomorph).pushforward
        (hS.restrictOpen V) := by
  -- `PushforwardStage.pushforwardAux_pullback` with `G := id`, `gᵢ := e.symm`, then `pullback_id`
  set e := hS.restrictBundleDiffeomorphOf V W hW with he
  let P' : PushforwardStage ψ s (hS.restrictOpen V).toAnalyticManifold :=
    ⟨M.restrict V, ⇑(M.inclusion V) ⁻¹' S, hS.restrictOpen V, Diffeomorph.refl _ _ _⟩
  have hst : PushforwardStage.IsPullbackStage (hS.restrictStageOf V W hW) P' ContMDiffMap.id
      ⟨e.symm, e.symm.contMDiff⟩ :=
    { isLocalDiffeomorph := AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id _
      sub_eq := rfl
      square := fun q => by
        change ((e (e.symm q) : (hS.restrictOpen V).toAnalyticManifold) : _).1 = (q : _).1
        rw [e.apply_symm_apply] }
  have h := PushforwardStage.pushforwardAux_pullback (hS.restrictStageOf V W hW) P'
    ContMDiffMap.id ⟨e.symm, e.symm.contMDiff⟩ e.symm.isLocalDiffeomorph hst L
  -- the pull-back along the identity is the identity (the stage's `space` projections are
  -- definitionally `M.restrict V`, so a term-level transitivity rather than a rewrite)
  have h' : (AnalyticManifold.BlowUpSequence.pushforwardAux (hS.restrictStageOf V W hW) L).pullback
      (ContMDiffMap.id : AnalyticMap (M.restrict V) (M.restrict V))
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id (M.restrict V)) =
      AnalyticManifold.BlowUpSequence.pushforwardAux (hS.restrictStageOf V W hW) L :=
    AnalyticManifold.BlowUpSequence.pullback_id _
  exact h'.symm.trans h

/-- The named instance unfolds to the stage recursion (`rfl`). -/
example (hS : IsClosedSubmanifold ψ S s) (U : Opens M)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((hS.toAnalyticManifold).restrict (hS.preimageOpens U))) :
    AnalyticManifold.BlowUpSequence.pushforwardRestrict hS U L =
      AnalyticManifold.BlowUpSequence.pushforwardAux (hS.restrictStageOf U
          (hS.preimageOpens U) rfl) L := rfl

/-- The bridge is the stage's `iso` (`rfl`). -/
example (hS : IsClosedSubmanifold ψ S s) (V : Opens M) (W : Opens hS.toAnalyticManifold)
    (hW : (W : Set hS.toAnalyticManifold) = ⇑hS.inclusionMap ⁻¹' (V : Set M)) :
    (hS.restrictStageOf V W hW).iso = hS.restrictBundleDiffeomorphOf V W hW := rfl

end Manifold

end
