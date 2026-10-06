/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BOanFamOfInput
public import Hironaka.Resolution.Analytic.OrderReduction.Step2Along
public import Hironaka.Resolution.Analytic.Functor.FamilyClosedEmbedding
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BDBridge
import Hironaka.Resolution.Analytic.OrderReduction.BDErase
import Hironaka.Resolution.Analytic.OrderReduction.BDFamComm
import Hironaka.Resolution.Analytic.OrderReduction.BDFamPullback
import Hironaka.Resolution.Analytic.OrderReduction.ClosedEmbeddingPrep
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.OrderReduction.InducedValue
import Hironaka.Resolution.Analytic.OrderReduction.Step22FamFunctoriality
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Theorem 103 (3) in the compatible-family form

Clause (3) of [Kol07, Theorem 103]: for a smooth hypersurface `τ : Y ↪ X` and an ideal sheaf
`J ⊂ 𝒪_Y`, nonzero on every component of `Y`, with `τ_*(𝒪_Y / J) = 𝒪_X / I`, one has
`max-ord I = 1` and `BO_{n,1}(X, I, ∅) = τ_* BMO_{n-1,1}(Y, J, 1, ∅)`. Kollár proves it in
[Kol07, 104, Step 2.4]: `I` contains the local equations of `Y`, so it has order `1` and
`I = W(I)`; with `E = ∅` Step 2.1 does nothing, in Step 2.2 one may choose `H = Y`, and the
statement follows from Lemma 102 (3). This module proves the analytic form for the construction
`BO.BOanFamOfInput` of `BOanFamOfInput.lean`, on every relatively compact open subset, with the
marked family of dimension `n - 1` at the mark `1` in the role of `BMO_{n-1,1}`: the predicate
`CommutesWithClosedEmbeddingsOfEmptyDivisorFam` of `Functor/FamilyClosedEmbedding.lean` asks that
the value on `(M, 𝓘, ∅)` over `U` be the push-forward of the value on `(Y, τ^* 𝓘, ∅)` over the
trace `U ∩ Y`. The finite counterpart is `ClosedEmbedding.lean`.

The argument follows Kollár's step by step.

* The triple `(M, 𝓘, ∅)` lies in `LocalMCClass 1` with `H := Y`, since the ideal sheaf of `Y`
  lies in `𝓘 = D⁰ 𝓘`; the value of the construction, the descent of the local family functor
  along a cover by pieces with maximal contact (`GlobalizeFam.lean`), is therefore the local
  functor's own value (`globalizeFam_fam_eq`), and no cover enters.
* At the mark `1` the tuning is the identity (`AnalyticTriple.tuned_one`), and the hypersurface of
  maximal contact chosen from the class may be replaced by `Y` (`hfStep2SeqFamOn_indep`, the
  independence of Step 2.3).
* Step 2.1 is idle on the empty boundary. To see it, the list of nonempty boundary members is made
  a parameter of Step 2 along the chain of opens (`hfStep2SeqFamAlongList`): over the empty list the
  chain of Step 2.1 is its initial state, and the value of Step 2 on `U` is the value of Step 2.2
  alone (`shrinkAppend_nil`), Lemma 102's family at the single member `Y` of `∅ + Y`, read on the
  reading open of the chain and carried to an open of `M` by the commutation of the Step 2.2
  functor with local analytic isomorphisms.
* Lemma 102's family at the mark `1` on `Y` (`BDanFam_one_eq_pushforwardRestrict`): the first
  centre `Z_{-1}` is empty because `𝓘|_Y` is nonzero everywhere, so the first blow-up is empty and
  deleted, the push-forward is transported along the isomorphism of the empty blow-up, and the
  value of the input family on the restricted triple is its value on `(Y, J, ∅)` pulled back along
  the restricted isomorphism, by its commutation with local analytic isomorphisms and its
  indifference to empty members.
* The push-forward over an open commutes with restriction to a smaller open ([Kol07, 30.3] on each
  open; `pushforwardRestrict_pullback_restrictLE`), and the compatibility of the input family
  carries its value from the trace of the larger open to `U ∩ Y`.

The result gives Theorem 103 (3) at every stage of the order-reduction tower
(`Stage/AllNFam.lean`) and enters the closed-embedding clause of the embedded desingularization
(`Modified/ClauseClosedEmbedding.lean`, `Functor/ChainClosedEmbeddingZero.lean`).
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace AnalyticManifold IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Step 2 along a chain, with the list of members as a parameter -/

namespace BO

open _root_.Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ)
  (hT : AnalyticTriple.BOClass s T) (W : ℕ → Opens M) (l : List T.F.ι)
  (hWsub : ∀ k, k < l.length + 1 → closure (W (k + 1) : Set M) ⊆ W k)
  (d : HFData ψ₀ s) (hW : ∀ k, IsCompact (closure (W k : Set M)))

/-- The state of the chain of Step 2.1 at the next-to-last open, over an arbitrary list `l` of
members of the boundary in place of the list of nonempty members (over data `d`). -/
noncomputable def hfChainList : ChainState T s (W l.length) :=
  step21FamAux T s d.bd₁ hT W (l.length + 1) hW hWsub l (Nat.le_succ _)

variable {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1)
  (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))

/-- Step 2 along a chain of opens with the list of members as a parameter (over data `d`):
`hfStep2SeqFamAlong` (`Step2Along.lean`) with the list of nonempty members of the boundary
replaced by `l`, so that the empty boundary can be substituted. The chain of Step 2.1 over `l` is
restricted to the last open, the value of Step 2.2 over its state (`hfStep22ValueOf`) is appended,
and the result is restricted to `U` with its empty blow-ups deleted. -/
noncomputable def hfStep2SeqFamAlongList (U : Opens M) (hUW : U ≤ W (l.length + 1)) :
    BlowUpSequence ψ₀ (M.restrict U) :=
  (((hfChainList T s hT W l hWsub d hW).L.shrinkAppend
      (M.restrictLE (ChainState.le_of_closure_subset (hWsub l.length (Nat.lt_succ_self _))))
      (isLocalDiffeomorph_restrictLE _)
      (hfStep22ValueOf d T hT hH hle (hfChainList T s hT W l hWsub d hW) (hW _)
        (hWsub l.length (Nat.lt_succ_self _)))).pullback
    (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE _)).eraseEmpty

/-- Step 2 along a chain is Step 2 along the chain over the list of nonempty members, by
definition. -/
theorem hfStep2SeqFamAlong_eq_list
    (hWsub' : ∀ k, k < memberCount T s hT + 1 → closure (W (k + 1) : Set M) ⊆ W k)
    (U : Opens M) (hUW : U ≤ W (memberCount T s hT + 1)) :
    hfStep2SeqFamAlong T s hT W hWsub' d hW hH hle U hUW =
      hfStep2SeqFamAlongList T s hT W (T.F.nonemptyList hT.2.2).reverse hWsub' d hW hH hle U
        hUW :=
  rfl

/-- The value depends on the list only; the hypotheses on the chain are transported. -/
theorem hfStep2SeqFamAlongList_congr_list {l₁ l₂ : List T.F.ι} (e : l₁ = l₂)
    (hWsub₁ : ∀ k, k < l₁.length + 1 → closure (W (k + 1) : Set M) ⊆ W k)
    (hWsub₂ : ∀ k, k < l₂.length + 1 → closure (W (k + 1) : Set M) ⊆ W k)
    (U : Opens M) (hUW₁ : U ≤ W (l₁.length + 1)) (hUW₂ : U ≤ W (l₂.length + 1)) :
    hfStep2SeqFamAlongList T s hT W l₁ hWsub₁ d hW hH hle U hUW₁ =
      hfStep2SeqFamAlongList T s hT W l₂ hWsub₂ d hW hH hle U hUW₂ := by
  subst e
  rfl

end BO


/-! ### The push-forward over an open under restriction and deletion of empty blow-ups -/

variable {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- The trace on a closed submanifold of a smaller open is smaller. -/
theorem _root_.Manifold.IsClosedSubmanifold.preimageOpens_mono (hS : IsClosedSubmanifold ψ S s)
    {U V : Opens M}
    (hUV : U ≤ V) : hS.preimageOpens U ≤ hS.preimageOpens V :=
  fun _ hx => hUV hx

omit [FiniteDimensional 𝕜 E] in
/-- The push-forward of a sequence of centres depends only on the set of the closed submanifold and
on the sequence. -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforward_congr_set {S₁ S₂ : Set M} (eS : S₁ = S₂)
    (h₁ : IsClosedSubmanifold ψ S₁ s) (h₂ : IsClosedSubmanifold ψ S₂ s)
    {L₁ : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) h₁.toAnalyticManifold}
    {L₂ : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) h₂.toAnalyticManifold}
    (hL : HEq L₁ L₂) : L₁.pushforward h₁ = L₂.pushforward h₂ := by
  subst eS
  cases hL
  rfl

omit [FiniteDimensional 𝕜 E] in
/-- The push-forward over an open commutes with restriction to a smaller open ([Kol07, 30.3] on
each open): the push-forward over `V` of a sequence on the trace `V ∩ S`, restricted to `U ≤ V`, is
the push-forward over `U` of the sequence restricted to the trace `U ∩ S`. -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforwardRestrict_pullback_restrictLE
    (hS : IsClosedSubmanifold ψ S s)
    {U V : Opens M} (hUV : U ≤ V)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((hS.toAnalyticManifold).restrict (hS.preimageOpens V))) :
    (BlowUpSequence.pushforwardRestrict hS V L).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV) =
      BlowUpSequence.pushforwardRestrict hS U
        (L.pullback ((hS.toAnalyticManifold).restrictLE (hS.preimageOpens_mono hUV))
          (isLocalDiffeomorph_restrictLE _)) :=
  PushforwardStage.pushforwardAux_pullback (hS.restrictStageOf V _ rfl) (hS.restrictStageOf U _ rfl)
    (M.restrictLE hUV) ((hS.toAnalyticManifold).restrictLE (hS.preimageOpens_mono hUV))
    (isLocalDiffeomorph_restrictLE _) ⟨isLocalDiffeomorph_restrictLE hUV, rfl, fun _ => rfl⟩ L

omit [FiniteDimensional 𝕜 E] in
/-- The push-forward over an open, unfolded: the sequence on the trace `U ∩ S` is carried by the
isomorphism between the trace and the closed submanifold `S ∩ U` of `M|_U`, then pushed forward. -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforwardRestrict_eq
    (hS : IsClosedSubmanifold ψ S s) (U : Opens M)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((hS.toAnalyticManifold).restrict (hS.preimageOpens U))) :
    BlowUpSequence.pushforwardRestrict hS U L =
      (L.pullback ⟨(hS.restrictBundleDiffeomorph U).symm,
          (hS.restrictBundleDiffeomorph U).symm.contMDiff⟩
        (hS.restrictBundleDiffeomorph U).symm.isLocalDiffeomorph).pushforward
        (hS.restrictOpen U) :=
  BlowUpSequence.pushforwardRestrictOf_eq hS U (hS.preimageOpens U) rfl L

omit [FiniteDimensional 𝕜 E] in
/-- The push-forward over an open of a sequence without empty centres has none ([Kol07, 32]). -/
theorem _root_.AnalyticManifold.BlowUpSequence.noEmptyCenters_pushforwardRestrict
    (hS : IsClosedSubmanifold ψ S 1) (U : Opens M)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      ((hS.toAnalyticManifold).restrict (hS.preimageOpens U)))
    (hL : L.NoEmptyCenters) : (BlowUpSequence.pushforwardRestrict hS U L).NoEmptyCenters := by
  rw [BlowUpSequence.pushforwardRestrict_eq]
  exact BlowUpSequence.noEmptyCenters_pushforward_of_bridge (pushforwardBridge ψ) _ _
    (BlowUpSequence.noEmptyCenters_pullback_of_surjective L _ _
      (hS.restrictBundleDiffeomorph U).symm.surjective hL)

omit [FiniteDimensional 𝕜 E] in
/-- Up to the deletion of empty blow-ups, the push-forward over an open does not see the empty
blow-ups of the sequence. -/
theorem _root_.AnalyticManifold.BlowUpSequence.eraseEmpty_pushforwardRestrict_eraseEmpty
    (hS : IsClosedSubmanifold ψ S s)
    (U : Opens M)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((hS.toAnalyticManifold).restrict (hS.preimageOpens U))) :
    (BlowUpSequence.pushforwardRestrict hS U L.eraseEmpty).eraseEmpty =
      (BlowUpSequence.pushforwardRestrict hS U L).eraseEmpty := by
  rw [BlowUpSequence.pushforwardRestrict_eq, BlowUpSequence.pushforwardRestrict_eq]
  have h1 := BlowUpSequence.eraseEmpty_pullback_eraseEmpty L
    ⟨(hS.restrictBundleDiffeomorph U).symm, (hS.restrictBundleDiffeomorph U).symm.contMDiff⟩
    (hS.restrictBundleDiffeomorph U).symm.isLocalDiffeomorph
  rw [← BlowUpSequence.eraseEmpty_pushforward_eraseEmpty (hS.restrictOpen U), h1,
    BlowUpSequence.eraseEmpty_pushforward_eraseEmpty]

/-! ### Lemma 102's family at the mark `1` on a member with empty first centre -/

/-- Lemma 102 (3) in the compatible-family form ([Kol07, Lemma 102 (3)], as used in
[Kol07, 104, Step 2.4]): at the mark `1`, on a member `Y` of the boundary all of whose other
members are empty, with `J := 𝓘|_Y` nonzero everywhere, the value of Lemma 102's family at `Y` on
`U` is the push-forward over `U` of the value of the input family on `(Y, J, ∅)` over the trace
`U ∩ Y`. The first centre `Z_{-1}` is empty (`Zminus1_one_eq_empty_of_isNonzeroEverywhere`), so the
first blow-up is empty and deleted and the push-forward is transported along the isomorphism of
the empty blow-up; the value of the input family on the restricted triple is its value on
`(Y, J, ∅)` pulled back along the restricted isomorphism, by its commutation with local analytic
isomorphisms and its indifference to empty members (the restricted boundary is empty), the ideal
sheaves agreeing because the weak transform by an empty blow-up is the pull-back
(`weakTransformI_eq_comap_of_eq_empty`) and restriction commutes with pull-back
(`pullback_inclusionMap_pullback`). -/
theorem BDanFam_one_eq_pushforwardRestrict (inp₁ : BMOanFam 𝕜 (n - 1) (tuningParam 1))
    {N : AnalyticManifold.{u} 𝕜 E} (X : AnalyticTriple ψ₀ N) (hX : AnalyticTriple.BOClass 1 X)
    (j : X.F.ι) {Y : Set N} (hY : IsClosedSubmanifold ψ₀ Y 1) (hYj : X.F.hyp j = Y)
    (hemp : ∀ k, k ≠ j → X.F.hyp k = ∅)
    (hJ : (X.I.pullback ⇑hY.inclusionMap hY.inclusionMap.contMDiff).IsNonzeroEverywhere)
    (U : Opens N) (hU : IsCompact (closure (U : Set N))) :
    BDanFam 1 inp₁ X hX j U hU =
      BlowUpSequence.pushforwardRestrict hY U
        ((inp₁.functor.fam _ (AnalyticTriple.bmoClass_one_empty _ hJ)).seqOn (hY.preimageOpens U)
          (hY.isCompact_closure_preimageOpens U hU)) := by
  -- the tuning at the mark `1` is the identity on triples; the triple is in Lemma 102's class
  have eX : X.tuned 1 hX.1 = X := AnalyticTriple.tuned_one X
  have hXc : BDan.BDClass 1 X := by
    rw [← eX]
    exact ⟨AnalyticTriple.boClass_tuned hX, AnalyticTriple.isDBalanced_tuned hX⟩
  unfold BDanFam
  refine (BDan.coreFamOn_congr 1 eX j j HEq.rfl inp₁ _ hXc U hU).trans ?_
  -- Lemma 102 at `Y`: the first centre is empty, its blowing-up is an isomorphism
  have hZeq : BD.Zminus1 X.I 1 (X.F.hyp j) = ∅ := by
    rw [hYj]
    exact BD.Zminus1_one_eq_empty_of_isNonzeroEverywhere hY X.I hJ
  set hZ := BD.isClosedSubmanifold_Zminus1 X 1 j with hhZ
  set φd := BlowUpSequence.emptyBlowUpDiffeomorph hZ hZeq with hφd
  set φ : AnalyticMap (blowUp ψ₀ hZ) N := Diffeomorph.toAnalyticMap φd with hφ
  have hφl : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ := φd.isLocalDiffeomorph
  have hfun : ⇑(blowUpπ ψ₀ hZ) = ⇑φ :=
    funext fun p => (BlowUpSequence.emptyBlowUpDiffeomorph_apply hZ hZeq p).symm
  have hφsymm : ∀ y : N, φ (φd.symm y) = y := fun y => φd.apply_symm_apply y
  set hS' := hY.preimage_of_isLocalDiffeomorph hφl with hhS'
  have hSeq : ⇑φ ⁻¹' Y = BDan.transformSOf X j hZ := by
    change ⇑φ ⁻¹' Y = ⇑(blowUpπ ψ₀ hZ) ⁻¹' X.F.hyp j
    rw [hfun]
    exact congrArg (fun S : Set N => ⇑φ ⁻¹' S) hYj.symm
  -- the per-open core over the empty centre and the transported value
  refine (BDan.coreFamOn_eq_coreOfListOf_of_eq X 1 j hZ hS' U inp₁ hXc rfl hSeq hU).trans ?_
  -- the empty centre over `U` and its blowing-up
  set hZU := hZ.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion N U) with hhZU
  have hZUeq : ⇑(N.inclusion U) ⁻¹' BD.Zminus1 X.I 1 (X.F.hyp j) = ∅ := by
    rw [hZeq]
    exact Set.preimage_empty
  set φdU := BlowUpSequence.emptyBlowUpDiffeomorph hZU hZUeq with hφdU
  have hψl : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (Diffeomorph.toAnalyticMap φdU.symm) :=
    φdU.symm.isLocalDiffeomorph
  set hSU := BDan.isClosedSubmanifold_transformSUOf hZ hS' U with hhSU
  set hSU' := hSU.preimage_of_isLocalDiffeomorph hψl with hhSU'
  have key : ∀ x : N.restrict U,
      φ (BlowUpSequence.liftStep (N.inclusion U) (isLocalDiffeomorph_inclusion N U) hZ
        (Diffeomorph.toAnalyticMap φdU.symm x)) = N.inclusion U x := by
    intro x
    rw [← hfun, BlowUpSequence.blowUpπ_liftStep, ← BlowUpSequence.emptyBlowUpDiffeomorph_apply hZU
        hZUeq]
    exact congrArg (fun q => N.inclusion U q) (φdU.apply_symm_apply x)
  -- the restricted isomorphism `φ|_{φ⁻¹Y} : φ⁻¹(Y) → Y` and the target triple `(Y, J, ∅)`
  set g' := hS'.restrictMap hY φ φ.contMDiff (fun _ hx => hx) with hg'def
  have hg' : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω g' :=
    BD.isLocalDiffeomorph_restrictMap φ hφl hY
  set T₁ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) hY.toAnalyticManifold :=
    ⟨X.I.pullback ⇑hY.inclusionMap hY.inclusionMap.contMDiff, hJ, HypersurfaceFamily.empty _,
      HypersurfaceFamily.isSnc_empty⟩ with hT₁
  have hT' : AnalyticTriple.BMOClass 1 T₁ := AnalyticTriple.bmoClass_one_empty _ hJ
  have hT₁' : AnalyticTriple.BMOClass 1 (T₁.pullback g' hg') :=
    AnalyticTriple.bmoClass_pullback hT' g' hg'
  have _e : IsEmpty (T₁.pullback g' hg').F.ι := inferInstanceAs (IsEmpty PEmpty)
  set R := BDan.restrictedTripleOf X 1 j hZ hS' hXc rfl hSeq with hR
  have hRc : AnalyticTriple.BMOClass 1 R :=
    BDan.bmoClass_restrictedTripleOf X 1 j hZ hS' hXc rfl hSeq
  -- the ideal sheaves agree
  have hI : R.I = (T₁.pullback g' hg').I := by
    change (BDan.weakTransformIOf X hZ).pullback ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff =
      T₁.I.pullback g' g'.contMDiff
    rw [show BDan.weakTransformIOf X hZ = BDan.weakTransformI X 1 j from rfl,
      BDan.weakTransformI_eq_comap_of_eq_empty X 1 j hZeq]
    change (X.I.pullback ⇑(blowUpπ ψ₀ hZ) (blowUpπ ψ₀ hZ).contMDiff).pullback _ _ =
      (X.I.pullback ⇑hY.inclusionMap hY.inclusionMap.contMDiff).pullback ⇑g' g'.contMDiff
    rw [IdealSheaf.pullback_congr X.I (blowUpπ ψ₀ hZ).contMDiff φ.contMDiff hfun]
    exact BD.pullback_inclusionMap_pullback φ X.I hY hS'
  -- the members of the restricted boundary are all empty
  have he' : ∀ b, b ∉ Set.range (OrderEmbedding.ofIsEmpty : (T₁.pullback g' hg').F.ι ↪o R.F.ι) →
      R.F.hyp b = ∅ := by
    intro b _
    change hS'.preimageVal (⇑(blowUpπ ψ₀ hZ) ⁻¹' ((X.F.emptyMember j).hyp b)) = ∅
    by_cases hb : b = j
    · rw [hb]
      erw [HypersurfaceFamily.emptyMember_hyp_self X.F j, Set.preimage_empty]
      exact Set.eq_empty_of_forall_notMem fun p hp => hp
    · erw [HypersurfaceFamily.emptyMember_hyp_of_ne X.F hb, hemp b hb, Set.preimage_empty]
      exact Set.eq_empty_of_forall_notMem fun p hp => hp
  -- the trace of `π⁻¹(U)` on the transform maps onto the trace `U_Y`
  set U'S := hS'.preimageOpens (BDan.piOpenOf hZ U) with hU'S
  have hU'Sc : IsCompact (closure (U'S : Set hS'.toAnalyticManifold)) :=
    hS'.isCompact_closure_preimageOpens _ (BDan.isCompact_closure_piOpenOf hZ U hU)
  have himg : ⇑g' '' (U'S : Set hS'.toAnalyticManifold) =
      (hY.preimageOpens U : Set hY.toAnalyticManifold) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      change φ p.1 ∈ U
      exact (congrArg (fun q : N => q ∈ (U : Set N)) (congrFun hfun p.1)).mp hp
    · intro hy
      refine ⟨⟨φd.symm y.1, ?_⟩, ?_, ?_⟩
      · change φ (φd.symm y.1) ∈ Y
        rw [hφsymm]
        exact y.2
      · change blowUpπ ψ₀ hZ (φd.symm y.1) ∈ U
        rw [hfun, hφsymm]
        exact hy
      · exact Subtype.ext (hφsymm y.1)
  -- the input family's value on the restricted triple is the pull-back of its value on `(Y, J, ∅)`
  set V_U := (inp₁.functor.fam T₁ hT').seqOn (hY.preimageOpens U)
    (hY.isCompact_closure_preimageOpens U hU) with hV_U
  set rg' := AnalyticMap.restrictMap g' U'S (hY.preimageOpens U) himg.le with hrg'def
  have hrg' : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω rg' :=
    AnalyticMap.isLocalDiffeomorph_restrictMap hg' U'S (hY.preimageOpens U) himg.le
  have hV : (inp₁.functor.fam R hRc).seqOn U'S hU'Sc = V_U.pullback rg' hrg' := by
    rw [← BlowUpSequence.eraseEmpty_pullback_of_surjective V_U
      ((inp₁.functor.fam T₁ hT').noEmptyCenters _ _) rg' hrg'
      (AnalyticMap.surjective_restrictMap himg),
      ← AnalyticFamilyFunctor.CommutesWithLocalIsos.seqOn_eq_of_image_eq inp₁.commutesWithLocalIsos
        hg' (AnalyticTriple.isPullbackOf_pullback T₁ g' hg') hT' hT₁' hU'Sc
        (hY.isCompact_closure_preimageOpens U hU) himg]
    have eR : R = ⟨(T₁.pullback g' hg').I, (T₁.pullback g' hg').isNonzeroEverywhere, R.F,
        R.isSnc⟩ :=
      AnalyticTriple.ext' hI rfl
    have hR₂ : AnalyticTriple.BMOClass 1 (⟨(T₁.pullback g' hg').I,
        (T₁.pullback g' hg').isNonzeroEverywhere, R.F, R.isSnc⟩ :
          AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) _) := by
      rw [← eR]
      exact hRc
    rw [AnalyticFamilyFunctor.fam_seqOn_congr_triple inp₁.functor eR hRc hR₂]
    exact inp₁.indifferentToEmptyMembers
      (⟨(T₁.pullback g' hg').I, (T₁.pullback g' hg').isNonzeroEverywhere, R.F, R.isSnc⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) _)
      (T₁.pullback g' hg').F (T₁.pullback g' hg').isSnc OrderEmbedding.ofIsEmpty (fun i => i.elim)
      he' hR₂ hT₁' U'S hU'Sc
  -- the transported value is the value on `(Y, J, ∅)` pulled back along the composite
  have hbInv : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (BDan.bundleInvOf hZ hS' U) :=
    (hS'.restrictBundleDiffeomorphOf (BDan.piOpenOf hZ U) (hS'.preimageOpens (BDan.piOpenOf hZ U))
      rfl).symm.isLocalDiffeomorph
  have hlS : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (BDan.liftInclSOf hZ hS' U) :=
    IsClosedSubmanifold.isLocalDiffeomorph_restrictMap (BDan.liftInclOf hZ U)
      (BDan.isLocalDiffeomorph_liftInclOf hZ U) _
  have hF : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      ((rg'.comp (BDan.bundleInvOf hZ hS' U)).comp (BDan.liftInclSOf hZ hS' U)) :=
    BlowUpSequence.isLocalDiffeomorph_comp (BlowUpSequence.isLocalDiffeomorph_comp hrg' hbInv) hlS
  have hTV : BDan.transportedValueOf X 1 j hZ hS' U inp₁ hXc rfl hSeq hU =
      V_U.pullback ((rg'.comp (BDan.bundleInvOf hZ hS' U)).comp (BDan.liftInclSOf hZ hS' U))
        hF := by
    change (((inp₁.functor.fam R hRc).seqOn U'S hU'Sc).pullback (BDan.bundleInvOf hZ hS' U)
      hbInv).pullback (BDan.liftInclSOf hZ hS' U) hlS = _
    rw [hV, BlowUpSequence.pullback_comp _ _ hrg' _ hbInv, BlowUpSequence.pullback_comp _ _ _ _ hlS]
  -- both sides have no empty centres: compare after the empty first blow-up is deleted
  have hR : (BlowUpSequence.pushforwardRestrict hY U V_U).NoEmptyCenters :=
    BlowUpSequence.noEmptyCenters_pushforwardRestrict hY U V_U
      ((inp₁.functor.fam T₁ hT').noEmptyCenters _ _)
  refine Eq.trans ?_ (BlowUpSequence.eraseEmpty_of_noEmptyCenters _ hR)
  set rψ := hSU'.restrictMap hSU (Diffeomorph.toAnalyticMap φdU.symm)
    (Diffeomorph.toAnalyticMap φdU.symm).contMDiff (fun _ hx => hx) with hrψdef
  have hrψ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω rψ :=
    IsClosedSubmanifold.isLocalDiffeomorph_restrictMap (Diffeomorph.toAnalyticMap φdU.symm) hψl hSU
  have hF' : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (((rg'.comp (BDan.bundleInvOf hZ hS' U)).comp (BDan.liftInclSOf hZ hS' U)).comp rψ) :=
    BlowUpSequence.isLocalDiffeomorph_comp hF hrψ
  set bInvY : AnalyticMap (hY.restrictOpen U).toAnalyticManifold
      ((hY.toAnalyticManifold).restrict (hY.preimageOpens U)) :=
    ⟨(hY.restrictBundleDiffeomorph U).symm, (hY.restrictBundleDiffeomorph U).symm.contMDiff⟩
    with hbInvY
  have hbY : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω bInvY :=
    (hY.restrictBundleDiffeomorph U).symm.isLocalDiffeomorph
  -- the transform over `U`, carried back along the empty blow-up, is `Y ∩ U`
  have eS : ⇑(Diffeomorph.toAnalyticMap φdU.symm) ⁻¹' (⇑(BDan.liftInclOf hZ U) ⁻¹'
      (⇑((blowUp ψ₀ hZ).inclusion (BDan.piOpenOf hZ U)) ⁻¹' (⇑φ ⁻¹' Y))) =
      ⇑(N.inclusion U) ⁻¹' Y := by
    ext q
    change φ (BlowUpSequence.liftStep (N.inclusion U) (isLocalDiffeomorph_inclusion N U) hZ
      (Diffeomorph.toAnalyticMap φdU.symm q)) ∈ Y ↔ N.inclusion U q ∈ Y
    rw [key]
  have hf : ∀ (x : N.restrict U) (hx₁ : x ∈ ⇑(Diffeomorph.toAnalyticMap φdU.symm) ⁻¹'
      (⇑(BDan.liftInclOf hZ U) ⁻¹'
        (⇑((blowUp ψ₀ hZ).inclusion (BDan.piOpenOf hZ U)) ⁻¹' (⇑φ ⁻¹' Y))))
      (hx₂ : x ∈ ⇑(N.inclusion U) ⁻¹' Y),
      (((rg'.comp (BDan.bundleInvOf hZ hS' U)).comp (BDan.liftInclSOf hZ hS' U)).comp rψ)
          ⟨x, hx₁⟩ =
        bInvY ⟨x, hx₂⟩ := by
    intro x hx₁ hx₂
    refine Subtype.ext (Subtype.ext ?_)
    exact key x
  -- assemble: delete the empty first blow-up, transport along the empty blow-up's isomorphism
  unfold BDan.coreOfListOf
  rw [BlowUpSequence.eraseEmpty_cons_of_eq_empty hZU _ hZUeq, BlowUpSequence.map_eq_pullback_symm,
    BlowUpSequence.eraseEmpty_pullback _ (Diffeomorph.toAnalyticMap φdU.symm) _ φdU.symm.surjective,
    BlowUpSequence.pushforward_pullback hSU (Diffeomorph.toAnalyticMap φdU.symm) hψl, hTV,
    BlowUpSequence.pullback_comp _ _ _ _ _,
    BlowUpSequence.pushforward_congr_set eS hSU' (hY.restrictOpen U)
      (BDan.heq_pullback_of_heq_bundled eS hSU' (hY.restrictOpen U) V_U _ bInvY hF' hbY hf)]
  exact congrArg BlowUpSequence.eraseEmpty (BlowUpSequence.pushforwardRestrict_eq hY U V_U).symm

end Hironaka.Manifold

namespace Hironaka.Manifold.BO

open _root_.Manifold

/-! ### Step 2 at the mark `1` along a global hypersurface -/

section Global

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} {S : Set M}

/-- **Step 2 at the mark `1` along a global hypersurface of codimension one**, over data `d`
([Kol07, 104, Step 2.4]; [Wlo09, §7.1]): on `(M, 𝓘 ⊇ I_S, ∅)` with `S` a closed hypersurface, if
the family functor of Step 2.2 at the triple of Step 2.2 over the empty sequence is, on every
relatively compact open, the push-forward of a compatible family `C` on `S`, then Step 2 on the
tuned triple is the push-forward of `C` on `U`. The tuning is the identity at the mark `1`
(`tuned_one`, `hfStep2FamOn_congr_triple`), the class's chosen hypersurface is replaced by `S`
(`hfStep2SeqFamOn_indep`), Step 2.1 is idle on the empty boundary (the list-parametrised chain at
`[]`, `shrinkAppend_nil`), and Step 2.2 is read on the chain's open and carried to `U`
(`hfStep22Functor_commutesWithLocalIsos`, `pushforwardRestrict_pullback_restrictLE`, the
compatibility of `C`). -/
theorem hfStep2FamOn_eq_pushforwardRestrict_of_global
    (d : HFData (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (tuningParam 1))
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) S 1)
    (I : AnalyticManifold.IdealSheaf M) (hI : I.IsNonzeroEverywhere) (hle : hS.idealSheaf ≤ I)
    (hL : AnalyticTriple.LocalMCClass 1
      (⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M))
    {T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) hS.toAnalyticManifold}
    (C : CompatibleFamily T')
    (hstep : ∀ hge hsnc hX (W : Opens M) (hW : IsCompact (closure (W : Set M))),
      ((hfStep22Functor d.hf).fam (step22TripleOf (s := tuningParam 1)
          ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ (BlowUpSequence.nil M)
          hge (H := S) hsnc) hX).seqOn W hW =
        BlowUpSequence.pushforwardRestrict hS W
          (C.seqOn (hS.preimageOpens W) (hS.isCompact_closure_preimageOpens W hW)))
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    hfStep2FamOn (tuningParam 1) d _ (AnalyticTriple.localMCClass_tuned hL) U hU =
      BlowUpSequence.pushforwardRestrict hS U
        (C.seqOn (hS.preimageOpens U) (hS.isCompact_closure_preimageOpens U hU)) := by
  have hle0 : hS.idealSheaf ≤ I.iteratedDeriv (1 - 1) := by
    rw [Nat.sub_self, IdealSheaf.iteratedDeriv_zero]
    exact hle
  set T₀ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M :=
    ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ with hT₀
  rw [BO.hfStep2FamOn_congr_triple (tuningParam 1) d (AnalyticTriple.tuned_one T₀)
    (AnalyticTriple.localMCClass_tuned hL) hL U hU]
  unfold BO.hfStep2FamOn
  rw [hfStep2SeqFamOn_indep d T₀ hL.1 U hU _ _ hS hle0,
    BO.hfStep2SeqFamOn_eq_along T₀ (tuningParam 1) hL.1 d hS hle0 U hU,
    BO.hfStep2SeqFamAlong_eq_list T₀ (tuningParam 1) hL.1 _ d _ hS hle0 _ U _]
  set W := chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU)
    (memberCount T₀ (tuningParam 1) hL.1 + 1) with hWdef
  have hW : ∀ k, IsCompact (closure (W k : Set M)) := fun k => isCompact_closure_chainOpens _ _ _ _
  have hmc : memberCount T₀ (tuningParam 1) hL.1 = 0 :=
    congrArg List.length (congrArg List.reverse (HypersurfaceFamily.nonemptyList_empty _))
  have e : (T₀.F.nonemptyList hL.1.2.2).reverse = [] := by
    rw [HypersurfaceFamily.nonemptyList_empty, List.reverse_nil]
  have hWsub₂ : ∀ k, k < ([] : List T₀.F.ι).length + 1 → closure (W (k + 1) : Set M) ⊆ W k :=
    fun k hk => closure_chainOpens_succ_subset _ _ _ (by rw [hmc]; exact hk)
  have h1 : memberCount T₀ (tuningParam 1) hL.1 + 1 = 1 := by omega
  have hUW₂ : U ≤ W 1 := by
    rw [← congrArg W h1]
    exact le_step2OpenV T₀ (tuningParam 1) hL.1 U hU
  refine (BO.hfStep2SeqFamAlongList_congr_list T₀ (tuningParam 1) hL.1 W d hW hS hle0 e _ hWsub₂
    U _ hUW₂).trans ?_
  -- the empty chain on `W 0`: Step 2.1 is idle, Step 2.2 is read at the single member `S ∩ W 0`
  set g₀ := M.inclusion (W 0) with hg₀def
  have hg₀ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g₀ :=
    isLocalDiffeomorph_inclusion M (W 0)
  have hW01 : W 1 ≤ W 0 := fun _ hx => hWsub₂ 0 (Nat.lt_succ_self _) (subset_closure hx)
  have hge₀ : (BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      M).toSuccession.IsOfOrderGe T₀.I (tuningParam 1) T₀.F.idealSheaf :=
    FiniteSuccession.isOfOrderGe_nil _ _ _
  have hsnc₀ : ((exceptionalOf (BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      M)).append (transformHOf (BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜
          (Fin n → 𝕜)) M)
        S)).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) :=
    isSnc_step22BoundaryOf T₀ (tuningParam 1) (BlowUpSequence.nil M) hL.1 hge₀ hS hle0
  set X_M : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M :=
    step22TripleOf T₀ (BlowUpSequence.nil M) hge₀ hsnc₀ with hX_M
  have hX_Ms : stepHClass (tuningParam 1) X_M :=
    stepHClass_step22TripleOf T₀ (tuningParam 1) (BlowUpSequence.nil M) hL.1 hge₀ hsnc₀
  set T₀W := T₀.pullback g₀ hg₀ with hT₀W
  have hT₀Wc : AnalyticTriple.BOClass (tuningParam 1) T₀W :=
    boClass_pullback_inclusion_of_boClass T₀ (W 0) hL.1
  have hge₂ : (BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (M.restrict (W 0))).toSuccession.IsOfOrderGe T₀W.I (tuningParam 1) T₀W.F.idealSheaf :=
    FiniteSuccession.isOfOrderGe_nil _ _ _
  have hsnc₂ : ((exceptionalOf (BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (M.restrict (W 0)))).append
        (transformHOf (BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (M.restrict (W 0))) (⇑g₀ ⁻¹' S))).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) :=
    isSnc_step22BoundaryOf T₀W (tuningParam 1) (BlowUpSequence.nil _) hT₀Wc hge₂
      (hS.preimage_of_isLocalDiffeomorph hg₀)
      (idealSheaf_preimage_le_iteratedDeriv_inclusion T₀ (tuningParam 1) hS hle0 (W 0))
  set T₂ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict (W 0)) :=
    step22TripleOf T₀W (BlowUpSequence.nil _) hge₂ hsnc₂ with hT₂
  have hT₂s : stepHClass (tuningParam 1) T₂ :=
    stepHClass_step22TripleOf T₀W (tuningParam 1) (BlowUpSequence.nil _) hT₀Wc hge₂ hsnc₂
  have hpb : T₂.IsPullbackOf X_M g₀ :=
    step22TripleOf_isPullbackOf T₀ g₀ hg₀ (BlowUpSequence.nil M) hge₀ hge₂ hsnc₀ hsnc₂
  set O : Opens (M.restrict (W 0)) :=
    (BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict
        (W 0))).liftRange
      (M.restrictLE hW01) (isLocalDiffeomorph_restrictLE _) with hO
  have hOc : IsCompact (closure (O : Set (M.restrict (W 0)))) :=
    (BlowUpSequence.nil _).isCompact_closure_liftRange _ _
      (isCompact_closure_range_restrictLE _ (hW 1) (hWsub₂ 0 (Nat.lt_succ_self _)))
  set V₂ := ((hfStep22Functor d.hf).fam T₂ hT₂s).seqOn O hOc with hV₂def
  set c : AnalyticMap (M.restrict (W 1)) ((M.restrict (W 0)).restrict O) :=
    (BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (M.restrict (W 0))).liftCorestrict (M.restrictLE hW01) (isLocalDiffeomorph_restrictLE _)
    with hcdef
  have hc : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω c :=
    BlowUpSequence.isLocalDiffeomorph_liftCorestrict _ _ _
  -- Step 2.1 is idle (`ChainState.init`, definitionally) and the shrink-and-append step of the
  -- empty chain is `shrinkAppend_nil` (a `rfl`): Step 2 on `U` is the Step-2.2 value pulled back
  -- along the corestriction and the inclusion `U ⊆ W 1`
  change ((V₂.pullback c hc).pullback (M.restrictLE hUW₂)
    (isLocalDiffeomorph_restrictLE _)).eraseEmpty = _
  -- Step 2.2 on `W 0` is Step 2.2 on `M` read at `W 1` (`hfStep22Functor_commutesWithLocalIsos`)
  have himg : ⇑g₀ '' (O : Set (M.restrict (W 0))) = (W 1 : Set M) :=
    (congrArg (fun s : Set (M.restrict (W 0)) => (Subtype.val : M.restrict (W 0) → M) '' s)
      (range_restrictLE hW01)).trans
      (Set.image_preimage_eq_of_subset fun x hx => ⟨⟨x, hW01 hx⟩, rfl⟩)
  set rm := AnalyticMap.restrictMap g₀ O (W 1) himg.le with hrmdef
  have hrm : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω rm :=
    AnalyticMap.isLocalDiffeomorph_restrictMap hg₀ O (W 1) himg.le
  have hV₂ : V₂ = ((((hfStep22Functor d.hf).fam X_M hX_Ms).seqOn (W 1) (hW 1)).pullback rm
      hrm).eraseEmpty :=
    AnalyticFamilyFunctor.CommutesWithLocalIsos.seqOn_eq_of_image_eq
      (hfStep22Functor_commutesWithLocalIsos d.hf) hg₀ hpb hX_Ms hT₂s hOc (hW 1) himg
  -- Step 2.2 on `M` is the push-forward of `C` (the hypothesis)
  have hVM : ((hfStep22Functor d.hf).fam X_M hX_Ms).seqOn (W 1) (hW 1) = _ :=
    hstep hge₀ hsnc₀ hX_Ms (W 1) (hW 1)
  -- assemble: the deletions of empty blow-ups, the composite restriction `U ⊆ W 1`, the
  -- push-forward of [Kol07, Definition 30, 30.3] under restriction,
  -- `R`'s compatibility on the traces
  rw [hV₂, hVM]
  have hcr : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      (c.comp (M.restrictLE hUW₂)) :=
    BlowUpSequence.isLocalDiffeomorph_comp hc (isLocalDiffeomorph_restrictLE _)
  have hcomp : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      (rm.comp (c.comp (M.restrictLE hUW₂))) :=
    BlowUpSequence.isLocalDiffeomorph_comp hrm hcr
  have hmap : rm.comp (c.comp (M.restrictLE hUW₂)) = M.restrictLE hUW₂ :=
    ContMDiffMap.ext fun x => Subtype.ext rfl
  rw [BlowUpSequence.pullback_comp _ _ _ _ _, BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _
      hcr,
    BlowUpSequence.pullback_comp _ _ _ _ _,
    BlowUpSequence.pullback_congr _ hmap hcomp (isLocalDiffeomorph_restrictLE hUW₂),
    BlowUpSequence.pushforwardRestrict_pullback_restrictLE hS hUW₂,
    C.compat (hS.preimageOpens U) (hS.preimageOpens (W 1))
      (hS.isCompact_closure_preimageOpens U hU) (hS.isCompact_closure_preimageOpens (W 1) (hW 1))
      (hS.preimageOpens_mono hUW₂)]
  exact (BlowUpSequence.eraseEmpty_pushforwardRestrict_eraseEmpty hS U _).symm.trans
    (BlowUpSequence.eraseEmpty_of_noEmptyCenters _
      (BlowUpSequence.noEmptyCenters_pushforwardRestrict hS U _
        (BlowUpSequence.noEmptyCenters_eraseEmpty _)))

end Global

/-! ### Theorem 103 (3) for the construction -/

variable (𝕜 : Type) [RCLike 𝕜] (n : ℕ)

/-- Theorem 103 (3) in the compatible-family form ([Kol07, Theorem 103 (3)], proved as in
[Kol07, 104, Step 2.4]): the order-reduction structure `BO.BOanFamOfInput 𝕜 n inp` at the mark `1`
commutes with closed embeddings of hypersurfaces when the boundary is empty, through the input
marked family `inp 1` of dimension `n - 1` at the mark `1`: for a closed hypersurface `S ⊆ M`, an
ideal sheaf `𝓘` containing the ideal sheaf of `S` and `J = 𝓘|_S`, the value on `(M, 𝓘, ∅)` over a
relatively compact open `U` is the push-forward over `U` of the value of `inp 1` on `(S, J, ∅)` over
the trace `U ∩ S`. The triple `(M, 𝓘, ∅)` has the global hypersurface of maximal contact `S`, so
the value is the local functor's, Step 2 at the mark `1` along `S`
(`hfStep2FamOn_eq_pushforwardRestrict_of_global`); Step 2.2 there is Lemma 102's family at the
member `S`, the push-forward of the input's value (`BDanFam_one_eq_pushforwardRestrict`). -/
theorem BOanFamOfInput_commutesWithClosedEmbeddingsOfEmptyDivisorFam
    (inp : ∀ s : ℕ, BMOanFam.{u} 𝕜 (n - 1) s) :
    (BOanFamOfInput 𝕜 n inp 1).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := 1)
      (inp 1).functor := by
  intro M S hS I hI J hJ hle hJI hT _ U hU
  subst hJI
  -- the triple `(M, 𝓘, ∅)` is in the local class, with `H := Y`
  have hle0 : hS.idealSheaf ≤ I.iteratedDeriv (1 - 1) := by
    rw [Nat.sub_self, IdealSheaf.iteratedDeriv_zero]
    exact hle
  set T₀ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M :=
    ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ with hT₀
  have hL : AnalyticTriple.LocalMCClass 1 T₀ := ⟨hT, S, hS, hle0⟩
  -- the value of the construction is the local functor's (no descent along a cover: `Y` is a global
  -- hypersurface of maximal contact)
  rw [BO.BOanFamOfInput_functor, AnalyticFamilyFunctor.globalizeFam_fam_eq _ _ T₀ hL,
    BO.localFunctorFam_fam_seqOn]
  -- the tuning at the mark `1` is the identity; Step 2.2 at the single member `Y` of `∅ + Y` is
  -- Lemma 102's family at `Y`, the push-forward of the input's value
  set bd := BO.bdanFamDataOfInput (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) inp with hbd
  refine hfStep2FamOn_eq_pushforwardRestrict_of_global (HFData.ofBDanFamData bd (tuningParam 1)) hS
    I hI hle hL ((inp 1).functor.fam _ (AnalyticTriple.bmoClass_one_empty _ hJ))
    (fun hge hsnc hX W hW => ?_) U hU
  exact ((bd (tuningParam 1)).fam_seqOn_congr (AnalyticTriple.tuned_one _)
    (AnalyticTriple.boClass_tuned hX.1) hX.1 (greatestIdx (stepHClass_tuned hX))
    (toLex (Sum.inr PUnit.unit))
    (heq_of_eq (greatestIdx_eq _ fun k => le_toLex_inr k)) W hW).trans
    (BDanFam_one_eq_pushforwardRestrict (inp 1) _ hX.1 (toLex (Sum.inr PUnit.unit)) hS rfl
      (fun k hk => absurd (HypersurfaceFamily.eq_toLex_inr_of_append_empty S k) hk) hJ W hW)

end Hironaka.Manifold.BO

