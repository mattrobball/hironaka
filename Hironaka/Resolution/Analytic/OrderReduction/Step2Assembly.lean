/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step2Along
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Resolution.Analytic.OrderReduction.ChainIndep
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.Step21FamIndep
import Hironaka.Resolution.Analytic.OrderReduction.Step2LinkTransport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2 on an open: independence of the chain and compatibility under restriction

The value of Step 2 on a relatively compact open `U` (`step2SeqFamOn`, `Step22Fam.lean`) is Step 2
along the chain of exhaustion opens (`hfStep2SeqFamOn_eq_along`, `Step2Along.lean`): the chain of
Step 2.1 with the value of Step 2.2 appended at the last link, restricted to `U`, with its empty
blow-ups deleted. This module proves that the value does not depend on the admissible chain of
opens, and derives the compatibility of the values under restriction, the clause (4) of
[Wlo09, Theorem 2.0.3] that makes them a compatible family:

* `BO.hfStep2SeqFamAlong_rel` — along two admissible chains the two values of Step 2 agree on every
  common open: the chains of Step 2.1 agree on the intersection of the next-to-last opens
  (`step21FamAux_filter_rel`, `ChainIndep.lean`); the link of Step 2.2 on each chain is compared,
  through the state over that intersection, with the link on the other (`hfStep22Link_rel` along the
  identity, `Step2LinkTransport.lean`), the two intermediate links being the same sequence; then
  both are restricted to the common open (`eraseEmpty_pullback_restrict_congr`).
* `hfStep2SeqFamOn_compat` — for `U ≤ V`, the value of Step 2 on `U` is the value on `V` restricted
  to `U` with its empty blow-ups deleted: independence of the chain, for the chain of `V` read on
  `U`. This is the second clause of [Kol07, 34.1] (pull-back along an open embedding, up to empty
  blow-ups) in the per-open form, the counterpart for Step 2 of `step21FamOn_compat`
  (`Step21FamIndep.lean`).

The `hf…` declarations are the general forms over data `d : HFData ψ₀ s` of Step 2
(`HFamData.lean`); the plain forms are their instances at Lemma 102's data. The compatibility is
the field `compat` of the compatible family of the local functor (`LocalFunctorFam.lean`).
-/

public section

universe u

open Set Topology TopologicalSpace Hironaka.Local
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {s : ℕ}

namespace BO

open _root_.Manifold

variable (bd : ∀ s : ℕ, BDanFamData ψ₀ s) (d : HFData ψ₀ s) (T : AnalyticTriple ψ₀ M)
  (hT : AnalyticTriple.BOClass s T) {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1)
  (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))

/-- Along two admissible chains of opens the values of Step 2 agree on every common open
([Kol07, 34.1] for the choice of the chain; over data `d`): the chains of Step 2.1 agree on the
intersection of the next-to-last opens (`step21FamAux_filter_rel`, applied to the same list of
members); the link of Step 2.2 on each chain is compared, through the state over that intersection
(`restrictEraseId`), with the link on the other (`hfStep22Link_rel` along the identity; the two
intermediate links are the same sequence); then both are restricted to the common open
(`eraseEmpty_pullback_restrict_congr`). -/
theorem hfStep2SeqFamAlong_rel (W : ℕ → Opens M)
    (hWsub : ∀ k, k < memberCount T s hT + 1 → closure (W (k + 1) : Set M) ⊆ W k)
    (hW : ∀ k, IsCompact (closure (W k : Set M))) (W' : ℕ → Opens M)
    (hWsub' : ∀ k, k < memberCount T s hT + 1 → closure (W' (k + 1) : Set M) ⊆ W' k)
    (hW' : ∀ k, IsCompact (closure (W' k : Set M))) (U : Opens M)
    (hU₁ : U ≤ W (memberCount T s hT + 1)) (hU₂ : U ≤ W' (memberCount T s hT + 1)) :
    hfStep2SeqFamAlong T s hT W hWsub d hW hH hle U hU₁ =
      hfStep2SeqFamAlong T s hT W' hWsub' d hW' hH hle U hU₂ := by
  -- the two chain states at the next-to-last opens agree on their intersection
  have ih := ChainState.step21FamAux_filter_rel T s d.bd₁ hT W (memberCount T s hT + 1) hW hWsub
    W' (memberCount T s hT + 1) hW' hWsub' (T.F.nonemptyList hT.2.2).reverse _
    (nonemptyList_reverse_hnil T hT d.bd₁) (nonemptyList_reverse_filter T hT) (Nat.le_succ _)
    (Nat.le_succ _) (W (memberCount T s hT) ⊓ W' (memberCount T s hT)) inf_le_left inf_le_right
  have hT_id : AnalyticTriple.BOClass s
      (T.pullback ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) :=
    AnalyticTriple.boClass_of_isPullbackOf hT
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)
      (AnalyticTriple.isPullbackOf_pullback _ _ _)
  have hI' : IsCompact (closure ((W (memberCount T s hT + 1) ⊓ W' (memberCount T s hT + 1) :
      Opens M) : Set M)) :=
    (hW _).of_isClosed_subset isClosed_closure (closure_mono inf_le_left)
  have hI'I : closure ((W (memberCount T s hT + 1) ⊓ W' (memberCount T s hT + 1) : Opens M) :
      Set M) ⊆ (W (memberCount T s hT) ⊓ W' (memberCount T s hT) : Opens M) := by
    rw [Opens.coe_inf, Opens.coe_inf]
    exact Set.subset_inter
      ((closure_mono Set.inter_subset_left).trans (closure_chainLast_subset T s hT W hWsub))
      ((closure_mono Set.inter_subset_right).trans (closure_chainLast_subset T s hT W' hWsub'))
  -- the virtual state over the intersection and its relations to the two chains
  have hrel₁ : ((hfStep2FamChainAlong T s hT W hWsub d hW).restrictEraseId T s
      (inf_le_left : W (memberCount T s hT) ⊓ W' (memberCount T s hT) ≤
        W (memberCount T s hT))).L.eraseEmpty =
      ((hfStep2FamChainAlong T s hT W hWsub d hW).L.pullback
        (AnalyticMap.restrictMap ContMDiffMap.id _ _ (ChainState.image_id_subset inf_le_left))
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
          (ChainState.image_id_subset inf_le_left))).eraseEmpty :=
    AnalyticManifold.BlowUpSequence.eraseEmpty_eraseEmpty _
  have hrel₂ : ((hfStep2FamChainAlong T s hT W hWsub d hW).restrictEraseId T s
      (inf_le_left : W (memberCount T s hT) ⊓ W' (memberCount T s hT) ≤
        W (memberCount T s hT))).L.eraseEmpty =
      ((hfStep2FamChainAlong T s hT W' hWsub' d hW').L.pullback
        (AnalyticMap.restrictMap ContMDiffMap.id _ _ (ChainState.image_id_subset inf_le_right))
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
          (ChainState.image_id_subset inf_le_right))).eraseEmpty :=
    hrel₁.trans ((congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
        (AnalyticManifold.BlowUpSequence.pullback_congr
      (hfStep2FamChainAlong T s hT W hWsub d hW).L (ContMDiffMap.ext fun _ => rfl) _
      (isLocalDiffeomorph_restrictLE inf_le_left))).trans
      (ih.trans (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
          (AnalyticManifold.BlowUpSequence.pullback_congr
        (hfStep2FamChainAlong T s hT W' hWsub' d hW').L (ContMDiffMap.ext fun _ => rfl)
        (isLocalDiffeomorph_restrictLE inf_le_right) _))))
  -- the Step-2.2 link on both chains, through the virtual state
  have h₁ := hfStep22Link_rel d T hT hH hle ContMDiffMap.id
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)
    hT_id (ChainState.image_id_subset inf_le_left) (hfStep2FamChainAlong T s hT W hWsub d hW) _
    hrel₁ (hW _) (closure_chainLast_subset T s hT W hWsub) hI' hI'I
    (ChainState.image_id_subset inf_le_left)
  have h₂ := hfStep22Link_rel d T hT hH hle ContMDiffMap.id
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)
    hT_id (ChainState.image_id_subset inf_le_right) (hfStep2FamChainAlong T s hT W' hWsub' d hW') _
    hrel₂ (hW' _) (closure_chainLast_subset T s hT W' hWsub') hI' hI'I
    (ChainState.image_id_subset inf_le_right)
  -- the two appended chains agree on the intersection of the last opens, hence on `U`
  have hI : (((hfStep2FamChainAlong T s hT W hWsub d hW).L.shrinkAppend
      (M.restrictLE (chainLast_le T s hT W hWsub)) (isLocalDiffeomorph_restrictLE _)
      (hfStep22FamOnAlong T s hT W hWsub d hW hH hle)).pullback
      (M.restrictLE (inf_le_left : W (memberCount T s hT + 1) ⊓ W' (memberCount T s hT + 1) ≤
        W (memberCount T s hT + 1))) (isLocalDiffeomorph_restrictLE _)).eraseEmpty =
      (((hfStep2FamChainAlong T s hT W' hWsub' d hW').L.shrinkAppend
        (M.restrictLE (chainLast_le T s hT W' hWsub')) (isLocalDiffeomorph_restrictLE _)
        (hfStep22FamOnAlong T s hT W' hWsub' d hW' hH hle)).pullback
        (M.restrictLE (inf_le_right : W (memberCount T s hT + 1) ⊓ W' (memberCount T s hT + 1) ≤
          W' (memberCount T s hT + 1))) (isLocalDiffeomorph_restrictLE _)).eraseEmpty :=
    (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
        (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => rfl)
      (isLocalDiffeomorph_restrictLE inf_le_left)
      (AnalyticMap.isLocalDiffeomorph_restrictMap
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
        (ChainState.image_id_subset inf_le_left)))).trans
      (h₁.symm.trans (h₂.trans (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
          (AnalyticManifold.BlowUpSequence.pullback_congr _
        (ContMDiffMap.ext fun _ => rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
          (ChainState.image_id_subset inf_le_right))
        (isLocalDiffeomorph_restrictLE inf_le_right)))))
  unfold hfStep2SeqFamAlong
  exact AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_restrict_congr _ _ inf_le_left
      inf_le_right
    (le_inf hU₁ hU₂) hI

end BO

/-- Compatibility of Step 2 under restriction ([Wlo09, Theorem 2.0.3 (4)]; the second clause of
[Kol07, 34.1] per open; over data `d`): for `U ≤ V` the value on `U` is the value on `V` restricted
to `U` with its empty blow-ups deleted, by the independence of the chain
(`hfStep2SeqFamAlong_rel`) for the chain of `V` read on `U`. -/
theorem hfStep2SeqFamOn_compat (d : HFData ψ₀ s) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass s T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1) (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))
    {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V) :
    BO.hfStep2SeqFamOn T s d hT U hU hH hle =
      ((BO.hfStep2SeqFamOn T s d hT V hV hH hle).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  have h := BO.hfStep2SeqFamAlong_rel d T hT hH hle
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) (memberCount T s hT + 1))
    (fun _ hk => closure_chainOpens_succ_subset _ _ _ hk) (isCompact_closure_chainOpens _ _ _)
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hV) (memberCount T s hT + 1))
    (fun _ hk => closure_chainOpens_succ_subset _ _ _ hk) (isCompact_closure_chainOpens _ _ _)
    U (BO.le_step2OpenV T s hT U hU) (hUV.trans (BO.le_step2OpenV T s hT V hV))
  rw [BO.hfStep2SeqFamOn_eq_along T s hT d hH hle U hU,
    BO.hfStep2SeqFamOn_eq_along T s hT d hH hle V hV, h]
  unfold BO.hfStep2SeqFamAlong
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
      AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => rfl) _ _)

end Hironaka.Manifold
