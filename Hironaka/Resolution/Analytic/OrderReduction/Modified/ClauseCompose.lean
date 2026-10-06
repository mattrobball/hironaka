/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseTools
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ComposeInducedFunctor
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.OrderReduction.Step21Functoriality
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The two stop clauses across the composite of two family functors

The modified functor is the composite `composeInduced` of its phases (`ModifiedFam.lean`): on an
open `U` its value is `composeOn`, the composite `alongList` over the canonical pair `(W, V)` of
opens above `U` (the first functor's value on `W` restricted to `V`, followed by the second
functor's value at the induced triple on the lifted range, `shrinkAppend`), pulled back to `U` and
cleaned of its empty blow-ups. This module carries the output clause and the stopped clause of
`ClauseTools.lean` across that construction, statement by statement alongside the order clause of
`ComposeInduced.lean` and `ComposeInducedFunctor.lean` at the mark `1`:

* `BlowUpSequence.outputClause_shrinkAppend`, `stoppedClause_shrinkAppend` (the analogues of
  `isOfOrderGe_shrinkAppend`): the appended value's clause for the induced triple restricted to the
  lifted range pulls back along the corestricted lift to the clause for the induced triple of the
  restricted list (`induced_pullback`), and the concatenation inherits the clause
  (`outputClause_concat`, `stoppedClause_concat`); for the stopped clause the list so far pulls
  back too.
* `alongList_outputClause`, `alongList_stoppedClause` (the analogues of `alongList_isOfOrderGe`):
  the composite over `(W, V)` from the second functor's output clause, resp. both functors'
  stopped clauses, the restricted triple rewritten by `pullback_inclusion_restrictLE`.
* `composeOn_outputClause`, `composeOn_stoppedClause` (the analogues of `composeOn_isOfOrderGe`):
  the pull-back to `U` (`outputClause_pullback`, `stoppedClause_pullback`) and the deletion of the
  empty blow-ups (`outputClause_eraseEmpty`, `stoppedClause_eraseEmpty`).
* `composeInduced_outputClauseFam`, `composeInduced_stoppedClauseFam`: the clauses of the
  composite functor. The output clause needs only the second functor's (the last stage is its);
  the stopped clause needs both.

Sources: the phases in succession per open in the proof of [Wlo09, Theorem 7.4.1];
[Kol07, 104, Step 2.1] and [Kol07, 34.1] for the concatenation of blow-up sequences and the
deletion of empty blow-ups. The statements themselves are not in the sources.
-/

public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)

/-- The chain step keeps the output clause (the analogue of `isOfOrderGe_shrinkAppend`): the
appended value's clause for the induced triple restricted to the lifted range pulls back along the
corestricted lift (`outputClause_pullback`) to the clause for the induced triple of the restricted
list (`induced_pullback`), and the concatenation has the clause (`outputClause_concat`). -/
theorem outputClause_shrinkAppend (T : AnalyticTriple ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe T.I 1 T.F.idealSheaf)
    (L' : BlowUpSequence ψ₀ ((L.stage (Fin.last _)).restrict (L.liftRange h hh)))
    (hL' : L'.toSuccession.IsOfOrderGe
      ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).I 1
      ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf)
    (hP' : L'.toSuccession.OutputClause ψ₀
      ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).I
      ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).F) :
    (L.shrinkAppend h hh L').toSuccession.OutputClause ψ₀ (T.pullback h hh).I
      (T.pullback h hh).F := by
  have hL₁ := T.isOfOrderGe_pullback 1 L hL h hh
  have e : ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).pullback (L.liftCorestrict h hh)
        (L.isLocalDiffeomorph_liftCorestrict h hh) =
      (T.pullback h hh).induced 1 (L.pullback h hh) hL₁ := by
    rw [AnalyticTriple.pullback_pullback _ _ _ _ _,
      AnalyticTriple.pullback_eq_of_eq _ (inclusion_comp_liftCorestrict L h hh) _
        (isLocalDiffeomorph_pullbackLiftLast L h hh)]
    exact AnalyticTriple.induced_pullback T 1 L hL h hh hL₁
  have hP₂ := outputClause_pullback ψ₀ L' (L.liftCorestrict h hh)
    (L.isLocalDiffeomorph_liftCorestrict h hh) _ hL' hP'
  rw [e] at hP₂
  unfold shrinkAppend
  exact outputClause_concat ψ₀ (L.pullback h hh) _ (T.pullback h hh) hL₁ hP₂

/-- The chain step keeps the stopped clause: the list so far pulls back (`stoppedClause_pullback`),
the appended value pulls back along the corestricted lift to the induced triple of the restricted
list, and the concatenation has the clause (`stoppedClause_concat`). -/
theorem stoppedClause_shrinkAppend (T : AnalyticTriple ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe T.I 1 T.F.idealSheaf)
    (hP : L.toSuccession.StoppedClause ψ₀ T.I T.F)
    (L' : BlowUpSequence ψ₀ ((L.stage (Fin.last _)).restrict (L.liftRange h hh)))
    (hL' : L'.toSuccession.IsOfOrderGe
      ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).I 1
      ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf)
    (hP' : L'.toSuccession.StoppedClause ψ₀
      ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).I
      ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).F) :
    (L.shrinkAppend h hh L').toSuccession.StoppedClause ψ₀ (T.pullback h hh).I
      (T.pullback h hh).F := by
  have hL₁ := T.isOfOrderGe_pullback 1 L hL h hh
  have e : ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion (L.liftRange h hh))
        (isLocalDiffeomorph_inclusion _ _)).pullback (L.liftCorestrict h hh)
        (L.isLocalDiffeomorph_liftCorestrict h hh) =
      (T.pullback h hh).induced 1 (L.pullback h hh) hL₁ := by
    rw [AnalyticTriple.pullback_pullback _ _ _ _ _,
      AnalyticTriple.pullback_eq_of_eq _ (inclusion_comp_liftCorestrict L h hh) _
        (isLocalDiffeomorph_pullbackLiftLast L h hh)]
    exact AnalyticTriple.induced_pullback T 1 L hL h hh hL₁
  have hP₁ := stoppedClause_pullback ψ₀ L h hh T hL hP
  have hP₂ := stoppedClause_pullback ψ₀ L' (L.liftCorestrict h hh)
    (L.isLocalDiffeomorph_liftCorestrict h hh) _ hL' hP'
  rw [e] at hP₂
  unfold shrinkAppend
  exact stoppedClause_concat ψ₀ (L.pullback h hh) _ (T.pullback h hh) hL₁ hP₁ hP₂

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace AnalyticFamilyFunctor

open _root_.Manifold

variable {Dom₁ Dom₂ : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
  (F : AnalyticFamilyFunctor ψ₀ Dom₁) (G : AnalyticFamilyFunctor ψ₀ Dom₂)
  (hF : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))),
    ((F.fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf)
  (hFG : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))),
    Dom₂ ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).induced 1
      ((F.fam T hT).seqOn U hU) (hF T hT U hU)))

section Along

omit [FiniteDimensional 𝕜 E]

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T)
  (W : Opens M) (hW : IsCompact (closure (W : Set M))) (V : Opens M)
  (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)

/-- The output clause of the composite over `(W, V)` from that of `G` (the analogue of
`alongList_isOfOrderGe`): `outputClause_shrinkAppend` with the order clause of `G` and its output
clause at the induced triple on the lifted range, the restricted triple rewritten by
`pullback_inclusion_restrictLE`. -/
theorem alongList_outputClause
    (hGo : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ N) (hT' : Dom₂ T')
      (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
      ((G.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
    (hG1 : G.OutputClauseFam ψ₀) :
    (alongList F G 1 hF hFG T hT W hW V hV hVW).toSuccession.OutputClause ψ₀
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).I
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).F := by
  have h := (firstList F T hT W hW).outputClause_shrinkAppend
    (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
    (firstTriple T W) (hF T hT W hW) (appendValue F G 1 hF hFG T hT W hW V hV hVW)
    (hGo (inducedOfFirst F 1 hF T hT W hW) (hFG T hT W hW) (firstReadOpen F T hT W hW V hVW)
      (isCompact_closure_firstReadOpen F T hT W hW V hV hVW))
    (hG1 (inducedOfFirst F 1 hF T hT W hW) (hFG T hT W hW) (firstReadOpen F T hT W hW V hVW)
      (isCompact_closure_firstReadOpen F T hT W hW V hV hVW))
  rwa [AnalyticTriple.pullback_inclusion_restrictLE T (ChainState.le_of_closure_subset hVW)] at h

/-- The stopped clause of the composite over `(W, V)` from those of `F` and `G`
(`stoppedClause_shrinkAppend`). -/
theorem alongList_stoppedClause
    (hGo : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ N) (hT' : Dom₂ T')
      (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
      ((G.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
    (hF8 : F.StoppedClauseFam ψ₀) (hG8 : G.StoppedClauseFam ψ₀) :
    (alongList F G 1 hF hFG T hT W hW V hV hVW).toSuccession.StoppedClause ψ₀
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).I
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).F := by
  have h := (firstList F T hT W hW).stoppedClause_shrinkAppend
    (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
    (firstTriple T W) (hF T hT W hW) (hF8 T hT W hW) (appendValue F G 1 hF hFG T hT W hW V hV hVW)
    (hGo (inducedOfFirst F 1 hF T hT W hW) (hFG T hT W hW) (firstReadOpen F T hT W hW V hVW)
      (isCompact_closure_firstReadOpen F T hT W hW V hV hVW))
    (hG8 (inducedOfFirst F 1 hF T hT W hW) (hFG T hT W hW) (firstReadOpen F T hT W hW V hVW)
      (isCompact_closure_firstReadOpen F T hT W hW V hV hVW))
  rwa [AnalyticTriple.pullback_inclusion_restrictLE T (ChainState.le_of_closure_subset hVW)] at h

end Along

/-- The output clause of the composite's value on `U` (the analogue of `composeOn_isOfOrderGe`): the
composite over the canonical pair pulled back to `U` (`outputClause_pullback`,
`pullback_inclusion_restrictLE`) and cleaned of its empty blow-ups (`outputClause_eraseEmpty`). -/
theorem composeOn_outputClause
    (hGo : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ N) (hT' : Dom₂ T')
      (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
      ((G.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
    (hG1 : G.OutputClauseFam ψ₀) {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : Dom₁ T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (composeOn F G 1 hF hFG T hT U hU).toSuccession.OutputClause ψ₀
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F := by
  have hge₀ := alongList_isOfOrderGe F G 1 hF hFG T hT
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 0)
    (isCompact_closure_chainOpens _ _ _ _)
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1)
    (isCompact_closure_chainOpens _ _ _ _) (closure_chainOpens_succ_subset _ _ _ Nat.zero_lt_one)
    hGo
  have hge := AnalyticTriple.isOfOrderGe_pullback
    (T.pullback (M.inclusion (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1))
      (isLocalDiffeomorph_inclusion M _)) 1 _ hge₀
    (M.restrictLE (le_chainOpens_last (exhaustion M) hU 1)) (isLocalDiffeomorph_restrictLE _)
  have h := AnalyticManifold.BlowUpSequence.outputClause_pullback ψ₀ _
    (M.restrictLE (le_chainOpens_last (exhaustion M) hU 1)) (isLocalDiffeomorph_restrictLE _)
    (T.pullback (M.inclusion (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1))
      (isLocalDiffeomorph_inclusion M _)) hge₀
    (alongList_outputClause F G hF hFG T hT _ (isCompact_closure_chainOpens _ _ _ _) _
      (isCompact_closure_chainOpens _ _ _ _) (closure_chainOpens_succ_subset _ _ _ Nat.zero_lt_one)
      hGo hG1)
  rw [AnalyticTriple.pullback_inclusion_restrictLE T (le_chainOpens_last (exhaustion M) hU 1)]
    at h hge
  exact AnalyticManifold.BlowUpSequence.outputClause_eraseEmpty ψ₀ _ _ hge h

/-- The stopped clause of the composite's value on `U` (`stoppedClause_pullback`,
`stoppedClause_eraseEmpty`). -/
theorem composeOn_stoppedClause
    (hGo : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ N) (hT' : Dom₂ T')
      (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
      ((G.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
    (hF8 : F.StoppedClauseFam ψ₀) (hG8 : G.StoppedClauseFam ψ₀) {M : AnalyticManifold.{u} 𝕜 E}
    (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (composeOn F G 1 hF hFG T hT U hU).toSuccession.StoppedClause ψ₀
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F := by
  have hge₀ := alongList_isOfOrderGe F G 1 hF hFG T hT
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 0)
    (isCompact_closure_chainOpens _ _ _ _)
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1)
    (isCompact_closure_chainOpens _ _ _ _) (closure_chainOpens_succ_subset _ _ _ Nat.zero_lt_one)
    hGo
  have hge := AnalyticTriple.isOfOrderGe_pullback
    (T.pullback (M.inclusion (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1))
      (isLocalDiffeomorph_inclusion M _)) 1 _ hge₀
    (M.restrictLE (le_chainOpens_last (exhaustion M) hU 1)) (isLocalDiffeomorph_restrictLE _)
  have h := AnalyticManifold.BlowUpSequence.stoppedClause_pullback ψ₀ _
    (M.restrictLE (le_chainOpens_last (exhaustion M) hU 1)) (isLocalDiffeomorph_restrictLE _)
    (T.pullback (M.inclusion (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1))
      (isLocalDiffeomorph_inclusion M _)) hge₀
    (alongList_stoppedClause F G hF hFG T hT _ (isCompact_closure_chainOpens _ _ _ _) _
      (isCompact_closure_chainOpens _ _ _ _) (closure_chainOpens_succ_subset _ _ _ Nat.zero_lt_one)
      hGo hF8 hG8)
  rw [AnalyticTriple.pullback_inclusion_restrictLE T (le_chainOpens_last (exhaustion M) hU 1)]
    at h hge
  exact AnalyticManifold.BlowUpSequence.stoppedClause_eraseEmpty ψ₀ _ _ hge h

variable (hFc : F.CommutesWithLocalIsos) (hG : G.CommutesWithLocalIsos)
  (hG' : G.IndifferentToEmptyMembers) (hDom : ClassPullbackClosed (ψ₀ := ψ₀) Dom₂)
  (hDomE : ClassInducedEraseEmptyClosed (ψ₀ := ψ₀) 1 Dom₂)
  (hDom₁ : ClassPullbackClosed (ψ₀ := ψ₀) Dom₁)

/-- The output clause of the composite functor (the analogue of `composeInduced_isOfOrderGe`). -/
theorem composeInduced_outputClauseFam
    (hGo : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ N) (hT' : Dom₂ T')
      (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
      ((G.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
    (hG1 : G.OutputClauseFam ψ₀) :
    (composeInduced F G 1 hF hFG hFc hG hG' hDom hDomE hDom₁).OutputClauseFam ψ₀ := by
  unfold OutputClauseFam
  intro M T hT U hU
  exact composeOn_outputClause F G hF hFG hGo hG1 T hT U hU

/-- The stopped clause of the composite functor from the stopped clauses of both functors. -/
theorem composeInduced_stoppedClauseFam
    (hGo : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ N) (hT' : Dom₂ T')
      (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
      ((G.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
    (hF8 : F.StoppedClauseFam ψ₀) (hG8 : G.StoppedClauseFam ψ₀) :
    (composeInduced F G 1 hF hFG hFc hG hG' hDom hDomE hDom₁).StoppedClauseFam ψ₀ := by
  unfold StoppedClauseFam
  intro M T hT U hU
  exact composeOn_stoppedClause F G hF hFG hGo hF8 hG8 T hT U hU

end AnalyticFamilyFunctor

end Hironaka.Manifold

end
