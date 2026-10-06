/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step2Along
public import Hironaka.Resolution.Analytic.OrderReduction.LocalFunctorComm
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
import Hironaka.Resolution.Analytic.Functor.EraseEmptyOrder
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Step2LinkPrep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The link of Step 2.2 along a local analytic isomorphism

`ChainTransport.lean` transports one link of the chain of Step 2.1 along a local analytic
isomorphism `h` with `h(W') ⊆ W`: the relation "the sequence over `W'` with its empty blow-ups
deleted is the pull-back of the sequence over `W` with its empty blow-ups deleted" is preserved by a
link. Step 2 appends one more link, the value of the family functor of Step 2.2 at the triple of
Step 2.2 over the chain's sequence, read on the lifted range of the last restriction (`step22FamOn`;
over a state of the chain, `hfStep22ValueOf` of `Step2Along.lean`). This module is the same
transport for that link, an instance of the general transport of a link along a value functor
(`ValueTransport.lean`) for the value functor "the family functor of Step 2.2 at the triple of
Step 2.2"; it is what makes the value of Step 2 independent of the chain of opens
(`Step2Assembly.lean`) and commute with local analytic isomorphisms (`Step2AssemblyComm.lean`), the
analytic form of the functoriality clause of Step 2.3 of the proof of Theorem 103
([Kol07, 104, Step 2.3]; [Kol07, 34.1]).

* `BO.hfStep22Value_rel` — the comparison of the two appended values:
  `BlowUpSequence.valueTransport_rel` with the naturality of the value functor supplied by
  `hfStep22Fam_seqOn_eraseEmpty`, `hfStep22Fam_seqOn_pullback_liftRange` and
  `hfStep22Fam_seqOn_congr` of `Step2LinkPrep.lean` (in place of `fam_seqOn_induced_eraseEmpty`,
  `fam_seqOn_induced_pullback_liftRange`, `fam_seqOn_induced_pullback_congr` of `linkValue_rel`);
* `BO.hfStep22Link_rel` — the relation is preserved by the link of Step 2.2
  (`ChainState.shrinkAppend_rel_of_value_rel`, the value over `W'` read at the pulled-back triple by
  `hfStep22Fam_seqOn_congr_triple`).

The `hf…` declarations are the general forms over data `d : HFData ψ₀ s` of Step 2
(`HFamData.lean`); the plain forms are their instances at Lemma 102's data.
-/

public section
universe u

open Set Topology TopologicalSpace Hironaka.Local
open scoped Manifold ContDiff

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {s : ℕ}

namespace BO

open _root_.Manifold

variable (bd : ∀ s : ℕ, BDanFamData ψ₀ s) (d : HFData ψ₀ s)

/-- The value of the family functor of Step 2.2 depends only on the triple (a substitution; over
data `d`). -/
theorem hfStep22Fam_seqOn_congr_triple {X : AnalyticManifold.{u} 𝕜 E} {X₁ X₂ : AnalyticTriple ψ₀ X}
    (e : X₁ = X₂) (h₁ : stepHClass s X₁) (h₂ : stepHClass s X₂) (U : Opens X)
    (hU : IsCompact (closure (U : Set X))) :
    ((hfStep22Functor d.hf).fam X₁ h₁).seqOn U hU =
      ((hfStep22Functor d.hf).fam X₂ h₂).seqOn U hU := by
  subst e
  rfl

omit [FiniteDimensional 𝕜 E] in
/-- The triple of Step 2.2 depends only on the triple and the sequence (a substitution). -/
theorem step22TripleOf_congr_triple {X : AnalyticManifold.{u} 𝕜 E} {T₁ T₂ : AnalyticTriple ψ₀ X}
    (e : T₁ = T₂) {H : Set X} (L : AnalyticManifold.BlowUpSequence ψ₀ X)
    (hL₁ : L.toSuccession.IsOfOrderGe T₁.I s T₁.F.idealSheaf)
    (hL₂ : L.toSuccession.IsOfOrderGe T₂.I s T₂.F.idealSheaf)
    (hsnc₁ : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀)
    (hsnc₂ : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀) :
    step22TripleOf T₁ L hL₁ hsnc₁ = step22TripleOf T₂ L hL₂ hsnc₂ := by
  subst e
  rfl

section ValueRel

variable {M N P Q : AnalyticManifold.{u} 𝕜 E} (T₁ : AnalyticTriple ψ₀ M)
  (hT₁ : AnalyticTriple.BOClass s T₁) {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1)
  (hle : hH.idealSheaf ≤ T₁.I.iteratedDeriv (s - 1)) (hW : AnalyticMap N M)
  (hhW : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hW)
  (hT₂ : AnalyticTriple.BOClass s (T₁.pullback hW hhW)) (L₁ : AnalyticManifold.BlowUpSequence ψ₀ M)
  (hL₁ : L₁.toSuccession.IsOfOrderGe T₁.I s T₁.F.idealSheaf)
  (ρ : AnalyticMap P M) (hρ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ)
  (ρ' : AnalyticMap Q N) (hρ' : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ')
  (hV : AnalyticMap Q P) (hhV : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hV)
  (hsq : ρ.comp hV = hW.comp ρ')

include hsq in
/-- The comparison of the two appended values of Step 2.2 (`linkValue_rel` for the link of
Step 2.2; over data `d`): for sequences `L₂` on `N` and `L₁` on `M` whose cleaned forms agree after
pulling `L₁` back along `hW`, the value of the family functor of Step 2.2 at the triple of Step 2.2
over `L₂` on the reading open of `ρ'`, and its value at the triple of Step 2.2 over `L₁` on the
reading open of `ρ`, both pulled back to the common cleaned last stage of the restricted sequences
and with their empty blow-ups deleted, agree. The general `valueTransport_rel` with the naturality
of the value functor: `hfStep22Fam_seqOn_eraseEmpty` (both are the value at the triple of Step 2.2
over the common cleaned sequence), `hfStep22Fam_seqOn_pullback_liftRange` (on the `L₁` side) and
`hfStep22Fam_seqOn_congr` (the substitution along `hrel`). -/
theorem hfStep22Value_rel (L₂ : AnalyticManifold.BlowUpSequence ψ₀ N)
    (hL₂ : L₂.toSuccession.IsOfOrderGe (T₁.pullback hW hhW).I s (T₁.pullback hW hhW).F.idealSheaf)
    (hrel : L₂.eraseEmpty = (L₁.pullback hW hhW).eraseEmpty)
    (hO₁ : IsCompact (closure (L₁.liftRange ρ hρ : Set (L₁.stage (Fin.last _)))))
    (hO₂ : IsCompact (closure (L₂.liftRange ρ' hρ' : Set (L₂.stage (Fin.last _)))))
    (hρ'c : IsCompact (closure (Set.range ρ')))
    (e₀ : (L₁.pullback ρ hρ).pullback hV hhV = (L₁.pullback hW hhW).pullback ρ' hρ')
    (hA : (L₂.pullback ρ' hρ').eraseEmpty = ((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmpty)
    (hκ₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm)))
    (hκ₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      (((L₁.liftCorestrict ρ hρ).comp ((L₁.pullback ρ hρ).pullbackLiftLast hV hhV)).comp
        (Diffeomorph.toAnalyticMap ((AnalyticManifold.BlowUpSequence.stageOfEq e₀).trans
          (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
            (AnalyticManifold.BlowUpSequence.stageOfEq hA.symm))).symm))) :
    ((((hfStep22Functor d.hf).fam (step22TripleOf (T₁.pullback hW hhW) L₂ hL₂
          (isSnc_step22BoundaryOf _ s L₂ hT₂ hL₂ (hH.preimage_of_isLocalDiffeomorph hhW)
            (T₁.idealSheaf_preimage_le_iteratedDeriv_pullback hW hhW hH hle)))
        (stepHClass_step22TripleOf _ s L₂ hT₂ hL₂ _)).seqOn (L₂.liftRange ρ' hρ') hO₂).pullback
      ((L₂.liftCorestrict ρ' hρ').comp
        (Diffeomorph.toAnalyticMap (L₂.pullback ρ' hρ').eraseEmptyLast.symm)) hκ₂).eraseEmpty =
    ((((hfStep22Functor d.hf).fam (step22TripleOf T₁ L₁ hL₁
          (isSnc_step22BoundaryOf T₁ s L₁ hT₁ hL₁ hH hle))
        (stepHClass_step22TripleOf T₁ s L₁ hT₁ hL₁ _)).seqOn (L₁.liftRange ρ hρ) hO₁).pullback
      (((L₁.liftCorestrict ρ hρ).comp ((L₁.pullback ρ hρ).pullbackLiftLast hV hhV)).comp
        (Diffeomorph.toAnalyticMap ((AnalyticManifold.BlowUpSequence.stageOfEq e₀).trans
          (((L₁.pullback hW hhW).pullback ρ' hρ').eraseEmptyLast.trans
            (AnalyticManifold.BlowUpSequence.stageOfEq hA.symm))).symm)) hκ₁).eraseEmpty := by
  -- the maximal-contact data of the pulled-back triple
  have hH' : IsClosedSubmanifold ψ₀ (⇑hW ⁻¹' H) 1 := hH.preimage_of_isLocalDiffeomorph hhW
  have hle' := T₁.idealSheaf_preimage_le_iteratedDeriv_pullback hW hhW hH hle
  -- the pulled-back list, its order clause and its reading open
  have hP : (L₁.pullback hW hhW).toSuccession.IsOfOrderGe (T₁.pullback hW hhW).I s
      (T₁.pullback hW hhW).F.idealSheaf := AnalyticTriple.isOfOrderGe_pullback T₁ s L₁ hL₁ hW hhW
  have hOP : IsCompact (closure ((L₁.pullback hW hhW).liftRange ρ' hρ' :
      Set ((L₁.pullback hW hhW).stage (Fin.last _)))) :=
    (L₁.pullback hW hhW).isCompact_closure_liftRange ρ' hρ' hρ'c
  -- the erased lists' order clauses
  have hL₂e := AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty L₂ (T₁.pullback hW hhW).I s
    (T₁.pullback hW hhW).isSnc hL₂
  have hPe := AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty (L₁.pullback hW hhW)
      (T₁.pullback hW hhW).I s
    (T₁.pullback hW hhW).isSnc hP
  exact AnalyticManifold.BlowUpSequence.valueTransport_rel L₁ L₂ hW hhW ρ hρ ρ' hρ' hV hhV hsq e₀
    hA hκ₂ hκ₁
    (hfStep22Fam_seqOn_eraseEmpty d (T₁.pullback hW hhW) hH' L₂ hL₂
      (isSnc_step22BoundaryOf _ s L₂ hT₂ hL₂ hH' hle') (stepHClass_step22TripleOf _ s L₂ hT₂ hL₂ _)
      hL₂e (isSnc_step22BoundaryOf _ s L₂.eraseEmpty hT₂ hL₂e hH' hle')
      (stepHClass_step22TripleOf _ s L₂.eraseEmpty hT₂ hL₂e _) (L₂.liftRange ρ' hρ') hO₂)
    (hfStep22Fam_seqOn_eraseEmpty d (T₁.pullback hW hhW) hH' (L₁.pullback hW hhW) hP
      (isSnc_step22BoundaryOf _ s (L₁.pullback hW hhW) hT₂ hP hH' hle')
      (stepHClass_step22TripleOf _ s (L₁.pullback hW hhW) hT₂ hP _) hPe
      (isSnc_step22BoundaryOf _ s (L₁.pullback hW hhW).eraseEmpty hT₂ hPe hH' hle')
      (stepHClass_step22TripleOf _ s (L₁.pullback hW hhW).eraseEmpty hT₂ hPe _)
      ((L₁.pullback hW hhW).liftRange ρ' hρ') hOP)
    (hfStep22Fam_seqOn_pullback_liftRange d T₁ hW hhW L₁ hL₁
      (isSnc_step22BoundaryOf T₁ s L₁ hT₁ hL₁ hH hle) (stepHClass_step22TripleOf T₁ s L₁ hT₁ hL₁ _)
      hP (isSnc_step22BoundaryOf _ s (L₁.pullback hW hhW) hT₂ hP hH' hle')
      (stepHClass_step22TripleOf _ s (L₁.pullback hW hhW) hT₂ hP _) ρ hρ ρ' hρ' hV hsq hO₁ hOP)
    fun hf₁ hf₂ => hfStep22Fam_seqOn_congr d (T₁.pullback hW hhW) hrel hL₂e hPe
      (isSnc_step22BoundaryOf _ s L₂.eraseEmpty hT₂ hL₂e hH' hle')
      (isSnc_step22BoundaryOf _ s (L₁.pullback hW hhW).eraseEmpty hT₂ hPe hH' hle')
      (stepHClass_step22TripleOf _ s L₂.eraseEmpty hT₂ hL₂e _)
      (stepHClass_step22TripleOf _ s (L₁.pullback hW hhW).eraseEmpty hT₂ hPe _) _ _ _ _
      (AnalyticManifold.BlowUpSequence.mem_imageOpens_eraseEmptyLast_liftRange_iff L₁ L₂ hW hhW ρ'
        hρ' hrel) _ _ hf₁ hf₂
      (AnalyticManifold.BlowUpSequence.stageOfEq_eraseEmptyLast_liftCorestrict_apply L₁ L₂ hW hhW
        ρ' hρ' hrel hA hκ₂)

end ValueRel

section Link

variable {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
  (hT : AnalyticTriple.BOClass s T) {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1)
  (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))

variable (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
  (hT' : AnalyticTriple.BOClass s (T.pullback h hh))

/-- The relation "the sequence over `W'` with its empty blow-ups deleted is the pull-back of the
sequence over `W` with its empty blow-ups deleted", along a local analytic isomorphism `h` with
`h(W') ⊆ W`, is preserved by the link of Step 2.2, for smaller opens `V ⊆ W`, `V' ⊆ W'` with
`h(V') ⊆ V` ([Kol07, 34.1]; `link_rel` for this link; over data `d`). The general
`ChainState.shrinkAppend_rel_of_value_rel`; the two appended values are compared by
`hfStep22Value_rel` after reading the value over `W'` at the pulled-back triple
(`hfStep22Fam_seqOn_congr_triple`). -/
theorem hfStep22Link_rel {W : Opens M} {W' : Opens N} (hWW' : ⇑h '' (W' : Set N) ⊆ W)
    (st : ChainState T s W) (st' : ChainState (T.pullback h hh) s W')
    (hrel : st'.L.eraseEmpty = (st.L.pullback (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).eraseEmpty)
    {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)
    {V' : Opens N} (hV' : IsCompact (closure (V' : Set N))) (hV'W' : closure (V' : Set N) ⊆ W')
    (hVV' : ⇑h '' (V' : Set N) ⊆ V) :
    (st'.L.shrinkAppend (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
      (isLocalDiffeomorph_restrictLE _)
      (hfStep22ValueOf d (T.pullback h hh) hT' (hH.preimage_of_isLocalDiffeomorph hh)
        (T.idealSheaf_preimage_le_iteratedDeriv_pullback h hh hH hle) st' hV' hV'W')).eraseEmpty =
    ((st.L.shrinkAppend (M.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE _) (hfStep22ValueOf d T hT hH hle st hV hVW)).pullback
      (AnalyticMap.restrictMap h V' V hVV')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')).eraseEmpty := by
  have hTWeq := ChainState.triple_pullback_restrictMap_eq T h hh hWW'
  have hT₂ := ChainState.boClass_triple_pullback_restrictMap T s h hh hT' hWW'
  have hL₂ := ChainState.isOfOrderGe_triple_pullback_restrictMap T s h hh hWW' st'
  -- the Step-2.2 value over `W'`, read at the pulled-back triple
  have hF₂ : hfStep22ValueOf d (T.pullback h hh) hT' (hH.preimage_of_isLocalDiffeomorph hh)
      (T.idealSheaf_preimage_le_iteratedDeriv_pullback h hh hH hle) st' hV' hV'W' =
      ((hfStep22Functor d.hf).fam (step22TripleOf ((T.pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).pullback (AnalyticMap.restrictMap h W' W hWW')
          (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')) st'.L hL₂
          (isSnc_step22BoundaryOf _ s st'.L hT₂ hL₂
            ((hH.preimage_of_isLocalDiffeomorph
              (isLocalDiffeomorph_inclusion M W)).preimage_of_isLocalDiffeomorph
              (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW'))
            ((T.pullback (M.inclusion W)
              (isLocalDiffeomorph_inclusion M W)).idealSheaf_preimage_le_iteratedDeriv_pullback
              (AnalyticMap.restrictMap h W' W hWW')
              (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')
              (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M W))
              (idealSheaf_preimage_le_iteratedDeriv_inclusion T s hH hle W))))
        (stepHClass_step22TripleOf _ s st'.L hT₂ hL₂ _)).seqOn
        (st'.L.liftRange (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
          (isLocalDiffeomorph_restrictLE _))
        (st'.L.isCompact_closure_liftRange (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
          (isLocalDiffeomorph_restrictLE _)
          (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hV'W') hV'
            hV'W')) :=
    hfStep22Fam_seqOn_congr_triple d
      (step22TripleOf_congr_triple hTWeq.symm st'.L st'.hge hL₂ _ _) _ _ _ _
  refine ChainState.shrinkAppend_rel_of_value_rel h hh hWW' hVW hV'W' hVV' st st' hrel
    (hfStep22ValueOf d T hT hH hle st hV hVW)
    (hfStep22ValueOf d (T.pullback h hh) hT' (hH.preimage_of_isLocalDiffeomorph hh)
      (T.idealSheaf_preimage_le_iteratedDeriv_pullback h hh hH hle) st' hV' hV'W')
    fun hκ₂ hκ₁ => ?_
  exact (congrArg (fun X : AnalyticManifold.BlowUpSequence ψ₀ ((st'.L.stage
      (Fin.last _)).restrict
      (st'.L.liftRange (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
        (isLocalDiffeomorph_restrictLE _))) => (X.pullback
          ((st'.L.liftCorestrict (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
            (isLocalDiffeomorph_restrictLE _)).comp (Diffeomorph.toAnalyticMap
            (st'.L.pullback (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
              (isLocalDiffeomorph_restrictLE _)).eraseEmptyLast.symm)) hκ₂).eraseEmpty) hF₂).trans
    (hfStep22Value_rel d (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
      (boClass_pullback_inclusion_of_boClass T W hT)
      (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M W))
      (idealSheaf_preimage_le_iteratedDeriv_inclusion T s hH hle W)
      (AnalyticMap.restrictMap h W' W hWW')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW') hT₂ st.L st.hge
      (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
      (N.restrictLE (ChainState.le_of_closure_subset hV'W')) (isLocalDiffeomorph_restrictLE _)
      (AnalyticMap.restrictMap h V' V hVV')
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')
      (ChainState.restrictLE_comp_restrictMap h hWW' hVW hV'W' hVV') st'.L hL₂ hrel
      (st.L.isCompact_closure_liftRange (M.restrictLE (ChainState.le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _)
        (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hVW) hV hVW))
      (st'.L.isCompact_closure_liftRange (N.restrictLE (ChainState.le_of_closure_subset hV'W'))
        (isLocalDiffeomorph_restrictLE _)
        (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hV'W') hV' hV'W'))
      (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hV'W') hV' hV'W')
      (ChainState.pullback_restrictLE_pullback_restrictMap h hh hWW' hVW hV'W' hVV' st)
      (ChainState.eraseEmpty_pullback_restrictLE h hh hWW' hV'W' st st' hrel) hκ₂ hκ₁)

end Link

end BO

end Hironaka.Manifold
