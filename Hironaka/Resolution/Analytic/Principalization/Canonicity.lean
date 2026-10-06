/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.Assembly
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
import Hironaka.Resolution.Analytic.Principalization.DisjoinBoundary
import Hironaka.Resolution.Analytic.Principalization.DisjoinNatural
import Hironaka.Resolution.Analytic.Principalization.Padding
import Hironaka.Resolution.Analytic.Principalization.ValueNatural
import Hironaka.Resolution.Analytic.Principalization.ValueRestrict
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Independence of the shrinking open; the principalization family functor

The value of the principalization family on a relatively compact open `U` was defined with a
shrinking open `W ⊇ closure U` (`principalizationValueOn`,
`Hironaka/Resolution/Analytic/Principalization/Assembly.lean`). This module proves it does not
depend on `W` and assembles the compatible family and the family functor:

* `principalizationValueOn_eq_of_le`: for `W ≤ W'`, the disjoining list over `W'` pulled back to
  `W` is the disjoining list over `W` at the (larger) bound of `W'` (`disjoinList_pullback`,
  `AnalyticTriple.pullback_inclusion_restrictLE`), so the value at `W'` is the value at `W`
  computed with that bound (`valueOf_pullback`, the disjoined triple being natural under
  pull-back), which is the value at `W`'s own bound by padding with empty blow-ups
  (`valueOf_disjoinList_eq`);
* `principalizationValueOn_eq`: two arbitrary shrinking opens compare through their union;
* `principalizationValue_compat`: the values on `U ≤ V` compare at the common shrinking open of
  `V` (`principalizationValueOn_restrict`) — the compatibility of the family under restriction
  (Kollár's functoriality for open embeddings [Kol07, 34.1]; Włodarczyk's compatibility of the
  factorizations over nested opens [Wlo09, Theorem 2.0.3 (4)]);
* `principalizationFam`: the family functor on all triples (`Dom := fun _ => True`).
-/

@[expose] public section

universe u

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-! ### Transports along equalities of the base triple and the list -/

/-- Transport of the snc hypothesis on the boundary along equalities of the list and the family. -/
theorem isSnc_totalTransformSeqFrom_last_congr₂ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
    {L₁ L₂ : AnalyticManifold.BlowUpSequence ψ₀ M} (eL : L₁ = L₂) {F₁ F₂ : HypersurfaceFamily M}
        (eF : F₁ = F₂)
    (h : (L₁.toSuccession.totalTransformSeqFrom F₁ (Fin.last _)).IsSnc ψ₀) :
    (L₂.toSuccession.totalTransformSeqFrom F₂ (Fin.last _)).IsSnc ψ₀ := by
  subst eL
  subst eF
  exact h

/-- Transport of the disjointness hypothesis on the original members along equalities of the list
and the family. -/
theorem meetLocus_two_subfamily_original_congr₂ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
    {L₁ L₂ : AnalyticManifold.BlowUpSequence ψ₀ M} (eL : L₁ = L₂) {F₁ F₂ : HypersurfaceFamily M}
        (eF : F₁ = F₂)
    (h : ((L₁.toSuccession.totalTransformSeqFrom F₁ (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L₁.toSuccession.originalIdx F₁ (Fin.last _)))).meetLocus 2 = ∅) :
    ((L₂.toSuccession.totalTransformSeqFrom F₂ (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L₂.toSuccession.originalIdx F₂ (Fin.last _)))).meetLocus 2 = ∅ := by
  subst eL
  subst eF
  exact h

/-- The value built from the disjoined triple is compatible with equalities of the base triple and
of the list. -/
theorem valueOf_disjoinedTripleOf_congr₂ (bmo : BMOanFam.{u} 𝕜 n 1)
    {X N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    {T₁ T₂ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X} (eT : T₁ = T₂)
    {L₁ L₂ : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X}
        (eL : L₁ = L₂)
    (h₁ : (L₁.toSuccession.totalTransformSeqFrom T₁.F (Fin.last _)).IsSnc _)
    (h₁' : ((L₁.toSuccession.totalTransformSeqFrom T₁.F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L₁.toSuccession.originalIdx T₁.F (Fin.last _)))).meetLocus 2 = ∅)
    (h₂ : (L₂.toSuccession.totalTransformSeqFrom T₂.F (Fin.last _)).IsSnc _)
    (h₂' : ((L₂.toSuccession.totalTransformSeqFrom T₂.F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L₂.toSuccession.originalIdx T₂.F (Fin.last _)))).meetLocus 2 = ∅)
    (ι : AnalyticMap N X) (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
    (hc : IsCompact (closure (Set.range ι))) :
    valueOf bmo L₁ (disjoinedTripleOf T₁ L₁ h₁ h₁') (disjoinedTripleOf_bmoClass T₁ L₁ h₁ h₁') ι hι
        hc =
      valueOf bmo L₂ (disjoinedTripleOf T₂ L₂ h₂ h₂') (disjoinedTripleOf_bmoClass T₂ L₂ h₂ h₂') ι hι
        hc := by
  subst eT
  subst eL
  rfl

variable {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-! ### Canonicity of the shrinking open -/

/-- **The value does not depend on the shrinking open**, for `W ≤ W'`: the disjoining list over
`W'` pulled back to `W` is the disjoining list over `W` at `W'`'s bound; the value at `W'` is the
value at `W` with that bound (`valueOf_pullback`), which is the value at `W`'s own bound
(`valueOf_disjoinList_eq`). -/
theorem principalizationValueOn_eq_of_le (bmo : BMOanFam.{u} 𝕜 n 1)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) {U W W' : Opens M}
    (hU : IsCompact (closure (U : Set M))) (hW : IsCompact (closure (W : Set M)))
    (hW' : IsCompact (closure (W' : Set M))) (hUW : closure (U : Set M) ⊆ (W : Set M))
    (hUW' : closure (U : Set M) ⊆ (W' : Set M)) (hWW' : W ≤ W') :
    principalizationValueOn bmo T U hU W hW hUW =
      principalizationValueOn bmo T U hU W' hW' hUW' := by
  have hcomp : (M.restrictLE hWW').comp (M.restrictLE (subset_closure.trans hUW)) =
      M.restrictLE (subset_closure.trans hUW') :=
    ContMDiffMap.ext fun _ => Subtype.ext rfl
  have hT : (restrictTriple T W').pullback (M.restrictLE hWW')
      (isLocalDiffeomorph_restrictLE hWW') = restrictTriple T W :=
    T.pullback_inclusion_restrictLE hWW'
  have hk' : (restrictTriple T W).F.meetLocus (disjoinBound T W' + 1) = ∅ := by
    have h := meetLocus_disjoinBound_eq_empty T W' hW'
    rw [← hT]
    change ((restrictTriple T W').F.comap (M.restrictLE hWW')).meetLocus _ = ∅
    rw [HypersurfaceFamily.meetLocus_comap, h, Set.preimage_empty]
  have hL : (disjoinListOn T W' hW').pullback (M.restrictLE hWW')
      (isLocalDiffeomorph_restrictLE hWW') =
      disjoinList (disjoinBound T W') (restrictTriple T W).F (restrictTriple T W).isSnc hk' := by
    rw [disjoinList_pullback]
    exact disjoinList_congr (congrArg AnalyticTriple.F hT) _ _ _ _ _
  have h₂ := isSnc_totalTransformSeqFrom_last_congr₂ hL.symm (congrArg AnalyticTriple.F hT).symm
    (disjoinList_isSnc_totalTransformSeqFrom _ _ _ hk' (Fin.last _))
  have h₂' := meetLocus_two_subfamily_original_congr₂ hL.symm (congrArg AnalyticTriple.F hT).symm
    (meetLocus_two_subfamily_original_eq_empty _ _ _ hk')
  unfold principalizationValueOn
  symm
  refine (valueOf_pullback bmo (disjoinListOn T W' hW') (M.restrictLE hWW')
    (isLocalDiffeomorph_restrictLE hWW') (M.restrictLE (subset_closure.trans hUW))
    (isLocalDiffeomorph_restrictLE _) (M.restrictLE (subset_closure.trans hUW'))
    (isLocalDiffeomorph_restrictLE _) hcomp (isCompact_closure_range_restrictLE _ hU hUW)
    (isCompact_closure_range_restrictLE _ hU hUW')
    (disjoinedTriple (restrictTriple T W') (meetLocus_disjoinBound_eq_empty T W' hW'))
    (disjoinedTriple_bmoClass _ _)
    (disjoinedTripleOf ((restrictTriple T W').pullback (M.restrictLE hWW')
      (isLocalDiffeomorph_restrictLE hWW'))
      ((disjoinListOn T W' hW').pullback (M.restrictLE hWW') (isLocalDiffeomorph_restrictLE hWW'))
      h₂ h₂')
    (disjoinedTripleOf_bmoClass _ _ _ _)
    (AnalyticManifold.BlowUpSequence.isEmptyExtensionOfPullback_disjoinedTripleOf_pullback _ _ _ _
        _ _ h₂
      h₂')).symm.trans ?_
  refine (valueOf_disjoinedTripleOf_congr₂ bmo hT hL h₂ h₂'
    (disjoinList_isSnc_totalTransformSeqFrom _ _ _ hk' (Fin.last _))
    (meetLocus_two_subfamily_original_eq_empty _ _ _ hk') _ _ _).trans ?_
  exact valueOf_disjoinList_eq bmo (restrictTriple T W) _ _ _ _ _ hk'
    (meetLocus_disjoinBound_eq_empty T W hW)

/-- **The value does not depend on the shrinking open**: two admissible shrinking opens compare
through their union. -/
theorem principalizationValueOn_eq (bmo : BMOanFam.{u} 𝕜 n 1)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) {U W W' : Opens M}
    (hU : IsCompact (closure (U : Set M))) (hW : IsCompact (closure (W : Set M)))
    (hW' : IsCompact (closure (W' : Set M))) (hUW : closure (U : Set M) ⊆ (W : Set M))
    (hUW' : closure (U : Set M) ⊆ (W' : Set M)) :
    principalizationValueOn bmo T U hU W hW hUW =
      principalizationValueOn bmo T U hU W' hW' hUW' := by
  have hWW' : IsCompact (closure ((W ⊔ W' : Opens M) : Set M)) := by
    rw [Opens.coe_sup, closure_union]
    exact hW.union hW'
  have hU₁ : closure (U : Set M) ⊆ ((W ⊔ W' : Opens M) : Set M) := by
    rw [Opens.coe_sup]
    exact hUW.trans Set.subset_union_left
  exact (principalizationValueOn_eq_of_le bmo T hU hW hWW' hUW hU₁ le_sup_left).trans
    (principalizationValueOn_eq_of_le bmo T hU hW' hWW' hUW' hU₁ le_sup_right).symm

/-! ### The compatible family and the functor -/

/-- **The compatibility clause of the principalization family** ([Kol07, 34.1];
[Wlo09, Theorem 2.0.3 (4)], per open): the value on `U ≤ V` is the value on `V` pulled back along
the open inclusion with the empty rounds deleted. Both values are computed at the shrinking open of
`V` (`principalizationValueOn_eq`), where they restrict (`principalizationValueOn_restrict`). -/
theorem principalizationValue_compat (bmo : BMOanFam.{u} 𝕜 n 1)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U V : Opens M)
    (hU : IsCompact (closure (U : Set M))) (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V) :
    principalizationValue bmo T U hU =
      ((principalizationValue bmo T V hV).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  have hUV' : closure (U : Set M) ⊆ (shrinkOpen V hV : Set M) :=
    (closure_mono fun x hx => hUV hx).trans (closure_subset_shrinkOpen V hV)
  unfold principalizationValue
  rw [principalizationValueOn_eq bmo T hU (isCompact_closure_shrinkOpen U hU)
    (isCompact_closure_shrinkOpen V hV) (closure_subset_shrinkOpen U hU) hUV']
  exact principalizationValueOn_restrict bmo T hU hV (isCompact_closure_shrinkOpen V hV) hUV'
    (closure_subset_shrinkOpen V hV) hUV

/-- **The principalization family functor** on all triples ([Kol07, Theorem 35] built as in
[Kol07, 72], in the compatible-family form): the value on each relatively compact open is
`principalizationValue` (no empty centres; compatible under restriction). -/
noncomputable def principalizationFam (bmo : BMOanFam.{u} 𝕜 n 1) :
    AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (fun _ => True) where
  fam T _ :=
    { seqOn := fun U hU => principalizationValue bmo T U hU
      noEmptyCenters := fun U hU => noEmptyCenters_principalizationValue bmo T U hU
      compat := fun U V hU hV hUV => principalizationValue_compat bmo T U V hU hV hUV }

theorem principalizationFam_seqOn (bmo : BMOanFam.{u} 𝕜 n 1)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : True) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    ((principalizationFam bmo).fam T hT).seqOn U hU = principalizationValue bmo T U hU := rfl

end Hironaka.Manifold
