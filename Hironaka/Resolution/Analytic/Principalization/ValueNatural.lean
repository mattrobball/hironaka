/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.Assembly
public import Hironaka.Resolution.Analytic.Principalization.DisjoinedNatural
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BDErase
import Hironaka.Resolution.Analytic.Principalization.ShrinkAppendPullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Naturality of the value under pull-back of the list

Kollár's functoriality for smooth morphisms [Kol07, 34.1] with the empty-blow-up convention
[Kol07, 32], for the value built from a list (`valueOf`): if `T''` on the last stage of `π^* L` is
an empty extension of the pull-back of `T'` on the last stage of `L` along the last-stage lift
`π_r` (`IsEmptyExtensionOfPullback`), then the value built from `π^* L` and `T''`, read along `ι`,
is the value built from `L` and `T'`, read along `π ∘ ι`. The input family `BMO_{n,1}` supplies
the two facts about its values that this needs — it is indifferent to empty members and commutes
with local analytic isomorphisms (`IndifferentToEmptyMembers`, `CommutesWithLocalIsos`, both
fields of the structure `BMOanFam`) — combined by `seqOn_eq_of_isEmptyExtensionOfPullback`; the
shrink-and-append step is handled by `pullback_shrinkAppend_eraseEmpty`, and the two reading
opens are compared by the input family's own compatibility clause (the image of the smaller
reading open lies in the larger one, `image_pullbackLiftLast_liftRange_subset`). Used by
`Padding.lean` for the canonicity of the shrinking chain.
-/

public section

universe u

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The value of a family functor is compatible with an equality of triples. -/
theorem AnalyticFamilyFunctor.seqOn_congr
    {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
    (B : AnalyticFamilyFunctor ψ₀ Dom) {M : AnalyticManifold.{u} 𝕜 E} {T₁ T₂ : AnalyticTriple ψ₀ M}
    (e : T₁ = T₂) (h₁ : Dom T₁) (h₂ : Dom T₂) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (B.fam T₁ h₁).seqOn U hU = (B.fam T₂ h₂).seqOn U hU := by
  subst e
  rfl

end General

/-! ### The input family on an empty extension of a pull-back -/

/-- [Kol07, 34.1] with the empty-blow-up convention [Kol07, 32]: the value of `BMO_{n,1}` on a
triple `T'` that is an empty extension of the pull-back of `T` along a local analytic isomorphism
`g` is the pull-back of its value on `T`, read on the image open, with the empty rounds erased —
`IndifferentToEmptyMembers` (the extra empty members do not change the value) followed by
`CommutesWithLocalIsos`. -/
theorem BMOanFam.seqOn_eq_of_isEmptyExtensionOfPullback (bmo : BMOanFam.{u} 𝕜 n 1)
    {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N) (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g)
    (h : T'.IsEmptyExtensionOfPullback T g) (hT : AnalyticTriple.BMOClass 1 T)
    (hT' : AnalyticTriple.BMOClass 1 T') (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))) :
    (bmo.functor.fam T' hT').seqOn U' hU' =
      (((bmo.functor.fam T hT).seqOn (AnalyticMap.imageOpens g hg U')
            (AnalyticMap.isCompact_closure_image g hU')).pullback
          (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
          (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
            Set.Subset.rfl)).eraseEmpty := by
  obtain ⟨hI, e, he⟩ := h
  have hT₃ : AnalyticTriple.BMOClass 1 (⟨T'.I, T'.isNonzeroEverywhere, T.F.comap g,
      HypersurfaceFamily.isSnc_comap T.isSnc g hg⟩ : AnalyticTriple _ N) :=
    ⟨le_rfl, (AnalyticTriple.bmoClass_pullback hT g hg).2⟩
  have hT₃eq : (⟨T'.I, T'.isNonzeroEverywhere, T.F.comap g,
      HypersurfaceFamily.isSnc_comap T.isSnc g hg⟩ : AnalyticTriple _ N) = T.pullback g hg :=
    AnalyticTriple.ext' hI rfl
  rw [bmo.indifferentToEmptyMembers T' (T.F.comap g) (HypersurfaceFamily.isSnc_comap T.isSnc g hg)
      e he.1 he.2 hT' hT₃ U' hU',
    bmo.functor.seqOn_congr hT₃eq hT₃ (AnalyticTriple.bmoClass_pullback hT g hg) U' hU']
  exact bmo.commutesWithLocalIsos T (T.pullback g hg) g hg (T.isPullbackOf_pullback g hg) hT
    (AnalyticTriple.bmoClass_pullback hT g hg) U' hU'

/-! ### The value under pull-back of the list -/

/-- **The value is natural under pull-back of the list** ([Kol07, 34.1]; [Kol07, 32]): the value
built from `π^* L` and a triple `T''` that is an empty extension of the pull-back of `T'` along the
last-stage lift `π_r`, read along `ι`, is the value built from `L` and `T'` read along `π ∘ ι`. -/
theorem valueOf_pullback (bmo : BMOanFam.{u} 𝕜 n 1)
    {X' X N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X')
        (π : AnalyticMap X X')
    (hπ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω π) (ι : AnalyticMap N X)
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι) (ι' : AnalyticMap N X')
    (hι' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι') (hcomp : π.comp ι = ι')
    (hc : IsCompact (closure (Set.range ι))) (hc' : IsCompact (closure (Set.range ι')))
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (L.stage (Fin.last _)))
    (hT' : AnalyticTriple.BMOClass 1 T')
    (T'' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((L.pullback π hπ).stage (Fin.last _)))
    (hT'' : AnalyticTriple.BMOClass 1 T'')
    (h : T''.IsEmptyExtensionOfPullback T' (L.pullbackLiftLast π hπ)) :
    valueOf bmo (L.pullback π hπ) T'' hT'' ι hι hc = valueOf bmo L T' hT' ι' hι' hc' := by
  unfold valueOf
  refine AnalyticManifold.BlowUpSequence.pullback_shrinkAppend_eraseEmpty L π hπ ι hι ι' hι' hcomp
      _ _ ?_
  have hle : AnalyticMap.imageOpens (L.pullbackLiftLast π hπ)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L π hπ)
          ((L.pullback π hπ).liftRange ι hι) ≤
      L.liftRange ι' hι' :=
    AnalyticManifold.BlowUpSequence.image_pullbackLiftLast_liftRange_subset L π hπ ι hι ι' hι' hcomp
  have hU' := (L.pullback π hπ).isCompact_closure_liftRange ι hι hc
  have hV' := L.isCompact_closure_liftRange ι' hι' hc'
  have e1 := bmo.seqOn_eq_of_isEmptyExtensionOfPullback T' T'' _
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L π hπ) h hT' hT'' _ hU'
  have e2 := (bmo.functor.fam T' hT').compat _ _ (AnalyticMap.isCompact_closure_image _ hU') hV' hle
  refine (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty e1).trans ?_
  refine (AnalyticManifold.BlowUpSequence.eraseEmpty_eraseEmpty _).trans ?_
  refine (congrArg (fun Z => (AnalyticManifold.BlowUpSequence.pullback Z
    (AnalyticMap.restrictMap (L.pullbackLiftLast π hπ) _ _ Set.Subset.rfl)
    (AnalyticMap.isLocalDiffeomorph_restrictMap
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L π hπ) _ _
          Set.Subset.rfl)).eraseEmpty)
    e2).trans ?_
  refine (AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _ _).trans ?_
  refine (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
      (AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _)).trans ?_
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ =>
        Subtype.ext rfl) _ _)

end Hironaka.Manifold
