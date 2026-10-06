/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bFamily
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.OrderReduction.BDErase
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bCommute
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bEmpty
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial phase as a family functor: commutation and indifference

The monomial phase (`step2bFam`, `Step2bFamily.lean`) packaged as a **family functor** on the marked
class `BMOClass 1` (`AnalyticFamilyFunctor`), with the two properties on each open that the
assembly of the modified algorithm asks of it:

* `step2bFunctor_commutesWithLocalIsos`, the two conditions of [Kol07, 34.1] in one clause per open
  (the functoriality of [Wlo09, Theorem 2.0.2 (4)]): for a local analytic isomorphism `g : N → M`
  and a triple `T'` carrying the pull-back data of `T`, the value on a relatively compact `U' ⊆ N`
  is the pull-back along `g|_{U'} : U' → g(U')` of the value on `g(U')`, with the empty blow-ups
  deleted. This is `step2bPhase_pullback_eraseEmpty` applied to the restricted triple `T|_{g(U')}`
  and the restricted map `g|_{U'}`, the two restrictions composing to the restriction of `T'` to
  `U'` (`pullback_pullback`), the fuels reconciled as in the compatibility of `step2bFam`.
* `step2bFunctor_indifferentToEmptyMembers`, the counterpart, for boundary members, of the empty
  blow-up convention [Kol07, 32], on each open: deleting empty boundary members does not change any
  value. The restricted boundaries differ by
  an empty extension (`IsEmptyExtension`), the phase is indifferent to it at equal fuel
  (`step2bPhase_eq_of_isEmptyExtension`, `Step2bEmpty.lean`), and the two fuels give the same
  complete phase (`step2bPhase_eq_of_step2bMeasure_le'`; the measure of the smaller boundary is at
  most the measure of the larger, `step2bMeasure_le_of_isEmptyExtension`).

The module ends with the support clause: the centres of the phase lie in the support of the current
controlled transform, as [Wlo09, Definition 3.2.4 (1)] requires of a multiple test blow-up.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BD

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜))

/-- **The monomial phase as a family functor** on the marked class `BMOClass 1`: the compatible
family `step2bFam` for every triple of the class. -/
def step2bFunctor : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.BMOClass 1) where
  fam := fun T hT => step2bFam T hT

variable {ψ₀}

theorem step2bFunctor_fam {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BMOClass 1 T) : (step2bFunctor ψ₀).fam T hT = step2bFam T hT := rfl

/-- [Kol07, 34.1] (the functoriality of [Wlo09, Theorem 2.0.2 (4)]), on each open: **the monomial
phase commutes with local analytic isomorphisms**, by `step2bPhase_pullback_eraseEmpty` on the
restricted triple along the restricted map, the restriction of the pull-back being the pull-back of
the restriction. -/
theorem step2bFunctor_commutesWithLocalIsos : (step2bFunctor ψ₀).CommutesWithLocalIsos := by
  intro M N T T' g hg hpb hT hT' U' hU'
  obtain rfl : T' = T.pullback g hg :=
    AnalyticTriple.IsPullbackOf.eq hpb (T.isPullbackOf_pullback g hg)
  rw [step2bFunctor_fam, step2bFunctor_fam, step2bFam_seqOn]
  -- the two restrictions compose to the restriction of the pull-back: `inclusion ∘ g|_{U'} =
  -- g ∘ inclusion` pointwise (`restrictMap_apply`), so both are pull-backs of `T` along one map
  have hmap : (M.inclusion (AnalyticMap.imageOpens g hg U')).comp
      (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl) =
      g.comp (N.inclusion U') :=
    ContMDiffMap.ext fun p =>
      AnalyticMap.restrictMap_apply g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl p
  have h₁ := (T.isPullbackOf_pullback (M.inclusion (AnalyticMap.imageOpens g hg U'))
      (isLocalDiffeomorph_inclusion M _)).comp
    ((T.pullback (M.inclusion (AnalyticMap.imageOpens g hg U'))
      (isLocalDiffeomorph_inclusion M _)).isPullbackOf_pullback
      (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
        Set.Subset.rfl))
  rw [hmap] at h₁
  have e := AnalyticTriple.IsPullbackOf.eq h₁
    ((T.isPullbackOf_pullback g hg).comp
      ((T.pullback g hg).isPullbackOf_pullback (N.inclusion U')
        (isLocalDiffeomorph_inclusion N U')))
  have hT₂ := AnalyticTriple.bmoClass_pullback
    (bmoClass_restrict T hT (AnalyticMap.imageOpens g hg U'))
    (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
    (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
      Set.Subset.rfl)
  refine (step2bPhase_congr (famFuel (T.pullback g hg) hT' U') e.symm
    (bmoClass_restrict (T.pullback g hg) hT' U') hT₂).trans ?_
  refine step2bPhase_pullback_eraseEmpty (famFuel T hT (AnalyticMap.imageOpens g hg U')) _
    (bmoClass_restrict T hT _) _ _ hT₂
    (step2bMeasure_restrict_le_famFuel T hT _ (AnalyticMap.isCompact_closure_image g hU'))
    (famFuel (T.pullback g hg) hT' U') ?_
  rw [step2bMeasure_congr e hT₂ (bmoClass_restrict (T.pullback g hg) hT' U')]
  exact step2bMeasure_restrict_le_famFuel (T.pullback g hg) hT' U' hU'

/-- The counterpart, for boundary members, of the empty blow-up convention [Kol07, 32], on each
open: **the monomial phase is indifferent to empty boundary members**. The restricted boundaries
differ by an empty extension, the phase is indifferent to it at equal fuel, and the two fuels give
the same complete phase. -/
theorem step2bFunctor_indifferentToEmptyMembers : (step2bFunctor ψ₀).IndifferentToEmptyMembers := by
  intro M T F' hsnc' e h₁ h₂ hT hT' U hU
  rw [step2bFunctor_fam, step2bFunctor_fam, step2bFam_seqOn, step2bFam_seqOn]
  set T₂ : AnalyticTriple ψ₀ M := ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ with hT₂def
  have hext : HypersurfaceFamily.IsEmptyExtension
      (G := (T₂.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F)
      (G' := (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F) e := by
    refine ⟨fun j => ?_, fun b hb => ?_⟩
    · change ⇑(M.inclusion U) ⁻¹' T.F.hyp (e j) = ⇑(M.inclusion U) ⁻¹' F'.hyp j
      rw [h₁ j]
    · change ⇑(M.inclusion U) ⁻¹' T.F.hyp b = ∅
      rw [h₂ b hb, Set.preimage_empty]
  have h1 := step2bPhase_eq_of_isEmptyExtension (famFuel T hT U)
    (T₂.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) rfl e hext
    (bmoClass_restrict T₂ hT' U) (bmoClass_restrict T hT U)
  rw [← h1]
  refine step2bPhase_eq_of_step2bMeasure_le' _ (bmoClass_restrict T₂ hT' U) ?_
    (step2bMeasure_restrict_le_famFuel T₂ hT' U hU)
  exact (step2bMeasure_le_of_isEmptyExtension
    (T₂.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) rfl e hext
    (bmoClass_restrict T₂ hT' U) (bmoClass_restrict T hT U)).trans
    (step2bMeasure_restrict_le_famFuel T hT U hU)

/-! ### The support clause from the order clause -/

section SupportClause

variable {M : AnalyticManifold.{u} 𝕜 E}

omit [FiniteDimensional 𝕜 E] in
/-- The order of `J` along any centre `D` at a point of the support of `D` is at most the order of
`J` there: `D_a ≠ 𝒪_a` lies in the maximal ideal, so `J_a ⊆ D_a^p ⊆ 𝔪_a^p` (the general form of
`ordAlong_le_ord`). -/
theorem ordAlongIdeal_le_ord_of_mem_support (D J : AnalyticManifold.IdealSheaf M) {a : M}
    (ha : a ∈ D.support) : IdealSheaf.ordAlongIdeal D J a ≤ J.ord a := by
  refine iSup₂_le fun p hp => ?_
  exact IsLocalRing.le_ord_iff.mpr
    (hp.trans (Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal ha) p))

omit [FiniteDimensional 𝕜 E] in
/-- The support clause of [Wlo09, Definition 3.2.4 (1)] ("`C_i ⊂ supp(M_i, Z_i, I_i, E_i, µ)`") from
the order clause of [Kol07, Definition 66]: the centres of a sequence of order `≥ m ≥ 1` lie in the
support `{x | 1 ≤ ord_x 𝓘_i}` of the current marked transform. -/
theorem center_support_subset_of_isOfOrderGe (S : FiniteSuccession M)
    {I E₀ : AnalyticManifold.IdealSheaf M} {m : ℕ} (hS : S.IsOfOrderGe I m E₀) (hm : 1 ≤ m)
    (i : Fin S.length) :
    (S.center i).support ⊆ {x | (1 : ℕ∞) ≤ (S.markedTransformSeq I m i.castSucc).ord x} := by
  intro x hx
  have h := (hS i).2 x hx
  exact (Nat.one_le_cast.mpr hm).trans (h.trans (ordAlongIdeal_le_ord_of_mem_support _ _ hx))

end SupportClause

/-- The support clause of [Wlo09, Definition 3.2.4 (1)] at `µ = 1` for the monomial phase: every
centre of the phase lies in the support of the current controlled transform. -/
theorem step2bFam_center_mem_support {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BMOClass 1 T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (i : Fin ((step2bFam T hT).seqOn U hU).toSuccession.length) :
    (((step2bFam T hT).seqOn U hU).toSuccession.center i).support ⊆
      {x | (1 : ℕ∞) ≤ (((step2bFam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 i.castSucc).ord x} :=
  center_support_subset_of_isOfOrderGe _ (step2bFam_isOfOrderGe T hT U hU) le_rfl i

end Hironaka.Manifold.BMOmod

end
