/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ComposeInducedFunctor
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bFunctor
public import Hironaka.Manifold.IdealSheaf.Monoid
public import Hironaka.Resolution.Analytic.OrderReduction.BD
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAComm
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Split
import Hironaka.Resolution.Analytic.OrderReduction.BMO.SplitOrder
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Comap
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1MeasureOrder
import Hironaka.Resolution.Analytic.OrderReduction.Modified.NonmonomialIndiff
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bExponent
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bTools
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAAlign
import Hironaka.Resolution.Analytic.OrderReduction.Step21Functoriality
import Hironaka.Resolution.Analytic.Wlo09.EmptyRound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The exit of the monomial phase, and the composite of the rounds with the monomial phase

The monomial phase (`Step2bPhase.lean`, `Step2bFamily.lean`, `Step2bFunctor.lean`) blows up the
positive locus of the top active member until no member is active ([Wlo09, Theorem 7.4.1];
[Wlo09, §6, Step 2b]). This module proves what its value leaves behind, in the two forms which the
next step of the modified algorithm (the restriction to a hypersurface of maximal contact) needs
("we arrive at the purely nonmonomial case `I′ = N(I′)`, where `max{ord_x(I) : x ∈ supp(I′)} = 1`",
[Wlo09, Theorem 7.4.1]):

* **the first exit property**: at the induced triple of the value of the phase no member is active
  (`activeMembers_induced_step2bPhase_eq_empty`, `activeMembers_induced_step2bFam_eq_empty`), since
  the measure `step2bMeasure` drops by one per step (`step2bMeasure_stepTriple_add_one_le`) and at
  measure `0` no member is active. Hence `M(𝓘) = ⊤`
  (`monomialPart_eq_top_of_activeMembers_eq_empty`: every component exponent is `0`) and `N(𝓘) = 𝓘`
  (`nonmonomialTriple_I_eq_of_monomialPart_eq_top`, the colon by the unit ideal): "no active member"
  means "the ideal is its own nonmonomial part".
* **the second exit property**: the pointwise bound `ord N(𝓘) ≤ d` survives every step
  (`nonmonomialOrdLe_stepTriple`) and the whole phase (`nonmonomialOrdLe_induced_step2bPhase`). One
  step is the blow-up of a centre of codimension one, a local analytic isomorphism `π`
  (`isLocalDiffeomorph_blowUpπ_of_codimOne`); `N(π^*𝓘) = π^* N(𝓘)` (`nonmonomialPart_comap`, the
  observation of [Kol07, 111, Step 1]); the ideal after the step is the division of `π^*𝓘` by one
  power of the ideal of the new member (`stalkIdeal_stepIdeal`; at the stalk
  `π^*𝓘 = 𝓘_{π⁻¹Z} · 𝓘′`, `stalkIdeal_comap_stepπ_eq_mul`, the transform (60.1) of
  [Kol07, Definition 60] at the mark `1`), which the fine nonmonomial part ignores
  (`nonmonomialPart_componentIdeal_pow_mul`, the uniqueness of the decomposition of
  [Kol07, Definition–Lemma 110]). The boundary after the step is `stepFamily` (the strict transforms
  and the new member `π⁻¹(Z)` last) while the pull-back lemmas speak of `F.comap π`; their fine
  parts agree **pointwise** (`stalkIdeal_monomialPart_stepFamily_eq`): at a point the components
  through it correspond member by member (`stepMemberOf`: `inl k ↦ k`, `inr ↦ top`; injective on the
  members through the point, `stepMemberOf_injective_of_mem`, and onto,
  `exists_mem_stepFamily_of_mem_comap`) with equal stalks (`stalkIdeal_idealSheaf_stepFamily_eq`;
  over `Z` the new member and the pulled-back top member have the same stalk, `Z` being open in
  `E^top`, `stalkIdeal_idealSheaf_stepFamily_inr_eq`) and hence equal exponents; globally
  `nonmonomialPart_stepFamily_eq_comap`. No global correspondence of component sets is used.

Together, under the bound `1` on the nonmonomial part of the restricted triple, the triple induced
by the value of the phase on every open lies in `BOClass 1` (`boClass_one_induced_step2bFam`).

Then **the composite of the rounds with the monomial phase**: `stepACFunctor`, the `composeInduced`
of `ComposeInducedFunctor.lean` of `stepAFunctor` at `m = 1`, `t = 2` and `step2bFunctor`, with the
class hypotheses of `BMOClass 1` (`bmoClass_inducedTriple`, `bmoClass_classPullbackClosed`,
`bmoClass_classInducedEraseEmptyClosed`); its order clause `stepACFunctor_isOfOrderGe`; and the fact
the next step needs, that the triple induced by its value on every open lies in `BOClass 1`
(`boClass_one_induced_stepACFunctor`): the terminal bound of the rounds **at the value**
(`nonmonomialOrdLe_induced_stepAFamOn`: `stepAChainState_bound` transported along the restriction,
`induced_pullback` and `nonmonomialOrdLe_pullback`, and the deletion of empty blow-ups,
`nonmonomialOrdLe_induced_eraseEmpty`), the exit of the monomial phase at the induced triple, and
the transport of `BOClass` along the `shrinkAppend`, restriction and deletion of the composite
(`boClass_induced_concat_aux`, `AnalyticFamilyFunctor.boClass_induced_alongList`,
`AnalyticFamilyFunctor.boClass_induced_composeAlong`).

The parameters `hcomp` and `hid` enter only through the rounds (`stepAFunctor`,
`nonmonomialOrdLe_pullback`).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Manifold.AnalyticTriple

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)

omit [FiniteDimensional 𝕜 E] in
/-- The induced triple of a `BMOClass m` triple along any list of order `≥ s` is in `BMOClass m`:
the mark is kept, the nonempty members are finite (`finite_nonempty_totalTransformSeqFrom`). Named
apart from `Hironaka.MarkedTriple.bmoClass_induced`, its scheme-theoretic counterpart. -/
theorem bmoClass_inducedTriple {m : ℕ} (hT : BMOClass m T) (s : ℕ) (L : BlowUpSequence ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) : BMOClass m (T.induced s L hL) :=
  ⟨hT.1, finite_nonempty_totalTransformSeqFrom L.toSuccession T.F hT.2 (Fin.last _)⟩

omit [FiniteDimensional 𝕜 E] in
/-- Substituting an equal inducing list inside a predicate on the induced triple: the two last
stages are only propositionally equal, so this is a substitution, not a rewrite. -/
theorem induced_congr_list (P : ∀ {N : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ N → Prop)
    (m : ℕ) {L₁ L₂ : BlowUpSequence ψ₀ M} (e : L₁ = L₂)
    (h₂ : L₂.toSuccession.IsOfOrderGe T.I m T.F.idealSheaf) (h : P (T.induced m L₂ h₂))
    (h₁ : L₁.toSuccession.IsOfOrderGe T.I m T.F.idealSheaf) : P (T.induced m L₁ h₁) := by
  subst e
  exact h

end Manifold.AnalyticTriple

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)

omit [FiniteDimensional 𝕜 E] in
/-- No active member implies that every component exponent is `0`
(`ordAlong_eq_zero_of_notMem_positiveLocus`, `componentExponent_eq_toNat_ordAlongIdeal`), hence
that the fine monomial part is the unit ideal (`stalkIdeal_monomialPart`, the product of the factors
of the components through the point). -/
theorem monomialPart_eq_top_of_activeMembers_eq_empty (h : activeMembers T = ∅) :
    monomialPart T.F T.isSnc T.I = ⊤ := by
  refine IdealSheaf.ext fun x => ?_
  rw [stalkIdeal_monomialPart, IdealSheaf.stalkIdeal_top, ← Ideal.one_eq_top]
  refine Finset.prod_eq_one fun i hi => ?_
  have hx : x ∈ componentSet T.F i := IdealSheaf.mem_activeFinset.mp hi
  have hxj : x ∈ T.F.hyp i.1 := Subtype.coe_image_subset _ _ hx
  have hnot : x ∉ positiveLocus T i.1 := fun hpos =>
    (Set.eq_empty_iff_forall_notMem.mp h i.1) ⟨x, hpos⟩
  have hord : IdealSheaf.ordAlongIdeal (componentIdeal T.F T.isSnc i) T.I x = 0 := by
    rw [IdealSheaf.ordAlongIdeal_congr_stalk_left _ _ _
      (componentIdeal_stalkIdeal_eq T.F T.isSnc i hx)]
    exact ordAlong_eq_zero_of_notMem_positiveLocus T hxj hnot
  rw [componentFactor, IdealSheaf.stalkIdeal_pow,
    componentExponent_eq_toNat_ordAlongIdeal T.F T.isSnc T.I i hx, hord]
  simp

omit [FiniteDimensional 𝕜 E] in
/-- `M(𝓘) = ⊤` implies `N(𝓘) = 𝓘` (the colon by the unit ideal, `stalkIdeal_nonmonomialPart`). -/
theorem nonmonomialTriple_I_eq_of_monomialPart_eq_top (h : monomialPart T.F T.isSnc T.I = ⊤) :
    (nonmonomialTriple T).I = T.I := by
  rw [nonmonomialTriple_I]
  refine IdealSheaf.ext fun x => ?_
  rw [stalkIdeal_nonmonomialPart, h, IdealSheaf.stalkIdeal_top]
  ext r
  constructor
  · intro hr
    simpa using Submodule.mem_colon.mp hr 1 Submodule.mem_top
  · intro hr
    exact Submodule.mem_colon.mpr fun p _ => Ideal.mul_mem_right p _ hr

variable (hT : AnalyticTriple.BMOClass 1 T)

/-- The head triple of a step of the monomial phase (the induced triple of the one-element list,
`headTriple` of `InducedConcat.lean`) is the triple after the step: the ideals by `headTriple_I` and
the definition of `stepIdeal`, the boundaries by `headTriple_F` and the definition of `stepFamily`
(the centre is the cosupport of its ideal sheaf). The order clause `h₁` is a hypothesis here; at the
uses it is the head clause of `isOfOrderGe_step2bPhase`, read off through `induced_cons`. -/
theorem headTriple_stepCenter_eq (hfin : (activeMembers T).Finite)
    (hne : (activeMembers T).Nonempty)
    (h₁ : (BlowUpSequence.cons (stepCenter T hfin hne) (BlowUpSequence.nil
        _)).toSuccession.IsOfOrderGe
      T.I 1 T.F.idealSheaf) :
    T.headTriple 1 (stepCenter T hfin hne) h₁ = stepTriple T hfin hne :=
  AnalyticTriple.ext' (T.headTriple_I 1 (stepCenter T hfin hne) h₁) (by
    rw [T.headTriple_F 1 (stepCenter T hfin hne) h₁, IsClosedSubmanifold.cosupport_idealSheaf]
    rfl)

/-- The recursion of the first exit property: at a fuel `k ≥ step2bMeasure T`, the triple induced by
the phase has no active member (induction on `k` with `induced_cons` and `headTriple_stepCenter_eq`;
the measure is lowered by one per step, `step2bMeasure_stepTriple_add_one_le`, and at measure `0`
no member is active, `one_le_step2bMeasure_of_nonempty`). -/
theorem activeMembers_induced_step2bPhase_eq_empty_aux :
    ∀ (k : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
      (hT : AnalyticTriple.BMOClass 1 T), step2bMeasure T hT ≤ k →
      activeMembers (T.induced 1 (step2bPhase k T hT) (isOfOrderGe_step2bPhase k T hT)) = ∅
  | 0, M, T, hT, hk => by
    have hne : ¬ (activeMembers T).Nonempty := fun hne => by
      have := (one_le_step2bMeasure_of_nonempty T hT hne).trans hk
      simp at this
    refine AnalyticTriple.induced_congr_list T (fun S => activeMembers S = ∅) 1
      (step2bPhase_zero T hT)
      (by rw [← step2bPhase_zero T hT]; exact isOfOrderGe_step2bPhase 0 T hT) ?_ _
    show activeMembers (T.induced 1 (BlowUpSequence.nil M) _) = ∅
    rw [AnalyticTriple.induced_nil]
    exact Set.not_nonempty_iff_eq_empty.mp hne
  | k + 1, M, T, hT, hk => by
    by_cases hne : (activeMembers T).Nonempty
    · have hk' : step2bMeasure (stepTriple T (activeMembers_finite T hT) hne)
          (bmoClass_stepTriple T (activeMembers_finite T hT) hne hT) ≤ k := by
        have h := (step2bMeasure_stepTriple_add_one_le T (activeMembers_finite T hT) hne
          hT).trans hk
        rw [Nat.cast_succ] at h
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h
      have e := step2bPhase_succ_of_nonempty T hT k hne
      refine AnalyticTriple.induced_congr_list T (fun S => activeMembers S = ∅) 1 e
        (by rw [← e]; exact isOfOrderGe_step2bPhase _ T hT) ?_ _
      show activeMembers (T.induced 1 (BlowUpSequence.cons _ _) _) = ∅
      rw [AnalyticTriple.induced_cons, AnalyticTriple.induced_congr
        (headTriple_stepCenter_eq T (activeMembers_finite T hT) hne _) 1 _ _
        (isOfOrderGe_step2bPhase k _ _)]
      exact activeMembers_induced_step2bPhase_eq_empty_aux k _ _ hk'
    · refine AnalyticTriple.induced_congr_list T (fun S => activeMembers S = ∅) 1
        (step2bPhase_succ_of_not_nonempty T hT k hne)
        (by
          rw [← step2bPhase_succ_of_not_nonempty T hT k hne]
          exact isOfOrderGe_step2bPhase _ T hT) ?_ _
      show activeMembers (T.induced 1 (BlowUpSequence.nil M) _) = ∅
      rw [AnalyticTriple.induced_nil]
      exact Set.not_nonempty_iff_eq_empty.mp hne

/-- **The first exit property**: at a fuel `k ≥ step2bMeasure T`, the triple induced by the phase
has no active member (induction on `k` with `induced_cons` and `headTriple_stepCenter_eq`; the
measure is lowered by one per step, `step2bMeasure_stepTriple_add_one_le`, and at measure `0` no
member is active, `one_le_step2bMeasure_of_nonempty`). -/
theorem activeMembers_induced_step2bPhase_eq_empty (k : ℕ) (hk : step2bMeasure T hT ≤ k) :
    activeMembers (T.induced 1 (step2bPhase k T hT) (isOfOrderGe_step2bPhase k T hT)) = ∅ :=
  activeMembers_induced_step2bPhase_eq_empty_aux k T hT hk

/-- The first exit property at the value of the family: the triple induced by the value of
`step2bFam` on `U` has no active member (`step2bFam_seqOn`, `step2bMeasure_restrict_le_famFuel`,
`activeMembers_induced_step2bPhase_eq_empty`). -/
theorem activeMembers_induced_step2bFam_eq_empty (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    activeMembers ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).induced 1
      ((step2bFam T hT).seqOn U hU) (step2bFam_isOfOrderGe T hT U hU)) = ∅ :=
  activeMembers_induced_step2bPhase_eq_empty _ (bmoClass_restrict T hT U) (famFuel T hT U)
    (step2bMeasure_restrict_le_famFuel T hT U hU)

omit [FiniteDimensional 𝕜 E] in
/-- The pointwise order is a function of the stalk
(`IdealSheaf.ord J x := IsLocalRing.ord (J.stalkIdeal x)`). -/
theorem ord_congr_stalk {N : AnalyticManifold.{u} 𝕜 E} {J₁ J₂ : AnalyticManifold.IdealSheaf N}
    {x : N}
    (h : J₁.stalkIdeal x = J₂.stalkIdeal x) : J₁.ord x = J₂.ord x := by
  change IsLocalRing.ord (J₁.stalkIdeal x) = IsLocalRing.ord (J₂.stalkIdeal x)
  rw [h]

omit [FiniteDimensional 𝕜 E] in
/-- For any boundary with simple normal crossings, the stalk of the nonmonomial part at a point
depends only on the stalk of the ideal there: the exponents of the components through the point
are orders along them at that point (`componentExponent_eq_toNat_ordAlongIdeal`,
`ordAlongIdeal_congr_stalk`), and the colon is stalkwise (`stalkIdeal_nonmonomialPart`). -/
theorem nonmonomialPart_stalkIdeal_congr {N : AnalyticManifold.{u} 𝕜 E} (G : HypersurfaceFamily N)
    (hG : G.IsSnc ψ₀) {J₁ J₂ : AnalyticManifold.IdealSheaf N} (x : N)
    (h : J₁.stalkIdeal x = J₂.stalkIdeal x) :
    (nonmonomialPart G hG J₁).stalkIdeal x = (nonmonomialPart G hG J₂).stalkIdeal x := by
  have hM : (monomialPart G hG J₁).stalkIdeal x = (monomialPart G hG J₂).stalkIdeal x := by
    rw [stalkIdeal_monomialPart, stalkIdeal_monomialPart]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hx : x ∈ componentSet G i := IdealSheaf.mem_activeFinset.mp hi
    rw [componentFactor, componentFactor, IdealSheaf.stalkIdeal_pow, IdealSheaf.stalkIdeal_pow,
      componentExponent_eq_toNat_ordAlongIdeal G hG J₁ i hx,
      componentExponent_eq_toNat_ordAlongIdeal G hG J₂ i hx,
      IdealSheaf.ordAlongIdeal_congr_stalk _ _ _ _ h]
  rw [stalkIdeal_nonmonomialPart, stalkIdeal_nonmonomialPart, h, hM]

/-! ### The fine parts for `stepFamily` and for `F.comap π` agree stalkwise -/

/-- The pulled-back boundary along the step's blow-down. -/
abbrev stepComapFamily (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty) :
    HypersurfaceFamily (stepStage T hfin hne) := T.F.comap ⇑(stepπ T hfin hne)

theorem isSnc_stepComapFamily (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty) :
    (stepComapFamily T hfin hne).IsSnc ψ₀ :=
  HypersurfaceFamily.isSnc_comap T.isSnc _ (isLocalDiffeomorph_stepπ T hfin hne)

/-- The member of `F.comap π` a member of `stepFamily` lies over: `inl k ↦ k`, `inr ↦ top`. -/
def stepMemberOf (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty)
    (i : (stepFamily T hfin hne).ι) : T.F.ι :=
  Sum.elim id (fun _ => topMember T hfin hne) (ofLex i)

/-- A point of a member of `stepFamily` lies on the member of `F.comap π` it lies over
(`mem_hyp_of_mem_strictTransform`, `step2bCenter_subset`). -/
theorem mem_stepComapFamily_of_mem_stepFamily (hfin : (activeMembers T).Finite)
    (hne : (activeMembers T).Nonempty) {i : (stepFamily T hfin hne).ι} {x' : stepStage T hfin hne}
    (hx' : x' ∈ (stepFamily T hfin hne).hyp i) :
    x' ∈ (stepComapFamily T hfin hne).hyp (stepMemberOf T hfin hne i) := by
  obtain ⟨j, rfl⟩ : ∃ j : T.F.ι ⊕ PUnit.{u + 1}, toLex j = i := ⟨ofLex i, toLex_ofLex i⟩
  rcases j with k | u
  · exact HypersurfaceFamily.mem_hyp_of_mem_strictTransform (isBlowUp_blowUpπ ψ₀ _) T.isSnc hx'
  · exact step2bCenter_subset T hfin hne hx'

/-- Two members of `stepFamily` through a common point over the same member of `F` coincide: the
strict transform of the top member and the new member `π⁻¹(Z)` never meet
(`notMem_step2bCenter_of_mem_stepFamily_top`). -/
theorem stepMemberOf_injective_of_mem (hfin : (activeMembers T).Finite)
    (hne : (activeMembers T).Nonempty) {i₁ i₂ : (stepFamily T hfin hne).ι}
    {x' : stepStage T hfin hne} (h₁ : x' ∈ (stepFamily T hfin hne).hyp i₁)
    (h₂ : x' ∈ (stepFamily T hfin hne).hyp i₂)
    (h : stepMemberOf T hfin hne i₁ = stepMemberOf T hfin hne i₂) : i₁ = i₂ := by
  obtain ⟨j₁, rfl⟩ : ∃ j : T.F.ι ⊕ PUnit.{u + 1}, toLex j = i₁ := ⟨ofLex i₁, toLex_ofLex i₁⟩
  obtain ⟨j₂, rfl⟩ : ∃ j : T.F.ι ⊕ PUnit.{u + 1}, toLex j = i₂ := ⟨ofLex i₂, toLex_ofLex i₂⟩
  rcases j₁ with k₁ | u₁ <;> rcases j₂ with k₂ | u₂
  · have hk : k₁ = k₂ := h
    rw [hk]
  · exfalso
    have hk : k₁ = topMember T hfin hne := h
    subst hk
    exact notMem_step2bCenter_of_mem_stepFamily_top T hfin hne h₁ h₂
  · exfalso
    have hk : k₂ = topMember T hfin hne := h.symm
    subst hk
    exact notMem_step2bCenter_of_mem_stepFamily_top T hfin hne h₂ h₁
  · cases u₁
    cases u₂
    rfl

/-- Every point of a member of `F.comap π` lies on a member of `stepFamily` over it: the other
members' strict transforms are their preimages (`stepFamily_hyp_inl_of_ne`); over the top member,
the new member `π⁻¹(Z)` over `Z`, the strict transform off `Z`
(`stepFamily_hyp_inl_inter_compl`). -/
theorem exists_mem_stepFamily_of_mem_comap (hfin : (activeMembers T).Finite)
    (hne : (activeMembers T).Nonempty) {k : T.F.ι} {x' : stepStage T hfin hne}
    (hx' : x' ∈ (stepComapFamily T hfin hne).hyp k) :
    ∃ i, x' ∈ (stepFamily T hfin hne).hyp i ∧ stepMemberOf T hfin hne i = k := by
  by_cases hk : k = topMember T hfin hne
  · subst hk
    by_cases hZ : stepπ T hfin hne x' ∈ step2bCenter T hfin hne
    · exact ⟨toLex (Sum.inr PUnit.unit), hZ, rfl⟩
    · refine ⟨toLex (Sum.inl (topMember T hfin hne)), ?_, rfl⟩
      have h : x' ∈ (stepFamily T hfin hne).hyp (toLex (Sum.inl (topMember T hfin hne))) ∩
          ⇑(stepπ T hfin hne) ⁻¹' (step2bCenter T hfin hne)ᶜ := by
        rw [stepFamily_hyp_inl_inter_compl T hfin hne _]
        exact ⟨hx', hZ⟩
      exact h.1
  · refine ⟨toLex (Sum.inl k), ?_, rfl⟩
    rw [stepFamily_hyp_inl_of_ne T hfin hne hk]
    exact hx'

/-- At a point over the centre, the ideal sheaf of the new member `π⁻¹(Z)` and the ideal sheaf of
the pulled-back top member `π⁻¹(E^j)` have the same stalk: `Z` is open in `E^j`
(`exists_isOpen_inter_subset_positiveLocus`), so the two closed hypersurfaces agree near the point
(`stalkIdeal_idealSheaf_congr_nhds`). -/
theorem stalkIdeal_idealSheaf_stepFamily_inr_eq (hfin : (activeMembers T).Finite)
    (hne : (activeMembers T).Nonempty) {x' : stepStage T hfin hne}
    (hx' : stepπ T hfin hne x' ∈ step2bCenter T hfin hne) :
    ((isSnc_stepFamily T hfin hne).1 (toLex (Sum.inr PUnit.unit))).idealSheaf.stalkIdeal x' =
      ((isSnc_stepComapFamily T hfin hne).1 (topMember T hfin hne)).idealSheaf.stalkIdeal x' := by
  obtain ⟨O, hO, hxO, hsub⟩ := exists_isOpen_inter_subset_positiveLocus T hx'
  refine IsClosedSubmanifold.stalkIdeal_idealSheaf_congr_nhds _ _ hx'
    (hO.preimage (stepπ T hfin hne).contMDiff.continuous) hxO ?_
  ext y
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨step2bCenter_subset T hfin hne h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hsub ⟨h2, h1⟩, h2⟩

/-- The ideal sheaves of the members of `stepFamily` and of `F.comap π` have the same stalks at a
common point: `inl k`, `k ≠ top`, by `idealSheaf_stepFamily_inl_of_ne`; `inl top` at a point of the
strict transform by `stalkIdeal_idealSheaf_stepFamily_inl_top`; `inr` by
`stalkIdeal_idealSheaf_stepFamily_inr_eq`; the ideal sheaf of the pulled-back member is the
pull-back (`comap_idealSheaf_of_isLocalDiffeomorph`). -/
theorem stalkIdeal_idealSheaf_stepFamily_eq (hfin : (activeMembers T).Finite)
    (hne : (activeMembers T).Nonempty) {i : (stepFamily T hfin hne).ι} {x' : stepStage T hfin hne}
    (hx' : x' ∈ (stepFamily T hfin hne).hyp i) :
    ((isSnc_stepFamily T hfin hne).1 i).idealSheaf.stalkIdeal x' =
      ((isSnc_stepComapFamily T hfin hne).1
        (stepMemberOf T hfin hne i)).idealSheaf.stalkIdeal x' := by
  obtain ⟨j, rfl⟩ : ∃ j : T.F.ι ⊕ PUnit.{u + 1}, toLex j = i := ⟨ofLex i, toLex_ofLex i⟩
  have hπ := isLocalDiffeomorph_stepπ T hfin hne
  rcases j with k | u
  · by_cases hk : k = topMember T hfin hne
    · subst hk
      exact (stalkIdeal_idealSheaf_stepFamily_inl_top T hfin hne hx').trans
        (congrArg
            (fun J : AnalyticManifold.IdealSheaf (stepStage T hfin hne) => J.stalkIdeal x')
          (comap_idealSheaf_of_isLocalDiffeomorph ψ₀ (stepπ T hfin hne) hπ (T.isSnc.1 _)))
    · exact congrArg
        (fun J : AnalyticManifold.IdealSheaf (stepStage T hfin hne) => J.stalkIdeal x')
        ((idealSheaf_stepFamily_inl_of_ne T hfin hne hk).trans
          (comap_idealSheaf_of_isLocalDiffeomorph ψ₀ (stepπ T hfin hne) hπ (T.isSnc.1 k)))
  · cases u
    exact stalkIdeal_idealSheaf_stepFamily_inr_eq T hfin hne hx'

/-- The stalks of the fine monomial parts with respect to `stepFamily` and to `F.comap π` agree: the
components through `x'` correspond member by member (`Finset.prod_bij`, as in `monomialPart_comap`;
`stepMemberOf` is injective on the members through `x'`, `stepMemberOf_injective_of_mem`, and onto,
`exists_mem_stepFamily_of_mem_comap`); the factors agree by `stalkIdeal_idealSheaf_stepFamily_eq`
through `componentIdeal_stalkIdeal_eq`, the exponents by `componentExponent_eq_toNat_ordAlongIdeal`
at `x'` and `ordAlongIdeal_congr_stalk_left`. -/
theorem stalkIdeal_monomialPart_stepFamily_eq (hfin : (activeMembers T).Finite)
    (hne : (activeMembers T).Nonempty) (J : AnalyticManifold.IdealSheaf (stepStage T hfin hne))
    (x' : stepStage T hfin hne) :
    (monomialPart (stepFamily T hfin hne) (isSnc_stepFamily T hfin hne) J).stalkIdeal x' =
      (monomialPart (stepComapFamily T hfin hne) (isSnc_stepComapFamily T hfin hne)
        J).stalkIdeal x' := by
  rw [stalkIdeal_monomialPart, stalkIdeal_monomialPart]
  have key : ∀ i : ComponentIndex (stepFamily T hfin hne),
      x' ∈ componentSet (stepFamily T hfin hne) i →
        x' ∈ (stepComapFamily T hfin hne).hyp (stepMemberOf T hfin hne i.1) := fun i hi =>
    mem_stepComapFamily_of_mem_stepFamily T hfin hne (Subtype.coe_image_subset _ _ hi)
  refine Finset.prod_bij
    (fun i hi => (⟨stepMemberOf T hfin hne i.1, ConnectedComponents.mk
      ⟨x', key i (IdealSheaf.mem_activeFinset.mp hi)⟩⟩ :
        ComponentIndex (stepComapFamily T hfin hne)))
    ?_ ?_ ?_ ?_
  · intro i hi
    rw [IdealSheaf.mem_activeFinset]
    exact mem_componentSet_mk _ _ (key i (IdealSheaf.mem_activeFinset.mp hi))
  · intro i₁ hi₁ i₂ hi₂ heq
    have h₁ := IdealSheaf.mem_activeFinset.mp hi₁
    have h₂ := IdealSheaf.mem_activeFinset.mp hi₂
    have hj : stepMemberOf T hfin hne i₁.1 = stepMemberOf T hfin hne i₂.1 := by
      have hf := congrArg Sigma.fst heq
      exact hf
    exact componentIndex_ext_of_mem h₁ h₂ (stepMemberOf_injective_of_mem T hfin hne
      (Subtype.coe_image_subset _ _ h₁) (Subtype.coe_image_subset _ _ h₂) hj)
  · intro i' hi'
    have hi'm := IdealSheaf.mem_activeFinset.mp hi'
    obtain ⟨i, hxi, hmem⟩ := exists_mem_stepFamily_of_mem_comap T hfin hne
      (Subtype.coe_image_subset _ _ hi'm)
    refine ⟨⟨i, ConnectedComponents.mk ⟨x', hxi⟩⟩, ?_, ?_⟩
    · rw [IdealSheaf.mem_activeFinset]
      exact mem_componentSet_mk _ _ hxi
    · exact componentIndex_ext_of_mem (mem_componentSet_mk _ _ _) hi'm hmem
  · intro i hi
    have hxi := IdealSheaf.mem_activeFinset.mp hi
    have hxi' : x' ∈ componentSet (stepComapFamily T hfin hne)
        ⟨stepMemberOf T hfin hne i.1, ConnectedComponents.mk ⟨x', key i hxi⟩⟩ :=
      mem_componentSet_mk _ _ _
    have hstalk : (componentIdeal (stepFamily T hfin hne) (isSnc_stepFamily T hfin hne)
          i).stalkIdeal x' =
        (componentIdeal (stepComapFamily T hfin hne) (isSnc_stepComapFamily T hfin hne)
          ⟨stepMemberOf T hfin hne i.1, ConnectedComponents.mk ⟨x', key i hxi⟩⟩).stalkIdeal x' := by
      rw [componentIdeal_stalkIdeal_eq _ _ _ hxi, componentIdeal_stalkIdeal_eq _ _ _ hxi']
      exact stalkIdeal_idealSheaf_stepFamily_eq T hfin hne (Subtype.coe_image_subset _ _ hxi)
    rw [componentFactor, componentFactor, IdealSheaf.stalkIdeal_pow, IdealSheaf.stalkIdeal_pow,
      componentExponent_eq_toNat_ordAlongIdeal _ _ J _ hxi,
      componentExponent_eq_toNat_ordAlongIdeal _ _ J _ hxi',
      IdealSheaf.ordAlongIdeal_congr_stalk_left _ _ _ hstalk, hstalk]

theorem stalkIdeal_nonmonomialPart_stepFamily_eq (hfin : (activeMembers T).Finite)
    (hne : (activeMembers T).Nonempty) (J : AnalyticManifold.IdealSheaf (stepStage T hfin hne))
    (x' : stepStage T hfin hne) :
    (nonmonomialPart (stepFamily T hfin hne) (isSnc_stepFamily T hfin hne) J).stalkIdeal x' =
      (nonmonomialPart (stepComapFamily T hfin hne) (isSnc_stepComapFamily T hfin hne)
        J).stalkIdeal x' := by
  rw [stalkIdeal_nonmonomialPart, stalkIdeal_nonmonomialPart,
    stalkIdeal_monomialPart_stepFamily_eq T hfin hne J x']

/-- At a point over the centre, the pulled-back ideal is the ideal after the step times the ideal of
the new member (the transform (60.1) of [Kol07, Definition 60] at the mark `1`):
`stalkIdeal_stepIdeal` is the colon by the principal ideal `(u)` of `π⁻¹(Z)`
(`stalkIdeal_idealSheaf_eq_span_singleton`, transported by the germ map), `(π^*𝓘)_{x'} ⊆ (u)` from
`𝓘 ⊆ 𝓘_Z` along `Z` (`one_le_ordAlong_step2bCenter`), and `Ideal.span_singleton_mul_colon_of_le`
recovers the product; the component of the pulled-back top member through `x'` has the stalk of
`π⁻¹(Z)` there (`stalkIdeal_idealSheaf_stepFamily_inr_eq`, `componentIdeal_stalkIdeal_eq`). -/
theorem stalkIdeal_comap_stepπ_eq_mul (hfin : (activeMembers T).Finite)
    (hne : (activeMembers T).Nonempty) {x' : stepStage T hfin hne}
    (hx' : stepπ T hfin hne x' ∈ step2bCenter T hfin hne) :
    (T.I.pullback _ (stepπ T hfin hne).contMDiff).stalkIdeal x' =
      (componentIdeal (stepComapFamily T hfin hne) (isSnc_stepComapFamily T hfin hne)
          ⟨topMember T hfin hne,
            ConnectedComponents.mk ⟨x', step2bCenter_subset T hfin hne hx'⟩⟩ ^ 1 *
        stepIdeal T hfin hne).stalkIdeal x' := by
  obtain ⟨φ, σ, hyφ, hφ⟩ := (stepCenter T hfin hne).exists_adaptedChart _ hx'
  set g := coord E ψ₀ φ hφ.1 hyφ (σ 0) with hg
  have hZy : (stepCenter T hfin hne).idealSheaf.stalkIdeal (stepπ T hfin hne x') =
      Ideal.span {g} :=
    (stepCenter T hfin hne).stalkIdeal_idealSheaf_eq_span_singleton hx' hφ hyφ
  have hIy : T.I.stalkIdeal (stepπ T hfin hne x') ≤ Ideal.span {g} := by
    have := (IdealSheaf.le_ordAlongIdeal_iff _ T.I _ 1).mp
      (one_le_ordAlong_step2bCenter T hfin hne _ hx')
    rwa [pow_one, hZy] at this
  have hexc : ((stepCenter T hfin hne).idealSheaf.pullback _ (stepπ T hfin
      hne).contMDiff).stalkIdeal x' =
        Ideal.span {stepGermMap T hfin hne x' g} := by
    rw [stalkIdeal_comap_stepπ, hZy, Ideal.map_span, Set.image_singleton]
  have hJ : (T.I.pullback _ (stepπ T hfin hne).contMDiff).stalkIdeal x' ≤
      Ideal.span {stepGermMap T hfin hne x' g} := by
    rw [stalkIdeal_comap_stepπ, ← Set.image_singleton, ← Ideal.map_span]
    exact Ideal.map_mono hIy
  have hC : (componentIdeal (stepComapFamily T hfin hne) (isSnc_stepComapFamily T hfin hne)
      ⟨topMember T hfin hne,
        ConnectedComponents.mk ⟨x', step2bCenter_subset T hfin hne hx'⟩⟩).stalkIdeal x' =
      Ideal.span {stepGermMap T hfin hne x' g} := by
    refine (componentIdeal_stalkIdeal_eq (stepComapFamily T hfin hne)
      (isSnc_stepComapFamily T hfin hne) _
      (mem_componentSet_mk (stepComapFamily T hfin hne) (topMember T hfin hne)
        (step2bCenter_subset T hfin hne hx'))).trans ?_
    have hA := stalkIdeal_idealSheaf_stepFamily_inr_eq T hfin hne hx'
    rw [idealSheaf_stepFamily_inr, hexc] at hA
    exact hA.symm
  rw [IdealSheaf.stalkIdeal_mul, IdealSheaf.stalkIdeal_pow, pow_one, hC, stalkIdeal_stepIdeal, hexc]
  exact (Ideal.span_singleton_mul_colon_of_le hJ).symm

/-- **The second exit property for one step**: the pointwise bound on the nonmonomial part survives
a step of the monomial phase. The blow-down `π` is a local analytic isomorphism
(`isLocalDiffeomorph_blowUpπ_of_codimOne`), `N(π^*𝓘) = π^* N(𝓘)` (`nonmonomialPart_comap`), the
ideal after the step is the division of `π^*𝓘` by one power of the ideal of the new member
(`stalkIdeal_stepIdeal`, `stalkIdeal_comap_stepπ_eq_mul`), which `N` ignores
(`nonmonomialPart_componentIdeal_pow_mul`, the uniqueness of the decomposition of [Kol07,
Definition–Lemma 110]), with the boundary re-indexed by `stepFamily` pointwise
(`stalkIdeal_nonmonomialPart_stepFamily_eq`). The transform identity of the rounds does not enter
here; it is first needed in the composite with the rounds. -/
theorem nonmonomialOrdLe_stepTriple (hfin : (activeMembers T).Finite)
    (hne : (activeMembers T).Nonempty) {d : ℕ} (h : NonmonomialOrdLe T d) :
    NonmonomialOrdLe (stepTriple T hfin hne) d := by
  intro x'
  have hπ := isLocalDiffeomorph_stepπ T hfin hne
  -- (1) the step's nonmonomial part, with respect to the pulled-back boundary
  have h1 : (nonmonomialTriple (stepTriple T hfin hne)).I.stalkIdeal x' =
      (nonmonomialPart (stepComapFamily T hfin hne) (isSnc_stepComapFamily T hfin hne)
        (stepIdeal T hfin hne)).stalkIdeal x' :=
    stalkIdeal_nonmonomialPart_stepFamily_eq T hfin hne (stepIdeal T hfin hne) x'
  -- (2) the step ideal and the pulled-back ideal have the same nonmonomial part
  have h2 : (nonmonomialPart (stepComapFamily T hfin hne) (isSnc_stepComapFamily T hfin hne)
        (stepIdeal T hfin hne)).stalkIdeal x' =
      (nonmonomialPart (stepComapFamily T hfin hne) (isSnc_stepComapFamily T hfin hne)
        (T.I.pullback _ (stepπ T hfin hne).contMDiff)).stalkIdeal x' := by
    by_cases hZ : stepπ T hfin hne x' ∈ step2bCenter T hfin hne
    · rw [nonmonomialPart_stalkIdeal_congr (stepComapFamily T hfin hne)
        (isSnc_stepComapFamily T hfin hne) x' (stalkIdeal_comap_stepπ_eq_mul T hfin hne hZ),
        nonmonomialPart_componentIdeal_pow_mul (stepComapFamily T hfin hne)
          (isSnc_stepComapFamily T hfin hne) _ (isNonzeroEverywhere_stepIdeal T hfin hne) _ 1]
    · exact nonmonomialPart_stalkIdeal_congr _ _ x' (stalkIdeal_stepIdeal_of_notMem T hfin hne hZ)
  -- (3) `N` commutes with the pull-back along the local isomorphism `π`
  have h3 := nonmonomialPart_comap (stepπ T hfin hne) hπ T.F T.isSnc T.I
  -- (4) the order at `x'` is the order of `N(𝓘)` at `π x'`
  change (nonmonomialTriple (stepTriple T hfin hne)).I.ord x' ≤ (d : ℕ∞)
  rw [ord_congr_stalk h1, ord_congr_stalk h2, h3,
    IdealSheaf.ord_comap_of_isLocalDiffeomorphAt _ _ (hπ x')]
  exact h _

/-- The re-indexing, proved pointwise: the nonmonomial part with respect to the boundary
`stepFamily` after the step (the components of the centre moved to the new member) equals the
nonmonomial part with respect to the pulled-back boundary `F.comap π`; at every point the components
through it correspond member by member with the same stalks and exponents, hence the same fine
monomial part and the same colon. -/
theorem nonmonomialPart_stepFamily_eq_comap (hfin : (activeMembers T).Finite)
    (hne : (activeMembers T).Nonempty)
        (J : AnalyticManifold.IdealSheaf (stepStage T hfin hne)) :
    nonmonomialPart (stepFamily T hfin hne) (isSnc_stepFamily T hfin hne) J =
      nonmonomialPart (T.F.comap ⇑(stepπ T hfin hne))
        (HypersurfaceFamily.isSnc_comap T.isSnc _ (isLocalDiffeomorph_blowUpπ_of_codimOne _)) J :=
  IdealSheaf.ext fun x' => stalkIdeal_nonmonomialPart_stepFamily_eq T hfin hne J x'

/-- The recursion of the second exit property along the phase: the bound survives the phase at every
fuel (induction with `induced_cons`, `headTriple_stepCenter_eq` and `nonmonomialOrdLe_stepTriple`).
-/
theorem nonmonomialOrdLe_induced_step2bPhase_aux :
    ∀ (k : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
      (hT : AnalyticTriple.BMOClass 1 T) {d : ℕ}, NonmonomialOrdLe T d →
      NonmonomialOrdLe (T.induced 1 (step2bPhase k T hT) (isOfOrderGe_step2bPhase k T hT)) d
  | 0, M, T, hT, d, h => by
    refine AnalyticTriple.induced_congr_list T (fun S => NonmonomialOrdLe S d) 1
      (step2bPhase_zero T hT)
      (by rw [← step2bPhase_zero T hT]; exact isOfOrderGe_step2bPhase 0 T hT) ?_ _
    show NonmonomialOrdLe (T.induced 1 (BlowUpSequence.nil M) _) d
    rw [AnalyticTriple.induced_nil]
    exact h
  | k + 1, M, T, hT, d, h => by
    by_cases hne : (activeMembers T).Nonempty
    · have e := step2bPhase_succ_of_nonempty T hT k hne
      refine AnalyticTriple.induced_congr_list T (fun S => NonmonomialOrdLe S d) 1 e
        (by rw [← e]; exact isOfOrderGe_step2bPhase _ T hT) ?_ _
      show NonmonomialOrdLe (T.induced 1 (BlowUpSequence.cons _ _) _) d
      rw [AnalyticTriple.induced_cons, AnalyticTriple.induced_congr
        (headTriple_stepCenter_eq T (activeMembers_finite T hT) hne _) 1 _ _
        (isOfOrderGe_step2bPhase k _ _)]
      exact nonmonomialOrdLe_induced_step2bPhase_aux k _ _
        (nonmonomialOrdLe_stepTriple T (activeMembers_finite T hT) hne h)
    · refine AnalyticTriple.induced_congr_list T (fun S => NonmonomialOrdLe S d) 1
        (step2bPhase_succ_of_not_nonempty T hT k hne)
        (by
          rw [← step2bPhase_succ_of_not_nonempty T hT k hne]
          exact isOfOrderGe_step2bPhase _ T hT) ?_ _
      show NonmonomialOrdLe (T.induced 1 (BlowUpSequence.nil M) _) d
      rw [AnalyticTriple.induced_nil]
      exact h

/-- **The second exit property along the phase**: the bound survives the phase at every fuel
(induction with `induced_cons`, `headTriple_stepCenter_eq` and `nonmonomialOrdLe_stepTriple`). -/
theorem nonmonomialOrdLe_induced_step2bPhase (k : ℕ) {d : ℕ} (h : NonmonomialOrdLe T d) :
    NonmonomialOrdLe (T.induced 1 (step2bPhase k T hT) (isOfOrderGe_step2bPhase k T hT)) d :=
  nonmonomialOrdLe_induced_step2bPhase_aux k T hT h

/-- Under the bound `1` on the nonmonomial part of the restricted triple, the triple induced by the
value of `step2bFam` on `U` is in `BOClass 1`: the mark; the order (`M = ⊤` by the first exit
property, `N = 𝓘` by `nonmonomialTriple_I_eq_of_monomialPart_eq_top`, `ord N ≤ 1` by the second);
and the finiteness (`bmoClass_inducedTriple`). -/
theorem boClass_one_induced_step2bFam (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (hN : NonmonomialOrdLe (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) 1) :
    AnalyticTriple.BOClass 1 ((T.pullback (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U)).induced 1
      ((step2bFam T hT).seqOn U hU) (step2bFam_isOfOrderGe T hT U hU)) := by
  have hemp := activeMembers_induced_step2bFam_eq_empty T hT U hU
  have hN' := nonmonomialOrdLe_induced_step2bPhase _ (bmoClass_restrict T hT U) (famFuel T hT U) hN
  refine ⟨le_rfl, fun x => ?_, (AnalyticTriple.bmoClass_inducedTriple _
    (bmoClass_restrict T hT U) 1 _ (step2bFam_isOfOrderGe T hT U hU)).2⟩
  have hI := nonmonomialTriple_I_eq_of_monomialPart_eq_top _
    (monomialPart_eq_top_of_activeMembers_eq_empty _ hemp)
  rw [← hI]
  exact hN' x

omit [FiniteDimensional 𝕜 E] in
/-- The pointwise bound on the nonmonomial part at the induced triple survives the deletion of empty
blow-ups from the inducing list: the ideals agree through `eraseEmptyLast⁻¹`
(`markedTransformSeq_last_eraseEmpty`), the boundary of the induced triple of the cleaned list is
an empty extension of the other's (`isEmptyExtension_eraseEmptyIdx_induced`), which `N` ignores
(`nonmonomialPart_eq_of_isEmptyExtension`), and `N` pulls back along the diffeomorphism
(`nonmonomialPart_comap`). -/
theorem nonmonomialOrdLe_induced_eraseEmpty (s : ℕ) (L : BlowUpSequence ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hLe : L.eraseEmpty.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) {d : ℕ}
    (h : NonmonomialOrdLe (T.induced s L hL) d) :
    NonmonomialOrdLe (T.induced s L.eraseEmpty hLe) d := by
  intro y
  have hI : (T.induced s L.eraseEmpty hLe).I =
      (T.induced s L hL).I.pullback _ (Diffeomorph.toAnalyticMap L.eraseEmptyLast.symm).contMDiff :=
    BlowUpSequence.markedTransformSeq_last_eraseEmpty L T.I T.F.idealSheaf s hL
  have h2 : (T.induced s L.eraseEmpty hLe).I.pullback _ (Diffeomorph.toAnalyticMap
      L.eraseEmptyLast).contMDiff = (T.induced s L hL).I := by
    rw [hI]
    exact comap_symm_comap L.eraseEmptyLast.symm _
  have h1 := nonmonomialPart_comap (Diffeomorph.toAnalyticMap L.eraseEmptyLast)
    L.eraseEmptyLast.isLocalDiffeomorph (T.induced s L.eraseEmpty hLe).F
    (T.induced s L.eraseEmpty hLe).isSnc (T.induced s L.eraseEmpty hLe).I
  rw [h2] at h1
  have h3 := nonmonomialPart_eq_of_isEmptyExtension
    (AnalyticTriple.isEmptyExtension_eraseEmptyIdx_induced T s L hL hLe)
    (HypersurfaceFamily.isSnc_comap (T.induced s L.eraseEmpty hLe).isSnc _
      L.eraseEmptyLast.isLocalDiffeomorph)
    (T.induced s L hL).isSnc (T.induced s L hL).I
  have hy : y = Diffeomorph.toAnalyticMap L.eraseEmptyLast (L.eraseEmptyLast.symm y) :=
    (L.eraseEmptyLast.apply_symm_apply y).symm
  rw [hy, ← IdealSheaf.ord_comap_of_isLocalDiffeomorphAt _
    (Diffeomorph.toAnalyticMap L.eraseEmptyLast)
    (L.eraseEmptyLast.isLocalDiffeomorph (L.eraseEmptyLast.symm y)), nonmonomialTriple_I, ← h1,
    ← h3]
  exact h _

omit [FiniteDimensional 𝕜 E] in
/-- The `BOClass` form of `nonmonomialOrdLe_induced_concat`, by recursion on the second list. -/
theorem boClass_induced_concat_aux : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (L : BlowUpSequence ψ₀ M) (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))) (m : ℕ)
    (hL : L.toSuccession.IsOfOrderGe T.I m T.F.idealSheaf)
    (hL' : L'.toSuccession.IsOfOrderGe (T.induced m L hL).I m (T.induced m L hL).F.idealSheaf)
    (hC : (L.concat L').toSuccession.IsOfOrderGe T.I m T.F.idealSheaf),
    AnalyticTriple.BOClass m ((T.induced m L hL).induced m L' hL') →
      AnalyticTriple.BOClass m (T.induced m (L.concat L') hC)
  | _, T, BlowUpSequence.nil _, L', m, hL, hL', hC, h => by
    rw [AnalyticTriple.induced_congr (AnalyticTriple.induced_nil T m hL) m L' hL' hC] at h
    exact h
  | _, T, BlowUpSequence.cons hY rest, L', m, hL, hL', hC, h => by
    have e₁ := AnalyticTriple.induced_cons T m hY hL
    have hL'' : L'.toSuccession.IsOfOrderGe
        ((T.headTriple m hY (T.isOfOrderGe_head_of_cons m hY hL)).induced m rest
          (T.isOfOrderGe_tail_of_cons m hY hL)).I m
        ((T.headTriple m hY (T.isOfOrderGe_head_of_cons m hY hL)).induced m rest
          (T.isOfOrderGe_tail_of_cons m hY hL)).F.idealSheaf := by
      rw [← e₁]; exact hL'
    rw [AnalyticTriple.induced_congr e₁ m L' hL' hL''] at h
    have ih := boClass_induced_concat_aux (T.headTriple m hY (T.isOfOrderGe_head_of_cons m hY hL))
      rest L' m (T.isOfOrderGe_tail_of_cons m hY hL) hL'' (T.isOfOrderGe_tail_of_cons m hY hC) h
    change AnalyticTriple.BOClass m (T.induced m (BlowUpSequence.cons hY (rest.concat L')) hC)
    rw [AnalyticTriple.induced_cons T m hY hC]
    exact ih

end BMOmod

/-! ### The class of the induced triple of a composite -/

namespace AnalyticFamilyFunctor

open _root_.Manifold

variable {Dom₁ Dom₂ : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
  (F : AnalyticFamilyFunctor ψ₀ Dom₁) (G : AnalyticFamilyFunctor ψ₀ Dom₂) (s : ℕ)
  (hF : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))),
    ((F.fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I s
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf)
  (hFG : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))),
    Dom₂ ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).induced s
      ((F.fam T hT).seqOn U hU) (hF T hT U hU)))
  {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T)
  (W : Opens M) (hW : IsCompact (closure (W : Set M))) (V : Opens M)
  (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)

/-- The class `BOClass s` of the triple induced by the list `alongList` of the link over `(W, V)`,
from the class of the triple induced by the appended value (`G` at the induced triple of the first
list of `F`, restricted to the reading open): the `shrinkAppend` is a concatenation of the
pulled-back first list and the pulled-back appended value (`induced_pullback`,
`boClass_classPullbackClosed`, `boClass_induced_concat_aux`), the restricted triple rewritten by
`pullback_inclusion_restrictLE`. -/
theorem boClass_induced_alongList
    (hAV : (appendValue F G s hF hFG T hT W hW V hV hVW).toSuccession.IsOfOrderGe
      ((inducedOfFirst F s hF T hT W hW).pullback
        (((firstList F T hT W hW).stage (Fin.last _)).inclusion (firstReadOpen F T hT W hW V hVW))
        (isLocalDiffeomorph_inclusion _ _)).I s
      ((inducedOfFirst F s hF T hT W hW).pullback
        (((firstList F T hT W hW).stage (Fin.last _)).inclusion (firstReadOpen F T hT W hW V hVW))
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf)
    (hA : AnalyticTriple.BOClass s (((inducedOfFirst F s hF T hT W hW).pullback
        (((firstList F T hT W hW).stage (Fin.last _)).inclusion (firstReadOpen F T hT W hW V hVW))
        (isLocalDiffeomorph_inclusion _ _)).induced s
      (appendValue F G s hF hFG T hT W hW V hV hVW) hAV))
    (hAL : (alongList F G s hF hFG T hT W hW V hV hVW).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).I s
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).F.idealSheaf) :
    AnalyticTriple.BOClass s ((T.pullback (M.inclusion V)
      (isLocalDiffeomorph_inclusion M V)).induced s
      (alongList F G s hF hFG T hT W hW V hV hVW) hAL) := by
  have hρ := isLocalDiffeomorph_restrictLE (ChainState.le_of_closure_subset hVW)
  have hL₁ := (firstTriple T W).isOfOrderGe_pullback s (firstList F T hT W hW) (hF T hT W hW)
    (M.restrictLE (ChainState.le_of_closure_subset hVW)) hρ
  have hlift := (firstList F T hT W hW).isLocalDiffeomorph_liftCorestrict
    (M.restrictLE (ChainState.le_of_closure_subset hVW)) hρ
  have hL₂ := AnalyticTriple.isOfOrderGe_pullback _ s _ hAV
    ((firstList F T hT W hW).liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW)) hρ)
    hlift
  have e : ((inducedOfFirst F s hF T hT W hW).pullback
        (((firstList F T hT W hW).stage (Fin.last _)).inclusion (firstReadOpen F T hT W hW V hVW))
        (isLocalDiffeomorph_inclusion _ _)).pullback
        ((firstList F T hT W hW).liftCorestrict
          (M.restrictLE (ChainState.le_of_closure_subset hVW)) hρ)
        hlift =
      ((firstTriple T W).pullback (M.restrictLE (ChainState.le_of_closure_subset hVW)) hρ).induced s
        ((firstList F T hT W hW).pullback (M.restrictLE (ChainState.le_of_closure_subset hVW)) hρ)
        hL₁ := by
    rw [AnalyticTriple.pullback_pullback _ _ _ _ _,
      AnalyticTriple.pullback_eq_of_eq _ (BlowUpSequence.inclusion_comp_liftCorestrict _ _ hρ) _
        (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ hρ)]
    exact AnalyticTriple.induced_pullback (firstTriple T W) s (firstList F T hT W hW) (hF T hT W hW)
      _ hρ hL₁
  have hL₂' : ((appendValue F G s hF hFG T hT W hW V hV hVW).pullback
      ((firstList F T hT W hW).liftCorestrict
        (M.restrictLE (ChainState.le_of_closure_subset hVW)) hρ)
      hlift).toSuccession.IsOfOrderGe
      (((firstTriple T W).pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          hρ).induced s
        ((firstList F T hT W hW).pullback (M.restrictLE (ChainState.le_of_closure_subset hVW)) hρ)
        hL₁).I s
      (((firstTriple T W).pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
          hρ).induced s
        ((firstList F T hT W hW).pullback (M.restrictLE (ChainState.le_of_closure_subset hVW)) hρ)
        hL₁).F.idealSheaf := by
    rw [← e]; exact hL₂
  -- the class of the pulled-back appended value's induced triple
  have hA' := boClass_classPullbackClosed s _
    ((appendValue F G s hF hFG T hT W hW V hV hVW).pullbackLiftLast
      ((firstList F T hT W hW).liftCorestrict
        (M.restrictLE (ChainState.le_of_closure_subset hVW)) hρ)
      hlift)
    (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _) hA
  rw [AnalyticTriple.induced_pullback _ s _ hAV _ _ hL₂,
    AnalyticTriple.induced_congr e s _ hL₂ hL₂'] at hA'
  -- the concatenation
  have hC : ((firstList F T hT W hW).pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
      hρ).concat ((appendValue F G s hF hFG T hT W hW V hV hVW).pullback
        ((firstList F T hT W hW).liftCorestrict (M.restrictLE (ChainState.le_of_closure_subset hVW))
          hρ) hlift) |>.toSuccession.IsOfOrderGe
      ((firstTriple T W).pullback (M.restrictLE (ChainState.le_of_closure_subset hVW)) hρ).I s
      ((firstTriple T W).pullback (M.restrictLE (ChainState.le_of_closure_subset hVW))
        hρ).F.idealSheaf := by
    rw [AnalyticTriple.pullback_inclusion_restrictLE T (ChainState.le_of_closure_subset hVW)]
    exact hAL
  have h₃ := BMOmod.boClass_induced_concat_aux _ _ _ s hL₁ hL₂' hC hA'
  rw [AnalyticTriple.induced_congr
    (AnalyticTriple.pullback_inclusion_restrictLE T (ChainState.le_of_closure_subset hVW)) s _ hC
    hAL] at h₃
  exact h₃

/-- The class `BOClass s` of the triple induced by the value `composeAlong` of the composite over
`(W, V) ∋ U`, from the class at `alongList`: the restriction to `U` (`induced_pullback`,
`boClass_classPullbackClosed`, `pullback_inclusion_restrictLE`) and the deletion of the empty
blow-ups (`boClass_induced_eraseEmpty`). -/
theorem boClass_induced_composeAlong (U : Opens M) (hUV : U ≤ V)
    (hAL : (alongList F G s hF hFG T hT W hW V hV hVW).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).I s
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).F.idealSheaf)
    (hA : AnalyticTriple.BOClass s ((T.pullback (M.inclusion V)
      (isLocalDiffeomorph_inclusion M V)).induced s
      (alongList F G s hF hFG T hT W hW V hV hVW) hAL))
    (hC : (composeAlong F G s hF hFG T hT W V hW hV hVW U hUV).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I s
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf) :
    AnalyticTriple.BOClass s ((T.pullback (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U)).induced s
      (composeAlong F G s hF hFG T hT W V hW hV hVW U hUV) hC) := by
  have hL₁ := AnalyticTriple.isOfOrderGe_pullback _ s _ hAL (M.restrictLE hUV)
    (isLocalDiffeomorph_restrictLE hUV)
  have h₁ := boClass_classPullbackClosed s _
    ((alongList F G s hF hFG T hT W hW V hV hVW).pullbackLiftLast (M.restrictLE hUV)
      (isLocalDiffeomorph_restrictLE hUV))
    (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _) hA
  rw [AnalyticTriple.induced_pullback _ s _ hAL _ _ hL₁] at h₁
  have hL₁' : ((alongList F G s hF hFG T hT W hW V hV hVW).pullback (M.restrictLE hUV)
      (isLocalDiffeomorph_restrictLE hUV)).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I s
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf := by
    rw [← AnalyticTriple.pullback_inclusion_restrictLE T hUV]; exact hL₁
  rw [AnalyticTriple.induced_congr (AnalyticTriple.pullback_inclusion_restrictLE T hUV) s _ hL₁
    hL₁'] at h₁
  exact AnalyticTriple.boClass_induced_eraseEmpty _ s _ hL₁' hC h₁

end AnalyticFamilyFunctor

/-! ### At the standard model: the terminal bound of the rounds at the value, and the composite -/

namespace BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
  (hT : AnalyticTriple.BMOClass 1 T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

/-- **The terminal bound of the rounds at the value**: the nonmonomial part of the triple induced by
the value of the rounds on `U` at `m = 1`, `t = 2` has order `≤ 1` everywhere ("until we drop
`max ord N(I)` to 1", [Wlo09, Theorem 7.4.1]): `stepAChainState_bound` (the bound at the induced
triple of the chain state) transported along the restriction (`induced_pullback`,
`nonmonomialOrdLe_pullback`) and the deletion of empty blow-ups
(`nonmonomialOrdLe_induced_eraseEmpty`). -/
theorem nonmonomialOrdLe_induced_stepAFamOn (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    NonmonomialOrdLe ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).induced 1
      (stepAFamOn T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU)
      (stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU)) 1 := by
  have hUW : U ≤ stepAChainOpens U hU (stepALinks T 2 U hU) := le_stepAChainOpens U hU _
  -- (1) the chain state's bound at `t = 2`, i.e. `≤ 1`
  have hb := stepAChainState_bound T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU
  -- (2) transported to the un-erased list on `U`
  have hL₁ := AnalyticTriple.isOfOrderGe_pullback _ 1 _
    (stepAChainState T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU).hge
    (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)
  have h₁ : NonmonomialOrdLe (((T.pullback (M.inclusion _)
      (isLocalDiffeomorph_inclusion M _)).pullback
      (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)).induced 1
      ((stepAChainState T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU).L.pullback (M.restrictLE hUW)
        (isLocalDiffeomorph_restrictLE hUW)) hL₁) 1 := by
    rw [← AnalyticTriple.induced_pullback _ 1 _ _ (M.restrictLE hUW)
      (isLocalDiffeomorph_restrictLE hUW) hL₁]
    exact nonmonomialOrdLe_pullback hcomp hb _ _
  have hL₂ : ((stepAChainState T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU).L.pullback
      (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf := by
    rw [← AnalyticTriple.pullback_inclusion_restrictLE T hUW]; exact hL₁
  rw [AnalyticTriple.induced_congr (AnalyticTriple.pullback_inclusion_restrictLE T hUW) 1 _ hL₁ hL₂]
    at h₁
  -- (3) the deletion of empty blow-ups
  exact nonmonomialOrdLe_induced_eraseEmpty _ 1 _ hL₂ _ h₁

/-- **The composite of the rounds with the monomial phase**: the rounds at `m = 1`, `t = 2`, then
the monomial phase at the induced triple, as the `composeInduced` of the two family functors, with
the class hypotheses of `BMOClass 1` (`bmoClass_inducedTriple`, `bmoClass_classPullbackClosed`,
`bmoClass_classInducedEraseEmptyClosed`). This is the modified second step of
[Wlo09, Theorem 7.4.1]. -/
noncomputable def stepACFunctor :
    AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (AnalyticTriple.BMOClass 1) :=
  AnalyticFamilyFunctor.composeInduced (stepAFunctor 1 bo hcomp hid 2 le_rfl one_le_two)
    (step2bFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) 1
    (fun T hT U hU => stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU)
    (fun T hT U hU => AnalyticTriple.bmoClass_inducedTriple _ (bmoClass_restrict T hT U) 1 _
      (stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU))
    (stepAFunctor_commutesWithLocalIsos 1 bo hcomp hid 2 le_rfl one_le_two)
    step2bFunctor_commutesWithLocalIsos step2bFunctor_indifferentToEmptyMembers
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    (AnalyticFamilyFunctor.bmoClass_classInducedEraseEmptyClosed 1 1)
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)

/-- The order clause of the composite at the mark `1`. -/
theorem stepACFunctor_isOfOrderGe (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (((stepACFunctor bo hcomp hid).fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf :=
  AnalyticFamilyFunctor.composeInduced_isOfOrderGe (stepAFunctor 1 bo hcomp hid 2 le_rfl one_le_two)
    (step2bFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) 1
    (fun T hT U hU => stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU)
    (fun T hT U hU => AnalyticTriple.bmoClass_inducedTriple _ (bmoClass_restrict T hT U) 1 _
      (stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU))
    (stepAFunctor_commutesWithLocalIsos 1 bo hcomp hid 2 le_rfl one_le_two)
    step2bFunctor_commutesWithLocalIsos step2bFunctor_indifferentToEmptyMembers
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    (AnalyticFamilyFunctor.bmoClass_classInducedEraseEmptyClosed 1 1)
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    (fun T' hT' U' hU' => step2bFam_isOfOrderGe T' hT' U' hU') T hT U hU

/-- **The triple induced by the value of the composite on `U` is in `BOClass 1`** (the hypothesis of
the next step of the modified algorithm): the value is the `shrinkAppend` of `alongList` restricted
and cleaned (`boClass_induced_composeAlong`, `boClass_induced_alongList`);
`boClass_one_induced_step2bFam` at the induced triple of the first list of the rounds, whose bound
on the nonmonomial part is `nonmonomialOrdLe_induced_stepAFamOn` pulled back to the reading open
(`nonmonomialOrdLe_pullback`). -/
theorem boClass_one_induced_stepACFunctor (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    AnalyticTriple.BOClass 1 ((T.pullback (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U)).induced 1
      (((stepACFunctor bo hcomp hid).fam T hT).seqOn U hU)
      (stepACFunctor_isOfOrderGe T hT bo hcomp hid U hU)) := by
  refine AnalyticFamilyFunctor.boClass_induced_composeAlong
    (stepAFunctor 1 bo hcomp hid 2 le_rfl one_le_two)
    (step2bFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) 1
    (fun T hT U hU => stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU)
    (fun T hT U hU => AnalyticTriple.bmoClass_inducedTriple _ (bmoClass_restrict T hT U) 1 _
      (stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU))
    T hT (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 0)
    (isCompact_closure_chainOpens _ _ _ _)
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1)
    (isCompact_closure_chainOpens _ _ _ _)
    (closure_chainOpens_succ_subset _ _ _ Nat.zero_lt_one) U (le_chainOpens_last _ hU 1)
    (AnalyticFamilyFunctor.alongList_isOfOrderGe _ _ 1 _ _ T hT _ _ _ _ _
      (fun T' hT' U' hU' => step2bFam_isOfOrderGe T' hT' U' hU'))
    ?_ (stepACFunctor_isOfOrderGe T hT bo hcomp hid U hU)
  refine AnalyticFamilyFunctor.boClass_induced_alongList
    (stepAFunctor 1 bo hcomp hid 2 le_rfl one_le_two)
    (step2bFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) 1
    (fun T hT U hU => stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU)
    (fun T hT U hU => AnalyticTriple.bmoClass_inducedTriple _ (bmoClass_restrict T hT U) 1 _
      (stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU))
    T hT (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 0)
    (isCompact_closure_chainOpens _ _ _ _)
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1)
    (isCompact_closure_chainOpens _ _ _ _)
    (closure_chainOpens_succ_subset _ _ _ Nat.zero_lt_one)
    (step2bFam_isOfOrderGe _ _ _ _) ?_ _
  exact boClass_one_induced_step2bFam _ _ _ _
    (nonmonomialOrdLe_pullback hcomp
      (nonmonomialOrdLe_induced_stepAFamOn T hT bo hcomp hid _ _) _ _)

end BMOmod

end Hironaka.Manifold

end
