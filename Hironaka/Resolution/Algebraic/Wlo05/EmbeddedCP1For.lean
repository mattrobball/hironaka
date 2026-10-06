/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedGenericLift
import Hironaka.Resolution.Algebraic.Wlo05.CenterContainsConcat
import Hironaka.Scheme.BlowUpSequence.ConcatIndex
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP1 along a sequence and its concatenation

`CP1For S I E η`: along the blow-up sequence `S`, at the FIRST stage whose centre contains the
strict transform of the component `c = V(closure {η})` of `V(I)`, the marked transform of `I` is
chain-relative monomial along that strict transform at every point of it (with respect to the
total transform of `E` at that stage). This is the statement CP1 of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative` as a predicate on one sequence: the form
of Włodarczyk's Claim (`ClaimFor`, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimAt`) with the
chain-relative conclusion in place of the false stalk equality. The concatenation lemma
`cp1For_concat`: the first containing stage lies in `S`, or none does and the lifted generic point
(`exists_genericLift`, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedGenericLift`) hands the question
to `R` at the end of `S`, the stages of the concatenation being read through the heterogeneous
equalities of `Hironaka.Scheme.BlowUpSequence.ConcatIndex`. Used by the CP1 modules `EmbeddedCP1At`,
`EmbeddedCP1Cons`, `EmbeddedCP1EraseEmpty`, `EmbeddedCP1Step1`, `EmbeddedCP1Step2`, and by
`EmbeddedCP1Absorbed`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData
  Hironaka.Sequence

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- **CP1 along a sequence**: at the first stage whose centre contains the strict transform of
`c = V(closure {η})`, the marked transform of `I` is chain-relative monomial along that strict
transform at each of its points. -/
def CP1For (S : BlowUpSequence X) (I : X.IdealSheafData) (E : DivisorFamily X) (η : X) : Prop :=
  ∀ i : Fin S.length, CenterContains S (IdealSheafData.vanishingIdeal (Closeds.closure {η})) i →
    (∀ l < i.val, ¬ CenterContains S (IdealSheafData.vanishingIdeal (Closeds.closure {η})) l) →
    ∀ p ∈ (S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) i.castSucc).support,
      ChainRelativeAt (S.totalTransformSeq E i.castSucc) (S.markedTransformSeq I 1 i.castSucc)
        (S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η})) i.castSucc) p

/-- The pointwise chain form transports across an equality of stages. -/
theorem forall_chainRelativeAt_of_heq {Y Y' : Scheme.{u}} (h : Y = Y') {E : DivisorFamily Y}
    {E' : DivisorFamily Y'} {I Γ : Y.IdealSheafData} {I' Γ' : Y'.IdealSheafData} (hE : HEq E E')
    (hI : HEq I I') (hΓ : HEq Γ Γ') (hc : ∀ p ∈ Γ'.support, ChainRelativeAt E' I' Γ' p) :
    ∀ p ∈ Γ.support, ChainRelativeAt E I Γ p := by
  subst h
  rw [eq_of_heq hE, eq_of_heq hI, eq_of_heq hΓ]
  exact hc

/-- CP1 along a concatenation: if `S` satisfies CP1 for `η`, and for every lift `η'` of `η` to the
end of `S` the rest `R` satisfies CP1 for `η'` (with the transformed data), then the concatenation
satisfies CP1 for `η`. -/
theorem cp1For_concat [IsLocallyNoetherian X] (S : BlowUpSequence X) (R : BlowUpSequence S.last)
    (I : X.IdealSheafData) (E : DivisorFamily X) {η : X} (hη : η ∈ I.support.genericPoints)
    (hηE : ∀ j, η ∉ (E.component j).support)
    (hIc : I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (hS : CP1For S I E η)
    (hR : ∀ η' : S.last, GenericLift S I E 1 η (Fin.last _) η' →
      CP1For R (S.markedTransformSeq I 1 (Fin.last _)) (S.totalTransformSeq E (Fin.last _)) η') :
    CP1For (S.concat R) I E η := by
  intro i hi hmin
  have hlen := length_concat S R
  rcases Nat.lt_or_ge i.val S.length with hlt | hge
  · -- the first containing stage lies in `S`
    have hi' : CenterContains S (IdealSheafData.vanishingIdeal (Closeds.closure {η})) i.val :=
      (centerContains_concat_iff_of_lt S R _ i.val hlt).mp hi
    have hmin' : ∀ l < i.val, ¬ CenterContains S (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) l :=
      fun l hl hcl =>
        hmin l hl ((centerContains_concat_iff_of_lt S R _ l (lt_trans hl hlt)).mpr hcl)
    have hS' := hS ⟨i.val, hlt⟩ hi' hmin'
    have hst := stage_concat_mk_of_le S R i.val i.castSucc.isLt (Nat.lt_succ_of_lt hlt)
    exact forall_chainRelativeAt_of_heq hst
      (totalTransformSeq_concat_heq_mk_of_le S R E i.val _ _)
      (markedTransformSeq_concat_heq_mk_of_le S R I 1 i.val _ _)
      (strictTransformSeq_concat_heq_mk_of_le S R _ i.val _ _) hS'
  · -- no centre of `S` contains `c̃`: lift and read the stage of `R`
    obtain ⟨i', hi'⟩ : ∃ i', i.val = S.length + i' := ⟨i.val - S.length, by omega⟩
    have hi'R : i' < R.length := by
      have h := i.isLt
      omega
    have hnone : ∀ l, ¬ CenterContains S (IdealSheafData.vanishingIdeal (Closeds.closure {η})) l :=
        by
      intro l hcl
      obtain ⟨hl, -⟩ := id hcl
      exact hmin l (by omega) ((centerContains_concat_iff_of_lt S R _ l hl).mpr hcl)
    obtain ⟨η', hlift⟩ :=
      exists_genericLift S I E 1 hη hηE hIc (Fin.last _) fun l _ => hnone l
    have hse : S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
        (Fin.last _) =
        (IdealSheafData.vanishingIdeal (Closeds.closure {η'}) : S.last.IdealSheafData) :=
            hlift.strict_eq
    have hcont : CenterContains R (IdealSheafData.vanishingIdeal (Closeds.closure {η'})) i' := by
      rw [← hse]
      have h : CenterContains (S.concat R) (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
          (S.length + i') := by
        rw [← hi']
        exact hi
      exact (centerContains_concat_add_iff S R _ i').mp h
    have hmin'' : ∀ l < i', ¬ CenterContains R (IdealSheafData.vanishingIdeal (Closeds.closure
        {η'})) l := by
      intro l hl hcl
      rw [← hse] at hcl
      exact hmin (S.length + l) (by omega) ((centerContains_concat_add_iff S R _ l).mpr hcl)
    have hR'' := hR η' hlift ⟨i', hi'R⟩ hcont hmin''
    have hst : (S.concat R).stage i.castSucc = R.stage ⟨i', Nat.lt_succ_of_lt hi'R⟩ :=
      stage_concat_mk S R i.val i' i.castSucc.isLt _ hi'
    have e1 := markedTransformSeq_concat_heq_mk S R I 1 i.val i' i.castSucc.isLt
      (Nat.lt_succ_of_lt hi'R) hi'
    have e3 := totalTransformSeq_concat_heq_mk S R E i.val i' i.castSucc.isLt
      (Nat.lt_succ_of_lt hi'R) hi'
    have e2 := strictTransformSeq_concat_heq_mk S R (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) i.val i'
      i.castSucc.isLt (Nat.lt_succ_of_lt hi'R) hi'
    rw [hse] at e2
    exact forall_chainRelativeAt_of_heq hst e3 e1 e2 hR''

end Hironaka.Resolution
