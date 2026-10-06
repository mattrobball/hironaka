/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedProtected
import Hironaka.Resolution.Algebraic.Kol07.StrictTransformSupport
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedIsolation
import Hironaka.Resolution.Algebraic.Wlo05.OffCentreTransport
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The state of the loop and its end result

Włodarczyk proves the clauses of [Wlo05, Theorem 4.7.1] (the strict transforms of the components
smooth and disjoint, the full transform of `I_Y` its monomial part times `I_Ỹ`) by an invariant
carried along the passes of the modified run. Here the invariant is a predicate on the state
`(X, I, E, C, Γ)` of the loop `BED` (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) — the members
`C` still to be absorbed and the protected components `Γ` already isolated:

* `EmbeddedStateData`: the invariant `InvCE` for the members
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`); each protected component has simple
  normal crossings with the boundary and is contained in no member near any point; the protected
  components are pairwise disjoint and disjoint from the members; and the nonmonomial part of the
  marked ideal is trivial along them;
* `EmbeddedEndData` and `EmbeddedEnd`: what holds at the end of the loop on that state — the final
  marked transform of `I` is the product of the final strict transforms of the members (`I_r = I_Ỹ`,
  the content of `σ^*(I_Y) = M(σ^*(I_Y)) · I_Ỹ` in [Wlo05, Theorem 4.7.1] once the monomial factor
  of [Kol07, 72] is supplied), each protected component's ideal pulls back to its strict transform,
  every final strict transform has simple normal crossings with the final boundary, and they are
  pairwise disjoint.

The definitions are used by the proof of the theorem
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCPBridge`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedEndBridge`). The theorems of this module — the
dichotomy for a run of `BMO_1` from the hypothesis `CentersInNonmonomialSupportOrStratum`, the
protected transport along the run from `StratumBlowUp`, and the base case of the loop
`embeddedEnd_bmoOneRun` (a run of `BMO_1` with no member left: the protected transport along the
whole run, and `I_r = 𝒪` at the end of the run by [Kol07, Theorem 69 (1)]) — are CONDITIONAL on
those two unproved hypotheses and are not used by the proof of the theorem.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- **The state of the loop** `(I, E, C, Γ)` (the invariant of the proof of
[Wlo05, Theorem 4.7.1]): the members `C` satisfy `InvCE`; every protected component `γ ∈ Γ` has
simple normal crossings with the boundary and is contained in no member near any of its points;
the protected components are pairwise disjoint and disjoint from the members; and the nonmonomial
part of `I` is trivial along them. -/
structure EmbeddedStateData {Y : Scheme.{u}} (I : Y.IdealSheafData) (E : DivisorFamily Y)
    (C Γ : Finset Y.IdealSheafData) : Prop where
  invCE : InvCE I E C
  snc : ∀ γ ∈ Γ, E.HasSncWith γ
  notContained : ∀ γ ∈ Γ, NotContainedInMembers E γ
  pairwise : (Γ : Set Y.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support
  disjointCΓ : ∀ c ∈ C, ∀ γ ∈ Γ, Disjoint c.support γ.support
  nonmonomial : ∀ γ ∈ Γ, Disjoint (nonmonomialPart I E).support γ.support

open Classical in
/-- The conclusions of [Wlo05, Theorem 4.7.1] at the end of the loop on a state, on the end data —
the final boundary `Eend`, the final marked transform `Iend`, the final strict transform `zEnd z`
of a closed subscheme `z`, and the pull-back `cEnd z` of its ideal along the composite: `Iend` is
the product of the members' final strict transforms, each protected component pulls back to its
strict transform, the final strict transforms of members and protected components have simple
normal crossings with the final boundary, and they are pairwise disjoint. -/
structure EmbeddedEndData {Y Yend : Scheme.{u}} (Eend : DivisorFamily Yend)
    (Iend : Yend.IdealSheafData) (zEnd cEnd : Y.IdealSheafData → Yend.IdealSheafData)
    (C Γ : Finset Y.IdealSheafData) : Prop where
  marked_eq : Iend = ∏ c ∈ C, zEnd c
  comap_eq : ∀ γ ∈ Γ, cEnd γ = zEnd γ
  snc : ∀ z ∈ C ∪ Γ, Eend.HasSncWith (zEnd z)
  pairwise : ((C ∪ Γ : Finset Y.IdealSheafData) : Set Y.IdealSheafData).Pairwise fun a b =>
    Disjoint (zEnd a).support (zEnd b).support

/-- `EmbeddedEndData` at the end of a blow-up sequence `S` on the marked triple `T`. -/
def EmbeddedEnd (T : MarkedTriple k) (C Γ : Finset T.X.left.IdealSheafData)
    (S : BlowUpSequence T.X.left) : Prop :=
  EmbeddedEndData (S.totalTransformSeq T.E (Fin.last _)) (S.markedTransformSeq T.I 1 (Fin.last _))
    (fun z => S.strictTransformSeq z (Fin.last _)) (fun z => z.comap S.composite) C Γ

/-- The state transports across a cast of the ambient scheme. -/
theorem EmbeddedStateData.of_heq {Y Y' : Scheme.{u}} (h : Y = Y') {I : Y.IdealSheafData}
    {I' : Y'.IdealSheafData} {E : DivisorFamily Y} {E' : DivisorFamily Y'}
    {C Γ : Finset Y.IdealSheafData} {C' Γ' : Finset Y'.IdealSheafData} (hI : HEq I I')
    (hE : HEq E E') (hC : HEq C C') (hΓ : HEq Γ Γ') (hs : EmbeddedStateData I' E' C' Γ') :
    EmbeddedStateData I E C Γ := by
  subst h
  rw [eq_of_heq hI, eq_of_heq hE, eq_of_heq hC, eq_of_heq hΓ]
  exact hs

/-- The end data transport across a cast of the end scheme. -/
theorem EmbeddedEndData.of_heq {Y Yend Yend' : Scheme.{u}} (h : Yend = Yend')
    {Eend : DivisorFamily Yend} {Eend' : DivisorFamily Yend'} {Iend : Yend.IdealSheafData}
    {Iend' : Yend'.IdealSheafData} {zEnd cEnd : Y.IdealSheafData → Yend.IdealSheafData}
    {zEnd' cEnd' : Y.IdealSheafData → Yend'.IdealSheafData} (hE : HEq Eend Eend')
    (hI : HEq Iend Iend') (hz : HEq zEnd zEnd') (hc : HEq cEnd cEnd')
    {C Γ : Finset Y.IdealSheafData} (hs : EmbeddedEndData Eend' Iend' zEnd' cEnd' C Γ) :
    EmbeddedEndData Eend Iend zEnd cEnd C Γ := by
  subst h
  rw [eq_of_heq hE, eq_of_heq hI, eq_of_heq hz, eq_of_heq hc]
  exact hs

/-- The dichotomy of the isolation passage for a run of `BMO_1`, from the hypothesis
`CentersInNonmonomialSupportOrStratum`: a closed subscheme along which the nonmonomial part of the
marked ideal is trivial is missed by every centre lying in the nonmonomial support, the other
centres being strata. -/
theorem missesOrStratum_bmoOneRun (hL : CentersInNonmonomialSupportOrStratum k)
    (T : MarkedTriple k) (hm : T.m = 1) {γ : T.X.left.IdealSheafData}
    (hγ : Disjoint (nonmonomialPart T.I T.E).support γ.support) :
    MissesOrStratum (bmoOneRun T hm) T.E γ := by
  intro i
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  rcases (hL T hm).1 i with hN | hstr
  · left
    refine disjoint_closeds_iff.mpr fun p hp hpγ => ?_
    have hpN : p ∈ (nonmonomialPart ((bmoOneRun T hm).markedTransformSeq T.I 1 i.castSucc)
        ((bmoOneRun T hm).totalTransformSeq T.E i.castSucc)).support := by
      by_contra hnot
      exact hN p hp (IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ hnot)
    exact notMem_of_disjoint_closeds hγ ((hL T hm).2 i.castSucc p hpN)
      (stageMap_mem_support_of_mem_support_strictTransformSeq _ γ i.castSucc hpγ)
  · exact Or.inr hstr

/-- The protected transport along a run of `BMO_1` on a state (conditional on `StratumBlowUp` and
`CentersInNonmonomialSupportOrStratum`): the strict transform of every protected component has
simple normal crossings with the boundary at every stage, is contained in no member, and is the
pull-back of the ideal of the component. -/
theorem EmbeddedStateData.protected_transport_bmoOneRun (hG : StratumBlowUp k)
    (hL : CentersInNonmonomialSupportOrStratum k) {T : MarkedTriple k} {hm : T.m = 1}
    {C Γ : Finset T.X.left.IdealSheafData} (hs : EmbeddedStateData T.I T.E C Γ)
    {γ : T.X.left.IdealSheafData} (hγ : γ ∈ Γ) (i : Fin ((bmoOneRun T hm).length + 1)) :
    ((bmoOneRun T hm).totalTransformSeq T.E i).HasSncWith
        ((bmoOneRun T hm).strictTransformSeq γ i) ∧
      NotContainedInMembers ((bmoOneRun T hm).totalTransformSeq T.E i)
        ((bmoOneRun T hm).strictTransformSeq γ i) ∧
      γ.comap ((bmoOneRun T hm).stageMap i) = (bmoOneRun T hm).strictTransformSeq γ i := by
  have hrun := isOrderGeSeq_bmoOneRun T hm
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  exact protected_transport hG (bmoOneRun T hm) (T.X.left ↘ Spec (.of k)) T.E γ
    (fun i => IsSmooth.smooth_stageMap (n := d) hrun.1 i) T.isSnc (fun i => (hrun.2 i).1)
    (missesOrStratum_bmoOneRun hL T hm (hs.nonmonomial γ hγ)) (hs.snc γ hγ)
    (hs.notContained γ hγ) i

/-- **The base case of the loop** (conditional on `StratumBlowUp` and
`CentersInNonmonomialSupportOrStratum`): on a state with no member left, the run of `BMO_1` ends
with the unit marked ideal ([Kol07, Theorem 69 (1)] at the mark `1`), and the protected components
pull back to their strict transforms, which have simple normal crossings with the final boundary
and are pairwise disjoint. -/
theorem embeddedEnd_bmoOneRun (hG : StratumBlowUp k) (hL : CentersInNonmonomialSupportOrStratum k)
    (T : MarkedTriple k) (hm : T.m = 1) (Γ : Finset T.X.left.IdealSheafData)
    (hs : EmbeddedStateData T.I T.E (∅ : Finset T.X.left.IdealSheafData) Γ) :
    EmbeddedEnd T ∅ Γ (bmoOneRun T hm) := by
  classical
  have hrun := isOrderGeSeq_bmoOneRun T hm
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hprot : ∀ γ ∈ Γ,
      ((bmoOneRun T hm).totalTransformSeq T.E (Fin.last _)).HasSncWith
          ((bmoOneRun T hm).strictTransformSeq γ (Fin.last _)) ∧
        NotContainedInMembers ((bmoOneRun T hm).totalTransformSeq T.E (Fin.last _))
          ((bmoOneRun T hm).strictTransformSeq γ (Fin.last _)) ∧
        γ.comap ((bmoOneRun T hm).stageMap (Fin.last _)) =
          (bmoOneRun T hm).strictTransformSeq γ (Fin.last _) := fun γ hγ =>
    protected_transport hG (bmoOneRun T hm) (T.X.left ↘ Spec (.of k)) T.E γ
      (fun i => IsSmooth.smooth_stageMap (n := d) hrun.1 i) T.isSnc (fun i => (hrun.2 i).1)
      (missesOrStratum_bmoOneRun hL T hm (hs.nonmonomial γ hγ)) (hs.snc γ hγ)
      (hs.notContained γ hγ) (Fin.last _)
  refine ⟨?_, fun γ hγ => (hprot γ hγ).2.2, fun z hz => ?_, ?_⟩
  · rw [markedTransformSeq_bmoOneRun_last_eq_top, Finset.prod_empty, IdealSheafData.one_eq_top]
  · rw [Finset.empty_union] at hz
    exact (hprot z hz).1
  · intro a ha b hb hab
    rw [Finset.coe_union, Finset.coe_empty, Set.empty_union] at ha hb
    exact disjoint_strictTransformSeq_support_of_disjoint (bmoOneRun T hm) a b
      (hs.pairwise ha hb hab) (Fin.last _)

end Hironaka.Resolution
