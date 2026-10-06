/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.Embedded
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.OffCenters
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedDisjoint
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.Wlo05.FirstCenterLocalIso
import Hironaka.Scheme.BlowUp.FlatColon
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.OrdMaximalIdeal
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The nonmonomial part at the generic point of a strict transform

The hypothesis of Włodarczyk's Claim in the proof of [Wlo05, Theorem 4.7.1]: `I = I_{Y₁}` near a
generic point `η` of `Y₁`, `η` on no member of the boundary. Before the first centre containing the
strict transform `c̃` of `c = I_{Y₁}` (the proof of [Kol07, Corollary 22]) the stage map is an
isomorphism on stalks at the generic point `η̃` of `c̃`, and no exceptional or boundary component
passes through `η̃` (`isIso_stalkMap_stageMap_of_forall_notMem`,
`notMem_support_totalTransformSeq_of_forall_notMem`). So the monomial part is the unit ideal at
`η̃`, the nonmonomial part is the marked transform itself, and its stalk is the image of
`I_η = 𝔪_η` under the isomorphism: `N(I_i)_{η̃} = 𝔪_{η̃}`, of order `1` (`ord_maximalIdeal_eq_one`;
`I` is nonzero at `η`). Together with `not_centerContains_of_leOrdAlong_two`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimTools`) this places the first containing centre
in the round of order `1` of Step 1 of the proof of [Kol07, Theorem 107]. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedGenericLift` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimStep1`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka BlowUpSequence
  Scheme.IdealSheafData IsLocalRing Hironaka.BMO Hironaka.Sequence

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- The hypothesis of Włodarczyk's Claim transported to a stage before the first containing centre:
at a point `η'` over `η` lying over no earlier centre, the marked transform (of any mark) of an
ideal sheaf `J` agreeing with `vanishingIdeal (closure {η})` at `η` has the maximal ideal as its
stalk — the image of `J_η = 𝔪_η` under the stalk isomorphism of the stage map. -/
theorem stalkIdeal_markedTransformSeq_eq_maximalIdeal
    (S : BlowUpSequence X) (J : X.IdealSheafData) (c : ℕ) {η : X}
    (hJ : J.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (i : Fin (S.length + 1)) {η' : S.stage i} (hmap : S.stageMap i η' = η)
    (h : ∀ (m : Fin S.length) (hmi : m.val < i.val),
      S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) η' ∉ (S.center m).support) :
    (S.markedTransformSeq J c i).stalkIdeal η' = maximalIdeal ((S.stage i).presheaf.stalk η') := by
  subst hmap
  have hiso := isIso_stalkMap_stageMap_of_forall_notMem S i η' h
  have hsurj : Function.Surjective ((S.stageMap i).stalkMap η').hom :=
    (asIso ((S.stageMap i).stalkMap η')).commRingCatIsoToRingEquiv.surjective
  rw [stalkIdeal_markedTransformSeq_of_forall_notMem S J c i η' h, hJ,
    stalkIdeal_vanishingIdeal_closure_self]
  exact map_maximalIdeal_of_surjective _ hsurj

/-- Under the hypotheses of `stalkIdeal_markedTransformSeq_eq_maximalIdeal`, with `J` nonzero at
`η`, the marked transform has order exactly `1` at `η'` ([Kol07, Definition 47] at the generic
point) — its stalk is the maximal ideal, nonzero since it is the image of `J_η ≠ 0` under an
isomorphism. -/
theorem ord_markedTransformSeq_eq_one (S : BlowUpSequence X)
    (J : X.IdealSheafData) (c : ℕ) {η : X}
    (hJ : J.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (hJ0 : J.stalkIdeal η ≠ ⊥) (i : Fin (S.length + 1)) [IsLocallyNoetherian (S.stage i)]
    {η' : S.stage i}
    (hmap : S.stageMap i η' = η)
    (h : ∀ (m : Fin S.length) (hmi : m.val < i.val),
      S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) η' ∉ (S.center m).support) :
    (S.markedTransformSeq J c i).ord η' = 1 := by
  have hst := stalkIdeal_markedTransformSeq_eq_maximalIdeal S J c hJ i hmap h
  subst hmap
  have hiso := isIso_stalkMap_stageMap_of_forall_notMem S i η' h
  have hbij : Function.Bijective ((S.stageMap i).stalkMap η').hom :=
    (asIso ((S.stageMap i).stalkMap η')).commRingCatIsoToRingEquiv.bijective
  refine IdealSheafData.ord_eq_one_of_stalkIdeal_eq_maximalIdeal _ hst fun hbot => hJ0 ?_
  rw [hJ, stalkIdeal_vanishingIdeal_closure_self]
  refine (Ideal.map_eq_bot_iff_of_injective hbij.1).mp ?_
  rw [map_maximalIdeal_of_surjective _ hbij.2]
  exact hbot

/-- The monomial part of any ideal sheaf at a point over `η ∉ E` lying over no earlier centre is
the unit ideal: no member of the total transform of `E` passes through the point. -/
theorem stalkIdeal_monomialPart_totalTransformSeq_eq_top [IsLocallyNoetherian X]
    (S : BlowUpSequence X) (E : DivisorFamily X) {η : X}
    (hηE : ∀ j, η ∉ (E.component j).support) (i : Fin (S.length + 1))
    [NoetherianSpace (S.stage i)] (K : (S.stage i).IdealSheafData) {η' : S.stage i}
    (hmap : S.stageMap i η' = η)
    (h : ∀ (m : Fin S.length) (hmi : m.val < i.val),
      S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) η' ∉ (S.center m).support) :
    (monomialPart K (S.totalTransformSeq E i)).stalkIdeal η' = ⊤ := by
  subst hmap
  refine stalkIdeal_monomialPart_eq_top_of_forall_notMem _ _ fun j => ?_
  refine notMem_component_support_of_notMem_support _ ?_ j
  refine notMem_support_totalTransformSeq_of_forall_notMem S E i η' h fun hηs => ?_
  rw [← SetLike.mem_coe, DivisorFamily.coe_support_eq_iUnion] at hηs
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hηs
  exact hηE j hj

/-- The nonmonomial part of the marked transform of `I` at a point over `η ∉ E` lying over no
earlier centre, with respect to the total transform of `E`, has the maximal ideal as its stalk —
the monomial part is the unit ideal there (`stalkIdeal_monomialPart_totalTransformSeq_eq_top`) and
the marked transform's stalk is the maximal ideal
(`stalkIdeal_markedTransformSeq_eq_maximalIdeal`). -/
theorem stalkIdeal_nonmonomialPart_markedTransformSeq_eq_maximalIdeal [IsLocallyNoetherian X]
    (S : BlowUpSequence X) (I : X.IdealSheafData) (E : DivisorFamily X) {η : X}
    (hηE : ∀ j, η ∉ (E.component j).support)
    (hIc : I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (i : Fin (S.length + 1)) [NoetherianSpace (S.stage i)]
    {η' : S.stage i} (hmap : S.stageMap i η' = η)
    (h : ∀ (m : Fin S.length) (hmi : m.val < i.val),
      S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) η' ∉ (S.center m).support) :
    (nonmonomialPart (S.markedTransformSeq I 1 i) (S.totalTransformSeq E i)).stalkIdeal η' =
      maximalIdeal ((S.stage i).presheaf.stalk η') := by
  have := isLocallyNoetherian_stage S i
  unfold nonmonomialPart
  rw [IdealSheafData.stalkIdeal_colon_of_isLocallyNoetherian,
    stalkIdeal_monomialPart_totalTransformSeq_eq_top S E hηE i _ hmap h, Submodule.top_coe,
    Submodule.colon_univ]
  exact stalkIdeal_markedTransformSeq_eq_maximalIdeal S I 1 hIc i hmap h

/-- Under the hypotheses of `stalkIdeal_nonmonomialPart_markedTransformSeq_eq_maximalIdeal`, with
`I` nonzero at `η`, the nonmonomial part of the marked transform has order exactly `1` at `η'`
([Kol07, Definition 47] at the generic point) — its stalk is the maximal ideal, nonzero since it is
the image of `I_η ≠ 0` under an isomorphism. -/
theorem ord_nonmonomialPart_markedTransformSeq_eq_one [IsLocallyNoetherian X]
    (S : BlowUpSequence X) (I : X.IdealSheafData) (E : DivisorFamily X) {η : X}
    (hηE : ∀ j, η ∉ (E.component j).support)
    (hIc : I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (hI0 : I.stalkIdeal η ≠ ⊥) (i : Fin (S.length + 1))
    [NoetherianSpace (S.stage i)] {η' : S.stage i} (hmap : S.stageMap i η' = η)
    (h : ∀ (m : Fin S.length) (hmi : m.val < i.val),
      S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) η' ∉ (S.center m).support) :
    (nonmonomialPart (S.markedTransformSeq I 1 i) (S.totalTransformSeq E i)).ord η' = 1 := by
  have := isLocallyNoetherian_stage S i
  have hst :=
    stalkIdeal_nonmonomialPart_markedTransformSeq_eq_maximalIdeal S I E hηE hIc i hmap h
  have hone := ord_markedTransformSeq_eq_one S I 1 hIc hI0 i hmap h
  rw [IdealSheafData.ord_eq_ord_stalkIdeal, stalkIdeal_markedTransformSeq_eq_maximalIdeal S I 1 hIc
      i hmap h]
    at hone
  rw [IdealSheafData.ord_eq_ord_stalkIdeal, hst]
  exact hone

variable {k : Type u} [Field k] [CharZero k]

/-- The hypothesis of Włodarczyk's Claim along the run of `BMO_1` (the proof of
[Kol07, Corollary 22]): for a marked triple `T`, a point `η` on no member of `T.E` at which `T.I`
agrees with `c := vanishingIdeal (closure {η})`, and a stage `i` of the run of `BMO_1` on `T` at or
before the first centre containing the strict transform of `c`, that strict transform has a
generic point `η'` over `η` at which the nonmonomial part of the induced marked ideal has order
`1`. -/
theorem exists_genericPoint_ord_nonmonomialPart_bmoOneRun_eq_one (T : MarkedTriple k)
    (hm : T.m = 1) {η : T.X.left} (hηE : ∀ j, η ∉ (T.E.component j).support)
    (hIc : T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (i : Fin ((bmoOneRun T hm).length + 1))
    (hi : i.val ≤ firstCenterIndex (bmoOneRun T hm) (IdealSheafData.vanishingIdeal (Closeds.closure
        {η}))) :
    ∃ η' : (bmoOneRun T hm).stage i,
      IsGenericPoint η' (((bmoOneRun T hm).strictTransformSeq
        (IdealSheafData.vanishingIdeal (Closeds.closure {η})) i).support : Set
            ((bmoOneRun T hm).stage i)) ∧
      (bmoOneRun T hm).stageMap i η' = η ∧
      (nonmonomialPart ((bmoOneRun T hm).markedTransformSeq T.I 1 i)
        ((bmoOneRun T hm).totalTransformSeq T.E i)).ord η' = 1 := by
  have hrun := isOrderGeSeq_bmoOneRun T hm
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have := isIntegral_subscheme_vanishingIdeal_closure η
  obtain ⟨η', hgen, hmap, -, havoid, -⟩ :=
    exists_isGenericPoint_strictTransformSeq_and_isIso_of_le_firstCenterIndex (bmoOneRun T hm) _
      (isGenericPoint_support_vanishingIdeal_closure η) i hi
  have hlN : IsLocallyNoetherian ((bmoOneRun T hm).stage i) :=
    ((T.induced (bmoOneRun T hm) hrun i).X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hNoeth : NoetherianSpace ((bmoOneRun T hm).stage i) :=
    Hironaka.BD.noetherianSpace_triple (T.induced (bmoOneRun T hm) hrun i).toTriple
  exact ⟨η', hgen, hmap, ord_nonmonomialPart_markedTransformSeq_eq_one (bmoOneRun T hm) T.I T.E
    hηE hIc (T.isNonzeroEverywhere η) i hmap havoid⟩

end Hironaka.Resolution
