/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedGenericOrder
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow
import Hironaka.Resolution.Algebraic.Wlo05.FirstCenterLocalIso
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The generic point of a strict transform before the first containing centre

The hypothesis of Włodarczyk's Claim in the proof of [Wlo05, Theorem 4.7.1] — `η` a generic point
of `supp I` on no member of the boundary at which `I = I_{closure η}` — transports along any stage
`i` of a blow-up sequence before the first centre containing the strict transform of
`c = I_{closure η}` (the proof of [Kol07, Corollary 22]): the strict transform at stage `i` is the
reduced ideal of the closure of a point `η'` over `η`, `η'` is a generic point of the support of the
marked transform of `I`, lies on no member of the total transform of the boundary, and the marked
transform agrees with the strict transform at `η'`. This is the invariant `GenericLift` carried
through the proof of CP1 (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`): the
hypotheses of `CP1For` for the triple induced at stage `i` with the member `c̃_i`, read off the
corresponding hypotheses at stage `0`. The round-by-round reading of the run of `BMO_1` (Step 1 of
the proof of [Kol07, Theorem 107]) applies it at the end of each round that never contains `c̃`.
Used throughout the CP1 modules (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For`,
`EmbeddedCP1Cover`, `EmbeddedCP1Step21`, `EmbeddedCP1Step22`, …).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData
  IsLocalRing Hironaka.BMO

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- **The lift of the hypothesis of Włodarczyk's Claim to a stage** — `η'` at stage `i` lies over
`η`, the strict transform of `c := vanishingIdeal (closure {η})` at stage `i` is
`vanishingIdeal (closure {η'})`, `η'` is a generic point of the support of the marked transform of
`I` (mark `m`), lies on no member of the total transform of `E`, the marked transform agrees with
`vanishingIdeal (closure {η'})` at `η'`, `η'` lies over no earlier centre, and it is the only point
of stage `i` over `η`. -/
structure GenericLift (S : BlowUpSequence X) (I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ)
    (η : X) (i : Fin (S.length + 1)) (η' : S.stage i) : Prop where
  map : S.stageMap i η' = η
  strict_eq : S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η})) i =
    IdealSheafData.vanishingIdeal (Closeds.closure {η'})
  mem_genericPoints : η' ∈ (S.markedTransformSeq I m i).support.genericPoints
  notMem : ∀ j, η' ∉ ((S.totalTransformSeq E i).component j).support
  stalk_eq : (S.markedTransformSeq I m i).stalkIdeal η' =
    (IdealSheafData.vanishingIdeal (Closeds.closure {η'})).stalkIdeal η'
  avoid : ∀ (l : Fin S.length) (hl : l.val < i.val),
    S.stageMapBetween i l.castSucc (Nat.le_of_lt hl) η' ∉ (S.center l).support
  uniq : ∀ y, S.stageMap i y = η → y = η'

/-- If no centre before stage `i` contains the strict transform of
`c := vanishingIdeal (closure {η})`,
the lift exists (the proof of [Kol07, Corollary 22]: the strict transform of an integral scheme has
a generic point over the original one before its first containing centre). -/
theorem exists_genericLift [IsLocallyNoetherian X] (S : BlowUpSequence X) (I : X.IdealSheafData)
    (E : DivisorFamily X) (m : ℕ) {η : X} (hη : η ∈ I.support.genericPoints)
    (hηE : ∀ j, η ∉ (E.component j).support)
    (hIc : I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (i : Fin (S.length + 1))
    (hi : ∀ l < i.val, ¬ CenterContains S (IdealSheafData.vanishingIdeal (Closeds.closure {η})) l) :
    ∃ η' : S.stage i, GenericLift S I E m η i η' := by
  have hint := isIntegral_subscheme_vanishingIdeal_closure η
  have hgen := isGenericPoint_support_vanishingIdeal_closure η
  have hi' : i.val ≤ firstCenterIndex S (IdealSheafData.vanishingIdeal (Closeds.closure {η})) :=
    le_firstCenterIndex_of_forall_lt_not S _ (Nat.lt_succ_iff.mp i.isLt) hi
  obtain ⟨η', hgen', hmap, huniq, havoid, -⟩ :=
    exists_isGenericPoint_strictTransformSeq_and_isIso_of_le_firstCenterIndex S _ hgen i hi'
  have hred := isReduced_subscheme_vanishingIdeal (X := X) (Closeds.closure {η})
  refine ⟨η', hmap, strictTransformSeq_eq_vanishingIdeal_closure S _ i hgen', ?_, ?_, ?_, havoid,
    huniq⟩
  · exact mem_genericPoints_markedTransformSeq_support_of_forall_notMem S I _ m hgen hη hIc i
      hmap huniq havoid
  · intro j
    refine notMem_component_support_of_notMem_support _ ?_ j
    refine notMem_support_totalTransformSeq_of_forall_notMem S E i η' havoid fun hηs => ?_
    rw [hmap, ← SetLike.mem_coe, DivisorFamily.coe_support_eq_iUnion] at hηs
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hηs
    exact hηE j hj
  · rw [stalkIdeal_markedTransformSeq_eq_maximalIdeal S I m hIc i hmap havoid,
      stalkIdeal_vanishingIdeal_closure_self]

namespace GenericLift

variable {S : BlowUpSequence X} {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ} {η : X}
  {i : Fin (S.length + 1)} {η' : S.stage i}

/-- The lifted point is a generic point of the strict transform's support. -/
theorem isGenericPoint_strictTransformSeq (h : GenericLift S I E m η i η') :
    IsGenericPoint η' ((S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) i).support :
      Set (S.stage i)) := by
  rw [h.strict_eq]
  exact isGenericPoint_support_vanishingIdeal_closure η'

/-- The lifted point lies on the strict transform. -/
theorem mem_support (h : GenericLift S I E m η i η') :
    η' ∈ (S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η})) i).support :=
  h.isGenericPoint_strictTransformSeq.mem

/-- The marked transform's stalk at the lifted point is the maximal ideal. -/
theorem stalkIdeal_eq_maximalIdeal (h : GenericLift S I E m η i η')
    (hIc : I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η) :
    (S.markedTransformSeq I m i).stalkIdeal η' = maximalIdeal ((S.stage i).presheaf.stalk η') :=
  stalkIdeal_markedTransformSeq_eq_maximalIdeal S I m hIc i h.map h.avoid

/-- The marked transform has order `1` at the lifted point when `I` is nonzero at `η`. -/
theorem ord_eq_one [IsLocallyNoetherian (S.stage i)]
    (h : GenericLift S I E m η i η')
    (hIc : I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (hI0 : I.stalkIdeal η ≠ ⊥) : (S.markedTransformSeq I m i).ord η' = 1 :=
  ord_markedTransformSeq_eq_one S I m hIc hI0 i h.map h.avoid

/-- Any ideal sheaf's monomial part with respect to the total transform of `E` is the unit ideal at
the lifted point. -/
theorem stalkIdeal_monomialPart_eq_top [IsLocallyNoetherian X] [NoetherianSpace (S.stage i)]
    (h : GenericLift S I E m η i η') (hηE : ∀ j, η ∉ (E.component j).support)
    (K : (S.stage i).IdealSheafData) :
    (monomialPart K (S.totalTransformSeq E i)).stalkIdeal η' = ⊤ :=
  stalkIdeal_monomialPart_totalTransformSeq_eq_top S E hηE i K h.map h.avoid

end GenericLift

end Hironaka.Resolution
