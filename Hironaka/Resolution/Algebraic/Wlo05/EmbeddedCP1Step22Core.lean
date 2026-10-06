/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.BoundaryClearing.Composite
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Cons
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Pushforward
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22Tools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainCaseA
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainDescentTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedComponentTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNotContained
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.LiftHypersurface
import Hironaka.Scheme.Snc.RelativeDimension
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The core of Step 2.2: CP1 along the raw output of Lemma 102

[Kol07, Lemma 102] on a triple `(X, I, E)` with a member `H = E^j` of maximal contact for `(I, 1)`
blows up `Z_{-1}`, the components of `H` along which `I` has order `≥ 1`, and pushes forward the
inductive run on the strict transform of `H`. For the reduced component `c̄ ⊆ V(I) ⊆ H` of a
generic point `η` of `V(I)` off the other members, the statement CP1 of the embedded
desingularization (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) along this raw
output for `(I, E − E^j)` follows from CP1 for the inductive run (the hypothesis `hcp1`, the stage
below):

* **Case A**: `Z_{-1}` contains `c̃`. Then `c̄` is a component of `H`
  (`mem_genericPoints_of_Zminus1_le`), a smooth divisor with the stalks of `H`
  (`isSmoothDivisor_vanishingIdeal_closure_of_mem_genericPoints`,
  `stalkIdeal_vanishingIdeal_closure_eq_of_isSmoothDivisor`), and
  `chainRelativeAt_of_le_isSmoothDivisor` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainCaseA`)
  gives the chain form at the first stage; later stages are excluded by the stop rule.
* **Case B**: the first blow-up does not contain `c̃`. On `H` the run is `cons (Z_{-1}|_H) (B …)`,
  its first blow-up does not contain the level component (`cp1For_cons_of_not_centerContains`),
  and `hcp1` on the restricted triple, whose ideal and boundary are exactly the level data after
  the first blow-up, gives CP1 for the tail; `cp1For_pushforward`
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Pushforward`) carries it to `X`.

This is Step 2.2 of the proof of [Kol07, Theorem 103] read for CP1; the argument is not in the
literature. Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BD Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} {Dom : MarkedTriple k → Prop}
  (B : OrderGeSeqAssignment k Dom)

/-- **The core of Step 2.2** (the proof of [Kol07, Lemma 102] read for CP1): for a triple
`(X, I, E)` with `max-ord I = m = 1`, a member `H = E^j` that is a smooth hypersurface with
`H ⊆ V(I)`, and a generic point `η` of `V(I)` off the other members with `I_η` its reduced ideal,
the raw output of Lemma 102 satisfies CP1 for `(I, E − E^j)` at `η`, given CP1 for the inductive
run `B` at the mark `1`. -/
theorem cp1For_rawSeq_of_cp1 (T : Triple k) (m : ℕ) (hm1 : m = 1) (j : T.E.ι)
    (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m) (hn : T.HasDimLE n)
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T')
    (hcp1 : ∀ (T' : MarkedTriple k) (hT' : Dom T'), T'.m = 1 → ∀ η' : T'.X.left,
      η' ∈ T'.I.support.genericPoints → (∀ i, η' ∉ (T'.E.component i).support) →
      T'.I.stalkIdeal η' = (IdealSheafData.vanishingIdeal (Closeds.closure {η'})).stalkIdeal η' →
      CP1For (B.seq T' hT') T'.I T'.E η')
    (hH : IsSmoothDivisor (T.E.component j)) (hHJ : T.E.component j ≤ T.I) {η : T.X.left}
    (hη : η ∈ T.I.support.genericPoints)
    (hηE : ∀ i, η ∉ ((T.E.erase j).component i).support)
    (hIc : T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η) :
    CP1For (rawSeq T m j hI hmax hn B hDom) T.I (T.E.erase j) η := by
  subst hm1
  -- standing facts on `X` and on `H`
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  have hsm : Smooth (T.X.left ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n' _
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hNS : NoetherianSpace T.X.left := Hironaka.BD.noetherianSpace_triple T
  have hN : IsNoetherian T.X.left :=
    { toIsLocallyNoetherian := hLN, toCompactSpace := inferInstance }
  have hker : (T.E.component j).subschemeι.ker = T.E.component j := IdealSheafData.ker_subschemeι _
  have hηH : η ∈ (T.E.component j).support := IdealSheafData.support_antitone hHJ hη.1
  -- `c̄ ⊆ H` and `I ⊆ I(c̄)`
  have hZ : Closeds.closure {η} ≤ (T.E.component j).support := by
    rw [← SetLike.coe_subset_coe, Closeds.coe_closure]
    exact (T.E.component j).support.isClosed.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hηH)
  have hHc : T.E.component j ≤ IdealSheafData.vanishingIdeal (Closeds.closure {η}) :=
    IdealSheafData.le_support_iff_le_vanishingIdeal.mp hZ
  have hZI : Closeds.closure {η} ≤ T.I.support := by
    rw [← SetLike.coe_subset_coe, Closeds.coe_closure]
    exact T.I.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη.1)
  have hIc' : T.I ≤ IdealSheafData.vanishingIdeal (Closeds.closure {η}) :=
    IdealSheafData.le_support_iff_le_vanishingIdeal.mp hZI
  -- the raw output is the push-forward of the run `L` on `H`
  set L : BlowUpSequence (T.E.component j).subscheme :=
    BlowUpSequence.cons (T.E.component j).subscheme (centerS T 1 j)
      (B.seq (restrictedTriple T 1 j hI hmax)
        (hDom _ (hasDimLE_restrictedTriple T 1 j hI hmax hn) rfl)) with hL
  have hraw : rawSeq T 1 j hI hmax hn B hDom = L.pushforward (T.E.component j).subschemeι := rfl
  have hord := isOrderSeq_rawSeq_erase T 1 j hI hmax hn B hDom
  have hS : (L.pushforward (T.E.component j).subschemeι).IsOrderGeSeq
      (T.X.left ↘ Spec (.of k)) T.I 1 (T.E.erase j) :=
    IsOrderSeq.isOrderGeSeq (T.X.left ↘ Spec (.of k)) n' hord
  have hEerase : (T.E.erase j).IsSnc := isSnc_erase T.E j T.isSnc
  have hEH : ((T.E.erase j).append (T.E.component j)).IsSnc :=
    DivisorFamily.isSnc_erase_append T.E j T.isSnc
  rw [hraw]
  by_cases hA : Zminus1 T.I 1 (T.E.component j) ≤ IdealSheafData.vanishingIdeal (Closeds.closure
      {η})
  · -- Case A: `Z_{-1}` contains `c̃`: `c̄` is a component of `H`, the smooth-divisor case applies
    have hηgen : η ∈ (T.E.component j).support.genericPoints :=
      mem_genericPoints_of_Zminus1_le T.I (T.E.component j) hη hA
    have hst : ∀ x ∈ (IdealSheafData.vanishingIdeal (Closeds.closure {η})).support,
        (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x =
            (T.E.component j).stalkIdeal x := by
      intro x hx
      rw [support_vanishingIdeal_eq] at hx
      exact stalkIdeal_vanishingIdeal_closure_eq_of_isSmoothDivisor hH hηgen
        (specializes_iff_mem_closure.mpr hx)
    have hcsm : IsSmoothDivisor (IdealSheafData.vanishingIdeal (Closeds.closure {η})) :=
      isSmoothDivisor_vanishingIdeal_closure_of_mem_genericPoints hH hηgen
    have hsupp : (IdealSheafData.vanishingIdeal (Closeds.closure {η})).support ≤
        (T.E.component j).support := by
      rw [support_vanishingIdeal_eq]
      exact hZ
    have hsnc : (T.E.erase j).HasSncWith (IdealSheafData.vanishingIdeal (Closeds.closure {η})) :=
      HasSncWith.of_embeds (fun i : (T.E.erase j).ι => i.1) Subtype.val_injective (fun _ => rfl)
        (HasSncWith.of_stalkIdeal_eq (hasSncWith_component_of_isSnc T.isSnc j) hsupp hst)
    have hord1 : ∀ p ∈ (IdealSheafData.vanishingIdeal (Closeds.closure {η})).support,
        (nonmonomialPart T.I (T.E.erase j)).ord p ≤ 1 := by
      intro p _
      have h1 : T.I.ord p ≤ 1 := by
        have := IdealSheafData.le_maxOrd T.I p
        rwa [hmax, Nat.cast_one] at this
      exact (IdealSheafData.ord_anti (IdealSheafData.le_colon_self _ _) p).trans h1
    have hnc : NotContainedInMembers (T.E.erase j) (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) :=
      notContainedInMembers_vanishingIdeal_closure _ hηE
    have hS3 := chainRelativeAt_of_le_isSmoothDivisor (T.X.left ↘ Spec (.of k)) hEerase
      hcsm hsnc hIc' hord1 hnc
    -- the first stage contains `c̃`
    have h0 : CenterContains (L.pushforward (T.E.component j).subschemeι)
        (IdealSheafData.vanishingIdeal (Closeds.closure {η})) 0 := by
      refine ⟨Nat.succ_pos _, ?_⟩
      change (centerS T 1 j).map (T.E.component j).subschemeι ≤ _
      exact (map_centerS T 1 j).le.trans hA
    rintro ⟨i, hi'⟩ _ hmin p hp
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact hS3 p hp
    · exact absurd h0 (hmin 0 hpos)
  · -- Case B: the first blow-up does not contain `c̃`; descend to `H` and use the level run
    obtain ⟨η', hη'⟩ := exists_eq_of_mem_support_ker (T.E.component j).subschemeι
      (by rw [hker]; exact hηH)
    have hHdim := smoothOfRelativeDimension_of_isSmoothDivisor (T.X.left ↘ Spec (.of k)) n'
      (T.E.component j) hH
    have hLN' : IsLocallyNoetherian (T.E.component j).subscheme :=
      ((T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (.of k))).isLocallyNoetherian_of_field
    -- the level hypotheses at `η'`
    have hη'gen : η' ∈ (T.I.comap (T.E.component j).subschemeι).support.genericPoints :=
      mem_genericPoints_comap_of_isClosedImmersion _ T.I (hη' ▸ hη)
    have hη'E : ∀ i,
        η' ∉ (((T.E.erase j).comap (T.E.component j).subschemeι).component i).support :=
      fun i hi => hηE i (by rw [← hη']; exact (mem_support_comap_iff_apply _ _ _).mp hi)
    have hIc'' : (T.I.comap (T.E.component j).subschemeι).stalkIdeal η' =
        (IdealSheafData.vanishingIdeal (Closeds.closure {η'})).stalkIdeal η' :=
      stalkIdeal_comap_eq_vanishingIdeal_closure_of_eq _ T.I η' (hη' ▸ hIc)
    have hcomap : (IdealSheafData.vanishingIdeal (Closeds.closure {η})).comap
        (T.E.component j).subschemeι =
        IdealSheafData.vanishingIdeal (Closeds.closure {η'}) := by
      rw [← hη']
      exact comap_vanishingIdeal_closure_of_isClosedImmersion _ η'
    have hkerc : (T.E.component j).subschemeι.ker ≤ IdealSheafData.vanishingIdeal (Closeds.closure
        {η}) := by
      rw [hker]
      exact hHc
    -- the first blow-up on `H` does not contain the level component
    have hD : ¬ CenterContains L (IdealSheafData.vanishingIdeal (Closeds.closure {η'})) 0 := by
      intro hc
      apply hA
      rw [← hcomap] at hc
      obtain ⟨h0', hle⟩ := id ((centerContains_pushforward_iff_of_ker_le L _ hkerc 0).mpr hc)
      change (centerS T 1 j).map (T.E.component j).subschemeι ≤ _ at hle
      exact (map_centerS T 1 j).symm.le.trans hle
    -- CP1 along `L` from the inductive hypothesis on the restricted triple
    have hCP : CP1For L (T.I.comap (T.E.component j).subschemeι)
        ((T.E.erase j).comap (T.E.component j).subschemeι) η' := by
      refine cp1For_cons_of_not_centerContains (centerS T 1 j) _ _ _ hη'gen hη'E hIc'' hD ?_
      intro η₁ hlift
      exact hcp1 (restrictedTriple T 1 j hI hmax)
        (hDom _ (hasDimLE_restrictedTriple T 1 j hI hmax hn) rfl) rfl η₁
        hlift.mem_genericPoints hlift.notMem hlift.stalk_eq
    exact cp1For_pushforward (T.X.left ↘ Spec (.of k)) n' hH hEerase hEH hHJ hηH L hS hη' hCP

end Hironaka.Resolution
