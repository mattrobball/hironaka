/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainTransport
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimCover
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimCoverTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedComponentTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP1 descends along the local cover of Theorem 105

[Kol07, Theorem 105] evaluates `BO_{n,1}` on a triple `T` through a local cover
`g : T'.X.left → T.X.left` (a coproduct of open immersions, surjective) on whose pieces a smooth
hypersurface of maximal contact exists: `BO(T') = g^* BO(T)`, since the functor commutes with smooth
morphisms ([Kol07, Theorem 103 (2)], `commutesWithSmooth`; [Kol07, 34.1]). The statement CP1 of the
embedded desingularization (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`; the
predicate `CP1For` of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For`) for the run on `T` at a
point `p` of the strict transform `c̃_i` follows from CP1 for the pulled-back run on `T'` at a point
`q` over `p`, for the member `c' := I_{closure η'}` of a suitable point `η'` over `η` (a component
of `g⁻¹(V(c))` through the image of `q`): the first containing stage is the same on both sides (the
stop-rule bookkeeping of `claimFor_of_pullback_cover`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimCover`, repeated here), the three data of the
pulled-back run at that stage are the pull-backs of the data of the run along the stage lift, and
the chain form descends along the stalk isomorphism of the stage lift
(`chainRelativeAt_of_comap_of_isIso_stalkMap`). Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step2` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3EraseEmpty`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] (T T' : Triple k) (g : T'.X.left ⟶ T.X.left)
  (hg : openImmersionCoprods g) (hsurj : Function.Surjective g) (hpb : T'.IsPullbackOf T g)
  (S : BlowUpSequence T.X.left) (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E)

include hg hsurj hpb hS in
/-- **CP1 descends along a coproduct of open immersions** ([Kol07, Theorem 105]; the counterpart
of `claimFor_of_pullback_cover`): if it holds for the pulled-back run on `T'` at every point `η'`
over `η` that is a generic point of `g⁻¹(V(c))` (with the member `I(closure η')`), it holds for
the run on `T` at `η`. The first containing stages agree (the lifted generic points correspond,
`GenericLift.uniq`); the three data of the pulled-back run at that stage are the pull-backs of
the data of the run along the stage lift (`totalTransformSeq_pullback`, [Kol07, Lemma 62]
iterated, the strict transform through `stalkIdeal_comap_vanishingIdeal_closure_eq`); and the
chain form descends along the stalk isomorphism of the stage lift. -/
theorem cp1For_of_pullback_cover {η : T.X.left} (hη : η ∈ T.I.support.genericPoints)
    (hηE : ∀ j, η ∉ (T.E.component j).support)
    (hIc : T.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
    (h : ∀ η' : T'.X.left, g η' = η → η' ∈ T'.I.support.genericPoints →
      (∀ j, η' ∉ (T'.E.component j).support) →
      T'.I.stalkIdeal η' = (IdealSheafData.vanishingIdeal (Closeds.closure {η'})).stalkIdeal η' →
      CP1For (S.pullback g) T'.I T'.E η') :
    CP1For S T.I T.E η := by
  obtain ⟨hover, hI', hE'⟩ := hpb
  have hsm : Smooth g := Hironaka.Sequence.openImmersionCoprods.smooth hg
  have hfl : Flat g := Hironaka.Sequence.openImmersionCoprods.flat hg
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hLN' : IsLocallyNoetherian T'.X.left :=
    (T'.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hNS' : NoetherianSpace T'.X.left := Hironaka.BD.noetherianSpace_triple T'
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  have hpbM : (⟨T', 1⟩ : MarkedTriple k).IsPullbackOf ⟨T, 1⟩ g := ⟨⟨hover, hI', hE'⟩, rfl⟩
  have hS' : (S.pullback g).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I 1 T'.E :=
    MarkedTriple.IsPullbackOf.isOrderGeSeq_pullback hpbM hS
  have hlen := length_pullback S g
  intro i hi hmin p hp
  -- the point over `p` and the component of `g⁻¹(V(c))` through it
  obtain ⟨q, hq⟩ := surjective_pullbackStageHom S g hsurj i.castSucc p
  have hq' : q ∈ ((S.pullback g).strictTransformSeq
      ((IdealSheafData.vanishingIdeal (Closeds.closure {η})).comap g)
      (S.pullbackStageIdx g i.castSucc)).support := by
    rw [strictTransformSeq_pullback, mem_support_comap_iff_apply, hq]
    exact hp
  have hgp := TopologicalSpace.Closeds.genericPoints_finite
    ((IdealSheafData.vanishingIdeal (Closeds.closure {η})).support.preimage g.continuous)
  have hJ := coe_support_comap_eq_iUnion g (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
  rw [← SetLike.mem_coe, coe_support_strictTransformSeq_biUnion (S.pullback g) _ hgp
    (fun η' => IdealSheafData.vanishingIdeal (Closeds.closure {η'})) _ hJ] at hq'
  obtain ⟨η', hη'gp, hqη'⟩ := Set.mem_iUnion₂.mp hq'
  rw [SetLike.mem_coe] at hqη'
  have hgη' : g η' = η := by
    have := apply_eq_of_mem_genericPoints_preimage g (η := η) (η' := η')
    rw [Hironaka.Sequence.support_vanishingIdeal_eq] at hη'gp
    exact this hη'gp
  subst hgη'
  have hgen' : η' ∈ ((IdealSheafData.vanishingIdeal (Closeds.closure
      {g η'})).comap g).support.genericPoints := by
    rw [IdealSheafData.support_comap]
    exact hη'gp
  -- the hypotheses of Włodarczyk's Claim at `η'`
  have hη'I : η' ∈ T'.I.support.genericPoints := by
    rw [hI']
    refine ⟨?_, fun ξ hξ hsp => ?_⟩
    · rw [mem_support_comap_iff_apply]
      exact hη.1
    · rw [mem_support_comap_iff_apply] at hξ
      have hgξ : g ξ = g η' := hη.2 hξ (hsp.map g.continuous)
      refine hgen'.2 ?_ hsp
      rw [mem_support_comap_iff_apply, hgξ, Hironaka.Sequence.support_vanishingIdeal_eq]
      exact subset_closure (Set.mem_singleton _)
  have hη'E : ∀ j, η' ∉ (T'.E.component j).support := by
    intro j hj
    have hsup : η' ∈ T'.E.support := le_iSup (fun i => (T'.E.component i).support) j hj
    rw [hE', ← SetLike.mem_coe, DivisorFamily.coe_support_eq_iUnion] at hsup
    obtain ⟨j', hj'⟩ := Set.mem_iUnion.mp hsup
    exact hηE j' ((mem_support_comap_iff_apply _ g η').mp hj')
  have hI'c : T'.I.stalkIdeal η' = (IdealSheafData.vanishingIdeal (Closeds.closure
      {η'})).stalkIdeal η' := by
    have := openImmersionCoprods.isIso_stalkMap hg η'
    rw [hI', IdealSheafData.stalkIdeal_comap, hIc, ← IdealSheafData.stalkIdeal_comap]
    exact stalkIdeal_comap_vanishingIdeal_closure_eq g le_rfl hgen'
  have hY := h η' rfl hη'I hη'E hI'c
  -- the stop rule agrees on both sides below the first containing stage
  have hmin' : ∀ l ≤ i.val, ∀ l' < l,
      ¬ CenterContains (S.pullback g) (IdealSheafData.vanishingIdeal (Closeds.closure {η'})) l' :=
          by
    intro l
    induction l with
    | zero => intro _ l' hl'; exact absurd hl' (Nat.not_lt_zero _)
    | succ l ih =>
      intro hl l' hl'
      have ihl := ih (Nat.le_of_succ_le hl)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
      · exact ihl l' hlt
      · intro hcl
        have hlS : l' < S.length := (Nat.lt_of_succ_le hl).trans i.isLt
        have hlS' : l' < (S.pullback g).length := by rw [hlen]; exact hlS
        obtain ⟨ζ, hζ⟩ := exists_genericLift (S.pullback g) T'.I T'.E 1 hη'I hη'E hI'c
          (S.pullbackStageIdx g ⟨l', Nat.lt_succ_of_lt hlS⟩) ihl
        obtain ⟨ξ, hξ⟩ := exists_genericLift S T.I T.E 1 hη hηE hIc ⟨l', Nat.lt_succ_of_lt hlS⟩
          fun m hm => hmin m (hm.trans (Nat.lt_of_succ_le hl))
        have hφζ : S.pullbackStageHom g ⟨l', Nat.lt_succ_of_lt hlS⟩ ζ = ξ := by
          refine hξ.uniq _ ?_
          rw [stageMap_pullbackStageHom_apply, hζ.map]
        have hse : (S.pullback g).strictTransformSeq (IdealSheafData.vanishingIdeal
            (Closeds.closure {η'}))
            ⟨l', Nat.lt_succ_of_lt hlS'⟩ = IdealSheafData.vanishingIdeal (Closeds.closure {ζ}) :=
                hζ.strict_eq
        have hζmem := (centerContains_iff_mem_center_support (S.pullback g) _ hlS' hse).mp hcl
        rw [center_pullback_mk' S g hlS hlS', mem_support_comap_iff_apply, hφζ] at hζmem
        exact hmin l' (Nat.lt_of_succ_le hl)
          ((centerContains_iff_mem_center_support S _ hlS hξ.strict_eq).mpr hζmem)
  have hmin'' := hmin' i.val le_rfl
  -- the lifts at the first containing stage
  have hiS' : i.val < (S.pullback g).length := by rw [hlen]; exact i.isLt
  obtain ⟨ζ, hζ⟩ := exists_genericLift (S.pullback g) T'.I T'.E 1 hη'I hη'E hI'c
    (S.pullbackStageIdx g i.castSucc) hmin''
  obtain ⟨ξ, hξ⟩ := exists_genericLift S T.I T.E 1 hη hηE hIc i.castSucc hmin
  have hφζ : S.pullbackStageHom g i.castSucc ζ = ξ := by
    refine hξ.uniq _ ?_
    rw [stageMap_pullbackStageHom_apply, hζ.map]
  have hse' : (S.pullback g).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
      {η'}))
      ⟨i.val, Nat.lt_succ_of_lt hiS'⟩ = IdealSheafData.vanishingIdeal (Closeds.closure {ζ}) :=
          hζ.strict_eq
  have hseX : S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {g η'}))
      ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = IdealSheafData.vanishingIdeal (Closeds.closure {ξ}) :=
          hξ.strict_eq
  -- the first containing stage on `T'`
  have hcont' : CenterContains (S.pullback g) (IdealSheafData.vanishingIdeal (Closeds.closure
      {η'})) i.val := by
    rw [centerContains_iff_mem_center_support (S.pullback g) _ hiS' hse',
      center_pullback_mk' S g i.isLt hiS', mem_support_comap_iff_apply]
    have hφζ' : S.pullbackStageHom g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ζ = ξ := hφζ
    rw [hφζ']
    exact (centerContains_iff_mem_center_support S _ i.isLt hseX).mp hi
  have hY' := hY ⟨i.val, hiS'⟩ hcont' hmin'' q hqη'
  -- descend the stalk identity along the stage lift
  have hcop := openImmersionCoprods_pullbackStageHom S hg i.castSucc
  have hiso := openImmersionCoprods.isIso_stalkMap hcop q
  have hζq : ζ ⤳ q := by
    rw [specializes_iff_mem_closure]
    have hq2 := hqη'
    rw [hζ.strict_eq, ← SetLike.mem_coe, IdealSheafData.coe_support_vanishingIdeal,
        Closeds.coe_closure] at hq2
    exact hq2
  have hζgen : ζ ∈ ((IdealSheafData.vanishingIdeal (Closeds.closure
      {S.pullbackStageHom g i.castSucc ζ})).comap
      (S.pullbackStageHom g i.castSucc)).support.genericPoints := by
    rw [hφζ]
    refine ⟨?_, fun ξ' hξ' hsp => ?_⟩
    · rw [mem_support_comap_iff_apply, hφζ, Hironaka.Sequence.support_vanishingIdeal_eq]
      exact subset_closure (Set.mem_singleton ξ)
    · rw [mem_support_comap_iff_apply, Hironaka.Sequence.support_vanishingIdeal_eq] at hξ'
      have h3 : S.pullbackStageHom g i.castSucc ξ' ⤳ ξ := by
        rw [← hφζ]
        exact hsp.map (S.pullbackStageHom g i.castSucc).continuous
      have hξ'ξ : S.pullbackStageHom g i.castSucc ξ' = ξ :=
        ((specializes_iff_mem_closure.mpr hξ').antisymm h3).eq.symm
      refine hζ.uniq ξ' ?_
      refine hη'I.2 ?_ ?_
      · rw [hI', mem_support_comap_iff_apply, ← stageMap_pullbackStageHom_apply, hξ'ξ, hξ.map]
        exact hη.1
      · rw [← hζ.map]
        exact hsp.map ((S.pullback g).stageMap _).continuous
  have hst := stalkIdeal_comap_vanishingIdeal_closure_eq (S.pullbackStageHom g i.castSucc) hζq hζgen
  rw [hφζ] at hst
  -- the three data of the pulled-back run are the pull-backs of the run's data
  have hE'' : (S.pullback g).totalTransformSeq T'.E (S.pullbackStageIdx g i.castSucc) =
      (S.totalTransformSeq T.E i.castSucc).comap (S.pullbackStageHom g i.castSucc) := by
    rw [hE']
    exact totalTransformSeq_pullback S g T.E i.castSucc
  have hI'' : (S.pullback g).markedTransformSeq T'.I 1 (S.pullbackStageIdx g i.castSucc) =
      (S.markedTransformSeq T.I 1 i.castSucc).comap (S.pullbackStageHom g i.castSucc) := by
    rw [hI']
    exact IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom (T.X.left ↘ Spec (.of k)) n' g hS
      i.castSucc
  have hY'' : ChainRelativeAt
      ((S.totalTransformSeq T.E i.castSucc).comap (S.pullbackStageHom g i.castSucc))
      ((S.markedTransformSeq T.I 1 i.castSucc).comap (S.pullbackStageHom g i.castSucc))
      ((S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
          {g η'})) i.castSucc).comap
        (S.pullbackStageHom g i.castSucc)) q := by
    rw [← hE'', ← hI'']
    refine (chainRelativeAt_congr_stalkIdeal ?_).mpr hY'
    rw [hξ.strict_eq, hst, ← hζ.strict_eq]
    rfl
  -- descend along the stalk isomorphism of the stage lift
  have hres := chainRelativeAt_of_comap_of_isIso_stalkMap (S.pullbackStageHom g i.castSucc) hY''
  rw [hq] at hres
  exact hres

end Hironaka.Resolution
