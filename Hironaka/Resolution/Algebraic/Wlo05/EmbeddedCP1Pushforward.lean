/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainDescentTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainPushforward
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.Snc.LiftHypersurface
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP1 descends along a pushed-forward run on a hypersurface of maximal contact

Step 2.2 of the proof of [Kol07, Theorem 103] runs the inductive order reduction on a smooth
hypersurface of maximal contact `H` and pushes the run forward to `X` ([Kol07, Definition 30,
30.3]; the proof of [Kol07, Lemma 102]). This module proves the corresponding step of the
statement CP1 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`; the predicate `CP1For` of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For`): CP1 for a run `L` on `H`, for the restricted
data `(J|_H, E|_H)` at a point `η'` over `η`, gives CP1 for the push-forward of `L`, for `(J, E)` at
`η`. Three facts combine. The first stage whose centre contains the strict transform of the
component `c̄ = V(closure {η}) ⊆ H` is the same on both sides, because the member restricts to
`c̄|_H = I(closure {η'})` and the stop rule is preserved by the push-forward
(`centerContains_pushforward_iff_of_ker_le`). Every point of the strict transform at that stage is
the image of a point of the level's strict transform, since the stage embedding is a closed
immersion with kernel the strict transform of `H ⊇ c̄`. The chain form of the level data at that
point gives the chain form of the data on `X` at its image (`chainRelativeAt_pushforward` of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainPushforward`). The hypersurfaces of maximal
contact are those of [Kol07, Theorem 80]. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22Core`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

/-- **CP1 descends along a push-forward.** For a smooth hypersurface `H ⊆ X` with `H ⊆ V(J)`,
`H ∪ E` snc, `η ∈ H`, and a run `L` on `H` whose push-forward is a smooth run of order `≥ 1` for
`(J, 1, E)`: CP1 for `L` with the restricted data `(J|_H, E|_H)` at the point `η'` over `η` gives
CP1 for the push-forward with `(J, E)` at `η`. The first containing stages correspond, the points
of the strict transform at that stage are images of points of the level's strict transform, and
the chain form is transported pointwise. -/
theorem cp1For_pushforward (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {H : X.IdealSheafData} (hH : IsSmoothDivisor H)
    {E : DivisorFamily X} (hE : E.IsSnc) (hEH : (E.append H).IsSnc) {J : X.IdealSheafData}
    (hHJ : H ≤ J) {η : X} (hηH : η ∈ H.support) (L : BlowUpSequence H.subscheme)
    (hS : (L.pushforward H.subschemeι).IsOrderGeSeq f J 1 E) {η' : H.subscheme}
    (hη' : H.subschemeι η' = η)
    (h : CP1For L (J.comap H.subschemeι) (E.comap H.subschemeι) η') :
    CP1For (L.pushforward H.subschemeι) J E η := by
  have hker : H.subschemeι.ker = H := IdealSheafData.ker_subschemeι H
  -- `c̄ ⊆ H`
  have hZ : Closeds.closure {η} ≤ H.support := by
    rw [← SetLike.coe_subset_coe, Closeds.coe_closure]
    exact H.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηH)
  have hHc : H ≤ IdealSheafData.vanishingIdeal (Closeds.closure {η}) :=
      IdealSheafData.le_support_iff_le_vanishingIdeal.mp hZ
  have hkerc : H.subschemeι.ker ≤ IdealSheafData.vanishingIdeal (Closeds.closure {η}) := by
    rw [hker]
    exact hHc
  -- the member restricts to the reduced closure of `η'`
  have hcomap : (IdealSheafData.vanishingIdeal (Closeds.closure {η})).comap H.subschemeι =
      IdealSheafData.vanishingIdeal (Closeds.closure {η'}) := by
    rw [← hη']
    exact comap_vanishingIdeal_closure_of_isClosedImmersion H.subschemeι η'
  intro i hi hmin p hp
  have hlen := length_pushforward L H.subschemeι
  have hiL : i.val < L.length := by
    rw [← hlen]
    exact i.isLt
  set i₀ : Fin (L.length + 1) := ⟨i.val, Nat.lt_succ_of_lt hiL⟩ with hi₀
  -- the stop rule corresponds
  have hi' : CenterContains L (IdealSheafData.vanishingIdeal (Closeds.closure {η'})) i.val := by
    rw [← hcomap]
    exact (centerContains_pushforward_iff_of_ker_le L H.subschemeι hkerc i.val).mp hi
  have hmin' : ∀ l < i.val, ¬ CenterContains L (IdealSheafData.vanishingIdeal (Closeds.closure
      {η'})) l := by
    intro l hl hc
    rw [← hcomap] at hc
    exact hmin l hl ((centerContains_pushforward_iff_of_ker_le L H.subschemeι hkerc l).mpr hc)
  -- the point lies on `H`'s strict transform, the image of the stage embedding
  have hpH : p ∈ ((L.pushforward H.subschemeι).strictTransformSeq H i.castSucc).support :=
    IdealSheafData.support_antitone (strictTransformSeq_mono _ hHc i.castSucc) hp
  have hcl := isClosedImmersion_pushforwardStageHom L H.subschemeι i₀
  have hkerφ := ker_pushforwardStageHom L H.subschemeι i₀
  rw [hker] at hkerφ
  obtain ⟨q, hq⟩ := exists_eq_of_mem_support_ker (L.pushforwardStageHom H.subschemeι i₀)
    (by rw [hkerφ]; exact hpH)
  have hq' : q ∈ (L.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
      {η'})) i₀).support := by
    rw [← hcomap, ← strictTransformSeq_pushforward_comap L H.subschemeι hkerc i₀,
      mem_support_comap_iff_apply, hq]
    exact hp
  -- CP1 for the level run at the corresponding stage, transported along the stage embedding
  have hY := h ⟨i.val, hiL⟩ hi' hmin' q hq'
  rw [← hcomap] at hY
  have hres := chainRelativeAt_pushforward f n hH hE hEH hHJ hHc L hS i₀ hY
  rw [hq] at hres
  exact hres

end Hironaka.Resolution
