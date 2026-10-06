/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Algebra.Local.ChartCompletion
import Hironaka.Algebra.Local.ChartOrderFaithful
import Hironaka.Algebra.Local.ChartShift
import Hironaka.Manifold.BlowUp.Transform.Bundled
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.KollarChart
import Hironaka.Manifold.BlowUp.Transform.KollarPerm
import Hironaka.Manifold.BlowUp.Transform.MarkedWeak
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceCompletion
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# Going up: Lemma 61 along a sequence, and Remark 67

Kollár's Lemma 61 [Kol07, Lemma 61] iterated along a sequence, and his Remark 67
[Kol07, Remark 67]: along a sequence of order `≥ m` for `(I, m)` with `ord I ≤ m` everywhere,
every marked transform has order `≤ m` everywhere, and the sequence is then of order exactly `m`
("the converse also holds").

* `ord_birationalTransform_le_of_mem`, `ord_birationalTransform_le`: **Lemma 61 on a manifold**
  for one blowing-up, `ord_{a'} π_*^{-1}(J, m) ≤ m` when `m ≤ ord_Y J` along the centre and
  `ord J ≤ m` everywhere. Over the centre: an adapted chart and a blow-up chart at `a'`, Kollár's
  coordinates at `a'` (`kollarCoords`, the centred coordinates shifted so that `a'` is the origin
  of the chart ring) and the chart-ring map `χ` (`exists_isChartRingHom`); the stalk of the marked
  transform is `χ(π_*^{-1}(J_a, m))` (the stalk formula for the centred coordinates, carried
  across the shift by `chartRingEquivShift`); the chart-level Lemma 61
  (`ord_map_transformIdeal_le_of_hasCohenChart`, with a Cohen chart on the regular local
  `ℚ`-algebra `𝒪_{π a'}`) bounds the order in the localisation `R'_{𝔪'}`; the induced local
  homomorphism `R'_{𝔪'} → 𝒪_{a'}` reflects the powers of the maximal ideal
  (`ordFaithful_chartLocalHom`, through the identification of completions), so the bound descends
  to the stalk. Off the centre the marked transform is the total transform and `π` is a local
  analytic isomorphism (`ord_pullback_of_isLocalDiffeomorphAt`).
* `ord_markedTransformSeq_le`: Lemma 61 iterated along the sequence.
* `isOfOrder_of_isOfOrderGe_of_ord_le`: Remark 67. The marked transforms are the birational
  transforms (the colon characterization with the exponent `m` on the exceptional divisor, the
  order along the centre being exactly `m`), and the order clause of [Kol07, Definition 66] holds
  with equality.

The algebraic counterparts are `maxOrd_markedTransformSeq_le` and `isOrderGeSeq_iff_isOrderSeq`.
Remark 67 is what lets the going-up theorem conclude with a sequence of order exactly `m`.
-/

public section

noncomputable section

open TopologicalSpace IsLocalRing
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} [FiniteDimensional 𝕜 E] {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M} {c : ℕ} {M' : Type u}
  [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M}

omit [FiniteDimensional 𝕜 E] [IsManifold 𝓘(𝕜, E) ω M] in
/-- [Kol07, Lemma 61] on a manifold, at a point over the centre: for `m ≤ ord_Y J` along the centre
and `ord J ≤ m` everywhere, the marked transform `π_*^{-1}(J, m)` has order `≤ m` at every point
`a'` over `Y`. Kollár's coordinates at `a'`, the stalk formula for the marked transform, the
chart-level Lemma 61 in the localisation of the chart ring at the origin, and the
order-faithfulness of the chart-ring local homomorphism. -/
theorem ord_birationalTransform_le_of_mem (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (J : IdealSheaf (structureSheaf 𝕜 E M)) {m : ℕ}
    (hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a)
    (hJ : ∀ y, J.ord y ≤ m) {a' : M'} (haY : π a' ∈ Y) :
    (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.ord a' ≤ m := by
  obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart (π a') haY
  obtain ⟨i, Φ, hΦ, haΦ⟩ := h.cover φ σ hφ a' haφ
  obtain ⟨r, τ, hτr, hlt⟩ := exists_kollarPerm σ i
  obtain ⟨χ, hχ⟩ := exists_isChartRingHom hφ hΦ haΦ r τ haY hτr hlt h
  -- the regular local `ℚ`-algebra `𝒪_{π a'}` and Kollár's coordinates at `a'`
  have haφ' : π a' ∈ φ.source := hΦ.source_subset haΦ
  have hRreg : IsRegularLocalRing ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) :=
    isRegularLocalRing_stalk_of_chart E ψ φ haφ' hφ.1
  have hSnoeth : IsNoetherianRing ((structureSheaf 𝕜 E M').presheaf.stalk a') :=
    isNoetherianRing_stalk_of_chart E ψ Φ haΦ hΦ.mem_maximalAtlas
  have hn : (n : WithBot ℕ∞) = ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) :=
    (ringKrullDim_stalk_of_chart E ψ φ haφ' hφ.1).symm
  have hx : maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) =
      Ideal.span (Set.range (kollarCoords hφ hΦ haΦ r τ)) :=
    maximalIdeal_eq_span_kollarCoords hφ hΦ haΦ r τ
  have hprime : (chartOrigin (kollarCoords hφ hΦ haΦ r τ) r).IsPrime :=
    (chartOrigin_isMaximal _ r hx hn).isPrime
  have hcomap := hχ.comap_maximalIdeal_eq_chartOrigin h hφ hΦ haΦ hx
  -- the centred coordinates `z := centredCoords …`, with `kollarCoords = shiftCoords z r a`
  have hτz : ∀ j, centredCoords hφ hΦ haΦ τ j = coord E ψ φ hφ.1 haφ' (τ j) -
      const 𝕜 E M (π a') (eval 𝕜 E M (π a') (coord E ψ φ hφ.1 haφ' (τ j))) := fun _ => rfl
  -- the shift of the chart rings and the stalk formula through `χ ∘ e⁻¹`
  set e := chartRingEquivShift (centredCoords hφ hΦ haΦ τ) r
    (fun j => const 𝕜 E M (π a') (eval 𝕜 E M' a' (coord E ψ Φ hΦ.mem_maximalAtlas haΦ (τ j))))
    with hedef
  set χ' : chartRing (centredCoords hφ hΦ haΦ τ) r →+*
      (structureSheaf 𝕜 E M').presheaf.stalk a' :=
    χ.comp (e.symm : chartRing (centredCoords hφ hΦ haΦ τ) r →+*
      chartRing (shiftCoords (centredCoords hφ hΦ haΦ τ) r
        (fun j => const 𝕜 E M (π a')
            (eval 𝕜 E M' a' (coord E ψ Φ hΦ.mem_maximalAtlas haΦ (τ j))))) r) with hχ'def
  have hχ'a : ∀ s, χ' (algebraMap _ _ s) = germMap π h.contMDiff a' s := fun s => by
    rw [hχ'def]
    exact (congrArg χ (e.symm.commutes s)).trans (hχ.algebraMap_eq s)
  have hstalk := birationalTransform_stalkIdeal_eq_map_transformIdeal hY h hφ hΦ haΦ haY
    (centredCoords hφ hΦ haΦ τ) r τ hτr hτz hlt χ' hχ'a J hm
  -- the hypotheses of Lemma 61: `J_a ⊆ 𝔪_Y^m` and `ord J_a = m`
  have hI : J.stalkIdeal (π a') ≤ chartCenter (centredCoords hφ hΦ haΦ τ) r ^ m := by
    rw [chartCenter_eq_stalkIdeal_idealSheaf hY hφ haY haφ' (centredCoords hφ hΦ haΦ τ) r τ hτr hτz
      hlt]
    exact (IdealSheaf.le_ordAlongIdeal_iff _ _ _ _).mp (hm _ haY)
  have hI' : J.stalkIdeal (π a') ≤
      chartCenter (kollarCoords hφ hΦ haΦ r τ) r ^ m := by
    rwa [show chartCenter (kollarCoords hφ hΦ haΦ r τ) r =
      chartCenter (centredCoords hφ hΦ haΦ τ) r from
        chartCenter_shiftCoords _ r _]
  have hord : ord (J.stalkIdeal (π a')) = m :=
    le_antisymm (hJ (π a')) ((hm _ haY).trans (ordAlong_le_ord hY J haY))
  -- carry the transform across the shift and factor `χ` through the localisation
  have hcomp : χ'.comp (e : chartRing (shiftCoords
      (centredCoords hφ hΦ haΦ τ) r (fun j => const 𝕜 E M (π a')
            (eval 𝕜 E M' a' (coord E ψ Φ hΦ.mem_maximalAtlas haΦ (τ j))))) r →+*
      chartRing (centredCoords hφ hΦ haΦ τ) r) = χ := by
    ext y
    rw [hχ'def]
    exact congrArg χ (e.symm_apply_apply y)
  have hshift : Ideal.map χ' (transformIdeal (centredCoords hφ hΦ haΦ τ) r
        (J.stalkIdeal (π a')) m) =
      Ideal.map χ (transformIdeal (kollarCoords hφ hΦ haΦ r τ) r
        (J.stalkIdeal (π a')) m) := by
    rw [← map_transformIdeal_chartRingEquivShift (centredCoords hφ hΦ haΦ τ) r
      (fun j => const 𝕜 E M (π a') (eval 𝕜 E M' a' (coord E ψ Φ hΦ.mem_maximalAtlas haΦ (τ j))))
      hI, Ideal.map_map, hcomp]
    rfl
  have hfac : Ideal.map χ (transformIdeal (kollarCoords hφ hΦ haΦ r τ) r
        (J.stalkIdeal (π a')) m) =
      Ideal.map (chartLocalHom _ r χ hcomap)
        ((transformIdeal (kollarCoords hφ hΦ haΦ r τ) r (J.stalkIdeal (π a')) m).map
          (algebraMap _ (Localization.AtPrime
            (chartOrigin (kollarCoords hφ hΦ haΦ r τ) r)))) := by
    rw [Ideal.map_map]
    congr 1
    ext y
    exact (chartLocalHom_algebraMap _ r χ hcomap y).symm
  -- Lemma 61 in the localisation, and the descent along the local homomorphism
  have h61 := ord_map_transformIdeal_le_of_hasCohenChart _ r hx hn
    (hasCohenChart _ r hx hn) hI' hord
  have hof := ordFaithful_chartLocalHom _ r χ hcomap
    (hχ.completionMap_bijective h hφ hΦ haΦ hx
      fun j hj => germMap_kollarCoords_of_gt hφ hΦ haΦ r τ hτr hlt h hj)
  calc (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.ord a'
      = ord ((MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.stalkIdeal a') :=
        rfl
    _ = ord (Ideal.map (chartLocalHom _ r χ hcomap)
        ((transformIdeal (kollarCoords hφ hΦ haΦ r τ) r (J.stalkIdeal (π a')) m).map
          (algebraMap _ (Localization.AtPrime
            (chartOrigin (kollarCoords hφ hΦ haΦ r τ) r))))) := by
        rw [hstalk, hshift, hfac]
    _ ≤ ord ((transformIdeal (kollarCoords hφ hΦ haΦ r τ) r
        (J.stalkIdeal (π a')) m).map (algebraMap _ (Localization.AtPrime
          (chartOrigin (kollarCoords hφ hΦ haΦ r τ) r)))) :=
        ord_map_le_of_ordFaithful hof _
    _ ≤ m := h61

omit [FiniteDimensional 𝕜 E] [IsManifold 𝓘(𝕜, E) ω M] in
/-- [Kol07, Lemma 61] on a manifold: for `m ≤ ord_Y J` along the centre and `ord J ≤ m` everywhere,
the marked transform `π_*^{-1}(J, m)` has order `≤ m` everywhere. Over the centre this is
`ord_birationalTransform_le_of_mem`; off the centre the marked transform is the total transform
(`birationalTransform_stalkIdeal_of_notMem`) and `π` is a local analytic isomorphism there. -/
theorem ord_birationalTransform_le (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (J : IdealSheaf (structureSheaf 𝕜 E M)) {m : ℕ}
    (hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a)
    (hJ : ∀ y, J.ord y ≤ m) (a' : M') :
    (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.ord a' ≤ m := by
  by_cases haY : π a' ∈ Y
  · exact ord_birationalTransform_le_of_mem hY h J hm hJ haY
  · change ord _ ≤ _
    rw [birationalTransform_stalkIdeal_of_notMem hY h hm haY]
    change (J.pullback π h.contMDiff).ord a' ≤ m
    rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt (φ := π) (hφ := h.contMDiff) J
      (h.isLocalDiffeomorphOn_compl ⟨a', haY⟩)]
    exact hJ _

end Hironaka.Manifold

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} (B : FiniteSuccession M)
  {I E₀ : IdealSheaf M} {m : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- [Kol07, Lemma 61] iterated (Kollár's "`max-ord I_i ≤ m` by (61)" in [Kol07, Remark 67]): along
a sequence of order `≥ m` for `(I, m)` with `ord I ≤ m` everywhere, every marked transform has
order `≤ m` everywhere. Over the centre by the chart-level Lemma 61 transported to the analytic
stalk, off the centre by `ord_pullback_of_isLocalDiffeomorphAt`. The algebraic counterpart is
`maxOrd_markedTransformSeq_le`. -/
theorem ord_markedTransformSeq_le (hge : B.IsOfOrderGe I m E₀) (hI : ∀ y, I.ord y ≤ m)
    (i : Fin (B.length + 1)) (x : B.stage i) : (B.markedTransformSeq I m i).ord x ≤ m := by
  induction i using Fin.induction with
  | zero => exact hI x
  | succ i ih =>
    rw [markedTransformSeq_succ]
    exact Hironaka.Manifold.ord_birationalTransform_le (B.isClosedSubmanifold_center i)
        (B.isBlowUp_map i) _
      (fun a ha => by rw [B.idealSheaf_center i]; exact hge.le_ordAlong i ha) ih x

omit [FiniteDimensional 𝕜 E] in
/-- [Kol07, Remark 67], "the converse also holds": a sequence of order `≥ m` for `(I, m)` with
`max-ord I ≤ m` is a sequence of order `m` starting with `(X, I)`. The marked transforms are the
birational transforms (the argument of `markedTransformSeq_eq_weakTransformSeq`), whose order
along the centres is `≥ m` by hypothesis and `≤ m` by `ord_markedTransformSeq_le`. The algebraic
counterpart is the converse direction of `isOrderGeSeq_iff_isOrderSeq`. -/
theorem isOfOrder_of_isOfOrderGe_of_ord_le (hge : B.IsOfOrderGe I m E₀) (hI : ∀ y, I.ord y ≤ m) :
    B.IsOfOrder I E₀ m := by
  -- the order along the centres is exactly `m`
  have hord : ∀ i : Fin B.length, ∀ a ∈ (B.center i).support,
      IdealSheaf.ordAlongIdeal (B.center i) (B.markedTransformSeq I m i.castSucc) a = m :=
    fun i a ha => le_antisymm (by
      rw [← B.idealSheaf_center i]
      exact (ordAlong_le_ord (B.isClosedSubmanifold_center i) _ ha).trans
        (B.ord_markedTransformSeq_le hge hI i.castSucc a)) (hge.le_ordAlong i ha)
  -- the marked transforms are the weak transforms
  have heq : ∀ i : Fin (B.length + 1), B.markedTransformSeq I m i = B.weakTransformSeq I i := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      rw [markedTransformSeq_succ, weakTransformSeq_succ, ih,
        weakTransform_eq (B.map i) (B.isClosedSubmanifold_center i) (B.isIdealSheafOf_center i)
          (B.isBlowUp_map i)]
      exact birationalTransform_eq_weakTransformOf_of_ordAlong_eq (B.isClosedSubmanifold_center i)
        (B.isBlowUp_map i) _ fun a ha => by
          rw [B.idealSheaf_center i, ← ih]
          exact hord i a ha
  intro i
  refine ⟨(hge i).1, fun a ha => ?_⟩
  rw [← heq]
  exact hord i a ha

end AnalyticManifold.FiniteSuccession

end
