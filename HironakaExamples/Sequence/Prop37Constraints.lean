/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Extension
public import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.Pullback
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Warning 38 and Example 28.1: why a blow-up sequence functor is given on disconnected schemes

By [Kol07, Warning 38] and [Kol07, Example 28.1] a blow-up sequence functor must be given on
disconnected inputs, because the order in which disjoint centers are blown up is data that the
connected pieces do not determine: on the two open pieces of Example 28.1 the rule "blow up the
smooth curve first" produces local sequences with different first centers on the overlap, so the
compatibility (37.1) of the proof of [Kol07, Proposition 37] fails and no sequence on `X`
restricts to both. This module proves the mechanism for an arbitrary covering family and the
resulting constraint on the extension of Proposition 37; the concrete model of Example 28.1 (two
disjoint cusp models in `𝔸³_k`) is computed in `HironakaExamples/KollarExample28_1.lean`.

* **(37.1) is necessary** (`agreeOnOverlaps_of_exists_pullback_eq`): the restrictions of one
  sequence agree on every overlap, because pullback is functorial (`pullback_comp`) and the two
  composites `fst ≫ ι i`, `snd ≫ ι j` are the same morphism (`pullback.condition`).
* **Different first centers do not glue** (`not_agreeOnOverlaps_of_center_ne`,
  `not_exists_pullback_eq_of_center_ne`): if the members `i, j` start with centers whose inverse
  images on the overlap differ, the pulled-back sequences differ already in their first center
  (`cons` injectivity), whatever the continuations.
* **The constraint** (`Triple.closedUnderSigma_univ`, `extendFromAffine_seq_of_isSigmaOf`): the
  class of all triples is closed under finite disjoint unions, and the extension of Proposition 37
  takes, on a disjoint union of affine triples, the value the given functor `B` carries there:
  "we need to know `B` for the disconnected affine scheme `∐ᵢ Uᵢ`" (the closure of the affine
  class under disjoint unions and `extendFromAffine_restrict`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}} {σ : Type u} {W : σ → Scheme.{u}}

/-- The restrictions of one blow-up sequence on `X` to a family of morphisms agree on the
overlaps: the compatibility (37.1) of the proof of [Kol07, Proposition 37] is necessary for
gluing. -/
theorem agreeOnOverlaps_of_exists_pullback_eq (ι : ∀ i, W i ⟶ X) (S : ∀ i, BlowUpSequence (W i))
    (h : ∃ S₀ : BlowUpSequence X, ∀ i, S₀.pullback (ι i) = S i) : AgreeOnOverlaps ι S := by
  obtain ⟨S₀, hS₀⟩ := h
  intro i j
  rw [← hS₀ i, ← hS₀ j, ← pullback_comp, ← pullback_comp, pullback.condition]

/-- Two members of a family whose first centers differ on their overlap do not agree on the
overlaps, whatever the continuations (the mechanism of [Kol07, Example 28.1]): the pulled-back
`cons` sequences differ in their first center (`cons_inj`). -/
theorem not_agreeOnOverlaps_of_center_ne (ι : ∀ i, W i ⟶ X) (S : ∀ i, BlowUpSequence (W i))
    {i j : σ} {Dᵢ : (W i).IdealSheafData} {rᵢ : BlowUpSequence Dᵢ.blowUp}
    {Dⱼ : (W j).IdealSheafData} {rⱼ : BlowUpSequence Dⱼ.blowUp}
    (hi : S i = cons (W i) Dᵢ rᵢ) (hj : S j = cons (W j) Dⱼ rⱼ)
    (hne : Dᵢ.comap (pullback.fst (ι i) (ι j)) ≠ Dⱼ.comap (pullback.snd (ι i) (ι j))) :
    ¬ AgreeOnOverlaps ι S := by
  intro hc
  have h : (cons (W i) Dᵢ rᵢ).pullback (pullback.fst (ι i) (ι j)) =
      (cons (W j) Dⱼ rⱼ).pullback (pullback.snd (ι i) (ι j)) := by
    have := hc i j
    rwa [hi, hj] at this
  exact hne (cons_inj h).1

/-- No blow-up sequence on `X` restricts to a family two of whose members start with centers that
differ on their overlap ([Kol07, Example 28.1 and Warning 38]). -/
theorem not_exists_pullback_eq_of_center_ne (ι : ∀ i, W i ⟶ X) (S : ∀ i, BlowUpSequence (W i))
    {i j : σ} {Dᵢ : (W i).IdealSheafData} {rᵢ : BlowUpSequence Dᵢ.blowUp}
    {Dⱼ : (W j).IdealSheafData} {rⱼ : BlowUpSequence Dⱼ.blowUp}
    (hi : S i = cons (W i) Dᵢ rᵢ) (hj : S j = cons (W j) Dⱼ rⱼ)
    (hne : Dᵢ.comap (pullback.fst (ι i) (ι j)) ≠ Dⱼ.comap (pullback.snd (ι i) (ι j))) :
    ¬ ∃ S₀ : BlowUpSequence X, ∀ i, S₀.pullback (ι i) = S i :=
  fun h =>
    not_agreeOnOverlaps_of_center_ne ι S hi hj hne (agreeOnOverlaps_of_exists_pullback_eq ι S h)

end Hironaka.Sequence

namespace Hironaka

variable {k : Type u} [Field k]

/-- The class of all triples is closed under finite disjoint unions. -/
theorem _root_.AlgebraicGeometry.Triple.closedUnderSigma_univ : Triple.ClosedUnderSigma
    (fun _ : Triple k => True) := by
  intro σ _ _ Ts T ι _ _
  trivial

/-- The class of all marked triples is closed under finite disjoint unions. -/
theorem MarkedTriple.closedUnderSigma_univ :
    MarkedTriple.ClosedUnderSigma (fun _ : MarkedTriple k => True) := by
  intro σ _ _ Ts T ι _ _
  trivial

/-- On a disjoint union of affine triples the extension of [Kol07, Proposition 37] is the given
functor ("we need to know `B` for the disconnected affine scheme", [Kol07, Warning 38]): the
disjoint union is affine and the extension restricts to `B` on affine triples
(`extendFromAffine_restrict`). -/
theorem OrderSeqAssignment.extendFromAffine_seq_of_isSigmaOf [CharZero k] {m : ℕ}
    (B : OrderSeqAssignment k m Triple.IsAffineScheme) (hB : B.CommutesWithSmoothSurjections)
    {σ : Type u} [Finite σ] [Nonempty σ] (Ts : σ → Triple k) (T : Triple k)
    (ι : ∀ i, (Ts i).X.left ⟶ T.X.left) (h : T.IsSigmaOf Ts ι) (hTs : ∀ i, (Ts i).IsAffineScheme) :
    (extendFromAffine B hB).seq T trivial =
      B.seq T (Triple.closedUnderSigma_isAffine Ts T ι h hTs) :=
  extendFromAffine_restrict B hB T _

/-- On a disjoint union of affine marked triples the extension of [Kol07, Proposition 37] is the
given functor. -/
theorem OrderGeSeqAssignment.extendFromAffine_seq_of_isSigmaOf [CharZero k]
    (B : OrderGeSeqAssignment k MarkedTriple.IsAffineScheme) (hB : B.CommutesWithSmoothSurjections)
    {σ : Type u} [Finite σ] [Nonempty σ] (Ts : σ → MarkedTriple k) (T : MarkedTriple k)
    (ι : ∀ i, (Ts i).X.left ⟶ T.X.left) (h : T.IsSigmaOf Ts ι) (hTs : ∀ i, (Ts i).IsAffineScheme) :
    (extendFromAffine B hB).seq T trivial =
      B.seq T (MarkedTriple.closedUnderSigma_isAffineScheme Ts T ι h hTs) :=
  extendFromAffine_restrict B hB T _

end Hironaka
