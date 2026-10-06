/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.NonmonomialTriple
public import Hironaka.Manifold.FiniteSuccession.CenterList
public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
public import Hironaka.Manifold.StructureSheaf
public import Hironaka.Manifold.FiniteSuccession.OrderLemmas
public import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Round
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The rounds on the nonmonomial part: the order transfer

Kollár's proof of the marked order reduction theorem [Kol07, Theorem 107] opens with rounds of
order reduction on the nonmonomial part `N(I)` at its maximal order `d`, "until its order drops
below `m`" [Kol07, 111, Step 1]; the modified algorithm of [Wlo09, Theorem 7.4.1] opens with the
same rounds, run "until we drop `max{ord_x N(I) : x ∈ supp I}` to 1", i.e. at `d ≥ 2` only. The
library writes this loop once, with the mark `m` and a threshold `t` (`m ≤ t`) as parameters: the
descent runs through the bounds `d = D, …, t`. Kollár's first step is the instance `t = m`, the
first phase of the modified algorithm is `m = 1`, `t = 2`. The modules `Modified/StepA*.lean` hold
this loop: the link (`StepALink.lean`), the descent (`StepAChain.lean`), the value on a relatively
compact open (`StepAFamily.lean`) and its naturality.

This module holds the **order transfer** of a round: a list of order `≥ d` for `(N(𝓘), d)` is of
order `≥ m` for `(𝓘, m)` when `m ≤ d`, by the identity `N((Π)⁻¹_*(𝓘, m)) = (Π)⁻¹_* N(𝓘)` of
[Kol07, 111, Step 1] and `𝓘 ≤ N(𝓘)` (the order along a centre is antitone in the ideal,
`ordAlongIdeal_anti`). The identity is the predicate `NonmonomialTransformIdentity`, which the
assembly takes as a parameter and which `nonmonomialTransformIdentity_inhabitant` proves.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

section Anti

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E}

/-- The order along a centre is antitone in the ideal: a smaller ideal lies in more powers. -/
theorem ordAlongIdeal_anti (D : AnalyticManifold.IdealSheaf M)
    {J J' : AnalyticManifold.IdealSheaf M}
    (h : J ≤ J') (a : M) : IdealSheaf.ordAlongIdeal D J' a ≤ IdealSheaf.ordAlongIdeal D J a := by
  refine iSup₂_le fun p hp => ?_
  exact le_iSup_of_le p (le_iSup_of_le ((IdealSheaf.le_def.mp h a).trans hp) le_rfl)

end Anti

section Identity

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ}

/-- **The transform identity for the nonmonomial part at the exact order**: along a list of order
`≥ d` for `(N(𝓘), d)`, with `1 ≤ m ≤ d` and `d` an upper bound of `ord N(𝓘)` on the manifold, the
nonmonomial part of the marked transform of `(𝓘, m)` at every stage is the marked transform of
`(N(𝓘), d)`. This is Kollár's observation that the two birational transforms differ only in their
monomial part, by a product of powers of the exceptional divisors [Kol07, 111, Step 1], in the
setting of that step: order reduction of `N(I)` at its maximal order, so that every centre has
order exactly `d` for `N(𝓘)` and the marked transform of `(N(𝓘), d)` stays purely nonmonomial.
Without the bound the identity fails: for `N = (x²)`, `d = 1` and the blow-up of `{x = 0}` the
marked transform of `(N, 1)` acquires a monomial factor. The predicate is a parameter of the
assembly; `nonmonomialTransformIdentity_inhabitant` proves it. -/
def NonmonomialTransformIdentity (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) : Prop :=
  ∀ {M : AnalyticManifold.{u} 𝕜 E} (S : AnalyticTriple ψ₀ M) (L : AnalyticManifold.BlowUpSequence
      ψ₀ M) (m d : ℕ),
    1 ≤ m → m ≤ d → (∀ x, ((nonmonomialTriple S).I).ord x ≤ (d : ℕ∞)) →
    ∀ (hL : L.toSuccession.IsOfOrderGe (nonmonomialTriple S).I d
        (S.F.idealSheaf (𝕜 := 𝕜) (E := E)))
      (i : Fin (L.toSuccession.length + 1)),
      nonmonomialPart (L.toSuccession.totalTransformSeqFrom S.F i)
          (L.toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq S.isSnc
            (fun j => hL.hasOnlyNormalCrossingsWith j) i).1
          (L.toSuccession.markedTransformSeq S.I m i) =
        L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

omit [FiniteDimensional 𝕜 E] in
/-- **The order transfer**: a list of order `≥ d` for `(N(𝓘), d)`, with `d` bounding `ord N(𝓘)`, is
of order `≥ m` for `(𝓘, m)` when `m ≤ d`. The normal crossings clause is shared (same centres, same
boundary), and at every stage `𝓘_i ≤ N(𝓘_i) = N_i` (`le_nonmonomialPart` and the transform
identity), so the order along the centre only grows: `ord_Z 𝓘_i ≥ ord_Z N_i ≥ d ≥ m`
[Kol07, 111, Step 1]. -/
theorem isOfOrderGe_of_nonmonomial (hid : NonmonomialTransformIdentity.{u} ψ₀)
    {M : AnalyticManifold.{u} 𝕜 E} (S : AnalyticTriple ψ₀ M) (L : AnalyticManifold.BlowUpSequence
        ψ₀ M) {m d : ℕ}
    (hm : 1 ≤ m) (hmd : m ≤ d) (hmax : ∀ x, ((nonmonomialTriple S).I).ord x ≤ (d : ℕ∞))
    (hL : L.toSuccession.IsOfOrderGe (nonmonomialTriple S).I d
      (S.F.idealSheaf (𝕜 := 𝕜) (E := E))) :
    L.toSuccession.IsOfOrderGe S.I m (S.F.idealSheaf (𝕜 := 𝕜) (E := E)) := by
  intro i
  refine ⟨(hL i).1, fun a ha => ?_⟩
  have h1 := (hL i).2 a ha
  have hid' := hid S L m d hm hmd hmax hL i.castSucc
  calc (m : ℕ∞) ≤ (d : ℕ∞) := Nat.cast_le.mpr hmd
    _ ≤ IdealSheaf.ordAlongIdeal (L.toSuccession.center i)
          (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i.castSucc) a := h1
    _ = IdealSheaf.ordAlongIdeal (L.toSuccession.center i)
          (nonmonomialPart (L.toSuccession.totalTransformSeqFrom S.F i.castSucc)
            (L.toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq S.isSnc
              (fun j => hL.hasOnlyNormalCrossingsWith j) i.castSucc).1
            (L.toSuccession.markedTransformSeq S.I m i.castSucc)) a := by rw [hid']
    _ ≤ IdealSheaf.ordAlongIdeal (L.toSuccession.center i)
          (L.toSuccession.markedTransformSeq S.I m i.castSucc) a :=
        ordAlongIdeal_anti _ (le_nonmonomialPart _ _ _) a

end Identity

end Hironaka.Manifold.BMOmod

end
