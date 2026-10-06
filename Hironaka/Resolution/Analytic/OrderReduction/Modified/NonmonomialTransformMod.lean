/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2Sep
public import Hironaka.Manifold.FiniteSuccession.OrderLemmas
public import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Manifold.BlowUp.Transform.MarkedWeak
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Round
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1MeasureOrder
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1PerBlowUp
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Purity
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bStep
import Hironaka.Resolution.Analytic.Restrict.GoingDown
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The transform identity for the nonmonomial part, at the exact order and modulo `N`

Kollár's proof of the marked order reduction theorem [Kol07, Theorem 107] rests on an
observation made at the end of its first step [Kol07, 111, Step 1]: along a blow-up sequence of
order `≥ m` for `(I, m)` whose centres also have order `≥ d` for the nonmonomial part `N(I)`, the
birational transforms of `(I, m)` and of `N(I)` differ by a product of powers of the exceptional
divisors, hence only in their monomial part, so that
`N((Π)⁻¹_*(I, m)) = (Π)⁻¹_* N(I)`. This module proves two forms of that identity on an analytic
manifold, stage by stage along a list of centres:

* `nonmonomialTransformIdentityMod_inhabitant`, the identity **modulo `N`** at an arbitrary
  order `s` for `(N(𝓘), s)`: `N(mt_i(𝓘, m)) = N(mt_i(N(𝓘), s))` at every stage `i`, with respect
  to the transformed boundary. No bound on the order of `N(𝓘)` and no relation between `m` and
  `s` is needed; the separation step of the proof [Kol07, 111, Step 2] uses it at `s < m`.
* `nonmonomialTransformIdentity_inhabitant`, the identity **at the exact order** `d ≥ m` when
  `ord N(𝓘) ≤ d` everywhere: `N(mt_i(𝓘, m)) = mt_i(N(𝓘), d)`, the right side without an outer
  `N`, because the marked transform of a purely nonmonomial ideal at its exact order stays purely
  nonmonomial (`componentExponent_markedTransformSeq_nonmonomialTriple_eq_zero`). The first step
  of the proof [Kol07, 111, Step 1] uses it.

The two identities are the predicates `NonmonomialTransformIdentityMod` and
`NonmonomialTransformIdentity`, which the assembly of the theorem takes as parameters. The input
is the identity for one blow-up along a smooth centre
(`nonmonomialPart_birationalTransform_eq_nonmonomialPart_totalTransform_nonmonomialPart` and its
consequences); the induction along the stages realigns the marked ideal from the chart of the
stage to the fixed model `ψ₀` at each step. The scheme-theoretic counterpart is
`Hironaka.BMO.nonmonomialPart_markedTransformSeq_eq_of_isOrderGeSeq`.
-/

public section

open Set Topology TopologicalSpace AnalyticManifold.FiniteSuccession
  Hironaka.Manifold.BMO
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- **The transform identity modulo `N`** along a list of centres: for a list of order `≥ m` for
`(𝓘, m)` and of order `≥ s` for `(N(𝓘), s)`, the nonmonomial parts of the marked transforms of
`(𝓘, m)` and of `(N(𝓘), s)` coincide at every stage, with respect to the transformed boundary
(the observation at the end of [Kol07, 111, Step 1], read modulo the monomial part). Induction on
the stage: the base case is the idempotence `N(N(𝓘)) = N(𝓘)` (`nonmonomialPart_nonmonomialPart`);
at a successor stage the marked ideal is realigned from the chart of the stage to the fixed model
`ψ₀`, the identity for one blow-up, `N(π⁻¹_*(J, k)) = N(π^* N(J))`, is applied to both marked
ideals, and the induction hypothesis identifies the two right sides. -/
theorem nonmonomialTransformIdentityMod_inhabitant (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) :
    NonmonomialTransformIdentityMod.{u} ψ₀ := by
  intro M S L m s hm hL hN i
  induction i using Fin.induction with
  | zero => exact (nonmonomialPart_nonmonomialPart S.F S.isSnc S.I).symm
  | succ i ih =>
    have hZ := (L.toSuccession.isClosedSubmanifold_center i).congr_chart ψ₀
    have hπ := (L.toSuccession.isBlowUp_map i).congr_chart ψ₀
    have hFi := (L.toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq S.isSnc
      (fun j => hN.hasOnlyNormalCrossingsWith j) i.castSucc).1
    have hsnc := L.toSuccession.hasSncWith_totalTransformSeqFrom_center_of_forall_lt S.isSnc i
      (fun i' _ => hN.hasOnlyNormalCrossingsWith i')
    have hkm : ∀ x ∈ (L.toSuccession.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        hZ.idealSheaf (L.toSuccession.markedTransformSeq S.I m i.castSucc) x := fun x hx => by
      rw [hZ.idealSheaf_eq_of_set (L.toSuccession.isClosedSubmanifold_center i),
        L.toSuccession.idealSheaf_center i]
      exact (hL i).2 x hx
    have hks : ∀ x ∈ (L.toSuccession.center i).support, (s : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        hZ.idealSheaf (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I s i.castSucc) x :=
      fun x hx => by
        rw [hZ.idealSheaf_eq_of_set (L.toSuccession.isClosedSubmanifold_center i),
          L.toSuccession.idealSheaf_center i]
        exact (hN i).2 x hx
    have hAm :=
      nonmonomialPart_birationalTransform_eq_nonmonomialPart_totalTransform_nonmonomialPart
        hZ hπ (L.toSuccession.totalTransformSeqFrom S.F i.castSucc) hFi hsnc m hkm
        (isNonzeroEverywhere_birationalTransform hZ hπ
          ⟨L.toSuccession.markedTransformSeq S.I m i.castSucc, m⟩ hkm
          (isNonzeroEverywhere_markedTransformSeq S.isNonzeroEverywhere hL i.castSucc))
        (isNonzeroEverywhere_totalTransform hZ hπ
          (nonmonomialPart_isNonzeroEverywhere (L.toSuccession.totalTransformSeqFrom S.F i.castSucc)
            hFi _ (isNonzeroEverywhere_markedTransformSeq S.isNonzeroEverywhere hL i.castSucc)))
    have hAs :=
      nonmonomialPart_birationalTransform_eq_nonmonomialPart_totalTransform_nonmonomialPart
        hZ hπ (L.toSuccession.totalTransformSeqFrom S.F i.castSucc) hFi hsnc s hks
        (isNonzeroEverywhere_birationalTransform hZ hπ
          ⟨L.toSuccession.markedTransformSeq (nonmonomialTriple S).I s i.castSucc, s⟩ hks
          (isNonzeroEverywhere_markedTransformSeq (nonmonomialTriple S).isNonzeroEverywhere hN
            i.castSucc))
        (isNonzeroEverywhere_totalTransform hZ hπ
          (nonmonomialPart_isNonzeroEverywhere (L.toSuccession.totalTransformSeqFrom S.F i.castSucc)
            hFi _ (isNonzeroEverywhere_markedTransformSeq (nonmonomialTriple S).isNonzeroEverywhere
                hN
              i.castSucc)))
    rw [markedTransformSeq_succ, markedTransformSeq_succ,
      MarkedIdealSheaf.birationalTransform_congr (L.toSuccession.isClosedSubmanifold_center i) hZ
        rfl (L.toSuccession.isBlowUp_map i) hπ,
      MarkedIdealSheaf.birationalTransform_congr (L.toSuccession.isClosedSubmanifold_center i) hZ
        rfl (L.toSuccession.isBlowUp_map i) hπ]
    calc nonmonomialPart _ _
          (MarkedIdealSheaf.birationalTransform hZ hπ
            ⟨L.toSuccession.markedTransformSeq S.I m i.castSucc, m⟩).I
        = nonmonomialPart _ _ (Manifold.IdealSheaf.pullback _ hπ.contMDiff
            (nonmonomialPart (L.toSuccession.totalTransformSeqFrom S.F i.castSucc) hFi
              (L.toSuccession.markedTransformSeq S.I m i.castSucc))) := hAm
      _ = nonmonomialPart _ _ (Manifold.IdealSheaf.pullback _ hπ.contMDiff
            (nonmonomialPart (L.toSuccession.totalTransformSeqFrom S.F i.castSucc) hFi
              (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I s i.castSucc))) := by
          rw [ih]
      _ = nonmonomialPart _ _ (MarkedIdealSheaf.birationalTransform hZ hπ
            ⟨L.toSuccession.markedTransformSeq (nonmonomialTriple S).I s i.castSucc, s⟩).I :=
          hAs.symm

omit [FiniteDimensional 𝕜 E] in
/-- **The marked transform of a purely nonmonomial ideal at its exact order stays purely
nonmonomial**: along a list of order `≥ d` for `(N(𝓘), d)`, where `d` bounds the order of `N(𝓘)`
everywhere, the marked transform of `(N(𝓘), d)` has, at every stage, vanishing exponent along
every component of the transformed boundary, i.e. its monomial part is trivial. Induction on the
stage: `N(𝓘)` itself has vanishing exponents (`componentExponent_nonmonomialPart_eq_zero`); at a
successor stage the order of the previous transform along the centre is exactly `d`, so the
marked transform is the weak transform (`birationalTransform_eq_weakTransformOf_of_ordAlong_eq`),
and the weak transform at the exact order of an ideal with vanishing exponents has vanishing
exponents (`componentExponent_weakTransformOf_eq_zero`). -/
theorem componentExponent_markedTransformSeq_nonmonomialTriple_eq_zero
    (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜))
    {M : AnalyticManifold.{u} 𝕜 E} (S : AnalyticTriple ψ₀ M) (L : AnalyticManifold.BlowUpSequence
        ψ₀ M) (d : ℕ)
    (hmax : ∀ x, ((nonmonomialTriple S).I).ord x ≤ (d : ℕ∞))
    (hL : L.toSuccession.IsOfOrderGe (nonmonomialTriple S).I d
      (S.F.idealSheaf (𝕜 := 𝕜) (E := E)))
    (i : Fin (L.toSuccession.length + 1)) :
    ∀ j : ComponentIndex (L.toSuccession.totalTransformSeqFrom S.F i),
      componentExponent (L.toSuccession.totalTransformSeqFrom S.F i)
          (L.toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq S.isSnc
            (fun k => hL.hasOnlyNormalCrossingsWith k) i).1
          (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i) j = 0 := by
  induction i using Fin.induction with
  | zero => exact fun j => componentExponent_nonmonomialPart_eq_zero S.F S.isSnc S.I j
  | succ i ih =>
    intro j
    have hZ := (L.toSuccession.isClosedSubmanifold_center i).congr_chart ψ₀
    have hπ := (L.toSuccession.isBlowUp_map i).congr_chart ψ₀
    have hFi := (L.toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq S.isSnc
      (fun k => hL.hasOnlyNormalCrossingsWith k) i.castSucc).1
    have hsnc := L.toSuccession.hasSncWith_totalTransformSeqFrom_center_of_forall_lt S.isSnc i
      (fun i' _ => hL.hasOnlyNormalCrossingsWith i')
    have hle : ∀ a ∈ (L.toSuccession.center i).support,
        (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i.castSucc).ord a ≤ d :=
      fun a _ => ord_markedTransformSeq_le L.toSuccession hL hmax i.castSucc a
    have hord : ∀ a ∈ (L.toSuccession.center i).support, IdealSheaf.ordAlongIdeal hZ.idealSheaf
        (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i.castSucc) a = d := by
      intro a ha
      refine le_antisymm ((ordAlong_le_ord hZ _ ha).trans (hle a ha)) ?_
      rw [hZ.idealSheaf_eq_of_set (L.toSuccession.isClosedSubmanifold_center i),
        L.toSuccession.idealSheaf_center i]
      exact (hL i).2 a ha
    rw [markedTransformSeq_succ,
      MarkedIdealSheaf.birationalTransform_congr (L.toSuccession.isClosedSubmanifold_center i) hZ
        rfl (L.toSuccession.isBlowUp_map i) hπ,
      birationalTransform_eq_weakTransformOf_of_ordAlong_eq hZ hπ
        (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i.castSucc) hord]
    exact componentExponent_weakTransformOf_eq_zero hZ hπ
      (L.toSuccession.totalTransformSeqFrom S.F i.castSucc) hFi hsnc _ hord hle ih j

omit [FiniteDimensional 𝕜 E] in
/-- **The transform identity at the exact order** (the observation at the end of
[Kol07, 111, Step 1]): for `m ≤ d`, along a list of order `≥ d` for `(N(𝓘), d)` with `ord N(𝓘) ≤ d`
everywhere, the nonmonomial part of the marked transform of `(𝓘, m)` at every stage is the marked
transform of `(N(𝓘), d)` itself, `N(mt_i(𝓘, m)) = mt_i(N(𝓘), d)`. The induction on the stage
carries along the fact that `mt_i(𝓘, m)` is nonzero everywhere; the order clause for `(𝓘, m)` at
each centre follows from the one for `(N(𝓘), d)`, since `𝓘_i ⊆ N(𝓘_i) = N_i` gives
`ord_Z 𝓘_i ≥ ord_Z N_i ≥ d ≥ m`. At a successor stage the identity for one blow-up gives
`N(mt_{i+1}(𝓘, m)) = N(π^* N(mt_i(𝓘, m)))`, the induction hypothesis rewrites the inner ideal to
`mt_i(N(𝓘), d)`, and the transform of that ideal at its exact order is its own nonmonomial part
(`nonmonomialPart_birationalTransform_eq_self`, from the purity of the previous theorem). -/
theorem nonmonomialTransformIdentity_inhabitant (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) :
    NonmonomialTransformIdentity.{u} ψ₀ := by
  intro M S L m d hm hmd hmax hL i
  suffices h : (L.toSuccession.markedTransformSeq S.I m i).IsNonzeroEverywhere ∧
      nonmonomialPart (L.toSuccession.totalTransformSeqFrom S.F i)
          (L.toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq S.isSnc
            (fun k => hL.hasOnlyNormalCrossingsWith k) i).1
          (L.toSuccession.markedTransformSeq S.I m i) =
        L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i from h.2
  induction i using Fin.induction with
  | zero => exact ⟨S.isNonzeroEverywhere, rfl⟩
  | succ i ih =>
    obtain ⟨ihnz, ihid⟩ := ih
    have hZ := (L.toSuccession.isClosedSubmanifold_center i).congr_chart ψ₀
    have hπ := (L.toSuccession.isBlowUp_map i).congr_chart ψ₀
    have hFi := (L.toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq S.isSnc
      (fun k => hL.hasOnlyNormalCrossingsWith k) i.castSucc).1
    have hsnc := L.toSuccession.hasSncWith_totalTransformSeqFrom_center_of_forall_lt S.isSnc i
      (fun i' _ => hL.hasOnlyNormalCrossingsWith i')
    have hNi_nz := isNonzeroEverywhere_markedTransformSeq (nonmonomialTriple S).isNonzeroEverywhere
      hL i.castSucc
    have hk_m : ∀ x ∈ (L.toSuccession.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        hZ.idealSheaf (L.toSuccession.markedTransformSeq S.I m i.castSucc) x := by
      intro x hx
      rw [hZ.idealSheaf_eq_of_set (L.toSuccession.isClosedSubmanifold_center i),
        L.toSuccession.idealSheaf_center i]
      calc (m : ℕ∞) ≤ (d : ℕ∞) := Nat.cast_le.mpr hmd
        _ ≤ IdealSheaf.ordAlongIdeal (L.toSuccession.center i)
              (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i.castSucc) x :=
            (hL i).2 x hx
        _ = IdealSheaf.ordAlongIdeal (L.toSuccession.center i)
              (nonmonomialPart (L.toSuccession.totalTransformSeqFrom S.F i.castSucc) hFi
                (L.toSuccession.markedTransformSeq S.I m i.castSucc)) x := by rw [← ihid]
        _ ≤ IdealSheaf.ordAlongIdeal (L.toSuccession.center i)
              (L.toSuccession.markedTransformSeq S.I m i.castSucc) x :=
            ordAlongIdeal_anti _ (le_nonmonomialPart _ _ _) x
    have hle : ∀ a ∈ (L.toSuccession.center i).support,
        (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i.castSucc).ord a ≤ d :=
      fun a _ => ord_markedTransformSeq_le L.toSuccession hL hmax i.castSucc a
    have hord : ∀ a ∈ (L.toSuccession.center i).support, IdealSheaf.ordAlongIdeal hZ.idealSheaf
        (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i.castSucc) a = d := by
      intro a ha
      refine le_antisymm ((ordAlong_le_ord hZ _ ha).trans (hle a ha)) ?_
      rw [hZ.idealSheaf_eq_of_set (L.toSuccession.isClosedSubmanifold_center i),
        L.toSuccession.idealSheaf_center i]
      exact (hL i).2 a ha
    have hk_d : ∀ x ∈ (L.toSuccession.center i).support, (d : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        hZ.idealSheaf (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i.castSucc) x :=
      fun x hx => (hord x hx).ge
    have hJmt := isNonzeroEverywhere_birationalTransform hZ hπ
      ⟨L.toSuccession.markedTransformSeq S.I m i.castSucc, m⟩ hk_m ihnz
    have hJmt' := isNonzeroEverywhere_birationalTransform hZ hπ
      ⟨L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i.castSucc, d⟩ hk_d hNi_nz
    have hNnz := isNonzeroEverywhere_totalTransform hZ hπ
      (nonmonomialPart_isNonzeroEverywhere (L.toSuccession.totalTransformSeqFrom S.F i.castSucc)
          hFi _
        ihnz)
    have hpure := componentExponent_markedTransformSeq_nonmonomialTriple_eq_zero ψ₀ S L d hmax hL
      i.castSucc
    refine ⟨?_, ?_⟩
    · rw [markedTransformSeq_succ,
        MarkedIdealSheaf.birationalTransform_congr (L.toSuccession.isClosedSubmanifold_center i) hZ
          rfl (L.toSuccession.isBlowUp_map i) hπ]
      exact hJmt
    · rw [markedTransformSeq_succ, markedTransformSeq_succ,
        MarkedIdealSheaf.birationalTransform_congr (L.toSuccession.isClosedSubmanifold_center i) hZ
          rfl (L.toSuccession.isBlowUp_map i) hπ,
        MarkedIdealSheaf.birationalTransform_congr (L.toSuccession.isClosedSubmanifold_center i) hZ
          rfl (L.toSuccession.isBlowUp_map i) hπ]
      -- The identity is assembled in term mode (`.trans`/`congrArg`), not by `calc`/`rw` on a goal
      -- carrying the huge transformed family `F.totalTransform` in the motive: the head-changing
      -- rewrite `ihid` is done on the small goal `hmid` (no outer family), the wrapper is restored
      -- by `congrArg`, and the outer family is reconciled with `F_{i.succ}` exactly once.
      have hAm :=
        nonmonomialPart_birationalTransform_eq_nonmonomialPart_totalTransform_nonmonomialPart
          hZ hπ (L.toSuccession.totalTransformSeqFrom S.F i.castSucc) hFi hsnc m hk_m hJmt hNnz
      have hAd :=
        nonmonomialPart_totalTransform_eq_nonmonomialPart_birationalTransform hZ hπ
          (L.toSuccession.totalTransformSeqFrom S.F i.castSucc) hFi hsnc d hk_d hJmt'
      have hSelf :=
        nonmonomialPart_birationalTransform_eq_self hZ hπ
          (L.toSuccession.totalTransformSeqFrom S.F i.castSucc) hFi hsnc _ hord hle hpure
      have hmid : Manifold.IdealSheaf.pullback _ hπ.contMDiff
            (nonmonomialPart (L.toSuccession.totalTransformSeqFrom S.F i.castSucc) hFi
              (L.toSuccession.markedTransformSeq S.I m i.castSucc)) =
          Manifold.IdealSheaf.pullback _ hπ.contMDiff
            (L.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i.castSucc) := by
        rw [ihid]
      exact hAm.trans ((congrArg (nonmonomialPart _ _) hmid).trans (hAd.trans hSelf))

end Hironaka.Manifold.BMOmod
