/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BDFamTransport
public import Hironaka.Manifold.FiniteSuccession.Functor.PushforwardPullback
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.TunedLemmas
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Lemma 102 in the compatible-family form: the order clause and clause (1)

The two clauses of [Kol07, Lemma 102] about the sequence itself, for the value `BDanFam` on a
relatively compact open `U` (`BDFam.lean`): it is a smooth blow-up sequence of order `m` starting
with the restricted triple (`BDanFam_isOfOrder`), and at its end the strict transform of `E^j`
misses `cosupp(I_r, m)` (`BDanFam_cosupp_disjoint`, clause (1)). By `coreFamOn_eq_coreOfListOf`
(`BDFamTransport.lean`) the core on `U` is the core over the input's value transported to the
restricted data, so the clauses are those of the core over a sequence
(`Hironaka/Resolution/Analytic/OrderReduction/BD.lean`) once the input family's clauses on its open
are transported along the two local analytic isomorphisms of the transport, the bundle
diffeomorphism and the restricted lift, and the restricted triple of the restricted data is
identified with the pull-back of the restricted triple along the composite
(`restrictedTripleOf_restrict_eq`; the proof of Lemma 102: restricting and pulling back commute).
The clauses hold first at the mark `s = tuningParam m` for the tuned triple, on which `BDanFam`
runs, and are carried back to `(𝓘, m)` by `orderReduction_tuned_iff` and `ord_lt_of_tuned`
(`TunedLemmas.lean`), as for `BDan` in `BDCore.lean` and `BDCosupp.lean`.

* `Zminus1_restrict`, `transformSU_eq` — the centre and the transform of the restricted data are
  the restrictions of `Z_{-1}` and `S_0`;
* `noEmptyCenters_transportedValue`, `isOfOrderGe_transportedValue`, `ord_lt_transportedValue` —
  the transported value inherits the input's three properties;
* `coreFamOn_isOfOrderGe`, `coreFamOn_cosupp_disjoint` — the clauses for the core on `U`;
* `BDanFam_isOfOrder`, `BDanFam_cosupp_disjoint` — the clauses for the value of `BD_{n,m,j}` on `U`.

These are the `isOfOrder` and `cosupp_disjoint` fields of Lemma 102's family data
`bdanFamDataOfInput` in `BOanFamOfInput.lean`.
-/

public section

universe u

open Set Topology TopologicalSpace AnalyticManifold IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace BDan

open _root_.Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ)
  (j : T.F.ι) (inp : BMOanFam 𝕜 (n - 1) s) (hT : BDClass s T) (U : Opens M)
  (hU : IsCompact (closure (U : Set M)))

/-- The centre of the restricted data is the restriction of `Z_{-1}` (`BD.Zminus1_comap` for the
inclusion of `U`). -/
theorem Zminus1_restrict :
    ⇑(M.inclusion U) ⁻¹' BD.Zminus1 T.I s (T.F.hyp j) =
      BD.Zminus1 (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I s
        ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.hyp j) :=
  (BD.Zminus1_comap (M.inclusion U) (isLocalDiffeomorph_inclusion M U) T.I s (T.isSnc.1 j)).symm

/-- The transform of `E^j` in the restricted blowing-up is the transform of the restricted data. -/
theorem transformSU_eq :
    ⇑(liftIncl T s j U) ⁻¹'
        (⇑((blowUp ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)).inclusion (piOpen T s j U)) ⁻¹'
          transformS T s j) =
      transformSOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) j
        ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
          (isLocalDiffeomorph_inclusion M U)) :=
  preimage_liftStep_transformS T s j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)

/-- The transported value has no empty centres: it is the input's value, which has none, pulled
back twice along surjective local analytic isomorphisms. -/
theorem noEmptyCenters_transportedValue : (transportedValue T s j inp hT U hU).NoEmptyCenters :=
  BlowUpSequence.noEmptyCenters_pullback_of_surjective _ _ _
    (IsClosedSubmanifold.surjective_restrictMap _ _ _ (surjective_liftIncl T s j U))
    (BlowUpSequence.noEmptyCenters_pullback_of_surjective _ _ _ (surjective_bundleInv T s j U)
      ((inp.functor.fam _ _).noEmptyCenters _ _))

/-- The composite of the two transport maps followed by the inclusion of the trace is the
restriction of the lift of the inclusion to the transforms of `E^j` (equal on the underlying
points). -/
theorem inclusion_comp_bundleInv_comp_liftInclS :
    (((isClosedSubmanifold_transformS T s j).toAnalyticManifold.inclusion
        ((isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j U))).comp
      (bundleInv T s j U)).comp (liftInclS T s j U) =
    (isClosedSubmanifold_transformSU T s j U).restrictMap (isClosedSubmanifold_transformS T s j)
      (BlowUpSequence.liftStep (M.inclusion U) (isLocalDiffeomorph_inclusion M U)
        (BD.isClosedSubmanifold_Zminus1 T s j))
      (BlowUpSequence.liftStep (M.inclusion U) (isLocalDiffeomorph_inclusion M U)
        (BD.isClosedSubmanifold_Zminus1 T s j)).contMDiff fun _ hx => hx :=
  ContMDiffMap.ext fun _ => Subtype.ext rfl

/-- The restricted triple of the restricted data is the pull-back of the restricted triple of `T`
along the composite transport map ("we get the same result" whether one first pulls back or
first restricts, the proof of [Kol07, Lemma 102]; `restrictedTripleOf_isPullbackOf`). -/
theorem restrictedTripleOf_restrict_eq
    (hT' : BDClass s (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U))) :
    restrictedTripleOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) s j
        ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
          (isLocalDiffeomorph_inclusion M U)) (isClosedSubmanifold_transformSU T s j U) hT'
        (Zminus1_restrict T s j U) (transformSU_eq T s j U) =
      (((restrictedTriple T s j hT).pullback
          ((isClosedSubmanifold_transformS T s j).toAnalyticManifold.inclusion
            ((isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j U)))
          (isLocalDiffeomorph_inclusion _ _)).pullback (bundleInv T s j U)
          (isLocalDiffeomorph_bundleInv T s j U)).pullback (liftInclS T s j U)
        (IsClosedSubmanifold.isLocalDiffeomorph_restrictMap (liftIncl T s j U)
          (isLocalDiffeomorph_liftInclOf _ U)
          ((isClosedSubmanifold_transformS T s j).restrictOpen (piOpen T s j U))) := by
  have hc₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (((isClosedSubmanifold_transformS T s j).toAnalyticManifold.inclusion
        ((isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j U))).comp
          (bundleInv T s j U)) :=
    BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_inclusion _ _)
      (isLocalDiffeomorph_bundleInv T s j U)
  have hc₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      ((((isClosedSubmanifold_transformS T s j).toAnalyticManifold.inclusion
        ((isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j U))).comp
          (bundleInv T s j U)).comp (liftInclS T s j U)) :=
    BlowUpSequence.isLocalDiffeomorph_comp hc₁ (IsClosedSubmanifold.isLocalDiffeomorph_restrictMap
      (liftIncl T s j U) (isLocalDiffeomorph_liftInclOf _ U) _)
  rw [AnalyticTriple.pullback_pullback (restrictedTriple T s j hT) _
      (isLocalDiffeomorph_inclusion _ _) (bundleInv T s j U) (isLocalDiffeomorph_bundleInv T s j U),
    AnalyticTriple.pullback_pullback (restrictedTriple T s j hT) _ hc₁ (liftInclS T s j U)
      (IsClosedSubmanifold.isLocalDiffeomorph_restrictMap (liftIncl T s j U)
        (isLocalDiffeomorph_liftInclOf _ U) _),
    AnalyticTriple.pullback_eq_of_eq (restrictedTriple T s j hT)
      (inclusion_comp_bundleInv_comp_liftInclS T s j U) hc₂
      (IsClosedSubmanifold.isLocalDiffeomorph_restrictMap _
        (BlowUpSequence.isLocalDiffeomorph_liftStep _ _ _) _)]
  exact AnalyticTriple.IsPullbackOf.eq
    (restrictedTripleOf_isPullbackOf T s j (M.inclusion U) (isLocalDiffeomorph_inclusion M U) hT
      hT')
    (AnalyticTriple.isPullbackOf_pullback _ _ _)

omit [FiniteDimensional 𝕜 E] in
/-- The clause "the controlled transform at the last stage has order `< m`" pulls back along a
local analytic isomorphism: the controlled transform of the pull-back at the last stage is the
pull-back of the controlled transform along the last lift, and the order is read at the image. -/
theorem ord_lt_last_pullback {M N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ M) (m : ℕ)
    (L : BlowUpSequence ψ₀ M) (hge : L.toSuccession.IsOfOrderGe T'.I m T'.F.idealSheaf)
    (hlt : ∀ y, (L.toSuccession.markedTransformSeq T'.I m (Fin.last _)).ord y < (m : ℕ∞))
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    ∀ y', ((L.pullback h hh).toSuccession.markedTransformSeq (T'.pullback h hh).I m
      (Fin.last _)).ord y' < (m : ℕ∞) := by
  intro y'
  change
      ((L.pullback h hh).toSuccession.markedTransformSeq
          (T'.I.pullback h h.contMDiff) m
    (Fin.last _)).ord y' < (m : ℕ∞)
  rw [BlowUpSequence.markedTransformSeq_last_pullbackLiftLast L h hh T'.I T'.F.idealSheaf m hge]
  change ((L.toSuccession.markedTransformSeq T'.I m (Fin.last _)).pullback
    ⇑(L.pullbackLiftLast h hh) (L.pullbackLiftLast h hh).contMDiff).ord y' < (m : ℕ∞)
  rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
    (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L h hh y')]
  exact hlt _

variable (hT' : BDClass s (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)))

/-- The transported value is a smooth blow-up sequence of order `≥ s` for the restricted triple of
the restricted data: the input family's clause on its open, pulled back twice. -/
theorem isOfOrderGe_transportedValue :
    (transportedValue T s j inp hT U hU).toSuccession.IsOfOrderGe
      (restrictedTripleOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) s j
        ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
          (isLocalDiffeomorph_inclusion M U)) (isClosedSubmanifold_transformSU T s j U) hT'
        (Zminus1_restrict T s j U) (transformSU_eq T s j U)).I s
      (restrictedTripleOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) s j
        ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
          (isLocalDiffeomorph_inclusion M U)) (isClosedSubmanifold_transformSU T s j U) hT'
        (Zminus1_restrict T s j U) (transformSU_eq T s j U)).F.idealSheaf := by
  rw [restrictedTripleOf_restrict_eq T s j hT U hT']
  exact AnalyticTriple.isOfOrderGe_pullback _ s _
    (AnalyticTriple.isOfOrderGe_pullback _ s _ (inp.isOfOrderGe _ _ _ _) _ _) _ _

/-- The controlled transform of the transported value at the last stage has order `< s`
everywhere: the input family's clause on its open, pulled back twice. -/
theorem ord_lt_transportedValue :
    ∀ y, ((transportedValue T s j inp hT U hU).toSuccession.markedTransformSeq
      (restrictedTripleOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) s j
        ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
          (isLocalDiffeomorph_inclusion M U)) (isClosedSubmanifold_transformSU T s j U) hT'
        (Zminus1_restrict T s j U) (transformSU_eq T s j U)).I s (Fin.last _)).ord y <
      (s : ℕ∞) := by
  rw [restrictedTripleOf_restrict_eq T s j hT U hT']
  exact ord_lt_last_pullback _ s _
    (AnalyticTriple.isOfOrderGe_pullback _ s _ (inp.isOfOrderGe _ _ _ _) _ _)
    (ord_lt_last_pullback _ s _ (inp.isOfOrderGe _ _ _ _) (inp.ord_lt _ _ _ _) _ _) _ _

include hT' in
/-- The order clause for the core on `U` at the mark `s`: it is a smooth blow-up sequence of order
`≥ s` for the restricted triple (`coreOfListOf_isOfOrderGe` at the transported value). -/
theorem coreFamOn_isOfOrderGe :
    (coreFamOn T s j inp hT U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I s
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf := by
  rw [coreFamOn_eq_coreOfListOf]
  exact coreOfListOf_isOfOrderGe (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) s j
    _ _ hT' (Zminus1_restrict T s j U) (transformSU_eq T s j U) _
    (noEmptyCenters_transportedValue T s j inp hT U hU)
    (isOfOrderGe_transportedValue T s j inp hT U hU hT')

include hT' in
/-- Clause (1) of [Kol07, Lemma 102] for the core on `U` at the mark `s`: the strict transform of
`E^j` at the end misses `cosupp(I_r, s)` (`coreOfListOf_cosupp_disjoint` at the transported
value). -/
theorem coreFamOn_cosupp_disjoint :
    Disjoint
      {x | (s : ℕ∞) ≤ ((coreFamOn T s j inp hT U hU).toSuccession.weakTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I (Fin.last _)).ord x}
      ((coreFamOn T s j inp hT U hU).toSuccession.strictTransformSeq
        ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.hyp j)
        (Fin.last _)) := by
  rw [coreFamOn_eq_coreOfListOf]
  exact coreOfListOf_cosupp_disjoint (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
    s j _ _ hT' (Zminus1_restrict T s j U) (transformSU_eq T s j U) _
    (noEmptyCenters_transportedValue T s j inp hT U hU)
    (isOfOrderGe_transportedValue T s j inp hT U hU hT')
    (ord_lt_transportedValue T s j inp hT U hU hT')

end BDan

section Clauses

variable {M : AnalyticManifold.{u} 𝕜 E} {m : ℕ}
  (inp : BMOanFam 𝕜 (n - 1) (tuningParam m)) (T : AnalyticTriple ψ₀ M)
  (hT : AnalyticTriple.BOClass m T) (j : T.F.ι) (U : Opens M)
  (hU : IsCompact (closure (U : Set M)))

/-- The tuned triple restricted to `U` lies in the class of the core (the tuning commutes with the
restriction, `tuned_pullback`). -/
theorem bdClass_tuned_pullback_inclusion :
    BDan.BDClass (tuningParam m)
      ((T.tuned m hT.1).pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) := by
  rw [← AnalyticTriple.tuned_pullback]
  exact ⟨AnalyticTriple.boClass_tuned (boClass_pullback_inclusion_of_boClass T U hT),
    AnalyticTriple.isDBalanced_tuned (boClass_pullback_inclusion_of_boClass T U hT)⟩

/-- The order clause of [Kol07, Lemma 102] ("a smooth blow-up sequence functor `BD_{n,m,j}` of order
`m`") for the value on `U`: `BDanFam m inp T hT j U hU` is a smooth blow-up sequence of order
exactly `m` starting with the restricted triple. The core's clause at the mark `s = tuningParam m`
on the tuned triple is carried back to `(𝓘, m)` by `orderReduction_tuned_iff`; the order is exactly
`m` because `ord 𝓘 ≤ m` everywhere. -/
theorem BDanFam_isOfOrder :
    (BDanFam m inp T hT j U hU).toSuccession.IsOfOrder
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf m := by
  have hTU := boClass_pullback_inclusion_of_boClass T U hT
  have hge := BDan.coreFamOn_isOfOrderGe (T.tuned m hT.1) (tuningParam m) j inp
    ⟨AnalyticTriple.boClass_tuned hT, AnalyticTriple.isDBalanced_tuned hT⟩ U hU
    (bdClass_tuned_pullback_inclusion T hT U)
  rw [← AnalyticTriple.tuned_pullback] at hge
  exact FiniteSuccession.isOfOrder_of_isOfOrderGe_of_ord_le _
    ((AnalyticTriple.orderReduction_tuned_iff _ hTU _).mp hge) hTU.2.1

/-- Clause (1) of [Kol07, Lemma 102], "`cosupp(I_r, m) ∩ Π^{-1}_*(E^j) = ∅`", for the value on `U`:
the strict transform of `E^j` at the end of `BDanFam m inp T hT j U hU` misses `cosupp(I_r, m)`.
The core's clause at the mark `s = tuningParam m` on the tuned triple is carried back to `(𝓘, m)`
by `ord_lt_of_tuned`. -/
theorem BDanFam_cosupp_disjoint :
    Disjoint
      {x | (m : ℕ∞) ≤ ((BDanFam m inp T hT j U hU).toSuccession.weakTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I (Fin.last _)).ord x}
      ((BDanFam m inp T hT j U hU).toSuccession.strictTransformSeq
        ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.hyp j)
        (Fin.last _)) := by
  have hTU := boClass_pullback_inclusion_of_boClass T U hT
  have hge := (BDanFam_isOfOrder inp T hT j U hU).isOfOrderGe
  have hQ := BDan.coreFamOn_cosupp_disjoint (T.tuned m hT.1) (tuningParam m) j inp
    ⟨AnalyticTriple.boClass_tuned hT, AnalyticTriple.isDBalanced_tuned hT⟩ U hU
    (bdClass_tuned_pullback_inclusion T hT U)
  refine Set.disjoint_left.mpr fun x hx hxH => ?_
  have hx' : (tuningParam m : ℕ∞) ≤ ((BDanFam m inp T hT j U hU).toSuccession.weakTransformSeq
      ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).tuned m hTU.1).I
        (Fin.last _)).ord x :=
    not_lt.mp fun hlt => not_lt.mpr hx (AnalyticTriple.ord_lt_of_tuned _ hTU _ hge x hlt)
  rw [AnalyticTriple.tuned_pullback] at hx'
  exact Set.disjoint_left.mp hQ hx' hxH

end Clauses

end Hironaka.Manifold
