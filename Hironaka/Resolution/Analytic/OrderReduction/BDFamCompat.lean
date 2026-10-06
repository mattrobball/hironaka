/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BDFam
import Hironaka.Manifold.FiniteSuccession.Functor.LiftedFibre
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BDFamOrder
import Hironaka.Resolution.Analytic.OrderReduction.BDFamPullback
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Lemma 102 in the compatible-family form: compatibility under restriction

The values of `BD_{n,m,j}` on the relatively compact open subsets (`BDanFam`, `BDFam.lean`) form a
compatible family: for `U ≤ V` the value on `U` is the pull-back of the value on `V` along the open
inclusion with its empty blow-ups deleted (`BDanFam_compat`; the compatibility clause of
[Wlo09, Theorem 2.0.3 (4)] with [Wlo09, Definition 3.2.6], and the second clause of
[Kol07, 34.1] for the open embedding `U ⊆ V`). Both sides are cores over transported values
(`coreFamOn_eq_coreOfListOf`, `coreOfListOf_pullback_eraseEmpty`): the centres and the transforms
agree as sets, because the lift of `U ⊆ V ⊆ M` to the blowings-up is the composite of the lifts
(uniqueness of lifts, `eq_of_comm_blowUp`), and the transported values are the input family's
values at the traces `U_S ≤ V_S`, identified by the family's own compatibility and the behaviour
of the core over a sequence under pull-back (`BDFamPullback.lean`).

* `piOpen_mono`, `preimageOpens_piOpen_mono` — `π_{-1}^{-1}` and the trace on `S_0` are monotone;
* `liftStep_inclusion_eq_comp`, `transformSU_pullback_eq` — the lifts compose, and the transform of
  `E^j` pulls back to the transform of the restricted data;
* `coreFamOn_compat`, `BDanFam_compat` — the compatibility for the core on an open and for the value
  of `BD_{n,m,j}`.

This is the `compat` field of the compatible family `bdanFam` in `BOanFamOfInput.lean`.
-/

public section

universe u

open Set Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace BDan

open _root_.Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ)
  (j : T.F.ι) {U V : Opens M}

/-- `π_{-1}^{-1}` is monotone on open sets. -/
theorem piOpen_mono (hUV : U ≤ V) : piOpen T s j U ≤ piOpen T s j V := fun _ hq => hUV hq

/-- The trace on `S_0` of `π_{-1}^{-1}` is monotone on open sets. -/
theorem preimageOpens_piOpen_mono (hUV : U ≤ V) :
    (isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j U) ≤
      (isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j V) :=
  fun _ hp => piOpen_mono T s j hUV hp

/-- The lift of the inclusion `U ⊆ M` to the blowings-up is the lift of `V ⊆ M` after the lift of
`U ⊆ V` (uniqueness of lifts, `eq_of_comm_blowUp`). -/
theorem liftStep_inclusion_eq_comp (hUV : U ≤ V) :
    ⇑(AnalyticManifold.BlowUpSequence.liftStep (M.inclusion U) (isLocalDiffeomorph_inclusion M U)
        (BD.isClosedSubmanifold_Zminus1 T s j)) =
      ⇑(AnalyticManifold.BlowUpSequence.liftStep (M.inclusion V) (isLocalDiffeomorph_inclusion M V)
          (BD.isClosedSubmanifold_Zminus1 T s j)) ∘
        ⇑(AnalyticManifold.BlowUpSequence.liftStep (M.restrictLE hUV)
            (isLocalDiffeomorph_restrictLE hUV)
          ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
            (isLocalDiffeomorph_inclusion M V))) :=
  eq_of_comm_blowUp (BD.isClosedSubmanifold_Zminus1 T s j)
    ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
      (isLocalDiffeomorph_inclusion M U)) rfl
    (AnalyticManifold.BlowUpSequence.liftStep _ _ _).contMDiff.continuous
    ((AnalyticManifold.BlowUpSequence.liftStep _ _ _).contMDiff.continuous.comp
      (AnalyticManifold.BlowUpSequence.liftStep _ _ _).contMDiff.continuous)
    (fun u => AnalyticManifold.BlowUpSequence.blowUpπ_liftStep _ _ _ u)
    (fun u => by
      change Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)
        (AnalyticManifold.BlowUpSequence.liftStep (M.inclusion V) (isLocalDiffeomorph_inclusion M V)
          (BD.isClosedSubmanifold_Zminus1 T s j)
          (AnalyticManifold.BlowUpSequence.liftStep (M.restrictLE hUV)
              (isLocalDiffeomorph_restrictLE hUV)
            ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
              (isLocalDiffeomorph_inclusion M V)) u)) =
        (Manifold.blowUpπ ψ₀ ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
          (isLocalDiffeomorph_inclusion M U)) u).1
      rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep]
      exact congrArg (M.inclusion V) (AnalyticManifold.BlowUpSequence.blowUpπ_liftStep
          (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)
        ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
          (isLocalDiffeomorph_inclusion M V)) u))

/-- The transform of `E^j` pulled back along the lift of `U ⊆ V` is the transform of the data
restricted to `U`. -/
theorem transformSU_pullback_eq (hUV : U ≤ V) :
    ⇑(AnalyticManifold.BlowUpSequence.liftStep (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)
        ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
          (isLocalDiffeomorph_inclusion M V))) ⁻¹'
        (⇑(liftIncl T s j V) ⁻¹'
          (⇑((Manifold.blowUp ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)).inclusion
              (piOpen T s j V)) ⁻¹'
            transformS T s j)) =
      ⇑(Manifold.blowUpπ ψ₀ (((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
          (isLocalDiffeomorph_inclusion M V)).preimage_of_isLocalDiffeomorph
            (isLocalDiffeomorph_restrictLE hUV))) ⁻¹'
        (⇑(M.inclusion U) ⁻¹' T.F.hyp j) := by
  ext q
  change Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)
      (AnalyticManifold.BlowUpSequence.liftStep (M.inclusion V) (isLocalDiffeomorph_inclusion M V)
        (BD.isClosedSubmanifold_Zminus1 T s j)
        (AnalyticManifold.BlowUpSequence.liftStep (M.restrictLE hUV)
            (isLocalDiffeomorph_restrictLE hUV)
          ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
            (isLocalDiffeomorph_inclusion M V)) q)) ∈ T.F.hyp j ↔
    (Manifold.blowUpπ ψ₀ (((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
      (isLocalDiffeomorph_inclusion M V)).preimage_of_isLocalDiffeomorph
        (isLocalDiffeomorph_restrictLE hUV)) q).1 ∈ T.F.hyp j
  rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep,
      AnalyticManifold.BlowUpSequence.blowUpπ_liftStep]
  exact Iff.rfl

variable (hUV : U ≤ V) (inp : BMOanFam 𝕜 (n - 1) s) (hT : BDClass s T)
  (hU : IsCompact (closure (U : Set M))) (hV : IsCompact (closure (V : Set M)))

/-- The core on an open is compatible under restriction: for `U ≤ V` the core on `U` is the
pull-back of the core on `V` along the open inclusion with its empty blow-ups deleted (the second
clause of [Kol07, 34.1]; [Wlo09, Theorem 2.0.3 (4)]). Both cores are cores over transported values
on the same centre and transform; the transported values agree because the input family is
compatible at the traces `U_S ≤ V_S` and the lift of `U ⊆ M` is the lift of `V ⊆ M` after the lift
of `U ⊆ V`. -/
theorem coreFamOn_compat :
    coreFamOn T s j inp hT U hU =
      ((coreFamOn T s j inp hT V hV).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  rw [coreFamOn_eq_coreOfListOf T s j inp hT V hV, coreOfListOf_pullback_eraseEmpty,
    coreFamOn_eq_coreOfListOf T s j inp hT U hU]
  -- the input family's compatibility at the traces `U_S ≤ V_S`
  have hfam := (inp.functor.fam (restrictedTriple T s j hT)
    (bmoClass_restrictedTriple T s j hT)).compat
    ((isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j U))
    ((isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j V))
    ((isClosedSubmanifold_transformS T s j).isCompact_closure_preimageOpens _
      (isCompact_closure_piOpenOf _ U hU))
    ((isClosedSubmanifold_transformS T s j).isCompact_closure_preimageOpens _
      (isCompact_closure_piOpenOf _ V hV))
    (preimageOpens_piOpen_mono T s j hUV)
  -- the transported values, with the restricted lifts' local-isomorphism proofs stated at the
  -- maps as named (so that the rewrites below match them)
  have hl : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (liftInclS T s j U) :=
    IsClosedSubmanifold.isLocalDiffeomorph_restrictMap (liftIncl T s j U)
      (isLocalDiffeomorph_liftInclOf _ U) _
  have hlV : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (liftInclS T s j V) :=
    IsClosedSubmanifold.isLocalDiffeomorph_restrictMap (liftIncl T s j V)
      (isLocalDiffeomorph_liftInclOf _ V) _
  have hU' : transportedValue T s j inp hT U hU =
      ((((inp.functor.fam (restrictedTriple T s j hT) (bmoClass_restrictedTriple T s j hT)).seqOn
            ((isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j V))
            ((isClosedSubmanifold_transformS T s j).isCompact_closure_preimageOpens _
              (isCompact_closure_piOpenOf _ V hV))).pullback
          ((isClosedSubmanifold_transformS T s j).toAnalyticManifold.restrictLE
            (preimageOpens_piOpen_mono T s j hUV))
          (isLocalDiffeomorph_restrictLE _)).eraseEmpty.pullback (bundleInv T s j U)
        (isLocalDiffeomorph_bundleInv T s j U)).pullback (liftInclS T s j U) hl := by
    unfold transportedValue transportedValueOf
    exact congrArg
      (fun L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
          ((isClosedSubmanifold_transformS T s j).toAnalyticManifold.restrict
            ((isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j U))) =>
        (L.pullback (bundleInv T s j U) (isLocalDiffeomorph_bundleInv T s j U)).pullback
          (liftInclS T s j U) hl) hfam
  have hV' : transportedValue T s j inp hT V hV =
      (((inp.functor.fam (restrictedTriple T s j hT) (bmoClass_restrictedTriple T s j hT)).seqOn
            ((isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j V))
            ((isClosedSubmanifold_transformS T s j).isCompact_closure_preimageOpens _
              (isCompact_closure_piOpenOf _ V hV))).pullback (bundleInv T s j V)
        (isLocalDiffeomorph_bundleInv T s j V)).pullback (liftInclS T s j V) hlV := rfl
  rw [hU', hV', coreOfListOf_pullback_pullback_eraseEmpty]
  -- both transported lists as one pull-back of the input value on the trace `V_S`
  have hab₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (((isClosedSubmanifold_transformS T s j).toAnalyticManifold.restrictLE
        (preimageOpens_piOpen_mono T s j hUV)).comp (bundleInv T s j U)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE _)
      (isLocalDiffeomorph_bundleInv T s j U)
  have habc₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      ((((isClosedSubmanifold_transformS T s j).toAnalyticManifold.restrictLE
        (preimageOpens_piOpen_mono T s j hUV)).comp (bundleInv T s j U)).comp
          (liftInclS T s j U)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hab₁
      (IsClosedSubmanifold.isLocalDiffeomorph_restrictMap (liftIncl T s j U)
        (isLocalDiffeomorph_liftInclOf _ U) _)
  have hab₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      ((bundleInv T s j V).comp (liftInclS T s j V)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_bundleInv T s j V)
      (IsClosedSubmanifold.isLocalDiffeomorph_restrictMap (liftIncl T s j V)
        (isLocalDiffeomorph_liftInclOf _ V) _)
  have habc₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (((bundleInv T s j V).comp (liftInclS T s j V)).comp
        (((isClosedSubmanifold_transformSU T s j V).preimage_of_isLocalDiffeomorph
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep (M.restrictLE hUV)
            (isLocalDiffeomorph_restrictLE hUV)
            ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
              (isLocalDiffeomorph_inclusion M V)))).restrictMap
          (isClosedSubmanifold_transformSU T s j V)
          (AnalyticManifold.BlowUpSequence.liftStep (M.restrictLE hUV)
              (isLocalDiffeomorph_restrictLE hUV)
            ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
              (isLocalDiffeomorph_inclusion M V)))
          (AnalyticManifold.BlowUpSequence.liftStep (M.restrictLE hUV)
              (isLocalDiffeomorph_restrictLE hUV)
            ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
              (isLocalDiffeomorph_inclusion M V))).contMDiff fun _ hx => hx)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hab₂
      (IsClosedSubmanifold.isLocalDiffeomorph_restrictMap _
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep _ _ _) _)
  rw [AnalyticManifold.BlowUpSequence.pullback_comp, AnalyticManifold.BlowUpSequence.pullback_comp,
    AnalyticManifold.BlowUpSequence.pullback_comp, AnalyticManifold.BlowUpSequence.pullback_comp]
  -- the two cores: the same centre and the same transform of `Eʲ` as sets (`transformSU_eq`,
  -- `transformSU_pullback_eq`), and transported lists agreeing pointwise because the lift of
  -- `U ⊆ M` is the lift of `V ⊆ M` after the lift of `U ⊆ V`
  refine coreOfListOf_congr _ _ _ _ rfl rfl (transformSU_eq T s j U)
    (transformSU_pullback_eq T s j hUV) _ _ ?_
  exact heq_pullback_of_heq_bundled
    ((transformSU_eq T s j U).trans (transformSU_pullback_eq T s j hUV).symm) _ _ _ _ _
    habc₁ habc₂ fun x _ _ =>
      Subtype.ext (Subtype.ext (congrFun (liftStep_inclusion_eq_comp T s j hUV) x))

end BDan

section Assembly

variable {M : AnalyticManifold.{u} 𝕜 E} {m : ℕ}

/-- The values of `BD_{n,m,j}` on the relatively compact open subsets are compatible under
restriction ([Wlo09, Theorem 2.0.3 (4)]; the second clause of [Kol07, 34.1]): for `U ≤ V` the value
on `U` is the pull-back of the value on `V` along the open inclusion with its empty blow-ups
deleted. This is `coreFamOn_compat` at the tuned triple. -/
theorem BDanFam_compat (inp : BMOanFam 𝕜 (n - 1) (tuningParam m)) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass m T) (j : T.F.ι) {U V : Opens M}
    (hU : IsCompact (closure (U : Set M))) (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V) :
    BDanFam m inp T hT j U hU =
      ((BDanFam m inp T hT j V hV).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  unfold BDanFam
  exact BDan.coreFamOn_compat (T.tuned m hT.1) (tuningParam m) j hUV inp _ hU hV

end Assembly

end Hironaka.Manifold
