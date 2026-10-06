/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.Family
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bMeasure
import Hironaka.Resolution.Analytic.OrderReduction.BDErase
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Finiteness
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bCommute
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial phase as a compatible family

The monomial phase at the mark `1` ([Wlo09, Theorem 7.4.1]) in the family form of the library
([Wlo09, Theorem 2.0.3 (4)], [Wlo09, Definition 3.2.6]; [Kol07, 34.1]): on every relatively compact
open `U` of `M` the value is the **complete** monomial phase of the restricted triple `T|U`, the
fuel being the measure `Σ_D a_D` of `T|U` (`Step2bMeasure.lean`), finite because the order of `𝓘` is
bounded on the compact closure of `U` (`exists_boClass_pullback_inclusion`); and the compatibility
along `U ≤ V` is the commutation theorem `step2bPhase_pullback_eraseEmpty` of `Step2bCommute.lean`
along the open inclusion, the restriction of the restriction being the restriction
(`pullback_inclusion_restrictLE`).

The family has no empty centre (`noEmptyCenters_step2bPhase`) and its value on every open is of
order `≥ 1` for the restricted `(𝓘, 1)` (`step2bFam_isOfOrderGe`, from `isOfOrderGe_step2bPhase`).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BD

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Congruence for equal triples -/

section Congr

variable {M : AnalyticManifold.{u} 𝕜 E}

/-- The phase of equal triples (on the same manifold) is the same list. -/
theorem step2bPhase_congr (k : ℕ) {T₁ T₂ : AnalyticTriple ψ₀ M} (e : T₁ = T₂)
    (h₁ : AnalyticTriple.BMOClass 1 T₁) (h₂ : AnalyticTriple.BMOClass 1 T₂) :
    step2bPhase k T₁ h₁ = step2bPhase k T₂ h₂ := by
  subst e
  rfl

omit [FiniteDimensional 𝕜 E] in
/-- The measure of equal triples is the same. -/
theorem step2bMeasure_congr {T₁ T₂ : AnalyticTriple ψ₀ M} (e : T₁ = T₂)
    (h₁ : AnalyticTriple.BMOClass 1 T₁) (h₂ : AnalyticTriple.BMOClass 1 T₂) :
    step2bMeasure T₁ h₁ = step2bMeasure T₂ h₂ := by
  subst e
  rfl

end Congr

/-! ### The restricted triple: its class and its finite measure -/

section Restrict

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BMOClass 1 T)

omit [FiniteDimensional 𝕜 E] in
include hT in
/-- The restriction of a triple of the class to an open is in the class
(`bmoClass_pullback_inclusion_of_bmoClass`). -/
theorem bmoClass_restrict (U : Opens M) :
    AnalyticTriple.BMOClass 1 (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) :=
  bmoClass_pullback_inclusion_of_bmoClass T U hT

/-- The measure of the restriction to a relatively compact open is finite: the order of `𝓘` is
bounded on the compact closure, so the restricted triple lies in some `BO_{n,m}` and
`step2bMeasure_ne_top` applies. -/
theorem step2bMeasure_restrict_ne_top (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    step2bMeasure (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
      (bmoClass_restrict T hT U) ≠ ⊤ := by
  obtain ⟨m, hm⟩ := exists_boClass_pullback_inclusion T U hU
  exact step2bMeasure_ne_top _ _ hm.2.1

/-- The fuel of the phase on an open: the measure of the restriction (finite on a relatively
compact open, `step2bMeasure_restrict_ne_top`). -/
def famFuel (U : Opens M) : ℕ :=
  (step2bMeasure (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
    (bmoClass_restrict T hT U)).toNat

/-- On a relatively compact open the fuel is at least the measure, so the phase is complete. -/
theorem step2bMeasure_restrict_le_famFuel (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    step2bMeasure (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
      (bmoClass_restrict T hT U) ≤ (famFuel T hT U : ℕ∞) :=
  (ENat.natCast_toNat (step2bMeasure_restrict_ne_top T hT U hU)).symm.le

end Restrict

/-! ### The family -/

section Family

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BMOClass 1 T)

/-- **The monomial phase as a compatible family** ([Wlo09, Theorem 7.4.1] at `µ = 1`, in the family
form of [Wlo09, Theorem 2.0.3 (4)] and [Wlo09, Definition 3.2.6]; the second condition of
[Kol07, 34.1]): on every relatively compact open the complete phase of the restricted triple,
compatible along open inclusions by the commutation theorem. -/
def step2bFam : CompatibleFamily T where
  seqOn U _ := step2bPhase (famFuel T hT U)
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) (bmoClass_restrict T hT U)
  noEmptyCenters U _ := noEmptyCenters_step2bPhase _ _ _
  compat U V hU hV hUV := by
    have e := AnalyticTriple.pullback_inclusion_restrictLE T hUV
    have hT₂ := AnalyticTriple.bmoClass_pullback (bmoClass_restrict T hT V)
      (M.restrictLE hUV) (isLocalDiffeomorph_restrictLE hUV)
    refine (step2bPhase_congr (famFuel T hT U) e.symm (bmoClass_restrict T hT U) hT₂).trans ?_
    refine step2bPhase_pullback_eraseEmpty (famFuel T hT V) _ (bmoClass_restrict T hT V)
      (M.restrictLE hUV) (isLocalDiffeomorph_restrictLE hUV) hT₂
      (step2bMeasure_restrict_le_famFuel T hT V hV) (famFuel T hT U) ?_
    rw [step2bMeasure_congr e hT₂ (bmoClass_restrict T hT U)]
    exact step2bMeasure_restrict_le_famFuel T hT U hU

/-- The family's value on an open is the complete phase of the restricted triple. -/
theorem step2bFam_seqOn (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (step2bFam T hT).seqOn U hU = step2bPhase (famFuel T hT U)
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) (bmoClass_restrict T hT U) :=
  rfl

/-- The order clause at the mark `1` for the monomial phase: the value on every open is of order
`≥ 1` for the restricted `(𝓘, 1)` (`isOfOrderGe_step2bPhase`). -/
theorem step2bFam_isOfOrderGe (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((step2bFam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf
        (𝕜 := 𝕜) (E := E)) :=
  isOfOrderGe_step2bPhase _ _ _

end Family

end Hironaka.Manifold.BMOmod

end
