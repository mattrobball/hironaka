/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.LocalIsoEquiv
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The marked transform does not depend on the chart witnesses; order `≥ 1` on `cons`

`FiniteSuccession.markedTransformSeq` (`Hironaka/Manifold/FiniteSuccession/Basic.lean`) is defined
through `MarkedIdealSheaf.birationalTransform` at the witnesses `chartAt`/`codim` chosen from
`isMonoidal` (`Classical.choose`), while the one-step descent lemma of
`Hironaka/Resolution/Analytic/MaximalContact/OneStepDescent.lean` produces the marked transform at
the list's model chart `ψ` and the given codimension. This module shows the two agree, because none
of the data of `birationalTransform hY h ⟨J, m⟩` depends on the witnesses:

* `MarkedIdealSheaf.birationalTransform_congr`: the ideal sheaf `I_Y` of a closed submanifold
  depends only on the set `Y` (`IsClosedSubmanifold.idealSheaf_congr`), hence the marked
  transform along one blow-down `π` is the same for any two witnesses `(ψ, c)`, `(ψ', c')` of
  "`Y` is a closed submanifold and `π` is its blowing-up";
* `FiniteSuccession.cons_markedTransformSeq_one`: on `cons ψ hZ C` the first marked transform is
  `birationalTransform hZ (isBlowUp_blowUpπ ψ hZ) ⟨J, m⟩`, the form the one-step lemma yields;
* `isMarkedOne_cons_zero` / `isMarkedOne_cons_tail`: the two clauses of `IsMarkedOne` on
  `cons ψ hZ C` — the first centre lies in `cosupp J`, and the tail is `IsMarkedOne` for the
  first marked transform (the recursion `cons_markedTransformSeq_succ_castSucc`).

These are the bookkeeping steps of Kollár's induction "`X_{i+1} = X'_{i+1}`, the blow-up of the
same centre" [Kol07, Theorem 97, proof], for sequences of order `≥ m` in the sense of
[Kol07, Definition 66].
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n n' : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {ψ' : E ≃L[𝕜] (Fin n' → 𝕜)}

section Unbundled

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y Y' : Set M} {c c' : ℕ}

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-- The marked transform `π_*^{-1}(J, m)` along a blow-down `π` does not depend on the witnesses
`(ψ, c)` of "`Y` is a closed submanifold and `π` its blowing-up": its inputs are the total
transform `π^*J` and the exceptional ideal sheaf `π^*I_Y`, and `I_Y` depends only on the set `Y`
(`idealSheaf_congr`). -/
theorem MarkedIdealSheaf.birationalTransform_congr (hY : IsClosedSubmanifold ψ Y c)
    (hY' : IsClosedSubmanifold ψ' Y' c') (hYY' : Y = Y') (h : IsBlowUp ψ Y c π)
    (h' : IsBlowUp ψ' Y' c' π) (J : MarkedIdealSheaf (structureSheaf 𝕜 E M)) :
    MarkedIdealSheaf.birationalTransform hY h J =
      MarkedIdealSheaf.birationalTransform hY' h' J := by
  subst hYY'
  unfold MarkedIdealSheaf.birationalTransform
  rw [IsClosedSubmanifold.idealSheaf_congr hY hY' rfl]

end Unbundled

end Manifold

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {Z : Set M} {c : ℕ}

/-- On `cons ψ hZ C` the marked transform at stage `1` is `birationalTransform` at the given
witnesses `(ψ, c)` and the blow-down `blowUpπ ψ hZ`: the chosen witnesses of `isMonoidal` give the
same value (`birationalTransform_congr`). -/
theorem cons_markedTransformSeq_one (hZ : IsClosedSubmanifold ψ Z c)
    (C : FiniteSuccession (blowUp ψ hZ)) (J : IdealSheaf M) (m : ℕ) :
    (cons ψ hZ C).markedTransformSeq J m (Fin.succ (0 : Fin (C.length + 1))) =
      (MarkedIdealSheaf.birationalTransform hZ (isBlowUp_blowUpπ ψ hZ) ⟨J, m⟩).I :=
  congrArg MarkedIdealSheaf.I (MarkedIdealSheaf.birationalTransform_congr
    ((cons ψ hZ C).isClosedSubmanifold_center ⟨0, Nat.succ_pos _⟩) hZ hZ.cosupport_idealSheaf
    ((cons ψ hZ C).isBlowUp_map ⟨0, Nat.succ_pos _⟩) (isBlowUp_blowUpπ ψ hZ) ⟨J, m⟩)

/-- Stage `0` of Kollár's "`Z_i^U ⊆ W_i`" [Kol07, Theorem 97, proof]: if `cons ψ hZ C` is of order
`≥ 1` for `(J, 1)`, its first centre `Z` lies in `cosupp J`. -/
theorem isMarkedOne_cons_zero (hZ : IsClosedSubmanifold ψ Z c) (C : FiniteSuccession (blowUp ψ hZ))
    {J : IdealSheaf M} (h : (cons ψ hZ C).IsMarkedOne J) : Z ⊆ J.support := by
  have h0 : hZ.idealSheaf.support ⊆ J.support := h ⟨0, Nat.succ_pos _⟩
  rwa [hZ.cosupport_idealSheaf] at h0

/-- The later stages: if `cons ψ hZ C` is of order `≥ 1` for `(J, 1)`, its tail `C` is of order
`≥ 1` for the first marked transform `(π_*^{-1}(J, 1), 1)` (the recursion of the marked transforms
on the constructor form). -/
theorem isMarkedOne_cons_tail (hZ : IsClosedSubmanifold ψ Z c) (C : FiniteSuccession (blowUp ψ hZ))
    {J : IdealSheaf M} (h : (cons ψ hZ C).IsMarkedOne J) :
    C.IsMarkedOne (MarkedIdealSheaf.birationalTransform hZ (isBlowUp_blowUpπ ψ hZ) ⟨J, 1⟩).I := by
  intro i
  have hi : ((cons ψ hZ C).center i.succ).support ⊆
      ((cons ψ hZ C).markedTransformSeq J 1 (i.succ.castSucc : Fin (C.length + 1 + 1))).support :=
    h i.succ
  rwa [cons_center_succ, cons_markedTransformSeq_succ_castSucc, cons_markedTransformSeq_one] at hi

end AnalyticManifold.FiniteSuccession

end
