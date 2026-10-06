/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Defs
public import Hironaka.Manifold.BlowUp.Transform.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
/-!
# Analytic blow-up sequences: witnesses and marked transforms

A blow-up sequence of length `r` starting with `X` is a chain of morphisms
`Π : X_r → X_{r−1} → ⋯ → X_1 → X_0 = X` in which each `π_i : X_{i+1} → X_i` is a blow-up with
centre `Z_i ⊂ X_i` and exceptional divisor `F_{i+1} ⊂ X_{i+1}`; trivial and empty blow-ups are
allowed [Kol07, Definition 29]. On analytic manifolds, with closed submanifolds as centres, this
notion is `AnalyticManifold.FiniteSuccession M`, the finite sequence of monoidal
transformations in which the analytic main theorems are stated [Wlo09, Theorem 2.0.3]; this
module adds no second notion of a sequence but equips that structure with the data Kollár's
definition reads off a sequence (his constructors `FiniteSuccession.nil` and
`FiniteSuccession.cons` are in `Hironaka/Manifold/FiniteSuccession/Cons.lean`). It provides:

* the last witness of `isMonoidal i`: besides the chosen chart data `dimAt`, `chartAt`, `codim`,
  the closed submanifold `Z_i` (`isClosedSubmanifold_center`) and the blowing-up
  (`isBlowUp_map`), the centre `C_i` is the ideal sheaf of `Z_i` (`isIdealSheafOf_center`), so
  that every step of an arbitrary sequence is a blow-up with centre `Z_i`;
* trivial and empty blow-ups [Kol07, Warning 20]: `IsEmptyAt` (`Z_i = ∅`, the unit ideal sheaf),
  `IsTrivialAt` (`Z_i` a closed submanifold of codimension one, a Cartier divisor),
  `NoEmptyCenters` (the empty blow-up convention [Kol07, 32]), and the exceptional divisor
  `exceptionalAt S i = π_i⁻¹(Z_i)`;
* the marked transforms `(X_{i+1}, I_{i+1}, m) := (B_{Z_i} X_i, (π_i)^{-1}_*(I_i, m))` along the
  sequence [Kol07, Definition 66 (1′)], by recursion on the sequence through
  `MarkedIdealSheaf.birationalTransform` at the witnesses of `isMonoidal i`
  (`markedTransformSeq`). The iterated birational transform is defined along the sequence, never
  as a function of the composite alone, as Kollár warns after his Definition 48. The recursions
  `weakTransformSeq` and `boundarySeq` (the weak transforms and the accumulated exceptional
  divisors) are those of `FiniteSuccession` itself.

The marked transforms are the ideals whose orders the order-reduction and resolution algorithms
control.
-/

@[expose] public section

noncomputable section

open TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff Topology

universe u

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜))

variable {M : AnalyticManifold.{u} 𝕜 E}

/-! ### The witnesses of `isMonoidal`: the centre is the ideal sheaf of a closed submanifold -/

section Witnesses

variable (S : FiniteSuccession M) (i : Fin S.length)

/-- The centre `C_i` is the ideal sheaf of the closed submanifold `Z_i`. -/
theorem isIdealSheafOf_center :
    IsIdealSheafOf (S.chartAt i) (S.center i).support (S.codim i) (S.center i) :=
  (S.isMonoidal i).choose_spec.choose_spec.choose_spec.2.1

end Witnesses

/-! ### Trivial and empty blow-ups, the exceptional divisor -/

/-- The `i`-th blow-up is **empty** if its centre is empty, i.e. the unit ideal sheaf
[Kol07, Warning 20]. -/
def IsEmptyAt (S : FiniteSuccession M) (i : Fin S.length) : Prop := S.center i = ⊤

/-- The `i`-th blow-up is **trivial** if its centre is a Cartier divisor [Kol07, Warning 20]: on a
manifold, a closed submanifold of codimension one, with its ideal sheaf as the centre. -/
def IsTrivialAt (S : FiniteSuccession M) (i : Fin S.length) : Prop :=
  ∃ (n : ℕ) (ψ : E ≃L[𝕜] (Fin n → 𝕜)), IsClosedSubmanifold ψ (S.center i).support 1 ∧
    IsIdealSheafOf ψ (S.center i).support 1 (S.center i)

/-- No blow-up of the sequence is empty (the empty blow-up convention [Kol07, 32]). -/
def NoEmptyCenters (S : FiniteSuccession M) : Prop := ∀ i, ¬ S.IsEmptyAt i

/-- The exceptional divisor `F_{i+1} = π_i⁻¹(Z_i) ⊂ X_{i+1}` of the `i`-th blow-up
[Kol07, Definition 29], as a subset of the stage `X_{i+1}`. -/
def exceptionalAt (S : FiniteSuccession M) (i : Fin S.length) : Set (S.stage i.succ) :=
  S.map i ⁻¹' (S.center i).support

/-! ### The marked transforms along the sequence -/

section Marked

variable (S : FiniteSuccession M)

/-- The `i`-th marked transform `(π_{i-1})^{-1}_* ⋯ (π_0)^{-1}_*(J, m)` on the stage `X_i`, by
recursion on `i` [Kol07, Definition 66 (1′)]: each step is `MarkedIdealSheaf.birationalTransform`
at the witnesses chosen from `isMonoidal`. -/
def markedTransformSeqAux (J : IdealSheaf M) (m : ℕ) :
    ∀ (i : ℕ) (h : i < S.length + 1), IdealSheaf (finStages M S.later ⟨i, h⟩)
  | 0, _ => J
  | i + 1, h =>
    (MarkedIdealSheaf.birationalTransform
      (S.isClosedSubmanifold_center ⟨i, Nat.lt_of_succ_lt_succ h⟩)
      (S.isBlowUp_map ⟨i, Nat.lt_of_succ_lt_succ h⟩)
      ⟨markedTransformSeqAux J m i (Nat.lt_of_succ_lt h), m⟩).I

/-- **The marked transforms `(I_i, m)` along the sequence** [Kol07, Definition 66 (1′)]:
`I_0 = J` and `I_{i+1} = (π_i)^{-1}_*(I_i, m)`, defined recursively along the sequence and never
as a function of the composite alone (the caution Kollár attaches to his Definition 48). -/
def markedTransformSeq (J : IdealSheaf M) (m : ℕ) (i : Fin (S.length + 1)) :
    IdealSheaf (S.stage i) :=
  S.markedTransformSeqAux J m i.1 i.2

end Marked

end AnalyticManifold.FiniteSuccession

end
