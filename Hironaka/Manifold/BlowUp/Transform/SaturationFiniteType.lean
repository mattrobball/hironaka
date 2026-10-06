/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Defs
import Hironaka.AnalyticSpace.Manifold.Defs
import Hironaka.AnalyticSpace.Noether.Saturation
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The saturation defining the strict transform is of finite type

For a blowing-up `π : M' → M` with centre `Y` and exceptional ideal `I_F`, and an ideal sheaf of
finite type `I` on `M`, the saturation `⋃_k (π⁻¹(I)_{a'} : I_{F,a'}^k)` (`saturationStalk`) is
the stalk family of an ideal sheaf of finite type, over `ℝ` as over `ℂ`
(`saturationStalk_hasLocalGenerators`): this is Bierstone–Milman's "`I_{X'}` is an ideal of
finite type since `X` is locally Noetherian" [BM97, Proposition 3.13], obtained here from the
finite type of saturations on analytic spaces (`AnalyticSpace.saturation_hasLocalGenerators`
of `Hironaka.AnalyticSpace.Noether.Saturation`) read on the analytic space of the blown-up manifold.
It is the hypothesis under which the strict transform `strictTransformSubspace` has the
saturation as its stalks, supplied at each step of a sequence of blowings-up.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {K : Type} [RCLike K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {n : ℕ}
  {ψ : E ≃L[K] (Fin n → K)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(K, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-- The saturation stalks `saturationStalk hY h I` of the total transform of `I` by the powers of
the exceptional ideal of the blowing-up `π` have local generators, over every `RCLike K`: the
ideal-theoretic strict transform is of finite type [BM97, Proposition 3.13]. This is
`AnalyticSpace.saturation_hasLocalGenerators` at the analytic space of `M'`. -/
theorem saturationStalk_hasLocalGenerators (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    (I : IdealSheaf (structureSheaf K E M)) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf K E M') (saturationStalk hY h I) :=
  AnalyticSpace.saturation_hasLocalGenerators
    (AnalyticSpace.toSpace ψ (⟨M'⟩ : AnalyticManifold.{u} K E))
    (I.pullback π h.contMDiff) (hY.idealSheaf.pullback π h.contMDiff)

end Manifold

end
