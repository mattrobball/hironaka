/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Basic
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.Weak
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# The weak transform of the bundled vocabulary

The vocabulary in which the main theorems are stated has its own weak transform
`AnalyticManifold.IdealSheaf.weakTransform f J D`: the colon-stalk definition applied to a
bundled analytic map `f` and an ideal sheaf `D` of the centre. For a blowing-up `f` with centre
the closed submanifold `Y` and `D` the ideal sheaf of `Y` it is the unbundled
`IdealSheaf.weakTransformOf` (an abbreviation of it) once `D` is identified with `hY.idealSheaf`
(`weakTransform_eq`, the
rewrite lemma used for the iterated transforms along a sequence of blowings-up), and it has the
colon stalks whenever `f` is the monoidal transformation with centre `D`
(`isDivExceptional_weakTransform`).
-/

public section

open TopologicalSpace Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {c : ℕ}

/-- For a blowing-up `f` with centre `Y` and `D` the ideal sheaf of `Y`, the bundled
`AnalyticManifold.IdealSheaf.weakTransform f J D` is the unbundled weak transform. -/
theorem weakTransform_eq {N N' : AnalyticManifold.{u} 𝕜 E}
    (f : AnalyticMap N' N) {Y : Set N} (hY : IsClosedSubmanifold ψ Y c)
    {D : AnalyticManifold.IdealSheaf N} (hD : IsIdealSheafOf ψ Y c D) (h : IsBlowUp ψ Y c f)
    (J : AnalyticManifold.IdealSheaf N) :
    AnalyticManifold.IdealSheaf.weakTransform f J D = IdealSheaf.weakTransformOf hY h J := by
  have hDeq := IsIdealSheafOf.eq_idealSheaf hY hD
  subst hDeq
  rfl

/-- When `f` is the monoidal transformation with centre `D`, the bundled weak transform has the
colon stalks `(f⁻¹(J)_{a'} : f⁻¹(D)_{a'}^{ν})`, `ν` the generic order of `J` along the component of
the centre through `f a'`. -/
theorem isDivExceptional_weakTransform {N N' : AnalyticManifold.{u} 𝕜 E}
    (f : AnalyticMap N' N) (D J : AnalyticManifold.IdealSheaf N)
    (hf : AnalyticMap.IsMonoidalTransformation f D) :
    IdealSheaf.IsDivExceptional (IdealSheaf.pullback f f.contMDiff J)
      (IdealSheaf.pullback f f.contMDiff D)
      (fun a' => (IdealSheaf.genericOrdAlong D J (f a')).toNat)
      (AnalyticManifold.IdealSheaf.weakTransform f J D) := by
  obtain ⟨n', ψ', c', hY, hD, h⟩ := hf
  rw [weakTransform_eq f hY hD h J]
  have key : ∀ X : AnalyticManifold.IdealSheaf N, X = hY.idealSheaf →
      IdealSheaf.IsDivExceptional (IdealSheaf.pullback f f.contMDiff J)
        (IdealSheaf.pullback f f.contMDiff X)
        (fun a' => (IdealSheaf.genericOrdAlong X J (f a')).toNat)
        (IdealSheaf.weakTransformOf hY h J) := by
    rintro X rfl
    exact isDivExceptional_weakTransformOf hY h J
  exact key D (IsIdealSheafOf.eq_idealSheaf hY hD)

end Manifold
