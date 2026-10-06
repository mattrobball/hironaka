/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Quotient.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The quotient of a locally ringed space by an ideal sheaf: basic properties

The canonical morphism `ι : quotientSpace X 𝒥 ⟶ X` of the quotient by an ideal sheaf has
surjective stalk maps: through the identification `𝒪_{Z,z} ≅ 𝒪_{X,z}/𝒥_z` they are the quotient
maps `𝒪_{X,z} → 𝒪_{X,z}/𝒥_z` (`stalkMap_surjective`).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u

namespace AnalyticSpace

namespace QuotientSpace

variable (X : LocallyRingedSpace.{u}) (J : IdealSheaf X.𝒪)

/-- The stalk map of the canonical morphism is the quotient map `𝒪_{X,z} → 𝒪_{X,z}/𝒥_z`, hence
surjective. -/
theorem stalkMap_surjective (z : support X J) :
    Function.Surjective ((ιHom X J).stalkMap z).hom := by
  intro ξ
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.mk_surjective ((evalHom X J z).hom ξ)
  refine ⟨σ, evalHom_injective X J z ?_⟩
  change evalHom X J z _ = evalHom X J z ξ
  rw [evalHom_stalkMap]
  exact hσ

end QuotientSpace

end AnalyticSpace
