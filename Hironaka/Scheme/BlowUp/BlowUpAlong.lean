/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.BlowUpAlong.Defs
public import Hironaka.Scheme.BlowUp.UniversalProperty

/-!
# The Mathlib-only effective Cartier ideal sheaves and blow-ups are the library's

`Scheme.IdealSheafData.IsEffectiveCartier` and `Scheme.Hom.IsBlowUpAlong`
(`Hironaka.Scheme.BlowUp.BlowUpAlong.Defs`), defined from Mathlib's notions alone, are the library's
`Scheme.IdealSheafData.IsInvertible` and `IsBlowUp`:
`Scheme.IdealSheafData.isEffectiveCartier_iff_isInvertible` and
`Scheme.Hom.isBlowUpAlong_iff_isBlowUp`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An effective Cartier ideal sheaf is an invertible one, in the library's sense. -/
theorem Scheme.IdealSheafData.isEffectiveCartier_iff_isInvertible {X : Scheme.{u}}
    (J : X.IdealSheafData) : J.IsEffectiveCartier ↔ J.IsInvertible :=
  Iff.rfl

/-- `π.IsBlowUpAlong I` is the library's `IsBlowUp I π`. -/
theorem Scheme.Hom.isBlowUpAlong_iff_isBlowUp {X B : Scheme.{u}} (π : B ⟶ X)
    (I : X.IdealSheafData) : π.IsBlowUpAlong I ↔ IsBlowUp I π :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.admissible, h.existsUnique_lift⟩⟩

end AlgebraicGeometry
