/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# The nilradical ideal sheaf

The nilradical ideal sheaf `reducedIdeal X` of a scheme `X`, the radical of the zero ideal sheaf,
whose closed subscheme is Hironaka's `red X`, the reduced scheme with the points of `X`
[Hir64, Main Theorem I*].
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The nilradical ideal sheaf of `X`; its subscheme is Hironaka's `red X`
[Hir64, Main Theorem I*]. -/
noncomputable def reducedIdeal (X : Scheme.{u}) : X.IdealSheafData :=
  (⊥ : X.IdealSheafData).radical

end AlgebraicGeometry
