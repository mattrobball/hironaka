/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.ClosedSubspace
public import Hironaka.AnalyticSpace.Restrict.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
/-!
# The open inclusion of a restriction, and inverse images along morphisms of `An/K`

* `AnalyticSpace.restrictInclusion X S : X.restrictSet S ⟶ X`, the open inclusion
  `ofRestrict X (openOf X S)` of the open subspace `X | S` (for a non-open `S`, `X.restrictSet S`
  is `X` restricted along `⊤`). The traces of the exceptional
  members of a local resolution on the part over an overlap are written with it.
* `ClosedSubspace.comap_comp_hom`, `ClosedSubspace.comap_id_hom`: the inverse image `D.comap f` of a
  closed subspace [Hir64, Ch. 0, §5, pp. 141–142] is functorial along morphisms of `An/K` —
  `QuotientSpace.comap_comp` (`Hironaka/AnalyticSpace/QuotientMap.lean`) read on these morphisms.

Used by `RunFamilyRestrict.lean`, `ExceptionalTransitionRestrict.lean`,
`HomOfPullbackEqCalculus.lean` and `Glue/OverFamilyPartner.lean` (all in this directory).
-/

@[expose] public section

open CategoryTheory AnalyticSpace KLocallyRingedSpace

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- **The open inclusion `X | S → X`** of the open subspace `X.restrictSet S`: the open immersion
`ofRestrict X (openOf X S)`; for a non-open `S` it is `ofRestrict X ⊤ : X | ⊤ → X`. Compare the
restriction of an analytic space to an open subset in [Hir64, Ch. 0, §1, p. 120]. The traces
`comap (restrictInclusion Ỹ (Π ⁻¹' N)) (𝓔 j)` of the exceptional members on the part over an
overlap `N` are written with it. -/
noncomputable def restrictInclusion (X : AnalyticSpace.{u} K) (S : Set X) :
    X.restrictSet S ⟶ X :=
  ofRestrict X.toKLocallyRingedSpace (openOf X S)

namespace ClosedSubspace

open Manifold.IdealSheaf

/-- The inverse image along a composite is the composite of the inverse images
([Hir64, Ch. 0, §5, pp. 141–142]; `QuotientSpace.comap_comp` at the composite `f ≫ g`). -/
theorem comap_comp_hom {X Y Z : AnalyticSpace.{u} K} (g : Y ⟶ Z)
    (f : X ⟶ Y) (D : ClosedSubspace Z) :
    D.comap (f ≫ g) = (D.comap g).comap f := by
  exact QuotientSpace.comap_comp g.1 D f.1

/-- The inverse image along the identity is the subspace itself. -/
theorem comap_id_hom {X : AnalyticSpace.{u} K} (D : ClosedSubspace X) :
    D.comap (𝟙 X) = D := by
  apply Manifold.IdealSheaf.ext
  intro x
  refine (QuotientSpace.stalkIdeal_comap (𝟙 X : X ⟶ X).1 D x).trans ?_
  rw [show (𝟙 X : X ⟶ X).1 = 𝟙 _ from rfl,
    AlgebraicGeometry.LocallyRingedSpace.stalkMap_id]
  exact Ideal.map_id _

end ClosedSubspace

end AnalyticSpace
