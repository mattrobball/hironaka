/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Restrict.Defs
import Hironaka.AnalyticSpace.ClosedSubspaceLemmas
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.RegDensityLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# The simple locus and the underlying map under open immersions

Elementary facts about analytic `K`-spaces used in the comparison of two local resolutions over
a piece (`Hironaka/Resolution/Analytic/Kol07Thm45/LocalResolutionIndependent.lean`,
`Hironaka/Resolution/Analytic/Kol07Thm45/CoproductGluedFamily.lean`,
`Hironaka/AnalyticSpace/Glue/OverReg.lean`,
`Hironaka/Resolution/Analytic/Kol07Thm45/IsoOverLemmas.lean`,
`Hironaka/Resolution/Analytic/Kol07Thm45/RestrictIsoOpen.lean`), where the simple locus of the piece
is read through an open immersion and the restricted local resolutions inherit non-singularity:

* a point is simple iff its image under an open immersion is simple
  (`mem_reg_iff_of_isOpenImmersion` — the stalk maps of an open immersion are isomorphisms of
  local rings, and regularity is invariant under ring isomorphisms; the simple points of
  [Hir64, Ch. 0, §1, p. 121]);
* the underlying map of an open immersion, or of an isomorphism, is injective
  (`injective_toFun_of_isOpenImmersion`, `injective_toFun_of_isIso`) and, for an open immersion,
  open (`isOpenMap_toFun_of_isOpenImmersion`);
* an open subspace of a non-singular space is non-singular (`isNonsingular_restrictSet`, for
  `restrict` at any set, with the convention `openOf` for non-open sets; the open subspaces of
  [Hir64, Ch. 0, §1, p. 120]).

Routine.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AnalyticSpace.KLocallyRingedSpace

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- **A point is simple iff its image under an open immersion is simple**: the stalk map of an
open immersion at `a` is an isomorphism `𝒪_{B, φ a} ≅ 𝒪_{A, a}` (Mathlib's
`LocallyRingedSpace.IsOpenImmersion.stalk_iso`), and a regular local ring is regular under a ring
isomorphism (`IsRegularLocalRing.of_ringEquiv`, both ways). -/
theorem mem_reg_iff_of_isOpenImmersion {A B : AnalyticSpace.{u} K} (φ : A ⟶ B)
    (hφ : LocallyRingedSpace.IsOpenImmersion φ.1) (a : A) :
    a ∈ regularLocus A ↔ Hom.toFun φ a ∈ regularLocus B := by
  have := hφ
  have hiso : IsIso (φ.1.stalkMap a) := LocallyRingedSpace.IsOpenImmersion.stalk_iso φ.1 a
  change IsRegularLocalRing (A.presheaf.stalk a) ↔
    IsRegularLocalRing (B.presheaf.stalk (φ.1.base a))
  constructor
  · intro h
    exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _
      (asIso (φ.1.stalkMap a)).commRingCatIsoToRingEquiv.symm
  · intro h
    exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _
      (asIso (φ.1.stalkMap a)).commRingCatIsoToRingEquiv

/-- The underlying map of an isomorphism of analytic `K`-spaces is injective (an isomorphism is an
open immersion, Mathlib's `LocallyRingedSpace.IsOpenImmersion.of_isIso`). -/
theorem injective_toFun_of_isIso {A B : AnalyticSpace.{u} K} (φ : A ⟶ B) (hφ : IsIso φ) :
    Function.Injective (Hom.toFun φ) := by
  have : IsIso φ.1 := (isIso_iff φ).mp hφ
  exact (inferInstance : LocallyRingedSpace.IsOpenImmersion φ.1).base_open.injective

/-- The underlying map of an open immersion is injective (its base map is an open embedding,
Mathlib's `IsOpenImmersion.base_open`). -/
theorem injective_toFun_of_isOpenImmersion {A B : AnalyticSpace.{u} K} (φ : A ⟶ B)
    (hφ : LocallyRingedSpace.IsOpenImmersion φ.1) : Function.Injective (Hom.toFun φ) :=
  hφ.base_open.injective

/-- **An open subspace of a non-singular analytic `K`-space is non-singular** (`restrict` at any
set, through the convention `openOf`): the stalks of `X | U` are the stalks of `X`
(`isRegularLocalRing_stalk_restrictOpen_iff`). -/
theorem isNonsingular_restrictSet {X : AnalyticSpace.{u} K} (hX : X.IsNonsingular) (S : Set X) :
    (X.restrictSet S).IsNonsingular := by
  rw [isNonsingular_iff] at hX ⊢
  intro x
  exact (isRegularLocalRing_stalk_restrictOpen_iff X.toKLocallyRingedSpace (openOf X S) x).mpr
    (hX x.1)

/-- The underlying map of an open immersion is an open map (its base map is an open embedding,
Mathlib's `IsOpenImmersion.base_open`). -/
theorem isOpenMap_toFun_of_isOpenImmersion {A B : AnalyticSpace.{u} K} (φ : A ⟶ B)
    (hφ : LocallyRingedSpace.IsOpenImmersion φ.1) : IsOpenMap (Hom.toFun φ) :=
  hφ.base_open.isOpenMap

end AnalyticSpace
