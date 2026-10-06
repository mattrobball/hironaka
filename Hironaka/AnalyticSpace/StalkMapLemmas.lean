/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Complexification
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Stalk maps of `K`-isomorphisms, open immersions and restricted morphisms

General lemmas on the stalk maps of morphisms of `K`-local-ringed spaces: the stalk maps of a
`K`-isomorphism are bijective; those of the open immersion `X | U ⟶ X` are bijective
(`KLocallyRingedSpace.isIso_ofRestrict_stalkMap`); and those of the restricted morphism
`g | U : A | U ⟶ B | U'` (`Hom.restrictTo`) are isomorphisms, respectively bijective, at the
points where those of `g` are. They serve the restriction of a complexification to an open
subspace and the gluing of local complexifications (`Hironaka/AnalyticSpace/Glue/Restrict.lean`,
`Hironaka/AnalyticSpace/Glue/Trivial.lean`) and the local isomorphism theory
(`Hironaka/AnalyticSpace/LocalIso.lean`, `Hironaka/AnalyticSpace/IsoOverOpen.lean`).

**Conventions.** Bijectivity is stated for the underlying ring homomorphism `(stalkMap a).hom`
(the form of `Complexification.bijective_stalkMap`); isomorphy in the category of commutative
rings is the equivalent `IsIso` (Mathlib's `ConcreteCategory.isIso_iff_bijective`). The stalk map
of `g | U` is conjugate to that of `g` by the stalk isomorphisms of the two open immersions,
through `Hom.restrictTo_comp_ofRestrict`. For `U = ⊤` the open immersion is an isomorphism and
the lemmas reduce to the statement for `g`. Routine; not in the sources.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Topology
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace

universe u

/-- Bijectivity of a composite of ring-category morphisms from that of the factors. -/
theorem bijective_hom_comp {R S T : CommRingCat.{u}} {φ : R ⟶ S} {ψ : S ⟶ T}
    (hφ : Function.Bijective φ.hom) (hψ : Function.Bijective ψ.hom) :
    Function.Bijective (φ ≫ ψ).hom := by
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact hψ.comp hφ

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The stalk maps of a `K`-isomorphism are bijective. -/
theorem KIso.bijective_stalkMap {A B : KLocallyRingedSpace.{u} K} (e : KIso A B) (a : A) :
    Function.Bijective (e.hom.1.stalkMap a).hom := by
  have h₁ : IsIso (LocallyRingedSpace.forgetToSheafedSpace.map e.hom.1) := inferInstance
  have h₂ : IsIso (SheafedSpace.forgetToPresheafedSpace.map
      (LocallyRingedSpace.forgetToSheafedSpace.map e.hom.1)) := inferInstance
  have h₃ : IsIso e.hom.1.toShHom.hom := h₂
  have h₄ : IsIso (e.hom.1.stalkMap a) := inferInstanceAs (IsIso (e.hom.1.toShHom.hom.stalkMap a))
  exact (ConcreteCategory.isIso_iff_bijective _).mp h₄

/-- The stalk maps of the open immersion `X | U ⟶ X` are bijective. -/
theorem bijective_stalkMap_ofRestrict (X : KLocallyRingedSpace.{u} K) (U : Opens X)
    (x : X.restrictOpen U) : Function.Bijective ((ofRestrict X U).1.stalkMap x).hom :=
  (ConcreteCategory.isIso_iff_bijective _).mp (KLocallyRingedSpace.isIso_ofRestrict_stalkMap X U x)

/-- The stalk maps of `g | U : A | U ⟶ B | U'` are isomorphisms where those of `g` are. -/
theorem isIso_stalkMap_restrictTo {A B : KLocallyRingedSpace.{u} K} (g : A ⟶ B) (U : Opens A)
    (U' : Opens B) (h : ∀ a ∈ U, Hom.toFun g a ∈ U') (a : A.restrictOpen U)
    (hg : IsIso (g.1.stalkMap ((ofRestrict A U).1.base a))) :
    IsIso ((Hom.restrictTo g U U' h).1.stalkMap a) := by
  have key : ∀ {φ ψ : A.restrictOpen U ⟶ B}, φ = ψ →
      IsIso (ψ.1.stalkMap a) → IsIso (φ.1.stalkMap a) := by
    rintro φ ψ rfl hψ
    exact hψ
  have h₂ : IsIso ((ofRestrict A U ≫ g).1.stalkMap a) := by
    rw [Hom.comp_val, LocallyRingedSpace.stalkMap_comp]
    exact IsIso.comp_isIso' hg (KLocallyRingedSpace.isIso_ofRestrict_stalkMap A U a)
  have h₁ := key (Hom.restrictTo_comp_ofRestrict g U U' h) h₂
  rw [Hom.comp_val, LocallyRingedSpace.stalkMap_comp] at h₁
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
      (KLocallyRingedSpace.isIso_ofRestrict_stalkMap B U' _) h₁

/-- The stalk maps of `g | U : A | U ⟶ B | U'` are bijective where those of `g` are. -/
theorem bijective_stalkMap_restrictTo {A B : KLocallyRingedSpace.{u} K} (g : A ⟶ B) (U : Opens A)
    (U' : Opens B) (h : ∀ a ∈ U, Hom.toFun g a ∈ U') (a : A.restrictOpen U)
    (hg : Function.Bijective (g.1.stalkMap ((ofRestrict A U).1.base a)).hom) :
    Function.Bijective ((Hom.restrictTo g U U' h).1.stalkMap a).hom :=
  (ConcreteCategory.isIso_iff_bijective _).mp (isIso_stalkMap_restrictTo g U U' h a
    ((ConcreteCategory.isIso_iff_bijective _).mpr hg))

end KLocallyRingedSpace

end AnalyticSpace
