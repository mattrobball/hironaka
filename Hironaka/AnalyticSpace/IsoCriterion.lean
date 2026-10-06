/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.KSpace.Defs
import Hironaka.AnalyticSpace.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Isomorphisms of `K`-local-ringed spaces through the base and the stalks

A morphism of locally ringed spaces whose underlying map is a homeomorphism and whose stalk maps
are all bijective is an isomorphism: the sheaf component `f.c : 𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism
of sheaves because its stalk maps are (`TopCat.Presheaf.isIso_of_stalkFunctor_map_iso`, the stalk
of `f_* 𝒪_X` at `f x` being the stalk of `𝒪_X` at `x` for a homeomorphism `f`), so `f` is an
isomorphism of presheafed spaces (`PresheafedSpace.isIso_of_components`), hence of sheafed and of
locally ringed spaces (the forgetful functors reflect isomorphisms). The criterion recognises the
`K`-isomorphism `(G', 𝒜_{G'}) ≅ X|V` at a simple point [Hir64, Ch. 0, §1, p. 121] from its
stalks, and identifies a space with a coproduct (`Hironaka/AnalyticSpace/SigmaLemmas.lean`).

* `LocallyRingedSpace.isIso_of_isIso_base_of_stalkMap_bijective`;
* `KLocallyRingedSpace.isIso_of_isIso_base_of_stalkMap_bijective` (through `isIso_of_isIso_val`).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AnalyticSpace

/-- A morphism of locally ringed spaces with a homeomorphism as base map (an isomorphism in
`TopCat`) and bijective stalk maps is an isomorphism. -/
theorem LocallyRingedSpace.isIso_of_isIso_base_of_stalkMap_bijective
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsIso f.1.base]
    (hs : ∀ x, Function.Bijective (f.stalkMap x).hom) : IsIso f := by
  have hsurj : Function.Surjective f.1.base := (TopCat.homeoOfIso (asIso f.1.base)).surjective
  have hind : Topology.IsInducing f.1.base := (TopCat.homeoOfIso (asIso f.1.base)).isInducing
  -- the stalk maps are isomorphisms
  have hstalk : ∀ x, IsIso (f.stalkMap x) := fun x =>
    (ConcreteCategory.isIso_iff_bijective _).mpr (hs x)
  -- hence the stalk components of `f.c` are
  have hc : ∀ y, IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map f.1.c) := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    have hpush : IsIso (X.presheaf.stalkPushforward CommRingCat.{u} f.1.base x) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing CommRingCat.{u} hind
        X.presheaf x
    have hcomp : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f.1.base x)).map f.1.c ≫
        X.presheaf.stalkPushforward CommRingCat.{u} f.1.base x) := hstalk x
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hpush hcomp
  -- so `f.c` is an isomorphism of sheaves, hence of presheaves
  let g : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.1.base).obj X.sheaf := ⟨f.1.c⟩
  have hg : ∀ y, IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map g.hom) := hc
  have hcs : IsIso g := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso g
  have hpc : IsIso f.1.c := (TopCat.Sheaf.forget CommRingCat.{u} Y.carrier).map_isIso g
  -- presheafed spaces, sheafed spaces, locally ringed spaces
  have hpsh := PresheafedSpace.isIso_of_components f.toHom
  have hsh' : IsIso (SheafedSpace.forgetToPresheafedSpace.map f.toShHom) := hpsh
  have hsh : IsIso f.toShHom := isIso_of_reflects_iso f.toShHom SheafedSpace.forgetToPresheafedSpace
  have hl : IsIso (LocallyRingedSpace.forgetToSheafedSpace.map f) := hsh
  exact isIso_of_reflects_iso f LocallyRingedSpace.forgetToSheafedSpace

variable {K : Type} [RCLike K]

/-- A `K`-morphism with a homeomorphism as base map and bijective stalk maps is a `K`-isomorphism
(`isIso_of_isIso_val`: a `K`-morphism whose underlying morphism is an isomorphism is one). -/
theorem KLocallyRingedSpace.isIso_of_isIso_base_of_stalkMap_bijective
    {X Y : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) [IsIso f.1.1.base]
    (hs : ∀ x, Function.Bijective (f.1.stalkMap x).hom) : IsIso f :=
  have := LocallyRingedSpace.isIso_of_isIso_base_of_stalkMap_bijective f.1 hs
  isIso_of_isIso_val f

end AnalyticSpace
