/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.KSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# `K`-local-ringed spaces: basic properties

The elementary theory of `K`-local-ringed spaces and their `K`-morphisms.

* A `K`-morphism pulls the constants back to the constants (`Hom.pullbackΓ`,
  `Hom.pullbackΓ_algebraMap`), and the germ of the pullback of a global section is the stalk map on
  its germ (`germ_top_pullbackΓ`).
* The underlying morphism of locally ringed spaces and the underlying map of identities, composites
  and factorizations (`Hom.id_val`, `Hom.comp_val`, `Hom.ofFac_val`, `Hom.toFun_id`,
  `Hom.toFun_comp`, `Hom.range_toFun_comp`), which is continuous (`Hom.continuous_toFun`); the range
  of the open immersion `X | U ⟶ X` is `U` (`range_toFun_ofRestrict`).
* A `K`-isomorphism is an isomorphism of locally ringed spaces (`KIso.isIso_hom_val`) and a
  homeomorphism (`KIso.homeomorph`).
* Two open immersions of `K`-local-ringed spaces with the same range are `K`-isomorphic
  (`isoOfRangeEq`, by Mathlib's `IsOpenImmersion.lift` and its uniqueness), and the range of an
  open immersion is open (`isOpen_range_toFun`).
* The `K`-morphisms of analytic maps are functorial (`ofManifoldHom_id`, `ofManifoldHom_comp`, both
  by `rfl`) and have the analytic map as underlying map (`toFun_ofManifoldHom`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The pullback of a global section along a `K`-morphism, `Γ(Y, 𝒪_Y) →+* Γ(X, 𝒪_X)`. -/
def Hom.pullbackΓ {X Y : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) :
    LocallyRingedSpace.Γ.obj (op Y.toLocallyRingedSpace) →+*
      LocallyRingedSpace.Γ.obj (op X.toLocallyRingedSpace) :=
  (LocallyRingedSpace.Γ.map f.1.op).hom

/-- A `K`-morphism pulls the constants of `Y` back to the constants of `X`. -/
theorem Hom.pullbackΓ_algebraMap {X Y : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) (c : K) :
    f.pullbackΓ (Y.algebraMap c) = X.algebraMap c :=
  congrArg (fun φ : K →+* _ => φ c) f.2

/-- The germ at `x` of the pullback of a global section is the stalk map on its germ. -/
theorem germ_top_pullbackΓ {A B : KLocallyRingedSpace.{u} K} (l : A ⟶ B)
    (τ : LocallyRingedSpace.Γ.obj (op B.toLocallyRingedSpace)) (x : A) :
    A.toLocallyRingedSpace.presheaf.germ ⊤ x trivial (l.pullbackΓ τ) =
      l.1.stalkMap x (B.toLocallyRingedSpace.presheaf.germ ⊤ (l.1.base x) trivial τ) := by
  have hA := PresheafedSpace.stalkMap_germ_apply l.1.1 ⊤ x trivial τ
  change A.toLocallyRingedSpace.presheaf.germ ⊤ x trivial
    ((LocallyRingedSpace.Γ.map l.1.op).hom τ) = _
  rw [LocallyRingedSpace.Γ_map_op]
  change A.toLocallyRingedSpace.presheaf.germ ((Opens.map l.1.1.base).obj ⊤) x trivial
    (l.1.1.c.app (op ⊤) τ) = _
  erw [← hA]
  rfl

@[simp]
theorem Hom.ofFac_val {A B X : KLocallyRingedSpace.{u} K} (a : A ⟶ X) (b : B ⟶ X)
    (l : A.toLocallyRingedSpace ⟶ B.toLocallyRingedSpace) (hl : l ≫ b.1 = a.1) :
    (Hom.ofFac a b l hl).1 = l :=
  rfl

/-- The morphism of locally ringed spaces underlying a composite of `K`-morphisms is the
composite. -/
@[simp]
theorem Hom.comp_val {X Y Z : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl

/-- The morphism of locally ringed spaces underlying the identity `K`-morphism is the identity. -/
@[simp]
theorem Hom.id_val (X : KLocallyRingedSpace.{u} K) : (𝟙 X : X ⟶ X).1 = 𝟙 X.toLocallyRingedSpace :=
  rfl

/-- The underlying map of a composite is the composite of the underlying maps. -/
@[simp]
theorem Hom.toFun_comp {X Y Z : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.toFun (f ≫ g) = Hom.toFun g ∘ Hom.toFun f :=
  rfl

/-- The underlying map of the identity is the identity. -/
theorem Hom.toFun_id (X : KLocallyRingedSpace.{u} K) : Hom.toFun (𝟙 X) = id :=
  rfl

/-- The range of a composite is the image under the second map of the range of the first. -/
theorem Hom.range_toFun_comp {X Y Z : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Set.range (Hom.toFun (f ≫ g)) = Hom.toFun g '' Set.range (Hom.toFun f) := by
  rw [Hom.toFun_comp, Set.range_comp]

/-- The underlying map of a `K`-morphism is continuous. -/
theorem Hom.continuous_toFun {X Y : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) :
    Continuous (Hom.toFun f) :=
  f.1.base.hom.continuous

/-- The range of the open immersion `X | U ⟶ X` is `U`. -/
@[simp]
theorem range_toFun_ofRestrict (X : KLocallyRingedSpace.{u} K) (U : Opens X) :
    Set.range (Hom.toFun (X.ofRestrict U)) = (U : Set X) :=
  Subtype.range_coe

/-- The underlying morphism of locally ringed spaces of a `K`-isomorphism is an isomorphism. -/
instance KIso.isIso_hom_val {A B : KLocallyRingedSpace.{u} K} (e : KIso A B) : IsIso e.hom.1 :=
  ⟨⟨e.inv.1, congrArg Subtype.val e.hom_inv_id, congrArg Subtype.val e.inv_hom_id⟩⟩

/-- The homeomorphism underlying a `K`-isomorphism. -/
def KIso.homeomorph {A B : KLocallyRingedSpace.{u} K} (e : KIso A B) : A ≃ₜ B :=
  TopCat.homeoOfIso (LocallyRingedSpace.forgetToTop.mapIso (asIso e.hom.1))

/-- Two open immersions of `K`-local-ringed spaces with the same range are `K`-isomorphic (the
`K`-version of Mathlib's `IsOpenImmersion.isoOfRangeEq`, by the universal property of open
immersions). -/
def isoOfRangeEq {A B X : KLocallyRingedSpace.{u} K} (a : A ⟶ X) (b : B ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion a.1] [LocallyRingedSpace.IsOpenImmersion b.1]
    (h : Set.range (Hom.toFun a) = Set.range (Hom.toFun b)) : A ≅ B :=
  have h₁ : Set.range a.1.base ⊆ Set.range b.1.base := le_of_eq h
  have h₂ : Set.range b.1.base ⊆ Set.range a.1.base := le_of_eq h.symm
  { hom := Hom.ofFac a b (LocallyRingedSpace.IsOpenImmersion.lift b.1 a.1 h₁)
      (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _)
    inv := Hom.ofFac b a (LocallyRingedSpace.IsOpenImmersion.lift a.1 b.1 h₂)
      (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _)
    hom_inv_id := Hom.ext (by
      rw [Hom.comp_val, Hom.id_val, Hom.ofFac_val, Hom.ofFac_val, ← cancel_mono a.1,
        Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac,
        LocallyRingedSpace.IsOpenImmersion.lift_fac, Category.id_comp])
    inv_hom_id := Hom.ext (by
      rw [Hom.comp_val, Hom.id_val, Hom.ofFac_val, Hom.ofFac_val, ← cancel_mono b.1,
        Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac,
        LocallyRingedSpace.IsOpenImmersion.lift_fac, Category.id_comp]) }

/-- The range of an open immersion of `K`-local-ringed spaces is open. -/
theorem isOpen_range_toFun {A X : KLocallyRingedSpace.{u} K} (a : A ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion a.1] : IsOpen (Set.range (Hom.toFun a)) :=
  (PresheafedSpace.IsOpenImmersion.base_open (f := a.1.toShHom.hom)).isOpenMap.isOpen_range

section OfManifoldHom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace K E'] {E'' : Type*} [NormedAddCommGroup E'']
  [NormedSpace K E''] {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {N : Type u}
  [TopologicalSpace N] [ChartedSpace E' N] {P : Type u} [TopologicalSpace P] [ChartedSpace E'' P]

theorem toFun_ofManifoldHom (f : M → N) (hf : ContMDiff 𝓘(K, E) 𝓘(K, E') ω f) :
    Hom.toFun (ofManifoldHom f hf) = f :=
  rfl

/-- Functoriality: the identity. -/
theorem ofManifoldHom_id :
    ofManifoldHom (M := M) (E := E) (E' := E) id contMDiff_id = 𝟙 (ofManifold K E M) :=
  rfl

/-- Functoriality: composition. -/
theorem ofManifoldHom_comp (f : M → N) (hf : ContMDiff 𝓘(K, E) 𝓘(K, E') ω f) (g : N → P)
    (hg : ContMDiff 𝓘(K, E') 𝓘(K, E'') ω g) :
    ofManifoldHom (g ∘ f) (hg.comp hf) = ofManifoldHom f hf ≫ ofManifoldHom g hg :=
  rfl

end OfManifoldHom

end KLocallyRingedSpace

end AnalyticSpace
