/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Hironaka.Manifold.Sheaf.ContMDiff
import Hironaka.Manifold.Sheaf.LocalRing
public import Hironaka.Manifold.StructureSheaf
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace  -- shake: keep (used only by `example`s)

/-!
# `K`-local-ringed spaces

Hironaka's analytic `K`-spaces, `K = ℝ` or `ℂ`, are `K`-local-ringed spaces: local-ringed spaces
with a structural morphism to `Spec K`, forming the category `ℜ/K` of which the analytic
`K`-spaces are the full subcategory `An/K` [Hir64, Ch. 0, §1, pp. 119–121]. This file defines
them and the constructions the rest of the theory rests on: the open subspace `X | U`, and the
`K`-local-ringed space `(M, 𝒪_M)` of an analytic manifold together with the `K`-morphism of an
analytic map.

## The `K`-structure

The `K`-structure is data: a ring homomorphism `K →+* Γ(X, 𝒪_X)`. By the adjunction between
global sections and `Spec` on locally ringed spaces this is the same as a morphism `X → Spec K`,
and it keeps `K : Type` while the carrier lives in an arbitrary universe. Morphisms of locally
ringed spaces need not respect it: over `ℂ` the map `f(z) ↦ conj (f (conj z))` is a ring
automorphism of the convergent power series ring `ℂ{z}` that is not `ℂ`-linear, and over `ℝ` a
nonzero `ℚ`-derivation `d` of `ℝ` gives the ring homomorphism `r ↦ r + d(r) ε` into `ℝ[ε]/(ε²)`,
different from the canonical one. The morphisms of `K`-local-ringed spaces are therefore the
`K`-morphisms: morphisms of locally ringed spaces that commute with the structural homomorphisms
on global sections. Every restriction map and every stalk map of a `K`-morphism is then
`K`-linear (`Hom.algebraMap_res`, `Hom.algebraMap_stalk`).

## Main definitions

* `KLocallyRingedSpace K`: a `LocallyRingedSpace` with `algebraMap : K →+* Γ(X, 𝒪_X)`, with its
  category (the `K`-morphisms), `KIso` (the `K`-isomorphisms) and `Hom.toFun` (the underlying
  continuous map); `Hom.ofFac`: a factorization of a `K`-morphism through a `K`-morphism is a
  `K`-morphism.
* `KLocallyRingedSpace.restrictOpen X U`: the open subspace `X | U`, the restriction of the
  locally ringed space along the open embedding of `U` with the restricted `K`-structure, and the
  open immersion `ofRestrict : X | U ⟶ X` as a `K`-morphism.
* `KLocallyRingedSpace.ofManifold K E M`: the locally ringed space `(M, 𝒪_M)` of an analytic
  manifold `M` modelled on `E`, `𝒪_M` the sheaf of analytic functions, with the constants as
  `K`-structure. For `M = Kⁿ` this is Hironaka's `(Kⁿ, 𝒜_{Kⁿ})` (`AnalyticSpace.affine`), and
  `𝒜_G` for an open `G ⊆ Kⁿ` is its restriction `restrictOpen`, as Hironaka defines it.
* `ofManifoldHom f hf : ofManifold K E M ⟶ ofManifold K E' N`, the `K`-morphism induced by an
  analytic map `f : M → N`, the analytic analogue of Mathlib's `ChartedSpace.locallyRingedSpaceMap`
  for smooth manifolds: the base map is `f`; the sheaf map `𝒪_N ⟶ f_* 𝒪_M` is precomposition with
  `f`, an analytic function `g` on `U ⊆ N` going to `g ∘ f` on `f⁻¹(U)` (`ofManifoldSheafHom`); the
  stalk maps `𝒪_{N, f x} → 𝒪_{M, x}` are local, because the value at `x` of `g ∘ f` is the value
  at `f x` of `g` (`stalkMap_ofManifoldHomAux_evalHom`) and a germ is a unit exactly when its value
  is nonzero; the `K`-structure is respected, a constant pulling back to the same constant. The
  model spaces `E`, `E'` of source and target may differ: a chart `φ : U → E` is an analytic map
  into the manifold `E`, and an open subset of `Kⁿ` is a manifold modelled on `Kⁿ`. This is the
  morphism part of the functor `Sp` from analytic manifolds to the analytic `K`-spaces of
  [Hir64, Ch. 0, §1, pp. 119–120] (`AnalyticSpace.toSpaceHom`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

/-- A `K`-local-ringed space [Hir64, Ch. 0, §1, p. 119]: a locally ringed space `X` together with
its structural homomorphism `algebraMap : K →+* Γ(X, 𝒪_X)`, the ring-homomorphism form of a
morphism `X → Spec K`. -/
structure KLocallyRingedSpace (K : Type) [RCLike K] extends LocallyRingedSpace.{u} where
  /-- The `K`-structure: the constants `K → Γ(X, 𝒪_X)`. -/
  algebraMap : K →+* LocallyRingedSpace.Γ.obj (op toLocallyRingedSpace)

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K]

instance : CoeSort (KLocallyRingedSpace.{u} K) (Type u) :=
  ⟨fun X => (X.toLocallyRingedSpace.carrier : Type u)⟩

/-- The `K`-morphisms [Hir64, Ch. 0, §1, p. 121]: the morphisms of locally ringed spaces that
commute with the structural homomorphisms on global sections. -/
abbrev Hom (X Y : KLocallyRingedSpace.{u} K) : Type u :=
  {f : X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace //
    (LocallyRingedSpace.Γ.map f.op).hom.comp Y.algebraMap = X.algebraMap}

/-- The category `ℜ/K` of `K`-local-ringed spaces [Hir64, Ch. 0, §1, p. 121]. -/
instance : Category (KLocallyRingedSpace.{u} K) where
  Hom := Hom
  id X := ⟨𝟙 X.toLocallyRingedSpace, by
    rw [op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id]
    exact RingHom.id_comp _⟩
  comp {X Y Z} f g := ⟨f.1 ≫ g.1, by
    rw [op_comp, CategoryTheory.Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_assoc, g.2,
      f.2]⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

/-- A `K`-morphism is determined by its underlying morphism of locally ringed spaces; the
`K`-condition is a proposition. -/
theorem Hom.ext {X Y : KLocallyRingedSpace.{u} K} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

/-- The underlying continuous map of a `K`-morphism. -/
def Hom.toFun {X Y : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) : X → Y := fun x => f.1.base x

/-- `K`-isomorphisms: the isomorphisms of the category `ℜ/K` (Hironaka's "`K`-isomorphic"). -/
abbrev KIso (X Y : KLocallyRingedSpace.{u} K) : Type u := X ≅ Y

/-- A factorization `l` of the `K`-morphism `a` through the `K`-morphism `b` is a `K`-morphism. -/
def Hom.ofFac {A B X : KLocallyRingedSpace.{u} K} (a : A ⟶ X) (b : B ⟶ X)
    (l : A.toLocallyRingedSpace ⟶ B.toLocallyRingedSpace) (hl : l ≫ b.1 = a.1) : A ⟶ B :=
  ⟨l, by
    have h := a.2
    rw [← hl, op_comp, CategoryTheory.Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_assoc,
      b.2] at h
    exact h⟩

/-- The open subspace `X | U` [Hir64, Ch. 0, §1, p. 120]: the restriction of the locally ringed
space along the open embedding of `U`, with the `K`-structure obtained by restricting the
constants. -/
@[implicit_reducible]
def restrictOpen (X : KLocallyRingedSpace.{u} K) (U : Opens X) : KLocallyRingedSpace.{u} K where
  toLocallyRingedSpace := X.toLocallyRingedSpace.restrict (Opens.isOpenEmbedding U)
  algebraMap := (LocallyRingedSpace.Γ.map
    (X.toLocallyRingedSpace.ofRestrict (Opens.isOpenEmbedding U)).op).hom.comp X.algebraMap

/-- The open immersion `X | U ⟶ X` as a `K`-morphism. -/
def ofRestrict (X : KLocallyRingedSpace.{u} K) (U : Opens X) : X.restrictOpen U ⟶ X :=
  ⟨X.toLocallyRingedSpace.ofRestrict (Opens.isOpenEmbedding U), rfl⟩

instance (X : KLocallyRingedSpace.{u} K) (U : Opens X) :
    LocallyRingedSpace.IsOpenImmersion (X.ofRestrict U).1 :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
    (X.toLocallyRingedSpace.ofRestrict (Opens.isOpenEmbedding U)))

variable (K) in
/-- The locally ringed space `(M, 𝒪_M)` of an analytic manifold `M` modelled on `E`: `𝒪_M` is the
sheaf of analytic functions on `M`, whose stalks are local rings, and the constants give the
`K`-structure. For `M = Kⁿ` this is Hironaka's `(Kⁿ, 𝒜_{Kⁿ})`, `𝒜_{Kⁿ}` the sheaf of germs of
analytic `K`-functions on `Kⁿ`, with the convergent power series rings `K{z₁ - x₁, …, zₙ - xₙ}`
as stalks [Hir64, Ch. 0, §1]. -/
@[implicit_reducible]
def ofManifold (E : Type*) [NormedAddCommGroup E] [NormedSpace K E] (M : Type u)
    [TopologicalSpace M] [ChartedSpace E M] : KLocallyRingedSpace.{u} K where
  carrier := TopCat.of M
  presheaf := (Manifold.structureSheaf K E M).presheaf
  IsSheaf := (Manifold.structureSheaf K E M).property
  isLocalRing := Manifold.structureSheaf.instLocalRing_stalk K E M
  algebraMap := Manifold.constHom K E M

/-! ### The `K`-morphism of an analytic map -/

section OfManifoldHom

open Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace K E'] {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] {N : Type u} [TopologicalSpace N] [ChartedSpace E' N]

/-- A map into an open subset `U` of a manifold is `C^n` iff it is `C^n` as a map into the manifold
(Mathlib's `ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff`, for every `n`). -/
theorem contMDiff_subtypeVal_comp_iff' {n : WithTop ℕ∞} {U : Opens N} (g : M → U) :
    ContMDiff 𝓘(K, E) 𝓘(K, E') n (Subtype.val ∘ g) ↔ ContMDiff 𝓘(K, E) 𝓘(K, E') n g :=
  forall_congr' fun x => ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff g Set.univ x

/-- The continuous map underlying an analytic map, as a morphism of `TopCat`. -/
def ofManifoldBase (f : M → N) (hf : ContMDiff 𝓘(K, E) 𝓘(K, E') ω f) :
    TopCat.of M ⟶ TopCat.of N :=
  TopCat.ofHom ⟨f, hf.continuous⟩

/-- **The sheaf map of an analytic map**, `𝒪_N ⟶ f_* 𝒪_M`: precomposition with `f`, an analytic
function `g` on `U ⊆ N` going to `g ∘ f` on `f⁻¹(U)`. -/
def ofManifoldSheafHom (f : M → N) (hf : ContMDiff 𝓘(K, E) 𝓘(K, E') ω f) :
    (structureSheaf K E' N).presheaf ⟶
      (ofManifoldBase f hf) _* (structureSheaf K E M).presheaf where
  app U := CommRingCat.ofHom
    { toFun := fun g => ⟨g ∘ Set.restrictPreimage _ f, by
        apply ContMDiff.comp (I' := 𝓘(K, E')) g.2
        exact (contMDiff_subtypeVal_comp_iff' _).mp (hf.comp contMDiff_subtype_val)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality _ _ _ := rfl

/-- (Implementation.) The morphism of presheafed spaces underlying `ofManifoldHom`. -/
def ofManifoldHomAux (f : M → N) (hf : ContMDiff 𝓘(K, E) 𝓘(K, E') ω f) :
    (ofManifold K E M).toPresheafedSpace ⟶ (ofManifold K E' N).toPresheafedSpace where
  base := ofManifoldBase f hf
  c := ofManifoldSheafHom f hf

/-- The stalk map of an analytic map followed by evaluation at `x` is evaluation at `f x`. -/
theorem stalkMap_ofManifoldHomAux_evalHom (f : M → N) (hf : ContMDiff 𝓘(K, E) 𝓘(K, E') ω f)
    (x : M) :
    (ofManifoldHomAux f hf).stalkMap x ≫ contMDiffSheafCommRing.evalHom 𝓘(K, E) 𝓘(K) ω M K x =
      contMDiffSheafCommRing.evalHom 𝓘(K, E') 𝓘(K) ω N K (f x) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  rw [PresheafedSpace.stalkMap_germ_assoc]
  refine CommRingCat.hom_ext (RingHom.ext fun g => ?_)
  exact (contMDiffSheafCommRing.evalHom_germ 𝓘(K, E) 𝓘(K) ω M K
    ((Opens.map (ofManifoldBase f hf)).obj U) x hxU _).trans
    (contMDiffSheafCommRing.evalHom_germ 𝓘(K, E') 𝓘(K) ω N K U (f x) hxU g).symm

/-- The evaluation at `x` of the stalk map applied to a germ at `f x` is the evaluation of the
germ at `f x`. -/
theorem eval_stalkMap_ofManifoldHomAux (f : M → N) (hf : ContMDiff 𝓘(K, E) 𝓘(K, E') ω f) (x : M)
    (a : (ofManifold K E' N).presheaf.stalk (f x)) :
    contMDiffSheafCommRing.eval 𝓘(K, E) 𝓘(K) ω M K x (((ofManifoldHomAux f hf).stalkMap x).hom a) =
      contMDiffSheafCommRing.eval 𝓘(K, E') 𝓘(K) ω N K (f x) a := by
  have h := congrArg
    (fun φ : (ofManifold K E' N).presheaf.stalk (f x) ⟶ CommRingCat.of (ULift.{u} K) => φ.hom a)
    (stalkMap_ofManifoldHomAux_evalHom f hf x)
  exact congrArg ULift.down h

/-- **The `K`-morphism induced by an analytic map** `f : M → N`: base map `f`, sheaf map
precomposition with `f`; the stalk maps are local since evaluation is preserved and a germ is a unit
exactly when its value is nonzero; constants go to constants. -/
def ofManifoldHom (f : M → N) (hf : ContMDiff 𝓘(K, E) 𝓘(K, E') ω f) :
    ofManifold K E M ⟶ ofManifold K E' N :=
  ⟨{ __ := ofManifoldHomAux f hf
     prop := fun x => by
       refine ⟨fun a ha => ?_⟩
       rw [contMDiffSheafCommRing.isUnit_stalk_iff] at ha ⊢
       exact ne_of_eq_of_ne (eval_stalkMap_ofManifoldHomAux f hf x a).symm ha },
   rfl⟩

end OfManifoldHom

end KLocallyRingedSpace

end AnalyticSpace
