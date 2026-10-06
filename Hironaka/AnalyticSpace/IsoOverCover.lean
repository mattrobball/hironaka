/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.IsoOverOpen
import Hironaka.AnalyticSpace.IsoCriterion
import Hironaka.AnalyticSpace.RestrictToIso
import Hironaka.AnalyticSpace.SigmaLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# Isomorphisms over an open cover of the target

The predicate `f.IsIsoOver U := IsIso (f.restrictSet U)` (`f` restricts to an isomorphism
`f⁻¹U → U`; condition (2) of a resolution in [Hir64, Introduction], clause (2) of
[Kol07, Theorem 45], "`Π` is an isomorphism over `X^ns`") is local on the target:

* the point-level readings of `IsIsoOver` over an open `V` — through the bridge
  `Hom.restrictSet_eq_restrictTo` (`Hironaka/AnalyticSpace/IsoOverOpen.lean`) and the readings of a
  local isomorphism in `Hironaka/AnalyticSpace/RestrictToIso.lean`: `f` is injective on `f⁻¹V`
  (`injOn_of_isIso_restrictSet`), maps `f⁻¹V` onto `V` (`surjOn_of_isIso_restrictSet`), maps opens
  inside `f⁻¹V` to opens (`isOpen_image_inter_preimage_of_isIso_restrictSet`) and has bijective
  stalk maps over `V` (`bijective_stalkMap_of_isIso_restrictSet`);
* `isIso_of_isIso_restrictSet_cover` / `Hom.isIso_of_isIsoOver_cover`: a morphism which is an
  isomorphism over each member of an open cover of the target is an isomorphism — its base map is
  a continuous open bijection, hence a homeomorphism, and the criterion
  `isIso_of_isIso_base_of_stalkMap_bijective` (`Hironaka/AnalyticSpace/IsoCriterion.lean`) applies;
* `isIso_restrictSet_iUnion_of_isIso_restrictSet` / `Hom.isIsoOver_iUnion`: an isomorphism over
  each member of a family of opens is an isomorphism over their union —
  `isIso_restrictTo_of_bijOn_of_bijective_stalkMap` at `f⁻¹(⋃ Vᵢ)`, `⋃ Vᵢ`;
* `isIso_toKLocallyRingedSpace_of_isIso`: the converse of `isIso_of_isIso_toKLocallyRingedSpace`
  (`Hironaka/AnalyticSpace/SigmaLemmas.lean`): an isomorphism of `An/K` is one of `ℜ/K`.

In the gluing of local desingularizations of [Wlo09, §4] the glued morphism inherits its properties
from the pieces. Routine; used by
`Hironaka/Resolution/Analytic/Kol07Thm45/AmbientFactorizationTransport.lean`,
`Hironaka/AnalyticSpace/SncFamilyTransport.lean` and
`Hironaka/Resolution/Analytic/Kol07Thm45/IsoOverLemmas.lean`.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- A morphism of `An/K` which is an isomorphism is an isomorphism in `ℜ/K` (the converse of
`isIso_of_isIso_toKLocallyRingedSpace`; the morphisms and compositions are the same). -/
theorem isIso_toKLocallyRingedSpace_of_isIso {Y Z : AnalyticSpace.{u} K} (f : Y ⟶ Z)
    [h : IsIso f] :
    @IsIso (KLocallyRingedSpace.{u} K) _ Y.toKLocallyRingedSpace Z.toKLocallyRingedSpace f :=
  ⟨⟨@inv (AnalyticSpace.{u} K) _ Y Z f h, @IsIso.hom_inv_id (AnalyticSpace.{u} K) _ Y Z f h,
    @IsIso.inv_hom_id (AnalyticSpace.{u} K) _ Y Z f h⟩⟩

section PointLevel

variable {X Y : AnalyticSpace.{u} K} (f : Y ⟶ X) {V : Set X} (hV : IsOpen V)
  [IsIso (Hom.restrictSet f V)]

/-- The restriction over `V`, as the local isomorphism `Hom.restrictTo` at the opens `openOf`. -/
theorem isIso_restrictTo_openOf_of_isIso_restrictSet :
    IsIso (KLocallyRingedSpace.Hom.restrictTo f
      (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' V)) (openOf X V) (Hom.mapsTo_openOf f V)) :=
  isIso_toKLocallyRingedSpace_of_isIso (Hom.restrictSet f V)

include hV in
/-- An isomorphism over the open `V` is injective on `f⁻¹V`. -/
theorem injOn_of_isIso_restrictSet :
    InjOn (KLocallyRingedSpace.Hom.toFun f) (KLocallyRingedSpace.Hom.toFun f ⁻¹' V) := by
  have := isIso_restrictTo_openOf_of_isIso_restrictSet f (V := V)
  have h := KLocallyRingedSpace.injOn_toFun_of_isIso_restrictTo f
    (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' V)) (openOf X V) (Hom.mapsTo_openOf f V)
  rwa [openOf_of_isOpen Y (hV.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))] at h

include hV in
/-- An isomorphism over the open `V` maps `f⁻¹V` onto `V`. -/
theorem surjOn_of_isIso_restrictSet :
    SurjOn (KLocallyRingedSpace.Hom.toFun f) (KLocallyRingedSpace.Hom.toFun f ⁻¹' V) V := by
  have := isIso_restrictTo_openOf_of_isIso_restrictSet f (V := V)
  intro x hx
  have hx' : x ∈ openOf X V := by rw [openOf_of_isOpen X hV]; exact hx
  set e := KLocallyRingedSpace.restrictToHomeomorph f
    (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' V)) (openOf X V) (Hom.mapsTo_openOf f V) with he
  set u := e.symm ⟨x, hx'⟩ with hu
  have h1 : (e u).1 = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx'⟩)
  have hfu : KLocallyRingedSpace.Hom.toFun f u.1 = x :=
    (KLocallyRingedSpace.restrictToHomeomorph_apply_val f _ _ (Hom.mapsTo_openOf f V) u).symm.trans
      h1
  refine ⟨u.1, ?_, hfu⟩
  have hset : ((openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' V) : Opens Y) : Set Y) =
      KLocallyRingedSpace.Hom.toFun f ⁻¹' V := by
    rw [openOf_of_isOpen Y (hV.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))]
    rfl
  exact (Set.ext_iff.mp hset _).mp u.2

include hV in
/-- An isomorphism over the open `V` maps the opens inside `f⁻¹V` to opens. -/
theorem isOpen_image_inter_preimage_of_isIso_restrictSet {S : Set Y} (hS : IsOpen S) :
    IsOpen (KLocallyRingedSpace.Hom.toFun f '' (S ∩ KLocallyRingedSpace.Hom.toFun f ⁻¹' V)) := by
  have := isIso_restrictTo_openOf_of_isIso_restrictSet f (V := V)
  have h := KLocallyRingedSpace.isOpen_image_of_isIso_restrictTo f
    (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' V)) (openOf X V) (Hom.mapsTo_openOf f V) hS
  rwa [openOf_of_isOpen Y (hV.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))] at h

include hV in
/-- An isomorphism over the open `V` has bijective stalk maps at the points over `V`. -/
theorem bijective_stalkMap_of_isIso_restrictSet (y : Y)
    (hy : KLocallyRingedSpace.Hom.toFun f y ∈ V) :
    Function.Bijective (f.1.stalkMap y).hom := by
  have := isIso_restrictTo_openOf_of_isIso_restrictSet f (V := V)
  refine KLocallyRingedSpace.bijective_stalkMap_of_isIso_restrictTo f
    (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' V)) (openOf X V) (Hom.mapsTo_openOf f V) y ?_
  rw [openOf_of_isOpen Y (hV.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))]
  exact hy

end PointLevel

section Cover

variable {X Y : AnalyticSpace.{u} K} (f : Y ⟶ X) {ι : Type*} (V : ι → Set X)
  (hV : ∀ i, IsOpen (V i)) (h : ∀ i, IsIso (Hom.restrictSet f (V i)))

include hV h in
/-- A morphism which is an isomorphism over each member of an open cover of the target is an
isomorphism (`IsIso f` in `AnalyticSpace`): its base map is a bijection (injective on each `f⁻¹Vᵢ`,
onto each `Vᵢ`) and open (the image of an open is the union of the images of its traces on the
`f⁻¹Vᵢ`), hence a homeomorphism; its stalk maps are bijective;
`isIso_of_isIso_base_of_stalkMap_bijective` concludes. -/
theorem isIso_of_isIso_restrictSet_cover (hcov : ⋃ i, V i = univ) : IsIso f := by
  have hmem : ∀ x : X, ∃ i, x ∈ V i := fun x => mem_iUnion.mp (hcov ▸ mem_univ x)
  have hinj : Function.Injective (KLocallyRingedSpace.Hom.toFun f) := by
    intro y₁ y₂ heq
    obtain ⟨i, hi⟩ := hmem (KLocallyRingedSpace.Hom.toFun f y₂)
    have := h i
    exact injOn_of_isIso_restrictSet f (hV i) (by rw [mem_preimage, heq]; exact hi) hi heq
  have hsurj : Function.Surjective (KLocallyRingedSpace.Hom.toFun f) := fun x => by
    obtain ⟨i, hi⟩ := hmem x
    have := h i
    obtain ⟨y, -, hy⟩ := surjOn_of_isIso_restrictSet f (hV i) hi
    exact ⟨y, hy⟩
  have hopen : IsOpenMap (KLocallyRingedSpace.Hom.toFun f) := by
    intro S hS
    have hS' : KLocallyRingedSpace.Hom.toFun f '' S =
        ⋃ i, KLocallyRingedSpace.Hom.toFun f '' (S ∩ KLocallyRingedSpace.Hom.toFun f ⁻¹' V i) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨i, hi⟩ := hmem (KLocallyRingedSpace.Hom.toFun f y)
        exact mem_iUnion.mpr ⟨i, y, ⟨hy, hi⟩, rfl⟩
      · intro hx
        obtain ⟨i, y, ⟨hy, -⟩, rfl⟩ := mem_iUnion.mp hx
        exact ⟨y, hy, rfl⟩
    rw [hS']
    exact isOpen_iUnion fun i => by
      have := h i
      exact isOpen_image_inter_preimage_of_isIso_restrictSet f (hV i) hS
  have hcont : Continuous (KLocallyRingedSpace.Hom.toFun f) :=
    KLocallyRingedSpace.Hom.continuous_toFun f
  let e := (Equiv.ofBijective _ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen
  have hb : f.1.1.base = (TopCat.isoOfHomeo e).hom := TopCat.ext fun _ => rfl
  have : IsIso f.1.1.base := by rw [hb]; infer_instance
  refine isIso_of_isIso_toKLocallyRingedSpace f
    (KLocallyRingedSpace.isIso_of_isIso_base_of_stalkMap_bijective f fun y => ?_)
  obtain ⟨i, hi⟩ := hmem (KLocallyRingedSpace.Hom.toFun f y)
  have := h i
  exact bijective_stalkMap_of_isIso_restrictSet f (hV i) y hi

include hV h in
/-- A morphism which is an isomorphism over each member of a family of opens is an isomorphism over
their union: `isIso_restrictTo_of_bijOn_of_bijective_stalkMap` at `f⁻¹(⋃ Vᵢ)`, `⋃ Vᵢ` — the base map
is a bijection there and the stalk maps are bijective. -/
theorem isIso_restrictSet_iUnion_of_isIso_restrictSet : IsIso (Hom.restrictSet f (⋃ i, V i)) := by
  have hU : IsOpen (⋃ i, V i) := isOpen_iUnion hV
  have hU' : IsOpen (KLocallyRingedSpace.Hom.toFun f ⁻¹' ⋃ i, V i) :=
    hU.preimage (KLocallyRingedSpace.Hom.continuous_toFun f)
  apply isIso_of_isIso_toKLocallyRingedSpace
  rw [Hom.restrictSet_eq_restrictTo]
  apply isIso_restrictTo_of_bijOn_of_bijective_stalkMap
  · rw [openOf_of_isOpen _ hU', openOf_of_isOpen _ hU]
    refine ⟨fun y hy => hy, ?_, ?_⟩
    · intro y₁ hy₁ y₂ hy₂ heq
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hy₂ : KLocallyRingedSpace.Hom.toFun f y₂ ∈ ⋃ i, V i)
      have := h i
      exact injOn_of_isIso_restrictSet f (hV i) (by rw [mem_preimage, heq]; exact hi) hi heq
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have := h i
      obtain ⟨y, hy, hyx⟩ := surjOn_of_isIso_restrictSet f (hV i) hi
      exact ⟨y, mem_iUnion.mpr ⟨i, hy⟩, hyx⟩
  · intro y hy
    rw [openOf_of_isOpen _ hU'] at hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    have := h i
    exact bijective_stalkMap_of_isIso_restrictSet f (hV i) y hi

end Cover

/-- A morphism of analytic spaces that is an isomorphism over each member of an open cover of the
target is an isomorphism (`Hom.IsIsoOver`, `IsIso`; [Kol07, Theorem 45 (2)] checked on the
pieces). -/
theorem Hom.isIso_of_isIsoOver_cover {X Y : AnalyticSpace.{u} K}
    (f : Y ⟶ X) {ι : Type*} (V : ι → Set X)
        (hV : ∀ i, IsOpen (V i))
    (hcov : ⋃ i, V i = univ) (h : ∀ i, f.IsIsoOver (V i)) : IsIso f :=
  isIso_of_isIso_restrictSet_cover f V hV h hcov

/-- `IsIsoOver` of a union of opens from `IsIsoOver` of each member ([Kol07, Theorem 45 (2)]: the
isomorphism over `X.regularLocus` assembled from the pieces). -/
theorem Hom.isIsoOver_iUnion {X Y : AnalyticSpace.{u} K}
    (f : Y ⟶ X) {ι : Type*} (V : ι → Set X)
        (hV : ∀ i, IsOpen (V i))
    (h : ∀ i, f.IsIsoOver (V i)) : f.IsIsoOver (⋃ i, V i) :=
  isIso_restrictSet_iUnion_of_isIso_restrictSet f V hV h

end AnalyticSpace

end
