/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Complexification
public import Hironaka.AnalyticSpace.Restrict.Defs
import Hironaka.AnalyticSpace.CoverLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Properness over an open of the target

Three general facts behind the properness of the resolution morphism over the members of an open
cover ([Wlo09, §4]: "`des_V : Ṽ → V` is bimeromorphic and proper", checked on the pieces of the
gluing; `isProperMap_resolutionOnMap` of
`Hironaka/Resolution/Analytic/Kol07Thm45/PieceGlueDatum.lean`), stated for plain continuous maps and
for `K`-morphisms:

* `isProperMap_of_homeomorph_comp_eq`: properness is invariant under conjugation by homeomorphisms
  of the source and of the target (`f = e_B⁻¹ ∘ f' ∘ e_A`) — the transport used to read the
  resolution morphism on the pieces and on the parts over the base opens;
* `isProperMap_restrictPreimage_of_cover`: a continuous map proper over each member of an open
  family `V i` of the target is proper over every `U ⊆ ⋃ V i` —
  `isProperMap_of_restrictPreimage_cover` of `Hironaka/AnalyticSpace/CoverLemmas.lean` (Mathlib's
  `IsOpenCover.isClosedMap_iff_restrictPreimage`) applied to the restriction over `U` and the
  cover `{U ∩ V i}` of `U`;
* `isProperMap_toFun_restrictTo`: the restriction `g|U : A|U ⟶ B|U'` of a `K`-morphism to opens
  with `U = g⁻¹U'` is proper as soon as `g` is proper over `U'` (the resolution morphism over an
  open is such a restriction); `isProperMap_toFun_restrictSet` for the restriction of the
  vocabulary.

Routine; used by `Hironaka/AnalyticSpace/Glue/OverProper.lean` and
`Hironaka/Resolution/Analytic/Kol07Thm45/ResolutionClauses.lean`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Topology

universe u

namespace AnalyticSpace

section Topology

variable {A B A' B' : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace A']
  [TopologicalSpace B']

/-- **Properness is invariant under conjugation by homeomorphisms** of the source and of the target:
if `e_B ∘ f = f' ∘ e_A` with `f'` proper, then `f = e_B⁻¹ ∘ f' ∘ e_A` is proper
(`Homeomorph.isProperMap`, `IsProperMap.comp`). -/
theorem isProperMap_of_homeomorph_comp_eq (eA : A ≃ₜ A') (eB : B ≃ₜ B') {f : A → B}
    {f' : A' → B'} (hf' : IsProperMap f') (h : ∀ a, eB (f a) = f' (eA a)) : IsProperMap f := by
  have hfe : f = eB.symm ∘ f' ∘ eA := by
    funext a
    exact (eB.symm_apply_apply (f a)).symm.trans (congrArg eB.symm (h a))
  rw [hfe]
  exact eB.symm.isProperMap.comp (hf'.comp eA.isProperMap)

/-- **Swapping two nested subtype conditions** is a homeomorphism:
`{a : {a // p a} // q a} ≃ₜ {a : {a // q a} // p a}` (both are the points with `p ∧ q`; the two
orders of restricting a map over a set of the target arise in
`isProperMap_restrictPreimage_of_cover`). -/
def nestedSubtypeSwap (p q : A → Prop) :
    {a : {a : A // p a} // q a.1} ≃ₜ {a : {a : A // q a} // p a.1} where
  toFun a := ⟨⟨a.1.1, a.2⟩, a.1.2⟩
  invFun a := ⟨⟨a.1.1, a.2⟩, a.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

/-- ([Wlo09, §4]: the properness of `des_V` is checked over the members of the cover `{V_i}` of
`V`.) **A continuous map proper over each member of an open family `V i` of the target is proper
over every `U ⊆ ⋃ V i`**: `isProperMap_of_restrictPreimage_cover`
(`Hironaka/AnalyticSpace/CoverLemmas.lean`) applied to the restriction `f|_U : f⁻¹U → U` with the
open cover `{U ∩ V i}` of `U`; over `U ∩ V i` the restriction of `f|_U` is the restriction of `f|_{V
i}` (`IsProperMap.restrictPreimage`), read through `nestedSubtypeSwap`. -/
theorem isProperMap_restrictPreimage_of_cover {Y X : Type*} [TopologicalSpace Y]
    [TopologicalSpace X] (f : Y → X) (hf : Continuous f) {ι : Type*} (V : ι → Set X)
    (hV : ∀ i, IsOpen (V i)) (h : ∀ i, IsProperMap ((V i).restrictPreimage f)) (U : Set X)
    (hUV : U ⊆ ⋃ i, V i) : IsProperMap (U.restrictPreimage f) := by
  refine isProperMap_of_restrictPreimage_cover (U.restrictPreimage f) hf.restrictPreimage
    (fun i => (Subtype.val : U → X) ⁻¹' V i) (fun i => (hV i).preimage continuous_subtype_val)
    ?_ fun i => ?_
  · refine eq_univ_of_forall fun u => mem_iUnion.mpr ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hUV u.2)
    exact ⟨i, hi⟩
  · exact isProperMap_of_homeomorph_comp_eq
      (nestedSubtypeSwap (fun y => y ∈ f ⁻¹' U) (fun y => f y ∈ V i))
      (nestedSubtypeSwap (fun x => x ∈ U) (fun x => x ∈ V i))
      ((h i).restrictPreimage ((Subtype.val : V i → X) ⁻¹' U)) (fun _ => rfl)

end Topology

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- **The restriction of a `K`-morphism to opens is proper when the morphism is proper over the
target open**: for `g : A ⟶ B` and opens `U = g⁻¹U'`, the underlying map of `g|U : A|U ⟶ B|U'` is
the restriction `U'.restrictPreimage g` read through the identification `U = g⁻¹U'` of the sources
(`Hom.toFun_restrictTo`). -/
theorem isProperMap_toFun_restrictTo {A B : KLocallyRingedSpace.{u} K} (g : A ⟶ B) (U : Opens A)
    (U' : Opens B) (h : ∀ a ∈ U, Hom.toFun g a ∈ U')
    (hset : (U : Set A) = Hom.toFun g ⁻¹' (U' : Set B))
    (hp : IsProperMap ((U' : Set B).restrictPreimage (Hom.toFun g))) :
    IsProperMap (Hom.toFun (Hom.restrictTo g U U' h)) :=
  isProperMap_of_homeomorph_comp_eq (Homeomorph.setCongr hset) (Homeomorph.refl _) hp
    (fun a => Subtype.ext (Hom.toFun_restrictTo g U U' h a))

end KLocallyRingedSpace


open KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- **The restriction `f|_{f⁻¹V} : X|f⁻¹V ⟶ Y|V` of a morphism of analytic spaces to an OPEN `V` of
the target is proper when `f` is proper over `V`** (`Hom.restrictSet`: for an open `V` the opens of
the convention are `V` and `f⁻¹V` themselves, `openOf_of_isOpen`). -/
theorem isProperMap_toFun_restrictSet {X Y : AnalyticSpace.{u} K} (f : X ⟶ Y) {V : Set Y}
    (hV : IsOpen V) (hp : IsProperMap (V.restrictPreimage (Hom.toFun f))) :
    IsProperMap (Hom.toFun (Hom.restrictSet f V)) := by
  have hV' : IsOpen (Hom.toFun f ⁻¹' V) := hV.preimage (Hom.continuous_toFun f)
  have h1 : ∀ y, y ∈ openOf Y V ↔ y ∈ V := fun y =>
    SetLike.ext_iff.mp (openOf_of_isOpen Y hV) y
  have h2 : ∀ x, x ∈ openOf X (Hom.toFun f ⁻¹' V) ↔ Hom.toFun f x ∈ V := fun x =>
    SetLike.ext_iff.mp (openOf_of_isOpen X hV') x
  have hcoe : ((openOf Y V : Opens Y) : Set Y) = V := congrArg SetLike.coe (openOf_of_isOpen Y hV)
  have hset : ((openOf X (Hom.toFun f ⁻¹' V) : Opens X) : Set X) =
      Hom.toFun f ⁻¹' ((openOf Y V : Opens Y) : Set Y) :=
    Set.ext fun x => (h2 x).trans (h1 (Hom.toFun f x)).symm
  have hp' : IsProperMap (((openOf Y V : Opens Y) : Set Y).restrictPreimage (Hom.toFun f)) :=
    isProperMap_of_homeomorph_comp_eq (Homeomorph.setCongr (congrArg (Hom.toFun f ⁻¹' ·) hcoe))
      (Homeomorph.setCongr hcoe) hp fun _ => rfl
  exact isProperMap_toFun_restrictTo f _ _ (fun x hx => (h1 _).mpr ((h2 x).mp hx)) hset hp'


end AnalyticSpace

end
