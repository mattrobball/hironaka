/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Complexification
public import Hironaka.AnalyticSpace.Restrict.Defs
import Hironaka.AnalyticSpace.IsoCriterion
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.AnalyticSpace.RestrictToIso
import Hironaka.AnalyticSpace.StalkMapLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Isomorphisms over an open set: from points and stalks

Three general tools for the predicate `f.IsIsoOver U := IsIso (f.restrictSet U)` (condition (2) of a
resolution in [Hir64, Introduction]; [Kol07, Theorem 45 (2)]), used to show that the local
resolution map is an isomorphism over the simple locus and wherever that clause is used:

* `AnalyticSpace.Hom.restrictSet_eq_restrictTo`: the restriction `f | f⁻¹V` of the vocabulary is
  `Hom.restrictTo` at the opens `openOf`, definitionally — the bridge from the predicate to the
  local-isomorphism vocabulary of `Hironaka/AnalyticSpace/LocalIso.lean`;
* `AnalyticSpace.isIso_restrictTo_of_bijOn_of_bijective_stalkMap`: a morphism of analytic
  `K`-spaces which is bijective from `U` onto `V` and has bijective stalk maps at the points of
  `U` is a `K`-isomorphism `X | U ≅ Y | V` — the local isomorphisms of
  `exists_isIso_restrictTo_of_bijective_stalkMap` make the base map open, so it is a
  homeomorphism, and the criterion `isIso_of_isIso_base_of_stalkMap_bijective` applies;
* `QuotientSpace.fiberMap_bijective_of_stalkIdeal_eq_map`: the fibre map of a compatible pair of
  ideal sheaves is bijective at a point where the stalk map is bijective and the target ideal is
  the image of the source ideal — `fiberMap_comap_bijective` of
  `Hironaka/AnalyticSpace/QuotientMap.lean` with the stalkwise hypothesis in place of `J' = comap φ
  J` (for a strict transform, equal to the pullback only off the exceptional locus).

Routine (general topology and the two criteria). Used by `Hironaka/AnalyticSpace/IsoOverCover.lean`,
`Hironaka/Resolution/Analytic/Kol07Thm45/IsoOverLemmas.lean`,
`Hironaka/Resolution/Analytic/Kol07Thm45/RestrictSetIncl.lean` and `Hironaka/Manifold/Sequence/`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u


variable {K : Type} [RCLike K]

namespace AnalyticSpace.QuotientSpace

/-- The induced map of fibres `𝒪_{X,φ z'}/𝒥_{φ z'} → 𝒪_{X',z'}/𝒥'_{z'}` of a compatible pair is
bijective at a point where the stalk map of `φ` is bijective and `𝒥'_{z'}` is the image of
`𝒥_{φ z'}` (the proof of `fiberMap_comap_bijective`, with the stalkwise hypothesis). -/
theorem fiberMap_bijective_of_stalkIdeal_eq_map {X' X : LocallyRingedSpace.{u}} (φ : X' ⟶ X)
    (J' : IdealSheaf X'.𝒪) (J : IdealSheaf X.𝒪) (h : Compat φ J' J) (z' : support X' J')
    (hb : Function.Bijective (φ.stalkMap z'.1).hom)
    (heq : stalkIdeal X' J' z'.1 = (stalkIdeal X J (φ.base z'.1)).map (φ.stalkMap z'.1).hom) :
    Function.Bijective (fiberMap φ J' J h z') := by
  refine ⟨Ideal.quotientMap_injective' ?_, Ideal.quotientMap_surjective hb.2⟩
  change (stalkIdeal X' J' z'.1).comap (φ.stalkMap z'.1).hom ≤ _
  rw [heq]
  exact (Ideal.comap_map_of_bijective _ hb).le

end AnalyticSpace.QuotientSpace

namespace AnalyticSpace

/-- The lift condition of the restriction `Hom.restrictSet`, in the form `Hom.restrictTo` takes it:
`f` maps `openOf X (f⁻¹V)` into `openOf Y V`. -/
theorem Hom.mapsTo_openOf {X Y : AnalyticSpace.{u} K} (f : X ⟶ Y) (V : Set Y) :
    ∀ a ∈ openOf X (KLocallyRingedSpace.Hom.toFun f ⁻¹' V),
      KLocallyRingedSpace.Hom.toFun f a ∈ openOf Y V := by
  intro a ha
  by_cases hV : IsOpen V
  · rw [openOf_of_isOpen Y hV]
    rw [openOf_of_isOpen X (hV.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))] at ha
    exact ha
  · rw [openOf_of_not_isOpen Y hV]
    exact trivial

/-- The restriction `f.restrictSet V : X | f⁻¹V ⟶ Y | V` is `Hom.restrictTo` at the opens
`openOf`: both are the lift of `f` through the open immersion `Y | V ⟶ Y`. -/
theorem Hom.restrictSet_eq_restrictTo {X Y : AnalyticSpace.{u} K} (f : X ⟶ Y) (V : Set Y) :
    Hom.restrictSet f V =
      KLocallyRingedSpace.Hom.restrictTo f (openOf X (KLocallyRingedSpace.Hom.toFun f ⁻¹' V))
        (openOf Y V) (Hom.mapsTo_openOf f V) :=
  rfl

/-- A morphism of analytic `K`-spaces which is bijective from the open `U` onto the open `V` and has
bijective stalk maps at the points of `U` restricts to a `K`-isomorphism `X | U ≅ Y | V`: the
restricted base map is a continuous bijection which is open — at every point of `U` the morphism is
a local isomorphism (`exists_isIso_restrictTo_of_bijective_stalkMap`), and a local isomorphism maps
opens to opens (`isOpen_image_of_isIso_restrictTo`) — hence a homeomorphism; the stalk maps of the
restriction are those of `φ`; the criterion `isIso_of_isIso_base_of_stalkMap_bijective` concludes.
-/
theorem isIso_restrictTo_of_bijOn_of_bijective_stalkMap {X Y : AnalyticSpace.{u} K} (φ : X ⟶ Y)
    (U : Opens X) (V : Opens Y) (hUV : ∀ u ∈ U, KLocallyRingedSpace.Hom.toFun φ u ∈ V)
    (hbij : Set.BijOn (KLocallyRingedSpace.Hom.toFun φ) U V)
    (hs : ∀ u ∈ U, Function.Bijective (φ.1.stalkMap u).hom) :
    IsIso (KLocallyRingedSpace.Hom.restrictTo φ U V hUV) := by
  set r := KLocallyRingedSpace.Hom.restrictTo φ U V hUV with hr
  have hval : ∀ u, (KLocallyRingedSpace.Hom.toFun r u).1 = KLocallyRingedSpace.Hom.toFun φ u.1 :=
    fun u => KLocallyRingedSpace.Hom.toFun_restrictTo φ U V hUV u
  -- the base map is bijective
  have hinj : Function.Injective (KLocallyRingedSpace.Hom.toFun r) := by
    intro u₁ u₂ h
    apply Subtype.ext
    apply hbij.injOn u₁.2 u₂.2
    rw [← hval, ← hval, h]
  have hsurj : Function.Surjective (KLocallyRingedSpace.Hom.toFun r) := by
    intro v
    obtain ⟨u, hu, huv⟩ := hbij.surjOn v.2
    exact ⟨⟨u, hu⟩, Subtype.ext ((hval ⟨u, hu⟩).trans huv)⟩
  -- `φ` maps opens of `X` inside `U` to opens of `Y`: it is a local isomorphism at every point
  have himage : ∀ S : Set X, IsOpen S → S ⊆ U → IsOpen (KLocallyRingedSpace.Hom.toFun φ '' S) := by
    intro S hS hSU
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨u, huS, rfl⟩
    obtain ⟨U₀, hu₀, V₀, hU₀V₀, hiso⟩ :=
      exists_isIso_restrictTo_of_bijective_stalkMap φ u (hs u (hSU huS))
    refine ⟨KLocallyRingedSpace.Hom.toFun φ '' (S ∩ U₀), Set.image_mono Set.inter_subset_left,
      KLocallyRingedSpace.isOpen_image_of_isIso_restrictTo φ U₀ V₀ hU₀V₀ hS, ⟨u, ⟨huS, hu₀⟩, rfl⟩⟩
  -- the base map is open: the image of an open `O` of `X | U` is the image under `φ` of the open
  -- `Subtype.val '' O ⊆ U` of `X`, read back inside `V`
  have hopen : IsOpenMap (KLocallyRingedSpace.Hom.toFun r) := by
    intro O hO
    have hO' : IsOpen (Subtype.val '' O) := U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hO
    have hset : Subtype.val '' (KLocallyRingedSpace.Hom.toFun r '' O) =
        KLocallyRingedSpace.Hom.toFun φ '' (Subtype.val '' O) := by
      ext y
      constructor
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨u.1, ⟨u, hu, rfl⟩, (hval u).symm⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨KLocallyRingedSpace.Hom.toFun r u, ⟨u, hu, rfl⟩, hval u⟩
    have key : IsOpen (Subtype.val '' (KLocallyRingedSpace.Hom.toFun r '' O)) := by
      rw [hset]
      refine himage _ hO' ?_
      rintro _ ⟨u, -, rfl⟩
      exact u.2
    exact V.isOpen.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mpr key
  -- the base map is a homeomorphism; the stalk maps are those of `φ`
  have hcont : Continuous (KLocallyRingedSpace.Hom.toFun r) :=
    KLocallyRingedSpace.Hom.continuous_toFun r
  let e := (Equiv.ofBijective _ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen
  have hb : r.1.1.base = (TopCat.isoOfHomeo e).hom := TopCat.ext fun _ => rfl
  have : IsIso r.1.1.base := by rw [hb]; infer_instance
  exact KLocallyRingedSpace.isIso_of_isIso_base_of_stalkMap_bijective r fun u =>
    KLocallyRingedSpace.bijective_stalkMap_restrictTo φ U V hUV u (hs u.1 u.2)

end AnalyticSpace

