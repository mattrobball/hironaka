/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Resolution.Defs
public import Hironaka.AnalyticSpace.HomExtDense
public import Hironaka.AnalyticSpace.Complexification
import Hironaka.AnalyticSpace.HomGlue
import Hironaka.AnalyticSpace.HomLocal
import Hironaka.AnalyticSpace.HomOfSections
import Hironaka.AnalyticSpace.IsoOverCover
import Hironaka.AnalyticSpace.IsoOverOpen
import Hironaka.AnalyticSpace.LiftRestrictStalk
import Hironaka.AnalyticSpace.RegPoints
import Hironaka.AnalyticSpace.RestrictToIso
import Hironaka.AnalyticSpace.SigmaLemmas
import Hironaka.AnalyticSpace.SncBoundaryChart
import Hironaka.AnalyticSpace.SncDivisorSetLocal
import Hironaka.Resolution.Analytic.Kol07Thm45.ClosedSubspaceHom
import Hironaka.Resolution.Analytic.Kol07Thm45.RestrictSetIncl
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Lifting local analytic isomorphisms to the resolutions

Włodarczyk's canonical desingularization is functorial with respect to local analytic
isomorphisms: "for any local analytic isomorphism `φ : Y' → Y` there is a natural lifting
`φ̃ : Ỹ' → Ỹ` which is a local analytic isomorphism" [Wlo09, Theorem 2.0.1 (3)]; for Kollár these
are the étale morphisms of his clause (5), "`R` commutes with smooth `K`-morphisms"
[Kol07, Theorem 45 (5)]. The lifting of isomorphisms between open subspaces of inputs (the unique
isomorphism `R(X')|_{Π⁻¹U'} ≅ R(X)|_{Π⁻¹V}` over `χ : X'|_{U'} ≅ X|_V`) is the only morphism over
`χ`, by rigidity, and extends to every local analytic isomorphism `φ : X' ⟶ X` between inputs by
gluing; these are the two clauses of `ResolutionAssignment.LiftsLocalIsomorphisms`
(`ResolutionAssignment.liftsLocalIsomorphisms_of_existsUnique_lift`):

* **Local lifts.** Around each point of `X'`, `φ` is an isomorphism `χ` of an open `U'` onto an
  open subspace `X|_V`; the lift `ψ₀` of `χ`, followed by the open immersion `R(X)|_{Π⁻¹V} → R(X)`,
  is a morphism `R(X')|_{Π⁻¹U'} → R(X)` over `φ`; the opens `Π⁻¹U'` cover `R(X')`.
* **Rigidity over `φ`** (`ResolutionAssignment.eq_of_comp_map_eq_of_isLocalIso`): two morphisms
  `h₁ h₂ : A → R(X)` from a non-singular space `A` over `X'` (through `p : A → X'` with
  `p⁻¹(Reg X')` dense) lying over `φ ∘ p` are equal. A local analytic isomorphism carries simple
  points to simple points (`Hom.IsLocalIso.mem_regularLocus`), so over `p⁻¹(Reg X')` both land in
  `Π⁻¹(Reg X)`, where `Π_X` is an isomorphism (clause (2)), and there both are the lift of
  `φ ∘ p` through `Π_X`; a morphism out of a non-singular space is determined on a dense open
  subset (`hom_ext_of_dense`, `Hironaka/AnalyticSpace/HomExtDense.lean`). The density of
  `Π⁻¹(Reg X')` in `R(X')` is clause (3): its complement is the support of a simple normal
  crossings divisor (`Hom.IsStrongResolution.dense_preimage_regularLocus`).
* **Gluing.** The local lifts agree on the overlaps by rigidity and glue
  (`KLocallyRingedSpace.glueOfCover`) to `ψ : R(X') → R(X)`, which lies over `φ` (equality of
  morphisms is local on the source), is a local analytic isomorphism (the local lifts are its
  restrictions), and is the only morphism over `φ`, by rigidity. The lift of an isomorphism
  `χ : X'|_{U'} ≅ X|_V` is likewise the only morphism over `χ`: composed with the inverse of
  another lift it lies over the identity of `X|_V`.
* **Restriction** (`LiftsLocalIsomorphisms.lift_restrict`): for every `R` lifting local analytic
  isomorphisms, the lift of `φ` restricts over every open `U'` which `φ` maps isomorphically onto
  an open subspace to the lift of that isomorphism, since the restriction lies over it and the lift
  is the only morphism over it.
* **Naturality** (`LiftsLocalIsomorphisms.lift_comp`, `lift_id`): the lift of a composite is the
  composite of the lifts and the lift of an identity is the identity, by the uniqueness; composites
  of local analytic isomorphisms are local analytic isomorphisms (`Hom.IsLocalIso.comp`), as are
  identities, isomorphisms and open immersions.

The sources state the clause and do not prove it in this form; the argument is the gluing of
[Kol07, Proposition 37, proof] with the uniqueness of [Kol07, Theorem 36, proof].
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Topology
open AnalyticSpace KLocallyRingedSpace

universe u w

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-! ### Local analytic isomorphisms -/

namespace Hom

variable {X' X : AnalyticSpace.{u} K}

/-- A local analytic isomorphism maps the open `U'` of its definition into the open `V`. -/
theorem IsLocalIso.mapsTo_of_comp_eq {φ : X' ⟶ X} {U' : Set X'} {V : Set X}
    {χ : X'.restrictSet U' ⟶ X.restrictSet V}
    (hχc : χ ≫ ofRestrict X.toKLocallyRingedSpace (openOf X V) =
      ofRestrict X'.toKLocallyRingedSpace (openOf X' U') ≫ φ) :
    ∀ a ∈ openOf X' U', KLocallyRingedSpace.Hom.toFun φ a ∈ openOf X V := by
  intro a ha
  have h := congrArg (fun ψ => KLocallyRingedSpace.Hom.toFun ψ
    (⟨a, ha⟩ : X'.toKLocallyRingedSpace.restrictOpen (openOf X' U'))) hχc
  change (KLocallyRingedSpace.Hom.toFun χ ⟨a, ha⟩).1 = KLocallyRingedSpace.Hom.toFun φ a at h
  rw [← h]
  exact (KLocallyRingedSpace.Hom.toFun χ ⟨a, ha⟩).2

/-- The isomorphism `χ` of the definition of a local analytic isomorphism is the restriction
`Hom.restrictTo` of `φ` (lifts through an open immersion are unique). -/
theorem IsLocalIso.eq_restrictTo {φ : X' ⟶ X} {U' : Set X'} {V : Set X}
    {χ : X'.restrictSet U' ⟶ X.restrictSet V}
    (hχc : χ ≫ ofRestrict X.toKLocallyRingedSpace (openOf X V) =
      ofRestrict X'.toKLocallyRingedSpace (openOf X' U') ≫ φ) :
    χ = KLocallyRingedSpace.Hom.restrictTo φ (openOf X' U') (openOf X V)
      (IsLocalIso.mapsTo_of_comp_eq hχc) :=
  KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict
    (hχc.trans (KLocallyRingedSpace.Hom.restrictTo_comp_ofRestrict φ _ _ _).symm)

/-- **A local analytic isomorphism has bijective stalk maps**: at `x'` it is the restriction of
`φ` to an open neighbourhood, an isomorphism onto an open subspace
(`bijective_stalkMap_of_isIso_restrictTo`). -/
theorem IsLocalIso.bijective_stalkMap {φ : X' ⟶ X} (hφ : φ.IsLocalIso) (x' : X') :
    Function.Bijective (φ.1.stalkMap x').hom := by
  obtain ⟨U', V, hU', hV, hx', χ, hχ, hχc⟩ := hφ x'
  have hχ' : CategoryTheory.IsIso χ := hχ
  have hK : CategoryTheory.IsIso (C := KLocallyRingedSpace.{u} K) χ :=
    isIso_toKLocallyRingedSpace_of_isIso χ
  have hx'' : x' ∈ openOf X' U' := by rw [openOf_of_isOpen X' hU']; exact hx'
  set p : X'.toKLocallyRingedSpace.restrictOpen (openOf X' U') := ⟨x', hx''⟩ with hp
  -- the stalk map of `χ` at `x'` is bijective, hence that of `ofRestrict ≫ φ`, hence that of `φ`
  have h1 : Function.Bijective (χ.1.stalkMap p).hom := bijective_stalkMap_of_isIso χ p
  have h2 := (bijective_stalkMap_iff_of_comp_eq χ
    (ofRestrict X'.toKLocallyRingedSpace (openOf X' U') ≫ φ) hχc p).mp h1
  have h3 := LocallyRingedSpace.stalkMap_comp (ofRestrict X'.toKLocallyRingedSpace (openOf X' U')).1
    φ.1 p
  change Function.Bijective (((ofRestrict X'.toKLocallyRingedSpace (openOf X' U')).1 ≫
    φ.1).stalkMap p).hom at h2
  rw [h3] at h2
  have ho : Function.Bijective
      ((ofRestrict X'.toKLocallyRingedSpace (openOf X' U')).1.stalkMap p).hom :=
    have := KLocallyRingedSpace.isIso_ofRestrict_stalkMap X'.toKLocallyRingedSpace (openOf X' U') p
    ConcreteCategory.bijective_of_isIso _
  exact (Function.Bijective.of_comp_iff' ho _).mp h2

/-- **A local analytic isomorphism carries simple points to simple points**: the stalk map at `x'`
is a ring isomorphism `𝒪_{X,φ x'} ≅ 𝒪_{X',x'}`, and regularity is invariant under ring
isomorphisms. -/
theorem IsLocalIso.mem_regularLocus {φ : X' ⟶ X} (hφ : φ.IsLocalIso) {x' : X'}
    (hx' : x' ∈ X'.regularLocus) : φ x' ∈ X.regularLocus := by
  have : IsRegularLocalRing (X'.presheaf.stalk x') := hx'
  exact IsRegularLocalRing.of_ringEquiv
    (RingEquiv.ofBijective (φ.1.stalkMap x').hom (hφ.bijective_stalkMap x')).symm

/-- At every point, a local analytic isomorphism `φ` restricts to an isomorphism of open
subspaces, in the form `Hom.restrictTo φ U' V` of the restriction. -/
theorem IsLocalIso.exists_isIso_restrictTo {φ : X' ⟶ X} (hφ : φ.IsLocalIso) (x' : X') :
    ∃ (U' : Opens X') (_ : x' ∈ U') (V : Opens X)
      (hUV : ∀ a ∈ U', KLocallyRingedSpace.Hom.toFun φ a ∈ V),
      CategoryTheory.IsIso (C := KLocallyRingedSpace.{u} K)
        (KLocallyRingedSpace.Hom.restrictTo φ U' V hUV) := by
  obtain ⟨U', V, hU', hV, hx', χ, hχ, hχc⟩ := hφ x'
  have hχ' : CategoryTheory.IsIso χ := hχ
  rw [IsLocalIso.eq_restrictTo hχc] at hχ'
  refine ⟨openOf X' U', by rw [openOf_of_isOpen X' hU']; exact hx', openOf X V,
    IsLocalIso.mapsTo_of_comp_eq hχc,
    isIso_toKLocallyRingedSpace_of_isIso (Y := X'.restrictSet U') (Z := X.restrictSet V) _⟩

/-- **Composites of local analytic isomorphisms are local analytic isomorphisms**: at `x`, with
`U₁ ∋ x` and `U₂ ∋ φ₁ x` the injectivity opens of `φ₁` and `φ₂`, the composite maps the open
`U := U₁ ∩ φ₁⁻¹U₂` bijectively onto the open `φ₂(φ₁(U))` with bijective stalk maps, so it
restricts to an isomorphism there (`isIso_restrictTo_of_bijOn_of_bijective_stalkMap`). -/
theorem IsLocalIso.comp {X'' : AnalyticSpace.{u} K} {φ₁ : X'' ⟶ X'} {φ₂ : X' ⟶ X}
    (h₁ : φ₁.IsLocalIso) (h₂ : φ₂.IsLocalIso) : (φ₁ ≫ φ₂).IsLocalIso := by
  intro x
  obtain ⟨U₁, hxU₁, V₁, hUV₁, hi₁⟩ := h₁.exists_isIso_restrictTo x
  obtain ⟨U₂, hxU₂, V₂, hUV₂, hi₂⟩ :=
    h₂.exists_isIso_restrictTo (KLocallyRingedSpace.Hom.toFun φ₁ x)
  set f₁ := KLocallyRingedSpace.Hom.toFun φ₁ with hf₁
  set f₂ := KLocallyRingedSpace.Hom.toFun φ₂ with hf₂
  have hf₁c : Continuous f₁ := KLocallyRingedSpace.Hom.continuous_toFun φ₁
  -- the open `U` and its image `V`
  set U : Set X'' := (U₁ : Set X'') ∩ f₁ ⁻¹' (U₂ : Set X') with hU
  have hUo : IsOpen U := U₁.isOpen.inter (U₂.isOpen.preimage hf₁c)
  have hV₁o : IsOpen (f₁ '' U) := by
    have := KLocallyRingedSpace.isOpen_image_of_isIso_restrictTo φ₁ U₁ V₁ hUV₁
      (U₂.isOpen.preimage hf₁c)
    rwa [Set.inter_comm] at this
  have hsub : f₁ '' U ∩ (U₂ : Set X') = f₁ '' U :=
    Set.inter_eq_left.mpr (by rintro _ ⟨u, hu, rfl⟩; exact hu.2)
  have hVo : IsOpen (f₂ '' (f₁ '' U)) := by
    have := KLocallyRingedSpace.isOpen_image_of_isIso_restrictTo φ₂ U₂ V₂ hUV₂ hV₁o
    rwa [hsub] at this
  set V : Set X := f₂ '' (f₁ '' U) with hV
  refine ⟨U, V, hUo, hVo, ⟨hxU₁, hxU₂⟩, ?_⟩
  -- the point-level criterion for the restriction of the composite
  have hcomp : ∀ a, KLocallyRingedSpace.Hom.toFun (φ₁ ≫ φ₂) a = f₂ (f₁ a) := fun _ => rfl
  have hmaps : ∀ a ∈ openOf X'' U, KLocallyRingedSpace.Hom.toFun (φ₁ ≫ φ₂) a ∈ openOf X V := by
    intro a ha
    rw [openOf_of_isOpen _ hUo] at ha
    rw [openOf_of_isOpen _ hVo, hcomp]
    exact ⟨f₁ a, ⟨a, ha, rfl⟩, rfl⟩
  have hbij : Set.BijOn (KLocallyRingedSpace.Hom.toFun (φ₁ ≫ φ₂)) (openOf X'' U) (openOf X V) := by
    rw [openOf_of_isOpen _ hUo, openOf_of_isOpen _ hVo]
    have h1inj := KLocallyRingedSpace.injOn_toFun_of_isIso_restrictTo φ₁ U₁ V₁ hUV₁
    have h2inj := KLocallyRingedSpace.injOn_toFun_of_isIso_restrictTo φ₂ U₂ V₂ hUV₂
    refine ⟨fun a ha => ⟨f₁ a, ⟨a, ha, rfl⟩, rfl⟩, fun a ha b hb hab => ?_, ?_⟩
    · rw [hcomp, hcomp] at hab
      exact h1inj ha.1 hb.1 (h2inj ha.2 hb.2 hab)
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
  have hs : ∀ a ∈ openOf X'' U, Function.Bijective ((φ₁ ≫ φ₂).1.stalkMap a).hom := by
    intro a _
    have hc := LocallyRingedSpace.stalkMap_comp φ₁.1 φ₂.1 a
    change Function.Bijective ((φ₁.1 ≫ φ₂.1).stalkMap a).hom
    rw [hc]
    exact (h₁.bijective_stalkMap a).comp (h₂.bijective_stalkMap _)
  have hiso := isIso_restrictTo_of_bijOn_of_bijective_stalkMap (φ₁ ≫ φ₂) (openOf X'' U)
    (openOf X V) hmaps hbij hs
  exact ⟨KLocallyRingedSpace.Hom.restrictTo (φ₁ ≫ φ₂) (openOf X'' U) (openOf X V) hmaps,
    isIso_of_isIso_toKLocallyRingedSpace _ hiso,
    KLocallyRingedSpace.Hom.restrictTo_comp_ofRestrict _ _ _ _⟩

/-- The identity is a local analytic isomorphism. -/
theorem isLocalIso_id (X : AnalyticSpace.{u} K) : (𝟙 X : X ⟶ X).IsLocalIso := by
  intro x
  refine ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ, Set.mem_univ x, 𝟙 _,
    (CategoryTheory.IsIso.id _ : CategoryTheory.IsIso (𝟙 (X.restrictSet Set.univ))), ?_⟩
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end Hom

/-- **The preimage of the simple locus under a strong resolution is dense**: its complement is
the support of a simple normal crossings divisor (`isSncDivisorSet_of_isSncBoundary`,
`IsSncDivisorSet.dense_compl`). -/
theorem Hom.IsStrongResolution.dense_preimage_regularLocus {X R : AnalyticSpace.{u} K} {π : R ⟶ X}
    (h : π.IsStrongResolution) : Dense (π ⁻¹' X.regularLocus) := by
  obtain ⟨E, hE, hsupp⟩ := h.exists_isSncBoundary_preimage
  have hd := (ClosedSubspace.isSncDivisorSet_of_isSncBoundary E hE).dense_compl
  rw [hsupp] at hd
  simpa [singularLocus, Set.preimage_compl] using hd

namespace ResolutionAssignment

variable {C : Type w} [HasUnderlyingSpace.{u, w} C K] {R : ResolutionAssignment C}

/-! ### Rigidity over a local analytic isomorphism -/

/-- **Rigidity over `φ`**: for a local analytic isomorphism `φ : X' ⟶ X` and `Π_X` an isomorphism
over the simple locus, two morphisms `h₁ h₂ : A ⟶ R(X)` from a non-singular space `A` over `X'`
(through `p`, with `p⁻¹(Reg X')` dense) that lie over `φ ∘ p` are equal: over `p⁻¹(Reg X')` both
land in `Π⁻¹(Reg X)` (`Hom.IsLocalIso.mem_regularLocus`) and are the lift of `φ ∘ p` through the
isomorphism `Π_X|_{Reg X}`, so they agree on a dense open subset (`hom_ext_of_dense`). -/
theorem eq_of_comp_map_eq_of_isLocalIso {X' : AnalyticSpace.{u} K} {T : C}
    (hX : (R.map T).IsIsoOver (toAnalyticSpace T).regularLocus) {φ : X' ⟶ toAnalyticSpace T}
    (hφ : φ.IsLocalIso) {A : AnalyticSpace.{u} K} (hA : A.IsNonsingular) (p : A ⟶ X')
    (hp : Dense (p ⁻¹' X'.regularLocus)) (h₁ h₂ : A ⟶ R.space T)
    (e₁ : h₁ ≫ R.map T = p ≫ φ) (e₂ : h₂ ≫ R.map T = p ≫ φ) : h₁ = h₂ := by
  let X : AnalyticSpace.{u} K := toAnalyticSpace T
  -- the `K`-level readings of the data
  let piK : (R.space T).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace := R.map T
  let φK : X'.toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace := φ
  let pK : A.toKLocallyRingedSpace ⟶ X'.toKLocallyRingedSpace := p
  let h₁K : A.toKLocallyRingedSpace ⟶ (R.space T).toKLocallyRingedSpace := h₁
  let h₂K : A.toKLocallyRingedSpace ⟶ (R.space T).toKLocallyRingedSpace := h₂
  have e₁K : h₁K ≫ piK = pK ≫ φK := e₁
  have e₂K : h₂K ≫ piK = pK ≫ φK := e₂
  have hpc : Continuous (KLocallyRingedSpace.Hom.toFun pK) :=
    KLocallyRingedSpace.Hom.continuous_toFun pK
  set D : Opens A := ⟨KLocallyRingedSpace.Hom.toFun pK ⁻¹' X'.regularLocus,
    (isOpen_reg X').preimage hpc⟩ with hD
  refine hom_ext_of_dense hA D hp h₁ h₂ ?_
  change ofRestrict A.toKLocallyRingedSpace D ≫ h₁K = ofRestrict A.toKLocallyRingedSpace D ≫ h₂K
  -- both restrictions land in `Π⁻¹(Reg X)`
  set RegX : Opens (R.space T) :=
    openOf (R.space T) (KLocallyRingedSpace.Hom.toFun piK ⁻¹' X.regularLocus) with hRegX
  have hopen : IsOpen (KLocallyRingedSpace.Hom.toFun piK ⁻¹' X.regularLocus) :=
    (isOpen_reg X).preimage (KLocallyRingedSpace.Hom.continuous_toFun piK)
  have hland : ∀ h : A.toKLocallyRingedSpace ⟶ (R.space T).toKLocallyRingedSpace,
      h ≫ piK = pK ≫ φK → ∀ d : A.toKLocallyRingedSpace.restrictOpen D,
        KLocallyRingedSpace.Hom.toFun (ofRestrict A.toKLocallyRingedSpace D ≫ h) d ∈ RegX := by
    intro h e d
    rw [hRegX, openOf_of_isOpen _ hopen]
    change KLocallyRingedSpace.Hom.toFun piK (KLocallyRingedSpace.Hom.toFun h d.1) ∈
      X.regularLocus
    have := congrArg (fun ψ => KLocallyRingedSpace.Hom.toFun ψ d.1) e
    change KLocallyRingedSpace.Hom.toFun piK (KLocallyRingedSpace.Hom.toFun h d.1) =
      KLocallyRingedSpace.Hom.toFun φK (KLocallyRingedSpace.Hom.toFun pK d.1) at this
    rw [this]
    exact hφ.mem_regularLocus d.2
  set l₁ := KLocallyRingedSpace.Hom.liftRestrict (ofRestrict A.toKLocallyRingedSpace D ≫ h₁K)
    RegX (hland h₁K e₁K) with hl₁
  set l₂ := KLocallyRingedSpace.Hom.liftRestrict (ofRestrict A.toKLocallyRingedSpace D ≫ h₂K)
    RegX (hland h₂K e₂K) with hl₂
  have hc₁ : l₁ ≫ ofRestrict (R.space T).toKLocallyRingedSpace RegX =
      ofRestrict A.toKLocallyRingedSpace D ≫ h₁K :=
    KLocallyRingedSpace.Hom.liftRestrict_comp_ofRestrict _ _ _
  have hc₂ : l₂ ≫ ofRestrict (R.space T).toKLocallyRingedSpace RegX =
      ofRestrict A.toKLocallyRingedSpace D ≫ h₂K :=
    KLocallyRingedSpace.Hom.liftRestrict_comp_ofRestrict _ _ _
  -- the lifts agree after the isomorphism `Π_X|_{Reg X}` (the `K`-level view `restrictSetTo`)
  have hiso : CategoryTheory.IsIso (C := KLocallyRingedSpace.{u} K)
      (Hom.restrictSetTo piK X.regularLocus) :=
    isIso_toKLocallyRingedSpace_of_isIso _ (h := hX)
  have hl : l₁ ≫ Hom.restrictSetTo piK X.regularLocus =
      l₂ ≫ Hom.restrictSetTo piK X.regularLocus := by
    apply KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict
    rw [Category.assoc, Category.assoc, Hom.restrictSetTo_comp_ofRestrict, ← Category.assoc, hc₁,
      ← Category.assoc, hc₂, Category.assoc, Category.assoc, e₁K, e₂K]
  have hl' : l₁ = l₂ := (cancel_mono _).mp hl
  rw [← hc₁, ← hc₂, hl']

/-- **Rigidity over an open subspace**: for `Π_T` a strong resolution, the only endomorphism `h`
of `R(T)|_{Π⁻¹V}` over the identity of `T|_V` (`h ≫ Π_T|_V = Π_T|_V`) is the identity: `h`
followed by the inclusion into `R(T)` and the inclusion itself lie over the identity of `T`, and
their source `R(T)|_{Π⁻¹V}` is non-singular (`eq_of_comp_map_eq_of_isLocalIso`). -/
theorem eq_id_of_comp_restrictSet_eq {T : C} (hT : (R.map T).IsStrongResolution)
    {V : Set (toAnalyticSpace T)}
    (h : (R.space T).restrictSet (R.map T ⁻¹' V) ⟶ (R.space T).restrictSet (R.map T ⁻¹' V))
    (hc : h ≫ (R.map T).restrictSet V = (R.map T).restrictSet V) : h = 𝟙 _ := by
  -- the `K`-level readings of the data
  let piK : (R.space T).toKLocallyRingedSpace ⟶ (toAnalyticSpace T).toKLocallyRingedSpace :=
    R.map T
  let idK : (toAnalyticSpace T).toKLocallyRingedSpace ⟶ (toAnalyticSpace T).toKLocallyRingedSpace :=
    𝟙 (toAnalyticSpace T)
  let B : Opens (R.space T) := openOf (R.space T) (KLocallyRingedSpace.Hom.toFun piK ⁻¹' V)
  let hK : (R.space T).toKLocallyRingedSpace.restrictOpen B ⟶
    (R.space T).toKLocallyRingedSpace.restrictOpen B := h
  have hcK : hK ≫ Hom.restrictSetTo piK V = Hom.restrictSetTo piK V := hc
  let incl : (R.space T).toKLocallyRingedSpace.restrictOpen B ⟶ (R.space T).toKLocallyRingedSpace :=
    ofRestrict (R.space T).toKLocallyRingedSpace B
  let pK : (R.space T).toKLocallyRingedSpace.restrictOpen B ⟶
    (toAnalyticSpace T).toKLocallyRingedSpace := incl ≫ piK
  let h₁ : (R.space T).toKLocallyRingedSpace.restrictOpen B ⟶ (R.space T).toKLocallyRingedSpace :=
    hK ≫ incl
  -- `h ≫ incl` and `incl` lie over the identity of `T`
  have e₁ : h₁ ≫ piK = pK ≫ idK := by
    change (hK ≫ ofRestrict _ B) ≫ piK = (ofRestrict _ B ≫ piK) ≫ 𝟙 _
    rw [Category.comp_id, Category.assoc, ← Hom.restrictSetTo_comp_ofRestrict piK V,
      ← Category.assoc, hcK]
  have e₂ : incl ≫ piK = pK ≫ idK := (Category.comp_id _).symm
  have := eq_of_comp_map_eq_of_isLocalIso (R := R) (T := T) (X' := toAnalyticSpace T)
    hT.isIsoOver_regularLocus (Hom.isLocalIso_id (toAnalyticSpace T))
    (A := AnalyticSpace.restrictOpen (R.space T) B) (isNonsingular_restrictOpen hT.isNonsingular B)
    pK (dense_preimage_toFun_ofRestrict _ B hT.dense_preimage_regularLocus) h₁ incl e₁ e₂
  exact KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict (this.trans (Category.id_comp _).symm)

/-! ### The glued lift -/

/-- **Lifting local analytic isomorphisms from the lifting of isomorphisms of open subspaces**
([Wlo09, Theorem 2.0.1 (3)] from clause (5) of [Kol07, Theorem 45]): a resolution assignment `R`
on inputs whose values are strong resolutions and which lifts every isomorphism between open
subspaces of inputs to exactly one isomorphism over it (`h5`) lifts local analytic isomorphisms
(`LiftsLocalIsomorphisms`). The lift of an isomorphism `φ` of open subspaces is the only morphism
over `φ`: for another one `ψ'`, the composite `ψ⁻¹ ≫ ψ'` lies over the identity, hence is the
identity by rigidity (`eq_of_comp_map_eq_of_isLocalIso`). For a local analytic isomorphism, the
local lifts of `h5`, one for each point of `X'`, agree on the overlaps by rigidity over `φ` and
glue (`KLocallyRingedSpace.glueOfCover`); the glued morphism lies over `φ`, is a local analytic
isomorphism and is unique, by rigidity. -/
theorem liftsLocalIsomorphisms_of_existsUnique_lift
    (h5 : ∀ (X Y : C) (U : Set (toAnalyticSpace X)) (V : Set (toAnalyticSpace Y)),
      IsOpen U → IsOpen V →
      ∀ φ : (toAnalyticSpace X).restrictSet U ⟶ (toAnalyticSpace Y).restrictSet V, IsIso φ →
        ∃! ψ : (R.space X).restrictSet (R.map X ⁻¹' U) ⟶ (R.space Y).restrictSet (R.map Y ⁻¹' V),
          IsIso ψ ∧ ψ ≫ (R.map Y).restrictSet V = (R.map X).restrictSet U ≫ φ)
    (hres : ∀ X : C, (R.map X).IsStrongResolution) : R.LiftsLocalIsomorphisms := by
  refine ⟨fun X Y U V hU hV φ hφ => ?_, fun T' T φ hφ => ?_⟩
  · obtain ⟨ψ, ⟨hψ, hψc⟩, -⟩ := h5 X Y U V hU hV φ hφ
    refine ⟨ψ, hψ, fun ψ' => ⟨fun hψ'c => ?_, fun h => h ▸ hψc⟩⟩
    -- `ψ⁻¹ ≫ ψ'` lies over the identity of `Y|_V`, hence is the identity
    have : CategoryTheory.IsIso ψ := hψ
    have h := eq_id_of_comp_restrictSet_eq (hres Y) (inv ψ ≫ ψ')
      (by rw [Category.assoc, hψ'c, ← hψc, IsIso.inv_hom_id_assoc])
    rw [← IsIso.hom_inv_id_assoc ψ ψ', h, Category.comp_id]
  let X' : AnalyticSpace.{u} K := toAnalyticSpace T'
  let X : AnalyticSpace.{u} K := toAnalyticSpace T
  have hR' : (R.space T').IsNonsingular := (hres T').isNonsingular
  have hXreg : (R.map T).IsIsoOver X.regularLocus := (hres T).isIsoOver_regularLocus
  -- the `K`-level readings of the data
  let piK : (R.space T).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace := R.map T
  let pi'K : (R.space T').toKLocallyRingedSpace ⟶ X'.toKLocallyRingedSpace := R.map T'
  let φK : X'.toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace := φ
  have hdense : Dense (KLocallyRingedSpace.Hom.toFun pi'K ⁻¹' X'.regularLocus) :=
    (hres T').dense_preimage_regularLocus
  -- the local data of `φ` at each point and the lifts of clause (5)
  have hφ' := hφ
  choose U' V hU' hV hxU' χ hχ hχc using hφ'
  choose ψ₀ hψ₀ using fun x' => h5 T' T (U' x') (V x') (hU' x') (hV x') (χ x') (hχ x')
  let χK : ∀ x', X'.toKLocallyRingedSpace.restrictOpen (openOf X' (U' x')) ⟶
    X.toKLocallyRingedSpace.restrictOpen (openOf X (V x')) := fun x' => χ x'
  have hχcK : ∀ x', χK x' ≫ ofRestrict X.toKLocallyRingedSpace (openOf X (V x')) =
      ofRestrict X'.toKLocallyRingedSpace (openOf X' (U' x')) ≫ φK := hχc
  -- the cover of `R(X')` by the preimages of the `U'`
  set A : X' → Opens (R.space T') := fun x' =>
    openOf (R.space T') (KLocallyRingedSpace.Hom.toFun pi'K ⁻¹' U' x') with hA
  have hAopen : ∀ x', IsOpen (KLocallyRingedSpace.Hom.toFun pi'K ⁻¹' U' x') := fun x' =>
    (hU' x').preimage (KLocallyRingedSpace.Hom.continuous_toFun pi'K)
  have hAeq : ∀ x', A x' = ⟨_, hAopen x'⟩ := fun x' => openOf_of_isOpen _ (hAopen x')
  have hcov : ∀ a : R.space T', ∃ x', a ∈ A x' := fun a => by
    refine ⟨KLocallyRingedSpace.Hom.toFun pi'K a, ?_⟩
    rw [hAeq]
    exact hxU' _
  let B : X' → Opens (R.space T) := fun x' =>
    openOf (R.space T) (KLocallyRingedSpace.Hom.toFun piK ⁻¹' V x')
  let ψK : ∀ x', (R.space T').toKLocallyRingedSpace.restrictOpen (A x') ⟶
    (R.space T).toKLocallyRingedSpace.restrictOpen (B x') := fun x' => ψ₀ x'
  have hψKc : ∀ x', ψK x' ≫ Hom.restrictSetTo piK (V x') = Hom.restrictSetTo pi'K (U' x') ≫ χK x' :=
    fun x' => (hψ₀ x').1.2
  -- the local lifts into `R(X)`, over `φ`
  let g : ∀ x', (R.space T').toKLocallyRingedSpace.restrictOpen (A x') ⟶
      (R.space T).toKLocallyRingedSpace := fun x' =>
    ψK x' ≫ ofRestrict (R.space T).toKLocallyRingedSpace (B x')
  have hgover : ∀ x', g x' ≫ piK = ofRestrict (R.space T').toKLocallyRingedSpace (A x') ≫
      pi'K ≫ φK := by
    intro x'
    change (ψK x' ≫ ofRestrict (R.space T).toKLocallyRingedSpace (B x')) ≫ piK = _
    rw [Category.assoc, ← Hom.restrictSetTo_comp_ofRestrict piK (V x'), ← Category.assoc, hψKc x',
      Category.assoc, hχcK x', ← Category.assoc, Hom.restrictSetTo_comp_ofRestrict pi'K (U' x'),
      Category.assoc]
  -- rigidity over `φ` on the open subspaces of `R(X')`
  have hrigid : ∀ (W : Opens (R.space T'))
      (h₁ h₂ : (R.space T').toKLocallyRingedSpace.restrictOpen W ⟶
        (R.space T).toKLocallyRingedSpace),
      h₁ ≫ piK = ofRestrict (R.space T').toKLocallyRingedSpace W ≫ pi'K ≫ φK →
      h₂ ≫ piK = ofRestrict (R.space T').toKLocallyRingedSpace W ≫ pi'K ≫ φK → h₁ = h₂ := by
    intro W h₁ h₂ e₁ e₂
    exact eq_of_comp_map_eq_of_isLocalIso hXreg hφ (A := AnalyticSpace.restrictOpen (R.space T') W)
      (isNonsingular_restrictOpen hR' W)
      (ofRestrict (R.space T').toKLocallyRingedSpace W ≫ pi'K)
      (dense_preimage_toFun_ofRestrict (R.space T').toKLocallyRingedSpace W hdense) h₁ h₂
      (e₁.trans (Category.assoc _ _ _).symm) (e₂.trans (Category.assoc _ _ _).symm)
  -- the local lifts are compatible on the overlaps and glue
  have hcompat : KLocallyRingedSpace.GlueCompatible A g := by
    intro i j
    refine hrigid (A i ⊓ A j) _ _ ?_ ?_
    · rw [Category.assoc, hgover i, ← Category.assoc,
        KLocallyRingedSpace.restrictIncl_comp_ofRestrict]
    · rw [Category.assoc, hgover j, ← Category.assoc,
        KLocallyRingedSpace.restrictIncl_comp_ofRestrict]
  let Φ : (R.space T').toKLocallyRingedSpace ⟶ (R.space T).toKLocallyRingedSpace :=
    KLocallyRingedSpace.glueOfCover A g hcov hcompat
  have hΦg : ∀ x', ofRestrict (R.space T').toKLocallyRingedSpace (A x') ≫ Φ = g x' := fun x' =>
    KLocallyRingedSpace.ofRestrict_comp_glueOfCover A g hcov hcompat x'
  -- the glued morphism lies over `φ`
  have hΦover : Φ ≫ piK = pi'K ≫ φK := by
    refine KLocallyRingedSpace.hom_ext_of_cover _ _ A hcov fun x' => ?_
    rw [← Category.assoc, hΦg x', hgover x']
  refine ⟨Φ, ?_, fun ψ' => ⟨fun hψ' => ?_, fun h => h ▸ hΦover⟩⟩
  · -- a local analytic isomorphism: over `A x'` it is the lift `ψ₀ x'`
    intro a
    obtain ⟨x', hax'⟩ := hcov a
    have hmem : a ∈ KLocallyRingedSpace.Hom.toFun pi'K ⁻¹' U' x' := by
      rw [hAeq] at hax'
      exact hax'
    exact ⟨KLocallyRingedSpace.Hom.toFun pi'K ⁻¹' U' x', KLocallyRingedSpace.Hom.toFun piK ⁻¹' V x',
      hAopen x', (hV x').preimage (KLocallyRingedSpace.Hom.continuous_toFun piK), hmem, ψ₀ x',
      (hψ₀ x').1.1, (hΦg x').symm⟩
  · -- uniqueness among the morphisms over `φ`
    exact eq_of_comp_map_eq_of_isLocalIso hXreg hφ hR' (R.map T')
      (hres T').dense_preimage_regularLocus ψ' Φ hψ' hΦover

/-! ### Naturality -/

/-- **The lifts respect composition**: for `R` lifting local analytic isomorphisms, the lift of a
composite `φ₁ ≫ φ₂` of local analytic isomorphisms between inputs is the composite of the lifts, by
the uniqueness of the lift. -/
theorem LiftsLocalIsomorphisms.lift_comp (hR : R.LiftsLocalIsomorphisms) {X'' X' X : C}
    (φ₁ : toAnalyticSpace X'' ⟶ toAnalyticSpace X') (φ₂ : toAnalyticSpace X' ⟶ toAnalyticSpace X)
    (h₁₂ : (φ₁ ≫ φ₂).IsLocalIso)
    (ψ₁ : R.space X'' ⟶ R.space X') (ψ₂ : R.space X' ⟶ R.space X)
    (hc₁ : ψ₁ ≫ R.map X' = R.map X'' ≫ φ₁) (hc₂ : ψ₂ ≫ R.map X = R.map X' ≫ φ₂)
    (ψ : R.space X'' ⟶ R.space X) (hc : ψ ≫ R.map X = R.map X'' ≫ φ₁ ≫ φ₂) :
    ψ = ψ₁ ≫ ψ₂ := by
  obtain ⟨ψ₀, -, hlift⟩ := hR.exists_lift_of_isLocalIso X'' X (φ₁ ≫ φ₂) h₁₂
  have huniq := fun ψ' => (hlift ψ').1
  refine (huniq ψ hc).trans (huniq (ψ₁ ≫ ψ₂) ?_).symm
  rw [Category.assoc, hc₂, ← Category.assoc, hc₁, Category.assoc]

/-- **The lifts respect identities**: for `R` lifting local analytic isomorphisms, the lift of the
identity of an input is the identity. -/
theorem LiftsLocalIsomorphisms.lift_id (hR : R.LiftsLocalIsomorphisms) {X : C}
    (ψ : R.space X ⟶ R.space X) (hc : ψ ≫ R.map X = R.map X) : ψ = 𝟙 _ := by
  obtain ⟨ψ₀, -, hlift⟩ := hR.exists_lift_of_isLocalIso X X (𝟙 _) (Hom.isLocalIso_id _)
  have huniq := fun ψ' => (hlift ψ').1
  exact (huniq ψ (hc.trans (Category.comp_id _).symm)).trans
    (huniq (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)).symm

/-! ### Restriction to the lifts of isomorphisms of open subspaces -/

/-- **The lift of a local analytic isomorphism restricts to the lifts of isomorphisms of open
subspaces**: for `R` lifting local analytic isomorphisms and a morphism `ψ : R(X') → R(X)` over
`φ : X' → X` (such as the lift of a local analytic isomorphism `φ`), over every open `U' ⊆ X'`
which `φ` maps isomorphically onto an open subspace `X|_V` (through `χ`), every morphism
`ψ₀ : R(X')|_{Π⁻¹U'} → R(X)|_{Π⁻¹V}` over `χ`, in particular the lift of `χ`, is the restriction
of `ψ`: the restriction of `ψ` lies over `χ`, and the lift of `χ` is the only morphism over it. -/
theorem LiftsLocalIsomorphisms.lift_restrict (hR : R.LiftsLocalIsomorphisms) {X' X : C}
    {φ : toAnalyticSpace X' ⟶ toAnalyticSpace X} {ψ : R.space X' ⟶ R.space X}
    (hψ : ψ ≫ R.map X = R.map X' ≫ φ) {U' : Set (toAnalyticSpace X')}
    {V : Set (toAnalyticSpace X)} (hU' : IsOpen U') (hV : IsOpen V)
    (χ : (toAnalyticSpace X').restrictSet U' ⟶ (toAnalyticSpace X).restrictSet V) (hχ : IsIso χ)
    (hχc : χ ≫ ofRestrict (toAnalyticSpace X).toKLocallyRingedSpace (openOf (toAnalyticSpace X) V) =
      ofRestrict (toAnalyticSpace X').toKLocallyRingedSpace (openOf (toAnalyticSpace X') U') ≫ φ)
    (ψ₀ : (R.space X').restrictSet (R.map X' ⁻¹' U') ⟶ (R.space X).restrictSet (R.map X ⁻¹' V))
    (hψ₀ : ψ₀ ≫ (R.map X).restrictSet V = (R.map X').restrictSet U' ≫ χ) :
    ψ₀ ≫ ofRestrict (R.space X).toKLocallyRingedSpace (openOf (R.space X) (R.map X ⁻¹' V)) =
      ofRestrict (R.space X').toKLocallyRingedSpace (openOf (R.space X') (R.map X' ⁻¹' U')) ≫
        ψ := by
  -- the `K`-level readings of the data
  let piK : (R.space X).toKLocallyRingedSpace ⟶ (toAnalyticSpace X).toKLocallyRingedSpace :=
    R.map X
  let pi'K : (R.space X').toKLocallyRingedSpace ⟶ (toAnalyticSpace X').toKLocallyRingedSpace :=
    R.map X'
  let φK : (toAnalyticSpace X').toKLocallyRingedSpace ⟶ (toAnalyticSpace X).toKLocallyRingedSpace :=
    φ
  let ψK : (R.space X').toKLocallyRingedSpace ⟶ (R.space X).toKLocallyRingedSpace := ψ
  let χK : (toAnalyticSpace X').toKLocallyRingedSpace.restrictOpen
      (openOf (toAnalyticSpace X') U') ⟶
      (toAnalyticSpace X).toKLocallyRingedSpace.restrictOpen (openOf (toAnalyticSpace X) V) := χ
  have hψK : ψK ≫ piK = pi'K ≫ φK := hψ
  have hχcK : χK ≫ ofRestrict (toAnalyticSpace X).toKLocallyRingedSpace
      (openOf (toAnalyticSpace X) V) =
      ofRestrict (toAnalyticSpace X').toKLocallyRingedSpace (openOf (toAnalyticSpace X') U') ≫ φK :=
    hχc
  -- `ψ` maps `Π⁻¹U'` into `Π⁻¹V`
  have hmaps : ∀ a ∈ openOf (R.space X') (KLocallyRingedSpace.Hom.toFun pi'K ⁻¹' U'),
      KLocallyRingedSpace.Hom.toFun ψK a ∈
        openOf (R.space X) (KLocallyRingedSpace.Hom.toFun piK ⁻¹' V) := by
    intro a ha
    rw [openOf_of_isOpen _ (hU'.preimage (KLocallyRingedSpace.Hom.continuous_toFun pi'K))] at ha
    rw [openOf_of_isOpen _ (hV.preimage (KLocallyRingedSpace.Hom.continuous_toFun piK))]
    have h := congrArg (fun f => KLocallyRingedSpace.Hom.toFun f a) hψK
    change KLocallyRingedSpace.Hom.toFun piK (KLocallyRingedSpace.Hom.toFun ψK a) =
      KLocallyRingedSpace.Hom.toFun φK (KLocallyRingedSpace.Hom.toFun pi'K a) at h
    change KLocallyRingedSpace.Hom.toFun piK (KLocallyRingedSpace.Hom.toFun ψK a) ∈ V
    have hφa := Hom.IsLocalIso.mapsTo_of_comp_eq hχc (KLocallyRingedSpace.Hom.toFun pi'K a)
      (by rw [openOf_of_isOpen _ hU']; exact ha)
    rw [openOf_of_isOpen _ hV] at hφa
    rw [h]
    exact hφa
  -- the restriction of `ψ` lies over `χ`, so it is the lift of `χ`, and so is `ψ₀`
  let ψr := KLocallyRingedSpace.Hom.restrictTo ψK _ _ hmaps
  have hψr : ψr ≫ ofRestrict (R.space X).toKLocallyRingedSpace
      (openOf (R.space X) (KLocallyRingedSpace.Hom.toFun piK ⁻¹' V)) =
      ofRestrict (R.space X').toKLocallyRingedSpace
        (openOf (R.space X') (KLocallyRingedSpace.Hom.toFun pi'K ⁻¹' U')) ≫ ψK :=
    KLocallyRingedSpace.Hom.restrictTo_comp_ofRestrict _ _ _ _
  have hover : ψr ≫ Hom.restrictSetTo piK V = Hom.restrictSetTo pi'K U' ≫ χK := by
    apply KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict
    rw [Category.assoc, Hom.restrictSetTo_comp_ofRestrict, ← Category.assoc, hψr, Category.assoc,
      hψK, Category.assoc, hχcK, Hom.restrictSetTo_comp_ofRestrict_assoc]
  obtain ⟨ψ₁, -, hlift⟩ := hR.exists_lift_of_isIso X' X U' V hU' hV χ hχ
  have huniq := fun ψ' => (hlift ψ').1
  have h₀ : ψ₀ = ψr := (huniq ψ₀ hψ₀).trans (huniq ψr hover).symm
  rw [h₀]
  exact hψr

end ResolutionAssignment

end AnalyticSpace
