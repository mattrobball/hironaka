/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.HomGlue
public import Hironaka.AnalyticSpace.IsoOverOpen
import Hironaka.AnalyticSpace.Glue.GlueIsoOver
import Hironaka.AnalyticSpace.HomLocal
import Hironaka.AnalyticSpace.Manifold.Restrict
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The restriction to a subset under nesting, and gluing over a base

For the open subspace `X.restrictSet S = X.restrictOpen (openOf X S)` (Hironaka's `X | U`
[Hir64, Ch. 0, §1, p. 120] with the convention `openOf` for non-open sets) and an open `T ⊆ S`:

* the inclusion `restrictSetIncl : X | T ⟶ X | S` (the `K`-level `restrictIncl` of
  `Hironaka/AnalyticSpace/HomGlue.lean` at `openOf X T ≤ openOf X S`), over `X`
  (`restrictSetIncl_comp_ofRestrict`) and the identity on points (`toFun_restrictSetIncl`), a
  monomorphism, composing as inclusions do;
* the restriction of a restriction `(X | S) | (T ∩ S) ≅ X | T` (`restrictSet_restrictSet_iso`,
  Mathlib's universal property of open immersions through `isoOfRangeEq`), and the isomorphism
  followed by the inclusion is the open immersion of the piece
  (`restrictSet_restrictSet_iso_hom_comp`);
* the restriction of a morphism is natural for the inclusions (`restrictSet_comp_restrictSetIncl`)
  and for the restriction-of-a-restriction isomorphisms of nested opens; equal sets give
  identified restrictions (`restrictSet_congr_iso`), over `X`.

**Gluing over a base.** For morphisms `f : A ⟶ Z`, `g : B ⟶ Z` of analytic `K`-spaces, in the
`K`-level view `Hom.restrictSetTo` of the restriction (which is `Hom.restrictSet`,
`Hom.restrictSetTo_eq_restrictSet`; kept so that every object is a `restrictOpen` of a
`K`-local-ringed space and every morphism a `K`-morphism, and the library's gluing of morphisms
along an open cover, `glueOfCover` of `Hironaka/AnalyticSpace/HomGlue.lean` and `hom_ext_of_cover`
of `Hironaka/AnalyticSpace/HomLocal.lean`, applies as it stands): given uniqueness of the morphisms
`A | f⁻¹N ⟶ B | g⁻¹N` over `Z | N` for every open `N` (`Hom.UniqueOver`), local morphisms over the
members of an open cover of `O` agree on the overlaps (`gluePieceSet`, the pieces read on the
members of the cover through the restriction-of-a-restriction isomorphism) and glue to a morphism
`A | f⁻¹O ⟶ B | g⁻¹O` over `Z`; local isomorphisms over the base around every point of `O` glue to
an isomorphism over `O` (`Hom.UniqueOver.exists_isIso_restrictSetTo`, a corollary of
`KLocallyRingedSpace.exists_isIso_over_of_cover` of `Hironaka/AnalyticSpace/Glue/GlueIsoOver.lean`);
and the unique isomorphism over the base transports along an isomorphism of bases. This is the
gluing of the local isomorphisms between two local resolutions over the opens of a piece to an
isomorphism over their union — the uniqueness argument in the proof of [Kol07, Theorem 36] and the
functoriality of [Wlo09, Theorem 6.0.6 (1), (2)]. Routine; used by
`Hironaka/Resolution/Analytic/Kol07Thm45/RestrictIsoOpen.lean`,
`Hironaka/Resolution/Analytic/Kol07Thm45/RestrictInclusion.lean` and
`Hironaka/Resolution/Analytic/Kol07Thm45/LocalResolutionIndependent.lean`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- Every set lies in the open of the convention: `S ⊆ openOf X S` (equality for an open `S`, the
whole space otherwise). -/
theorem subset_openOf (X : AnalyticSpace.{u} K) (S : Set X) : S ⊆ (openOf X S : Set X) := by
  by_cases hS : IsOpen S
  · rw [openOf_of_isOpen X hS]
    exact Set.Subset.rfl
  · rw [openOf_of_not_isOpen X hS]
    exact Set.subset_univ S

/-- The opens of the convention are monotone on an open `T ⊆ S`. -/
theorem openOf_mono_of_isOpen (X : AnalyticSpace.{u} K) {T S : Set X} (hT : IsOpen T)
    (hTS : T ⊆ S) :
    openOf X T ≤ openOf X S := by
  rw [openOf_of_isOpen X hT]
  exact hTS.trans (subset_openOf X S)

/-! Every statement below is in the `K`-level view of the restriction `restrictSet`:
`X.toKLocallyRingedSpace.restrictOpen (openOf X T)`, definitionally
`(X.restrictSet T).toKLocallyRingedSpace`, so that the `K`-level lemmas on open subspaces apply. -/

/-- **The inclusion `X | T → X | S`** of the restrictions, `T ⊆ S` with `T` open: the `K`-level
`restrictIncl` at `openOf X T ≤ openOf X S`. -/
noncomputable def restrictSetIncl (X : AnalyticSpace.{u} K) {T S : Set X} (hT : IsOpen T)
    (hTS : T ⊆ S) :
    X.toKLocallyRingedSpace.restrictOpen (openOf X T) ⟶
      X.toKLocallyRingedSpace.restrictOpen (openOf X S) :=
  KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace (openOf_mono_of_isOpen X hT hTS)

/-- The inclusion lies over `X`. -/
theorem restrictSetIncl_comp_ofRestrict (X : AnalyticSpace.{u} K) {T S : Set X} (hT : IsOpen T)
    (hTS : T ⊆ S) :
    restrictSetIncl X hT hTS ≫ KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X S) =
      KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X T) :=
  KLocallyRingedSpace.restrictIncl_comp_ofRestrict X.toKLocallyRingedSpace
    (openOf_mono_of_isOpen X hT hTS)

/-- The inclusion is the identity on points. -/
theorem toFun_restrictSetIncl (X : AnalyticSpace.{u} K) {T S : Set X} (hT : IsOpen T) (hTS : T ⊆ S)
    (p : X.toKLocallyRingedSpace.restrictOpen (openOf X T)) :
    (KLocallyRingedSpace.Hom.toFun (restrictSetIncl X hT hTS) p).1 = p.1 :=
  congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ p) (restrictSetIncl_comp_ofRestrict X hT hTS)

/-- The inclusion `X | T → X | S` is a monomorphism: two morphisms into `X | T` with the same
composite into `X | S` are equal (compose further into `X`, where the open immersion is mono). -/
theorem ext_of_comp_restrictSetIncl (X : AnalyticSpace.{u} K) {T S : Set X} (hT : IsOpen T)
    (hTS : T ⊆ S) {Y : KLocallyRingedSpace.{u} K}
    {a b : Y ⟶ X.toKLocallyRingedSpace.restrictOpen (openOf X T)}
    (h : a ≫ restrictSetIncl X hT hTS = b ≫ restrictSetIncl X hT hTS) : a = b := by
  apply KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict (U := openOf X T)
  rw [← restrictSetIncl_comp_ofRestrict X hT hTS, ← Category.assoc, h, Category.assoc]

/-- The inclusions compose: `X | T → X | S → X | R` is `X | T → X | R`. -/
theorem restrictSetIncl_comp_restrictSetIncl (X : AnalyticSpace.{u} K) {T S R : Set X}
    (hT : IsOpen T) (hS : IsOpen S) (hTS : T ⊆ S) (hSR : S ⊆ R) :
    restrictSetIncl X hT hTS ≫ restrictSetIncl X hS hSR = restrictSetIncl X hT (hTS.trans hSR) := by
  apply KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict (U := openOf X R)
  rw [Category.assoc, restrictSetIncl_comp_ofRestrict, restrictSetIncl_comp_ofRestrict,
    restrictSetIncl_comp_ofRestrict]

/-- The piece of `X | S` over an open `T` of `X`: the open `T ∩ S` of `X | S`. Packaged as a
definition so that the statements about it carry a constant, not an anonymous constructor (the
rewrite motives stay type-correct). -/
def restrictSetPieceOpens (X : AnalyticSpace.{u} K) (S : Set X) {T : Set X} (hT : IsOpen T) :
    Opens (X.toKLocallyRingedSpace.restrictOpen (openOf X S)) :=
  ⟨Subtype.val ⁻¹' T, hT.preimage continuous_subtype_val⟩

/-- Membership in the piece over `T`. -/
theorem mem_restrictSetPieceOpens (X : AnalyticSpace.{u} K) (S : Set X) {T : Set X} (hT : IsOpen T)
    (p : X.toKLocallyRingedSpace.restrictOpen (openOf X S)) :
    p ∈ restrictSetPieceOpens X S hT ↔ p.1 ∈ T := Iff.rfl

/-- The pieces are monotone. -/
theorem restrictSetPieceOpens_le (X : AnalyticSpace.{u} K) (S : Set X) {T' T : Set X}
    (hT' : IsOpen T') (hT : IsOpen T) (h : T' ⊆ T) :
    restrictSetPieceOpens X S hT' ≤ restrictSetPieceOpens X S hT := fun _ hp => h hp

/-- The open immersion `(X | S) | (T ∩ S) → X | S → X` has range `T` for an open `T ⊆ S`. -/
theorem range_toFun_ofRestrict_pieceOpens_comp (X : AnalyticSpace.{u} K) {T S : Set X}
    (hT : IsOpen T) (hTS : T ⊆ S) :
    Set.range (KLocallyRingedSpace.Hom.toFun
        (KLocallyRingedSpace.ofRestrict (X.toKLocallyRingedSpace.restrictOpen (openOf X S))
          (restrictSetPieceOpens X S hT) ≫
          KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X S))) =
      Set.range (KLocallyRingedSpace.Hom.toFun
        (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X T))) := by
  have hmemT : ∀ x : X, x ∈ openOf X T ↔ x ∈ T := fun x =>
    Iff.of_eq (congrArg (fun U : Opens X => x ∈ U) (openOf_of_isOpen X hT))
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨⟨_, (hmemT _).mpr p.2⟩, rfl⟩
  · rintro ⟨q, rfl⟩
    have hq : q.1 ∈ T := (hmemT q.1).mp q.2
    exact ⟨⟨⟨q.1, subset_openOf X S (hTS hq)⟩, hq⟩, rfl⟩

/-- The open immersion of the piece over `T` into `X` (the composite of two `ofRestrict`s). -/
theorem isOpenImmersion_ofRestrict_pieceOpens_comp (X : AnalyticSpace.{u} K) (S : Set X) {T : Set X}
    (hT : IsOpen T) :
    LocallyRingedSpace.IsOpenImmersion
      (KLocallyRingedSpace.ofRestrict (X.toKLocallyRingedSpace.restrictOpen (openOf X S))
          (restrictSetPieceOpens X S hT) ≫
        KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X S)).1 := by
  rw [KLocallyRingedSpace.Hom.comp_val]
  infer_instance

/-- **The restriction of a restriction**: `(X | S) | (T ∩ S) ≅ X | T` for an open `T ⊆ S` — the two
open immersions into `X` have the same range `T` (`isoOfRangeEq`). -/
noncomputable def restrictSet_restrictSet_iso (X : AnalyticSpace.{u} K) {T S : Set X}
    (hT : IsOpen T) (hTS : T ⊆ S) :
    KLocallyRingedSpace.KIso ((X.toKLocallyRingedSpace.restrictOpen (openOf X S)).restrictOpen
        (restrictSetPieceOpens X S hT))
      (X.toKLocallyRingedSpace.restrictOpen (openOf X T)) :=
  have := isOpenImmersion_ofRestrict_pieceOpens_comp X S hT
  KLocallyRingedSpace.isoOfRangeEq
    (KLocallyRingedSpace.ofRestrict (X.toKLocallyRingedSpace.restrictOpen (openOf X S))
        (restrictSetPieceOpens X S hT) ≫
      KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X S))
    (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X T))
    (range_toFun_ofRestrict_pieceOpens_comp X hT hTS)

/-- The isomorphism lies over `X`: followed by the open immersion `X | T → X` it is the open
immersion of the piece `(X | S) | (T ∩ S) → X | S → X`. -/
theorem restrictSet_restrictSet_iso_hom_comp_ofRestrict (X : AnalyticSpace.{u} K) {T S : Set X}
    (hT : IsOpen T) (hTS : T ⊆ S) :
    (restrictSet_restrictSet_iso X hT hTS).hom ≫
        KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X T) =
      KLocallyRingedSpace.ofRestrict (X.toKLocallyRingedSpace.restrictOpen (openOf X S))
          (restrictSetPieceOpens X S hT) ≫
        KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X S) :=
  have := isOpenImmersion_ofRestrict_pieceOpens_comp X S hT
  KLocallyRingedSpace.isoOfRangeEq_hom_comp _ _ (range_toFun_ofRestrict_pieceOpens_comp X hT hTS)

/-- The isomorphism followed by the inclusion `X | T → X | S` is the open immersion of the piece
`(X | S) | (T ∩ S) → X | S` (the open immersion `X | S → X` is a monomorphism,
`Hom.ext_of_comp_ofRestrict`). -/
theorem restrictSet_restrictSet_iso_hom_comp (X : AnalyticSpace.{u} K) {T S : Set X}
    (hT : IsOpen T) (hTS : T ⊆ S) :
    (restrictSet_restrictSet_iso X hT hTS).hom ≫ restrictSetIncl X hT hTS =
      KLocallyRingedSpace.ofRestrict (X.toKLocallyRingedSpace.restrictOpen (openOf X S))
        (restrictSetPieceOpens X S hT) := by
  apply KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict (U := openOf X S)
  rw [Category.assoc, restrictSetIncl_comp_ofRestrict,
    restrictSet_restrictSet_iso_hom_comp_ofRestrict]

/-- **Naturality of the restriction for the inclusions of nested opens** (the `K`-level form,
`Hom.restrictTo` at the opens of the convention): `f | f⁻¹T` followed by `Z | T → Z | S` is
`A | f⁻¹T → A | f⁻¹S` followed by `f | f⁻¹S` — both are lifts of `A | f⁻¹T → A → Z` through the open
immersion `Z | S → Z` (`Hom.restrictTo_comp_ofRestrict`), which is a monomorphism. -/
theorem restrictTo_comp_restrictSetIncl {A Z : AnalyticSpace.{u} K} (f : A ⟶ Z) {T S : Set Z}
    (hT : IsOpen T) (hTS : T ⊆ S) :
    KLocallyRingedSpace.Hom.restrictTo f (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' T)) (openOf
    Z T)
        (Hom.mapsTo_openOf f T) ≫ restrictSetIncl Z hT hTS =
      restrictSetIncl A (hT.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))
          (Set.preimage_mono hTS) ≫
        KLocallyRingedSpace.Hom.restrictTo f (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' S))
          (openOf Z S) (Hom.mapsTo_openOf f S) := by
  apply KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict (U := openOf Z S)
  rw [Category.assoc, restrictSetIncl_comp_ofRestrict,
    KLocallyRingedSpace.Hom.restrictTo_comp_ofRestrict,
    Category.assoc, KLocallyRingedSpace.Hom.restrictTo_comp_ofRestrict, ← Category.assoc,
    restrictSetIncl_comp_ofRestrict]

/-- The same for `Hom.restrictSet` (which is `Hom.restrictTo` at the opens of the convention,
`Hom.restrictSet_eq_restrictTo`). -/
theorem restrictSet_comp_restrictSetIncl {A Z : AnalyticSpace.{u} K} (f : A ⟶ Z) {T S : Set Z}
    (hT : IsOpen T) (hTS : T ⊆ S) :
    Hom.restrictSet f T ≫ restrictSetIncl Z hT hTS =
      restrictSetIncl A (hT.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))
          (Set.preimage_mono hTS) ≫
        Hom.restrictSet f S :=
  restrictTo_comp_restrictSetIncl f hT hTS

/-- **Naturality of the restriction-of-a-restriction isomorphism for nested opens**: for opens
`T' ⊆ T ⊆ S`, the inverse isomorphism of `T'`, the inclusion of the pieces and the isomorphism of
`T` compose to the inclusion `X | T' → X | T` — every step lies over `X`. -/
theorem restrictSet_restrictSet_iso_inv_comp_restrictIncl (X : AnalyticSpace.{u} K)
    {T' T S : Set X} (hT' : IsOpen T') (hT : IsOpen T) (hT'T : T' ⊆ T) (hTS : T ⊆ S) :
    (restrictSet_restrictSet_iso X hT' (hT'T.trans hTS)).inv ≫
        KLocallyRingedSpace.restrictIncl (X.toKLocallyRingedSpace.restrictOpen (openOf X S))
          (restrictSetPieceOpens_le X S hT' hT hT'T) ≫
        (restrictSet_restrictSet_iso X hT hTS).hom =
      restrictSetIncl X hT' hT'T := by
  apply KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict (U := openOf X T)
  rw [restrictSetIncl_comp_ofRestrict, Category.assoc, Category.assoc,
    restrictSet_restrictSet_iso_hom_comp_ofRestrict,
    ← Category.assoc _ (KLocallyRingedSpace.ofRestrict _ _),
    KLocallyRingedSpace.restrictIncl_comp_ofRestrict,
    ← restrictSet_restrictSet_iso_hom_comp_ofRestrict X hT' (hT'T.trans hTS), Iso.inv_hom_id_assoc]

/-- Equal sets give the same restriction: the identification `X | s ≅ X | t` for `s = t`
(`eqToIso`), the identity on points. -/
noncomputable def restrictSet_congr_iso (X : AnalyticSpace.{u} K) {s t : Set X} (h : s = t) :
    KLocallyRingedSpace.KIso (X.toKLocallyRingedSpace.restrictOpen (openOf X s))
      (X.toKLocallyRingedSpace.restrictOpen (openOf X t)) :=
  eqToIso (congrArg (fun r => X.toKLocallyRingedSpace.restrictOpen (openOf X r)) h)

/-- The identification of equal restrictions lies over `X`. -/
theorem restrictSet_congr_iso_hom_comp_ofRestrict (X : AnalyticSpace.{u} K) {s t : Set X}
    (h : s = t) :
    (restrictSet_congr_iso X h).hom ≫ KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace
      (openOf X t) =
      KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X s) := by
  subst h
  exact Category.id_comp _

/-- The inverse identification of equal restrictions lies over `X`. -/
theorem restrictSet_congr_iso_inv_comp_ofRestrict (X : AnalyticSpace.{u} K) {s t : Set X}
    (h : s = t) :
    (restrictSet_congr_iso X h).inv ≫ KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace
      (openOf X s) =
      KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X t) := by
  subst h
  exact Category.id_comp _

/-! ### Gluing over a base

The gluing and transport statements, for arbitrary morphisms `f : A ⟶ Z`, `g : B ⟶ Z` of analytic
`K`-spaces in the `K`-level view of the restriction (`Hom.restrictSetTo`, which is
`Hom.restrictSet`): every object is a `restrictOpen` of a `K`-local-ringed space at an open of the
convention `openOf`, every morphism a `K`-morphism, so that the library's gluing of morphisms
along an open cover (`glueOfCover`, `hom_ext_of_cover`) applies as it stands. -/

section GlueOver

variable {A B Z : AnalyticSpace.{u} K}

/-- The `K`-view of the restriction `f | f⁻¹N : A | f⁻¹N ⟶ Z | N`: `Hom.restrictTo` at the opens of
the convention (`Hom.restrictSet_eq_restrictTo`), stated on the `K`-local-ringed spaces so that the
gluing statements of this section live in one category. -/
noncomputable def Hom.restrictSetTo (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace)
    (N : Set Z) :
    A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N)) ⟶
      Z.toKLocallyRingedSpace.restrictOpen (openOf Z N) :=
  KLocallyRingedSpace.Hom.restrictTo f _ _ (Hom.mapsTo_openOf f N)

/-- `Hom.restrictSetTo` is `Hom.restrictSet`. -/
theorem Hom.restrictSetTo_eq_restrictSet (f : A ⟶ Z) (N : Set Z) :
    Hom.restrictSetTo f N = Hom.restrictSet f N :=
  rfl

/-- The restriction lies over `f`. -/
theorem Hom.restrictSetTo_comp_ofRestrict (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace)
    (N : Set Z) :
    Hom.restrictSetTo f N ≫ KLocallyRingedSpace.ofRestrict Z.toKLocallyRingedSpace (openOf Z N) =
      KLocallyRingedSpace.ofRestrict A.toKLocallyRingedSpace
        (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N)) ≫ f :=
  KLocallyRingedSpace.Hom.restrictTo_comp_ofRestrict f _ _ _

/-- The restriction lies over `f` (reassociated form). -/
theorem Hom.restrictSetTo_comp_ofRestrict_assoc
    (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace) (N : Set Z)
    {Y : KLocallyRingedSpace.{u} K} (k : Z.toKLocallyRingedSpace ⟶ Y) :
    Hom.restrictSetTo f N ≫ KLocallyRingedSpace.ofRestrict Z.toKLocallyRingedSpace (openOf Z N) ≫
        k =
      KLocallyRingedSpace.ofRestrict A.toKLocallyRingedSpace
        (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N)) ≫ f ≫ k := by
  rw [← Category.assoc, Hom.restrictSetTo_comp_ofRestrict, Category.assoc]

/-- The restriction on points. -/
theorem Hom.toFun_restrictSetTo (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace) (N : Set Z)
    (p : A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N))) :
    (KLocallyRingedSpace.Hom.toFun (Hom.restrictSetTo f N) p).1 =
      KLocallyRingedSpace.Hom.toFun f p.1 :=
  KLocallyRingedSpace.Hom.toFun_restrictTo f _ _ _ p

/-- Naturality of the restriction for the inclusions of nested opens, in the `K`-view. -/
theorem Hom.restrictSetTo_comp_restrictSetIncl
    (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace) {T S : Set Z} (hT : IsOpen T)
    (hTS : T ⊆ S) :
    Hom.restrictSetTo f T ≫ restrictSetIncl Z hT hTS =
      restrictSetIncl A (hT.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))
          (Set.preimage_mono hTS) ≫
        Hom.restrictSetTo f S :=
  restrictTo_comp_restrictSetIncl f hT hTS

/-- Membership in the open of the convention, for an open set. -/
theorem mem_openOf_iff_of_isOpen (X : AnalyticSpace.{u} K) {S : Set X} (hS : IsOpen S) (x : X) :
    x ∈ openOf X S ↔ x ∈ S :=
  Iff.of_eq (congrArg (fun U : Opens X => x ∈ U) (openOf_of_isOpen X hS))

/-- The member of the open cover of `A | f⁻¹O` over an open `N` of `Z`: the points of `A | f⁻¹O`
lying over `N` (the piece `restrictSetPieceOpens` at `f⁻¹N`). -/
abbrev Hom.preimagePieceOpens (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace) (O : Set Z)
    {N : Set Z} (hN : IsOpen N) :
    Opens (A.toKLocallyRingedSpace.restrictOpen
      (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' O))) :=
  restrictSetPieceOpens A (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)
    (hN.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))

/-- Membership in the member over `N`. -/
theorem Hom.mem_preimagePieceOpens (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace)
    (O : Set Z) {N : Set Z} (hN : IsOpen N)
    (a : A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' O))) :
    a ∈ Hom.preimagePieceOpens f O hN ↔ KLocallyRingedSpace.Hom.toFun f a.1 ∈ N :=
  Iff.rfl

/-- The members over opens `N i` covering `O` cover `A | f⁻¹O`. -/
theorem Hom.exists_mem_preimagePieceOpens (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace)
    {O : Set Z} (hO : IsOpen O) {ι : Type*} (N : ι → Set Z) (hN : ∀ i, IsOpen (N i))
    (hcov : ∀ x ∈ O, ∃ i, x ∈ N i)
    (a : A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' O))) :
    ∃ i, a ∈ Hom.preimagePieceOpens f O (hN i) := by
  have ha : KLocallyRingedSpace.Hom.toFun f a.1 ∈ O :=
    (mem_openOf_iff_of_isOpen A (hO.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))
      a.1).mp a.2
  obtain ⟨i, hi⟩ := hcov _ ha
  exact ⟨i, hi⟩

/-- **Uniqueness over the base**: for every open `N` of `Z`, two morphisms `A | f⁻¹N ⟶ B | g⁻¹N`
over `Z | N` are equal — the hypothesis of the gluing below, which the local resolution maps
satisfy. -/
def Hom.UniqueOver (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace)
    (g : B.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace) : Prop :=
  ∀ {N : Set Z}, IsOpen N →
    ∀ χ₁ χ₂ : A.toKLocallyRingedSpace.restrictOpen
        (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N)) ⟶
      B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N)),
      χ₁ ≫ Hom.restrictSetTo g N = Hom.restrictSetTo f N →
        χ₂ ≫ Hom.restrictSetTo g N = Hom.restrictSetTo f N → χ₁ = χ₂

/-- A morphism `A | f⁻¹M ⟶ B | g⁻¹O` over `Z` through the inclusion `Z | M ⟶ Z | O` maps every point
into the member over `M`. -/
theorem Hom.toFun_mem_of_comp_restrictSetTo_eq
    (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace)
    (g : B.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace) {M O : Set Z} (hM : IsOpen M)
    (hMO : M ⊆ O)
    (χ : A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' M)) ⟶
      B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' O)))
    (h : χ ≫ Hom.restrictSetTo g O = Hom.restrictSetTo f M ≫ restrictSetIncl Z hM hMO)
    (p : A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' M))) :
    KLocallyRingedSpace.Hom.toFun χ p ∈ Hom.preimagePieceOpens g O hM := by
  have e : (KLocallyRingedSpace.Hom.toFun (Hom.restrictSetTo g O)
        (KLocallyRingedSpace.Hom.toFun χ p)).1 =
      (KLocallyRingedSpace.Hom.toFun (restrictSetIncl Z hM hMO)
        (KLocallyRingedSpace.Hom.toFun (Hom.restrictSetTo f M) p)).1 :=
    congrArg (fun k : A.toKLocallyRingedSpace.restrictOpen
        (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' M)) ⟶
        Z.toKLocallyRingedSpace.restrictOpen (openOf Z O) =>
      (KLocallyRingedSpace.Hom.toFun k p).1) h
  rw [Hom.toFun_restrictSetTo, toFun_restrictSetIncl, Hom.toFun_restrictSetTo] at e
  change KLocallyRingedSpace.Hom.toFun g (KLocallyRingedSpace.Hom.toFun χ p).1 ∈ M
  rw [e]
  exact (mem_openOf_iff_of_isOpen A (hM.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))
    p.1).mp p.2

/-- **Uniqueness over the base with the target over a larger open**: two morphisms
`A | f⁻¹M ⟶ B | g⁻¹O` (`M ⊆ O` open) over `Z` through the inclusion `Z | M ⟶ Z | O` are equal — each
factors through the open `B | g⁻¹M` (`Hom.liftRestrict`, the restriction-of-a-restriction
isomorphism), the factors are over `Z | M` (naturality; the inclusion is mono), so the uniqueness
over `M` identifies them. -/
theorem Hom.UniqueOver.ext_over_incl {f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace}
    {g : B.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace} (huniq : Hom.UniqueOver f g)
    {M O : Set Z} (hM : IsOpen M) (hMO : M ⊆ O)
    (χ₁ χ₂ : A.toKLocallyRingedSpace.restrictOpen
        (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' M)) ⟶
      B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' O)))
    (h₁ : χ₁ ≫ Hom.restrictSetTo g O = Hom.restrictSetTo f M ≫ restrictSetIncl Z hM hMO)
    (h₂ : χ₂ ≫ Hom.restrictSetTo g O = Hom.restrictSetTo f M ≫ restrictSetIncl Z hM hMO) :
    χ₁ = χ₂ := by
  have hM' : IsOpen (KLocallyRingedSpace.Hom.toFun g ⁻¹' M) :=
    hM.preimage (KLocallyRingedSpace.Hom.continuous_toFun g)
  have hMO' : KLocallyRingedSpace.Hom.toFun g ⁻¹' M ⊆ KLocallyRingedSpace.Hom.toFun g ⁻¹' O :=
    Set.preimage_mono hMO
  -- the factorisations through `B | g⁻¹M`
  let lift : ∀ χ : A.toKLocallyRingedSpace.restrictOpen
        (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' M)) ⟶
      B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' O)),
      χ ≫ Hom.restrictSetTo g O = Hom.restrictSetTo f M ≫ restrictSetIncl Z hM hMO →
      (A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' M)) ⟶
        B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' M))) :=
    fun χ h => KLocallyRingedSpace.Hom.liftRestrict χ (Hom.preimagePieceOpens g O hM)
      (fun p => Hom.toFun_mem_of_comp_restrictSetTo_eq f g hM hMO χ h p) ≫
      (restrictSet_restrictSet_iso B hM' hMO').hom
  have hlift : ∀ χ h, lift χ h ≫ restrictSetIncl B hM' hMO' = χ := by
    intro χ h
    change (KLocallyRingedSpace.Hom.liftRestrict χ _ _ ≫
      (restrictSet_restrictSet_iso B hM' hMO').hom) ≫ restrictSetIncl B hM' hMO' = χ
    rw [Category.assoc, restrictSet_restrictSet_iso_hom_comp,
      KLocallyRingedSpace.Hom.liftRestrict_comp_ofRestrict]
  -- the factors are over `Z | M`
  have hcomp : ∀ χ h, lift χ h ≫ Hom.restrictSetTo g M = Hom.restrictSetTo f M := by
    intro χ h
    apply ext_of_comp_restrictSetIncl Z hM hMO
    rw [Category.assoc, Hom.restrictSetTo_comp_restrictSetIncl g hM hMO, ← Category.assoc,
      hlift χ h, h]
  have key := huniq hM (lift χ₁ h₁) (lift χ₂ h₂) (hcomp χ₁ h₁) (hcomp χ₂ h₂)
  rw [← hlift χ₁ h₁, ← hlift χ₂ h₂, key]

/-- The piece of the glued morphism over an open `N ⊆ O`: the local morphism
`ψ : A | f⁻¹N ⟶ B | g⁻¹N` read on the member of the cover through the restriction-of-a-restriction
isomorphism, then into `B | g⁻¹O` by the inclusion. -/
noncomputable def Hom.gluePieceSet (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace)
    (g : B.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace) {O N : Set Z} (hN : IsOpen N)
    (hNO : N ⊆ O)
    (ψ : A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N)) ⟶
      B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N))) :
    (A.toKLocallyRingedSpace.restrictOpen
        (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' O))).restrictOpen
        (Hom.preimagePieceOpens f O hN) ⟶
      B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' O)) :=
  (restrictSet_restrictSet_iso A (hN.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))
      (Set.preimage_mono hNO)).hom ≫
    ψ ≫ restrictSetIncl B (hN.preimage (KLocallyRingedSpace.Hom.continuous_toFun g))
      (Set.preimage_mono hNO)

/-- The piece lies over `Z`: `gluePieceSet ψ ≫ g|O = ofRestrict ≫ f|O` when `ψ ≫ g|N = f|N`
(naturality twice, and the restriction-of-a-restriction isomorphism). -/
theorem Hom.gluePieceSet_comp_restrictSetTo (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace)
    (g : B.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace) {O N : Set Z} (hN : IsOpen N)
    (hNO : N ⊆ O)
    (ψ : A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N)) ⟶
      B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N)))
    (hψ : ψ ≫ Hom.restrictSetTo g N = Hom.restrictSetTo f N) :
    Hom.gluePieceSet f g hN hNO ψ ≫ Hom.restrictSetTo g O =
      KLocallyRingedSpace.ofRestrict _ (Hom.preimagePieceOpens f O hN) ≫ Hom.restrictSetTo f O := by
  unfold Hom.gluePieceSet
  rw [Category.assoc, Category.assoc, ← Hom.restrictSetTo_comp_restrictSetIncl g hN hNO,
    ← Category.assoc ψ, hψ, Hom.restrictSetTo_comp_restrictSetIncl f hN hNO, ← Category.assoc,
    restrictSet_restrictSet_iso_hom_comp]

/-- Two pieces agree on the overlap of their members (the `GlueCompatible` of the gluing): both are
morphisms `A | f⁻¹(N ∩ N') ⟶ B | g⁻¹O` over `Z` through the inclusion `Z | (N ∩ N') ⟶ Z | O`, equal
by the uniqueness over the base; the members are identified with the restrictions to `f⁻¹(N ∩ N')`
by the nested-opens naturality. -/
theorem Hom.UniqueOver.gluePieceSet_compat {f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace}
    {g : B.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace} (huniq : Hom.UniqueOver f g)
    {O N N' : Set Z} (hN : IsOpen N) (hNO : N ⊆ O) (hN' : IsOpen N') (hN'O : N' ⊆ O)
    (ψ : A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N)) ⟶
      B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N)))
    (hψ : ψ ≫ Hom.restrictSetTo g N = Hom.restrictSetTo f N)
    (ψ' : A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N')) ⟶
      B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N')))
    (hψ' : ψ' ≫ Hom.restrictSetTo g N' = Hom.restrictSetTo f N') :
    KLocallyRingedSpace.restrictIncl _
        (inf_le_left : Hom.preimagePieceOpens f O hN ⊓ Hom.preimagePieceOpens f O hN' ≤
          Hom.preimagePieceOpens f O hN) ≫ Hom.gluePieceSet f g hN hNO ψ =
      KLocallyRingedSpace.restrictIncl _
        (inf_le_right : Hom.preimagePieceOpens f O hN ⊓ Hom.preimagePieceOpens f O hN' ≤
          Hom.preimagePieceOpens f O hN') ≫ Hom.gluePieceSet f g hN' hN'O ψ' := by
  have hM : IsOpen (N ∩ N') := hN.inter hN'
  have hMO : N ∩ N' ⊆ O := Set.inter_subset_left.trans hNO
  have hM₁ : IsOpen (KLocallyRingedSpace.Hom.toFun f ⁻¹' (N ∩ N')) :=
    hM.preimage (KLocallyRingedSpace.Hom.continuous_toFun f)
  -- the two morphisms out of `A | f⁻¹(N ∩ N')`
  let χ : ∀ {N₀ : Set Z} (hN₀ : IsOpen N₀) (_ : N₀ ⊆ O) (_ : N ∩ N' ⊆ N₀)
      (_ : A.toKLocallyRingedSpace.restrictOpen
          (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N₀)) ⟶
        B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N₀))),
      A.toKLocallyRingedSpace.restrictOpen
          (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' (N ∩ N'))) ⟶
        B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' O)) :=
    fun hN₀ hN₀O hMN₀ ψ₀ =>
      restrictSetIncl A hM₁ (Set.preimage_mono hMN₀) ≫ ψ₀ ≫
        restrictSetIncl B (hN₀.preimage (KLocallyRingedSpace.Hom.continuous_toFun g))
          (Set.preimage_mono hN₀O)
  -- each is over `Z` through the inclusion `Z | (N ∩ N') ⟶ Z | O`
  have hχ : ∀ {N₀ : Set Z} (hN₀ : IsOpen N₀) (hN₀O : N₀ ⊆ O) (hMN₀ : N ∩ N' ⊆ N₀)
      (ψ₀ : A.toKLocallyRingedSpace.restrictOpen
          (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N₀)) ⟶
        B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N₀)))
      (_ : ψ₀ ≫ Hom.restrictSetTo g N₀ = Hom.restrictSetTo f N₀),
      χ hN₀ hN₀O hMN₀ ψ₀ ≫ Hom.restrictSetTo g O =
        Hom.restrictSetTo f (N ∩ N') ≫ restrictSetIncl Z hM hMO := by
    intro N₀ hN₀ hN₀O hMN₀ ψ₀ hψ₀
    change (restrictSetIncl A hM₁ (Set.preimage_mono hMN₀) ≫ ψ₀ ≫
        restrictSetIncl B (hN₀.preimage (KLocallyRingedSpace.Hom.continuous_toFun g))
          (Set.preimage_mono hN₀O)) ≫ Hom.restrictSetTo g O = _
    rw [Category.assoc, Category.assoc, ← Hom.restrictSetTo_comp_restrictSetIncl g hN₀ hN₀O,
      ← Category.assoc ψ₀, hψ₀, Hom.restrictSetTo_comp_restrictSetIncl f hN₀ hN₀O,
      ← Category.assoc, restrictSetIncl_comp_restrictSetIncl,
      Hom.restrictSetTo_comp_restrictSetIncl f hM hMO]
  -- the pieces restricted to the overlap are the two morphisms, through the nested-opens naturality
  have hpiece : ∀ {N₀ : Set Z} (hN₀ : IsOpen N₀) (hN₀O : N₀ ⊆ O) (hMN₀ : N ∩ N' ⊆ N₀)
      (ψ₀ : A.toKLocallyRingedSpace.restrictOpen
          (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N₀)) ⟶
        B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N₀))),
      KLocallyRingedSpace.restrictIncl _ (restrictSetPieceOpens_le A _ hM₁
          (hN₀.preimage (KLocallyRingedSpace.Hom.continuous_toFun f)) (Set.preimage_mono hMN₀)) ≫
        Hom.gluePieceSet f g hN₀ hN₀O ψ₀ =
      (restrictSet_restrictSet_iso A hM₁ (Set.preimage_mono hMO)).hom ≫ χ hN₀ hN₀O hMN₀ ψ₀ := by
    intro N₀ hN₀ hN₀O hMN₀ ψ₀
    change _ = (restrictSet_restrictSet_iso A hM₁ (Set.preimage_mono hMO)).hom ≫
      (restrictSetIncl A hM₁ (Set.preimage_mono hMN₀) ≫ ψ₀ ≫
        restrictSetIncl B (hN₀.preimage (KLocallyRingedSpace.Hom.continuous_toFun g))
          (Set.preimage_mono hN₀O))
    unfold Hom.gluePieceSet
    rw [← restrictSet_restrictSet_iso_inv_comp_restrictIncl A hM₁
      (hN₀.preimage (KLocallyRingedSpace.Hom.continuous_toFun f)) (Set.preimage_mono hMN₀)
      (Set.preimage_mono hN₀O)]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change KLocallyRingedSpace.restrictIncl _ (restrictSetPieceOpens_le A _ hM₁
        (hN.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))
        (Set.preimage_mono Set.inter_subset_left)) ≫ Hom.gluePieceSet f g hN hNO ψ =
    KLocallyRingedSpace.restrictIncl _ (restrictSetPieceOpens_le A _ hM₁
        (hN'.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))
        (Set.preimage_mono Set.inter_subset_right)) ≫ Hom.gluePieceSet f g hN' hN'O ψ'
  rw [hpiece hN hNO Set.inter_subset_left ψ, hpiece hN' hN'O Set.inter_subset_right ψ',
    huniq.ext_over_incl hM hMO _ _ (hχ hN hNO Set.inter_subset_left ψ hψ)
      (hχ hN' hN'O Set.inter_subset_right ψ' hψ')]

/-- **The glued morphism** (the gluing in the proof of [Kol07, Theorem 36]): local morphisms
`ψ i : A | f⁻¹(N i) ⟶ B | g⁻¹(N i)` over `Z`, the opens `N i ⊆ O` covering `O`, glue (`glueOfCover`,
the pieces being compatible on the overlaps) to a morphism `A | f⁻¹O ⟶ B | g⁻¹O` restricting to each
piece and lying over `Z`. -/
theorem Hom.UniqueOver.exists_glue {f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace}
    {g : B.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace} (huniq : Hom.UniqueOver f g)
    {O : Set Z} (hO : IsOpen O) {ι : Type*} (N : ι → Set Z) (hN : ∀ i, IsOpen (N i))
    (hNO : ∀ i, N i ⊆ O) (hcov : ∀ x ∈ O, ∃ i, x ∈ N i)
    (ψ : ∀ i, A.toKLocallyRingedSpace.restrictOpen
        (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N i)) ⟶
      B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N i)))
    (hψ : ∀ i, ψ i ≫ Hom.restrictSetTo g (N i) = Hom.restrictSetTo f (N i)) :
    ∃ Φ : A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)) ⟶
        B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' O)),
      (∀ i, KLocallyRingedSpace.ofRestrict _ (Hom.preimagePieceOpens f O (hN i)) ≫ Φ =
        Hom.gluePieceSet f g (hN i) (hNO i) (ψ i)) ∧
      Φ ≫ Hom.restrictSetTo g O = Hom.restrictSetTo f O := by
  have hcov' := Hom.exists_mem_preimagePieceOpens f hO N hN hcov
  have hglue : KLocallyRingedSpace.GlueCompatible (fun i => Hom.preimagePieceOpens f O (hN i))
      (fun i => Hom.gluePieceSet f g (hN i) (hNO i) (ψ i)) :=
    fun i j => huniq.gluePieceSet_compat (hN i) (hNO i) (hN j) (hNO j) (ψ i) (hψ i) (ψ j) (hψ j)
  have hΦ : ∀ i, KLocallyRingedSpace.ofRestrict _ (Hom.preimagePieceOpens f O (hN i)) ≫
      KLocallyRingedSpace.glueOfCover (fun i => Hom.preimagePieceOpens f O (hN i))
        (fun i => Hom.gluePieceSet f g (hN i) (hNO i) (ψ i)) hcov' hglue =
      Hom.gluePieceSet f g (hN i) (hNO i) (ψ i) :=
    fun i => KLocallyRingedSpace.ofRestrict_comp_glueOfCover _ _ hcov' hglue i
  refine ⟨KLocallyRingedSpace.glueOfCover (fun i => Hom.preimagePieceOpens f O (hN i))
    (fun i => Hom.gluePieceSet f g (hN i) (hNO i) (ψ i)) hcov' hglue, hΦ, ?_⟩
  apply KLocallyRingedSpace.hom_ext_of_cover _ _ (fun i => Hom.preimagePieceOpens f O (hN i)) hcov'
  intro i
  rw [← Category.assoc, hΦ i, Hom.gluePieceSet_comp_restrictSetTo f g (hN i) (hNO i) (ψ i) (hψ i)]

/-- **Local isomorphisms over the base around every point of an open `O` glue to an isomorphism over
`O`**, given uniqueness over the base (the uniqueness argument in the proof of [Kol07, Theorem 36];
[Wlo09, Theorem 6.0.6 (1)]). Proof: a corollary of `KLocallyRingedSpace.exists_isIso_over_of_cover`
(`Hironaka/AnalyticSpace/Glue/GlueIsoOver.lean`) — the opens `openOf A (f⁻¹N)` are the `Opens.comap`
of the open `N` (`openOf_of_isOpen`), so the pieces, their over-conditions and the uniqueness
transport along `eqToIso`; the second uniqueness hypothesis `_huniq'` is kept in the signature (the
cited theorem derives it, `uniq_symm`); the gluing lemmas of this file (`gluePieceSet` and its
properties) are general lemmas not on this proof path. -/
theorem Hom.UniqueOver.exists_isIso_restrictSetTo
    {f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace}
    {g : B.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace} (huniq : Hom.UniqueOver f g)
    (_huniq' : Hom.UniqueOver g f) {O : Set Z} (hO : IsOpen O)
    (hloc : ∀ x ∈ O, ∃ N : Set Z, IsOpen N ∧ x ∈ N ∧ N ⊆ O ∧
      ∃ ψ : A.toKLocallyRingedSpace.restrictOpen
          (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N)) ⟶
        B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N)),
        CategoryTheory.IsIso ψ ∧ ψ ≫ Hom.restrictSetTo g N = Hom.restrictSetTo f N) :
    ∃ ψ : A.toKLocallyRingedSpace.restrictOpen (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)) ⟶
        B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' O)),
      CategoryTheory.IsIso ψ ∧ ψ ≫ Hom.restrictSetTo g O = Hom.restrictSetTo f O := by
  choose N hNo hxN hNO ψ hψi hψc using fun x : O => hloc x.1 x.2
  -- the open of the convention at an open preimage is the `comap` of the open
  have hopen : ∀ (C : AnalyticSpace.{u} K) (h : C.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace)
      {N : Set Z} (hN : IsOpen N),
      openOf C (KLocallyRingedSpace.Hom.toFun h ⁻¹' N) =
        Opens.comap ⟨KLocallyRingedSpace.Hom.toFun h, KLocallyRingedSpace.Hom.continuous_toFun h⟩
          ⟨N, hN⟩ :=
    fun C h N hN => openOf_of_isOpen C (hN.preimage (KLocallyRingedSpace.Hom.continuous_toFun h))
  -- transport along an equality of opens is over the space
  have trh : ∀ (X : KLocallyRingedSpace.{u} K) {U U' : Opens X} (h : U = U') {W :
KLocallyRingedSpace.{u} K}
      (k : X ⟶ W), (eqToIso (congrArg X.restrictOpen h)).hom ≫ KLocallyRingedSpace.ofRestrict X U'
≫ k =
        KLocallyRingedSpace.ofRestrict X U ≫ k := by
    intro X U U' h W k; subst h; simp
  have tri : ∀ (X : KLocallyRingedSpace.{u} K) {U U' : Opens X} (h : U = U') {W :
KLocallyRingedSpace.{u} K}
      (k : X ⟶ W), (eqToIso (congrArg X.restrictOpen h)).inv ≫ KLocallyRingedSpace.ofRestrict X U ≫
k =
        KLocallyRingedSpace.ofRestrict X U' ≫ k := by
    intro X U U' h W k; subst h; simp
  -- the over-condition of the restriction, read in `Z`
  have hover : ∀ {N : Set Z} (t : A.toKLocallyRingedSpace.restrictOpen
        (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N)) ⟶
      B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N))),
      t ≫ Hom.restrictSetTo g N = Hom.restrictSetTo f N ↔
        t ≫ KLocallyRingedSpace.ofRestrict B.toKLocallyRingedSpace
            (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N)) ≫ g =
          KLocallyRingedSpace.ofRestrict A.toKLocallyRingedSpace
            (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N)) ≫ f := by
    intro N t
    constructor
    · intro h
      have := congrArg (fun k => k ≫ KLocallyRingedSpace.ofRestrict Z.toKLocallyRingedSpace
        (openOf Z N)) h
      simp only [Category.assoc, Hom.restrictSetTo_comp_ofRestrict] at this
      exact this
    · intro h
      apply KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict (U := openOf Z N)
      simp only [Category.assoc, Hom.restrictSetTo_comp_ofRestrict]
      exact h
  -- the pieces and the uniqueness, transported to the cited theorem's opens and back
  have key : ∀ {N : Set Z} (hN : IsOpen N)
      (s : A.toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun f, KLocallyRingedSpace.Hom.continuous_toFun f⟩
            ⟨N, hN⟩) ⟶
        B.toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun g, KLocallyRingedSpace.Hom.continuous_toFun g⟩
            ⟨N, hN⟩)),
      KLocallyRingedSpace.ofRestrict _ _ ≫ f = (s ≫ KLocallyRingedSpace.ofRestrict _ _) ≫ g →
        ((eqToIso (congrArg A.toKLocallyRingedSpace.restrictOpen (hopen A f hN))).hom ≫ s ≫
            (eqToIso (congrArg B.toKLocallyRingedSpace.restrictOpen (hopen B g hN))).inv) ≫
          Hom.restrictSetTo g N = Hom.restrictSetTo f N := by
    intro N hN s hs
    rw [hover, Category.assoc, Category.assoc, tri B.toKLocallyRingedSpace (hopen B g hN),
      ← Category.assoc s, ← hs, trh A.toKLocallyRingedSpace (hopen A f hN)]
  have key' : ∀ {N : Set Z} (hN : IsOpen N) (t : A.toKLocallyRingedSpace.restrictOpen
        (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' N)) ⟶
      B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' N))),
      t ≫ Hom.restrictSetTo g N = Hom.restrictSetTo f N →
        KLocallyRingedSpace.ofRestrict A.toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun f, KLocallyRingedSpace.Hom.continuous_toFun
f⟩
              ⟨N, hN⟩) ≫ f =
          (((eqToIso (congrArg A.toKLocallyRingedSpace.restrictOpen (hopen A f hN))).inv ≫ t ≫
              (eqToIso (congrArg B.toKLocallyRingedSpace.restrictOpen (hopen B g hN))).hom) ≫
            KLocallyRingedSpace.ofRestrict B.toKLocallyRingedSpace
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun g,
                KLocallyRingedSpace.Hom.continuous_toFun g⟩ ⟨N, hN⟩)) ≫ g := by
    intro N hN t ht
    rw [hover] at ht
    rw [Category.assoc, Category.assoc, Category.assoc, trh B.toKLocallyRingedSpace (hopen B g hN),
      ht, tri A.toKLocallyRingedSpace (hopen A f hN)]
  -- the cited theorem at the cover `N x` of `O`
  obtain ⟨s, hsi, hs⟩ := KLocallyRingedSpace.exists_isIso_over_of_cover f g ⟨O, hO⟩
    (fun x : O => ⟨N x, hNo x⟩) (fun x => hNO x) (fun z hz => ⟨⟨z, hz⟩, hxN ⟨z, hz⟩⟩)
    (fun x => by
      have := hψi x
      exact ⟨(eqToIso (congrArg A.toKLocallyRingedSpace.restrictOpen (hopen A f (hNo x)))).inv ≫
        ψ x ≫ (eqToIso (congrArg B.toKLocallyRingedSpace.restrictOpen (hopen B g (hNo x)))).hom,
        inferInstance, key' (hNo x) (ψ x) (hψc x)⟩)
    (fun O' _ s s' hs hs' hso hso' => by
      have e := huniq O'.isOpen _ _ (key O'.isOpen s hso) (key O'.isOpen s' hso')
      have := hs
      have := hs'
      simpa only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc] using
        congrArg (fun k => (eqToIso (congrArg A.toKLocallyRingedSpace.restrictOpen
          (hopen A f O'.isOpen))).inv ≫ k ≫
          (eqToIso (congrArg B.toKLocallyRingedSpace.restrictOpen (hopen B g O'.isOpen))).hom) e)
  have := hsi
  exact ⟨(eqToIso (congrArg A.toKLocallyRingedSpace.restrictOpen (hopen A f hO))).hom ≫ s ≫
    (eqToIso (congrArg B.toKLocallyRingedSpace.restrictOpen (hopen B g hO))).inv,
    inferInstance, key hO s hs⟩

/-- `f` is an isomorphism of `An/K` iff it is an isomorphism of the underlying `K`-local-ringed
spaces (the categories share composition and identities). -/
theorem Hom.isIso_iff_isIso_toKLocallyRingedSpace {X Y : AnalyticSpace.{u} K} (f : X ⟶ Y) :
    IsIso f ↔
      @CategoryTheory.IsIso (KLocallyRingedSpace.{u} K) _ X.toKLocallyRingedSpace
        Y.toKLocallyRingedSpace f :=
  ⟨fun ⟨⟨g, h1, h2⟩⟩ => ⟨⟨g, h1, h2⟩⟩, fun ⟨⟨g, h1, h2⟩⟩ => ⟨⟨g, h1, h2⟩⟩⟩

/-- The identification of equal restrictions lies over `X` (reassociated form). -/
theorem restrictSet_congr_iso_hom_comp_ofRestrict_assoc (X : AnalyticSpace.{u} K) {s t : Set X}
    (h : s = t) {Y : KLocallyRingedSpace.{u} K} (k : X.toKLocallyRingedSpace ⟶ Y) :
    (restrictSet_congr_iso X h).hom ≫
        KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X t) ≫ k =
      KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X s) ≫ k := by
  rw [← Category.assoc, restrictSet_congr_iso_hom_comp_ofRestrict]

/-- The inverse identification of equal restrictions lies over `X` (reassociated form). -/
theorem restrictSet_congr_iso_inv_comp_ofRestrict_assoc (X : AnalyticSpace.{u} K) {s t : Set X}
    (h : s = t) {Y : KLocallyRingedSpace.{u} K} (k : X.toKLocallyRingedSpace ⟶ Y) :
    (restrictSet_congr_iso X h).inv ≫
        KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X s) ≫ k =
      KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X t) ≫ k := by
  rw [← Category.assoc, restrictSet_congr_iso_inv_comp_ofRestrict]

/-- **Transport of the unique isomorphism over the base along an isomorphism of bases**
([Kol07, Theorem 36, proof]; [Wlo09, Theorem 6.0.6 (2)]): for `f : A ⟶ Z`, `g : B ⟶ Z'` and an
isomorphism `φ : Z ⟶ Z'`, the unique isomorphism `A | f⁻¹O' ≅ B | g'⁻¹O'` over `Z | O'` for
`g' = g ∘ φ⁻¹` and `O' = φ⁻¹O` is the unique isomorphism `A | f⁻¹(φ⁻¹O) ≅ B | g⁻¹O` over `φ | O` —
the restrictions transported along the identity of the sets `g'⁻¹O' = g⁻¹O`
(`restrictSet_congr_iso`), the compatibilities read in `Z'` (the open immersion `Z' | O ⟶ Z'` is a
monomorphism). -/
theorem Hom.existsUnique_isIso_restrictSetTo_transport {Z' : AnalyticSpace.{u} K}
    (f : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace)
    (g : B.toKLocallyRingedSpace ⟶ Z'.toKLocallyRingedSpace)
    (φ : Z.toKLocallyRingedSpace ⟶ Z'.toKLocallyRingedSpace) [CategoryTheory.IsIso φ] {O : Set Z'}
    {O' : Set Z}
    (hO' : O' = KLocallyRingedSpace.Hom.toFun φ ⁻¹' O)
    {g' : B.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace} (hg' : g' ≫ φ = g)
    (h : ∃! ψ : A.toKLocallyRingedSpace.restrictOpen
          (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' O')) ⟶
        B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g' ⁻¹' O')),
      CategoryTheory.IsIso ψ ∧ ψ ≫ Hom.restrictSetTo g' O' = Hom.restrictSetTo f O') :
    ∃! ψ : A.toKLocallyRingedSpace.restrictOpen
          (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹' (KLocallyRingedSpace.Hom.toFun φ ⁻¹' O))) ⟶
        B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' O)),
      CategoryTheory.IsIso ψ ∧ ψ ≫ Hom.restrictSetTo g O =
        Hom.restrictSetTo f (KLocallyRingedSpace.Hom.toFun φ ⁻¹' O) ≫ Hom.restrictSetTo φ O := by
  have hg'' : g' = g ≫ inv φ := (CategoryTheory.IsIso.eq_comp_inv φ).mpr hg'
  subst hO' hg''
  -- the set identity `(g ∘ φ⁻¹)⁻¹(φ⁻¹O) = g⁻¹O`
  have hS : KLocallyRingedSpace.Hom.toFun (g ≫ inv φ) ⁻¹' (KLocallyRingedSpace.Hom.toFun φ ⁻¹' O) =
      KLocallyRingedSpace.Hom.toFun g ⁻¹' O := by
    ext b
    have hb : KLocallyRingedSpace.Hom.toFun φ
        (KLocallyRingedSpace.Hom.toFun (inv φ) (KLocallyRingedSpace.Hom.toFun g b)) =
        KLocallyRingedSpace.Hom.toFun g b :=
      congrArg (fun k => KLocallyRingedSpace.Hom.toFun k (KLocallyRingedSpace.Hom.toFun g b))
        (CategoryTheory.IsIso.inv_hom_id φ)
    change KLocallyRingedSpace.Hom.toFun φ
      (KLocallyRingedSpace.Hom.toFun (inv φ) (KLocallyRingedSpace.Hom.toFun g b)) ∈ O ↔ _
    rw [hb]
    exact Iff.rfl
  obtain ⟨ψ₀, ⟨hi₀, hc₀⟩, huniq₀⟩ := h
  -- the compatibility of `ψ₀`, read in `Z'`
  have hc₀' : ψ₀ ≫ KLocallyRingedSpace.ofRestrict B.toKLocallyRingedSpace (openOf B _) ≫ g =
      KLocallyRingedSpace.ofRestrict A.toKLocallyRingedSpace (openOf A _) ≫ f ≫ φ := by
    have := congrArg (fun k => k ≫ KLocallyRingedSpace.ofRestrict Z.toKLocallyRingedSpace
      (openOf Z (KLocallyRingedSpace.Hom.toFun φ ⁻¹' O)) ≫ φ) hc₀
    simp only [Category.assoc, Hom.restrictSetTo_comp_ofRestrict_assoc,
      CategoryTheory.IsIso.inv_hom_id, Category.comp_id] at this
    exact this
  refine ⟨ψ₀ ≫ (restrictSet_congr_iso B hS).hom, ⟨inferInstance, ?_⟩, ?_⟩
  · apply KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict (U := openOf Z' O)
    simp only [Category.assoc, Hom.restrictSetTo_comp_ofRestrict_assoc,
      Hom.restrictSetTo_comp_ofRestrict, restrictSet_congr_iso_hom_comp_ofRestrict_assoc]
    exact hc₀'
  · rintro ψ' ⟨hi', hc'⟩
    have hc'' : ψ' ≫ KLocallyRingedSpace.ofRestrict B.toKLocallyRingedSpace
        (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' O)) ≫ g ≫ inv φ =
        KLocallyRingedSpace.ofRestrict A.toKLocallyRingedSpace (openOf A _) ≫ f := by
      have := congrArg (fun k => k ≫ KLocallyRingedSpace.ofRestrict Z'.toKLocallyRingedSpace
        (openOf Z' O) ≫ inv φ) hc'
      simp only [Category.assoc, Hom.restrictSetTo_comp_ofRestrict_assoc,
        Hom.restrictSetTo_comp_ofRestrict, CategoryTheory.IsIso.hom_inv_id, Category.comp_id]
        at this
      exact this
    have hu := huniq₀ (ψ' ≫ (restrictSet_congr_iso B hS).inv) ⟨inferInstance, ?_⟩
    · rw [← hu, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · apply KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict
        (U := openOf Z (KLocallyRingedSpace.Hom.toFun φ ⁻¹' O))
      simp only [Category.assoc, Hom.restrictSetTo_comp_ofRestrict,
        restrictSet_congr_iso_inv_comp_ofRestrict_assoc]
      exact hc''

end GlueOver

end AnalyticSpace
