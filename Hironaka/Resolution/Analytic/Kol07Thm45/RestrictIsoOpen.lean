/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.RestrictSetIncl
public import Hironaka.AnalyticSpace.HomOfSections
import Hironaka.AnalyticSpace.RegOpenImmersion
import Hironaka.AnalyticSpace.RestrictToIso
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Restricting an isomorphism of open subspaces to a smaller open

For a morphism `φ : X|U → Y|V` of the open subspaces `restrictSet` and an open `S ⊆ V`, the
preimage `φ⁻¹S ⊆ U` (`Hom.preimageOpen`), the image `φ(P) ⊆ V` of a set `P ⊆ U` (`Hom.imageOpen`),
and the restriction
`φ|φ⁻¹S : X|φ⁻¹S → Y|S` (`Hom.restrictIsoTo`, the lift of `X|φ⁻¹S → X|U → Y|V → Y` through the
open immersion `Y|S → Y`), which lies over `φ` (`restrictIsoTo_comp_restrictSetIncl`) and is an
isomorphism when `φ` is (`isIso_restrictIsoTo`, the inverse being the restriction of `φ⁻¹`).
Needed for the functoriality of the resolution under isomorphisms of open subspaces (clause (5) of
the resolution theorem; the functoriality in the proof of [Kol07, Theorem 36]), which transports a
piece embedding of `Y` near `φ x` along `φ`
(`Hironaka/Resolution/Analytic/Kol07Thm45/ResolutionFunctorial.lean`) and needs `φ` restricted to
the open of that piece — an isomorphism `X|φ⁻¹O' ≅ Y|O'` of the open subspaces of the vocabulary,
not the nested `(X|U)|…`. The open subspaces are Hironaka's `X | U` [Hir64, Ch. 0, §1, p. 120].
Routine.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K] {X Y : AnalyticSpace.{u} K} {U : Set X} {V : Set Y}

/-- The preimage in `X` of a set `S ⊆ Y` under
`φ : X|U → Y|V`: the points of `U` whose image lies in `S`. -/
def Hom.preimageOpen (φ : X.restrictSet U ⟶ Y.restrictSet V) (S : Set Y) : Set X :=
  Subtype.val '' (KLocallyRingedSpace.Hom.toFun φ ⁻¹' (Subtype.val ⁻¹' S))

/-- The preimage of an open is open (`Subtype.val` is an open map on the open subspace). -/
theorem Hom.isOpen_preimageOpen (φ : X.restrictSet U ⟶ Y.restrictSet V) (S : Set Y)
    (hS : IsOpen S) : IsOpen (Hom.preimageOpen φ S) :=
  (openOf X U).isOpen.isOpenEmbedding_subtypeVal.isOpenMap _
    ((hS.preimage continuous_subtype_val).preimage (KLocallyRingedSpace.Hom.continuous_toFun φ))

/-- The preimage lies in `U`. -/
theorem Hom.preimageOpen_subset (φ : X.restrictSet U ⟶ Y.restrictSet V) (hU : IsOpen U)
    (S : Set Y) : Hom.preimageOpen φ S ⊆ U := by
  rintro _ ⟨p, -, rfl⟩
  exact (mem_openOf_iff_of_isOpen X hU p.1).mp p.2

/-- Membership in the preimage. -/
theorem Hom.mem_preimageOpen_iff (φ : X.restrictSet U ⟶ Y.restrictSet V) (S : Set Y) (x : X) :
    x ∈ Hom.preimageOpen φ S ↔
      ∃ p : X.restrictSet U, p.1 = x ∧ (KLocallyRingedSpace.Hom.toFun φ p).1 ∈ S :=
  ⟨fun ⟨p, hp, hpx⟩ => ⟨p, hpx, hp⟩, fun ⟨p, hpx, hp⟩ => ⟨p, hp, hpx⟩⟩

/-- The image in `Y` of a set `P ⊆ X` under `φ : X|U → Y|V`. -/
def Hom.imageOpen (φ : X.restrictSet U ⟶ Y.restrictSet V) (P : Set X) : Set Y :=
  Subtype.val '' (KLocallyRingedSpace.Hom.toFun φ '' (Subtype.val ⁻¹' P))

/-- The image of an open under an isomorphism is open (the underlying homeomorphism
`KIso.homeomorph`, then `Subtype.val`). -/
theorem Hom.isOpen_imageOpen (φ : X.restrictSet U ⟶ Y.restrictSet V) (hφ : IsIso φ)
    (P : Set X) (hP : IsOpen P) : IsOpen (Hom.imageOpen φ P) := by
  have hK : @CategoryTheory.IsIso (KLocallyRingedSpace.{u} K) _ _ _ φ :=
    (Hom.isIso_iff_isIso_toKLocallyRingedSpace φ).mp hφ
  have hmap : IsOpenMap (KLocallyRingedSpace.Hom.toFun φ) := by
    have he := (KLocallyRingedSpace.KIso.homeomorph (@asIso _ _ _ _ φ hK)).isOpenMap
    have hfun : ⇑(KLocallyRingedSpace.KIso.homeomorph (@asIso _ _ _ _ φ hK)) =
        KLocallyRingedSpace.Hom.toFun φ :=
      funext fun x => by rw [KLocallyRingedSpace.KIso.homeomorph_apply, asIso_hom]
    rwa [hfun] at he
  exact (openOf Y V).isOpen.isOpenEmbedding_subtypeVal.isOpenMap _
    (hmap _ (hP.preimage continuous_subtype_val))

/-- The image lies in `V`. -/
theorem Hom.imageOpen_subset (φ : X.restrictSet U ⟶ Y.restrictSet V) (hV : IsOpen V)
    (P : Set X) : Hom.imageOpen φ P ⊆ V := by
  rintro _ ⟨q, -, rfl⟩
  exact (mem_openOf_iff_of_isOpen Y hV q.1).mp q.2

/-- Membership in the image. -/
theorem Hom.mem_imageOpen_iff (φ : X.restrictSet U ⟶ Y.restrictSet V) (P : Set X) (y : Y) :
    y ∈ Hom.imageOpen φ P ↔
      ∃ p : X.restrictSet U, p.1 ∈ P ∧ (KLocallyRingedSpace.Hom.toFun φ p).1 = y := by
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩

/-- For an isomorphism, the preimage of the image of `P ⊆ U` is `P`
(`injective_toFun_of_isIso`). -/
theorem Hom.preimageOpen_imageOpen (φ : X.restrictSet U ⟶ Y.restrictSet V) (hφ : IsIso φ)
    (hU : IsOpen U) (P : Set X) (hPU : P ⊆ U) :
    Hom.preimageOpen φ (Hom.imageOpen φ P) = P := by
  have hinj : Function.Injective (KLocallyRingedSpace.Hom.toFun φ) :=
    injective_toFun_of_isIso φ hφ
  ext x
  rw [Hom.mem_preimageOpen_iff]
  constructor
  · rintro ⟨p, rfl, hp⟩
    obtain ⟨q, hq, hqp⟩ := (Hom.mem_imageOpen_iff φ P _).mp hp
    have hqp' : q = p := hinj (Subtype.ext hqp)
    exact hqp' ▸ hq
  · intro hx
    exact ⟨⟨x, (mem_openOf_iff_of_isOpen X hU x).mpr (hPU hx)⟩, rfl,
      (Hom.mem_imageOpen_iff φ P _).mpr ⟨_, hx, rfl⟩⟩

/-- **The restriction of `φ : X|U → Y|V` to an open
`S ⊆ V`**, `X|φ⁻¹S → Y|S`: the lift of `X|φ⁻¹S → X|U → Y|V → Y` through the open immersion
`Y|S → Y` (`Hom.liftRestrict`). -/
noncomputable def Hom.restrictIsoTo (φ : X.restrictSet U ⟶ Y.restrictSet V) (hU : IsOpen U)
    (S : Set Y) (hS : IsOpen S) :
    X.toKLocallyRingedSpace.restrictOpen (openOf X (Hom.preimageOpen φ S)) ⟶
      Y.toKLocallyRingedSpace.restrictOpen (openOf Y S) :=
  KLocallyRingedSpace.Hom.liftRestrict
    (restrictSetIncl X (Hom.isOpen_preimageOpen φ S hS) (Hom.preimageOpen_subset φ hU S) ≫
      φ ≫ KLocallyRingedSpace.ofRestrict Y.toKLocallyRingedSpace (openOf Y V))
    (openOf Y S) fun p => by
      obtain ⟨q, hqp, hq⟩ := (Hom.mem_preimageOpen_iff φ S p.1).mp
        ((mem_openOf_iff_of_isOpen X (Hom.isOpen_preimageOpen φ S hS) p.1).mp p.2)
      have hq' : KLocallyRingedSpace.Hom.toFun
          (restrictSetIncl X (Hom.isOpen_preimageOpen φ S hS) (Hom.preimageOpen_subset φ hU S))
            p = q :=
        Subtype.ext ((toFun_restrictSetIncl X _ _ p).trans hqp.symm)
      exact (congrArg (fun r => (KLocallyRingedSpace.Hom.toFun φ r).1 ∈ openOf Y S) hq').mpr
        ((mem_openOf_iff_of_isOpen Y hS _).mpr hq)

/-- The defining factorization of the restriction: followed by the open immersion `Y|S → Y` it is
`X|φ⁻¹S → X|U → Y|V → Y`. -/
theorem Hom.restrictIsoTo_comp_ofRestrict (φ : X.restrictSet U ⟶ Y.restrictSet V) (hU : IsOpen U)
    (S : Set Y) (hS : IsOpen S) :
    Hom.restrictIsoTo φ hU S hS ≫
        KLocallyRingedSpace.ofRestrict Y.toKLocallyRingedSpace (openOf Y S) =
      restrictSetIncl X (Hom.isOpen_preimageOpen φ S hS) (Hom.preimageOpen_subset φ hU S) ≫
        φ ≫ KLocallyRingedSpace.ofRestrict Y.toKLocallyRingedSpace (openOf Y V) :=
  KLocallyRingedSpace.Hom.liftRestrict_comp_ofRestrict _ _ _

/-- The restriction lies over `φ`: followed by the inclusion `Y|S → Y|V` it is the inclusion
`X|φ⁻¹S → X|U` followed by `φ` (both sides agree after the monomorphism `Y|V → Y`). -/
theorem Hom.restrictIsoTo_comp_restrictSetIncl (φ : X.restrictSet U ⟶ Y.restrictSet V)
    (hU : IsOpen U) (S : Set Y) (hS : IsOpen S) (hSV : S ⊆ V) :
    Hom.restrictIsoTo φ hU S hS ≫ restrictSetIncl Y hS hSV =
      restrictSetIncl X (Hom.isOpen_preimageOpen φ S hS) (Hom.preimageOpen_subset φ hU S) ≫ φ :=
  KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict (U := openOf Y V)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => Hom.restrictIsoTo φ hU S hS ≫ k)
        (restrictSetIncl_comp_ofRestrict Y hS hSV)).trans
        ((Hom.restrictIsoTo_comp_ofRestrict φ hU S hS).trans (Category.assoc _ _ _).symm)))

/-- The restriction on points: the image of `p` is the image under `φ` of `p` read in
`X|U`. -/
theorem Hom.toFun_restrictIsoTo (φ : X.restrictSet U ⟶ Y.restrictSet V) (hU : IsOpen U)
    (S : Set Y) (hS : IsOpen S)
    (p : X.toKLocallyRingedSpace.restrictOpen (openOf X (Hom.preimageOpen φ S))) :
    (KLocallyRingedSpace.Hom.toFun (Hom.restrictIsoTo φ hU S hS) p).1 =
      (KLocallyRingedSpace.Hom.toFun φ (KLocallyRingedSpace.Hom.toFun
        (restrictSetIncl X (Hom.isOpen_preimageOpen φ S hS) (Hom.preimageOpen_subset φ hU S))
          p)).1 :=
  congrArg (fun k => KLocallyRingedSpace.Hom.toFun k p)
    (Hom.restrictIsoTo_comp_ofRestrict φ hU S hS)

/-- A point of `X|φ⁻¹S` maps into the image of `P` iff it lies in `P`
(`injective_toFun_of_isIso`). -/
theorem Hom.toFun_restrictIsoTo_mem_imageOpen_iff (φ : X.restrictSet U ⟶ Y.restrictSet V)
    (hφ : IsIso φ) (hU : IsOpen U) (S : Set Y) (hS : IsOpen S) (P : Set X)
    (p : X.toKLocallyRingedSpace.restrictOpen (openOf X (Hom.preimageOpen φ S))) :
    (KLocallyRingedSpace.Hom.toFun (Hom.restrictIsoTo φ hU S hS) p).1 ∈ Hom.imageOpen φ P ↔
      p.1 ∈ P := by
  have hinj : Function.Injective (KLocallyRingedSpace.Hom.toFun φ) :=
    injective_toFun_of_isIso φ hφ
  rw [Hom.toFun_restrictIsoTo, Hom.mem_imageOpen_iff]
  constructor
  · rintro ⟨q, hq, hqp⟩
    have hqp' : q = KLocallyRingedSpace.Hom.toFun
        (restrictSetIncl X (Hom.isOpen_preimageOpen φ S hS) (Hom.preimageOpen_subset φ hU S)) p :=
      hinj (Subtype.ext hqp)
    exact (congrArg (· ∈ P) (toFun_restrictSetIncl X _ _ p)).mp (hqp' ▸ hq)
  · intro hp
    exact ⟨_, (congrArg (· ∈ P) (toFun_restrictSetIncl X _ _ p)).mpr hp, rfl⟩

/-- The inverse of the restriction of an isomorphism: the restriction of `φ⁻¹` to `φ⁻¹S`, as the
lift of `Y|S → Y|V → X|U → X` through `X|φ⁻¹S → X`. -/
noncomputable def Hom.restrictIsoToInv (φ : X.restrictSet U ⟶ Y.restrictSet V) (hφ : IsIso φ)
    (S : Set Y) (hS : IsOpen S) (hSV : S ⊆ V) :
    Y.toKLocallyRingedSpace.restrictOpen (openOf Y S) ⟶
      X.toKLocallyRingedSpace.restrictOpen (openOf X (Hom.preimageOpen φ S)) :=
  KLocallyRingedSpace.Hom.liftRestrict
    (restrictSetIncl Y hS hSV ≫
      @inv (KLocallyRingedSpace.{u} K) _ _ _ φ
        ((Hom.isIso_iff_isIso_toKLocallyRingedSpace φ).mp hφ) ≫
      KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X U))
    (openOf X (Hom.preimageOpen φ S)) fun q => by
      have hK : @CategoryTheory.IsIso (KLocallyRingedSpace.{u} K) _ _ _ φ :=
        (Hom.isIso_iff_isIso_toKLocallyRingedSpace φ).mp hφ
      have hφψ : KLocallyRingedSpace.Hom.toFun φ (KLocallyRingedSpace.Hom.toFun
          (@inv (KLocallyRingedSpace.{u} K) _ _ _ φ hK)
            (KLocallyRingedSpace.Hom.toFun (restrictSetIncl Y hS hSV) q)) =
          KLocallyRingedSpace.Hom.toFun (restrictSetIncl Y hS hSV) q :=
        congrArg (fun k => KLocallyRingedSpace.Hom.toFun k
          (KLocallyRingedSpace.Hom.toFun (restrictSetIncl Y hS hSV) q))
          (@CategoryTheory.IsIso.inv_hom_id (KLocallyRingedSpace.{u} K) _ _ _ φ hK)
      refine (mem_openOf_iff_of_isOpen X (Hom.isOpen_preimageOpen φ S hS) _).mpr ?_
      refine (Hom.mem_preimageOpen_iff φ S _).mpr ⟨_, rfl, ?_⟩
      exact (congrArg (fun r => r.1 ∈ S) hφψ).mpr
        ((congrArg (· ∈ S) (toFun_restrictSetIncl Y hS hSV q)).mpr
          ((mem_openOf_iff_of_isOpen Y hS _).mp q.2))

/-- The inverse's factorization through the open immersion `X|φ⁻¹S → X`. -/
theorem Hom.restrictIsoToInv_comp_ofRestrict (φ : X.restrictSet U ⟶ Y.restrictSet V)
    (hφ : IsIso φ) (S : Set Y) (hS : IsOpen S) (hSV : S ⊆ V) :
    Hom.restrictIsoToInv φ hφ S hS hSV ≫
        KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X (Hom.preimageOpen φ S)) =
      restrictSetIncl Y hS hSV ≫
        @inv (KLocallyRingedSpace.{u} K) _ _ _ φ
          ((Hom.isIso_iff_isIso_toKLocallyRingedSpace φ).mp hφ) ≫
        KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X U) :=
  KLocallyRingedSpace.Hom.liftRestrict_comp_ofRestrict _ _ _

/-- The restriction of an isomorphism is an isomorphism: the inverse is the restriction of
`φ⁻¹` (`restrictIsoToInv`); both composites are the identity after the monomorphisms
`X|φ⁻¹S → X`, `Y|S → Y`. -/
theorem Hom.isIso_restrictIsoTo (φ : X.restrictSet U ⟶ Y.restrictSet V) (hφ : IsIso φ)
    (hU : IsOpen U) (S : Set Y) (hS : IsOpen S) (hSV : S ⊆ V) :
    CategoryTheory.IsIso (Hom.restrictIsoTo φ hU S hS) := by
  have hK : @CategoryTheory.IsIso (KLocallyRingedSpace.{u} K) _ _ _ φ :=
    (Hom.isIso_iff_isIso_toKLocallyRingedSpace φ).mp hφ
  -- `χ ≫ (X|φ⁻¹S → X|U) = (Y|S → Y|V) ≫ φ⁻¹` after the monomorphism `X|U → X`
  have hχ : Hom.restrictIsoToInv φ hφ S hS hSV ≫
      restrictSetIncl X (Hom.isOpen_preimageOpen φ S hS) (Hom.preimageOpen_subset φ hU S) =
        restrictSetIncl Y hS hSV ≫ @inv (KLocallyRingedSpace.{u} K) _ _ _ φ hK :=
    KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict (U := openOf X U)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => Hom.restrictIsoToInv φ hφ S hS hSV ≫ k)
          (restrictSetIncl_comp_ofRestrict X _ _)).trans
          ((Hom.restrictIsoToInv_comp_ofRestrict φ hφ S hS hSV).trans
            (Category.assoc _ _ _).symm)))
  refine ⟨⟨Hom.restrictIsoToInv φ hφ S hS hSV, ?_, ?_⟩⟩
  · -- after `X|φ⁻¹S → X`: `ι ≫ φ ≫ φ⁻¹ ≫ X|U → X = ι ≫ X|U → X = X|φ⁻¹S → X`
    refine KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict (U := openOf X (Hom.preimageOpen φ S))
      ((Category.assoc _ _ _).trans ?_)
    refine (congrArg (fun k => Hom.restrictIsoTo φ hU S hS ≫ k)
      (Hom.restrictIsoToInv_comp_ofRestrict φ hφ S hS hSV)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ (@inv (KLocallyRingedSpace.{u} K) _ _ _ φ hK ≫
      KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X U)))
      (Hom.restrictIsoTo_comp_restrictSetIncl φ hU S hS hSV)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => restrictSetIncl X (Hom.isOpen_preimageOpen φ S hS)
      (Hom.preimageOpen_subset φ hU S) ≫ k)
      (@CategoryTheory.IsIso.hom_inv_id_assoc (KLocallyRingedSpace.{u} K) _ _ _ φ hK _
        (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (openOf X U)))).trans ?_
    exact (restrictSetIncl_comp_ofRestrict X _ _).trans (Category.id_comp _).symm
  · -- after `Y|S → Y`: `χ ≫ ι ≫ φ ≫ Y|V → Y = (Y|S → Y|V) ≫ φ⁻¹ ≫ φ ≫ Y|V → Y = Y|S → Y`
    refine KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict (U := openOf Y S)
      ((Category.assoc _ _ _).trans ?_)
    refine (congrArg (fun k => Hom.restrictIsoToInv φ hφ S hS hSV ≫ k)
      (Hom.restrictIsoTo_comp_ofRestrict φ hU S hS)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k : Y.toKLocallyRingedSpace.restrictOpen (openOf Y S) ⟶
        X.toKLocallyRingedSpace.restrictOpen (openOf X U) => k ≫ (φ ≫
      KLocallyRingedSpace.ofRestrict Y.toKLocallyRingedSpace (openOf Y V))) hχ).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => restrictSetIncl Y hS hSV ≫ k)
      (@CategoryTheory.IsIso.inv_hom_id_assoc (KLocallyRingedSpace.{u} K) _ _ _ φ hK _
        (KLocallyRingedSpace.ofRestrict Y.toKLocallyRingedSpace (openOf Y V)))).trans ?_
    exact (restrictSetIncl_comp_ofRestrict Y hS hSV).trans (Category.id_comp _).symm

end AnalyticSpace
