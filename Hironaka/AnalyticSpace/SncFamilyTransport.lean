/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.SncFamily
public import Hironaka.AnalyticSpace.ClosedSubspace
public import Hironaka.AnalyticSpace.Restrict.Defs
import Hironaka.AnalyticSpace.IsoOverCover
import Hironaka.AnalyticSpace.LiftRestrictStalk
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Transport of snc families along morphisms and locality for a given family

Bookkeeping of `ClosedSubspace.IsSncFamily` (`Hironaka/AnalyticSpace/SncFamily.lean`) under the
pull-back of closed subspaces along morphisms of analytic spaces (`QuotientSpace.comap`,
`Hironaka/AnalyticSpace/QuotientMap.lean`; Hironaka's inverse image of an analytic subspace,
[Hir64, Ch. 0, §5, pp. 141–142]): the support of a pull-back is the preimage of the support; an
isomorphism carries snc families and snc boundaries to snc families and snc boundaries; and, for a
given global family, the snc condition is local on an open cover. The cover form for the predicate
`IsSncBoundary` on a divisor alone is false — a nodal cubic is locally the union of two smooth
branches without being the divisor of one global family of smooth members — so the gluing of
families over a cover is a separate construction. The pointwise clause is isolated as
`IsSncAtIdeals` on a family of ideals of a local ring and transported along a bijective ring
homomorphism (`IsSncAtIdeals.map_ringHom_of_bijective`) and back along an isomorphism of
`CommRingCat` (`IsSncAtIdeals.of_map_isIso`).

Used by `Hironaka/Resolution/Analytic/Kol07Thm45/CoproductGluedFamily.lean`,
`Hironaka/AnalyticSpace/SncBoundaryChart.lean` and
`Hironaka/Resolution/Analytic/Kol07Thm45/Glue/OverFamilyPartner.lean`.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Manifold

universe u

namespace AnalyticSpace

/-- The pointwise clause of `IsSncFamily` on a family of ideals of a local ring: a regular system of
parameters `z` and an injection `c` of the proper members into its indices with `I j = (z (c j))`.
-/
def IsSncAtIdeals {R : Type*} [CommRing R] [IsLocalRing R] {ι : Type*} (I : ι → Ideal R) : Prop :=
  ∃ (n : ℕ) (z : Fin n → R),
    (Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R) ∧
    ∃ c : {j // I j ≠ ⊤} → Fin n, Function.Injective c ∧ ∀ j, I j.1 = Ideal.span {z (c j)}

namespace IsSncAtIdeals

variable {R : Type*} [CommRing R] [IsLocalRing R] {ι : Type*}

theorem congr_ideals {I J : ι → Ideal R} (hIJ : I = J) (h : IsSncAtIdeals I) : IsSncAtIdeals J :=
  hIJ ▸ h

theorem map_ne_top_iff_of_bijective {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (hg : Function.Bijective g) (I : Ideal R) : I.map g ≠ ⊤ ↔ I ≠ ⊤ :=
  not_congr ⟨fun h => by
    rw [← Ideal.comap_map_of_bijective g hg (I := I), h, Ideal.comap_top],
    fun h => by rw [h, Ideal.map_top]⟩

variable {S : Type*} [CommRing S] [IsLocalRing S]

/-- The pointwise clause transports along a bijective ring homomorphism. -/
theorem map_ringHom_of_bijective {I : ι → Ideal R} (g : R →+* S)
    (hg : Function.Bijective g) (h : IsSncAtIdeals I) :
    IsSncAtIdeals fun j => (I j).map g := by
  obtain ⟨n, z, ⟨hz, hn⟩, c, hc, hcz⟩ := h
  let e : {j // (I j).map g ≠ ⊤} → {j // I j ≠ ⊤} :=
    fun j => ⟨j.1, (map_ne_top_iff_of_bijective g hg _).mp j.2⟩
  refine ⟨n, g ∘ z, ⟨?_, ?_⟩, fun j => c (e j),
    fun j₁ j₂ h => Subtype.ext (show (e j₁).1 = (e j₂).1 from congrArg Subtype.val (hc h)),
    fun j => ?_⟩
  · rw [Set.range_comp, ← Ideal.map_span, hz, IsLocalRing.map_maximalIdeal_of_surjective g hg.2]
  · rw [hn, ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective g hg)]
  · change (I j.1).map g = _
    rw [hcz (e j), Ideal.map_span, Set.image_singleton]
    rfl

/-- The pointwise clause transports back along an isomorphism of commutative rings (the target's
local-ring instance is passed explicitly: on a restricted space it is not found by search). -/
theorem of_map_isIso {R S : CommRingCat.{u}} [IsLocalRing R] (instS : IsLocalRing S) (g : R ⟶ S)
    (hg : IsIso g) {I : ι → Ideal R}
    (h : @IsSncAtIdeals S _ instS ι fun j => (I j).map g.hom) : IsSncAtIdeals I := by
  have := instS
  have := hg
  refine (h.map_ringHom_of_bijective (CategoryTheory.inv g).hom
    (ConcreteCategory.bijective_of_isIso _)).congr_ideals (funext fun j => ?_)
  change ((I j).map g.hom).map (CategoryTheory.inv g).hom = I j
  rw [Ideal.map_map, ← CommRingCat.hom_comp, IsIso.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]

end IsSncAtIdeals

namespace ClosedSubspace

variable {K : Type} [RCLike K] {X Y : AnalyticSpace.{u} K}

theorem isSncFamily_iff_isSncAtIdeals {ι : Type u} (H : ι → ClosedSubspace X) :
    IsSncFamily H ↔ LocallyFinite (fun j => (H j).support) ∧
      ∀ x : X, IsSncAtIdeals fun j => (H j).stalkIdeal x :=
  Iff.rfl

/-- The support of the pull-back of a closed subspace along a morphism is the preimage of its
support (Hironaka's inverse image, [Hir64, Ch. 0, §5, pp. 141–142];
`QuotientSpace.cosupport_comap`). Named apart from `HypersurfaceFamily.support_comap`. -/
theorem support_comap_eq_preimage (f : Y ⟶ X) (D : ClosedSubspace X) :
    IdealSheaf.support (QuotientSpace.comap f.1 D) =
      ⇑f ⁻¹' D.support :=
  QuotientSpace.cosupport_comap f.1 D

/-- An isomorphism of analytic spaces carries an snc family of closed subspaces to an snc family
([Kol07, Definition 24] is pointwise): its stalk maps are ring isomorphisms, so regular systems of
parameters go to regular systems and the members' principal stalk ideals to principal ideals
(`QuotientSpace.stalkIdeal_comap`). -/
theorem isSncFamily_comap_of_isIso {ι : Type u} (f : Y ⟶ X) (hf : IsIso f)
    {H : ι → ClosedSubspace X} (h : IsSncFamily H) :
    IsSncFamily fun j => (QuotientSpace.comap f.1 (H j) : ClosedSubspace Y) := by
  have : IsIso f := hf
  have : @IsIso (KLocallyRingedSpace.{u} K) _ Y.toKLocallyRingedSpace X.toKLocallyRingedSpace f :=
    AnalyticSpace.isIso_toKLocallyRingedSpace_of_isIso f
  rw [isSncFamily_iff_isSncAtIdeals] at h ⊢
  refine ⟨?_, fun y => ?_⟩
  · have hsupp : (fun j => IdealSheaf.support (QuotientSpace.comap f.1 (H j))) =
        fun j => ⇑f ⁻¹' (H j).support :=
      funext fun j => support_comap_eq_preimage f (H j)
    rw [hsupp]
    exact h.1.preimage_continuous (KLocallyRingedSpace.Hom.continuous_toFun f)
  · have hb := KLocallyRingedSpace.bijective_stalkMap_of_isIso
      (f : Y.toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace) y
    refine ((h.2 (f y)).map_ringHom_of_bijective _ hb).congr_ideals
      (funext fun j => ?_)
    exact (QuotientSpace.stalkIdeal_comap f.1 (H j) y).symm

/-- An isomorphism of analytic spaces carries an snc boundary to an snc boundary: the family, the
regular systems of parameters and the product clause transport along the stalk isomorphisms. -/
theorem isSncBoundary_comap_of_isIso (f : Y ⟶ X) (hf : IsIso f)
    {E : ClosedSubspace X} (h : E.IsSncBoundary) :
    ClosedSubspace.IsSncBoundary (X := Y) (QuotientSpace.comap f.1 E) := by
  have : IsIso f := hf
  have : @IsIso (KLocallyRingedSpace.{u} K) _ Y.toKLocallyRingedSpace X.toKLocallyRingedSpace f :=
    AnalyticSpace.isIso_toKLocallyRingedSpace_of_isIso f
  obtain ⟨ι, H, hlf, hx⟩ := h
  refine ⟨ι, fun j => QuotientSpace.comap f.1 (H j), ?_, fun y => ?_⟩
  · have hsupp : (fun j => IdealSheaf.support (QuotientSpace.comap f.1 (H j))) =
        fun j => ⇑f ⁻¹' (H j).support :=
      funext fun j => support_comap_eq_preimage f (H j)
    rw [hsupp]
    exact hlf.preimage_continuous (KLocallyRingedSpace.Hom.continuous_toFun f)
  · obtain ⟨n, z, ⟨hz, hn⟩, ⟨c, s, hc, hrange, hcz, hE⟩, -⟩ := hx (f.1.base y)
    have hb := KLocallyRingedSpace.bijective_stalkMap_of_isIso
      (A := Y.toKLocallyRingedSpace) (B := X.toKLocallyRingedSpace) f y
    have hmem : ∀ j, y ∈ IdealSheaf.support (QuotientSpace.comap f.1 (H j)) ↔
        f.1.base y ∈ (H j).support := fun j => by
      rw [support_comap_eq_preimage]; exact Iff.rfl
    let e : {j // y ∈ IdealSheaf.support (QuotientSpace.comap f.1 (H j))} →
        {j // f.1.base y ∈ (H j).support} := fun j => ⟨j.1, (hmem j.1).mp j.2⟩
    have he : Function.Surjective e := fun j' => ⟨⟨j'.1, (hmem j'.1).mpr j'.2⟩, rfl⟩
    refine ⟨n, (f.1.stalkMap y).hom ∘ z, ⟨?_, ?_⟩, ⟨fun j => c (e j), s,
      fun j₁ j₂ h => Subtype.ext (show (e j₁).1 = (e j₂).1 from congrArg Subtype.val (hc h)),
      ?_, fun j => ?_, ?_⟩, fun _ => ⟨∅, ?_⟩⟩
    · rw [Set.range_comp, ← Ideal.map_span, hz,
        IsLocalRing.map_maximalIdeal_of_surjective _ hb.2]
    · rw [hn, ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)]
    · rw [show (fun j => c (e j)) = c ∘ e from rfl, he.range_comp, hrange]
    · have hj := hcz (e j)
      change (H j.1).stalkIdeal (f.1.base y) = _ at hj
      have hcm := QuotientSpace.stalkIdeal_comap f.1 (H j.1) y
      change (QuotientSpace.comap f.1 (H j.1)).stalkIdeal y =
        Ideal.map (f.1.stalkMap y).hom ((H j.1).stalkIdeal (f.1.base y)) at hcm
      change (QuotientSpace.comap f.1 (H j.1)).stalkIdeal y = _
      rw [hcm, hj]
      exact (Ideal.map_span _ _).trans (congrArg Ideal.span Set.image_singleton)
    · have hcm := QuotientSpace.stalkIdeal_comap f.1 E y
      change (QuotientSpace.comap f.1 E).stalkIdeal y =
        Ideal.map (f.1.stalkMap y).hom (E.stalkIdeal (f.1.base y)) at hcm
      change (QuotientSpace.comap f.1 E).stalkIdeal y = _
      rw [hcm, hE]
      exact (Ideal.map_span _ _).trans (congrArg Ideal.span (Set.image_singleton.trans
        (congrArg (fun t => ({t} : Set _)) (map_prod _ _ _))))
    · rw [IdealSheaf.stalkIdeal_bot, Finset.coe_empty, Set.image_empty, Ideal.span_empty]
      rfl

/-- For a given global family the snc condition is local: local finiteness and the pointwise stalk
clause are read on an open cover, along the inclusions `X | Uᵢ ⟶ X` of `K`-locally ringed spaces
(`KLocallyRingedSpace.ofRestrict`), whose stalk maps are isomorphisms. No gluing of index sets is
involved. -/
theorem isSncFamily_of_openCover {ι : Type u} {ι' : Type*} (U : ι' → Opens X)
    (hU : (⋃ i, (U i : Set X)) = Set.univ) (H : ι → ClosedSubspace X)
    (h : ∀ i, IsSncFamily fun j =>
      (QuotientSpace.comap (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (U i)).1 (H j) :
        ClosedSubspace (X.restrictOpen (U i)))) :
    IsSncFamily H := by
  have hcov : ∀ x : X, ∃ i, x ∈ U i := fun x =>
    Set.mem_iUnion.mp (hU.symm ▸ Set.mem_univ x)
  rw [isSncFamily_iff_isSncAtIdeals]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · obtain ⟨i, hx⟩ := hcov x
    obtain ⟨t, ht, hfin⟩ := (h i).1 (⟨x, hx⟩ : X.restrictOpen (U i))
    refine ⟨Subtype.val '' t, ?_, hfin.subset fun j ⟨y, hy, hyt⟩ => ?_⟩
    · have := (Opens.isOpenEmbedding (U i)).map_nhds_eq ⟨x, hx⟩
      exact this ▸ Filter.image_mem_map ht
    · obtain ⟨y', hy't, rfl⟩ := hyt
      refine ⟨y', ?_, hy't⟩
      change y' ∈ (QuotientSpace.comap
        (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (U i)).1 (H j)).support
      rw [QuotientSpace.cosupport_comap]
      exact hy
  · obtain ⟨i, hx⟩ := hcov x
    obtain ⟨n, z, ⟨hz, hn⟩, c, hc, hcz⟩ := (h i).2 (⟨x, hx⟩ : X.restrictOpen (U i))
    have instS : IsLocalRing
        ((X.restrictOpen (U i)).presheaf.stalk (⟨x, hx⟩ : X.restrictOpen (U i))) :=
      (X.restrictOpen (U i)).toLocallyRingedSpace.isLocalRing _
    have hpt : @IsSncAtIdeals _ _ instS _ (fun j =>
        (QuotientSpace.comap (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (U i)).1
          (H j) : ClosedSubspace (X.restrictOpen (U i))).stalkIdeal
            (⟨x, hx⟩ : X.restrictOpen (U i))) :=
      ⟨n, z, ⟨hz, hn⟩, c, hc, hcz⟩
    refine IsSncAtIdeals.of_map_isIso instS
      ((KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (U i)).1.stalkMap
        (⟨x, hx⟩ : X.restrictOpen (U i)))
      (KLocallyRingedSpace.isIso_ofRestrict_stalkMap X.toKLocallyRingedSpace (U i)
        (⟨x, hx⟩ : X.restrictOpen (U i))) ?_
    exact Eq.mp (congrArg (@IsSncAtIdeals _ _ instS _)
      (funext fun j => QuotientSpace.stalkIdeal_comap
        (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (U i)).1 (H j)
        (⟨x, hx⟩ : X.restrictOpen (U i)))) hpt

end ClosedSubspace

end AnalyticSpace

end
