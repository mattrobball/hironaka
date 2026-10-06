/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Admissible
public import Hironaka.Scheme.BlowUp.Glue.BlowUp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The glued blow-up of an affine scheme is the affine blow-up

The blow-up `blowUp I` is glued from the affine blow-ups `affineBlowUp (I.ideal U)` over the
affine opens `U` of `X` [Sta, Tag 01OF], the component `blowUp.ι I U` being an open immersion
with image `π⁻¹(U)`.  For `X = Spec R` and `U = ⊤` the component is therefore an isomorphism
onto the whole blow-up, and its source `affineBlowUp (I.ideal ⊤)` is the affine blow-up of `J`
itself through the ring isomorphism `R ≅ Γ(Spec R, ⊤)` (`affineBlowUp.mapOfEq`).  This module
packages the composite as `blowUpSpecIso J : blowUp (specIdealSheaf J) ≅ affineBlowUp J`, over
`Spec R` (`blowUpSpecIso_hom_π`), together with the transport of inverse images along it — the
identification through which the charts of the blow-up of an affine scheme (such as the charts
of `B_0 𝔸⁴` in Kollár's worked example [Kol07, Example 106]) are read off the affine blow-up
[Sta, Tag 0804]; [Hau14, Theorem 4.19].
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData

namespace Hironaka.BlowUp

open AlgebraicGeometry Scheme.IdealSheafData

variable {R : Type u} [CommRing R] (J : Ideal R)

/-- `⊤` as an affine open of `Spec R`. -/
noncomputable abbrev topAffineOpen : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩

/-- `Γ(Spec R, ⊤) → R → Γ(Spec R, ⊤)` is the identity (the two halves of `ΓSpecIso`). -/
theorem ΓSpecIso_inv_hom_comp_hom_hom :
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).comp (Scheme.ΓSpecIso (.of R)).hom.hom =
      RingHom.id _ := by
  rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]

/-- `R → Γ(Spec R, ⊤) → R` is the identity. -/
theorem ΓSpecIso_hom_hom_comp_inv_hom :
    ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom).comp (Scheme.ΓSpecIso (.of R)).inv.hom =
      RingHom.id R := by
  rw [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id]

/-- The sections of `specIdealSheaf J` over `⊤` are the image of `J` in `Γ(Spec R, ⊤)`. -/
theorem map_eq_ideal_topAffineOpen :
    J.map (Scheme.ΓSpecIso (.of R)).inv.hom = (specIdealSheaf J).ideal topAffineOpen :=
  (specIdealSheaf_ideal_top J).symm

/-- The image of those sections back in `R` is `J`. -/
theorem ideal_topAffineOpen_map_eq :
    ((specIdealSheaf J).ideal topAffineOpen).map (Scheme.ΓSpecIso (.of R)).hom.hom = J := by
  rw [← map_eq_ideal_topAffineOpen, Ideal.map_map, ΓSpecIso_hom_hom_comp_inv_hom, Ideal.map_id]

/-- Over `X = Spec R` the component `ι ⊤` of the gluing is an isomorphism — an open immersion
whose image `π⁻¹(⊤)` is everything [Sta, Tag 0804]. -/
instance isIso_ι_topAffineOpen : IsIso (blowUp.ι (specIdealSheaf J) topAffineOpen) := by
  have hsurj : Function.Surjective (blowUp.ι (specIdealSheaf J) topAffineOpen).base := fun x => by
    have hx : x ∈ (blowUp.ι (specIdealSheaf J) topAffineOpen).opensRange := by
      rw [blowUp.opensRange_ι]
      exact Set.mem_univ _
    exact hx
  have : Epi (blowUp.ι (specIdealSheaf J) topAffineOpen).base :=
    (TopCat.epi_iff_surjective _).mpr hsurj
  exact IsOpenImmersion.isIso _

/-- **The glued blow-up of `Spec R` along the ideal sheaf of `J` is the affine blow-up of `J`**
[Sta, Tags 01OF and 0804]: the inverse of the component `ι ⊤` followed by the affine blow-up's
functoriality along `R ≅ Γ(Spec R, ⊤)`. -/
noncomputable def blowUpSpecIso : blowUp (specIdealSheaf J) ≅ affineBlowUp J where
  hom := inv (blowUp.ι (specIdealSheaf J) topAffineOpen) ≫
    affineBlowUp.mapOfEq (Scheme.ΓSpecIso (.of R)).inv.hom (map_eq_ideal_topAffineOpen J)
  inv := affineBlowUp.mapOfEq (Scheme.ΓSpecIso (.of R)).hom.hom (ideal_topAffineOpen_map_eq J) ≫
    blowUp.ι (specIdealSheaf J) topAffineOpen
  hom_inv_id := by
    rw [Category.assoc, ← Category.assoc (affineBlowUp.mapOfEq _ _),
      ← affineBlowUp.mapOfEq_eq_comp rfl (ideal_topAffineOpen_map_eq J)
        (map_eq_ideal_topAffineOpen J)
        (by rw [ΓSpecIso_inv_hom_comp_hom_hom, Ideal.map_id]),
      affineBlowUp.mapOfEq_eq_id (ΓSpecIso_inv_hom_comp_hom_hom (R := R)), Category.id_comp,
      IsIso.inv_hom_id]
  inv_hom_id := by
    rw [Category.assoc, IsIso.hom_inv_id_assoc,
      ← affineBlowUp.mapOfEq_eq_comp rfl (map_eq_ideal_topAffineOpen J)
        (ideal_topAffineOpen_map_eq J)
        (by rw [ΓSpecIso_hom_hom_comp_inv_hom, Ideal.map_id]),
      affineBlowUp.mapOfEq_eq_id (ΓSpecIso_hom_hom_comp_inv_hom (R := R))]

/-- `Spec` of `ΓSpecIso⁻¹` is the inverse of the canonical `Spec R ≅ Spec Γ(Spec R, ⊤)`. -/
theorem Spec_map_ΓSpecIso_inv_eq_isoSpec_inv :
    Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv = (Spec (CommRingCat.of R)).isoSpec.inv := by
  rw [← IsIso.Iso.inv_hom (Spec (CommRingCat.of R)).isoSpec]
  exact IsIso.eq_inv_of_hom_inv_id (toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of R))

/-- The identification lies over `Spec R`. -/
theorem blowUpSpecIso_hom_π :
    (blowUpSpecIso J).hom ≫ affineBlowUp.π J = blowUpπ (specIdealSheaf J) := by
  simp only [blowUpSpecIso, Category.assoc, affineBlowUp.mapOfEq_π]
  rw [IsIso.inv_comp_eq, blowUp.ι_π, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    IsAffineOpen.fromSpec_top, CommRingCat.ofHom_hom, Spec_map_ΓSpecIso_inv_eq_isoSpec_inv]

/-- The inverse identification lies over `Spec R`. -/
theorem blowUpSpecIso_inv_π :
    (blowUpSpecIso J).inv ≫ blowUpπ (specIdealSheaf J) = affineBlowUp.π J := by
  rw [← blowUpSpecIso_hom_π, Iso.inv_hom_id_assoc]

/-- Inverse images of ideal sheaves of `Spec R` along the blow-up, transported to the affine
blow-up. -/
theorem comap_comap_blowUpSpecIso_inv (K : (Spec (.of R)).IdealSheafData) :
    (K.comap (blowUpπ (specIdealSheaf J))).comap (blowUpSpecIso J).inv =
      K.comap (affineBlowUp.π J) := by
  rw [← comap_comp, blowUpSpecIso_inv_π]

end Hironaka.BlowUp
