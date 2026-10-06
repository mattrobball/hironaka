/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.ProjectiveBundle.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Hironaka.Scheme.Modules.AffineLocal
import Hironaka.Scheme.ProjectiveBundle.Affine.Properties

/-!
# Projective morphisms are proper

The projective bundle `P(E) ⟶ X` of a quasi-coherent sheaf of finite type is proper
(`Scheme.Modules.isProper_projectiveBundleπ`, as in the proof of [Sta, Tag 01WC]): over an
affine open `U` with `Γ(E, U)` finitely generated (such opens cover `X`,
`Scheme.Modules.exists_isAffineOpen_finite_sections`) it is the projective bundle of the finitely
generated module `Γ(E, U)` over `Spec Γ(X, U) ≅ U`, which is proper
(`affineProjectiveBundle.isProper_π`), and properness is local on the target. A projective morphism,
a closed immersion into such a `P(E)` followed by `P(E) ⟶ X`, is therefore proper
(`AlgebraicGeometry.IsGrothendieckProjective.isProper`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- **The projective bundle of a quasi-coherent sheaf of finite type is proper** over the base, as
in the proof of [Sta, Tag 01WC]. -/
theorem Scheme.Modules.isProper_projectiveBundleπ {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] [SheafOfModules.IsFiniteType.{u} F] : IsProper F.projectiveBundleπ := by
  choose U hU hxU hfin using F.exists_isAffineOpen_finite_sections
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U
    (eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x => ?_
  let V : X.affineOpens := ⟨U x, hU x⟩
  have h₁ : IsPullback ((projectiveBundleGluingData F).natTrans.app V)
      (colimit.ι (projectiveBundleGluingData F).functor V) (U x).ι F.projectiveBundleπ :=
    (projectiveBundleGluingData F).isPullback_natTrans_ι_toBase V
  have h₂ := isPullback_morphismRestrict F.projectiveBundleπ (U x)
  have : Module.Finite Γ(X, U x) Γ(F, U x) := hfin x
  have : IsProper ((projectiveBundleGluingData F).natTrans.app V) := by
    change IsProper (affineProjectiveBundle.π Γ(X, U x) Γ(F, U x) ≫ (hU x).isoSpec.inv)
    have := affineProjectiveBundle.isProper_π (R := Γ(X, U x)) (M := Γ(F, U x))
    infer_instance
  exact (MorphismProperty.arrow_mk_iso_iff @IsProper
    (Arrow.isoMk (h₁.flip.isoIsPullback _ _ h₂.flip) (Iso.refl _)
      ((h₁.flip.isoIsPullback_hom_snd _ _ h₂.flip).trans (Category.comp_id _).symm))).mp this

/-- **A projective morphism is proper** [Sta, Tag 01WC]: it is a closed immersion into the
projective bundle of a quasi-coherent sheaf of finite type followed by the bundle projection, both
proper. -/
instance (priority := 100) IsGrothendieckProjective.isProper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hf : IsGrothendieckProjective f] : IsProper f := by
  obtain ⟨E, hE, hE', i, hi, rfl⟩ := hf.exists_isClosedImmersion
  have := E.isProper_projectiveBundleπ
  infer_instance

end AlgebraicGeometry
