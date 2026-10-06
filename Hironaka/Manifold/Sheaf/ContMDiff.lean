/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.StructureSheaf.Defs

/-!
# The sheaf of `C^n` functions on a manifold: sections and evaluation

For a manifold `M` modelled on `(EM, HM)` over a nontrivially normed field `𝕜`, a manifold `N`
modelled on `(E, H)` and any smoothness `n : ℕ∞ω`, the sections of the sheaf of `C^n` functions
`contMDiffSheaf IM I n M N` over `U` are, definitionally, the bundled maps `C^n⟮IM, U; I, N⟯`
(`contMDiffSheaf.obj_eq`), and likewise for the sheaf of commutative rings
`contMDiffSheafCommRing IM I n M R` of `C^n` functions valued in a `C^n` commutative ring `R`, on
which restriction is restriction of functions (`contMDiffSheafCommRing.map_apply`).

The evaluation at a point, `contMDiffSheafCommRing.eval IM I n M R x : stalk x →+* R`, takes the
germ of a section to its value at `x` (`eval_germ`) and is surjective, every value being taken by a
constant section (`eval_surjective`); in particular the stalks are nontrivial when `R` is.

This is the sheaf of regular functions of Bierstone–Milman's regular coordinate charts
[BM97, (0.3)]: the coordinates of a chart are sections and the stalks are the local rings of germs
(`contMDiffSheafCommRing.instLocalRing_stalk`).
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (n : ℕ∞ω)
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]
  (N : Type) [TopologicalSpace N] [ChartedSpace H N]

variable {M}

/-- The sections of `contMDiffSheaf IM I n M N` over `U` are, definitionally, the `C^n` functions
`C^n⟮IM, U; I, N⟯`. -/
theorem contMDiffSheaf.obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    (contMDiffSheaf IM I n M N).presheaf.obj U = C^n⟮IM, (unop U : Opens M); I, N⟯ := rfl

theorem contMDiffSheaf.contMDiff_section {U : (Opens (TopCat.of M))ᵒᵖ}
    (f : (contMDiffSheaf IM I n M N).presheaf.obj U) : ContMDiff IM I n f :=
  f.2

variable {N}

section CommRing

variable (M) (R : Type) [CommRing R] [TopologicalSpace R] [ChartedSpace H R] [ContMDiffRing I n R]

/-- The sections of `contMDiffSheafCommRing IM I n M R` over `U` are, definitionally, the `C^n`
functions `C^n⟮IM, U; I, R⟯`. -/
theorem contMDiffSheafCommRing.obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    ((contMDiffSheafCommRing IM I n M R).presheaf.obj U : Type u) =
      C^n⟮IM, (unop U : Opens M); I, R⟯ := rfl

theorem contMDiffSheafCommRing.contMDiff_section {U : (Opens (TopCat.of M))ᵒᵖ}
    (f : (contMDiffSheafCommRing IM I n M R).presheaf.obj U) : ContMDiff IM I n f :=
  f.2

/-- Restriction is restriction of functions. -/
@[simp]
theorem contMDiffSheafCommRing.map_apply {U V : Opens (TopCat.of M)} (h : U ≤ V)
    (f : (contMDiffSheafCommRing IM I n M R).presheaf.obj (op V)) (x : U) :
    ((contMDiffSheafCommRing IM I n M R).presheaf.map (homOfLE h).op f) x =
      f (Set.inclusion h x) := rfl

/-- Evaluation at `x` on the sections over an open neighbourhood `U` of `x`, valued in the lift of
`R` to the universe of `M` (so that it is a morphism of `CommRingCat.{u}`). -/
def contMDiffSheafCommRing.evalAt (x : TopCat.of M) (U : OpenNhds x) :
    (contMDiffSheafCommRing IM I n M R).presheaf.obj (op U.1) ⟶ CommRingCat.of (ULift.{u} R) :=
  CommRingCat.ofHom ((ULift.ringEquiv.symm : R ≃+* ULift.{u} R).toRingHom.comp
    (ContMDiffMap.evalRingHom ⟨x, U.2⟩))

/-- The evaluation at `x`, as a morphism from the stalk of `C^n` functions at `x` to the lift of
`R` in the category of commutative rings. -/
def contMDiffSheafCommRing.evalHom (x : TopCat.of M) :
    (contMDiffSheafCommRing IM I n M R).presheaf.stalk x ⟶ CommRingCat.of (ULift.{u} R) := by
  refine CategoryTheory.Limits.colimit.desc _ ⟨_, ⟨fun U => ?_, ?_⟩⟩
  · apply contMDiffSheafCommRing.evalAt
  · cat_disch

/-- The evaluation `ev_x : 𝒪_x →+* R` at `x` on the stalk of `C^n` functions. -/
def contMDiffSheafCommRing.eval (x : M) :
    (contMDiffSheafCommRing IM I n M R).presheaf.stalk x →+* R :=
  (ULift.ringEquiv : ULift.{u} R ≃+* R).toRingHom.comp
    (contMDiffSheafCommRing.evalHom IM I n M R x).hom

@[simp, reassoc, elementwise]
theorem contMDiffSheafCommRing.ι_evalHom (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ contMDiffSheafCommRing.evalHom IM I n M R x =
      contMDiffSheafCommRing.evalAt IM I n M R x (unop U) :=
  colimit.ι_desc _ _

theorem contMDiffSheafCommRing.evalHom_germ (U : Opens (TopCat.of M)) (x : M) (hx : x ∈ U)
    (f : (contMDiffSheafCommRing IM I n M R).presheaf.obj (op U)) :
    contMDiffSheafCommRing.evalHom IM I n M R (x : TopCat.of M)
      ((contMDiffSheafCommRing IM I n M R).presheaf.germ U x hx f) = ULift.up (f ⟨x, hx⟩) :=
  congr_arg (fun a => a f) <| contMDiffSheafCommRing.ι_evalHom IM I n M R x (op ⟨U, hx⟩)

/-- The evaluation at `x` of the germ of a section is the value of the section at `x`. -/
@[simp]
theorem contMDiffSheafCommRing.eval_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (f : (contMDiffSheafCommRing IM I n M R).presheaf.obj (op U)) :
    contMDiffSheafCommRing.eval IM I n M R x
      ((contMDiffSheafCommRing IM I n M R).presheaf.germ U x hx f) = f ⟨x, hx⟩ := by
  unfold contMDiffSheafCommRing.eval
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  change ULift.ringEquiv (contMDiffSheafCommRing.evalHom IM I n M R x _) = _
  rw [contMDiffSheafCommRing.evalHom_germ]
  rfl

/-- The evaluation at `x` is surjective: every value is taken by a constant section. -/
theorem contMDiffSheafCommRing.eval_surjective (x : M) :
    Function.Surjective (contMDiffSheafCommRing.eval IM I n M R x) := fun r =>
  ⟨(contMDiffSheafCommRing IM I n M R).presheaf.germ ⊤ x trivial
    (⟨fun _ => r, contMDiff_const⟩ : C^n⟮IM, ((⊤ : Opens M) : Opens M); I, R⟯),
    contMDiffSheafCommRing.eval_germ IM I n M R _ _ _ _⟩

instance [Nontrivial R] (x : M) :
    Nontrivial ((contMDiffSheafCommRing IM I n M R).presheaf.stalk x) :=
  (contMDiffSheafCommRing.eval_surjective IM I n M R x).nontrivial

end CommRing

end Manifold
