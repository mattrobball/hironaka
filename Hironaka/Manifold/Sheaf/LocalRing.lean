/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Sheaf.ContMDiff
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# The stalks of the sheaf of `C^n` functions are local rings

The stalk at `x` of the sheaf of `C^n` functions valued in a nontrivially normed field `𝕜`
(`contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜`) is a local
ring: a germ is a unit iff its value at `x` is nonzero (`contMDiffSheafCommRing.isUnit_stalk_iff`),
the non-units form the kernel of the evaluation at `x`, which is therefore the maximal ideal
(`maximalIdeal_stalk`), and the residue field is `𝕜` through the evaluation
(`residueFieldEquiv`). Mathlib proves this for `n = ∞` (`smoothSheafCommRing.instLocalRing_stalk`);
the argument is the same for every `n`: a germ with nonzero value is nonzero on a neighbourhood of
`x`, on which its pointwise inverse is again `C^n` (`contDiffAt_inv`).

Instantiated at `n = ω`, these are the local rings `𝒪_{M,a}` of the structure sheaf of an analytic
manifold (`structureSheaf`); the stalk contains its residue field as the
constants, as Bierstone–Milman require of the local rings of their category of spaces
[BM97, (0.1)(2)].
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Topology IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  (n : ℕ∞ω) (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]

-- The rewrite by `map_mul` must see `ConcreteCategory.hom (S.germ V x _) f` as the application of a
-- ring homomorphism, which needs the concrete-category coercion unfolded; the older behaviour is
-- restored for this declaration.
set_option backward.isDefEq.respectTransparency.types false in
/-- A germ of the sheaf of `C^n` functions valued in `𝕜` is a unit iff its value at the point is
nonzero. -/
theorem contMDiffSheafCommRing.isUnit_stalk_iff {x : M}
    (f : (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.stalk x) :
    IsUnit f ↔ contMDiffSheafCommRing.eval IM 𝓘(𝕜) n M 𝕜 x f ≠ 0 := by
  constructor
  · rintro ⟨⟨f, g, hf, hg⟩, rfl⟩ (h' : contMDiffSheafCommRing.eval IM 𝓘(𝕜) n M 𝕜 x f = 0)
    simpa [h'] using congr_arg (contMDiffSheafCommRing.eval IM 𝓘(𝕜) n M 𝕜 x) hf
  · let S := (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf
    rintro (hf : _ ≠ 0)
    obtain ⟨U : Opens M, hxU, f : C^n⟮IM, U; 𝓘(𝕜), 𝕜⟯, rfl⟩ := S.exists_germ_eq f
    have hf' : f ⟨x, hxU⟩ ≠ 0 := by
      convert! hf
      exact (contMDiffSheafCommRing.eval_germ IM 𝓘(𝕜) n M 𝕜 U x hxU f).symm
    have H : ∀ᶠ (z : U) in 𝓝 ⟨x, hxU⟩, f z ≠ 0 :=
      f.2.continuous.continuousAt.eventually_ne hf'
    rw [eventually_nhds_iff] at H
    obtain ⟨V₀, hV₀f, hV₀, hxV₀⟩ := H
    let V : Opens M := ⟨Subtype.val '' V₀, U.2.isOpenMap_subtype_val V₀ hV₀⟩
    have hUV : V ≤ U := Subtype.coe_image_subset (U : Set M) V₀
    have hV : V₀ = Set.range (Set.inclusion hUV) := by
      convert! (Set.range_inclusion hUV).symm
      ext y
      change _ ↔ y ∈ Subtype.val ⁻¹' Subtype.val '' V₀
      rw [Set.preimage_image_eq _ Subtype.coe_injective]
    clear_value V
    subst hV
    have hxV : x ∈ (V : Set M) := by
      obtain ⟨x₀, hxx₀⟩ := hxV₀
      convert! x₀.2
      exact congr_arg Subtype.val hxx₀.symm
    have hVf : ∀ y : V, f (Set.inclusion hUV y) ≠ 0 :=
      fun y => hV₀f (Set.inclusion hUV y) (Set.mem_range_self y)
    let g : C^n⟮IM, V; 𝓘(𝕜), 𝕜⟯ := ⟨(f ∘ Set.inclusion hUV)⁻¹, ?_⟩
    · refine ⟨⟨S.germ _ x hxV (ContMDiffMap.restrictRingHom IM 𝓘(𝕜) 𝕜 hUV f), S.germ _ x hxV g,
        ?_, ?_⟩, S.germ_res_apply hUV.hom x hxV f⟩
      · rw [← map_mul]
        convert! RingHom.map_one _
        apply Subtype.ext
        ext y
        apply mul_inv_cancel₀
        exact hVf y
      · rw [← map_mul]
        convert! RingHom.map_one _
        apply Subtype.ext
        ext y
        apply inv_mul_cancel₀
        exact hVf y
    · intro y
      exact (((contDiffAt_inv _ (hVf y)).contMDiffAt).comp y
        (f.contMDiff.comp (contMDiff_inclusion hUV)).contMDiffAt :)

/-- The non-units of the stalk are the germs vanishing at the point. -/
theorem contMDiffSheafCommRing.nonunits_stalk (x : M) :
    nonunits ((contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.stalk x) =
      RingHom.ker (contMDiffSheafCommRing.eval IM 𝓘(𝕜) n M 𝕜 x) := by
  ext1 f
  rw [mem_nonunits_iff, not_iff_comm, Iff.comm]
  apply contMDiffSheafCommRing.isUnit_stalk_iff

/-- The stalks of the sheaf of `C^n` functions valued in `𝕜` are local rings. -/
instance contMDiffSheafCommRing.instLocalRing_stalk (x : M) :
    IsLocalRing ((contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.stalk x) := by
  apply IsLocalRing.of_nonunits_add
  rw [contMDiffSheafCommRing.nonunits_stalk]
  intro f g
  exact Ideal.add_mem _

/-- The maximal ideal of the stalk is the kernel of the evaluation. -/
theorem contMDiffSheafCommRing.maximalIdeal_stalk (x : M) :
    maximalIdeal ((contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.stalk x) =
      RingHom.ker (contMDiffSheafCommRing.eval IM 𝓘(𝕜) n M 𝕜 x) := by
  ext f
  rw [mem_maximalIdeal, contMDiffSheafCommRing.nonunits_stalk]
  exact Iff.rfl

/-- The residue field of the stalk is `𝕜`, through the evaluation. -/
def contMDiffSheafCommRing.residueFieldEquiv (x : M) :
    ResidueField ((contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.stalk x) ≃+* 𝕜 :=
  (Ideal.quotEquivOfEq (contMDiffSheafCommRing.maximalIdeal_stalk IM n M x)).trans
    (RingHom.quotientKerEquivOfSurjective
      (contMDiffSheafCommRing.eval_surjective IM 𝓘(𝕜) n M 𝕜 x))

theorem contMDiffSheafCommRing.residueFieldEquiv_residue (x : M)
    (f : (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.stalk x) :
    contMDiffSheafCommRing.residueFieldEquiv IM n M x (residue _ f) =
      contMDiffSheafCommRing.eval IM 𝓘(𝕜) n M 𝕜 x f := rfl

end Manifold
