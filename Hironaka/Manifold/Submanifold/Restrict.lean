/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold
import Hironaka.Manifold.Germ.ChartTransport
import Hironaka.Manifold.Submanifold.Manifold
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The restriction of germs to a closed submanifold

The inclusion `Y → M` of a closed submanifold is analytic for the induced charts (`contMDiff_val`:
in an induced chart it is `φ⁻¹ ∘ ψ⁻¹ ∘ embedCompl`), so the restriction of an analytic function on
`M` to `Y` is analytic, and the germs of sections of `𝒪_M` at `a ∈ Y` restrict to germs of sections
of `𝒪_Y`: through the embeddings of the stalks into the rings of germs of functions
(`stalkToGerm`), the restriction `𝒪_{M,a} →+* 𝒪_{Y,a}` is the composition with the inclusion
(`germRestrict`) read back in `𝒪_{Y,a}` (`restrictStalk`). It satisfies the specification
`IsRestrictStalk` of `Hironaka/Manifold/Submanifold.lean` (`isRestrictStalk_restrictStalk`) and
is the unique map doing so (`IsRestrictStalk.eq`). The local ring `𝒪_{Y,a}` of Hironaka's
non-singular subspace `D` is thereby a quotient of `𝒪_{M,a}` [Hir64, Definition 2, p. 141]; its
kernel is computed in `Hironaka/Manifold/Submanifold/Ideal.lean`.
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
  {Y : Set M} {c : ℕ}

/-- The inclusion of a closed submanifold is analytic for the induced charts. -/
theorem IsClosedSubmanifold.contMDiff_val (hY : IsClosedSubmanifold ψ Y c) :
    letI := hY.chartedSpace
    ContMDiff 𝓘(𝕜, Fin (n - c) → 𝕜) 𝓘(𝕜, E) ω (Subtype.val : Y → M) := by
  let _i := hY.chartedSpace
  intro x
  obtain ⟨φ, σ, hxs, h⟩ := hY.exists_adaptedChart x x.2
  have hx : x ∈ (h.chartOn x.2).source := hxs
  have he : ContMDiffOn 𝓘(𝕜, Fin (n - c) → 𝕜) 𝓘(𝕜, Fin (n - c) → 𝕜) ω (h.chartOn x.2)
      (h.chartOn x.2).source :=
    contMDiffOn_of_mem_maximalAtlas (n := ω) (h.chartOn_mem_maximalAtlas' hY x.2)
  have hlin : ContMDiff 𝓘(𝕜, Fin (n - c) → 𝕜) 𝓘(𝕜, E) ω (ψ.symm ∘ embedCompl σ) :=
    contMDiff_iff_contDiff.mpr (ψ.symm.contDiff.comp (contDiff_embedCompl σ))
  have hφ : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ.symm φ.target :=
    contMDiffOn_symm_of_mem_maximalAtlas (n := ω) h.1
  have hcomp : ContMDiffOn 𝓘(𝕜, Fin (n - c) → 𝕜) 𝓘(𝕜, E) ω
      (φ.symm ∘ (ψ.symm ∘ embedCompl σ) ∘ h.chartOn x.2) (h.chartOn x.2).source := by
    refine hφ.comp ((hlin.contMDiffOn (s := univ)).comp he fun _ _ => mem_univ _) fun y hy => ?_
    exact (h.chartOn x.2).map_source hy
  refine (hcomp.congr fun y hy => ?_).contMDiffAt ((h.chartOn x.2).open_source.mem_nhds hx)
  change (y : M) = φ.symm (ψ.symm (embedCompl σ (projCompl σ (ψ (φ y)))))
  rw [embedCompl_projCompl σ ((h.2 y hy).mp y.2), ψ.symm_apply_apply, φ.left_inv hy]

/-- The restriction of germs of functions along the inclusion `Y → M`. -/
def germRestrict (Y : Set M) (a : Y) : (𝓝 (a : M)).Germ 𝕜 →+* (𝓝 a).Germ 𝕜 :=
  germCompRingHom (Subtype.val : Y → M) continuous_subtype_val.continuousAt

/-- `germRestrict` sends the germ of `f` at `a` to the germ of `f ∘ Subtype.val` (unfolding
lemma). -/
theorem germRestrict_coe (Y : Set M) (a : Y) (f : M → 𝕜) :
    germRestrict (𝕜 := 𝕜) Y a (↑f : (𝓝 (a : M)).Germ 𝕜) = ↑(f ∘ (Subtype.val : Y → M)) := rfl

/-- The restriction to `Y` of the germ of a section of `𝒪_M` is the germ of a section of `𝒪_Y`. -/
theorem IsClosedSubmanifold.germRestrict_mem_range (hY : IsClosedSubmanifold ψ Y c) (a : Y)
    (s : (structureSheaf 𝕜 E M).presheaf.stalk (a : M)) :
    letI := hY.chartedSpace
    germRestrict Y a (stalkToGerm 𝓘(𝕜, E) ω M a s) ∈
      Set.range (stalkToGerm 𝓘(𝕜, Fin (n - c) → 𝕜) ω Y a) := by
  let _i := hY.chartedSpace
  obtain ⟨U, hU, f, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
  rw [stalkToGerm_structureSheaf_germ, germRestrict_coe]
  refine (mem_range_stalkToGerm_iff _ _ _ _ _).mpr ⟨_, rfl,
    ⟨Subtype.val ⁻¹' (U : Set M), U.2.preimage continuous_subtype_val⟩, hU, ?_⟩
  exact (contMDiffOn_extendBy0 𝓘(𝕜, E) ω M f).comp hY.contMDiff_val.contMDiffOn fun _ hy => hy

/-- `𝒪_{Y,a}` is isomorphic to the ring of germs of analytic functions on `Y` at `a`, the range of
`stalkToGerm`. -/
def IsClosedSubmanifold.stalkEquivRange (hY : IsClosedSubmanifold ψ Y c) (a : Y) :
    letI := hY.chartedSpace
    hY.stalk a ≃+* (stalkToGerm 𝓘(𝕜, Fin (n - c) → 𝕜) ω Y a).range :=
  letI := hY.chartedSpace
  RingEquiv.ofBijective (stalkToGerm 𝓘(𝕜, Fin (n - c) → 𝕜) ω Y a).rangeRestrict
    ⟨fun _ _ h => stalkToGerm_injective _ _ _ _ (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

/-- **The restriction of germs** `𝒪_{M,a} →+* 𝒪_{Y,a}`. -/
def IsClosedSubmanifold.restrictStalk (hY : IsClosedSubmanifold ψ Y c) (a : Y) :
    (structureSheaf 𝕜 E M).presheaf.stalk (a : M) →+* hY.stalk a :=
  letI := hY.chartedSpace
  (hY.stalkEquivRange a).symm.toRingHom.comp
    (((germRestrict Y a).comp (stalkToGerm 𝓘(𝕜, E) ω M a)).codRestrict _ fun s =>
      RingHom.mem_range.mpr (hY.germRestrict_mem_range a s))

/-- The restriction of germs read through `stalkToGerm`: the germ on `Y` of `restrictStalk s` is
the restriction (`germRestrict`) of the germ of `s`. -/
theorem IsClosedSubmanifold.stalkToGerm_restrictStalk (hY : IsClosedSubmanifold ψ Y c) (a : Y)
    (s : (structureSheaf 𝕜 E M).presheaf.stalk (a : M)) :
    letI := hY.chartedSpace
    stalkToGerm 𝓘(𝕜, Fin (n - c) → 𝕜) ω Y a (hY.restrictStalk a s) =
      germRestrict Y a (stalkToGerm 𝓘(𝕜, E) ω M a s) := by
  let _i := hY.chartedSpace
  have h1 : ∀ y : (stalkToGerm 𝓘(𝕜, Fin (n - c) → 𝕜) ω Y a).range,
      stalkToGerm 𝓘(𝕜, Fin (n - c) → 𝕜) ω Y a ((hY.stalkEquivRange a).symm y) = y := by
    intro y
    have := (hY.stalkEquivRange a).apply_symm_apply y
    exact congrArg Subtype.val this
  exact h1 _

/-- `restrictStalk` satisfies the specification `IsRestrictStalk`. -/
theorem IsClosedSubmanifold.isRestrictStalk_restrictStalk (hY : IsClosedSubmanifold ψ Y c)
    (a : Y) : hY.IsRestrictStalk a (hY.restrictStalk a) := by
  let _i := hY.chartedSpace
  intro U hU f
  rw [hY.stalkToGerm_restrictStalk, stalkToGerm_structureSheaf_germ, germRestrict_coe]

/-- The restriction of germs is determined by its specification. -/
theorem IsClosedSubmanifold.IsRestrictStalk.eq (hY : IsClosedSubmanifold ψ Y c) {a : Y}
    {r r' : (structureSheaf 𝕜 E M).presheaf.stalk (a : M) →+* hY.stalk a}
    (hr : hY.IsRestrictStalk a r) (hr' : hY.IsRestrictStalk a r') : r = r' := by
  let _i := hY.chartedSpace
  refine RingHom.ext fun s => ?_
  obtain ⟨U, hU, f, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
  exact stalkToGerm_injective _ _ _ _ ((hr U hU f).trans (hr' U hU f).symm)

end Manifold
