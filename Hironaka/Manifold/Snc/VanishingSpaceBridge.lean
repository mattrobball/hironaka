/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.VanishingIdeal
public import Hironaka.AnalyticSpace.Manifold.Defs
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.IdealSheaf.Vanishing
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The two vanishing ideals of a set at a point of a manifold agree

The ideal `vanishingStalk Z x ⊆ 𝒪_{M,x}` is the ideal of the germs vanishing on `Z` near `x`, for
a manifold `M`; `Hironaka/AnalyticSpace/VanishingIdeal.lean`
defines, for a locally ringed space `X`, the ideal `vanishingStalkIdeal X C y` of the germs at `y`
of sections whose value vanishes at every point of `C` near `y` — the ideal Rückert's
Nullstellensatz computes as the radical of a stalk ideal
(`radical_stalkIdeal_eq_vanishingStalkIdeal`, at the analytic space of a complex manifold). In the
stalk `𝒪_{M,x} = 𝒪_{Sp(M),x}` (the analytic space `Sp(M)` of `M` carries the structure sheaf of
`M`, `Hironaka/AnalyticSpace/Manifold/Defs.lean`) the two ideals coincide, since a germ vanishes at
a point iff it lies in the maximal ideal there (`vanishingStalk_eq_vanishingStalkIdeal`). This is
the bridge by which the Nullstellensatz is read on the manifold-side vanishing ideals. Not in the
sources; bookkeeping between the two definitions.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace Opposite CategoryTheory
open scoped Manifold ContDiff

universe u

noncomputable section

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M]

omit [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] in
/-- The germ of a section lies in the maximal ideal at `y` iff the section's value at `y`
vanishes. -/
theorem germ_mem_maximalIdeal_iff_extendSection {V : Opens M} {y : M} (hy : y ∈ V)
    (g : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    (structureSheaf 𝕜 E M).presheaf.germ V y hy g ∈
        IsLocalRing.maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk y) ↔
      extendSection 𝕜 E g y = 0 := by
  rw [mem_maximalIdeal_iff_eval, eval_germ']

/-- The analytic space `Sp(M)` of the manifold `M`, as a locally ringed space: its structure sheaf
is `structureSheaf 𝕜 E M`. The form in which Rückert's theorem
(`radical_stalkIdeal_eq_vanishingStalkIdeal`) is stated. -/
abbrev toSpaceLRS : AlgebraicGeometry.LocallyRingedSpace :=
  (AnalyticSpace.toSpace ψ
    ({ carrier := M } : AnalyticManifold.{u} 𝕜 E)).toLocallyRingedSpace

/-- Membership in the space-side vanishing ideal of `Sp(M)`, read on the structure sheaf of `M`. -/
theorem mem_vanishingStalkIdeal_toSpaceLRS_iff (Z : Set M) (x : M)
    (s : (structureSheaf 𝕜 E M).presheaf.stalk x) :
    s ∈ AnalyticSpace.vanishingStalkIdeal (toSpaceLRS ψ (M := M)) Z x ↔
      ∃ (V : Opens M) (hy : x ∈ V) (g : (structureSheaf 𝕜 E M).presheaf.obj (op V)),
        (structureSheaf 𝕜 E M).presheaf.germ V x hy g = s ∧
          ∀ (y' : M) (hy' : y' ∈ V), y' ∈ Z →
            (structureSheaf 𝕜 E M).presheaf.germ V y' hy' g ∈
              IsLocalRing.maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk y') :=
  Iff.rfl

/-- The manifold-side vanishing ideal of `Z` at `x` is the space-side vanishing ideal of `Z` at `x`
in `Sp(M)`. -/
theorem vanishingStalk_eq_vanishingStalkIdeal (Z : Set M) (x : M) :
    vanishingStalk (𝕜 := 𝕜) (E := E) Z x =
      AnalyticSpace.vanishingStalkIdeal (toSpaceLRS ψ (M := M)) Z x := by
  ext s
  refine Iff.trans ?_ (mem_vanishingStalkIdeal_toSpaceLRS_iff ψ Z x s).symm
  obtain ⟨V, hxV, g, rfl⟩ := TopCat.Presheaf.exists_germ_eq (structureSheaf 𝕜 E M).presheaf s
  constructor
  · intro hs
    have h : Germ.VanishesOn Z x ((stalkToGerm 𝓘(𝕜, E) ω M x)
        ((structureSheaf 𝕜 E M).presheaf.germ V x hxV g)) := hs
    rw [stalkToGerm_structureSheaf_germ, Germ.vanishesOn_coe] at h
    obtain ⟨W, hWo, hxW, hW⟩ := mem_nhdsWithin.mp h
    refine ⟨V ⊓ ⟨W, hWo⟩, ⟨hxV, hxW⟩,
      (structureSheaf 𝕜 E M).presheaf.map (homOfLE (inf_le_left : V ⊓ ⟨W, hWo⟩ ≤ V)).op g,
      (structureSheaf 𝕜 E M).presheaf.germ_res_apply _ x _ g, fun y' hy' hy'Z => ?_⟩
    rw [(structureSheaf 𝕜 E M).presheaf.germ_res_apply (homOfLE (inf_le_left : V ⊓ ⟨W, hWo⟩ ≤ V))
      y' hy' g, germ_mem_maximalIdeal_iff_extendSection]
    exact hW ⟨hy'.2, hy'Z⟩
  · rintro ⟨W, hxW, g', hg', hW⟩
    change Germ.VanishesOn Z x ((stalkToGerm 𝓘(𝕜, E) ω M x)
      ((structureSheaf 𝕜 E M).presheaf.germ V x hxV g))
    rw [← hg', stalkToGerm_structureSheaf_germ, Germ.vanishesOn_coe]
    exact mem_nhdsWithin.mpr ⟨W, W.isOpen, hxW, fun y hy =>
      (germ_mem_maximalIdeal_iff_extendSection hy.1 g').mp (hW y hy.1 hy.2)⟩

end Manifold

end
