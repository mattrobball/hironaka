/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The vanishing ideal of a set at a point: basic properties

Hironaka's `red(f⁻¹(E) ∪ f⁻¹(D))` [Hir64, Main Theorem II'(N) (iii), p. 156] is the reduced closed
analytic subspace with a given set of points: its ideal sheaf is, at every point `x`, the ideal
`vanishingStalk Z x` of the germs of analytic functions vanishing on the set near `x`
(Bierstone–Milman's reduced space, `𝓘_{X_red} = √𝓘_X` [BM97, Remark 3.14]; Hironaka's "reduced"
means no nilpotent elements [Hir64, p. 111]). This module unfolds the definitions
(`Germ.vanishesOn_coe`, `mem_vanishingGermIdeal_iff`, `mem_vanishingStalk_iff`), transports the
vanishing of a germ along a surjective embedding (`Germ.vanishesOn_compTendsto_of_isEmbedding`),
and proves the two facts the support of the reduced transform needs: the stalk is the unit ideal
exactly off the closure of `Z` (`vanishingStalk_eq_top_of_notMem_closure`,
`vanishingStalk_ne_top_of_mem_closure`). Whether these stalks are the stalks of a locally finitely
generated ideal sheaf (coherence of the ideal of an analytic set) is a separate question, answered
for simple normal crossings divisors in `Hironaka/Manifold/Snc/Coherence.lean` and left as a guard
in the definition of the reduced transform (`IdealSheaf.reducedTransform`).
-/

public section

open Filter Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Manifold

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {M : Type*} [TopologicalSpace M]

/-- Vanishing of the germ of a function, unfolded. -/
theorem Germ.vanishesOn_coe (Z : Set M) (x : M) (f : M → 𝕜) :
    Germ.VanishesOn Z x (f : (𝓝 x).Germ 𝕜) ↔ ∀ᶠ y in 𝓝[Z] x, f y = 0 :=
  Iff.rfl

/-- A germ at `h x` vanishes on `Z` iff its composite with the embedding `h` (onto `Y`) vanishes
on `h⁻¹ Z` at `x`. -/
theorem Germ.vanishesOn_compTendsto_of_isEmbedding {Y : Type*} [TopologicalSpace Y] {h : M → Y}
    (hh : Topology.IsEmbedding h) (hs : Function.Surjective h) (Z : Set Y) (x : M)
    (k : (𝓝 (h x)).Germ 𝕜) :
    Germ.VanishesOn (h ⁻¹' Z) x (k.compTendsto h (hh.continuous.tendsto x)) ↔
      Germ.VanishesOn Z (h x) k := by
  induction k using Germ.inductionOn with
  | h f =>
    rw [Germ.coe_compTendsto, Germ.vanishesOn_coe, Germ.vanishesOn_coe]
    have hmap : Filter.map h (𝓝[h ⁻¹' Z] x) = 𝓝[Z] (h x) := by
      rw [hh.map_nhdsWithin_eq, Set.image_preimage_eq Z hs]
    rw [← hmap, Filter.eventually_map]
    exact Iff.rfl

theorem mem_vanishingGermIdeal_iff (Z : Set M) (x : M) (g : (𝓝 x).Germ 𝕜) :
    g ∈ vanishingGermIdeal Z x ↔ Germ.VanishesOn Z x g :=
  Iff.rfl

/-- Off the closure of `Z` every germ vanishes on `Z` near `x`: the ideal is the unit ideal. -/
theorem vanishingGermIdeal_eq_top_of_notMem_closure {Z : Set M} {x : M} (hx : x ∉ closure Z) :
    vanishingGermIdeal (𝕜 := 𝕜) Z x = ⊤ := by
  have hbot : 𝓝[Z] x = ⊥ := by
    by_contra h
    exact hx (mem_closure_iff_nhdsWithin_neBot.mpr ⟨h⟩)
  refine (Ideal.eq_top_iff_one _).mpr ?_
  change Germ.VanishesOn Z x ((1 : M → 𝕜) : (𝓝 x).Germ 𝕜)
  rw [Germ.vanishesOn_coe, hbot]
  exact Filter.eventually_bot

/-- On the closure of `Z` the constant `1` does not vanish on `Z` near `x`: the ideal is proper. -/
theorem vanishingGermIdeal_ne_top_of_mem_closure {Z : Set M} {x : M} (hx : x ∈ closure Z) :
    vanishingGermIdeal (𝕜 := 𝕜) Z x ≠ ⊤ := by
  intro h
  have h1 : Germ.VanishesOn Z x ((1 : M → 𝕜) : (𝓝 x).Germ 𝕜) :=
    (Ideal.eq_top_iff_one _).mp h
  rw [Germ.vanishesOn_coe] at h1
  have : NeBot (𝓝[Z] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  obtain ⟨y, hy⟩ := h1.exists
  exact one_ne_zero hy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ChartedSpace E M]

theorem mem_vanishingStalk_iff (Z : Set M) (x : M) (s : (structureSheaf 𝕜 E M).presheaf.stalk x) :
    s ∈ vanishingStalk Z x ↔ Germ.VanishesOn Z x (stalkToGerm 𝓘(𝕜, E) ω M x s) :=
  Iff.rfl

/-- Off the closure of `Z` the vanishing ideal is the unit ideal. -/
theorem vanishingStalk_eq_top_of_notMem_closure {Z : Set M} {x : M} (hx : x ∉ closure Z) :
    vanishingStalk (𝕜 := 𝕜) (E := E) Z x = ⊤ := by
  rw [vanishingStalk, vanishingGermIdeal_eq_top_of_notMem_closure hx, Ideal.comap_top]

/-- On the closure of `Z` the vanishing ideal is proper (the constant `1` does not vanish). -/
theorem vanishingStalk_ne_top_of_mem_closure {Z : Set M} {x : M} (hx : x ∈ closure Z) :
    vanishingStalk (𝕜 := 𝕜) (E := E) Z x ≠ ⊤ := by
  intro h
  apply vanishingGermIdeal_ne_top_of_mem_closure (𝕜 := 𝕜) hx
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : (structureSheaf 𝕜 E M).presheaf.stalk x) ∈ vanishingStalk Z x := by
    rw [h]; exact Submodule.mem_top
  simpa [vanishingStalk, Ideal.mem_comap, map_one] using h1

end Manifold
