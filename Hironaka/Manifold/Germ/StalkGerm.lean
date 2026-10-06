/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.StructureSheaf.Defs

/-!
# The germ at a point of a section of the sheaf of `C^n` functions

The stalk `𝒪_{M,a}` of the sheaf of `C^n` functions valued in `𝕜` embeds into
`Filter.Germ (𝓝 a) 𝕜` through the germs at `a` of the extensions by zero of the sections
(`germAt`, `stalkToGerm`). This module records that `germAt` is the germ of the extension by zero
(`germAt_apply`) and that the germ at `a` of a restriction is the germ of the section
(`germAt_restrict`).
-/

public noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits Filter Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  (n : ℕ∞ω) (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]

theorem germAt_apply (a : TopCat.of M) (U : Opens M) (ha : a ∈ U)
    (f : (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.obj (op U)) :
    germAt IM n M a U ha f = ↑(extendBy0 IM n M f) := rfl

/-- The germs at `a` of restrictions are the germs of the sections. -/
theorem germAt_restrict (a : TopCat.of M) (U V : Opens M) (i : U ⟶ V) (ha : a ∈ U)
    (f : (contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.obj (op V)) :
    germAt IM n M a U ha ((contMDiffSheafCommRing IM 𝓘(𝕜) n M 𝕜).presheaf.map i.op f) =
      germAt IM n M a V (leOfHom i ha) f := by
  rw [germAt_apply, germAt_apply]
  refine Germ.coe_eq.mpr ?_
  filter_upwards [U.2.mem_nhds ha] with x hx
  rw [extendBy0_of_mem IM n M _ hx, extendBy0_of_mem IM n M _ (leOfHom i hx)]
  rfl

end Manifold
