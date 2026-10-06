/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Defs
import Hironaka.AnalyticSpace.Glue
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# An analytic space from an open cover by analytic pieces

A Hausdorff `K`-local-ringed space `Y` with a countable open cover `(W i)` such that every open
subspace `Y | W i` is `K`-isomorphic to an analytic `K`-space is an analytic `K`-space
(`AnalyticSpace.ofOpenCover`): in the definition of [Hir64, Ch. 0, §1, pp. 119–120], clause (i) is
local and transports along the isomorphisms, clause (ii), countability at infinity, is inherited
from countably many σ-compact open subsets, and clause (iii), Hausdorffness, is assumed. This is how
the space glued from local complexifications, or from local resolutions, receives its analytic
structure (`gluedAnalytic`, `Hironaka.AnalyticSpace.Glue.KSpace`): the pieces are the glued open
subsets `ι_i(Y_i)`, isomorphic to the `Y_i`, and the Hausdorffness comes from
`Hironaka.AnalyticSpace.Glue.Topology`.

Conventions. `Y.restrictOpen W` is the open subspace; the local models are transported with
`restrictOpenIso` and `restrictOpen_restrictOpen_iso` (`(Y | W) | U ≅ Y | imageOpens W U`,
`Hironaka.AnalyticSpace.OpenSubspaceLemmas`). A single piece `W = ⊤` gives `Y ≅ Z` an analytic
space; `Y = ∅` with `ι` empty gives the empty analytic space.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology Set
open AnalyticSpace.KLocallyRingedSpace


universe u

variable {K : Type} [RCLike K]

/-- An analytic `K`-space structure on a Hausdorff `K`-space with a countable open cover by opens
`K`-isomorphic to analytic spaces. -/
noncomputable def AnalyticSpace.ofOpenCover (Y : KLocallyRingedSpace.{u} K) [T2Space Y]
    {ι : Type u} [Countable ι] (W : ι → Opens Y) (hcov : ⋃ i, (W i : Set Y) = Set.univ)
    (Z : ι → AnalyticSpace.{u} K)
    (e : ∀ i, KIso (Y.restrictOpen (W i)) (Z i).toKLocallyRingedSpace) : AnalyticSpace.{u} K where
  toKLocallyRingedSpace := Y
  locallyModel := by
    intro y
    obtain ⟨i, hy⟩ : ∃ i, y ∈ W i := by
      have : y ∈ ⋃ i, (W i : Set Y) := hcov ▸ Set.mem_univ y
      exact Set.mem_iUnion.mp this
    obtain ⟨U', hy'U', n, k, G, f, W', ⟨e'⟩⟩ := (Z i).locallyModel ((e i).hom.1.base ⟨y, hy⟩)
    let U'' : Opens (Y.restrictOpen (W i)) := (Opens.map (e i).hom.1.base).obj U'
    refine ⟨imageOpens (W i) U'', ?_, n, k, G, f, W',
      ⟨(restrictOpen_restrictOpen_iso (W i) U'').symm ≪≫ restrictOpenIso (e i) U' ≪≫ e'⟩⟩
    exact (mem_imageOpens (V := W i) (T := U'')).mpr ⟨hy, hy'U'⟩
  t2 := inferInstanceAs (T2Space Y)
  sigmaCompact := by
    refine isSigmaCompact_univ_iff.mp ?_
    rw [← hcov]
    refine isSigmaCompact_iUnion _ fun i => ?_
    have hrange : Set.range (fun z : (Z i).toKLocallyRingedSpace =>
        ((KIso.homeomorph (e i)).symm z).1) = (W i : Set Y) := by
      rw [Set.range_comp' (fun w : Y.restrictOpen (W i) => w.1) (KIso.homeomorph (e i)).symm,
        (KIso.homeomorph (e i)).symm.surjective.range_eq, Set.image_univ]
      exact Subtype.range_coe
    rw [← hrange]
    exact isSigmaCompact_range (continuous_subtype_val.comp (KIso.homeomorph (e i)).symm.continuous)

