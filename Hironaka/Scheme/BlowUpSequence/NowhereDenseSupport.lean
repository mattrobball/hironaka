/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.IdealSheaf.StalkIdeal
/-!
# Nowhere dense subschemes have ideal sheaves nonzero at every point

Hironaka's hypothesis on the algebraic subscheme `W ⊆ X` in [Hir64, Corollary 3], and on the
center of a monoidal transformation, is topological: "the set of points of `W` is nowhere dense in
the underlying topological space of `X`" (Mathlib's `IsNowhereDense`). Kollár's triples
[Kol07, Definition 31 and Notation 64] and the predicate `IsNonzeroEverywhere` used in the main
theorems ask instead that the ideal sheaf of `W` be nonzero at every point. On a locally Noetherian
scheme the first implies the second (`isNonzeroEverywhere_of_isNowhereDense_support`): a stalk of
the ideal sheaf zero at `x` gives zero germs of the finitely many local generators, which then
vanish on a neighbourhood of `x` (`TopCat.Presheaf.germ_eq`), so the ideal sheaf vanishes near `x`
and `V(W)` has interior. The converse (a nonzero stalk at every point makes the support nowhere
dense) is not needed; `isNonzeroEverywhere_iff_irreducibleComponents` of
`Hironaka/Scheme/BlowUpSequence/InducedData.lean` is the form in terms of irreducible components.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Scheme.IdealSheafData

namespace AlgebraicGeometry

/-- On a locally Noetherian scheme, a closed subscheme with nowhere dense underlying set
(Hironaka's hypothesis in [Hir64, Corollary 3]) has an ideal sheaf with nonzero stalks (Kollár's
convention in [Kol07, Notation 64]): a zero stalk at `x` kills each of the finitely many local
generators on a neighbourhood of `x` (`TopCat.Presheaf.germ_eq`), so the ideal sheaf vanishes on a
neighbourhood of `x`, which then lies in the support. -/
theorem isNonzeroEverywhere_of_isNowhereDense_support {X : Scheme.{u}} [IsLocallyNoetherian X]
    (W : X.IdealSheafData) (hW : IsNowhereDense (W.support : Set X)) : IsNonzeroEverywhere W := by
  intro x hx
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  have hN : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (W.ideal U)
  -- the generators have zero germ at `x`
  have hgerm : ∀ g ∈ s, (X.presheaf.germ U.1 x hxU).hom g = 0 := by
    intro g hg
    have hmem : (X.presheaf.germ U.1 x hxU).hom g ∈ W.stalkIdeal x := by
      rw [stalkIdeal_eq_map_germ W U hxU]
      exact Ideal.mem_map_of_mem _ (hs ▸ Ideal.subset_span hg)
    have hx' : W.stalkIdeal x = ⊥ := hx
    rw [hx'] at hmem
    exact (Submodule.mem_bot _).mp hmem
  -- hence they vanish near `x`
  have hall : ∀ g ∈ s, ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ U.1, (X.presheaf.germ U.1 y hy).hom g = 0 := by
    intro g hg
    obtain ⟨V, hxV, iU, iU', hV⟩ := TopCat.Presheaf.germ_eq X.presheaf x hxU hxU g 0
      (by rw [map_zero]; exact hgerm g hg)
    rw [map_zero] at hV
    refine Filter.eventually_of_mem (V.2.mem_nhds hxV) fun y hyV hyU => ?_
    have h1 := X.presheaf.germ_res_apply iU y hyV g
    rw [hV, map_zero] at h1
    exact h1.symm
  -- so a neighbourhood of `x` lies in the support
  have key : ∀ᶠ y in 𝓝 x, y ∈ (W.support : Set X) := by
    filter_upwards [U.1.2.mem_nhds hxU, (Filter.eventually_all_finset s).mpr hall] with y hyU hy
    have hbot : W.stalkIdeal y = ⊥ := by
      rw [stalkIdeal_eq_map_germ W U hyU, ← hs, Ideal.map_span]
      refine Ideal.span_eq_bot.mpr fun a ha => ?_
      obtain ⟨g, hg, rfl⟩ := ha
      exact hy g hg hyU
    by_contra hnot
    have := stalkIdeal_eq_top_of_notMem_support W hnot
    rw [hbot] at this
    exact bot_ne_top this
  have hint : x ∈ interior (W.support : Set X) := mem_interior_iff_mem_nhds.mpr key
  rw [W.support.isClosed.isNowhereDense_iff] at hW
  rw [hW] at hint
  exact hint

end AlgebraicGeometry
