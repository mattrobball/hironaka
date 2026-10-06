/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Defs
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.LocallyFiniteProduct
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Principalization.MonomialStep
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.MonomialPart

/-!
# Germ-locality of the ideal sheaf of a closed submanifold, and total transforms of products

Four general facts about ideal sheaves on an analytic manifold, used to compute the total transform
of the monomial part under a blow-up (`BMO/Step1ExistsComap.lean`):

* the ideal sheaf of a closed submanifold is **germ-local**: its stalk at `x` depends only on the
  submanifold near `x`, so two closed submanifolds that agree on an open neighbourhood of `x` have
  the same ideal stalk there (`IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_of_inter_eq`; the
  variant `…_left` for a submanifold cut out of another by an open set);
* the total transform of an ideal sheaf has unit stalk at every point whose image lies off a set
  outside which the ideal sheaf has unit stalks
  (`totalTransform_stalkIdeal_eq_top_of_notMem_preimage`);
* the stalk of the total transform of a locally finite product of ideal sheaves
  (`BMO/LocallyFiniteProduct.lean`) is the finite product of the stalks of the total transforms of
  the factors active at the image point (`stalkIdeal_totalTransform_locallyFiniteProduct`);
* the total transform is multiplicative, `π^*(A · B) = π^*(A) · π^*(B)` (`IdealSheaf.pullback_mul`).

Not in the sources; auxiliary lemmas for Step 1 of the proof of [Kol07, Theorem 107].
-/

public section

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ ψ' : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- Germ-locality of the ideal sheaf of a closed submanifold: if two closed submanifolds `S`, `T`
agree on an open set `W` containing `x`, their ideal stalks at `x` coincide. At a point of `S`
(hence of `T`) a germ lies in either stalk ideal exactly when its section vanishes on the
submanifold near `x`, and `𝓝[S] x = 𝓝[T] x`; off `S` (hence off `T`) both stalks are the unit ideal.
-/
theorem _root_.Manifold.IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_of_inter_eq {S T : Set M}
    {c c' : ℕ}
    (hS : IsClosedSubmanifold ψ S c) (hT : IsClosedSubmanifold ψ' T c') {W : Set M} (hW : IsOpen W)
    {x : M} (hxW : x ∈ W) (hST : S ∩ W = T ∩ W) :
    hS.idealSheaf.stalkIdeal x = hT.idealSheaf.stalkIdeal x := by
  by_cases hxS : x ∈ S
  · have hxT : x ∈ T := ((Set.ext_iff.1 hST x).1 ⟨hxS, hxW⟩).1
    have hWS : W ∈ 𝓝[S] x := mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hxW)
    have hWT : W ∈ 𝓝[T] x := mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hxW)
    have hnhds : 𝓝[S] x = 𝓝[T] x := by
      rw [← nhdsWithin_inter_of_mem hWS, Set.inter_comm W S, hST, Set.inter_comm T W]
      exact nhdsWithin_inter_of_mem hWT
    ext s
    obtain ⟨V, hxV, g, rfl⟩ := (structureSheaf 𝕜 E M).presheaf.exists_germ_eq s
    rw [hS.germ_mem_stalkIdeal_idealSheaf_iff V hxS hxV,
      hT.germ_mem_stalkIdeal_idealSheaf_iff V hxT hxV,
      eventually_nhds_subtype_iff S ⟨x, hxS⟩ fun z => extendSection 𝕜 E g z = 0,
      eventually_nhds_subtype_iff T ⟨x, hxT⟩ fun z => extendSection 𝕜 E g z = 0, hnhds]
  · have hxT : x ∉ T := fun h => hxS ((Set.ext_iff.1 hST x).2 ⟨h, hxW⟩).1
    rw [hS.stalkIdeal_idealSheaf_of_notMem hxS, hT.stalkIdeal_idealSheaf_of_notMem hxT]

/-- If a closed submanifold `C` is cut out of a closed submanifold `S` by an open set, `S ∩ W = C`,
then at a point of `C` the two ideal sheaves have the same stalk: `S` and `C` agree on `W`. The case
of a connected component of a member of a boundary family. -/
theorem _root_.Manifold.IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_of_inter_eq_left {S C : Set M}
    {c c' : ℕ}
    (hS : IsClosedSubmanifold ψ S c) (hC : IsClosedSubmanifold ψ' C c') {W : Set M} (hW : IsOpen W)
    (hSW : S ∩ W = C) {x : M} (hxC : x ∈ C) :
    hS.idealSheaf.stalkIdeal x = hC.idealSheaf.stalkIdeal x := by
  have hCW : C ⊆ W := hSW ▸ Set.inter_subset_right
  exact hS.stalkIdeal_idealSheaf_eq_of_inter_eq hC hW (hCW hxC)
    (hSW.trans (Set.inter_eq_left.mpr hCW).symm)

variable {Y : Set M} {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M']
  [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

/-- The total transform of an ideal sheaf `B` has unit stalk at every point whose image lies off a
set `S₀` outside which `B` has unit stalks. -/
theorem totalTransform_stalkIdeal_eq_top_of_notMem_preimage (h : IsBlowUp ψ Y c π)
    (B : IdealSheaf (structureSheaf 𝕜 E M)) {S₀ : Set M}
    (hB : ∀ y, y ∉ S₀ → B.stalkIdeal y = ⊤) {x : M'} (hx : x ∉ π ⁻¹' S₀) :
    (B.pullback π h.contMDiff).stalkIdeal x = ⊤ := by
  rw [IdealSheaf.stalkIdeal_pullback, hB (π x) (by simpa only [Set.mem_preimage] using hx),
    Ideal.map_top]

open Hironaka.Manifold.BMO IdealSheaf in
/-- The total transform of a locally finite product, stalkwise: at a point `x` of the blow-up, the
stalk of `π^*(∏ᵢ Aᵢ)` is the finite product, over the indices `i` active at `π x`, of the stalks of
`π^*(Aᵢ)`. The stalk of a total transform is the image of the stalk below under the germ map, and
`Ideal.map` distributes over the finite product. -/
theorem stalkIdeal_totalTransform_locallyFiniteProduct {κ : Type u} (h : IsBlowUp ψ Y c π)
    (A : κ → IdealSheaf (structureSheaf 𝕜 E M)) (S : κ → Set M) (hLF : LocallyFinite S)
    (hunit : ∀ i x, x ∉ S i → (A i).stalkIdeal x = ⊤) (x : M') :
    ((locallyFiniteProduct (structureSheaf 𝕜 E M) A S hLF hunit).pullback π h.contMDiff).stalkIdeal
        x =
      ∏ i ∈ activeFinset S hLF (π x), ((A i).pullback π h.contMDiff).stalkIdeal x := by
  rw [IdealSheaf.stalkIdeal_pullback, stalkIdeal_locallyFiniteProduct, Ideal.map_finset_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (IdealSheaf.stalkIdeal_pullback π h.contMDiff (A i) x).symm
end Hironaka.Manifold
