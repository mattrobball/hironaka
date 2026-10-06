/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Defs
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Stalk identities of ideal sheaves spread to a neighbourhood

An identity `J_x = (g_1, …, g_k)` between the stalk of a locally finitely generated ideal sheaf
`J` and the ideal spanned by the germs of finitely many sections `g_i` over an open set `U ∋ x`
holds at every point of an open neighbourhood `W ⊆ U` of `x`
(`IdealSheaf.exists_opens_stalkIdeal_eq_span`). Both sides are finitely generated: the local
generators `f_j` of `J` near `x` are combinations `f_j = ∑ a_{ji} g_i` at `x`, and each `g_i` has
the germ of a section of `J` at `x`; the coefficients `a_{ji}` are germs of sections, and an
identity of germs is an identity of sections on a smaller open set (`TopCat.Presheaf.germ_eq`),
so on the common open set the two ideals of germs coincide at every point. Also: finitely many
germs at a point are the germs of sections over one common open set (`exists_sections_of_germs`).

Stated for ideal sheaves over any sheaf of commutative rings; the step shared by the two dictionary
theorems `isNonsingular_iff` and `hasOnlyNormalCrossingsWith_idealSheaf_iff` (a stalk identity at a
point of a chart is spread to a neighbourhood on which the chart is adapted). Not in the sources;
standard.
-/

public section

open TopologicalSpace Opposite CategoryTheory

universe u

namespace Manifold

variable {X : TopCat.{u}} (𝒪 : TopCat.Sheaf CommRingCat.{u} X)

/-- Finitely many germs at `x` are the germs at `x` of sections over one open neighbourhood of
`x`. -/
theorem exists_sections_of_germs {x : X} {ι : Type*} [Finite ι] (s : ι → 𝒪.presheaf.stalk x) :
    ∃ (U : Opens X) (hx : x ∈ U) (g : ι → 𝒪.presheaf.obj (op U)),
      ∀ i, 𝒪.presheaf.germ U x hx (g i) = s i := by
  have h : ∀ i, ∃ (V : Opens X) (hxV : x ∈ V) (f : 𝒪.presheaf.obj (op V)),
      𝒪.presheaf.germ V x hxV f = s i := fun i => 𝒪.presheaf.exists_germ_eq (s i)
  choose V hxV f hf using h
  let U : Opens X := ⟨⋂ i, (V i : Set X), isOpen_iInter_of_finite fun i => (V i).2⟩
  have hxU : x ∈ U := Set.mem_iInter.mpr hxV
  have hle : ∀ i, U ≤ V i := fun i => Set.iInter_subset (fun i => (V i : Set X)) i
  refine ⟨U, hxU, fun i => 𝒪.presheaf.map (homOfLE (hle i)).op (f i), fun i => ?_⟩
  rw [TopCat.Presheaf.germ_res_apply]
  exact hf i

namespace IdealSheaf

variable {𝒪} (J : IdealSheaf 𝒪)

/-- A section whose germ at `x` lies in `J_x` lies in `J` on a neighbourhood of `x`. -/
theorem exists_opens_res_mem_of_germ_mem {U : Opens X} {x : X} (hx : x ∈ U)
    (g : 𝒪.presheaf.obj (op U)) (hg : 𝒪.presheaf.germ U x hx g ∈ J.stalkIdeal x) :
    ∃ (W : Opens X) (_ : x ∈ W) (i : W ⟶ U), 𝒪.presheaf.map i.op g ∈ J.carrier W := by
  obtain ⟨V, hxV, h, hh, hgerm⟩ := J.mem_stalkIdeal_iff.mp hg
  obtain ⟨W, hxW, iV, iU, hW⟩ := 𝒪.presheaf.germ_eq x hxV hx h g hgerm
  exact ⟨W, hxW, iU, hW ▸ J.res_mem iV h hh⟩

/-- If the stalk `J_x` is spanned by the germs of finitely many sections `g_i` over `U ∋ x`, the
same holds at every point of an open neighbourhood `W ⊆ U` of `x`. -/
theorem exists_opens_stalkIdeal_eq_span {U : Opens X} {x : X} (hx : x ∈ U) {ι : Type*}
    [Finite ι] (g : ι → 𝒪.presheaf.obj (op U))
    (hJx : J.stalkIdeal x = Ideal.span (Set.range fun i => 𝒪.presheaf.germ U x hx (g i))) :
    ∃ (W : Opens X) (_ : x ∈ W) (hWU : W ≤ U), ∀ y (hy : y ∈ W),
      J.stalkIdeal y = Ideal.span (Set.range fun i => 𝒪.presheaf.germ U y (hWU hy) (g i)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨U', hxU', m, f, hfmem, hf⟩ := J.exists_generators x
  -- (A) each `g i` lies in `J` near `x`
  have hA : ∀ i, ∃ (W : Opens X) (_ : x ∈ W) (iW : W ⟶ U),
      𝒪.presheaf.map iW.op (g i) ∈ J.carrier W := fun i =>
    J.exists_opens_res_mem_of_germ_mem hx (g i) (hJx ▸ Ideal.subset_span ⟨i, rfl⟩)
  choose W₁ hxW₁ iW₁ hW₁ using hA
  -- (B) each generator `f j` is a combination of the `g i` near `x`
  have hB : ∀ j, ∃ (W : Opens X) (_ : x ∈ W) (iW : W ⟶ U) (iW' : W ⟶ U'),
      𝒪.presheaf.map iW'.op (f j) ∈
        Ideal.span (Set.range fun i => 𝒪.presheaf.map iW.op (g i)) := by
    intro j
    have hmem : 𝒪.presheaf.germ U' x hxU' (f j) ∈ J.stalkIdeal x :=
      J.germ_mem_stalkIdeal hxU' (hfmem j)
    rw [hJx, Ideal.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    obtain ⟨V, hxV, a, ha⟩ := exists_sections_of_germs 𝒪 c
    let VU : Opens X := ⟨(V : Set X) ∩ U, V.2.inter U.2⟩
    have hxVU : x ∈ VU := ⟨hxV, hx⟩
    have hVU_V : VU ≤ V := Set.inter_subset_left
    have hVU_U : VU ≤ U := Set.inter_subset_right
    -- the section `∑ a i * g i` over `V ⊓ U` has the germ of `f j` at `x`
    have hgerm : 𝒪.presheaf.germ VU x hxVU (∑ i, 𝒪.presheaf.map (homOfLE hVU_V).op (a i) *
        𝒪.presheaf.map (homOfLE hVU_U).op (g i)) = 𝒪.presheaf.germ U' x hxU' (f j) := by
      rw [← hc, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ha i]
    obtain ⟨W, hxW, iVU, iU', hW⟩ := 𝒪.presheaf.germ_eq x hxVU hxU' _ _ hgerm
    refine ⟨W, hxW, iVU ≫ homOfLE hVU_U, iU', ?_⟩
    rw [← hW, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [map_mul]
    refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, ?_⟩)
    rw [op_comp, Functor.map_comp]
    rfl
  choose W₂ hxW₂ iW₂ iW₂' hW₂ using hB
  -- the common neighbourhood
  let W : Opens X := ⟨(U : Set X) ∩ (U' : Set X) ∩ (⋂ i, (W₁ i : Set X)) ∩ ⋂ j, (W₂ j : Set X),
    (((U.2.inter U'.2).inter (isOpen_iInter_of_finite fun i => (W₁ i).2)).inter
      (isOpen_iInter_of_finite fun j => (W₂ j).2))⟩
  have hxW : x ∈ W := ⟨⟨⟨hx, hxU'⟩, Set.mem_iInter.mpr hxW₁⟩, Set.mem_iInter.mpr hxW₂⟩
  have hWU : W ≤ U := fun _ hy => hy.1.1.1
  have hWU' : W ≤ U' := fun _ hy => hy.1.1.2
  have hWW₁ : ∀ i, W ≤ W₁ i := fun i _ hy => Set.mem_iInter.mp hy.1.2 i
  have hWW₂ : ∀ j, W ≤ W₂ j := fun j _ hy => Set.mem_iInter.mp hy.2 j
  refine ⟨W, hxW, hWU, fun y hy => le_antisymm ?_ ?_⟩
  · -- `J_y = (f_j)_y ≤ (g_i)_y`
    rw [hf y (hWU' hy), Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe]
    beta_reduce
    have h1 : 𝒪.presheaf.germ U' y (hWU' hy) (f j) =
        𝒪.presheaf.germ (W₂ j) y (hWW₂ j hy) (𝒪.presheaf.map (iW₂' j).op (f j)) := by
      rw [TopCat.Presheaf.germ_res_apply]
    rw [h1]
    have h2 := hW₂ j
    have h3 : Ideal.map (𝒪.presheaf.germ (W₂ j) y (hWW₂ j hy)).hom
        (Ideal.span (Set.range fun i => 𝒪.presheaf.map (iW₂ j).op (g i))) ≤
        Ideal.span (Set.range fun i => 𝒪.presheaf.germ U y (hWU hy) (g i)) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      refine Ideal.subset_span ⟨i, ?_⟩
      change 𝒪.presheaf.germ U y (hWU hy) (g i) =
        𝒪.presheaf.germ (W₂ j) y (hWW₂ j hy) (𝒪.presheaf.map (iW₂ j).op (g i))
      rw [TopCat.Presheaf.germ_res_apply]
    exact h3 (Ideal.mem_map_of_mem _ h2)
  · -- `(g_i)_y ≤ J_y`
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe]
    beta_reduce
    have h1 : 𝒪.presheaf.germ U y (hWU hy) (g i) =
        𝒪.presheaf.germ (W₁ i) y (hWW₁ i hy) (𝒪.presheaf.map (iW₁ i).op (g i)) := by
      rw [TopCat.Presheaf.germ_res_apply]
    rw [h1]
    exact J.germ_mem_stalkIdeal (hWW₁ i hy) (hW₁ i)

end IdealSheaf

end Manifold
