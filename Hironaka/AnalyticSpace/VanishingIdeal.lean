/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Hironaka.Manifold.IdealSheaf.Defs
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The vanishing ideal of a set of points

For a locally ringed space `X` and a set `C ⊆ |X|`, the vanishing ideal of `C` at `y` is the
ideal `𝓘_C(y) ⊆ 𝒪_{X,y}` of the germs of sections `g` (over some open `V ∋ y`) that vanish at
every point of `C ∩ V` — "vanish at `y'`" meaning that the germ of `g` at `y'` lies in the maximal
ideal of `𝒪_{X,y'}`. This is the stalk at `y` of the sheaf of ideals of the closed set `C`, the
ideal sheaf `𝓘(A)` of an analytic set `A` in [GR84, Ch. 4, §1]. The closed subspace of an
irreducible component `C` of an analytic space is the one cut out by this ideal, once Cartan's
theorem (`hasLocalGenerators_radical_of_cartan`, `Hironaka/AnalyticSpace/ModelTransport.lean`)
provides local generators (`IdealSheaf.ofStalks`); see
`Hironaka/AnalyticSpace/Nullstellensatz.lean`.

* `vanishingStalkIdeal X C y`, with `vanishingStalkIdeal_eq_top_of_not_mem_closure` (the unit
  ideal off the closure of `C`), `vanishingStalkIdeal_ne_top_of_mem` (proper on `C`),
  `isRadical_vanishingStalkIdeal` (radical: a power vanishing on `C` has its base vanishing on
  `C`), `vanishingStalkIdeal_anti`, `vanishingStalkIdeal_inter_of_mem_nhds` (only the germ of
  `C` at `y` matters).
* Transport along a morphism `φ : A ⟶ B` of locally ringed spaces: the stalk map carries
  `𝓘_D(φ a)` into `𝓘_{φ⁻¹D}(a)` (`map_stalkMap_vanishingStalkIdeal_le`, the stalk maps being
  local), with equality when `φ.base` is inducing, the stalk maps are surjective and
  `D ⊆ φ(|A|)` (`vanishingStalkIdeal_preimage_eq_map`) — the cases used: open immersions,
  `K`-isomorphisms, and the closed immersion of a quotient `(S(𝒥), 𝒪/𝒥) ⟶ X`.
* `vanishingIdealSheaf X C hgen`, the ideal sheaf with these stalks given local generators
  (`hasLocalGenerators_vanishingStalkIdeal_of_forall_mem_closure` reduces the generators to the
  points of the closure), its stalks and its cosupport (`cosupport_vanishingIdealSheaf`: `C` when
  `C` is closed).
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Topology

universe u

namespace AnalyticSpace

open Manifold

/-- A local ring homomorphism pulls the maximal ideal back to the maximal ideal. -/
theorem map_mem_maximalIdeal_iff {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (a : R) :
    f a ∈ IsLocalRing.maximalIdeal S ↔ a ∈ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_map_iff]

variable (X : LocallyRingedSpace.{u}) (C : Set X)

/-- The vanishing ideal of `C` at `y` [GR84, Ch. 4, §1]: the germs at `y` of the sections
vanishing at every point of `C` near `y` — a germ vanishes at a point when it lies in the maximal
ideal of the stalk there. -/
def vanishingStalkIdeal (y : X) : Ideal (X.presheaf.stalk y) where
  carrier := {s | ∃ (V : Opens X) (hy : y ∈ V) (g : X.presheaf.obj (op V)),
    X.presheaf.germ V y hy g = s ∧
    ∀ y' (hy' : y' ∈ V), y' ∈ C → X.presheaf.germ V y' hy' g ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk y')}
  zero_mem' := ⟨⊤, trivial, 0, map_zero _, fun y' _ _ => by rw [map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro s t ⟨V, hyV, g, rfl, hg⟩ ⟨V', hyV', g', rfl, hg'⟩
    refine ⟨V ⊓ V', ⟨hyV, hyV'⟩,
      X.presheaf.map (homOfLE inf_le_left).op g + X.presheaf.map (homOfLE inf_le_right).op g',
      ?_, ?_⟩
    · rw [map_add, X.presheaf.germ_res_apply (homOfLE inf_le_left) y ⟨hyV, hyV'⟩ g,
        X.presheaf.germ_res_apply (homOfLE inf_le_right) y ⟨hyV, hyV'⟩ g']
    · intro y' hy' hC
      rw [map_add, X.presheaf.germ_res_apply (homOfLE inf_le_left) y' hy' g,
        X.presheaf.germ_res_apply (homOfLE inf_le_right) y' hy' g']
      exact add_mem (hg y' hy'.1 hC) (hg' y' hy'.2 hC)
  smul_mem' := by
    rintro r s ⟨V, hyV, g, rfl, hg⟩
    obtain ⟨V', hyV', h, rfl⟩ := X.presheaf.exists_germ_eq r
    refine ⟨V ⊓ V', ⟨hyV, hyV'⟩,
      X.presheaf.map (homOfLE inf_le_right).op h * X.presheaf.map (homOfLE inf_le_left).op g,
      ?_, ?_⟩
    · rw [map_mul, X.presheaf.germ_res_apply (homOfLE inf_le_right) y ⟨hyV, hyV'⟩ h,
        X.presheaf.germ_res_apply (homOfLE inf_le_left) y ⟨hyV, hyV'⟩ g]
      rfl
    · intro y' hy' hC
      rw [map_mul, X.presheaf.germ_res_apply (homOfLE inf_le_right) y' hy' h,
        X.presheaf.germ_res_apply (homOfLE inf_le_left) y' hy' g]
      exact Ideal.mul_mem_left _ _ (hg y' hy'.1 hC)

theorem mem_vanishingStalkIdeal_iff {y : X} {s : X.presheaf.stalk y} :
    s ∈ vanishingStalkIdeal X C y ↔
      ∃ (V : Opens X) (hy : y ∈ V) (g : X.presheaf.obj (op V)),
        X.presheaf.germ V y hy g = s ∧
        ∀ y' (hy' : y' ∈ V), y' ∈ C → X.presheaf.germ V y' hy' g ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk y') := Iff.rfl

/-- The germ of a section vanishing on `C` near `y` lies in the vanishing ideal. -/
theorem germ_mem_vanishingStalkIdeal {V : Opens X} {y : X} (hy : y ∈ V) (g : X.presheaf.obj (op V))
    (hg : ∀ y' (hy' : y' ∈ V), y' ∈ C → X.presheaf.germ V y' hy' g ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk y')) :
    X.presheaf.germ V y hy g ∈ vanishingStalkIdeal X C y :=
  ⟨V, hy, g, rfl, hg⟩

/-- Off the closure of `C` the vanishing ideal is everything. -/
theorem vanishingStalkIdeal_eq_top_of_not_mem_closure {y : X} (hy : y ∉ closure C) :
    vanishingStalkIdeal X C y = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  refine ⟨⟨(closure C)ᶜ, isClosed_closure.isOpen_compl⟩, hy, 1, map_one _, fun y' hy' hC => ?_⟩
  exact absurd (subset_closure hC) hy'

/-- At a point of `C` the vanishing ideal is proper. -/
theorem vanishingStalkIdeal_ne_top_of_mem {y : X} (hy : y ∈ C) : vanishingStalkIdeal X C y ≠ ⊤ := by
  intro htop
  rw [Ideal.eq_top_iff_one] at htop
  obtain ⟨V, hyV, g, hg1, hg⟩ := htop
  have := hg y hyV hy
  rw [hg1] at this
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr this)

/-- The vanishing ideal is radical. -/
theorem isRadical_vanishingStalkIdeal (y : X) : (vanishingStalkIdeal X C y).IsRadical := by
  intro s ⟨k, hk⟩
  obtain ⟨V, hyV, g, hgk, hg⟩ := hk
  obtain ⟨V₀, hyV₀, g₀, rfl⟩ := X.presheaf.exists_germ_eq s
  -- `g₀ ^ k` and `g` have the same germ at `y`: they agree near `y`
  have hgerm : X.presheaf.germ V₀ y hyV₀ (g₀ ^ k) = X.presheaf.germ V y hyV g := by
    rw [map_pow, hgk]
  obtain ⟨W, hyW, iU, iV, hW⟩ := X.presheaf.germ_eq y hyV₀ hyV _ _ hgerm
  refine ⟨W, hyW, X.presheaf.map iU.op g₀, ?_, ?_⟩
  · rw [X.presheaf.germ_res_apply]
  · intro y' hy' hC
    have h1 : X.presheaf.germ W y' hy' (X.presheaf.map iU.op g₀) ^ k ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk y') := by
      rw [← map_pow, ← map_pow, hW, X.presheaf.germ_res_apply]
      exact hg y' (iV.le hy') hC
    exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_of_pow_mem _ h1

variable {X}

/-- Vanishing on a larger set is the stronger condition. -/
theorem vanishingStalkIdeal_anti {C D : Set X} (h : C ⊆ D) (y : X) :
    vanishingStalkIdeal X D y ≤ vanishingStalkIdeal X C y := by
  rintro s ⟨V, hy, g, rfl, hg⟩
  exact ⟨V, hy, g, rfl, fun y' hy' hC => hg y' hy' (h hC)⟩

/-- Only the germ of `C` at `y` matters: cutting `C` down to a neighbourhood of `y` changes
nothing. -/
theorem vanishingStalkIdeal_inter_of_mem_nhds {t : Set X} {y : X} (ht : t ∈ 𝓝 y) :
    vanishingStalkIdeal X (C ∩ t) y = vanishingStalkIdeal X C y := by
  refine le_antisymm ?_ (vanishingStalkIdeal_anti Set.inter_subset_left y)
  rintro s ⟨V, hy, g, rfl, hg⟩
  have hyt : y ∈ interior t := mem_interior_iff_mem_nhds.mpr ht
  refine ⟨V ⊓ ⟨interior t, isOpen_interior⟩, ⟨hy, hyt⟩, X.presheaf.map (homOfLE inf_le_left).op g,
    X.presheaf.germ_res_apply (homOfLE inf_le_left) y ⟨hy, hyt⟩ g, fun y' hy' hC => ?_⟩
  rw [X.presheaf.germ_res_apply (homOfLE inf_le_left) y' hy' g]
  exact hg y' hy'.1 ⟨hC, interior_subset hy'.2⟩

/-- Vanishing on a union is vanishing on both sets. -/
theorem vanishingStalkIdeal_union (A B : Set X) (y : X) :
    vanishingStalkIdeal X (A ∪ B) y = vanishingStalkIdeal X A y ⊓ vanishingStalkIdeal X B y := by
  refine le_antisymm (le_inf (vanishingStalkIdeal_anti Set.subset_union_left y)
    (vanishingStalkIdeal_anti Set.subset_union_right y)) ?_
  rintro s ⟨⟨V, hyV, g, rfl, hg⟩, ⟨V', hyV', g', hg', hg'B⟩⟩
  obtain ⟨W, hyW, iV, iV', hW⟩ := X.presheaf.germ_eq y hyV hyV' _ _ hg'.symm
  refine ⟨W, hyW, X.presheaf.map iV.op g, X.presheaf.germ_res_apply iV y hyW g,
    fun y' hy' hC => ?_⟩
  rcases hC with hA | hB
  · rw [X.presheaf.germ_res_apply iV y' hy' g]
    exact hg y' (iV.le hy') hA
  · rw [hW, X.presheaf.germ_res_apply iV' y' hy' g']
    exact hg'B y' (iV'.le hy') hB

/-- The stalk map of a morphism carries the vanishing ideal of `D` into the vanishing ideal of the
preimage of `D` (sections pull back; the stalk maps are local). -/
theorem map_stalkMap_vanishingStalkIdeal_le {A B : LocallyRingedSpace.{u}} (φ : A ⟶ B) (D : Set B)
    (a : A) :
    Ideal.map (φ.stalkMap a).hom (vanishingStalkIdeal B D (φ.base a)) ≤
      vanishingStalkIdeal A (φ.base ⁻¹' D) a := by
  rw [Ideal.map_le_iff_le_comap]
  rintro s ⟨V, hV, g, rfl, hg⟩
  rw [Ideal.mem_comap, LocallyRingedSpace.stalkMap_germ_apply]
  refine ⟨(Opens.map φ.base).obj V, hV, φ.c.app (op V) g, rfl, fun a' ha' haD => ?_⟩
  rw [← LocallyRingedSpace.stalkMap_germ_apply φ V a' ha' g, map_mem_maximalIdeal_iff]
  exact hg (φ.base a') ha' haD

/-- Transport of the vanishing ideal along a morphism `φ` whose base map is inducing and whose
stalk maps are surjective (an open immersion, a `K`-isomorphism, the closed immersion of a
quotient): for `D` inside the image of `φ`, the vanishing ideal of `φ⁻¹D` at `a` is the image of
the vanishing ideal of `D` at `φ a`. -/
theorem vanishingStalkIdeal_preimage_eq_map {A B : LocallyRingedSpace.{u}} (φ : A ⟶ B)
    (hind : IsInducing φ.base) (hsurj : ∀ a, Function.Surjective (φ.stalkMap a).hom)
    {D : Set B} (hD : D ⊆ Set.range φ.base) (a : A) :
    vanishingStalkIdeal A (φ.base ⁻¹' D) a =
      Ideal.map (φ.stalkMap a).hom (vanishingStalkIdeal B D (φ.base a)) := by
  refine le_antisymm ?_ (map_stalkMap_vanishingStalkIdeal_le φ D a)
  rintro s ⟨W, haW, σ, rfl, hσ⟩
  obtain ⟨s₀, hs₀⟩ := hsurj a (A.presheaf.germ W a haW σ)
  obtain ⟨V, hV, g, rfl⟩ := B.presheaf.exists_germ_eq s₀
  have hs₀' := hs₀
  rw [LocallyRingedSpace.stalkMap_germ_apply] at hs₀'
  obtain ⟨W', haW', iU, iW, hW'⟩ := A.presheaf.germ_eq a hV haW _ _ hs₀'
  obtain ⟨V'', hV''o, hV''⟩ := hind.isOpen_iff.mp W'.isOpen
  have haV'' : φ.base a ∈ V'' := by rw [← Set.mem_preimage, hV'']; exact haW'
  rw [← hs₀]
  refine Ideal.mem_map_of_mem _ ⟨V ⊓ ⟨V'', hV''o⟩, ⟨hV, haV''⟩,
    B.presheaf.map (homOfLE inf_le_left).op g,
    B.presheaf.germ_res_apply (homOfLE inf_le_left) (φ.base a) ⟨hV, haV''⟩ g,
    fun b hb hbD => ?_⟩
  obtain ⟨a', rfl⟩ := hD hbD
  have ha'W' : a' ∈ W' := hV''.subset hb.2
  rw [B.presheaf.germ_res_apply (homOfLE inf_le_left) (φ.base a') hb g,
    ← map_mem_maximalIdeal_iff (φ.stalkMap a').hom, LocallyRingedSpace.stalkMap_germ_apply,
    ← A.presheaf.germ_res_apply iU a' ha'W', hW', A.presheaf.germ_res_apply iW a' ha'W' σ]
  exact hσ a' (iW.le ha'W') hbD

variable (X)

/-- Local generators of the vanishing ideal, given them at the points of the closure of `C` (off the
closure the ideal is everything, generated by `1`). -/
theorem hasLocalGenerators_vanishingStalkIdeal_of_forall_mem_closure
    (h : ∀ y ∈ closure C, ∃ (U : Opens X) (_ : y ∈ U) (ι : Type) (_ : Fintype ι)
      (f : ι → X.presheaf.obj (op U)), ∀ b (hb : b ∈ U),
        vanishingStalkIdeal X C b = Ideal.span (Set.range fun i => X.presheaf.germ U b hb (f i))) :
    IdealSheaf.HasLocalGenerators (𝒪 := X.𝒪) (vanishingStalkIdeal X C) := by
  intro y
  by_cases hy : y ∈ closure C
  · exact h y hy
  · refine ⟨⟨(closure C)ᶜ, isClosed_closure.isOpen_compl⟩, hy, Unit, inferInstance, fun _ => 1,
      fun b hb => ?_⟩
    rw [vanishingStalkIdeal_eq_top_of_not_mem_closure X C hb]
    refine ((Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ?_)).symm
    exact ⟨(), map_one _⟩

/-- The vanishing ideal sheaf of `C`, once its stalks have local generators. -/
def vanishingIdealSheaf
    (hgen : IdealSheaf.HasLocalGenerators (𝒪 := X.𝒪) (vanishingStalkIdeal X C)) :
    IdealSheaf X.𝒪 :=
  IdealSheaf.ofStalks _ _ hgen

theorem stalkIdeal_vanishingIdealSheaf
    (hgen : IdealSheaf.HasLocalGenerators (𝒪 := X.𝒪) (vanishingStalkIdeal X C)) (y : X) :
    (vanishingIdealSheaf X C hgen).stalkIdeal y = vanishingStalkIdeal X C y :=
  IdealSheaf.stalkIdeal_ofStalks _ hgen y

/-- The support of the vanishing ideal sheaf of a closed set `C` is `C`. -/
theorem cosupport_vanishingIdealSheaf (hC : IsClosed C)
    (hgen : IdealSheaf.HasLocalGenerators (𝒪 := X.𝒪) (vanishingStalkIdeal X C)) :
    (vanishingIdealSheaf X C hgen).support = C := by
  ext y
  rw [IdealSheaf.mem_support, stalkIdeal_vanishingIdealSheaf]
  constructor
  · intro h
    by_contra hyC
    exact h (vanishingStalkIdeal_eq_top_of_not_mem_closure X C (by rwa [hC.closure_eq]))
  · exact fun hy => vanishingStalkIdeal_ne_top_of_mem X C hy

end AnalyticSpace

end
