/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Defs
import Hironaka.Manifold.IdealSheaf.Monoid
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The locally finite product of ideal sheaves

The monomial part `M(I)` of an ideal sheaf `I` with respect to a boundary family `F` ([Kol07,
Definition–Lemma 110], in the form used by this library: `BMO/MonomialPart.lean`) is the product,
over the connected components `D` of the members of `F`, of the powers `𝓘_D^{ord_D I}`. On a
non-compact manifold a member can have infinitely many connected components, so the product is
infinite; it is nevertheless locally finite, because the components form a locally finite family of
closed sets and each factor is the unit ideal off its component. This file defines the **locally
finite product** of a family of ideal sheaves `A i` with *controlling sets* `S i` (each `A i` is the
unit ideal outside `S i`, and the `S i` are locally finite): the ideal sheaf whose stalk at `x` is
the finite product of the stalks of the `A i` with `x ∈ S i`. It has local generators because, near
any point, it agrees with the finite product over the indices whose controlling set meets a
neighbourhood of the point.

The statements are about ideal sheaves on an arbitrary sheaf of commutative rings on a topological
space; the topological lemma `locallyFinite_sigma` at the top is general as well. Not in the
sources; auxiliary for the monomial part of [Kol07, Definition–Lemma 110] on manifolds.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace TopCat

namespace Manifold

universe u

variable {X : Type u} [TopologicalSpace X] {𝒪 : TopCat.Sheaf CommRingCat (TopCat.of X)}
variable {κ : Type u}

/-- A sigma-indexed family of sets is locally finite when it is dominated by a locally finite outer
family `T` (`S ⟨i, c⟩ ⊆ T i`) and, for each outer index `i`, the inner family `c ↦ S ⟨i, c⟩` is
locally finite: near a point only finitely many outer sets `T i` are met, and for each of those only
finitely many inner sets. Applied to the connected components of the members of a boundary family,
indexed by the member and the component. -/
theorem _root_.Hironaka.Manifold.locallyFinite_sigma {ι : Type*} {β : ι → Type*} {T : ι → Set X}
    (hT : LocallyFinite T)
    {S : (Σ i, β i) → Set X} (hS : ∀ i, LocallyFinite fun c : β i => S ⟨i, c⟩)
    (hsub : ∀ i c, S ⟨i, c⟩ ⊆ T i) : LocallyFinite S := by
  intro x
  classical
  obtain ⟨U₀, hU₀, hF₀⟩ := hT x
  set F₀ : Finset ι := hF₀.toFinset with hF₀def
  choose W hW hWfin using fun i => hS i x
  refine ⟨U₀ ∩ ⋂ i ∈ F₀, W i,
    Filter.inter_mem hU₀ ((Filter.biInter_finset_mem F₀).2 fun i _ => hW i), ?_⟩
  refine Set.Finite.subset
    (F₀.finite_toSet.biUnion fun i _ => (hWfin i).image fun c => (⟨i, c⟩ : Σ i, β i)) ?_
  rintro ⟨i, c⟩ ⟨y, hyS, hyU⟩
  simp only [Set.mem_inter_iff, Set.mem_iInter] at hyU
  obtain ⟨hyU₀, hyW⟩ := hyU
  have hiF₀ : i ∈ F₀ := by
    rw [hF₀def, Set.Finite.mem_toFinset]
    exact ⟨y, hsub i c hyS, hyU₀⟩
  exact Set.mem_biUnion hiF₀ (Set.mem_image_of_mem _ ⟨y, hyS, hyW i hiF₀⟩)

namespace IdealSheaf

/-- The finite set of indices `i` whose controlling set `S i` contains `x`; finite because the
family `S` is locally finite, so only finitely many `S i` meet a neighbourhood of `x`. -/
noncomputable def activeFinset (S : κ → Set X) (hLF : LocallyFinite S) (x : X) : Finset κ :=
  (hLF.point_finite x).toFinset

/-- An index `i` is active at `x` exactly when `x` lies in its controlling set `S i`. -/
@[simp] theorem mem_activeFinset {S : κ → Set X} {hLF : LocallyFinite S} {x : X} {i : κ} :
    i ∈ activeFinset S hLF x ↔ x ∈ S i := by
  simp [activeFinset]

/-- The stalk assignment of the locally finite product: at `x`, the finite product of the stalks of
the `A i` over the indices active at `x`. -/
noncomputable def lfpStalk (A : κ → IdealSheaf 𝒪) (S : κ → Set X) (hLF : LocallyFinite S) (x : X) :
    Ideal (𝒪.presheaf.stalk x) :=
  ∏ i ∈ activeFinset S hLF x, (A i).stalkIdeal x

/-- The stalk assignment `lfpStalk` has local generators: near any point it agrees with the finite
product `∏ i ∈ T, A i` over the indices whose controlling set meets a neighbourhood of the point,
the inactive factors being the unit ideal by `hunit`, and the local generators of that finite
product, restricted to a smaller open set, generate it. -/
theorem hasLocalGenerators_lfpStalk (A : κ → IdealSheaf 𝒪) (S : κ → Set X) (hLF : LocallyFinite S)
    (hunit : ∀ i x, x ∉ S i → (A i).stalkIdeal x = ⊤) :
    HasLocalGenerators (𝒪 := 𝒪) (lfpStalk A S hLF) := by
  intro a
  obtain ⟨U, hUnhds, hUfin⟩ := hLF a
  -- The finite index set of controlling sets meeting `U`.
  set T : Finset κ := hUfin.toFinset with hT
  -- On `U`, the locally finite product agrees with the finite product `∏ i ∈ T, A i`.
  have hB : HasLocalGenerators ((∏ i ∈ T, A i).stalkIdeal) := fun b => by
    obtain ⟨V, hbV, k, f, -, hf⟩ := (∏ i ∈ T, A i).exists_generators b
    exact ⟨V, hbV, Fin k, inferInstance, f, hf⟩
  obtain ⟨V, hbV, k, f, hf⟩ := hB.exists_fin a
  obtain ⟨Uo, hUoU, hUoOpen, haUo⟩ := mem_nhds_iff.mp hUnhds
  refine ⟨V ⊓ ⟨Uo, hUoOpen⟩, ⟨hbV, haUo⟩, Fin k, inferInstance,
    fun i => 𝒪.presheaf.map (homOfLE inf_le_left).op (f i), fun b hb => ?_⟩
  obtain ⟨hbV', hbU⟩ := hb
  have hactive : activeFinset S hLF b ⊆ T := by
    intro i hi
    rw [mem_activeFinset] at hi
    rw [hT, Set.Finite.mem_toFinset]
    exact ⟨b, hi, hUoU hbU⟩
  have hagree : lfpStalk A S hLF b = (∏ i ∈ T, A i).stalkIdeal b := by
    rw [lfpStalk, stalkIdeal_finset_prod]
    refine Finset.prod_subset hactive fun i _ hni => ?_
    have hbnot : b ∉ S i := by rw [← mem_activeFinset (hLF := hLF)]; exact hni
    rw [hunit i b hbnot]
    exact Ideal.one_eq_top.symm
  rw [hagree, hf b hbV']
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  exact (𝒪.presheaf.germ_res_apply (homOfLE inf_le_left) b ⟨hbV', hbU⟩ (f i)).symm

variable (𝒪) in
/-- The **locally finite product** of a family `A : κ → IdealSheaf 𝒪` with controlling sets
`S : κ → Set X` (each `A i` is the unit ideal outside `S i`) that form a locally finite family: the
ideal sheaf whose stalk at `x` is `∏ i ∈ activeFinset S hLF x, (A i).stalkIdeal x`. This is the form
in which the monomial part of an ideal sheaf on a non-compact manifold is assembled from its
component factors ([Kol07, Definition–Lemma 110]), where a finite product would not do. -/
noncomputable def locallyFiniteProduct (A : κ → IdealSheaf 𝒪) (S : κ → Set X)
    (hLF : LocallyFinite S) (hunit : ∀ i x, x ∉ S i → (A i).stalkIdeal x = ⊤) : IdealSheaf 𝒪 :=
  ofStalks 𝒪 (lfpStalk A S hLF) (hasLocalGenerators_lfpStalk A S hLF hunit)

/-- The stalk of the locally finite product at `x` is the finite product of the stalks of the
factors active at `x`. -/
@[simp] theorem stalkIdeal_locallyFiniteProduct (A : κ → IdealSheaf 𝒪) (S : κ → Set X)
    (hLF : LocallyFinite S) (hunit : ∀ i x, x ∉ S i → (A i).stalkIdeal x = ⊤) (x : X) :
    (locallyFiniteProduct 𝒪 A S hLF hunit).stalkIdeal x =
      ∏ i ∈ activeFinset S hLF x, (A i).stalkIdeal x := by
  have h : locallyFiniteProduct 𝒪 A S hLF hunit
      = ofStalks 𝒪 (lfpStalk A S hLF) (hasLocalGenerators_lfpStalk A S hLF hunit) := rfl
  rw [h, stalkIdeal_ofStalks, lfpStalk]

end IdealSheaf

end Manifold
