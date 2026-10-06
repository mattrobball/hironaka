/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold.Defs
import Hironaka.Manifold.AdaptedChart
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.Chart.Adapted
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Manifold.Submanifold.Generators
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Flag coordinates for a closed submanifold containing the centre

In the proof of [Kol07, Theorem 88], Kollár chooses coordinates `x_1, …, x_n` with `S = (x_1 = 0)`
and the centre of the blow-up `π` equal to `(x_1 = ⋯ = x_r = 0)`, without proof. On manifolds, and
for a submanifold `S` of any codimension `s`: at a point `a` of a closed submanifold `Y ⊆ S` of
codimension `c` there is a chart adapted to `Y` in which `S` is the zero set of `s` of the `c`
centre coordinates (`exists_adaptedChart_flag`). The pair-chart lemma `exists_adaptedChart_pair`
of `Hironaka.Manifold.BlowUp.Transform.StrictCharts` is the case `s = 1`; this file proves the
general case by the same argument, generalized from one function to `s`:

* the adapted coordinates `h_1, …, h_s` of `S` at `a` vanish on `Y`, so their germs lie in the
  stalk ideal of `Y`, which is spanned by the centre coordinates `z_1, …, z_c` of an adapted chart
  of `Y` (`stalkIdeal_idealSheaf_eq_span`): `h_j = ∑_k g_{jk} z_k` near `a` with analytic
  `g_{jk}`;
* the differentials satisfy `dh_j(a) = ∑_k g_{jk}(a) dz_k(a)` and are independent (`S` is a
  submanifold), so by the exchange lemma (`exists_finset_linearIndependent_sum`) there is a set `K`
  of `c − s` centre indices such that the `dh_j(a)` together with the `dz_k(a)`, `k ∈ K`, are
  independent; the complementary `s` indices are enumerated by `τ : Fin s ↪ Fin c`;
* the family `z'` (the `h_j` in the slots `τ j`, the `z_k` in the slots `k ∈ K`) has independent
  differentials, so the chart completion `exists_adaptedChart_zeroSet'` makes it the coordinates
  of a chart at `a`; its common zero set is `Y` near `a`: the `s × s` matrix `(g_{j (τ j')}(a))`
  is invertible (the independence of the exchanged family says exactly that), hence invertible
  near `a`, and on `{z_K = 0}` the system `h = G_τ · z_τ` gives `h = 0 ⟺ z_τ = 0`.

The argument is not in the sources. Flag coordinates are the setting of the codimension-`s`
description of the strict transform in `Hironaka.Manifold.BlowUp.Transform.Strict`.
-/

public section

open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

/-- The coercion to germs commutes with finite sums. -/
theorem germ_coe_sum {α β ι : Type*} [AddCommMonoid β] {l : Filter α} (s : Finset ι)
    (f : ι → α → β) : (∑ i ∈ s, (↑(f i) : l.Germ β)) = ↑(∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, Germ.coe_add]

/-! ### Linear algebra: the exchange lemma -/

section LinearAlgebra

variable {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- The exchange lemma: an independent family `d` of `s` vectors inside the span of an independent
family `e` of `c` vectors can be completed to a basis of that span by `c − s` of the vectors `e k`,
`k ∈ K`. -/
theorem exists_finset_linearIndependent_sum {c s : ℕ} (e : Fin c → V) (he : LinearIndependent 𝕜 e)
    (d : Fin s → V) (hd : LinearIndependent 𝕜 d) (hsub : ∀ j, d j ∈ Submodule.span 𝕜 (range e)) :
    ∃ K : Finset (Fin c), s + K.card = c ∧
      LinearIndependent 𝕜 (Sum.elim d fun k : K => e k) := by
  classical
  obtain ⟨b, hbt, hdb, htb, hb⟩ := exists_linearIndepOn_id_extension hd.linearIndepOn_id
    (subset_union_left : range d ⊆ range d ∪ range e)
  set K : Finset (Fin c) := Finset.univ.filter fun k => e k ∈ b ∧ e k ∉ range d with hKdef
  set f : Fin s ⊕ K → V := Sum.elim d fun k : K => e k with hfdef
  have hmemK : ∀ k : K, e k ∈ b ∧ e k ∉ range d := fun k => (Finset.mem_filter.mp k.2).2
  have hmem : ∀ x, f x ∈ b := by
    rintro (j | k)
    · exact hdb ⟨j, rfl⟩
    · exact (hmemK k).1
  have hinj : Function.Injective f := by
    rintro (j | k) (j' | k') hxy
    · exact congrArg Sum.inl (hd.injective hxy)
    · exact absurd ⟨j, hxy⟩ (hmemK k').2
    · exact absurd ⟨j', hxy.symm⟩ (hmemK k).2
    · exact congrArg Sum.inr (Subtype.ext (he.injective hxy))
  have hli : LinearIndependent 𝕜 f := by
    have : f = (fun x : b => (x : V)) ∘ fun x => (⟨f x, hmem x⟩ : b) := rfl
    rw [this]
    exact hb.linearIndependent.comp _ fun x y hxy => hinj (congrArg Subtype.val hxy)
  refine ⟨K, ?_, hli⟩
  have hrange : range f = b := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact hmem x
    · intro hv
      rcases hbt hv with ⟨j, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨Sum.inl j, rfl⟩
      · by_cases hk : e k ∈ range d
        · obtain ⟨j, hj⟩ := hk
          exact ⟨Sum.inl j, hj⟩
        · exact ⟨Sum.inr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, hk⟩⟩, rfl⟩
  have hspan : Submodule.span 𝕜 (range f) = Submodule.span 𝕜 (range e) := by
    rw [hrange]
    refine le_antisymm (Submodule.span_le.mpr fun v hv => ?_)
      (Submodule.span_le.mpr fun v hv => htb (Or.inr hv))
    rcases hbt hv with ⟨j, rfl⟩ | ⟨k, rfl⟩
    · exact hsub j
    · exact Submodule.subset_span ⟨k, rfl⟩
  have h1 := finrank_span_eq_card hli
  have h2 := finrank_span_eq_card he
  rw [hspan, h2] at h1
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] at h1
  omega

/-- An enumeration of the complement of a finset of `c − s` indices by `Fin s`. -/
theorem exists_embedding_range_eq_compl {c s : ℕ} (K : Finset (Fin c)) (h : s + K.card = c) :
    ∃ τ : Fin s ↪ Fin c, ∀ k, k ∈ range τ ↔ k ∉ K := by
  classical
  have hc : Kᶜ.card = s := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  let e : ↥(Kᶜ : Finset (Fin c)) ≃ Fin s :=
    (Finset.equivFin (Kᶜ : Finset (Fin c))).trans (finCongr hc)
  refine ⟨⟨fun j => (e.symm j).1, fun j j' hjj' => e.symm.injective (Subtype.ext hjj')⟩,
    fun k => ⟨?_, fun hk => ⟨e ⟨k, Finset.mem_compl.mpr hk⟩, ?_⟩⟩⟩
  · rintro ⟨j, rfl⟩
    exact Finset.mem_compl.mp (e.symm j).2
  · change ((e.symm (e ⟨k, _⟩)) : Fin c) = k
    rw [e.symm_apply_apply]

end LinearAlgebra

/-! ### Flag coordinates -/

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y S : Set M} {c s : ℕ}

/-- At a point of a closed
submanifold `Y` of codimension `c` contained in a closed submanifold `S` of codimension `s`, there
is a chart adapted to `Y` in which `S` is the zero set of `s` of the `c` centre coordinates. -/
theorem exists_adaptedChart_flag (hY : IsClosedSubmanifold ψ Y c) (hS : IsClosedSubmanifold ψ S s)
    (hYS : Y ⊆ S) {a : M} (ha : a ∈ Y) :
    ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n) (τ : Fin s ↪ Fin c),
      a ∈ φ.source ∧ IsAdaptedChart ψ Y φ σ ∧
        ∀ x ∈ φ.source, x ∈ S ↔ ∀ j, ψ (φ x) (σ (τ j)) = 0 := by
  classical
  obtain ⟨φ₀, σ₀, haφ₀, hφ₀⟩ := hY.exists_adaptedChart a ha
  obtain ⟨φ₁, σ₁, haφ₁, hφ₁⟩ := hS.exists_adaptedChart a (hYS ha)
  set z : Fin c → M → 𝕜 := fun k x => ψ (φ₀ x) (σ₀ k) with hzdef
  set hfun : Fin s → M → 𝕜 := fun j x => ψ (φ₁ x) (σ₁ j) with hhdef
  set V : Opens M := ⟨φ₀.source ∩ φ₁.source, φ₀.open_source.inter φ₁.open_source⟩ with hVdef
  have haV : a ∈ V := ⟨haφ₀, haφ₁⟩
  -- (A) `h_j = ∑_k g_{jk} z_k` near `a`, with `g_{jk}` analytic near `a`
  have hrepr : ∀ j, ∃ g : Fin c → M → 𝕜,
      (∀ k, ∃ U : Opens M, a ∈ U ∧ ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (g k) U) ∧
        ∀ᶠ x in 𝓝 a, hfun j x = ∑ k, g k x * z k x := by
    intro j
    have hhV : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (hfun j) V :=
      (coordFunctional ψ (σ₁ j)).contMDiff.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas hφ₁.1).mono fun x hx => hx.2)
    set hsec := sectionOfContMDiffOn (hfun j) V hhV with hhsec
    have hmem : (structureSheaf 𝕜 E M).presheaf.germ V a haV hsec ∈ hY.idealSheaf.stalkIdeal a := by
      rw [hY.germ_mem_stalkIdeal_idealSheaf_iff V ha haV]
      filter_upwards [(continuous_subtype_val.isOpen_preimage _ V.2).mem_nhds
        (show (⟨a, ha⟩ : Y) ∈ {y : Y | (y : M) ∈ V} from haV)] with y hyV
      rw [extendSection_of_mem 𝕜 E _ hyV, sectionOfContMDiffOn_apply]
      exact (hφ₁.2 _ hyV.2).1 (hYS y.2) j
    rw [hY.stalkIdeal_idealSheaf_eq_span ha hφ₀ haφ₀, Submodule.mem_span_range_iff_exists_fun]
      at hmem
    obtain ⟨cf, hcf⟩ := hmem
    have hg : ∀ k, ∃ g : M → 𝕜, stalkToGerm 𝓘(𝕜, E) ω M a (cf k) = ↑g ∧
        ∃ U : Opens M, a ∈ U ∧ ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω g U := fun k =>
      (mem_range_stalkToGerm_iff 𝓘(𝕜, E) ω M a _).mp ⟨_, rfl⟩
    choose g hgc U haU hgU using hg
    refine ⟨g, fun k => ⟨U k, haU k, hgU k⟩, ?_⟩
    have h1 := congrArg (stalkToGerm 𝓘(𝕜, E) ω M a) hcf
    rw [map_sum, stalkToGerm_structureSheaf_germ] at h1
    simp only [smul_eq_mul, map_mul, hgc, stalkToGerm_coord, ← Germ.coe_mul] at h1
    rw [germ_coe_sum, Germ.coe_eq] at h1
    filter_upwards [h1, V.2.mem_nhds haV] with x hx hxV
    rw [Finset.sum_apply] at hx
    have hx' : extendSection 𝕜 E hsec x = hfun j x := by
      rw [extendSection_of_mem 𝕜 E _ hxV, sectionOfContMDiffOn_apply]
    rw [← hx', ← hx]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.mul_apply, extendSection_of_mem 𝕜 E _ hxV.1]
    rfl
  choose g hgU hrep using hrepr
  choose U haU hgU using hgU
  -- (B) the differentials in the chart `φ₀`
  have hcd : ∀ k, DifferentiableAt 𝕜 (fun v : E => ψ v (σ₀ k)) (φ₀ a) := fun k =>
    (coordFunctional ψ (σ₀ k)).differentiableAt
  have hcf : ∀ k, fderiv 𝕜 (fun v : E => ψ v (σ₀ k)) (φ₀ a) = coordFunctional ψ (σ₀ k) := fun k =>
    (coordFunctional ψ (σ₀ k)).fderiv
  have hgd : ∀ j k, DifferentiableAt 𝕜 (g j k ∘ φ₀.symm) (φ₀ a) := by
    intro j k
    have h2 : IsOpen (φ₀.target ∩ φ₀.symm ⁻¹' (U j k : Set M)) :=
      φ₀.isOpen_inter_preimage_symm (U j k).2
    have h1 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (g j k ∘ φ₀.symm)
        (φ₀.target ∩ φ₀.symm ⁻¹' (U j k : Set M)) :=
      (hgU j k).comp ((contMDiffOn_symm_of_mem_maximalAtlas hφ₀.1).mono Set.inter_subset_left)
        fun v hv => hv.2
    have h3 : φ₀ a ∈ φ₀.target ∩ φ₀.symm ⁻¹' (U j k : Set M) :=
      ⟨φ₀.map_source haφ₀, by rw [Set.mem_preimage, φ₀.left_inv haφ₀]; exact haU j k⟩
    exact (contMDiffAt_iff_contDiffAt.mp (h1.contMDiffAt (h2.mem_nhds h3))).differentiableAt
      (by simp)
  set e : Fin c → E →L[𝕜] 𝕜 := fun k => coordFunctional ψ (σ₀ k) with hedef
  set d : Fin s → E →L[𝕜] 𝕜 := fun j => fderiv 𝕜 (hfun j ∘ φ₀.symm) (φ₀ a) with hddef
  have hDh : ∀ j, d j = ∑ k, g j k a • e k := by
    intro j
    have hrep' : (hfun j ∘ φ₀.symm) =ᶠ[𝓝 (φ₀ a)]
        fun v => ∑ k, (g j k ∘ φ₀.symm) v * ψ v (σ₀ k) := by
      filter_upwards [(φ₀.tendsto_symm haφ₀).eventually (hrep j),
        φ₀.open_target.mem_nhds (φ₀.map_source haφ₀)] with v hv hvT
      rw [Function.comp_apply, hv]
      refine Finset.sum_congr rfl fun k _ => ?_
      change g j k (φ₀.symm v) * ψ (φ₀ (φ₀.symm v)) (σ₀ k) = g j k (φ₀.symm v) * ψ v (σ₀ k)
      rw [φ₀.right_inv hvT]
    change fderiv 𝕜 (hfun j ∘ φ₀.symm) (φ₀ a) = _
    rw [hrep'.fderiv_eq]
    have hsumfun : (fun v : E => ∑ k, (g j k ∘ φ₀.symm) v * ψ v (σ₀ k)) =
        ∑ k, fun v : E => (g j k ∘ φ₀.symm) v * ψ v (σ₀ k) := by
      ext v
      simp [Finset.sum_apply]
    rw [hsumfun, fderiv_sum (A := fun k => fun v : E => (g j k ∘ φ₀.symm) v * ψ v (σ₀ k))
      fun k _ => (hgd j k).mul (hcd k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    change fderiv 𝕜 ((g j k ∘ φ₀.symm) * fun v : E => ψ v (σ₀ k)) (φ₀ a) = _
    rw [fderiv_mul (hgd j k) (hcd k), hcf k]
    have h0 : ψ (φ₀ a) (σ₀ k) = 0 := (hφ₀.2 a haφ₀).1 ha k
    refine ContinuousLinearMap.ext fun v => ?_
    simp [h0, Function.comp_apply, φ₀.left_inv haφ₀, hedef]
  have hfdz : ∀ k, fderiv 𝕜 (z k ∘ φ₀.symm) (φ₀ a) = e k := by
    intro k
    have hev : (z k ∘ φ₀.symm) =ᶠ[𝓝 (φ₀ a)] fun v => ψ v (σ₀ k) := by
      filter_upwards [φ₀.open_target.mem_nhds (φ₀.map_source haφ₀)] with v hv
      change ψ (φ₀ (φ₀.symm v)) (σ₀ k) = ψ v (σ₀ k)
      rw [φ₀.right_inv hv]
    rw [hev.fderiv_eq]
    exact hcf k
  have hdiffh : ∀ j, MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (hfun j) a := fun j =>
    (((coordFunctional ψ (σ₁ j)).contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas hφ₁.1)).contMDiffAt
        (φ₁.open_source.mem_nhds haφ₁)).mdifferentiableAt (by simp)
  have hdiffz : ∀ k, MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (z k) a := fun k =>
    (((coordFunctional ψ (σ₀ k)).contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas hφ₀.1)).contMDiffAt
        (φ₀.open_source.mem_nhds haφ₀)).mdifferentiableAt (by simp)
  have hdind : LinearIndependent 𝕜 d :=
    (hasIndependentDifferentialsAt_iff_chart hφ₀.1 haφ₀ hdiffh).mp
      (hφ₁.hasIndependentDifferentialsAt haφ₁)
  have heind : LinearIndependent 𝕜 e := by
    have h1 := (hasIndependentDifferentialsAt_iff_chart hφ₀.1 haφ₀ hdiffz).mp
      (hφ₀.hasIndependentDifferentialsAt haφ₀)
    have h2 : (fun k => fderiv 𝕜 (z k ∘ φ₀.symm) (φ₀ a)) = e := funext hfdz
    rwa [h2] at h1
  have hsub : ∀ j, d j ∈ Submodule.span 𝕜 (range e) := fun j => by
    rw [hDh j]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨K, hKc, hli⟩ := exists_finset_linearIndependent_sum e heind d hdind hsub
  obtain ⟨τ, hτ⟩ := exists_embedding_range_eq_compl K hKc
  have hmapK : Finset.univ.map τ = Kᶜ := by
    ext k
    rw [Finset.mem_map, Finset.mem_compl, ← hτ k]
    simp only [Finset.mem_univ, true_and, Set.mem_range]
  -- (C) the exchanged family, indexed by `Fin c` through `Fin s ⊕ K ≃ Fin c`
  set F : Fin s ⊕ K → Fin c := Sum.elim τ Subtype.val with hFdef
  have hFinj : Function.Injective F := by
    rintro (j | k) (j' | k') hxy
    · exact congrArg Sum.inl (τ.injective hxy)
    · exact absurd ((hτ k').mp ⟨j, hxy⟩) (not_not.mpr k'.2)
    · exact absurd ((hτ k).mp ⟨j', hxy.symm⟩) (not_not.mpr k.2)
    · exact congrArg Sum.inr (Subtype.ext hxy)
  have hFsurj : Function.Surjective F := by
    intro k
    by_cases hk : k ∈ K
    · exact ⟨Sum.inr ⟨k, hk⟩, rfl⟩
    · obtain ⟨j, hj⟩ := (hτ k).mpr hk
      exact ⟨Sum.inl j, hj⟩
  set Eq : Fin s ⊕ K ≃ Fin c := Equiv.ofBijective F ⟨hFinj, hFsurj⟩ with hEqdef
  have hEq_inl : ∀ j, Eq.symm (τ j) = Sum.inl j := fun j => Eq.symm_apply_eq.mpr rfl
  have hEq_inr : ∀ k : K, Eq.symm k = Sum.inr k := fun k => Eq.symm_apply_eq.mpr rfl
  set Z : Fin s ⊕ K → M → 𝕜 := Sum.elim hfun fun k : K => z k with hZdef
  set z' : Fin c → M → 𝕜 := fun k => Z (Eq.symm k) with hz'def
  have hz'τ : ∀ j, z' (τ j) = hfun j := fun j => by
    simp only [hz'def, hEq_inl j, hZdef, Sum.elim_inl]
  have hz'K : ∀ k : K, z' k = z k := fun k => by
    simp only [hz'def, hEq_inr k, hZdef, Sum.elim_inr]
  have hZc : ∀ x, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (Z x) a := by
    rintro (j | k)
    · exact ((coordFunctional ψ (σ₁ j)).contMDiff.comp_contMDiffOn
        (contMDiffOn_of_mem_maximalAtlas hφ₁.1)).contMDiffAt (φ₁.open_source.mem_nhds haφ₁)
    · exact ((coordFunctional ψ (σ₀ k)).contMDiff.comp_contMDiffOn
        (contMDiffOn_of_mem_maximalAtlas hφ₀.1)).contMDiffAt (φ₀.open_source.mem_nhds haφ₀)
  have hz'c : ∀ k, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (z' k) a := fun k => hZc (Eq.symm k)
  have hZ0 : ∀ x, Z x a = 0 := by
    rintro (j | k)
    · exact (hφ₁.2 a haφ₁).1 (hYS ha) j
    · exact (hφ₀.2 a haφ₀).1 ha k
  have hz'0 : ∀ k, z' k a = 0 := fun k => hZ0 (Eq.symm k)
  have hz'd : ∀ k, MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (z' k) a := fun k =>
    (hz'c k).mdifferentiableAt (by simp)
  have hZfd : ∀ x, fderiv 𝕜 (Z x ∘ φ₀.symm) (φ₀ a) = Sum.elim d (fun k : K => e k) x := by
    rintro (j | k)
    · rfl
    · exact hfdz k
  have hind : HasIndependentDifferentialsAt E z' a := by
    rw [hasIndependentDifferentialsAt_iff_chart hφ₀.1 haφ₀ hz'd]
    have h2 : (fun k => fderiv 𝕜 (z' k ∘ φ₀.symm) (φ₀ a)) =
        (Sum.elim d fun k : K => e k) ∘ Eq.symm := funext fun k => hZfd (Eq.symm k)
    rw [h2]
    exact (linearIndependent_equiv Eq.symm).mpr hli
  -- (D) the chart and the open set where the representation and the invertibility hold
  obtain ⟨e₀, σ, he₀, hae₀, -, hZad, hz'e⟩ := exists_adaptedChart_zeroSet' E ψ z' a hz'c hz'0 hind
  set Gτ : M → Matrix (Fin s) (Fin s) 𝕜 := fun x => Matrix.of fun j j' => g j (τ j') x with hGτ
  -- invertibility of `Gτ a` from the independence of the exchanged family
  have hGa : IsUnit (Gτ a) := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    have hker : ∀ v : Fin s → 𝕜, Matrix.vecMul v (Gτ a) = 0 → v = 0 := by
      intro v hv
      have hv' : ∀ j', ∑ j, v j * g j (τ j') a = 0 := fun j' => congrFun hv j'
      have hsum : ∑ x : Fin s ⊕ K,
          (Sum.elim v fun k : K => -(∑ j, v j * g j k a)) x •
            Sum.elim d (fun k : K => e k) x = 0 := by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        have hA : ∑ j, v j • d j = ∑ k, (∑ j, v j * g j k a) • e k := by
          simp_rw [hDh, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_smul]
        rw [hA, ← Finset.sum_add_sum_compl K, ← hmapK, Finset.sum_map]
        have hB : ∑ j', (∑ j, v j * g j (τ j') a) • e (τ j') = 0 :=
          Finset.sum_eq_zero fun j' _ => by rw [hv' j', zero_smul]
        rw [hB, add_zero, Finset.sum_coe_sort K fun k => -(∑ j, v j * g j k a) • e k]
        simp only [neg_smul, Finset.sum_neg_distrib, add_neg_cancel]
      have := Fintype.linearIndependent_iff.mp hli _ hsum
      funext j
      exact this (Sum.inl j)
    intro v w hvw
    have hvw' : Matrix.vecMul v (Gτ a) = Matrix.vecMul w (Gτ a) := hvw
    have := hker (v - w) (by rw [Matrix.sub_vecMul, hvw', sub_self])
    exact sub_eq_zero.mp this
  have hdet_a : (Gτ a).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hGa).ne_zero
  -- the open neighbourhood `N` of `a`
  have hN : ∀ᶠ x in 𝓝 a, x ∈ V ∧ (∀ j, hfun j x = ∑ k, g j k x * z k x) ∧
      (∀ j k, x ∈ U j k) ∧ (Gτ x).det ≠ 0 := by
    have h1 : ∀ᶠ x in 𝓝 a, ∀ j, hfun j x = ∑ k, g j k x * z k x := eventually_all.mpr hrep
    have h2 : ∀ᶠ x in 𝓝 a, ∀ j k, x ∈ U j k :=
      eventually_all.mpr fun j => eventually_all.mpr fun k => (U j k).2.mem_nhds (haU j k)
    have h3 : ∀ᶠ x in 𝓝 a, (Gτ x).det ≠ 0 := by
      have hcont : ContinuousAt (fun x => (Gτ x).det) a := by
        refine (Continuous.matrix_det continuous_id).continuousAt.comp ?_
        refine continuousAt_pi.mpr fun j => continuousAt_pi.mpr fun j' => ?_
        exact ((hgU j (τ j')).continuousOn.continuousAt ((U j (τ j')).2.mem_nhds (haU j (τ j'))))
      exact hcont.eventually_ne hdet_a
    filter_upwards [V.2.mem_nhds haV, h1, h2, h3] with x hxV hx1 hx2 hx3 using ⟨hxV, hx1, hx2, hx3⟩
  obtain ⟨N, hNsub, hNo, haN⟩ := mem_nhds_iff.mp hN
  have hZad' := hZad.restrOpen' N hNo
  refine ⟨e₀.restrOpen N hNo, σ, τ, ?_, ⟨hZad'.1, fun x hx => ?_⟩, fun x hx => ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hae₀, haN⟩
  · have hx' := hx
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    obtain ⟨hxV, hxrep, hxU, hxdet⟩ := hNsub hx.2
    rw [← hZad'.2 x hx']
    constructor
    · intro hxY
      refine ⟨hx.1, fun k => ?_⟩
      rcases hEqk : Eq.symm k with j | kk
      · change Z (Eq.symm k) x = 0
        rw [hEqk]
        exact (hφ₁.2 x hxV.2).1 (hYS hxY) j
      · change Z (Eq.symm k) x = 0
        rw [hEqk]
        exact (hφ₀.2 x hxV.1).1 hxY kk
    · rintro ⟨-, hall⟩
      have hh0 : ∀ j, hfun j x = 0 := fun j => by
        have := hall (τ j)
        rwa [hz'τ j] at this
      have hzK : ∀ k : K, z k x = 0 := fun k => by
        have := hall k
        rwa [hz'K k] at this
      have hzτ : ∀ j', z (τ j') x = 0 := by
        have hGx : IsUnit (Gτ x) :=
          (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hxdet)
        have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hGx
        have hmul : (Gτ x).mulVec (fun j' => z (τ j') x) = 0 := by
          funext j
          change ∑ j', g j (τ j') x * z (τ j') x = 0
          rw [← hh0 j, hxrep j, ← Finset.sum_add_sum_compl K, ← hmapK, Finset.sum_map]
          have hK0 : ∑ k ∈ K, g j k x * z k x = 0 :=
            Finset.sum_eq_zero fun k hk => by rw [hzK ⟨k, hk⟩, mul_zero]
          rw [hK0, zero_add]
        have := hinj (hmul.trans (Matrix.mulVec_zero _).symm)
        exact fun j' => congrFun this j'
      rw [hφ₀.2 x hxV.1]
      intro k
      by_cases hk : k ∈ K
      · exact hzK ⟨k, hk⟩
      · obtain ⟨j', hj'⟩ := (hτ k).mpr hk
        rw [← hj']
        exact hzτ j'
  · rw [OpenPartialHomeomorph.restrOpen_source] at hx
    obtain ⟨hxV, -, -, -⟩ := hNsub hx.2
    rw [hφ₁.2 x hxV.2]
    refine forall_congr' fun j => ?_
    have h1 : ψ ((e₀.restrOpen N hNo) x) (σ (τ j)) = hfun j x := by
      change ψ (e₀ x) (σ (τ j)) = hfun j x
      rw [← hz'e x hx.1 (τ j), hz'τ j]
    rw [h1]

end Manifold
