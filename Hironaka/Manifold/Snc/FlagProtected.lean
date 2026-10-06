/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Defs
public import Hironaka.Manifold.Submanifold.Generators
import Hironaka.Manifold.AdaptedChart
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.BlowUp.Transform.StrictFlag
import Hironaka.Manifold.Chart.Adapted
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Flag charts with prescribed centre coordinates

`exists_adaptedChart_flag` (`Hironaka/Manifold/BlowUp/Transform/StrictFlag.lean`) produces, for
nested closed submanifolds `Y ⊆ S`, a chart adapted to `Y` in which `S` is cut out by `s` of the
`c` centre coordinates. Its construction exchanges `s` of the centre coordinates
`z_k = ψ_{σ₀ k} ∘ φ₀` of a chart `φ₀` adapted to `Y` for the `s` equations `h_j = ψ_{σ₁ j} ∘ φ₁` of
`S` taken from a chart `φ₁` adapted to `S`. In the presence of a divisor the exchange has to spare
the centre coordinates that are equations of components of the divisor: this module reproves the
construction with the two charts as inputs and a prescribed set `P` of centre indices that must be
kept, under the hypothesis that the differentials of the `h_j` and of the kept `z_p` are
independent (`exists_adaptedChart_flag_protected`), recording that the `S`-block of the new chart
is exactly the `h_j` and that the kept coordinates are unchanged
(`exists_finset_linearIndependent_sum_of_subset` is the exchange lemma with the prescribed subset).
A second step (`exists_adaptedChart_extend`) adjoins further functions with independent
differentials as coordinates outside the centre block, keeping the centre block; the conormal
lemma `fderiv_comp_symm_mem_span_of_forall_eq_zero` (the differential of a function vanishing on a
submanifold lies in the span of the centre coordinate functionals) supplies the independence
hypotheses. The module closes with the simultaneous chart for `(F, H, Z)`
(`HypersurfaceFamily.exists_isSncChartAt_flag_proper`): at a point of `Z ⊆ H`, from one chart
adapted to `Z` which is an snc chart of the family `F` and one chart adapted to `H` which is an snc
chart of `F` with no component coordinate in the `H`-block, a chart adapted to `Z`, cutting out `H`
by centre coordinates, which is an snc chart of `F` with every component coordinate off the
`H`-block.

These are the coordinates in which Kollár restricts a blow-up sequence to the strict transforms of
a closed subvariety [Kol07, 30.2] and requires the centres to have simple normal crossings with
the boundary [Kol07, Definition 66]; the local coordinates `x_1, …, x_n` with `S = (x_1 = 0)` and
centre `(x_1 = ⋯ = x_r = 0)` of the proof of [Kol07, Theorem 88] are the case `c = r`, `s = 1`. Not
in the sources as separate statements; used by `Hironaka/Manifold/Snc/Proper.lean` and
`Hironaka/Manifold/Snc/Trace.lean`.
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

/-! ### Linear algebra: the exchange lemma with a prescribed kept subset -/

section LinearAlgebra

variable {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- The exchange lemma with a prescribed kept subset: if the independent family `d` of `s` vectors
inside the span of the independent family `e` of `c` vectors stays independent together with the
`e p`, `p ∈ P`, it can be completed to a basis of that span by `c − s` of the `e k`, `k ∈ K`, with
`P ⊆ K`. -/
theorem exists_finset_linearIndependent_sum_of_subset {c s : ℕ} (e : Fin c → V)
    (he : LinearIndependent 𝕜 e) (d : Fin s → V)
    (hsub : ∀ j, d j ∈ Submodule.span 𝕜 (range e)) (P : Finset (Fin c))
    (hP : LinearIndependent 𝕜 (Sum.elim d fun p : P => e p)) :
    ∃ K : Finset (Fin c), P ⊆ K ∧ s + K.card = c ∧
      LinearIndependent 𝕜 (Sum.elim d fun k : K => e k) := by
  classical
  -- the family `d` together with the kept `e p`, indexed by `Fin (s + P.card)`
  set E₁ : Fin s ⊕ P ≃ Fin (s + P.card) :=
    (Equiv.sumCongr (Equiv.refl (Fin s)) P.equivFin).trans finSumFinEquiv with hE₁
  set d' : Fin (s + P.card) → V := (Sum.elim d fun p : P => e p) ∘ E₁.symm with hd'def
  have hd' : LinearIndependent 𝕜 d' := (linearIndependent_equiv E₁.symm).mpr hP
  have hsub' : ∀ j, d' j ∈ Submodule.span 𝕜 (range e) := by
    intro j
    rcases hj : E₁.symm j with i | p
    · simp only [hd'def, Function.comp_apply, hj, Sum.elim_inl]
      exact hsub i
    · simp only [hd'def, Function.comp_apply, hj, Sum.elim_inr]
      exact Submodule.subset_span ⟨p, rfl⟩
  obtain ⟨K', hK'c, hli'⟩ := exists_finset_linearIndependent_sum e he d' hd' hsub'
  -- `K'` misses `P`: a vector of `e` cannot appear twice in an independent family
  have hdisj : ∀ k ∈ K', k ∉ P := by
    intro k hk hkP
    have h : (Sum.inl (E₁ (Sum.inr ⟨k, hkP⟩)) : Fin (s + P.card) ⊕ K') = Sum.inr ⟨k, hk⟩ :=
      hli'.injective (by simp [hd'def])
    exact absurd h (by simp)
  refine ⟨P ∪ K', Finset.subset_union_left, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun k hkP hkK' => hdisj k hkK' hkP)]
    omega
  · -- reindex `Sum.elim d' (e k)_{k ∈ K'}` along `Fin s ⊕ (P ∪ K') → Fin (s + P.card) ⊕ K'`
    set f : Fin s ⊕ ↥(P ∪ K') → Fin (s + P.card) ⊕ K' := fun x =>
      match x with
      | Sum.inl j => Sum.inl (E₁ (Sum.inl j))
      | Sum.inr k =>
        if hk : (k : Fin c) ∈ P then Sum.inl (E₁ (Sum.inr ⟨k, hk⟩))
        else Sum.inr ⟨k, (Finset.mem_union.mp k.2).resolve_left hk⟩ with hfdef
    have hcomp : (Sum.elim d fun k : ↥(P ∪ K') => e k) = (Sum.elim d' fun k : K' => e k) ∘ f := by
      funext x
      rcases x with j | k
      · simp [hfdef, hd'def]
      · by_cases hk : (k : Fin c) ∈ P
        · simp [hfdef, hd'def, hk]
        · simp [hfdef, hk]
    have hfinj : Function.Injective f := by
      rintro (j | k) (j' | k') hxy
      · simp only [hfdef, Sum.inl.injEq] at hxy
        exact congrArg Sum.inl (Sum.inl_injective (E₁.injective hxy))
      · by_cases hk' : (k' : Fin c) ∈ P
        · simp only [hfdef, hk', dite_true, Sum.inl.injEq] at hxy
          exact absurd (E₁.injective hxy) (by simp)
        · simp [hfdef, hk'] at hxy
      · by_cases hk : (k : Fin c) ∈ P
        · simp only [hfdef, hk, dite_true, Sum.inl.injEq] at hxy
          exact absurd (E₁.injective hxy) (by simp)
        · simp [hfdef, hk] at hxy
      · by_cases hk : (k : Fin c) ∈ P <;> by_cases hk' : (k' : Fin c) ∈ P
        · simp only [hfdef, hk, hk', dite_true, Sum.inl.injEq] at hxy
          have := Sum.inr_injective (E₁.injective hxy)
          exact congrArg Sum.inr (Subtype.ext (Subtype.mk.inj this))
        · simp [hfdef, hk, hk'] at hxy
        · simp [hfdef, hk, hk'] at hxy
        · simp only [hfdef, hk, hk', dite_false, Sum.inr.injEq] at hxy
          exact congrArg Sum.inr (Subtype.ext (Subtype.mk.inj hxy))
    rw [hcomp]
    exact hli'.comp f hfinj

end LinearAlgebra

/-! ### Flag charts with prescribed kept centre coordinates -/

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y S Z H : Set M} {c s : ℕ}

/-- The flag chart with a prescribed set `P` of kept centre coordinates: let `φ₀` be a chart adapted
to `Y` and `φ₁` a chart adapted to `S ⊇ Y`, both containing `a ∈ Y`, and `P` a set of centre indices
such that the differentials at `a` of the `S`-equations `h_j = ψ_{σ₁ j} ∘ φ₁` together with the
kept centre coordinates `z_p = ψ_{σ₀ p} ∘ φ₀`, `p ∈ P`, are independent. Then there is a chart `e`
at `a`, with source inside both sources, adapted to `Y` (`σ`), in which `S` is cut out by the `s`
centre coordinates `σ (τ j)` — and these are exactly the `h_j` — while the kept centre coordinates
`σ p`, `p ∈ P` (all outside `range τ`), are exactly the `z_p`. Proof: the `h_j` vanish on `Y`, so
near `a` they are combinations `h_j = ∑_k g_{jk} z_k` of the centre coordinates (the germs of the
`h_j` lie in the ideal of `Y`, generated by the `z_k`); the exchange lemma replaces `s` non-kept
`z_k` by the `h_j` in the cotangent basis, the chart-extension theorem makes the exchanged family
the coordinates of a chart, and on the open set where the `s × s` minor of `(g_{jk})` on the
exchanged indices is invertible the flag equations hold. -/
theorem exists_adaptedChart_flag_protected (hY : IsClosedSubmanifold ψ Y c) (hYS : Y ⊆ S)
    {φ₀ : OpenPartialHomeomorph M E} {σ₀ : Fin c ↪ Fin n} (hφ₀ : IsAdaptedChart ψ Y φ₀ σ₀)
    {φ₁ : OpenPartialHomeomorph M E} {σ₁ : Fin s ↪ Fin n} (hφ₁ : IsAdaptedChart ψ S φ₁ σ₁)
    {a : M} (ha : a ∈ Y) (haφ₀ : a ∈ φ₀.source) (haφ₁ : a ∈ φ₁.source) (P : Finset (Fin c))
    (hP : LinearIndependent 𝕜 (Sum.elim
      (fun j => fderiv 𝕜 ((fun x => ψ (φ₁ x) (σ₁ j)) ∘ φ₀.symm) (φ₀ a))
      fun p : P => coordFunctional ψ (σ₀ p))) :
    ∃ (e : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n) (τ : Fin s ↪ Fin c),
      a ∈ e.source ∧ e.source ⊆ φ₀.source ∩ φ₁.source ∧ IsAdaptedChart ψ Y e σ ∧
        (∀ x ∈ e.source, x ∈ S ↔ ∀ j, ψ (e x) (σ (τ j)) = 0) ∧
        (∀ x ∈ e.source, ∀ j, ψ (e x) (σ (τ j)) = ψ (φ₁ x) (σ₁ j)) ∧
        ∀ p ∈ P, p ∉ Set.range τ ∧ ∀ x ∈ e.source, ψ (e x) (σ p) = ψ (φ₀ x) (σ₀ p) := by
  classical
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
  have hdiffz : ∀ k, MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (z k) a := fun k =>
    (((coordFunctional ψ (σ₀ k)).contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas hφ₀.1)).contMDiffAt
        (φ₀.open_source.mem_nhds haφ₀)).mdifferentiableAt (by simp)
  have heind : LinearIndependent 𝕜 e := by
    have h1 := (hasIndependentDifferentialsAt_iff_chart hφ₀.1 haφ₀ hdiffz).mp
      (hφ₀.hasIndependentDifferentialsAt haφ₀)
    have h2 : (fun k => fderiv 𝕜 (z k ∘ φ₀.symm) (φ₀ a)) = e := funext hfdz
    rwa [h2] at h1
  have hsub : ∀ j, d j ∈ Submodule.span 𝕜 (range e) := fun j => by
    rw [hDh j]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨K, hPK, hKc, hli⟩ := exists_finset_linearIndependent_sum_of_subset e heind d hsub P hP
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
  have hsrc : ∀ x, x ∈ (e₀.restrOpen N hNo).source ↔ x ∈ e₀.source ∧ x ∈ N := fun x => by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact Iff.rfl
  have hcoordτ : ∀ x ∈ (e₀.restrOpen N hNo).source, ∀ j,
      ψ ((e₀.restrOpen N hNo) x) (σ (τ j)) = hfun j x := by
    intro x hx j
    change ψ (e₀ x) (σ (τ j)) = hfun j x
    rw [← hz'e x ((hsrc x).mp hx).1 (τ j), hz'τ j]
  refine ⟨e₀.restrOpen N hNo, σ, τ, ?_, ?_, ⟨hZad'.1, fun x hx => ?_⟩, fun x hx => ?_,
    hcoordτ, fun p hpP => ⟨?_, fun x hx => ?_⟩⟩
  · exact (hsrc a).mpr ⟨hae₀, haN⟩
  · intro x hx
    exact (hNsub ((hsrc x).mp hx).2).1
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
    rw [hcoordτ x ((hsrc x).mpr hx) j]
  · intro hpτ
    exact ((hτ p).mp hpτ) (hPK hpP)
  · change ψ (e₀ x) (σ p) = z p x
    rw [← hz'e x ((hsrc x).mp hx).1 p, hz'K ⟨p, hPK hpP⟩]

/-! ### The conormal lemma, chart independence of independent differentials, and extension -/

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The conormal lemma: the differential at `a ∈ Y` of an analytic function vanishing on `Y` near
`a`, read in a chart `φ` adapted to `Y`, lies in the span of the centre coordinate functionals
`ψ_{σ k}` — the conormal space of `Y` at `a` (from
`IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_span`). -/
theorem fderiv_comp_symm_mem_span_of_forall_eq_zero (hY : IsClosedSubmanifold ψ Y c)
    {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} (hφ : IsAdaptedChart ψ Y φ σ) {a : M}
    (ha : a ∈ Y) (haφ : a ∈ φ.source) {f : M → 𝕜} (U : Opens M) (haU : a ∈ U)
    (hfU : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω f U) (hf0 : ∀ x ∈ U, x ∈ Y → f x = 0) :
    fderiv 𝕜 (f ∘ φ.symm) (φ a) ∈ Submodule.span 𝕜 (range fun k => coordFunctional ψ (σ k)) := by
  classical
  set hsec := sectionOfContMDiffOn f U hfU with hhsec
  have hmem : (structureSheaf 𝕜 E M).presheaf.germ U a haU hsec ∈ hY.idealSheaf.stalkIdeal a := by
    rw [hY.germ_mem_stalkIdeal_idealSheaf_iff U ha haU]
    filter_upwards [(continuous_subtype_val.isOpen_preimage _ U.2).mem_nhds
      (show (⟨a, ha⟩ : Y) ∈ {y : Y | (y : M) ∈ U} from haU)] with y hyU
    rw [extendSection_of_mem 𝕜 E _ hyU, sectionOfContMDiffOn_apply]
    exact hf0 y hyU y.2
  rw [hY.stalkIdeal_idealSheaf_eq_span ha hφ haφ, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨cf, hcf⟩ := hmem
  have hg : ∀ k, ∃ g : M → 𝕜, stalkToGerm 𝓘(𝕜, E) ω M a (cf k) = ↑g ∧
      ∃ W : Opens M, a ∈ W ∧ ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω g W := fun k =>
    (mem_range_stalkToGerm_iff 𝓘(𝕜, E) ω M a _).mp ⟨_, rfl⟩
  choose g hgc W haW hgW using hg
  -- the representation `f = ∑ g k * z k` near `a`
  have hrep : ∀ᶠ x in 𝓝 a, f x = ∑ k, g k x * ψ (φ x) (σ k) := by
    have h1 := congrArg (stalkToGerm 𝓘(𝕜, E) ω M a) hcf
    rw [map_sum, stalkToGerm_structureSheaf_germ] at h1
    simp only [smul_eq_mul, map_mul, hgc, stalkToGerm_coord, ← Germ.coe_mul] at h1
    rw [germ_coe_sum, Germ.coe_eq] at h1
    filter_upwards [h1, U.2.mem_nhds haU, φ.open_source.mem_nhds haφ] with x hx hxU hxφ
    rw [Finset.sum_apply] at hx
    have hx' : extendSection 𝕜 E hsec x = f x := by
      rw [extendSection_of_mem 𝕜 E _ hxU, sectionOfContMDiffOn_apply]
    rw [← hx', ← hx]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.mul_apply, extendSection_of_mem 𝕜 E _ hxφ]
    rfl
  -- the differentials of the coefficients and of the coordinates
  have hcd : ∀ k, DifferentiableAt 𝕜 (fun v : E => ψ v (σ k)) (φ a) := fun k =>
    (coordFunctional ψ (σ k)).differentiableAt
  have hcf' : ∀ k, fderiv 𝕜 (fun v : E => ψ v (σ k)) (φ a) = coordFunctional ψ (σ k) := fun k =>
    (coordFunctional ψ (σ k)).fderiv
  have hgd : ∀ k, DifferentiableAt 𝕜 (g k ∘ φ.symm) (φ a) := by
    intro k
    have h2 : IsOpen (φ.target ∩ φ.symm ⁻¹' (W k : Set M)) :=
      φ.isOpen_inter_preimage_symm (W k).2
    have h1 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (g k ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (W k : Set M)) :=
      (hgW k).comp ((contMDiffOn_symm_of_mem_maximalAtlas hφ.1).mono Set.inter_subset_left)
        fun v hv => hv.2
    have h3 : φ a ∈ φ.target ∩ φ.symm ⁻¹' (W k : Set M) :=
      ⟨φ.map_source haφ, by rw [Set.mem_preimage, φ.left_inv haφ]; exact haW k⟩
    exact (contMDiffAt_iff_contDiffAt.mp (h1.contMDiffAt (h2.mem_nhds h3))).differentiableAt
      (by simp)
  have hrep' : (f ∘ φ.symm) =ᶠ[𝓝 (φ a)] fun v => ∑ k, (g k ∘ φ.symm) v * ψ v (σ k) := by
    filter_upwards [(φ.tendsto_symm haφ).eventually hrep,
      φ.open_target.mem_nhds (φ.map_source haφ)] with v hv hvT
    rw [Function.comp_apply, hv]
    refine Finset.sum_congr rfl fun k _ => ?_
    change g k (φ.symm v) * ψ (φ (φ.symm v)) (σ k) = g k (φ.symm v) * ψ v (σ k)
    rw [φ.right_inv hvT]
  rw [hrep'.fderiv_eq]
  have hsumfun : (fun v : E => ∑ k, (g k ∘ φ.symm) v * ψ v (σ k)) =
      ∑ k, fun v : E => (g k ∘ φ.symm) v * ψ v (σ k) := by
    ext v
    simp [Finset.sum_apply]
  rw [hsumfun, fderiv_sum (A := fun k => fun v : E => (g k ∘ φ.symm) v * ψ v (σ k))
    fun k _ => (hgd k).mul (hcd k)]
  refine Submodule.sum_mem _ fun k _ => ?_
  change fderiv 𝕜 ((g k ∘ φ.symm) * fun v : E => ψ v (σ k)) (φ a) ∈ _
  rw [fderiv_mul (hgd k) (hcd k), hcf' k]
  have h0 : ψ (φ a) (σ k) = 0 := (hφ.2 a haφ).1 ha k
  simp only [h0, zero_smul, add_zero]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The independence of the differentials of a finite family of functions at `a`, read in a chart,
does not depend on the chart (`hasIndependentDifferentialsAt_iff_chart`). -/
theorem linearIndependent_fderiv_comp_symm_iff {ι : Type*} [Finite ι] {w : ι → M → 𝕜} {a : M}
    (hw : ∀ i, MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (w i) a) {χ₀ χ₁ : OpenPartialHomeomorph M E}
    (hχ₀ : χ₀ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (haχ₀ : a ∈ χ₀.source)
    (hχ₁ : χ₁ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (haχ₁ : a ∈ χ₁.source) :
    LinearIndependent 𝕜 (fun i => fderiv 𝕜 (w i ∘ χ₀.symm) (χ₀ a)) ↔
      LinearIndependent 𝕜 fun i => fderiv 𝕜 (w i ∘ χ₁.symm) (χ₁ a) := by
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  have hw' : ∀ i, MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) ((w ∘ e.symm) i) a := fun i => hw _
  have h0 := hasIndependentDifferentialsAt_iff_chart hχ₀ haχ₀ hw'
  have h1 := hasIndependentDifferentialsAt_iff_chart hχ₁ haχ₁ hw'
  rw [← linearIndependent_equiv e.symm (f := fun i => fderiv 𝕜 (w i ∘ χ₀.symm) (χ₀ a)),
    ← linearIndependent_equiv e.symm (f := fun i => fderiv 𝕜 (w i ∘ χ₁.symm) (χ₁ a))]
  exact h0.symm.trans h1

/-- A chart `e` adapted to `Y` at `a ∈ Y` and a finite family `v` of analytic functions vanishing at
`a` whose differentials are independent together with those of the centre coordinates of `e` (read
in any chart `χ`) can be completed to a chart `e'` adapted to `Y`, with source inside that of `e`,
whose centre block is that of `e` and which has the `v l` as coordinates outside the centre block
(from the chart-extension theorem `exists_chart_extending`). -/
theorem exists_adaptedChart_extend {e : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n}
    (he : IsAdaptedChart ψ Y e σ) {a : M} (ha : a ∈ Y) (hae : a ∈ e.source)
    {ι : Type*} [Finite ι] (v : ι → M → 𝕜) (hv : ∀ l, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (v l) a)
    (hv0 : ∀ l, v l a = 0) {χ : OpenPartialHomeomorph M E} (hχ : χ ∈ maximalAtlas 𝓘(𝕜, E) ω M)
    (haχ : a ∈ χ.source)
    (hind : LinearIndependent 𝕜 (Sum.elim
      (fun k => fderiv 𝕜 ((fun x => ψ (e x) (σ k)) ∘ χ.symm) (χ a))
      fun l => fderiv 𝕜 (v l ∘ χ.symm) (χ a))) :
    ∃ (e' : OpenPartialHomeomorph M E) (σ' : Fin c ↪ Fin n) (ρ : ι ↪ Fin n),
      a ∈ e'.source ∧ e'.source ⊆ e.source ∧ IsAdaptedChart ψ Y e' σ' ∧
        (∀ x ∈ e'.source, ∀ k, ψ (e' x) (σ' k) = ψ (e x) (σ k)) ∧
        (∀ x ∈ e'.source, ∀ l, ψ (e' x) (ρ l) = v l x) ∧ ∀ l, ρ l ∉ Set.range σ' := by
  classical
  obtain ⟨N, ⟨eι⟩⟩ := Finite.exists_equiv_fin ι
  set E₂ : Fin c ⊕ ι ≃ Fin (c + N) :=
    (Equiv.sumCongr (Equiv.refl _) eι).trans finSumFinEquiv with hE₂
  set Z : Fin c ⊕ ι → M → 𝕜 := Sum.elim (fun k x => ψ (e x) (σ k)) v with hZ
  set w : Fin (c + N) → M → 𝕜 := Z ∘ E₂.symm with hw
  have hZc : ∀ i, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (Z i) a := by
    rintro (k | l)
    · exact ((coordFunctional ψ (σ k)).contMDiff.comp_contMDiffOn
        (contMDiffOn_of_mem_maximalAtlas he.1)).contMDiffAt (e.open_source.mem_nhds hae)
    · exact hv l
  have hZ0 : ∀ i, Z i a = 0 := by
    rintro (k | l)
    · exact (he.2 a hae).1 ha k
    · exact hv0 l
  have hwc : ∀ i, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (w i) a := fun i => hZc _
  have hw0 : ∀ i, w i a = 0 := fun i => hZ0 _
  have hwd : ∀ i, MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (w i) a := fun i =>
    (hwc i).mdifferentiableAt (by simp)
  have hind' : HasIndependentDifferentialsAt E w a := by
    rw [hasIndependentDifferentialsAt_iff_chart hχ haχ hwd]
    have : (fun i => fderiv 𝕜 (w i ∘ χ.symm) (χ a)) =
        (Sum.elim (fun k => fderiv 𝕜 ((fun x => ψ (e x) (σ k)) ∘ χ.symm) (χ a))
          fun l => fderiv 𝕜 (v l ∘ χ.symm) (χ a)) ∘ E₂.symm := by
      funext i
      rcases hi : E₂.symm i with k | l <;> simp [hw, hZ, hi]
    rw [this]
    exact (linearIndependent_equiv E₂.symm).mpr hind
  obtain ⟨e₀, σ₀, he₀, hae₀, -, hwe⟩ := exists_chart_extending ψ w a hwc hw0 hind'
  set e' := e₀.restrOpen e.source e.open_source with he'
  have hsrc : ∀ x, x ∈ e'.source ↔ x ∈ e₀.source ∧ x ∈ e.source := fun x => by
    rw [he', OpenPartialHomeomorph.restrOpen_source]
    exact Iff.rfl
  have he'mem : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M := by
    rw [he', OpenPartialHomeomorph.restrOpen_eq_restr]
    exact restr_mem_maximalAtlas _ he₀ e.open_source
  set σ' : Fin c ↪ Fin n :=
    ⟨fun k => σ₀ (E₂ (Sum.inl k)), fun k k' h =>
      Sum.inl_injective (E₂.injective (σ₀.injective h))⟩ with hσ'
  set ρ : ι ↪ Fin n :=
    ⟨fun l => σ₀ (E₂ (Sum.inr l)), fun l l' h =>
      Sum.inr_injective (E₂.injective (σ₀.injective h))⟩ with hρ
  have hcoordσ : ∀ x ∈ e'.source, ∀ k, ψ (e' x) (σ' k) = ψ (e x) (σ k) := by
    intro x hx k
    change ψ (e₀ x) (σ₀ (E₂ (Sum.inl k))) = ψ (e x) (σ k)
    rw [← hwe x ((hsrc x).mp hx).1]
    simp [hw, hZ]
  have hcoordρ : ∀ x ∈ e'.source, ∀ l, ψ (e' x) (ρ l) = v l x := by
    intro x hx l
    change ψ (e₀ x) (σ₀ (E₂ (Sum.inr l))) = v l x
    rw [← hwe x ((hsrc x).mp hx).1]
    simp [hw, hZ]
  refine ⟨e', σ', ρ, (hsrc a).mpr ⟨hae₀, hae⟩, fun x hx => ((hsrc x).mp hx).2,
    ⟨he'mem, fun x hx => ?_⟩, hcoordσ, hcoordρ, fun l ⟨k, hk⟩ => ?_⟩
  · rw [he.2 x ((hsrc x).mp hx).2]
    exact forall_congr' fun k => by rw [hcoordσ x hx k]
  · have hk' : σ₀ (E₂ (Sum.inl k)) = σ₀ (E₂ (Sum.inr l)) := hk
    exact Sum.inl_ne_inr (E₂.injective (σ₀.injective hk'))

/-! ### Simultaneous adapted coordinates for `(F, H, Z)` -/

variable {F : HypersurfaceFamily M}

/-- Simultaneous adapted coordinates for `(F, H, Z)` (the coordinates of the proof of
[Kol07, Theorem 88], with a boundary; [Kol07, Definition 24 (4)]). Let `Z ⊆ H` be closed
submanifolds and `F` an snc family; suppose `φ₀` is a chart adapted to `Z` which is an snc chart of
`F` at `a ∈ Z` and `φ₁` a chart adapted to `H` which is an snc chart of `F` at `a` whose component
coordinates lie outside the `H`-block (properly: no component contains `H` near `a`). Then there
is a chart adapted to `Z` in which `H` is cut out by `s` of the centre coordinates (`σ ∘ τ`) and
which is an snc chart of `F` at `a` with every component coordinate outside the `H`-block `σ ∘ τ`.
Proof: the exchange of `exists_adaptedChart_flag_protected` keeps the centre coordinates of `φ₀`
that are component equations (their differentials are independent of the `H`-equations, being
nonzero multiples of the `φ₁`-coordinates `cidx₁ j ∉ range σ₁` by the conormal lemma), and
`exists_adaptedChart_extend` adjoins the component equations of `φ₀` off the centre block
(independent of the centre block, again by the conormal lemma). -/
theorem HypersurfaceFamily.exists_isSncChartAt_flag_proper (hF : F.IsSnc ψ)
    (hZ : IsClosedSubmanifold ψ Z c) (hZH : Z ⊆ H)
    {φ₀ : OpenPartialHomeomorph M E} {σ₀ : Fin c ↪ Fin n} (hφ₀ : IsAdaptedChart ψ Z φ₀ σ₀)
    {a : M} (ha : a ∈ Z) {cidx₀ : {j // a ∈ F.hyp j} → Fin n} (hc₀ : F.IsSncChartAt ψ φ₀ a cidx₀)
    {φ₁ : OpenPartialHomeomorph M E} {σ₁ : Fin s ↪ Fin n} (hφ₁ : IsAdaptedChart ψ H φ₁ σ₁)
    {cidx₁ : {j // a ∈ F.hyp j} → Fin n} (hc₁ : F.IsSncChartAt ψ φ₁ a cidx₁)
    (hproper : ∀ j, cidx₁ j ∉ Set.range σ₁) :
    ∃ (e : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n) (τ : Fin s ↪ Fin c)
      (cidx : {j // a ∈ F.hyp j} → Fin n),
      IsAdaptedChart ψ Z e σ ∧ (∀ x ∈ e.source, x ∈ H ↔ ∀ j, ψ (e x) (σ (τ j)) = 0) ∧
        F.IsSncChartAt ψ e a cidx ∧ ∀ j, cidx j ∉ Set.range (τ.trans σ) := by
  classical
  have haφ₀ : a ∈ φ₀.source := hc₀.2.1
  have haφ₁ : a ∈ φ₁.source := hc₁.2.1
  -- the differential of a chart coordinate read in its own chart
  have hfd : ∀ (χ : OpenPartialHomeomorph M E), a ∈ χ.source → ∀ i : Fin n,
      fderiv 𝕜 ((fun x => ψ (χ x) i) ∘ χ.symm) (χ a) = coordFunctional ψ i := by
    intro χ haχ i
    have hev : ((fun x => ψ (χ x) i) ∘ χ.symm) =ᶠ[𝓝 (χ a)] fun v => ψ v i := by
      filter_upwards [χ.open_target.mem_nhds (χ.map_source haχ)] with v hv
      change ψ (χ (χ.symm v)) i = ψ v i
      rw [χ.right_inv hv]
    rw [hev.fderiv_eq]
    exact (coordFunctional ψ i).fderiv
  -- the centre coordinates of `φ₀` that are component equations
  set P : Finset (Fin c) := Finset.univ.filter fun p => ∃ j : {j // a ∈ F.hyp j}, cidx₀ j = σ₀ p
    with hPdef
  have hPj : ∀ p : P, ∃ j : {j // a ∈ F.hyp j}, cidx₀ j = σ₀ p := fun p =>
    (Finset.mem_filter.mp p.2).2
  choose jp hjp using hPj
  set z : Fin c → M → 𝕜 := fun p x => ψ (φ₀ x) (σ₀ p) with hzdef
  have hzV : ∀ p, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (z p) φ₀.source := fun p =>
    (coordFunctional ψ (σ₀ p)).contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas hφ₀.1)
  have hzc : ∀ p, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (z p) a := fun p =>
    (hzV p).contMDiffAt (φ₀.open_source.mem_nhds haφ₀)
  have hzd : ∀ p, MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (z p) a := fun p =>
    (hzc p).mdifferentiableAt (by simp)
  -- in the chart `φ₁`, `z p` (`p ∈ P`) vanishes on the component `jp p`: its differential is a
  -- nonzero multiple of `ψ_{cidx₁ (jp p)}`
  have hzind : LinearIndependent 𝕜 fun p => fderiv 𝕜 (z p ∘ φ₁.symm) (φ₁ a) :=
    (hasIndependentDifferentialsAt_iff_chart hφ₁.1 haφ₁ hzd).mp
      (hφ₀.hasIndependentDifferentialsAt haφ₀)
  have hzP : ∀ p : P, ∃ t : 𝕜, t ≠ 0 ∧
      fderiv 𝕜 (z p ∘ φ₁.symm) (φ₁ a) = t • coordFunctional ψ (cidx₁ (jp p)) := by
    intro p
    have hmem := fderiv_comp_symm_mem_span_of_forall_eq_zero (hF.1 (jp p).1)
      (hc₁.isAdaptedChart_hyp (jp p)) (jp p).2 haφ₁ ⟨φ₀.source, φ₀.open_source⟩ haφ₀ (hzV p)
      fun x hx hxj => by
        have := (hc₀.mem_iff (jp p) hx).mp hxj
        rwa [hjp p] at this
    simp only [singleEmb_apply, Set.range_const, Submodule.mem_span_singleton] at hmem
    obtain ⟨t, ht⟩ := hmem
    refine ⟨t, fun ht0 => ?_, ht.symm⟩
    have hne := hzind.ne_zero (p : Fin c)
    rw [← ht, ht0, zero_smul] at hne
    exact hne rfl
  choose t ht0 htz using hzP
  -- the exchange with the `P`-coordinates protected
  set hfun : Fin s → M → 𝕜 := fun j x => ψ (φ₁ x) (σ₁ j) with hhdef
  have hhc : ∀ j, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (hfun j) a := fun j =>
    ((coordFunctional ψ (σ₁ j)).contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas hφ₁.1)).contMDiffAt (φ₁.open_source.mem_nhds haφ₁)
  set W : Fin s ⊕ P → M → 𝕜 := Sum.elim hfun fun p : P => z p with hWdef
  have hWd : ∀ i, MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (W i) a := by
    rintro (j | p)
    · exact (hhc j).mdifferentiableAt (by simp)
    · exact hzd p
  have hW₁ : LinearIndependent 𝕜 fun i => fderiv 𝕜 (W i ∘ φ₁.symm) (φ₁ a) := by
    set ι : Fin s ⊕ P → Fin n := Sum.elim σ₁ fun p => cidx₁ (jp p) with hιdef
    have hιinj : Function.Injective ι := by
      rintro (j | p) (j' | p') h <;> simp only [hιdef, Sum.elim_inl, Sum.elim_inr] at h
      · exact congrArg Sum.inl (σ₁.injective h)
      · exact absurd ⟨j, h⟩ (hproper (jp p'))
      · exact absurd ⟨j', h.symm⟩ (hproper (jp p))
      · have h1 : jp p = jp p' := hc₁.injective h
        have h2 : σ₀ p = σ₀ p' := by rw [← hjp p, ← hjp p', h1]
        exact congrArg Sum.inr (Subtype.ext (σ₀.injective h2))
    have hbase : LinearIndependent 𝕜 fun i => coordFunctional ψ (ι i) :=
      (linearIndependent_coordFunctional ψ (Function.Embedding.refl _)).comp ι hιinj
    set u : Fin s ⊕ P → 𝕜ˣ := Sum.elim (fun _ => 1) fun p => Units.mk0 (t p) (ht0 p) with hudef
    have := hbase.units_smul u
    convert this using 1
    funext i
    rcases i with j | p
    · simp only [hWdef, hudef, hιdef, Sum.elim_inl, Pi.smul_apply', one_smul]
      exact hfd φ₁ haφ₁ (σ₁ j)
    · simp only [hWdef, hudef, hιdef, Sum.elim_inr, Pi.smul_apply', Units.smul_def, Units.val_mk0]
      exact htz p
  have hW₀ : LinearIndependent 𝕜 fun i => fderiv 𝕜 (W i ∘ φ₀.symm) (φ₀ a) :=
    (linearIndependent_fderiv_comp_symm_iff hWd hφ₀.1 haφ₀ hφ₁.1 haφ₁).mpr hW₁
  have hP : LinearIndependent 𝕜 (Sum.elim
      (fun j => fderiv 𝕜 ((fun x => ψ (φ₁ x) (σ₁ j)) ∘ φ₀.symm) (φ₀ a))
      fun p : P => coordFunctional ψ (σ₀ p)) := by
    convert hW₀ using 1
    funext i
    rcases i with j | p
    · rfl
    · simp only [Sum.elim_inr, hWdef]
      exact (hfd φ₀ haφ₀ (σ₀ p)).symm
  obtain ⟨e, σ, τ, hae, hesub, heZ, hflag, hcoordτ, hkeep⟩ :=
    exists_adaptedChart_flag_protected hZ hZH hφ₀ hφ₁ ha haφ₀ haφ₁ P hP
  -- the component equations of `φ₀` off the centre block, adjoined as coordinates
  have : Finite {j // a ∈ F.hyp j} := Finite.of_injective cidx₀ hc₀.injective
  set Q := {j : {j // a ∈ F.hyp j} // cidx₀ j ∉ Set.range σ₀} with hQdef
  set v : Q → M → 𝕜 := fun q x => ψ (φ₀ x) (cidx₀ q.1) with hvdef
  have hvc : ∀ q : Q, ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (v q) a := fun q =>
    ((coordFunctional ψ (cidx₀ q.1)).contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas hφ₀.1)).contMDiffAt (φ₀.open_source.mem_nhds haφ₀)
  have hv0 : ∀ q : Q, v q a = 0 := fun q => (hc₀.mem_iff q.1 haφ₀).mp q.1.2
  have hed : ∀ k, MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (fun y => ψ (e y) (σ k)) a := fun k =>
    (((coordFunctional ψ (σ k)).contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas heZ.1)).contMDiffAt
        (e.open_source.mem_nhds hae)).mdifferentiableAt (by simp)
  have hA : LinearIndependent 𝕜 fun k => fderiv 𝕜 ((fun y => ψ (e y) (σ k)) ∘ φ₀.symm) (φ₀ a) :=
    (hasIndependentDifferentialsAt_iff_chart hφ₀.1 haφ₀ hed).mp
      (heZ.hasIndependentDifferentialsAt hae)
  have hAspan : ∀ k, fderiv 𝕜 ((fun y => ψ (e y) (σ k)) ∘ φ₀.symm) (φ₀ a) ∈
      Submodule.span 𝕜 (range fun k' => coordFunctional ψ (σ₀ k')) := fun k =>
    fderiv_comp_symm_mem_span_of_forall_eq_zero hZ hφ₀ ha haφ₀ ⟨e.source, e.open_source⟩ hae
      ((coordFunctional ψ (σ k)).contMDiff.comp_contMDiffOn
        (contMDiffOn_of_mem_maximalAtlas heZ.1))
      fun x hx hxZ => (heZ.2 x hx).1 hxZ k
  have hBli : LinearIndependent 𝕜 fun q : Q => coordFunctional ψ (cidx₀ q.1) :=
    (linearIndependent_coordFunctional ψ (Function.Embedding.refl _)).comp (fun q : Q => cidx₀ q.1)
      fun q q' h => Subtype.ext (hc₀.injective h)
  have hindext : LinearIndependent 𝕜 (Sum.elim
      (fun k => fderiv 𝕜 ((fun x => ψ (e x) (σ k)) ∘ φ₀.symm) (φ₀ a))
      fun q : Q => fderiv 𝕜 (v q ∘ φ₀.symm) (φ₀ a)) := by
    have hB : (fun q : Q => fderiv 𝕜 (v q ∘ φ₀.symm) (φ₀ a)) =
        fun q => coordFunctional ψ (cidx₀ q.1) := funext fun q => hfd φ₀ haφ₀ (cidx₀ q.1)
    rw [hB]
    refine LinearIndependent.sum_type hA hBli ?_
    have hLI := linearIndependent_coordFunctional ψ (Function.Embedding.refl (Fin n))
    have hst : Disjoint (range σ₀) (range fun q : Q => cidx₀ q.1) := by
      rw [Set.disjoint_right]
      rintro _ ⟨q, rfl⟩ hq
      exact q.2 hq
    have hd := hLI.disjoint_span_image hst
    simp only [Function.Embedding.refl_apply, ← Set.range_comp] at hd
    refine Disjoint.mono_left ?_ hd
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hAspan k
  obtain ⟨e', σ', ρ, hae', he'sub, he'Z, hcoordσ, hcoordρ, hρσ⟩ :=
    exists_adaptedChart_extend heZ ha hae v hvc hv0 hφ₀.1 haφ₀ hindext
  -- the component coordinates of the new chart
  have hcidx : ∀ j : {j // a ∈ F.hyp j}, ∃ i : Fin n,
      (∀ x ∈ e'.source, x ∈ F.hyp j.1 ↔ ψ (e' x) i = 0) ∧ i ∉ range (τ.trans σ') ∧
        ((∃ p : P, i = σ' p ∧ cidx₀ j = σ₀ p) ∨ ∃ q : Q, q.1 = j ∧ i = ρ q) := by
    intro j
    by_cases h : cidx₀ j ∈ range σ₀
    · obtain ⟨p, hp⟩ := h
      have hpP : p ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hp.symm⟩
      obtain ⟨hpτ, hpz⟩ := hkeep p hpP
      refine ⟨σ' p, fun x hx => ?_, ?_, Or.inl ⟨⟨p, hpP⟩, rfl, hp.symm⟩⟩
      · have hxe : x ∈ e.source := he'sub hx
        rw [hcoordσ x hx p, hpz x hxe, hp]
        exact hc₀.mem_iff j (hesub hxe).1
      · rintro ⟨j', hj'⟩
        have hj'' : σ' (τ j') = σ' p := hj'
        exact hpτ ⟨j', σ'.injective hj''⟩
    · refine ⟨ρ ⟨j, h⟩, fun x hx => ?_, ?_, Or.inr ⟨⟨j, h⟩, rfl, rfl⟩⟩
      · rw [hcoordρ x hx ⟨j, h⟩]
        exact hc₀.mem_iff j (hesub (he'sub hx)).1
      · rintro ⟨j', hj'⟩
        exact hρσ ⟨j, h⟩ ⟨τ j', hj'⟩
  choose cidx hcmem hcτ hccase using hcidx
  refine ⟨e', σ', τ, cidx, he'Z, fun x hx => ?_, ⟨he'Z.1, hae', hcmem, ?_⟩, hcτ⟩
  · rw [hflag x (he'sub hx)]
    exact forall_congr' fun j => by rw [hcoordσ x hx (τ j)]
  · intro j j' hjj'
    rcases hccase j with ⟨p, hp, hp0⟩ | ⟨q, hq, hq0⟩ <;>
      rcases hccase j' with ⟨p', hp', hp0'⟩ | ⟨q', hq', hq0'⟩
    · have h1 : σ' p = σ' p' := by rw [← hp, ← hp', hjj']
      have h2 : (p : Fin c) = p' := σ'.injective h1
      exact hc₀.injective (by rw [hp0, hp0', h2])
    · exact absurd (hp.symm.trans (hjj'.trans hq0')) fun h => hρσ q' ⟨p, h⟩
    · exact absurd (hp'.symm.trans (hjj'.symm.trans hq0)) fun h => hρσ q ⟨p', h⟩
    · have h1 : ρ q = ρ q' := by rw [← hq0, ← hq0', hjj']
      have h2 : q = q' := ρ.injective h1
      rw [← hq, ← hq', h2]

end Manifold

end
