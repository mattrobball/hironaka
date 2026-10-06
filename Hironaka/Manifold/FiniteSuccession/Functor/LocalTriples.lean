/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
public import Hironaka.Manifold.SigmaManifold
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaTriple
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Chart domains transport along analytic open embeddings; countable chart unions

An analytic open embedding `ι : N → M` (a local analytic isomorphism that is injective) is an
analytic isomorphism onto its open range: `IsAnalyticOpenEmbedding.toPartialDiffeomorph` (source
`univ`, target `range ι`, inverse `Function.invFun ι`, analytic because it agrees near every point
of the range with the inverse of a local inverse of `ι`). Along it a chart of `N` transports to a
chart of `M` with source the image (`transportChart`), so a countable disjoint union of countable
chart unions is a countable chart union (`isCountableChartUnion_of_cover`), whence the local
triples of [Kol07, Proposition 37] are closed under countable disjoint unions
(`closedUnderSigma_isLocal`, clause (2)(ii) of [Kol07, Theorem 105]; [Kol07, Warning 38]) and the
disjoint union of chart unions is one (`isCountableChartUnion_sigma`).
-/

@[expose] public section

noncomputable section

open Set Topology Function
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

namespace IsAnalyticOpenEmbedding

variable {ι : AnalyticMap N M} (hι : IsAnalyticOpenEmbedding ι)
include hι

theorem isOpenEmbedding : IsOpenEmbedding ι :=
  .of_continuous_injective_isOpenMap ι.contMDiff.continuous hι.2 hι.1.isOpenMap

theorem isOpen_range : IsOpen (range ι) := hι.1.isOpen_range

/-- Near a point of the range, `Function.invFun ι` is the inverse of a local inverse of `ι`. -/
theorem contMDiffAt_invFun [Nonempty N] {y : M} (hy : y ∈ range ι) :
    ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (Function.invFun ι) y := by
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨Φ, hxΦ, hΦ⟩ := (hι.1 x).exists_partialDiffeomorph
  have hyΦ : ι x ∈ Φ.target := by
    rw [hΦ hxΦ]
    exact Φ.map_source hxΦ
  have hsymm : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω Φ.symm (ι x) :=
    Φ.symm.contMDiffOn_toFun.contMDiffAt (Φ.open_target.mem_nhds hyΦ)
  refine hsymm.congr_of_eventuallyEq ?_
  filter_upwards [Φ.open_target.mem_nhds hyΦ] with y' hy'
  have hmem : Φ.symm y' ∈ Φ.source := Φ.map_target hy'
  have hι' : ι (Φ.symm y') = y' := by
    rw [hΦ hmem]
    exact Φ.right_inv hy'
  exact hι.2 (by rw [Function.invFun_eq ⟨Φ.symm y', hι'⟩, hι'])

/-- An analytic open embedding as an analytic isomorphism onto its range. -/
def toPartialDiffeomorph [Nonempty N] : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω where
  toFun := ι
  invFun := Function.invFun ι
  source := univ
  target := range ι
  map_source' x _ := mem_range_self x
  map_target' _ _ := mem_univ _
  left_inv' x _ := Function.leftInverse_invFun hι.2 x
  right_inv' _ hy := Function.invFun_eq hy
  open_source := isOpen_univ
  open_target := hι.isOpen_range
  contMDiffOn_toFun := ι.contMDiff.contMDiffOn
  contMDiffOn_invFun _ hy := (hι.contMDiffAt_invFun hy).contMDiffWithinAt

/-- A chart of `N` transports along the embedding to a chart of `M` with source the image of its
source (`transportChart`). -/
theorem exists_chart_image [Nonempty N] {φ : OpenPartialHomeomorph N E}
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω N) :
    ∃ χ : OpenPartialHomeomorph M E, χ ∈ maximalAtlas 𝓘(𝕜, E) ω M ∧ χ.source = ι '' φ.source := by
  refine ⟨transportChart hι.toPartialDiffeomorph φ,
    transportChart_mem_maximalAtlas _ hφ, ?_⟩
  rw [transportChart_source]
  ext y
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    have : Function.invFun ι (ι x) = x := Function.leftInverse_invFun hι.2 x
    change Function.invFun ι (ι x) ∈ φ.source at hx
    rwa [this] at hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨mem_range_self x, ?_⟩
    change Function.invFun ι (ι x) ∈ φ.source
    rw [Function.leftInverse_invFun hι.2 x]
    exact hx

end IsAnalyticOpenEmbedding

/-- A family of analytic open embeddings with pairwise disjoint ranges covering `M`: each range is
clopen (its complement is the union of the other ranges). -/
theorem isClopen_range_of_cover {σ : Type u} {N : σ → AnalyticManifold.{u} 𝕜 E}
    (ι : ∀ i, AnalyticMap (N i) M) (hι : ∀ i, IsAnalyticOpenEmbedding (ι i))
    (hdisj : Pairwise (fun i j => Disjoint (range (ι i)) (range (ι j))))
    (hcov : (⋃ i, range (ι i)) = univ) (i : σ) : IsClopen (range (ι i)) := by
  refine ⟨?_, (hι i).isOpen_range⟩
  rw [← isOpen_compl_iff]
  have : (range (ι i))ᶜ = ⋃ j ∈ ({i}ᶜ : Set σ), range (ι j) := by
    ext y
    constructor
    · intro hy
      have hy' : y ∈ ⋃ j, range (ι j) := hcov ▸ mem_univ y
      obtain ⟨j, hj⟩ := mem_iUnion.mp hy'
      refine mem_iUnion₂.mpr ⟨j, fun hji => hy ?_, hj⟩
      rw [mem_singleton_iff] at hji
      exact hji ▸ hj
    · intro hy hyi
      obtain ⟨j, hji, hj⟩ := mem_iUnion₂.mp hy
      exact (hdisj (Ne.symm hji)).notMem_of_mem_left hyi hj
  rw [this]
  exact isOpen_biUnion fun j _ => (hι j).isOpen_range

/-- [Kol07, Warning 38], Proposition 37: a manifold covered by a
countable family of analytic open embeddings with pairwise disjoint ranges, each from a countable
chart union, is a countable chart union — the pieces are the images of the pieces, clopen because
the ranges are clopen, with the charts transported along the embeddings. -/
theorem _root_.AnalyticManifold.isCountableChartUnion_of_cover {σ : Type u}
    [Countable σ] {N : σ → AnalyticManifold.{u} 𝕜 E} (ι : ∀ i, AnalyticMap (N i) M)
    (hι : ∀ i, IsAnalyticOpenEmbedding (ι i))
    (hdisj : Pairwise (fun i j => Disjoint (range (ι i)) (range (ι j))))
    (hcov : (⋃ i, range (ι i)) = univ) (hN : ∀ i, (N i).IsCountableChartUnion) :
    M.IsCountableChartUnion := by
  choose τ hτ U hU using hN
  have : ∀ i, Countable (τ i) := hτ
  refine ⟨Σ i, τ i, inferInstance, fun p => ι p.1 '' U p.1 p.2, fun p => ?_, ?_, ?_, fun p => ?_⟩
  · have hclo := isClopen_range_of_cover ι hι hdisj hcov p.1
    have hemb := (hι p.1).isOpenEmbedding
    refine ⟨?_, hemb.isOpenMap _ ((hU p.1).1 p.2).2⟩
    exact hemb.isEmbedding.isInducing.isClosedMap hclo.1 _ ((hU p.1).1 p.2).1
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    by_cases hii : i = i'
    · subst hii
      have hjj : j ≠ j' := fun h => hne (h ▸ rfl)
      exact (Set.disjoint_image_iff (hι i).2).mpr ((hU i).2.1 hjj)
    · exact ((hdisj hii).mono (image_subset_range _ _) (image_subset_range _ _))
  · refine eq_univ_of_forall fun y => ?_
    have hy : y ∈ ⋃ i, range (ι i) := hcov ▸ mem_univ y
    obtain ⟨i, x, rfl⟩ := mem_iUnion.mp hy
    have hx : x ∈ ⋃ j, U i j := (hU i).2.2.1 ▸ mem_univ x
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨⟨i, j⟩, x, hj, rfl⟩
  · obtain ⟨φ, hφ, hφs⟩ := (hU p.1).2.2.2 p.2
    have : Nonempty (N p.1) := ⟨φ.symm 0⟩
    obtain ⟨χ, hχ, hχs⟩ := (hι p.1).exists_chart_image hφ
    exact ⟨χ, hχ, hχs.trans (congrArg (fun t => ι p.1 '' t) hφs)⟩

theorem pairwise_disjoint_range_sigmaMk {σ : Type u} [Countable σ]
    (N : σ → AnalyticManifold.{u} 𝕜 E) :
    Pairwise (fun i j => Disjoint (range (sigmaMk N i)) (range (sigmaMk N j))) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro _ ⟨y, rfl⟩ ⟨z, hz⟩
  exact hij (congrArg Sigma.fst hz).symm

theorem iUnion_range_sigmaMk {σ : Type u} [Countable σ] (N : σ → AnalyticManifold.{u} 𝕜 E) :
    (⋃ i, range (sigmaMk N i)) = univ :=
  eq_univ_of_forall fun p => mem_iUnion.mpr ⟨p.1, p.2, rfl⟩

/-- [Kol07, Warning 38] ([Kol07, Theorem 105, (2)(ii)] for the classes of [Kol07, Proposition 37]):
the local triples are closed under countable disjoint unions. -/
theorem AnalyticTriple.closedUnderSigma_isLocal :
    AnalyticTriple.ClosedUnderSigma (ψ₀ := ψ₀) AnalyticTriple.IsLocal := by
  intro σ _ N Ts M T ι hsig hTs
  exact AnalyticManifold.isCountableChartUnion_of_cover ι hsig.1 hsig.2.1 hsig.2.2.1 hTs

/-- [Kol07, Warning 38]: a countable disjoint union of countable chart unions is a
countable chart union. -/
theorem _root_.AnalyticManifold.isCountableChartUnion_sigma {σ : Type u}
    [Countable σ]
    (N : σ → AnalyticManifold.{u} 𝕜 E) (hN : ∀ i, (N i).IsCountableChartUnion) :
    (sigmaManifold N).IsCountableChartUnion :=
  AnalyticManifold.isCountableChartUnion_of_cover (sigmaMk N) (isAnalyticOpenEmbedding_sigmaMk N)
    (pairwise_disjoint_range_sigmaMk N) (iUnion_range_sigmaMk N) hN

end Manifold

end
