/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.Family
public import Hironaka.Manifold.FiniteSuccession.Functor.CoverData
import Hironaka.Manifold.FiniteSuccession.Functor.LocalTriples
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Finite shrunk covers of a relatively compact open by open embeddings

The per-open identities of the family functors are read on a relatively compact open `U` of a
manifold `M`, so a local question on `M` reduces to finitely many pieces covering the compact
`closure U`. Two such reductions share their cover: Step 3 of the proof of [Kol07, Theorem 103]
(the neighbourhoods with maximal contact, `ShrunkMCCover`) and the chaining of the commutation with
closed embeddings [Kol07, 108] (the sources of adapted charts, `FlagCover`). This module holds the
data and the lemmas common to both:

* `ShrunkEmbeddingCover M U`: finitely many analytic open embeddings `ιᵢ : Nᵢ → M` with opens
  `Vᵢ ⋐ range ιᵢ` (compact closures inside the ranges) covering `closure U`;
* the coproduct `sigma = ⨆ᵢ Nᵢ` with the coproduct map `desc = ⨆ᵢ ιᵢ` (Kollár's `g : X^* → X`), a
  local analytic isomorphism and a coproduct of open embeddings;
* the open `opens = ⨆ᵢ ιᵢ⁻¹(Vᵢ ∩ U)` of the coproduct, with compact closure
  (`isCompact_closure_opens`, through the closed compact `closedHull = ⨆ᵢ ιᵢ⁻¹(closure Vᵢ)`) and
  image `U` (`image_opens_eq`);
* the restricted cover map `coverMap : sigma.restrict opens → M.restrict U`, a surjective local
  analytic isomorphism and a coproduct of open embeddings.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Function
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A **shrunk embedding cover** of the relatively compact open `U` of `M` — finitely many analytic
open embeddings `ιᵢ : Nᵢ → M` with opens `Vᵢ` of `M` with compact closures inside the ranges of the
`ιᵢ`, covering `closure U`. -/
structure ShrunkEmbeddingCover (M : AnalyticManifold.{u} 𝕜 E) (U : Opens M) where
  /-- The (finite) index type of the pieces. -/
  ι : Type u
  [finite : Finite ι]
  /-- The manifolds of the pieces. -/
  N : ι → AnalyticManifold.{u} 𝕜 E
  /-- The open embeddings of the pieces. -/
  incl : ∀ i, AnalyticMap (N i) M
  /-- The maps `ιᵢ` are analytic open embeddings. -/
  isAnalyticOpenEmbedding_incl : ∀ i, IsAnalyticOpenEmbedding (incl i)
  /-- The shrunk opens. -/
  V : ι → Opens M
  /-- The shrunk opens have compact closures. -/
  hVc : ∀ i, IsCompact (closure (V i : Set M))
  /-- The closures of the shrunk opens lie in the ranges of the embeddings. -/
  hVr : ∀ i, closure (V i : Set M) ⊆ range (incl i)
  /-- The shrunk opens cover `closure U`. -/
  hcov : closure (U : Set M) ⊆ ⋃ i, (V i : Set M)

attribute [instance] ShrunkEmbeddingCover.finite

namespace ShrunkEmbeddingCover

variable {M : AnalyticManifold.{u} 𝕜 E} {U : Opens M} (C : ShrunkEmbeddingCover M U)

/-! ### The coproduct of the pieces and its cover map -/

/-- The coproduct `⨆ᵢ Nᵢ` of the pieces (Kollár's `X^*`). -/
def sigma : AnalyticManifold.{u} 𝕜 E := sigmaManifold C.N

/-- The coproduct map `⨆ᵢ ιᵢ : ⨆ᵢ Nᵢ → M` (Kollár's `g : X^* → X`). -/
abbrev desc : AnalyticMap C.sigma M := sigmaDescMap C.incl

theorem desc_apply (p : C.sigma) : C.desc p = C.incl p.1 p.2 := rfl

/-- The coproduct map is a local analytic isomorphism. -/
theorem isLocalDiffeomorph_desc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω C.desc :=
  isLocalDiffeomorph_sigmaDescMap C.incl fun i => (C.isAnalyticOpenEmbedding_incl i).1

/-- The coproduct map is a coproduct of open embeddings. -/
theorem isCoprodOfOpenEmbeddings_desc : IsCoprodOfOpenEmbeddings C.desc :=
  isCoprodOfOpenEmbeddings_sigmaDescMap C.incl C.isAnalyticOpenEmbedding_incl

/-- The open `⨆ᵢ ιᵢ⁻¹(Vᵢ ∩ U)` of the coproduct. -/
def opens : Opens C.sigma :=
  ⟨{p : Σ i, (C.N i : Type u) | C.incl p.1 p.2 ∈ (C.V p.1 : Set M) ∩ (U : Set M)}, by
    refine isOpen_sigma_iff.mpr fun i => ?_
    exact ((C.V i).isOpen.inter U.isOpen).preimage (C.incl i).contMDiff.continuous⟩

theorem mem_opens (p : C.sigma) :
    p ∈ (C.opens : Set C.sigma) ↔ C.incl p.1 p.2 ∈ (C.V p.1 : Set M) ∩ (U : Set M) := Iff.rfl

/-- The closed set `⨆ᵢ ιᵢ⁻¹(closure Vᵢ)` of the coproduct, which contains the closure of
`opens`. -/
def closedHull : Set C.sigma :=
  {p : Σ i, (C.N i : Type u) | C.incl p.1 p.2 ∈ closure (C.V p.1 : Set M)}

theorem isClosed_closedHull : IsClosed C.closedHull :=
  isClosed_sigma_iff.mpr fun i =>
    (isClosed_closure.preimage (C.incl i).contMDiff.continuous :
      IsClosed ((C.incl i) ⁻¹' closure (C.V i : Set M)))

theorem closedHull_eq_iUnion :
    C.closedHull = ⋃ i, (sigmaMk C.N i) '' ((C.incl i) ⁻¹' closure (C.V i : Set M)) := by
  ext p
  constructor
  · intro h
    exact mem_iUnion.mpr ⟨p.1, ⟨p.2, h, rfl⟩⟩
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    obtain ⟨w, hw, rfl⟩ := hj
    exact hw

/-- `⨆ᵢ ιᵢ⁻¹(closure Vᵢ)` is compact: finitely many pieces, each the preimage under an open
embedding of a compact set inside its range. -/
theorem isCompact_closedHull : IsCompact C.closedHull := by
  rw [C.closedHull_eq_iUnion]
  refine isCompact_iUnion fun i =>
    IsCompact.image ?_ (sigmaMk C.N i).contMDiff.continuous
  exact ((C.isAnalyticOpenEmbedding_incl i).isOpenEmbedding.isInducing.isCompact_preimage_iff
    (C.hVr i)).mpr (C.hVc i)

theorem closure_opens_subset : closure (C.opens : Set C.sigma) ⊆ C.closedHull :=
  closure_minimal (fun p hp => subset_closure ((C.mem_opens p).mp hp).1) C.isClosed_closedHull

/-- The open `⨆ᵢ ιᵢ⁻¹(Vᵢ ∩ U)` has compact closure (`closure (Vᵢ ⊓ U) ⊆ closure Vᵢ`, finitely
many compact pieces). -/
theorem isCompact_closure_opens : IsCompact (closure (C.opens : Set C.sigma)) :=
  C.isCompact_closedHull.of_isClosed_subset isClosed_closure C.closure_opens_subset

/-- The coproduct map sends `⨆ᵢ ιᵢ⁻¹(Vᵢ ∩ U)` into `U`. -/
theorem image_opens_subset : ⇑C.desc '' (C.opens : Set C.sigma) ⊆ (U : Set M) := by
  rintro _ ⟨p, hp, rfl⟩
  exact ((C.mem_opens p).mp hp).2

/-- The coproduct map sends `⨆ᵢ ιᵢ⁻¹(Vᵢ ∩ U)` onto `U`: the `Vᵢ` cover `closure U ⊇ U` and each
lies in the range of `ιᵢ`. -/
theorem image_opens_eq : ⇑C.desc '' (C.opens : Set C.sigma) = (U : Set M) := by
  refine subset_antisymm C.image_opens_subset fun y hy => ?_
  obtain ⟨i, hyV⟩ := mem_iUnion.mp (C.hcov (subset_closure hy))
  obtain ⟨z, hz⟩ := C.hVr i (subset_closure hyV)
  refine ⟨⟨i, z⟩, ?_, hz⟩
  change C.incl i z ∈ (C.V i : Set M) ∩ (U : Set M)
  exact ⟨hz.symm ▸ hyV, hz.symm ▸ hy⟩

/-- The cover map `⨆ᵢ ιᵢ⁻¹(Vᵢ ∩ U) → U`, the restriction of the coproduct map (Kollár's
`g : X^* → X` over `U`). -/
abbrev coverMap : AnalyticMap (C.sigma.restrict C.opens) (M.restrict U) :=
  AnalyticMap.restrictMap C.desc C.opens U C.image_opens_subset

/-- The cover map is a local analytic isomorphism. -/
theorem isLocalDiffeomorph_coverMap : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω C.coverMap :=
  AnalyticMap.isLocalDiffeomorph_restrictMap C.isLocalDiffeomorph_desc C.opens U
    C.image_opens_subset

/-- The cover map is surjective onto `U`. -/
theorem surjective_coverMap : Function.Surjective C.coverMap :=
  AnalyticMap.surjective_restrictMap C.image_opens_eq

/-- The cover map is a coproduct of open embeddings. -/
theorem isCoprodOfOpenEmbeddings_coverMap : IsCoprodOfOpenEmbeddings C.coverMap :=
  AnalyticMap.isCoprodOfOpenEmbeddings_restrictMap C.isCoprodOfOpenEmbeddings_desc C.opens U
    C.image_opens_subset

end ShrunkEmbeddingCover

end Hironaka.Manifold

end
