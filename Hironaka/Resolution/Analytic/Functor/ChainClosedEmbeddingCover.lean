/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.ShrunkEmbeddingCover
public import Hironaka.Manifold.Submanifold.Charts
public import Mathlib.Analysis.InnerProductSpace.Basic
import Hironaka.Manifold.Exhaustion
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaTriple
import Hironaka.Manifold.FiniteSuccession.Restrict.RestrictBundle
import Hironaka.Manifold.Submanifold.DisjointUnion
import Hironaka.Resolution.Analytic.Submanifold.FlagIdeal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The chaining of the closed-embedding commutation, II: the flag cover

[Kol07, 108] reduces the commutation with closed embeddings to the hypersurface case along a
chain of smooth subvarieties `Y = Y₀ ⊂ Y₁ ⊂ ⋯ ⊂ Y_c = X`, each a hypersurface in the next, the
identity being a local question on `X`. On analytic manifolds the per-open identity of the
predicate `CommutesWithClosedEmbeddingsOfEmptyDivisorFam` is read on a relatively compact open
`U`, so only the compact `closure U` has to be covered (compare [BM97, Theorem 1.6] and the remark
following it on relatively compact opens), and a closed submanifold `S` of codimension `s + 1`
is, on the source of each of its adapted charts, the bottom of a flag `S ∩ W ⊂ Y ⊂ W` with `Y`
the zero set of the first `s` normal coordinates (`IsAdaptedChart.exists_flag`). This module
builds the cover:

* `FlagPiece hS W`: an open `W` with a closed submanifold `Y` of the open submanifold `W` of
  codimension `s` containing the trace of `S`, of which the trace is a hypersurface;
  `exists_flagPiece_of_adaptedChart` (the source of an adapted chart, through the chart
  transported to the open submanifold, where its source is the whole manifold) and
  `FlagPiece.compl` (the complement `M ∖ S` with `Y = ∅`);
* `FlagCover hS U`: finitely many pieces `Wᵢ` with shrunk opens `Vᵢ ⋐ Wᵢ` (compact closures
  inside the pieces) covering `closure U`; `exists_flagCover` by compactness, as
  `exists_finite_shrunk_mcCover` (`Hironaka.Resolution.Analytic.OrderReduction.GlobalizeFamCover`);
* the coproduct `FlagCover.sigma = ⨆ᵢ Wᵢ` of the pieces with the cover map `desc`, the open
  `opens = ⨆ᵢ (Vᵢ ∩ U)` with compact closure and image `U`, and the restricted cover map
  `coverMap : sigma.restrict opens → M.restrict U`, a surjective local analytic isomorphism — all
  read off the shrunk embedding cover `FlagCover.toCover` (`ShrunkEmbeddingCover`, shared with
  `ShrunkMCCover`);
* the flag on the coproduct: `flag = ⋃ᵢ sigmaMk i '' Yᵢ` is a closed submanifold of codimension
  `s` (`IsClosedSubmanifold.iUnion_image`) containing the preimage of `S`, of which that preimage
  is a hypersurface (`preimage_val_of_subset` at codimension `s + 1 - s = 1`).

The chaining lemma (`Hironaka.Resolution.Analytic.Functor.ChainClosedEmbeddingChain`) pulls the
two sides of the identity on `U` back along the cover map, where the flag exists, and descends by
the injectivity of the pull-back along a surjective local isomorphism
(`BlowUpSequence.pullback_injective_of_surjective`).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Function
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-! ### Flag pieces -/

/-- A **flag piece** for `S` (codimension
`s + 1`) on the open `W` — a closed submanifold `Y` of the open submanifold `W` of codimension `s`
containing the trace of `S`, of which the trace is a hypersurface. -/
structure FlagPiece {S : Set M} {s : ℕ} (hS : IsClosedSubmanifold ψ S (s + 1)) (W : Opens M) where
  /-- The middle member of the flag on the piece. -/
  Y : Set (M.restrict W)
  /-- `Y` is a closed submanifold of codimension `s`. -/
  hY : IsClosedSubmanifold ψ Y s
  /-- The trace of `S` lies in `Y`. -/
  subset : (⇑(M.inclusion W) ⁻¹' S) ⊆ Y
  /-- The trace of `S` is a hypersurface of the bundled `Y`. -/
  hSY : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
    (⇑hY.inclusionMap ⁻¹' (⇑(M.inclusion W) ⁻¹' S)) 1

/-- The trace of `S` on a piece is a closed submanifold of codimension `s + 1` (`restrictOpen`). -/
theorem FlagPiece.isClosedSubmanifold_trace {S : Set M} {s : ℕ}
    (hS : IsClosedSubmanifold ψ S (s + 1)) (W : Opens M) :
    IsClosedSubmanifold ψ (⇑(M.inclusion W) ⁻¹' S : Set (M.restrict W)) (s + 1) :=
  hS.restrictOpen W

/-- The flag piece on the source of an adapted chart of `S`: the chart transported to the open
submanifold `φ.source` (`transportChart` along the inverse of the inclusion, as
`IsClosedSubmanifoldOn.restrict`) is an adapted chart of the trace whose source is the whole
manifold, and `IsAdaptedChart.exists_flag` gives the flag. -/
theorem exists_flagPiece_of_adaptedChart {S : Set M} {s : ℕ} (hS : IsClosedSubmanifold ψ S (s + 1))
    {φ : OpenPartialHomeomorph M E} {σ : Fin (s + 1) ↪ Fin n} (hφ : IsAdaptedChart ψ S φ σ) {a : M}
    (ha : a ∈ φ.source) : Nonempty (FlagPiece hS ⟨φ.source, φ.open_source⟩) := by
  set W : Opens M := ⟨φ.source, φ.open_source⟩
  have hS' : IsClosedSubmanifold ψ (⇑(M.inclusion W) ⁻¹' S) (s + 1) := hS.restrictOpen W
  have hφ' : IsAdaptedChart ψ (⇑(M.inclusion W) ⁻¹' S)
      (transportChart (inclusionPartialDiffeomorph M W ⟨a, ha⟩).symm φ) σ :=
    isAdaptedChart_transportChart _ (image_inclusionInv_eq W ⟨a, ha⟩ S) hφ
  have hsrc : (transportChart (inclusionPartialDiffeomorph M W ⟨a, ha⟩).symm φ).source = univ := by
    rw [transportChart_source]
    exact Set.eq_univ_iff_forall.mpr fun q => ⟨Set.mem_univ _, q.2⟩
  obtain ⟨Y, hY, hsub, hSY⟩ := IsAdaptedChart.exists_flag hS' hφ' hsrc
  exact ⟨⟨Y, hY, hsub, hSY⟩⟩

/-- The flag piece on the complement of
`S` — the empty middle member (`isClosedSubmanifold_empty'`). -/
def FlagPiece.compl {S : Set M} {s : ℕ} (hS : IsClosedSubmanifold ψ S (s + 1)) :
    FlagPiece hS ⟨Sᶜ, hS.isClosed.isOpen_compl⟩ where
  Y := ∅
  hY := isClosedSubmanifold_empty' ψ s
  subset := fun q hq => (q.2 hq).elim
  hSY := by
    have h : (⇑(isClosedSubmanifold_empty' ψ s
        (M := M.restrict ⟨Sᶜ, hS.isClosed.isOpen_compl⟩)).inclusionMap ⁻¹'
          (⇑(M.inclusion ⟨Sᶜ, hS.isClosed.isOpen_compl⟩) ⁻¹' S)) = ∅ :=
      Set.eq_empty_of_forall_notMem fun q _ => q.2
    rw [h]
    exact isClosedSubmanifold_empty' _ 1

/-! ### The finite shrunk flag cover of a relatively compact open -/

/-- A **flag cover** of the relatively compact open `U` — finitely
many flag pieces `Wᵢ` with shrunk opens `Vᵢ` (compact closures inside the `Wᵢ`) covering
`closure U`. -/
structure FlagCover {S : Set M} {s : ℕ} (hS : IsClosedSubmanifold ψ S (s + 1)) (U : Opens M) where
  /-- The (finite) index type of the pieces. -/
  ι : Type u
  [finite : Finite ι]
  /-- The pieces. -/
  W : ι → Opens M
  /-- The flag on each piece. -/
  piece : ∀ i, FlagPiece hS (W i)
  /-- The shrunk opens. -/
  V : ι → Opens M
  /-- The shrunk opens have compact closures. -/
  hVc : ∀ i, IsCompact (closure (V i : Set M))
  /-- The closures of the shrunk opens lie in the pieces. -/
  hVW : ∀ i, closure (V i : Set M) ⊆ W i
  /-- The shrunk opens cover `closure U`. -/
  hcov : closure (U : Set M) ⊆ ⋃ i, (V i : Set M)

attribute [instance] FlagCover.finite

/-- Every relatively compact
open has a flag cover — at a point of `S` the source of an adapted chart
(`exists_flagPiece_of_adaptedChart`), off `S` the complement (`FlagPiece.compl`); a compact
neighbourhood inside the piece (`exists_compact_subset`, the manifold being locally compact);
finitely many by the compactness of `closure U`. -/
theorem exists_flagCover {S : Set M} {s : ℕ} (hS : IsClosedSubmanifold ψ S (s + 1)) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) : Nonempty (FlagCover hS U) := by
  have := finiteDimensional_of_chartIso ψ
  have : LocallyCompactSpace M := locallyCompactSpace_of_finiteDimensional 𝕜 E M
  have hpiece : ∀ x : M, ∃ W : Opens M, x ∈ W ∧ Nonempty (FlagPiece hS W) := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨φ, σ, hxφ, hφ⟩ := hS.exists_adaptedChart x hx
      exact ⟨⟨φ.source, φ.open_source⟩, hxφ, exists_flagPiece_of_adaptedChart hS hφ hxφ⟩
    · exact ⟨⟨Sᶜ, hS.isClosed.isOpen_compl⟩, hx, ⟨FlagPiece.compl hS⟩⟩
  choose W hxW hP using hpiece
  have hcpt : ∀ x : M, ∃ K : Set M, IsCompact K ∧ x ∈ interior K ∧ K ⊆ W x :=
    fun x => exists_compact_subset (W x).isOpen (hxW x)
  choose K hK hxK hKW using hcpt
  obtain ⟨t, -, hcov⟩ := hU.elim_nhds_subcover (fun x => interior (K x))
    fun x _ => isOpen_interior.mem_nhds (hxK x)
  refine ⟨⟨t, fun i => W i.1, fun i => Classical.choice (hP i.1),
    fun i => ⟨interior (K i.1), isOpen_interior⟩, fun i => ?_, fun i => ?_, ?_⟩⟩
  · exact (hK i.1).of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset (hK i.1).isClosed)
  · exact (closure_minimal interior_subset (hK i.1).isClosed).trans (hKW i.1)
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hcov hy)
    exact Set.mem_iUnion.mpr ⟨⟨x, hxt⟩, hyx⟩

namespace FlagCover

open _root_.Manifold

variable {S : Set M} {s : ℕ} {hS : IsClosedSubmanifold ψ S (s + 1)} {U : Opens M}
  (C : FlagCover hS U)

/-! ### The coproduct of the pieces and its cover map -/

/-- The pieces as open submanifolds. -/
abbrev N (i : C.ι) : AnalyticManifold.{u} 𝕜 E := M.restrict (C.W i)

/-- The inclusions of the pieces. -/
abbrev incl (i : C.ι) : AnalyticMap (C.N i) M := M.inclusion (C.W i)

theorem isAnalyticOpenEmbedding_incl (i : C.ι) : IsAnalyticOpenEmbedding (C.incl i) :=
  isAnalyticOpenEmbedding_inclusion M (C.W i)

theorem range_incl (i : C.ι) : Set.range (C.incl i) = (C.W i : Set M) :=
  Subtype.range_val

/-- The flag cover as a shrunk embedding cover (`ShrunkEmbeddingCover`): the pieces embedded by
their inclusions, the shrunk opens inside their ranges. The coproduct, the open `⨆ᵢ (Vᵢ ∩ U)` and
the cover map below are those of this cover. -/
abbrev toCover : ShrunkEmbeddingCover M U :=
  ⟨C.ι, C.N, C.incl, C.isAnalyticOpenEmbedding_incl, C.V, C.hVc,
    fun i => (C.hVW i).trans (C.range_incl i).symm.subset, C.hcov⟩

/-- The coproduct `⨆ᵢ Wᵢ` of the pieces. -/
abbrev sigma : AnalyticManifold.{u} 𝕜 E := C.toCover.sigma

/-- The cover map `⨆ᵢ Wᵢ → M`. -/
abbrev desc : AnalyticMap C.sigma M := C.toCover.desc

theorem isLocalDiffeomorph_desc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω C.desc :=
  C.toCover.isLocalDiffeomorph_desc

theorem desc_apply (p : C.sigma) : C.desc p = p.2.1 := rfl

/-- The open `⨆ᵢ (Vᵢ ∩ U)` of the coproduct. -/
abbrev opens : Opens C.sigma := C.toCover.opens

theorem mem_opens (p : C.sigma) :
    p ∈ (C.opens : Set C.sigma) ↔ C.incl p.1 p.2 ∈ (C.V p.1 : Set M) ∩ (U : Set M) := Iff.rfl

/-- The closed set `⨆ᵢ ιᵢ⁻¹(closure Vᵢ)` containing the closure of `opens`. -/
abbrev closedHull : Set C.sigma := C.toCover.closedHull

theorem isClosed_closedHull : IsClosed C.closedHull := C.toCover.isClosed_closedHull

theorem closedHull_eq_iUnion :
    C.closedHull = ⋃ i, (sigmaMk C.N i) '' ((C.incl i) ⁻¹' closure (C.V i : Set M)) :=
  C.toCover.closedHull_eq_iUnion

theorem isCompact_closedHull : IsCompact C.closedHull := C.toCover.isCompact_closedHull

theorem closure_opens_subset : closure (C.opens : Set C.sigma) ⊆ C.closedHull :=
  C.toCover.closure_opens_subset

/-- The open `⨆ᵢ (Vᵢ ∩ U)` has compact closure. -/
theorem isCompact_closure_opens : IsCompact (closure (C.opens : Set C.sigma)) :=
  C.toCover.isCompact_closure_opens

theorem image_opens_subset : ⇑C.desc '' (C.opens : Set C.sigma) ⊆ (U : Set M) :=
  C.toCover.image_opens_subset

/-- The cover map sends `⨆ᵢ (Vᵢ ∩ U)` onto `U` (the `Vᵢ` cover `closure U ⊇ U`). -/
theorem image_opens_eq : ⇑C.desc '' (C.opens : Set C.sigma) = (U : Set M) :=
  C.toCover.image_opens_eq

/-- The cover map `⨆ᵢ (Vᵢ ∩ U) → U` (Kollár's `g : X^* → X` over `U`). -/
abbrev coverMap : AnalyticMap (C.sigma.restrict C.opens) (M.restrict U) := C.toCover.coverMap

theorem isLocalDiffeomorph_coverMap : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω C.coverMap :=
  C.toCover.isLocalDiffeomorph_coverMap

theorem surjective_coverMap : Function.Surjective C.coverMap := C.toCover.surjective_coverMap

/-! ### The flag on the coproduct -/

theorem pairwise_disjoint_range_sigmaMk :
    Pairwise fun i j => Disjoint (Set.range (sigmaMk C.N i)) (Set.range (sigmaMk C.N j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  exact hij (congrArg Sigma.fst hy).symm

theorem iUnion_range_sigmaMk : (⋃ i, Set.range (sigmaMk C.N i)) = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun p => Set.mem_iUnion.mpr ⟨p.1, p.2, rfl⟩

/-- The preimage of `S` in the coproduct, a closed submanifold of codimension `s + 1`
(`preimage_of_isLocalDiffeomorph`). -/
theorem isClosedSubmanifold_preimage : IsClosedSubmanifold ψ (⇑C.desc ⁻¹' S) (s + 1) :=
  hS.preimage_of_isLocalDiffeomorph C.isLocalDiffeomorph_desc

/-- The flag `⋃ᵢ sigmaMk i '' Yᵢ` on the coproduct (`Y_N`). -/
def flag : Set C.sigma := ⋃ i, ⇑(sigmaMk C.N i) '' (C.piece i).Y

/-- The flag is a closed submanifold of codimension `s` (`IsClosedSubmanifold.iUnion_image`). -/
theorem isClosedSubmanifold_flag : IsClosedSubmanifold ψ C.flag s :=
  IsClosedSubmanifold.iUnion_image (sigmaMk C.N) (fun i => isAnalyticOpenEmbedding_sigmaMk C.N i)
    C.pairwise_disjoint_range_sigmaMk C.iUnion_range_sigmaMk _ fun i => (C.piece i).hY

theorem preimage_subset_flag : ⇑C.desc ⁻¹' S ⊆ C.flag := by
  intro p hp
  exact Set.mem_iUnion.mpr ⟨p.1, ⟨p.2, (C.piece p.1).subset hp, rfl⟩⟩

/-- The preimage of `S` is a hypersurface of the bundled flag (`preimage_val_of_subset`
at codimension `s + 1 - s = 1`). -/
theorem isClosedSubmanifold_preimage_flag :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (⇑C.isClosedSubmanifold_flag.inclusionMap ⁻¹' (⇑C.desc ⁻¹' S)) 1 := by
  have h := C.isClosedSubmanifold_flag.preimage_val_of_subset C.isClosedSubmanifold_preimage
    C.preimage_subset_flag
  rwa [Nat.add_sub_cancel_left] at h

end FlagCover

end Hironaka.Manifold

end
