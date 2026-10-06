/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductExceptionalFamily
public import Hironaka.Manifold.FiniteSuccession.Functor.CoverData
public import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionOn
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.Kol07Thm45.ExceptionalFamilyGlue
import Hironaka.Resolution.Analytic.Kol07Thm45.RunFamilyRestrict
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The common datum of two adjacent levels and its summand inclusions

The labels of two adjacent levels `n`, `n + 1` of the exhaustion are compared through ONE run —
the functor's value on the coproduct of ALL the pieces of both levels, padded to a common
dimension `n₁ + n₂` (`PieceEmbedding.padLeft`, `padRight`: the two embeddings `(i₁, 0)`, `(0, i₂)`
into `𝔸ⁿ¹⁺ⁿ²` of [Kol07, Lemma 39]), over the union of the reading opens — Kollár's single run on
the disjoint union of a cover [Kol07, Proposition 37, proof]. This module builds that datum and
its two summand inclusions:

* `padLeftData D m`, `padRightData D m` — the same pieces, every embedding padded (dimension
  `D.n + m`, `m + D.n`); `sumData D D' h` — the pieces of both data, indexed by `D.ι ⊕ D'.ι`, over
  `U ∪ U'` (the embeddings of `D'` transported along `h : D.n = D'.n`);
  `sumPadData D₁ D₂` — THE COMMON DATUM (a cast-free literal, equal field by field to
  `sumData (D₁.padLeftData D₂.n) (D₂.padRightData D₁.n) rfl`: `sumPadData_eq_sumData`), whose
  single run (`sigmaRun`) is the common run and whose label set (`sigmaIndex`) is the common
  label set;
* `sumInlAmbient D D' h : D.sigmaAmbient → (sumData D D' h).sigmaAmbient` — the inclusion of the
  first summand's coproduct ambient, the descent (`sigmaDescMap`) of the summand inclusions
  `sigmaMk (Sum.inl i)`; it is an analytic open embedding (`isAnalyticOpenEmbedding_sumInlAmbient`)
  along which the first datum's coproduct triple is the pull-back of the sum's
  (`isPullbackOf_sigmaTriple_sum`, by `IdealSheaf.ext_of_comap_sigmaMk` summand by summand); at the
  common datum the two summand inclusions `sumPadInlAmbient D₁ D₂`, `sumInrAmbient D₁ D₂` likewise;
* the reading opens of the common run from those of the two padded data (`sumPadOpens`), with
  the first datum's ambient image carried into the sum's (`image_sumInlAmbient_ambImage_subset`);
* **the label maps** — `exists_orderEmbedding_comap_sumInlResIn_sigmaMembers` and its `inr`
  counterpart: the GENERAL restriction identity of `RunFamilyRestrict.lean` ([Kol07, 34.1]) at
  the summand inclusion, read on the datum's `sigmaMembers`: an order embedding
  of the padded level's label set into the common label set, the common run's member of label
  `lab k` pulling back along the open immersion `sumInlResIn` of the local resolutions to the
  level's member `k`, the members off the range to `⊤`.

The padding identity — the padded level's labels and members against the level's own
(`exists_isIso_localResolution_padAlong` at the coproduct slice) — is the remaining link of the
comparison of the two levels; it is `CoproductPadIdentity.lean`. `hbed` is the only hypothesis.
Not in the sources beyond Kollár's single run; bookkeeping.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.LocalEmbeddingData

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜}

/-- **The left-padded datum** ([Kol07, Lemma 39]) — the same pieces, each embedding padded by `m`
trailing coordinates (`PieceEmbedding.padLeft`); dimension `D.n + m`. -/
abbrev padLeftData {U : Set X} (D : LocalEmbeddingData 𝕜 X U) (m : ℕ) :
    LocalEmbeddingData 𝕜 X U where
  n := D.n + m
  ι := D.ι
  finite := D.finite
  piece := D.piece
  isOpen_piece := D.isOpen_piece
  inner := D.inner
  isOpen_inner := D.isOpen_inner
  isCompact_closure_inner := D.isCompact_closure_inner
  closure_inner_subset := D.closure_inner_subset
  subset_iUnion_inner := D.subset_iUnion_inner
  embedding := fun i => (D.embedding i).padLeft m

/-- **The right-padded datum** — each embedding padded by `m` leading coordinates
(`PieceEmbedding.padRight`); dimension `m + D.n`. -/
abbrev padRightData {U : Set X} (D : LocalEmbeddingData 𝕜 X U) (m : ℕ) :
    LocalEmbeddingData 𝕜 X U where
  n := m + D.n
  ι := D.ι
  finite := D.finite
  piece := D.piece
  isOpen_piece := D.isOpen_piece
  inner := D.inner
  isOpen_inner := D.isOpen_inner
  isCompact_closure_inner := D.isCompact_closure_inner
  closure_inner_subset := D.closure_inner_subset
  subset_iUnion_inner := D.subset_iUnion_inner
  embedding := fun i => (D.embedding i).padRight m

/-- **The sum of two data of the same dimension** over the union of their opens
([Kol07, Proposition 37, proof]) — the pieces of both, indexed by the sum type, the second datum's
embeddings transported along `h`. -/
abbrev sumData {U U' : Set X} (D : LocalEmbeddingData 𝕜 X U) (D' : LocalEmbeddingData 𝕜 X U')
    (h : D.n = D'.n) : LocalEmbeddingData 𝕜 X (U ∪ U') where
  n := D.n
  ι := D.ι ⊕ D'.ι
  finite := inferInstance
  piece := Sum.elim D.piece D'.piece
  isOpen_piece := fun k => by cases k <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
    first | exact D.isOpen_piece _ | exact D'.isOpen_piece _
  inner := Sum.elim D.inner D'.inner
  isOpen_inner := fun k => by cases k <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
    first | exact D.isOpen_inner _ | exact D'.isOpen_inner _
  isCompact_closure_inner := fun k => by cases k <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
    first | exact D.isCompact_closure_inner _ | exact D'.isCompact_closure_inner _
  closure_inner_subset := fun k => by cases k <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
    first | exact D.closure_inner_subset _ | exact D'.closure_inner_subset _
  subset_iUnion_inner := by
    rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (D.subset_iUnion_inner hx)
      exact Set.mem_iUnion.mpr ⟨Sum.inl i, hi⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (D'.subset_iUnion_inner hx)
      exact Set.mem_iUnion.mpr ⟨Sum.inr j, hj⟩
  embedding := fun k => match k with
    | Sum.inl i => D.embedding i
    | Sum.inr j => h ▸ D'.embedding j

/-- **The common padded datum of two adjacent levels** — `D₁` padded on the right by `D₂.n`
coordinates and `D₂` padded on the left by `D₁.n`, both of dimension `D₁.n + D₂.n`, summed; its
single run is the common run. Written as a literal (not through `sumData … rfl`): the two padded
dimensions are the same term `D₁.n + D₂.n`, so no transport of the second summand's embeddings is
needed — `sumData`'s `h ▸` on the `inr` summand made every identification of the sum's `inr`
pieces with the padded pieces a `whnf` timeout at the level of morphisms of local resolutions (the
comparison of adjacent levels); `sumPadData_eq_sumData` records that the literal is
`sumData … rfl` — field by field by `rfl`, the `match` auxiliaries by `cases`. -/
abbrev sumPadData {U₁ U₂ : Set X} (D₁ : LocalEmbeddingData 𝕜 X U₁)
    (D₂ : LocalEmbeddingData 𝕜 X U₂) : LocalEmbeddingData 𝕜 X (U₁ ∪ U₂) where
  n := D₁.n + D₂.n
  ι := D₁.ι ⊕ D₂.ι
  finite := inferInstance
  piece := Sum.elim D₁.piece D₂.piece
  isOpen_piece := fun k => by cases k <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
    first | exact D₁.isOpen_piece _ | exact D₂.isOpen_piece _
  inner := Sum.elim D₁.inner D₂.inner
  isOpen_inner := fun k => by cases k <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
    first | exact D₁.isOpen_inner _ | exact D₂.isOpen_inner _
  isCompact_closure_inner := fun k => by cases k <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
    first | exact D₁.isCompact_closure_inner _ | exact D₂.isCompact_closure_inner _
  closure_inner_subset := fun k => by cases k <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
    first | exact D₁.closure_inner_subset _ | exact D₂.closure_inner_subset _
  subset_iUnion_inner := by
    rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (D₁.subset_iUnion_inner hx)
      exact Set.mem_iUnion.mpr ⟨Sum.inl i, hi⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (D₂.subset_iUnion_inner hx)
      exact Set.mem_iUnion.mpr ⟨Sum.inr j, hj⟩
  embedding := fun k => match k with
    | Sum.inl i => (D₁.embedding i).padLeft D₂.n
    | Sum.inr j => (D₂.embedding j).padRight D₁.n

/-- The literal IS the generic sum of the two padded data along `rfl` — every field agrees by
`rfl` (the transport along `rfl` reduces); the two `match` auxiliaries on the index are identified
summand by summand. -/
theorem sumPadData_eq_sumData {U₁ U₂ : Set X} (D₁ : LocalEmbeddingData 𝕜 X U₁)
    (D₂ : LocalEmbeddingData 𝕜 X U₂) :
    sumPadData D₁ D₂ = sumData (D₁.padLeftData D₂.n) (D₂.padRightData D₁.n) rfl := by
  refine congrArg (LocalEmbeddingData.mk (D₁.n + D₂.n) (D₁.ι ⊕ D₂.ι) (Sum.elim D₁.piece D₂.piece)
    _ (Sum.elim D₁.inner D₂.inner) _ _ _ _) ?_
  funext k
  cases k <;> rfl

section Sum

variable {U U' : Set X} (D : LocalEmbeddingData 𝕜 X U) (D' : LocalEmbeddingData 𝕜 X U')
  (h : D.n = D'.n)

/-- The inclusion of `D`'s coproduct ambient into the sum's — the descent of the summand
inclusions `sigmaMk (Sum.inl i)`. -/
def sumInlAmbient : AnalyticMap D.sigmaAmbient (sumData D D' h).sigmaAmbient :=
  sigmaDescMap fun i =>
    sigmaMk (fun k => pieceAmbient.{u} 𝕜 ((sumData D D' h).embedding k).G) (Sum.inl i)

/-- The inclusion after a summand inclusion of `D` is the summand inclusion of the sum. -/
theorem sumInlAmbient_comp_sigmaMk (i : D.ι) :
    (sumInlAmbient D D' h).comp (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) =
      sigmaMk (fun k => pieceAmbient.{u} 𝕜 ((sumData D D' h).embedding k).G) (Sum.inl i) :=
  sigmaDescMap_comp_sigmaMk _ i

/-- The inclusion is an analytic open embedding (the argument of
`isCoprodOfOpenEmbeddings_sigmaDescMap`) — a local isomorphism (each summand inclusion is one) and
injective (`Sigma.mk.inj_iff`, the summands' ranges disjoint). -/
theorem isAnalyticOpenEmbedding_sumInlAmbient : IsAnalyticOpenEmbedding (sumInlAmbient D D' h) := by
  refine ⟨isLocalDiffeomorph_sigmaDescMap _ fun i =>
    (isAnalyticOpenEmbedding_sigmaMk _ (Sum.inl i)).1, ?_⟩
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  have h' : (Sigma.mk (Sum.inl i) x :
      Σ k, (pieceAmbient.{u} 𝕜 ((sumData D D' h).embedding k).G : Type u)) =
    Sigma.mk (Sum.inl j) y := hxy
  obtain ⟨hij, hxy'⟩ := Sigma.mk.inj_iff.mp h'
  obtain rfl := Sum.inl.inj hij
  exact congrArg (Sigma.mk i) (eq_of_heq hxy')

/-- `D`'s coproduct triple is the pull-back of the sum's along the inclusion (the pull-back of
[Kol07, 34.1]) — summand by summand (`IdealSheaf.ext_of_comap_sigmaMk`,
`isPullbackOf_ambientTriple_sigmaTriple` on both sides); the divisors are empty. -/
theorem isPullbackOf_sigmaTriple_sum :
    D.sigmaTriple.IsPullbackOf (sumData D D' h).sigmaTriple (sumInlAmbient D D' h) := by
  refine ⟨IdealSheaf.ext_of_comap_sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) _ _
    fun i => ?_, ?_⟩
  · rw
      [← (D.isPullbackOf_ambientTriple_sigmaTriple i).1,
          AnalyticManifold.IdealSheaf.pullback_comp,
      sumInlAmbient_comp_sigmaMk]
    exact ((sumData D D' h).isPullbackOf_ambientTriple_sigmaTriple (Sum.inl i)).1
  · exact (HypersurfaceFamily.empty_comap _).symm

end Sum

section SumPad

variable {U₁ U₂ : Set X} (D₁ : LocalEmbeddingData 𝕜 X U₁) (D₂ : LocalEmbeddingData 𝕜 X U₂)

/-- The inclusion of the first padded level's coproduct ambient into the common datum's — the
descent of the summand inclusions `sigmaMk (Sum.inl i)` (`sumInlAmbient` at the literal
`sumPadData`). -/
def sumPadInlAmbient :
    AnalyticMap (D₁.padLeftData D₂.n).sigmaAmbient
        (sumPadData D₁ D₂).sigmaAmbient :=
  sigmaDescMap fun i =>
    sigmaMk (fun k => pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G) (Sum.inl i)

/-- The `inl` inclusion after a summand inclusion. -/
theorem sumPadInlAmbient_comp_sigmaMk (i : D₁.ι) :
    (sumPadInlAmbient D₁ D₂).comp
        (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G) i) =
      sigmaMk (fun k => pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G) (Sum.inl i) :=
  sigmaDescMap_comp_sigmaMk _ i

/-- The `inl` inclusion is an analytic open embedding. -/
theorem isAnalyticOpenEmbedding_sumPadInlAmbient :
    IsAnalyticOpenEmbedding (sumPadInlAmbient D₁ D₂) := by
  refine ⟨isLocalDiffeomorph_sigmaDescMap _ fun i =>
    (isAnalyticOpenEmbedding_sigmaMk _ (Sum.inl i)).1, ?_⟩
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  have h' : (Sigma.mk (Sum.inl i) x :
      Σ k, (pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G : Type u)) =
    Sigma.mk (Sum.inl j) y := hxy
  obtain ⟨hij, hxy'⟩ := Sigma.mk.inj_iff.mp h'
  obtain rfl := Sum.inl.inj hij
  exact congrArg (Sigma.mk i) (eq_of_heq hxy')

/-- The first padded level's coproduct triple is the pull-back of the common datum's along the
`inl` inclusion. -/
theorem isPullbackOf_sigmaTriple_sumPad_inl :
    (D₁.padLeftData D₂.n).sigmaTriple.IsPullbackOf (sumPadData D₁ D₂).sigmaTriple
      (sumPadInlAmbient D₁ D₂) := by
  refine ⟨IdealSheaf.ext_of_comap_sigmaMk
    (fun i => pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G) _ _ fun i => ?_, ?_⟩
  · rw [← ((D₁.padLeftData D₂.n).isPullbackOf_ambientTriple_sigmaTriple i).1,
      AnalyticManifold.IdealSheaf.pullback_comp, sumPadInlAmbient_comp_sigmaMk]
    exact ((sumPadData D₁ D₂).isPullbackOf_ambientTriple_sigmaTriple (Sum.inl i)).1
  · exact (HypersurfaceFamily.empty_comap _).symm

/-- The inclusion of the second padded level's coproduct ambient into the common datum's — the
descent of the summand inclusions `sigmaMk (Sum.inr j)`. -/
def sumInrAmbient :
    AnalyticMap (D₂.padRightData D₁.n).sigmaAmbient
        (sumPadData D₁ D₂).sigmaAmbient :=
  sigmaDescMap fun j =>
    sigmaMk (fun k => pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G) (Sum.inr j)

/-- The `inr` inclusion after a summand inclusion. -/
theorem sumInrAmbient_comp_sigmaMk (j : D₂.ι) :
    (sumInrAmbient D₁ D₂).comp
        (sigmaMk (fun j => pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G) j) =
      sigmaMk (fun k => pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G) (Sum.inr j) :=
  sigmaDescMap_comp_sigmaMk _ j

/-- The `inr` inclusion is an analytic open embedding. -/
theorem isAnalyticOpenEmbedding_sumInrAmbient :
    IsAnalyticOpenEmbedding (sumInrAmbient D₁ D₂) := by
  refine ⟨isLocalDiffeomorph_sigmaDescMap _ fun j =>
    (isAnalyticOpenEmbedding_sigmaMk _ (Sum.inr j)).1, ?_⟩
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  have h' : (Sigma.mk (Sum.inr i) x :
      Σ k, (pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G : Type u)) =
    Sigma.mk (Sum.inr j) y := hxy
  obtain ⟨hij, hxy'⟩ := Sigma.mk.inj_iff.mp h'
  obtain rfl := Sum.inr.inj hij
  exact congrArg (Sigma.mk i) (eq_of_heq hxy')

/-- The second padded level's coproduct triple is the pull-back of the common datum's along the
`inr` inclusion. -/
theorem isPullbackOf_sigmaTriple_sumPad_inr :
    (D₂.padRightData D₁.n).sigmaTriple.IsPullbackOf (sumPadData D₁ D₂).sigmaTriple
      (sumInrAmbient D₁ D₂) := by
  refine ⟨IdealSheaf.ext_of_comap_sigmaMk
    (fun j => pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G) _ _ fun j => ?_, ?_⟩
  · rw [← ((D₂.padRightData D₁.n).isPullbackOf_ambientTriple_sigmaTriple j).1,
      AnalyticManifold.IdealSheaf.pullback_comp, sumInrAmbient_comp_sigmaMk]
    exact ((sumPadData D₁ D₂).isPullbackOf_ambientTriple_sigmaTriple (Sum.inr j)).1
  · exact (HypersurfaceFamily.empty_comap _).symm

variable (W₁ : ∀ i : D₁.ι, Opens (pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G))
  (W₂ : ∀ j : D₂.ι, Opens (pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G))

/-- **The reading opens of the common run** from those of the two padded levels. -/
def sumPadOpens :
    ∀ k : (sumPadData D₁ D₂).ι, Opens (pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G)
  | Sum.inl i => W₁ i
  | Sum.inr j => W₂ j

/-- Relatively compact reading opens sum to relatively compact ones. -/
theorem isCompact_closure_sumPadOpens
    (hW₁ : ∀ i, IsCompact (closure (W₁ i : Set (pieceAmbient.{u} 𝕜
      ((D₁.padLeftData D₂.n).embedding i).G))))
    (hW₂ : ∀ j, IsCompact (closure (W₂ j : Set (pieceAmbient.{u} 𝕜
      ((D₂.padRightData D₁.n).embedding j).G)))) :
    ∀ k, IsCompact (closure (sumPadOpens D₁ D₂ W₁ W₂ k :
      Set (pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G)))
  | Sum.inl i => hW₁ i
  | Sum.inr j => hW₂ j

/-- The first padded level's ambient image lands in the common run's (`coe_sigmaCoordImage`: the
images are unions of summand images). -/
theorem image_sumInlAmbient_ambImage_subset :
    ⇑(sumPadInlAmbient D₁ D₂) ''
        ((D₁.padLeftData D₂.n).ambImage W₁ : Set (D₁.padLeftData D₂.n).sigmaAmbient) ⊆
      ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂) :
        Set (sumPadData D₁ D₂).sigmaAmbient) := by
  rintro _ ⟨q, hq, rfl⟩
  unfold ambImage at hq ⊢
  rw [coe_sigmaCoordImage] at hq ⊢
  obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hq
  exact Set.mem_iUnion.mpr ⟨Sum.inl i, x, hx, rfl⟩

/-- The second padded level's ambient image lands in the common run's. -/
theorem image_sumInrAmbient_ambImage_subset :
    ⇑(sumInrAmbient D₁ D₂) ''
        ((D₂.padRightData D₁.n).ambImage W₂ : Set (D₂.padRightData D₁.n).sigmaAmbient) ⊆
      ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂) :
        Set (sumPadData D₁ D₂).sigmaAmbient) := by
  rintro _ ⟨q, hq, rfl⟩
  unfold ambImage at hq ⊢
  rw [coe_sigmaCoordImage] at hq ⊢
  obtain ⟨j, x, hx, rfl⟩ := Set.mem_iUnion.mp hq
  exact Set.mem_iUnion.mpr ⟨Sum.inr j, x, hx, rfl⟩

variable (bed : BEDanFamStar.{u} 𝕜)
  (hW₁ : ∀ i, IsCompact (closure (W₁ i : Set (pieceAmbient.{u} 𝕜
    ((D₁.padLeftData D₂.n).embedding i).G))))
  (hW₂ : ∀ j, IsCompact (closure (W₂ j : Set (pieceAmbient.{u} 𝕜
    ((D₂.padRightData D₁.n).embedding j).G))))
  (hbed : bed.IsEmbeddedDesing)

/-- **The open immersion of the first padded level's local resolution into the common run's** —
`localResolutionHomOn` (`LocalResolutionOn.lean`) at the `inl` inclusion. -/
abbrev sumInlResIn :
    (bed.localResolutionOn (D₁.padLeftData D₂.n).sigmaTriple
          (D₁.padLeftData D₂.n).domBEDan_sigmaTriple ((D₁.padLeftData D₂.n).ambImage W₁)
          ((D₁.padLeftData D₂.n).isCompact_closure_ambImage W₁ hW₁) ⟶
          bed.localResolutionOn (sumPadData D₁ D₂).sigmaTriple
          (sumPadData D₁ D₂).domBEDan_sigmaTriple
          ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂))
          ((sumPadData D₁ D₂).isCompact_closure_ambImage _
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂))) :=
  bed.localResolutionHomOn (sumPadData D₁ D₂).sigmaTriple (sumPadData D₁ D₂).domBEDan_sigmaTriple
    ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂))
    ((sumPadData D₁ D₂).isCompact_closure_ambImage _
      (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂))
    (D₁.padLeftData D₂.n).sigmaTriple (D₁.padLeftData D₂.n).domBEDan_sigmaTriple
    (sumPadInlAmbient D₁ D₂) (isAnalyticOpenEmbedding_sumPadInlAmbient D₁ D₂)
    (isPullbackOf_sigmaTriple_sumPad_inl D₁ D₂)
    ((D₁.padLeftData D₂.n).ambImage W₁) ((D₁.padLeftData D₂.n).isCompact_closure_ambImage W₁ hW₁)
    (image_sumInlAmbient_ambImage_subset D₁ D₂ W₁ W₂) hbed

/-- **The open immersion of the second padded level's local resolution into the common run's** —
`localResolutionHomOn` at the `inr` inclusion. -/
abbrev sumInrResIn :
    (bed.localResolutionOn (D₂.padRightData D₁.n).sigmaTriple
          (D₂.padRightData D₁.n).domBEDan_sigmaTriple ((D₂.padRightData D₁.n).ambImage W₂)
          ((D₂.padRightData D₁.n).isCompact_closure_ambImage W₂ hW₂) ⟶
          bed.localResolutionOn (sumPadData D₁ D₂).sigmaTriple
          (sumPadData D₁ D₂).domBEDan_sigmaTriple
          ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂))
          ((sumPadData D₁ D₂).isCompact_closure_ambImage _
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂))) :=
  bed.localResolutionHomOn (sumPadData D₁ D₂).sigmaTriple (sumPadData D₁ D₂).domBEDan_sigmaTriple
    ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂))
    ((sumPadData D₁ D₂).isCompact_closure_ambImage _
      (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂))
    (D₂.padRightData D₁.n).sigmaTriple (D₂.padRightData D₁.n).domBEDan_sigmaTriple
    (sumInrAmbient D₁ D₂)
    (isAnalyticOpenEmbedding_sumInrAmbient D₁ D₂) (isPullbackOf_sigmaTriple_sumPad_inr D₁ D₂)
    ((D₂.padRightData D₁.n).ambImage W₂) ((D₂.padRightData D₁.n).isCompact_closure_ambImage W₂ hW₂)
    (image_sumInrAmbient_ambImage_subset D₁ D₂ W₁ W₂) hbed

/-- **The label map of the first padded level into the common label set** ([Kol07, 34.1]) — the
general restriction identity
(`BEDanFamStar.exists_orderEmbedding_comap_localResolutionHomOn_runMembers`) at the `inl`
inclusion, read on the data's `sigmaMembers`: the common run's member of label `lab k` pulls back
along `sumInlResIn` to the level's member `k`, the members off the range to `⊤`. -/
theorem exists_orderEmbedding_comap_sumInlResIn_sigmaMembers :
    ∃ lab : (D₁.padLeftData D₂.n).sigmaIndex bed W₁ hW₁ ↪o
        (sumPadData D₁ D₂).sigmaIndex bed (sumPadOpens D₁ D₂ W₁ W₂)
          (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂),
      (∀ k, AnalyticSpace.QuotientSpace.comap (sumInlResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (lab k)) =
        (D₁.padLeftData D₂.n).sigmaMembers bed W₁ hW₁ hbed k) ∧
      ∀ σ, σ ∉ Set.range lab →
        AnalyticSpace.QuotientSpace.comap (sumInlResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ) = ⊤ :=
  bed.exists_orderEmbedding_comap_localResolutionHomOn_runMembers _ _ _ _ hbed _ _ _ _ _ _ _ _

/-- **The label map of the second padded level into the common label set** ([Kol07, 34.1]) — the
general identity at the `inr` inclusion. -/
theorem exists_orderEmbedding_comap_sumInrResIn_sigmaMembers :
    ∃ lab : (D₂.padRightData D₁.n).sigmaIndex bed W₂ hW₂ ↪o
        (sumPadData D₁ D₂).sigmaIndex bed (sumPadOpens D₁ D₂ W₁ W₂)
          (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂),
      (∀ k, AnalyticSpace.QuotientSpace.comap (sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (lab k)) =
        (D₂.padRightData D₁.n).sigmaMembers bed W₂ hW₂ hbed k) ∧
      ∀ σ, σ ∉ Set.range lab →
        AnalyticSpace.QuotientSpace.comap (sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1
          ((sumPadData D₁ D₂).sigmaMembers bed (sumPadOpens D₁ D₂ W₁ W₂)
            (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed σ) = ⊤ :=
  bed.exists_orderEmbedding_comap_localResolutionHomOn_runMembers _ _ _ _ hbed _ _ _ _ _ _ _ _

end SumPad

end Hironaka.Manifold.LocalEmbeddingData

end
