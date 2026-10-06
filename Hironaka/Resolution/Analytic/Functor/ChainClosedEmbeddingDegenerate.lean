/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.FamilyClosedEmbedding
public import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Resolution.Analytic.Restrict.GoingDown
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The chaining of the closed-embedding commutation, I: the degenerate codimensions

[Kol07, 108] reduces the commutation of the order-reduction functors with closed embeddings to
the hypersurface case along a flag `Y = Y₀ ⊂ Y₁ ⊂ ⋯ ⊂ Y_c = X`. The predicate
`AnalyticFamilyFunctor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s)` has two degenerate
codimensions the printed reduction (the chain of hypersurfaces) does not mention: `s > n`, where
every closed submanifold of codimension `s` of an `n`-dimensional manifold is empty, and `s = 0`
(the codimension-zero clause, `Hironaka.Resolution.Analytic.Functor.ChainClosedEmbeddingZero`).
This module proves the first:

* `BlowUpSequence.eq_nil_of_isEmpty`: a list of centres without empty centres on an empty manifold
  is `nil` (a first centre would be a nonempty subset of the empty carrier);
* `AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_of_lt`: at a codimension
  `s > n` the predicate holds through any partner functor, given the codimension-zero clause of
  the outer functor (through some partner) and the restriction of its domain to the empty
  submanifold. The closed submanifold is empty (`IsClosedSubmanifold.codim_le'`), so the right
  side of the per-open identity is the push-forward of a list on the empty manifold, `nil`; the
  left side is the value of the functor on a triple whose ideal contains the unit ideal of the
  empty submanifold, which the codimension-zero clause at the empty submanifold (a closed
  submanifold of every codimension, `isClosedSubmanifold_empty'`; its reduced ideal is independent
  of the codimension, `idealSheaf_eq_of_set`) reads as the push-forward of a list on the empty
  manifold, `nil` again.

The tower lemma uses this case at every `s ≥ n`, where its codimension-one hypothesis `h1`
(`(F m).CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := 1) (F (m - 1))` for `0 < m`) is not
available at `m = n - s = 0`.
-/

public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- A list of centres without empty centres on an empty
manifold is the empty list — a first centre would be a nonempty subset of the empty carrier. -/
theorem _root_.AnalyticManifold.BlowUpSequence.eq_nil_of_isEmpty {M : AnalyticManifold.{u} 𝕜 E}
    (hM : IsEmpty M)
    (L : AnalyticManifold.BlowUpSequence ψ₀ M) (hL : L.NoEmptyCenters) : L =
        AnalyticManifold.BlowUpSequence.nil M := by
  cases L with
  | nil => rfl
  | cons hY rest =>
    exact absurd (Set.eq_empty_of_isEmpty _)
      ((AnalyticManifold.BlowUpSequence.noEmptyCenters_cons_iff hY rest).mp hL).1

/-- The degenerate case `s > n` ([Kol07, 108] prints only the chain of hypersurfaces): at a
codimension `s > n` every closed submanifold of an `n`-dimensional manifold is empty
(`IsClosedSubmanifold.codim_le'`), so the predicate holds through ANY partner `B'`, given the
codimension-zero clause of `B` (through some `B₀`) and the restriction of the domain to the empty
submanifold: both sides of the per-open identity are `nil`. -/
theorem AnalyticFamilyFunctor.commutesWithClosedEmbeddingsOfEmptyDivisorFam_of_lt
    {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
    (B : AnalyticFamilyFunctor ψ₀ Dom)
    {Dom₀ : ∀ {M₀ : AnalyticManifold.{u} 𝕜 (Fin (n - 0) → 𝕜)},
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 0) → 𝕜)) M₀ → Prop}
    (B₀ : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 0) → 𝕜)) Dom₀) {s : ℕ}
    {Dom' : ∀ {M' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)},
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) M' → Prop}
    (B' : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Dom')
    (hlt : n < s) (h0 : B.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := 0) B₀)
    (hDom0 : ∀ {M : AnalyticManifold.{u} 𝕜 E} (I : AnalyticManifold.IdealSheaf M)
      (hI : I.IsNonzeroEverywhere)
      (hJ : (I.pullback (isClosedSubmanifold_empty' ψ₀ 0 (M := M)).inclusionMap
        (isClosedSubmanifold_empty' ψ₀ 0 (M := M)).inclusionMap.contMDiff).IsNonzeroEverywhere),
      (isClosedSubmanifold_empty' ψ₀ 0 (M := M)).idealSheaf ≤ I →
      Dom ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ →
      Dom₀ ⟨I.pullback (isClosedSubmanifold_empty' ψ₀ 0 (M := M)).inclusionMap
        (isClosedSubmanifold_empty' ψ₀ 0 (M := M)).inclusionMap.contMDiff, hJ,
        HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩) :
    B.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s) B' := by
  intro M S hS I hI J hJ hle hJI hT hT' U hU
  have hSe : S = ∅ := by
    by_contra hne
    exact absurd (hS.codim_le' (Set.nonempty_iff_ne_empty.mpr hne)) (not_le.mpr hlt)
  subst hSe
  -- the right side: a list on the empty manifold
  have hemp : IsEmpty ((hS.toAnalyticManifold).restrict (hS.preimageOpens U)) :=
    ⟨fun p => p.1.2.elim⟩
  rw [AnalyticManifold.BlowUpSequence.eq_nil_of_isEmpty hemp _ ((B'.fam _ hT').noEmptyCenters _ _)]
  -- the left side: the codimension-zero clause at the empty submanifold
  have hE : IsClosedSubmanifold ψ₀ (∅ : Set M) 0 := isClosedSubmanifold_empty' ψ₀ 0
  have hle0 : hE.idealSheaf ≤ I := by
    rw [hE.idealSheaf_eq_of_set hS]
    exact hle
  have hJ0 : (I.pullback hE.inclusionMap hE.inclusionMap.contMDiff).IsNonzeroEverywhere :=
    fun x => x.2.elim
  rw [h0 hE I hI _ hJ0 hle0 rfl hT (hDom0 I hI hJ0 hle0 hT) U hU]
  have hemp0 : IsEmpty ((hE.toAnalyticManifold).restrict (hE.preimageOpens U)) :=
    ⟨fun p => p.1.2.elim⟩
  rw [AnalyticManifold.BlowUpSequence.eq_nil_of_isEmpty hemp0 _ ((B₀.fam _ _).noEmptyCenters _ _)]
  rfl

end Hironaka.Manifold
