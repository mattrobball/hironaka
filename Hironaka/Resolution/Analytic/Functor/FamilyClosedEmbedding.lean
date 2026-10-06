/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.Family
public import Hironaka.Manifold.FiniteSuccession.Restrict.RestrictBundle
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The per-open closed-embeddings predicate for family functors

The commutation with closed embeddings of [Kol07, 34.3], in the form of [Kol07, Theorem 103, (3)],
per relatively compact open: the family functor `B` at the model `(E, ψ₀)` commutes with closed
embeddings whenever `E = ∅`, through the family functor `B'` at the model `𝕜^{n−s}`; this is the
per-open version of `AnalyticBlowUpSequenceAssignment.CommutesWithClosedEmbeddingsOfEmptyDivisor`
(`Hironaka.Manifold.FiniteSuccession.Functor.Basic`), the `(n−s)`-dimensional family read at `U ∩ S`
and pushed forward by `BlowUpSequence.pushforwardRestrict`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.Manifold.AnalyticFamilyFunctor

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}
  {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
  (B : AnalyticFamilyFunctor ψ₀ Dom)

/-- `B`
**commutes with closed embeddings whenever
`E = ∅`, through `B'`** — for every closed submanifold `τ : S ↪ M` of codimension `s`, ideal sheaves
`𝓘` on `M` and `J` on the bundled `S` with `𝓘 ⊇ I_S` and `J = τ^* 𝓘`, and every relatively compact
open `U ⊆ M`, the value of `B` on `U` is the push-forward of the value of `B'` on `U_S`. -/
def CommutesWithClosedEmbeddingsOfEmptyDivisorFam {s : ℕ}
    {Dom' : ∀ {M' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)},
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) M' → Prop}
    (B' : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Dom') :
    Prop :=
  ∀ {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} (hS : IsClosedSubmanifold ψ₀ S s)
    (I : AnalyticManifold.IdealSheaf M) (hI : I.IsNonzeroEverywhere)
    (J : AnalyticManifold.IdealSheaf hS.toAnalyticManifold) (hJ : J.IsNonzeroEverywhere),
    hS.idealSheaf ≤ I → J = I.pullback hS.inclusionMap hS.inclusionMap.contMDiff →
    ∀ (hT : Dom ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩)
      (hT' : Dom' ⟨J, hJ, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩)
      (U : Opens M) (hU : IsCompact (closure (U : Set M))),
      (B.fam _ hT).seqOn U hU =
        AnalyticManifold.BlowUpSequence.pushforwardRestrict hS U
          ((B'.fam _ hT').seqOn (hS.preimageOpens U) (hS.isCompact_closure_preimageOpens U hU))

end Hironaka.Manifold.AnalyticFamilyFunctor

end
