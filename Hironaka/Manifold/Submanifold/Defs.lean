/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Closed analytic submanifolds and their ideal sheaves

A closed subset `Y` of a manifold `M` modelled on `E` over `𝕜 ∈ {ℝ, ℂ}` is a **closed analytic
submanifold of codimension `c`** when every point of `Y` has a chart
`φ : U → V × W ⊆ 𝕜^c × 𝕜^{n-c}` with `φ(Y ∩ U) = {0} × W`, an **adapted chart** — the charts in
which Bierstone–Milman describe the blowing-up of a manifold along a closed submanifold
[BM88, Definition 4.1 (2)], and the sense in which a smooth subspace is "locally a coordinate
subspace of a coordinate chart" [BM97, (3.8)(2); §3, "Blowing-up"]. Read on the coordinates
`ψ : E ≃L[𝕜] (Fin n → 𝕜)`, an adapted chart is a chart `φ` of the maximal atlas together with an
injection `σ : Fin c ↪ Fin n` such that, on the source of `φ`, `x ∈ Y ↔ ∀ i, ψ (φ x) (σ i) = 0`
(`IsAdaptedChart ψ Y φ σ`); the product form of the target is recovered by shrinking the source.
`IsClosedSubmanifold ψ Y c` asks for a closed `Y` with an adapted chart at each of its points. No
`IsManifold` instance is assumed: the charts are members of the maximal atlas of the analytic
groupoid.

The ideal sheaf of a closed submanifold: `IsIdealSheafOf ψ Y c J` says that the ideal sheaf `J` has
cosupport `Y` and that at every point of `Y`, in every adapted chart, its stalk is spanned by the
germs of the adapted coordinates `x_{σ i} = ψ_{σ i} ∘ φ` (`coord`); `IsClosedSubmanifold.idealSheaf`
is the ideal sheaf satisfying this specification (a classical choice, the unit ideal sheaf if there
is none). The centres of the monoidal transformations of the analytic main theorems are closed
submanifolds with their ideal sheaves — Hironaka's regular system of parameters containing
equations for the centre [Hir64, Definition 2, p. 141] is realised by an adapted chart.
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section Submanifold

open Filter Topology Set

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-- An **adapted chart** for `Y`: a chart `φ` of the maximal atlas on whose source `Y` is the
coordinate subspace `{z_σ = 0}` of the coordinates `ψ ∘ φ`. -/
def IsAdaptedChart (Y : Set M) (φ : OpenPartialHomeomorph M E) {c : ℕ} (σ : Fin c ↪ Fin n) : Prop :=
  φ ∈ maximalAtlas 𝓘(𝕜, E) ω M ∧ ∀ x ∈ φ.source, (x ∈ Y ↔ ∀ i, ψ (φ x) (σ i) = 0)

/-- A **closed analytic submanifold** of codimension `c`: a closed set with an adapted chart at
each of its points [BM88, Definition 4.1 (2)]. -/
structure IsClosedSubmanifold (Y : Set M) (c : ℕ) : Prop where
  isClosed : IsClosed Y
  exists_adaptedChart : ∀ a ∈ Y, ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n),
    a ∈ φ.source ∧ IsAdaptedChart ψ Y φ σ

end Submanifold

section IdealSheafOf

open CategoryTheory
open scoped Topology

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

variable [IsManifold 𝓘(𝕜, E) ω M]

/-- `J` is **the ideal sheaf of the closed submanifold `Y`**: its cosupport is `Y` and, at every
point of `Y` in an adapted chart `φ` with indices `σ`, its stalk is spanned by the germs of the
adapted coordinates `x_{σ i} = ψ_{σ i} ∘ φ`. -/
def IsIdealSheafOf (Y : Set M) (c : ℕ) (J : IdealSheaf (structureSheaf 𝕜 E M)) : Prop :=
  J.support = Y ∧ ∀ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n)
    (hφ : IsAdaptedChart ψ Y φ σ) (a : M) (ha : a ∈ φ.source), a ∈ Y →
      J.stalkIdeal a = Ideal.span (Set.range fun i => coord E ψ φ hφ.1 ha (σ i))

end IdealSheafOf

section IdealSheaf

open CategoryTheory Filter Topology Set IsLocalRing

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M} {c : ℕ}

open scoped Classical in
/-- **The ideal sheaf `I_Y` of a closed submanifold**: the unique ideal sheaf satisfying the
specification `IsIdealSheafOf ψ Y c` (cosupport `Y`, stalks spanned by the adapted coordinates),
when one exists; the unit ideal sheaf otherwise. Existence and uniqueness are proved in
`Hironaka.Manifold.BlowUp.Transform.Object`. -/
def IsClosedSubmanifold.idealSheaf (_hY : IsClosedSubmanifold ψ Y c) :
    IdealSheaf (structureSheaf 𝕜 E M) :=
  if h : ∃ J, IsIdealSheafOf ψ Y c J then Classical.choose h else ⊤

end IdealSheaf

end Manifold
