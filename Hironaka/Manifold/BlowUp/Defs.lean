/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The blowing-up of a manifold with centre a closed submanifold: the definition

Let `M` be an analytic manifold over `𝕜 = ℝ` or `ℂ` and `Y ⊆ M` a closed analytic submanifold.
The blowing-up `π : M' → M` with centre `Y` is an analytic manifold `M'` with a proper analytic
map `π` such that
(1) `π` restricts to an analytic isomorphism `M' ∖ π⁻¹(Y) → M ∖ Y`;
(2) over every chart `φ : U → V × W` of `M` adapted to `Y` (`φ(Y ∩ U) = {0} × W`), `π⁻¹(U)` is
    the blowing-up `V' × W → V × W` of the local model.
Conditions (1) and (2) determine `π : M' → M` uniquely, up to an isomorphism of `M'` commuting
with `π` [BM88, Definition 4.1].

The local model: for an open neighbourhood `V` of `0` in `𝕜^m`, the blowing-up `V' → V` with
centre `{0}` is covered by the charts `V'_i = {ξ_i ≠ 0}` with coordinates `x_ii = x_i` and
`x_ij = ξ_j / ξ_i` for `j ≠ i`, in which it reads `x_i = x_ii`, `x_j = x_ii x_ij` [BM88,
Definition 4.1]. `blowUpChartMap σ i` is this chart map `π_i` in *block form* on `𝕜^n`: the centre
is the coordinate subspace `{x_{σ k} = 0}` cut out by an embedding `σ : Fin c ↪ Fin n`, slot `σ i`
is the scaling variable, the block slots `σ k` with `k ≠ i` are multiplied by it, and the
coordinates off the block pass through.

Condition (2) is stated here *in coordinates*: for every adapted chart `φ` of `Y`, with block
indices `σ : Fin c ↪ Fin n` (`IsAdaptedChart`), and every `i`, `M'` has a chart `Φ` of its maximal
atlas, a *blow-up chart of index `i` over `φ`* (`IsBlowUpChart`), with source inside `π⁻¹(U)`,
target the full chart domain `π_i⁻¹(ψ(φ(U)))` of the local model, on which
`ψ ∘ φ ∘ π = π_i ∘ ψ ∘ Φ`, and these sources cover `π⁻¹(U)` (`IsBlowUp`). For a Hausdorff `M'`
this is equivalent to condition (2) as printed: the chartwise identification with the glued local
model is injective by continuity from the dense complement of the exceptional set.

On bundled analytic manifolds, `AnalyticMap.IsMonoidalTransformation f D` says that `f` is the
monoidal transformation with centre the closed subspace defined by the ideal sheaf `D`: the
cosupport of `D` is a closed submanifold, `D` is its ideal sheaf (`IsIdealSheafOf`) and `f` is a
blowing-up with that centre. The coordinates `ψ : E ≃ 𝕜ⁿ` and the codimension of the centre are
existentially quantified inside the predicate, as Kollár names local coordinates at each point; the
statements carry no model isomorphism among their binders.
-/

@[expose] public section

open TopologicalSpace Opposite CategoryTheory
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section ChartMap

variable {𝕜 : Type} [RCLike 𝕜] {n c : ℕ}

/-- The chart map `π_i` of the `i`-th blow-up chart in block form [BM88, Definition 4.1]: slot
`σ i` is the scaling variable, the other block slots `σ k` are ratio variables multiplied by it,
and the coordinates off the block pass through. -/
noncomputable def blowUpChartMap (σ : Fin c ↪ Fin n) (i : Fin c) :
    (Fin n → 𝕜) → (Fin n → 𝕜) := by
  classical
  exact fun u j => if ∃ k, k ≠ i ∧ σ k = j then u (σ i) * u j else u j

end ChartMap

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M']

/-- Condition (2) of [BM88, Definition 4.1] in coordinates: `Φ` is **a blow-up chart of index `i`**
over the chart `φ` of `M` with block indices `σ`, for the map `π : M' → M`, when it is a chart of
the maximal atlas of `M'` with source inside `π⁻¹(φ.source)` and target the chart domain
`π_i⁻¹(ψ(φ.target))` of the local model, on which `ψ ∘ φ ∘ π = π_i ∘ ψ ∘ Φ`. -/
structure IsBlowUpChart (π : M' → M) (φ : OpenPartialHomeomorph M E) {c : ℕ} (σ : Fin c ↪ Fin n)
    (i : Fin c) (Φ : OpenPartialHomeomorph M' E) : Prop where
  mem_maximalAtlas : Φ ∈ maximalAtlas 𝓘(𝕜, E) ω M'
  source_subset : Φ.source ⊆ π ⁻¹' φ.source
  mem_target_iff : ∀ v, v ∈ Φ.target ↔ blowUpChartMap σ i (ψ v) ∈ ψ '' φ.target
  comm : ∀ p ∈ Φ.source, ψ (φ (π p)) = blowUpChartMap σ i (ψ (Φ p))

/-- **`π : M' → M` is the blowing-up of `M` with centre `Y`** [BM88, Definition 4.1], for `Y` a
closed submanifold of codimension `c` (the hypotheses on `Y` are carried by the theorems, not by
this predicate): `M'` is an analytic manifold (Hausdorff, second countable), `π` is proper and
analytic, (1) `π` restricts to an analytic isomorphism `M' ∖ π⁻¹(Y) → M ∖ Y`, and (2) over every
adapted chart of `Y` the blow-up charts of every index exist and their sources cover `π⁻¹(U)`. -/
structure IsBlowUp (Y : Set M) (c : ℕ) [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
    [SecondCountableTopology M'] (π : M' → M) : Prop where
  contMDiff : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω π
  isProperMap : IsProperMap π
  isLocalDiffeomorphOn_compl : IsLocalDiffeomorphOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω π (π ⁻¹' Yᶜ)
  bijOn_compl : Set.BijOn π (π ⁻¹' Yᶜ) Yᶜ
  exists_chart : ∀ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n), IsAdaptedChart ψ Y φ σ →
    ∀ i : Fin c, ∃ Φ : OpenPartialHomeomorph M' E, IsBlowUpChart ψ π φ σ i Φ
  cover : ∀ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n), IsAdaptedChart ψ Y φ σ →
    ∀ p, π p ∈ φ.source →
      ∃ (i : Fin c) (Φ : OpenPartialHomeomorph M' E), IsBlowUpChart ψ π φ σ i Φ ∧ p ∈ Φ.source

end Manifold

namespace AnalyticManifold

/- The field is `RCLike` from here on: the blowing-up of Bierstone–Milman is built over
`K ∈ {ℝ, ℂ}` (the main theorems instantiate `ℝ`). -/
variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `f : M' → M` is the monoidal transformation of `M` with centre the closed analytic subspace
defined by `D` (Hironaka's monoidal transformation; the blowing-up of [BM88, Definition 4.1]): for
some coordinates `ψ : E ≃ 𝕜ⁿ` and some codimension `c`, the cosupport `Y` of `D` is a closed
analytic submanifold of codimension `c` (`IsClosedSubmanifold`), `D` is the ideal sheaf of `Y`
(`IsIdealSheafOf`: cosupport `Y`, stalks at the points of `Y` spanned by the adapted coordinates),
and `f` is a blowing-up of `M` with centre `Y` (`IsBlowUp`: proper analytic, an analytic
isomorphism off `Y`, with the blow-up charts over every adapted chart). -/
def _root_.AnalyticMap.IsMonoidalTransformation {M M' : AnalyticManifold.{u} 𝕜 E}
    (f : AnalyticMap M' M)
    (D : IdealSheaf M) : Prop :=
  ∃ (n : ℕ) (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (c : ℕ),
    Manifold.IsClosedSubmanifold ψ D.support c ∧
      Manifold.IsIdealSheafOf ψ D.support c D ∧
        Manifold.IsBlowUp ψ D.support c f

end AnalyticManifold
