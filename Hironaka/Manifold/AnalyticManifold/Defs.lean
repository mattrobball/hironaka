/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Hironaka.Manifold.DisjointUnion.Defs
public import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Geometry.Manifold.ContMDiffMap  -- shake: keep (used only by `example`s)
import Mathlib.Analysis.RCLike.Basic  -- shake: keep (used only by `example`s)

/-!
# Analytic manifolds and analytic maps

Hironaka's "non-singular analytic `K`-space" [Hir64, pp. 119–121] is an analytic manifold
`AnalyticManifold 𝕜 E`: a bundled manifold without boundary modelled on a normed space `E` over
`𝕜`, with analytic (`C^ω`) chart changes, Hausdorff and second countable (Hironaka's spaces are
Hausdorff and countable at infinity). Its carrier carries Mathlib's unbundled instances
(`ChartedSpace`, `IsManifold 𝓘(𝕜, E) ω`, `T2Space`, `SecondCountableTopology`), and it coerces to
the type of its points.

* Analytic maps `AnalyticMap M N` are Mathlib's bundled `C^ω` maps `C^ω⟮𝓘(𝕜, E), M; 𝓘(𝕜, E), N⟯`.
* `AnalyticMap.IsIsoOver f U`: `f` restricts to an analytic isomorphism `f⁻¹(U) → U`, condition (1)
  of Bierstone–Milman's blowing-up off its centre [BM88, Definition 4.1].
* An open subset `U : Opens M` is an analytic manifold `M.restrict U` (Mathlib's charted-space and
  `IsManifold` instances on `Opens`; Hausdorff and second countable as a subspace), with the
  analytic inclusion `M.inclusion U`.
* The disjoint union of a countable family of opens `Gᵢ ⊆ Kⁿ` is an analytic manifold
  `sigmaOpens G` modelled on `Kⁿ` (`ChartedSpace.sigma`, `IsManifold.sigma`).

The definitions are stated over any nontrivially normed field; the blowing-up, the monoidal
transformations and the boundary predicates built on them are stated over `𝕜 ∈ {ℝ, ℂ}` (`RCLike`,
the fields of Hironaka's real and complex statements), and the main theorems instantiate `𝕜 = ℝ`.
-/

@[expose] public section

universe u

open scoped Manifold ContDiff

/-- A bundled analytic manifold over `𝕜` modelled on `E`: Hausdorff, second countable, without
boundary, with analytic (`C^ω`) chart changes — for `E` finite-dimensional, Hironaka's
non-singular analytic `𝕜`-space [Hir64, pp. 119–121]. -/
structure AnalyticManifold (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] where
  /-- The underlying type of points. -/
  carrier : Type u
  [top : TopologicalSpace carrier]
  [charted : ChartedSpace E carrier]
  [manifold : IsManifold 𝓘(𝕜, E) ω carrier]
  [t2 : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]

namespace AnalyticManifold

attribute [instance] AnalyticManifold.top AnalyticManifold.charted AnalyticManifold.manifold
  AnalyticManifold.t2 AnalyticManifold.secondCountable

/- The field lives in `Type` from here on: the ideal sheaves of an analytic manifold are built from
functions `U → 𝕜` and must live in the universe of the manifold (the main theorems instantiate
`ℝ`). -/
section General

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

instance : CoeSort (AnalyticManifold.{u} 𝕜 E) (Type u) := ⟨AnalyticManifold.carrier⟩

/-- Analytic maps between analytic manifolds: Mathlib's bundled `C^ω` maps. -/
abbrev _root_.AnalyticMap (M N : AnalyticManifold.{u} 𝕜 E) : Type u :=
  C^ω⟮𝓘(𝕜, E), M; 𝓘(𝕜, E), N⟯

/-- `f` restricts to an analytic isomorphism `f⁻¹(U) → U` over the open set `U`: `f` is a local
diffeomorphism on `f⁻¹(U)` and a bijection `f⁻¹(U) → U` — condition (1) of Bierstone–Milman's
blowing-up [BM88, Definition 4.1], off the centre; the clause "`σ` is an isomorphism off the
cosupport of `I`" of the principalization theorem. -/
def _root_.AnalyticMap.IsIsoOver {M M' : AnalyticManifold.{u} 𝕜 E} (f : AnalyticMap M' M)
    (U : Set M) : Prop :=
  IsLocalDiffeomorphOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω f (f ⁻¹' U) ∧ Set.BijOn f (f ⁻¹' U) U

end General

section Open

open TopologicalSpace

noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- The open subset `U` of `M` as an analytic manifold (Włodarczyk's neighbourhood `U ⊃ Z` of a
compact set and the stages `U_i` over it, [Wlo09, Theorem 2.0.3 (1)]): Mathlib's charted-space
and `IsManifold` instances on `Opens`; Hausdorff and second countable as a subspace of `M`. -/
def restrict (M : AnalyticManifold.{u} 𝕜 E) (U : Opens M) :
    AnalyticManifold.{u} 𝕜 E where
  carrier := U

/-- The inclusion `U → M` of an open subset as an analytic map (Mathlib's
`contMDiff_subtype_val`). -/
def inclusion (M : AnalyticManifold.{u} 𝕜 E) (U : Opens M) :
    AnalyticMap (M.restrict U) M :=
  ⟨Subtype.val, contMDiff_subtype_val⟩

end

end Open

section SigmaOpens

variable {K : Type} [RCLike K] {n : ℕ}

/-- The disjoint union `A := ⊔ᵢ Gᵢ` of a countable family of open subsets `Gᵢ ⊆ Kⁿ` as an analytic
manifold modelled on `Kⁿ` (the ambient `X' = ⊔ Uᵢ` of the proof of [Kol07, Proposition 37]): the
`Σ`-type with the charts of the summands (`ChartedSpace.sigma`, `IsManifold.sigma`), Hausdorff as
a disjoint union of Hausdorff spaces and second countable for a countable index. -/
noncomputable def sigmaOpens {ι : Type u} [Countable ι]
    (G : ι → TopologicalSpace.Opens (Fin n → K)) : AnalyticManifold.{u} K (Fin n → K) where
  carrier := Σ i, ↥(G i)

end SigmaOpens

end AnalyticManifold
