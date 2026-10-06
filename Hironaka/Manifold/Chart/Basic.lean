/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.RingTheory.Ideal.Cotangent
public import Hironaka.Manifold.StructureSheaf
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Charts of an analytic manifold: coordinate swaps, pullback of germs, cotangent classes

Three definitions used by the chart lemmas of `Hironaka/Manifold/Chart/`:

* `IsCoordinateSwap e e' p Φ`: `Φ` is the coordinate-swap isomorphism `φ_p = e'⁻¹ ∘ e` from the
  chart `e` to the chart `e'` at `p` — a `PartialDiffeomorph` of `M` with `p` in its source, source
  inside the source of `e`, target inside the source of `e'`, and `e' ∘ Φ = e` on the source. Its
  source is Kollár's neighbourhood `U(p)` and its target `V(p)`, two neighbourhoods of `p` which
  need not coincide (the automorphism `φ` of [Kol07, 95], realised on a neighbourhood; the
  coordinate change `φ_{uv}` of [Wlo09, Lemma 5.5.3, proof, step (0)]).
* `IsPullbackStalk Φ r`: `r : 𝒪_{M,p} →+* 𝒪_{M,p}` is the pullback `g ↦ g ∘ Φ` on germs at `p`,
  read through `stalkToGerm`.
* `cotangentClass a s`: the class of `s − s(a)` in `𝔪_a / 𝔪_a²`, the cotangent space of `𝒪_{M,a}`,
  a `𝕜`-module through the `𝕜`-algebra structure of the stalk.

The swaps are constructed in `Hironaka/Manifold/Chart/Swap.lean`; the cotangent classes are
compared with differentials in `Hironaka/Manifold/Chart/Cotangent.lean`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite Filter Topology Set IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (M : Type u) [TopologicalSpace M] [ChartedSpace E M]

/-- `Φ` is the coordinate-swap isomorphism from the chart `e` to the chart `e'` at `p` — an analytic
isomorphism between two neighbourhoods `U(p) = Φ.source ⊆ e.source` and
`V(p) = Φ.target ⊆ e'.source` of `p` with `e' ∘ Φ = e` on `U(p)`, i.e. `Φ = e'⁻¹ ∘ e` (the
automorphism of [Kol07, 95]; the coordinate change of [Wlo09, Lemma 5.5.3, proof, step (0)]). -/
def IsCoordinateSwap (e e' : OpenPartialHomeomorph M E) (p : M)
    (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M M ω) : Prop :=
  p ∈ Φ.source ∧ Φ.source ⊆ e.source ∧ Φ.target ⊆ e'.source ∧ ∀ x ∈ Φ.source, e' (Φ x) = e x

/-- `r : 𝒪_{M,p} →+* 𝒪_{M,p}` is the pullback of germs along a map `Φ` with `Φ p = p` (continuous
at `p`): the germ of `g` goes to the germ of `g ∘ Φ`, read through `stalkToGerm`. -/
def IsPullbackStalk (Φ : M → M) {p : M}
    (r : (structureSheaf 𝕜 E M).presheaf.stalk p →+* (structureSheaf 𝕜 E M).presheaf.stalk p) :
    Prop :=
  ∃ hΦ : Tendsto Φ (𝓝 p) (𝓝 p), ∀ s,
    stalkToGerm 𝓘(𝕜, E) ω M p (r s) = germCompRingHom Φ hΦ (stalkToGerm 𝓘(𝕜, E) ω M p s)

variable {M}

/-- The class of `s − s(a)` in the cotangent space `𝔪_a / 𝔪_a²` of the stalk at `a`. -/
def cotangentClass (a : M) (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a)).Cotangent :=
  (maximalIdeal _).toCotangent ⟨s - const 𝕜 E M a (eval 𝕜 E M a s),
    (mem_maximalIdeal_iff_eval E _).mpr (by simp [map_sub])⟩

end Manifold

end
