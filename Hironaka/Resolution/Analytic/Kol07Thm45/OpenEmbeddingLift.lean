/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Restrict.DiffeomorphTransport
public import Hironaka.Resolution.Analytic.TransportBase
public import Hironaka.Resolution.Analytic.Functor.Family
import Hironaka.Resolution.Analytic.OrderReduction.ChainTransportPrep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The last-stage lift of an injective local isomorphism is an open embedding

A local analytic isomorphism `h : N → M` lifts to the blow-up sequence pulled back along it
[Kol07, Definition 30.1], `pullbackLiftLast : (L.pullback h).stage r → L.stage r`, with image the
preimage of `range h` under the composite blow-down (`range_pullbackLiftLast`). When `h` is
INJECTIVE — the case of an open inclusion `W' ↪ W`, through which the local resolutions over two
opens of one piece, and over the overlap of two pieces, are compared (the open neighbourhoods
`A⁰_X ⊂ A_X` of [Kol07, Theorem 36, proof]; the embeddings `Y_{Z_i ∩ Z_j} → Y_{Z_i}` of
[Wlo09, §4, (3)⇒(4)]) — the lift is an open embedding and a diffeomorphism onto its open image.
This module proves that in two general lemmas about any injective local analytic isomorphism
(`AnalyticMap.isOpenEmbedding_of_injective`, `AnalyticMap.diffeomorphOntoImage`) and their
instances at the lift (`BlowUpSequence.isOpenEmbedding_pullbackLiftLast`,
`BlowUpSequence.pullbackLiftLastDiffeomorphOntoImage`, with
`coe_image_isLocalDiffeomorph_pullbackLiftLast` identifying the image open). Not in the sources;
routine.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.Manifold

section OpenEmbedding

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {N M : AnalyticManifold.{u} 𝕜 E}

/-- An injective local analytic isomorphism is an open embedding (Mathlib's
`IsLocalDiffeomorph.isOpenMap` with `IsOpenEmbedding.of_continuous_injective_isOpenMap`). -/
theorem AnalyticMap.isOpenEmbedding_of_injective (f : AnalyticMap N M)
    (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) (hi : Function.Injective f) :
    Topology.IsOpenEmbedding f :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap f.contMDiff.continuous hi hf.isOpenMap

/-- The image of the whole source under `f` is the range, inside Mathlib's image open
(`IsLocalDiffeomorph.image`). -/
theorem AnalyticMap.image_top_subset_image (f : AnalyticMap N M)
    (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) :
    ⇑f '' ((⊤ : Opens N) : Set N) ⊆ (hf.image : Set M) := by
  rintro _ ⟨x, -, rfl⟩
  exact ⟨x, rfl⟩

/-- **An injective local analytic isomorphism is a diffeomorphism onto its image**, the open
`hf.image = ⟨range f, _⟩` of Mathlib (`IsLocalDiffeomorph.image`), read as the open submanifold
`M.restrict hf.image`: the codomain restriction of `f` is a bijective local diffeomorphism
(`AnalyticMap.isLocalDiffeomorph_restrictMap` at `U' = ⊤`, `surjective_restrictMap`,
`IsLocalDiffeomorph.toDiffeomorphOfBijective`), after the identification `N.restrict ⊤ ≃ N`
(`restrictTopDiffeomorph`). -/
def AnalyticMap.diffeomorphOntoImage (f : AnalyticMap N M)
    (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) (hi : Function.Injective f) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N (M.restrict hf.image) ω :=
  (AnalyticManifold.restrictTopDiffeomorph N).symm.trans
    ((AnalyticMap.isLocalDiffeomorph_restrictMap hf ⊤ hf.image
      (AnalyticMap.image_top_subset_image f hf)).toDiffeomorphOfBijective
      ⟨fun a b hab => Subtype.ext (hi (congrArg Subtype.val hab)),
        AnalyticMap.surjective_restrictMap (by rw [Opens.coe_top, Set.image_univ]; rfl)⟩)

/-- On points the diffeomorphism onto the image is `f`. -/
theorem AnalyticMap.coe_diffeomorphOntoImage (f : AnalyticMap N M)
    (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) (hi : Function.Injective f) (p : N) :
    (AnalyticMap.diffeomorphOntoImage f hf hi p).1 = f p :=
  rfl

end OpenEmbedding

end Hironaka.Manifold

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- **The last-stage lift of an injective local analytic isomorphism is an open embedding**
(`injective_pullbackLiftLast`, `isLocalDiffeomorph_pullbackLiftLast`,
`AnalyticMap.isOpenEmbedding_of_injective`); the lift of [Kol07, Definition 30.1]. -/
theorem isOpenEmbedding_pullbackLiftLast (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hi : Function.Injective h) :
    Topology.IsOpenEmbedding (L.pullbackLiftLast h hh) :=
  AnalyticMap.isOpenEmbedding_of_injective _ (L.isLocalDiffeomorph_pullbackLiftLast h hh)
    (L.injective_pullbackLiftLast h hh hi)

/-- The image open of the last-stage lift is the preimage of `range h` under the composite
blow-down (`range_pullbackLiftLast`). -/
theorem coe_image_isLocalDiffeomorph_pullbackLiftLast (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    ((L.isLocalDiffeomorph_pullbackLiftLast h hh).image : Set (L.stage (Fin.last _))) =
      ⇑(L.toSuccession.stageMap (Fin.last _)) ⁻¹' Set.range h :=
  L.range_pullbackLiftLast h hh

/-- **The last-stage lift of an injective local analytic isomorphism, as a diffeomorphism onto its
image** — the open submanifold of the last stage over `range h` ([Kol07, Definition 30.1]). The
form used when `h` is the open inclusion `W' ↪ W` of two ambient opens of a piece. -/
def pullbackLiftLastDiffeomorphOntoImage (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hi : Function.Injective h) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ((L.pullback h hh).stage (Fin.last _))
      ((L.stage (Fin.last _)).restrict (L.isLocalDiffeomorph_pullbackLiftLast h hh).image) ω :=
  AnalyticMap.diffeomorphOntoImage (L.pullbackLiftLast h hh)
    (L.isLocalDiffeomorph_pullbackLiftLast h hh) (L.injective_pullbackLiftLast h hh hi)

/-- On points the diffeomorphism onto the image is the lift. -/
theorem coe_pullbackLiftLastDiffeomorphOntoImage (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hi : Function.Injective h)
    (p : (L.pullback h hh).stage (Fin.last _)) :
    (L.pullbackLiftLastDiffeomorphOntoImage h hh hi p).1 = L.pullbackLiftLast h hh p :=
  rfl

end AnalyticManifold.BlowUpSequence

end
