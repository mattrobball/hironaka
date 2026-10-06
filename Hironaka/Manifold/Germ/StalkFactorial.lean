/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.StructureSheaf
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Analytic.Rueckert.UFD
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.IdealSheaf.Order
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# The germ ring as a factorial Noetherian regular local ring

The stalk `𝒪_{M,a}` of an analytic manifold is a Noetherian regular local ring of Krull dimension
`n` (`Hironaka/Manifold/Germ/StalkNoetherian.lean`, bundled here as
`isNoetherianRing_isRegularLocalRing_stalk`) and a unique factorization domain
(`uniqueFactorizationMonoid_stalk`): the classical factoriality of the ring `Conv 𝕜 n` of
convergent power series (`Hironaka/Analytic/Rueckert/UFD.lean`, from Rückert's basis theorem
and Gauss's lemma) transported through the Taylor isomorphism `𝒪_{M,a} ≃+* Conv 𝕜 n`. Two
corollaries on principal ideals: the Krull dimension of the quotient of `𝒪_{M,a}` by a proper
principal ideal `(f)` is at least `n − 1` (Mathlib's `dim R ≤ dim R/(x) + 1` for `x` in the maximal
ideal of a Noetherian local ring), and exactly `n − 1` when `f ≠ 0` (Krull's principal ideal
theorem in the domain `𝒪_{M,a}`: a nonzero `f ∈ 𝔪_a` is a nonzerodivisor in the Jacobson radical).
These are the ring-theoretic facts about hypersurface germs used for analytic spaces
(`Hironaka/Space/`) and in the order computations of the resolution algorithm.
-/

public section

open TopologicalSpace IsLocalRing Analytic
open scoped Manifold ContDiff Pointwise
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

section Chart

variable {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (φ : OpenPartialHomeomorph M E) {a : M}
  (ha : a ∈ φ.source) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)

include ψ φ ha hφ in
/-- In a chart of the maximal atlas at `a`, the stalk `𝒪_{M,a}` is a unique factorization domain:
the factoriality of the ring of convergent power series (`uniqueFactorizationMonoid_conv`) through
the Taylor isomorphism `taylorEquivConv`. -/
theorem uniqueFactorizationMonoid_stalk_of_chart :
    UniqueFactorizationMonoid ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
  (taylorEquivConv E ψ φ ha hφ).symm.toMulEquiv.uniqueFactorizationMonoid inferInstance

end Chart

variable [IsManifold 𝓘(𝕜, E) ω M] [FiniteDimensional 𝕜 E]

/-- `𝒪_{M,a}` is a Noetherian regular local ring of Krull dimension `n`, bundled. -/
theorem isNoetherianRing_isRegularLocalRing_stalk (a : M) :
    IsNoetherianRing ((structureSheaf 𝕜 E M).presheaf.stalk a) ∧
      IsRegularLocalRing ((structureSheaf 𝕜 E M).presheaf.stalk a) ∧
      ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk a) = Module.finrank 𝕜 E :=
  ⟨inferInstance, inferInstance, ringKrullDim_stalk (E := E) a⟩

/-- The stalks of an analytic manifold are unique factorization domains. -/
theorem uniqueFactorizationMonoid_stalk (a : M) :
    UniqueFactorizationMonoid ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
  uniqueFactorizationMonoid_stalk_of_chart E (IdealSheaf.modelCoord (𝕜 := 𝕜) (E := E)) (chartAt E a)
    (mem_chart_source E a) (IsManifold.chart_mem_maximalAtlas a)

/-- For `f ∈ 𝔪_a`, `n ≤ dim 𝒪_{M,a} / (f) + 1`: Mathlib's `dim R ≤ dim R/(x) + 1` for `x` in the
maximal ideal of a Noetherian local ring. -/
theorem le_ringKrullDim_quotient_span_singleton_stalk (a : M)
    {f : (structureSheaf 𝕜 E M).presheaf.stalk a}
    (hf : f ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a)) :
    (Module.finrank 𝕜 E : WithBot ℕ∞) ≤
      ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk a ⧸ Ideal.span {f}) + 1 := by
  have h := ringKrullDim_le_ringKrullDim_quotSMulTop_succ hf
  rw [ringKrullDim_stalk (E := E) a] at h
  have hsp : Ideal.span {f} = f • (⊤ : Ideal ((structureSheaf 𝕜 E M).presheaf.stalk a)) := by
    simp [← Submodule.ideal_span_singleton_smul]
  rwa [hsp]

/-- The sharp form, Krull's principal ideal theorem in the domain `𝒪_{M,a}`: for `0 ≠ f ∈ 𝔪_a`,
`dim 𝒪_{M,a} / (f) + 1 = n` — a nonzero element of the maximal ideal of the domain `𝒪_{M,a}` is a
nonzerodivisor in the Jacobson radical. -/
theorem ringKrullDim_quotient_span_singleton_stalk (a : M)
    {f : (structureSheaf 𝕜 E M).presheaf.stalk a}
    (hf : f ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a)) (hf0 : f ≠ 0) :
    ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk a ⧸ Ideal.span {f}) + 1 =
      Module.finrank 𝕜 E := by
  have hdom : IsDomain ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
    isDomain_stalk (IdealSheaf.modelCoord (𝕜 := 𝕜) (E := E)) (IsManifold.chart_mem_maximalAtlas a)
      (mem_chart_source E a)
  rw [ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
    (IsLeftRegular.isSMulRegular (mul_right_injective₀ hf0))
    (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal]; exact hf), ringKrullDim_stalk (E := E) a]

end Manifold
