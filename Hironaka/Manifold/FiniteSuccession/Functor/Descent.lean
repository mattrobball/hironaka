/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Basic
import Hironaka.Manifold.FiniteSuccession.Functor.LiftedFibre
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.Saturation
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Descent of a blow-up sequence along a surjective local analytic isomorphism

The descent of [Kol07, Proposition 37], (37.1)–(37.2), iterated along the sequence. On manifolds,
with the functors valued in centre lists: a list `L'` on `N` whose two pull-backs to a fibre
product `(P, p₁, p₂)` of the surjective local analytic isomorphism `g : N → M` with itself agree is
the pull-back of a unique list `L` on `M`, by recursion on `L'`. The first centre is saturated
(`saturated_of_isFibreProduct`), so it is the preimage of a closed submanifold `Z` of `M`
(`IsClosedSubmanifold.image_of_saturated`); the tail lives on the blowing-up of `N` along `g⁻¹Z`,
which is the domain of the lift `g₁ : Bl_{g⁻¹Z} N → Bl_Z M`; the lifted projections form again a
fibre product (`isFibreProduct_lifted`), and the tail descends by the recursive call. Uniqueness is
`pullback_injective_of_surjective`.
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- [Kol07, Proposition 37], (37.1)–(37.2) iterated ("we can repeat the above argument"): a list on
`N` whose two pull-backs to a fibre product of `g` with itself agree descends to `M`. -/
theorem exists_pullback_eq_of_isFibreProduct {N : AnalyticManifold.{u} 𝕜 E}
    (L' : BlowUpSequence ψ₀ N) :
    ∀ {M P : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
      (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g), Function.Surjective g →
      ∀ (p₁ p₂ : AnalyticMap P N) (hp : IsFibreProduct g g p₁ p₂),
        L'.pullback p₁ hp.1 = L'.pullback p₂ hp.2.1 →
          ∃ L : BlowUpSequence ψ₀ M, L.pullback g hg = L' := by
  induction L' with
  | nil N => exact fun {M} _ _ _ _ _ _ _ _ => ⟨nil M, rfl⟩
  | @cons N Z' c hZ' rest' ih =>
    intro M P g hg hs p₁ p₂ hp hL'
    have hL₂ : cons (hZ'.preimage_of_isLocalDiffeomorph hp.1)
        (rest'.pullback (liftStep p₁ hp.1 hZ') (isLocalDiffeomorph_liftStep p₁ hp.1 hZ')) =
      cons (hZ'.preimage_of_isLocalDiffeomorph hp.2.1)
        (rest'.pullback (liftStep p₂ hp.2.1 hZ') (isLocalDiffeomorph_liftStep p₂ hp.2.1 hZ')) := hL'
    have hsat := saturated_of_isFibreProduct hp (cons.inj hL₂).1
    obtain ⟨Z, hZ, hsat'⟩ : ∃ (Z : Set M) (_ : IsClosedSubmanifold ψ₀ Z c), g ⁻¹' Z = Z' :=
      ⟨_, hZ'.image_of_saturated hg hs hsat, hsat⟩
    subst hsat'
    have h₁ := (cons.inj hL₂).2.2
    have h₂ := pullback_heq_of_comm hZ' (hZ'.preimage_of_isLocalDiffeomorph hp.2.1)
      (hZ'.preimage_of_isLocalDiffeomorph hp.1) (preimage_eq_of_isFibreProduct hp) rfl
      (liftStep p₂ hp.2.1 hZ') (liftedSndMap hg hp hZ) (isLocalDiffeomorph_liftStep p₂ hp.2.1 hZ')
      (isLocalDiffeomorph_liftedSnd hg hp hZ) (blowUpπ_liftStep p₂ hp.2.1 hZ')
      (blowUpπ_liftedSnd hg hp hZ) rest'
    have hrest : rest'.pullback (liftStep p₁ hp.1 hZ') (isFibreProduct_lifted hg hp hZ).1 =
        rest'.pullback (liftedSndMap hg hp hZ) (isFibreProduct_lifted hg hp hZ).2.1 :=
      eq_of_heq (h₁.trans h₂)
    obtain ⟨L₁, hL₁⟩ := ih (liftStep g hg hZ) (isLocalDiffeomorph_liftStep g hg hZ)
      (surjective_liftStep g hg hZ hs) (liftStep p₁ hp.1 hZ') (liftedSndMap hg hp hZ)
      (isFibreProduct_lifted hg hp hZ) hrest
    exact ⟨cons hZ L₁, congrArg (cons hZ') hL₁⟩

/-- [Kol07, Proposition 37], the descent step with its uniqueness: a list on the
cover whose two pull-backs to the fibre product agree is the pull-back of exactly one list on the
base (uniqueness by `pullback_injective_of_surjective`). -/
theorem exists_unique_pullback_eq_of_isFibreProduct {M N P : AnalyticManifold.{u} 𝕜 E}
    (g : AnalyticMap N M) (hg : IsCoprodOfOpenEmbeddings g) (hs : Function.Surjective g)
    (p₁ p₂ : AnalyticMap P N) (hp : IsFibreProduct g g p₁ p₂) (L' : BlowUpSequence ψ₀ N)
    (hL' : L'.pullback p₁ hp.1 = L'.pullback p₂ hp.2.1) :
    ∃! L : BlowUpSequence ψ₀ M, L.pullback g hg.1 = L' := by
  obtain ⟨L, hL⟩ := exists_pullback_eq_of_isFibreProduct L' g hg.1 hs p₁ p₂ hp hL'
  exact ⟨L, hL, fun L₂ hL₂ => pullback_injective_of_surjective g hg.1 hs L₂ L (hL₂.trans hL.symm)⟩

end AnalyticManifold.BlowUpSequence

end
