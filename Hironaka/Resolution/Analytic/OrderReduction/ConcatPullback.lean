/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Concat
public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BDCosupp
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Pull-back of a concatenation, and the transforms at the last stage along the lift

The pull-back of a blow-up sequence along a smooth morphism `h` is formed stage by stage
([Kol07, Definition 30], 30.1), the morphism lifting through each blow-up to the next stage. For
sequences of centres this module gives the lift `h_r` of a local analytic isomorphism `h : N → M`
to the last stages, shows that the pull-back of a concatenation `L.concat L'` is the concatenation
of the pull-back of `L` and the pull-back of `L'` along `h_r`, and shows that along `h_r` the
controlled transform of `(𝓘, m)` and the boundary family from a start `F` pull back.

* `BlowUpSequence.pullbackLiftLast`, `isLocalDiffeomorph_pullbackLiftLast`,
  `surjective_pullbackLiftLast` — the lift of `h` to the last stages, typed on the last stages
  directly (the stage-indexed lift `pullbackLift` carries the length identity in its index).
* `BlowUpSequence.pullback_concat` — the pull-back of a concatenation.
* `HypersurfaceFamily.totalTransform_comap_liftStep`,
  `BlowUpSequence.totalTransformSeqFrom_last_pullbackLiftLast` — the boundary family from `F` at the
  last stage of `h^* L` is the pull-back along `h_r` of the family at the last stage of `L`.
* `BlowUpSequence.markedTransformSeq_last_pullbackLiftLast` — the controlled transform at the last
stage of
  `h^* L` is the pull-back along `h_r`, for `L` of order `≥ m`.

These are the transport lemmas behind the functoriality of Steps 2.1 and 2.2 of the proof of
[Kol07, Theorem 103] (`Step21Functoriality.lean`, `Step22Pullback.lean`), where each step of the
construction is pulled back along the lift to the last stage of the previous one. Not in the
sources; bookkeeping.
-/

@[expose] public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- The total transform of `h⁻¹(F)` under the blow-up of `h⁻¹(Y)` is the pull-back along the lift
`liftStep` of the total transform of `F` under the blow-up of `Y` ([Kol07, Definition 25]): the
strict transforms pull back (`strictTransformSet_preimage_liftStep`), and the exceptional divisor
lies over the exceptional divisor. -/
theorem HypersurfaceFamily.totalTransform_comap_liftStep (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (F : HypersurfaceFamily M) :
    (F.comap h).totalTransform (blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)) (⇑h ⁻¹' Y) =
      (F.totalTransform (blowUpπ ψ₀ hY) Y).comap (BlowUpSequence.liftStep h hh hY) := by
  unfold HypersurfaceFamily.totalTransform HypersurfaceFamily.comap
  congr 1
  funext k
  obtain ⟨k', rfl⟩ : ∃ k', toLex k' = k := ⟨ofLex k, rfl⟩
  rcases k' with j | u
  · exact BlowUpSequence.strictTransformSet_preimage_liftStep h hh hY (F.hyp j)
  · ext q
    change q ∈ ⇑(blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)) ⁻¹' (⇑h ⁻¹' Y) ↔
      q ∈ ⇑(BlowUpSequence.liftStep h hh hY) ⁻¹' (⇑(blowUpπ ψ₀ hY) ⁻¹' Y)
    simp only [Set.mem_preimage, BlowUpSequence.blowUpπ_liftStep]

end Manifold

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- The lift `h_r` of a local analytic isomorphism `h : N → M` to the last stages of `h^* L` and `L`
([Kol07, Definition 30], 30.1), by recursion on the sequence of centres, typed on the last stages
directly. -/
def pullbackLiftLast : {M N : AnalyticManifold.{u} 𝕜 E} → (L : BlowUpSequence ψ₀ M) →
    (h : AnalyticMap N M) → (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) →
    AnalyticMap ((L.pullback h hh).stage (Fin.last _)) (L.stage (Fin.last _))
  | _, _, nil _, h, _ => h
  | _, _, cons hY rest, h, hh =>
    rest.pullbackLiftLast (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)

theorem pullbackLiftLast_nil (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    (nil (ψ₀ := ψ₀) M).pullbackLiftLast h hh = h := rfl

/-- The lift to the last stages is a local analytic isomorphism. -/
theorem isLocalDiffeomorph_pullbackLiftLast : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (L.pullbackLiftLast h hh)
  | _, _, nil _, _, hh => hh
  | _, _, cons hY rest, h, hh =>
    isLocalDiffeomorph_pullbackLiftLast rest (liftStep h hh hY)
      (isLocalDiffeomorph_liftStep h hh hY)

/-- The lift to the last stages of a surjective local analytic isomorphism is surjective. -/
theorem surjective_pullbackLiftLast : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    Function.Surjective h → Function.Surjective (L.pullbackLiftLast h hh)
  | _, _, nil _, _, _, hs => hs
  | _, _, cons hY rest, h, hh, hs =>
    surjective_pullbackLiftLast rest (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)
      (surjective_liftStep h hh hY hs)

/-- The pull-back of a concatenation is the concatenation of the pull-backs, the second along the
lift of `h` to the last stage of `L` ([Kol07, Definition 30], 30.1, for a composite sequence). -/
theorem pullback_concat : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    (L.concat L').pullback h hh =
      (L.pullback h hh).concat
        (L'.pullback (L.pullbackLiftLast h hh) (isLocalDiffeomorph_pullbackLiftLast L h hh))
  | _, _, nil _, _, _, _ => rfl
  | _, _, cons hY rest, L', h, hh =>
    congrArg (cons (hY.preimage_of_isLocalDiffeomorph hh))
      (pullback_concat rest L' (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY))

/-- The boundary family from `h⁻¹(F)` at the last stage of `h^* L` is the pull-back along the lift
`h_r` of the boundary family from `F` at the last stage of `L`
(`totalTransform_comap_liftStep` at each step). -/
theorem totalTransformSeqFrom_last_pullbackLiftLast : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (F : HypersurfaceFamily M),
    (L.pullback h hh).toSuccession.totalTransformSeqFrom (F.comap h) (Fin.last _) =
      (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).comap (L.pullbackLiftLast h hh)
  | _, _, nil _, _, _, _ => rfl
  | _, _, cons hY rest, h, hh, F => by
    have e1 : ((cons hY rest).pullback h hh).toSuccession.totalTransformSeqFrom (F.comap h)
          (Fin.last _) =
        (rest.pullback (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY)).toSuccession.totalTransformSeqFrom
          ((F.comap h).totalTransform (blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh))
            (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf.support) (Fin.last _) :=
      FiniteSuccession.cons_totalTransformSeqFromAux_succ (hY.preimage_of_isLocalDiffeomorph hh)
        (rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)).toSuccession
        (F.comap h) _ (Fin.last _).2
    have e2 : (cons hY rest).toSuccession.totalTransformSeqFrom F (Fin.last _) =
        rest.toSuccession.totalTransformSeqFrom
          (F.totalTransform (blowUpπ ψ₀ hY) hY.idealSheaf.support) (Fin.last _) :=
      FiniteSuccession.cons_totalTransformSeqFromAux_succ hY rest.toSuccession F _ (Fin.last _).2
    rw [e1, e2, hY.cosupport_idealSheaf,
      (hY.preimage_of_isLocalDiffeomorph hh).cosupport_idealSheaf,
      HypersurfaceFamily.totalTransform_comap_liftStep h hh hY F]
    exact totalTransformSeqFrom_last_pullbackLiftLast rest (liftStep h hh hY) _ _

/-- The controlled transform of `(h^* 𝓘, m)` at the last stage of `h^* L` is the pull-back along the
lift `h_r` of the controlled transform of `(𝓘, m)` at the last stage of `L`, for `L` of order `≥ m`
(`birationalTransform_comap_liftStep` at each step). -/
theorem markedTransformSeq_last_pullbackLiftLast :
    ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (I E₀ : IdealSheaf M)
        (m : ℕ),
    L.toSuccession.IsOfOrderGe I m E₀ →
    (L.pullback h hh).toSuccession.markedTransformSeq (I.pullback h h.contMDiff) m
        (Fin.last _) =
      (L.toSuccession.markedTransformSeq I m (Fin.last _)).pullback _ (L.pullbackLiftLast h
          hh).contMDiff
  | _, _, nil _, _, _, _, _, _, _ => rfl
  | _, _, cons hY rest, h, hh, I, E₀, m, hge => by
    have := finiteDimensional_of_chartIso ψ₀
    obtain ⟨⟨-, hm⟩, hrest⟩ := (FiniteSuccession.isOfOrderGe_cons_iff (I := I) (m := m) (E₀ := E₀)
      hY rest.toSuccession).mp hge
    have e1 : ((cons hY rest).pullback h hh).toSuccession.markedTransformSeq
          (I.pullback h h.contMDiff) m (Fin.last _) =
        (rest.pullback (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY)).toSuccession.markedTransformSeq
          ((FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
            (rest.pullback (liftStep h hh hY)
              (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).markedTransformSeq
            (I.pullback h h.contMDiff) m
            (Fin.succ (0 : Fin ((rest.pullback (liftStep h hh hY)
              (isLocalDiffeomorph_liftStep h hh hY)).toSuccession.length + 1)))) m (Fin.last _) :=
      FiniteSuccession.cons_markedTransformSeqAux_succ (hY.preimage_of_isLocalDiffeomorph hh)
        (rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)).toSuccession
        (I.pullback h h.contMDiff) m _ (Fin.last _).2
    have e2 : (cons hY rest).toSuccession.markedTransformSeq I m (Fin.last _) =
        rest.toSuccession.markedTransformSeq
          ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).markedTransformSeq I m
            (Fin.succ (0 : Fin (rest.toSuccession.length + 1)))) m (Fin.last _) :=
      FiniteSuccession.cons_markedTransformSeqAux_succ hY rest.toSuccession I m _ (Fin.last _).2
    have e3 : (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).markedTransformSeq
          (I.pullback h h.contMDiff) m
              (Fin.succ (0 : Fin ((rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession.length + 1))) =
        ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).markedTransformSeq I m
            (Fin.succ (0 : Fin (rest.toSuccession.length + 1)))).pullback _ (liftStep h hh
                hY).contMDiff := by
      rw [FiniteSuccession.cons_markedTransformSeq_one,
        FiniteSuccession.cons_markedTransformSeq_one]
      exact (Hironaka.Manifold.birationalTransform_comap_liftStep h hh hY ⟨I, m⟩ hm).symm
    rw [e1, e2, e3]
    exact markedTransformSeq_last_pullbackLiftLast rest (liftStep h hh hY) _ _ _ m hrest

end AnalyticManifold.BlowUpSequence

end
