/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.ConcatPullback
public import Hironaka.Resolution.Analytic.OrderReduction.Step22Defs
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Resolution.Analytic.MaximalContactLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BDCosupp
public import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
public import Hironaka.Resolution.Algebraic.Tuning.Parameter
import Hironaka.Manifold.FiniteSuccession.CenterList

/-!
# The triple of Step 2.2 over a first sequence, and its pull-back

The functoriality of Step 2.2 of the proof of [Kol07, Theorem 103] is that of Lemma 102
([Kol07, 104, Step 2.3]). The triple of Step 2.2 is built on the last stage of the first sequence
(the sequence of Step 2.1), so it is defined over an arbitrary first sequence (`step22TripleOf`),
the dependent types being handled as in `BDOf.lean`. For the pulled-back data over the pulled-back
first sequence it is the pull-back of the triple of Step 2.2 along the lift to the last stage: the
controlled transform, the exceptional divisors and the transform of `H` all pull back along the
lift (`ConcatPullback.lean`).

* `HypersurfaceFamily.append_comap`, `HypersurfaceFamily.empty_comap`,
  `BlowUpSequence.strictTransformSeq_last_pullbackLiftLast` — the pieces of the boundary pull back.
* `BO.transformHOf`, `BO.exceptionalOf`, `BO.step22TripleOf`, `BO.stepHClass_step22TripleOf_congr`
  — the data of Step 2.2 over an arbitrary first sequence.
* `BO.step22TripleOf_isPullbackOf` — the triple of Step 2.2 of the pull-back.

Step 2.2 in the compatible-family form (`Step22Fam.lean`) is built on these data.
-/

@[expose] public section

noncomputable section

open Set Topology AnalyticManifold Hironaka.Local
open scoped Manifold ContDiff

universe u

namespace Manifold

/-- Appending a hypersurface commutes with the inverse image of a family. -/
theorem HypersurfaceFamily.append_comap {M N : Type u} (F : HypersurfaceFamily M) (H : Set M)
    (g : N → M) : (F.append H).comap g = (F.comap g).append (g ⁻¹' H) := by
  unfold HypersurfaceFamily.append HypersurfaceFamily.comap
  congr 1
  funext k
  obtain ⟨k', rfl⟩ : ∃ k', toLex k' = k := ⟨ofLex k, rfl⟩
  rcases k' with j | u <;> rfl

/-- The inverse image of the empty family is the empty family. -/
theorem HypersurfaceFamily.empty_comap {M N : Type u} (g : N → M) :
    (HypersurfaceFamily.empty M).comap g = HypersurfaceFamily.empty N := by
  unfold HypersurfaceFamily.empty HypersurfaceFamily.comap
  congr 1
  funext j
  exact j.elim

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

end Manifold

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The strict transform of `h⁻¹(H)` at the last stage of `h^* L` is the preimage under the lift
`h_r` of the strict transform of `H` at the last stage of `L`. -/
theorem strictTransformSeq_last_pullbackLiftLast : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (H : Set M),
    (L.pullback h hh).toSuccession.strictTransformSeq (⇑h ⁻¹' H) (Fin.last _) =
      ⇑(L.pullbackLiftLast h hh) ⁻¹' (L.toSuccession.strictTransformSeq H (Fin.last _))
  | _, _, nil _, _, _, _ => rfl
  | _, _, cons hY rest, h, hh, H => by
    have e1 : ((cons hY rest).pullback h hh).toSuccession.strictTransformSeq (⇑h ⁻¹' H)
          (Fin.last _) =
        (rest.pullback (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY)).toSuccession.strictTransformSeq
          (strictTransformSet (blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh))
            (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf.support (⇑h ⁻¹' H))
          (Fin.last _) :=
      FiniteSuccession.cons_strictTransformSeqAux_succ (hY.preimage_of_isLocalDiffeomorph hh)
        (rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)).toSuccession
        (⇑h ⁻¹' H) _ (Fin.last _).2
    have e2 : (cons hY rest).toSuccession.strictTransformSeq H (Fin.last _) =
        rest.toSuccession.strictTransformSeq
          (strictTransformSet (blowUpπ ψ₀ hY) hY.idealSheaf.support H) (Fin.last _) :=
      FiniteSuccession.cons_strictTransformSeqAux_succ hY rest.toSuccession H _ (Fin.last _).2
    rw [e1, e2, hY.cosupport_idealSheaf,
      (hY.preimage_of_isLocalDiffeomorph hh).cosupport_idealSheaf,
      strictTransformSet_preimage_liftStep h hh hY H]
    exact strictTransformSeq_last_pullbackLiftLast rest (liftStep h hh hY) _ _

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {s : ℕ}

namespace BO

open _root_.Manifold

variable (T : AnalyticTriple ψ₀ M)

/-! ### The data of Step 2.2 parametrized by the first sequence -/

section Of

variable (L : BlowUpSequence ψ₀ M) (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)

/-- The birational transform `H_r` of `H` at the last stage of an arbitrary first sequence `L`. -/
def transformHOf (H : Set M) : Set (L.stage (Fin.last _)) :=
  L.toSuccession.strictTransformSeq H (Fin.last _)

/-- The family of exceptional divisors at the last stage of an arbitrary first sequence `L` (from
the empty start). -/
def exceptionalOf : HypersurfaceFamily (L.stage (Fin.last _)) :=
  L.toSuccession.totalTransformSeq (Fin.last _)

variable {H : Set M}

/-- The triple `(X_r, I_r, E_r^{exc} + H_r)` of Step 2.2 over an arbitrary first sequence `L` (the
normal-crossings proof as a hypothesis). -/
def step22TripleOf (hsnc : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀) :
    AnalyticTriple ψ₀ (L.stage (Fin.last _)) where
  I := L.toSuccession.markedTransformSeq T.I s (Fin.last _)
  isNonzeroEverywhere := isNonzeroEverywhere_markedTransformSeq T.isNonzeroEverywhere hL _
  F := (exceptionalOf L).append (transformHOf L H)
  isSnc := hsnc

end Of

variable (hT : AnalyticTriple.BOClass s T) {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1)
  (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))

omit [FiniteDimensional 𝕜 E] in
/-- The class of Step 2.2 for the parametrized triple depends only on the first sequence. -/
theorem stepHClass_step22TripleOf_congr {L₁ L₂ : BlowUpSequence ψ₀ M} (e : L₁ = L₂)
    (hL₁ : L₁.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hL₂ : L₂.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hsnc₁ : ((exceptionalOf L₁).append (transformHOf L₁ H)).IsSnc ψ₀)
    (hsnc₂ : ((exceptionalOf L₂).append (transformHOf L₂ H)).IsSnc ψ₀)
    (hcls : stepHClass s (step22TripleOf T L₁ hL₁ hsnc₁)) :
    stepHClass s (step22TripleOf T L₂ hL₂ hsnc₂) := by
  subst e
  exact hcls

omit [FiniteDimensional 𝕜 E] in
/-- The triple of Step 2.2 for the pulled-back data over the pulled-back first sequence is the
pull-back of the triple of Step 2.2 along the lift `h_r` to the last stage
([Kol07, 104, Step 2.3]): the controlled transform, the exceptional divisors and the transform of
`H`
pull back along the lift. -/
theorem step22TripleOf_isPullbackOf {N : AnalyticManifold.{u} 𝕜 E} (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (L : BlowUpSequence ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hL' : (L.pullback h hh).toSuccession.IsOfOrderGe (T.pullback h hh).I s
      (T.pullback h hh).F.idealSheaf)
    (hsnc : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀)
    (hsnc' : ((exceptionalOf (L.pullback h hh)).append
      (transformHOf (L.pullback h hh) (⇑h ⁻¹' H))).IsSnc ψ₀) :
    (step22TripleOf (T.pullback h hh) (L.pullback h hh) hL' hsnc').IsPullbackOf
      (step22TripleOf T L hL hsnc) (L.pullbackLiftLast h hh) := by
  refine ⟨?_, ?_⟩
  · exact BlowUpSequence.markedTransformSeq_last_pullbackLiftLast L h hh T.I T.F.idealSheaf s hL
  · change ((L.pullback h hh).toSuccession.totalTransformSeqFrom (HypersurfaceFamily.empty _)
        (Fin.last _)).append
          ((L.pullback h hh).toSuccession.strictTransformSeq (⇑h ⁻¹' H) (Fin.last _)) =
      ((L.toSuccession.totalTransformSeqFrom (HypersurfaceFamily.empty _) (Fin.last _)).append
        (L.toSuccession.strictTransformSeq H (Fin.last _))).comap ⇑(L.pullbackLiftLast h hh)
    rw [← HypersurfaceFamily.empty_comap ⇑h,
      BlowUpSequence.totalTransformSeqFrom_last_pullbackLiftLast,
      BlowUpSequence.strictTransformSeq_last_pullbackLiftLast, HypersurfaceFamily.append_comap]

end BO

end Hironaka.Manifold

end
