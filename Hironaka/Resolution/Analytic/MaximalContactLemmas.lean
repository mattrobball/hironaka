/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictTransformSeq
public import Hironaka.Manifold.FiniteSuccession.Cons
import Hironaka.Manifold.BlowUp.Transform.Object
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The strict transforms on `cons`

The recursion of the strict transforms `H_0 = H`, `H_{i+1} =` closure of `π_i⁻¹(H_i ∖ Z_i)`
along a sequence (`strictTransformSeq`, the "birational transform `H⁰_i` of `H⁰`" of
[Kol07, Definition 78]) restarts, on the constructor form `cons ψ hY rest`, from the strict
transform of `H` by the first blow-down, with centre `Y`: an induction on the stage
(`cons_strictTransformSeqAux_succ`, `rfl` at every step because `cons` puts the head before the
fields of `rest` by `Fin.cases` over `finStages`), with `Z_0 = cosupp I_Y = Y`.
-/

public section

noncomputable section

open TopologicalSpace Manifold Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}

/-- The strict transforms of `H` along `cons ψ hY rest` after the first step are those of `rest`
starting from the strict transform of `H` by the first blow-down, with centre `cosupp I_Y`. -/
theorem cons_strictTransformSeqAux_succ (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (H : Set M) :
    ∀ (k : ℕ) (h : k + 1 < (cons ψ hY rest).length + 1),
      (cons ψ hY rest).strictTransformSeqAux H (k + 1) h =
        rest.strictTransformSeqAux
          (strictTransformSet (blowUpπ ψ hY) hY.idealSheaf.support H) k
          (Nat.lt_of_succ_lt_succ h)
  | 0, _ => rfl
  | k + 1, h => by
    change strictTransformSet ((cons ψ hY rest).map ⟨k + 1, _⟩)
      ((cons ψ hY rest).center ⟨k + 1, _⟩).support
      ((cons ψ hY rest).strictTransformSeqAux H (k + 1) (Nat.lt_of_succ_lt h)) = _
    rw [cons_strictTransformSeqAux_succ hY rest H k (Nat.lt_of_succ_lt h)]
    rfl

/-- The recursion of the strict transforms on the constructor form, indexed by `Fin` and with
`Z_0 = Y`. -/
theorem cons_strictTransformSeq_succ (H : Set M) (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (j : Fin (rest.length + 1)) :
    (cons ψ hY rest).strictTransformSeq H j.succ =
      rest.strictTransformSeq (strictTransformSet (blowUpπ ψ hY) Y H) j := by
  have h := cons_strictTransformSeqAux_succ hY rest H j.1 j.succ.2
  rw [hY.cosupport_idealSheaf] at h
  exact h

end AnalyticManifold.FiniteSuccession

end
