/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Concat
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2: the order drop along a concatenation

Step 2.2 of the proof of [Kol07, Theorem 103] ([Kol07, 104, Step 2.2]): at the end the cosupport
of the controlled transform of `(I, m)` misses the transform of `H` while, `H` being a
hypersurface of maximal contact, it lies in that transform, so it is empty. The order drop at the
end of Step 2.2 gives that at the end of the whole of Step 2 by the concatenation.

* `BlowUpSequence.forall_ord_lt_concat_of_forall` — the order drop along a concatenation.

The order drop for Step 2 on a relatively compact open is proved in `Step22FamOrdLt.lean`.
-/

public section

noncomputable section

open Set Topology AnalyticManifold IsLocalRing
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The order drop at the last stage of a concatenation `L.concat L'` follows from the order drop at
the last stage of `L'` for the weak transform reached by `L`; by induction on `L`, reading through
the first blow-up (`cons_weakTransformSeq_succ`). -/
theorem forall_ord_lt_concat_of_forall : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))) (I : IdealSheaf M) (s : ℕ),
    (∀ x, (L'.toSuccession.weakTransformSeq (L.toSuccession.weakTransformSeq I (Fin.last _))
      (Fin.last _)).ord x < (s : ℕ∞)) →
    ∀ x, ((L.concat L').toSuccession.weakTransformSeq I (Fin.last _)).ord x < (s : ℕ∞)
  | _, nil _, _, _, _, h => h
  | _, cons hY rest, L', I, s, h => by
    rw [concat_cons]
    have e1 : (cons hY rest).toSuccession.weakTransformSeq I
          (Fin.last (cons hY rest).toSuccession.length) =
        rest.toSuccession.weakTransformSeq
          (IdealSheaf.weakTransform (blowUpπ ψ₀ hY) I hY.idealSheaf)
          (Fin.last rest.toSuccession.length) :=
      FiniteSuccession.cons_weakTransformSeqAux_succ hY rest.toSuccession I rest.length
        (Fin.last (rest.length + 1)).2
    rw [e1] at h
    have e1' : (cons hY (rest.concat L')).toSuccession.weakTransformSeq I
          (Fin.last (cons hY (rest.concat L')).toSuccession.length) =
        (rest.concat L').toSuccession.weakTransformSeq
          (IdealSheaf.weakTransform (blowUpπ ψ₀ hY) I hY.idealSheaf)
          (Fin.last (rest.concat L').toSuccession.length) :=
      FiniteSuccession.cons_weakTransformSeqAux_succ hY (rest.concat L').toSuccession I
        (rest.concat L').length (Fin.last ((rest.concat L').length + 1)).2
    rw [e1']
    exact forall_ord_lt_concat_of_forall rest L' _ s h

end AnalyticManifold.BlowUpSequence

end
