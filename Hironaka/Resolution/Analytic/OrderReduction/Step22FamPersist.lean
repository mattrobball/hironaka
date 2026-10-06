/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step22Fam
import Hironaka.Manifold.FiniteSuccession.DerivTransform
import Hironaka.Resolution.Analytic.MaximalContactTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Maximal contact persists along a sequence of order `≥ s`

Step 2 of the proof of [Kol07, Theorem 103] notes that under a smooth blow-up of order `m` the
birational transform of a smooth hypersurface of maximal contact "is again a smooth hypersurface of
maximal contact", and its Warning ([Kol07, 104]) insists on using these transforms rather than new
hypersurfaces. `maximalContact_persistsFam` states this for a triple of the class `BOClass s` and
an arbitrary sequence of order `≥ s` for it, the form in which the chain of Step 2.1 supplies its
sequence: the transform `H_r` of a hypersurface of maximal contact `H` is a hypersurface of
maximal contact for the controlled transform `I_r`, that is, the ideal sheaf of `H_r` lies in
`D^{s-1} I_r`. The sequence is of order exactly `s` (`isOfOrderOf`), so the ideal sheaf of `H_r`
lies in the controlled transform of `(D^{s-1} 𝓘, 1)` ([Kol07, Theorem 80 (1)]), which lies in
`D^{s-1}` of the controlled transform of `(𝓘, s)` ([Kol07, Corollary 77]).

The statement enters the order clause of Step 2.2 on an open (`Step22FamOrdLt.lean`).
-/

public section

universe u

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {s : ℕ}

/-- Maximal contact persists along any sequence of order `≥ s` for a triple of the class `BOClass s`
(Step 2 of the proof of [Kol07, Theorem 103]; [Kol07, Theorem 80 (1)]): the transform `H_r` of a
hypersurface of maximal contact `H` is a hypersurface of maximal contact for the controlled
transform `I_r`. The sequence is of order exactly `s` (`isOfOrderOf`), the ideal sheaf of `H_r` lies
in the controlled transform of `(D^{s-1} 𝓘, 1)`
(`idealSheaf_strictTransformSeq_le_markedTransformSeq`), and that lies in `D^{s-1} I_r`
(`markedTransformSeq_iteratedDeriv_le`, [Kol07, Corollary 77]). -/
theorem maximalContact_persistsFam (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass s T) (L : AnalyticManifold.BlowUpSequence ψ₀ M)
    (hge : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) {H : Set M}
    (hH : IsClosedSubmanifold ψ₀ H 1) (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1)) :
    (BO.isClosedSubmanifold_transformHOf T s L hT hge hH hle).idealSheaf ≤
      (BO.step22TripleOf T L hge (BO.isSnc_step22BoundaryOf T s L hT hge hH hle)).I.iteratedDeriv
        (s - 1) := by
  have h1 := (BO.isOfOrderOf T s L hT hge).idealSheaf_strictTransformSeq_le_markedTransformSeq
    hT.1 hH hle (Fin.last _) (BO.isClosedSubmanifold_transformHOf T s L hT hge hH hle)
  have h2 := hge.markedTransformSeq_iteratedDeriv_le (Nat.sub_le s 1) (Fin.last _)
  rw [Nat.sub_sub_self hT.1] at h2
  exact h1.trans h2

end Hironaka.Manifold
