/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BDFam
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BDLemmas
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Lemma 102 in the compatible-family form: the value at an empty member

At an empty member `E^j = ∅` the value of `BD_{n,m,j}` on every relatively compact open is the empty
sequence (`BDanFam_eq_nil_of_hyp_eq_empty`; the counterpart of `BDan_eq_nil_of_hyp_eq_empty` of
`BDLemmas.lean`). The centre `Z_{-1} ⊆ E^j` is empty, so its restriction to `U` is empty and the
first blow-up is deleted ([Kol07, 32]); the transform `S_0 = π_{-1}^{-1}(E^j)` is empty, so the
value of the input family on any open of it is a sequence without centres on an empty manifold,
hence the empty sequence, and so are its push-forward and its pull-back along the lift.

This is the hypothesis on the data that the commutation of Steps 2.1 and 2.2 with local analytic
isomorphisms requires of Lemma 102's family (`hnil` in `LocalFunctorFam.lean`), discharged for the
family built from the marked families in `BOanFamOfInput.lean`
(`bdanFamDataOfInput_fam_eq_nil_of_hyp_eq_empty`).
-/

public section

universe u

open Set Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {m : ℕ}

/-- At an empty member the value of `BD_{n,m,j}` on every relatively compact open is the empty
sequence ([Kol07, 32]): the centre `Z_{-1} ∩ U` is empty and deleted, and the transform `S_0` of
`E^j` is empty, so the input family's value on it has no centres. -/
theorem BDanFam_eq_nil_of_hyp_eq_empty (inp : BMOanFam 𝕜 (n - 1) (tuningParam m))
    (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass m T) (j : T.F.ι) (hj : T.F.hyp j = ∅)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    BDanFam m inp T hT j U hU = AnalyticManifold.BlowUpSequence.nil (M.restrict U) := by
  have hZ : BD.Zminus1 (T.tuned m hT.1).I (tuningParam m) ((T.tuned m hT.1).F.hyp j) = ∅ := by
    have hsub := BD.Zminus1_subset (T.tuned m hT.1) (tuningParam m) j
    have hj' : (T.tuned m hT.1).F.hyp j = ∅ := hj
    refine Set.eq_empty_of_subset_empty fun x hx => ?_
    have hx' := hsub hx
    rw [hj'] at hx'
    exact hx'
  have hZU : ⇑(M.inclusion U) ⁻¹'
      BD.Zminus1 (T.tuned m hT.1).I (tuningParam m) ((T.tuned m hT.1).F.hyp j) = ∅ := by
    rw [hZ, Set.preimage_empty]
  have hnil : ∀ (W : Opens (BDan.isClosedSubmanifold_transformS (T.tuned m hT.1) (tuningParam m)
        j).toAnalyticManifold)
      (hW : IsCompact (closure (W : Set (BDan.isClosedSubmanifold_transformS (T.tuned m hT.1)
        (tuningParam m) j).toAnalyticManifold))),
      (inp.functor.fam (BDan.restrictedTriple (T.tuned m hT.1) (tuningParam m) j
          ⟨AnalyticTriple.boClass_tuned hT, AnalyticTriple.isDBalanced_tuned hT⟩)
        (BDan.bmoClass_restrictedTriple (T.tuned m hT.1) (tuningParam m) j
          ⟨AnalyticTriple.boClass_tuned hT, AnalyticTriple.isDBalanced_tuned hT⟩)).seqOn W hW =
        AnalyticManifold.BlowUpSequence.nil _ := by
    intro W hW
    refine AnalyticManifold.BlowUpSequence.eq_nil_of_noEmptyCenters_of_isEmpty _
      ((inp.functor.fam _ _).noEmptyCenters _ _) ?_
    intro x
    have hx : BDan.piMinusOne (T.tuned m hT.1) (tuningParam m) j x.1.1 ∈ T.F.hyp j := x.1.2
    rw [hj] at hx
    exact hx
  unfold BDanFam BDan.coreFamOn
  rw [hnil, AnalyticManifold.BlowUpSequence.eraseEmpty_cons_of_eq_empty _ _ hZU]
  simp only [AnalyticManifold.BlowUpSequence.pushforwardRestrict,
      AnalyticManifold.BlowUpSequence.pushforwardRestrictOf,
    AnalyticManifold.BlowUpSequence.pushforwardAux]
  erw [AnalyticManifold.BlowUpSequence.pullback_nil,
      AnalyticManifold.BlowUpSequence.eraseEmpty_nil, AnalyticManifold.BlowUpSequence.map_nil]

end Hironaka.Manifold
