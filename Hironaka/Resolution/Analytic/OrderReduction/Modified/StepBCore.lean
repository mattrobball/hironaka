/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBRestrict
public import Hironaka.Resolution.Analytic.OrderReduction.ClosedEmbeddingFam
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The modified first step: the run one dimension down on `H⁺`, pushed forward

The modified first step of [Wlo09, Theorem 7.4.1] restricts `(I′, 1) = C(H(I))` to a hypersurface
of maximal contact `V(u₁)` and repeats the modified algorithm for the restriction `I′|_{V(u₁)}`.
This is the core of the proof of [Kol07, Lemma 102]
("consider the triple `(S, I_0|_S, E_S)` … push it forward"; `BDan.coreFamOn`) **without** the first
blow-up of `Z_{-1}` (the stop, `StepBRestrict.lean`): on a relatively compact open `U`, the value of
the modified functor one dimension down, `R`, on the restricted triple `restrictedTripleMod T j`
over the trace `U ∩ H⁺`, pushed forward to `U` (`pushforwardRestrict`, the push-forward of
[Kol07, Definition 30, 30.3] on each open), with its empty blow-ups deleted [Kol07, 32]: this is
`coreModOn`. The functor `R` enters only through its values. The properties of a compatible family
hold: no empty centres, and compatibility under restriction (`coreModOn_compat`: the compatibility
of `R` on the traces, the push-forward commuting with the open inclusions,
`pushforwardRestrict_pullback_restrictLE`, `eraseEmpty_pushforwardRestrict_eraseEmpty`).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
  (R : AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (AnalyticTriple.BMOClass 1))
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (j : T.F.ι)
  (hT : AnalyticTriple.BMOClass 1 T)

/-! ### The trace of an open on `H⁺` and the lower-dimensional value there -/

/-- The value of the modified functor one dimension down on the restricted triple over the trace
`U ∩ H⁺` of a relatively compact open `U` ("repeated for the restriction",
[Wlo09, Theorem 7.4.1]). -/
def coreModTrace (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      ((isClosedSubmanifold_hplus T j).toAnalyticManifold.restrict
        ((isClosedSubmanifold_hplus T j).preimageOpens U)) :=
  (R.fam (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT)).seqOn
    ((isClosedSubmanifold_hplus T j).preimageOpens U)
    ((isClosedSubmanifold_hplus T j).isCompact_closure_preimageOpens U hU)

/-- The compatibility of `R` on the traces: the value over `U ∩ H⁺` is the value over `V ∩ H⁺`
restricted and cleaned. -/
theorem coreModTrace_compat {U V : Opens M} (hU : IsCompact (closure (U : Set M)))
    (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V) :
    coreModTrace R T j hT U hU =
      ((coreModTrace R T j hT V hV).pullback
        ((isClosedSubmanifold_hplus T j).toAnalyticManifold.restrictLE
          ((isClosedSubmanifold_hplus T j).preimageOpens_mono hUV))
        (isLocalDiffeomorph_restrictLE _)).eraseEmpty :=
  (R.fam (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT)).compat _ _ _ _ _

/-! ### The modified core -/

/-- **The modified core on `U`** ([Wlo09, Theorem 7.4.1]; the counterpart of `BDan.coreFamOn`
without the first blow-up): the run one dimension down on the restricted triple over the trace
`U ∩ H⁺`, pushed forward to `U` (`pushforwardRestrict`), with its empty blow-ups deleted
[Kol07, 32]. Nothing happens over the stopped components `Z_{-1}` ("the algorithm is
stopped"). -/
def coreModOn (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict U) :=
  (AnalyticManifold.BlowUpSequence.pushforwardRestrict (isClosedSubmanifold_hplus T j) U
    (coreModTrace R T j hT U hU)).eraseEmpty

/-- The modified core read on a closed hypersurface `S = H⁺` (a substitution). -/
theorem coreModOn_eq_of_eq {S : Set M}
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) S 1)
    (hSeq : S = hplus T j) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    coreModOn R T j hT U hU =
      (AnalyticManifold.BlowUpSequence.pushforwardRestrict hS U
        ((R.fam (restrictedTripleModOf T j hS hSeq)
            (bmoClass_restrictedTripleModOf T j hT hS hSeq)).seqOn
          (hS.preimageOpens U) (hS.isCompact_closure_preimageOpens U hU))).eraseEmpty := by
  subst hSeq
  rfl

/-- The value of the modified core has no empty centres [Kol07, 32]. -/
theorem noEmptyCenters_coreModOn (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (coreModOn R T j hT U hU).NoEmptyCenters :=
  AnalyticManifold.BlowUpSequence.noEmptyCenters_eraseEmpty _

/-- The compatibility of the modified core ([Wlo09, Theorem 2.0.3 (4)], [Wlo09, Definition 3.2.6]):
**the value on `U ≤ V` is the value on `V` restricted to `U` and cleaned**, from the compatibility
of `R` on the traces, the push-forward commuting with the open inclusions
(`pushforwardRestrict_pullback_restrictLE`), and the deletion of empty blow-ups moved through the
push-forward (`eraseEmpty_pushforwardRestrict_eraseEmpty`). -/
theorem coreModOn_compat {U V : Opens M} (hU : IsCompact (closure (U : Set M)))
    (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V) :
    coreModOn R T j hT U hU =
      ((coreModOn R T j hT V hV).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  unfold coreModOn
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
    AnalyticManifold.BlowUpSequence.pushforwardRestrict_pullback_restrictLE
        (isClosedSubmanifold_hplus T j) hUV,
    coreModTrace_compat R T j hT hU hV hUV,
    AnalyticManifold.BlowUpSequence.eraseEmpty_pushforwardRestrict_eraseEmpty]

/-- The modified core as a compatible family of the triple `T`, in the shape the link of the
maximal-contact step takes. -/
def coreModFam : CompatibleFamily T where
  seqOn U hU := coreModOn R T j hT U hU
  noEmptyCenters U hU := noEmptyCenters_coreModOn R T j hT U hU
  compat _ _ hU hV hUV := coreModOn_compat R T j hT hU hV hUV

@[simp] theorem coreModFam_seqOn (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (coreModFam R T j hT).seqOn U hU = coreModOn R T j hT U hU := rfl

end Hironaka.Manifold.BMOmod

end
