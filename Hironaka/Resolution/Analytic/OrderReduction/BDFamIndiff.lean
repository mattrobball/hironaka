/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BDFam
public import Hironaka.Resolution.Analytic.OrderReduction.BDIndiff
public import Hironaka.Resolution.Analytic.OrderReduction.BDOf
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Lemma 102 in the compatible-family form: indifference to empty boundary members

The value of `BD_{n,m,j}` on a relatively compact open does not see empty members of the boundary
(`BDanFam_indifferentToEmptyMembers`; the counterpart of `BDan_indifferentToEmptyMembers` of
`BDIndiff.lean`; for boundary members the counterpart of Kollár's convention that empty
blow-ups are ignored, [Kol07, 32]): when `F'` is `E` with empty members deleted along an order
embedding `e`,
the value at the member `e i` of `E` equals the value at the member `i` of `F'`, on every open. As
in `BDIndiff.lean`, the core on an open is first written over an arbitrary centre and transform
(`coreFamOn_eq_of_eq`, the counterpart of `core_eq_of_eq`; the centre and the transform at `e i` and
at `i` agree as sets by `Zminus1_eq_of_hyp_eq` and `transformS_eq_transformSOf`, so both sides live
on the same data), and then the input family's own indifference identifies the two values read at
the trace of `π_{-1}^{-1}(U)`: the restricted boundary of `E - E^{e i}` embeds that of `F' - F'^i`
along `e`, with empty members outside the range.

* `coreFamOn_eq_of_eq` — the core on an open over an arbitrary closed hypersurface `Z` and a
  closed hypersurface `S'` of its blowing-up (with `piOpenOf`, `liftInclOf` of `BDFam.lean`);
* `coreFamOn_indifferentToEmptyMembers`, `BDanFam_indifferentToEmptyMembers`.

This is the `indifferentToEmptyMembers` field of Lemma 102's family data `bdanFamDataOfInput` in
`BOanFamOfInput.lean`.
-/

public section

universe u

open Set Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace BDan

open _root_.Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ)
  (j : T.F.ι)

/-! ### The core on an open over an arbitrary centre and transform -/

section Of

variable {Z : Set M} (hZ : IsClosedSubmanifold ψ₀ Z 1) {S' : Set (Manifold.blowUp ψ₀ hZ)}
  (hS' : IsClosedSubmanifold ψ₀ S' 1)

/-- The core on an open (`coreFamOn`, `BDFam.lean`) read over any closed hypersurface `Z = Z_{-1}`
and any closed hypersurface `S' = S_0` of its blowing-up (a substitution; the counterpart of
`core_eq_of_eq` in `BDOf.lean`). -/
theorem coreFamOn_eq_of_eq (inp : BMOanFam 𝕜 (n - 1) s) (hT : BDClass s T)
    (hZeq : Z = BD.Zminus1 T.I s (T.F.hyp j)) (hSeq : S' = transformSOf T j hZ) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    coreFamOn T s j inp hT U hU =
      (AnalyticManifold.BlowUpSequence.cons (hZ.preimage_of_isLocalDiffeomorph
          (isLocalDiffeomorph_inclusion M U))
        ((AnalyticManifold.BlowUpSequence.pushforwardRestrict hS' (piOpenOf hZ U)
          ((inp.functor.fam (restrictedTripleOf T s j hZ hS' hT hZeq hSeq)
              (bmoClass_restrictedTripleOf T s j hZ hS' hT hZeq hSeq)).seqOn
            (hS'.preimageOpens (piOpenOf hZ U))
            (hS'.isCompact_closure_preimageOpens _ (isCompact_closure_piOpenOf hZ U hU)))).pullback
          (liftInclOf hZ U) (isLocalDiffeomorph_liftInclOf hZ U))).eraseEmpty := by
  subst hZeq
  subst hSeq
  rfl

end Of

/-! ### Indifference -/

variable (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι)
  (he : ∀ i, T.F.hyp (e i) = F'.hyp i) (i : F'.ι)

include he in
/-- The core on an open is indifferent to empty boundary members: the core at the
member `e i` of `E` is the core at the member `i` of `F'`, when `F'` is `E` with the empty members
outside the range of `e` deleted. The first centre and the transform are the same sets, and the
input family is indifferent, on the trace of `π_{-1}^{-1}(U)`, to the empty members of the
restricted
boundary `(E - E^{e i})|_{S_0}`, which embeds `(F' - F'^i)|_{S_0}` along `e`. -/
theorem coreFamOn_indifferentToEmptyMembers (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    (inp : BMOanFam 𝕜 (n - 1) s) (hT : BDClass s T) (hT₂ : BDClass s (withBoundary T F' hsnc'))
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    coreFamOn T s (e i) inp hT U hU = coreFamOn (withBoundary T F' hsnc') s i inp hT₂ U hU := by
  rw [coreFamOn_eq_of_eq T s (e i) (BD.isClosedSubmanifold_Zminus1 T s (e i))
      (isClosedSubmanifold_transformS T s (e i)) inp hT rfl rfl U hU,
    coreFamOn_eq_of_eq (withBoundary T F' hsnc') s i (BD.isClosedSubmanifold_Zminus1 T s (e i))
      (isClosedSubmanifold_transformS T s (e i)) inp hT₂ (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
      (transformS_eq_transformSOf T s F' hsnc' e he i) U hU]
  -- the restricted boundary of `E − E^{e i}` embeds that of `F' − F'^i` along `e`
  have hmatch : ∀ k, (restrictedTripleOf T s (e i) (BD.isClosedSubmanifold_Zminus1 T s (e i))
      (isClosedSubmanifold_transformS T s (e i)) hT rfl rfl).F.hyp (e k) =
      (restrictedTripleOf (withBoundary T F' hsnc') s i
        (BD.isClosedSubmanifold_Zminus1 T s (e i)) (isClosedSubmanifold_transformS T s (e i)) hT₂
        (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
        (transformS_eq_transformSOf T s F' hsnc' e he i)).F.hyp k := by
    intro k
    change (isClosedSubmanifold_transformS T s (e i)).preimageVal
        (⇑(Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s (e i))) ⁻¹'
          (T.F.emptyMember (e i)).hyp (e k)) =
      (isClosedSubmanifold_transformS T s (e i)).preimageVal
        (⇑(Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s (e i))) ⁻¹'
            (F'.emptyMember i).hyp k)
    congr 2
    by_cases hk : k = i
    · subst hk
      rw [HypersurfaceFamily.emptyMember_hyp_self, HypersurfaceFamily.emptyMember_hyp_self]
    · rw [HypersurfaceFamily.emptyMember_hyp_of_ne T.F fun h => hk (e.injective h),
        HypersurfaceFamily.emptyMember_hyp_of_ne F' hk, he k]
  have hout : ∀ b, b ∉ Set.range e →
      (restrictedTripleOf T s (e i) (BD.isClosedSubmanifold_Zminus1 T s (e i))
        (isClosedSubmanifold_transformS T s (e i)) hT rfl rfl).F.hyp b = ∅ := by
    intro b hb
    change (isClosedSubmanifold_transformS T s (e i)).preimageVal
        (⇑(Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s (e i))) ⁻¹'
          (T.F.emptyMember (e i)).hyp b) = ∅
    have hb0 : (T.F.emptyMember (e i)).hyp b = ∅ := by
      by_cases hbi : b = e i
      · subst hbi
        exact HypersurfaceFamily.emptyMember_hyp_self T.F (e i)
      · rw [HypersurfaceFamily.emptyMember_hyp_of_ne T.F hbi]
        exact he' b hb
    rw [hb0, Set.preimage_empty]
    exact Set.eq_empty_iff_forall_notMem.mpr fun p hp => hp
  -- the input family's indifference at the trace of `π_{-1}^{-1}(U)`
  have hX : (inp.functor.fam
        (restrictedTripleOf T s (e i) (BD.isClosedSubmanifold_Zminus1 T s (e i))
          (isClosedSubmanifold_transformS T s (e i)) hT rfl rfl)
        (bmoClass_restrictedTripleOf T s (e i) (BD.isClosedSubmanifold_Zminus1 T s (e i))
          (isClosedSubmanifold_transformS T s (e i)) hT rfl rfl)).seqOn
      ((isClosedSubmanifold_transformS T s (e i)).preimageOpens
        (piOpenOf (BD.isClosedSubmanifold_Zminus1 T s (e i)) U))
      ((isClosedSubmanifold_transformS T s (e i)).isCompact_closure_preimageOpens _
        (isCompact_closure_piOpenOf (BD.isClosedSubmanifold_Zminus1 T s (e i)) U hU)) =
      (inp.functor.fam
        (restrictedTripleOf (withBoundary T F' hsnc') s i
          (BD.isClosedSubmanifold_Zminus1 T s (e i)) (isClosedSubmanifold_transformS T s (e i)) hT₂
          (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
          (transformS_eq_transformSOf T s F' hsnc' e he i))
        (bmoClass_restrictedTripleOf (withBoundary T F' hsnc') s i
          (BD.isClosedSubmanifold_Zminus1 T s (e i)) (isClosedSubmanifold_transformS T s (e i)) hT₂
          (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
          (transformS_eq_transformSOf T s F' hsnc' e he i))).seqOn
      ((isClosedSubmanifold_transformS T s (e i)).preimageOpens
        (piOpenOf (BD.isClosedSubmanifold_Zminus1 T s (e i)) U))
      ((isClosedSubmanifold_transformS T s (e i)).isCompact_closure_preimageOpens _
        (isCompact_closure_piOpenOf (BD.isClosedSubmanifold_Zminus1 T s (e i)) U hU)) :=
    inp.indifferentToEmptyMembers
    (restrictedTripleOf T s (e i) (BD.isClosedSubmanifold_Zminus1 T s (e i))
      (isClosedSubmanifold_transformS T s (e i)) hT rfl rfl)
    (restrictedTripleOf (withBoundary T F' hsnc') s i
      (BD.isClosedSubmanifold_Zminus1 T s (e i)) (isClosedSubmanifold_transformS T s (e i)) hT₂
      (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
      (transformS_eq_transformSOf T s F' hsnc' e he i)).F
    (restrictedTripleOf (withBoundary T F' hsnc') s i
      (BD.isClosedSubmanifold_Zminus1 T s (e i)) (isClosedSubmanifold_transformS T s (e i)) hT₂
      (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
      (transformS_eq_transformSOf T s F' hsnc' e he i)).isSnc
    e hmatch hout (bmoClass_restrictedTripleOf T s (e i) _ _ hT rfl rfl)
    (bmoClass_restrictedTripleOf (withBoundary T F' hsnc') s i _ _ hT₂
      (Zminus1_eq_of_hyp_eq T s F' hsnc' e he i)
      (transformS_eq_transformSOf T s F' hsnc' e he i))
    ((isClosedSubmanifold_transformS T s (e i)).preimageOpens
      (piOpenOf (BD.isClosedSubmanifold_Zminus1 T s (e i)) U))
    ((isClosedSubmanifold_transformS T s (e i)).isCompact_closure_preimageOpens _
      (isCompact_closure_piOpenOf (BD.isClosedSubmanifold_Zminus1 T s (e i)) U hU))
  rw [hX]

end BDan

section Assembly

variable {M : AnalyticManifold.{u} 𝕜 E} {m : ℕ}

/-- The value of `BD_{n,m,·}` on every relatively compact open is indifferent to empty boundary
members: when `F'` is `E` with the empty members outside the range of the order
embedding `e` deleted, the value at the member `e i` of `E` equals the value at the member `i` of
`F'`. This is `coreFamOn_indifferentToEmptyMembers` at the tuned triple (the tuning keeps the
boundary). -/
theorem BDanFam_indifferentToEmptyMembers (inp : BMOanFam 𝕜 (n - 1) (tuningParam m))
    (T : AnalyticTriple ψ₀ M) (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι)
    (he : ∀ i, T.F.hyp (e i) = F'.hyp i) (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    (hT : AnalyticTriple.BOClass m T)
    (hT' : AnalyticTriple.BOClass m
      (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M)) (i : F'.ι) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    BDanFam m inp T hT (e i) U hU =
      BDanFam m inp ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ hT' i U hU := by
  unfold BDanFam
  exact BDan.coreFamOn_indifferentToEmptyMembers (T.tuned m hT.1) (tuningParam m) F' hsnc' e he i
    he' inp _ ⟨AnalyticTriple.boClass_tuned hT', AnalyticTriple.isDBalanced_tuned hT'⟩ U hU

end Assembly

end Hironaka.Manifold
