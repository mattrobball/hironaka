/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Induced
public import Hironaka.Resolution.Analytic.BM97.Ledger
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Manifold.Jacobian.Units
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Resolution.Analytic.BM97.LedgerStep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The Jacobian ledger of a blow-up sequence

**Every blow-up sequence whose centres have simple normal crossings with the accumulated total
transform carries a Jacobian ledger** (Kollár's condition that "the centers `Z_i` have simple
normal crossings with `E`", under which the total transform `Π⁻¹_tot(E)` is a simple normal
crossings divisor [Kol07, Definition 25]): for a list of centres `L : CenterList ψ₀ M` and a start
family `F`, if at every stage the centre has simple normal crossings with the current total
transform (`HasSncWith`), the composite `σ^r : M_r → M` has a ledger
(`JacobianLedger`, `Hironaka/Resolution/Analytic/BM97/Ledger.lean`) relative to the final total
transform `totalTransformSeqFrom F (Fin.last _)`, the exceptional members being those off the
range of `originalIdx` — the strict transforms of the original members are the non-exceptional
ones (`jacobianLedger_composite_of_forall_hasSncWith`). The proof is the induction along the list
with the step of `Hironaka/Resolution/Analytic/BM97/LedgerStep.lean` (`JacobianLedger.step`) at
every blow-up, `r = 0` being the identity (`jacobianStalk = ⊤`, `s = ∅`; `jacobianLedger_id`): the
joint statement `isSnc_and_jacobianLedger_stageMap_totalTransformSeqFrom` carries the simple normal
crossings property of the boundary family along (`isSnc_totalTransform`), reads each blowing-up of
the succession in the fixed chart `ψ₀` through `IsBlowUp.congr_chart` and
`IsClosedSubmanifold.congr_chart`, and keeps the exceptional index set in the form
`(range originalIdx)ᶜ` by `compl_range_toLex_inl`. The instance used for the Jacobian clause of the
principalization theorem (`jacobianLedger_composite_of_forall_hasSncWith_empty`,
`Hironaka/Resolution/Analytic/BM97/JacobianAssembly.lean`) is the empty start, `exc = univ`.
-/

public section

open Set TopologicalSpace Filter Topology AnalyticManifold
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

universe u

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- The start of the induction, `r = 0`: the identity carries the empty ledger relative to any
simple normal crossings family — `jacobianStalk id x = ⊤` (the identity being a local analytic
isomorphism) is the empty product. -/
theorem jacobianLedger_id (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) :
    JacobianLedger ψ₀ ⇑(ContMDiffMap.id : AnalyticMap M M) F ∅ := by
  intro x
  refine ⟨hF.exists_isSncChartAt x, ∅, fun _ => 0, fun j hj => absurd hj (Finset.notMem_empty j),
    fun j hj => absurd hj (Finset.notMem_empty j), ?_⟩
  rw [Finset.prod_empty, Ideal.one_eq_top]
  exact jacobianStalk_eq_top_of_isLocalDiffeomorphAt (ContMDiffMap.id : AnalyticMap M M).contMDiff
    (BlowUpSequence.isLocalDiffeomorph_id M x)

/-- The bookkeeping of the exceptional indices: the members of the total transform off the range
of `inl ∘ g` are the strict transforms of the members off the range of `g` together with the new
exceptional divisor `inr`. -/
theorem compl_range_toLex_inl {α β : Type*} (g : α → β) :
    (Set.range fun a => toLex (Sum.inl (g a) : β ⊕ PUnit))ᶜ =
      (fun b : β => toLex (Sum.inl b : β ⊕ PUnit)) '' (Set.range g)ᶜ ∪
        {toLex (Sum.inr PUnit.unit)} := by
  ext k
  obtain ⟨k, rfl⟩ : ∃ k' : β ⊕ PUnit, toLex k' = k := ⟨ofLex k, rfl⟩
  constructor
  · intro hk
    rcases k with b | u
    · exact Or.inl ⟨b, fun ⟨a, ha⟩ =>
        hk ⟨a, congrArg (fun x : β => toLex (Sum.inl x : β ⊕ PUnit)) ha⟩, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨b, hb, hbk⟩ | hk) ⟨a, ha⟩
    · exact hb ⟨a, Sum.inl_injective (toLex_inj.mp (ha.trans hbk.symm))⟩
    · exact Sum.inl_ne_inr (toLex_inj.mp (ha.trans hk))

/-- **The joint induction along a blow-up sequence** (the hypothesis "the centres have simple
normal crossings with the boundary" of [Kol07, Definition 25]): at every stage `i` the boundary
family `F_i = totalTransformSeqFrom F i` is a simple normal crossings family and the partial
composite `σ^i = stageMap i` carries a Jacobian ledger relative to `F_i`, the exceptional members
being those off the range of `originalIdx` (the strict transforms of the original members are the
non-exceptional ones). `Fin.induction`: the start is the identity's empty ledger; the step is
`JacobianLedger.step` at the `i`-th blowing-up, read in the fixed chart `ψ₀` through
`IsBlowUp.congr_chart` and `IsClosedSubmanifold.congr_chart` (the codimension stays `S.codim i`),
with `isSnc_totalTransform` for the simple normal crossings clause and the index bookkeeping
`compl_range_toLex_inl` at the successor. -/
theorem isSnc_and_jacobianLedger_stageMap_totalTransformSeqFrom (S : FiniteSuccession M)
    (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (h3 : ∀ i : Fin S.length,
      (S.totalTransformSeqFrom F i.castSucc).HasSncWith ψ₀ (S.center i).support (S.codim i))
    (i : Fin (S.length + 1)) :
    (S.totalTransformSeqFrom F i).IsSnc ψ₀ ∧
      JacobianLedger ψ₀ ⇑(S.stageMap i) (S.totalTransformSeqFrom F i)
        (Set.range (S.originalIdx F i))ᶜ := by
  induction i using Fin.induction with
  | zero =>
    refine ⟨hF, ?_⟩
    have h0 : (Set.range (S.originalIdx F 0))ᶜ = ∅ := by
      rw [Set.compl_empty_iff]
      exact Set.range_eq_univ.mpr fun j => ⟨j, rfl⟩
    rw [h0]
    exact jacobianLedger_id F hF
  | succ i ih =>
    obtain ⟨hsnc, hL⟩ := ih
    have hZ : IsClosedSubmanifold ψ₀ (S.center i).support (S.codim i) :=
      (S.isClosedSubmanifold_center i).congr_chart ψ₀
    have hπ : IsBlowUp ψ₀ (S.center i).support (S.codim i) (S.map i) :=
      (S.isBlowUp_map i).congr_chart ψ₀
    refine ⟨HypersurfaceFamily.isSnc_totalTransform hZ hπ hsnc (h3 i), ?_⟩
    have hstep := JacobianLedger.step ψ₀ (S.stageMap i.castSucc).contMDiff hsnc hL hZ (h3 i) hπ
    have hexc : (Set.range (S.originalIdx F i.succ))ᶜ =
        (fun j => toLex (Sum.inl j)) '' (Set.range (S.originalIdx F i.castSucc))ᶜ ∪
          {toLex (Sum.inr PUnit.unit)} :=
      compl_range_toLex_inl (S.originalIdx F i.castSucc)
    rw [hexc, S.stageMap_succ]
    exact hstep

/-- **The Jacobian ledger of a blow-up sequence** ([Kol07, Definition 25]): every blow-up sequence
whose centres have simple normal crossings with the accumulated total transform carries a Jacobian
ledger relative to the final total transform, the exceptional members being those off the range of
`originalIdx`. The last stage of the joint induction. -/
theorem jacobianLedger_composite_of_forall_hasSncWith (L : BlowUpSequence ψ₀ M)
    (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (h3 : ∀ i : Fin L.toSuccession.length,
      (L.toSuccession.totalTransformSeqFrom F i.castSucc).HasSncWith ψ₀
        (L.toSuccession.center i).support (L.toSuccession.codim i)) :
    JacobianLedger ψ₀ ⇑L.toSuccession.composite
      (L.toSuccession.totalTransformSeqFrom F (Fin.last _))
      (Set.range (L.toSuccession.originalIdx F (Fin.last _)))ᶜ :=
  (isSnc_and_jacobianLedger_stageMap_totalTransformSeqFrom L.toSuccession F hF h3 (Fin.last _)).2

/-- The instance used for the Jacobian clause of the principalization theorem: for a list of
centres whose centres have simple normal crossings with the accumulated exceptional divisor
`totalTransformSeq` (the empty start), the composite carries a ledger relative to the final family
of exceptional divisors with every member exceptional (`exc = univ`) — the general form at the empty
family (`isSnc_empty`), whose `originalIdx` has empty range. -/
theorem jacobianLedger_composite_of_forall_hasSncWith_empty (L : BlowUpSequence ψ₀ M)
    (h3 : ∀ i : Fin L.toSuccession.length,
      (L.toSuccession.totalTransformSeq i.castSucc).HasSncWith ψ₀
        (L.toSuccession.center i).support (L.toSuccession.codim i)) :
    JacobianLedger ψ₀ ⇑L.toSuccession.composite (L.toSuccession.totalTransformSeq (Fin.last _))
      Set.univ := by
  have h := jacobianLedger_composite_of_forall_hasSncWith L (HypersurfaceFamily.empty M)
    (HypersurfaceFamily.isSnc_empty (ψ := ψ₀)) h3
  have hexc : (Set.range (L.toSuccession.originalIdx (HypersurfaceFamily.empty M)
      (Fin.last _)))ᶜ = Set.univ := by
    rw [Set.compl_univ_iff]
    exact Set.range_eq_empty_iff.mpr ⟨fun j => PEmpty.elim j⟩
  rw [hexc] at h
  exact h

end Hironaka.Manifold
