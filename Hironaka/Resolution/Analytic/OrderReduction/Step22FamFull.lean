/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step22Fam
public import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyOrder
import Hironaka.Resolution.Analytic.OrderReduction.BoundaryEnlarge
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Step21Cosupp
import Hironaka.Resolution.Analytic.OrderReduction.Step21FamCosupp
import Hironaka.Resolution.Analytic.OrderReduction.TunedLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2 on an open is of order `≥ s` for the full transformed boundary

The triple of Step 2.2 carries the boundary `E^{exc}_r + H_r` of exceptional divisors and the
transform of the hypersurface of maximal contact, while the clause of [Kol07, Definition 66] for
Step 2 as a whole concerns the full transformed boundary, which also contains the transforms of the
original members `E^j`. After Step 2.1 these miss the cosupport `{ord I_r ≥ s}` (the conclusion
of [Kol07, 104, Step 2.1.j]: "`Π^{-1}_{r(s)∗} E` is disjoint from `cosupp(I_{r(s)}, m)`"), so a
member of the full boundary through the cosupport is an exceptional divisor, a member of both
boundaries; this is what lets the order clause pass from the one boundary to the other.

* `BO.fullToPosIdxOf`, `BO.exists_exceptionalEmb_of_mem_of_disjoint`,
  `BO.isOfOrderGe_full_of_positional` — over an arbitrary sequence `L` of order `≥ s`: a
  correspondence from the members of the full boundary to those of `E^{exc}_r + H_r` sending an
  exceptional divisor to itself; a member of the full boundary through the cosupport is an
  exceptional divisor when the transforms of the original members miss the cosupport; and a
  sequence of order `≥ s` for the triple of Step 2.2 restricted to an open is then of order `≥ s`
  for the induced triple (`Induced.lean`) restricted to the open.
* `BO.hfStep22FamOn_isOfOrderGe_positional`, `BO.hfStep22FamOn_isOfOrderGe_full` — the value of
  Step 2.2 on its reading open is of order `≥ s` for the restricted triple of Step 2.2 (the order
  clause of the data at the re-tuned mark, carried back through the tuning by
  `orderReduction_tuned_iff`), hence for the restricted induced triple (the cosupport clause of
  the chain of Step 2.1, `Step21FamCosupp.lean`).
* `hfStep2SeqFamOn_isOfOrderGe` — the value of Step 2 on `U` is a smooth blow-up sequence of order
  `≥ s` starting with the restricted triple `(U, 𝓘|_U, E|_U)`: the appended chain is of order `≥ s`
  (`isOfOrderGe_shrinkAppend`), then restricted to `U` and its empty blow-ups deleted.

The `hf…` declarations are the general forms over data `d : HFData ψ₀ s` of Step 2
(`HFamData.lean`); the plain forms are their instances at Lemma 102's data. This is the order
clause of the family structure `BOanFam` for the local functor (`LocalFunctorFam.lean`).
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace AnalyticManifold IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {s : ℕ}

namespace BO

open _root_.Manifold

section FullBoundary

variable {X : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ X) (L : BlowUpSequence ψ₀ X)
  (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) {H : Set X}
  (hsnc : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀)

/-- A correspondence from the members of the full transformed boundary (the induced triple) to
those of the boundary `E^{exc}_r + H_r` of the triple of Step 2.2: an exceptional divisor to
itself (chosen among the members indexing that divisor), the transform of an original member to
an arbitrary member. Only the values at exceptional divisors matter. -/
noncomputable def fullToPosIdxOf : (T.induced s L hL).F.ι → (step22TripleOf T L hL hsnc).F.ι :=
  fun a =>
  have : Nonempty (step22TripleOf T L hL hsnc).F.ι := ⟨idxHOf T s L hL hsnc⟩
  Classical.epsilon fun p =>
    ∃ k, a = L.toSuccession.exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 k ∧
      p = toLex (Sum.inl k)

omit [FiniteDimensional 𝕜 E] in
/-- At an exceptional divisor `E_k`, the correspondence picks a member indexing that divisor. -/
theorem fullToPosIdxOf_spec (a : (T.induced s L hL).F.ι)
    (hk : ∃ k, a = L.toSuccession.exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 k) :
    ∃ k, a = L.toSuccession.exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 k ∧
      fullToPosIdxOf T L hL hsnc a = toLex (Sum.inl k) := by
  obtain ⟨k, hk⟩ := hk
  have : Nonempty (step22TripleOf T L hL hsnc).F.ι := ⟨idxHOf T s L hL hsnc⟩
  exact Classical.epsilon_spec
    (p := fun p => ∃ k, a = L.toSuccession.exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 k ∧
      p = toLex (Sum.inl k)) ⟨toLex (Sum.inl k), k, hk, rfl⟩

omit [FiniteDimensional 𝕜 E] hsnc in
/-- A member of the full transformed boundary meeting the cosupport `{ord I_r ≥ s}` is an
exceptional divisor, when the transforms of the original members miss the cosupport (the
conclusion of Step 2.1, [Kol07, 104, Step 2.1.j]). -/
theorem exists_exceptionalEmb_of_mem_of_disjoint
    (hdis : ∀ j, Disjoint
      {x | (s : ℕ∞) ≤ (L.toSuccession.markedTransformSeq T.I s (Fin.last _)).ord x}
      (L.toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _)))
    (a : (T.induced s L hL).F.ι)
    (ha : ∃ x ∈ (T.induced s L hL).F.hyp a, (s : ℕ∞) ≤ (T.induced s L hL).I.ord x) :
    ∃ k, a = L.toSuccession.exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 k := by
  rcases L.toSuccession.originalIdxAux_or_exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 a with
    ⟨j, rfl⟩ | h
  · exfalso
    obtain ⟨x, hx, hord⟩ := ha
    have hx' : x ∈ L.toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _) := by
      change x ∈ (L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).hyp
        (L.toSuccession.originalIdx T.F (Fin.last _) j) at hx
      rwa [FiniteSuccession.hyp_originalIdx] at hx
    exact Set.disjoint_left.mp (hdis j) hord hx'
  · exact h

/-- Over an arbitrary sequence `L` of order `≥ s` and restricted to an open `O` of its last stage:
a sequence of order `≥ s` for the restricted triple of Step 2.2 (boundary `E^{exc}_r + H_r`) is
of order `≥ s` for the restricted induced triple (the full transformed boundary), provided the
transforms of the original members miss the cosupport. The members of the full boundary through
the cosupport are exceptional divisors (`exists_exceptionalEmb_of_mem_of_disjoint`, the order read
at the point's image in the last stage), members of both boundaries, so the normal-crossings
condition on the centres transfers (`IsOfOrderGe.of_forall_hyp_eq_of_mem`). -/
theorem isOfOrderGe_full_of_positional
    (hdis : ∀ j, Disjoint
      {x | (s : ℕ∞) ≤ (L.toSuccession.markedTransformSeq T.I s (Fin.last _)).ord x}
      (L.toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _)))
    (O : Opens (L.stage (Fin.last _)))
    (S : BlowUpSequence ψ₀ ((L.stage (Fin.last _)).restrict O))
    (hpos : S.toSuccession.IsOfOrderGe
      ((step22TripleOf T L hL hsnc).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).I s
      ((step22TripleOf T L hL hsnc).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf) :
    S.toSuccession.IsOfOrderGe
      ((T.induced s L hL).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).I s
      ((T.induced s L hL).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf := by
  -- a member of the restricted full boundary through the cosupport is an exceptional divisor
  have hexc : ∀ k : (T.induced s L hL).F.ι,
      (∃ a ∈ ((T.induced s L hL).pullback ((L.stage (Fin.last _)).inclusion O)
          (isLocalDiffeomorph_inclusion _ _)).F.hyp k,
        (s : ℕ∞) ≤ ((step22TripleOf T L hL hsnc).pullback ((L.stage (Fin.last _)).inclusion O)
            (isLocalDiffeomorph_inclusion _ _)).I.ord a) →
      ∃ k', k = L.toSuccession.exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 k' := by
    rintro k ⟨a, hak, hord⟩
    refine exists_exceptionalEmb_of_mem_of_disjoint T L hL hdis k
      ⟨(L.stage (Fin.last _)).inclusion O a, hak, ?_⟩
    exact hord.trans_eq (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
      (isLocalDiffeomorph_inclusion _ O a))
  refine FiniteSuccession.IsOfOrderGe.of_forall_hyp_eq_of_mem
    (F := ((step22TripleOf T L hL hsnc).pullback ((L.stage (Fin.last _)).inclusion O)
      (isLocalDiffeomorph_inclusion _ _)).F)
    (G := ((T.induced s L hL).pullback ((L.stage (Fin.last _)).inclusion O)
      (isLocalDiffeomorph_inclusion _ _)).F) _ (fullToPosIdxOf T L hL hsnc)
    ((step22TripleOf T L hL hsnc).pullback _ (isLocalDiffeomorph_inclusion _ _)).isSnc
    ((T.induced s L hL).pullback _ (isLocalDiffeomorph_inclusion _ _)).isSnc hpos ?_ ?_
  · intro k hk
    obtain ⟨k', hkk', he⟩ := fullToPosIdxOf_spec T L hL hsnc k (hexc k hk)
    rw [he]
    change ⇑((L.stage (Fin.last _)).inclusion O) ⁻¹' (T.induced s L hL).F.hyp k =
      ⇑((L.stage (Fin.last _)).inclusion O) ⁻¹' (exceptionalOf L).hyp k'
    exact congrArg (Set.preimage _) ((congrArg (T.induced s L hL).F.hyp hkk').trans
      (L.toSuccession.hyp_exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 k'))
  · intro k k' hk hk' heq
    obtain ⟨j, hkj, he⟩ := fullToPosIdxOf_spec T L hL hsnc k (hexc k hk)
    obtain ⟨j', hkj', he'⟩ := fullToPosIdxOf_spec T L hL hsnc k' (hexc k' hk')
    rw [he, he'] at heq
    have hjj : j = j' := Sum.inl_injective (toLex.injective heq)
    exact hkj.trans ((congrArg _ hjj).trans hkj'.symm)

end FullBoundary

section StepTwo

variable (bd : ∀ s : ℕ, BDanFamData ψ₀ s) (d : HFData ψ₀ s) (T : AnalyticTriple ψ₀ M)
  (hT : AnalyticTriple.BOClass s T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
  {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1) (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))

/-- The value of Step 2.2 on its reading open is of order `≥ s` for the triple of Step 2.2
restricted to the open (over data `d`): the order clause of the data at the re-tuned mark, the
tuned triple pulled back being the pulled-back triple tuned (`tuned_pullback`), carried back
through the tuning by `orderReduction_tuned_iff`. -/
theorem hfStep22FamOn_isOfOrderGe_positional :
    (hfStep22FamOn T s d hT U hU hH hle).toSuccession.IsOfOrderGe
      ((hfStep22TripleFam T s d hT U hU hH hle).pullback
        (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).I s
      ((hfStep22TripleFam T s d hT U hU hH hle).pullback
        (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf := by
  have hT₂₂ : stepHClass s (hfStep22TripleFam T s d hT U hU hH hle) :=
    stepHClass_hfStep22TripleFam T s d hT U hU hH hle
  have hT₂ : AnalyticTriple.BOClass s ((hfStep22TripleFam T s d hT U hU hH hle).pullback
      (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
        (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)) :=
    boClass_pullback_inclusion_of_boClass _ _ hT₂₂.1
  have hord : (hfStep22FamOn T s d hT U hU hH hle).toSuccession.IsOfOrderGe
      (((hfStep22TripleFam T s d hT U hU hH hle).tuned s hT₂₂.1.1).pullback
        (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).I (tuningParam s)
      (((hfStep22TripleFam T s d hT U hU hH hle).tuned s hT₂₂.1.1).pullback
        (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf :=
    d.hf.isOfOrderGe ((hfStep22TripleFam T s d hT U hU hH hle).tuned s hT₂₂.1.1)
      (AnalyticTriple.boClass_tuned hT₂₂.1) (greatestIdx (stepHClass_tuned hT₂₂)) _
      (isCompact_closure_hfStep2ReadOpen T s d hT U hU)
  have eI : (((hfStep22TripleFam T s d hT U hU hH hle).tuned s hT₂₂.1.1).pullback
      (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
        (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).I =
      (((hfStep22TripleFam T s d hT U hU hH hle).pullback
        (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).tuned s hT₂.1).I :=
    congrArg AnalyticTriple.I
      (AnalyticTriple.tuned_pullback (hfStep22TripleFam T s d hT U hU hH hle) hT₂₂.1.1 _ _).symm
  rw [eI] at hord
  exact (AnalyticTriple.orderReduction_tuned_iff _ hT₂ _).mp hord

/-- The value of Step 2.2 on its reading open is of order `≥ s` for the restricted induced triple,
with the full transformed boundary (over data `d`): the clause for the boundary `E^{exc}_r + H_r`
(`hfStep22FamOn_isOfOrderGe_positional`) and the cosupport clause of the chain of Step 2.1 for
every original member (`step21FamAux_cosupp_disjoint`; an empty member has empty strict transform),
through `isOfOrderGe_full_of_positional`. -/
theorem hfStep22FamOn_isOfOrderGe_full :
    (hfStep22FamOn T s d hT U hU hH hle).toSuccession.IsOfOrderGe
      (((T.pullback (M.inclusion (step2OpenW T s hT U hU))
        (isLocalDiffeomorph_inclusion M _)).induced s (hfStep2FamChain T s d hT U hU).L
        (hfStep2FamChain T s d hT U hU).hge).pullback
        (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).I s
      (((T.pullback (M.inclusion (step2OpenW T s hT U hU))
        (isLocalDiffeomorph_inclusion M _)).induced s (hfStep2FamChain T s d hT U hU).L
        (hfStep2FamChain T s d hT U hU).hge).pullback
        (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf := by
  refine isOfOrderGe_full_of_positional _ _ _ _ ?_ _ _
    (hfStep22FamOn_isOfOrderGe_positional d T hT U hU hH hle)
  intro j
  by_cases hj : T.F.hyp j = ∅
  · have h0 : (T.pullback (M.inclusion (step2OpenW T s hT U hU))
        (isLocalDiffeomorph_inclusion M _)).F.hyp j = ∅ := by
      change ⇑(M.inclusion (step2OpenW T s hT U hU)) ⁻¹' T.F.hyp j = ∅
      rw [hj, Set.preimage_empty]
    rw [h0, FiniteSuccession.strictTransformSeq_empty]
    exact Set.disjoint_empty _
  · exact ChainState.step21FamAux_cosupp_disjoint d.bd₁ T hT
      (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) (memberCount T s hT + 1))
      (memberCount T s hT + 1) (isCompact_closure_chainOpens _ _ _)
      (fun _ hk => closure_chainOpens_succ_subset _ _ _ hk) (T.F.nonemptyList hT.2.2).reverse
      (Nat.le_succ _) j (List.mem_reverse.mpr ((T.F.mem_nonemptyList hT.2.2 j).mpr hj))

end StepTwo

end BO

/-- The value of Step 2 on the open `U` is a smooth blow-up sequence of order `≥ s` starting with
the restricted triple `(U, 𝓘|_U, E|_U)`, with the full boundary ([Kol07, Definition 66
(1′)–(4′)]; over data `d`): the chain of Step 2.1 with the value of Step 2.2 appended is of order
`≥ s` for the triple restricted to the next open (`isOfOrderGe_shrinkAppend` with
`hfStep22FamOn_isOfOrderGe_full`), then restricted to `U` (`isOfOrderGe_pullback`) and its empty
blow-ups deleted (`isOfOrderGe_eraseEmpty`). -/
theorem hfStep2SeqFamOn_isOfOrderGe (d : HFData ψ₀ s)
    (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1)
    (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1)) :
    (BO.hfStep2SeqFamOn T s d hT U hU hH hle).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I s
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf := by
  have hA := (BO.hfStep2FamChain T s d hT U hU).L.isOfOrderGe_shrinkAppend
    (M.restrictLE (BO.step2OpenV_le T s hT U hU)) (isLocalDiffeomorph_restrictLE _)
    (T.pullback (M.inclusion (BO.step2OpenW T s hT U hU)) (isLocalDiffeomorph_inclusion M _)) s
    (BO.hfStep2FamChain T s d hT U hU).hge (BO.hfStep22FamOn T s d hT U hU hH hle)
    (BO.hfStep22FamOn_isOfOrderGe_full d T hT U hU hH hle)
  have hB := AnalyticTriple.isOfOrderGe_pullback _ s _ hA
    (M.restrictLE (BO.le_step2OpenV T s hT U hU)) (isLocalDiffeomorph_restrictLE _)
  rw [AnalyticTriple.pullback_inclusion_restrictLE T (BO.step2OpenV_le T s hT U hU),
    AnalyticTriple.pullback_inclusion_restrictLE T (BO.le_step2OpenV T s hT U hU)] at hB
  exact BlowUpSequence.isOfOrderGe_eraseEmpty _ _ s
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc hB

end Hironaka.Manifold
