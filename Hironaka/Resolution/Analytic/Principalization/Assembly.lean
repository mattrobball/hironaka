/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.DisjoinInput
public import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
public import Hironaka.Resolution.Analytic.Functor.Family
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
public import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The value of the principalization family on a relatively compact open

Kollár's construction of the principalization functor [Kol07, 72] read over a relatively compact
open `U ⋐ M` of the triple `(M, 𝓘, E)`: choose a relatively compact open `W` with
`closure U ⊆ W` (the shrinking chain `U ⋐ W ⋐ M`), restrict the triple to `W` — finitely many
members of `E` meet `closure W` (`IsSnc.finite_of_isCompact`) — blow up the disjoining centres of
[Kol07, 72] (`disjoinList`), form the disjoined triple on the last stage (`disjoinedTriple`, in the
marked class at mark `1`), apply the marked order-reduction family `BMO_{n,1}` to it and read its
value on the reading open over `U` (`liftRange`, relatively compact since the composite blow-down
is proper), append it to the disjoining list restricted to `U` (`shrinkAppend`), and delete the
empty rounds (Kollár's convention [Kol07, 32]). This module defines that value,
`principalizationValue`, and proves it has no empty centres; that it does not depend on `W`, and
the compatibility clause of the family, are proved in `Canonicity.lean`; the clauses of
[Kol07, Theorem 35] in the `Clause*.lean` modules of this directory. The value is what the
resolution of an analytic space is assembled from (`Hironaka/Manifold/Sequence/Resolve/`).
-/

@[expose] public section

universe u

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-! ### The shrinking open `W` of the chain `U ⋐ W ⋐ M` -/

/-- The shrinking open of the chain: a relatively compact open containing `closure U` (chosen;
Mathlib's `exists_isOpen_superset_and_isCompact_closure` on the locally compact manifold). -/
noncomputable def shrinkOpen (U : Opens M) (hU : IsCompact (closure (U : Set M))) : Opens M :=
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin n → 𝕜) M
  ⟨Classical.choose (exists_isOpen_superset_and_isCompact_closure hU),
    (Classical.choose_spec (exists_isOpen_superset_and_isCompact_closure hU)).1⟩

theorem closure_subset_shrinkOpen (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    closure (U : Set M) ⊆ (shrinkOpen U hU : Set M) :=
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin n → 𝕜) M
  (Classical.choose_spec (exists_isOpen_superset_and_isCompact_closure hU)).2.1

theorem isCompact_closure_shrinkOpen (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    IsCompact (closure (shrinkOpen U hU : Set M)) :=
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin n → 𝕜) M
  (Classical.choose_spec (exists_isOpen_superset_and_isCompact_closure hU)).2.2

theorem le_shrinkOpen (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    U ≤ shrinkOpen U hU :=
  fun _ hx => closure_subset_shrinkOpen U hU (subset_closure hx)

/-! ### The restricted triple over `W` and its disjoining list -/

/-- The triple restricted to the open `W` (Kollár's "over a relatively compact open"). -/
noncomputable abbrev restrictTriple
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (W : Opens M) :
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict W) :=
  T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)

/-- Finitely many members of `E` meet a relatively compact open (Kollár's `E_1, …, E_k`,
[Kol07, 72]; `IsSnc.finite_of_isCompact`), so the restricted family has finitely many nonempty
members. -/
theorem finite_nonempty_restrictTriple
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (W : Opens M)
    (hW : IsCompact (closure (W : Set M))) :
    Finite {j // (restrictTriple T W).F.hyp j ≠ ∅} := by
  have hfin := T.isSnc.finite_of_isCompact hW
  refine Set.finite_coe_iff.mpr (hfin.subset fun j hj => ?_)
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hj
  exact ⟨x.1, hx, subset_closure x.2⟩

/-- Kollár's `k`: the number of members of `E` meeting `W`. -/
noncomputable def disjoinBound (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (W : Opens M) : ℕ :=
  Nat.card {j // (restrictTriple T W).F.hyp j ≠ ∅}

/-- No point of `W` lies on `k + 1` members. -/
theorem meetLocus_disjoinBound_eq_empty
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (W : Opens M)
    (hW : IsCompact (closure (W : Set M))) :
    (restrictTriple T W).F.meetLocus (disjoinBound T W + 1) = ∅ :=
  haveI := finite_nonempty_restrictTriple T W hW
  HypersurfaceFamily.meetLocus_eq_empty_of_finite_nonempty _

/-- The disjoining blow-ups of [Kol07, 72] for the triple restricted to `W`. -/
noncomputable abbrev disjoinListOn (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (W : Opens M) (hW : IsCompact (closure (W : Set M))) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict W) :=
  disjoinList (disjoinBound T W) (restrictTriple T W).F (restrictTriple T W).isSnc
    (meetLocus_disjoinBound_eq_empty T W hW)

/-! ### The value built from a list and a triple on its last stage -/

/-- **The value built from a list** `L` on `X` and a triple `T'` of the marked class on its last
stage, read along a local analytic isomorphism `ι : N → X` with relatively compact range: the
shrink-and-append of `L` along `ι` with the order-reduction value of `T'` on the reading open, the
empty rounds deleted. The value on `U` is its instance at the disjoining list and the disjoined
triple; the general form is what the independence of the shrinking open compares. -/
noncomputable def valueOf (bmo : BMOanFam.{u} 𝕜 n 1) {X N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (L.stage (Fin.last _)))
    (hT' : AnalyticTriple.BMOClass 1 T') (ι : AnalyticMap N X)
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
    (hc : IsCompact (closure (Set.range ι))) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N :=
  (L.shrinkAppend ι hι ((bmo.functor.fam T' hT').seqOn (L.liftRange ι hι)
    (L.isCompact_closure_liftRange ι hι hc))).eraseEmpty

/-- The value is compatible with an equality of the reading maps. -/
theorem valueOf_congr_map (bmo : BMOanFam.{u} 𝕜 n 1) {X N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (L.stage (Fin.last _)))
    (hT' : AnalyticTriple.BMOClass 1 T') {ι ι' : AnalyticMap N X} (e : ι = ι')
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
    (hι' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι')
    (hc : IsCompact (closure (Set.range ι))) (hc' : IsCompact (closure (Set.range ι'))) :
    valueOf bmo L T' hT' ι hι hc = valueOf bmo L T' hT' ι' hι' hc' := by
  subst e
  rfl

/-- The value built from the disjoined triple is compatible with an equality of lists. -/
theorem valueOf_disjoinedTripleOf_congr (bmo : BMOanFam.{u} 𝕜 n 1)
    {X N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    {L₁ L₂ : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X}
        (e : L₁ = L₂)
    (h₁ : (L₁.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).IsSnc _)
    (h₁' : ((L₁.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L₁.toSuccession.originalIdx T.F (Fin.last _)))).meetLocus 2 = ∅)
    (h₂ : (L₂.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).IsSnc _)
    (h₂' : ((L₂.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L₂.toSuccession.originalIdx T.F (Fin.last _)))).meetLocus 2 = ∅)
    (ι : AnalyticMap N X) (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
    (hc : IsCompact (closure (Set.range ι))) :
    valueOf bmo L₁ (disjoinedTripleOf T L₁ h₁ h₁') (disjoinedTripleOf_bmoClass T L₁ h₁ h₁') ι hι
        hc =
      valueOf bmo L₂ (disjoinedTripleOf T L₂ h₂ h₂') (disjoinedTripleOf_bmoClass T L₂ h₂ h₂') ι hι
        hc := by
  subst e
  rfl

/-! ### The value on `U` -/

/-- **The value on `U` computed with a shrinking open `W`** ([Kol07, 72], per relatively compact
open): for any relatively compact open `W` with `closure U ⊆ W`, disjoin over `W`, apply
`BMO_{n,1}` to the disjoined triple, read it on the reading open over `U`, append to the disjoining
list restricted to `U`, and delete the empty rounds ([Kol07, 32]). The independence of `W` is
proved with the compatibility clause (`Canonicity.lean`). -/
noncomputable def principalizationValueOn (bmo : BMOanFam.{u} 𝕜 n 1)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) (W : Opens M) (hW : IsCompact (closure (W : Set M)))
    (hUW : closure (U : Set M) ⊆ (W : Set M)) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict U) :=
  valueOf bmo (disjoinListOn T W hW)
    (disjoinedTriple (restrictTriple T W) (meetLocus_disjoinBound_eq_empty T W hW))
    (disjoinedTriple_bmoClass _ _) (M.restrictLE (subset_closure.trans hUW))
    (isLocalDiffeomorph_restrictLE (subset_closure.trans hUW))
    (isCompact_closure_range_restrictLE (subset_closure.trans hUW) hU hUW)

/-- **The value of the principalization family on `U`**: the value computed with the chosen
shrinking open `shrinkOpen U hU`. -/
noncomputable def principalizationValue (bmo : BMOanFam.{u} 𝕜 n 1)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict U) :=
  principalizationValueOn bmo T U hU (shrinkOpen U hU) (isCompact_closure_shrinkOpen U hU)
    (closure_subset_shrinkOpen U hU)

/-- The value has no empty centres (Kollár's convention on empty blow-ups, [Kol07, 32]). -/
theorem noEmptyCenters_principalizationValue (bmo : BMOanFam.{u} 𝕜 n 1)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    (principalizationValue bmo T U hU).NoEmptyCenters :=
  AnalyticManifold.BlowUpSequence.noEmptyCenters_eraseEmpty _

end Hironaka.Manifold
