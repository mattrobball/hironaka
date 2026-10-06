/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step22Fam
import Hironaka.Resolution.Analytic.OrderReduction.TunedLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The family functors of Step 2.2 commute with local analytic isomorphisms

Step 2.3 of the proof of Theorem 103 ([Kol07, 104, Step 2.3]) obtains the functoriality of Step 2.1
"by the corresponding functoriality in (102)", and that of Step 2.2 through the choice of the
hypersurface (Theorems 92 and 97). For the family functors of Step 2.2
(`Step22Fam.lean`), which apply Lemma 102's data at the greatest member of the boundary, the
commutation with local analytic isomorphisms (both clauses of [Kol07, 34.1], in the per-open form
of `AnalyticFamilyFunctor.CommutesWithLocalIsos`) comes from the commutation of the data:

* `BO.greatestIdx_pullback` — the pulled-back triple keeps the index set of the boundary, hence
  its greatest member;
* `HFamData.hstepFunctor_commutesWithLocalIsos`, `stepHFamFunctor_commutesWithLocalIsos` — the
  family at the greatest member commutes with local analytic isomorphisms because the data do,
  the member index being kept;
* `hfStepH_tuned_pullback_seqOn`, `BO.stepH_tuned_pullback_seqOn` — the value of the data at the
  re-tuned mark on the tuned pulled-back triple, at its greatest member, is the pull-back of the
  value on the tuned triple at its greatest member: the tuning commutes with pull-back
  (`tuned_pullback`, `TunedLemmas.lean`) and the greatest member is kept;
* `hfStep22Functor_commutesWithLocalIsos` — the family functor of Step 2.2 commutes with local
  analytic isomorphisms.

The `hf…` declarations are the general forms over data `hf : HFamData ψ₀ (tuningParam s)` for the
hypersurface step (`HFamData.lean`); the plain forms are their instances at Lemma 102's data. The
result enters the transport of the Step 2.2 link along local analytic isomorphisms
(`Step2LinkPrep.lean`).
-/

public section

universe u

open Set Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}
  {s : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- The greatest member of a pulled-back triple of the class `stepHClass s` is the greatest member
of the triple: the pull-back keeps the ordered index set of the boundary, and a linear order has at
most one greatest element. -/
theorem BO.greatestIdx_pullback (T : AnalyticTriple ψ₀ M) (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hT : BO.stepHClass s T)
    (hT' : BO.stepHClass s (T.pullback g hg)) :
    BO.greatestIdx hT' = BO.greatestIdx hT :=
  le_antisymm (BO.le_greatestIdx hT _) (BO.le_greatestIdx hT' _)

omit [FiniteDimensional 𝕜 E] in
/-- The family at the greatest member commutes with local analytic isomorphisms, for data `hf` for
the hypersurface step: the pulled-back triple is the pull-back, its greatest member is the greatest
member (`greatestIdx_pullback`), and the data commute with the member index kept. -/
theorem HFamData.hstepFunctor_commutesWithLocalIsos (hf : HFamData ψ₀ s) :
    hf.hstepFunctor.CommutesWithLocalIsos := by
  intro M N T T' g hg hpb hT hT' U' hU'
  obtain rfl := hpb.eq (T.isPullbackOf_pullback g hg)
  exact (hf.fam_congr_seqOn rfl hT'.1 hT'.1 _ _
    (heq_of_eq (BO.greatestIdx_pullback T g hg hT hT')) U' hU').trans
    (hf.commutesWithLocalIsos T g hg hT.1 hT'.1 (BO.greatestIdx hT) U' hU')

omit [FiniteDimensional 𝕜 E] in
/-- Lemma 102's family at the greatest member commutes with local analytic isomorphisms (the
functoriality
of the application of Lemma 102 in Step 2.2, [Kol07, 104, Step 2.3]): the pulled-back triple is the
pull-back, its greatest member is the greatest member (`greatestIdx_pullback`), and the data of
Lemma 102 commute with the member index kept. -/
theorem stepHFamFunctor_commutesWithLocalIsos (bd₀ : BDanFamData ψ₀ s) :
    (BO.stepHFamFunctor bd₀).CommutesWithLocalIsos :=
  bd₀.toHFamData.hstepFunctor_commutesWithLocalIsos

omit [FiniteDimensional 𝕜 E] M N in
/-- The value of the data `hf` at the re-tuned mark on the tuned pulled-back triple, at its greatest
member, is the pull-back of the value on the tuned triple at its greatest member, with empty
blow-ups deleted ([Kol07, 104, Step 2.3]): the tuning commutes with pull-back (`tuned_pullback`),
the greatest member is kept (`greatestIdx_pullback`), and the data commute with the member index
kept. `BO.stepH_tuned_pullback_seqOn` is the instance at Lemma 102's data. -/
theorem hfStepH_tuned_pullback_seqOn [FiniteDimensional 𝕜 E] {M N : AnalyticManifold.{u} 𝕜 E}
    (hf : HFamData ψ₀ (tuningParam s)) (T : AnalyticTriple ψ₀ M) (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hT : BO.stepHClass s T)
    (hT' : BO.stepHClass s (T.pullback g hg)) (U' : Opens N)
    (hU' : IsCompact (closure (U' : Set N))) :
    (hf.fam ((T.pullback g hg).tuned s hT'.1.1) (AnalyticTriple.boClass_tuned hT'.1)
      (BO.greatestIdx (BO.stepHClass_tuned hT'))).seqOn U' hU' =
      (((hf.fam (T.tuned s hT.1.1) (AnalyticTriple.boClass_tuned hT.1)
          (BO.greatestIdx (BO.stepHClass_tuned hT))).seqOn (AnalyticMap.imageOpens g hg U')
            (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty := by
  have e := AnalyticTriple.tuned_pullback T hT'.1.1 g hg
  have hTt : AnalyticTriple.BOClass (tuningParam s) ((T.tuned s hT'.1.1).pullback g hg) := by
    rw [← e]
    exact AnalyticTriple.boClass_tuned hT'.1
  have hHt : BO.stepHClass (tuningParam s) ((T.tuned s hT'.1.1).pullback g hg) := by
    rw [← e]
    exact BO.stepHClass_tuned hT'
  have hj : HEq (BO.greatestIdx (BO.stepHClass_tuned hT')) (BO.greatestIdx hHt) :=
    heq_of_eq (le_antisymm (BO.le_greatestIdx hHt _)
      (BO.le_greatestIdx (BO.stepHClass_tuned hT') _))
  have hgi : BO.greatestIdx hHt = BO.greatestIdx (BO.stepHClass_tuned hT) :=
    BO.greatestIdx_pullback (T.tuned s hT'.1.1) g hg (BO.stepHClass_tuned hT) hHt
  rw [hf.fam_congr_seqOn e (AnalyticTriple.boClass_tuned hT'.1) hTt _ _ hj U' hU', hgi]
  exact hf.commutesWithLocalIsos (T.tuned s hT'.1.1) g hg (AnalyticTriple.boClass_tuned hT.1) hTt
    (BO.greatestIdx (BO.stepHClass_tuned hT)) U' hU'

/-- The value of Lemma 102's data at the re-tuned mark on the tuned pulled-back triple, at its
greatest member, is the pull-back of the value on the tuned triple at its greatest member, with
empty blow-ups deleted ([Kol07, 104, Step 2.3]): the tuning commutes with pull-back
(`tuned_pullback`), the greatest member is kept (`greatestIdx_pullback`), and the data commute with
the member index kept. -/
theorem BO.stepH_tuned_pullback_seqOn (bd : ∀ s : ℕ, BDanFamData ψ₀ s) (T : AnalyticTriple ψ₀ M)
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hT : BO.stepHClass s T)
    (hT' : BO.stepHClass s (T.pullback g hg)) (U' : Opens N)
    (hU' : IsCompact (closure (U' : Set N))) :
    ((bd (tuningParam s)).fam ((T.pullback g hg).tuned s hT'.1.1)
      (AnalyticTriple.boClass_tuned hT'.1) (BO.greatestIdx (BO.stepHClass_tuned hT'))).seqOn U'
      hU' =
      ((((bd (tuningParam s)).fam (T.tuned s hT.1.1) (AnalyticTriple.boClass_tuned hT.1)
          (BO.greatestIdx (BO.stepHClass_tuned hT))).seqOn (AnalyticMap.imageOpens g hg U')
            (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty :=
  hfStepH_tuned_pullback_seqOn (HFData.ofBDanFamData bd s).hf T g hg hT hT' U' hU'

omit [FiniteDimensional 𝕜 E] in
/-- The family functor of Step 2.2 over data `hf` for the hypersurface step commutes with local
analytic isomorphisms ([Kol07, 104, Step 2.3]; [Kol07, 34.1]). -/
theorem hfStep22Functor_commutesWithLocalIsos [FiniteDimensional 𝕜 E]
    (hf : HFamData ψ₀ (tuningParam s)) : (hfStep22Functor hf).CommutesWithLocalIsos := by
  intro M N T T' g hg hpb hT hT' U' hU'
  obtain rfl := hpb.eq (T.isPullbackOf_pullback g hg)
  exact (hfStep22Functor_fam_seqOn hf (T.pullback g hg) hT' U' hU').trans
    ((hfStepH_tuned_pullback_seqOn hf T g hg hT hT' U' hU').trans
      (congrArg (fun L => (L.pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty)
        (hfStep22Functor_fam_seqOn hf T hT (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).symm))

end Hironaka.Manifold
