/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBData
import Hironaka.Resolution.Analytic.OrderReduction.BDFamClauses
import Hironaka.Resolution.Analytic.OrderReduction.BDFamComm
import Hironaka.Resolution.Analytic.OrderReduction.BDFamIndiff
import Hironaka.Resolution.Analytic.OrderReduction.BDFamOrder
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The modified first step: the data of the second step at the mark `1`, and the local functor

The modified first step of [Wlo09, Theorem 7.4.1] is the second step of [Kol07, Theorem 103] at
the mark `1` with two changes of data and nothing else. Its Step 1a "moves the old divisors as
before": this is [Kol07, Theorem 103, Step 2.1] on the family data of [Kol07, Lemma 102] from the
**unmodified** marked order reduction one dimension down, `bmo (n−1)`, at the mark `1` (with the
modified functor one dimension down the stopped points would stay on the strict transform of an
old divisor, against the transversality to the old divisors which [Wlo09, Theorem 2.0.3] promises).
Its Step 1b replaces the maximal-contact step at the greatest member by the modified core. The two
are the components of one datum of the second step, `stepBData : HFData (refl) (tuningParam 1)`:
`bd₁ = bdanFamDataOne bmo₁` (the data of [Kol07, Lemma 102], `bdanFamDataOfInput`, at the single
mark `1 = tuningParam 1`, `tuningParam_one`: the input at the mark `1` is the input at the mark
`1!`), and `hf = hFamDataMod R hRo hRc hRi` (the modified core as the data of the maximal-contact
step at the mark `1`). **The local functor of the modified first step** on the local
maximal-contact class is the assembly of the second step at that datum, stated over `HFData`:

* `stepBLocalFunctorFam = hfLocalFunctorFam 1 stepBData`, an
  `AnalyticFamilyFunctor (refl) (LocalMCClass 1)`;
* its three properties: `stepBLocalFunctorFam_commutesWithLocalIsos`
  (`hfLocalFunctorFam_commutesWithLocalIsos`, with the triviality of the family of
  [Kol07, Lemma 102] at an empty member, `BDanFam_eq_nil_of_hyp_eq_empty`),
  `stepBLocalFunctorFam_indifferentToEmptyMembers`, and `stepBLocalFunctorFamOn_isOfOrderGe`
  ([Kol07, Definition 66 (2′)–(4′)] at the mark `1` on each open,
  `hfLocalFunctorFamOn_isOfOrderGe`).

The descent from the local class to `BOClass 1` is `StepBGlobal.lean`. The functor one dimension
down enters as `R` with its three properties `hRo`, `hRc`, `hRi` as hypotheses, the unmodified
marked order reduction one dimension down as `bmo₁`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- **The family data of [Kol07, Lemma 102] at the mark `1` from the unmodified marked order
reduction one dimension down** (Step 1a of the modified first step is [Kol07, Theorem 103, Step 2.1]
"as before", [Wlo09, Theorem 7.4.1]): `bdanFamDataOfInput` at the single mark `1 = tuningParam 1`,
i.e. `bdanFam` on `bmo₁` with its five properties (`BDanFam_isOfOrder`, `BDanFam_compat`,
`BDanFam_cosupp_disjoint`, `BDanFam_commutesWithLocalIsos`, `BDanFam_indifferentToEmptyMembers`). -/
def bdanFamDataOne (bmo₁ : BMOanFam.{u} 𝕜 (n - 1) 1) :
    BDanFamData.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (tuningParam 1) where
  fam T hT j := BO.bdanFam (tuningParam 1) bmo₁ T hT j
  isOfOrder T hT j U hU := BDanFam_isOfOrder (m := tuningParam 1) bmo₁ T hT j U hU
  cosupp_disjoint T hT j U hU := BDanFam_cosupp_disjoint (m := tuningParam 1) bmo₁ T hT j U hU
  commutesWithLocalIsos T g hg hT hT' j U' hU' :=
    BDanFam_commutesWithLocalIsos (m := tuningParam 1) bmo₁ T g hg hT hT' j U' hU'
  indifferentToEmptyMembers T F' hsnc' e he he' hT hT' i U hU :=
    BDanFam_indifferentToEmptyMembers (m := tuningParam 1) bmo₁ T F' hsnc' e he he' hT hT' i
      U hU

theorem bdanFamDataOne_fam (bmo₁ : BMOanFam.{u} 𝕜 (n - 1) 1)
    {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BOClass (tuningParam 1) T) (j : T.F.ι) :
    (bdanFamDataOne bmo₁).fam T hT j = BO.bdanFam (tuningParam 1) bmo₁ T hT j := rfl

/-- At an empty member the family of the data at the mark `1` is the trivial one
(`BDanFam_eq_nil_of_hyp_eq_empty`; [Kol07, 32]). -/
theorem bdanFamDataOne_fam_eq_nil_of_hyp_eq_empty (bmo₁ : BMOanFam.{u} 𝕜 (n - 1) 1)
    {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BOClass (tuningParam 1) T) (j : T.F.ι) (hj : T.F.hyp j = ∅) :
    (bdanFamDataOne bmo₁).fam T hT j = CompatibleFamily.nil T := by
  ext U hU
  exact BDanFam_eq_nil_of_hyp_eq_empty (m := tuningParam 1) bmo₁ T hT j hj U hU

variable (R : AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (AnalyticTriple.BMOClass 1))
  (hRo : ∀ {N : AnalyticManifold.{u} 𝕜 (Fin (n - 1) → 𝕜)}
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) N)
    (hT' : AnalyticTriple.BMOClass 1 T') (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
    ((R.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
  (hRc : R.CommutesWithLocalIsos) (hRi : R.IndifferentToEmptyMembers)
  (bmo₁ : BMOanFam.{u} 𝕜 (n - 1) 1)

/-- **The datum of the second step for the modified first step at the mark `1`**
([Wlo09, Theorem 7.4.1]): the data of [Kol07, Theorem 103, Step 2.1] from the unmodified marked
order reduction one dimension down at the mark `1` (`bdanFamDataOne`), and the modified core as the
data of the maximal-contact step (`hFamDataMod`, at the mark `1 = tuningParam 1`). -/
def stepBData : HFData.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (tuningParam 1) :=
  ⟨bdanFamDataOne bmo₁, hFamDataMod R hRo hRc hRi⟩

theorem stepBData_bd₁ : (stepBData R hRo hRc hRi bmo₁).bd₁ = bdanFamDataOne bmo₁ := rfl

theorem stepBData_hf : (stepBData R hRo hRc hRi bmo₁).hf = hFamDataMod R hRo hRc hRi := rfl

/-- **The local functor of the modified first step** on the local maximal-contact class at the mark
`1`: the assembly of the second step (`hfLocalFunctorFam`) at the modified datum, i.e. the chain of
[Kol07, Theorem 103, Step 2.1] from the marked order reduction one dimension down, the triple of
Step 2.2 at its last stage, the modified core at the greatest member, read on the lifted range,
restricted and cleaned; on each relatively compact open, compatible, without empty centres
([Wlo09, Theorem 7.4.1]). -/
def stepBLocalFunctorFam :
    AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (AnalyticTriple.LocalMCClass 1) :=
  BO.hfLocalFunctorFam 1 (stepBData R hRo hRc hRi bmo₁)

theorem stepBLocalFunctorFam_fam_seqOn {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hL : AnalyticTriple.LocalMCClass 1 T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((stepBLocalFunctorFam R hRo hRc hRi bmo₁).fam T hL).seqOn U hU =
      BO.hfLocalFunctorFamOn 1 (stepBData R hRo hRc hRi bmo₁) T hL U hU := rfl

/-- [Kol07, Theorem 103 (2)] for the local functor of the modified first step: it commutes with
local analytic isomorphisms (`hfLocalFunctorFam_commutesWithLocalIsos`; the data of Step 2.1 is
trivial at an empty member, `bdanFamDataOne_fam_eq_nil_of_hyp_eq_empty`). -/
theorem stepBLocalFunctorFam_commutesWithLocalIsos :
    (stepBLocalFunctorFam R hRo hRc hRi bmo₁).CommutesWithLocalIsos :=
  BO.hfLocalFunctorFam_commutesWithLocalIsos 1 (stepBData R hRo hRc hRi bmo₁)
    fun T' hT' j hj => bdanFamDataOne_fam_eq_nil_of_hyp_eq_empty bmo₁ T' hT' j hj

/-- The counterpart, for boundary members, of the empty blow-up convention [Kol07, 32], for the
local functor of the modified first step: indifference to empty boundary members
(`hfLocalFunctorFam_indifferentToEmptyMembers`). -/
theorem stepBLocalFunctorFam_indifferentToEmptyMembers :
    (stepBLocalFunctorFam R hRo hRc hRi bmo₁).IndifferentToEmptyMembers :=
  BO.hfLocalFunctorFam_indifferentToEmptyMembers 1 (stepBData R hRo hRc hRi bmo₁)

/-- [Kol07, Definition 66 (2′)–(4′)] at the mark `1` on each open for the local functor of the
modified first step: the value on `U` is of order `≥ 1` for the restricted triple
(`hfLocalFunctorFamOn_isOfOrderGe`: the order clause of Step 2.1 and `coreModOn_isOfOrderGe` of the
modified core through [Kol07, Corollary 85]). -/
theorem stepBLocalFunctorFamOn_isOfOrderGe {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hL : AnalyticTriple.LocalMCClass 1 T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (((stepBLocalFunctorFam R hRo hRc hRi bmo₁).fam T hL).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf :=
  hfLocalFunctorFamOn_isOfOrderGe (stepBData R hRo hRc hRi bmo₁) T hL U hU

end Hironaka.Manifold.BMOmod

end
