/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.LocalFunctorFam
public import Hironaka.Resolution.Analytic.OrderReduction.BDFamCompat
public import Hironaka.Resolution.Analytic.OrderReduction.GlobalizeFam
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.OrderReduction.BDFamClauses
public import Hironaka.Resolution.Analytic.OrderReduction.BDFamComm
public import Hironaka.Resolution.Analytic.OrderReduction.BDFamIndiff
public import Hironaka.Resolution.Analytic.OrderReduction.BDFamOrder
public import Hironaka.Resolution.Analytic.OrderReduction.GlobalizeFamClauses
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Theorem 103 in the compatible-family form

The order-reduction functor `BO_{n,m}` of [Kol07, Theorem 103], assembled in the form suited to
non-compact analytic manifolds: the structure `BOanFam 𝕜 n m` (`Functor/Family.lean`), whose values
are compatible families of finite blow-up sequences over the relatively compact open subsets, from
the marked structures `BMOanFam 𝕜 (n - 1) s` at every mark `s`, Kollár's hypothesis "assume that
(69) holds in dimensions `< n`". The assembly follows the proof of Theorem 103:

* `bdanFam`, `bdanFamDataOfInput` — Lemma 102's functor `BD_{n,s,j}` ([Kol07, Lemma 102]) as a
  compatible family (`BDanFam`, `BDFam.lean`: on each relatively compact open, from the marked
  family one dimension down at the mark `tuningParam s`, the tuning of Step 1 being applied inside
  Lemma 102 as in Kollár's proof) and as the data `BDanFamData ψ₀ s` (`FamilyData.lean`) at every
  mark, its clauses being proved in `BDFamOrder.lean`, `BDFamComm.lean`, `BDFamIndiff.lean` and
  `BDFamCompat.lean`; at an empty member the family is trivial ([Kol07, 32]).
* `hfLocalFunctorFam`, `localFunctorFam` — the local family functor on the class `LocalMCClass m`
  of triples with a global hypersurface of maximal contact: Steps 1 and 2 of the proof on each
  relatively compact open (`localFunctorFamOn`, `LocalFunctorFam.lean`: the tuning, Step 2.1
  member by member along a shrinking chain of opens, Step 2.2 at the hypersurface), with its
  commutation with local analytic isomorphisms (Theorem 103 (2) for the local functor, through the
  independence of Step 2.3) and its indifference to empty members. The general form is over the
  data `HFData` of Step 2 (`HFamData.lean`), of which Lemma 102's data is the instance.
* `BO.BOanFamOfInputOf`, `BO.BOanFamOfInput` — Step 3 of the proof: the descent of the local
  family functor to the class `BOClass m` along covers by pieces with maximal contact
  (`globalizeFam`, `GlobalizeFam.lean`), with the clauses of Theorem 103 descended
  (`GlobalizeFamClauses.lean`).

`BO.BOanFamOfInput 𝕜 n inp m` is the first reduction step of the order-reduction tower
(`theorem103FamStar`, `Stage/InstancesFam.lean`); its clause (3), the commutation with closed
embeddings when the boundary is empty, is proved in `ClosedEmbeddingFam.lean`. Włodarczyk's
modified algorithm (the proof of [Wlo09, Theorem 7.4.1]: the components on which the ideal has
become the ideal of a smooth hypersurface are left alone) is the same assembly at other data of
Step 2 (`Modified/`).
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace AnalyticManifold IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace BO

open _root_.Manifold

/-! ### Lemma 102's family data from the marked families one dimension down -/

/-- Lemma 102's functor at the member `j` as a compatible family ([Kol07, Lemma 102]): the
sequence `BDanFam` (`BDFam.lean`) on every relatively compact open, without empty centres
(`noEmptyCenters_BDanFam`), compatible under restriction (`BDanFam_compat`). -/
noncomputable def bdanFam (m : ℕ) (inp : BMOanFam 𝕜 (n - 1) (tuningParam m))
    {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass m T)
    (j : T.F.ι) : CompatibleFamily T where
  seqOn U hU := BDanFam m inp T hT j U hU
  noEmptyCenters U hU := noEmptyCenters_BDanFam m inp T hT j U hU
  compat _ _ hU hV hUV := BDanFam_compat inp T hT j hU hV hUV

/-- The value of `bdanFam` on an open is `BDanFam`, by definition. -/
theorem bdanFam_seqOn (m : ℕ) (inp : BMOanFam 𝕜 (n - 1) (tuningParam m))
    {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass m T)
    (j : T.F.ι) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (bdanFam m inp T hT j).seqOn U hU = BDanFam m inp T hT j U hU := rfl

/-- Lemma 102's family data at every mark ([Kol07, Lemma 102]) from the marked families one
dimension down: at the mark `s`, `bdanFam` on the input at the mark `tuningParam s`, the mark of
the tuned ideal sheaf (Step 1 of the proof of Theorem 103, applied inside Lemma 102), with the
order clause and Lemma 102 (1) (`BDFamOrder.lean`), the commutation with local analytic
isomorphisms (`BDFamComm.lean`) and the indifference to empty members (`BDFamIndiff.lean`). -/
noncomputable def bdanFamDataOfInput (inp : ∀ s : ℕ, BMOanFam 𝕜 (n - 1) s) (s : ℕ) :
    BDanFamData ψ₀ s where
  fam T hT j := bdanFam s (inp (tuningParam s)) T hT j
  isOfOrder T hT j U hU := BDanFam_isOfOrder (inp (tuningParam s)) T hT j U hU
  cosupp_disjoint T hT j U hU := BDanFam_cosupp_disjoint (inp (tuningParam s)) T hT j U hU
  commutesWithLocalIsos T g hg hT hT' j U' hU' :=
    BDanFam_commutesWithLocalIsos (inp (tuningParam s)) T g hg hT hT' j U' hU'
  indifferentToEmptyMembers T F' hsnc' e he he' hT hT' i U hU :=
    BDanFam_indifferentToEmptyMembers (inp (tuningParam s)) T F' hsnc' e he he' hT hT' i U hU

/-- The family of `bdanFamDataOfInput` at the mark `s` is `bdanFam` on the input at the mark
`tuningParam s`, by definition. -/
theorem bdanFamDataOfInput_fam (inp : ∀ s : ℕ, BMOanFam 𝕜 (n - 1) s) (s : ℕ)
    {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T)
    (j : T.F.ι) : (bdanFamDataOfInput inp s).fam T hT j = bdanFam s (inp (tuningParam s)) T hT j :=
  rfl

/-- At an empty member Lemma 102's family is the trivial one ([Kol07, 32]): the hypothesis under
which the local family functor commutes with local analytic isomorphisms
(`localFunctorFam_commutesWithLocalIsos`). -/
theorem bdanFamDataOfInput_fam_eq_nil_of_hyp_eq_empty (inp : ∀ s : ℕ, BMOanFam 𝕜 (n - 1) s)
    (s : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass s T) (j : T.F.ι) (hj : T.F.hyp j = ∅) :
    (bdanFamDataOfInput inp s).fam T hT j = CompatibleFamily.nil T := by
  ext U hU
  exact BDanFam_eq_nil_of_hyp_eq_empty (inp (tuningParam s)) T hT j hj U hU

/-! ### The local family functor -/

/-- The local family functor of the data `d` of Step 2 (`HFData`, `HFamData.lean`) on the class
`LocalMCClass m`: Steps 1 and 2 of the proof of [Kol07, Theorem 103] on every relatively compact
open (`hfLocalFunctorFamOn`, `LocalFunctorFam.lean`), without empty centres and compatible under
restriction. -/
noncomputable def hfLocalFunctorFam (m : ℕ) (d : HFData ψ₀ (tuningParam m)) :
    AnalyticFamilyFunctor ψ₀ (AnalyticTriple.LocalMCClass m) where
  fam T hL :=
    ⟨fun U hU => hfLocalFunctorFamOn m d T hL U hU,
      fun U hU => hfLocalFunctorFamOn_noEmptyCenters m d T hL U hU,
      fun _ _ hU hV hUV => hfLocalFunctorFamOn_compat d T hL hU hV hUV⟩

/-- The value of `hfLocalFunctorFam` on an open is `hfLocalFunctorFamOn`, by definition. -/
theorem hfLocalFunctorFam_fam_seqOn (m : ℕ) (d : HFData ψ₀ (tuningParam m))
    {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hL : AnalyticTriple.LocalMCClass m T)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((hfLocalFunctorFam m d).fam T hL).seqOn U hU = hfLocalFunctorFamOn m d T hL U hU := rfl

/-- The local family functor of data `d` of Step 2 commutes with local analytic isomorphisms
(Theorem 103 (2) for the local functor, [Kol07, 104, Step 2.3]) when the family of Step 2.1's data
is trivial at an empty member (`hnil`): a pull-back need not be surjective and may empty a member
that Step 2.1 iterates over. -/
theorem hfLocalFunctorFam_commutesWithLocalIsos (m : ℕ) (d : HFData ψ₀ (tuningParam m))
    (hnil : ∀ {M' : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ M')
      (hT' : AnalyticTriple.BOClass (tuningParam m) T') (j : T'.F.ι),
      T'.F.hyp j = ∅ → d.bd₁.fam T' hT' j = CompatibleFamily.nil T') :
    (hfLocalFunctorFam m d).CommutesWithLocalIsos := by
  intro M N T T' g hg hpb hL hL' U' hU'
  obtain rfl := hpb.eq (T.isPullbackOf_pullback g hg)
  exact hfLocalFunctorFamOn_commutesWithLocalIsos d hnil T g hg hL hL' U' hU'

/-- The local family functor of data `d` of Step 2 is indifferent to empty boundary members. -/
theorem hfLocalFunctorFam_indifferentToEmptyMembers (m : ℕ) (d : HFData ψ₀ (tuningParam m)) :
    (hfLocalFunctorFam m d).IndifferentToEmptyMembers :=
  fun T F' hsnc' e he he' hL hL' U hU =>
    hfLocalFunctorFamOn_indifferentToEmptyMembers d T F' hsnc' e he he' hL hL' U hU

variable (bd : ∀ s : ℕ, BDanFamData ψ₀ s)

/-- The local family functor on `LocalMCClass m` for Lemma 102's data `bd` at every mark: Steps 1
and 2 of the proof of [Kol07, Theorem 103] on every relatively compact open
(`localFunctorFamOn`). -/
noncomputable def localFunctorFam (m : ℕ) :
    AnalyticFamilyFunctor ψ₀ (AnalyticTriple.LocalMCClass m) :=
  hfLocalFunctorFam m (HFData.ofBDanFamData bd (tuningParam m))

/-- The value of `localFunctorFam` on an open is `localFunctorFamOn`, by definition. -/
theorem localFunctorFam_fam_seqOn (m : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hL : AnalyticTriple.LocalMCClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((localFunctorFam bd m).fam T hL).seqOn U hU = localFunctorFamOn bd m T hL U hU := rfl

/-- Theorem 103 (2) for the local family functor ([Kol07, 104, Step 2.3]): it commutes with local
analytic isomorphisms when the data's family at an empty member is trivial at every mark. -/
theorem localFunctorFam_commutesWithLocalIsos
    (hnil : ∀ (s' : ℕ) {M' : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ M')
      (hT' : AnalyticTriple.BOClass s' T') (j : T'.F.ι),
      T'.F.hyp j = ∅ → (bd s').fam T' hT' j = CompatibleFamily.nil T')
    (m : ℕ) : (localFunctorFam bd m).CommutesWithLocalIsos :=
  hfLocalFunctorFam_commutesWithLocalIsos m (HFData.ofBDanFamData bd (tuningParam m))
    (hnil (tuningParam m))

/-- The local family functor is indifferent to empty boundary members. -/
theorem localFunctorFam_indifferentToEmptyMembers (m : ℕ) :
    (localFunctorFam bd m).IndifferentToEmptyMembers :=
  hfLocalFunctorFam_indifferentToEmptyMembers m (HFData.ofBDanFamData bd (tuningParam m))

end BO

/-! ### The structure `BOanFam` at the standard model -/

section

variable (𝕜 : Type) [RCLike 𝕜] (n : ℕ)

/-- The structure `BOanFam 𝕜 n m` from the marked structures one dimension down, given that the
local family functor commutes with local analytic isomorphisms (`hcomm`, the hypothesis of Step 3
of the proof of [Kol07, Theorem 103]): the descent `globalizeFam` (`GlobalizeFam.lean`) of the
local family functor to the class `BOClass m`, with the four clauses of `BOanFam`. The order
clause and the output clause descend from the local functor along the covers
(`isOfOrderGe_of_agreeFam`, `ord_lt_of_agreeFam`, `GlobalizeFamClauses.lean`; the output clause
for the controlled transform follows from the one for the weak transform because along a sequence
of order `≥ m` starting from an ideal sheaf of order `≤ m` the two transforms agree); the descent
commutes with local analytic isomorphisms (`globalizeFam_commutesWithLocalIsos`) and is
indifferent to empty members (`indifferentToEmptyMembers_of_agreeFam`). -/
noncomputable def BO.BOanFamOfInputOf (inp : ∀ s : ℕ, BMOanFam.{u} 𝕜 (n - 1) s) (m : ℕ)
    (hcomm : (BO.localFunctorFam
      (BO.bdanFamDataOfInput (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) inp)
      m).CommutesWithLocalIsos) :
    BOanFam.{u} 𝕜 n m where
  functor := AnalyticFamilyFunctor.globalizeFam (BO.localFunctorFam (BO.bdanFamDataOfInput inp) m)
    hcomm
  isOfOrderGe T hT U hU :=
    AnalyticFamilyFunctor.isOfOrderGe_of_agreeFam _ _
      (fun T hL => AnalyticFamilyFunctor.globalizeFam_fam_eq _ hcomm T hL)
      (AnalyticFamilyFunctor.globalizeFam_commutesWithLocalIsos _ hcomm)
      (fun T hL U hU => localFunctorFamOn_isOfOrderGe _ T hL U hU) T hT U hU
  ord_lt T hT U hU x := by
    have hge := AnalyticFamilyFunctor.isOfOrderGe_of_agreeFam
      (BO.localFunctorFam (BO.bdanFamDataOfInput inp) m) _
      (fun T hL => AnalyticFamilyFunctor.globalizeFam_fam_eq _ hcomm T hL)
      (AnalyticFamilyFunctor.globalizeFam_commutesWithLocalIsos _ hcomm)
      (fun T hL U hU => localFunctorFamOn_isOfOrderGe _ T hL U hU) T hT U hU
    rw [(FiniteSuccession.isOfOrder_of_isOfOrderGe_of_ord_le _ hge
      (boClass_pullback_inclusion_of_boClass T U hT).2.1).markedTransformSeq_eq_weakTransformSeq
      (Fin.last _)]
    exact AnalyticFamilyFunctor.ord_lt_of_agreeFam _ _
      (fun T hL => AnalyticFamilyFunctor.globalizeFam_fam_eq _ hcomm T hL)
      (AnalyticFamilyFunctor.globalizeFam_commutesWithLocalIsos _ hcomm)
      (fun T hL U hU x => localFunctorFamOn_ord_lt _ T hL U hU x) T hT U hU x
  commutesWithLocalIsos := AnalyticFamilyFunctor.globalizeFam_commutesWithLocalIsos _ hcomm
  indifferentToEmptyMembers :=
    AnalyticFamilyFunctor.indifferentToEmptyMembers_of_agreeFam _ _
      (fun T hL => AnalyticFamilyFunctor.globalizeFam_fam_eq _ hcomm T hL)
      (AnalyticFamilyFunctor.globalizeFam_commutesWithLocalIsos _ hcomm)
      (BO.localFunctorFam_indifferentToEmptyMembers _ m)

/-- Order reduction for ideals in the compatible-family form ([Kol07, Theorem 103]): the structure
`BOanFam 𝕜 n m` from the marked structures `BMOanFam 𝕜 (n - 1) s` at every mark, without further
hypothesis, the local family functor commuting with local analytic isomorphisms because Lemma 102's
family is trivial at an empty member (`bdanFamDataOfInput_fam_eq_nil_of_hyp_eq_empty`). This is
the first reduction step of the order-reduction tower (`theorem103FamStar`,
`Stage/InstancesFam.lean`). -/
noncomputable def BO.BOanFamOfInput (inp : ∀ s : ℕ, BMOanFam.{u} 𝕜 (n - 1) s) (m : ℕ) :
    BOanFam.{u} 𝕜 n m :=
  BO.BOanFamOfInputOf 𝕜 n inp m
    (BO.localFunctorFam_commutesWithLocalIsos _
      (BO.bdanFamDataOfInput_fam_eq_nil_of_hyp_eq_empty inp) m)

/-- The family functor of `BO.BOanFamOfInput` is the descent of the local family functor, by
definition. -/
theorem BO.BOanFamOfInput_functor (inp : ∀ s : ℕ, BMOanFam.{u} 𝕜 (n - 1) s) (m : ℕ) :
    (BO.BOanFamOfInput 𝕜 n inp m).functor =
      AnalyticFamilyFunctor.globalizeFam (BO.localFunctorFam (BO.bdanFamDataOfInput inp) m)
        (BO.localFunctorFam_commutesWithLocalIsos _
          (BO.bdanFamDataOfInput_fam_eq_nil_of_hyp_eq_empty inp) m) := rfl

end

end Hironaka.Manifold
