/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BDIndiff
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBCore
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBIndiff
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBOrder
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBComm

/-!
# The modified first step: the modified core as the data of the maximal-contact step

The structure `HFamData` (with `HFData`) collects the four properties of the family data of
[Kol07, Lemma 102] which the link of [Kol07, Theorem 103, Step 2.2] uses: the family, its order
clause, its commutation with local analytic isomorphisms, and its indifference to empty boundary
members indexed by the member. The assembly of the second step of the order reduction is stated
over it. This module gives **the modified core as such data at the mark `1`**:
`BMOmod.hFamDataMod R hRo hRc hRi : HFamData (refl) 1`, from the modified functor `R` one
dimension down with its three properties `hRo`, `hRc`, `hRi` (hypotheses here), through
`coreModFam`, `coreModOn_isOfOrderGe`, `coreModOn_commutesWithLocalIsos` and
`coreModOn_indifferentToEmptyMembers`. The exact-order clause and the disjointness of cosupports of
[Kol07, Lemma 102] are not part of the structure: the modified core does not satisfy them, the
stopped components keeping order `1` ("the algorithm is stopped", [Wlo09, Theorem 7.4.1]).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Hironaka.Local
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
  (R : AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (AnalyticTriple.BMOClass 1))
  (hRo : ∀ {N : AnalyticManifold.{u} 𝕜 (Fin (n - 1) → 𝕜)}
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) N)
    (hT' : AnalyticTriple.BMOClass 1 T') (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
    ((R.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
  (hRc : R.CommutesWithLocalIsos) (hRi : R.IndifferentToEmptyMembers)

/-- **The modified core as the data of the maximal-contact step at the mark `1`**
([Wlo09, Theorem 7.4.1]): at a triple of the class of `BO_{n,1}` and a member `j`, the modified core
`coreModFam R T j`, with the order clause (`coreModOn_isOfOrderGe`), the commutation
(`coreModOn_commutesWithLocalIsos`) and the indifference (`coreModOn_indifferentToEmptyMembers`)
from the three properties `hRo`, `hRc`, `hRi` of the functor one dimension down. -/
def hFamDataMod : HFamData (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) 1 where
  fam T hT j := coreModFam R T j ⟨hT.1, hT.2.2⟩
  isOfOrderGe T hT j U hU := coreModOn_isOfOrderGe R T j ⟨hT.1, hT.2.2⟩ hT.2.1 hRo U hU
  commutesWithLocalIsos T g hg hT hT' j U' hU' :=
    coreModOn_commutesWithLocalIsos R T j ⟨hT.1, hT.2.2⟩ g hg ⟨hT'.1, hT'.2.2⟩ hRc U' hU'
  indifferentToEmptyMembers T F' hsnc' e he he' hT hT' i U hU :=
    coreModOn_indifferentToEmptyMembers R T F' hsnc' e he i he' hRi ⟨hT.1, hT.2.2⟩
      ⟨hT'.1, hT'.2.2⟩ U hU

theorem hFamDataMod_fam {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BOClass 1 T) (j : T.F.ι) :
    (hFamDataMod R hRo hRc hRi).fam T hT j = coreModFam R T j ⟨hT.1, hT.2.2⟩ := rfl

end Hironaka.Manifold.BMOmod

end
