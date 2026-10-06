/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
public import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
public import Hironaka.Resolution.Analytic.OrderReduction.HFamData
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.MaximalContactTheorem
import Hironaka.Resolution.Analytic.OrderReduction.LocalFunctorComm
import Hironaka.Resolution.Analytic.Restrict.BoundaryTrace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2 of Theorem 103 as a compatible family: Step 2.2 and the assembly on an open

Step 2 of the proof of [Kol07, Theorem 103] runs on a triple `(X, I, E)` with a global hypersurface
of maximal contact `H`: Step 2.1 clears the transforms of the boundary members from the cosupport
by applying Lemma 102 member by member, and Step 2.2 "restricts everything to the birational
transform of `H`", that is, applies Lemma 102 once more to `(X_r, I_r, H_r + E_r)` at the member
`H_r`, after replacing `I_r` by its tuning once more ([Kol07, 104, Step 2.2]). This module builds
Step 2 in the compatible-family form ([Wlo09, Theorem 2.0.3 (1), (4)]), where the value on a
triple is a finite blow-up sequence on every relatively compact open subset `U`, and Lemma 102's
data are themselves compatible families (`FamilyData.lean`), whose values can only be read on
relatively compact opens.

* `CompatibleFamily.changeTriple` — a compatible family for `T` read as one for another triple on
  the same manifold (the fields do not mention the triple); it feeds the family on the tuned
  triple back to the class of the original.
* `BO.stepHFamFunctor`, `hfStep22Functor` — Lemma 102's family at the
  greatest member of the boundary, as a family functor on the class `stepHClass s` of triples with
  a greatest member (`Step22Defs.lean`); and the family functor of Step 2.2: the data at the
  greatest member at the re-tuned mark `tuningParam s`, applied to the tuned triple and read back
  on the original.
* The triple of Step 2.2 over an arbitrary sequence `L` of order `≥ s` (`step22TripleOf`,
  `Step22Pullback.lean`): its boundary `E^{exc}_r + H_r` has simple normal crossings
  (`isSnc_step22BoundaryOf`), because every centre of `L` lies in the transforms of `H`
  ([Kol07, Theorem 80 (1)]) so that the exceptional divisors meet `H_r` properly (the new
  exceptional divisors "have simple normal crossings with the birational transforms of `H`",
  Step 2.1 of the proof); the triple lies in `BOClass s` and in `stepHClass s`, its greatest
  member being `H_r` (`idxHOf`).
* Step 2 on a relatively compact open `U` (`BO.step2SeqFamOn`): the chain of Step 2.1
  (`Step21Fam.lean`) is run over the exhaustion opens `M_{n₀+r+1} ⊋ ⋯ ⊋ M_{n₀+1} ⊋ M_{n₀} ⊇
  closure U` (`r` the number of nonempty boundary members) and read at its state over `M_{n₀+1}`
  (`step2FamChain`), a sequence `L` on `M_{n₀+1}` of order `≥ s`; the triple of Step 2.2 over `L`
  (`step22TripleFam`) is fed to the family functor of Step 2.2, whose value is read on the lifted
  range of `M_{n₀} ⊆ M_{n₀+1}` at the last stage of `L` (`step2ReadOpen`, `step22FamOn`); the
  result is appended to `L` (`shrinkAppend`, `FamilyChain.lean`), the whole is restricted to `U`
  and its empty blow-ups are deleted ([Kol07, 32]). The triple of Step 2.2 needs the order clause
  of Step 2.1's sequence on the open (the controlled transform is nonzero, the boundary has simple
  normal crossings), which is the invariant carried by the chain's state.
* The values on the class `LocalMCClass s` (`hfStep2FamOn`, with the class's own hypersurface of
  maximal contact chosen) and of the local functor (`localFunctorFamOn`: Step 2 at the mark
  `tuningParam m` on the tuned triple, Step 1 of the proof), with the absence of empty centres.

Every construction comes in two forms: `hf…`, over arbitrary data `d : HFData ψ₀ s` of Step 2
(`HFamData.lean`: Step 2.1's data `d.bd₁` and the data `d.hf` for the hypersurface step at the
re-tuned mark), and the plain form, its instance at Lemma 102's data `HFData.ofBDanFamData bd s`
for `bd : ∀ s, BDanFamData ψ₀ s`, which is how Kollár proceeds. The general form is what the
modified algorithm of Włodarczyk (the proof of [Wlo09, Theorem 7.4.1]) requires, where the
hypersurface step is taken from the modified marked resolution (`Modified/StepBData.lean`).

The clauses of Theorem 103 for these values are proved in `Step22FamFull.lean` (order `≥ s` with
the full boundary), `Step22FamOrdLt.lean` (the order drops), `Step22FamFunctoriality.lean`,
`Step2Assembly.lean` (compatibility under restriction), `Step2AssemblyComm.lean` (commutation
with local analytic isomorphisms, indifference to empty members) and `FamilyIndependence.lean`
(independence of the hypersurface of maximal contact); the compatible family of the local functor
is assembled in `LocalFunctorFam.lean`.
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace AnalyticManifold IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- A compatible family for `T` read as one for another triple `T'` on the same manifold: the
fields (`seqOn`, `noEmptyCenters`, `compat`) do not mention the triple. It feeds the family on the
tuned triple back to the class of the original triple. -/
def CompatibleFamily.changeTriple {T T' : AnalyticTriple ψ₀ M} (C : CompatibleFamily T) :
    CompatibleFamily T' :=
  ⟨C.seqOn, C.noEmptyCenters, C.compat⟩

@[simp] theorem CompatibleFamily.changeTriple_seqOn {T T' : AnalyticTriple ψ₀ M}
    (C : CompatibleFamily T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (C.changeTriple (T' := T')).seqOn U hU = C.seqOn U hU := rfl

namespace BO

open _root_.Manifold

variable {s : ℕ}

/-! ### Lemma 102's family at the greatest member -/

/-- Lemma 102's family applied at the greatest member of the boundary, as a family functor on the
class `stepHClass s` of triples with a greatest member (Step 2.2 of the proof of
[Kol07, Theorem 103] applies Lemma 102 at the member `H`, which the library appends as the greatest
member). -/
noncomputable def stepHFamFunctor (bd : BDanFamData ψ₀ s) :
    AnalyticFamilyFunctor ψ₀ (stepHClass s) :=
  bd.toHFamData.hstepFunctor

theorem stepHFamFunctor_fam (bd : BDanFamData ψ₀ s) (T : AnalyticTriple ψ₀ M)
    (hT : stepHClass s T) : (stepHFamFunctor bd).fam T hT = bd.fam T hT.1 (greatestIdx hT) := rfl

variable [FiniteDimensional 𝕜 E]

/-- The family functor of Step 2.2 of the proof of [Kol07, Theorem 103] over data `hf` for the
hypersurface step at the re-tuned mark ([Kol07, 104, Step 2.2]: "we can again replace `I` by
`W(I)`"): the data at the greatest member, applied to the tuned triple and read back on the class
of the original. -/
noncomputable def _root_.Hironaka.Manifold.hfStep22Functor (hf : HFamData ψ₀ (tuningParam s)) :
    AnalyticFamilyFunctor ψ₀ (stepHClass s) where
  fam T hT :=
    (hf.hstepFunctor.fam (T.tuned s hT.1.1) (stepHClass_tuned hT)).changeTriple

omit M [FiniteDimensional 𝕜 E] in
theorem _root_.Hironaka.Manifold.hfStep22Functor_fam_seqOn [FiniteDimensional 𝕜 E]
    {M : AnalyticManifold.{u} 𝕜 E} (hf : HFamData ψ₀ (tuningParam s)) (T : AnalyticTriple ψ₀ M)
    (hT : stepHClass s T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((hfStep22Functor hf).fam T hT).seqOn U hU =
      (hf.fam (T.tuned s hT.1.1) (AnalyticTriple.boClass_tuned hT.1)
        (greatestIdx (stepHClass_tuned hT))).seqOn U hU := rfl

/-! ### The triple of Step 2.2 over a sequence of order `≥ s` -/

section TripleOf

variable (T : AnalyticTriple ψ₀ M) (s : ℕ) (L : BlowUpSequence ψ₀ M) {H : Set M}

omit [FiniteDimensional 𝕜 E] in
/-- A sequence of order `≥ s` starting with a triple of the class `BOClass s` is of order exactly
`s`: every centre has order at least `s`, and the order at a point is at most `s`. -/
theorem isOfOrderOf (hT : AnalyticTriple.BOClass s T)
    (hge : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) :
    L.toSuccession.IsOfOrder T.I T.F.idealSheaf s :=
  FiniteSuccession.isOfOrder_of_isOfOrderGe_of_ord_le _ hge hT.2.1

/-- The strict transform `H_r` of a hypersurface of maximal contact along a sequence of order `≥ s`
is a closed hypersurface ([Kol07, Theorem 80 (1)]: the centres lie in the transforms of `H`). -/
theorem isClosedSubmanifold_transformHOf (hT : AnalyticTriple.BOClass s T)
    (hge : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) (hH : IsClosedSubmanifold ψ₀ H 1)
    (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1)) :
    IsClosedSubmanifold ψ₀ (transformHOf L H) 1 :=
  (isOfOrderOf T s L hT hge).isClosedSubmanifold_strictTransformSeq_of_le hT.1 hH hle
    (Fin.last _)

/-- Every centre of a sequence of order `≥ s` lies in the transform of the hypersurface of maximal
contact `H` ([Kol07, Theorem 80 (1)]). -/
theorem centersInOf (hT : AnalyticTriple.BOClass s T)
    (hge : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) (hH : IsClosedSubmanifold ψ₀ H 1)
    (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1)) : L.toSuccession.CentersIn H :=
  (isOfOrderOf T s L hT hge).centersIn_of_idealSheaf_le_iteratedDeriv hT.1 hH hle

omit [FiniteDimensional 𝕜 E] in
/-- A sequence of order `≥ s` for `(𝓘, s, E)` is of order `≥ s` for `(𝓘, s, ∅)`: the boundary
condition is weakened. -/
theorem isOfOrderGe_unitOf (hge : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) :
    L.toSuccession.IsOfOrderGe T.I s (⊤) :=
  FiniteSuccession.IsOfOrderGe.unit_of_idealSheaf T.F L.toSuccession T.isSnc hge

omit [FiniteDimensional 𝕜 E] in
/-- The family of exceptional divisors of a sequence of order `≥ s` has simple normal crossings
(the total exceptional set of [Kol07, Definition 25]; the normal crossings from
[Kol07, Definition 66 (3′)]). -/
theorem isSnc_exceptionalOf (hge : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) :
    (exceptionalOf L).IsSnc ψ₀ :=
  FiniteSuccession.isSnc_totalTransformSeq (isOfOrderGe_unitOf T s L hge) (Fin.last _)

/-- "The new exceptional divisors obtained in the process have simple normal crossings with the
birational transforms of `H`" (Step 2.1 of the proof of [Kol07, Theorem 103]): the exceptional
family of a sequence of order `≥ s` has proper simple normal crossings with `H_r`, no exceptional
divisor containing it, because every centre lies in the transforms of `H`. -/
theorem hasSncWithProper_exceptionalOf (hT : AnalyticTriple.BOClass s T)
    (hge : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) (hH : IsClosedSubmanifold ψ₀ H 1)
    (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1)) :
    (exceptionalOf L).HasSncWithProper ψ₀ (transformHOf L H) 1 :=
  L.toSuccession.hasSncWithProper_totalTransformSeq_strictTransformSeq hH
    (centersInOf T s L hT hge hH hle) (isOfOrderGe_unitOf T s L hge) (Fin.last _)

/-- The boundary `E^{exc}_r + H_r` of the triple of Step 2.2 over a sequence of order `≥ s` has
simple normal crossings ("`H_r + E_r` is a simple normal crossing divisor", Step 2.1 of the proof
of [Kol07, Theorem 103]): an exceptional family with proper simple normal crossings with a
hypersurface stays with simple normal crossings when the hypersurface is appended. -/
theorem isSnc_step22BoundaryOf (hT : AnalyticTriple.BOClass s T)
    (hge : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) (hH : IsClosedSubmanifold ψ₀ H 1)
    (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1)) :
    ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀ :=
  HypersurfaceFamily.isSnc_append_of_hasSncWithProper (isSnc_exceptionalOf T s L hge)
    (isClosedSubmanifold_transformHOf T s L hT hge hH hle)
    (hasSncWithProper_exceptionalOf T s L hT hge hH hle)

omit [FiniteDimensional 𝕜 E] in
/-- The triple of Step 2.2 over a sequence of order `≥ s` lies in the class `BOClass s`: the
controlled transform has order `≤ s` everywhere, and finitely many members of its boundary are
nonempty. -/
theorem boClass_step22TripleOf (hT : AnalyticTriple.BOClass s T)
    (hge : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hsnc : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀) :
    AnalyticTriple.BOClass s (step22TripleOf T L hge hsnc) :=
  ⟨hT.1,
    fun x => FiniteSuccession.ord_markedTransformSeq_le L.toSuccession hge hT.2.1 (Fin.last _) x,
    HypersurfaceFamily.finite_nonempty_append _ _
      (finite_nonempty_totalTransformSeq L.toSuccession (Fin.last _))⟩

/-- The index of `H_r` in the boundary of the triple of Step 2.2: the appended, greatest member. -/
def idxHOf (hge : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hsnc : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀) :
    (step22TripleOf T L hge hsnc).F.ι :=
  toLex (Sum.inr PUnit.unit)

omit [FiniteDimensional 𝕜 E] in
/-- The triple of Step 2.2 lies in the class `stepHClass s` of the family functor of Step 2.2,
with `H_r` as its greatest member. -/
theorem stepHClass_step22TripleOf (hT : AnalyticTriple.BOClass s T)
    (hge : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hsnc : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀) :
    stepHClass s (step22TripleOf T L hge hsnc) :=
  ⟨boClass_step22TripleOf T s L hT hge hsnc, ⟨idxHOf T s L hge hsnc, fun k => le_toLex_inr k⟩⟩

end TripleOf

/-! ### Step 2 on a relatively compact open -/

section StepTwo

variable (bd : ∀ s : ℕ, BDanFamData ψ₀ s) (T : AnalyticTriple ψ₀ M) (s : ℕ) (d : HFData ψ₀ s)
  (hT : AnalyticTriple.BOClass s T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- A hypersurface of maximal contact restricted to an open subset is one for the restricted
triple. -/
theorem idealSheaf_preimage_le_iteratedDeriv_inclusion {H : Set M}
    (hH : IsClosedSubmanifold ψ₀ H 1) (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))
    (W : Opens M) :
    (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M W)).idealSheaf ≤
      (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).I.iteratedDeriv (s - 1) :=
  T.idealSheaf_preimage_le_iteratedDeriv_pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)
    hH hle

/-- The next-to-last open `M_{n₀+1}` of the chain of exhaustion opens for Step 2 on `U`: Step 2.1
ends here. -/
noncomputable abbrev step2OpenW : Opens M :=
  chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) (memberCount T s hT + 1)
    (memberCount T s hT)

/-- The last open `M_{n₀} ⊇ closure U` of the chain of exhaustion opens for Step 2 on `U`: Step 2.2
is read at its lifted range. -/
noncomputable abbrev step2OpenV : Opens M :=
  chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) (memberCount T s hT + 1)
    (memberCount T s hT + 1)

theorem closure_step2OpenV_subset :
    closure (step2OpenV T s hT U hU : Set M) ⊆ step2OpenW T s hT U hU :=
  closure_chainOpens_succ_subset _ _ _ (Nat.lt_succ_self _)

theorem step2OpenV_le : step2OpenV T s hT U hU ≤ step2OpenW T s hT U hU :=
  fun _ hx => closure_step2OpenV_subset T s hT U hU (subset_closure hx)

theorem isCompact_closure_step2OpenV : IsCompact (closure (step2OpenV T s hT U hU : Set M)) :=
  isCompact_closure_chainOpens _ _ _ _

theorem le_step2OpenV : U ≤ step2OpenV T s hT U hU :=
  le_chainOpens_last _ hU _

/-- The chain of Step 2.1 for Step 2 on `U`, over data `d`: the nonempty boundary members processed
along the `r + 1` exhaustion opens `M_{n₀+r+1} ⊋ ⋯ ⊋ M_{n₀+1} ⊋ M_{n₀}`, read at its state over
`M_{n₀+1}`; the last link is Step 2.2's. `step2FamChain` is its instance at Lemma 102's data. -/
noncomputable def hfStep2FamChain : ChainState T s (step2OpenW T s hT U hU) :=
  step21FamAux T s d.bd₁ hT
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) (memberCount T s hT + 1))
    (memberCount T s hT + 1) (isCompact_closure_chainOpens _ _ _)
    (fun _ hk => closure_chainOpens_succ_subset _ _ _ hk) (T.F.nonemptyList hT.2.2).reverse
    (Nat.le_succ _)

/-- The chain of Step 2.1 for Step 2 on `U` (Step 2.1 of the proof of [Kol07, Theorem 103]): the
nonempty boundary members processed along the `r + 1` exhaustion opens
`M_{n₀+r+1} ⊋ ⋯ ⊋ M_{n₀+1} ⊋ M_{n₀}`, read at its state over `M_{n₀+1}`; the last link is
Step 2.2's. -/
noncomputable def step2FamChain : ChainState T s (step2OpenW T s hT U hU) :=
  hfStep2FamChain T s (HFData.ofBDanFamData bd s) hT U hU

/-- The open on which Step 2.2 is read: the lifted range of `M_{n₀} ⊆ M_{n₀+1}` at the last stage
of the chain (over data `d`; `step2ReadOpen` is the instance at Lemma 102's data). -/
noncomputable def hfStep2ReadOpen : Opens ((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)) :=
  (hfStep2FamChain T s d hT U hU).L.liftRange (M.restrictLE (step2OpenV_le T s hT U hU))
    (isLocalDiffeomorph_restrictLE _)

/-- The open on which Step 2.2 is read: the lifted range of `M_{n₀} ⊆ M_{n₀+1}` at the last stage
of the chain. -/
noncomputable def step2ReadOpen : Opens ((step2FamChain bd T s hT U hU).L.stage (Fin.last _)) :=
  hfStep2ReadOpen T s (HFData.ofBDanFamData bd s) hT U hU

/-- The open on which Step 2.2 is read is relatively compact (the composite blow-down is proper). -/
theorem isCompact_closure_hfStep2ReadOpen :
    IsCompact (closure (hfStep2ReadOpen T s d hT U hU :
      Set ((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)))) :=
  (hfStep2FamChain T s d hT U hU).L.isCompact_closure_liftRange _ _
    (isCompact_closure_range_restrictLE _ (isCompact_closure_step2OpenV T s hT U hU)
      (closure_step2OpenV_subset T s hT U hU))

/-- The open on which Step 2.2 is read is relatively compact (the composite blow-down is proper). -/
theorem isCompact_closure_step2ReadOpen :
    IsCompact (closure (step2ReadOpen bd T s hT U hU :
      Set ((step2FamChain bd T s hT U hU).L.stage (Fin.last _)))) :=
  isCompact_closure_hfStep2ReadOpen T s (HFData.ofBDanFamData bd s) hT U hU

variable {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1)
  (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))

/-- The triple of Step 2.2 on the open, over data `d`: `step22TripleOf` over the chain's sequence at
`M_{n₀+1}`, for the triple and the hypersurface of maximal contact restricted to `M_{n₀+1}`; its
boundary has simple normal crossings by the order clause carried by the chain's state.
`step22TripleFam` is the instance at Lemma 102's data. -/
noncomputable def hfStep22TripleFam :
    AnalyticTriple ψ₀ ((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)) :=
  step22TripleOf (T.pullback (M.inclusion _) (isLocalDiffeomorph_inclusion M _))
    (hfStep2FamChain T s d hT U hU).L (hfStep2FamChain T s d hT U hU).hge
    (isSnc_step22BoundaryOf _ s _ (boClass_pullback_inclusion_of_boClass T _ hT)
      (hfStep2FamChain T s d hT U hU).hge
      (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M _))
      (idealSheaf_preimage_le_iteratedDeriv_inclusion T s hH hle _))

/-- The triple of Step 2.2 on the open (Step 2.2 of the proof of [Kol07, Theorem 103]):
`step22TripleOf` over the chain's sequence at `M_{n₀+1}`, for the triple and the hypersurface of
maximal contact restricted to `M_{n₀+1}`; its boundary has simple normal crossings by the order
clause carried by the chain's state. -/
noncomputable def step22TripleFam :
    AnalyticTriple ψ₀ ((step2FamChain bd T s hT U hU).L.stage (Fin.last _)) :=
  hfStep22TripleFam T s (HFData.ofBDanFamData bd s) hT U hU hH hle

/-- The triple of Step 2.2 on the open lies in the class of the family functor of Step 2.2. -/
theorem stepHClass_hfStep22TripleFam : stepHClass s (hfStep22TripleFam T s d hT U hU hH hle) :=
  stepHClass_step22TripleOf _ s _ (boClass_pullback_inclusion_of_boClass T _ hT) _ _

/-- The triple of Step 2.2 on the open lies in the class of the family functor of Step 2.2. -/
theorem stepHClass_step22TripleFam : stepHClass s (step22TripleFam bd T s hT U hU hH hle) :=
  stepHClass_hfStep22TripleFam T s (HFData.ofBDanFamData bd s) hT U hU hH hle

/-- The value of Step 2.2 on the open, over data `d`: the family functor of Step 2.2 at the triple
of Step 2.2, read at the lifted range of `M_{n₀} ⊆ M_{n₀+1}`. `step22FamOn` is the instance at
Lemma 102's data. -/
noncomputable def hfStep22FamOn :
    BlowUpSequence ψ₀ (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).restrict
      (hfStep2ReadOpen T s d hT U hU)) :=
  ((hfStep22Functor d.hf).fam (hfStep22TripleFam T s d hT U hU hH hle)
    (stepHClass_hfStep22TripleFam T s d hT U hU hH hle)).seqOn _
    (isCompact_closure_hfStep2ReadOpen T s d hT U hU)

/-- The value of Step 2.2 on the open (Step 2.2 of the proof of [Kol07, Theorem 103]): the family
functor of Step 2.2 at the triple of Step 2.2, read at the lifted range of `M_{n₀} ⊆ M_{n₀+1}`. -/
noncomputable def step22FamOn :
    BlowUpSequence ψ₀ (((step2FamChain bd T s hT U hU).L.stage (Fin.last _)).restrict
      (step2ReadOpen bd T s hT U hU)) :=
  hfStep22FamOn T s (HFData.ofBDanFamData bd s) hT U hU hH hle

/-- The value of Step 2 on the relatively compact open `U`, over data `d` (Step 2 of the proof of
[Kol07, Theorem 103], per open): the chain of Step 2.1 with the value of Step 2.2 appended at the
last link (`shrinkAppend`), restricted to `U`, with its empty blow-ups deleted ([Kol07, 32]).
`step2SeqFamOn` is the instance at Lemma 102's data. -/
noncomputable def hfStep2SeqFamOn : BlowUpSequence ψ₀ (M.restrict U) :=
  (((hfStep2FamChain T s d hT U hU).L.shrinkAppend (M.restrictLE (step2OpenV_le T s hT U hU))
      (isLocalDiffeomorph_restrictLE _) (hfStep22FamOn T s d hT U hU hH hle)).pullback
    (M.restrictLE (le_step2OpenV T s hT U hU)) (isLocalDiffeomorph_restrictLE _)).eraseEmpty

/-- The value of Step 2 on the relatively compact open `U` (Step 2 of the proof of
[Kol07, Theorem 103], per open): the chain of Step 2.1 with the value of Step 2.2 appended at the
last link (`shrinkAppend`), restricted to `U`, with its empty blow-ups deleted ([Kol07, 32]). -/
noncomputable def step2SeqFamOn : BlowUpSequence ψ₀ (M.restrict U) :=
  hfStep2SeqFamOn T s (HFData.ofBDanFamData bd s) hT U hU hH hle

/-- The value of Step 2 on the open has no empty centre ([Kol07, 32]). -/
theorem hfStep2SeqFamOn_noEmptyCenters : (hfStep2SeqFamOn T s d hT U hU hH hle).NoEmptyCenters :=
  BlowUpSequence.noEmptyCenters_eraseEmpty _

end StepTwo

/-! ### The values on the class with a global hypersurface of maximal contact -/

variable (bd : ∀ s : ℕ, BDanFamData ψ₀ s)

/-- Step 2 on an open for a triple of the class `LocalMCClass s`, over data `d`, with the
hypersurface of maximal contact taken from the class (a choice; the value does not depend on it,
`hfStep2SeqFamOn_indep` in `FamilyIndependence.lean`). -/
noncomputable def hfStep2FamOn (s : ℕ) (d : HFData ψ₀ s) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.LocalMCClass s T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    BlowUpSequence ψ₀ (M.restrict U) :=
  hfStep2SeqFamOn T s d hT.1 U hU (Classical.choose (Classical.choose_spec hT.2))
    (Classical.choose_spec (Classical.choose_spec hT.2))

/-- The value on an open of the local functor of Steps 1 and 2 of the proof of
[Kol07, Theorem 103], over data `d` at the mark `tuningParam m`: Step 2 at that mark on the tuned
triple. `localFunctorFamOn` is the instance at Lemma 102's data. -/
noncomputable def hfLocalFunctorFamOn (m : ℕ) (d : HFData ψ₀ (tuningParam m))
    (T : AnalyticTriple ψ₀ M) (hL : AnalyticTriple.LocalMCClass m T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) : BlowUpSequence ψ₀ (M.restrict U) :=
  hfStep2FamOn (tuningParam m) d (T.tuned m hL.1.1) (AnalyticTriple.localMCClass_tuned hL) U hU

/-- The value on an open of the local functor of Steps 1 and 2 of the proof of
[Kol07, Theorem 103]: Step 2 at the mark `tuningParam m` on the tuned triple (the family form of
`localFunctor`, `Assembly.lean`). -/
noncomputable def localFunctorFamOn (m : ℕ) (T : AnalyticTriple ψ₀ M)
    (hL : AnalyticTriple.LocalMCClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    BlowUpSequence ψ₀ (M.restrict U) :=
  hfLocalFunctorFamOn m (HFData.ofBDanFamData bd (tuningParam m)) T hL U hU

/-- The value of the local functor on an open has no empty centre ([Kol07, 32]). -/
theorem hfLocalFunctorFamOn_noEmptyCenters (m : ℕ) (d : HFData ψ₀ (tuningParam m))
    (T : AnalyticTriple ψ₀ M) (hL : AnalyticTriple.LocalMCClass m T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    (hfLocalFunctorFamOn m d T hL U hU).NoEmptyCenters :=
  hfStep2SeqFamOn_noEmptyCenters _ _ _ _ _ _ _ _

end BO

end Hironaka.Manifold
