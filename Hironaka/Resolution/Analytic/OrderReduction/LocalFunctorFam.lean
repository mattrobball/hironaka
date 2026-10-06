/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step22Fam
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.OrderReduction.GlobalizeFam
import Hironaka.Resolution.Analytic.OrderReduction.LocalFunctorComm
import Hironaka.Resolution.Analytic.OrderReduction.Step22FamFull
import Hironaka.Resolution.Analytic.OrderReduction.Step22FamOrdLt
import Hironaka.Resolution.Analytic.OrderReduction.Step2Assembly
import Hironaka.Resolution.Analytic.OrderReduction.Step2AssemblyComm
import Hironaka.Resolution.Analytic.OrderReduction.TunedLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The local functor of Theorem 103 in the compatible-family form: its clauses

The local functor of Steps 1 and 2 of the proof of [Kol07, Theorem 103], in the compatible-family
form, is `BO.localFunctorFamOn` (`Step22Fam.lean`): on a triple with a global hypersurface of
maximal contact and a relatively compact open `U`, Step 2 at the mark `s = tuningParam m` on the
tuned triple (Step 1), with the hypersurface of maximal contact chosen from the class. This module
proves its clauses, each by transporting the clause of Step 2 (`Step22FamFull.lean`,
`Step22FamOrdLt.lean`, `Step2Assembly.lean`, `Step2AssemblyComm.lean`) across the tuning:

* `localFunctorFamOn_isOfOrderGe` — the value on `U` is a smooth blow-up sequence of order `≥ m`
  starting with the restricted triple ([Kol07, Definition 66]): the clause of Step 2 at the mark `s`
  on the tuned triple, the tuning commuting with the restriction (`tuned_pullback`), carried back
  to the mark `m` by `orderReduction_tuned_iff` (`TunedLemmas.lean`);
* `localFunctorFamOn_ord_lt` — Theorem 103 (1) on `U`: the order of the final transform is `< m`,
  from the clause of Step 2 at the mark `s` by `ord_lt_of_tuned`;
* `hfLocalFunctorFamOn_commutesWithLocalIsos` — Theorem 103 (2), both clauses of [Kol07, 34.1] per
  open, on the class `LocalMCClass m`: the tuning commutes with the pull-back, the hypersurface of
  maximal contact chosen for the pulled-back triple may be replaced by the pull-back of the one
  chosen for the triple (`hfStep2SeqFamOn_indep`, `FamilyIndependence.lean`: Step 2.3 of the proof),
  and Step 2 commutes with local analytic isomorphisms, given that Lemma 102's data take the empty
  value at an empty member (`hnil`);
* `hfLocalFunctorFamOn_indifferentToEmptyMembers` — the value does not see empty boundary members:
  the tuning does not see the boundary, and the chosen hypersurface is the same on both sides, the
  tuned ideal sheaves being equal;
* `hfLocalFunctorFamOn_compat` — the values are compatible under restriction
  ([Wlo09, Theorem 2.0.3 (4)]).

Each statement is proved first in the general form `hf…` over the data `HFData ψ₀ s` of Step 2
(`HFamData.lean`: Lemma 102's data for Step 2.1 and the data of the hypersurface step of Step 2.2
at the re-tuned mark), and then stated for Lemma 102's data `bd : ∀ s, BDanFamData ψ₀ s` as the
instance at `HFData.ofBDanFamData bd`; the general form is what Włodarczyk's modified algorithm
(the proof of [Wlo09, Theorem 7.4.1]) uses with its own data for the hypersurface step
(`Modified/`). The clauses are assembled into the order-reduction family in `BOanFamOfInput.lean`
(`localFunctorFam`, descended by `globalizeFam`).
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- Step 2 with the chosen hypersurface of maximal contact depends on the triple only: the proof of
membership in the class is irrelevant, the chosen hypersurface being a choice from it (general form
over the data `HFData` of Step 2). -/
theorem BO.hfStep2FamOn_congr_triple (s : ℕ) (d : HFData ψ₀ s)
    {N : AnalyticManifold.{u} 𝕜 E} {T₁ T₂ : AnalyticTriple ψ₀ N} (e : T₁ = T₂)
    (h₁ : AnalyticTriple.LocalMCClass s T₁) (h₂ : AnalyticTriple.LocalMCClass s T₂) (U : Opens N)
    (hU : IsCompact (closure (U : Set N))) :
    BO.hfStep2FamOn s d T₁ h₁ U hU = BO.hfStep2FamOn s d T₂ h₂ U hU := by
  subst e
  rfl

/-- The value of the local functor on `U` is a smooth blow-up sequence of order `≥ m` starting with
the restricted triple ([Kol07, Definition 66]; the order clause of [Kol07, Theorem 103]), in the
general form over the data `HFData` of Step 2: the clause of Step 2 at the mark `s = tuningParam m`
on the tuned triple (`hfStep2SeqFamOn_isOfOrderGe`), the tuning commuting with the restriction
(`tuned_pullback`), carried back to the mark `m` by `orderReduction_tuned_iff`. -/
theorem hfLocalFunctorFamOn_isOfOrderGe {m : ℕ} (d : HFData ψ₀ (tuningParam m))
    {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N) (hL : AnalyticTriple.LocalMCClass m T)
    (U : Opens N) (hU : IsCompact (closure (U : Set N))) :
    (BO.hfLocalFunctorFamOn m d T hL U hU).toSuccession.IsOfOrderGe
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I m
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).F.idealSheaf := by
  have h := hfStep2SeqFamOn_isOfOrderGe d (T.tuned m hL.1.1)
    (AnalyticTriple.localMCClass_tuned hL).1 U hU
    (Classical.choose (Classical.choose_spec (AnalyticTriple.localMCClass_tuned hL).2))
    (Classical.choose_spec (Classical.choose_spec (AnalyticTriple.localMCClass_tuned hL).2))
  rw [← AnalyticTriple.tuned_pullback T hL.1.1 (N.inclusion U) (isLocalDiffeomorph_inclusion N U)]
    at h
  exact (AnalyticTriple.orderReduction_tuned_iff _
    (boClass_pullback_inclusion_of_boClass T U hL.1) _).mp h

/-- The value of the local functor on `U` is a smooth blow-up sequence of order `≥ m` starting with
the restricted triple ([Kol07, Definition 66]; the order clause of [Kol07, Theorem 103]): the clause
of Step 2 at the mark `s = tuningParam m` on the tuned triple, carried back to the mark `m` by
`orderReduction_tuned_iff`. -/
theorem localFunctorFamOn_isOfOrderGe {m : ℕ} (bd : ∀ s : ℕ, BDanFamData ψ₀ s)
    {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N) (hL : AnalyticTriple.LocalMCClass m T)
    (U : Opens N) (hU : IsCompact (closure (U : Set N))) :
    (BO.localFunctorFamOn bd m T hL U hU).toSuccession.IsOfOrderGe
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I m
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).F.idealSheaf :=
  hfLocalFunctorFamOn_isOfOrderGe (HFData.ofBDanFamData bd (tuningParam m)) T
    hL U hU

/-- Theorem 103 (1) for the value of the local functor on `U`: the final weak transform of `𝓘|_U`
has order `< m` at every point. The clause of Step 2 at the mark `s = tuningParam m` on the tuned
triple (`step2SeqFamOn_ord_lt`) is carried back to `(𝓘, m)` by `ord_lt_of_tuned`. -/
theorem localFunctorFamOn_ord_lt {m : ℕ} (bd : ∀ s : ℕ, BDanFamData ψ₀ s)
    {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N) (hL : AnalyticTriple.LocalMCClass m T)
    (U : Opens N) (hU : IsCompact (closure (U : Set N)))
    (x : (BO.localFunctorFamOn bd m T hL U hU).toSuccession.stage (Fin.last _)) :
    ((BO.localFunctorFamOn bd m T hL U hU).toSuccession.weakTransformSeq
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I (Fin.last _)).ord x <
      (m : ℕ∞) := by
  refine AnalyticTriple.ord_lt_of_tuned _ (boClass_pullback_inclusion_of_boClass T U hL.1) _
    (localFunctorFamOn_isOfOrderGe bd T hL U hU) x ?_
  have h := step2SeqFamOn_ord_lt bd (T.tuned m hL.1.1)
    (AnalyticTriple.localMCClass_tuned hL).1 U hU
    (Classical.choose (Classical.choose_spec (AnalyticTriple.localMCClass_tuned hL).2))
    (Classical.choose_spec (Classical.choose_spec (AnalyticTriple.localMCClass_tuned hL).2)) x
  rwa [← AnalyticTriple.tuned_pullback T hL.1.1 (N.inclusion U) (isLocalDiffeomorph_inclusion N U)]
    at h

/-- Theorem 103 (2) for the local functor, both clauses of [Kol07, 34.1] per open, on the class
`LocalMCClass m`, in the general form over the data `HFData` of Step 2: the tuning commutes with the
pull-back (`tuned_pullback`, passed through the class proof by `hfStep2FamOn_congr_triple`), the
hypersurface of maximal contact chosen for the pulled-back triple is replaced by the pull-back of
the one chosen for the triple (`hfStep2SeqFamOn_indep`, Step 2.3 of the proof of Theorem 103), and
Step 2 commutes with local analytic isomorphisms (`hfStep2SeqFamOn_commutesWithLocalIsos`), given
that the data of Step 2.1 take the empty value at an empty member (`hnil`). -/
theorem hfLocalFunctorFamOn_commutesWithLocalIsos {m : ℕ} (d : HFData ψ₀ (tuningParam m))
    (hnil : ∀ {M' : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ M')
      (hT' : AnalyticTriple.BOClass (tuningParam m) T') (j : T'.F.ι),
      T'.F.hyp j = ∅ → d.bd₁.fam T' hT' j = CompatibleFamily.nil T')
    {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hL : AnalyticTriple.LocalMCClass m T)
    (hL' : AnalyticTriple.LocalMCClass m (T.pullback g hg)) (U' : Opens N)
    (hU' : IsCompact (closure (U' : Set N))) :
    BO.hfLocalFunctorFamOn m d (T.pullback g hg) hL' U' hU' =
      ((BO.hfLocalFunctorFamOn m d T hL (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty := by
  have hLt := AnalyticTriple.localMCClass_tuned hL
  have hLt' : AnalyticTriple.LocalMCClass (tuningParam m) ((T.tuned m hL.1.1).pullback g hg) :=
    AnalyticFamilyFunctor.localMCClass_pullback' _ g hg hLt
  unfold BO.hfLocalFunctorFamOn
  rw [BO.hfStep2FamOn_congr_triple (tuningParam m) d (AnalyticTriple.tuned_pullback T hL.1.1 g hg)
    (AnalyticTriple.localMCClass_tuned hL') hLt' U' hU']
  unfold BO.hfStep2FamOn
  rw [hfStep2SeqFamOn_indep d ((T.tuned m hL.1.1).pullback g hg) hLt'.1 U' hU'
    (Classical.choose (Classical.choose_spec hLt'.2))
    (Classical.choose_spec (Classical.choose_spec hLt'.2))
    ((Classical.choose (Classical.choose_spec hLt.2)).preimage_of_isLocalDiffeomorph hg)
    (AnalyticTriple.idealSheaf_preimage_le_iteratedDeriv_pullback (T.tuned m hL.1.1) g hg _
      (Classical.choose_spec (Classical.choose_spec hLt.2)))]
  exact hfStep2SeqFamOn_commutesWithLocalIsos d (T.tuned m hL.1.1) hLt.1
    (Classical.choose (Classical.choose_spec hLt.2))
    (Classical.choose_spec (Classical.choose_spec hLt.2)) hnil g hg hLt'.1 _ _ U' hU'

/-- The value of the local functor on `U` does not see empty boundary members, in the
general form over the data `HFData` of Step 2: the clause of Step 2 on the tuned triples
(`hfStep2SeqFamOn_indifferentToEmptyMembers`); the tuning does not see the boundary, and the chosen
hypersurface of maximal contact is the same on both sides, the tuned ideal sheaves being equal. -/
theorem hfLocalFunctorFamOn_indifferentToEmptyMembers {m : ℕ}
    (d : HFData ψ₀ (tuningParam m))
    {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N) (F' : HypersurfaceFamily N)
    (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i)
    (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅) (hL : AnalyticTriple.LocalMCClass m T)
    (hL' : AnalyticTriple.LocalMCClass m
      (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ N))
    (U : Opens N) (hU : IsCompact (closure (U : Set N))) :
    BO.hfLocalFunctorFamOn m d T hL U hU =
      BO.hfLocalFunctorFamOn m d ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ hL' U hU :=
  hfStep2SeqFamOn_indifferentToEmptyMembers d (T.tuned m hL.1.1)
    (AnalyticTriple.localMCClass_tuned hL).1 U hU
    (Classical.choose (Classical.choose_spec (AnalyticTriple.localMCClass_tuned hL).2))
    (Classical.choose_spec (Classical.choose_spec (AnalyticTriple.localMCClass_tuned hL).2))
    F' hsnc' e he he' (AnalyticTriple.localMCClass_tuned hL').1

/-- The values of the local functor are compatible under restriction ([Wlo09, Theorem 2.0.3 (4)];
the second clause of [Kol07, 34.1]), in the general form over the data `HFData` of Step 2: the
clause of Step 2 on the tuned triple (`hfStep2SeqFamOn_compat`). -/
theorem hfLocalFunctorFamOn_compat {m : ℕ} (d : HFData ψ₀ (tuningParam m))
    {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N) (hL : AnalyticTriple.LocalMCClass m T)
    {U V : Opens N} (hU : IsCompact (closure (U : Set N))) (hV : IsCompact (closure (V : Set N)))
    (hUV : U ≤ V) :
    BO.hfLocalFunctorFamOn m d T hL U hU =
      ((BO.hfLocalFunctorFamOn m d T hL V hV).pullback (N.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty :=
  hfStep2SeqFamOn_compat d (T.tuned m hL.1.1) (AnalyticTriple.localMCClass_tuned hL).1 U hU
    (Classical.choose (Classical.choose_spec (AnalyticTriple.localMCClass_tuned hL).2))
    (Classical.choose_spec (Classical.choose_spec (AnalyticTriple.localMCClass_tuned hL).2)) hV hUV

end Hironaka.Manifold
