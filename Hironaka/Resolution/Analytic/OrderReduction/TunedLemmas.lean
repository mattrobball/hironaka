/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Tuned
public import Hironaka.Resolution.Analytic.MaximalContact.StalkEquiv
public import Hironaka.Manifold.FiniteSuccession.Order
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.TuningLemmas
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.Tuning
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 1 of Theorem 103: transfer between the triple and its tuned triple

Step 1 of the proof of [Kol07, Theorem 103] replaces `I` by the maximal coefficient ideal `W_s(I)`
([Kol07, Definition 98]), for which order reduction is "equivalent to order reduction for
`(X, W(I), E)`" ([Kol07, Corollary 101]). This module proves what the construction
needs about the tuned triple of `Tuned.lean`:

* `comap_tuning` — the tuning commutes with pull-back along a local analytic isomorphism,
  `h^*(W_s(J)) = W_s(h^* J)`. Stalkwise: the stalk of the pull-back is the image of the stalk under
  the germ algebra isomorphism, the stalk of `W_s(J)` is Kollár's sum
  `∑_{wt(e) ≥ s} ∏_j (D^j J)^{e_j}`, the image of an ideal under a ring isomorphism distributes over
  sums, products and powers, and the derivative ideal sheaves commute with the pull-back
  ([Kol07, Lemma 74 (4)]).
* `AnalyticTriple.tuned_pullback` — the tuned triple of a pull-back is the pull-back of the tuned
  triple.
* `AnalyticTriple.orderReduction_tuned_iff` — Kollár's equivalence: a sequence of centres is a
  smooth blow-up sequence of order `≥ s` for the tuned triple iff it is one of order `≥ m` for the
  triple (`tuning_orderReduction_equiv`; the boundary is kept by the tuning).
* `AnalyticTriple.ord_lt_of_tuned` — the output clause transfers back: where the final transform of
  `W_s(𝓘)` has order `< s`, the final transform of `𝓘` has order `< m`. Along a sequence of order
  `≥ m` for `(𝓘, m)` (of order `≥ s` for `(W_s(𝓘), s)` by the equivalence) the controlled transforms
  are the weak transforms, because every centre has order exactly `m`, respectively `s`; the
  controlled transform of `W_s(𝓘)` lies in the tuning of the controlled transform of `𝓘`
  (`markedTransformSeq_tuning_le`), whose order is `≥ s` exactly where the transform of `𝓘` has
  order `≥ m`; and a smaller ideal sheaf has a larger order. So `ord W_r < s` forces `ord I_r < m`.

These lemmas carry Theorem 103 (1) and (2) from the tuned triple back to the triple for the local
functor in the compatible-family form (`LocalFunctorFam.lean`).
-/

public section

noncomputable section

open Set Topology AnalyticManifold IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section Comap

variable [FiniteDimensional 𝕜 E] {M N : AnalyticManifold.{u} 𝕜 E} (h : AnalyticMap N M)
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)

include hh in
/-- The tuning commutes with pull-back along a local analytic isomorphism,
`h^*(W_s(J)) = W_s(h^* J)` ([Kol07, Definition 98] with [Kol07, Lemma 74 (4)]): stalkwise, Kollár's
sum is carried by the germ algebra isomorphism term by term. Not in the sources; the ingredient of
the functoriality of Step 1. -/
theorem _root_.Hironaka.Manifold.comap_tuning (J : AnalyticManifold.IdealSheaf M) (m s : ℕ) :
    (J.tuning m s).pullback h h.contMDiff =
      (J.pullback h h.contMDiff).tuning m s := by
  refine IdealSheaf.ext fun b => ?_
  have hprod : ∀ Q : Fin (m + 1) → Ideal ((structureSheaf 𝕜 E M).presheaf.stalk (h b)),
      (∏ j, Q j).map (germAlgEquiv h (hh b)) = ∏ j, (Q j).map (germAlgEquiv h (hh b)) := by
    intro Q
    have := map_prod (Ideal.mapHom (germAlgEquiv h (hh b))) Q Finset.univ
    simpa only [Ideal.mapHom_apply] using this
  rw [stalkIdeal_comap_eq_map_germAlgEquiv h hh, IdealSheaf.stalkIdeal_tuning,
    IdealSheaf.stalkIdeal_tuning, Ideal.map_iSup]
  refine iSup_congr fun e => ?_
  rw [Ideal.map_iSup]
  refine iSup_congr fun _ => ?_
  rw [hprod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Ideal.map_pow, ← stalkIdeal_comap_eq_map_germAlgEquiv h hh, comap_iteratedDeriv h hh]

end Comap

namespace AnalyticTriple

variable [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {m : ℕ}

/-- The tuned triple of a pull-back along a local analytic isomorphism is the pull-back of the
tuned triple (`comap_tuning`): Step 1 of the proof of [Kol07, Theorem 103] commutes with local
analytic isomorphisms. -/
theorem tuned_pullback {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hm : 1 ≤ m)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    (T.pullback h hh).tuned m hm = (T.tuned m hm).pullback h hh :=
  AnalyticTriple.ext' (comap_tuning h hh T.I m (tuningParam m)).symm rfl

/-- Order reduction for `(X, I, E)` "is equivalent to order reduction for `(X, W(I), E)`" (Step 1
of the proof of [Kol07, Theorem 103]; [Kol07, Corollary 101]): a sequence of centres is a smooth
blow-up sequence of order `≥ s` for the tuned triple iff it is one of order `≥ m` for the triple,
`s = tuningParam m` (`tuning_orderReduction_equiv`; the boundary is kept by the tuning). -/
theorem orderReduction_tuned_iff (T : AnalyticTriple ψ₀ M) (hT : BOClass m T)
    (L : BlowUpSequence ψ₀ M) :
    L.toSuccession.IsOfOrderGe (T.tuned m hT.1).I (tuningParam m) (T.tuned m hT.1).F.idealSheaf ↔
      L.toSuccession.IsOfOrderGe T.I m T.F.idealSheaf :=
  (FiniteSuccession.tuning_orderReduction_equiv hT.2.1 hT.1).symm

/-- The output clause of Theorem 103 transfers from the tuned triple back to the triple: where the
final transform of `W_s(𝓘)` has order `< s`, the final transform of `𝓘` has order `< m`. Along the
sequence the controlled transforms are the weak transforms; the controlled transform of `W_s(𝓘)`
lies in the tuning of the controlled transform of `𝓘` (`markedTransformSeq_tuning_le`), whose order
is `≥ s` exactly where the transform of `𝓘` has order `≥ m` (`le_ord_tuning_iff`). -/
theorem ord_lt_of_tuned (T : AnalyticTriple ψ₀ M) (hT : BOClass m T) (L : BlowUpSequence ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe T.I m T.F.idealSheaf) (x : L.toSuccession.stage (Fin.last _))
    (hx : (L.toSuccession.weakTransformSeq (T.tuned m hT.1).I (Fin.last _)).ord x <
      (tuningParam m : ℕ∞)) :
    (L.toSuccession.weakTransformSeq T.I (Fin.last _)).ord x < (m : ℕ∞) := by
  by_contra hcon
  rw [not_lt] at hcon
  have hW : L.toSuccession.IsOfOrderGe (T.tuned m hT.1).I (tuningParam m) T.F.idealSheaf :=
    (FiniteSuccession.tuning_orderReduction_equiv hT.2.1 hT.1).mp hL
  have hIo := FiniteSuccession.isOfOrder_of_isOfOrderGe_of_ord_le L.toSuccession hL hT.2.1
  have hWo :=
    FiniteSuccession.isOfOrder_of_isOfOrderGe_of_ord_le L.toSuccession hW (ord_tuned_le hT)
  rw [← hWo.markedTransformSeq_eq_weakTransformSeq] at hx
  rw [← hIo.markedTransformSeq_eq_weakTransformSeq] at hcon
  have hle := hL.markedTransformSeq_tuning_le (tuningParam m) (Fin.last _)
  have h1 : (tuningParam m : ℕ∞) ≤
      ((L.toSuccession.markedTransformSeq T.I m (Fin.last _)).tuning m (tuningParam m)).ord x :=
    (IdealSheaf.le_ord_tuning_iff _ m (tuningParam m) hT.1 (one_le_tuningParam m) x).mpr hcon
  exact lt_irrefl _ (lt_of_le_of_lt (h1.trans (IdealSheaf.ord_anti hle x)) hx)

end AnalyticTriple

end Manifold

end
