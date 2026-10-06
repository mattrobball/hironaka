/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Basic
public import Hironaka.Manifold.FiniteSuccession.Functor.LocalCover
import Hironaka.Manifold.IdealSheaf.CosupportDeriv
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Finiteness over relatively compact open subsets

On a non-compact manifold the finite index sets and the maximal order of Kollár's triples are not
available globally. They are restored over an open subset `U` with compact closure, the setting of
Bierstone–Milman's "relatively quasi-compact open subset" ([BM97, Theorem 1.6] and the remark
following it) and of Kollár's "small neighborhoods of compact sets" ([Kol07, 44]): only finitely
many members of a locally finite family meet the compact closure, and the order of an ideal sheaf
that is nonzero at every point is bounded on a compact set, being finite at each point and upper
semicontinuous (`{ord ≤ k}` is open because `{ord ≥ k + 1}` is the cosupport of the derivative
ideal sheaf `D^k 𝓘` (`cosupport_iteratedDeriv`), which is closed).

* `AnalyticTriple.boClass_iff` — the class `BOClass m` unfolded;
* `HypersurfaceFamily.IsSnc.finite_meeting_compact` — only finitely many members of a family
  with simple normal crossings meet a compact set;
* `IdealSheaf.bddAbove_ord_on_compact` — the order of an ideal sheaf nonzero everywhere is bounded
  on a compact set;
* `boClass_pullback_inclusion`, `exists_boClass_pullback_inclusion` — the restriction of a triple
  to an open subset with compact closure lies in `BOClass m` for `m` a bound of the order on `U`,
  and for some `m`.

This is what makes the compatible-family form of the order-reduction functors meaningful: the
value on each relatively compact open is that of a functor on `BOClass m` for a suitable `m`
(`Functor/Family.lean`, `BOanFamOfInput.lean`).
-/

public section

noncomputable section

open TopologicalSpace Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [hfd : FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

-- The finite-dimensionality `[FiniteDimensional 𝕜 E]` of the model space belongs to every statement
-- here, as to Kollár's varieties; a proof that does not need it names it (`have _hfd := hfd`) so
-- that it remains part of the statement.

/-- The class of `BO_{n,m}` unfolded ([Kol07, Theorem 103]: "`dim X = n`, `max-ord I ≤ m`"): a
triple is in `BOClass m` iff `1 ≤ m`, `ord 𝓘 ≤ m` at every point and only finitely many members of
`E` are nonempty. -/
theorem AnalyticTriple.boClass_iff (m : ℕ) (T : AnalyticTriple ψ₀ M) :
    AnalyticTriple.BOClass m T ↔
      1 ≤ m ∧ (∀ x, T.I.ord x ≤ (m : ℕ∞)) ∧ Finite {j // T.F.hyp j ≠ ∅} := by
  have _hfd := hfd
  exact Iff.rfl

/-- Only finitely many members of a family of hypersurfaces with simple normal crossings meet a
compact set: the family is locally finite. -/
theorem HypersurfaceFamily.IsSnc.finite_meeting_compact {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ₀) {K : Set M} (hK : IsCompact K) : {j | (F.hyp j ∩ K).Nonempty}.Finite := by
  have _hfd := hfd
  exact hF.locallyFinite.finite_nonempty_inter_compact hK

/-- The order of an ideal sheaf that is nonzero at every point is bounded on a compact set: it is
finite at every point and upper semicontinuous (`isOpen_setOf_ord_le`), so finitely many of the
open sets `{ord ≤ ord x}` cover the compact set. Not in the sources as such; the analytic
substitute for Kollár's `max-ord I`. -/
theorem IdealSheaf.bddAbove_ord_on_compact {I : AnalyticManifold.IdealSheaf M}
    (hI : I.IsNonzeroEverywhere) {K : Set M} (hK : IsCompact K) :
    ∃ m : ℕ, ∀ x ∈ K, I.ord x ≤ (m : ℕ∞) := by
  have hfin : ∀ x : M, I.ord x ≠ ⊤ := fun x hx =>
    hI x ((IdealSheaf.ord_eq_top_iff (J := I) x).mp hx)
  let k : M → ℕ := fun x => (I.ord x).toNat
  have hk : ∀ x, I.ord x = (k x : ℕ∞) := fun x => (ENat.natCast_toNat (hfin x)).symm
  have hV : ∀ x ∈ K, {y : M | I.ord y ≤ (k x : ℕ∞)} ∈ 𝓝 x := fun x _ =>
    (I.isOpen_setOf_ord_le (k x)).mem_nhds (by simp only [Set.mem_ofPred_eq, hk x, le_refl])
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {y : M | I.ord y ≤ (k x : ℕ∞)}) hV
  refine ⟨t.sup k, fun y hy => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
  exact hyx.trans (Nat.cast_le.mpr (Finset.le_sup hxt))

/-- The restriction of a triple to an open subset `U` with compact closure, on which the order of
`𝓘` is at most `m ≥ 1`, lies in the class `BOClass m` (the setting of the remark after
[BM97, Theorem 1.6]): the pull-back along the inclusion has the order of `𝓘` at the image, and a
member of the pulled-back family is nonempty only if the member meets `U ⊆ closure U`, which
finitely many do. -/
theorem _root_.Hironaka.Manifold.boClass_pullback_inclusion (T : AnalyticTriple ψ₀ M) {m : ℕ}
    (hm : 1 ≤ m) (U : Opens M)
    (hU : IsCompact (closure (U : Set M)))
    (hord : ∀ x ∈ (U : Set M), T.I.ord x ≤ (m : ℕ∞)) :
    AnalyticTriple.BOClass m (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) := by
  refine ⟨hm, fun y => ?_, ?_⟩
  · change (T.I.pullback ⇑(M.inclusion U) (M.inclusion U).contMDiff).ord y ≤ (m : ℕ∞)
    rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ T.I
      (isLocalDiffeomorph_inclusion M U y)]
    exact hord _ y.2
  · have hfin : {j | (T.F.hyp j ∩ closure (U : Set M)).Nonempty}.Finite :=
      T.isSnc.finite_meeting_compact hU
    have := hfin.to_subtype
    refine Finite.of_injective
      (fun j : {j // (T.F.comap ⇑(M.inclusion U)).hyp j ≠ ∅} =>
        (⟨j.1, ?_⟩ : {j | (T.F.hyp j ∩ closure (U : Set M)).Nonempty})) ?_
    · obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.mpr j.2
      exact ⟨y.1, hy, subset_closure y.2⟩
    · intro j₁ j₂ h
      exact Subtype.ext (Subtype.mk.inj h)

/-- The restriction of a triple to an open subset with compact closure lies in the class
`BOClass m` for some `m` ([BM97, Theorem 1.6] and the remark after it; [Kol07, 44]): the order of
`𝓘` is bounded on the compact closure. -/
theorem _root_.Hironaka.Manifold.exists_boClass_pullback_inclusion (T : AnalyticTriple ψ₀ M)
    (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    ∃ m : ℕ, AnalyticTriple.BOClass m
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) := by
  obtain ⟨m₀, hm₀⟩ := IdealSheaf.bddAbove_ord_on_compact T.isNonzeroEverywhere hU
  exact ⟨max m₀ 1, Hironaka.Manifold.boClass_pullback_inclusion T
      (le_max_right _ _) U hU fun x hx =>
    (hm₀ x (subset_closure hx)).trans (Nat.cast_le.mpr (le_max_left _ _))⟩

end Manifold

end
