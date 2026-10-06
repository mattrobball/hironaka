/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BD
public import Hironaka.Resolution.Analytic.MaximalContact.StalkEquiv
import Hironaka.Algebra.Derivative.Equiv
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.Weak
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lemma 102: the weak transform under the first blow-up, and the empty member

Auxiliary facts about the construction of `BDan` (`BD.lean`), the analytic functor `BD_{n,m,j}`
of [Kol07, Lemma 102]: the proof of the lemma blows up the union `Z_{-1}` of the components of
`E^j` contained in `cosupp(I, m)` — a trivial blow-up, "the blow-up is an isomorphism", but the
order
of `I` along `E^{jk}` drops by `m` — and continues with the weak transform `I_0`.

* `BlowUpSequence.eq_nil_of_noEmptyCenters_of_isEmpty` — a list of centres on an empty manifold with
  no empty centre is the empty list ([Kol07, 32] on the empty manifold).
* `BDan.stalkIdeal_weakTransformI_of_notMem` — off `Z_{-1}` the weak transform `I_0` is the
  pull-back of `𝓘` along the isomorphism `π_{-1}`: the exponent of the exceptional ideal in the
  colon description of the weak transform is the generic order of `𝓘` along the component of
  `Z_{-1}` through the point, which is `0` off `Z_{-1}`, so the stalk of `I_0` is the image of the
  stalk of `𝓘` under the isomorphism of germ algebras induced by `π_{-1}`.
* `BDan.isDBalanced_weakTransformI` — **the weak transform of a D-balanced ideal sheaf under the
  first blow-up is D-balanced** (not in the sources; needed because the input functor is applied to
  the restriction of `I_0`, and [Kol07, Corollary 85] asks for a D-balanced ideal). D-balancedness
  is a stalkwise condition; over `Z_{-1}` the weak transform has order `0`, so its stalk is the
  unit ideal and the condition is trivial; off `Z_{-1}` the stalk is the image of a D-balanced
  stalk under a ring isomorphism, and iterated derivatives and powers commute with isomorphisms.
* `BDan.ord_weakTransformI_le` — `ord I_0 ≤ s` everywhere (the proof of [Kol07, Lemma 102]: the
  order of `I_0` along `E^{jk}` is that of `I` diminished by `m`, hence `≤ 0`).
* `BDan_eq_nil_of_hyp_eq_empty` — at an empty member the value of `BD_{n,m,·}` is the empty list:
  `Z_{-1} ⊆ E^j = ∅`, the restricted triple lives on the empty manifold, where the value of the
  input has no nonempty centre, and the empty first blow-up is deleted.
-/

public section

noncomputable section

open Set Topology IsLocalRing
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open _root_.Manifold
open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- [Kol07, 32] on the empty manifold: a list of centres with no empty centre on a manifold without
points is the empty list. -/
theorem eq_nil_of_noEmptyCenters_of_isEmpty {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (hL : L.NoEmptyCenters) (hM : ∀ _ : M, False) : L = nil M := by
  cases L with
  | nil => rfl
  | cons hY rest =>
    exact absurd (Set.eq_empty_of_forall_notMem fun x _ => hM x)
      ((noEmptyCenters_cons_iff hY rest).mp hL).1

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace BDan

open _root_.Manifold

variable [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  (T : AnalyticTriple ψ₀ M) (s : ℕ) (j : T.F.ι)

/-- Off `Z_{-1}` the weak transform `I_0` is the pull-back of `𝓘` along the isomorphism `π_{-1}`:
the stalk at `x'` is the image of the stalk of `𝓘` at `π_{-1} x'` under the isomorphism of germ
algebras. In the colon description of the weak transform the exceptional ideal appears with the
exponent given by the generic order of `𝓘` along the component of `Z_{-1}` through the point, which
is `0` off `Z_{-1}`, so the weak transform there is the total transform, whose stalk is
`stalkIdeal_comap_eq_map_germAlgEquiv`. -/
theorem stalkIdeal_weakTransformI_of_notMem
    {x' : Manifold.blowUp ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)}
    (hx : piMinusOne T s j x' ∉ BD.Zminus1 T.I s (T.F.hyp j)) :
    (weakTransformI T s j).stalkIdeal x' =
      (T.I.stalkIdeal (piMinusOne T s j x')).map
        (germAlgEquiv (piMinusOne T s j) (isLocalDiffeomorph_piMinusOne T s j x')) := by
  have h := isBlowUp_blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)
  have hexp : (IdealSheaf.genericOrdAlong (BD.isClosedSubmanifold_Zminus1 T s j).idealSheaf T.I
      (piMinusOne T s j x')).toNat = 0 := by
    rw [IdealSheaf.genericOrdAlong_def, (BD.isClosedSubmanifold_Zminus1 T s j).cosupport_idealSheaf,
      connectedComponentIn_eq_empty hx]
    simp
  have hcol := isDivExceptional_weakTransformOf (BD.isClosedSubmanifold_Zminus1 T s j) h T.I x'
  dsimp only at hcol
  rw [hexp, pow_zero, Ideal.one_eq_top, Ideal.colon_coe_top] at hcol
  rw [weakTransformI, weakTransformIOf, hcol]
  exact stalkIdeal_comap_eq_map_germAlgEquiv (piMinusOne T s j)
    (isLocalDiffeomorph_piMinusOne T s j) T.I x'

/-- **The weak transform of a D-balanced ideal sheaf under the first blow-up of Lemma 102 is
D-balanced** at the same mark (not in the sources; the proof of [Kol07, Lemma 102] applies the
going-up theorem to the D-balanced `I_0`). Stalkwise: over `Z_{-1}` the weak transform has order
`0` (`BD.ord_weakTransformOf_eq_zero_of_mem_Zminus1`), so its stalk is the unit ideal and the
inclusion `(D^i J)^s ≤ J^{s-i}` is trivial; off `Z_{-1}` the stalk is the image of the stalk of
`𝓘` under a ring isomorphism (`stalkIdeal_weakTransformI_of_notMem`), and the image of a
D-balanced ideal under a ring isomorphism is D-balanced, iterated derivatives and powers commuting
with the isomorphism. -/
theorem isDBalanced_weakTransformI (hT : BDClass s T) :
    (weakTransformI T s j).IsDBalanced s := by
  intro i hi
  rw [IdealSheaf.le_def]
  intro x'
  rw [IdealSheaf.stalkIdeal_pow, IdealSheaf.stalkIdeal_pow, IdealSheaf.stalkIdeal_iteratedDeriv]
  by_cases hx : piMinusOne T s j x' ∈ BD.Zminus1 T.I s (T.F.hyp j)
  · have h0 := BD.ord_weakTransformOf_eq_zero_of_mem_Zminus1 T s j hT.1.2.1
      (BD.isClosedSubmanifold_Zminus1 T s j) hx
    have htop : (weakTransformI T s j).stalkIdeal x' = ⊤ := by
      rw [IdealSheaf.ord_eq_zero_iff, IdealSheaf.mem_support, not_not] at h0
      exact h0
    rw [htop, Ideal.top_pow]
    exact le_top
  · rw [stalkIdeal_weakTransformI_of_notMem T s j hx, Ideal.derivativeIter_map_algEquiv,
      ← Ideal.map_pow, ← Ideal.map_pow]
    apply Ideal.map_mono
    have hst := IdealSheaf.le_def.mp (hT.2 i hi) (piMinusOne T s j x')
    rwa [IdealSheaf.stalkIdeal_pow, IdealSheaf.stalkIdeal_pow, IdealSheaf.stalkIdeal_iteratedDeriv]
      at hst

/-- The proof of [Kol07, Lemma 102], "since `max-ord_{E^{jk}} I ≤ m` to start with": the weak
transform `I_0` has order at most `s` everywhere — order `0` over `Z_{-1}`, the order of `𝓘` at the
image point off it. -/
theorem ord_weakTransformI_le (hT : BDClass s T)
    (x' : Manifold.blowUp ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)) :
    (weakTransformI T s j).ord x' ≤ (s : ℕ∞) := by
  by_cases hx : piMinusOne T s j x' ∈ BD.Zminus1 T.I s (T.F.hyp j)
  · exact (BD.ord_weakTransformOf_eq_zero_of_mem_Zminus1 T s j hT.1.2.1 _ hx).le.trans zero_le
  · exact (BD.ord_weakTransformOf_eq_of_not_mem T s j _ hx).le.trans (hT.1.2.1 _)

end BDan

section EmptyMember

variable [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {m : ℕ}

/-- **At an empty member the value of `BD_{n,m,·}` is the empty list** ([Kol07, 32]): `Z_{-1} ⊆
E^j = ∅`, the restricted triple lives on the empty manifold, where the value of the input functor
has no nonempty centre, and the empty first blow-up is deleted. -/
theorem BDan_eq_nil_of_hyp_eq_empty (inp : BMOanData 𝕜 (n - 1) (tuningParam m))
    (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass m T) (j : T.F.ι)
    (hj : T.F.hyp j = ∅) : BDan m inp T hT j = AnalyticManifold.BlowUpSequence.nil M := by
  have hZ : BD.Zminus1 (T.tuned m hT.1).I (tuningParam m) ((T.tuned m hT.1).F.hyp j) = ∅ := by
    have hsub := BD.Zminus1_subset (T.tuned m hT.1) (tuningParam m) j
    have hj' : (T.tuned m hT.1).F.hyp j = ∅ := hj
    refine Set.eq_empty_of_subset_empty fun x hx => ?_
    have hx' := hsub hx
    rw [hj'] at hx'
    exact hx'
  have hnil : inp.functor.seq
      (BDan.restrictedTriple (T.tuned m hT.1) (tuningParam m) j
        ⟨AnalyticTriple.boClass_tuned hT, AnalyticTriple.isDBalanced_tuned hT⟩)
      (BDan.bmoClass_restrictedTriple (T.tuned m hT.1) (tuningParam m) j
        ⟨AnalyticTriple.boClass_tuned hT, AnalyticTriple.isDBalanced_tuned hT⟩) =
      AnalyticManifold.BlowUpSequence.nil _ := by
    refine AnalyticManifold.BlowUpSequence.eq_nil_of_noEmptyCenters_of_isEmpty _
        (inp.functor.noEmptyCenters _ _) ?_
    intro x
    have hx : BDan.piMinusOne (T.tuned m hT.1) (tuningParam m) j x.1 ∈ T.F.hyp j := x.2
    rw [hj] at hx
    exact hx
  unfold BDan BDan.core BDan.coreOfListOf
  rw [hnil, AnalyticManifold.BlowUpSequence.eraseEmpty_cons_of_eq_empty _ _ hZ]
  simp only [AnalyticManifold.BlowUpSequence.pushforward,
      AnalyticManifold.BlowUpSequence.pushforwardAux,
      AnalyticManifold.BlowUpSequence.eraseEmpty_nil,
    AnalyticManifold.BlowUpSequence.map_nil]

end EmptyMember

end Hironaka.Manifold

end
