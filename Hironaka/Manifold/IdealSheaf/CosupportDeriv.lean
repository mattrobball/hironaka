/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Deriv
import Hironaka.Manifold.Germ.CoordDerivCoords
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# The cosupport of the maximal contact ideal is the locus of order at least `m`

Kollár's maximal contact ideal is the `(m−1)`-st derivative `MC(I) := D^{m−1}(I)` of an ideal
sheaf `I` of maximal order `m`; it has order `1` at the points where `I` has order `m` and order
`0` where `I` has smaller order, so that "`cosupp MC(I) = cosupp(I, m)`" [Kol07, Definition 79].
On an analytic manifold, for `m ≥ 1`, the
cosupport of `D^{m−1}(J)` is the locus `{a | m ≤ ν_a(J)}` (`cosupport_iteratedDeriv`): the
cosupport of a locally finitely generated ideal sheaf, hence closed. The proof is
[Kol07, Lemma 74 (3)] at the stalk — `m ≤ ord I ↔ m − r ≤ ord Dʳ(I)` for `r < m`, in the `Hironaka`
library's regular coordinates of the stalk (`le_ord_iff_le_ord_Dpow`), which the analytic stalk
carries (`exists_regularCoords_stalk`, once it is a regular local ring of dimension `n`) —
through `stalkIdeal_iteratedDeriv_eq_Dpow`. Consequently `{a | ν_a(J) ≤ k}` is open
(`isOpen_setOf_ord_le`), the upper semicontinuity of the order in the form the order-reduction
algorithm uses. Bierstone–Milman's locally Noetherian hypothesis on their category of spaces
[BM97, (3.8)(3); Definitions and remarks 3.9] is not needed for this: the closedness of the locus
comes from the local finite generation of the derivative ideal sheaves.
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory IsLocalRing
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold.IdealSheaf

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M]
  [FiniteDimensional 𝕜 E] (J : IdealSheaf (structureSheaf 𝕜 E M))

/-- Kollár's "`cosupp MC(I) = cosupp(I, m)`" [Kol07, Definition 79], from [Kol07, Lemma 74 (3)]:
for `m ≥ 1`, the cosupport of `D^{m−1}(J)` is the locus where the order of `J` is at least `m`. -/
theorem support_iteratedDeriv {m : ℕ} (hm : 1 ≤ m) :
    (J.iteratedDeriv (m - 1)).support = {a | (m : ℕ∞) ≤ J.ord a} := by
  ext a
  have hφ : chartAt E a ∈ maximalAtlas 𝓘(𝕜, E) ω M := IsManifold.chart_mem_maximalAtlas a
  have hdim : ((Module.finrank 𝕜 E : ℕ) : WithBot ℕ∞) =
      ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk a) := (ringKrullDim_stalk E a).symm
  obtain ⟨c, -, -, hk, hs⟩ := exists_regularCoords_stalk E (modelCoord (𝕜 := 𝕜) (E := E))
    (chartAt E a) hφ (mem_chart_source E a) hdim
  rw [mem_support, Set.mem_ofPred_eq, J.stalkIdeal_iteratedDeriv_eq_Dpow c hk hs, IdealSheaf.ord,
    c.le_ord_iff_le_ord_Dpow (J.stalkIdeal a) (Nat.sub_lt hm one_pos), Nat.sub_sub_self hm,
    Nat.cast_one, Order.one_le_iff_ne_zero, ne_eq, ne_eq, IsLocalRing.ord_eq_zero_iff]

end Manifold.IdealSheaf

/-! ### The order is upper semicontinuous: `{ord ≤ k}` is open -/

namespace Manifold.IdealSheaf

open Set

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [hfd : FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E}

/-- `{ord 𝓘 ≤ k}` is open: its complement `{ord 𝓘 ≥ k + 1}` is the cosupport of the derivative
ideal sheaf `D^k 𝓘`, a closed set. -/
theorem isOpen_setOf_ord_le (I : AnalyticManifold.IdealSheaf M) (k : ℕ) :
    IsOpen {y : M | I.ord y ≤ (k : ℕ∞)} := by
  have h1 : (I.iteratedDeriv k).support = {a : M | (k : ℕ∞) < I.ord a} := by
    have h0 := support_iteratedDeriv I (Nat.succ_pos k)
    rw [Nat.succ_sub_one] at h0
    rw [h0]
    ext a
    simp only [Set.mem_ofPred_eq, Nat.cast_succ, ENat.add_one_le_iff (ENat.natCast_ne_top k)]
  have h : {y : M | I.ord y ≤ (k : ℕ∞)} = (I.iteratedDeriv k).supportᶜ := by
    ext y
    rw [h1]
    simp only [Set.mem_ofPred_eq, mem_compl_iff, not_lt]
  rw [h]
  exact (I.iteratedDeriv k).isClosed_support.isOpen_compl

end Manifold.IdealSheaf

end
