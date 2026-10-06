/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Tuning
public import Hironaka.Manifold.Germ.StalkNoetherian
public import Hironaka.Algebra.Local.TuningParam
public import Hironaka.Algebra.Local.TuningFinite
public import Hironaka.Manifold.IdealSheaf.Monoid
import Hironaka.Manifold.Germ.CoordDerivCoords
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The maximal coefficient ideal sheaf: Proposition 99, orders and cosupports

Kollár's maximal coefficient ideal [Kol07, Definition 98] on an analytic manifold,
`IdealSheaf.tuning J m s` (`Hironaka/Manifold/IdealSheaf/Tuning.lean`), has Kollár's sum
`∑_{wt(e) ≥ s} ∏_j (D^j J)^{e_j}` as its stalk at every point. Through the regular coordinates `c`
of the stalk `𝒪_{M,a}` (`exists_regularCoords_stalk`) the derivative stalks are the `Hironaka`
library's `c.Dpow j J_a` (`stalkIdeal_iteratedDeriv_eq_Dpow`), so `W_s(J)_a = c.W m s J_a` is the
`Hironaka` library's coefficient ideal (`stalkIdeal_tuning_eq_W`). Every statement here is the
corresponding statement of the `Hironaka` library read at each stalk (`IdealSheaf.ext`, `le_def`):
[Kol07, Proposition 99] (1) `tuning_anti`, (2) `tuning_mul_le`, (3) `deriv_tuning_succ`,
(4) `tuning_one` and `iteratedDeriv_tuning`, (5) `isMCInvariant_tuning`, (6) `tuning_mul_tuning`,
(7) `tuning_pow`, (8) `isDBalanced_tuning`; [Kol07, Corollary 101] at the parameter
`tuningParam m = max (m − 1) 1 · lcm(2, …, m)`; the order and cosupport identities
`le_ord_tuning_iff`, `ord_tuning`, `cosupport_tuning` (the local form of Kollár's
`max-ord W(I) = m!` [Kol07, Theorem 54.2], and the remark after [Kol07, Definition 83] that the
cosupport of a D-balanced ideal is `cosupp(I, m)`); and `W_{s(1)}(J) = J`. Kollár's hypothesis
`m = max-ord I` enters as `hI : ∀ y, J.ord y ≤ m`, i.e. `ord J_a ≤ m` at each stalk, exactly what
the `Hironaka` library uses. These are the properties of the tuned ideal sheaves that the
order-reduction algorithm relies on (`Hironaka/Resolution/Analytic/OrderReduction/Tuned.lean`).
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
  [FiniteDimensional 𝕜 E]

variable (𝕜 E) in
/-- Regular coordinates of the stalk at any point, `𝕜`-linear and spanning the `𝕜`-derivations
(`exists_regularCoords_stalk` in the chart at the point). -/
theorem exists_regularCoords_stalk_linear (a : M) :
    ∃ c : RegularCoords ((structureSheaf 𝕜 E M).presheaf.stalk a) (Module.finrank 𝕜 E),
      c.IsLinearOver 𝕜 ∧ c.SpansDerivations 𝕜 := by
  have hφ : chartAt E a ∈ maximalAtlas 𝓘(𝕜, E) ω M := IsManifold.chart_mem_maximalAtlas a
  have hdim : ((Module.finrank 𝕜 E : ℕ) : WithBot ℕ∞) =
      ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk a) := (ringKrullDim_stalk E a).symm
  obtain ⟨c, -, -, hk, hs⟩ := exists_regularCoords_stalk E (modelCoord (𝕜 := 𝕜) (E := E))
    (chartAt E a) hφ (mem_chart_source E a) hdim
  exact ⟨c, hk, hs⟩

variable (J : IdealSheaf (structureSheaf 𝕜 E M)) (m s : ℕ)

/-! ### Definition 98 at the stalks and its finite form -/

/-- The stalk of `W_s(J)` is Kollár's sum [Kol07, Definition 98]. -/
theorem stalkIdeal_tuning (x : M) :
    (J.tuning m s).stalkIdeal x =
      ⨆ (e : Fin (m + 1) → ℕ) (_ : s ≤ wt m e),
        ∏ j : Fin (m + 1), (J.iteratedDeriv (j : ℕ)).stalkIdeal x ^ e j :=
  stalkIdeal_ofStalks _ (J.hasLocalGenerators_tuning m s) x

/-- Through regular coordinates of the stalk, `W_s(J)_a = c.W m s J_a`, the `Hironaka` library's
coefficient ideal. -/
theorem stalkIdeal_tuning_eq_W {a : M} {n : ℕ}
    [IsRegularLocalRing ((structureSheaf 𝕜 E M).presheaf.stalk a)]
    (c : RegularCoords ((structureSheaf 𝕜 E M).presheaf.stalk a) n) (hk : c.IsLinearOver 𝕜)
    (hs : c.SpansDerivations 𝕜) :
    (J.tuning m s).stalkIdeal a = c.W m s (J.stalkIdeal a) := by
  rw [stalkIdeal_tuning, RegularCoords.W]
  refine iSup_congr fun e => iSup_congr fun _ => Finset.prod_congr rfl fun j _ => ?_
  rw [J.stalkIdeal_iteratedDeriv_eq_Dpow c hk hs]

/-- The finite form of `W_s(J)`: a finite sum of finite products
(`IsLocalRing.iSup_wt_eq_sum_tuningExponents` at every stalk). -/
theorem tuning_eq_finset_sum :
    J.tuning m s = ∑ e ∈ tuningExponents m s, ∏ j : Fin (m + 1), J.iteratedDeriv (j : ℕ) ^ e j := by
  refine IdealSheaf.ext fun x => ?_
  rw [stalkIdeal_tuning, stalkIdeal_finset_sum, iSup_wt_eq_sum_tuningExponents m s
    (fun j : Fin (m + 1) => (J.iteratedDeriv (j : ℕ)).stalkIdeal x)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [stalkIdeal_finset_prod]
  exact Finset.prod_congr rfl fun j _ => (stalkIdeal_pow _ _ _).symm

/-! ### Proposition 99 (1)–(8) -/

/-- `W_0(J) = 𝒪`. -/
theorem tuning_zero : J.tuning m 0 = ⊤ := by
  refine IdealSheaf.ext fun a => ?_
  obtain ⟨c, hk, hs⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [J.stalkIdeal_tuning_eq_W m 0 c hk hs, c.W_zero, stalkIdeal_top]

/-- `W_t(J) ⊆ W_s(J)` for `s ≤ t` [Kol07, Proposition 99 (1)]. -/
theorem tuning_anti {t : ℕ} (h : s ≤ t) : J.tuning m t ≤ J.tuning m s := by
  rw [IdealSheaf.le_def]
  intro a
  obtain ⟨c, hk, hs'⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [J.stalkIdeal_tuning_eq_W m t c hk hs', J.stalkIdeal_tuning_eq_W m s c hk hs']
  exact c.W_anti h _

/-- `W_s(J) · W_t(J) ⊆ W_{s+t}(J)` [Kol07, Proposition 99 (2)]. -/
theorem tuning_mul_le (t : ℕ) : J.tuning m s * J.tuning m t ≤ J.tuning m (s + t) := by
  rw [IdealSheaf.le_def]
  intro a
  obtain ⟨c, hk, hs'⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [stalkIdeal_mul, J.stalkIdeal_tuning_eq_W m s c hk hs', J.stalkIdeal_tuning_eq_W m t c hk hs',
    J.stalkIdeal_tuning_eq_W m (s + t) c hk hs']
  exact c.W_mul_le m s t _

/-- `J^k ⊆ W_s(J)` when `s ≤ m k`: `J^k` is the term of `W_s(J)` with exponent vector
`(k, 0, …, 0)`, of weight `m k`. -/
theorem pow_le_tuning {k : ℕ} (h : s ≤ m * k) : J ^ k ≤ J.tuning m s := by
  rw [IdealSheaf.le_def]
  intro a
  obtain ⟨c, hk, hs'⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [stalkIdeal_pow, J.stalkIdeal_tuning_eq_W m s c hk hs']
  exact c.pow_le_W h _

/-- `MC(J)^s ⊆ W_s(J)`: `MC(J) = D^{m−1} J` has weight `1`, so `MC(J)^s` is a term of weight
`s`. -/
theorem iteratedDeriv_pow_le_tuning (hm : 1 ≤ m) : J.iteratedDeriv (m - 1) ^ s ≤ J.tuning m s := by
  rw [IdealSheaf.le_def]
  intro a
  obtain ⟨c, hk, hs'⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [stalkIdeal_pow, J.stalkIdeal_iteratedDeriv_eq_Dpow c hk hs',
    J.stalkIdeal_tuning_eq_W m s c hk hs']
  exact c.MC_pow_le_W hm s _

/-- `W_1(J) = D^{m−1} J`: Kollár's "`W_1(I) = MC(I)`" [Kol07, Proposition 99 (4)]. -/
theorem tuning_one (hm : 1 ≤ m) : J.tuning m 1 = J.iteratedDeriv (m - 1) := by
  refine IdealSheaf.ext fun a => ?_
  obtain ⟨c, hk, hs⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [J.stalkIdeal_tuning_eq_W m 1 c hk hs, J.stalkIdeal_iteratedDeriv_eq_Dpow c hk hs]
  exact c.W_one hm _

/-- `D(W_{s+1}(J)) = W_s(J)` for `ord J ≤ m`, `m ≥ 1` [Kol07, Proposition 99 (3)]. -/
theorem deriv_tuning_succ (hm : 1 ≤ m) (hI : ∀ y, J.ord y ≤ m) :
    (J.tuning m (s + 1)).deriv = J.tuning m s := by
  refine IdealSheaf.ext fun a => ?_
  obtain ⟨c, hk, hs'⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [(J.tuning m (s + 1)).stalkIdeal_deriv_eq_D c hk hs',
    J.stalkIdeal_tuning_eq_W m (s + 1) c hk hs', J.stalkIdeal_tuning_eq_W m s c hk hs']
  exact c.D_W_succ hm (hI a) s

/-- Kollár's "`MC(W_s(I)) = W_1(I) = MC(I)`" [Kol07, Proposition 99 (4)]:
`D^{s−1}(W_s(J)) = D^{m−1} J` for `s ≥ 1`. -/
theorem iteratedDeriv_tuning (hm : 1 ≤ m) (hI : ∀ y, J.ord y ≤ m) (hs : 1 ≤ s) :
    (J.tuning m s).iteratedDeriv (s - 1) = J.iteratedDeriv (m - 1) := by
  refine IdealSheaf.ext fun a => ?_
  obtain ⟨c, hk, hs'⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [(J.tuning m s).stalkIdeal_iteratedDeriv_eq_Dpow c hk hs',
    J.stalkIdeal_tuning_eq_W m s c hk hs', J.stalkIdeal_iteratedDeriv_eq_Dpow c hk hs',
    c.Dpow_W hm (hI a) (Nat.sub_le s 1), Nat.sub_sub_self hs]
  exact c.W_one hm _

/-- `W_s(J)` is MC-invariant with respect to `s` [Kol07, Proposition 99 (5)]. -/
theorem isMCInvariant_tuning (hm : 1 ≤ m) (hI : ∀ y, J.ord y ≤ m) (hs : 1 ≤ s) :
    (J.tuning m s).IsMCInvariant s := by
  change _ * _ ≤ _
  rw [IdealSheaf.le_def]
  intro a
  obtain ⟨c, hk, hs'⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [stalkIdeal_mul, (J.tuning m s).stalkIdeal_iteratedDeriv_eq_Dpow c hk hs',
    (J.tuning m s).stalkIdeal_deriv_eq_D c hk hs', J.stalkIdeal_tuning_eq_W m s c hk hs']
  exact c.isMCInvariant_W hm (hI a) hs

/-- `W_s(J) · W_t(J) = W_{s+t}(J)` for `s = r · lcm(2, …, m)` and `t ≥ (m − 1) · lcm(2, …, m)`
[Kol07, Proposition 99 (6)]. -/
theorem tuning_mul_tuning (hm : 1 ≤ m) (r t : ℕ) (ht : (m - 1) * Lcm m ≤ t) :
    J.tuning m (r * Lcm m) * J.tuning m t = J.tuning m (r * Lcm m + t) := by
  refine IdealSheaf.ext fun a => ?_
  obtain ⟨c, hk, hs⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [stalkIdeal_mul, J.stalkIdeal_tuning_eq_W m (r * Lcm m) c hk hs,
    J.stalkIdeal_tuning_eq_W m t c hk hs, J.stalkIdeal_tuning_eq_W m (r * Lcm m + t) c hk hs]
  exact c.W_mul_W_eq hm r t ht _

/-- `W_s(J)^j = W_{js}(J)` for `s = r · lcm(2, …, m)`, `r ≥ m − 1` [Kol07, Proposition 99 (7)]. -/
theorem tuning_pow (hm : 1 ≤ m) {r : ℕ} (hr : m - 1 ≤ r) (j : ℕ) :
    J.tuning m (r * Lcm m) ^ j = J.tuning m (j * (r * Lcm m)) := by
  refine IdealSheaf.ext fun a => ?_
  obtain ⟨c, hk, hs⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [stalkIdeal_pow, J.stalkIdeal_tuning_eq_W m (r * Lcm m) c hk hs,
    J.stalkIdeal_tuning_eq_W m (j * (r * Lcm m)) c hk hs]
  exact c.W_pow hm hr j _

/-- `W_s(J)` is D-balanced with respect to `s` for `s = r · lcm(2, …, m)`, `r ≥ m − 1`
[Kol07, Proposition 99 (8)]. -/
theorem isDBalanced_tuning (hm : 1 ≤ m) (hI : ∀ y, J.ord y ≤ m) {r : ℕ} (hr : m - 1 ≤ r) :
    (J.tuning m (r * Lcm m)).IsDBalanced (r * Lcm m) := by
  intro i hi
  rw [IdealSheaf.le_def]
  intro a
  obtain ⟨c, hk, hs⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [stalkIdeal_pow, stalkIdeal_pow,
    (J.tuning m (r * Lcm m)).stalkIdeal_iteratedDeriv_eq_Dpow c hk hs,
    J.stalkIdeal_tuning_eq_W m (r * Lcm m) c hk hs]
  exact c.isDBalanced_W hm (hI a) hr i hi

/-! ### Corollary 101 at the parameter `tuningParam m` -/

/-- `W_{s(m)}(J)` is D-balanced with respect to `s(m) = tuningParam m` ([Kol07, Corollary 101] at
`s = s(m)`). -/
theorem isDBalanced_tuning_tuningParam (hm : 1 ≤ m) (hI : ∀ y, J.ord y ≤ m) :
    (J.tuning m (tuningParam m)).IsDBalanced (tuningParam m) :=
  J.isDBalanced_tuning m hm hI (le_max_left _ _)

/-- `W_{s(m)}(J)` is MC-invariant with respect to `s(m) = tuningParam m` ([Kol07, Corollary 101]
at `s = s(m)`). -/
theorem isMCInvariant_tuning_tuningParam (hm : 1 ≤ m) (hI : ∀ y, J.ord y ≤ m) :
    (J.tuning m (tuningParam m)).IsMCInvariant (tuningParam m) :=
  J.isMCInvariant_tuning m (tuningParam m) hm hI (one_le_tuningParam m)

/-! ### Orders and cosupports -/

/-- For `m, s ≥ 1`, `s ≤ ord_x W_s(J) ↔ m ≤ ord_x J` (the local form of Kollár's
`max-ord W(I) = m!`, [Kol07, Theorem 54.2 (i)]). -/
theorem le_ord_tuning_iff (hm : 1 ≤ m) (hs : 1 ≤ s) (x : M) :
    (s : ℕ∞) ≤ (J.tuning m s).ord x ↔ (m : ℕ∞) ≤ J.ord x := by
  obtain ⟨c, hk, hs'⟩ := exists_regularCoords_stalk_linear 𝕜 E x
  unfold IdealSheaf.ord
  rw [J.stalkIdeal_tuning_eq_W m s c hk hs']
  exact c.le_ord_W_iff hm hs

/-- The cosupport of `W_s(J)` is the locus where `J` has order `≥ m` (the remark after
[Kol07, Definition 83]: "`cosupp(I, m) = cosupp I`" for a D-balanced ideal): off it `W_s(J)` is
the unit sheaf (`W_eq_top_of_ord_lt`), on it `W_s(J)` has order `≥ s ≥ 1` (`le_ord_W`). -/
theorem support_tuning (hm : 1 ≤ m) (hs : 1 ≤ s) :
    (J.tuning m s).support = {x | (m : ℕ∞) ≤ J.ord x} := by
  refine Set.ext fun a => ?_
  obtain ⟨c, hk, hs'⟩ := exists_regularCoords_stalk_linear 𝕜 E a
  rw [mem_support, Set.mem_ofPred_eq, J.stalkIdeal_tuning_eq_W m s c hk hs', IdealSheaf.ord,
    ne_eq, ← IsLocalRing.ord_eq_zero_iff]
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    exact h (by rw [c.W_eq_top_of_ord_lt hm hlt, ord_top])
  · intro h h0
    have h1 : (s : ℕ∞) ≤ 0 := h0 ▸ c.le_ord_W h s
    have h2 : s = 0 := by exact_mod_cast le_antisymm h1 bot_le
    omega

/-- `ord_x W_s(J) = s` where `ord_x J = m ≥ 1` (the local form of [Kol07, Theorem 54.2 (i)]). -/
theorem ord_tuning (hm : 1 ≤ m) {x : M} (hx : J.ord x = m) : (J.tuning m s).ord x = s := by
  obtain ⟨c, hk, hs'⟩ := exists_regularCoords_stalk_linear 𝕜 E x
  unfold IdealSheaf.ord at hx ⊢
  rw [J.stalkIdeal_tuning_eq_W m s c hk hs']
  exact c.ord_W hm hx s

/-- `W_{s(1)}(J) = J`: for `m = 1` the coefficient ideal is the ideal itself (Kollár's "`I = W(I)`"
for an ideal of order `1`, [Kol07, Theorem 103, proof, Step 2.4]). -/
theorem tuning_one_tuningParam : J.tuning 1 (tuningParam 1) = J := by
  rw [show tuningParam 1 = 1 by decide, J.tuning_one 1 le_rfl, Nat.sub_self, iteratedDeriv_zero]

end Manifold.IdealSheaf

end
