/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Differential
import Hironaka.Algebra.Local.QuotientParameters
import Hironaka.Algebra.Local.Regular
import Hironaka.AnalyticSpace.Jacobian
import Hironaka.AnalyticSpace.ModelChart
import Hironaka.AnalyticSpace.ModelSupport
import Hironaka.AnalyticSpace.RegularParameters
import Hironaka.AnalyticSpace.RegularStalk
import Hironaka.Manifold.IdealSheaf.Identity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# The Jacobian criterion on four hypersurfaces

The Jacobian criterion for the simple points of a local model,
`isRegularLocalRing_stalk_iff_jacobian` (`Hironaka.AnalyticSpace.Jacobian`), read on four
hypersurfaces: the node `y² = x² + x³` and the cusp `y² = x³` in `K²` (simple exactly off the
origin), the Whitney umbrella `x² = z y²` in `ℝ³` (the multiple points are exactly the `z`-axis,
the handle `z < 0` included: there the real points form a line, but the stalk is not regular),
and `V(x² + y²) ⊆ ℝ²`, which has no simple point: the standard example of the phenomenon
Hironaka remarks on [Hir64, Introduction], a reduced real-analytic space whose simple locus is
not dense. (Its support is the origin, since `x² + y² = 0` forces `x = y = 0` over `ℝ`, and it
is reduced; neither is recorded as a statement in this file — `RealPlaneCircle` proves the
support statement for the ideal sheaf `circleIdeal`.) "Simple point" is `regularLocus`'s clause,
`IsRegularLocalRing 𝒪_{X,z}`, stated on the local model `V(g) ⊆ (Kⁿ, 𝒜_{Kⁿ})`.

For a hypersurface `X = V(g)` the criterion reads: `z ∈ X` is simple iff `dg_z ≠ 0`. If
`dg_z ≠ 0` then `g_z` is a regular parameter and `𝒜/(g_z)` is regular
(`isRegularLocalRing_stalk_of_dlin_ne_zero`). If `dg_z = 0`, i.e. `g_z ∈ 𝔪_z²`, the only
subfamily of the one generator with independent differentials is the empty one, which would
force `dim 𝒜/(g_z) = n = dim 𝒜`, i.e. `g_z = 0` in the domain `𝒜_{Kⁿ,z}`
(`eq_bot_of_ringKrullDim_quotient_eq`) — excluded because `g` does not vanish identically near
`z` (`germTop_ne_zero_of_curve`: the germ of a section is zero iff the section vanishes near the
point, the identity lemma). The differential of a polynomial in the coordinates is computed by
expanding around the point: `g_z = ∑ aᵢ (zᵢ − qᵢ) + r` with `r ∈ 𝔪_z²` gives `dg_z = a`
(`dlin_eq_of_sub_sum_mem_sq`; `dlin` is `K`-linear, kills `𝔪²` and sends `zᵢ − qᵢ` to `eᵢ`).

The equation `circleEq` of the last example is used again in `HironakaExamples.Space.CircleSpace`
(the analytic space `V(x² + y²)`).
-/

@[expose] public section

open TopologicalSpace Opposite CategoryTheory Filter IsLocalRing
open scoped Manifold ContDiff Topology
open Manifold

universe u

noncomputable section

namespace Hironaka.Space

open AnalyticSpace

variable {K : Type} [RCLike K] {n : ℕ}

section Hypersurface

/-- The germ at `q` of a global analytic function on `Kⁿ` (a `def`, so that the expansion lemmas
below rewrite it as a single term). -/
def germTop (g : AnalyticFun K n ⊤) (q : Kn.{u} K n) :
    (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q :=
  (affine K n).toLocallyRingedSpace.presheaf.germ ⊤ q (Opens.mem_top q) g

theorem germTop_coordSection (q : Kn.{u} K n) (i : Fin n) :
    germTop (AnalyticSpace.coordSection K n i) q = coordAt K n q i := rfl

theorem germTop_mul (a b : AnalyticFun K n ⊤) (q : Kn.{u} K n) :
    germTop (a * b) q = germTop a q * germTop b q :=
  map_mul ((affine K n).toLocallyRingedSpace.presheaf.germ ⊤ q (Opens.mem_top q)).hom a b

theorem germTop_sub (a b : AnalyticFun K n ⊤) (q : Kn.{u} K n) :
    germTop (a - b) q = germTop a q - germTop b q :=
  map_sub ((affine K n).toLocallyRingedSpace.presheaf.germ ⊤ q (Opens.mem_top q)).hom a b

theorem germTop_add (a b : AnalyticFun K n ⊤) (q : Kn.{u} K n) :
    germTop (a + b) q = germTop a q + germTop b q :=
  map_add ((affine K n).toLocallyRingedSpace.presheaf.germ ⊤ q (Opens.mem_top q)).hom a b

/-- A global section whose values along a continuous curve through `q` are nonzero off `q` has
nonzero germ at `q` (the identity lemma `germ_eq_zero_iff`). -/
theorem germTop_ne_zero_of_curve (g : AnalyticFun K n ⊤) (q : Kn.{u} K n) (γ : K → Kn.{u} K n)
    (hγ : Continuous γ) (hγ0 : γ 0 = q)
    (h : ∀ᶠ t in 𝓝[≠] (0 : K), AnalyticFun.eval g ⟨γ t, Opens.mem_top _⟩ ≠ 0) :
    germTop g q ≠ 0 := by
  subst hγ0
  intro h0
  have hev : extendSection K (Kn.{u} K n) g =ᶠ[𝓝 (γ 0)] 0 :=
    (IdealSheaf.germ_eq_zero_iff (Opens.mem_top (γ 0)) g).mp h0
  have h1 : ∀ᶠ t in 𝓝 (0 : K), AnalyticFun.eval g ⟨γ t, Opens.mem_top _⟩ = 0 := by
    filter_upwards [(hγ.tendsto 0).eventually hev] with t ht
    exact (extendSection_of_mem K (Kn.{u} K n) g (Opens.mem_top (γ t))).symm.trans ht
  obtain ⟨t, ht1, ht2⟩ := (h.and (h1.filter_mono nhdsWithin_le_nhds)).exists
  exact ht1 ht2

/-- The coordinate germ `zᵢ − qᵢ` lies in `𝔪_q`. -/
theorem coordAt_sub_const_mem_maximalIdeal (q : Kn.{u} K n) (i : Fin n) :
    coordAt K n q i - const K (Kn.{u} K n) (Kn.{u} K n) q (q.down i) ∈
      maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) := by
  have := mem_maximalIdeal_coordAt_sub K n q i
  rwa [eval_coordAt] at this

/-- `dlin` of an explicit expansion: if `s − ∑ i, aᵢ (zᵢ − qᵢ) ∈ 𝔪_q²`, then `d_q s = a`. -/
theorem dlin_eq_of_sub_sum_mem_sq (q : Kn.{u} K n)
    (s : (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) (a : Fin n → K)
    (hr : s - ∑ i, const K (Kn.{u} K n) (Kn.{u} K n) q (a i) *
        (coordAt K n q i - const K (Kn.{u} K n) (Kn.{u} K n) q (q.down i)) ∈
      maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) ^ 2) :
    dlin K n q s = a := by
  have hlin : dlin K n q (∑ i, const K (Kn.{u} K n) (Kn.{u} K n) q (a i) *
      (coordAt K n q i - const K (Kn.{u} K n) (Kn.{u} K n) q (q.down i))) = a := by
    rw [map_sum]
    simp_rw [dlin_const_mul', dlin_coordAt_sub]
    simp only [← Pi.single_smul, smul_eq_mul, mul_one, Finset.univ_sum_single]
  have hr0 := (dlin_eq_zero_iff_mem_maximalIdeal_sq K n q
    ((Ideal.pow_le_self two_ne_zero) hr)).mpr hr
  rw [map_sub, hlin, sub_eq_zero] at hr0
  exact hr0

variable (f : Fin 1 → AnalyticFun K n ⊤)

/-- The criterion for one equation, negative half: at a point `z` of `V(g)` where `g_z ∈ 𝔪_z²`
and `g_z ≠ 0` the stalk `𝒜_{Kⁿ,z}/(g_z)` is not regular. -/
theorem not_isRegularLocalRing_stalk_of_germ_mem_sq_of_ne_zero (z : localModel K n ⊤ f)
    (hsq : germTop (f 0) z.1.1 ∈
      maximalIdeal ((structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk z.1.1) ^ 2)
    (hne : germTop (f 0) z.1.1 ≠ 0) :
    ¬ IsRegularLocalRing ((localModel K n ⊤ f).toLocallyRingedSpace.presheaf.stalk z) := by
  rw [isRegularLocalRing_stalk_iff_jacobian]
  rintro ⟨c, σ, hdim, hli⟩
  have hc : c ≤ 1 := by
    have := Fintype.card_le_of_embedding σ
    simpa only [Fintype.card_fin] using this
  obtain hc0 | hc1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hc
  · subst hc0
    rw [Nat.cast_zero, zero_add, ringKrullDim_eq_of_ringEquiv (stalkEquivQuotientF z),
      ← ringKrullDim_stalk_affine K n z.1.1] at hdim
    have := isRegularLocalRing_stalk_affine K n z.1.1
    have hbot := Ideal.eq_bot_of_ringKrullDim_quotient_eq
      (span_germ_le_maximalIdeal z) hdim
    exact hne (Ideal.span_eq_bot.mp hbot _ ⟨0, rfl⟩)
  · subst hc1
    have h0 := hli.ne_zero 0
    rw [Subsingleton.elim (σ 0) 0] at h0
    exact h0 ((dlin_eq_zero_iff_mem_maximalIdeal_sq K n z.1.1
      ((Ideal.pow_le_self two_ne_zero) hsq)).mpr hsq)

/-- The criterion for one equation, positive half: at a point `z` of `V(g)` where `dg_z ≠ 0`
the stalk is regular (`g_z` is a regular parameter). -/
theorem isRegularLocalRing_stalk_of_dlin_ne_zero (z : localModel K n ⊤ f)
    (hd : dlin K n z.1.1 (germTop (f 0) z.1.1) ≠ 0) :
    IsRegularLocalRing ((localModel K n ⊤ f).toLocallyRingedSpace.presheaf.stalk z) := by
  have hm : ∀ j : Fin 1, (affine K n).toLocallyRingedSpace.presheaf.germ ⊤ z.1.1 z.1.2 (f j) ∈
      maximalIdeal ((affine K n).toLocallyRingedSpace.presheaf.stalk z.1.1) := fun j =>
    germ_mem_maximalIdeal_of_mem_cosupport ⊤ f z j
  have hli : LinearIndependent K (fun j : Fin 1 => dlin K n z.1.1
      ((affine K n).toLocallyRingedSpace.presheaf.germ ⊤ z.1.1 z.1.2 (f j))) := by
    rw [linearIndependent_unique_iff]
    exact hd
  have hreg := (isRegularLocalRing_quotient_span_range_and_ringKrullDim K n z.1.1
    (fun j : Fin 1 => (affine K n).toLocallyRingedSpace.presheaf.germ ⊤ z.1.1 z.1.2 (f j))
    hm hli).1
  exact @IsRegularLocalRing.of_ringEquiv _ _ hreg _ _ (stalkEquivQuotientF z).symm

end Hypersurface

section Node

variable (K) in
/-- The node `y² = x² + x³` in `K²`: the one equation `y·y − x·x − x·x·x`. -/
def nodeEq : Fin 1 → AnalyticFun K 2 (⊤ : Opens (Kn.{u} K 2)) :=
  ![AnalyticSpace.coordSection K 2 1 * AnalyticSpace.coordSection K 2 1 -
      AnalyticSpace.coordSection K 2 0 * AnalyticSpace.coordSection K 2 0 -
    AnalyticSpace.coordSection K 2 0 * AnalyticSpace.coordSection K 2 0 *
        AnalyticSpace.coordSection K 2 0]

theorem nodeEq_germ (q : Kn.{u} K 2) :
    germTop (nodeEq K 0) q = coordAt K 2 q 1 * coordAt K 2 q 1 - coordAt K 2 q 0 * coordAt K 2 q 0 -
      coordAt K 2 q 0 * coordAt K 2 q 0 * coordAt K 2 q 0 := by
  simp only [nodeEq, Matrix.cons_val_zero]
  erw [germTop_sub, germTop_sub, germTop_mul, germTop_mul, germTop_mul, germTop_mul]
  rfl

/-- The origin lies on the node. -/
example : ∃ z : localModel K 2 ⊤ (nodeEq.{u} K), z.1.1 = ULift.up 0 :=
  ⟨⟨⟨ULift.up 0, Opens.mem_top _⟩,
    (mem_cosupport_modelIdeal_iff K 2 ⊤ (nodeEq K) ⟨ULift.up 0, Opens.mem_top _⟩).mpr fun i => by
      rw [Subsingleton.elim i 0]
      change (0 : K) * 0 - 0 * 0 - 0 * 0 * 0 = 0
      ring⟩, rfl⟩

/-- The node `y² = x² + x³` is simple exactly off the origin — at the origin the
differential `(−2x − 3x², 2y)` vanishes and the equation lies in `𝔪²`; at every other point of
the curve it does not vanish (`y ≠ 0`, or `y = 0` and then `x = −1`). -/
theorem node_isRegularLocalRing_stalk_iff (z : localModel K 2 ⊤ (nodeEq.{u} K)) :
    IsRegularLocalRing ((localModel K 2 ⊤ (nodeEq K)).toLocallyRingedSpace.presheaf.stalk z) ↔
      z.1.1 ≠ ULift.up 0 := by
  have hz : z.1.1.down 1 * z.1.1.down 1 - z.1.1.down 0 * z.1.1.down 0 -
      z.1.1.down 0 * z.1.1.down 0 * z.1.1.down 0 = 0 :=
    (mem_cosupport_modelIdeal_iff K 2 ⊤ (nodeEq K) z.1).mp z.2 0
  obtain ⟨X, hXdef⟩ : ∃ X, X = coordAt K 2 z.1.1 0 -
    const K (Kn.{u} K 2) (Kn.{u} K 2) z.1.1 (z.1.1.down 0) := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = coordAt K 2 z.1.1 1 -
    const K (Kn.{u} K 2) (Kn.{u} K 2) z.1.1 (z.1.1.down 1) := ⟨_, rfl⟩
  have hX : X ∈ maximalIdeal _ := hXdef ▸ coordAt_sub_const_mem_maximalIdeal z.1.1 0
  have hY : Y ∈ maximalIdeal _ := hYdef ▸ coordAt_sub_const_mem_maximalIdeal z.1.1 1
  have hgx : coordAt K 2 z.1.1 0 = X + const K (Kn.{u} K 2) (Kn.{u} K 2) z.1.1 (z.1.1.down 0) := by
    rw [hXdef, sub_add_cancel]
  have hgy : coordAt K 2 z.1.1 1 = Y + const K (Kn.{u} K 2) (Kn.{u} K 2) z.1.1 (z.1.1.down 1) := by
    rw [hYdef, sub_add_cancel]
  constructor
  · intro hreg h0
    have hx0 : z.1.1.down 0 = 0 := by rw [h0]; rfl
    have hy0 : z.1.1.down 1 = 0 := by rw [h0]; rfl
    rw [hx0, map_zero, add_zero] at hgx
    rw [hy0, map_zero, add_zero] at hgy
    refine not_isRegularLocalRing_stalk_of_germ_mem_sq_of_ne_zero (nodeEq K) z ?_ ?_ hreg
    · rw [nodeEq_germ, hgx, hgy, pow_two]
      exact Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_mul hY hY) (Ideal.mul_mem_mul hX hX))
        (Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hX hX))
    · refine germTop_ne_zero_of_curve _ _ (fun t : K => (ULift.up ![t, 0] : Kn.{u} K 2))
        (continuous_uliftUp.comp (continuous_pi fun i => by
          fin_cases i
          · exact continuous_id
          · exact continuous_const)) ?_ ?_
      · rw [h0]
        congr 1
        ext i
        fin_cases i <;> rfl
      · have h1 : ∀ᶠ t in 𝓝 (0 : K), 1 + t ≠ 0 :=
          (continuous_const.add continuous_id).continuousAt.eventually_ne (by simp)
        filter_upwards [h1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t h1t ht
        change (0 : K) * 0 - t * t - t * t * t ≠ 0
        intro h
        have h2 : t * t * (1 + t) = 0 := by linear_combination -h
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact ht (mul_self_eq_zero.mp h3)
        · exact h1t h3
  · intro h0
    apply isRegularLocalRing_stalk_of_dlin_ne_zero
    have key : dlin K 2 z.1.1 (germTop (nodeEq K 0) z.1.1) =
        ![-(2 * z.1.1.down 0 + 3 * (z.1.1.down 0 * z.1.1.down 0)), 2 * z.1.1.down 1] := by
      apply dlin_eq_of_sub_sum_mem_sq
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hmem : Y * Y - X * X - X * X * X -
          const K (Kn.{u} K 2) (Kn.{u} K 2) z.1.1 (3 * z.1.1.down 0) * (X * X) ∈
          maximalIdeal ((structureSheaf K (Kn.{u} K 2) (Kn.{u} K 2)).presheaf.stalk z.1.1) ^ 2 := by
        rw [pow_two]
        exact Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_mul hY hY)
          (Ideal.mul_mem_mul hX hX)) (Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hX hX)))
          (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hX hX))
      convert hmem using 1
      have hc := congrArg (const K (Kn.{u} K 2) (Kn.{u} K 2) z.1.1) hz
      simp only [map_sub, map_mul, map_zero] at hc
      rw [nodeEq_germ, hgx, hgy]
      simp only [map_neg, map_add, map_mul, map_ofNat]
      linear_combination hc
    rw [key]
    intro h
    have h1 := congrFun h 1
    have h2 := congrFun h 0
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply,
      mul_eq_zero, OfNat.ofNat_ne_zero, false_or, neg_eq_zero] at h1 h2
    have hx : z.1.1.down 0 ≠ 0 := fun hx => h0 (by
      rw [← ULift.up_down z.1.1]
      congr 1
      funext i
      fin_cases i
      · exact hx
      · exact h1)
    rw [h1] at hz
    have h3 : z.1.1.down 0 * z.1.1.down 0 * (1 + z.1.1.down 0) = 0 := by linear_combination -hz
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hx (mul_self_eq_zero.mp h4)
    · have h5 : z.1.1.down 0 = -1 := by linear_combination h4
      rw [h5] at h2
      norm_num at h2

end Node

section Cusp

variable (K) in
/-- The cusp `y² = x³` in `K²`: the one equation `y·y − x·x·x`. -/
def cuspEq : Fin 1 → AnalyticFun K 2 (⊤ : Opens (Kn.{u} K 2)) :=
  ![AnalyticSpace.coordSection K 2 1 * AnalyticSpace.coordSection K 2 1 -
    AnalyticSpace.coordSection K 2 0 * AnalyticSpace.coordSection K 2 0 *
        AnalyticSpace.coordSection K 2 0]

theorem cuspEq_germ (q : Kn.{u} K 2) :
    germTop (cuspEq K 0) q = coordAt K 2 q 1 * coordAt K 2 q 1 -
      coordAt K 2 q 0 * coordAt K 2 q 0 * coordAt K 2 q 0 := by
  simp only [cuspEq, Matrix.cons_val_zero]
  erw [germTop_sub, germTop_mul, germTop_mul, germTop_mul]
  rfl

/-- The origin lies on the cusp. -/
example : ∃ z : localModel K 2 ⊤ (cuspEq.{u} K), z.1.1 = ULift.up 0 :=
  ⟨⟨⟨ULift.up 0, Opens.mem_top _⟩,
    (mem_cosupport_modelIdeal_iff K 2 ⊤ (cuspEq K) ⟨ULift.up 0, Opens.mem_top _⟩).mpr fun i => by
      rw [Subsingleton.elim i 0]
      change (0 : K) * 0 - 0 * 0 * 0 = 0
      ring⟩, rfl⟩

/-- The cusp `y² = x³` is simple exactly off the origin — the differential
`(−3x², 2y)` vanishes on the curve only at the origin, where the equation lies in `𝔪²`. -/
theorem cusp_isRegularLocalRing_stalk_iff (z : localModel K 2 ⊤ (cuspEq.{u} K)) :
    IsRegularLocalRing ((localModel K 2 ⊤ (cuspEq K)).toLocallyRingedSpace.presheaf.stalk z) ↔
      z.1.1 ≠ ULift.up 0 := by
  have hz : z.1.1.down 1 * z.1.1.down 1 - z.1.1.down 0 * z.1.1.down 0 * z.1.1.down 0 = 0 :=
    (mem_cosupport_modelIdeal_iff K 2 ⊤ (cuspEq K) z.1).mp z.2 0
  obtain ⟨X, hXdef⟩ : ∃ X, X = coordAt K 2 z.1.1 0 -
    const K (Kn.{u} K 2) (Kn.{u} K 2) z.1.1 (z.1.1.down 0) := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = coordAt K 2 z.1.1 1 -
    const K (Kn.{u} K 2) (Kn.{u} K 2) z.1.1 (z.1.1.down 1) := ⟨_, rfl⟩
  have hX : X ∈ maximalIdeal _ := hXdef ▸ coordAt_sub_const_mem_maximalIdeal z.1.1 0
  have hY : Y ∈ maximalIdeal _ := hYdef ▸ coordAt_sub_const_mem_maximalIdeal z.1.1 1
  have hgx : coordAt K 2 z.1.1 0 = X + const K (Kn.{u} K 2) (Kn.{u} K 2) z.1.1 (z.1.1.down 0) := by
    rw [hXdef, sub_add_cancel]
  have hgy : coordAt K 2 z.1.1 1 = Y + const K (Kn.{u} K 2) (Kn.{u} K 2) z.1.1 (z.1.1.down 1) := by
    rw [hYdef, sub_add_cancel]
  constructor
  · intro hreg h0
    have hx0 : z.1.1.down 0 = 0 := by rw [h0]; rfl
    have hy0 : z.1.1.down 1 = 0 := by rw [h0]; rfl
    rw [hx0, map_zero, add_zero] at hgx
    rw [hy0, map_zero, add_zero] at hgy
    refine not_isRegularLocalRing_stalk_of_germ_mem_sq_of_ne_zero (cuspEq K) z ?_ ?_ hreg
    · rw [cuspEq_germ, hgx, hgy, pow_two]
      exact Ideal.sub_mem _ (Ideal.mul_mem_mul hY hY)
        (Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hX hX))
    · refine germTop_ne_zero_of_curve _ _ (fun t : K => (ULift.up ![t, 0] : Kn.{u} K 2))
        (continuous_uliftUp.comp (continuous_pi fun i => by
          fin_cases i
          · exact continuous_id
          · exact continuous_const)) ?_ ?_
      · rw [h0]
        congr 1
        ext i
        fin_cases i <;> rfl
      · filter_upwards [self_mem_nhdsWithin] with t ht
        change (0 : K) * 0 - t * t * t ≠ 0
        intro h
        have h2 : t * t * t = 0 := by linear_combination -h
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact ht (mul_self_eq_zero.mp h3)
        · exact ht h3
  · intro h0
    apply isRegularLocalRing_stalk_of_dlin_ne_zero
    have key : dlin K 2 z.1.1 (germTop (cuspEq K 0) z.1.1) =
        ![-(3 * (z.1.1.down 0 * z.1.1.down 0)), 2 * z.1.1.down 1] := by
      apply dlin_eq_of_sub_sum_mem_sq
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hmem : Y * Y - X * X * X -
          const K (Kn.{u} K 2) (Kn.{u} K 2) z.1.1 (3 * z.1.1.down 0) * (X * X) ∈
          maximalIdeal ((structureSheaf K (Kn.{u} K 2) (Kn.{u} K 2)).presheaf.stalk z.1.1) ^ 2 := by
        rw [pow_two]
        exact Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_mul hY hY)
          (Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hX hX)))
          (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hX hX))
      convert hmem using 1
      have hc := congrArg (const K (Kn.{u} K 2) (Kn.{u} K 2) z.1.1) hz
      simp only [map_sub, map_mul, map_zero] at hc
      rw [cuspEq_germ, hgx, hgy]
      simp only [map_neg, map_mul, map_ofNat]
      linear_combination hc
    rw [key]
    intro h
    have h1 := congrFun h 1
    have h2 := congrFun h 0
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply,
      mul_eq_zero, OfNat.ofNat_ne_zero, false_or, neg_eq_zero, or_self] at h1 h2
    exact h0 (by
      rw [← ULift.up_down z.1.1]
      congr 1
      funext i
      fin_cases i
      · exact h2
      · exact h1)

end Cusp

section Umbrella

/-- The Whitney umbrella `x² = z y²` in `ℝ³`: the one equation `x·x − z·(y·y)`. -/
def umbrellaEq : Fin 1 → AnalyticFun ℝ 3 (⊤ : Opens (Kn.{u} ℝ 3)) :=
  ![AnalyticSpace.coordSection ℝ 3 0 * AnalyticSpace.coordSection ℝ 3 0 -
    AnalyticSpace.coordSection ℝ 3 2 * (AnalyticSpace.coordSection ℝ 3 1 *
        AnalyticSpace.coordSection ℝ 3 1)]

theorem umbrellaEq_germ (q : Kn.{u} ℝ 3) :
    germTop (umbrellaEq 0) q = coordAt ℝ 3 q 0 * coordAt ℝ 3 q 0 -
      coordAt ℝ 3 q 2 * (coordAt ℝ 3 q 1 * coordAt ℝ 3 q 1) := by
  simp only [umbrellaEq, Matrix.cons_val_zero]
  erw [germTop_sub, germTop_mul, germTop_mul, germTop_mul]
  rfl

/-- The `z`-axis lies on the umbrella. -/
example (c : ℝ) : ∃ z : localModel ℝ 3 ⊤ umbrellaEq.{u}, z.1.1 = ULift.up ![0, 0, c] :=
  ⟨⟨⟨ULift.up ![0, 0, c], Opens.mem_top _⟩,
    (mem_cosupport_modelIdeal_iff ℝ 3 ⊤ umbrellaEq ⟨ULift.up ![0, 0, c], Opens.mem_top _⟩).mpr
      fun i => by
        rw [Subsingleton.elim i 0]
        change (0 : ℝ) * 0 - c * (0 * 0) = 0
        ring⟩, rfl⟩

/-- On the `z`-axis the umbrella's stalk is not regular: the equation lies in `𝔪²` there and
does not vanish identically (`x² ≠ 0` along the `x`-direction). -/
theorem umbrella_not_isRegularLocalRing_of_axis (z : localModel ℝ 3 ⊤ umbrellaEq.{u})
    (hx0 : z.1.1.down 0 = 0) (hy0 : z.1.1.down 1 = 0) :
    ¬ IsRegularLocalRing ((localModel ℝ 3 ⊤ umbrellaEq).toLocallyRingedSpace.presheaf.stalk z) := by
  have hX := coordAt_sub_const_mem_maximalIdeal z.1.1 0
  have hY := coordAt_sub_const_mem_maximalIdeal z.1.1 1
  rw [hx0, map_zero, sub_zero] at hX
  rw [hy0, map_zero, sub_zero] at hY
  refine not_isRegularLocalRing_stalk_of_germ_mem_sq_of_ne_zero umbrellaEq z ?_ ?_
  · rw [umbrellaEq_germ, pow_two]
    exact Ideal.sub_mem _ (Ideal.mul_mem_mul hX hX)
      (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hY hY))
  · refine germTop_ne_zero_of_curve _ _ (fun t : ℝ => (ULift.up ![t, 0, z.1.1.down 2] : Kn.{u} ℝ 3))
      (continuous_uliftUp.comp (continuous_pi fun i => by
        fin_cases i
        · exact continuous_id
        · exact continuous_const
        · exact continuous_const)) ?_ ?_
    · rw [← ULift.up_down z.1.1]
      congr 1
      funext i
      fin_cases i
      · exact hx0.symm
      · exact hy0.symm
      · rfl
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change t * t - z.1.1.down 2 * ((0 : ℝ) * 0) ≠ 0
      intro h
      exact ht (mul_self_eq_zero.mp (by linear_combination h))

/-- The multiple points of the Whitney umbrella `x² = z y²` are exactly the `z`-axis:
off the axis (`y ≠ 0` on the surface) the differential `(2x, −2zy, −y²)` does not vanish. -/
theorem umbrella_isRegularLocalRing_stalk_iff (z : localModel ℝ 3 ⊤ umbrellaEq.{u}) :
    IsRegularLocalRing ((localModel ℝ 3 ⊤ umbrellaEq).toLocallyRingedSpace.presheaf.stalk z) ↔
      ¬ (z.1.1.down 0 = 0 ∧ z.1.1.down 1 = 0) := by
  have hz : z.1.1.down 0 * z.1.1.down 0 - z.1.1.down 2 * (z.1.1.down 1 * z.1.1.down 1) = 0 :=
    (mem_cosupport_modelIdeal_iff ℝ 3 ⊤ umbrellaEq z.1).mp z.2 0
  constructor
  · intro hreg ⟨hx0, hy0⟩
    exact umbrella_not_isRegularLocalRing_of_axis z hx0 hy0 hreg
  · intro h0
    apply isRegularLocalRing_stalk_of_dlin_ne_zero
    obtain ⟨X, hXdef⟩ : ∃ X, X = coordAt ℝ 3 z.1.1 0 -
      const ℝ (Kn.{u} ℝ 3) (Kn.{u} ℝ 3) z.1.1 (z.1.1.down 0) := ⟨_, rfl⟩
    obtain ⟨Y, hYdef⟩ : ∃ Y, Y = coordAt ℝ 3 z.1.1 1 -
      const ℝ (Kn.{u} ℝ 3) (Kn.{u} ℝ 3) z.1.1 (z.1.1.down 1) := ⟨_, rfl⟩
    obtain ⟨Z, hZdef⟩ : ∃ Z, Z = coordAt ℝ 3 z.1.1 2 -
      const ℝ (Kn.{u} ℝ 3) (Kn.{u} ℝ 3) z.1.1 (z.1.1.down 2) := ⟨_, rfl⟩
    have hX : X ∈ maximalIdeal _ := hXdef ▸ coordAt_sub_const_mem_maximalIdeal z.1.1 0
    have hY : Y ∈ maximalIdeal _ := hYdef ▸ coordAt_sub_const_mem_maximalIdeal z.1.1 1
    have hgx : coordAt ℝ 3 z.1.1 0 =
        X + const ℝ (Kn.{u} ℝ 3) (Kn.{u} ℝ 3) z.1.1 (z.1.1.down 0) := by
      rw [hXdef, sub_add_cancel]
    have hgy : coordAt ℝ 3 z.1.1 1 =
        Y + const ℝ (Kn.{u} ℝ 3) (Kn.{u} ℝ 3) z.1.1 (z.1.1.down 1) := by
      rw [hYdef, sub_add_cancel]
    have hgz : coordAt ℝ 3 z.1.1 2 =
        Z + const ℝ (Kn.{u} ℝ 3) (Kn.{u} ℝ 3) z.1.1 (z.1.1.down 2) := by
      rw [hZdef, sub_add_cancel]
    have key : dlin ℝ 3 z.1.1 (germTop (umbrellaEq 0) z.1.1) =
        ![2 * z.1.1.down 0, -(2 * (z.1.1.down 2 * z.1.1.down 1)),
          -(z.1.1.down 1 * z.1.1.down 1)] := by
      apply dlin_eq_of_sub_sum_mem_sq
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      have hmem : X * X - Z * (Y * Y) -
          const ℝ (Kn.{u} ℝ 3) (Kn.{u} ℝ 3) z.1.1 (2 * z.1.1.down 1) * (Z * Y) -
          const ℝ (Kn.{u} ℝ 3) (Kn.{u} ℝ 3) z.1.1 (z.1.1.down 2) * (Y * Y) ∈
          maximalIdeal ((structureSheaf ℝ (Kn.{u} ℝ 3) (Kn.{u} ℝ 3)).presheaf.stalk z.1.1) ^ 2 := by
        rw [pow_two]
        exact Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_mul hX hX)
          (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hY hY)))
          (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul
            (hZdef ▸ coordAt_sub_const_mem_maximalIdeal z.1.1 2) hY)))
          (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hY hY))
      convert hmem using 1
      have hc := congrArg (const ℝ (Kn.{u} ℝ 3) (Kn.{u} ℝ 3) z.1.1) hz
      simp only [map_sub, map_mul, map_zero] at hc
      rw [umbrellaEq_germ, hgx, hgy, hgz]
      simp only [map_neg, map_mul, map_ofNat]
      linear_combination hc
    rw [key]
    intro h
    have h2 := congrFun h 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply, neg_eq_zero,
      mul_self_eq_zero] at h2
    rw [h2, mul_zero, mul_zero, sub_zero, mul_self_eq_zero] at hz
    exact h0 ⟨hz, h2⟩

/-- The handle of the umbrella: every point with `z < 0` is a multiple point — the
real points there form the `z`-axis (`x² = z y² ≤ 0` forces `x = y = 0`), so the handle is
disjoint from the closure of the simple points, although its real point set is a line. -/
theorem umbrella_not_isRegularLocalRing_stalk_of_neg (z : localModel ℝ 3 ⊤ umbrellaEq.{u})
    (hneg : z.1.1.down 2 < 0) :
    ¬ IsRegularLocalRing ((localModel ℝ 3 ⊤ umbrellaEq).toLocallyRingedSpace.presheaf.stalk z) := by
  have hz : z.1.1.down 0 * z.1.1.down 0 - z.1.1.down 2 * (z.1.1.down 1 * z.1.1.down 1) = 0 :=
    (mem_cosupport_modelIdeal_iff ℝ 3 ⊤ umbrellaEq z.1).mp z.2 0
  have hx2 : z.1.1.down 0 * z.1.1.down 0 = 0 := by
    nlinarith [mul_self_nonneg (z.1.1.down 0), mul_self_nonneg (z.1.1.down 1),
      mul_nonneg (neg_nonneg.mpr hneg.le) (mul_self_nonneg (z.1.1.down 1))]
  have hx0 : z.1.1.down 0 = 0 := mul_self_eq_zero.mp hx2
  rw [hx2, zero_sub, neg_eq_zero, mul_eq_zero, mul_self_eq_zero] at hz
  exact umbrella_not_isRegularLocalRing_of_axis z hx0 (hz.resolve_left hneg.ne)

end Umbrella

section Circle

/-- `V(x² + y²) ⊆ ℝ²`: the one equation `x·x + y·y`, the standard example of the phenomenon
Hironaka remarks on [Hir64, Introduction]. -/
def circleEq : Fin 1 → AnalyticFun ℝ 2 (⊤ : Opens (Kn.{u} ℝ 2)) :=
  ![AnalyticSpace.coordSection ℝ 2 0 * AnalyticSpace.coordSection ℝ 2 0 +
      AnalyticSpace.coordSection ℝ 2 1 * AnalyticSpace.coordSection ℝ 2 1]

theorem circleEq_germ (q : Kn.{u} ℝ 2) :
    germTop (circleEq 0) q =
      coordAt ℝ 2 q 0 * coordAt ℝ 2 q 0 + coordAt ℝ 2 q 1 * coordAt ℝ 2 q 1 := by
  simp only [circleEq, Matrix.cons_val_zero]
  erw [germTop_add, germTop_mul, germTop_mul]
  rfl

/-- The origin lies on `V(x² + y²)` (the support is not empty). -/
example : ∃ z : localModel ℝ 2 ⊤ circleEq.{u}, z.1.1 = ULift.up 0 :=
  ⟨⟨⟨ULift.up 0, Opens.mem_top _⟩,
    (mem_cosupport_modelIdeal_iff ℝ 2 ⊤ circleEq ⟨ULift.up 0, Opens.mem_top _⟩).mpr fun i => by
      rw [Subsingleton.elim i 0]
      change (0 : ℝ) * 0 + 0 * 0 = 0
      ring⟩, rfl⟩

/-- `V(x² + y²) ⊆ ℝ²` has no simple point. A point `z` of the model has `x = y = 0` (a real sum
of two squares vanishes only if both do), and there the equation lies in `𝔪²` and does not
vanish identically (`x² ≠ 0` along the `x`-axis): `X.regularLocus = ∅` although `X ≠ ∅`. This is the
phenomenon Hironaka remarks on [Hir64, Introduction]. That the support is exactly the origin is
not recorded as a separate statement here. -/
theorem circle_setOf_isRegularLocalRing_stalk_eq_empty : {z : localModel ℝ 2 ⊤ circleEq.{u} |
    IsRegularLocalRing ((localModel ℝ 2 ⊤ circleEq).toLocallyRingedSpace.presheaf.stalk z)} =
      ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hreg
  have hz : z.1.1.down 0 * z.1.1.down 0 + z.1.1.down 1 * z.1.1.down 1 = 0 :=
    (mem_cosupport_modelIdeal_iff ℝ 2 ⊤ circleEq z.1).mp z.2 0
  obtain ⟨hx0, hy0⟩ := mul_self_add_mul_self_eq_zero.mp hz
  have hX := coordAt_sub_const_mem_maximalIdeal z.1.1 0
  have hY := coordAt_sub_const_mem_maximalIdeal z.1.1 1
  rw [hx0, map_zero, sub_zero] at hX
  rw [hy0, map_zero, sub_zero] at hY
  refine not_isRegularLocalRing_stalk_of_germ_mem_sq_of_ne_zero circleEq z ?_ ?_ hreg
  · rw [circleEq_germ, pow_two]
    exact Ideal.add_mem _ (Ideal.mul_mem_mul hX hX) (Ideal.mul_mem_mul hY hY)
  · refine germTop_ne_zero_of_curve _ _ (fun t : ℝ => (ULift.up ![t, 0] : Kn.{u} ℝ 2))
      (continuous_uliftUp.comp (continuous_pi fun i => by
        fin_cases i
        · exact continuous_id
        · exact continuous_const)) ?_ ?_
    · rw [← ULift.up_down z.1.1]
      congr 1
      funext i
      fin_cases i
      · exact hx0.symm
      · exact hy0.symm
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change t * t + (0 : ℝ) * 0 ≠ 0
      intro h
      exact ht (mul_self_eq_zero.mp (by linear_combination h))

end Circle

end Hironaka.Space

end
