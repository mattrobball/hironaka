/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.HomExt
public import Hironaka.Manifold.Chart.Cotangent
import Hironaka.Manifold.Germ.TaylorIdeal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The differential of a germ of `𝒜_{Kⁿ}`

The Taylor homomorphism `T_q : 𝒜_{Kⁿ,q} → K[[X]]` of a regular coordinate chart [BM97, (0.3)],
here `taylorHom` in the identity chart of `Kⁿ`. The **differential** `d_q s` of a germ `s` at `q`
is the linear part of its Taylor series: the vector `(∂_i s (q))_i ∈ Kⁿ` of the coefficients of
`X_i` in `T_q s`, read as the functional `v ↦ ∑ ∂_i s(q) v_i` on `Kⁿ`. It is the `linearPart` of
`Hironaka/Manifold/Chart/Cotangent.lean` in the identity chart of `Kⁿ` with the coordinates
`ContinuousLinearEquiv.ulift`, here as an additive map `dlin : 𝒜_{Kⁿ,q} →+ (Fin n → K)` on the
presentation `(affine K n).presheaf.stalk q` of the stalk (the same type as
`(structureSheaf K Kⁿ Kⁿ).presheaf.stalk q`, on which the `K`-algebra structure and `linearPart`
live; `dlin_eq_linearPart` is `rfl`). The differential identifies `𝔪_q/𝔪_q²` with the dual of
`Kⁿ`, and germs of `𝔪_q` are part of a regular system of parameters iff their differentials are
linearly independent (`Hironaka/AnalyticSpace/RegularParameters.lean`); the statements about `dlin`
alone are proved here.

* `taylorAt K n q`: the Taylor homomorphism of `𝒜_{Kⁿ,q}` in the identity chart of `Kⁿ` with the
  coordinates `ContinuousLinearEquiv.ulift`;
* `dlin K n q`: the differential, `s ↦ (coeff (X_i) (T_q s))_i`; `dlin_eq_linearPart`;
* `dlin_coordAt_sub`: the normalisation `d_q (z_i − q_i) = e_i`, so `dlin` is *the* coordinate
  differential and not one up to `GL_n(K)`;
* `dlin_constAt`, `dlin_const_mul`, `dlin_eq_zero_iff_mem_maximalIdeal_sq`,
  `exists_mem_maximalIdeal_dlin_eq`,
  `linearIndependent_dlin_germ_iff_hasIndependentDifferentialsAt`: the differential of a constant
  vanishes, `dlin` is `K`-linear, a germ of `𝔪_q` has zero differential iff it lies in `𝔪_q²`
  (Hadamard's lemma), every functional is a differential, and the linear independence of the
  differentials of germs of analytic functions is the independence of their derivatives
  (`HasIndependentDifferentialsAt`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

variable (K : Type) [RCLike K] (n : ℕ)

/-- The Taylor homomorphism `T_q : 𝒜_{Kⁿ,q} →+* K[[X₁, …, Xₙ]]` in the identity chart of `Kⁿ`,
with the coordinates `ContinuousLinearEquiv.ulift : Kⁿ ≃L[K] (Fin n → K)`. -/
def taylorAt (q : Kn.{u} K n) :
    (affine K n).toLocallyRingedSpace.presheaf.stalk q →+* MvPowerSeries (Fin n) K :=
  taylorHom (Kn.{u} K n) ContinuousLinearEquiv.ulift (chartAt (Kn.{u} K n) q)
    (mem_chart_source _ q) (IsManifold.chart_mem_maximalAtlas q)

theorem taylorAt_apply (q : Kn.{u} K n) (s : (affine K n).toLocallyRingedSpace.presheaf.stalk q) :
    taylorAt K n q s =
      taylorHom (Kn.{u} K n) ContinuousLinearEquiv.ulift (chartAt (Kn.{u} K n) q)
        (mem_chart_source _ q) (IsManifold.chart_mem_maximalAtlas q) s :=
  rfl

/-- The **differential** of a germ at `q`, the linear part of its Taylor series: the vector of the
coefficients of `X₁, …, Xₙ` in `T_q s`, i.e. `(∂_i s (q))_i`. It is `linearPart` in the identity
chart of `Kⁿ` (`dlin_eq_linearPart`). -/
def dlin (q : Kn.{u} K n) : (affine K n).toLocallyRingedSpace.presheaf.stalk q →+ (Fin n → K) where
  toFun s i := MvPowerSeries.coeff (Finsupp.single i 1) (taylorAt K n q s)
  map_zero' := by
    funext i
    simp only [map_zero]
    rfl
  map_add' s t := by
    funext i
    simp only [map_add]
    rfl

theorem dlin_apply (q : Kn.{u} K n) (s : (affine K n).toLocallyRingedSpace.presheaf.stalk q)
    (i : Fin n) : dlin K n q s i = MvPowerSeries.coeff (Finsupp.single i 1) (taylorAt K n q s) :=
  rfl

/-- `dlin` is the `K`-linear `linearPart` of `Hironaka/Manifold/Chart/Cotangent.lean` in the
identity chart of `Kⁿ` with the coordinates `ContinuousLinearEquiv.ulift`, definitionally. -/
theorem dlin_eq_linearPart (q : Kn.{u} K n)
    (s : (affine K n).toLocallyRingedSpace.presheaf.stalk q) :
    dlin K n q s =
      linearPart (Kn.{u} K n) ContinuousLinearEquiv.ulift (chartAt (Kn.{u} K n) q)
        (IsManifold.chart_mem_maximalAtlas q) (mem_chart_source _ q) s :=
  rfl

/-- The constants of `𝒜_{Kⁿ,q}` given by the `K`-structure (`constAt`) are the constant germs
`const`. -/
theorem constAt_affine_eq (q : Kn.{u} K n) (c : K) :
    KLocallyRingedSpace.constAt (affine K n) q c = const K (Kn.{u} K n) (Kn.{u} K n) q c :=
  rfl

/-- The normalisation: the differential of the centred coordinate germ `z_i − q_i` is the `i`-th
standard basis vector — `dlin` is *the* coordinate differential `(∂_i s (q))_i`. -/
theorem dlin_coordAt_sub (q : Kn.{u} K n) (i : Fin n) :
    dlin K n q (coordAt K n q i - const K (Kn.{u} K n) (Kn.{u} K n) q (q.down i)) =
      Pi.single i 1 := by
  have h := taylorHom_coord_sub (Kn.{u} K n) ContinuousLinearEquiv.ulift (chartAt (Kn.{u} K n) q)
    (mem_chart_source _ q) (IsManifold.chart_mem_maximalAtlas q) i
  rw [eval_coordAt] at h
  funext j
  rw [dlin_apply, taylorAt_apply, h, MvPowerSeries.coeff_X, Pi.single_apply]
  by_cases hji : j = i
  · subst hji; simp
  · simp [hji, Finsupp.single_eq_single_iff]

/-- The differential of a constant vanishes. -/
theorem dlin_constAt (q : Kn.{u} K n) (c : K) :
    dlin K n q (KLocallyRingedSpace.constAt (affine K n) q c) = 0 := by
  rw [dlin_eq_linearPart, constAt_affine_eq]
  exact linearPart_const _ _ _ _ _ c

/-- The differential is `K`-linear: it scales with the constant germs `const`. -/
theorem dlin_const_mul' (q : Kn.{u} K n) (c : K)
    (s : (structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.stalk q) :
    dlin K n q (const K (Kn.{u} K n) (Kn.{u} K n) q c * s) = c • dlin K n q s := by
  rw [dlin_eq_linearPart, dlin_eq_linearPart, ← algebraMap_stalk_eq, ← Algebra.smul_def, map_smul]

/-- The differential is `K`-linear: it scales with the constants `constAt` of the
`K`-structure. -/
theorem dlin_const_mul (q : Kn.{u} K n) (c : K)
    (s : (affine K n).toLocallyRingedSpace.presheaf.stalk q) :
    dlin K n q (KLocallyRingedSpace.constAt (affine K n) q c * s) = c • dlin K n q s :=
  dlin_const_mul' K n q c s

/-- A germ of `𝔪_q` has zero differential iff it lies in `𝔪_q²` (Hadamard's lemma). -/
theorem dlin_eq_zero_iff_mem_maximalIdeal_sq (q : Kn.{u} K n)
    {s : (affine K n).toLocallyRingedSpace.presheaf.stalk q}
    (hs : s ∈ IsLocalRing.maximalIdeal ((affine K n).toLocallyRingedSpace.presheaf.stalk q)) :
    dlin K n q s = 0 ↔
      s ∈ IsLocalRing.maximalIdeal ((affine K n).toLocallyRingedSpace.presheaf.stalk q) ^ 2 := by
  rw [dlin_eq_linearPart]
  exact ⟨fun h => mem_sq_of_linearPart_eq_zero _ _ _ _ _ hs h,
    fun h => linearPart_eq_zero_of_mem_sq _ _ _ _ _ h⟩

/-- Every functional on `Kⁿ` is the differential of a germ vanishing at `q` — the differential is
onto: `v = d_q (∑ v_i (z_i − q_i))`. -/
theorem exists_mem_maximalIdeal_dlin_eq (q : Kn.{u} K n) (v : Fin n → K) :
    ∃ s ∈ IsLocalRing.maximalIdeal ((affine K n).toLocallyRingedSpace.presheaf.stalk q),
      dlin K n q s = v := by
  refine ⟨∑ i, const K (Kn.{u} K n) (Kn.{u} K n) q (v i) *
    (coordAt K n q i - const K (Kn.{u} K n) (Kn.{u} K n) q (q.down i)), ?_, ?_⟩
  · refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
    have h := coord_sub_mem_maximalIdeal (Kn.{u} K n) ContinuousLinearEquiv.ulift
      (chartAt (Kn.{u} K n) q) (mem_chart_source _ q) (IsManifold.chart_mem_maximalAtlas q) i
    rwa [eval_coordAt] at h
  · rw [map_sum]
    simp only [dlin_const_mul', dlin_coordAt_sub]
    funext j
    simp [Finset.sum_apply, Pi.single_apply]

/-- For germs of analytic functions on an open `U ⊆ Kⁿ`, the linear independence of the
differentials is the independence of the derivatives of the functions
(`HasIndependentDifferentialsAt`, in terms of `mfderiv`). -/
theorem linearIndependent_dlin_germ_iff_hasIndependentDifferentialsAt (U : Opens (Kn.{u} K n))
    {c : ℕ} (g : Fin c → AnalyticFun K n U) (q : Kn.{u} K n) (hq : q ∈ U) :
    LinearIndependent K (fun i => dlin K n q
        ((affine K n).toLocallyRingedSpace.presheaf.germ U q hq (g i))) ↔
      HasIndependentDifferentialsAt (Kn.{u} K n)
        (fun i => extendSection K (Kn.{u} K n) (g i)) q := by
  rw [hasIndependentDifferentialsAt_iff_linearIndependent_cotangentClass' (Kn.{u} K n) hq g,
    linearIndependent_cotangentClass_iff_linearPart (Kn.{u} K n) ContinuousLinearEquiv.ulift
      (chartAt (Kn.{u} K n) q) (IsManifold.chart_mem_maximalAtlas q) (mem_chart_source _ q)]
  exact Iff.rfl

end AnalyticSpace
