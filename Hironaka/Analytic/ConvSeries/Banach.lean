/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.ConvNorm
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# `B_ρ` is a Banach algebra over `K = ℝ` or `ℂ`

The series of finite majorant norm `‖f‖_ρ = ∑_ν ‖a_ν‖ ρ^ν`, for a radius vector `ρ : Radius m`
with positive entries, form a normed algebra over `K` under the norm `‖f‖ = (‖f‖_ρ).toReal`
(subadditive, homogeneous and submultiplicative by the inequalities of `ConvNorm.lean`; definite
because every `ρ^ν` is positive), and it is complete: the weighted coefficient family
`ν ↦ a_ν ρ^ν` is a `K`-linear isometry onto the sequence space `ℓ¹(Fin m →₀ ℕ; K)`
(`lp (fun _ => K) 1`), which Mathlib knows to be complete. The real weights `ρ^ν` enter `K`
through `RCLike.ofReal`. These are the Banach algebras of [GR71, Kapitel I]; the Weierstrass
division theorem needs their completeness (the contraction `T q = Q f + Q (h q)` on `B_ρ` in
`Hironaka/Analytic/Weierstrass/Contraction.lean`), and the evaluation of series
(`Eval.lean`) uses their norm.


-/

@[expose] public section

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ} {ρ : Radius m}

theorem BanachSeries.convNorm_ne_top (f : BanachSeries K ρ) :
    ConvNorm ρ (f : MvPowerSeries (Fin m) K) ≠ ⊤ := f.2

/-- A series of zero `ρ`-norm is zero (every `ρ^ν` is positive). -/
theorem eq_zero_of_convNorm_eq_zero {f : MvPowerSeries (Fin m) K} (h : ConvNorm ρ f = 0) :
    f = 0 := by
  ext ν
  have hν := (ENNReal.tsum_eq_zero.mp h) ν
  rw [mul_eq_zero, enorm_eq_zero, ENNReal.coe_eq_zero] at hν
  rcases hν with h0 | h0
  · simpa using h0
  · exact absurd h0 (monomialEval_pos' ρ ν).ne'

/-- The norm of `B ρ`: the real value of the majorant norm. -/
noncomputable instance : NormedAddCommGroup (BanachSeries K ρ) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun f => (ConvNorm ρ (f : MvPowerSeries (Fin m) K)).toReal
      map_zero' := by simp [ConvNorm_zero]
      add_le' := fun f g => by
        rw [← ENNReal.toReal_add f.2 g.2]
        exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨f.2, g.2⟩) (ConvNorm_add_le _ _ _)
      neg' := fun f => by simp [ConvNorm_neg]
      eq_zero_of_map_eq_zero' := fun f hf => by
        have h0 : ConvNorm ρ (f : MvPowerSeries (Fin m) K) = 0 :=
          ((ENNReal.toReal_eq_zero_iff _).mp hf).resolve_right f.2
        exact Subtype.ext (eq_zero_of_convNorm_eq_zero h0) }

theorem BanachSeries.norm_def (f : BanachSeries K ρ) :
    ‖f‖ = (ConvNorm ρ (f : MvPowerSeries (Fin m) K)).toReal := rfl

/-- `B_ρ` is a normed ring, `‖f g‖ ≤ ‖f‖ ‖g‖`. -/
noncomputable instance : NormedRing (BanachSeries K ρ) :=
  { (inferInstance : NormedAddCommGroup (BanachSeries K ρ)),
    (inferInstance : Ring (BanachSeries K ρ)) with
    norm_mul_le := fun f g => by
      rw [BanachSeries.norm_def, BanachSeries.norm_def, BanachSeries.norm_def,
        ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top f.2 g.2) (ConvNorm_mul_le _ _ _) }

noncomputable instance : NormOneClass (BanachSeries K ρ) where
  norm_one := by rw [BanachSeries.norm_def]; simp [ConvNorm_one]

noncomputable instance : NormedAlgebra K (BanachSeries K ρ) where
  norm_smul_le c f := by
    rw [BanachSeries.norm_def, BanachSeries.norm_def, Subalgebra.coe_smul, ConvNorm_smul,
      ENNReal.toReal_mul, toReal_enorm]

/-! ## Completeness through `ℓ¹` -/

/-- The majorant norm as a sum of nonnegative reals coerced to `ℝ≥0∞`. -/
theorem convNorm_eq_tsum_coe (f : MvPowerSeries (Fin m) K) :
    ConvNorm ρ f = ∑' ν : Fin m →₀ ℕ, ((‖coeff ν f‖₊ * monomialEval ρ ν : ℝ≥0) : ℝ≥0∞) := by
  unfold ConvNorm
  refine tsum_congr fun ν => ?_
  rw [ENNReal.coe_mul, enorm_eq_nnnorm]

/-- The real weight `ρ^ν`, coerced into `K`, has norm `ρ^ν`. -/
theorem norm_coe_monomialEval (ρ : Fin m → ℝ≥0) (ν : Fin m →₀ ℕ) :
    ‖((monomialEval ρ ν : ℝ) : K)‖ = (monomialEval ρ ν : ℝ) := by
  rw [RCLike.norm_ofReal, NNReal.abs_eq]

theorem nnnorm_coe_monomialEval (ρ : Fin m → ℝ≥0) (ν : Fin m →₀ ℕ) :
    ‖((monomialEval ρ ν : ℝ) : K)‖₊ = monomialEval ρ ν :=
  NNReal.eq (by rw [coe_nnnorm, norm_coe_monomialEval])

theorem coe_monomialEval_ne_zero (ρ : Radius m) (ν : Fin m →₀ ℕ) :
    ((monomialEval ρ ν : ℝ) : K) ≠ 0 := by
  exact_mod_cast (NNReal.coe_pos.mpr (monomialEval_pos' ρ ν)).ne'

/-- The weighted coefficient family `ν ↦ a_ν ρ^ν` of a series of finite norm is summable. -/
theorem BanachSeries.summable_weighted (f : BanachSeries K ρ) :
    Summable fun ν : Fin m →₀ ℕ =>
      ‖coeff ν (f : MvPowerSeries (Fin m) K) * ((monomialEval ρ ν : ℝ) : K)‖ := by
  have hf : ConvNorm ρ (f : MvPowerSeries (Fin m) K) ≠ ⊤ := f.2
  rw [convNorm_eq_tsum_coe] at hf
  have h := NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hf)
  convert h using 1
  funext ν
  rw [NNReal.coe_mul, coe_nnnorm, norm_mul, norm_coe_monomialEval]

/-- The weighted coefficient family, as an element of `ℓ¹`. -/
noncomputable def BanachSeries.toLp (f : BanachSeries K ρ) : lp (fun _ : Fin m →₀ ℕ => K) 1 :=
  ⟨fun ν => coeff ν (f : MvPowerSeries (Fin m) K) * ((monomialEval ρ ν : ℝ) : K),
    (memℓp_gen_iff (by simp)).mpr (by simpa using BanachSeries.summable_weighted f)⟩

theorem BanachSeries.toLp_apply (f : BanachSeries K ρ) (ν : Fin m →₀ ℕ) :
    BanachSeries.toLp f ν = coeff ν (f : MvPowerSeries (Fin m) K) * ((monomialEval ρ ν : ℝ) : K) :=
  rfl

theorem BanachSeries.norm_toLp (f : BanachSeries K ρ) : ‖BanachSeries.toLp f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp) (BanachSeries.toLp f), BanachSeries.norm_def]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one, BanachSeries.toLp_apply]
  unfold ConvNorm
  rw [ENNReal.tsum_toReal_eq fun _ => ENNReal.mul_ne_top enorm_ne_top ENNReal.coe_ne_top]
  refine tsum_congr fun ν => ?_
  rw [ENNReal.toReal_mul, toReal_enorm, ENNReal.coe_toReal, norm_mul, norm_coe_monomialEval]

variable (K) in
/-- The series with coefficients `g ν / ρ^ν` attached to an `ℓ¹` family `g`. -/
noncomputable def ofLpSeries (ρ : Radius m) (g : lp (fun _ : Fin m →₀ ℕ => K) 1) :
    MvPowerSeries (Fin m) K :=
  fun ν => (g ν : K) / ((monomialEval ρ ν : ℝ) : K)

theorem coeff_ofLpSeries (g : lp (fun _ : Fin m →₀ ℕ => K) 1) (ν : Fin m →₀ ℕ) :
    coeff ν (ofLpSeries K ρ g) = (g ν : K) / ((monomialEval ρ ν : ℝ) : K) := rfl

/-- The inverse: an `ℓ¹` family `g` gives a series of finite `ρ`-norm, namely `‖g‖₁`. -/
theorem convNorm_ofLpSeries_ne_top (g : lp (fun _ : Fin m →₀ ℕ => K) 1) :
    ConvNorm ρ (ofLpSeries K ρ g) ≠ ⊤ := by
  have h1 : Summable fun ν : Fin m →₀ ℕ => ‖(g ν : K)‖ := by
    simpa using (memℓp_gen_iff (p := 1) (by simp)).mp (lp.memℓp g)
  have hsum : Summable fun ν : Fin m →₀ ℕ => ‖(g ν : K)‖₊ :=
    NNReal.summable_coe.mp (by simpa [coe_nnnorm] using h1)
  have h : (∑' ν : Fin m →₀ ℕ, ((‖(g ν : K)‖₊ : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr hsum
  rw [convNorm_eq_tsum_coe]
  refine ne_of_eq_of_ne (tsum_congr fun ν => ?_) h
  rw [coeff_ofLpSeries]
  congr 1
  rw [nnnorm_div, nnnorm_coe_monomialEval, div_mul_cancel₀ _ (monomialEval_pos' ρ ν).ne']

/-- The series with coefficients `g ν / ρ^ν`, in `B ρ`. -/
noncomputable def BanachSeries.ofLp (g : lp (fun _ : Fin m →₀ ℕ => K) 1) : BanachSeries K ρ :=
  ⟨ofLpSeries K ρ g, convNorm_ofLpSeries_ne_top g⟩

/-- `B_ρ` is isometric to `ℓ¹(Fin m →₀ ℕ; K)` through the weighted coefficients. -/
noncomputable def BanachSeries.toLpEquiv :
    BanachSeries K ρ ≃ₗᵢ[K] lp (fun _ : Fin m →₀ ℕ => K) 1 where
  toFun := BanachSeries.toLp
  invFun := BanachSeries.ofLp
  left_inv f := by
    refine Subtype.ext (MvPowerSeries.ext fun ν => ?_)
    change coeff ν (ofLpSeries K ρ (BanachSeries.toLp f)) = coeff ν (f : MvPowerSeries (Fin m) K)
    rw [coeff_ofLpSeries, BanachSeries.toLp_apply,
      mul_div_cancel_right₀ _ (coe_monomialEval_ne_zero ρ ν)]
  right_inv g := by
    ext ν
    change coeff ν (ofLpSeries K ρ g) * ((monomialEval ρ ν : ℝ) : K) = (g ν : K)
    rw [coeff_ofLpSeries, div_mul_cancel₀ _ (coe_monomialEval_ne_zero ρ ν)]
  map_add' f g := by
    ext ν
    change coeff ν ((f : MvPowerSeries (Fin m) K) + (g : MvPowerSeries (Fin m) K))
        * ((monomialEval ρ ν : ℝ) : K) = _
    rw [map_add, add_mul]
    rfl
  map_smul' c f := by
    ext ν
    change coeff ν (c • (f : MvPowerSeries (Fin m) K)) * ((monomialEval ρ ν : ℝ) : K) = _
    rw [MvPowerSeries.coeff_smul, mul_assoc]
    rfl
  norm_map' := BanachSeries.norm_toLp

/-- `B_ρ` is complete (a Banach algebra), by the isometry with `ℓ¹`. -/
instance : CompleteSpace (BanachSeries K ρ) :=
  (BanachSeries.toLpEquiv (K := K) (ρ := ρ)).toIsometryEquiv.completeSpace_iff.mpr inferInstance

variable (K)

/-- The normed-ring structure of `B_ρ`, as a named declaration (the instance above). -/
noncomputable abbrev banachSeries_normedRing (ρ : Radius m) : NormedRing (BanachSeries K ρ) :=
  inferInstance

end Analytic

/-! ### The real case -/

open scoped ENNReal NNReal
open MvPowerSeries

namespace Analytic

variable {m : ℕ} {ρ : Radius m}

/-- `B ρ` is complete, as a named declaration. -/
theorem banachSeries_completeSpace (ρ : Radius m) : CompleteSpace (BanachSeries ℝ ρ) :=
  inferInstance

end Analytic
