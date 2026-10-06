/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.ConvSeries.ConvNorm
import Hironaka.Analytic.ConvSeries.Bridge
import Hironaka.Analytic.ConvSeries.Mul
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Tactic.Positivity.Finset

/-!
# `Conv K m` is a domain, and its units are the series with nonzero constant term

`Conv K m` is a subalgebra of `MvPowerSeries (Fin m) K`, which has no zero divisors, so it is a
domain. A convergent series `f` with `a_0 ≠ 0` is a unit of `Conv K m`: its function is analytic
near `0` with nonzero value `a_0`, so `1 / evalSeries f` is analytic near `0` and, by
`Bridge.lean`, is the function of a convergent series `c`; the function of `f c` is then `1` near
`0` (multiplicativity of evaluation), so `f c = 1` by uniqueness of coefficients. Conversely a
unit of `Conv K m` is a unit of the formal power series ring, whose constant term is a unit
(`MvPowerSeries.isUnit_iff_constantCoeff`). Standard [GR71, Kapitel I], where the inverse is
constructed through the majorant norms; here it comes from Mathlib's `AnalyticAt.inv`. These are
the basic ring-theoretic facts about the local ring of germs that the Weierstrass theory and the
germ theory use throughout.


-/

public section

open scoped ENNReal NNReal Topology
open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {m : ℕ}

/-- A convergent series is a unit of `Conv K m` iff its constant coefficient is nonzero. -/
theorem isUnit_iff_constantCoeff_ne_zero {f : MvPowerSeries (Fin m) K} (hf : f ∈ Conv K m) :
    IsUnit (⟨f, hf⟩ : Conv K m) ↔ constantCoeff f ≠ 0 := by
  constructor
  · intro hu
    have hfu : IsUnit f := hu.map (Conv K m).val
    exact isUnit_iff_ne_zero.mp (MvPowerSeries.isUnit_iff_constantCoeff.mp hfu)
  · intro h0
    have hf' := hf
    obtain ⟨ρ, hρ⟩ := hf'
    have hρ' : ConvNorm ρ f ≠ ⊤ := hρ
    obtain ⟨r, hr0, hr⟩ := ρ.exists_le
    have han : AnalyticAt K (evalSeries f) 0 :=
      (hasFPowerSeriesOnBall_evalSeries hρ' hr0 hr).analyticAt
    have hval : evalSeries f 0 ≠ 0 := by rw [evalSeries_zero_eq]; exact h0
    obtain ⟨ρ', c, hc, hce⟩ := AnalyticAt.exists_conv_coeff (han.inv hval)
    have hcConv : c ∈ Conv K m := ⟨ρ', hc⟩
    have hfc : f * c ∈ Conv K m := mul_mem hf hcConv
    -- the function of `f c` is `1` near `0`
    have hev : evalSeries (f * c) =ᶠ[𝓝 0] evalSeries (1 : MvPowerSeries (Fin m) K) := by
      have hne : ∀ᶠ x in 𝓝 (0 : Fin m → K), evalSeries f x ≠ 0 :=
        han.continuousAt.eventually_ne hval
      obtain ⟨r'', hr''0, hr''⟩ := (ρ.min ρ').exists_le
      have hnb : ∀ᶠ x in 𝓝 (0 : Fin m → K), ∀ k, ‖x k‖ < ((ρ.min ρ') k : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds (0 : Fin m → K)
          (show (0 : ℝ) < r'' by exact_mod_cast hr''0)] with x hx k
        exact (norm_le_pi_norm x k).trans_lt ((mem_ball_zero_iff.mp hx).trans_le
          (by exact_mod_cast hr'' k))
      filter_upwards [hne, hnb] with x hx0 hxk
      have hxρ' : ∀ k, ‖x k‖ < ρ' k := fun k =>
        (hxk k).trans_le (by exact_mod_cast ρ.min_le_right ρ' k)
      rw [evalSeries_mul (ρ := ρ.min ρ') (BanachSeries.mono (ρ.min_le_left ρ') hρ)
        (BanachSeries.mono (ρ.min_le_right ρ') hc) (fun k => (hxk k).le), evalSeries_one,
        ← sub_eq_zero]
      have hcx := hce x hxρ'
      rw [zero_add, Pi.inv_apply] at hcx
      rw [← hcx, mul_inv_cancel₀ hx0, sub_self]
    have hmul : f * c = 1 := eq_of_evalSeries_eventuallyEq hfc (one_mem _) hev
    refine ⟨⟨⟨f, hf⟩, ⟨c, hcConv⟩, Subtype.ext hmul, Subtype.ext ?_⟩, rfl⟩
    change c * f = 1
    rw [mul_comm]
    exact hmul

end Analytic
