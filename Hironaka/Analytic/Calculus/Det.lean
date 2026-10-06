/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The determinant of continuous linear maps is analytic; the Jacobian determinant of an analytic map

Calculus shared by the analytic strands: the determinant is a polynomial on `E →L[𝕜] E`
(`contDiff_det`), so `x ↦ det (DF x)` is `C^ω` on an open set on which `F` is `C^ω`
(`contDiffOn_det_fderiv`) and analytic on an open set on which `F` is analytic
(`analyticOnNhd_det_fderiv`, through `AnalyticOnNhd.contDiffOn_of_completeSpace`,
`ContDiffOn.analyticOn` and `IsOpen.analyticOn_iff_analyticOnNhd`). Multiplicativity of the
determinant of continuous linear maps (`det_clm_comp`) sits beside them. Not in the sources as
such: it is what makes the Jacobian of a blowing-up an analytic function and its zero set a
divisor, as in the remark after [BM97, Theorem 1.10] ("if `J ⊆ 𝒪_{M_k}` denotes the ideal generated
by the Jacobian determinant of `π`, then `J · π⁻¹(I)` is a normal-crossings divisor"). Used by the
Jacobian computations of the analytic manifolds (`Hironaka/Manifold/Jacobian`).
-/

public section

open scoped ContDiff

namespace Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- The determinant of a composite of continuous linear maps is the product of the determinants
(Mathlib's `LinearMap.det_comp` through the coercion `E →L[𝕜] E → E →ₗ[𝕜] E`). -/
theorem det_clm_comp (A B : E →L[𝕜] E) : (A.comp B).det = A.det * B.det :=
  LinearMap.det_comp (A : E →ₗ[𝕜] E) (B : E →ₗ[𝕜] E)

variable [CompleteSpace 𝕜]

/-- **The determinant is analytic on `E →L[𝕜] E`.** With a finite basis `b`,
`det L = det (toMatrix b b L)` is a polynomial (Leibniz's formula) in the entries
`b.repr (L (b j)) i`, continuous linear functions of `L`; without one, `det = 1`. -/
theorem contDiff_det {n : WithTop ℕ∞} : ContDiff 𝕜 n fun L : E →L[𝕜] E => L.det := by
  classical
  by_cases hfin : Module.Finite 𝕜 E
  · let b := Module.finBasis 𝕜 E
    have hdet : (fun L : E →L[𝕜] E => L.det) =
        fun L : E →L[𝕜] E => (LinearMap.toMatrix b b (L : E →ₗ[𝕜] E)).det :=
      funext fun L => (LinearMap.det_toMatrix b _).symm
    rw [hdet]
    simp only [Matrix.det_apply']
    refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
    have hentry : (fun L : E →L[𝕜] E => LinearMap.toMatrix b b (L : E →ₗ[𝕜] E) (σ i) i) =
        (LinearMap.toContinuousLinearMap (b.coord (σ i))) ∘
          (ContinuousLinearMap.apply 𝕜 E (b i)) := by
      funext L
      simp [LinearMap.toMatrix_apply, Module.Basis.coord_apply]
    rw [hentry]
    exact (LinearMap.toContinuousLinearMap (b.coord (σ i))).contDiff.comp
      (ContinuousLinearMap.apply 𝕜 E (b i)).contDiff
  · have hone : (fun L : E →L[𝕜] E => L.det) = fun _ => 1 :=
      funext fun L => LinearMap.det_eq_one_of_not_module_finite hfin _
    rw [hone]
    exact contDiff_const

/-- **`x ↦ det (DF x)` is `C^ω` on an open set on which `F` is `C^ω`**
(`ContDiffOn.fderiv_of_isOpen` with `ω + 1 = ω`, then `contDiff_det`). -/
theorem contDiffOn_det_fderiv {F : E → E} {s : Set E} (hF : ContDiffOn 𝕜 ω F s) (hs : IsOpen s) :
    ContDiffOn 𝕜 ω (fun x => (fderiv 𝕜 F x).det) s :=
  contDiff_det.comp_contDiffOn (hF.fderiv_of_isOpen hs le_top)

/-- The Jacobian determinant of an analytic map is analytic on an open set: analytic is `C^ω`
(`AnalyticOnNhd.contDiffOn_of_completeSpace`), `C^ω` on an open set is analytic
(`ContDiffOn.analyticOn`, `IsOpen.analyticOn_iff_analyticOnNhd`). -/
theorem analyticOnNhd_det_fderiv [CompleteSpace E] {F : E → E} {V : Set E} (hV : IsOpen V)
    (hF : AnalyticOnNhd 𝕜 F V) : AnalyticOnNhd 𝕜 (fun x => (fderiv 𝕜 F x).det) V :=
  hV.analyticOn_iff_analyticOnNhd.mp
    (contDiffOn_det_fderiv hF.contDiffOn_of_completeSpace hV).analyticOn

end Analytic
