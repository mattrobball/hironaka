/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Order
public import Hironaka.Manifold.Germ.TaylorHom
public import Hironaka.Manifold.IdealSheaf.Defs
public import Mathlib.RingTheory.MvPowerSeries.Order
import Hironaka.Algebra.Local.PowerSeries
import Hironaka.Manifold.Germ.TaylorIdeal
import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Manifold.Sheaf.LocalRing
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Cosupport and order of an ideal sheaf on an analytic manifold

For a locally finitely generated ideal sheaf `J` of the structure sheaf of an analytic manifold:

* the cosupport `V(J)` is, on a generating open set `U`, the common zero set of the generators
  (`mem_cosupport_iff_forall_eq_zero`: a germ is a unit iff its value is nonzero) —
  Bierstone–Milman's `V(I) = {x : f(x) = 0 for all f ∈ I}` [BM97, Introduction];
* the order `ν_a(J)` [Hir64, p. 133] is read on the Taylor series in a chart: the order of a germ
  is the order of its Taylor series (`ordElem_eq_order_taylorHom`, through
  `taylorHom_mem_maximalIdeal_pow_iff`), `ν_a(J) = min_i ord T_a(f_i)` over local generators
  (`ord_eq_iInf_order_taylorHom`; the order of a function at a point in the sense of
  Bierstone–Milman [BM97, §3]), `ν_a(J) ≥ p` iff the Taylor coefficients of degree `< p` of the
  generators vanish (`le_ord_iff_forall_coeff_eq_zero`), and `ν_a(J) = ∞` iff `J_a = 0`
  (`ord_eq_top_iff`, the Taylor homomorphism being injective).

Also here: `modelCoord`, coordinates on the finite-dimensional model space, the chart coordinates
used whenever a statement is chart-free. The order is the invariant the order-reduction algorithm
lowers.
-/

@[expose] public section

open TopologicalSpace Opposite CategoryTheory Filter Analytic
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

namespace IdealSheaf

section Cosupport

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  (J : IdealSheaf (structureSheaf 𝕜 E M))

/-- On a generating open set, `V(J) ∩ U` is the common zero set of the generators
([BM97, Introduction]): a germ is a unit iff its value is nonzero. -/
theorem mem_support_iff_forall_eq_zero {U : Opens M} {k : ℕ}
    {f : Fin k → (structureSheaf 𝕜 E M).presheaf.obj (op U)}
    (hgen : ∀ b (hb : b ∈ U), J.stalkIdeal b =
      Ideal.span (Set.range fun i => (structureSheaf 𝕜 E M).presheaf.germ U b hb (f i)))
    {a : M} (ha : a ∈ U) : a ∈ J.support ↔ ∀ i, f i ⟨a, ha⟩ = 0 := by
  rw [mem_support, Ne, J.stalkIdeal_eq_top_iff_exists_isUnit ha (hgen a ha), not_exists]
  refine forall_congr' fun i => ?_
  have hu : IsUnit ((structureSheaf 𝕜 E M).presheaf.germ U a ha (f i)) ↔
      eval 𝕜 E M a ((structureSheaf 𝕜 E M).presheaf.germ U a ha (f i)) ≠ 0 :=
    contMDiffSheafCommRing.isUnit_stalk_iff 𝓘(𝕜, E) ω M _
  have he : eval 𝕜 E M a ((structureSheaf 𝕜 E M).presheaf.germ U a ha (f i)) = f i ⟨a, ha⟩ :=
    contMDiffSheafCommRing.eval_germ 𝓘(𝕜, E) 𝓘(𝕜) ω M 𝕜 U a ha (f i)
  rw [hu, not_not, he]

end Cosupport

section Order

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))
  (φ : OpenPartialHomeomorph M E) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M} (ha : a ∈ φ.source)

/-- The order of a germ is the order of its Taylor series. -/
theorem ordElem_eq_order_taylorHom (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    IsLocalRing.ordElem s = (taylorHom E ψ φ ha hφ s).order := by
  rw [← MvPowerSeries.ordElem_eq_order]
  refine le_antisymm ?_ ?_ <;> rw [← ENat.forall_natCast_le_iff_le] <;> intro r hr <;>
    rw [← IsLocalRing.mem_maximalIdeal_pow_iff_le_ordElem] at hr ⊢
  · exact (taylorHom_mem_maximalIdeal_pow_iff E ψ φ ha hφ s r).mpr hr
  · exact (taylorHom_mem_maximalIdeal_pow_iff E ψ φ ha hφ s r).mp hr

variable (J : IdealSheaf (structureSheaf 𝕜 E M))

/-- `ν_a(J) = min_i ord T_a(f_i)` for local generators [BM97, §3]. -/
theorem ord_eq_iInf_order_taylorHom {U : Opens M} (haU : a ∈ U) {k : ℕ}
    {f : Fin k → (structureSheaf 𝕜 E M).presheaf.obj (op U)}
    (hgen : ∀ b (hb : b ∈ U), J.stalkIdeal b =
      Ideal.span (Set.range fun i => (structureSheaf 𝕜 E M).presheaf.germ U b hb (f i))) :
    J.ord a = ⨅ i, (taylorHom E ψ φ ha hφ
      ((structureSheaf 𝕜 E M).presheaf.germ U a haU (f i))).order := by
  rw [ord, hgen a haU, IsLocalRing.ord_span, iInf_range]
  exact iInf_congr fun i => ordElem_eq_order_taylorHom ψ φ hφ ha _

/-- `ν_a(J) ≥ p` iff the Taylor coefficients of degree `< p` of the generators vanish. -/
theorem le_ord_iff_forall_coeff_eq_zero {U : Opens M} (haU : a ∈ U) {k : ℕ}
    {f : Fin k → (structureSheaf 𝕜 E M).presheaf.obj (op U)}
    (hgen : ∀ b (hb : b ∈ U), J.stalkIdeal b =
      Ideal.span (Set.range fun i => (structureSheaf 𝕜 E M).presheaf.germ U b hb (f i))) (p : ℕ) :
    (p : ℕ∞) ≤ J.ord a ↔ ∀ i (ν : Fin n →₀ ℕ), ν.degree < p →
      MvPowerSeries.coeff ν (taylorHom E ψ φ ha hφ
        ((structureSheaf 𝕜 E M).presheaf.germ U a haU (f i))) = 0 := by
  rw [J.ord_eq_iInf_order_taylorHom ψ φ hφ ha haU hgen, le_iInf_iff]
  refine forall_congr' fun i => ⟨fun h ν hν => MvPowerSeries.coeff_of_lt_order
    (lt_of_lt_of_le (by exact_mod_cast hν) h), fun h => MvPowerSeries.nat_le_order h⟩

end Order

section Semicontinuity

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] (J : IdealSheaf (structureSheaf 𝕜 E M))

/-- Coordinates on the finite-dimensional model space. -/
noncomputable def modelCoord : E ≃L[𝕜] (Fin (Module.finrank 𝕜 E) → 𝕜) :=
  (Module.finBasis 𝕜 E).equivFun.toContinuousLinearEquiv

/-- `ν_a(J) = ∞` iff `J_a = 0` (the Taylor homomorphism is injective). -/
theorem ord_eq_top_iff (a : M) : J.ord a = ⊤ ↔ J.stalkIdeal a = ⊥ := by
  refine ⟨fun h => ?_, J.ord_eq_top_of_stalkIdeal_eq_bot⟩
  rw [eq_bot_iff]
  intro s hs
  have h1 : IsLocalRing.ordElem s = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← h, ord, IsLocalRing.ord_eq_iInf]
    exact iInf₂_le s hs
  have hφ := IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := ω) a
  rw [ordElem_eq_order_taylorHom (modelCoord (𝕜 := 𝕜) (E := E)) (chartAt E a) hφ
    (mem_chart_source E a),
    MvPowerSeries.order_eq_top_iff] at h1
  exact (IsTaylorHom.injective' E _ _ (mem_chart_source E a) (isTaylorHom_taylorHom E _ _ _ hφ))
    (h1.trans (map_zero _).symm)

end Semicontinuity

end IdealSheaf

end Manifold
