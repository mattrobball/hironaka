/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.RealPlane
public import Hironaka.Manifold.FiniteSuccession.Restrict.CenterComponents
public import Hironaka.Manifold.StructureSheaf
public import Mathlib.Analysis.InnerProductSpace.Basic
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.IdealSheaf.Identity
import Hironaka.Resolution.Analytic.Wlo09.Clauses
import HironakaExamples.Local.SingularQuotient
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `V(x² + y²) ⊆ ℝ²` has support the origin and no simple point

The standard example `x² + y²` of the phenomenon Hironaka remarks on [Hir64, Introduction], a
reduced real-analytic space whose simple locus is not dense: the closed subspace
`X = V(x² + y²)` of the real plane (reduced, since `x² + y²` is irreducible in `ℝ{x, y}` and
the quotient `𝒪_{ℝ²,0} / (x² + y²)` is therefore a domain: `circleSpace_isReduced` of
`HironakaExamples/Space/CircleReduced.lean`, for the analytic space of the same equation) has the
single real point `0`, and `0` is not a simple point — the stalk `𝒪_{ℝ²,0} / (x² + y²)` is not
regular, since
`x² + y²` is a nonzero element of `𝔪_0²` of the regular local ring `𝒪_{ℝ²,0}`
(`Hironaka.Local.not_isRegularLocalRing_quotient_span_singleton`, [Sta, Tag 00NR]). So
`X.regularLocus = ∅` with `X ≠ ∅`, and the lift of the simple locus is empty; this is why the
resolution of real-analytic spaces (`AnalyticSpace.exists_functorial_resolution`) asserts only that
the image of the resolution is the closure of the simple locus.

* the coordinate germs of the identity chart at a point of the plane, their values and the germ
  of `x² + y²` (`germ_circleSection`, `extendSection_circleSection`);
* `circleIdeal_cosupport_eq_singleton`: `|X| = {0}` (`x² + y² = 0` iff `x = y = 0` over `ℝ`);
* `circleIdeal_regSet_eq_empty`: no simple point — the stalk of `X` at its only point is
  `𝒪_{ℝ²,0} / (x² + y²)` (`mem_reg_toAnalyticSpace_iff`), `x² + y² ∈ 𝔪_0²`, and `x² + y²` does
  not vanish identically near `0` (its value at `(t, t)` is `2 t²`; the identity lemma
  `germ_eq_zero_iff`).
-/

public section

open Set TopologicalSpace Opposite CategoryTheory Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.Manifold

open _root_.Manifold

/-! ### The plane's coordinate germs at a point -/

/-- Every point of the plane lies in the source of the identity chart (the form `rw` needs). -/
theorem mem_chartAt_source_plane (x : realPlane) :
    x ∈ (chartAt (Fin 2 → ℝ) (0 : realPlane)).source :=
  mem_planeChart x

/-- The germ at `x` of the `i`-th coordinate section is the coordinate germ of the identity chart
(`coord`). -/
theorem germ_planeCoordSection (x : realPlane) (i : Fin 2) :
    (structureSheaf ℝ (Fin 2 → ℝ) realPlane).presheaf.germ planeChart x (mem_planeChart x)
        (planeCoordSection i) =
      coord (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
        (chartAt (Fin 2 → ℝ) (0 : realPlane)) (IsManifold.chart_mem_maximalAtlas (0 : realPlane))
        (mem_chartAt_source_plane x) i :=
  rfl

/-- The value at `x` of the `i`-th coordinate germ is `x i`. -/
theorem eval_coord_plane (x : realPlane) (i : Fin 2) :
    Manifold.eval ℝ (Fin 2 → ℝ) realPlane x
      (coord (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
        (chartAt (Fin 2 → ℝ) (0 : realPlane)) (IsManifold.chart_mem_maximalAtlas (0 : realPlane))
        (mem_chartAt_source_plane x) i) = x i := by
  rw [eval_coord]
  rfl

/-- The germ of `x² + y²` at `x` in the coordinate germs. -/
theorem germ_circleSection (x : realPlane) :
    (structureSheaf ℝ (Fin 2 → ℝ) realPlane).presheaf.germ planeChart x (mem_planeChart x)
        circleSection =
      coord (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
        (chartAt (Fin 2 → ℝ) (0 : realPlane)) (IsManifold.chart_mem_maximalAtlas (0 : realPlane))
        (mem_chartAt_source_plane x) 0 ^ 2 +
      coord (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
        (chartAt (Fin 2 → ℝ) (0 : realPlane)) (IsManifold.chart_mem_maximalAtlas (0 : realPlane))
        (mem_chartAt_source_plane x) 1 ^ 2 := by
  rw [circleSection, map_add, map_pow, map_pow, germ_planeCoordSection, germ_planeCoordSection]

/-- The value of `x² + y²` at a point `p` of the plane is `p 0 ^ 2 + p 1 ^ 2`. -/
theorem extendSection_circleSection (p : realPlane) :
    extendSection ℝ (Fin 2 → ℝ) circleSection p = p 0 ^ 2 + p 1 ^ 2 := by
  rw [← eval_germ' planeChart (mem_planeChart p) circleSection, germ_circleSection, map_add,
    map_pow, map_pow, eval_coord_plane, eval_coord_plane]

/-! ### `V(x² + y²)`: the support and the simple points -/

/-- The support of `V(x² + y²) ⊆ ℝ²` is the origin ([Hir64, Introduction]). -/
theorem circleIdeal_cosupport_eq_singleton : circleIdeal.support = {0} := by
  ext x
  rw [IdealSheaf.mem_support, stalkIdeal_circleIdeal, Ne, Ideal.span_singleton_eq_top,
    Set.mem_singleton_iff, germ_circleSection, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
    mem_maximalIdeal_iff_eval, map_add, map_pow, map_pow, eval_coord_plane, eval_coord_plane]
  constructor
  · intro h
    have h0 := (add_eq_zero_iff_of_nonneg (sq_nonneg (x 0)) (sq_nonneg (x 1))).mp h
    funext i
    fin_cases i
    · exact pow_eq_zero_iff two_ne_zero |>.mp h0.1
    · exact pow_eq_zero_iff two_ne_zero |>.mp h0.2
  · rintro rfl
    change (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 0
    norm_num

/-- The coordinate germs at the origin lie in the maximal ideal. -/
theorem coord_plane_mem_maximalIdeal (i : Fin 2) :
    coord (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
        (chartAt (Fin 2 → ℝ) (0 : realPlane)) (IsManifold.chart_mem_maximalAtlas (0 : realPlane))
        (mem_chartAt_source_plane 0) i ∈
      IsLocalRing.maximalIdeal ((structureSheaf ℝ (Fin 2 → ℝ) realPlane).presheaf.stalk 0) := by
  rw [mem_maximalIdeal_iff_eval, eval_coord_plane]
  rfl

/-- `x² + y²` does not vanish identically near the origin: its value at `(t, t)` is `2 t²`
(the identity lemma `germ_eq_zero_iff`). -/
theorem germ_circleSection_ne_zero :
    (structureSheaf ℝ (Fin 2 → ℝ) realPlane).presheaf.germ planeChart 0 (mem_planeChart 0)
      circleSection ≠ 0 := by
  rw [Ne, IdealSheaf.germ_eq_zero_iff]
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  have hp : dist (fun _ : Fin 2 => ε / 2) (0 : Fin 2 → ℝ) < ε := by
    rw [dist_pi_lt_iff hε]
    intro b
    rw [Pi.zero_apply, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have h0 := hball hp
  rw [extendSection_circleSection, Pi.zero_apply] at h0
  have hpos : (0 : ℝ) < (ε / 2) ^ 2 + (ε / 2) ^ 2 := by positivity
  exact hpos.ne' h0

/-- At a point of the support of `x² + y²` (the origin), `𝒪_{ℝ²,0}/(x² + y²)` is not a regular
local ring: `x² + y²` is a nonzero element of the square of the maximal ideal. -/
theorem not_isRegularLocalRing_stalk_circleIdeal {x : realPlane} (hx : x ∈ circleIdeal.support) :
    ¬ IsRegularLocalRing ((structureSheaf ℝ (Fin 2 → ℝ) realPlane).presheaf.stalk x ⧸
      circleIdeal.stalkIdeal x) := by
  rw [circleIdeal_cosupport_eq_singleton, Set.mem_singleton_iff] at hx
  subst hx
  intro hreg'
  rw [stalkIdeal_circleIdeal, germ_circleSection] at hreg'
  have : IsRegularLocalRing ((structureSheaf ℝ (Fin 2 → ℝ) realPlane).presheaf.stalk 0) :=
    isRegularLocalRing_stalk_of_chart (Fin 2 → ℝ) (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
      (chartAt (Fin 2 → ℝ) (0 : realPlane)) (mem_chartAt_source_plane 0)
      (IsManifold.chart_mem_maximalAtlas (0 : realPlane))
  have : IsDomain ((structureSheaf ℝ (Fin 2 → ℝ) realPlane).presheaf.stalk 0) :=
    isDomain_stalk (ContinuousLinearEquiv.refl ℝ (Fin 2 → ℝ))
      (IsManifold.chart_mem_maximalAtlas (0 : realPlane)) (mem_chartAt_source_plane 0)
  refine Hironaka.Local.not_isRegularLocalRing_quotient_span_singleton ?_ ?_ hreg'
  · refine mem_nonZeroDivisors_of_ne_zero ?_
    rw [← germ_circleSection]
    exact germ_circleSection_ne_zero
  · simp only [pow_two]
    exact Ideal.add_mem _
      (Ideal.mul_mem_mul (coord_plane_mem_maximalIdeal 0) (coord_plane_mem_maximalIdeal 0))
      (Ideal.mul_mem_mul (coord_plane_mem_maximalIdeal 1) (coord_plane_mem_maximalIdeal 1))

/-- `V(x² + y²) ⊆ ℝ²` has no simple point ([Hir64, Introduction]). At the only point `0` the
stalk of `X` is `𝒪_{ℝ²,0} / (x² + y²)` (`mem_reg_toAnalyticSpace_iff`) with `x² + y²` a nonzero
element of `𝔪_0²`, and a regular local ring modulo a nonzero element of `𝔪²` is not regular. -/
theorem circleIdeal_regSet_eq_empty : AnalyticManifold.IdealSheaf.regSet circleIdeal = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro _ ⟨⟨p, hp⟩, hreg, rfl⟩
  exact not_isRegularLocalRing_stalk_circleIdeal hp
    ((mem_reg_toAnalyticSpace_iff circleIdeal _).mp hreg)

end Hironaka.Manifold

end
