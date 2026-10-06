/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.CenterComponents
public import Mathlib.Analysis.InnerProductSpace.Basic
import Hironaka.Analytic.Rueckert.ParametrizationGraph
import Hironaka.Analytic.Rueckert.ParametrizationPrimitive
import Hironaka.AnalyticSpace.RegDensity
import Hironaka.Manifold.FiniteSuccession.Restrict.RegSetBasic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The simple locus of a reduced complex space is dense

Over `ℂ`, the simple points of a reduced complex analytic space are dense
(`dense_reg_of_isReduced_complex`: [Fre17, II 5.13], proved in `Hironaka/Space/RegDensity` from
Noether normalization by a primitive element and the graph description of Rückert's
parametrization); read in the ambient manifold, `|J| ⊆ closure (regSet J)` for `J` with radical
stalks (`cosupport_subset_closure_regSet`). This is the density Kollár's proof of Corollary 22 uses
([Kol07, Corollary 22, proof]; compare the remark after Main Theorem I in [Hir64, Ch. 0, §3]).
-/

public section

open Set Filter Topology TopologicalSpace

universe u

noncomputable section

namespace Manifold

/-- The simple points of a reduced complex analytic space are dense [Fre17, II 5.13]: the general
theorem of `Hironaka/Space/RegDensity`, at the hypotheses proved for `ℂ` (Noether normalization
by a primitive element and the graph description of Rückert's parametrization). -/
theorem dense_reg_of_isReduced_complex (X : AnalyticSpace.{u} ℂ)
    (hX : X.IsReduced) : Dense X.regularLocus :=
  AnalyticSpace.dense_reg_of_isReduced_of_hyps X hX
    Analytic.exists_primitive_normalization
    Analytic.exists_graph_of_isPrime

variable {n : ℕ} {A : AnalyticManifold.{u} ℂ (Fin n → ℂ)} (J : AnalyticManifold.IdealSheaf A)

/-- Over `ℂ`, for `J` with radical stalks, the simple locus of `V(J)` read in the ambient is dense
in the support `|J|`. -/
theorem cosupport_subset_closure_regSet (hJ : ∀ x, (J.stalkIdeal x).IsRadical) :
    J.support ⊆ closure (AnalyticManifold.IdealSheaf.regSet J) := by
  intro a ha
  obtain ⟨y, rfl⟩ := (range_toFun_toAnalyticSpaceι J).ge ha
  have hd := dense_reg_of_isReduced_complex _ (isReduced_toAnalyticSpace_of_isRadical J hJ)
  exact image_closure_subset_closure_image (continuous_toFun_toAnalyticSpaceι J) ⟨y, hd y, rfl⟩

end Manifold

end
