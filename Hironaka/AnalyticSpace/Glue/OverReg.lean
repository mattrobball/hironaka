/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Over
import Hironaka.AnalyticSpace.CoverLemmas
import Hironaka.AnalyticSpace.Glue.OverProper
import Hironaka.AnalyticSpace.RegOpenImmersion
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Non-singularity and properness of a glued space over a base

Two clauses of the resolution theorem for analytic spaces (the manifold clause (1) and the
properness clause (3) of the resolution problem, [Hir64, Introduction, p. 111]; [Kol07, Theorem 45,
(1)]; [Wlo09, §4]: "`des_V : Ṽ → V` is bimeromorphic and proper") for a gluing datum
`G : GlueOver X R π dom`:

* `isNonsingular_gluedOver`: a glued space of non-singular pieces is non-singular: every point comes
  from a piece through the open immersion `ιGlued i` (`exists_ιGlued_eq`), and an open immersion
  preserves the regularity of the stalk (`mem_reg_iff_of_isOpenImmersion`);
* `isProperMap_descMap_of_iUnion`: the descended map is proper when the base open subsets cover `X`
  and every piece map is proper onto its base open subset: properness is local on the target
  (`isProperMap_of_restrictPreimage_cover`), and over `dom i` the descended map is the `i`-th piece
  map (`isProperMap_restrictPreimage_descMap`, `Hironaka.AnalyticSpace.Glue.OverProper`).

Both are applied to the glued local resolutions in
`Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionClauses`.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace.KLocallyRingedSpace

universe u

namespace AnalyticSpace.GlueOver

variable {K : Type} [RCLike K] {X : AnalyticSpace.{u} K} {ι : Type u}
  {R : ι → AnalyticSpace.{u} K} {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace}
  {dom : ι → Opens X} (G : GlueOver X R π dom) [Countable ι]

/-- **A glued space of non-singular pieces is non-singular** (the smoothness clause [Kol07, Theorem
45, (1)], piece by piece): every point of the glued space is the image of a point of a piece under
the open immersion `ιGlued i`, and regularity of the stalk is carried across an open immersion
(`mem_reg_iff_of_isOpenImmersion`). -/
theorem isNonsingular_gluedOver (h : ∀ i, (R i).IsNonsingular) : G.gluedOver.IsNonsingular := by
  change regularLocus G.gluedOver = Set.univ
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨i, y, rfl⟩ := G.exists_ιGlued_eq z
  exact (AnalyticSpace.mem_reg_iff_of_isOpenImmersion (G.ιGlued i) (G.isOpenImmersion_ιGlued i)
    y).mp (Set.eq_univ_iff_forall.mp (h i) y)

/-- **The descended map is proper when the base open subsets cover `X` and every piece map is proper
onto its base open subset** ("`des_V` is proper", [Wlo09, §4]; the properness clause of the
resolution problem, [Hir64, Introduction, p. 111]): properness is local on the target
(`isProperMap_of_restrictPreimage_cover`), and over `dom i` the descended map is the `i`-th piece
map (`isProperMap_restrictPreimage_descMap`). -/
theorem isProperMap_descMap_of_iUnion (hcov : ⋃ i, (dom i : Set X) = univ)
    (hπ : ∀ i, IsProperMap fun y : R i =>
      (⟨KLocallyRingedSpace.Hom.toFun (π i) y, G.range_subset i ⟨y, rfl⟩⟩ : dom i)) :
    IsProperMap (KLocallyRingedSpace.Hom.toFun G.descMap) :=
  isProperMap_of_restrictPreimage_cover (KLocallyRingedSpace.Hom.toFun G.descMap)
      (Hom.continuous_toFun _)
    (fun i => (dom i : Set X)) (fun i => (dom i).isOpen) hcov
    (fun i => G.isProperMap_restrictPreimage_descMap i (hπ i))

end AnalyticSpace.GlueOver

end
