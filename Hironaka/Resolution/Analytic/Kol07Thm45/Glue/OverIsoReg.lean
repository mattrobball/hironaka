/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Over
public import Hironaka.AnalyticSpace.Restrict.Defs
import Hironaka.AnalyticSpace.Glue.OverPart
import Hironaka.AnalyticSpace.HomOfSections
import Hironaka.AnalyticSpace.IsoOverCover
import Hironaka.AnalyticSpace.Manifold.Restrict
import Hironaka.AnalyticSpace.RestrictOverLemmas
import Hironaka.AnalyticSpace.SigmaLemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.IsoOverLemmas
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The descended map of a gluing is an isomorphism where the pieces are

The resolution is an isomorphism over the simple points (clause (2) of the resolution problem,
[Hir64, Introduction, p. 111]; [Kol07, Theorem 45, (2)]; [Wlo09, Theorem 2.0.1, (1)]), read on a
gluing datum `G : GlueOver X R π dom`: over an open subset `V ⊆ dom i` the glued space is the `i`-th
piece (`partIso`, `Hironaka.AnalyticSpace.Glue.OverPart`), so the descended map is an isomorphism
over `V` when the piece map is (`isIsoOver_descMap_of_isIsoOver`, through
`Hom.IsIsoOver.of_isIso_restrictSet_comm`); over an open subset `S`, isomorphisms over `S ∩ dom i`
for every piece assemble to one over `S ∩ ⋃ dom i` (`isIsoOver_descMap_inter_iUnion`). The latter is
applied to the glued local resolutions in
`Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionIsoReg`.
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

/-- **The descended map is an isomorphism over an open subset `V ⊆ dom i` when the `i`-th piece map
is** ([Kol07, Theorem 45, (2)], piece by piece): the part of the glued space over `dom i` is the
part of the piece (`partIso`, read between the restrictions `openOf`), over `X`; then
`Hom.IsIsoOver.of_isIso_restrictSet_comm` at `P := V`. -/
theorem isIsoOver_descMap_of_isIsoOver (i : ι) {V : Set X} (hV : IsOpen V)
    (hVi : V ⊆ (dom i : Set X)) (h : AnalyticSpace.Hom.IsIsoOver (π i) V) :
    AnalyticSpace.Hom.IsIsoOver G.descMap V := by
  have hoG : IsOpen (KLocallyRingedSpace.Hom.toFun G.descMap ⁻¹' (dom i : Set X)) :=
    (dom i).isOpen.preimage (Hom.continuous_toFun G.descMap)
  have hoR : IsOpen (KLocallyRingedSpace.Hom.toFun (π i) ⁻¹' (dom i : Set X)) :=
    (dom i).isOpen.preimage (Hom.continuous_toFun (π i))
  -- the two spellings of the parts over `dom i`
  have hr1 : range (KLocallyRingedSpace.Hom.toFun (ofRestrict G.gluedOver.toKLocallyRingedSpace
        (AnalyticSpace.openOf G.gluedOver (KLocallyRingedSpace.Hom.toFun G.descMap ⁻¹'
            (dom i : Set X))))) =
      range (KLocallyRingedSpace.Hom.toFun (ofRestrict G.gluedOver.toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G.descMap, Hom.continuous_toFun G.descMap⟩
            (dom i)))) := by
    rw [range_toFun_ofRestrict, range_toFun_ofRestrict,
      AnalyticSpace.openOf_of_isOpen G.gluedOver hoG]
    rfl
  have hr2 : range (KLocallyRingedSpace.Hom.toFun (ofRestrict (R i).toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ (dom i)))) =
      range (KLocallyRingedSpace.Hom.toFun (ofRestrict (R i).toKLocallyRingedSpace
        (AnalyticSpace.openOf (R i) (KLocallyRingedSpace.Hom.toFun (π i) ⁻¹' (dom i : Set X))))) :=
            by
    rw [range_toFun_ofRestrict, range_toFun_ofRestrict,
      AnalyticSpace.openOf_of_isOpen (R i) hoR]
    rfl
  let e₁ := isoOfRangeEq _ _ hr1
  let e₂ := isoOfRangeEq _ _ hr2
  -- the identification of the two restrictions of the descended map over `dom i`, as one morphism
  obtain ⟨eK, heK⟩ : ∃ eK : G.gluedOver.toKLocallyRingedSpace.restrictOpen
        (AnalyticSpace.openOf G.gluedOver (KLocallyRingedSpace.Hom.toFun G.descMap ⁻¹'
            (dom i : Set X))) ⟶
      (R i).toKLocallyRingedSpace.restrictOpen
        (AnalyticSpace.openOf (R i) (KLocallyRingedSpace.Hom.toFun (π i) ⁻¹' (dom i : Set X))),
      eK = e₁.hom ≫ (G.partIso i (dom i) le_rfl).inv ≫ e₂.hom := ⟨_, rfl⟩
  have hK : IsIso eK := by rw [heK]; infer_instance
  -- it lies over `X`
  have hover : eK ≫ ofRestrict (R i).toKLocallyRingedSpace
        (AnalyticSpace.openOf (R i) (KLocallyRingedSpace.Hom.toFun (π i) ⁻¹'
            (dom i : Set X))) ≫ π i =
      ofRestrict G.gluedOver.toKLocallyRingedSpace
        (AnalyticSpace.openOf G.gluedOver (KLocallyRingedSpace.Hom.toFun G.descMap ⁻¹'
            (dom i : Set X))) ≫
        G.descMap := by
    rw [heK]
    exact conj_over_eq _ _ _ _ _ _ _ _ _ (isoOfRangeEq_hom_comp _ _ hr1)
      (isoOfRangeEq_hom_comp _ _ hr2)
      ((G.partIso_inv_comp_over i (dom i) le_rfl).symm.trans (Category.assoc _ _ _).symm)
  have hcomm : eK ≫ AnalyticSpace.Hom.restrictSet (π i) (dom i : Set X) =
      AnalyticSpace.Hom.restrictSet G.descMap (dom i : Set X) := by
    refine Hom.ext_of_comp_ofRestrict ?_
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Hom.restrictTo_comp_ofRestrict G.descMap _ _
      (AnalyticSpace.Hom.mapsTo_openOf G.descMap (dom i : Set X))).symm)
    exact (congrArg (fun k => eK ≫ k) (Hom.restrictTo_comp_ofRestrict (π i) _ _
      (AnalyticSpace.Hom.mapsTo_openOf (π i) (dom i : Set X)))).trans hover
  exact AnalyticSpace.Hom.IsIsoOver.of_isIso_restrictSet_comm (Y := G.gluedOver) (Y' := R i)
    (O := (dom i : Set X)) G.descMap (π i) eK
    (AnalyticSpace.isIso_of_isIso_toKLocallyRingedSpace
      (Y := G.gluedOver.restrictSet (KLocallyRingedSpace.Hom.toFun G.descMap ⁻¹' (dom i : Set X)))
      (Z := (R i).restrictSet (KLocallyRingedSpace.Hom.toFun (π i) ⁻¹'
          (dom i : Set X))) eK hK) hcomm hV hVi h

/-- **Over an open subset `S`, isomorphisms over `S ∩ dom i` for every piece give one over
`S ∩ ⋃ dom i`.** -/
theorem isIsoOver_descMap_inter_iUnion (S : Set X) (hS : IsOpen S)
    (h : ∀ i, AnalyticSpace.Hom.IsIsoOver (π i) (S ∩ (dom i : Set X))) :
    AnalyticSpace.Hom.IsIsoOver G.descMap (S ∩ ⋃ i, (dom i : Set X)) := by
  have key := AnalyticSpace.Hom.isIsoOver_iUnion G.descMap (fun i => S ∩ (dom i : Set X))
    (fun i => hS.inter (dom i).isOpen)
    (fun i => G.isIsoOver_descMap_of_isIsoOver i (hS.inter (dom i).isOpen) inter_subset_right
      (h i))
  have hset : S ∩ ⋃ i, (dom i : Set X) = ⋃ i, S ∩ (dom i : Set X) := Set.inter_iUnion S _
  exact (congrArg (AnalyticSpace.Hom.IsIsoOver G.descMap) hset).mpr key

end AnalyticSpace.GlueOver

end
