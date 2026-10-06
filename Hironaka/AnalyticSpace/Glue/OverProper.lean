/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Over
import Hironaka.AnalyticSpace.Glue.Morphism
import Hironaka.AnalyticSpace.ProperRestrict
import Hironaka.AnalyticSpace.Sigma
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The descended map of a gluing over a base is proper over the base open subsets

"`des_V : Ṽ → V` … is proper" [Wlo09, §4]: the map descended from proper piece maps
`π i : R i → dom i` is proper over the union of the base open subsets. Two facts about a gluing
datum `G : GlueOver X R π dom`:

* `mem_range_toFun_ιGlued_iff`: the part of the glued space over `dom i` is exactly the image of the
  `i`-th piece under the open immersion `ιGlued i`: a point of the `j`-th piece over `dom i` lies
  over `dom i ∩ dom j`, where the transition `t j i` carries it into the `i`-th piece (the glue
  condition `KGlueData.ofRestrict_comp_ιK`);
* `isProperMap_restrictPreimage_descMap`: hence over `dom i` the descended map is `π i` read through
  the homeomorphism `R i ≃ₜ des⁻¹(dom i)`, and it is proper there when `π i : R i → dom i` is;
  `isProperMap_restrictPreimage_descMap_of_subset` assembles the base open subsets into properness
  over every `V ⊆ ⋃ dom i` (`isProperMap_restrictPreimage_of_cover`).

Both properness statements enter the gluing datum of the local resolutions
(`Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueDatum`), and through
`Hironaka.AnalyticSpace.Glue.OverReg` the properness clause of the resolution
(`Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionClauses`).
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

/-- **The part of the glued space over `dom i` is the image of the `i`-th piece** (the part of `Ṽ`
over `V_i` is `Ṽ_i`, [Wlo09, §4]): a point over `dom i` coming from the `j`-th piece lies over
`dom i ∩ dom j`, where the transition `t j i` carries it into the `i`-th piece (the glue condition
`KGlueData.ofRestrict_comp_ιK`). -/
theorem mem_range_toFun_ιGlued_iff (i : ι) (z : G.gluedOver) :
    z ∈ range (KLocallyRingedSpace.Hom.toFun (G.ιGlued i)) ↔ KLocallyRingedSpace.Hom.toFun
        G.descMap z ∈ dom i := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [G.toFun_descMap_ιGlued]
    exact G.range_subset i ⟨y, rfl⟩
  · intro hz
    obtain ⟨j, y, rfl⟩ := G.exists_ιGlued_eq z
    rw [G.toFun_descMap_ιGlued] at hz
    have hy : y ∈ glueOpens X R π dom j i :=
      (mem_glueOpens X R π dom).mpr ⟨G.range_subset j ⟨y, rfl⟩, hz⟩
    have hglue := congrArg
      (fun φ => KLocallyRingedSpace.Hom.toFun φ
        (Subtype.mk y hy : (R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i)))
      (G.toKGlueData.ofRestrict_comp_ιK j i)
    exact ⟨(KLocallyRingedSpace.Hom.toFun (G.t j i) (Subtype.mk y hy)).1, hglue.symm⟩

/-- The part of the glued space over `dom i`, as a set: the image of the `i`-th piece. -/
theorem preimage_toFun_descMap_dom (i : ι) :
    KLocallyRingedSpace.Hom.toFun G.descMap ⁻¹' (dom i : Set X) = range
        (KLocallyRingedSpace.Hom.toFun (G.ιGlued i)) :=
  Set.ext fun z => (G.mem_range_toFun_ιGlued_iff i z).symm

/-- **The descended map is proper over `dom i` when the `i`-th piece map is** ("`des_V` is proper",
[Wlo09, §4]): over `dom i` the glued space is the `i`-th piece (`ιGlued i`, an open embedding onto
the part over `dom i`), and the descended map is `π i` there (`toFun_descMap_ιGlued`). -/
theorem isProperMap_restrictPreimage_descMap (i : ι)
    (hπ : IsProperMap fun y : R i =>
      (⟨KLocallyRingedSpace.Hom.toFun (π i) y, G.range_subset i ⟨y, rfl⟩⟩ : dom i)) :
    IsProperMap ((dom i : Set X).restrictPreimage (KLocallyRingedSpace.Hom.toFun G.descMap)) := by
  have hemb : IsOpenEmbedding (KLocallyRingedSpace.Hom.toFun (G.ιGlued i)) :=
      Hom.isOpenEmbedding_toFun _
  let e : R i ≃ₜ range (KLocallyRingedSpace.Hom.toFun (G.ιGlued i)) :=
      hemb.toIsEmbedding.toHomeomorph
  refine isProperMap_of_homeomorph_comp_eq
    ((Homeomorph.setCongr (G.preimage_toFun_descMap_dom i)).trans e.symm) (Homeomorph.refl _) hπ
    (fun a => Subtype.ext ?_)
  have hy : ∀ p : range (KLocallyRingedSpace.Hom.toFun (G.ιGlued i)), KLocallyRingedSpace.Hom.toFun
      (G.ιGlued i) (e.symm p) = p.1 :=
    fun p => congrArg Subtype.val (e.apply_symm_apply p)
  change KLocallyRingedSpace.Hom.toFun G.descMap a.1 = KLocallyRingedSpace.Hom.toFun (π i) (e.symm
      ⟨a.1, _⟩)
  rw [← G.toFun_descMap_ιGlued i, hy]

/-- **The descended map is proper over every `V ⊆ ⋃ dom i`** when every piece map is proper over its
base open subset (`isProperMap_restrictPreimage_of_cover` on the base open subsets). -/
theorem isProperMap_restrictPreimage_descMap_of_subset
    (hπ : ∀ i, IsProperMap fun y : R i =>
      (⟨KLocallyRingedSpace.Hom.toFun (π i) y, G.range_subset i ⟨y, rfl⟩⟩ : dom i))
    (V : Set X) (hVsub : V ⊆ ⋃ i, (dom i : Set X)) :
    IsProperMap (V.restrictPreimage (KLocallyRingedSpace.Hom.toFun G.descMap)) :=
  isProperMap_restrictPreimage_of_cover (KLocallyRingedSpace.Hom.toFun G.descMap)
      (Hom.continuous_toFun _)
    (fun i => (dom i : Set X)) (fun i => (dom i).isOpen)
    (fun i => G.isProperMap_restrictPreimage_descMap i (hπ i)) V hVsub

end AnalyticSpace.GlueOver

end
