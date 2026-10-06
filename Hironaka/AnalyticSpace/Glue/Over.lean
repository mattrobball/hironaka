/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Desc
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Gluing analytic spaces over a base along the overlaps of their base open subsets

Włodarczyk builds the canonical desingularization of an analytic space by gluing the
desingularizations of the pieces of a cover along their overlaps: `Ṽ` is the manifold "obtained by
gluing `Ṽ_i` along `Ṽ_i ∩ Ṽ_j`", and the desingularization morphism `des_V : Ṽ → V` is bimeromorphic
and proper [Wlo09, §4], and for a whole analytic space `Ỹ` is the manifold obtained by gluing the
`Ũ_i` along the `Ũ_ij` [Wlo09, §4.3]; Kollár globalizes likewise, from neighbourhoods of compact
sets to an increasing union of them [Kol07, 44]. Both the finite gluing over a relatively compact
open subset and the countable one along an exhaustion glue analytic `K`-spaces `R i` lying over a
base `X` through maps `π i : R i → X`, the `i`-th piece living over an open subset `dom i ⊆ X`,
along the overlaps `dom i ∩ dom j` of the base open subsets: the gluing open subsets are the
preimages `π i ⁻¹(dom i ∩ dom j)`, the transitions are `K`-isomorphisms between them compatible with
the `π i`, and the glued space comes with the descended map to `X`. This module packages that shape
once, over the gluing of `K`-spaces (`KGlueData`, `gluedAnalytic`, `descK` of
`Hironaka.AnalyticSpace.Glue.KSpace` and `Hironaka.AnalyticSpace.Glue.Desc`):

* `GlueOver.glueOpens X R π dom i j`: the gluing open subset `π i ⁻¹(dom i ∩ dom j)` of the `i`-th
  piece towards the `j`-th (the embedding `(V_i ∩ V_j)~ → Ṽ_i` of [Wlo09, §4]), the points
  `overOpens π i (dom i ⊓ dom j)` over the overlap (`overOpens_eq_comap`: Mathlib's `Opens.comap`);
  `glueOpens_self_eq_top` is the `W_id` field of the gluing core once every `π i` lands in `dom i`;
* `GlueOver X R π dom`: the data: `range_subset`, the transitions `t i j` with `t_id` and `t_inter`
  (the fields of `KGlueCore`), their compatibility `compat` with the `π i` (the descent hypothesis
  of `descK`), the cocycle identity `cocycle` (`KGlueData`), and the Hausdorffness `t2` of the glued
  space, which the sources take for granted with the manifold structure of `Ṽ`; it is discharged
  where the data are built, by the closed-graph criterion `t2Space_of_isClosed_transitionGraph` of
  `Hironaka.AnalyticSpace.Glue.KSpace`, applied in `Hironaka.AnalyticSpace.Glue.OverLemmas`;
* `GlueOver.gluedOver`: the glued analytic `K`-space, for a countable index type (`gluedAnalytic`,
  every piece being analytic);
  `GlueOver.descMap : gluedOver ⟶ X`, the descended map (`des_V`); `GlueOver.ιGlued i`, the open
  immersions of the pieces, with `ιGlued_descMap : ιGlued i ≫ descMap = π i` and
  `range_toFun_descMap_subset : range descMap ⊆ ⋃ i, dom i`.

The gluing data over a base are used to assemble the resolution of an analytic space from the local
resolutions of the pieces of a cover, and along an exhaustion, in
`Hironaka.Manifold.Sequence.Restrict` (`PieceGlue`, `PieceGlueDatum`, `PieceGlueIndep`,
`ResolutionClauses`), which establish the clauses of the resolution theorem for analytic spaces.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace

universe u

variable {K : Type} [RCLike K]

namespace GlueOver

variable (X : AnalyticSpace.{u} K) {ι : Type u} (R : ι → AnalyticSpace.{u} K)
  (π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace) (dom : ι → Opens X)

variable {X R} in
/-- The points of the `i`-th piece over an open `O` of the base — the same open as Mathlib's
`Opens.comap` (`overOpens_eq_comap`), spelled so that `glueOpens i j` is literally `overOpens` of
the overlap. -/
abbrev overOpens (i : ι) (O : Opens X) : Opens (R i) :=
  ⟨KLocallyRingedSpace.Hom.toFun (π i) ⁻¹' (O : Set X), O.isOpen.preimage (Hom.continuous_toFun
      (π i))⟩

variable {X R} in
/-- `overOpens π i O` is Mathlib's `Opens.comap` of `O` along `π i`. -/
theorem overOpens_eq_comap (i : ι) (O : Opens X) :
    overOpens π i O = Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun
        (π i)⟩ O :=
  Opens.ext (by rw [Opens.coe_comap]; rfl)

/-- The gluing open subset of the `i`-th piece towards the `j`-th: the points of `R i` lying over
the overlap `dom i ∩ dom j` of the base open subsets (the piece `(V_i ∩ V_j)~` of `Ṽ_i` in [Wlo09,
§4]). -/
def glueOpens (i j : ι) : Opens (R i) :=
  overOpens π i (dom i ⊓ dom j)

theorem mem_glueOpens {i j : ι} {x : R i} :
    x ∈ glueOpens X R π dom i j ↔ KLocallyRingedSpace.Hom.toFun
        (π i) x ∈ dom i ∧ KLocallyRingedSpace.Hom.toFun (π i) x ∈ dom j :=
  Iff.rfl

/-- The `W_id` field of the gluing core: a piece landing in its own base open is glued to itself
along everything. -/
theorem glueOpens_self_eq_top (hrange : ∀ i, range (KLocallyRingedSpace.Hom.toFun (π i)) ⊆ dom i)
    (i : ι) :
    glueOpens X R π dom i i = ⊤ := by
  ext x
  refine ⟨fun _ => trivial, fun _ => (mem_glueOpens X R π dom).mpr ⟨?_, ?_⟩⟩ <;>
    exact hrange i ⟨x, rfl⟩

/-- The `K`-gluing core (`KGlueCore`) of the pieces `R i` over `X` with the given transitions: index
type `ι`, pieces `R i`, gluing open subsets `glueOpens`, `W_id` from `hrange`. -/
abbrev overCore (hrange : ∀ i, range (KLocallyRingedSpace.Hom.toFun (π i)) ⊆ dom i)
    (t : ∀ i j, (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) ⟶
      (R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i))
    (t_id : ∀ i, t i i = 𝟙 _)
    (t_inter : ∀ i j k (x : (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j)),
      x.1 ∈ glueOpens X R π dom i k → (KLocallyRingedSpace.Hom.toFun
          (t i j) x).1 ∈ glueOpens X R π dom j k) :
    Glue.KGlueCore.{u} K where
  J := ι
  Y i := (R i).toKLocallyRingedSpace
  W := glueOpens X R π dom
  W_id := glueOpens_self_eq_top X R π dom hrange
  t := t
  t_id := t_id
  t_inter := t_inter

/-- The `K`-gluing data (`KGlueData`): the core with the cocycle identity. -/
abbrev overData (hrange : ∀ i, range (KLocallyRingedSpace.Hom.toFun (π i)) ⊆ dom i)
    (t : ∀ i j, (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) ⟶
      (R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i))
    (t_id : ∀ i, t i i = 𝟙 _)
    (t_inter : ∀ i j k (x : (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j)),
      x.1 ∈ glueOpens X R π dom i k → (KLocallyRingedSpace.Hom.toFun
          (t i j) x).1 ∈ glueOpens X R π dom j k)
    (cocycle : ∀ i j k, (overCore X R π dom hrange t t_id t_inter).tRes i j k ≫
      (overCore X R π dom hrange t t_id t_inter).tRes j k i ≫
        (overCore X R π dom hrange t t_id t_inter).tRes k i j = 𝟙 _) :
    Glue.KGlueData.{u} K :=
  { overCore X R π dom hrange t t_id t_inter with cocycle := cocycle }

end GlueOver

/-- **Gluing data over a base** [Wlo09, §4 and §4.3]: analytic `K`-spaces `R i` lying over the base
`X` through `π i : R i → X`, the `i`-th over the open subset `dom i ⊆ X`, glued along the overlaps
of the base open subsets. The fields: every `π i` lands in `dom i`; the transitions `t i j` between
the gluing open subsets `π i ⁻¹(dom i ∩ dom j)` and `π j ⁻¹(dom j ∩ dom i)`, with `t_id` and
`t_inter` (the fields of `KGlueCore`), compatible with the `π i` (`compat`, the descent hypothesis
of `descK`); the cocycle identity; and the Hausdorffness of the glued space. -/
structure GlueOver (X : AnalyticSpace.{u} K) {ι : Type u} (R : ι → AnalyticSpace.{u} K)
    (π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace) (dom : ι → Opens X) where
  /-- Every piece lies over its base open. -/
  range_subset : ∀ i, range (KLocallyRingedSpace.Hom.toFun (π i)) ⊆ dom i
  /-- The transition `K`-morphisms between the gluing opens. -/
  t : ∀ i j, (R i).toKLocallyRingedSpace.restrictOpen (GlueOver.glueOpens X R π dom i j) ⟶
    (R j).toKLocallyRingedSpace.restrictOpen (GlueOver.glueOpens X R π dom j i)
  t_id : ∀ i, t i i = 𝟙 _
  /-- The transition from `i` to `j` maps the points over `dom k` to points over `dom k`. -/
  t_inter : ∀ i j k
    (x : (R i).toKLocallyRingedSpace.restrictOpen (GlueOver.glueOpens X R π dom i j)),
    x.1 ∈ GlueOver.glueOpens X R π dom i k →
      (KLocallyRingedSpace.Hom.toFun (t i j) x).1 ∈ GlueOver.glueOpens X R π dom j k
  /-- The transitions lie over `X`: `π j ∘ t i j = π i` on the gluing open. -/
  compat : ∀ i j,
    ofRestrict (R i).toKLocallyRingedSpace (GlueOver.glueOpens X R π dom i j) ≫ π i =
      (t i j ≫ ofRestrict (R j).toKLocallyRingedSpace (GlueOver.glueOpens X R π dom j i)) ≫ π j
  /-- The cocycle identity of the gluing data. -/
  cocycle : ∀ i j k,
    (GlueOver.overCore X R π dom range_subset t t_id t_inter).tRes i j k ≫
      (GlueOver.overCore X R π dom range_subset t t_id t_inter).tRes j k i ≫
        (GlueOver.overCore X R π dom range_subset t t_id t_inter).tRes k i j = 𝟙 _
  /-- The glued space is Hausdorff. -/
  t2 : T2Space (GlueOver.overData X R π dom range_subset t t_id t_inter cocycle).glued

namespace GlueOver

variable {X : AnalyticSpace.{u} K} {ι : Type u} {R : ι → AnalyticSpace.{u} K}
  {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace} {dom : ι → Opens X}
  (G : GlueOver X R π dom)

/-- The `K`-gluing data of the gluing over `X`. -/
abbrev toKGlueData : Glue.KGlueData.{u} K :=
  overData X R π dom G.range_subset G.t G.t_id G.t_inter G.cocycle

theorem toKGlueData_J : G.toKGlueData.J = ι := rfl

theorem toKGlueData_Y (i : ι) : G.toKGlueData.Y i = (R i).toKLocallyRingedSpace := rfl

theorem toKGlueData_W (i j : ι) : G.toKGlueData.W i j = glueOpens X R π dom i j := rfl

theorem toKGlueData_t (i j : ι) : G.toKGlueData.t i j = G.t i j := rfl

variable [Countable ι]

/-- **The glued analytic `K`-space** ("`Ṽ` obtained by gluing `Ṽ_i` along `Ṽ_i ∩ Ṽ_j`", [Wlo09,
§4]), for a countable index type: `gluedAnalytic` of the `K`-gluing data, the pieces being the
analytic spaces `R i` themselves. -/
def gluedOver : AnalyticSpace.{u} K :=
  letI : Countable G.toKGlueData.J := ‹Countable ι›
  G.toKGlueData.gluedAnalytic G.t2 R fun _ => Iso.refl _

theorem gluedOver_toKLocallyRingedSpace :
    G.gluedOver.toKLocallyRingedSpace = G.toKGlueData.gluedK :=
  rfl

/-- **The descended map to the base** (`des_V : Ṽ → V` of [Wlo09, §4]): the `π i` descend to the
glued space by `compat` (`descK`). -/
def descMap : G.gluedOver.toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace :=
  G.toKGlueData.descK π fun i j => congrArg Subtype.val (G.compat i j)

/-- The open immersion of the `i`-th piece into the glued space. -/
def ιGlued (i : ι) : (R i).toKLocallyRingedSpace ⟶ G.gluedOver.toKLocallyRingedSpace :=
  G.toKGlueData.ιK i

instance isOpenImmersion_ιGlued (i : ι) : LocallyRingedSpace.IsOpenImmersion (G.ιGlued i).1 :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (G.toKGlueData.ιK i).1)

/-- The descended map restricts to `π i` on the `i`-th piece. -/
theorem ιGlued_descMap (i : ι) : G.ιGlued i ≫ G.descMap = π i :=
  G.toKGlueData.ιK_descK _ _ i

theorem toFun_descMap_ιGlued (i : ι) (y : R i) :
    KLocallyRingedSpace.Hom.toFun G.descMap (KLocallyRingedSpace.Hom.toFun
        (G.ιGlued i) y) = KLocallyRingedSpace.Hom.toFun (π i) y :=
  G.toKGlueData.toFun_descK_ιK _ _ i y

/-- Every point of the glued space comes from a piece (`exists_ι_base_eq`, with the index and piece
types of the gluing over `X`). -/
theorem exists_ιGlued_eq (z : G.gluedOver) : ∃ (i : ι) (y : R i), KLocallyRingedSpace.Hom.toFun
    (G.ιGlued i) y = z :=
  G.toKGlueData.exists_ι_base_eq z

/-- The glued space lies over the union of the base opens. -/
theorem range_toFun_descMap_subset : range (KLocallyRingedSpace.Hom.toFun G.descMap) ⊆ ⋃ i,
    (dom i : Set X) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨i, y, rfl⟩ := G.exists_ιGlued_eq z
  rw [toFun_descMap_ιGlued]
  exact mem_iUnion.mpr ⟨i, G.range_subset i ⟨y, rfl⟩⟩

end GlueOver

end AnalyticSpace

end
