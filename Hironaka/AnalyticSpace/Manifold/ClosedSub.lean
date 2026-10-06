/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Manifold.Defs
public import Hironaka.Manifold.StructureSheaf
public import Hironaka.Manifold.Submanifold.Restrict
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.Manifold.FullyFaithful
public import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Germ.ChartTransport
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.Submanifold.Ideal
import Hironaka.Manifold.Submanifold.Manifold
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The space of a closed submanifold is the closed subspace cut out by its ideal sheaf

For a closed submanifold `Y ⊆ M` of an analytic manifold (`IsClosedSubmanifold`, with its induced
charts), the analytic space `Sp(Y)` is `K`-isomorphic to the closed subspace `Sp(M) / 𝓘_Y` of
`Sp(M)` cut out by the ideal sheaf `𝓘_Y = hY.idealSheaf` of the functions vanishing on `Y`,
compatibly with the inclusion `Y → M` (`toSpace_closedSubmanifold`,
`toSpace_closedSubmanifold_comp`). Thus the closed submanifolds of `M` are closed subspaces of
`Sp(M)` in the sense of [Hir64, Ch. 0, §1, p. 119] (a local analytic `K`-space is
`(S(I), (𝒜_G/I)|S(I))`) and of [BM97, §3] (a closed subspace is defined by an ideal sheaf of finite
type). The comparison is used to read a closed submanifold, the exceptional divisor of a blow-up, as
a closed subspace of the analytic space
(`Hironaka.Resolution.Analytic.Wlo09.PreimageSing`); the local description of the sections
of the quotient sheaf (`exists_local_rep`) is used in the gluing of local resolutions
(`Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Model`).

The morphism `closedHom : Sp(Y) ⟶ Sp(M) / 𝓘_Y` is built directly:

* its base is the identification of `Y` with the cosupport of `𝓘_Y` (`cosupport_idealSheaf`:
  `S(𝓘_Y) = Y`);
* a section of the quotient sheaf over `V` is a compatible family of classes
  `s_z ∈ 𝒪_{M,z}/𝓘_{Y,z}`; since `𝓘_{Y,z}` is proper it lies in the maximal ideal, so evaluation at
  `z` descends to the fibre (`fiberEval`), and `y ↦ ev_y(s_y)` is an analytic function on `Y ∩ V`,
  being locally the restriction to `Y` of the ambient section representing `s` (`exists_local_rep`,
  `contMDiff_closedSectionFun`);
* on stalks the map is `𝒪_{M,y}/𝓘_{Y,y} → 𝒪_{Y,y}` induced by the restriction of germs
  `restrictStalk` (`stalkMap_closedHomAux_eq`), a bijection because `restrictStalk` is onto with
  kernel exactly `𝓘_{Y,y}` (`bijective_fiberRestrict`);
* a morphism of locally ringed spaces that is a homeomorphism on points and an isomorphism on every
  stalk is an isomorphism (Mathlib's stalk criterion); the `K`-structure is respected because
  constants evaluate to constants.

The composite with the canonical morphism `Sp(M)/𝓘_Y ⟶ Sp(M)` is `Sp` of the inclusion
(`closedHom_comp_quotientι`), by the extensionality of morphisms between spaces of manifolds on
their underlying maps (`hom_ext_baseFun`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff Topology

universe u

noncomputable section

namespace AnalyticSpace

namespace KLocallyRingedSpace

open QuotientSpace

variable {K : Type} [RCLike K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {M : Type u}
  [TopologicalSpace M] [ChartedSpace E M]

local notation "XM" => KLocallyRingedSpace.toLocallyRingedSpace (ofManifold K E M)

/-- A compatible germ family on the quotient of `Sp(M)` is, near each point of its domain, the
family of the classes of one ambient analytic function (the local predicate defining the quotient
sheaf, unfolded). -/
theorem exists_local_rep (J : IdealSheaf (structureSheaf K E M)) (V : Opens (support XM J))
    (s : (presheafCommRing XM J).obj (op V)) (z₀ : V) :
    ∃ (U₁ : Opens (support XM J)) (_ : z₀.1 ∈ U₁) (W₁ : Opens M)
      (a : (structureSheaf K E M).presheaf.obj (op W₁)),
      ∀ (z : support XM J) (_ : z ∈ U₁), ∃ (hzV : z ∈ V) (hzW : z.1 ∈ W₁),
        s.1 ⟨z, hzV⟩ = Ideal.Quotient.mk _ ((structureSheaf K E M).presheaf.germ W₁ z.1 hzW a) := by
  obtain ⟨U₁, hz₁, i₁, W₁, a, h⟩ := s.2 z₀
  refine ⟨U₁, hz₁, W₁, a, fun z hzU => ?_⟩
  obtain ⟨hw, e⟩ := h ⟨z, hzU⟩
  exact ⟨i₁.le hzU, hw, e⟩

/-- On the cosupport of `𝒥`, the stalk ideal `𝒥_z` is proper, hence contained in the maximal ideal,
which is the kernel of evaluation. -/
theorem eval_eq_zero_of_mem_stalkIdeal (J : IdealSheaf (structureSheaf K E M)) (z : support XM J)
    {a : (structureSheaf K E M).presheaf.stalk (z.1 : M)} (ha : a ∈ J.stalkIdeal z.1) :
    Manifold.eval K E M z.1 a = 0 := by
  have hJ : J.stalkIdeal z.1 ≠ ⊤ := z.2
  exact (mem_maximalIdeal_iff_eval E a).mp (IsLocalRing.le_maximalIdeal hJ ha)

/-- Evaluation at `z` on the fibre `𝒪_{M,z}/𝒥_z` of a point of the cosupport. -/
def fiberEval (J : IdealSheaf (structureSheaf K E M)) (z : support XM J) : fiber XM J z →+* K :=
  Ideal.Quotient.lift (J.stalkIdeal z.1) (Manifold.eval K E M z.1) fun _ ha =>
    eval_eq_zero_of_mem_stalkIdeal J z ha

theorem fiberEval_mk_germ (J : IdealSheaf (structureSheaf K E M)) (z : support XM J) (W : Opens M)
    (hz : z.1 ∈ W) (a : (structureSheaf K E M).presheaf.obj (op W)) :
    fiberEval J z (Ideal.Quotient.mk _ ((structureSheaf K E M).presheaf.germ W z.1 hz a)) =
      a ⟨z.1, hz⟩ :=
  contMDiffSheafCommRing.eval_germ 𝓘(K, E) 𝓘(K) ω M K W z.1 hz a

variable {n : ℕ} {ψ : E ≃L[K] (Fin n → K)} {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c)

/-- The ideal sheaf `𝓘_Y` of the closed submanifold, read as an ideal sheaf on the locally ringed
space `Sp(M)` (the same term; the retyping lets the quotient constructions apply). Internal to the
construction: the exported `closedHom`, `closedHom_comp_quotientι`, `closedSubmanifoldIso` and
`toFun_closedSubmanifoldIso_hom_comp` are typed with `hY.idealSheaf`. -/
abbrev idealSheafSp : IdealSheaf (XM).𝒪 := hY.idealSheaf

local notation "𝓙" => idealSheafSp hY

/-- The points of a closed submanifold are the cosupport of its ideal sheaf. -/
def closedBaseHomeo : Y ≃ₜ support XM 𝓙 where
  toFun y := ⟨y.1, hY.cosupport_idealSheaf.symm.subset y.2⟩
  invFun z := ⟨z.1, hY.cosupport_idealSheaf.subset z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The base map `Y → S(𝓘_Y)` of the comparison morphism. -/
def closedBase : TopCat.of Y ⟶ support XM 𝓙 :=
  TopCat.ofHom ⟨closedBaseHomeo hY, (closedBaseHomeo hY).continuous⟩

theorem closedBase_apply (y : Y) : (closedBase hY y).1 = (y : M) := rfl

/-- The function on `Y ∩ V` underlying the image of a section of the quotient sheaf over `V`:
the evaluation of its classes. -/
def closedSectionFun (V : Opens (support XM 𝓙)) (s : (presheafCommRing XM 𝓙).obj (op V))
    (y : (Opens.map (closedBase hY)).obj V) : K :=
  fiberEval 𝓙 (closedBase hY y.1) (s.1 ⟨closedBase hY y.1, y.2⟩)

/-- The evaluated family is analytic on `Y ∩ V`: near each point it is the restriction to `Y` of the
ambient section representing the family. -/
theorem contMDiff_closedSectionFun (V : Opens (support XM 𝓙))
    (s : (presheafCommRing XM 𝓙).obj (op V)) :
    letI := hY.chartedSpace
    ContMDiff 𝓘(K, Fin (n - c) → K) 𝓘(K) ω (closedSectionFun hY V s) := by
  let _i := hY.chartedSpace
  intro y₀
  obtain ⟨U₁, hz₁, W₁, a, h⟩ := exists_local_rep 𝓙 V s ⟨closedBase hY y₀.1, y₀.2⟩
  have hw₀ : (y₀.1 : M) ∈ W₁ := (h _ hz₁).2.1
  have hg : ContMDiffAt 𝓘(K, Fin (n - c) → K) 𝓘(K) ω
      (fun y : (Opens.map (closedBase hY)).obj V => extendSection K E a (y.1 : M)) y₀ :=
    ((contMDiffOn_extendSection a).contMDiffAt (W₁.2.mem_nhds hw₀)).comp y₀
      (hY.contMDiff_val.comp contMDiff_subtype_val).contMDiffAt
  refine hg.congr_of_eventuallyEq ?_
  have hopen : IsOpen {y : (Opens.map (closedBase hY)).obj V | closedBase hY y.1 ∈ U₁} :=
    U₁.2.preimage ((closedBase hY).hom.continuous.comp continuous_subtype_val)
  filter_upwards [hopen.mem_nhds hz₁] with y hy
  obtain ⟨hyV, hyW, e⟩ := h _ hy
  have hyW' : (y.1 : M) ∈ W₁ := hyW
  change fiberEval 𝓙 (closedBase hY y.1) (s.1 ⟨closedBase hY y.1, hyV⟩) =
    extendSection K E a (y.1 : M)
  rw [e, fiberEval_mk_germ 𝓙 (closedBase hY y.1) W₁ hyW a, extendSection_of_mem K E a hyW']
  rfl

/-- The sheaf map of the comparison morphism, `𝒪_M/𝓘_Y ⟶ 𝒪_Y` on `Y = S(𝓘_Y)`: a compatible family
of classes goes to its evaluation. -/
def closedSheafHom :
    letI := hY.chartedSpace
    (quotientSpace XM 𝓙).presheaf ⟶
      (closedBase hY) _* (structureSheaf K (Fin (n - c) → K) Y).presheaf :=
  letI := hY.chartedSpace
  { app := fun (V : (Opens (support XM 𝓙))ᵒᵖ) => CommRingCat.ofHom
      { toFun := fun s =>
          ⟨closedSectionFun hY (unop V) s, contMDiff_closedSectionFun hY (unop V) s⟩
        map_one' := ContMDiffMap.ext fun y => map_one (fiberEval 𝓙 (closedBase hY y.1))
        map_mul' := fun _ _ =>
          ContMDiffMap.ext fun y => map_mul (fiberEval 𝓙 (closedBase hY y.1)) _ _
        map_zero' := ContMDiffMap.ext fun y => map_zero (fiberEval 𝓙 (closedBase hY y.1))
        map_add' := fun _ _ =>
          ContMDiffMap.ext fun y => map_add (fiberEval 𝓙 (closedBase hY y.1)) _ _ }
    naturality := fun _ _ _ => rfl }

/-- (Implementation.) The morphism of presheafed spaces `Sp(Y) ⟶ Sp(M)/𝓘_Y`. -/
def closedHomAux :
    letI := hY.chartedSpace
    (ofManifold K (Fin (n - c) → K) Y).toPresheafedSpace ⟶ (quotientSpace XM 𝓙).toPresheafedSpace :=
  letI := hY.chartedSpace
  { base := closedBase hY
    c := closedSheafHom hY }

/-- **The fibre `𝒪_{M,y}/𝓘_{Y,y}` maps to `𝒪_{Y,y}`** by the restriction of germs, `𝓘_{Y,y}` being
its kernel. -/
def fiberRestrict (y : Y) : fiber XM 𝓙 (closedBase hY y) →+* hY.stalk y :=
  Ideal.Quotient.lift (hY.idealSheaf.stalkIdeal (y : M)) (hY.restrictStalk y) fun a ha => by
    have ha' : a ∈ hY.idealSheaf.stalkIdeal (y : M) := ha
    rw [hY.stalkIdeal_idealSheaf_of_mem y.2] at ha'
    exact RingHom.mem_ker.mp ha'

/-- The induced map `𝒪_{M,y}/𝓘_{Y,y} → 𝒪_{Y,y}` is a bijection: `restrictStalk` is onto with kernel
`𝓘_{Y,y}`. -/
theorem bijective_fiberRestrict (y : Y) : Function.Bijective (fiberRestrict hY y) := by
  refine ⟨RingHom.lift_injective_of_ker_le_ideal _ _ fun a ha => ?_,
    Ideal.Quotient.lift_surjective_of_surjective _ _ (hY.restrictStalk_surjective y)⟩
  change a ∈ hY.idealSheaf.stalkIdeal (y : M)
  rw [hY.stalkIdeal_idealSheaf_of_mem y.2]
  exact ha

/-- **The stalk map of the comparison morphism is the restriction of germs** through the
identification `𝒪_{Sp(M)/𝓘_Y, y} ≃ 𝒪_{M,y}/𝓘_{Y,y}` (`stalkEquiv`). -/
theorem stalkMap_closedHomAux_eq (y : Y)
    (σ : (quotientSpace XM 𝓙).presheaf.stalk (closedBase hY y)) :
    letI := hY.chartedSpace
    (closedHomAux hY).stalkMap y σ = fiberRestrict hY y (evalHom XM 𝓙 (closedBase hY y) σ) := by
  let _i := hY.chartedSpace
  obtain ⟨V, hz, s, rfl⟩ := (presheafCommRing XM 𝓙).exists_germ_eq σ
  have hz' : y ∈ (Opens.map (closedBase hY)).obj V := hz
  set sec : (structureSheaf K (Fin (n - c) → K) Y).presheaf.obj
      (op ((Opens.map (closedBase hY)).obj V)) :=
    ⟨closedSectionFun hY V s, contMDiff_closedSectionFun hY V s⟩ with hsec
  have h1 : (closedHomAux hY).stalkMap y ((presheafCommRing XM 𝓙).germ V (closedBase hY y) hz s) =
      (structureSheaf K (Fin (n - c) → K) Y).presheaf.germ ((Opens.map (closedBase hY)).obj V) y
        hz' sec :=
    PresheafedSpace.stalkMap_germ_apply (closedHomAux hY) V y hz s
  have h2 : evalHom XM 𝓙 (closedBase hY y)
      ((presheafCommRing XM 𝓙).germ V (closedBase hY y) hz s) = s.1 ⟨closedBase hY y, hz⟩ :=
    evalHom_germ XM 𝓙 V (closedBase hY y) hz s
  rw [h1, h2]
  obtain ⟨U₁, hz₁, W₁, a, h⟩ := exists_local_rep 𝓙 V s ⟨closedBase hY y, hz⟩
  obtain ⟨hyV, hyW, e⟩ := h _ hz₁
  have hyW' : (y : M) ∈ W₁ := hyW
  rw [e]
  apply stalkToGerm_injective 𝓘(K, Fin (n - c) → K) ω Y y
  change _ = stalkToGerm 𝓘(K, Fin (n - c) → K) ω Y y
    (hY.restrictStalk y ((structureSheaf K E M).presheaf.germ W₁ (y : M) hyW' a))
  have hr := hY.isRestrictStalk_restrictStalk y W₁ hyW' a
  rw [hr, stalkToGerm_structureSheaf_germ]
  refine Filter.Germ.coe_eq.mpr ?_
  have hopen : IsOpen {y' : Y | closedBase hY y' ∈ U₁} :=
    U₁.2.preimage (closedBase hY).hom.continuous
  filter_upwards [hopen.mem_nhds hz₁] with y' hy'
  obtain ⟨hy'V, hy'W, e'⟩ := h _ hy'
  have hy'V' : y' ∈ (Opens.map (closedBase hY)).obj V := hy'V
  have hy'W' : (y' : M) ∈ W₁ := hy'W
  change extendSection K (Fin (n - c) → K) sec y' = extendSection K E a (y' : M)
  rw [extendSection_of_mem K _ sec hy'V', extendSection_of_mem K E a hy'W']
  change fiberEval 𝓙 (closedBase hY y') (s.1 ⟨closedBase hY y', hy'V⟩) = a ⟨(y' : M), hy'W'⟩
  rw [e', fiberEval_mk_germ 𝓙 (closedBase hY y') W₁ hy'W a]
  rfl

theorem bijective_stalkMap_closedHomAux (y : Y) :
    letI := hY.chartedSpace
    Function.Bijective ((closedHomAux hY).stalkMap y).hom := by
  let _i := hY.chartedSpace
  have h : ((closedHomAux hY).stalkMap y).hom =
      (fiberRestrict hY y).comp (stalkEquiv XM 𝓙 (closedBase hY y)).toRingHom :=
    RingHom.ext fun σ => stalkMap_closedHomAux_eq hY y σ
  rw [h]
  exact (bijective_fiberRestrict hY y).comp (stalkEquiv XM 𝓙 _).bijective

theorem isLocalHom_stalkMap_closedHomAux (y : Y) :
    letI := hY.chartedSpace
    IsLocalHom ((closedHomAux hY).stalkMap y).hom := by
  let _i := hY.chartedSpace
  exact IsLocalHom.of_surjective _ (bijective_stalkMap_closedHomAux hY y).2

/-- (Implementation.) The morphism of locally ringed spaces `Sp(Y) ⟶ Sp(M)/𝓘_Y`. -/
def closedHomL :
    letI := hY.chartedSpace
    (ofManifold K (Fin (n - c) → K) Y).toLocallyRingedSpace ⟶ quotientSpace XM 𝓙 :=
  letI := hY.chartedSpace
  ⟨closedHomAux hY, fun y => isLocalHom_stalkMap_closedHomAux hY y⟩

theorem closedHomL_Γ_algebraMap (r : K) :
    letI := hY.chartedSpace
    (LocallyRingedSpace.Γ.map (closedHomL hY).op).hom
        (((ofManifold K E M).quotient 𝓙).algebraMap r) =
      constHom K (Fin (n - c) → K) Y r := by
  let _i := hY.chartedSpace
  apply ContMDiffMap.ext
  intro y
  exact fiberEval_mk_germ 𝓙 (closedBase hY y.1) ⊤ trivial (constSection K E M r)

/-- **The comparison `K`-morphism `Sp(Y) ⟶ Sp(M)/𝓘_Y`**: the identification of `Y` with `S(𝓘_Y)` on
points, evaluation of classes on sections. -/
def closedHom :
    letI := hY.chartedSpace
    ofManifold K (Fin (n - c) → K) Y ⟶
      (ofManifold K E M).quotient (hY.idealSheaf : IdealSheaf (XM).𝒪) :=
  letI := hY.chartedSpace
  ⟨closedHomL hY, RingHom.ext fun r => closedHomL_Γ_algebraMap hY r⟩

/-- The comparison morphism followed by the canonical morphism `Sp(M)/𝓘_Y ⟶ Sp(M)` is `Sp` of the
inclusion `Y → M` (a morphism into `Sp(M)` is determined by its points, `hom_ext_baseFun`). -/
theorem closedHom_comp_quotientι [IsManifold 𝓘(K, E) ω M] :
    letI := hY.chartedSpace
    closedHom hY ≫ quotientι (ofManifold K E M) (hY.idealSheaf : IdealSheaf (XM).𝒪) =
      ofManifoldHom (Subtype.val : Y → M) hY.contMDiff_val := by
  let _i := hY.chartedSpace
  have _j := hY.isManifold'
  exact hom_ext_baseFun (ContinuousLinearEquiv.refl K (Fin (n - c) → K)) ψ _ _
    (funext fun _ => rfl)

theorem isIso_closedHomAux_base :
    letI := hY.chartedSpace
    IsIso (closedHomAux hY).base := by
  let _i := hY.chartedSpace
  have h : (closedHomAux hY).base = (TopCat.isoOfHomeo (closedBaseHomeo hY)).hom := by
    ext x
    rfl
  rw [h]
  infer_instance

theorem isIso_closedHomAux_c :
    letI := hY.chartedSpace
    IsIso (closedHomAux hY).c := by
  let _i := hY.chartedSpace
  let G : TopCat.Sheaf CommRingCat.{u} (support XM 𝓙) :=
    (TopCat.Sheaf.pushforward CommRingCat.{u} (closedBase hY)).obj
      (structureSheaf K (Fin (n - c) → K) Y)
  let φ : sheafCommRing XM 𝓙 ⟶ G := ⟨(closedHomAux hY).c⟩
  have hstalk : ∀ z : support XM 𝓙,
      IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map φ.hom) := by
    intro z
    obtain ⟨y, rfl⟩ : ∃ y, closedBase hY y = z :=
      ⟨(closedBaseHomeo hY).symm z, (closedBaseHomeo hY).apply_symm_apply z⟩
    have hpush : IsIso ((ofManifold K (Fin (n - c) → K) Y).presheaf.stalkPushforward
        CommRingCat.{u} (closedHomAux hY).base y) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing _
        (closedBaseHomeo hY).isInducing _ y
    have hmap : IsIso ((closedHomAux hY).stalkMap y) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_stalkMap_closedHomAux hY y)
    change IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} ((closedHomAux hY).base y)).map
      φ.hom)
    exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ hpush hmap rfl
  have : IsIso φ := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso φ
  exact Functor.map_isIso (TopCat.Sheaf.forget CommRingCat.{u} (support XM 𝓙)) φ

/-- **The comparison morphism is an isomorphism**: a homeomorphism on points, an isomorphism on
every stalk. -/
theorem isIso_closedHom :
    letI := hY.chartedSpace
    IsIso (closedHom hY) := by
  let _i := hY.chartedSpace
  have h1 : IsIso (closedHomAux hY) := by
    have := isIso_closedHomAux_base hY
    have := isIso_closedHomAux_c hY
    exact PresheafedSpace.isIso_of_components _
  have h2 : IsIso (LocallyRingedSpace.forgetToSheafedSpace.map (closedHomL hY)) := by
    have : IsIso (SheafedSpace.forgetToPresheafedSpace.map
        (LocallyRingedSpace.forgetToSheafedSpace.map (closedHomL hY))) := h1
    exact isIso_of_reflects_iso _ SheafedSpace.forgetToPresheafedSpace
  have h3 : IsIso (closedHomL hY) :=
    isIso_of_reflects_iso _ LocallyRingedSpace.forgetToSheafedSpace
  have h4 : IsIso (closedHom hY).1 := h3
  exact isIso_of_isIso_val _

/-- **`Sp(Y) ≅ Sp(M)/𝓘_Y`**, the `K`-isomorphism given by the comparison morphism. -/
def closedSubmanifoldIso :
    letI := hY.chartedSpace
    KIso (ofManifold K (Fin (n - c) → K) Y)
      ((ofManifold K E M).quotient (hY.idealSheaf : IdealSheaf (XM).𝒪)) :=
  letI := hY.chartedSpace
  haveI := isIso_closedHom hY
  asIso (closedHom hY)

theorem toFun_closedSubmanifoldIso_hom_comp [IsManifold 𝓘(K, E) ω M] (y : Y) :
    letI := hY.chartedSpace
    Hom.toFun ((closedSubmanifoldIso hY).hom ≫
      quotientι (ofManifold K E M) (hY.idealSheaf : IdealSheaf (XM).𝒪)) y = (y : M) := by
  let _i := hY.chartedSpace
  change Hom.toFun (closedHom hY ≫ quotientι (ofManifold K E M) 𝓙) y = _
  rw [closedHom_comp_quotientι]
  rfl

end KLocallyRingedSpace

open KLocallyRingedSpace

variable {K : Type} [RCLike K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {n : ℕ}
  (ψ : E ≃L[K] (Fin n → K))

/-- **`Sp` sends a closed submanifold `Y` to the closed subspace of `Sp(M)` cut out by its ideal
sheaf**, compatibly with the inclusion on points. -/
theorem toSpace_closedSubmanifold (M : AnalyticManifold.{u} K E) {Y : Set M}
    {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) :
    letI := hY.chartedSpace
    ∃ e : KIso (ofManifold K (Fin (n - c) → K) Y)
        ((toSpace ψ M).toKLocallyRingedSpace.quotient hY.idealSheaf),
      ∀ y : Y, KLocallyRingedSpace.Hom.toFun (e.hom ≫ quotientι _ _) y = (y : M) :=
  ⟨closedSubmanifoldIso hY, fun y => toFun_closedSubmanifoldIso_hom_comp hY y⟩

/-- **`Sp(Y) ≅ Sp(M)/𝓘_Y` composed with the canonical morphism is `Sp` of the inclusion**: the
morphism form of `toSpace_closedSubmanifold`. -/
theorem toSpace_closedSubmanifold_comp (M : AnalyticManifold.{u} K E)
    {Y : Set M}
    {c : ℕ} (hY : IsClosedSubmanifold ψ Y c) :
    letI := hY.chartedSpace
    ∃ e : KIso (ofManifold K (Fin (n - c) → K) Y)
        ((toSpace ψ M).toKLocallyRingedSpace.quotient hY.idealSheaf),
      (e.hom ≫ quotientι _ _ : ofManifold K (Fin (n - c) → K) Y ⟶ ofManifold K E M) =
        ofManifoldHom (Subtype.val : Y → M) hY.contMDiff_val :=
  ⟨closedSubmanifoldIso hY, closedHom_comp_quotientι hY⟩

end AnalyticSpace
