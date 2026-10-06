/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Manifold.Stratum
public import Hironaka.AnalyticSpace.Manifold.Chart
public import Hironaka.AnalyticSpace.Manifold.Defs
public import Hironaka.AnalyticSpace.RegEval
import Hironaka.AnalyticSpace.Glue
import Hironaka.AnalyticSpace.IsoCriterion
import Hironaka.AnalyticSpace.Manifold.FullyFaithful
import Hironaka.Manifold.Sheaf.LocalRing
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The stratum of a non-singular analytic space is the space of its manifold

With `X_d` the stratum of dimension `d` of a non-singular analytic `K`-space `X`, an analytic
manifold by `Hironaka.AnalyticSpace.Manifold.Stratum`, the comparison morphism `Sp(X_d) ⟶ X | X_d`
(`stratumHom`) is the identity on points and sends a section `s` of `𝒪_X` to the function
`y ↦ ev_y(s_y)` of its values at the simple points (`regEval`, `Hironaka.AnalyticSpace.RegEval`),
which is analytic because through a chart `e : (G', 𝒜_{G'}) ≅ X | V` it is the chart pullback `e^*
s` composed with the chart (`regEval_germ`, `contMDiff_stratumFun`). Its stalk maps are local
(evaluation is preserved, `eval_stalkMap_stratumHomAux`) and it respects the constants. It is an
isomorphism (`isIso_stratumHom`, `stratumKIso : Sp(X_d) ≅ X | X_d`) because on every chart domain
`V_x` it agrees, by the extensionality of morphisms between spaces of manifolds on their underlying
maps (`hom_ext_baseFun`), with the composite of the known isomorphisms
`Sp(X_d) | V_x ≅ Sp(V_x) ≅ Sp(G'_x) ≅ X | V_x` (`stratumCompare_eq`), so that its stalk maps are
isomorphisms and the stalk criterion applies.

The three closing theorems state the result in set-theoretic form: `isOpen_setOf_ringKrullDim_eq`,
`iUnion_setOf_ringKrullDim_eq_univ`, and `exists_manifold_of_isNonsingular`, which says that every
stratum of a non-singular analytic space is `K`-isomorphic to the space of an analytic manifold
modelled on `K^d`. This is Hironaka's description of the non-singular analytic spaces as those
locally isomorphic to some `(G, 𝒜_G)` [Hir64, Ch. 0, §1, p. 121] and Bierstone–Milman's "every
smooth space is a manifold" [BM97, (3.8)(2)]; it is how the manifold-level theorems of the analytic
strand are applied to the non-singular analytic spaces of the analytic-space main theorem.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AnalyticSpace.KLocallyRingedSpace Manifold
open scoped Manifold ContDiff Topology

universe u

noncomputable section

namespace AnalyticSpace

variable {K : Type} [RCLike K] (X : AnalyticSpace.{u} K) (hX : X.IsNonsingular) (d : ℕ)

/-- The image in `X` of an open of the stratum. -/
abbrev stratumImage (W : Opens (dimOpens X hX d)) : Opens X :=
  (Opens.isOpenEmbedding (dimOpens X hX d)).isOpenMap.functor.obj W

theorem mem_stratumImage {W : Opens (dimOpens X hX d)} (y : W) : y.1.1 ∈ stratumImage X hX d W :=
  ⟨y.1, y.2, rfl⟩

/-- The evaluation at a point `y` of the stratum of the sections over (the image of) an open
`W ∋ y` of the stratum: `s ↦ ev_y(s_y)`, a ring homomorphism. -/
def stratumEval (W : Opens (dimOpens X hX d)) (y : W) :
    X.toLocallyRingedSpace.presheaf.obj (op (stratumImage X hX d W)) →+* K :=
  (regEval X (mem_reg_of_isNonsingular X hX y.1.1)).comp
    (X.toLocallyRingedSpace.presheaf.germ (stratumImage X hX d W) y.1.1
      (mem_stratumImage X hX d y)).hom

/-- **The function of a section** `s` of `𝒪_X` over (the image of) an open `W` of the stratum:
`y ↦ ev_y(s_y)`. -/
def stratumFun (W : Opens (dimOpens X hX d))
    (s : X.toLocallyRingedSpace.presheaf.obj (op (stratumImage X hX d W))) (y : W) : K :=
  stratumEval X hX d W y s

variable {X hX d}

/-- The chart formula: at the point `e_x(q)` of the stratum the function of `s` is the value at `q`
of the chart pullback of `s`. -/
theorem stratumFun_chartPt (W : Opens (dimOpens X hX d))
    (s : X.toLocallyRingedSpace.presheaf.obj (op (stratumImage X hX d W))) (x : dimOpens X hX d)
    (q : analyticSpaceOfOpen K d (chartG X hX d x)) (hq : chartPt x q ∈ W) :
    stratumFun X hX d W s ⟨chartPt x q, hq⟩ =
      extendSection K (Kn.{u} K d) (sectionViaChart X (chartE X hX d x) (stratumImage X hX d W) s)
        q.1 :=
  regEval_germ X (chartE X hX d x) q (stratumImage X hX d W) (mem_stratumImage X hX d ⟨_, hq⟩) s

/-- The chart at `x` writes a point `w` of `V_x` as `e_x(q)`, `q = e_x⁻¹(w)`. -/
theorem chartPt_symm (x : dimOpens X hX d) (w : dimOpens X hX d) (hw : w.1 ∈ chartV X hX d x) :
    chartPt x ((chartHomeo X hX d x).symm ⟨w.1, hw⟩) = w := by
  apply Subtype.ext
  change ((chartE X hX d x).hom.1.base ((chartHomeo X hX d x).symm ⟨w.1, hw⟩)).1 = w.1
  exact congrArg Subtype.val ((chartHomeo X hX d x).apply_symm_apply ⟨w.1, hw⟩)

theorem up_stratumCoord (x : dimOpens X hX d) (w : dimOpens X hX d) (hw : w.1 ∈ chartV X hX d x) :
    (ULift.up (stratumCoord x w hw) : Kn.{u} K d) = ((chartHomeo X hX d x).symm ⟨w.1, hw⟩).1 :=
  ULift.up_down _

/-- **The function of a section is analytic**: near `x` it is the chart pullback of `s`, an analytic
function on an open subset of `K^d`, composed with the chart. -/
theorem contMDiff_stratumFun (W : Opens (dimOpens X hX d))
    (s : X.toLocallyRingedSpace.presheaf.obj (op (stratumImage X hX d W))) :
    ContMDiff 𝓘(K, Fin d → K) 𝓘(K) ω (stratumFun X hX d W s) := by
  intro y₀
  set x := y₀.1 with hx
  set a := sectionViaChart X (chartE X hX d x) (stratumImage X hX d W) s with ha
  set q₀ := (chartHomeo X hX d x).symm ⟨x.1, mem_chartV X hX d x⟩ with hq₀
  -- the open of `K^d` on which the chart pullback lives
  set U' : Opens (Kn.{u} K d) := (Opens.isOpenEmbedding
    (X := (affine K d).toLocallyRingedSpace.toTopCat) (chartG X hX d x)).isOpenMap.functor.obj
    ((Opens.map (chartE X hX d x).hom.1.base).obj
      ((Opens.map (ofRestrict X.toKLocallyRingedSpace (chartV X hX d x)).1.base).obj
        (stratumImage X hX d W))) with hU'
  have hq₀W : chartPt x q₀ ∈ W := by
    rw [chartPt_symm]
    exact y₀.2
  have hq₀U' : q₀.1 ∈ U' := ⟨q₀, ⟨chartPt x q₀, hq₀W, rfl⟩, rfl⟩
  -- the analytic function `extendSection a ∘ up ∘ chart ∘ val` near `y₀`
  have hg : ContMDiffAt 𝓘(K, Fin d → K) 𝓘(K) ω (fun y : W =>
      extendSection K (Kn.{u} K d) a (ULift.up (chartAt (Fin d → K) x y.1))) y₀ := by
    have h1 : ContMDiffAt 𝓘(K, Kn.{u} K d) 𝓘(K) ω (extendSection K (Kn.{u} K d) a) q₀.1 :=
      (contMDiffOn_extendSection a).contMDiffAt (U'.2.mem_nhds hq₀U')
    have h2 : ContMDiff 𝓘(K, Fin d → K) 𝓘(K, Kn.{u} K d) ω
        (fun z : Fin d → K => (ULift.up z : Kn.{u} K d)) :=
      ((ContinuousLinearEquiv.ulift.symm : (Fin d → K) ≃L[K] Kn.{u} K d) :
        (Fin d → K) →L[K] Kn.{u} K d).contMDiff
    have h3 : ContMDiffAt 𝓘(K, Fin d → K) 𝓘(K, Fin d → K) ω
        (fun y : W => chartAt (Fin d → K) x y.1) y₀ :=
      (contMDiffOn_chart (x := x)).contMDiffAt
        ((chartAt (Fin d → K) x).open_source.mem_nhds (mem_chart_source _ x)) |>.comp y₀
        contMDiff_subtype_val.contMDiffAt
    have hq₀' : (ULift.up (chartAt (Fin d → K) x x) : Kn.{u} K d) = q₀.1 := by
      rw [chartAt_eq, stratumChart_apply x (mem_chartV X hX d x)]
      exact up_stratumCoord x x (mem_chartV X hX d x)
    have h1' : ContMDiffAt 𝓘(K, Kn.{u} K d) 𝓘(K) ω (extendSection K (Kn.{u} K d) a)
        (ULift.up (chartAt (Fin d → K) x x)) := by
      rw [hq₀']
      exact h1
    exact h1'.comp y₀ (h2.contMDiffAt.comp y₀ h3)
  refine hg.congr_of_eventuallyEq ?_
  have hopen : IsOpen {y : W | y.1.1 ∈ chartV X hX d x} :=
    (chartV X hX d x).2.preimage (continuous_subtype_val.comp continuous_subtype_val)
  filter_upwards [hopen.mem_nhds (mem_chartV X hX d x)] with y hy
  have hyV : y.1.1 ∈ chartV X hX d x := hy
  set q := (chartHomeo X hX d x).symm ⟨y.1.1, hyV⟩ with hq
  have hyq : y = ⟨chartPt x q, by rw [chartPt_symm]; exact y.2⟩ := by
    apply Subtype.ext
    exact (chartPt_symm x y.1 hyV).symm
  rw [hyq, stratumFun_chartPt W s x q]
  change extendSection K (Kn.{u} K d) a q.1 =
    extendSection K (Kn.{u} K d) a (ULift.up (chartAt (Fin d → K) x (chartPt x q)))
  congr 1
  rw [chartAt_eq, stratumChart_apply x ((chartE X hX d x).hom.1.base q).2,
    stratumCoord_chartPt x q, ULift.up_down]

variable (X hX d)

/-- The stratum's space of the bundled manifold `stratumManifold`. -/
abbrev stratumSpace : KLocallyRingedSpace.{u} K :=
  ofManifold K (Fin d → K) (dimOpens X hX d)

/-- The open subspace `X | X_d`. -/
abbrev stratumRestrict : KLocallyRingedSpace.{u} K :=
  X.toKLocallyRingedSpace.restrictOpen (dimOpens X hX d)

/-- **The sheaf map of the comparison morphism**: a section of `𝒪_X` goes to the function of its
values. -/
def stratumSheafHom :
    (stratumRestrict X hX d).toLocallyRingedSpace.presheaf ⟶
      (𝟙 (TopCat.of (dimOpens X hX d))) _* (structureSheaf K (Fin d → K) (dimOpens X hX d)).presheaf
    where
  app W := CommRingCat.ofHom
    { toFun := fun s => ⟨fun y => stratumFun X hX d (unop W) s ⟨y.1, y.2⟩,
        (contMDiff_stratumFun (unop W) s).comp
          ((contMDiff_subtypeVal_comp_iff' _).mp contMDiff_subtype_val)⟩
      map_one' := ContMDiffMap.ext fun y => map_one (stratumEval X hX d (unop W) ⟨y.1, y.2⟩)
      map_mul' := fun _ _ =>
        ContMDiffMap.ext fun y => map_mul (stratumEval X hX d (unop W) ⟨y.1, y.2⟩) _ _
      map_zero' := ContMDiffMap.ext fun y => map_zero (stratumEval X hX d (unop W) ⟨y.1, y.2⟩)
      map_add' := fun _ _ =>
        ContMDiffMap.ext fun y => map_add (stratumEval X hX d (unop W) ⟨y.1, y.2⟩) _ _ }
  naturality W W' i := by
    ext s
    apply ContMDiffMap.ext
    intro y
    change regEval X _ (X.toLocallyRingedSpace.presheaf.germ (stratumImage X hX d (unop W')) y.1.1
        (mem_stratumImage X hX d ⟨y.1, y.2⟩) (X.toLocallyRingedSpace.presheaf.map
          ((Opens.isOpenEmbedding (dimOpens X hX d)).isOpenMap.functor.map i.unop).op s)) =
      regEval X _ (X.toLocallyRingedSpace.presheaf.germ (stratumImage X hX d (unop W)) y.1.1
        (mem_stratumImage X hX d ⟨y.1, i.unop.le y.2⟩) s)
    exact congrArg (regEval X (mem_reg_of_isNonsingular X hX y.1.1))
      (TopCat.Presheaf.germ_res_apply X.toLocallyRingedSpace.presheaf
        ((Opens.isOpenEmbedding (dimOpens X hX d)).isOpenMap.functor.map i.unop) y.1.1
        (mem_stratumImage X hX d ⟨y.1, y.2⟩) s)

/-- (Implementation.) The morphism of presheafed spaces `Sp(X_d) ⟶ X | X_d`: the identity on points,
evaluation on sections. -/
def stratumHomAux :
    (stratumSpace X hX d).toPresheafedSpace ⟶ (stratumRestrict X hX d).toPresheafedSpace where
  base := 𝟙 _
  c := stratumSheafHom X hX d

/-- The evaluation at a point `y` of the stratum on the stalk of the open subspace `X | X_d`. -/
def stratumRegEval (y : dimOpens X hX d) :
    (stratumRestrict X hX d).toLocallyRingedSpace.presheaf.stalk y →+* K :=
  (regEval X (mem_reg_of_isNonsingular X hX y.1)).comp
    (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding (dimOpens X hX d)) y).hom.hom

theorem isLocalHom_stratumRegEval (y : dimOpens X hX d) : IsLocalHom (stratumRegEval X hX d y) := by
  have h1 := isLocalHom_regEval X (mem_reg_of_isNonsingular X hX y.1)
  set ρ := X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding (dimOpens X hX d)) y
    with hρ
  have h2 : IsLocalHom ρ.hom.hom := ⟨fun a ha => by
    have h := ha.map ρ.inv.hom
    have e : ρ.inv.hom (ρ.hom.hom a) = a := Iso.hom_inv_id_apply ρ a
    rw [e] at h
    exact h⟩
  exact ⟨fun a ha => h2.map_nonunit _ (h1.map_nonunit _ ha)⟩

theorem stratumRegEval_germ (W : Opens (dimOpens X hX d)) (y : dimOpens X hX d) (hy : y ∈ W)
    (s : (stratumRestrict X hX d).toLocallyRingedSpace.presheaf.obj (op W)) :
    stratumRegEval X hX d y
        ((stratumRestrict X hX d).toLocallyRingedSpace.presheaf.germ W y hy s) =
      stratumEval X hX d W ⟨y, hy⟩ s :=
  congrArg (regEval X (mem_reg_of_isNonsingular X hX y.1))
    (LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply X.toLocallyRingedSpace
      (Opens.isOpenEmbedding (dimOpens X hX d)) W y hy s)

/-- **Evaluation is preserved by the comparison morphism.** -/
theorem eval_stalkMap_stratumHomAux (y : dimOpens X hX d)
    (σ : (stratumRestrict X hX d).toLocallyRingedSpace.presheaf.stalk y) :
    Manifold.eval K (Fin d → K) (dimOpens X hX d) y (((stratumHomAux X hX d).stalkMap y).hom σ) =
      stratumRegEval X hX d y σ := by
  obtain ⟨W, hy, s, rfl⟩ :=
    (stratumRestrict X hX d).toLocallyRingedSpace.presheaf.exists_germ_eq σ
  have h1 : ((stratumHomAux X hX d).stalkMap y).hom
      ((stratumRestrict X hX d).toLocallyRingedSpace.presheaf.germ W y hy s) =
      (stratumSpace X hX d).toLocallyRingedSpace.presheaf.germ
        ((Opens.map (stratumHomAux X hX d).base).obj W) y hy
        (((stratumSheafHom X hX d).app (op W)).hom s) :=
    PresheafedSpace.stalkMap_germ_apply (stratumHomAux X hX d) W y hy s
  have h2 : Manifold.eval K (Fin d → K) (dimOpens X hX d) y
      ((structureSheaf K (Fin d → K) (dimOpens X hX d)).presheaf.germ
        ((Opens.map (stratumHomAux X hX d).base).obj W) y hy
        (((stratumSheafHom X hX d).app (op W)).hom s)) =
      stratumEval X hX d W ⟨y, hy⟩ s :=
    contMDiffSheafCommRing.eval_germ 𝓘(K, Fin d → K) 𝓘(K) ω (dimOpens X hX d) K
      ((Opens.map (stratumHomAux X hX d).base).obj W) y hy _
  rw [h1]
  exact h2.trans (stratumRegEval_germ X hX d W y hy s).symm

theorem isLocalHom_stalkMap_stratumHomAux (y : dimOpens X hX d) :
    IsLocalHom ((stratumHomAux X hX d).stalkMap y).hom := by
  refine ⟨fun σ hσ => ?_⟩
  have h1 := isLocalHom_stratumRegEval X hX d y
  apply h1.map_nonunit
  have h := eval_stalkMap_stratumHomAux X hX d y σ
  exact (congrArg IsUnit h).mp (isUnit_iff_ne_zero.mpr
    ((contMDiffSheafCommRing.isUnit_stalk_iff 𝓘(K, Fin d → K) ω _ _).mp hσ))

/-- (Implementation.) The morphism of locally ringed spaces `Sp(X_d) ⟶ X | X_d`. -/
def stratumHomL :
    (stratumSpace X hX d).toLocallyRingedSpace ⟶ (stratumRestrict X hX d).toLocallyRingedSpace :=
  ⟨stratumHomAux X hX d, fun y => isLocalHom_stalkMap_stratumHomAux X hX d y⟩

theorem stratumHomL_Γ_algebraMap (c : K) :
    (LocallyRingedSpace.Γ.map (stratumHomL X hX d).op).hom
        ((stratumRestrict X hX d).algebraMap c) =
      constHom K (Fin d → K) (dimOpens X hX d) c := by
  have ht : (stratumRestrict X hX d).algebraMap c =
      X.toLocallyRingedSpace.presheaf.map (homOfLE (le_top : stratumImage X hX d ⊤ ≤ ⊤)).op
        (X.toKLocallyRingedSpace.algebraMap c) := by
    change X.toLocallyRingedSpace.presheaf.map _ (X.toKLocallyRingedSpace.algebraMap c) = _
    rfl
  apply ContMDiffMap.ext
  intro y
  change stratumEval X hX d ⊤ ⟨y.1, y.2⟩ ((stratumRestrict X hX d).algebraMap c) = c
  rw [ht]
  change regEval X (mem_reg_of_isNonsingular X hX y.1.1)
    (X.toLocallyRingedSpace.presheaf.germ (stratumImage X hX d ⊤) y.1.1
      (mem_stratumImage X hX d ⟨y.1, y.2⟩)
      (X.toLocallyRingedSpace.presheaf.map (homOfLE (le_top : stratumImage X hX d ⊤ ≤ ⊤)).op
        (X.toKLocallyRingedSpace.algebraMap c))) = c
  exact (congrArg (regEval X (mem_reg_of_isNonsingular X hX y.1.1))
    (TopCat.Presheaf.germ_res_apply X.toLocallyRingedSpace.presheaf
      (homOfLE (le_top : stratumImage X hX d ⊤ ≤ ⊤)) y.1.1 (mem_stratumImage X hX d ⟨y.1, y.2⟩)
      (X.toKLocallyRingedSpace.algebraMap c))).trans (regEval_constAt X _ c)

/-- **The comparison `K`-morphism** `Sp(X_d) ⟶ X | X_d`. -/
def stratumHom : stratumSpace X hX d ⟶ stratumRestrict X hX d :=
  ⟨stratumHomL X hX d, RingHom.ext fun c => stratumHomL_Γ_algebraMap X hX d c⟩

theorem stratumHom_base_apply (y : dimOpens X hX d) : (stratumHom X hX d).1.base y = y :=
  rfl

/-! ### The comparison morphism is an isomorphism: comparison with `Sp(chart)` on each chart -/

section LocalIso

variable {X hX d} (x : dimOpens X hX d)

/-- The chart domain `V_x ∩ X_d` as an open of the stratum. -/
def chartOpensD : Opens (dimOpens X hX d) :=
  ⟨{w | w.1 ∈ chartV X hX d x}, (chartV X hX d x).2.preimage continuous_subtype_val⟩

theorem mem_chartOpensD {w : dimOpens X hX d} : w ∈ chartOpensD x ↔ w.1 ∈ chartV X hX d x :=
  Iff.rfl

theorem range_ofRestrict_comp_stratumHom :
    Set.range (ofRestrict (stratumSpace X hX d) (chartOpensD x) ≫ stratumHom X hX d).1.base ⊆
      Set.range (ofRestrict (stratumRestrict X hX d) (chartOpensD x)).1.base := by
  change Set.range (KLocallyRingedSpace.Hom.toFun
    (ofRestrict (stratumSpace X hX d) (chartOpensD x) ≫ stratumHom X hX d)) ⊆
    Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict (stratumRestrict X hX d) (chartOpensD x)))
  rw [Hom.range_toFun_comp, range_toFun_ofRestrict (stratumSpace X hX d) (chartOpensD x),
    range_toFun_ofRestrict (stratumRestrict X hX d) (chartOpensD x)]
  rintro _ ⟨w, hw, rfl⟩
  exact hw

/-- The restriction of the comparison morphism to a chart domain. -/
def stratumHomRestrict :
    (stratumSpace X hX d).restrictOpen (chartOpensD x) ⟶
      (stratumRestrict X hX d).restrictOpen (chartOpensD x) :=
  have h₁ : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (stratumRestrict X hX d) (chartOpensD x)).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      ((stratumRestrict X hX d).toLocallyRingedSpace.ofRestrict
        (Opens.isOpenEmbedding (chartOpensD x))))
  Hom.ofFac (ofRestrict (stratumSpace X hX d) (chartOpensD x) ≫ stratumHom X hX d)
    (ofRestrict (stratumRestrict X hX d) (chartOpensD x))
    (LocallyRingedSpace.IsOpenImmersion.lift (H := h₁)
      (ofRestrict (stratumRestrict X hX d) (chartOpensD x)).1
      (ofRestrict (stratumSpace X hX d) (chartOpensD x) ≫ stratumHom X hX d).1
      (by exact range_ofRestrict_comp_stratumHom x))
    (LocallyRingedSpace.IsOpenImmersion.lift_fac (H := h₁) _ _ _)

theorem stratumHomRestrict_comp :
    stratumHomRestrict x ≫ ofRestrict (stratumRestrict X hX d) (chartOpensD x) =
      ofRestrict (stratumSpace X hX d) (chartOpensD x) ≫ stratumHom X hX d :=
  have h₁ : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (stratumRestrict X hX d) (chartOpensD x)).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      ((stratumRestrict X hX d).toLocallyRingedSpace.ofRestrict
        (Opens.isOpenEmbedding (chartOpensD x))))
  Hom.ext (LocallyRingedSpace.IsOpenImmersion.lift_fac (H := h₁)
    (ofRestrict (stratumRestrict X hX d) (chartOpensD x)).1
    (ofRestrict (stratumSpace X hX d) (chartOpensD x) ≫ stratumHom X hX d).1
    (range_ofRestrict_comp_stratumHom x))

theorem stratumHomRestrict_base (p : (stratumSpace X hX d).restrictOpen (chartOpensD x)) :
    ((stratumHomRestrict x).1.base p).1 = p.1 :=
  congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ p) (stratumHomRestrict_comp x)

theorem imageOpens_chartOpensD :
    imageOpens (dimOpens X hX d) (chartOpensD x) = chartV X hX d x := by
  ext w
  simp only [SetLike.mem_coe]
  constructor
  · intro h
    exact ((mem_imageOpens (V := dimOpens X hX d) (T := chartOpensD x)).mp h).2
  · intro hw
    exact (mem_imageOpens (V := dimOpens X hX d) (T := chartOpensD x)).mpr
      ⟨chartV_subset X hX d x hw, hw⟩

theorem eqToIso_restrictOpen_hom_base {Y : KLocallyRingedSpace.{u} K} {U U' : Opens Y} (h : U = U')
    (p : Y.restrictOpen U) : ((eqToIso (congrArg Y.restrictOpen h)).hom.1.base p).1 = p.1 := by
  subst h
  rfl

/-- The chart domain of `X | X_d`, read as `(G'_x, 𝒜_{G'_x})` through the chart. -/
def chartRestrictIso :
    (stratumRestrict X hX d).restrictOpen (chartOpensD x) ≅
      analyticSpaceOfOpen K d (chartG X hX d x) :=
  restrictOpen_restrictOpen_iso (dimOpens X hX d) (chartOpensD x) ≪≫
    eqToIso (congrArg X.toKLocallyRingedSpace.restrictOpen (imageOpens_chartOpensD x)) ≪≫
    (chartE X hX d x).symm

theorem chartRestrictIso_hom_base (r : (stratumRestrict X hX d).restrictOpen (chartOpensD x)) :
    ((chartE X hX d x).hom.1.base ((chartRestrictIso x).hom.1.base r)).1 = r.1.1 := by
  have hI₁ : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (stratumRestrict X hX d) (chartOpensD x)).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      ((stratumRestrict X hX d).toLocallyRingedSpace.ofRestrict
        (Opens.isOpenEmbedding (chartOpensD x))))
  have hI : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (stratumRestrict X hX d) (chartOpensD x) ≫
        ofRestrict X.toKLocallyRingedSpace (dimOpens X hX d)).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      ((ofRestrict (stratumRestrict X hX d) (chartOpensD x)).1 ≫
        (ofRestrict X.toKLocallyRingedSpace (dimOpens X hX d)).1))
  have h1 := congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ r)
    (isoOfRangeEq_hom_comp
      (ofRestrict (stratumRestrict X hX d) (chartOpensD x) ≫
        ofRestrict X.toKLocallyRingedSpace (dimOpens X hX d))
      (ofRestrict X.toKLocallyRingedSpace (imageOpens (dimOpens X hX d) (chartOpensD x)))
      (by rw [range_toFun_ofRestrict]; rfl))
  change ((chartE X hX d x).hom.1.base ((chartE X hX d x).inv.1.base
    ((eqToIso (congrArg X.toKLocallyRingedSpace.restrictOpen (imageOpens_chartOpensD x))).hom.1.base
      ((restrictOpen_restrictOpen_iso (dimOpens X hX d) (chartOpensD x)).hom.1.base r)))).1 = r.1.1
  rw [KIso.hom_base_inv_base (chartE X hX d x),
    eqToIso_restrictOpen_hom_base (imageOpens_chartOpensD x)]
  exact h1

/-- The chart `V_x ∩ X_d → G'_x` as a map of the open submanifolds. -/
def chartMap : chartOpensD x → chartG X hX d x :=
  fun w => (chartHomeo X hX d x).symm ⟨w.1.1, w.2⟩

/-- The inverse chart `G'_x → V_x ∩ X_d`. -/
def chartMapInv : chartG X hX d x → chartOpensD x :=
  fun q => ⟨chartPt x q, ((chartE X hX d x).hom.1.base q).2⟩

theorem chartMap_chartInv (q : chartG X hX d x) : chartMap x (chartMapInv x q) = q := by
  change (chartHomeo X hX d x).symm ⟨(chartPt x q).1, _⟩ = q
  rw [show (⟨(chartPt x q).1, ((chartE X hX d x).hom.1.base q).2⟩ :
    X.toKLocallyRingedSpace.restrictOpen (chartV X hX d x)) = chartHomeo X hX d x q from rfl]
  exact (chartHomeo X hX d x).symm_apply_apply q

theorem chartInv_chartMap (w : chartOpensD x) : chartMapInv x (chartMap x w) = w := by
  apply Subtype.ext
  exact chartPt_symm x w.1 w.2

theorem contMDiff_ulift_up :
    ContMDiff 𝓘(K, Fin d → K) 𝓘(K, Kn.{u} K d) ω (fun z : Fin d → K => (ULift.up z : Kn.{u} K d)) :=
  ((ContinuousLinearEquiv.ulift.symm : (Fin d → K) ≃L[K] Kn.{u} K d) :
    (Fin d → K) →L[K] Kn.{u} K d).contMDiff

theorem contMDiff_ulift_down :
    ContMDiff 𝓘(K, Kn.{u} K d) 𝓘(K, Fin d → K) ω (fun w : Kn.{u} K d => w.down) :=
  ((ContinuousLinearEquiv.ulift : Kn.{u} K d ≃L[K] (Fin d → K)) :
    Kn.{u} K d →L[K] (Fin d → K)).contMDiff

theorem contMDiff_chartMap : ContMDiff 𝓘(K, Fin d → K) 𝓘(K, Kn.{u} K d) ω (chartMap x) := by
  refine (contMDiff_subtypeVal_comp_iff' _).mp ?_
  have h : (Subtype.val ∘ chartMap x : chartOpensD x → Kn.{u} K d) =
      fun w => ULift.up (chartAt (Fin d → K) x w.1) := by
    funext w
    have hw : w.1.1 ∈ chartV X hX d x := w.2
    change ((chartHomeo X hX d x).symm ⟨w.1.1, hw⟩).1 = ULift.up (chartAt (Fin d → K) x w.1)
    rw [chartAt_eq, stratumChart_apply x hw]
    exact (up_stratumCoord x w.1 hw).symm
  rw [h]
  exact contMDiff_ulift_up.comp
    ((contMDiffOn_chart (x := x)).comp_contMDiff contMDiff_subtype_val fun w => w.2)

theorem contMDiff_chartInv : ContMDiff 𝓘(K, Kn.{u} K d) 𝓘(K, Fin d → K) ω (chartMapInv x) := by
  refine (contMDiff_subtypeVal_comp_iff' _).mp ?_
  have h : (Subtype.val ∘ chartMapInv x : chartG X hX d x → dimOpens X hX d) =
      (chartAt (Fin d → K) x).symm ∘ fun q : chartG X hX d x => q.1.down := by
    funext q
    change chartPt x q = (chartAt (Fin d → K) x).symm q.1.down
    have hq : (ULift.up q.1.down : Kn.{u} K d) ∈ chartG X hX d x := by
      rw [ULift.up_down]
      exact q.2
    rw [chartAt_eq, stratumChart_symm_apply x hq]
    exact congrArg (chartPt x) (Subtype.ext (ULift.up_down _).symm)
  rw [h]
  refine (contMDiffOn_chart_symm (x := x)).comp_contMDiff
    (contMDiff_ulift_down.comp contMDiff_subtype_val) fun q => ?_
  rw [chartAt_eq, stratumChart_target]
  change (ULift.up q.1.down : Kn.{u} K d) ∈ chartG X hX d x
  rw [ULift.up_down]
  exact q.2

/-- `Sp` of the chart, a `K`-isomorphism `Sp(V_x ∩ X_d) ≅ Sp(G'_x)`. -/
def chartKIsoM :
    KIso (ofManifold K (Fin d → K) (chartOpensD x)) (ofManifold K (Kn.{u} K d) (chartG X hX d x)) :=
  ofManifoldIso (chartMap x) (chartMapInv x) (contMDiff_chartMap x) (contMDiff_chartInv x)
    (chartInv_chartMap x) (chartMap_chartInv x)

/-- The comparison morphism on the chart domain, read between `Sp(V_x ∩ X_d)` and `Sp(G'_x)`. -/
def stratumCompare :
    ofManifold K (Fin d → K) (chartOpensD x) ⟶ ofManifold K (Kn.{u} K d) (chartG X hX d x) :=
  (ofManifold_restrictOpen_iso (K := K) (E := Fin d → K) (chartOpensD x)).inv ≫
    stratumHomRestrict x ≫ (chartRestrictIso x).hom ≫
    (ofManifold_restrictOpen_iso (K := K) (E := Kn.{u} K d) (M := Kn.{u} K d) (chartG X hX d x)).hom

/-- **On a chart domain the comparison morphism is `Sp` of the chart**: the two `K`-morphisms
`Sp(V_x ∩ X_d) ⟶ Sp(G'_x)` agree on points, hence are equal (`hom_ext_baseFun`). -/
theorem stratumCompare_eq : stratumCompare x = (chartKIsoM x).hom := by
  refine hom_ext_baseFun (ContinuousLinearEquiv.refl K (Fin d → K)) ContinuousLinearEquiv.ulift _ _
    (funext fun w => ?_)
  apply Subtype.ext
  have e1 : ((ofManifold_restrictOpen_iso (K := K) (E := Fin d → K) (chartOpensD x)).inv.1.base
      w).1 = w.1 := ofManifold_restrictOpen_iso_inv_base _ w
  have e2 := stratumHomRestrict_base x
    ((ofManifold_restrictOpen_iso (K := K) (E := Fin d → K) (chartOpensD x)).inv.1.base w)
  have e3 := chartRestrictIso_hom_base x ((stratumHomRestrict x).1.base
    ((ofManifold_restrictOpen_iso (K := K) (E := Fin d → K) (chartOpensD x)).inv.1.base w))
  have e4 := ofManifold_restrictOpen_iso_hom_base (K := K) (E := Kn.{u} K d) (M := Kn.{u} K d)
    (chartG X hX d x) ((chartRestrictIso x).hom.1.base ((stratumHomRestrict x).1.base
      ((ofManifold_restrictOpen_iso (K := K) (E := Fin d → K) (chartOpensD x)).inv.1.base w)))
  change ((ofManifold_restrictOpen_iso (K := K) (E := Kn.{u} K d) (M := Kn.{u} K d)
    (chartG X hX d x)).hom.1.base ((chartRestrictIso x).hom.1.base ((stratumHomRestrict x).1.base
      ((ofManifold_restrictOpen_iso (K := K) (E := Fin d → K) (chartOpensD x)).inv.1.base w)))).1 =
    ((chartHomeo X hX d x).symm ⟨w.1.1, w.2⟩).1
  rw [e4]
  have h5 : chartHomeo X hX d x ((chartRestrictIso x).hom.1.base ((stratumHomRestrict x).1.base
      ((ofManifold_restrictOpen_iso (K := K) (E := Fin d → K) (chartOpensD x)).inv.1.base w))) =
      ⟨w.1.1, w.2⟩ := by
    apply Subtype.ext
    rw [chartHomeo_apply, e3, e2, e1]
  rw [← h5, (chartHomeo X hX d x).symm_apply_apply]

theorem isIso_stratumHomRestrict : IsIso (stratumHomRestrict x) := by
  have h1 : IsIso ((ofManifold_restrictOpen_iso (K := K) (E := Fin d → K) (chartOpensD x)).inv ≫
      stratumHomRestrict x ≫ (chartRestrictIso x).hom ≫
      (ofManifold_restrictOpen_iso (K := K) (E := Kn.{u} K d) (M := Kn.{u} K d)
        (chartG X hX d x)).hom) := by
    have : IsIso (stratumCompare x) := by
      rw [stratumCompare_eq]
      infer_instance
    exact this
  have h2 : IsIso (stratumHomRestrict x ≫ (chartRestrictIso x).hom ≫
      (ofManifold_restrictOpen_iso (K := K) (E := Kn.{u} K d) (M := Kn.{u} K d)
        (chartG X hX d x)).hom) :=
    IsIso.of_isIso_comp_left
      (ofManifold_restrictOpen_iso (K := K) (E := Fin d → K) (chartOpensD x)).inv _
  exact IsIso.of_isIso_comp_right _ ((chartRestrictIso x).hom ≫
    (ofManifold_restrictOpen_iso (K := K) (E := Kn.{u} K d) (M := Kn.{u} K d)
      (chartG X hX d x)).hom)

end LocalIso

/-- **The stalk maps of the comparison morphism are isomorphisms**: on the chart domain through `y`
the morphism is `Sp` of the chart. -/
theorem isIso_stalkMap_stratumHom (y : dimOpens X hX d) :
    IsIso ((stratumHom X hX d).1.stalkMap y) := by
  let p : (stratumSpace X hX d).restrictOpen (chartOpensD y) := ⟨y, mem_chartV X hX d y⟩
  have hΦ' : IsIso (stratumHomRestrict y).1 :=
    have := isIso_stratumHomRestrict y
    KIso.isIso_hom_val (asIso (stratumHomRestrict y))
  have hB : IsIso ((ofRestrict (stratumRestrict X hX d) (chartOpensD y)).1.stalkMap
      ((stratumHomRestrict y).1.base p)) := by
    have e : (ofRestrict (stratumRestrict X hX d) (chartOpensD y)).1.stalkMap
        ((stratumHomRestrict y).1.base p) =
        ((stratumRestrict X hX d).toLocallyRingedSpace.restrictStalkIso
          (Opens.isOpenEmbedding (X := (stratumRestrict X hX d).toLocallyRingedSpace.toTopCat)
            (chartOpensD y)) ((stratumHomRestrict y).1.base p)).inv :=
      (PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict _ _ _).symm
    rw [e]
    exact ⟨⟨_, Iso.inv_hom_id _, Iso.hom_inv_id _⟩⟩
  have hA : IsIso ((ofRestrict (stratumSpace X hX d) (chartOpensD y)).1.stalkMap p) := by
    have e : (ofRestrict (stratumSpace X hX d) (chartOpensD y)).1.stalkMap p =
        ((stratumSpace X hX d).toLocallyRingedSpace.restrictStalkIso
          (Opens.isOpenEmbedding (X := (stratumSpace X hX d).toLocallyRingedSpace.toTopCat)
            (chartOpensD y)) p).inv :=
      (PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict _ _ _).symm
    rw [e]
    exact ⟨⟨_, Iso.inv_hom_id _, Iso.hom_inv_id _⟩⟩
  have hΦ'₁ : IsIso (LocallyRingedSpace.forgetToSheafedSpace.map (stratumHomRestrict y).1) :=
    inferInstance
  have hΦ'₂ : IsIso (SheafedSpace.forgetToPresheafedSpace.map
      (LocallyRingedSpace.forgetToSheafedSpace.map (stratumHomRestrict y).1)) := inferInstance
  have hΦ'₃ : IsIso (stratumHomRestrict y).1.toShHom.hom := hΦ'₂
  have hΦ's : IsIso ((stratumHomRestrict y).1.stalkMap p) :=
    inferInstanceAs (IsIso ((stratumHomRestrict y).1.toShHom.hom.stalkMap p))
  have hL : IsIso ((stratumHomRestrict y ≫
      ofRestrict (stratumRestrict X hX d) (chartOpensD y)).1.stalkMap p) := by
    rw [Hom.comp_val, LocallyRingedSpace.stalkMap_comp]
    exact IsIso.comp_isIso' hB hΦ's
  rw [stratumHomRestrict_comp, Hom.comp_val, LocallyRingedSpace.stalkMap_comp] at hL
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hA hL

/-- **The comparison morphism is a `K`-isomorphism** (the stalk criterion; the base map is the
identity). -/
theorem isIso_stratumHom : IsIso (stratumHom X hX d) := by
  have : IsIso (stratumHom X hX d).1.1.base :=
    inferInstanceAs (IsIso (𝟙 (TopCat.of (dimOpens X hX d))))
  exact KLocallyRingedSpace.isIso_of_isIso_base_of_stalkMap_bijective (stratumHom X hX d) fun y =>
    (ConcreteCategory.isIso_iff_bijective _).mp (isIso_stalkMap_stratumHom X hX d y)

/-- **`Sp(X_d) ≅ X | X_d`.** -/
def stratumKIso : KIso (stratumSpace X hX d) (stratumRestrict X hX d) :=
  haveI := isIso_stratumHom X hX d
  asIso (stratumHom X hX d)

/-! ### The strata in set-theoretic form -/

include hX in
/-- The dimension is locally constant on a non-singular space: `isOpen_dimSet`
(`Hironaka.AnalyticSpace.Manifold.Stratum`) with `dimSet` unfolded, the set-theoretic form used in
the statement `exists_manifold_of_isNonsingular`. -/
theorem isOpen_setOf_ringKrullDim_eq :
    IsOpen {x : X |
      ringKrullDim (X.toLocallyRingedSpace.presheaf.stalk x) = ((d : ℕ) : WithBot ℕ∞)} :=
  isOpen_dimSet X hX d

include hX in
/-- The strata cover a non-singular space: `iUnion_dimSet_eq_univ`
(`Hironaka.AnalyticSpace.Manifold.Stratum`) with `dimSet` unfolded, the set-theoretic form of the
statement. -/
theorem iUnion_setOf_ringKrullDim_eq_univ :
    ⋃ d : ℕ, {x : X |
      ringKrullDim (X.toLocallyRingedSpace.presheaf.stalk x) = ((d : ℕ) : WithBot ℕ∞)} =
      Set.univ :=
  iUnion_dimSet_eq_univ X hX

include hX in
/-- **Every stratum of a non-singular analytic `K`-space is the space of an analytic manifold**
modelled on `K^d` [Hir64, Ch. 0, §1, p. 121], [BM97, (3.8)(2)]: `Sp` is essentially surjective onto
the non-singular spaces, dimension by dimension. The stratum is quantified as an open set `U` whose
carrier is the set of points of dimension `d`, so that the statement does not presuppose the
openness lemma. -/
theorem exists_manifold_of_isNonsingular :
    ∃ U : Opens X, (U : Set X) =
        {x : X | ringKrullDim (X.toLocallyRingedSpace.presheaf.stalk x) = ((d : ℕ) : WithBot ℕ∞)} ∧
      ∃ M : AnalyticManifold.{u} K (Fin d → K),
        Nonempty (KIso (toSpace (ContinuousLinearEquiv.refl K (Fin d → K)) M).toKLocallyRingedSpace
          (X.toKLocallyRingedSpace.restrictOpen U)) :=
  ⟨dimOpens X hX d, rfl, stratumManifold X hX d, ⟨stratumKIso X hX d⟩⟩

end AnalyticSpace
