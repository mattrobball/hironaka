/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.ModelIso
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.RegPoints
import Hironaka.AnalyticSpace.RegularStalk
import Hironaka.Manifold.Sheaf.LocalRing
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Evaluation at a simple point of an analytic `K`-space

At a simple point `x` of an analytic `K`-space `X` (a regular stalk),
`Hironaka/AnalyticSpace/RegPoints.lean` provides a `K`-isomorphism `e : (G', 𝒜_{G'}) ≅ X | V` of a
neighbourhood with an open of `K^d` [Hir64, Ch. 0, §1, p. 121]. Reading the stalk `𝒪_{X,x}`
through it, `𝒪_{X,x} ≅ 𝒜_{K^d, q}`, and evaluating at `q` gives a local ring homomorphism
`𝒪_{X,x} →+* K` fixing the constants (`chartEval`). Such a homomorphism is unique
(`ringHom_eq_of_isLocalHom_of_const`: for `r`, `r − (f r)` is a non-unit, hence so is its image
under any other local `g`, forcing `g r = f r`), so the evaluation `regEval` is canonical — it does
not depend on the chart — and can be computed through any chart (`chartEval_eq_regEval`); the
evaluation of the germ of a section is the value of its chart pullback (`regEval_germ`). That
the residue field of a simple point is `K` is read off a local coordination; the inference is the
library's. Routine; used by `Hironaka/AnalyticSpace/Manifold/Stratum.lean`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AnalyticSpace.KLocallyRingedSpace Manifold
open scoped Manifold ContDiff

universe u

noncomputable section


variable {K : Type} [RCLike K]

/-- A ring homomorphism `f` and a local ring homomorphism `g` from a ring `R` to the field `K` that
agree on the constants `c : K →+* R` are equal — `f` kills `r − c (f r)`, which is therefore a
non-unit, so `g` sends it to a non-unit of `K`, that is to `0`. -/
theorem AnalyticSpace.ringHom_eq_of_isLocalHom_of_const {R : Type*} [CommRing R] (c : K →+* R)
    (f g : R →+* K) [IsLocalHom g] (hf : ∀ a, f (c a) = a)
    (hg : ∀ a, g (c a) = a) : f = g := by
  ext r
  have h1 : f (r - c (f r)) = 0 := by rw [map_sub, hf, sub_self]
  have h2 : ¬ IsUnit (r - c (f r)) := fun hu => by
    have := hu.map f
    rw [h1] at this
    exact not_isUnit_zero this
  have h3 : g (r - c (f r)) = 0 := by
    by_contra hne
    exact h2 (IsLocalHom.map_nonunit _ (isUnit_iff_ne_zero.mpr hne))
  rw [map_sub, hg, sub_eq_zero] at h3
  exact h3.symm

namespace AnalyticSpace.KLocallyRingedSpace

theorem KIso.inv_base_hom_base {A B : KLocallyRingedSpace.{u} K} (e : KIso A B) (a : A) :
    e.inv.1.base (e.hom.1.base a) = a :=
  congrArg (fun φ => Hom.toFun φ a) e.hom_inv_id

theorem KIso.hom_base_inv_base {A B : KLocallyRingedSpace.{u} K} (e : KIso A B) (b : B) :
    e.hom.1.base (e.inv.1.base b) = b :=
  congrArg (fun φ => Hom.toFun φ b) e.inv_hom_id

end AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace

variable (X : AnalyticSpace.{u} K)

/-- Reading the stalk of `X` at a point of `V` through a `K`-isomorphism `e : (G', 𝒜_{G'}) ≅ X | V`
and evaluating: `𝒪_{X, e q} → 𝒪_{X|V, e q} → 𝒜_{G', q} → K`. -/
def chartEval {V : Opens X} {d : ℕ} {G' : Opens (Kn.{u} K d)}
    (e : KIso (analyticSpaceOfOpen K d G') (X.toKLocallyRingedSpace.restrictOpen V))
    (q : analyticSpaceOfOpen K d G') :
    X.toLocallyRingedSpace.presheaf.stalk (e.hom.1.base q).1 →+* K :=
  (evalRestrict G' q).comp ((e.hom.1.stalkMap q).hom.comp
    (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding V) (e.hom.1.base q)).inv.hom)

/-- `evalRestrict` is a local homomorphism (a germ is a unit iff its value is nonzero). -/
theorem isLocalHom_evalRestrict (d : ℕ) (G : Opens (Kn.{u} K d)) (q : analyticSpaceOfOpen K d G) :
    IsLocalHom (evalRestrict G q) := by
  refine ⟨fun a ha => ?_⟩
  set ρ := (affine K d).toLocallyRingedSpace.restrictStalkIso
    (Opens.isOpenEmbedding (X := (affine K d).toLocallyRingedSpace.toTopCat) G) q with hρ
  change IsUnit (Manifold.eval K (Kn.{u} K d) (Kn.{u} K d) q.1 (ρ.hom.hom a)) at ha
  have h : IsUnit (ρ.hom.hom a) :=
    (contMDiffSheafCommRing.isUnit_stalk_iff 𝓘(K, Kn.{u} K d) ω (Kn.{u} K d) _).mpr
      (isUnit_iff_ne_zero.mp ha)
  have h2 := h.map ρ.inv.hom
  have e : ρ.inv.hom (ρ.hom.hom a) = a := Iso.hom_inv_id_apply ρ a
  rw [e] at h2
  exact h2

/-- `evalRestrict` fixes the constants. -/
theorem evalRestrict_constAt (d : ℕ) (G : Opens (Kn.{u} K d)) (q : analyticSpaceOfOpen K d G)
    (c : K) : evalRestrict G q (constAt (analyticSpaceOfOpen K d G) q c) = c := by
  refine (evalRestrict_germ G q (Opens.mem_top q) ((analyticSpaceOfOpen K d G).algebraMap c)).trans
    ?_
  refine (extendSection_of_mem K (Kn.{u} K d) (M := Kn.{u} K d) _ (show q.1 ∈ (Opens.isOpenEmbedding
    (X := (affine K d).toLocallyRingedSpace.toTopCat) G).isOpenMap.functor.obj ⊤ from
      ⟨q, trivial, rfl⟩)).trans ?_
  rfl

theorem isLocalHom_chartEval {V : Opens X} {d : ℕ} {G' : Opens (Kn.{u} K d)}
    (e : KIso (analyticSpaceOfOpen K d G') (X.toKLocallyRingedSpace.restrictOpen V))
    (q : analyticSpaceOfOpen K d G') : IsLocalHom (chartEval X e q) := by
  have h1 := isLocalHom_evalRestrict d G' q
  have h2 : IsLocalHom (e.hom.1.stalkMap q).hom := e.hom.1.prop q
  have h3 : IsLocalHom (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding V)
      (e.hom.1.base q)).inv.hom := by
    have hinv : (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding V)
        (e.hom.1.base q)).inv =
        (X.toLocallyRingedSpace.ofRestrict (Opens.isOpenEmbedding V)).stalkMap (e.hom.1.base q) :=
      PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict _ _ _
    rw [hinv]
    exact (X.toLocallyRingedSpace.ofRestrict (Opens.isOpenEmbedding V)).prop (e.hom.1.base q)
  exact ⟨fun a ha => h3.map_nonunit _ (h2.map_nonunit _ (h1.map_nonunit _ ha))⟩

theorem chartEval_constAt {V : Opens X} {d : ℕ} {G' : Opens (Kn.{u} K d)}
    (e : KIso (analyticSpaceOfOpen K d G') (X.toKLocallyRingedSpace.restrictOpen V))
    (q : analyticSpaceOfOpen K d G') (c : K) :
    chartEval X e q (constAt X.toKLocallyRingedSpace (e.hom.1.base q).1 c) = c := by
  have h1 : (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding V)
      (e.hom.1.base q)).inv.hom (constAt X.toKLocallyRingedSpace (e.hom.1.base q).1 c) =
      constAt (X.toKLocallyRingedSpace.restrictOpen V) (e.hom.1.base q) c := by
    have hinv : (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding V)
        (e.hom.1.base q)).inv =
        (X.toLocallyRingedSpace.ofRestrict (Opens.isOpenEmbedding V)).stalkMap (e.hom.1.base q) :=
      PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict _ _ _
    rw [hinv]
    exact (ofRestrict X.toKLocallyRingedSpace V).algebraMap_stalk (e.hom.1.base q) c
  have h2 : (e.hom.1.stalkMap q).hom (constAt (X.toKLocallyRingedSpace.restrictOpen V)
      (e.hom.1.base q) c) = constAt (analyticSpaceOfOpen K d G') q c :=
    e.hom.algebraMap_stalk q c
  change evalRestrict G' q ((e.hom.1.stalkMap q).hom
    ((X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding V) (e.hom.1.base q)).inv.hom
      (constAt X.toKLocallyRingedSpace (e.hom.1.base q).1 c))) = c
  rw [h1, h2, evalRestrict_constAt]

/-- At a simple point there is a local homomorphism `𝒪_{X,x} →+* K` fixing the constants (through
a manifold chart, `isRegular_stalk_iff_exists_manifold_nhd`). -/
theorem exists_isLocalHom_const_eq {x : X} (hx : x ∈ regularLocus X) :
    ∃ f : X.toLocallyRingedSpace.presheaf.stalk x →+* K,
      IsLocalHom f ∧ ∀ c, f (constAt X.toKLocallyRingedSpace x c) = c := by
  obtain ⟨d, -, V, hxV, G', ⟨e⟩⟩ := (isRegular_stalk_iff_exists_manifold_nhd X x).mp hx
  obtain ⟨q, hq⟩ : ∃ q, (e.symm.hom.1.base q).1 = x :=
    ⟨e.hom.1.base ⟨x, hxV⟩, congrArg Subtype.val (KIso.inv_base_hom_base e ⟨x, hxV⟩)⟩
  subst hq
  exact ⟨chartEval X e.symm q, isLocalHom_chartEval X e.symm q, chartEval_constAt X e.symm q⟩

/-- **The evaluation at a simple point** `x`: the unique local ring homomorphism `𝒪_{X,x} →+* K`
fixing the constants. -/
def regEval {x : X} (hx : x ∈ regularLocus X) : X.toLocallyRingedSpace.presheaf.stalk x →+* K :=
  Classical.choose (exists_isLocalHom_const_eq X hx)

theorem isLocalHom_regEval {x : X} (hx : x ∈ regularLocus X) : IsLocalHom (regEval X hx) :=
  (Classical.choose_spec (exists_isLocalHom_const_eq X hx)).1

theorem regEval_constAt {x : X} (hx : x ∈ regularLocus X) (c : K) :
    regEval X hx (constAt X.toKLocallyRingedSpace x c) = c :=
  (Classical.choose_spec (exists_isLocalHom_const_eq X hx)).2 c

/-- The evaluation is the unique ring homomorphism to `K` fixing the constants. -/
theorem eq_regEval {x : X} (hx : x ∈ regularLocus X) (f : X.toLocallyRingedSpace.presheaf.stalk x
    →+* K)
    (hf : ∀ c, f (constAt X.toKLocallyRingedSpace x c) = c) :
    f = regEval X hx :=
  have := isLocalHom_regEval X hx
  ringHom_eq_of_isLocalHom_of_const (constAt X.toKLocallyRingedSpace x) f (regEval X hx) hf
    (regEval_constAt X hx)

/-- The evaluation can be computed through any chart. -/
theorem chartEval_eq_regEval {V : Opens X} {d : ℕ} {G' : Opens (Kn.{u} K d)}
    (e : KIso (analyticSpaceOfOpen K d G') (X.toKLocallyRingedSpace.restrictOpen V))
    (q : analyticSpaceOfOpen K d G') (hreg : (e.hom.1.base q).1 ∈ regularLocus X) :
    chartEval X e q = regEval X hreg :=
  have := isLocalHom_chartEval X e q
  eq_regEval X hreg (chartEval X e q) (chartEval_constAt X e q)

/-- Every point of a chart neighbourhood is simple
(`isRegularLocalRing_stalk_of_kIso_analyticSpaceOfOpen`). -/
theorem mem_reg_of_chart {V : Opens X} {d : ℕ} {G' : Opens (Kn.{u} K d)}
    (e : KIso (analyticSpaceOfOpen K d G') (X.toKLocallyRingedSpace.restrictOpen V))
    (q : analyticSpaceOfOpen K d G') : (e.hom.1.base q).1 ∈ regularLocus X :=
  (isRegularLocalRing_stalk_of_kIso_analyticSpaceOfOpen (e.hom.1.base q).2 e.symm).1

/-- The pullback along the chart of a section `s` of `𝒪_X` over `W`, as a section of `𝒜_{G'}` over
the preimage of `W ∩ V`. -/
def sectionViaChart {V : Opens X} {d : ℕ} {G' : Opens (Kn.{u} K d)}
    (e : KIso (analyticSpaceOfOpen K d G') (X.toKLocallyRingedSpace.restrictOpen V))
    (W : Opens X) (s : X.toLocallyRingedSpace.presheaf.obj (op W)) :
    (analyticSpaceOfOpen K d G').toLocallyRingedSpace.presheaf.obj
      (op ((Opens.map e.hom.1.base).obj
        ((Opens.map (ofRestrict X.toKLocallyRingedSpace V).1.base).obj W))) :=
  (e.hom.1.c.app _).hom (((ofRestrict X.toKLocallyRingedSpace V).1.c.app (op W)).hom s)

/-- **The evaluation of the germ of a section is the value of its chart pullback**:
`regEval (s_x) = (e^* s)(q)` for `x = e q`. -/
theorem regEval_germ {V : Opens X} {d : ℕ} {G' : Opens (Kn.{u} K d)}
    (e : KIso (analyticSpaceOfOpen K d G') (X.toKLocallyRingedSpace.restrictOpen V))
    (q : analyticSpaceOfOpen K d G') (W : Opens X) (hW : (e.hom.1.base q).1 ∈ W)
    (s : X.toLocallyRingedSpace.presheaf.obj (op W)) :
    regEval X (mem_reg_of_chart X e q) (X.toLocallyRingedSpace.presheaf.germ W _ hW s) =
      extendSection K (Kn.{u} K d) (sectionViaChart X e W s) q.1 := by
  rw [← chartEval_eq_regEval X e q (mem_reg_of_chart X e q)]
  have hW₁ : e.hom.1.base q ∈ (Opens.map (ofRestrict X.toKLocallyRingedSpace V).1.base).obj W :=
    hW
  have hW₂ : q ∈ (Opens.map e.hom.1.base).obj
      ((Opens.map (ofRestrict X.toKLocallyRingedSpace V).1.base).obj W) := hW
  have hinv : (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding V)
      (e.hom.1.base q)).inv =
      (X.toLocallyRingedSpace.ofRestrict (Opens.isOpenEmbedding V)).stalkMap (e.hom.1.base q) :=
    PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict _ _ _
  have h1 : (X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding V)
      (e.hom.1.base q)).inv.hom (X.toLocallyRingedSpace.presheaf.germ W _ hW s) =
      (X.toKLocallyRingedSpace.restrictOpen V).toLocallyRingedSpace.presheaf.germ
        ((Opens.map (ofRestrict X.toKLocallyRingedSpace V).1.base).obj W) (e.hom.1.base q) hW₁
        (((ofRestrict X.toKLocallyRingedSpace V).1.c.app (op W)).hom s) := by
    rw [hinv]
    exact PresheafedSpace.stalkMap_germ_apply
      (X.toLocallyRingedSpace.ofRestrict (Opens.isOpenEmbedding V)).toShHom.hom W
      (e.hom.1.base q) hW s
  have h2 : (e.hom.1.stalkMap q).hom
      ((X.toKLocallyRingedSpace.restrictOpen V).toLocallyRingedSpace.presheaf.germ
        ((Opens.map (ofRestrict X.toKLocallyRingedSpace V).1.base).obj W) (e.hom.1.base q) hW₁
        (((ofRestrict X.toKLocallyRingedSpace V).1.c.app (op W)).hom s)) =
      (analyticSpaceOfOpen K d G').toLocallyRingedSpace.presheaf.germ
        ((Opens.map e.hom.1.base).obj
          ((Opens.map (ofRestrict X.toKLocallyRingedSpace V).1.base).obj W)) q hW₂
        (sectionViaChart X e W s) :=
    PresheafedSpace.stalkMap_germ_apply e.hom.1.toShHom.hom _ q hW₁ _
  change evalRestrict G' q ((e.hom.1.stalkMap q).hom
    ((X.toLocallyRingedSpace.restrictStalkIso (Opens.isOpenEmbedding V) (e.hom.1.base q)).inv.hom
      (X.toLocallyRingedSpace.presheaf.germ W _ hW s))) = _
  rw [h1, h2]
  exact evalRestrict_germ G' q hW₂ _

end AnalyticSpace

