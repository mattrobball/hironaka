/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionOn
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueDatum
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientEmb
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Hom
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceTransition
public import Hironaka.Resolution.Analytic.OrderReduction.ChainIndep
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The restriction of a piece's local resolution to a smaller open

The functoriality of the sequence functor under open embeddings ([Kol07, Definition 30.1]), at the
inclusion `W' ↪ W` of two relatively compact opens of a piece's ambient: the restriction
`Ỹ(W') → Ỹ(W)` of the piece's local resolution (`localResolutionHomOn` of `LocalResolutionOn.lean`
at the identity of the ambient) — an open immersion onto the part over `W'`, lying over
`Sp(W' ↪ W)` on the closed subspaces, compatible with the piece maps to `X` (the identity of the
two restriction-of-a-quotient maps). With the generic tools the lift of the glued space into the
last transform (`AmbientLift.lean`) uses: the point lemmas of isomorphisms of `K`-spaces, open
immersions as monomorphisms, `Sp(f) ≫ Sp(g) = Sp(g ∘ f)`, and the characterisation of the points
of the piece over `W` lying over an open `W'`. Not in the sources beyond the functoriality cited;
bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

section Generic

/-- The underlying map of an isomorphism of `K`-spaces is surjective. -/
theorem KIso.surjective_toFun_hom {A B : KLocallyRingedSpace.{u} 𝕜} (e : A ≅ B) :
    Function.Surjective (KLocallyRingedSpace.Hom.toFun e.hom) :=
  fun y => ⟨KLocallyRingedSpace.Hom.toFun e.inv y,
    congrArg (fun k => KLocallyRingedSpace.Hom.toFun k y) e.inv_hom_id⟩

/-- The underlying map of the inverse of an isomorphism of `K`-spaces is
surjective. -/
theorem KIso.surjective_toFun_inv {A B : KLocallyRingedSpace.{u} 𝕜} (e : A ≅ B) :
    Function.Surjective (KLocallyRingedSpace.Hom.toFun e.inv) :=
  fun y => ⟨KLocallyRingedSpace.Hom.toFun e.hom y,
    congrArg (fun k => KLocallyRingedSpace.Hom.toFun k y) e.hom_inv_id⟩

/-- `e.hom ∘ e.inv = id` on points. -/
theorem KIso.toFun_hom_toFun_inv {A B : KLocallyRingedSpace.{u} 𝕜} (e : A ≅ B) (y : B) :
    KLocallyRingedSpace.Hom.toFun e.hom (KLocallyRingedSpace.Hom.toFun e.inv y) = y :=
  congrArg (fun k => KLocallyRingedSpace.Hom.toFun k y) e.inv_hom_id

/-- `e.inv ∘ e.hom = id` on points. -/
theorem KIso.toFun_inv_toFun_hom {A B : KLocallyRingedSpace.{u} 𝕜} (e : A ≅ B) (x : A) :
    KLocallyRingedSpace.Hom.toFun e.inv (KLocallyRingedSpace.Hom.toFun e.hom x) = x :=
  congrArg (fun k => KLocallyRingedSpace.Hom.toFun k x) e.hom_inv_id

/-- Open immersions of `K`-spaces are monomorphisms: two morphisms agreeing after
an open immersion agree (`cancel_mono` on the locally ringed spaces). -/
theorem Hom.ext_of_comp_of_isOpenImmersion {A B C : KLocallyRingedSpace.{u} 𝕜} (q : B ⟶ C)
    [AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion q.1] {f g : A ⟶ B}
    (h : f ≫ q = g ≫ q) : f = g :=
  Hom.ext ((cancel_mono q.1).mp (by rw [← Hom.comp_val, ← Hom.comp_val, h]))

/-- The identity of an analytic manifold is an analytic open embedding. -/
theorem isAnalyticOpenEmbedding_id {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : AnalyticManifold.{u} 𝕜 E) :
    IsAnalyticOpenEmbedding (ContMDiffMap.id : AnalyticMap M M) :=
  ⟨(Diffeomorph.refl 𝓘(𝕜, E) M ω).isLocalDiffeomorph, fun _ _ h => h⟩

/-- `Sp(f) ≫ Sp(g) = Sp(k)` when `g ∘ f = k` pointwise (`ofManifoldHom_comp`). -/
theorem toSpaceHom_comp_eq {n : ℕ} {A B C : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (f : AnalyticMap A B) (g : AnalyticMap B C)
    (k : AnalyticMap A C) (h : ∀ x, g (f x) = k x) :
    toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) f ≫
        toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) g =
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) k :=
  (ofManifoldHom_comp (K := 𝕜) (E := Fin n → 𝕜) (E' := Fin n → 𝕜) (E'' := Fin n → 𝕜) _
    f.contMDiff _ g.contMDiff).symm.trans
    (congrArg (fun q : {f : A → C // ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω f} =>
        ofManifoldHom (K := 𝕜) (E := Fin n → 𝕜) (E' := Fin n → 𝕜) q.1 q.2)
      (Subtype.ext (funext h) :
        (⟨⇑g ∘ ⇑f, g.contMDiff.comp f.contMDiff⟩ :
          {f : A → C // ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω f}) = ⟨⇑k, k.contMDiff⟩))

end Generic

section Piece

variable {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}

/-- The restricted ideal over `W' ≤ W` is the pull-back of the one over `W` along the inclusion
`W' ↪ W` of the restricted manifolds (`pullback_inclusion_restrictLE`). -/
theorem PieceEmbedding.restrictedIdeal_eq_pullback_restrictLE (E : PieceEmbedding 𝕜 n X V)
    (W W' : Opens (pieceAmbient.{u} 𝕜 E.G)) (hle : W' ≤ W) :
    E.restrictedIdeal W' =
      (E.restrictedIdeal W).pullback ⇑((pieceAmbient.{u} 𝕜 E.G).restrictLE hle)
        ((pieceAmbient.{u} 𝕜 E.G).restrictLE hle).contMDiff :=
  (congrArg AnalyticTriple.I
    (AnalyticTriple.pullback_inclusion_restrictLE E.ambientTriple hle)).symm

/-- The piece triple is its own pull-back along the identity (its divisor is
empty). -/
theorem PieceEmbedding.isPullbackOf_ambientTriple_id (E : PieceEmbedding 𝕜 n X V) :
    E.ambientTriple.IsPullbackOf E.ambientTriple
      (ContMDiffMap.id :
        AnalyticMap (pieceAmbient.{u} 𝕜 E.G) (pieceAmbient.{u} 𝕜 E.G)) :=
  ⟨(IdealSheaf.pullback_id_eq_self E.ideal).symm, (HypersurfaceFamily.empty_comap _).symm⟩

/-- **The restriction of the local resolution to a smaller open** `W' ≤ W`
([Kol07, Definition 30.1]): `localResolutionHomOn` at the identity of the ambient — an open
immersion `Ỹ(W') → Ỹ(W)` onto the part over `W'`. -/
def PieceEmbedding.localResolutionRestrictHom (E : PieceEmbedding 𝕜 n X V)
    (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) (W' : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 E.G)))) (hle : W' ≤ W)
    (hbed : bed.IsEmbeddedDesing) :
    E.localResolution bed W' hW' ⟶ E.localResolution bed W hW :=
  bed.localResolutionHomOn E.ambientTriple E.domBEDan_ambientTriple W hW E.ambientTriple
    E.domBEDan_ambientTriple ContMDiffMap.id (isAnalyticOpenEmbedding_id _)
    E.isPullbackOf_ambientTriple_id W' hW' (ChainState.image_id_subset hle) hbed

theorem PieceEmbedding.isOpenImmersion_localResolutionRestrictHom (E : PieceEmbedding 𝕜 n X V)
    (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) (W' : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 E.G)))) (hle : W' ≤ W)
    (hbed : bed.IsEmbeddedDesing) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (E.localResolutionRestrictHom bed W hW W' hW' hle hbed).1 :=
  bed.isOpenImmersion_localResolutionHomOn E.ambientTriple E.domBEDan_ambientTriple W hW
    E.ambientTriple E.domBEDan_ambientTriple ContMDiffMap.id (isAnalyticOpenEmbedding_id _)
    E.isPullbackOf_ambientTriple_id W' hW' (ChainState.image_id_subset hle) hbed

/-- Its range: the points of `Ỹ(W)` whose ambient image lies in `W'`. -/
theorem PieceEmbedding.range_toFun_localResolutionRestrictHom (E : PieceEmbedding 𝕜 n X V)
    (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) (W' : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 E.G)))) (hle : W' ≤ W)
    (hbed : bed.IsEmbeddedDesing) :
    Set.range ⇑(E.localResolutionRestrictHom bed W hW W' hW' hle hbed) =
      {y | ((bed.seqOn E.ambientTriple E.domBEDan_ambientTriple W hW).toSuccession.stageMap
          (Fin.last _)
          ((bed.lastIdealOn E.ambientTriple E.domBEDan_ambientTriple W hW).toAnalyticSpaceι
            y)).1 ∈ W'} :=
  (bed.range_toFun_localResolutionHomOn E.ambientTriple E.domBEDan_ambientTriple W hW
    E.ambientTriple E.domBEDan_ambientTriple ContMDiffMap.id (isAnalyticOpenEmbedding_id _)
    E.isPullbackOf_ambientTriple_id W' hW' (ChainState.image_id_subset hle) hbed).trans
    (Set.ext fun y => by
      change _ ∈ ⇑(ContMDiffMap.id : AnalyticMap (pieceAmbient.{u} 𝕜 E.G)
        (pieceAmbient.{u} 𝕜 E.G)) '' (W' : Set (pieceAmbient.{u} 𝕜 E.G)) ↔
        _ ∈ (W' : Set (pieceAmbient.{u} 𝕜 E.G))
      rw [show ⇑(ContMDiffMap.id : AnalyticMap (pieceAmbient.{u} 𝕜 E.G)
        (pieceAmbient.{u} 𝕜 E.G)) = id from rfl, Set.image_id])

/-- It lies over `Sp(W' ↪ W)` on the closed subspaces (`localResolutionHomOn_comp_map`). -/
theorem PieceEmbedding.localResolutionRestrictHom_comp_map (E : PieceEmbedding 𝕜 n X V)
    (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) (W' : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 E.G)))) (hle : W' ≤ W)
    (hbed : bed.IsEmbeddedDesing) :
    E.localResolutionRestrictHom bed W hW W' hW' hle hbed ≫ E.localResolutionMap bed W hW =
      E.localResolutionMap bed W' hW' ≫ (IdealSheaf.homOfPullbackEq
          ⇑((pieceAmbient.{u} 𝕜 E.G).restrictLE hle) ((pieceAmbient.{u} 𝕜 E.G).restrictLE
          hle).contMDiff (E.restrictedIdeal_eq_pullback_restrictLE W W' hle)) :=
  bed.localResolutionHomOn_comp_map E.ambientTriple E.domBEDan_ambientTriple W hW
    E.ambientTriple E.domBEDan_ambientTriple ContMDiffMap.id (isAnalyticOpenEmbedding_id _)
    E.isPullbackOf_ambientTriple_id W' hW' (ChainState.image_id_subset hle) hbed

/-- **The open immersion of the piece over `W` lands in `domOpens W'` exactly over
`W'`**: `pieceOverIncl W z ∈ domOpens W'` iff the ambient point of `z` lies in `W'`. -/
theorem PieceEmbedding.pieceOverIncl_mem_domOpens_iff (E : PieceEmbedding 𝕜 n X V)
    (W W' : Opens (pieceAmbient.{u} 𝕜 E.G)) (z : (E.restrictedIdeal W).toAnalyticSpace) :
    E.pieceOverIncl W z ∈ E.domOpens W' ↔
      ((E.restrictedIdeal W).toAnalyticSpaceι z).1 ∈ W' := by
  have hamb : E.ambientPoint (E.embInv (E.restrictedIdealHom W z)) =
      ((E.restrictedIdeal W).toAnalyticSpaceι z).1 :=
    congrArg (fun k => k z)
      (E.ambient_comp_embInv_restrictedIdealHom W)
  constructor
  · intro h
    have h1 : E.ambientPoint (E.embInv (E.restrictedIdealHom W z)) ∈ W' :=
      E.mem_embPreimage_of_val_mem_domOpens W' _ h
    exact hamb ▸ h1
  · intro h
    refine ⟨_, ?_, rfl⟩
    change E.ambientPoint (E.embInv (E.restrictedIdealHom W z)) ∈ W'
    exact hamb ▸ h

end Piece

section PieceTwo

variable {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}

/-- `homOfPullbackEq` along `W' ↪ W` followed by the restriction-of-a-quotient map over `W` is the
one over `W'` (both lie over `Sp(W' ↪ G)`). Internal. -/
theorem PieceEmbedding.homOfPullbackEq_restrictLE_comp_restrictedIdealHom
    (E : PieceEmbedding 𝕜 n X V) (W W' : Opens (pieceAmbient.{u} 𝕜 E.G)) (hle : W' ≤ W) :
    (IdealSheaf.homOfPullbackEq ⇑((pieceAmbient.{u} 𝕜 E.G).restrictLE hle)
        ((pieceAmbient.{u} 𝕜 E.G).restrictLE hle).contMDiff
        (E.restrictedIdeal_eq_pullback_restrictLE W W' hle) :
        (E.restrictedIdeal W').toAnalyticSpace.toKLocallyRingedSpace ⟶
          (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace) ≫
      (E.restrictedIdealHom W : (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
        E.ideal.toAnalyticSpace.toKLocallyRingedSpace) =
    (E.restrictedIdealHom W' : (E.restrictedIdeal W').toAnalyticSpace.toKLocallyRingedSpace ⟶
      E.ideal.toAnalyticSpace.toKLocallyRingedSpace) := by
  obtain ⟨H, hH⟩ : ∃ H : (E.restrictedIdeal W').toAnalyticSpace.toKLocallyRingedSpace ⟶
      (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace,
      H = IdealSheaf.homOfPullbackEq ⇑((pieceAmbient.{u} 𝕜 E.G).restrictLE hle)
        ((pieceAmbient.{u} 𝕜 E.G).restrictLE hle).contMDiff
        (E.restrictedIdeal_eq_pullback_restrictLE W W' hle) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
      E.ideal.toAnalyticSpace.toKLocallyRingedSpace, R = E.restrictedIdealHom W := ⟨_, rfl⟩
  obtain ⟨R', hR'⟩ : ∃ R' : (E.restrictedIdeal W').toAnalyticSpace.toKLocallyRingedSpace ⟶
      E.ideal.toAnalyticSpace.toKLocallyRingedSpace, R' = E.restrictedIdealHom W' := ⟨_, rfl⟩
  have e1 : H ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((pieceAmbient.{u} 𝕜 E.G).restrict W)).toKLocallyRingedSpace (E.restrictedIdeal W) =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((pieceAmbient.{u} 𝕜 E.G).restrict W')).toKLocallyRingedSpace (E.restrictedIdeal W') ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((pieceAmbient.{u} 𝕜 E.G).restrictLE hle) := by
    rw [hH]
    exact homOfPullbackEq_comp_toAnalyticSpaceι _ _ _
  have e2 : R ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (pieceAmbient.{u} 𝕜 E.G)).toKLocallyRingedSpace E.ideal =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((pieceAmbient.{u} 𝕜 E.G).restrict W)).toKLocallyRingedSpace (E.restrictedIdeal W) ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((pieceAmbient.{u} 𝕜 E.G).inclusion W) := by
    rw [hR]
    exact E.toAnalyticSpaceι_comp_restrictedIdealHom W
  have e3 : R' ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (pieceAmbient.{u} 𝕜 E.G)).toKLocallyRingedSpace E.ideal =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((pieceAmbient.{u} 𝕜 E.G).restrict W')).toKLocallyRingedSpace (E.restrictedIdeal W') ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((pieceAmbient.{u} 𝕜 E.G).inclusion W') := by
    rw [hR']
    exact E.toAnalyticSpaceι_comp_restrictedIdealHom W'
  have e4 := toSpaceHom_comp_eq ((pieceAmbient.{u} 𝕜 E.G).restrictLE hle)
    ((pieceAmbient.{u} 𝕜 E.G).inclusion W) ((pieceAmbient.{u} 𝕜 E.G).inclusion W') fun _ => rfl
  have hK : H ≫ R = R' := by
    refine Hom.ext_of_comp_quotientι _ ?_
    exact (Category.assoc _ _ _).trans ((congrArg (fun k => H ≫ k) e2).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ toSpaceHom
          (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) ((pieceAmbient.{u} 𝕜 E.G).inclusion W))
          e1).trans
        ((Category.assoc _ _ _).trans ((congrArg (fun k => quotientι (toSpace
            (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
            ((pieceAmbient.{u} 𝕜 E.G).restrict W')).toKLocallyRingedSpace
            (E.restrictedIdeal W') ≫ k) e4).trans e3.symm)))))
  subst hH hR hR'
  exact hK

/-- The restriction `Ỹ(W') → Ỹ(W)` followed by the piece map of `Ỹ(W)` is the piece map of
`Ỹ(W')`. -/
theorem PieceEmbedding.localResolutionRestrictHom_comp_toSpaceMap (E : PieceEmbedding 𝕜 n X V)
    (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) (W' : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 E.G)))) (hle : W' ≤ W)
    (hbed : bed.IsEmbeddedDesing) :
    (E.localResolutionRestrictHom bed W hW W' hW' hle hbed :
        (E.localResolution bed W' hW').toKLocallyRingedSpace ⟶
          (E.localResolution bed W hW).toKLocallyRingedSpace) ≫ E.toSpaceMap bed W hW =
      E.toSpaceMap bed W' hW' := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (E.localResolution bed W' hW').toKLocallyRingedSpace ⟶
      (E.localResolution bed W hW).toKLocallyRingedSpace,
      ρ = E.localResolutionRestrictHom bed W hW W' hW' hle hbed := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : (E.localResolution bed W hW).toKLocallyRingedSpace ⟶
      (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace,
      A = E.localResolutionMap bed W hW := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A' : (E.localResolution bed W' hW').toKLocallyRingedSpace ⟶
      (E.restrictedIdeal W').toAnalyticSpace.toKLocallyRingedSpace,
      A' = E.localResolutionMap bed W' hW' := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : (E.restrictedIdeal W').toAnalyticSpace.toKLocallyRingedSpace ⟶
      (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace,
      H = IdealSheaf.homOfPullbackEq ⇑((pieceAmbient.{u} 𝕜 E.G).restrictLE hle)
        ((pieceAmbient.{u} 𝕜 E.G).restrictLE hle).contMDiff
        (E.restrictedIdeal_eq_pullback_restrictLE W W' hle) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
      E.ideal.toAnalyticSpace.toKLocallyRingedSpace, R = E.restrictedIdealHom W := ⟨_, rfl⟩
  obtain ⟨R', hR'⟩ : ∃ R' : (E.restrictedIdeal W').toAnalyticSpace.toKLocallyRingedSpace ⟶
      E.ideal.toAnalyticSpace.toKLocallyRingedSpace, R' = E.restrictedIdealHom W' := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : E.ideal.toAnalyticSpace.toKLocallyRingedSpace ⟶
      X.toKLocallyRingedSpace.restrictOpen (openOf X V),
      B = E.embInv := ⟨_, rfl⟩
  have sq1 : ρ ≫ A = A' ≫ H := by
    rw [hρ, hA, hA', hH]
    exact E.localResolutionRestrictHom_comp_map bed W hW W' hW' hle hbed
  have sq2 : H ≫ R = R' := by
    rw [hH, hR, hR']
    exact E.homOfPullbackEq_restrictLE_comp_restrictedIdealHom W W' hle
  have hT : E.toSpaceMap bed W hW = A ≫ R ≫ B ≫
      ofRestrict X.toKLocallyRingedSpace (openOf X V) := by
    rw [hA, hR, hB]
    exact E.toSpaceMap_eq_comp_pieceOverHom bed W hW
  have hT' : E.toSpaceMap bed W' hW' = A' ≫ R' ≫ B ≫
      ofRestrict X.toKLocallyRingedSpace (openOf X V) := by
    rw [hA', hR', hB]
    exact E.toSpaceMap_eq_comp_pieceOverHom bed W' hW'
  have hK : ρ ≫ A ≫ R ≫ B ≫
      ofRestrict X.toKLocallyRingedSpace (openOf X V) =
      A' ≫ R' ≫ B ≫
        ofRestrict X.toKLocallyRingedSpace (openOf X V) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ R ≫ B ≫
        ofRestrict X.toKLocallyRingedSpace (openOf X V)) sq1).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => A' ≫ k)
        ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ B ≫
          ofRestrict X.toKLocallyRingedSpace (openOf X V)) sq2)))))
  have hfin : ρ ≫ E.toSpaceMap bed W hW = E.toSpaceMap bed W' hW' :=
    (congrArg (fun k => ρ ≫ k) hT).trans (hK.trans hT'.symm)
  subst hρ
  exact hfin

end PieceTwo

end Hironaka.Manifold

end
