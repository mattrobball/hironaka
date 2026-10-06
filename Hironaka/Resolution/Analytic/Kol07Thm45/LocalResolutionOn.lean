/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceIndependence
public import Hironaka.Resolution.Analytic.OrderReduction.ConcatPullback
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.StrictSubspaceSeqCompat
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
import Hironaka.Resolution.Analytic.OrderReduction.ChainTransportPrep
import Hironaka.Resolution.Analytic.OrderReduction.ValueTransport
import Hironaka.Resolution.Analytic.Restrict.DiffeomorphTransport
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The local resolution of a triple over an open, and its transport along an open embedding

The value of the embedded desingularization functor `bed` on a triple `T` of the class over a
relatively compact open `W` is a finite blow-up sequence on `M|W` (the canonical embedded
desingularization of a local embedding, [Wlo09, §4, (3)⇒(4)]); the **local resolution** of `T`
over `W` is the closed subspace of the last stage cut out by the final strict transform of
`T.I|W`, with its map to `Sp(W)/T.I|W` (`localResolutionOn`, `localResolutionMapOn`, defined in
`PieceResolution.lean`, where the `localResolution` of a piece is their instance at the piece's
ambient triple).

For an analytic open embedding `g : N → M` with `T'` the pull-back of `T` and relatively compact
`W' ⊆ N`, `W ⊆ M` with `g(W') ⊆ W`, the value over `W'` is the pull-back of the value over `W`
along `g|W'`, empty blow-ups erased (the commutation with smooth morphisms, [Kol07, 34.1] —
`hbed`'s `CommutesWithLocalIsos` — and the family's restriction compatibility,
[Wlo09, Theorem 2.0.2(5)]), so the final strict transforms correspond under the last-stage lift
(the lift of [Kol07, Definition 30.1]; the transports of `LocalResolutionRestrict.lean`) and the
local resolution of `T'` over `W'` is the part of the local resolution of `T` over `W` lying over
`g(W')` (`localResolutionHomOn`, an open immersion over the restricted closed subspaces) — the
transport `exists_localResolution_restrictPiece_iso` of `PieceRestrictResolution.lean` made generic
in the open embedding, for the disjoint-union presentation of the local model
([Kol07, Proposition 37, proof]).

Not in the sources beyond the statements cited; bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace Hironaka.Manifold
open AnalyticManifold.BlowUpSequence
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BEDanFamStar

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] (bed : BEDanFamStar.{u} 𝕜) {n : ℕ}
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
  (W : Opens M) (hW : IsCompact (closure (W : Set M)))
  {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N) (hT' : DomBEDan 𝕜 T')
  (g : AnalyticMap N M) (hg : IsAnalyticOpenEmbedding g)
      (hpb : T'.IsPullbackOf T g)
  (W' : Opens N) (hW' : IsCompact (closure (W' : Set N))) (hle : ⇑g '' (W' : Set N) ⊆ (W : Set M))

/-- **The restricted ideal of the pulled-back triple over `W'` is the pull-back, along the
restricted embedding `g|W' : W' → W`, of the restricted ideal of `T` over `W`** — both are `T.I`
pulled back along `W' → M` (`pullback_pullback`). -/
theorem restrictedIdealOn_eq_pullback_restrictMap (hpb : T'.IsPullbackOf T g) :
    restrictedIdealOn T' W' =
      (restrictedIdealOn T W).pullback ⇑(AnalyticMap.restrictMap g W' W hle)
        (AnalyticMap.restrictMap g W' W hle).contMDiff := by
  change T'.I.pullback _ (N.inclusion W').contMDiff = _
  rw [hpb.1]
  change (T.I.pullback ⇑g g.contMDiff).pullback ⇑(N.inclusion W') (N.inclusion W').contMDiff =
    (T.I.pullback ⇑(M.inclusion W) (M.inclusion W).contMDiff).pullback
      ⇑(AnalyticMap.restrictMap g W' W hle) (AnalyticMap.restrictMap g W' W hle).contMDiff
  rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
  exact IdealSheaf.pullback_congr _ _ _ (funext fun _ => rfl)

include hpb in
/-- **The sequence identity along an open embedding of triples** ([Kol07, 34.1];
[Wlo09, Theorem 2.0.2(5)]): the value over `W'` is the pull-back along `g|W' : W' → W` of the value
over `W`, empty blow-ups erased — `hbed`'s `CommutesWithLocalIsos` at `g` and `U' := W'` (onto the
image open `g(W')`), the family's restriction compatibility from `g(W')` up to `W`,
`eraseEmpty_pullback_eraseEmpty` and `pullback_comp`. -/
theorem seqOn_eq_of_isAnalyticOpenEmbedding (hbed : bed.IsEmbeddedDesing) :
    bed.seqOn T' hT' W' hW' =
      ((bed.seqOn T hT W hW).pullback (AnalyticMap.restrictMap g W' W hle)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)).eraseEmpty := by
  have h1 := hbed.2 n T T' g hg.1 hpb hT hT' W' hW'
  have himg : AnalyticMap.imageOpens g hg.1 W' ≤ W := fun _ hx => hle hx
  have h2 := ((bed.fam n).fam T hT).compat (AnalyticMap.imageOpens g hg.1 W') W
    (AnalyticMap.isCompact_closure_image g hW') hW himg
  have hcomp : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((M.restrictLE himg).comp (AnalyticMap.restrictMap g W' (AnalyticMap.imageOpens g hg.1 W')
        Set.Subset.rfl)) :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE himg)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' _ Set.Subset.rfl)
  have key : ∀ (k : AnalyticMap (N.restrict W') (M.restrict W))
      (hk : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω k),
      (M.restrictLE himg).comp (AnalyticMap.restrictMap g W' (AnalyticMap.imageOpens g hg.1 W')
        Set.Subset.rfl) = k →
      (((bed.fam n).fam T hT).seqOn W hW).pullback ((M.restrictLE himg).comp
        (AnalyticMap.restrictMap g W' (AnalyticMap.imageOpens g hg.1 W') Set.Subset.rfl))
          hcomp = (((bed.fam n).fam T hT).seqOn W hW).pullback k hk := by
    rintro k hk rfl
    rfl
  change ((bed.fam n).fam T' hT').seqOn W' hW' = _
  rw [h1, h2, eraseEmpty_pullback_eraseEmpty, pullback_comp _ _ _ _ _,
    key (AnalyticMap.restrictMap g W' W hle)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)
      (Subtype.ext (funext fun _ => rfl))]
  rfl

/-- **The last-stage lift** along the open embedding (the lift of [Kol07, Definition 30.1]):
`stageOfEq` of the sequence identity, `eraseEmptyLast⁻¹`, `pullbackLiftLast` (the pattern of
`liftOfLe`, `LocalResolutionRestrict.lean`). -/
def liftOn (hbed : bed.IsEmbeddedDesing) :
    AnalyticMap ((bed.seqOn T' hT' W' hW').stage (Fin.last _))
      ((bed.seqOn T hT W hW).stage (Fin.last _)) :=
  ((bed.seqOn T hT W hW).pullbackLiftLast (AnalyticMap.restrictMap g W' W hle)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)).comp
    ((Diffeomorph.toAnalyticMap (((bed.seqOn T hT W hW).pullback
        (AnalyticMap.restrictMap g W' W hle)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)).eraseEmptyLast.symm)).comp
      (Diffeomorph.toAnalyticMap (stageOfEq
        (bed.seqOn_eq_of_isAnalyticOpenEmbedding T hT W hW T' hT' g hg hpb W' hW' hle hbed))))

/-- The lift is a local analytic isomorphism. -/
theorem isLocalDiffeomorph_liftOn (hbed : bed.IsEmbeddedDesing) :
    IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) :=
  isLocalDiffeomorph_comp (isLocalDiffeomorph_pullbackLiftLast _ _ _)
    (isLocalDiffeomorph_comp (Diffeomorph.isLocalDiffeomorph _) (Diffeomorph.isLocalDiffeomorph _))

/-- The lift is injective (`g|W'` is). -/
theorem injective_liftOn (hbed : bed.IsEmbeddedDesing) :
    Function.Injective (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) := by
  have hinj : Function.Injective (AnalyticMap.restrictMap g W' W hle) := fun p q h =>
    Subtype.ext (hg.2 (congrArg Subtype.val h))
  have h₂ := (((bed.seqOn T hT W hW).pullback (AnalyticMap.restrictMap g W' W hle)
    (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)).eraseEmptyLast.symm
    ).toEquiv.injective
  have h₃ := (stageOfEq
    (bed.seqOn_eq_of_isAnalyticOpenEmbedding T hT W hW T' hT' g hg hpb W' hW' hle hbed)
    ).toEquiv.injective
  exact (injective_pullbackLiftLast _ _ _ hinj).comp (h₂.comp h₃)

/-- The lift lies over `g|W'` (`stageMap_last_pullbackLiftLast`,
`stageMap_last_eraseEmptyLast_symm`, `stageMap_last_stageOfEq`). Internal. -/
theorem stageMap_last_liftOn' (hbed : bed.IsEmbeddedDesing)
    (p : (bed.seqOn T' hT' W' hW').stage (Fin.last _)) :
    (bed.seqOn T hT W hW).toSuccession.stageMap (Fin.last _)
        (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed p) =
      AnalyticMap.restrictMap g W' W hle
        ((bed.seqOn T' hT' W' hW').toSuccession.stageMap (Fin.last _) p) := by
  change (bed.seqOn T hT W hW).toSuccession.stageMap (Fin.last _)
      ((bed.seqOn T hT W hW).pullbackLiftLast (AnalyticMap.restrictMap g W' W hle)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)
        (((bed.seqOn T hT W hW).pullback _ _).eraseEmptyLast.symm
          (stageOfEq
            (bed.seqOn_eq_of_isAnalyticOpenEmbedding T hT W hW T' hT' g hg hpb W' hW' hle hbed)
            p))) = _
  rw [stageMap_last_pullbackLiftLast, stageMap_last_eraseEmptyLast_symm, stageMap_last_stageOfEq]

/-- **The lift lies over `g`**: the ambient point of the image is `g` of the ambient point. -/
theorem stageMap_last_liftOn (hbed : bed.IsEmbeddedDesing)
    (p : (bed.seqOn T' hT' W' hW').stage (Fin.last _)) :
    ((bed.seqOn T hT W hW).toSuccession.stageMap (Fin.last _)
        (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed p)).1 =
      g ((bed.seqOn T' hT' W' hW').toSuccession.stageMap (Fin.last _) p).1 :=
  congrArg Subtype.val (bed.stageMap_last_liftOn' T hT W hW T' hT' g hg hpb W' hW' hle hbed p)

/-- The range of the lift is the part of the last stage over `g(W')` (`range_pullbackLiftLast`).
Internal. -/
theorem range_liftOn (hbed : bed.IsEmbeddedDesing) :
    Set.range (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) =
      ⇑((bed.seqOn T hT W hW).toSuccession.stageMap (Fin.last _)) ⁻¹'
        Set.range (AnalyticMap.restrictMap g W' W hle) := by
  have hs : Function.Surjective (⇑(((bed.seqOn T hT W hW).pullback
      (AnalyticMap.restrictMap g W' W hle)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)).eraseEmptyLast.symm) ∘
      ⇑(stageOfEq
        (bed.seqOn_eq_of_isAnalyticOpenEmbedding T hT W hW T' hT' g hg hpb W' hW' hle hbed))) :=
    (((bed.seqOn T hT W hW).pullback _ _).eraseEmptyLast.symm.toEquiv.surjective).comp
      (stageOfEq _).toEquiv.surjective
  change Set.range (⇑((bed.seqOn T hT W hW).pullbackLiftLast (AnalyticMap.restrictMap g W' W hle)
    (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)) ∘
    (⇑(((bed.seqOn T hT W hW).pullback _ _).eraseEmptyLast.symm) ∘
      ⇑(stageOfEq
        (bed.seqOn_eq_of_isAnalyticOpenEmbedding T hT W hW T' hT' g hg hpb W' hW' hle hbed)))) = _
  rw [hs.range_comp, range_pullbackLiftLast]

/-- **The final strict transforms correspond under the lift**
(`strictTransformSubspaceSeq_last_of_eq_pullback_eraseEmpty`). -/
theorem lastIdealOn_eq_pullback_liftOn (hbed : bed.IsEmbeddedDesing) :
    bed.lastIdealOn T' hT' W' hW' =
      (bed.lastIdealOn T hT W hW).pullback ⇑(bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)
        (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed).contMDiff :=
  strictTransformSubspaceSeq_last_of_eq_pullback_eraseEmpty (bed.seqOn T hT W hW)
    (AnalyticMap.restrictMap g W' W hle) (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)
    (bed.seqOn T' hT' W' hW')
    (bed.seqOn_eq_of_isAnalyticOpenEmbedding T hT W hW T' hT' g hg hpb W' hW' hle hbed)
    (restrictedIdealOn T' W') (restrictedIdealOn T W)
    (restrictedIdealOn_eq_pullback_restrictMap T W T' g W' hle hpb)

/-- **The morphism of local resolutions along an open embedding of triples** ([Kol07, Theorem 36,
proof]): `homOfPullbackEq` along the lift. -/
def localResolutionHomOn (hbed : bed.IsEmbeddedDesing) :
    bed.localResolutionOn T' hT' W' hW' ⟶ bed.localResolutionOn T hT W hW :=
  IdealSheaf.homOfPullbackEq _ _
    (bed.lastIdealOn_eq_pullback_liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)

/-- It is an open immersion (`isOpenImmersion_homOfPullbackEq_of_injective` at the injective local
isomorphism `liftOn`). -/
theorem isOpenImmersion_localResolutionHomOn (hbed : bed.IsEmbeddedDesing) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (bed.localResolutionHomOn T hT W hW T' hT' g hg hpb W' hW' hle hbed).1 :=
  isOpenImmersion_homOfPullbackEq_of_injective _
    (bed.isLocalDiffeomorph_liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)
    (bed.injective_liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) _

/-- **Its range is the part of the local resolution of `T` over `g(W')`**
(`range_toFun_homOfPullbackEq`, `range_liftOn`, `range_restrictMap`). -/
theorem range_toFun_localResolutionHomOn (hbed : bed.IsEmbeddedDesing) :
    Set.range ⇑(bed.localResolutionHomOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) =
      {y | ((bed.seqOn T hT W hW).toSuccession.stageMap (Fin.last _)
        ((bed.lastIdealOn T hT W hW).toAnalyticSpaceι
            y)).1 ∈
          ⇑g '' (W' : Set N)} := by
  refine (range_toFun_homOfPullbackEq (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)
    (bed.isLocalDiffeomorph_liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)
    (bed.lastIdealOn_eq_pullback_liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)).trans ?_
  ext y
  change _ ∈ Set.range (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) ↔ _
  exact (Set.ext_iff.mp (bed.range_liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) _).trans
    (Set.ext_iff.mp (AnalyticMap.range_restrictMap g W' W hle) _)

/-- **It lies over the restricted closed subspaces**: the square of the local resolution maps
with `Sp(g|W')` on the closed subspaces, closed by `Hom.ext_of_comp_quotientι`
(`quotientMap_comp_quotientι` four times, the composite of the ambient maps by
`stageMap_last_liftOn`, `ofManifoldHom_comp`). -/
theorem localResolutionHomOn_comp_map (hbed : bed.IsEmbeddedDesing) :
    bed.localResolutionHomOn T hT W hW T' hT' g hg hpb W' hW' hle hbed ≫ bed.localResolutionMapOn T
        hT W hW =
      bed.localResolutionMapOn T' hT' W' hW' ≫ IdealSheaf.homOfPullbackEq _ _
          (restrictedIdealOn_eq_pullback_restrictMap T W T' g W' hle hpb) := by
  -- the composite of the ambient analytic maps: `σ_r ∘ lift = g|W' ∘ σ'_r`
  have hfun : (⇑(bed.seqOn T hT W hW).toSuccession.composite ∘
        ⇑(bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)) =
      (⇑(AnalyticMap.restrictMap g W' W hle) ∘ ⇑(bed.seqOn T' hT' W' hW').toSuccession.composite) :=
    funext fun p => bed.stageMap_last_liftOn' T hT W hW T' hT' g hg hpb W' hW' hle hbed p
  have hamb : toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (bed.seqOn T hT W hW).toSuccession.composite =
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (bed.seqOn T' hT' W' hW').toSuccession.composite ≫
        toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (AnalyticMap.restrictMap g W' W hle) := by
    refine (ofManifoldHom_comp (K := 𝕜) (E := Fin n → 𝕜) (E' := Fin n → 𝕜) (E'' := Fin n → 𝕜) _
      (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed).contMDiff _
      (bed.seqOn T hT W hW).toSuccession.composite.contMDiff).symm.trans (Eq.trans ?_
        (ofManifoldHom_comp (K := 𝕜) (E := Fin n → 𝕜) (E' := Fin n → 𝕜) (E'' := Fin n → 𝕜) _
          (bed.seqOn T' hT' W' hW').toSuccession.composite.contMDiff _
          (AnalyticMap.restrictMap g W' W hle).contMDiff))
    exact congrArg (fun k : {f : (bed.seqOn T' hT' W' hW').stage (Fin.last _) → M.restrict W //
        ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω f} =>
      ofManifoldHom (K := 𝕜) (E := Fin n → 𝕜) (E' := Fin n → 𝕜) k.1 k.2)
      (Subtype.ext hfun : (⟨_, (bed.seqOn T hT W hW).toSuccession.composite.contMDiff.comp
          (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed).contMDiff⟩ :
        {f : (bed.seqOn T' hT' W' hW').stage (Fin.last _) → M.restrict W //
          ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω f}) =
        ⟨_, (AnalyticMap.restrictMap g W' W hle).contMDiff.comp
          (bed.seqOn T' hT' W' hW').toSuccession.composite.contMDiff⟩)
  -- the four quotient-map squares
  have e1 := quotientMap_comp_quotientι
    (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (bed.seqOn T hT W hW).toSuccession.composite) _ _
    ((bed.seqOn T hT W hW).toSuccession.compat_composite_strictTransformSubspaceSeq
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (restrictedIdealOn T W))
  have e2 := quotientMap_comp_quotientι
    (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)) _ _
    (compat_ofManifoldHom_of_eq _ _
      (bed.lastIdealOn_eq_pullback_liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed))
  have e3 := quotientMap_comp_quotientι
    (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (AnalyticMap.restrictMap g W' W hle)) _ _
    (compat_ofManifoldHom_of_eq _ _ (restrictedIdealOn_eq_pullback_restrictMap T W T' g W' hle hpb))
  have e4 := quotientMap_comp_quotientι
    (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (bed.seqOn T' hT' W' hW').toSuccession.composite) _ _
    ((bed.seqOn T' hT' W' hW').toSuccession.compat_composite_strictTransformSubspaceSeq
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (restrictedIdealOn T' W'))
  -- the K-typed names of the four morphisms of closed subspaces
  obtain ⟨χ, hχ⟩ : ∃ χ : (bed.localResolutionOn T' hT' W' hW').toKLocallyRingedSpace ⟶
      (bed.localResolutionOn T hT W hW).toKLocallyRingedSpace,
      χ = bed.localResolutionHomOn T hT W hW T' hT' g hg hpb W' hW' hle hbed := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : (bed.localResolutionOn T hT W hW).toKLocallyRingedSpace ⟶
      (restrictedIdealOn T W).toAnalyticSpace.toKLocallyRingedSpace,
      A = bed.localResolutionMapOn T hT W hW := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : (bed.localResolutionOn T' hT' W' hW').toKLocallyRingedSpace ⟶
      (restrictedIdealOn T' W').toAnalyticSpace.toKLocallyRingedSpace,
      D = bed.localResolutionMapOn T' hT' W' hW' := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : (restrictedIdealOn T' W').toAnalyticSpace.toKLocallyRingedSpace ⟶
      (restrictedIdealOn T W).toAnalyticSpace.toKLocallyRingedSpace,
      R = IdealSheaf.homOfPullbackEq _ _
        (restrictedIdealOn_eq_pullback_restrictMap T W T' g W' hle hpb) := ⟨_, rfl⟩
  have e1' : A ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (M.restrict W)).toKLocallyRingedSpace (restrictedIdealOn T W) =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((bed.seqOn T hT W hW).stage (Fin.last _))).toKLocallyRingedSpace
        (bed.lastIdealOn T hT W hW) ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (bed.seqOn T hT W hW).toSuccession.composite := by
    rw [hA]; exact e1
  have e2' : χ ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((bed.seqOn T hT W hW).stage (Fin.last _))).toKLocallyRingedSpace
        (bed.lastIdealOn T hT W hW) =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((bed.seqOn T' hT' W' hW').stage (Fin.last _))).toKLocallyRingedSpace
        (bed.lastIdealOn T' hT' W' hW') ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) := by
    rw [hχ]; exact e2
  have e3' : R ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (M.restrict W)).toKLocallyRingedSpace (restrictedIdealOn T W) =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (N.restrict W')).toKLocallyRingedSpace (restrictedIdealOn T' W') ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (AnalyticMap.restrictMap g W' W hle) := by
    rw [hR]; exact e3
  have e4' : D ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (N.restrict W')).toKLocallyRingedSpace (restrictedIdealOn T' W') =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((bed.seqOn T' hT' W' hW').stage (Fin.last _))).toKLocallyRingedSpace
        (bed.lastIdealOn T' hT' W' hW') ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (bed.seqOn T' hT' W' hW').toSuccession.composite := by
    rw [hD]; exact e4
  have hK : χ ≫ A = D ≫ R := by
    refine Hom.ext_of_comp_quotientι _ ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => χ ≫ k) e1').trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ toSpaceHom
              (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
              (bed.seqOn T hT W hW).toSuccession.composite) e2').trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun k => quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
                  ((bed.seqOn T' hT' W' hW').stage (Fin.last _))).toKLocallyRingedSpace
                  (bed.lastIdealOn T' hT' W' hW') ≫ k) hamb).trans
                ((Category.assoc _ _ _).symm.trans
                  ((congrArg (fun k => k ≫ toSpaceHom
                      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
                      (AnalyticMap.restrictMap g W' W hle)) e4'.symm).trans
                    ((Category.assoc _ _ _).trans
                      ((congrArg (fun k => D ≫ k) e3'.symm).trans
                        (Category.assoc _ _ _).symm)))))))))
  subst hχ hA hD hR
  exact hK

end Hironaka.Manifold.BEDanFamStar

end
