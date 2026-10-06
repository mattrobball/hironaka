/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrict
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlue
public import Hironaka.AnalyticSpace.HomGlue
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
public import Hironaka.Resolution.Analytic.Restrict.DiffeomorphTransport
import Hironaka.AnalyticSpace.HomOfSections
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.AnalyticSpace.RestrictToIso
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Hom
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Hironaka.Resolution.Analytic.OrderReduction.ValueTransport
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The local resolution of a restricted piece embedding

Włodarczyk: the canonical resolution pulled back along a local analytic isomorphism is an
extension of the canonical resolution of the source [Wlo09, Theorem 6.0.6(2)], and an open
embedding of germs `Y_Z ⊂ Y_{Z'}` extends to an open embedding `U_Z ⊂ U_{Z'}` of the ambient
manifolds [Wlo09, §4, (3)⇒(4)]; Kollár: a blow-up sequence functor commuting with smooth morphisms
gives, along an open immersion, the pull-back with the empty blow-ups deleted [Kol07, 34.1]. For
the restricted piece embedding `E|V' = E.restrictPiece hV' hsub` of `PieceRestrict.lean` and a
relatively compact open `W'` of the shrunk ambient `G'`, the local resolution of `E|V'` over `W'`
is identified with the local resolution of `E` over the image `pieceAmbientIncl '' W' ⊆ G` — the
value of the functor on the pulled-back triple is the pull-back of its value on the image open,
empty blow-ups erased: **the commutation of `IsEmbeddedDesing` with local analytic isomorphisms**
(`CommutesWithLocalIsos`, the family functor's `hbed.2 n`) at the local analytic isomorphism
`pieceAmbientIncl` restricted to `W'` (a diffeomorphism onto its image, `restrictPieceIncl`). Then
the final strict transforms correspond under the last-stage lift
(`strictTransformSubspaceSeq_last_of_eq_pullback_eraseEmpty`, `LocalResolutionRestrict.lean`), the
lift is a diffeomorphism (`pullbackLiftLastDiffeomorphOfBijective`), and the morphism of closed
subspaces along it (`IdealSheaf.homOfPullbackEq`, an isomorphism by
`isIso_homOfPullbackEq_of_diffeomorph`) is the isomorphism of local resolutions

* `PieceEmbedding.localResolutionHomRestrictPiece E hV' hsub bed hbed W' hW'` with
  `isIso_localResolutionHomRestrictPiece`.

Composed with `localResolutionHomOfLe` (`LocalResolutionRestrict.lean`) at
`pieceAmbientImageOpens _ W' ≤ W` this gives the transport of the local resolution along the open
inclusion of ambients, `exists_localResolution_restrictPiece_iso` (the second half of this
module).

Not in the sources beyond the remarks cited; bookkeeping.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The identification `X|U' ≅ (X|U)|_V` built from
`imageOpens U V = U'` (an `eqToIso` followed by the inverse of `restrictOpen_restrictOpen_iso`),
followed by the two open immersions, is the open immersion of `U'` — proved by `subst`, so that
the `eqToIso` is the identity and no equation proof is ever unfolded. -/
theorem eqToIso_trans_restrictOpen_restrictOpen_iso_symm_hom_comp {X : KLocallyRingedSpace.{u} K}
    (U : Opens X) (V : Opens (X.restrictOpen U)) {U' : Opens X} (h : imageOpens U V = U') :
    (eqToIso (congrArg X.restrictOpen h.symm) ≪≫ (restrictOpen_restrictOpen_iso U V).symm).hom ≫
        (ofRestrict (X.restrictOpen U) V ≫ ofRestrict X U) =
      ofRestrict X U' := by
  subst h
  rw [eqToIso_refl, Iso.refl_trans, Iso.symm_hom,
      restrictOpen_restrictOpen_iso_inv_comp]

end AnalyticSpace.KLocallyRingedSpace

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- The associativity bookkeeping of the argument of
`localResolutionToPiece_comp_localResolutionHomOfLe`, in any category — two composites `Y' → T`
agree once each layer commutes
(`e1`/`e1'`: the closed subspaces over the open inclusions, `e2`/`e2'`: the maps of closed
subspaces over the blow-downs, `e3`: the lift, `e4`: the square of the ambient maps). -/
theorem layer_square_comp_eq {Y' Y Q Q' Z Z' T T' A A' B B' : C}
    (Φ : Y' ⟶ Y) (PW : Y ⟶ Q) (ρ : Q ⟶ Z) (ι : Z ⟶ T)
    (PW' : Y' ⟶ Q') (ρ' : Q' ⟶ Z') (ι' : Z' ⟶ T') (Spg : T' ⟶ T)
    (qW : Q ⟶ B) (SpιW : B ⟶ T) (ιW : Y ⟶ A) (SpcW : A ⟶ B)
    (qW' : Q' ⟶ B') (SpιW' : B' ⟶ T') (ιW' : Y' ⟶ A') (SpcW' : A' ⟶ B') (SpD : A' ⟶ A)
    (e1 : ρ ≫ ι = qW ≫ SpιW) (e1' : ρ' ≫ ι' = qW' ≫ SpιW')
    (e2 : PW ≫ qW = ιW ≫ SpcW) (e2' : PW' ≫ qW' = ιW' ≫ SpcW')
    (e3 : Φ ≫ ιW = ιW' ≫ SpD) (e4 : SpD ≫ SpcW ≫ SpιW = SpcW' ≫ SpιW' ≫ Spg) :
    Φ ≫ PW ≫ ρ ≫ ι = PW' ≫ ρ' ≫ ι' ≫ Spg :=
  calc Φ ≫ PW ≫ ρ ≫ ι = Φ ≫ PW ≫ qW ≫ SpιW := by rw [e1]
    _ = Φ ≫ ιW ≫ SpcW ≫ SpιW := by rw [← Category.assoc PW, e2, Category.assoc]
    _ = ιW' ≫ SpD ≫ SpcW ≫ SpιW := by rw [← Category.assoc Φ, e3, Category.assoc]
    _ = ιW' ≫ SpcW' ≫ SpιW' ≫ Spg := by rw [e4]
    _ = PW' ≫ qW' ≫ SpιW' ≫ Spg := by rw [← Category.assoc ιW', ← e2', Category.assoc]
    _ = PW' ≫ ρ' ≫ ι' ≫ Spg := by rw [← Category.assoc qW', ← e1', Category.assoc]

/-- A morphism with a one-sided inverse is cancelled on the right. -/
theorem eq_of_comp_eq_of_comp_inv_eq_id {A V Z : C} {g g' : A ⟶ V} (emb : V ⟶ Z) (embInv : Z ⟶ V)
    (hε : emb ≫ embInv = 𝟙 V) (h : g ≫ emb = g' ≫ emb) : g = g' := by
  rw [← Category.comp_id g, ← hε, ← Category.assoc, h, Category.assoc, hε, Category.comp_id]

/-- The second half of that argument, in any category — the two composites into the closed
subspace `Z` agree after `ι` (`h`), so they agree (`hι`); the model isomorphisms `emb`, `emb'` are
moved across the chain `hB1` (the model isomorphism of the restricted embedding over the inclusion
of the ambients) and cancelled. -/
theorem over_square_comp_embInv_eq {Y' Y Q Q' Z Z' T T' V V' : C}
    (Φ : Y' ⟶ Y) (PW : Y ⟶ Q) (ρ : Q ⟶ Z) (ι : Z ⟶ T)
    (PW' : Y' ⟶ Q') (ρ' : Q' ⟶ Z') (ι' : Z' ⟶ T') (Spg : T' ⟶ T)
    (emb : V ⟶ Z) (embInv : Z ⟶ V) (emb' : V' ⟶ Z') (embInv' : Z' ⟶ V') (rI : V' ⟶ V)
    (hι : ∀ {A : C} (g g' : A ⟶ Z), g ≫ ι = g' ≫ ι → g = g')
    (hε : emb ≫ embInv = 𝟙 V) (hε₂ : embInv ≫ emb = 𝟙 Z) (hε₂' : embInv' ≫ emb' = 𝟙 Z')
    (h : Φ ≫ PW ≫ ρ ≫ ι = PW' ≫ ρ' ≫ ι' ≫ Spg) (hB1 : emb' ≫ ι' ≫ Spg = rI ≫ emb ≫ ι) :
    Φ ≫ ((PW ≫ ρ) ≫ embInv) = ((PW' ≫ ρ') ≫ embInv') ≫ rI := by
  refine eq_of_comp_eq_of_comp_inv_eq_id emb embInv hε (hι _ _ ?_)
  simp only [Category.assoc]
  rw [← Category.assoc embInv, hε₂, Category.id_comp, ← hB1, ← Category.assoc embInv', hε₂',
    Category.id_comp]
  exact h

end CategoryTheory

namespace Hironaka.Manifold

namespace PieceEmbedding

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V) {V' : Set X} (hV' : IsOpen V') (hsub : V' ⊆ V)

/-! ### The restricted embedding's triple is the pull-back of the piece's triple -/

/-- The triple `(G', 𝓘', ∅)` of the restricted embedding is the pull-back of the piece's triple
`(G, 𝓘, ∅)` along the ambient inclusion `Sp(G') → Sp(G)` ([Wlo09, §4, (3)⇒(4)]) — the ideal by
`restrictPiece_ideal` (`rfl`), the empty family by `empty_comap`. -/
theorem ambientTriple_restrictPiece_isPullbackOf :
    (E.restrictPiece hV' hsub).ambientTriple.IsPullbackOf E.ambientTriple
      (pieceAmbientIncl (E.restrictAmbient_le hV')) :=
  ⟨rfl, (HypersurfaceFamily.empty_comap _).symm⟩

/-! ### The ambient inclusion restricted to `W'`, a diffeomorphism onto its image -/

section RestrictIncl

variable (W' : Opens (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')))

/-- **The ambient inclusion restricted to `W'`**, onto the image open `pieceAmbientImageOpens _ W'`
(the smooth morphism along which the functor is pulled back, [Kol07, 34.1]). -/
def restrictPieceIncl :
    AnalyticMap ((pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')).restrict W')
      ((pieceAmbient.{u} 𝕜 E.G).restrict (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')) :=
  AnalyticMap.restrictMap (pieceAmbientIncl (E.restrictAmbient_le hV')) W'
    (pieceAmbientImageOpens (E.restrictAmbient_le hV') W') Set.Subset.rfl

/-- The restricted inclusion is a local analytic isomorphism
(`AnalyticMap.isLocalDiffeomorph_restrictMap`). -/
theorem isLocalDiffeomorph_restrictPieceIncl :
    IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (E.restrictPieceIncl hV' W') :=
  AnalyticMap.isLocalDiffeomorph_restrictMap (isLocalDiffeomorph_pieceAmbientIncl _) W' _ _

/-- The restricted inclusion on points. -/
theorem val_restrictPieceIncl (p : (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')).restrict W') :
    (E.restrictPieceIncl hV' W' p).1 = pieceAmbientIncl (E.restrictAmbient_le hV') p.1 := rfl

/-- The restricted inclusion is bijective — injective as the inclusion is, onto its image open
(`AnalyticMap.surjective_restrictMap`). -/
theorem bijective_restrictPieceIncl : Function.Bijective (E.restrictPieceIncl hV' W') :=
  ⟨fun p q h => Subtype.ext (pieceAmbientIncl_injective _
      ((E.val_restrictPieceIncl hV' W' p).symm.trans
        ((congrArg Subtype.val h).trans (E.val_restrictPieceIncl hV' W' q)))),
    AnalyticMap.surjective_restrictMap rfl⟩

end RestrictIncl

/-! ### The commutation with local isomorphisms at the restricted inclusion: the sequences -/

section Sequences

variable (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W' : Opens (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')))
  (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 (E.restrictAmbient hV')))))

include hW' in
/-- The image of a relatively compact open is relatively compact
(`AnalyticMap.isCompact_closure_image`). -/
theorem isCompact_closure_pieceAmbientImageOpens' :
    IsCompact (closure (pieceAmbientImageOpens (E.restrictAmbient_le hV') W' :
      Set (pieceAmbient 𝕜 E.G))) :=
  AnalyticMap.isCompact_closure_image (pieceAmbientIncl (E.restrictAmbient_le hV')) hW'

include hbed in
/-- **The embedded desingularization sequence of the restricted embedding over `W'` is the
pull-back along the restricted inclusion of the sequence of the piece over the image open, empty
blow-ups erased** ([Wlo09, Theorem 6.0.6(2)] at an open embedding; [Kol07, 34.1]) — the
commutation `CommutesWithLocalIsos` of `IsEmbeddedDesing` (`hbed.2 n`) at the local analytic
isomorphism `pieceAmbientIncl`, the restricted embedding's triple being the pull-back of the
piece's (`ambientTriple_restrictPiece_isPullbackOf`). -/
theorem localResolutionSeq_restrictPiece :
    (E.restrictPiece hV' hsub).localResolutionSeq bed W' hW' =
      ((E.localResolutionSeq bed (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')
          (E.isCompact_closure_pieceAmbientImageOpens' hV' W' hW')).pullback
        (E.restrictPieceIncl hV' W') (E.isLocalDiffeomorph_restrictPieceIncl hV' W')).eraseEmpty :=
  hbed.2 n E.ambientTriple (E.restrictPiece hV' hsub).ambientTriple
    (pieceAmbientIncl (E.restrictAmbient_le hV')) (isLocalDiffeomorph_pieceAmbientIncl _)
    (E.ambientTriple_restrictPiece_isPullbackOf hV' hsub) E.domBEDan_ambientTriple
    (E.restrictPiece hV' hsub).domBEDan_ambientTriple W' hW'

/-- The restricted ideal of the restricted embedding over `W'` is the pull-back, along the
restricted inclusion, of the piece's restricted ideal over the image open — both are `𝓘` pulled
back along `W' → G` (`pullback_pullback`). -/
theorem restrictedIdeal_restrictPiece :
    (E.restrictPiece hV' hsub).restrictedIdeal W' =
      (E.restrictedIdeal (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')).pullback _
          (E.restrictPieceIncl hV' W').contMDiff :=
  (IdealSheaf.pullback_pullback E.ideal ⇑(pieceAmbientIncl (E.restrictAmbient_le hV'))
      (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff
      ⇑(AnalyticManifold.inclusion _ W')
      (AnalyticManifold.inclusion _ W').contMDiff).trans
    ((IdealSheaf.pullback_congr E.ideal _
      ((AnalyticManifold.inclusion _
        (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')).contMDiff.comp
          (E.restrictPieceIncl hV' W').contMDiff) (funext fun _ => rfl)).trans
      (IdealSheaf.pullback_pullback E.ideal
        ⇑(AnalyticManifold.inclusion _
          (pieceAmbientImageOpens (E.restrictAmbient_le hV') W'))
        (AnalyticManifold.inclusion _
          (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')).contMDiff
        ⇑(E.restrictPieceIncl hV' W') (E.restrictPieceIncl hV' W').contMDiff).symm)

/-! ### The last-stage lift -/

include hbed in
/-- **The last-stage lift** of the restricted inclusion through `localResolutionSeq_restrictPiece`
(the lift of [Kol07, Definition 30.1] at the restricted inclusion): `stageOfEq`, then
`eraseEmptyLast⁻¹`, then `pullbackLiftLast` — an analytic map from the last stage of the restricted
embedding's sequence over `W'` to the last stage of the piece's sequence over the image open (the
pattern of `liftOfLe`, `LocalResolutionRestrict.lean`). -/
def liftRestrictPiece :
    AnalyticMap
      (((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').stage (Fin.last _))
      ((E.localResolutionSeq bed (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')
        (E.isCompact_closure_pieceAmbientImageOpens' hV' W' hW')).stage (Fin.last _)) :=
  ((E.localResolutionSeq bed (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')
      (E.isCompact_closure_pieceAmbientImageOpens' hV' W' hW')).pullbackLiftLast
      (E.restrictPieceIncl hV' W') (E.isLocalDiffeomorph_restrictPieceIncl hV' W')).comp
    ((Diffeomorph.toAnalyticMap
        (((E.localResolutionSeq bed (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')
          (E.isCompact_closure_pieceAmbientImageOpens' hV' W' hW')).pullback
          (E.restrictPieceIncl hV' W')
          (E.isLocalDiffeomorph_restrictPieceIncl hV' W')).eraseEmptyLast.symm)).comp
      (Diffeomorph.toAnalyticMap
        (AnalyticManifold.BlowUpSequence.stageOfEq (E.localResolutionSeq_restrictPiece hV' hsub bed
            hbed W' hW'))))

include hbed in
/-- The lift, as a diffeomorphism — `pullbackLiftLast` of the bijective local isomorphism
`restrictPieceIncl` is a diffeomorphism (`pullbackLiftLastDiffeomorphOfBijective`), the two
transports are. -/
def liftRestrictPieceDiffeo :
    Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜)
      (((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').stage (Fin.last _))
      ((E.localResolutionSeq bed (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')
        (E.isCompact_closure_pieceAmbientImageOpens' hV' W' hW')).stage (Fin.last _)) ω :=
  (AnalyticManifold.BlowUpSequence.stageOfEq (E.localResolutionSeq_restrictPiece hV' hsub bed hbed
      W' hW')).trans
    (((E.localResolutionSeq bed (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')
        (E.isCompact_closure_pieceAmbientImageOpens' hV' W' hW')).pullback
        (E.restrictPieceIncl hV' W')
        (E.isLocalDiffeomorph_restrictPieceIncl hV' W')).eraseEmptyLast.symm.trans
      ((E.localResolutionSeq bed (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')
        (E.isCompact_closure_pieceAmbientImageOpens' hV' W'
          hW')).pullbackLiftLastDiffeomorphOfBijective (E.restrictPieceIncl hV' W')
        (E.isLocalDiffeomorph_restrictPieceIncl hV' W') (E.bijective_restrictPieceIncl hV' W')))

include hbed in
/-- The diffeomorphism and the analytic map are the same function. -/
theorem coe_liftRestrictPieceDiffeo :
    ⇑(E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW') =
      ⇑(E.liftRestrictPiece hV' hsub bed hbed W' hW') :=
  funext fun _ => rfl

include hbed in
/-- **The final strict transforms correspond under the lift**
(`strictTransformSubspaceSeq_last_of_eq_pullback_eraseEmpty`) — the final strict transform of
`𝓘'|W'` along the restricted embedding's sequence is the pull-back along `liftRestrictPiece` of
the final strict transform of `𝓘|_{g(W')}` along the piece's sequence. -/
theorem strictTransformSubspaceSeq_last_liftRestrictPiece :
    ((E.restrictPiece hV' hsub).localResolutionSeq bed W'
        hW').toSuccession.strictTransformSubspaceSeq
        ((E.restrictPiece hV' hsub).restrictedIdeal W') (Fin.last _) =
      ((E.localResolutionSeq bed (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')
          (E.isCompact_closure_pieceAmbientImageOpens' hV' W'
            hW')).toSuccession.strictTransformSubspaceSeq
        (E.restrictedIdeal (pieceAmbientImageOpens (E.restrictAmbient_le hV') W'))
        (Fin.last _)).pullback (E.liftRestrictPiece hV' hsub bed hbed W' hW')
        (E.liftRestrictPiece hV' hsub bed hbed W' hW').contMDiff :=
  AnalyticManifold.BlowUpSequence.strictTransformSubspaceSeq_last_of_eq_pullback_eraseEmpty _ _ _ _
    (E.localResolutionSeq_restrictPiece hV' hsub bed hbed W' hW') _ _
    (E.restrictedIdeal_restrictPiece hV' hsub W')

include hbed in
/-- The same, along the diffeomorphism. -/
theorem strictTransformSubspaceSeq_last_liftRestrictPieceDiffeo :
    ((E.restrictPiece hV' hsub).localResolutionSeq bed W'
        hW').toSuccession.strictTransformSubspaceSeq
        ((E.restrictPiece hV' hsub).restrictedIdeal W') (Fin.last _) =
      ((E.localResolutionSeq bed (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')
          (E.isCompact_closure_pieceAmbientImageOpens' hV' W'
            hW')).toSuccession.strictTransformSubspaceSeq
        (E.restrictedIdeal (pieceAmbientImageOpens (E.restrictAmbient_le hV') W'))
        (Fin.last _)).pullback ⇑(E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW')
        (E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW').contMDiff :=
  (E.strictTransformSubspaceSeq_last_liftRestrictPiece hV' hsub bed hbed W' hW').trans
    (IdealSheaf.pullback_congr _ _ _ (E.coe_liftRestrictPieceDiffeo hV' hsub bed hbed W' hW').symm)

include hbed in
/-- **The lift lies over the restricted inclusion** ([Kol07, Definition 30.1]) — the blow-down of
the lifted point is the inclusion of the blow-down
(`stageMap_last_pullbackLiftLast`, `stageMap_last_eraseEmptyLast_symm`,
`stageMap_last_stageOfEq`). -/
theorem stageMap_last_liftRestrictPiece
    (q : ((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').stage (Fin.last _)) :
    (E.localResolutionSeq bed (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')
        (E.isCompact_closure_pieceAmbientImageOpens' hV' W' hW')).toSuccession.stageMap (Fin.last _)
        (E.liftRestrictPiece hV' hsub bed hbed W' hW' q) =
      E.restrictPieceIncl hV' W'
        (((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').toSuccession.stageMap
          (Fin.last _) q) := by
  change (E.localResolutionSeq bed _ _).toSuccession.stageMap (Fin.last _)
      ((E.localResolutionSeq bed _ _).pullbackLiftLast (E.restrictPieceIncl hV' W')
        (E.isLocalDiffeomorph_restrictPieceIncl hV' W')
        (((E.localResolutionSeq bed _ _).pullback _ _).eraseEmptyLast.symm
          (AnalyticManifold.BlowUpSequence.stageOfEq (E.localResolutionSeq_restrictPiece hV' hsub
              bed hbed W' hW') q))) =
    _
  exact (AnalyticManifold.BlowUpSequence.stageMap_last_pullbackLiftLast _ _ _ _).trans
    (congrArg (E.restrictPieceIncl hV' W')
      ((AnalyticManifold.BlowUpSequence.stageMap_last_eraseEmptyLast_symm _ _).trans
        (AnalyticManifold.BlowUpSequence.stageMap_last_stageOfEq _ _)))

/-! ### The isomorphism of local resolutions -/

include hbed in
/-- **The local resolution of the restricted embedding over `W'` maps to the local resolution of
the piece over the image open** ([Wlo09, §4, (3)⇒(4)]; [Wlo09, Theorem 6.0.6(2)]) — the morphism
of closed subspaces `IdealSheaf.homOfPullbackEq` along the lift, with
`strictTransformSubspaceSeq_last_liftRestrictPieceDiffeo`; typed as a morphism of `K`-spaces, so
that every composite with it is a `K`-composite. -/
def localResolutionHomRestrictPiece :
    ((E.restrictPiece hV' hsub).localResolution bed W' hW').toKLocallyRingedSpace ⟶
      (E.localResolution bed (pieceAmbientImageOpens (E.restrictAmbient_le hV') W')
        (E.isCompact_closure_pieceAmbientImageOpens' hV' W' hW')).toKLocallyRingedSpace :=
  IdealSheaf.homOfPullbackEq ⇑(E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW')
    (E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW').contMDiff
    (E.strictTransformSubspaceSeq_last_liftRestrictPieceDiffeo hV' hsub bed hbed W' hW')

include hbed in
/-- It is an isomorphism of `K`-spaces — the morphism of closed subspaces along a diffeomorphism
(`isIso_homOfPullbackEq_of_diffeomorph`; the two categories share composition and identities
definitionally). -/
theorem isIso_localResolutionHomRestrictPiece :
    IsIso (E.localResolutionHomRestrictPiece hV' hsub bed hbed W' hW') := by
  obtain ⟨⟨g, h1, h2⟩⟩ := isIso_homOfPullbackEq_of_diffeomorph
    (E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW')
    (E.strictTransformSubspaceSeq_last_liftRestrictPieceDiffeo hV' hsub bed hbed W' hW')
  exact ⟨⟨g, h1, h2⟩⟩

end Sequences

/-! ### The restricted embedding lies over the inclusion, at the morphism level -/

section OverIncl

/-- `Sp(g) : Sp(G') → Sp(G)`, the morphism of ambient
spaces induced by the inclusion `g` of the shrunk ambient, typed at the abbreviations
`restrictAmbientSpace`/`ambientSpace` (the right-hand side of
`restrictAmbientKIso_hom_comp_ofRestrict`). -/
def ambientInclHom : E.restrictAmbientSpace hV' ⟶ E.ambientSpace :=
  ofManifoldHom (⇑(pieceAmbientIncl (E.restrictAmbient_le hV')))
    (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff

include hV' hsub in
/-- `openOf X V' ≤ openOf X V` for `V' ⊆ V`. -/
theorem openOf_le_openOf :
    openOf X V' ≤ openOf X V :=
  fun _ hx => mem_openOf_of_subset hsub
    (mem_of_mem_openOf hV' hx)

/-- The identification `X|V' ≅ (X|V)|_W` of
`PieceRestrict.lean`, followed by the open immersion `(X|V)|_W → X|V`, is the inclusion `X|V' → X|V`
(both are over `X`). -/
theorem subPieceIso₁_hom_comp_ofRestrict :
    (E.subPieceIso₁ hV' hsub).hom ≫
        ofRestrict (X.toKLocallyRingedSpace.restrictOpen
          (openOf X V)) (E.subPieceOpens₁ hV') =
      KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace (openOf_le_openOf hV' hsub) :=
  Hom.ext_of_comp_ofRestrict ((Category.assoc _ _ _).trans
    ((eqToIso_trans_restrictOpen_restrictOpen_iso_symm_hom_comp _ _
        (E.imageOpens_subPieceOpens₁ hV' hsub)).trans
      (KLocallyRingedSpace.restrictIncl_comp_ofRestrict _ _).symm))

/-- **The model isomorphism of the restricted embedding lies over the inclusion of the ambients,
as morphisms** — `emb' ≫ ι' ≫ Sp(g)`
is the inclusion `X|V' → X|V` followed by `emb ≫ ι` (the five-factor chain of
`restrictPieceEmbIso`, factor by factor; every junction is a syntactic `Category.assoc`, no
rewriting — the carriers mix `Opens (pieceAmbient 𝕜 E.G)` with `Opens E.ambientSpace`). -/
theorem restrictPiece_emb_comp_quotientι_comp_ambientInclHom :
    (E.restrictPiece hV' hsub).emb ≫
        (quotientι (E.restrictAmbientSpace hV') (E.restrictPiece hV' hsub).ideal ≫
          E.ambientInclHom hV') =
      KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace (openOf_le_openOf hV' hsub) ≫
        (E.emb ≫ quotientι E.ambientSpace E.ideal) := by
  -- the factors
  have e₀ : (E.restrictPiece hV' hsub).emb =
      (E.subPieceIso₁ hV' hsub).hom ≫
        ((restrictOpenIso E.embKIso
          (quotientOpens E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))).hom ≫
          ((restrictOpen_quotient_iso E.ambientSpace E.ideal
              (coordPreimage (E.restrictAmbient hV') E.G)).inv ≫
            ((quotient_kIso (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
                (coordPreimage (E.restrictAmbient hV') E.G))).inv ≫
              (quotientIsoOfEq (E.transportIdeal_restrictAmbientKIso hV')).hom))) := rfl
  -- (c1) the transport isomorphism lies over the identity
  have c1 : (quotientIsoOfEq (E.transportIdeal_restrictAmbientKIso hV')).hom ≫
        (quotientι (E.restrictAmbientSpace hV') (E.restrictPiece hV' hsub).ideal ≫
          E.ambientInclHom hV') =
      quotientι (E.restrictAmbientSpace hV') (transportIdeal (E.restrictAmbientKIso hV')
          (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))) ≫
        E.ambientInclHom hV' :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ E.ambientInclHom hV')
      (quotientIsoOfEq_hom_comp_quotientι (E.transportIdeal_restrictAmbientKIso hV')))
  -- (c2) `Sp(g)` through `Sp(G') ≅ Sp(G)|U → Sp(G)`
  have c2 : quotientι (E.restrictAmbientSpace hV') (transportIdeal (E.restrictAmbientKIso hV')
          (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))) ≫
        E.ambientInclHom hV' =
      quotientι (E.restrictAmbientSpace hV') (transportIdeal (E.restrictAmbientKIso hV')
          (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))) ≫
        ((E.restrictAmbientKIso hV').hom ≫
          ofRestrict E.ambientSpace (coordPreimage (E.restrictAmbient hV') E.G)) :=
    congrArg (fun k => quotientι (E.restrictAmbientSpace hV') (transportIdeal
      (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
        (coordPreimage (E.restrictAmbient hV') E.G))) ≫ k)
      (E.restrictAmbientKIso_hom_comp_ofRestrict hV').symm
  -- (c3) the quotient of the `K`-isomorphism, cancelled
  have hq : quotientι (E.restrictAmbientSpace hV') (transportIdeal (E.restrictAmbientKIso hV')
          (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))) ≫
        (E.restrictAmbientKIso hV').hom =
      quotientMap (E.restrictAmbientKIso hV').hom (transportIdeal (E.restrictAmbientKIso hV')
          (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G)))
        (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))
        (QuotientSpace.compat_comap _ _) ≫
      quotientι (E.ambientSpace.restrictOpen (coordPreimage (E.restrictAmbient hV') E.G))
        (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G)) :=
    (quotientMap_comp_quotientι _ _ _ _).symm
  have c3 : (quotient_kIso (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
        (coordPreimage (E.restrictAmbient hV') E.G))).inv ≫
        (quotientι (E.restrictAmbientSpace hV') (transportIdeal (E.restrictAmbientKIso hV')
          (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))) ≫
          ((E.restrictAmbientKIso hV').hom ≫
            ofRestrict E.ambientSpace (coordPreimage (E.restrictAmbient hV') E.G))) =
      quotientι (E.ambientSpace.restrictOpen (coordPreimage (E.restrictAmbient hV') E.G))
          (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G)) ≫
        ofRestrict E.ambientSpace (coordPreimage (E.restrictAmbient hV') E.G) :=
    (congrArg (fun k => (quotient_kIso (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace
        E.ideal (coordPreimage (E.restrictAmbient hV') E.G))).inv ≫ k)
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫
          ofRestrict E.ambientSpace (coordPreimage (E.restrictAmbient hV') E.G)) hq).trans
        (Category.assoc _ _ _)))).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫
          (quotientι (E.ambientSpace.restrictOpen (coordPreimage (E.restrictAmbient hV') E.G))
            (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G)) ≫
          ofRestrict E.ambientSpace (coordPreimage (E.restrictAmbient hV') E.G)))
        (quotient_kIso_inv_comp_quotientMap (E.restrictAmbientKIso hV') _)).trans
        (Category.id_comp _)))
  -- (c4) the restriction-quotient isomorphism, cancelled
  have c4 : (restrictOpen_quotient_iso E.ambientSpace E.ideal
        (coordPreimage (E.restrictAmbient hV') E.G)).inv ≫
        (quotientι (E.ambientSpace.restrictOpen (coordPreimage (E.restrictAmbient hV') E.G))
          (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G)) ≫
          ofRestrict E.ambientSpace (coordPreimage (E.restrictAmbient hV') E.G)) =
      ofRestrict (E.ambientSpace.quotient E.ideal)
          (quotientOpens E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G)) ≫
        quotientι E.ambientSpace E.ideal :=
    (congrArg (fun k => (restrictOpen_quotient_iso E.ambientSpace E.ideal
        (coordPreimage (E.restrictAmbient hV') E.G)).inv ≫ k)
      (quotientMap_comp_quotientι (ofRestrict E.ambientSpace
        (coordPreimage (E.restrictAmbient hV') E.G))
        (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G)) E.ideal
        (QuotientSpace.compat_comap _ _)).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ quotientι E.ambientSpace E.ideal)
        (restrictOpen_quotient_iso_inv_comp_quotientMap E.ambientSpace E.ideal
          (coordPreimage (E.restrictAmbient hV') E.G))))
  -- (c5) the restricted `K`-isomorphism lies over `emb`
  have c5 : (restrictOpenIso E.embKIso
        (quotientOpens E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))).hom ≫
        (ofRestrict (E.ambientSpace.quotient E.ideal)
            (quotientOpens E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G)) ≫
          quotientι E.ambientSpace E.ideal) =
      (ofRestrict (X.toKLocallyRingedSpace.restrictOpen
          (openOf X V)) (E.subPieceOpens₁ hV') ≫ E.emb) ≫
        quotientι E.ambientSpace E.ideal :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ quotientι E.ambientSpace E.ideal)
      (restrictOpenIso_hom_comp_ofRestrict E.embKIso
        (quotientOpens E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))))
  -- assemble, innermost first
  have t4 := (Category.assoc _ _ _).trans
    ((congrArg (fun k => (quotient_kIso (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace
      E.ideal (coordPreimage (E.restrictAmbient hV') E.G))).inv ≫ k) (c1.trans c2)).trans c3)
  have t3 := (Category.assoc _ _ _).trans
    ((congrArg (fun k => (restrictOpen_quotient_iso E.ambientSpace E.ideal
      (coordPreimage (E.restrictAmbient hV') E.G)).inv ≫ k) t4).trans c4)
  have t2 := (Category.assoc _ _ _).trans
    ((congrArg (fun k => (restrictOpenIso E.embKIso (quotientOpens E.ambientSpace E.ideal
      (coordPreimage (E.restrictAmbient hV') E.G))).hom ≫ k) t3).trans
      (c5.trans (Category.assoc _ _ _)))
  have t1 := (Category.assoc _ _ _).trans
    ((congrArg (fun k => (E.subPieceIso₁ hV' hsub).hom ≫ k) t2).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ (E.emb ≫ quotientι E.ambientSpace E.ideal))
          (E.subPieceIso₁_hom_comp_ofRestrict hV' hsub))))
  exact (congrArg (fun k => k ≫ (quotientι (E.restrictAmbientSpace hV')
    (E.restrictPiece hV' hsub).ideal ≫ E.ambientInclHom hV')) e₀).trans t1

end OverIncl

/-! ### The compatibility square: the isomorphism of local resolutions lies over `X` -/

section Square

variable (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W' : Opens (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')))
  (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 (E.restrictAmbient hV')))))

local notation "𝕊" => toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
local notation "𝔚" => pieceAmbientImageOpens (E.restrictAmbient_le hV') W'
local notation "𝔥" => E.isCompact_closure_pieceAmbientImageOpens' hV' W' hW'

include hbed in
/-- **The square of the ambient maps** — `incl_{g(W')} ∘ σ ∘ D = g ∘ incl_{W'} ∘ σ'` as functions
from the last
stage of the restricted embedding's sequence to `G` (`stageMap_last_liftRestrictPiece`
pointwise). -/
theorem inclusion_comp_composite_comp_liftRestrictPieceDiffeo :
    (⇑(AnalyticManifold.inclusion _ 𝔚) ∘
        ⇑(E.localResolutionSeq bed 𝔚 𝔥).toSuccession.composite) ∘
        ⇑(E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW') =
      (⇑(pieceAmbientIncl (E.restrictAmbient_le hV')) ∘
          ⇑(AnalyticManifold.inclusion _ W')) ∘
        ⇑((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').toSuccession.composite :=
  funext fun q =>
    congrArg Subtype.val (E.stageMap_last_liftRestrictPiece hV' hsub bed hbed W' hW' q)

include hbed in
/-- **The isomorphism of local resolutions lies over `X`** — `Φ ≫ (Ỹ(g W') → X) = (Ỹ'(W') → X)`;
the argument of `localResolutionToPiece_comp_localResolutionHomOfLe` in the two generic lemmas
`layer_square_comp_eq` (the layers) and `over_square_comp_embInv_eq` (the chain
`restrictPiece_emb_comp_quotientι_comp_ambientInclHom` moves `emb'` across,
`Hom.ext_of_comp_quotientι` cancels `ι`, `embInv` is prepended), instantiated
in the category of analytic `𝕜`-spaces; the square of the ambient maps is
`inclusion_comp_composite_comp_liftRestrictPieceDiffeo` read as morphisms (`ofManifoldHom_comp`,
`ofManifoldHom_congr`). -/
theorem localResolutionHomRestrictPiece_comp_toSpaceMap :
    E.localResolutionHomRestrictPiece hV' hsub bed hbed W' hW' ≫ E.toSpaceMap bed 𝔚 𝔥 =
      (E.restrictPiece hV' hsub).toSpaceMap bed W' hW' := by
  -- the square of the ambient maps, as morphisms of `𝕜`-spaces
  have s1 : (show
      𝕊 ((E.localResolutionSeq bed 𝔚 𝔥).stage (Fin.last _)) ⟶
      𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict 𝔚) from
        toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (E.localResolutionSeq bed 𝔚 𝔥).toSuccession.composite) ≫
        (show 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict 𝔚) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (AnalyticManifold.inclusion _ 𝔚)
          (AnalyticManifold.inclusion _ 𝔚).contMDiff) =
      (show 𝕊 ((E.localResolutionSeq bed 𝔚 𝔥).stage (Fin.last _)) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G)
          from
        ofManifoldHom (⇑(AnalyticManifold.inclusion _ 𝔚) ∘
            ⇑(E.localResolutionSeq bed 𝔚 𝔥).toSuccession.composite)
          ((AnalyticManifold.inclusion _ 𝔚).contMDiff.comp
            (E.localResolutionSeq bed 𝔚 𝔥).toSuccession.composite.contMDiff)) :=
    (ofManifoldHom_comp _ _ _ _).symm
  have s2 : (show
      𝕊 (((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
      𝕊 ((E.localResolutionSeq bed 𝔚 𝔥).stage (Fin.last _)) from
        ofManifoldHom ⇑(E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW')
          (E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW').contMDiff) ≫
        (show 𝕊 ((E.localResolutionSeq bed 𝔚 𝔥).stage (Fin.last _)) ⟶
            𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (⇑(AnalyticManifold.inclusion _ 𝔚) ∘
            ⇑(E.localResolutionSeq bed 𝔚 𝔥).toSuccession.composite)
          ((AnalyticManifold.inclusion _ 𝔚).contMDiff.comp
            (E.localResolutionSeq bed 𝔚 𝔥).toSuccession.composite.contMDiff)) =
      (show 𝕊 (((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
          𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom ((⇑(AnalyticManifold.inclusion _ 𝔚) ∘
            ⇑(E.localResolutionSeq bed 𝔚 𝔥).toSuccession.composite) ∘
            ⇑(E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW'))
          (((AnalyticManifold.inclusion _ 𝔚).contMDiff.comp
            (E.localResolutionSeq bed 𝔚 𝔥).toSuccession.composite.contMDiff).comp
            (E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW').contMDiff)) :=
    (ofManifoldHom_comp _ _ _ _).symm
  have s3 : (show
      𝕊 ((pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')).restrict W') ⟶
      𝕊 (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')) from
        ofManifoldHom (AnalyticManifold.inclusion _ W')
          (AnalyticManifold.inclusion _ W').contMDiff) ≫
        (E.ambientInclHom hV' : 𝕊 (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')) ⟶ 𝕊
            (pieceAmbient.{u} 𝕜 E.G)) =
      (show 𝕊 ((pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')).restrict W') ⟶
          𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (⇑(pieceAmbientIncl (E.restrictAmbient_le hV')) ∘
            ⇑(AnalyticManifold.inclusion _ W'))
          ((pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff.comp
            (AnalyticManifold.inclusion _ W').contMDiff)) :=
    (ofManifoldHom_comp _ _ _ _).symm
  have s4 : (show
      𝕊 (((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
      𝕊 ((pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')).restrict W') from
        toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          ((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').toSuccession.composite) ≫
        (show 𝕊 ((pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')).restrict W') ⟶
            𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (⇑(pieceAmbientIncl (E.restrictAmbient_le hV')) ∘
            ⇑(AnalyticManifold.inclusion _ W'))
          ((pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff.comp
            (AnalyticManifold.inclusion _ W').contMDiff)) =
      (show 𝕊 (((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
          𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom ((⇑(pieceAmbientIncl (E.restrictAmbient_le hV')) ∘
            ⇑(AnalyticManifold.inclusion _ W')) ∘
            ⇑((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').toSuccession.composite)
          (((pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff.comp
            (AnalyticManifold.inclusion _ W').contMDiff).comp
            ((E.restrictPiece hV' hsub).localResolutionSeq bed W'
              hW').toSuccession.composite.contMDiff)) :=
    (ofManifoldHom_comp _ _ _ _).symm
  have e4 := (congrArg
      (fun k => (show
      𝕊 (((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
      𝕊 ((E.localResolutionSeq bed 𝔚 𝔥).stage (Fin.last _)) from
      ofManifoldHom ⇑(E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW')
        (E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW').contMDiff) ≫ k) s1).trans
    (s2.trans ((ofManifoldHom_congr
      (E.inclusion_comp_composite_comp_liftRestrictPieceDiffeo hV' hsub bed hbed W' hW') _).trans
      ((congrArg (fun k =>
          (show 𝕊 (((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').stage (Fin.last _))
          ⟶ 𝕊 ((pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')).restrict W') from
        toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          ((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').toSuccession.composite) ≫ k)
        s3).trans s4).symm))
  -- the two composites into `Sp(G)` agree (the layers)
  have key := CategoryTheory.layer_square_comp_eq (C := AnalyticSpace.{u} 𝕜)
    (E.localResolutionHomRestrictPiece hV' hsub bed hbed W' hW')
    (E.localResolutionMap bed 𝔚 𝔥) (E.restrictedIdealHom 𝔚) E.ideal.toAnalyticSpaceι
    ((E.restrictPiece hV' hsub).localResolutionMap bed W' hW')
    ((E.restrictPiece hV' hsub).restrictedIdealHom W')
    ((E.restrictPiece hV' hsub).ideal.toAnalyticSpaceι :
      ((E.restrictPiece hV' hsub).ideal.toAnalyticSpace ⟶ 𝕊
          (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV'))))
    (E.ambientInclHom hV' : 𝕊 (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')) ⟶ 𝕊
        (pieceAmbient.{u} 𝕜 E.G))
    (E.restrictedIdeal 𝔚).toAnalyticSpaceι
    (show 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict 𝔚) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) from
      ofManifoldHom (AnalyticManifold.inclusion _ 𝔚)
        (AnalyticManifold.inclusion _ 𝔚).contMDiff)
    ((E.localResolutionSeq bed 𝔚 𝔥).toSuccession.strictTransformSubspaceSeq
      (E.restrictedIdeal 𝔚) (Fin.last _)).toAnalyticSpaceι
    (show 𝕊 ((E.localResolutionSeq bed 𝔚 𝔥).stage (Fin.last _)) ⟶
        𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict 𝔚) from
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (E.localResolutionSeq bed 𝔚 𝔥).toSuccession.composite)
    (((E.restrictPiece hV' hsub).restrictedIdeal W').toAnalyticSpaceι :
      (((E.restrictPiece hV' hsub).restrictedIdeal W').toAnalyticSpace ⟶ 𝕊
          ((pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')).restrict W')))
    (show 𝕊 ((pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')).restrict W') ⟶
        𝕊 (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')) from
      ofManifoldHom (AnalyticManifold.inclusion _ W')
        (AnalyticManifold.inclusion _ W').contMDiff)
    (((E.restrictPiece hV' hsub).localResolutionSeq bed W'
        hW').toSuccession.strictTransformSubspaceSeq
      ((E.restrictPiece hV' hsub).restrictedIdeal W') (Fin.last _)).toAnalyticSpaceι
    (show 𝕊 (((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
        𝕊 ((pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')).restrict W') from
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').toSuccession.composite)
    (show 𝕊 (((E.restrictPiece hV' hsub).localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
        𝕊 ((E.localResolutionSeq bed 𝔚 𝔥).stage (Fin.last _)) from
      ofManifoldHom ⇑(E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW')
        (E.liftRestrictPieceDiffeo hV' hsub bed hbed W' hW').contMDiff)
    (E.toAnalyticSpaceι_comp_restrictedIdealHom 𝔚)
    ((E.restrictPiece hV' hsub).toAnalyticSpaceι_comp_restrictedIdealHom W')
    (E.localResolutionMap_comp_ι bed 𝔚 𝔥)
    ((E.restrictPiece hV' hsub).localResolutionMap_comp_ι bed W' hW')
    (homOfPullbackEq_comp_toAnalyticSpaceι _ _
      (E.strictTransformSubspaceSeq_last_liftRestrictPieceDiffeo hV' hsub bed hbed W' hW'))
    e4
  -- move `emb'` across the chain, cancel `ι` and `emb`, prepend `embInv`
  have sq := CategoryTheory.over_square_comp_embInv_eq (C := AnalyticSpace.{u} 𝕜)
    (E.localResolutionHomRestrictPiece hV' hsub bed hbed W' hW')
    (E.localResolutionMap bed 𝔚 𝔥) (E.restrictedIdealHom 𝔚) E.ideal.toAnalyticSpaceι
    ((E.restrictPiece hV' hsub).localResolutionMap bed W' hW')
    ((E.restrictPiece hV' hsub).restrictedIdealHom W')
    ((E.restrictPiece hV' hsub).ideal.toAnalyticSpaceι :
      ((E.restrictPiece hV' hsub).ideal.toAnalyticSpace ⟶ 𝕊
          (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV'))))
    (E.ambientInclHom hV' : 𝕊 (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')) ⟶ 𝕊
        (pieceAmbient.{u} 𝕜 E.G))
    E.emb E.embInv (E.restrictPiece hV' hsub).emb (E.restrictPiece hV' hsub).embInv
    (KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace (openOf_le_openOf hV' hsub) :
      X.restrictSet V' ⟶ X.restrictSet V)
    (fun g g' h => Hom.ext_of_comp_quotientι
      (X := ofManifold 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 E.G)) E.ideal h)
    E.embInv_comp_emb E.emb_comp_embInv (E.restrictPiece hV' hsub).emb_comp_embInv key
    (E.restrictPiece_emb_comp_quotientι_comp_ambientInclHom hV' hsub)
  -- the maps to `X`
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k :
          ((E.restrictPiece hV' hsub).localResolution bed W' hW').toKLocallyRingedSpace ⟶
            (X.restrictSet V).toKLocallyRingedSpace =>
        k ≫ ofRestrict X.toKLocallyRingedSpace (openOf X V))
      sq).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => ((E.restrictPiece hV' hsub).localResolutionToPiece bed W' hW' :
            ((E.restrictPiece hV' hsub).localResolution bed W' hW').toKLocallyRingedSpace ⟶
              (X.restrictSet V').toKLocallyRingedSpace) ≫ k)
          (KLocallyRingedSpace.restrictIncl_comp_ofRestrict X.toKLocallyRingedSpace
            (openOf_le_openOf hV' hsub)))))

end Square

end PieceEmbedding

/-! ### The local resolution of the restricted embedding is the restriction of the local
resolution -/

namespace PieceEmbedding

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V) (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))
  {V' : Set X} (hV' : IsOpen V') (hsub : V' ⊆ V)
  (W' : Opens (pieceAmbient.{u} 𝕜 (E.restrictAmbient hV')))
  (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 (E.restrictAmbient hV')))))
  (hWW' : pieceAmbientImageOpens (E.restrictAmbient_le hV') W' ≤ W)

local notation "𝔚" => pieceAmbientImageOpens (E.restrictAmbient_le hV') W'
local notation "𝔥" => E.isCompact_closure_pieceAmbientImageOpens' hV' W' hW'

include hbed hWW' in
/-- **Transport of the local resolution along the open inclusion of ambients**
([Wlo09, §4, (3)⇒(4)]; [Wlo09, Theorem 6.0.6(2)]; [Kol07, 34.1]) — the local resolution of the
restricted embedding `E|V'` over `W' ⋐ G'` is the part of the local resolution of `E` over
`W ⊇ g(W')` lying over the points of `X` with ambient point in `g(W')`, compatibly with the maps
to `X`. The isomorphism is `Φ` (`localResolutionHomRestrictPiece`, the sequences identified by the
commutation with local isomorphisms) followed by the open immersion `Ỹ(g W') → Ỹ(W)`
(`localResolutionHomOfLe`) read onto its range (`isoOfRangeEq`); the range is the part over the
base open by `preimage_subset_range_localResolutionHomOfLe` and the square
`localResolutionToPiece_comp_localResolutionHomOfLe`; the compatibility is
`localResolutionHomRestrictPiece_comp_toSpaceMap`. -/
theorem exists_localResolution_restrictPiece_iso :
    ∃ e : ((E.restrictPiece hV' hsub).localResolution bed W' hW').toKLocallyRingedSpace ⟶
        (E.localResolution bed W hW).toKLocallyRingedSpace.restrictOpen
          (GlueOver.overOpens (R := fun _ : PUnit.{u + 1} => E.localResolution bed W hW)
            (fun _ => E.toSpaceMap bed W hW) PUnit.unit
            (E.domOpens (pieceAmbientImageOpens (E.restrictAmbient_le hV') W'))),
      IsIso e ∧
        e ≫ ofRestrict _ _ ≫ E.toSpaceMap bed W hW =
          (E.restrictPiece hV' hsub).toSpaceMap bed W' hW' := by
  -- the open immersion `χ : Ỹ(g W') → Ỹ(W)` and its range: the part over the base open
  have hχ : LocallyRingedSpace.IsOpenImmersion (E.localResolutionHomOfLe bed W hW 𝔚 𝔥 hWW').1 :=
    E.isOpenImmersion_localResolutionHomOfLe bed W hW 𝔚 𝔥 hWW'
  have hO : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (E.localResolution bed W hW).toKLocallyRingedSpace
      (GlueOver.overOpens (R := fun _ : PUnit.{u + 1} => E.localResolution bed W hW)
        (fun _ => E.toSpaceMap bed W hW) PUnit.unit (E.domOpens 𝔚))).1 := inferInstance
  have hrange : Set.range (KLocallyRingedSpace.Hom.toFun (E.localResolutionHomOfLe bed W hW 𝔚 𝔥
      hWW' :
          (E.localResolution bed 𝔚 𝔥).toKLocallyRingedSpace ⟶
            (E.localResolution bed W hW).toKLocallyRingedSpace)) =
      Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict (E.localResolution bed W
          hW).toKLocallyRingedSpace
        (GlueOver.overOpens (R := fun _ : PUnit.{u + 1} => E.localResolution bed W hW)
          (fun _ => E.toSpaceMap bed W hW) PUnit.unit (E.domOpens 𝔚)))) := by
    rw [range_toFun_ofRestrict]
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      change KLocallyRingedSpace.Hom.toFun (E.toSpaceMap bed W hW)
          (KLocallyRingedSpace.Hom.toFun (E.localResolutionHomOfLe bed W hW 𝔚 𝔥 hWW') w) ∈
              E.domOpens 𝔚
      have h1 : (E.localResolutionToPiece bed W hW)
          (E.localResolutionHomOfLe bed W hW 𝔚 𝔥 hWW' w) =
          (E.localResolutionToPiece bed 𝔚 𝔥) w :=
        congrArg
          (fun k => k w)
          (E.localResolutionToPiece_comp_localResolutionHomOfLe bed W hW 𝔚 𝔥 hWW')
      exact (E.mem_domOpens).mpr ⟨_, Set.mem_of_eq_of_mem h1
        (E.range_localResolutionToPiece_subset bed 𝔚 𝔥 ⟨w, rfl⟩), rfl⟩
    · intro hz
      obtain ⟨y, hy, hyz⟩ := (E.mem_domOpens).mp
        (hz : KLocallyRingedSpace.Hom.toFun (E.toSpaceMap bed W hW) z ∈ E.domOpens 𝔚)
      have hmem :
          (E.localResolutionToPiece bed W hW) z ∈
          E.embPreimage 𝔚 :=
        Set.mem_of_eq_of_mem (Subtype.ext hyz :
          y =
              (E.localResolutionToPiece bed W hW)
                  z).symm hy
      exact E.preimage_subset_range_localResolutionHomOfLe bed W hW 𝔚 𝔥 hWW' _ Set.Subset.rfl hmem
  have hχt : (E.localResolutionHomOfLe bed W hW 𝔚 𝔥 hWW' :
        (E.localResolution bed 𝔚 𝔥).toKLocallyRingedSpace ⟶
          (E.localResolution bed W hW).toKLocallyRingedSpace) ≫ E.toSpaceMap bed W hW =
      E.toSpaceMap bed 𝔚 𝔥 :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k : (E.localResolution bed 𝔚 𝔥).toKLocallyRingedSpace ⟶
          (X.restrictSet V).toKLocallyRingedSpace =>
        k ≫ ofRestrict X.toKLocallyRingedSpace (openOf X V))
        (E.localResolutionToPiece_comp_localResolutionHomOfLe bed W hW 𝔚 𝔥 hWW'))
  refine ⟨E.localResolutionHomRestrictPiece hV' hsub bed hbed W' hW' ≫
      (@isoOfRangeEq _ _ _ _ _ _ _ hχ hO hrange).hom,
    @IsIso.comp_isIso _ _ _ _ _ _ _
      (E.isIso_localResolutionHomRestrictPiece hV' hsub bed hbed W' hW') (Iso.isIso_hom _), ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => E.localResolutionHomRestrictPiece hV' hsub bed hbed W' hW' ≫ k)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ E.toSpaceMap bed W hW)
          (@isoOfRangeEq_hom_comp _ _ _ _ _ _ _ hχ hO hrange)).trans hχt))).trans
      (E.localResolutionHomRestrictPiece_comp_toSpaceMap hV' hsub bed hbed W' hW'))

end PieceEmbedding

end Hironaka.Manifold

end
