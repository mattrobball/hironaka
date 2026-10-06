/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionOn
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlue
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrictHom
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The parts of a piece's local resolution over a base open, read on the ambient

Two bookkeeping identities for the assembly of the mixed-pair transition of the common datum
(`CoproductMixedTransition.lean`):

* a point of a piece's local resolution lies over the base open `domOpens Q` (in `X`) iff its
  ambient point — the last stage's composite blow-down read through the closed inclusion — lies
  in the ambient open `Q` (`toFun_toSpaceMap_eq`, `pieceOverIncl_mem_domOpens_iff`,
  `localResolutionMap_comp_ι`);
* along the open immersion `localResolutionHomOn` (`LocalResolutionOn.lean`) of the piece's local
  resolution over `W'` into the local resolution of `(T, W)` along an open embedding `g` of
  admissible inputs, the part of the source over the base open `domOpens Q` (`Q ≤ W'`) maps ONTO
  the part of the target over the ambient open `g(Q)` (`range_toFun_localResolutionHomOn`,
  `stageMap_last_liftOn`).

Both are used by `isoOfRangeEq` in the assembly: the two padded pieces' parts over one base open
`P` are identified with the local resolution of the common admissible input over `W₁'` through the
common run's local resolution. `hbed` is the only hypothesis. Not in the sources; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set
open AnalyticSpace.KLocallyRingedSpace AnalyticManifold.BlowUpSequence
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.PieceEmbedding

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V) (bed : BEDanFamStar.{u} 𝕜)

/-- **A point of the local resolution lies over the base open of `Q` iff its ambient point lies in
`Q`** — `toSpaceMap = pieceOverIncl ∘ Π`
(`toFun_toSpaceMap_eq`), `pieceOverIncl_mem_domOpens_iff`, and the square
`ι_W ∘ Π = composite ∘ ι_Y` (`localResolutionMap_comp_ι`). -/
theorem toFun_toSpaceMap_mem_domOpens_iff (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) (Q : Opens (pieceAmbient.{u} 𝕜 E.G))
    (y : E.localResolution bed W hW) :
    Hom.toFun (E.toSpaceMap bed W hW) y ∈ E.domOpens Q ↔
      ((E.localResolutionSeq bed W hW).toSuccession.stageMap (Fin.last _)
        (((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq
            (E.restrictedIdeal W) (Fin.last _)).toAnalyticSpaceι y)).1 ∈ Q := by
  rw [E.toFun_toSpaceMap_eq bed W hW y]
  refine (E.pieceOverIncl_mem_domOpens_iff W Q _).trans ?_
  have h : (E.restrictedIdeal W).toAnalyticSpaceι
      (E.localResolutionMap bed W hW y) =
      (E.localResolutionSeq bed W hW).toSuccession.composite
        (((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq
            (E.restrictedIdeal W) (Fin.last _)).toAnalyticSpaceι y) :=
    congrArg (fun k => k y)
      (E.localResolutionMap_comp_ι bed W hW)
  exact Iff.of_eq (congrArg (fun p : (pieceAmbient.{u} 𝕜 E.G).restrict W => p.1 ∈ Q) h)

variable {m : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
  (W : Opens M) (hW : IsCompact (closure (W : Set M)))
  (g : AnalyticMap (pieceAmbient.{u} 𝕜 E.G) M) (hg : IsAnalyticOpenEmbedding g)
  (hpb : E.ambientTriple.IsPullbackOf T g) (W' : Opens (pieceAmbient.{u} 𝕜 E.G))
  (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 E.G))))
  (hle : ⇑g '' (W' : Set (pieceAmbient 𝕜 E.G)) ⊆ (W : Set M)) (hbed : bed.IsEmbeddedDesing)

/-- **The part of the piece's local resolution over the base open `domOpens Q` maps under
`localResolutionHomOn` ONTO the part of the target's local resolution over the ambient open `g(Q)`**
(`Q ≤ W'`): the lift covers `g`
(`stageMap_last_liftOn`), the range of the immersion is the part over `g(W')`
(`range_toFun_localResolutionHomOn`), and `g` is injective. -/
theorem range_ofRestrict_comp_localResolutionHomOn (Q : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hQ : Q ≤ W') :
    Set.range (Hom.toFun
        (ofRestrict (E.localResolution bed W' hW').toKLocallyRingedSpace
          (Opens.comap ⟨Hom.toFun (E.toSpaceMap bed W' hW'),
            Hom.continuous_toFun (E.toSpaceMap bed W' hW')⟩ (E.domOpens Q)) ≫
          (bed.localResolutionHomOn T hT W hW E.ambientTriple E.domBEDan_ambientTriple g hg hpb
              W' hW' hle hbed :
            (E.localResolution bed W' hW').toKLocallyRingedSpace ⟶
              (bed.localResolutionOn T hT W hW).toKLocallyRingedSpace))) =
      {y | ((bed.seqOn T hT W hW).toSuccession.stageMap (Fin.last _)
        ((bed.lastIdealOn T hT W hW).toAnalyticSpaceι
            y)).1 ∈
          ⇑g '' (Q : Set (pieceAmbient.{u} 𝕜 E.G))} := by
  -- the ambient point of the image is `g` of the ambient point
  have hamb : ∀ y : E.localResolution bed W' hW',
      ((bed.seqOn T hT W hW).toSuccession.stageMap (Fin.last _)
        ((bed.lastIdealOn T hT W hW).toAnalyticSpaceι
          ((bed.localResolutionHomOn T hT W hW E.ambientTriple E.domBEDan_ambientTriple g hg hpb
              W' hW' hle hbed) y))).1 =
      g ((E.localResolutionSeq bed W' hW').toSuccession.stageMap (Fin.last _)
        (((E.localResolutionSeq bed W' hW').toSuccession.strictTransformSubspaceSeq
            (E.restrictedIdeal W') (Fin.last _)).toAnalyticSpaceι y)).1 :=
    fun y => bed.stageMap_last_liftOn T hT W hW E.ambientTriple E.domBEDan_ambientTriple g hg hpb
      W' hW' hle hbed _
  ext z
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    change ((bed.seqOn T hT W hW).toSuccession.stageMap (Fin.last _)
      ((bed.lastIdealOn T hT W hW).toAnalyticSpaceι
        ((bed.localResolutionHomOn T hT W hW E.ambientTriple E.domBEDan_ambientTriple g hg hpb W'
            hW' hle hbed) y))).1 ∈ ⇑g '' (Q : Set _)
    exact ⟨_, (E.toFun_toSpaceMap_mem_domOpens_iff bed W' hW' Q y).mp hy, (hamb y).symm⟩
  · intro hz
    have hz' : z ∈ Set.range ⇑(bed.localResolutionHomOn T hT W hW E.ambientTriple
        E.domBEDan_ambientTriple g hg hpb W' hW' hle hbed) := by
      rw [bed.range_toFun_localResolutionHomOn T hT W hW E.ambientTriple E.domBEDan_ambientTriple g
        hg hpb W' hW' hle hbed]
      exact Set.image_mono hQ hz
    obtain ⟨y, rfl⟩ := hz'
    obtain ⟨q, hq, hqz⟩ := hz
    have hgq : g q = g ((E.localResolutionSeq bed W' hW').toSuccession.stageMap (Fin.last _)
        (((E.localResolutionSeq bed W' hW').toSuccession.strictTransformSubspaceSeq
            (E.restrictedIdeal W') (Fin.last _)).toAnalyticSpaceι y)).1 :=
      hqz.trans (hamb y)
    have hyQ : ((E.localResolutionSeq bed W' hW').toSuccession.stageMap (Fin.last _)
        (((E.localResolutionSeq bed W' hW').toSuccession.strictTransformSubspaceSeq
            (E.restrictedIdeal W') (Fin.last _)).toAnalyticSpaceι y)).1 ∈ Q :=
      Set.mem_of_eq_of_mem (hg.2 hgq).symm hq
    exact ⟨⟨y, (E.toFun_toSpaceMap_mem_domOpens_iff bed W' hW' Q y).mpr hyQ⟩, rfl⟩

end Hironaka.Manifold.PieceEmbedding

end
