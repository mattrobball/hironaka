/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.ClosedSubspaceHom
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueProof
import Hironaka.AnalyticSpace.Glue.OverLemmas
import Hironaka.AnalyticSpace.Glue.OverProper
import Hironaka.AnalyticSpace.ProperRestrict
import Hironaka.AnalyticSpace.Sigma
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionIndependent
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrict
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceTransitionGlue
import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The gluing datum of the local resolutions

Włodarczyk's gluing of the canonical desingularizations of the local embeddings
[Wlo09, §4, (3)⇒(4)]: under `hbed` and the independence of the local resolution from the embedding
(as the hypothesis `LocalResolutionIndependentOn X bed`), a gluing datum `ResolutionGluing D bed`
exists — the relatively compact ambient opens `W_i` over the inner opens (`exists_W`), the
transitions on the overlaps of the base opens (`exists_transition`), and
`GlueOver.exists_glueOver_of_transitions` (`Hironaka/AnalyticSpace/Glue/OverLemmas.lean`), whose
cocycle, `t_id` and Hausdorffness come from the UNIQUENESS of the transitions
(`transition_unique`). This is the form of `resolutionGluesOn_of_isEmbeddedDesing`
(`GluingProperties.lean`) with the independence as a hypothesis; that module discharges `hind`.

`isProperMap_resolutionOnMap` (Włodarczyk: `des_V : Ṽ → V` is proper, [Wlo09, §4, (3)⇒(4)]): the
map `Π_U : resolutionOn D bed → X|U` is proper for an OPEN `U`. Over each base open
`pieceDom i (W i)` the glued space is the local resolution `Ỹ_i` of the piece and the descended
map is the piece map `Π_i` (`GlueOver.isProperMap_restrictPreimage_descMap`);
`Π_i : Ỹ_i → Sp(W)/𝓘|W` is proper because it lies over the proper composite `σ^r` along the closed
embedding of the strict transform (`isProperMap_toFun_localResolutionMap`), and `Sp(W)/𝓘|W → X` is
an open immersion onto the base open (`range_pieceOverIncl`); the base opens cover `U ⊆ ⋃ inner i`
(`isProperMap_restrictPreimage_of_cover`). Two remarks on the hypotheses: `hU : IsOpen U` is
NECESSARY (for a non-open `U` the convention `openOf` makes `Π_U` the full map `Ṽ → X`, whose image
is the open `⋃ pieceDom i`), and the theorem takes no hypothesis on `bed` (without a gluing
datum the pair is `⟨X, 𝟙 X⟩` and `Π_U` is the identity of `X|U`).

Kollár's counterpart is the gluing of the local resolutions by a formal property of blow-up
sequence functors [Kol07, Theorem 36, proof]. Not in the sources beyond that; bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace

universe u

namespace Hironaka.Manifold.PieceEmbedding

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V) (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
  (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))

/-- **The local resolution map `Π : Ỹ → Sp(W)/𝓘|W` is proper** (Włodarczyk's `des` proper,
[Wlo09, §4, (3)⇒(4)]): `ι_Y ∘ Π = Sp(σ^r) ∘ ι_Ỹ`
(`localResolutionMap_comp_ι`) with `ι_Ỹ` a closed embedding
(`isClosedEmbedding_toFun_toAnalyticSpaceι`) and `σ^r` proper (`isProperMap_stageMap`), and `ι_Y`
continuous injective (`isProperMap_of_comp_of_inj`). -/
theorem isProperMap_toFun_localResolutionMap :
    IsProperMap ⇑(E.localResolutionMap bed W hW) := by
  have hι := isClosedEmbedding_toFun_toAnalyticSpaceι (E.restrictedIdeal W)
  have hι' := isClosedEmbedding_toFun_toAnalyticSpaceι
    ((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq
      (E.restrictedIdeal W) (Fin.last _))
  have hσ := (E.localResolutionSeq bed W hW).toSuccession.isProperMap_stageMap (Fin.last _)
  have hcomp : (fun z =>
      ((E.restrictedIdeal W).toAnalyticSpaceι z :
      (pieceAmbient.{u} 𝕜 E.G).restrict W)) ∘
        ⇑(E.localResolutionMap bed W hW) =
      ⇑((E.localResolutionSeq bed W hW).toSuccession.stageMap (Fin.last _)) ∘
        fun z => (((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq
            (E.restrictedIdeal W) (Fin.last _)).toAnalyticSpaceι z :
              (E.localResolutionSeq bed W hW).toSuccession.stage (Fin.last _)) :=
    congrArg AnalyticSpace.Hom.toFun (E.localResolutionMap_comp_ι bed W hW)
  have hprop : IsProperMap (X := E.localResolution bed W hW)
      (Y := (pieceAmbient.{u} 𝕜 E.G).restrict W)
      ((fun z =>
          (E.restrictedIdeal W).toAnalyticSpaceι z) ∘
        ⇑(E.localResolutionMap bed W hW)) :=
    (congrArg (@IsProperMap (E.localResolution bed W hW) ((pieceAmbient.{u} 𝕜 E.G).restrict W) _ _)
      hcomp).mpr (hσ.comp hι'.isProperMap)
  exact isProperMap_of_comp_of_inj
    (Hom.continuous_toFun (E.localResolutionMap bed W hW)) hι.continuous hprop hι.injective

/-- **The range of the restriction-of-a-quotient map `Sp(W)/𝓘|W → Sp(G)/𝓘` is the set of points
over `W`**: `range_toFun_homOfPullbackEq` at the open inclusion `W ↪ G`. -/
theorem range_toFun_restrictedIdealHom :
    range ⇑(E.restrictedIdealHom W) =
      {z | E.ideal.toAnalyticSpaceι z ∈ W} := by
  rw [restrictedIdealHom,
    range_toFun_homOfPullbackEq (AnalyticManifold.inclusion _ W)
      (Manifold.isLocalDiffeomorph_inclusion _ W) rfl]
  exact Set.ext fun z => ⟨fun ⟨w, hw⟩ =>
    show E.ideal.toAnalyticSpaceι z ∈ W from hw ▸ w.2,
    fun hz => ⟨⟨_, hz⟩, rfl⟩⟩

/-- **The open immersion of the piece over `W` into `X`**, on points (Włodarczyk's
`Ṽ_i → V_i ⊆ Y`, [Wlo09, §4, (3)⇒(4)]): the restriction-of-a-quotient map, the inverse of the
embedding and the inclusion of the piece — the second factor of
`toSpaceMap = Π ≫ (Sp(W)/𝓘|W → X)`. -/
def pieceOverIncl (w : (E.restrictedIdeal W).toAnalyticSpace) : X :=
  (E.embInv
    (E.restrictedIdealHom W w)).1

/-- `toSpaceMap` on points is the open immersion of the piece over `W` after the local resolution
map — the factorisation `toSpaceMap = pieceOverIncl ∘ Π`, `rfl`. -/
theorem toFun_toSpaceMap_eq (y : E.localResolution bed W hW) :
    KLocallyRingedSpace.Hom.toFun (E.toSpaceMap bed W hW) y =
      E.pieceOverIncl W
          (E.localResolutionMap bed W hW y) :=
  rfl

/-- The open immersion of the piece over `W` is an open embedding on points: the
three factors are open immersions (`isOpenImmersion_restrictedIdealHom`, `isOpenImmersion_inv_emb`,
the inclusion of the open piece). -/
theorem isOpenEmbedding_pieceOverIncl : IsOpenEmbedding (E.pieceOverIncl W) := by
  have : IsIso E.emb := E.emb_isIso
  have h₁ := E.isOpenImmersion_restrictedIdealHom W
  have h₂ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion E.embInv.1 :=
    E.isOpenImmersion_inv_emb
  exact (openOf X V).isOpen.isOpenEmbedding_subtypeVal.comp
    ((Hom.isOpenEmbedding_toFun E.embInv).comp
      (Hom.isOpenEmbedding_toFun (E.restrictedIdealHom W)))

/-- **The open immersion of the piece over `W` lands onto the base open `domOpens W`**: the points
of the piece whose ambient point lies in `W`
(`range_toFun_restrictedIdealHom`; `embInv` inverts the embedding). -/
theorem range_pieceOverIncl : range (E.pieceOverIncl W) = (E.domOpens W : Set X) := by
  have hE : IsIso E.emb := E.emb_isIso
  have h1 : ∀ z, E.emb
      (E.embInv z) = z := fun z =>
    congrArg
        (fun k => k z)
      (E.emb_comp_embInv)
  have h2 : ∀ y, E.embInv
      (E.emb y) = y := fun y =>
    congrArg
        (fun k => k y)
      (E.embInv_comp_emb)
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨E.embInv
      (E.restrictedIdealHom W w), ?_, rfl⟩
    have e : E.ideal.toAnalyticSpaceι
        (E.emb
            (E.embInv
          (E.restrictedIdealHom W w))) =
        (((E.restrictedIdeal W).toAnalyticSpaceι w).1 :
          pieceAmbient.{u} 𝕜 E.G) :=
      (congrArg E.ideal.toAnalyticSpaceι
          (h1 _)).trans
        (toFun_toAnalyticSpaceι_restrictedIdealHom E W w)
    change E.ideal.toAnalyticSpaceι
      (E.emb
          (E.embInv
        (E.restrictedIdealHom W w))) ∈
          (W : Set (pieceAmbient.{u} 𝕜 E.G))
    exact Set.mem_of_eq_of_mem e
      ((E.restrictedIdeal W).toAnalyticSpaceι w).2
  · rintro ⟨y, hy, rfl⟩
    have hy' : E.emb y ∈
        range ⇑(E.restrictedIdealHom W) :=
      (E.range_toFun_restrictedIdealHom W).symm ▸ hy
    obtain ⟨w, hw⟩ := hy'
    exact ⟨w, congrArg Subtype.val
      ((congrArg E.embInv hw).trans (h2 y))⟩

/-- **The piece map `Ỹ → domOpens W` onto its base open is proper** (Włodarczyk's `des_V` proper
on one piece, [Wlo09, §4, (3)⇒(4)]): `Π : Ỹ → Sp(W)/𝓘|W` is proper
(`isProperMap_toFun_localResolutionMap`) and `Sp(W)/𝓘|W → domOpens W` is a homeomorphism
(`isOpenEmbedding_pieceOverIncl`, `range_pieceOverIncl`). -/
theorem isProperMap_toSpaceMap_dom :
    IsProperMap fun y : E.localResolution bed W hW =>
      (⟨KLocallyRingedSpace.Hom.toFun (E.toSpaceMap bed W hW) y,
          E.range_toFun_toSpaceMap_subset bed W hW ⟨y, rfl⟩⟩ :
        E.domOpens W) := by
  let e : (E.restrictedIdeal W).toAnalyticSpace ≃ₜ E.domOpens W :=
    (E.isOpenEmbedding_pieceOverIncl W).toIsEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (E.range_pieceOverIncl W))
  have hfun : (fun y : E.localResolution bed W hW =>
      (⟨KLocallyRingedSpace.Hom.toFun (E.toSpaceMap bed W hW) y,
          E.range_toFun_toSpaceMap_subset bed W hW ⟨y, rfl⟩⟩ :
        E.domOpens W)) =
      e ∘ ⇑(E.localResolutionMap bed W hW) :=
    funext fun y => Subtype.ext rfl
  rw [hfun]
  exact e.isProperMap.comp (E.isProperMap_toFun_localResolutionMap bed W hW)

end Hironaka.Manifold.PieceEmbedding

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)

/-- **The local resolutions of the pieces of `D` glue** ([Wlo09, §4, (3)⇒(4)]; [Kol07, Theorem 36,
proof]) — `resolutionGluesOn_of_isEmbeddedDesing` (`GluingProperties.lean`) with the independence
of the local resolution as the hypothesis `hind`: the ambient opens from `exists_W`, the
transitions from `exists_transition`, the gluing datum from
`GlueOver.exists_glueOver_of_transitions` with the uniqueness `transition_unique` supplying the
cocycle, `t_id` and Hausdorffness. -/
theorem resolutionGluesOn_of_isEmbeddedDesing_of_independent (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) : D.ResolutionGluesOn bed := by
  choose W hWc hWinner using fun i => D.exists_W i
  choose t htiso htc using fun i j => D.exists_transition bed W hWc hbed hind i j
  exact ⟨{ W := W
           isCompact_closure_W := hWc
           closure_inner_subset_pieceDom := hWinner
           glue := (GlueOver.exists_glueOver_of_transitions
             (fun i => (D.embedding i).range_toFun_toSpaceMap_subset bed (W i) (hWc i)) t htiso htc
             (fun i j O hO s s' hs hs' hc hc' =>
               D.transition_unique bed W hWc hbed hind i j O hO s s' hs hs' hc hc')).some }⟩

/-- **The map `Π_U : resolutionOn D bed → X|U` is proper** for an open `U` (Włodarczyk's
`des_V : Ṽ → V` proper, [Wlo09, §4, (3)⇒(4)]). With a gluing datum, over each base open
`pieceDom i (W i)` the glued space is `Ỹ_i` and the descended map is the proper piece map `Π_i`
(`GlueOver.isProperMap_restrictPreimage_descMap_of_subset` on the cover `{pieceDom i (W i)}` of
`U ⊆ ⋃ inner i`); without one, the pair is `⟨X, 𝟙 X⟩` and `Π_U` is the identity of `X|U`. No
hypothesis on `bed` is needed, and `hU : IsOpen U` is necessary. -/
theorem isProperMap_resolutionOnMap (hU : IsOpen U) : IsProperMap (D.resolutionOnMap bed) := by
  have key : ∀ p : Σ R :
      AnalyticSpace.{u} 𝕜, (R ⟶ X),
      p = D.resolutionOnFullPair bed → IsProperMap (U.restrictPreimage
          (KLocallyRingedSpace.Hom.toFun p.2)) := by
    intro p hp
    by_cases h : D.ResolutionGluesOn bed
    · rw [D.resolutionOnFullPair_eq_of_glues bed h] at hp
      subst hp
      exact GlueOver.isProperMap_restrictPreimage_descMap_of_subset h.some.glue
        (fun i => (D.embedding i).isProperMap_toSpaceMap_dom bed (h.some.W i)
          (h.some.isCompact_closure_W i))
        U (D.subset_iUnion_inner.trans (iUnion_mono fun i =>
          subset_closure.trans (h.some.closure_inner_subset_pieceDom i)))
    · rw [D.resolutionOnFullPair_eq_of_not_glues bed h] at hp
      subst hp
      exact (Homeomorph.setCongr (Set.ext fun _ => Iff.rfl :
        KLocallyRingedSpace.Hom.toFun (𝟙 X) ⁻¹' U =
            U)).isProperMap
  exact isProperMap_toFun_restrictSet
    (D.resolutionOnFullMap bed) hU (key _ rfl)

end Hironaka.Manifold.LocalEmbeddingData

end
