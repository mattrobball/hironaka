/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.SncDivisorSetLocal
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueDatum
public import Hironaka.Resolution.Analytic.Kol07Thm45.Resolution
import Hironaka.AnalyticSpace.Glue.OverSnc
import Hironaka.AnalyticSpace.IsoOverCover
import Hironaka.AnalyticSpace.RegOpenImmersion
import Hironaka.AnalyticSpace.RegPoints
import Hironaka.AnalyticSpace.SncDivisorSetCover
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionIndependent
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueIndep
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionClauses
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionIsoReg
import Hironaka.Resolution.Analytic.Wlo09.PreimageSing
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The exceptional set is a simple normal crossings divisor set; the range of the resolution

Clause (3) of `exists_functorial_resolution` (`ResolutionAssembly.lean`) in its set form
([Wlo09, Theorem 2.0.1(2)]; [Kol07, Theorem 45(3)]): `Π_X⁻¹(X.singularLocus)` is a simple normal
crossings divisor set of `R(X)`. Over each piece,
`localResolutionMap_preimage_sing_eq_inter_exceptional`
(`Hironaka/Resolution/Analytic/Wlo09/PreimageSing.lean`) gives it for
`Π⁻¹((Sp(W)/𝓘|W).singularLocus)`, and the open immersion `q` of `Sp(W)/𝓘|W` onto its base open
carries the singular locus to the singular locus (`isSncDivisorSet_toSpaceMap_preimage_sing`); the
predicate is local on glued spaces (`isSncDivisorSet_gluedOver_preimage`,
`Hironaka/AnalyticSpace/Glue/OverSnc.lean`) and restricts to the open subspaces `Ũ_n = Ṿ_n|Π_n⁻¹U_n`
(`IsSncDivisorSet.restrictOpen`); then over the exhaustion.

The range conjunct of clause (4) of `exists_functorial_resolution`:
`range Π_X = closure X.regularLocus` — for a real-analytic space the simple points need not be
dense, so `Π_X` need not be surjective [Hir64, Introduction]. The range is closed (`Π_X` proper) and
contains `X.regularLocus` (the restricted map onto `X.regularLocus` is onto, by clause (2)), and the
complement of the divisor set `Π_X⁻¹(X.singularLocus)` is dense in `R(X)`
(`IsSncDivisorSet.dense_compl`, `Hironaka/AnalyticSpace/SncDivisorSetLocal.lean`) and maps into
`X.regularLocus`.

The independence of the local resolution enters as the hypothesis `hind`. Not in the sources
beyond the statements cited; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace.KLocallyRingedSpace

universe u

namespace Hironaka.Manifold.PieceEmbedding

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V) (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
  (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))

/-- **The open immersion `q : Sp(W)/𝓘|W → X` of the piece over `W`** (`pieceOverIncl` on points;
Włodarczyk's `Ṽ_i → V_i ⊆ Y`, [Wlo09, §4, (3)⇒(4)]): the restriction-of-a-quotient map, the
inverse of the embedding and the inclusion of the piece, with `toSpaceMap = Π ≫ q`. -/
theorem exists_openImmersion_toSpaceMap_eq :
    ∃ q : (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace,
      AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion q.1 ∧
      Hom.toFun q = E.pieceOverIncl W ∧
      E.toSpaceMap bed W hW =
        (E.localResolutionMap bed W hW : (E.localResolution bed W hW).toKLocallyRingedSpace ⟶
          (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace) ≫ q := by
  have hE : IsIso E.emb := E.emb_isIso
  have h₁ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (E.restrictedIdealHom W : (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
        E.ideal.toAnalyticSpace.toKLocallyRingedSpace).1 :=
    E.isOpenImmersion_restrictedIdealHom W
  have h₂ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (E.embInv : E.ideal.toAnalyticSpace.toKLocallyRingedSpace ⟶
        X.toKLocallyRingedSpace.restrictOpen (AnalyticSpace.openOf X V)).1 :=
    E.isOpenImmersion_inv_emb
  have hoR : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict X.toKLocallyRingedSpace (AnalyticSpace.openOf X V)).1 :=
    inferInstance
  set q : (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
      X.toKLocallyRingedSpace :=
    (E.restrictedIdealHom W : (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
        E.ideal.toAnalyticSpace.toKLocallyRingedSpace) ≫
      (E.embInv : E.ideal.toAnalyticSpace.toKLocallyRingedSpace ⟶
        X.toKLocallyRingedSpace.restrictOpen (AnalyticSpace.openOf X V)) ≫
      ofRestrict X.toKLocallyRingedSpace (AnalyticSpace.openOf X V) with hqdef
  have hq : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion q.1 := by
    rw [hqdef]
    exact @AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (E.restrictedIdealHom W).1 h₁
      (E.embInv.1 ≫ (ofRestrict X.toKLocallyRingedSpace
        (AnalyticSpace.openOf X V)).1)
      (@AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _ E.embInv.1 h₂
        (ofRestrict X.toKLocallyRingedSpace (AnalyticSpace.openOf X V)).1 hoR)
  have hqfun : Hom.toFun q = E.pieceOverIncl W := rfl
  have heq : E.toSpaceMap bed W hW =
      (E.localResolutionMap bed W hW : (E.localResolution bed W hW).toKLocallyRingedSpace ⟶
        (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace) ≫ q := by
    unfold toSpaceMap
    rw [E.localResolutionToPiece_eq bed W hW]
    exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)
  exact ⟨q, hq, hqfun, heq⟩

/-- **The inverse image of the singular locus of `X` under the piece map `Ỹ → X` is a simple
normal crossings divisor set** ([Wlo09, Theorem 2.0.1(2)]): it is
`Π⁻¹((Sp(W)/𝓘|W).singularLocus)` (`localResolutionMap_preimage_sing_eq_inter_exceptional`), the open
immersion `q` carrying the singular locus to the singular locus
(`mem_reg_iff_of_isOpenImmersion`). -/
theorem isSncDivisorSet_toSpaceMap_preimage_sing (hbed : bed.IsEmbeddedDesing) :
    AnalyticSpace.IsSncDivisorSet (E.localResolution bed W hW)
      (Hom.toFun (E.toSpaceMap bed W hW) ⁻¹' X.singularLocus) := by
  obtain ⟨q, hq, -, heq⟩ := E.exists_openImmersion_toSpaceMap_eq bed W hW
  have hsing : Hom.toFun q ⁻¹' X.singularLocus =
      (E.restrictedIdeal W).toAnalyticSpace.singularLocus := by
    ext w
    exact not_congr (AnalyticSpace.mem_reg_iff_of_isOpenImmersion q hq w).symm
  have hset : Hom.toFun (E.toSpaceMap bed W hW) ⁻¹' X.singularLocus =
      ⇑(E.localResolutionMap bed W hW) ⁻¹'
        (E.restrictedIdeal W).toAnalyticSpace.singularLocus :=
    (congrArg (fun k : (E.localResolution bed W hW).toKLocallyRingedSpace ⟶
        X.toKLocallyRingedSpace =>
            Hom.toFun k ⁻¹' X.singularLocus) heq).trans
      (congrArg
          (fun T =>
              ⇑(E.localResolutionMap bed W hW) ⁻¹' T)
        hsing)
  exact (congrArg (AnalyticSpace.IsSncDivisorSet (E.localResolution bed W hW))
    hset).mpr (E.localResolutionMap_preimage_sing_eq_inter_exceptional bed W hW hbed).2

end Hironaka.Manifold.PieceEmbedding

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)

/-- The same on the glued space of the pieces: the pieces' inverse images of the singular locus are
simple normal crossings divisor sets (`isSncDivisorSet_toSpaceMap_preimage_sing`) and the predicate
is local on the glued space (`isSncDivisorSet_gluedOver_preimage`); the map `resolutionOnFullMap`
unfolds to the chosen datum's descended map. -/
theorem isSncDivisorSet_resolutionOnFullMap_preimage_sing (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) :
    AnalyticSpace.IsSncDivisorSet (D.resolutionOnFull bed)
      (Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' X.singularLocus) := by
  have h := D.resolutionGluesOn_of_isEmbeddedDesing_of_independent bed hbed hind
  suffices key : ∀ p : Σ R :
      AnalyticSpace.{u} 𝕜, (R ⟶ X),
      p = D.resolutionOnFullPair bed →
        AnalyticSpace.IsSncDivisorSet p.1
          (Hom.toFun p.2 ⁻¹' X.singularLocus) from key _ rfl
  intro p hp
  rw [D.resolutionOnFullPair_eq_of_glues bed h] at hp
  subst hp
  exact h.some.glue.isSncDivisorSet_gluedOver_preimage _ fun i =>
    (D.embedding i).isSncDivisorSet_toSpaceMap_preimage_sing bed (h.some.W i)
      (h.some.isCompact_closure_W i) hbed

/-- The same on the space `resolutionOn` over `U`: `Ũ = Ṿ|Π⁻¹U` is an open subspace of the glued
space (`IsSncDivisorSet.restrictOpen`) and `Π_U` read into `X` is the open immersion followed by the
descended map (`restrictTo_comp_ofRestrict`). No `hU`: the restriction lemma takes any `openOf`. -/
theorem isSncDivisorSet_resolutionOnToSpace_preimage_sing (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) :
    AnalyticSpace.IsSncDivisorSet (D.resolutionOn bed)
      (Hom.toFun (D.resolutionOnToSpace bed) ⁻¹' X.singularLocus) := by
  have h1 := D.isSncDivisorSet_resolutionOnFullMap_preimage_sing bed hbed hind
  have h2 := AnalyticSpace.IsSncDivisorSet.restrictOpen h1
    (AnalyticSpace.openOf (D.resolutionOnFull bed)
      (Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))
  have heq : D.resolutionOnToSpace bed =
      ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
          (AnalyticSpace.openOf (D.resolutionOnFull bed)
            (Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U)) ≫
        (D.resolutionOnFullMap bed : (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
          X.toKLocallyRingedSpace) :=
    Hom.restrictTo_comp_ofRestrict (D.resolutionOnFullMap bed) _ _
      (AnalyticSpace.Hom.mapsTo_openOf (D.resolutionOnFullMap bed) U)
  exact (congrArg (fun k : (D.resolutionOn bed).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace =>
    AnalyticSpace.IsSncDivisorSet (D.resolutionOn bed)
      (Hom.toFun k ⁻¹' X.singularLocus)) heq).mpr h2

end Hironaka.Manifold.LocalEmbeddingData

namespace Hironaka.Manifold.BEDanFamStar

variable {𝕜 : Type} [RCLike 𝕜]

/-- **`Π_X⁻¹(X.singularLocus)` is a simple normal crossings divisor set of `R(X)`** ([Wlo09, Theorem
2.0.1(2)]; [Kol07, Theorem 45(3)]), for a reduced `X`, with the independence of the local resolution
as `hind` — over each member `U_n` of the exhaustion the inverse image of the singular locus under
`Π_{U_n}` is a simple normal crossings divisor set
(`isSncDivisorSet_resolutionOnToSpace_preimage_sing`) and the predicate is local on the glued space
(`isSncDivisorSet_gluedOver_preimage`, `resolutionPair_eq_of_glues`). -/
theorem resolution_isSncDivisorSet_preimage_sing_of_independent
    (X : AnalyticSpace.{u} 𝕜)
    (hX : X.IsReduced) (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) :
    AnalyticSpace.IsSncDivisorSet (bed.resolution X)
      ((bed.resolutionMap X) ⁻¹' X.singularLocus) := by
  have h := resolutionGlues_of_isEmbeddedDesing_of_independent X hX bed hbed hind
  suffices key : ∀ p : Σ R :
      AnalyticSpace.{u} 𝕜, (R ⟶ X),
      p = bed.resolutionPair X →
        AnalyticSpace.IsSncDivisorSet p.1
          (⇑p.2 ⁻¹'
              X.singularLocus) from
    key _ rfl
  intro p hp
  rw [bed.resolutionPair_eq_of_glues X hX h] at hp
  subst hp
  exact h.some.glue.isSncDivisorSet_gluedOver_preimage _ fun n =>
    (h.some.D n.down).isSncDivisorSet_resolutionOnToSpace_preimage_sing bed hbed hind

/-- **`range Π_X = closure X.regularLocus`** (for a real-analytic space the simple points need not
be dense, [Hir64, Introduction]), for a reduced `X`, with the independence of the local resolution
as `hind` — `⊇`: the range is closed (`Π_X` proper, `isProperMap_resolutionMap`) and contains
`X.regularLocus` (the restricted map `Π_X⁻¹(X.regularLocus) → X.regularLocus` is an isomorphism,
hence onto, `resolutionMap_isIsoOver_reg_of_independent`); `⊆`: the complement of the divisor set
`Π_X⁻¹(X.singularLocus)` is dense in `R(X)` (`IsSncDivisorSet.dense_compl`) and `Π_X` maps it into
`X.regularLocus`.
-/
theorem range_resolutionMap_eq_closure_reg_of_independent
    (X : AnalyticSpace.{u} 𝕜)
    (hX : X.IsReduced) (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) :
    Set.range (bed.resolutionMap X) = closure X.regularLocus := by
  have hprop := isProperMap_resolutionMap X bed
  have hiso : IsIso (AnalyticSpace.Hom.restrictSet (bed.resolutionMap X)
      X.regularLocus) :=
    resolutionMap_isIsoOver_reg_of_independent X hX bed hbed hind
  have hsnc := resolution_isSncDivisorSet_preimage_sing_of_independent X hX bed hbed hind
  have hReg : IsOpen X.regularLocus :=
    AnalyticSpace.isOpen_reg X
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨r, rfl⟩
    have hd :
        Dense (Hom.toFun (bed.resolutionMap X) ⁻¹' X.singularLocus)ᶜ :=
      AnalyticSpace.IsSncDivisorSet.dense_compl hsnc
    have hr : Hom.toFun (bed.resolutionMap X) r ∈ closure (Hom.toFun (bed.resolutionMap X) ''
        (Hom.toFun (bed.resolutionMap X) ⁻¹' X.singularLocus)ᶜ) :=
      image_closure_subset_closure_image (Hom.continuous_toFun (bed.resolutionMap X))
        ⟨r, hd r, rfl⟩
    refine closure_mono ?_ hr
    rintro _ ⟨s, hs, rfl⟩
    by_contra hn
    exact hs hn
  · refine closure_minimal ?_ hprop.isClosedMap.isClosed_range
    intro x hx
    obtain ⟨r, -, hr⟩ :=
      AnalyticSpace.surjOn_of_isIso_restrictSet (bed.resolutionMap X) hReg hx
    exact ⟨r, hr⟩

end Hironaka.Manifold.BEDanFamStar

end
