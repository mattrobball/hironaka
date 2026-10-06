/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueProof
public import Hironaka.Resolution.Analytic.Kol07Thm45.Resolution
import Hironaka.AnalyticSpace.RegOpenImmersion
import Hironaka.AnalyticSpace.RegPoints
import Hironaka.Resolution.Analytic.Kol07Thm45.Glue.OverIsoReg
import Hironaka.Resolution.Analytic.Kol07Thm45.IsoOverLemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionIndependent
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueDatum
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueIndep
import Hironaka.Resolution.Analytic.Wlo09.IsoOverReg
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The resolution is an isomorphism over the simple points

Clause (2) of `exists_functorial_resolution` (`ResolutionAssembly.lean`): the map
`Π_X : R(X) → X` is an isomorphism over the simple locus `X.regularLocus` — clause (2) of Hironaka's
resolution problem [Hir64, Introduction], [Kol07, Theorem 45(2)], [Wlo09, Theorem 2.0.1(1)]. Read on
the pieces: over each piece, `localResolutionMap_isIsoOver_reg`
(`Hironaka/Resolution/Analytic/Wlo09/IsoOverReg.lean`; the local resolution `Ỹ → Sp(W)/𝓘|W` is an
isomorphism over the simple points, the centres being disjoint from them, [Wlo09, Theorem 2.0.2(2)])
after the open immersion `Sp(W)/𝓘|W → X` onto the base open `domOpens W`, which carries the simple
locus to the simple locus (`isIsoOver_toSpaceMap_reg`); on a glued space the descended map is an
isomorphism over `X.regularLocus ∩ ⋃ dom i` when every piece map is
(`isIsoOver_descMap_inter_iUnion`, `Hironaka/Resolution/Analytic/Kol07Thm45/Glue/OverIsoReg.lean`);
then over the exhaustion.

The independence of the local resolution enters as the hypothesis `hind` (discharged in
`GluingProperties.lean`). Not in the sources beyond the statements cited; bookkeeping.
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

/-- **The piece map `Ỹ → X` is an isomorphism over the simple points of its base open**
([Wlo09, Theorem 2.0.2(2)]; Kollár's `g⁻¹(Sing X̄) = Z_j ∩ Ex_tot`, [Kol07, Theorem 27, proof]):
`toSpaceMap = Π ≫ q` with `q`
the open immersion of `Sp(W)/𝓘|W` onto `domOpens W` (`pieceOverIncl` on points); `q` is an
isomorphism over `X.regularLocus ∩ domOpens W` (`isIsoOver_of_isOpenImmersion`), and
`q⁻¹(X.regularLocus ∩ domOpens W)` is the simple locus of `Sp(W)/𝓘|W`
(`mem_reg_iff_of_isOpenImmersion`), over which `Π` is an isomorphism
(`localResolutionMap_isIsoOver_reg`); `IsIsoOver.comp`. -/
theorem isIsoOver_toSpaceMap_reg (hbed : bed.IsEmbeddedDesing) :
    AnalyticSpace.Hom.IsIsoOver (E.toSpaceMap bed W hW) (X.regularLocus ∩ E.domOpens W) := by
  have hE : IsIso E.emb := E.emb_isIso
  have h₁ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (E.restrictedIdealHom W : (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
        E.ideal.toAnalyticSpace.toKLocallyRingedSpace).1 :=
    E.isOpenImmersion_restrictedIdealHom W
  have h₂ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (E.embInv : E.ideal.toAnalyticSpace.toKLocallyRingedSpace ⟶
        X.toKLocallyRingedSpace.restrictOpen (AnalyticSpace.openOf X V)).1 :=
    E.isOpenImmersion_inv_emb
  -- the open immersion of the piece over `W` into `X`, as a morphism (`pieceOverIncl` on points)
  set q : (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
      X.toKLocallyRingedSpace :=
    (E.restrictedIdealHom W : (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
        E.ideal.toAnalyticSpace.toKLocallyRingedSpace) ≫
      (E.embInv : E.ideal.toAnalyticSpace.toKLocallyRingedSpace ⟶
        X.toKLocallyRingedSpace.restrictOpen (AnalyticSpace.openOf X V)) ≫
      ofRestrict X.toKLocallyRingedSpace (AnalyticSpace.openOf X V) with hqdef
  have hoR : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict X.toKLocallyRingedSpace (AnalyticSpace.openOf X V)).1 :=
    inferInstance
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
  have hS : IsOpen (X.regularLocus ∩ (E.domOpens W : Set X)) :=
    (AnalyticSpace.isOpen_reg X).inter (E.domOpens W).isOpen
  have hsub : X.regularLocus ∩ (E.domOpens W : Set X) ⊆
      range (Hom.toFun q) :=
    fun _ hx => (Set.ext_iff.mp (E.range_pieceOverIncl W) _).mpr hx.2
  have hpre : Hom.toFun q ⁻¹' (X.regularLocus ∩ (E.domOpens W : Set X)) =
      (E.restrictedIdeal W).toAnalyticSpace.regularLocus := by
    ext w
    constructor
    · intro hw
      exact (AnalyticSpace.mem_reg_iff_of_isOpenImmersion q hq w).mpr hw.1
    · intro hw
      exact ⟨(AnalyticSpace.mem_reg_iff_of_isOpenImmersion q hq w).mp hw,
        (Set.ext_iff.mp (E.range_pieceOverIncl W) _).mp ⟨w, rfl⟩⟩
  rw [heq]
  refine AnalyticSpace.Hom.IsIsoOver.comp (f := E.localResolutionMap bed W hW)
    (g := q) ?_
    (AnalyticSpace.Hom.isIsoOver_of_isOpenImmersion (hg := hq) q hS hsub)
  exact (congrArg ((E.localResolutionMap bed W hW).IsIsoOver)
    hpre).mpr (E.localResolutionMap_isIsoOver_reg bed W hW hbed)

end Hironaka.Manifold.PieceEmbedding

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)

/-- **The descended map of the glued space is an isomorphism over the simple points of the OPEN
`U`** ([Wlo09, §4, (3)⇒(4)]) — the pieces' base opens
cover `U` (`closure_inner_subset_pieceDom`, `subset_iUnion_inner`), each piece map is an isomorphism
over `X.regularLocus ∩ pieceDom i` (`isIsoOver_toSpaceMap_reg`), so the descended map is one over
`X.regularLocus ∩ ⋃ pieceDom i` (`isIsoOver_descMap_inter_iUnion`) and hence over the open subset
`X.regularLocus ∩ U` (`IsIsoOver.mono`); the map `resolutionOnFullMap` unfolds to the chosen datum's
descended map. -/
theorem isIsoOver_resolutionOnFullMap_reg (hU : IsOpen U) (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) :
    (D.resolutionOnFullMap bed).IsIsoOver (X.regularLocus ∩ U) := by
  have h := D.resolutionGluesOn_of_isEmbeddedDesing_of_independent bed hbed hind
  suffices key : ∀ p : Σ R :
      AnalyticSpace.{u} 𝕜, (R ⟶ X),
      p = D.resolutionOnFullPair bed →
        p.2.IsIsoOver (X.regularLocus ∩ U) from
    key _ rfl
  intro p hp
  rw [D.resolutionOnFullPair_eq_of_glues bed h] at hp
  subst hp
  have hReg : IsOpen X.regularLocus :=
    AnalyticSpace.isOpen_reg X
  have hopen : IsOpen (⋃ i, (D.pieceDom i (h.some.W i) : Set X)) :=
    isOpen_iUnion fun i => (D.pieceDom i (h.some.W i)).isOpen
  have hUsub : U ⊆ ⋃ i, (D.pieceDom i (h.some.W i) : Set X) :=
    D.subset_iUnion_inner.trans (iUnion_mono fun i =>
      subset_closure.trans (h.some.closure_inner_subset_pieceDom i))
  refine AnalyticSpace.Hom.IsIsoOver.mono (hReg.inter hopen) (hReg.inter hU)
    (inter_subset_inter_right _ hUsub) ?_
  exact h.some.glue.isIsoOver_descMap_inter_iUnion _ hReg fun i =>
    (D.embedding i).isIsoOver_toSpaceMap_reg bed (h.some.W i) (h.some.isCompact_closure_W i) hbed

/-- The same on the space `resolutionOn` over the OPEN `U`: `Π_U` read into `X` is the open
immersion `Ũ → Ṿ` followed by the descended map (`restrictTo_comp_ofRestrict`); the first is an
isomorphism over `Π⁻¹(X.regularLocus ∩ U) ⊆ Π⁻¹U` (`isIsoOver_of_isOpenImmersion`), the second over
`X.regularLocus ∩ U` (`isIsoOver_resolutionOnFullMap_reg`); `IsIsoOver.comp`. -/
theorem isIsoOver_resolutionOnToSpace_reg (hU : IsOpen U) (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) :
    (D.resolutionOnToSpace bed).IsIsoOver (X.regularLocus ∩ U) := by
  have hReg : IsOpen X.regularLocus :=
    AnalyticSpace.isOpen_reg X
  have hpre : IsOpen (Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U) :=
    hU.preimage (Hom.continuous_toFun (D.resolutionOnFullMap bed))
  have heq : D.resolutionOnToSpace bed =
      ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
          (AnalyticSpace.openOf (D.resolutionOnFull bed)
            (Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U)) ≫
        (D.resolutionOnFullMap bed : (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
          X.toKLocallyRingedSpace) :=
    Hom.restrictTo_comp_ofRestrict (D.resolutionOnFullMap bed) _ _
      (AnalyticSpace.Hom.mapsTo_openOf (D.resolutionOnFullMap bed) U)
  rw [heq]
  refine AnalyticSpace.Hom.IsIsoOver.comp (A := D.resolutionOn bed)
    (B := D.resolutionOnFull bed) (X := X)
    (f := ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
      (AnalyticSpace.openOf (D.resolutionOnFull bed)
        (Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U)))
    (g := D.resolutionOnFullMap bed) ?_ (D.isIsoOver_resolutionOnFullMap_reg bed hU hbed hind)
  have hoi : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
        (AnalyticSpace.openOf (D.resolutionOnFull bed)
          (Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))).1 := inferInstance
  refine AnalyticSpace.Hom.isIsoOver_of_isOpenImmersion (hg := hoi) _
    ((hReg.inter hU).preimage (Hom.continuous_toFun (D.resolutionOnFullMap bed))) fun r hr => ?_
  exact (Set.ext_iff.mp (range_toFun_ofRestrict _ _) r).mpr
    ((SetLike.ext_iff.mp (AnalyticSpace.openOf_of_isOpen _ hpre) r).mpr hr.2)

end Hironaka.Manifold.LocalEmbeddingData

namespace Hironaka.Manifold.BEDanFamStar

variable {𝕜 : Type} [RCLike 𝕜]

/-- **`Π_X` is an isomorphism over the simple locus `X.regularLocus`** ([Hir64, Introduction],
clause (2) of the resolution problem; [Kol07, Theorem 45(2)]; [Wlo09, Theorem 2.0.1(1)]), for a
reduced `X`, with the independence of the local resolution as `hind` — over each member `U_n` of the
exhaustion the map `Π_{U_n}` is an isomorphism over `X.regularLocus ∩ U_n`
(`isIsoOver_resolutionOnToSpace_reg`), the members cover `X`, and the descended map of the
exhaustion gluing is an isomorphism over `X.regularLocus ∩ ⋃ U_n = X.regularLocus`
(`isIsoOver_descMap_inter_iUnion`); the map `bed.resolutionMap X` unfolds to the chosen datum's
descended map (`resolutionPair_eq_of_glues`). -/
theorem resolutionMap_isIsoOver_reg_of_independent (X : AnalyticSpace.{u} 𝕜)
    (hX : X.IsReduced) (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) :
    (bed.resolutionMap X).IsIsoOver X.regularLocus := by
  have h := resolutionGlues_of_isEmbeddedDesing_of_independent X hX bed hbed hind
  suffices key : ∀ p : Σ R :
      AnalyticSpace.{u} 𝕜, (R ⟶ X),
      p = bed.resolutionPair X →
        p.2.IsIsoOver X.regularLocus from
    key _ rfl
  intro p hp
  rw [bed.resolutionPair_eq_of_glues X hX h] at hp
  subst hp
  have hReg : IsOpen X.regularLocus :=
    AnalyticSpace.isOpen_reg X
  have hcov : ⋃ n : ULift.{u} ℕ, ((h.some.U n.down : Opens X) : Set X) = univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := mem_iUnion.mp (h.some.iUnion_U ▸ mem_univ x)
    exact mem_iUnion.mpr ⟨⟨n⟩, hn⟩
  have hopen : IsOpen (⋃ n : ULift.{u} ℕ, ((h.some.U n.down : Opens X) : Set X)) :=
    isOpen_iUnion fun n => (h.some.U n.down).isOpen
  refine AnalyticSpace.Hom.IsIsoOver.mono (hReg.inter hopen) hReg
    (subset_inter Subset.rfl (by rw [hcov]; exact subset_univ _)) ?_
  exact h.some.glue.isIsoOver_descMap_inter_iUnion _ hReg fun n =>
    (h.some.D n.down).isIsoOver_resolutionOnToSpace_reg bed (h.some.U n.down).isOpen hbed hind

end Hironaka.Manifold.BEDanFamStar

end
