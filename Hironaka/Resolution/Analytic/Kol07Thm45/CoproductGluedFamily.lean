/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.OverFamily
public import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientLift
public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductExceptionalFamily
import Hironaka.AnalyticSpace.IsoOverOpen
import Hironaka.AnalyticSpace.RegOpenImmersion
import Hironaka.AnalyticSpace.SncBoundaryChart
import Hironaka.AnalyticSpace.SncFamilyTransport
import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductExceptionalSnc
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionSnc
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The glued exceptional family of a local embedding datum

Kollár descends the centres of the run on the disjoint union of a cover through their agreement
on the overlaps, (37.2) in [Kol07, Proposition 37, proof]: over a local embedding datum `D` the
functor runs ONCE on the coproduct triple (`CoproductExceptionalFamily.lean`); the coproduct's
exceptional members (`sigmaMembers`, indexed by the STAGE SET of the single run) trace on every
piece's local resolution along the open immersion `resIn i` (`pieceTrace`), the trace of label `σ`
being the piece's exceptional member of that label or the unit ideal (`RunFamilyRestrict.lean`
at the summand inclusion `sigmaMk i`). Kollár's (37.2) says the transitions of the gluing
datum carry the trace of label `σ` on one piece to the trace of the SAME label on the other — the
fixed-run device at the padded coproduct (`ExceptionalFamilyGlue.lean`, `FixedRunDevice.lean`,
`CoproductMixedTransition.lean`) with the label reconciliation of the common datum; it is taken
here as the HYPOTHESIS `hcomp`/`hc`, discharged in `CoproductGluedFamilyCompat.lean`. Under it the
traces are a LABELLED compatible family with the identity labelling on the coproduct's stage set
(`labelledCompat_pieceTrace_of_compat`), and the closed-subspace descent of
`Hironaka/AnalyticSpace/Glue/OverFamily.lean` glues them to **the datum's exceptional family on the
glued space** `gluedMembersOn`, one member per stage, with the restriction identity along
`ιGlued i`, simple normal crossings (`isSncFamily_gluedMembersOn`: from the pieces' — the
coproduct's family of `CoproductExceptionalSnc.lean` pulled back along the open immersion
`resIn i`, the general `IsSncFamily.comap_openImmersion` proved here from
`IsSncFamily.comap_ofRestrict`'s stalk argument), local finiteness (the coproduct run is finite)
and the support identity `⋃ σ, support = Π⁻¹(X.singularLocus)` (`iUnion_support_gluedMembersOn`: the
support identity on every piece, read through the open immersions `resIn i` and
`q : Sp(Y_i|W_i) → X` — `mem_reg_iff_of_isOpenImmersion` — and the descended map, the pieces
covering the glued space). Through the unfolding lemma `resolutionOnFullPair_eq_of_glues` the
family lives on `resolutionOnFull D bed` and, restricted over `U`, on `resolutionOn D bed` with the
map `resolutionOnToSpace` (`exists_gluedMembers_resolutionOn`, an existence statement keeping the
coproduct's stage set as its index — what the exhaustion-level assembly uses level by level).

Not in the sources beyond Kollár's descent; bookkeeping.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Hironaka.Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace.ClosedSubspace

variable {K : Type} [RCLike K] {X Y : AnalyticSpace.{u} K}

/-- The inverse image of a simple normal crossings family along an OPEN IMMERSION of analytic
spaces has simple normal crossings ([Kol07, Definition 24] is pointwise) — the stalk maps are
isomorphisms (`IsSncFamily.comap_ofRestrict`'s argument for an arbitrary open immersion). -/
theorem IsSncFamily.comap_openImmersion {ι : Type u} {H : ι → ClosedSubspace X}
    (h : IsSncFamily H) (f : Y.toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace)
    (hf : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion f.1) :
    IsSncFamily (X := Y) fun j => QuotientSpace.comap f.1 (H j) := by
  rw [isSncFamily_iff_isSncAtIdeals] at h ⊢
  refine ⟨?_, fun y => ?_⟩
  · have hsupp : (fun j => Manifold.IdealSheaf.support (QuotientSpace.comap f.1 (H j))) =
        fun j => f.1.base ⁻¹' (H j).support :=
      funext fun j => QuotientSpace.cosupport_comap _ (H j)
    rw [hsupp]
    exact h.1.preimage_continuous f.1.base.hom.continuous
  · have instS : IsLocalRing (Y.presheaf.stalk y) := Y.toLocallyRingedSpace.isLocalRing y
    have : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion f.1 := hf
    have hiso : CategoryTheory.IsIso (f.1.stalkMap y) := inferInstance
    have hb := CategoryTheory.ConcreteCategory.bijective_of_isIso (f.1.stalkMap y)
    have hpt := @IsSncAtIdeals.map_ringHom_of_bijective _ _ _ _ _ _ instS _ _ hb
      (h.2 (f.1.base y))
    exact Eq.mp (congrArg (@IsSncAtIdeals _ _ instS _) (funext fun j =>
      (QuotientSpace.stalkIdeal_comap f.1 (H j) y).symm)) hpt

end AnalyticSpace.ClosedSubspace

namespace Hironaka.Manifold.LocalEmbeddingData

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜) (Γ : D.ResolutionGluing bed)
  (hbed : bed.IsEmbeddedDesing)

/-- **The coproduct member of label `σ` traced on piece `i`** along the open immersion `resIn i` —
the piece's exceptional member of that label, or the unit ideal when the stage is empty on the
piece (`RunFamilyRestrict.lean` at the summand inclusion `sigmaMk i`). -/
abbrev pieceTrace : ∀ i : D.ι, D.sigmaIndex bed Γ.W Γ.isCompact_closure_W →
    AnalyticSpace.ClosedSubspace
        ((D.embedding i).localResolution bed (Γ.W i) (Γ.isCompact_closure_W
      i)) :=
  fun i σ => AnalyticSpace.QuotientSpace.comap
    (D.resIn bed Γ.W Γ.isCompact_closure_W hbed i).1 (D.sigmaMembers bed Γ.W
      Γ.isCompact_closure_W hbed σ)

/-- The traces on a piece form a simple normal crossings family — `isSncFamily_sigmaMembers` along
the open immersion `resIn i`. -/
theorem isSncFamily_pieceTrace (i : D.ι) :
    AnalyticSpace.ClosedSubspace.IsSncFamily (pieceTrace D bed Γ hbed i) :=
  (D.isSncFamily_sigmaMembers bed Γ.W Γ.isCompact_closure_W hbed).comap_openImmersion _
    (D.isOpenImmersion_resIn bed Γ.W Γ.isCompact_closure_W hbed i)

/-- Compatibility of the traces label by label (Kollár's (37.2)) IS the labelled compatibility
`LabelledCompat` with the identity labelling on the coproduct's stage set (`memberOfLabel_lab`). -/
theorem labelledCompat_pieceTrace_of_compat
    (hcomp : ∀ σ, Γ.glue.CompatClosedSubspaces (fun i => pieceTrace D bed Γ hbed i σ)) :
    Γ.glue.LabelledCompat (pieceTrace D bed Γ hbed) (fun _ σ => σ) := by
  intro l
  have e : (fun i => AnalyticSpace.GlueOver.memberOfLabel (pieceTrace D bed Γ hbed)
      (fun _ σ => σ) i l) = fun i => pieceTrace D bed Γ hbed i l :=
    funext fun i => AnalyticSpace.GlueOver.memberOfLabel_lab (fun _ => Function.injective_id)
      i l
  rw [e]
  exact hcomp l

/-- **The glued exceptional family of the datum** on the glued space, indexed by the coproduct's
stage set — `glueFamily` (`Hironaka/AnalyticSpace/Glue/OverFamily.lean`) with the identity
labelling, under the compatibility `hc` ((37.2) in [Kol07, Proposition 37, proof]). -/
def gluedMembersOn (hc : Γ.glue.LabelledCompat (pieceTrace D bed Γ hbed) (fun _ σ => σ)) :
    D.sigmaIndex bed Γ.W Γ.isCompact_closure_W →
        AnalyticSpace.ClosedSubspace Γ.glue.gluedOver :=
  Γ.glue.glueFamily (pieceTrace D bed Γ hbed) (fun _ σ => σ) hc

/-- The glued member of label `σ` pulls back along `ιGlued i` to the trace of label `σ` on piece `i`
(`comap_ιGlued_glueFamily_lab`). -/
theorem comap_ιGlued_gluedMembersOn
    (hc : Γ.glue.LabelledCompat (pieceTrace D bed Γ hbed) (fun _ σ => σ)) (i : D.ι)
    (σ : D.sigmaIndex bed Γ.W Γ.isCompact_closure_W) :
    AnalyticSpace.QuotientSpace.comap (Γ.glue.ιGlued i).1 (gluedMembersOn D bed Γ hbed hc σ) =
      pieceTrace D bed Γ hbed i σ :=
  Γ.glue.comap_ιGlued_glueFamily_lab (fun _ => Function.injective_id) hc i σ

/-- The glued family is a simple normal crossings family ([Kol07, Theorem 45(3)];
`isSncFamily_glueFamily` from the pieces' `isSncFamily_pieceTrace`). -/
theorem isSncFamily_gluedMembersOn
    (hc : Γ.glue.LabelledCompat (pieceTrace D bed Γ hbed) (fun _ σ => σ)) :
    AnalyticSpace.ClosedSubspace.IsSncFamily (gluedMembersOn D bed Γ hbed hc) :=
  Γ.glue.isSncFamily_glueFamily (fun _ => Function.injective_id) hc
    (isSncFamily_pieceTrace D bed Γ hbed)

/-- The glued family is locally finite (`locallyFinite_glueFamily`; the coproduct run is
finite). -/
theorem locallyFinite_gluedMembersOn
    (hc : Γ.glue.LabelledCompat (pieceTrace D bed Γ hbed) (fun _ σ => σ)) :
    LocallyFinite fun σ =>
      IdealSheaf.support (gluedMembersOn D bed Γ hbed hc σ) :=
  Γ.glue.locallyFinite_glueFamily (fun _ => Function.injective_id) hc
    fun i => (isSncFamily_pieceTrace D bed Γ hbed i).1

/-- The support of a trace is the preimage of the coproduct member's support along `resIn i`
(`support_comap`). -/
theorem support_pieceTrace (i : D.ι) (σ : D.sigmaIndex bed Γ.W Γ.isCompact_closure_W) :
    IdealSheaf.support (pieceTrace D bed Γ hbed i σ) =
      AnalyticSpace.KLocallyRingedSpace.Hom.toFun (D.resIn bed Γ.W Γ.isCompact_closure_W hbed i)
        ⁻¹' IdealSheaf.support
          (D.sigmaMembers bed Γ.W Γ.isCompact_closure_W hbed σ) :=
  AnalyticSpace.ClosedSubspace.support_comap_eq_preimage _ _

/-- **The union of the traces' supports on piece `i` is the preimage of `X.singularLocus`** under
the piece's map to `X` ([Kol07, Theorem 45(3)]) — `iUnion_support_sigmaMembers` at the coproduct,
read through the open immersions `resIn i` (`localResolutionHomOn_comp_map`,
`isOpenImmersion_homOfPullbackEq_of_injective`) and `q` (`exists_openImmersion_toSpaceMap_eq`) with
`mem_reg_iff_of_isOpenImmersion` at every point. -/
theorem iUnion_support_pieceTrace (i : D.ι) :
    (⋃ σ, IdealSheaf.support (pieceTrace D bed Γ hbed i σ)) =
      AnalyticSpace.KLocallyRingedSpace.Hom.toFun
        (D.pieceToSpace bed i (Γ.W i) (Γ.isCompact_closure_W i)) ⁻¹'
        X.singularLocus := by
  set g := sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i with hg
  have hgo : IsAnalyticOpenEmbedding g := isAnalyticOpenEmbedding_sigmaMk _ i
  have e1 : (⋃ σ, IdealSheaf.support (pieceTrace D bed Γ hbed i σ)) =
      AnalyticSpace.KLocallyRingedSpace.Hom.toFun (D.resIn bed Γ.W Γ.isCompact_closure_W hbed i)
        ⁻¹' ⋃ σ, IdealSheaf.support
          (D.sigmaMembers bed Γ.W Γ.isCompact_closure_W hbed σ) := by
    rw [Set.preimage_iUnion]
    exact Set.iUnion_congr fun σ => support_pieceTrace D bed Γ hbed i σ
  rw [e1]
  refine (congrArg (fun S => AnalyticSpace.KLocallyRingedSpace.Hom.toFun
    (D.resIn bed Γ.W Γ.isCompact_closure_W hbed i) ⁻¹' S)
    (D.iUnion_support_sigmaMembers bed Γ.W Γ.isCompact_closure_W hbed)).trans ?_
  have e2 := bed.localResolutionHomOn_comp_map D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage Γ.W)
    (D.isCompact_closure_ambImage Γ.W Γ.isCompact_closure_W) (D.embedding i).ambientTriple
    (D.embedding i).domBEDan_ambientTriple g hgo (D.isPullbackOf_ambientTriple_sigmaTriple i)
    (Γ.W i) (Γ.isCompact_closure_W i) (D.image_subset_ambImage Γ.W i) hbed
  have hinj : Function.Injective
      (AnalyticMap.restrictMap g (Γ.W i) (D.ambImage Γ.W) (D.image_subset_ambImage Γ.W i)) :=
    fun a b h => Subtype.ext (hgo.2 (congrArg Subtype.val h))
  have hOI := isOpenImmersion_homOfPullbackEq_of_injective
    (AnalyticMap.restrictMap g (Γ.W i) (D.ambImage Γ.W) (D.image_subset_ambImage Γ.W i))
    (AnalyticMap.isLocalDiffeomorph_restrictMap hgo.1 (Γ.W i) (D.ambImage Γ.W)
      (D.image_subset_ambImage Γ.W i)) hinj
    (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap D.sigmaTriple (D.ambImage Γ.W)
      (D.embedding i).ambientTriple g (Γ.W i) (D.image_subset_ambImage Γ.W i)
      (D.isPullbackOf_ambientTriple_sigmaTriple i))
  obtain ⟨q, hq, -, heq⟩ :=
    (D.embedding i).exists_openImmersion_toSpaceMap_eq bed (Γ.W i) (Γ.isCompact_closure_W i)
  ext w
  have hw := congrFun (congrArg AnalyticSpace.Hom.toFun e2) w
  have hq' := congrFun (congrArg AnalyticSpace.KLocallyRingedSpace.Hom.toFun heq) w
  change (bed.localResolutionMapOn D.sigmaTriple D.domBEDan_sigmaTriple
      (D.ambImage Γ.W) (D.isCompact_closure_ambImage Γ.W Γ.isCompact_closure_W))
      (AnalyticSpace.KLocallyRingedSpace.Hom.toFun
        (D.resIn bed Γ.W Γ.isCompact_closure_W hbed i) w) ∈
      AnalyticSpace.singularLocus _ ↔
    AnalyticSpace.KLocallyRingedSpace.Hom.toFun
      (D.pieceToSpace bed i (Γ.W i) (Γ.isCompact_closure_W i)) w ∈
          X.singularLocus
  rw [show (bed.localResolutionMapOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage Γ.W)
      (D.isCompact_closure_ambImage Γ.W Γ.isCompact_closure_W))
      (AnalyticSpace.KLocallyRingedSpace.Hom.toFun
        (D.resIn bed Γ.W Γ.isCompact_closure_W hbed i) w) =
    (IdealSheaf.homOfPullbackEq
        ⇑(AnalyticMap.restrictMap g (Γ.W i) (D.ambImage Γ.W) (D.image_subset_ambImage Γ.W i)) _
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap D.sigmaTriple (D.ambImage Γ.W)
          (D.embedding i).ambientTriple g (Γ.W i) (D.image_subset_ambImage Γ.W i)
          (D.isPullbackOf_ambientTriple_sigmaTriple i)))
      ((bed.localResolutionMapOn (D.embedding i).ambientTriple
          (D.embedding i).domBEDan_ambientTriple (Γ.W i) (Γ.isCompact_closure_W i)) w) from hw]
  rw [show AnalyticSpace.KLocallyRingedSpace.Hom.toFun
      (D.pieceToSpace bed i (Γ.W i) (Γ.isCompact_closure_W i)) w =
    AnalyticSpace.KLocallyRingedSpace.Hom.toFun q
      ((bed.localResolutionMapOn (D.embedding i).ambientTriple
          (D.embedding i).domBEDan_ambientTriple (Γ.W i) (Γ.isCompact_closure_W i)) w) from hq']
  exact (not_congr (AnalyticSpace.mem_reg_iff_of_isOpenImmersion _ hOI
    _)).symm.trans
    (not_congr (AnalyticSpace.mem_reg_iff_of_isOpenImmersion q hq _))

/-- **The support of the datum's glued family is `Π⁻¹(X.singularLocus)`** ([Kol07, Theorem 45(3)]) —
`iUnion_support_glueFamily`, the pieces' supports
(`iUnion_support_pieceTrace`), `toFun_descMap_ιGlued`, the pieces covering the glued space
(`exists_ιGlued_eq`). -/
theorem iUnion_support_gluedMembersOn
    (hc : Γ.glue.LabelledCompat (pieceTrace D bed Γ hbed) (fun _ σ => σ)) :
    (⋃ σ, IdealSheaf.support (gluedMembersOn D bed Γ hbed hc σ)) =
      AnalyticSpace.KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹'
        X.singularLocus := by
  have h1 := Γ.glue.iUnion_support_glueFamily (H := pieceTrace D bed Γ hbed) (lab := fun _ σ => σ)
    (fun _ => Function.injective_id) hc
  change (⋃ σ, IdealSheaf.support
    (Γ.glue.glueFamily (pieceTrace D bed Γ hbed) (fun _ σ => σ) hc σ)) = _
  rw [h1]
  have h2 : ∀ i, (⋃ σ, IdealSheaf.support (pieceTrace D bed Γ hbed i σ)) =
      AnalyticSpace.KLocallyRingedSpace.Hom.toFun (Γ.glue.ιGlued i) ⁻¹'
        (AnalyticSpace.KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹'
          X.singularLocus) := by
    intro i
    rw [iUnion_support_pieceTrace D bed Γ hbed i]
    ext y
    exact Iff.of_eq (congrArg (fun p => p ∈ X.singularLocus)
      (Γ.glue.toFun_descMap_ιGlued i y).symm)
  simp_rw [h2, Set.image_preimage_eq_inter_range]
  rw [← Set.inter_iUnion]
  refine Set.inter_eq_left.mpr ?_
  intro z _
  obtain ⟨i, y, rfl⟩ := Γ.glue.exists_ιGlued_eq z
  exact Set.mem_iUnion.mpr ⟨i, y, rfl⟩

/-- The datum's glued family on `resolutionOnFull D bed` — the CHOSEN gluing datum's glued space
(the unfolding lemma `resolutionOnFullPair_eq_of_glues`) — with its three facts, as an existence
statement over the coproduct's stage set. -/
theorem exists_gluedMembers_resolutionOnFull (h : D.ResolutionGluesOn bed)
    (hc : h.some.glue.LabelledCompat (pieceTrace D bed h.some hbed) (fun _ σ => σ)) :
    ∃ H : D.sigmaIndex bed h.some.W h.some.isCompact_closure_W →
        AnalyticSpace.ClosedSubspace (D.resolutionOnFull bed),
      AnalyticSpace.ClosedSubspace.IsSncFamily H ∧
      LocallyFinite (fun σ => IdealSheaf.support (H σ)) ∧
      (⋃ σ, IdealSheaf.support (H σ)) =
        AnalyticSpace.KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹'
          X.singularLocus := by
  suffices key : ∀ p : Σ R :
      AnalyticSpace.{u} 𝕜, (R ⟶ X),
      p = D.resolutionOnFullPair bed →
        ∃ H : D.sigmaIndex bed h.some.W h.some.isCompact_closure_W →
            AnalyticSpace.ClosedSubspace p.1,
          AnalyticSpace.ClosedSubspace.IsSncFamily H ∧
          LocallyFinite (fun σ => IdealSheaf.support (H σ)) ∧
          (⋃ σ, IdealSheaf.support (H σ)) =
            AnalyticSpace.KLocallyRingedSpace.Hom.toFun p.2 ⁻¹'
              X.singularLocus from key _ rfl
  intro p hp
  rw [D.resolutionOnFullPair_eq_of_glues bed h] at hp
  subst hp
  exact ⟨gluedMembersOn D bed h.some hbed hc, isSncFamily_gluedMembersOn D bed h.some hbed hc,
    locallyFinite_gluedMembersOn D bed h.some hbed hc,
    iUnion_support_gluedMembersOn D bed h.some hbed hc⟩

/-- **The datum's glued family on `resolutionOn D bed`** (the part over `U`,
`IsSncFamily.comap_ofRestrict` along the open immersion) with its three facts — clause (3) of
`exists_functorial_resolution` for ONE datum ([Kol07, Theorem 45(3)]; [Wlo09, §4.3]): simple normal
crossings, locally finite, support `Π_U⁻¹(X.singularLocus)` under the map `resolutionOnToSpace` read
into `X` (`resolutionOnToSpace = ofRestrict ≫ resolutionOnFullMap`,
`Hom.restrictTo_comp_ofRestrict`). -/
theorem exists_gluedMembers_resolutionOn (h : D.ResolutionGluesOn bed)
    (hc : h.some.glue.LabelledCompat (pieceTrace D bed h.some hbed) (fun _ σ => σ)) :
    ∃ H : D.sigmaIndex bed h.some.W h.some.isCompact_closure_W →
        AnalyticSpace.ClosedSubspace (D.resolutionOn bed),
      AnalyticSpace.ClosedSubspace.IsSncFamily H ∧
      LocallyFinite (fun σ => IdealSheaf.support (H σ)) ∧
      (⋃ σ, IdealSheaf.support (H σ)) =
        AnalyticSpace.KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed) ⁻¹'
          X.singularLocus := by
  obtain ⟨H, hsnc, hfin, hsupp⟩ := D.exists_gluedMembers_resolutionOnFull bed hbed h hc
  set V := AnalyticSpace.openOf (D.resolutionOnFull bed)
    (AnalyticSpace.KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U) with hV
  set ρ := AnalyticSpace.KLocallyRingedSpace.ofRestrict
    (D.resolutionOnFull bed).toKLocallyRingedSpace V with hρ
  have hsupp' : ∀ σ, IdealSheaf.support (AnalyticSpace.QuotientSpace.comap ρ.1
        (H σ)) =
      Subtype.val ⁻¹' IdealSheaf.support (H σ) :=
    fun σ => AnalyticSpace.QuotientSpace.cosupport_comap _ (H σ)
  have heq : D.resolutionOnToSpace bed = CategoryTheory.CategoryStruct.comp ρ
      (D.resolutionOnFullMap bed : (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
        X.toKLocallyRingedSpace) :=
    AnalyticSpace.KLocallyRingedSpace.Hom.restrictTo_comp_ofRestrict (D.resolutionOnFullMap bed)
      _ _ (AnalyticSpace.Hom.mapsTo_openOf (D.resolutionOnFullMap bed) U)
  refine ⟨fun σ => AnalyticSpace.QuotientSpace.comap ρ.1 (H σ), hsnc.comap_ofRestrict V, ?_, ?_⟩
  · change LocallyFinite fun σ => IdealSheaf.support (AnalyticSpace.QuotientSpace.comap ρ.1
        (H σ))
    simp only [hsupp']
    exact hfin.preimage_continuous continuous_subtype_val
  · change (⋃ σ, IdealSheaf.support (AnalyticSpace.QuotientSpace.comap ρ.1
        (H σ))) = _
    simp only [hsupp']
    rw [heq]
    change (⋃ σ, Subtype.val ⁻¹' IdealSheaf.support (H σ)) =
      Subtype.val ⁻¹' (AnalyticSpace.KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap
        bed) ⁻¹'
        X.singularLocus)
    rw [← hsupp, Set.preimage_iUnion]

end Hironaka.Manifold.LocalEmbeddingData

end
