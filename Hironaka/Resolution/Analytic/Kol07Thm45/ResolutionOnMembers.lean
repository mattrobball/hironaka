/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductGluedFamily
import Hironaka.AnalyticSpace.IsoOverOpen
import Hironaka.AnalyticSpace.SncBoundaryChart
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalModel
import Hironaka.Resolution.Analytic.Kol07Thm45.RigidOverLocalResolution
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The glued family on `resolutionOn` with its piece-compatibility clause

Kollár's descent of the centres through their agreement on the overlaps, (37.2) in
[Kol07, Proposition 37, proof]; the glued family's support is `Π⁻¹(X.singularLocus)` [Kol07, Theorem
45(3)] ([Wlo09, §4, (3)⇒(4)]; [Wlo09, §4.3]). Clause (3) of `exists_functorial_resolution` for one
datum `D` is the existence of a labelled family `H` of closed subspaces of `resolutionOn D bed` —
simple normal crossings, locally finite, with support `Π_U⁻¹(X.singularLocus)`
(`exists_gluedMembers_resolutionOn`, `CoproductGluedFamily.lean`). The assembly of the exhaustion's
chain families (`ExhaustionChainFamilies.lean`) needs more than the existence: it compares the
members of two adjacent levels over their overlap through the pieces, so it must know that the
member of label `σ` restricts, on the part of `resolutionOn` over a base open `P` inside a piece's
domain, to the piece trace of label `σ` — along the identification of that part with the part of the
piece's local resolution over `P` (`exists_isoOver_resolutionOn_localResolution`,
`LocalModel.lean`). The clause is stated for EVERY isomorphism over `X` between the two parts, so
that no user has to know which identification was chosen: under the independence of the local
resolution (`hind`) the parts of `resolutionOn` are rigid over `X` (`rigidOver_resolutionOnToSpace`,
`RigidOverLocalResolution.lean`), hence any two such isomorphisms agree (`isoOver_unique_of_aut`),
and the clause reduces to the one chosen identification: the inverse of the gluing's `partIso`,
along which the glued member pulls back to the piece's member (`comap_ιGlued_gluedMembersOn`).

The construction repeats that of `CoproductGluedFamily.lean` (`gluedMembersOn` on the chosen
gluing's glued space, read into the definition of the resolution through
`resolutionOnFullPair_eq_of_glues`, restricted to the part over `U`), because the statements there
are existential and hide the members.

* `KLocallyRingedSpace.exists_iso_restrictOpen_restrictOpen_comap'` — the identification of the part
  of a restriction with the part of the space (`Hironaka/AnalyticSpace/RestrictOverLemmas.lean` has
  the unprimed form), with the identity of the two open immersions into the space as its conclusion
  (the over-`Z` form follows);
* `KLocallyRingedSpace.isIso_restrictTo_of_isIso` — the restriction of an isomorphism to matching
  opens is an isomorphism (used by `CoproductLevelPair.lean`).
* `LocalEmbeddingData.exists_gluedMembers_resolutionOn_compat` — the glued family with its
  piece-compatibility clause.

Not in the sources beyond Kollár's descent; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace

universe u

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- **The part of the restriction `g|U : A|U ⟶ Z|U'` over an open `O` with `g⁻¹O ⊆ U` is the part
of `A` over `O`**, as open subspaces of `A`: the isomorphism `isoOfRangeEq` of the two open
immersions `(A|U)|_{(g|U)⁻¹O} ⟶ A|U ⟶ A` and `A|g⁻¹O ⟶ A`, followed by the second, is the
first. -/
theorem exists_iso_restrictOpen_restrictOpen_comap' {A Z : KLocallyRingedSpace.{u} K} (g : A ⟶ Z)
    (U : Opens A) (U' : Opens Z) (h : ∀ a ∈ U, Hom.toFun g a ∈ U') (O : Opens Z)
    (hOU : ∀ a, Hom.toFun g a ∈ O → a ∈ U) :
    ∃ e : (A.restrictOpen U).restrictOpen
          (Opens.comap ⟨Hom.toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U'),
            Hom.continuous_toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U')⟩ O) ⟶
        A.restrictOpen (Opens.comap ⟨Hom.toFun g, Hom.continuous_toFun g⟩ O),
      IsIso e ∧
        e ≫ ofRestrict A (Opens.comap ⟨Hom.toFun g, Hom.continuous_toFun g⟩ O) =
          ofRestrict _ _ ≫ ofRestrict A U := by
  have hπ : ∀ a : A.restrictOpen U,
      Hom.toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U') a = Hom.toFun g a.1 := fun a =>
    Hom.toFun_restrictTo g U U' h a
  have hinst : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (A.restrictOpen U)
        (Opens.comap ⟨Hom.toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U'),
          Hom.continuous_toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U')⟩ O) ≫
        ofRestrict A U).1 :=
    inferInstanceAs (AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      ((ofRestrict (A.restrictOpen U) _).1 ≫ (ofRestrict A U).1))
  have hrange : range (Hom.toFun (ofRestrict (A.restrictOpen U)
        (Opens.comap ⟨Hom.toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U'),
          Hom.continuous_toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U')⟩ O) ≫
        ofRestrict A U)) =
      range (Hom.toFun (ofRestrict A (Opens.comap ⟨Hom.toFun g, Hom.continuous_toFun g⟩ O))) := by
    rw [range_toFun_ofRestrict]
    ext a
    constructor
    · rintro ⟨v, rfl⟩
      change Hom.toFun g v.1.1 ∈ O
      rw [← hπ]
      exact v.2
    · intro ha
      refine ⟨Subtype.mk (Subtype.mk a (hOU a ha)) ?_, rfl⟩
      change Hom.toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U') (Subtype.mk a (hOU a ha)) ∈
        (O : Set Z)
      exact Set.mem_of_eq_of_mem (hπ (Subtype.mk a (hOU a ha))) ha
  exact ⟨(isoOfRangeEq _ _ hrange).hom, Iso.isIso_hom _, isoOfRangeEq_hom_comp _ _ hrange⟩

/-- **The restriction of an isomorphism to matching opens is an isomorphism** — the inverse is the
restriction of the inverse (`Hom.restrictTo_comp_ofRestrict`, `Hom.ext_of_comp_ofRestrict`). -/
theorem isIso_restrictTo_of_isIso {A B : KLocallyRingedSpace.{u} K} (g : A ⟶ B) [IsIso g]
    (U : Opens A) (U' : Opens B) (hU : ∀ a ∈ U, Hom.toFun g a ∈ U')
    (hU' : ∀ b ∈ U', Hom.toFun (inv g) b ∈ U) : IsIso (Hom.restrictTo g U U' hU) :=
  ⟨⟨Hom.restrictTo (inv g) U' U hU', by
    refine Hom.ext_of_comp_ofRestrict ?_
    rw [Category.id_comp, Category.assoc, Hom.restrictTo_comp_ofRestrict, ← Category.assoc,
      Hom.restrictTo_comp_ofRestrict, Category.assoc, IsIso.hom_inv_id, Category.comp_id], by
    refine Hom.ext_of_comp_ofRestrict ?_
    rw [Category.id_comp, Category.assoc, Hom.restrictTo_comp_ofRestrict, ← Category.assoc,
      Hom.restrictTo_comp_ofRestrict, Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩⟩

end AnalyticSpace.KLocallyRingedSpace

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
  (hind : LocalResolutionIndependentOn X bed) (h : D.ResolutionGluesOn bed)

/-- **The glued members and the chosen identifications on the full glued space**, for any pair
equal to `resolutionOnFullPair` — unfolded to the chosen gluing
(`resolutionOnFullPair_eq_of_glues`): the members are `gluedMembersOn`, the identification of the
part over `P ≤ pieceDom i (W i)` with the part of the piece is the inverse of the gluing's
`partIso`, along which the glued member of label `σ` pulls back to the piece trace of label `σ`
(`comap_ιGlued_gluedMembersOn`, `partIso_inv_comp_ofRestrict`). -/
theorem gluedMembers_resolutionOnFullPair_compat_aux
    (hc : h.some.glue.LabelledCompat (pieceTrace D bed h.some hbed) (fun _ σ => σ))
    (R : AnalyticSpace.{u} 𝕜) (π : R ⟶ X)
    (hp : (⟨R, π⟩ : Σ R : AnalyticSpace.{u} 𝕜, (R ⟶ X)) = D.resolutionOnFullPair bed) :
    ∃ H : D.sigmaIndex bed h.some.W h.some.isCompact_closure_W →
        ClosedSubspace R,
      ClosedSubspace.IsSncFamily H ∧
      LocallyFinite (fun σ => Manifold.IdealSheaf.support (H σ)) ∧
      (⋃ σ, Manifold.IdealSheaf.support (H σ)) =
        KLocallyRingedSpace.Hom.toFun π ⁻¹' singularLocus X ∧
      ∀ (i : D.ι) (P : Opens X), P ≤ D.pieceDom i (h.some.W i) →
        ∃ t : R.toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun π, Hom.continuous_toFun π⟩ P) ⟶
            ((D.embedding i).localResolution bed (h.some.W i)
                (h.some.isCompact_closure_W i)).toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed
                  (h.some.W i)
                  (h.some.isCompact_closure_W i)),
                Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                  (h.some.isCompact_closure_W i))⟩ P),
          IsIso t ∧
          ofRestrict _ _ ≫ π = (t ≫ ofRestrict _ _) ≫
            (D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i) ∧
          ∀ σ, QuotientSpace.comap t.1
              (QuotientSpace.comap (ofRestrict ((D.embedding i).localResolution bed
                  (h.some.W i) (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
                (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed
                    (h.some.W i)
                    (h.some.isCompact_closure_W i)),
                  Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                    (h.some.isCompact_closure_W i))⟩ P)).1
                (pieceTrace D bed h.some hbed i σ)) =
            QuotientSpace.comap (ofRestrict R.toKLocallyRingedSpace
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun π, Hom.continuous_toFun π⟩ P)).1 (H σ) :=
                  by
  rw [D.resolutionOnFullPair_eq_of_glues bed h] at hp
  obtain ⟨rfl, hπ⟩ := Sigma.mk.inj hp
  obtain rfl := eq_of_heq hπ
  refine ⟨gluedMembersOn D bed h.some hbed hc, isSncFamily_gluedMembersOn D bed h.some hbed hc,
    locallyFinite_gluedMembersOn D bed h.some hbed hc,
    iUnion_support_gluedMembersOn D bed h.some hbed hc, ?_⟩
  intro i P hPi
  refine ⟨(h.some.glue.partIso i P hPi).inv, Iso.isIso_inv _,
    (h.some.glue.partIso_inv_comp_over i P hPi).symm.trans (Category.assoc _ _ _).symm, ?_⟩
  intro σ
  have h6 : QuotientSpace.comap (h.some.glue.partIso i P hPi).inv.1 (QuotientSpace.comap
        (ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)).1 (QuotientSpace.comap (h.some.glue.ιGlued i).1
          (gluedMembersOn D bed h.some hbed hc σ))) =
      QuotientSpace.comap ((h.some.glue.partIso i P hPi).inv ≫ ofRestrict ((D.embedding
          i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P) ≫
        h.some.glue.ιGlued i).1 (gluedMembersOn D bed h.some hbed hc σ) :=
    (congrArg (QuotientSpace.comap (h.some.glue.partIso i P hPi).inv.1)
      (QuotientSpace.comap_comp (h.some.glue.ιGlued i).1 (gluedMembersOn D bed h.some hbed hc σ)
        (ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)).1).symm).trans
      (QuotientSpace.comap_comp ((ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)).1 ≫ (h.some.glue.ιGlued i).1)
        (gluedMembersOn D bed h.some hbed hc σ) (h.some.glue.partIso i P hPi).inv.1).symm
  calc QuotientSpace.comap (h.some.glue.partIso i P hPi).inv.1
        (QuotientSpace.comap (ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)).1 (pieceTrace D bed h.some hbed i σ))
      = QuotientSpace.comap (h.some.glue.partIso i P hPi).inv.1 (QuotientSpace.comap
          (ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)).1 (QuotientSpace.comap (h.some.glue.ιGlued i).1
            (gluedMembersOn D bed h.some hbed hc σ))) :=
        congrArg (fun J => QuotientSpace.comap (h.some.glue.partIso i P hPi).inv.1
          (QuotientSpace.comap (ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)).1 J))
          (comap_ιGlued_gluedMembersOn D bed h.some hbed hc i σ).symm
    _ = QuotientSpace.comap ((h.some.glue.partIso i P hPi).inv ≫
          ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P) ≫
          h.some.glue.ιGlued i).1 (gluedMembersOn D bed h.some hbed hc σ) := h6
    _ = _ :=
        congrArg (fun k : h.some.glue.gluedOver.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun h.some.glue.descMap,
              Hom.continuous_toFun h.some.glue.descMap⟩ P) ⟶
            h.some.glue.gluedOver.toKLocallyRingedSpace =>
          QuotientSpace.comap k.1 (gluedMembersOn D bed h.some hbed hc σ))
          (h.some.glue.partIso_inv_comp_ofRestrict i P hPi)

include hind in
/-- **The datum's glued family on `resolutionOn D bed` WITH its piece-compatibility clause**
((37.2) in [Kol07, Proposition 37, proof]; [Kol07, Theorem 45(3)]; [Wlo09, §4.3]), with the
independence of the local resolution as `hind` — the family has simple normal crossings, is
locally finite, its support is `Π_U⁻¹(X.singularLocus)`, and over every base open `P ⊆ U` inside the
domain of a piece `i`, along EVERY isomorphism `s` over `X` from the part of `resolutionOn` over `P`
to the part of the piece's local resolution over `P`, the pull-back of the piece trace of label `σ`
is the pull-back of the member of label `σ` (rigidity: all such `s` are the chosen
identification). -/
theorem exists_gluedMembers_resolutionOn_compat
    (hc : h.some.glue.LabelledCompat (pieceTrace D bed h.some hbed) (fun _ σ => σ)) :
    ∃ H : D.sigmaIndex bed h.some.W h.some.isCompact_closure_W →
        ClosedSubspace (D.resolutionOn bed),
      ClosedSubspace.IsSncFamily H ∧
      LocallyFinite (fun σ => Manifold.IdealSheaf.support (H σ)) ∧
      (⋃ σ, Manifold.IdealSheaf.support (H σ)) =
        KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed) ⁻¹'
            singularLocus X ∧
      ∀ (i : D.ι) (P : Opens X), (P : Set X) ⊆ U → P ≤ D.pieceDom i (h.some.W i) →
        ∀ s : (D.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
                Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ⟶
            ((D.embedding i).localResolution bed (h.some.W i)
                (h.some.isCompact_closure_W i)).toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed
                  (h.some.W i)
                  (h.some.isCompact_closure_W i)),
                Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                  (h.some.isCompact_closure_W i))⟩ P),
          IsIso s →
          ofRestrict _ _ ≫ D.resolutionOnToSpace bed =
            (s ≫ ofRestrict _ _) ≫
              (D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i) →
          ∀ σ, QuotientSpace.comap s.1
              (QuotientSpace.comap (ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
                  (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
                (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed
                    (h.some.W i)
                    (h.some.isCompact_closure_W i)),
                  Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                    (h.some.isCompact_closure_W i))⟩ P)).1
                (pieceTrace D bed h.some hbed i σ)) =
            QuotientSpace.comap (ofRestrict (D.resolutionOn bed).toKLocallyRingedSpace
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
                Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P)).1 (H σ) := by
  -- the members and the chosen identifications on the full glued space
  obtain ⟨H, hsnc, hfin, hsupp, hpart⟩ := D.gluedMembers_resolutionOnFullPair_compat_aux bed hbed
    h hc (D.resolutionOnFull bed) (D.resolutionOnFullMap bed) rfl
  -- the part over `U`: the members pulled back along the open immersion `ρ`
  have hsupp' : ∀ σ, Manifold.IdealSheaf.support
      (QuotientSpace.comap (ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))).1 (H σ)) =
      Subtype.val ⁻¹' Manifold.IdealSheaf.support (H σ) :=
    fun σ => QuotientSpace.cosupport_comap _ (H σ)
  have heq : D.resolutionOnToSpace bed = ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U)) ≫
                  (D.resolutionOnFullMap bed :
                  (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
            X.toKLocallyRingedSpace) :=
    Hom.restrictTo_comp_ofRestrict (D.resolutionOnFullMap bed) _ _
      (Hom.mapsTo_openOf (D.resolutionOnFullMap bed) U)
  refine ⟨fun σ => QuotientSpace.comap (ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))).1 (H σ), ?_, ?_,
                  ?_, ?_⟩
  · exact hsnc.comap_ofRestrict _
  · change LocallyFinite fun σ => Manifold.IdealSheaf.support
      (QuotientSpace.comap (ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))).1 (H σ))
    simp only [hsupp']
    exact hfin.preimage_continuous continuous_subtype_val
  · change (⋃ σ, Manifold.IdealSheaf.support
      (QuotientSpace.comap (ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))).1 (H σ))) = _
    simp only [hsupp']
    rw [heq]
    change (⋃ σ, Subtype.val ⁻¹' Manifold.IdealSheaf.support (H σ)) =
      Subtype.val ⁻¹' (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹'
        singularLocus X)
    rw [← hsupp, Set.preimage_iUnion]
  · -- the compatibility clause: every `s` over `X` is the chosen identification (rigidity)
    intro i P hPU hPi s hs hover σ
    obtain ⟨t, ht, htc, htm⟩ := hpart i P hPi
    -- the identification of the part of `resolutionOn` over `P` with the part of the full glued
    -- space over `P`, stated ONCE in the spelling of `resolutionOn` (the two spellings of the
    -- part are definitionally equal; every later step is syntactic in this spelling)
    have hE : ∃ e : (D.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ⟶
        (D.resolutionOnFull bed).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
            Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ P),
        IsIso e ∧ e ≫ ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
              Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ P) = ofRestrict (D.resolutionOn
                  bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ≫ ofRestrict (D.resolutionOnFull
                  bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U)) := by
      obtain ⟨e, he, hei⟩ := exists_iso_restrictOpen_restrictOpen_comap' (D.resolutionOnFullMap bed
          : (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
            X.toKLocallyRingedSpace)
        (openOf (D.resolutionOnFull bed)
          (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))
        (openOf X U)
        (Hom.mapsTo_openOf (D.resolutionOnFullMap bed) U) P
        (fun a ha => mem_openOf_of_subset Set.Subset.rfl (hPU ha))
      exact ⟨e, he, hei⟩
    obtain ⟨e, he, hei'⟩ := hE
    -- the chosen identification `e ≫ t` lies over `X`, step by step
    have c1 : ofRestrict (D.resolutionOn bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ≫ D.resolutionOnToSpace bed =
                  ofRestrict (D.resolutionOn bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ≫ (ofRestrict
                  (D.resolutionOnFull bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U)) ≫
                  (D.resolutionOnFullMap bed :
                  (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
            X.toKLocallyRingedSpace)) :=
      congrArg (fun k => ofRestrict (D.resolutionOn bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ≫ k) heq
    have c2 : ofRestrict (D.resolutionOn bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ≫ (ofRestrict
                  (D.resolutionOnFull bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U)) ≫
                  (D.resolutionOnFullMap bed :
                  (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
            X.toKLocallyRingedSpace)) = (ofRestrict (D.resolutionOn bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ≫ ofRestrict (D.resolutionOnFull
                  bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))) ≫
                  (D.resolutionOnFullMap bed :
                  (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
            X.toKLocallyRingedSpace) := (Category.assoc _ _ _).symm
    have c3 : (ofRestrict (D.resolutionOn bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ≫ ofRestrict (D.resolutionOnFull
                  bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))) ≫
                  (D.resolutionOnFullMap bed :
                  (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
            X.toKLocallyRingedSpace) = (e ≫ ofRestrict (D.resolutionOnFull
                bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
              Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ P)) ≫ (D.resolutionOnFullMap bed :
                  (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
            X.toKLocallyRingedSpace) := congrArg (fun k : (D.resolutionOn
                bed).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ⟶ (D.resolutionOnFull
                  bed).toKLocallyRingedSpace => k ≫ (D.resolutionOnFullMap bed :
                  (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
            X.toKLocallyRingedSpace)) hei'.symm
    have c4 : (e ≫ ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
              Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ P)) ≫ (D.resolutionOnFullMap bed :
                  (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
            X.toKLocallyRingedSpace) = e ≫ (ofRestrict (D.resolutionOnFull
                bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
              Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ P) ≫ (D.resolutionOnFullMap bed :
                  (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
            X.toKLocallyRingedSpace)) := Category.assoc _ _ _
    have c5 : e ≫ (ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
              Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ P) ≫ (D.resolutionOnFullMap bed :
                  (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
            X.toKLocallyRingedSpace)) = e ≫ ((t ≫ ofRestrict ((D.embedding i).localResolution bed
                (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)) ≫ (D.embedding i).toSpaceMap bed (h.some.W i)
                    (h.some.isCompact_closure_W i)) := congrArg (fun k => e ≫ k) htc
    have c6 : e ≫ ((t ≫ ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)) ≫ (D.embedding i).toSpaceMap bed (h.some.W i)
                    (h.some.isCompact_closure_W i)) = ((e ≫ t) ≫ ofRestrict ((D.embedding
                    i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)) ≫ (D.embedding i).toSpaceMap bed (h.some.W i)
                    (h.some.isCompact_closure_W i) := by
      simp only [Category.assoc]
    have hc₀ : ofRestrict (D.resolutionOn bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ≫ D.resolutionOnToSpace bed =
                  ((e ≫ t) ≫ ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)) ≫ (D.embedding i).toSpaceMap bed (h.some.W i)
                    (h.some.isCompact_closure_W i) :=
      c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6))))
    have hs_eq : s = e ≫ t := isoOver_unique_of_aut (D.resolutionOnToSpace bed)
      ((D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i)) P
      (D.rigidOver_resolutionOnToSpace bed hbed hind P hPU) s (e ≫ t) hs
      (@IsIso.comp_isIso _ _ _ _ _ _ _ he ht) hover hc₀
    -- the members: `s = e ≫ t`, `t` carries the trace to the glued member, `e ≫ ofR = ofR ≫ ρ`
    have m1 : QuotientSpace.comap (e ≫ t).1
          (QuotientSpace.comap (ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)).1 (pieceTrace D bed h.some hbed i σ)) =
        QuotientSpace.comap e.1 (QuotientSpace.comap t.1
          (QuotientSpace.comap (ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)).1 (pieceTrace D bed h.some hbed i σ))) :=
      QuotientSpace.comap_comp t.1 (QuotientSpace.comap (ofRestrict ((D.embedding
          i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)).1
        (pieceTrace D bed h.some hbed i σ)) e.1
    have m2 : QuotientSpace.comap e.1 (QuotientSpace.comap (ofRestrict (D.resolutionOnFull
        bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
              Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ P)).1 (H σ)) =
        QuotientSpace.comap (e ≫ ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
              Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ P)).1 (H σ) :=
      (QuotientSpace.comap_comp (ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
              Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ P)).1 (H σ) e.1).symm
    have m3 : QuotientSpace.comap (e ≫ ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
              Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ P)).1 (H σ) =
        QuotientSpace.comap (ofRestrict (D.resolutionOn bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ≫ ofRestrict (D.resolutionOnFull
                  bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))).1 (H σ) :=
      congrArg (fun k : (D.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ⟶ (D.resolutionOnFull
                  bed).toKLocallyRingedSpace =>
        QuotientSpace.comap k.1 (H σ)) hei'
    have m4 : QuotientSpace.comap (ofRestrict (D.resolutionOn bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ≫ ofRestrict (D.resolutionOnFull
                  bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))).1 (H σ) =
        QuotientSpace.comap (ofRestrict (D.resolutionOn bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P)).1 (QuotientSpace.comap
                  (ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))).1 (H σ)) :=
      QuotientSpace.comap_comp (ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
            (openOf (D.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))).1 (H σ)
                  (ofRestrict (D.resolutionOn
                  bed).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P)).1
    exact (congrArg (fun k => QuotientSpace.comap (k : (D.resolutionOn
        bed).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ⟶
        ((D.embedding i).localResolution bed (h.some.W i)
          (h.some.isCompact_closure_W i)).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
            (h.some.isCompact_closure_W i)),
          Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
            (h.some.isCompact_closure_W i))⟩ P)).1
        (QuotientSpace.comap (ofRestrict ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P)).1 (pieceTrace D bed h.some hbed i σ)))
                    hs_eq).trans
      (m1.trans ((congrArg (QuotientSpace.comap e.1) (htm σ)).trans (m2.trans (m3.trans m4))))

end Hironaka.Manifold.LocalEmbeddingData

end
