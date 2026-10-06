/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.HomGlue
public import Hironaka.AnalyticSpace.HomOfSections
import Hironaka.AnalyticSpace.HomLocal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Isomorphisms over a base, glued along an open cover of the base

The resolutions of two pieces of a cover are identified over their overlap: the resolution is
independent of the chosen embedding up to a canonical isomorphism [Kol07, Theorem 36, proof], and it
commutes with open embeddings [Kol07, 44] and with local analytic isomorphisms [Wlo09, §4]. When an
isomorphism over the base between two resolutions of one open subset is unique, the identifications
given on the members of an open cover of the overlap agree where the members meet, and glue to one
over the whole overlap. That is the statement here, for `K`-locally-ringed spaces over a base with
the uniqueness as hypothesis. Two `K`-locally-ringed spaces `A`, `B` over `Z` (`πA`, `πB`), an open
subset `O ⊆ Z` covered by open subsets `N i ≤ O`, and isomorphisms `s i : A|πA⁻¹(N i) ≅ B|πB⁻¹(N i)`
over `Z`, unique among such on every open subset `O' ≤ O`: they glue to an isomorphism
`A|πA⁻¹O ≅ B|πB⁻¹O` over `Z`.

* `KLocallyRingedSpace.restrictOver`: the restriction of a morphism over `Z` between the parts over
  `P` to the parts over `Q ≤ P`, with its compatibility lemmas; an isomorphism over `Z` restricts to
  an isomorphism (`isIso_restrictOver`), and uniqueness of isomorphisms over `Z` from `A` to `B`
  gives uniqueness from `B` to `A` (`uniq_symm`).
* `KLocallyRingedSpace.glueIsoPieces`: the morphism `A|πA⁻¹O ⟶ B|πB⁻¹O` assembled from the `s i` by
  `glueOfCover` on the cover of `A|πA⁻¹O` by the parts over the `N i`; the pieces agree on the
  overlaps by the uniqueness at `N i ⊓ N j` (`gluePiece_compatible`); it lies over `Z`
  (`glueIsoPieces_over`) and restricts to the pieces (`ofRestrict_comp_glueIsoPieces`).
* `KLocallyRingedSpace.glueIsoPieces_comp_glueIsoPieces`: the assemblies of two piecewise inverse
  families are inverse (`hom_ext_of_cover`).
* `KLocallyRingedSpace.exists_isIso_over_of_cover`: the statement.

The restriction `restrictOver` is the transition of a gluing datum restricted to the parts over a
smaller base open subset (`Hironaka.Resolution.Analytic.Kol07Thm45.Glue.OverRigidity`,
`Hironaka.Resolution.Analytic.Kol07Thm45.PieceTransitionGlue`, `PieceGlueIndep`,
`ResolutionFunctorial`, `RigidOverLocalResolution`, `CoproductLevelPair`);
`exists_isIso_over_of_cover` gives the transition isomorphisms between the local resolutions of two
pieces over their overlap (`Hironaka.Resolution.Analytic.Kol07Thm45.PieceTransitionGlue`,
`PieceGlueIndep`, `ResolutionFunctorial`,
`Hironaka.Resolution.Analytic.Kol07Thm45.RestrictSetIncl`).
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K] {A B Z : KLocallyRingedSpace.{u} K} (πA : A ⟶ Z) (πB : B ⟶ Z)

/-! ### Restricting a morphism over `Z` to a smaller open of the base -/

section RestrictOver

variable {P Q : Opens Z} (hQP : Q ≤ P)
  (s : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ P) ⟶
    B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ P))
  (hs : ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ P) ≫ πA =
    (s ≫ ofRestrict B (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ P)) ≫ πB)

include hs in
/-- A morphism over `Z` preserves the point of the base. -/
theorem toFun_π_eq_of_over
    (x : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ P)) :
    Hom.toFun πB (Hom.toFun s x).1 = Hom.toFun πA x.1 :=
  (congrArg (fun φ => Hom.toFun φ x) hs).symm

/-- The restriction of a morphism over `Z` between the parts over `P` to the parts over `Q ≤ P`:
the lift of `A|πA⁻¹Q ⟶ A|πA⁻¹P ⟶ B|πB⁻¹P ⟶ B` through `B|πB⁻¹Q ⟶ B`. -/
def restrictOver : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ Q) ⟶
    B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ Q) :=
  Hom.liftRestrict
      (KLocallyRingedSpace.restrictIncl A (Opens.comap_mono _ hQP) ≫ s ≫ ofRestrict B _) _ fun x
          => by
    change Hom.toFun πB (Hom.toFun s (Hom.toFun (KLocallyRingedSpace.restrictIncl A _) x)).1 ∈ Q
    rw [toFun_π_eq_of_over πA πB s hs]
    exact x.2

/-- The restriction of `s` to the parts over `Q` lies over `s`: followed by the inclusion of
`B|πB⁻¹Q` into `B` it is the inclusion of `A|πA⁻¹Q` into `A|πA⁻¹P` followed by `s` and the inclusion
into `B` (`liftRestrict`'s factorization). -/
@[reassoc]
theorem restrictOver_comp_ofRestrict :
    restrictOver πA πB hQP s hs ≫ ofRestrict B _ =
      KLocallyRingedSpace.restrictIncl A (Opens.comap_mono _ hQP) ≫ s ≫ ofRestrict B _ :=
  Hom.liftRestrict_comp_ofRestrict _ _ _

/-- The restriction of `s` to the parts over `Q`, followed by the inclusion of open subspaces
`B|πB⁻¹Q ⟶ B|πB⁻¹P`, is the inclusion `A|πA⁻¹Q ⟶ A|πA⁻¹P` followed by `s` (both sides agree after
the open immersion into `B`). -/
@[reassoc]
theorem restrictOver_comp_restrictIncl :
    restrictOver πA πB hQP s hs ≫ KLocallyRingedSpace.restrictIncl B (Opens.comap_mono _ hQP) =
      KLocallyRingedSpace.restrictIncl A (Opens.comap_mono _ hQP) ≫ s :=
  Hom.ext_of_comp_ofRestrict (by
    rw
        [Category.assoc, KLocallyRingedSpace.restrictIncl_comp_ofRestrict,
            restrictOver_comp_ofRestrict,
      Category.assoc])

/-- The restriction of a morphism over `Z` is over `Z`. -/
theorem restrictOver_over :
    ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ Q) ≫ πA =
      (restrictOver πA πB hQP s hs ≫
        ofRestrict B (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ Q)) ≫ πB := by
  rw [restrictOver_comp_ofRestrict, Category.assoc, ← hs, ← Category.assoc,
    KLocallyRingedSpace.restrictIncl_comp_ofRestrict]

include hs in
/-- The inverse of an isomorphism over `Z` is over `Z`. -/
theorem inv_over [IsIso s] :
    ofRestrict B (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ P) ≫ πB =
      (inv s ≫ ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ P)) ≫ πA := by
  rw [Category.assoc, hs, Category.assoc, IsIso.inv_hom_id_assoc]

/-- The restrictions of two piecewise inverse morphisms over `Z` are inverse. -/
theorem restrictOver_comp_restrictOver
    (t : B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ P) ⟶
      A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ P))
    (ht : ofRestrict B (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ P) ≫ πB =
      (t ≫ ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ P)) ≫ πA)
    (hst : s ≫ t = 𝟙 _) :
    restrictOver πA πB hQP s hs ≫ restrictOver πB πA hQP t ht = 𝟙 _ :=
  Hom.ext_of_comp_ofRestrict (by
    rw [Category.assoc, restrictOver_comp_ofRestrict, restrictOver_comp_restrictIncl_assoc,
      reassoc_of% hst, KLocallyRingedSpace.restrictIncl_comp_ofRestrict, Category.id_comp])

/-- An isomorphism over `Z` restricts to an isomorphism over `Z`. -/
theorem isIso_restrictOver [IsIso s] : IsIso (restrictOver πA πB hQP s hs) :=
  ⟨⟨restrictOver πB πA hQP (inv s) (inv_over πA πB s hs),
    restrictOver_comp_restrictOver πA πB hQP s hs (inv s) (inv_over πA πB s hs)
      (IsIso.hom_inv_id s),
    restrictOver_comp_restrictOver πB πA hQP (inv s) (inv_over πA πB s hs) s hs
      (IsIso.inv_hom_id s)⟩⟩

end RestrictOver

/-- Uniqueness of the isomorphisms over `Z` from the parts of `A` to the parts of `B` over every
open `O' ≤ O` gives the uniqueness of those from `B` to `A`: the inverses are isomorphisms over `Z`
from `A` to `B`. -/
theorem uniq_symm (O : Opens Z)
    (huniq : ∀ (O' : Opens Z), O' ≤ O →
      ∀ s s' : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O') ⟶
        B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O'),
        IsIso s → IsIso s' → ofRestrict _ _ ≫ πA = (s ≫ ofRestrict _ _) ≫ πB →
        ofRestrict _ _ ≫ πA = (s' ≫ ofRestrict _ _) ≫ πB → s = s')
    (O' : Opens Z) (hO' : O' ≤ O)
    (t t' : B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O') ⟶
      A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O'))
    (ht : IsIso t) (ht' : IsIso t')
    (hto : ofRestrict B (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O') ≫ πB =
      (t ≫ ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O')) ≫ πA)
    (hto' : ofRestrict B (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O') ≫ πB =
      (t' ≫ ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O')) ≫ πA) :
    t = t' :=
  IsIso.inv_eq_inv.mp (huniq O' hO' (inv t) (inv t') inferInstance inferInstance
    (inv_over πB πA t hto) (inv_over πB πA t' hto'))

/-! ### The gluing of the local isomorphisms -/

section Glue

variable (O : Opens Z) {ι : Type*} (N : ι → Opens Z) (hN : ∀ i, N i ≤ O)
  (s : ∀ i, A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ (N i)) ⟶
    B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ (N i)))
  (hs : ∀ i, ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ (N i)) ≫ πA =
    (s i ≫ ofRestrict B (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ (N i))) ≫ πB)
  (hiso : ∀ i, IsIso (s i))

/-- The cover of `A|πA⁻¹O` by the parts over the `N i`. -/
def glueCoverOpens (i : ι) :
    Opens (A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O)) :=
  Opens.comap ⟨Hom.toFun (ofRestrict A _), Hom.continuous_toFun _⟩
    (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ (N i))

/-- A point of `A|πA⁻¹O` lies in the `i`-th member of the cover iff its base point lies in `N i`
(definitional). -/
theorem mem_glueCoverOpens {i : ι}
    {x : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O)} :
    x ∈ glueCoverOpens πA O N i ↔ Hom.toFun πA x.1 ∈ N i :=
  Iff.rfl

/-- The parts over the `N i` cover `A|πA⁻¹O`, since the `N i` cover `O`. -/
theorem glueCoverOpens_cover (hcov : ∀ z ∈ O, ∃ i, z ∈ N i)
    (x : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O)) :
    ∃ i, x ∈ glueCoverOpens πA O N i :=
  hcov _ x.2

/-- The inclusion of a member of the cover into the part of `A` over `N i`. -/
def pieceIncl (i : ι) :
    (A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O)).restrictOpen
        (glueCoverOpens πA O N i) ⟶
      A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ (N i)) :=
  Hom.liftRestrict (ofRestrict _ (glueCoverOpens πA O N i) ≫ ofRestrict A _) _ fun x => x.2

/-- The inclusion of a member of the cover into `A|πA⁻¹(N i)`, followed by the open immersion into
`A`, is the composite of the two open immersions `(A|πA⁻¹O)|_{cover} ⟶ A|πA⁻¹O ⟶ A`
(`liftRestrict`'s factorization). -/
@[reassoc]
theorem pieceIncl_comp_ofRestrict (i : ι) :
    pieceIncl πA O N i ≫ ofRestrict A _ =
      ofRestrict _ (glueCoverOpens πA O N i) ≫
        ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O) :=
  Hom.liftRestrict_comp_ofRestrict _ _ _

/-- The piece of the gluing over `N i`: `s i` on the part over `N i`, followed by the inclusion
into `B|πB⁻¹O`. -/
def gluePiece (i : ι) :
    (A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O)).restrictOpen
        (glueCoverOpens πA O N i) ⟶
      B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O) :=
  Hom.liftRestrict (pieceIncl πA O N i ≫ s i ≫ ofRestrict B _) _ fun x =>
    hN i (Hom.toFun (s i) (Hom.toFun (pieceIncl πA O N i) x)).2

/-- The `i`-th piece of the gluing, followed by the open immersion `B|πB⁻¹O ⟶ B`, is
`pieceIncl i ≫ s i` followed by the open immersion `B|πB⁻¹(N i) ⟶ B` (`liftRestrict`'s
factorization). -/
@[reassoc]
theorem gluePiece_comp_ofRestrict (i : ι) :
    gluePiece πA πB O N hN s i ≫ ofRestrict B _ =
      pieceIncl πA O N i ≫ s i ≫
        ofRestrict B (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ (N i)) :=
  Hom.liftRestrict_comp_ofRestrict _ _ _

include hs hiso in
/-- The pieces agree on the overlaps: both restrictions to the part over `N i ⊓ N j` are
isomorphisms over `Z`, hence equal by the uniqueness hypothesis. -/
theorem gluePiece_compatible
    (huniq : ∀ (O' : Opens Z), O' ≤ O →
      ∀ s s' : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O') ⟶
        B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O'),
        IsIso s → IsIso s' → ofRestrict _ _ ≫ πA = (s ≫ ofRestrict _ _) ≫ πB →
        ofRestrict _ _ ≫ πA = (s' ≫ ofRestrict _ _) ≫ πB → s = s') :
    KLocallyRingedSpace.GlueCompatible (glueCoverOpens πA O N) (gluePiece πA πB O N hN s) := by
  intro i j
  -- the inclusion of the overlap into the part of `A` over `N i ⊓ N j`
  let c : (A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O)).restrictOpen
      (glueCoverOpens πA O N i ⊓ glueCoverOpens πA O N j) ⟶
      A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ (N i ⊓ N j)) :=
    Hom.liftRestrict (ofRestrict _ _ ≫ ofRestrict A _) _ fun x => ⟨x.2.1, x.2.2⟩
  have hc : c ≫ ofRestrict A _ = ofRestrict _ _ ≫
      ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O) :=
    Hom.liftRestrict_comp_ofRestrict _ _ _
  have hi :
      KLocallyRingedSpace.restrictIncl _
          (inf_le_left : glueCoverOpens πA O N i ⊓ glueCoverOpens πA O N j ≤ _) ≫
      pieceIncl πA O N i = c ≫
          KLocallyRingedSpace.restrictIncl A (Opens.comap_mono _ inf_le_left) :=
    Hom.ext_of_comp_ofRestrict (by
      rw
          [Category.assoc, pieceIncl_comp_ofRestrict, Category.assoc,
              KLocallyRingedSpace.restrictIncl_comp_ofRestrict,
        hc, ← Category.assoc, KLocallyRingedSpace.restrictIncl_comp_ofRestrict])
  have hj :
      KLocallyRingedSpace.restrictIncl _
          (inf_le_right : glueCoverOpens πA O N i ⊓ glueCoverOpens πA O N j ≤ _) ≫
      pieceIncl πA O N j = c ≫
          KLocallyRingedSpace.restrictIncl A (Opens.comap_mono _ inf_le_right) :=
    Hom.ext_of_comp_ofRestrict (by
      rw
          [Category.assoc, pieceIncl_comp_ofRestrict, Category.assoc,
              KLocallyRingedSpace.restrictIncl_comp_ofRestrict,
        hc, ← Category.assoc, KLocallyRingedSpace.restrictIncl_comp_ofRestrict])
  have := hiso i
  have := hiso j
  have heq := huniq (N i ⊓ N j) (inf_le_of_left_le (hN i))
    (restrictOver πA πB inf_le_left (s i) (hs i)) (restrictOver πA πB inf_le_right (s j) (hs j))
    (isIso_restrictOver πA πB inf_le_left (s i) (hs i))
    (isIso_restrictOver πA πB inf_le_right (s j) (hs j))
    (restrictOver_over πA πB inf_le_left (s i) (hs i))
    (restrictOver_over πA πB inf_le_right (s j) (hs j))
  have e1 :
      (KLocallyRingedSpace.restrictIncl _
          (inf_le_left : glueCoverOpens πA O N i ⊓ glueCoverOpens πA O N j ≤ _) ≫
      gluePiece πA πB O N hN s i) ≫ ofRestrict B _ =
      c ≫ restrictOver πA πB inf_le_left (s i) (hs i) ≫ ofRestrict B _ := by
    rw [Category.assoc, gluePiece_comp_ofRestrict, reassoc_of% hi, restrictOver_comp_ofRestrict]
  have e2 :
      (KLocallyRingedSpace.restrictIncl _
          (inf_le_right : glueCoverOpens πA O N i ⊓ glueCoverOpens πA O N j ≤ _) ≫
      gluePiece πA πB O N hN s j) ≫ ofRestrict B _ =
      c ≫ restrictOver πA πB inf_le_right (s j) (hs j) ≫ ofRestrict B _ := by
    rw [Category.assoc, gluePiece_comp_ofRestrict, reassoc_of% hj, restrictOver_comp_ofRestrict]
  exact Hom.ext_of_comp_ofRestrict (by rw [e1, e2, heq])

variable (hcov : ∀ z ∈ O, ∃ i, z ∈ N i)
  (huniq : ∀ (O' : Opens Z), O' ≤ O →
    ∀ s s' : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O') ⟶
      B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O'),
      IsIso s → IsIso s' → ofRestrict _ _ ≫ πA = (s ≫ ofRestrict _ _) ≫ πB →
      ofRestrict _ _ ≫ πA = (s' ≫ ofRestrict _ _) ≫ πB → s = s')

/-- The morphism `A|πA⁻¹O ⟶ B|πB⁻¹O` glued from the local isomorphisms `s i` along the cover of
`A|πA⁻¹O` by the parts over the `N i`. -/
def glueIsoPieces :
    A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O) ⟶
      B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O) :=
  KLocallyRingedSpace.glueOfCover (glueCoverOpens πA O N) (gluePiece πA πB O N hN s)
      (glueCoverOpens_cover πA O N hcov)
    (gluePiece_compatible πA πB O N hN s hs hiso huniq)

/-- The glued morphism restricts to the `i`-th piece on the `i`-th member of the cover
(`ofRestrict_comp_glueOfCover`). -/
@[reassoc]
theorem ofRestrict_comp_glueIsoPieces (i : ι) :
    ofRestrict _ (glueCoverOpens πA O N i) ≫ glueIsoPieces πA πB O N hN s hs hiso hcov huniq =
      gluePiece πA πB O N hN s i :=
  KLocallyRingedSpace.ofRestrict_comp_glueOfCover _ _ _ _ i

/-- The glued morphism lies over `Z`. -/
theorem glueIsoPieces_over :
    ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O) ≫ πA =
      (glueIsoPieces πA πB O N hN s hs hiso hcov huniq ≫
        ofRestrict B (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O)) ≫ πB := by
  apply hom_ext_of_cover _ _ (glueCoverOpens πA O N) (glueCoverOpens_cover πA O N hcov)
  intro i
  have hs' : s i ≫ ofRestrict B (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ (N i)) ≫
      πB = ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ (N i)) ≫ πA := by
    rw [← Category.assoc]; exact (hs i).symm
  simp only [Category.assoc, ofRestrict_comp_glueIsoPieces_assoc, gluePiece_comp_ofRestrict_assoc,
    hs', pieceIncl_comp_ofRestrict_assoc]

/-- The assemblies of two piecewise inverse families of isomorphisms over `Z` are inverse. -/
theorem glueIsoPieces_comp_glueIsoPieces
    (t : ∀ i, B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ (N i)) ⟶
      A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ (N i)))
    (ht : ∀ i, ofRestrict B (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ (N i)) ≫ πB =
      (t i ≫ ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ (N i))) ≫ πA)
    (htiso : ∀ i, IsIso (t i))
    (huniqB : ∀ (O' : Opens Z), O' ≤ O →
      ∀ s s' : B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O') ⟶
        A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O'),
        IsIso s → IsIso s' → ofRestrict _ _ ≫ πB = (s ≫ ofRestrict _ _) ≫ πA →
        ofRestrict _ _ ≫ πB = (s' ≫ ofRestrict _ _) ≫ πA → s = s')
    (hst : ∀ i, s i ≫ t i = 𝟙 _) :
    glueIsoPieces πA πB O N hN s hs hiso hcov huniq ≫
      glueIsoPieces πB πA O N hN t ht htiso hcov huniqB = 𝟙 _ := by
  apply hom_ext_of_cover _ _ (glueCoverOpens πA O N) (glueCoverOpens_cover πA O N hcov)
  intro i
  -- the piece of the first gluing lands in the member of the cover of `B|πB⁻¹O` over `N i`
  let g : (A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O)).restrictOpen
      (glueCoverOpens πA O N i) ⟶
      (B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O)).restrictOpen
        (glueCoverOpens πB O N i) :=
    Hom.liftRestrict (gluePiece πA πB O N hN s i) _ fun x => by
      have h := congrArg (fun φ => Hom.toFun φ x) (gluePiece_comp_ofRestrict πA πB O N hN s i)
      change (Hom.toFun (gluePiece πA πB O N hN s i) x).1 =
        (Hom.toFun (s i) (Hom.toFun (pieceIncl πA O N i) x)).1 at h
      change Hom.toFun πB (Hom.toFun (gluePiece πA πB O N hN s i) x).1 ∈ N i
      rw [h]
      exact (Hom.toFun (s i) (Hom.toFun (pieceIncl πA O N i) x)).2
  have hg : g ≫ ofRestrict _ (glueCoverOpens πB O N i) = gluePiece πA πB O N hN s i :=
    Hom.liftRestrict_comp_ofRestrict _ _ _
  have hgp : g ≫ pieceIncl πB O N i = pieceIncl πA O N i ≫ s i :=
    Hom.ext_of_comp_ofRestrict (by
      rw [Category.assoc, pieceIncl_comp_ofRestrict, ← Category.assoc, hg,
        gluePiece_comp_ofRestrict, Category.assoc])
  rw [Category.comp_id, ← Category.assoc, ofRestrict_comp_glueIsoPieces, ← hg, Category.assoc,
    ofRestrict_comp_glueIsoPieces]
  apply Hom.ext_of_comp_ofRestrict
  rw [Category.assoc, gluePiece_comp_ofRestrict, ← Category.assoc, hgp, Category.assoc,
    reassoc_of% (hst i), pieceIncl_comp_ofRestrict]

end Glue

/-- **Isomorphisms over `Z` glue along an open cover of the base**: isomorphisms over `Z` between
the parts of `A` and `B` over the members of an open cover of an open subset `O ⊆ Z`, unique among
such on every open subset of `O`, glue to an isomorphism over `Z` between the parts over `O`
(`glueOfCover` on the cover pulled back to `A`, `hom_ext_of_cover`). -/
theorem exists_isIso_over_of_cover (O : Opens Z) {ι : Type*} (N : ι → Opens Z)
    (_hN : ∀ i, N i ≤ O) (_hcov : ∀ z ∈ O, ∃ i, z ∈ N i)
    (_hloc : ∀ i, ∃ s : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ (N i)) ⟶
        B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ (N i)),
      IsIso s ∧ ofRestrict _ _ ≫ πA = (s ≫ ofRestrict _ _) ≫ πB)
    (_huniq : ∀ (O' : Opens Z), O' ≤ O →
      ∀ s s' : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O') ⟶
        B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O'),
        IsIso s → IsIso s' → ofRestrict _ _ ≫ πA = (s ≫ ofRestrict _ _) ≫ πB →
        ofRestrict _ _ ≫ πA = (s' ≫ ofRestrict _ _) ≫ πB → s = s') :
    ∃ s : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O) ⟶
        B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O),
      IsIso s ∧ ofRestrict _ _ ≫ πA = (s ≫ ofRestrict _ _) ≫ πB := by
  choose s hsiso hs using _hloc
  have huniqB := uniq_symm πA πB O _huniq
  refine ⟨glueIsoPieces πA πB O N _hN s hs hsiso _hcov _huniq, ?_,
    glueIsoPieces_over πA πB O N _hN s hs hsiso _hcov _huniq⟩
  let t : ∀ i, B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ (N i)) ⟶
      A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ (N i)) :=
    fun i => @inv _ _ _ _ (s i) (hsiso i)
  have ht : ∀ i, ofRestrict B (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ (N i)) ≫ πB =
      (t i ≫ ofRestrict A (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ (N i))) ≫ πA :=
    fun i => by have := hsiso i; exact inv_over πA πB (s i) (hs i)
  have hinv : ∀ i, IsIso (t i) := fun i => by have := hsiso i; exact inferInstance
  exact ⟨⟨glueIsoPieces πB πA O N _hN t ht hinv _hcov huniqB,
    glueIsoPieces_comp_glueIsoPieces πA πB O N _hN s hs hsiso _hcov _huniq t ht hinv huniqB
      (fun i => by have := hsiso i; exact IsIso.hom_inv_id (s i)),
    glueIsoPieces_comp_glueIsoPieces πB πA O N _hN t ht hinv _hcov huniqB s hs hsiso _huniq
      (fun i => by have := hsiso i; exact IsIso.inv_hom_id (s i))⟩⟩

end AnalyticSpace.KLocallyRingedSpace

end
