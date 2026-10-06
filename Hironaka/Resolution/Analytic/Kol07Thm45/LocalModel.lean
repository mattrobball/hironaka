/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueProof
public import Hironaka.Resolution.Analytic.Kol07Thm45.Resolution
import Hironaka.AnalyticSpace.Glue.OverPart
import Hironaka.AnalyticSpace.IsoOverOpen
import Hironaka.AnalyticSpace.RestrictOverLemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueIndep
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrict
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceTransitionGlue
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The local model of the glued resolution, and its automorphisms over `X`

Włodarczyk's independence of the canonical desingularization from the ambient manifold
[Wlo09, §4, (3)⇒(4)] and Kollár's uniqueness of the comparison [Kol07, Theorem 36, proof], read on
the glued spaces: the part of `resolutionOn D` over an open `P` inside a piece's base open is that
piece's local resolution over `P` (the chosen gluing's `partIso`); **the local model** — at a
point `x` of the base open of ANY piece embedding `E` over `W`, the part of the glued space `R(X)`
(an exhaustion gluing) over a small open `P ∋ x` is the part of `E`'s local resolution over `P`,
over `X` (the exhaustion glue's `partIso`, the first item, and the mixed local transition
`exists_localTransition_pair` under the independence `hind`); **`R(X)` has no non-trivial
automorphism over `X` on any part** (the assembly `exists_isoOver_of_localTransitions` for the
exhaustion glue against itself); and, in any category of spaces over `Z`, the absence of
automorphisms makes the isomorphisms over `Z` to any other space unique.

**Why.** The functoriality of the resolution for isomorphisms of open subspaces
(`ResolutionFunctorial.lean`) glues local isomorphisms over `X` between `R(X)` and `R(Y)|V` (viewed
over `X` through `φ⁻¹`) along a cover of `U`, by `exists_isIso_over_of_cover`; the local
isomorphisms come from the local models of both sides at the same local resolution (the transport
`transportAlongIso`), and the uniqueness hypothesis from the last two items.

Not in the sources beyond the remarks cited; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace

universe u

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- If the parts of `A` over `O` have no non-trivial automorphism over `Z`, the isomorphisms over
`Z` from the parts of `A` to the parts of `B` over `O` are unique: `s' ≫ s⁻¹` is an automorphism
over `Z` (`inv_over`), hence the identity. -/
theorem isoOver_unique_of_aut {A B Z : KLocallyRingedSpace.{u} K} (πA : A ⟶ Z) (πB : B ⟶ Z)
    (O : Opens Z)
    (haut : ∀ t : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O) ⟶
        A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O),
      IsIso t → ofRestrict _ _ ≫ πA = (t ≫ ofRestrict _ _) ≫ πA → t = 𝟙 _)
    (s s' : A.restrictOpen (Opens.comap ⟨Hom.toFun πA, Hom.continuous_toFun πA⟩ O) ⟶
      B.restrictOpen (Opens.comap ⟨Hom.toFun πB, Hom.continuous_toFun πB⟩ O))
    (hs : IsIso s) (hs' : IsIso s')
    (hc : ofRestrict _ _ ≫ πA = (s ≫ ofRestrict _ _) ≫ πB)
    (hc' : ofRestrict _ _ ≫ πA = (s' ≫ ofRestrict _ _) ≫ πB) : s = s' := by
  have hinv : ofRestrict _ _ ≫ πB = (inv s ≫ ofRestrict _ _) ≫ πA := inv_over πA πB s hc
  have ht : ofRestrict _ _ ≫ πA = ((s' ≫ inv s) ≫ ofRestrict _ _) ≫ πA := by
    rw [hc', Category.assoc, hinv]
    simp only [Category.assoc]
  have h := haut (s' ≫ inv s) inferInstance ht
  exact ((IsIso.comp_inv_eq s).mp h).trans (Category.id_comp s) |>.symm

end AnalyticSpace.KLocallyRingedSpace

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}

/-- **The part of `resolutionOn D` over an open `P ⊆ U` inside a piece's base open is the part of
that piece's local resolution**, over `X` ([Wlo09, §4, (3)⇒(4)]):
`resolutionOn D = Ṽ_D|Π⁻¹U` read into the full glued space
(`exists_iso_restrictOpen_restrictOpen_comap`), the pair unfolded to the chosen gluing
(`resolutionOnFullPair_eq_of_glues`), and its `partIso` at `P ≤ pieceDom i (W i)`. -/
theorem exists_isoOver_resolutionOn_localResolution (D : LocalEmbeddingData 𝕜 X U)
    (bed : BEDanFamStar.{u} 𝕜) (h : D.ResolutionGluesOn bed) (i : D.ι) (P : Opens X)
    (hPU : (P : Set X) ⊆ U) (hPi : P ≤ D.pieceDom i (h.some.W i)) :
    ∃ s : (D.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
            Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ⟶
        ((D.embedding i).localResolution bed (h.some.W i)
            (h.some.isCompact_closure_W i)).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
              (h.some.isCompact_closure_W i)),
            Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
              (h.some.isCompact_closure_W i))⟩ P),
      IsIso s ∧
        ofRestrict _ _ ≫ D.resolutionOnToSpace bed =
          (s ≫ ofRestrict _ _) ≫
            (D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i) := by
  -- the part of the restriction `Ṽ_D|Π⁻¹U` over `P` is the part of `Ṽ_D` over `P`
  obtain ⟨e, he, hec⟩ := exists_iso_restrictOpen_restrictOpen_comap
    (D.resolutionOnFullMap bed : (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
      X.toKLocallyRingedSpace)
    (openOf (D.resolutionOnFull bed)
      (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))
    (openOf X U)
    (Hom.mapsTo_openOf (D.resolutionOnFullMap bed) U) P
    (fun a ha => mem_openOf_of_subset Set.Subset.rfl (hPU ha))
  -- the part of the full glued space over `P` is the part of the piece: the pair unfolded
  suffices key : ∀ p : Σ R :
      AnalyticSpace.{u} 𝕜, (R ⟶ X),
      p = D.resolutionOnFullPair bed →
      ∃ t : p.1.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun p.2, Hom.continuous_toFun p.2⟩ P) ⟶
          ((D.embedding i).localResolution bed (h.some.W i)
              (h.some.isCompact_closure_W i)).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i)),
              Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
                (h.some.isCompact_closure_W i))⟩ P),
        IsIso t ∧
          ofRestrict _ _ ≫ p.2 = (t ≫ ofRestrict _ _) ≫
            (D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i) by
    obtain ⟨t, ht, htc⟩ := key _ rfl
    refine ⟨e ≫ t, @IsIso.comp_isIso _ _ _ _ _ _ _ he ht, ?_⟩
    exact hec.trans ((Category.assoc _ _ _).trans
      ((congrArg (fun k => e ≫ k) htc).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ (D.embedding i).toSpaceMap bed (h.some.W i)
            (h.some.isCompact_closure_W i)) (Category.assoc _ _ _).symm))))
  intro p hp
  rw [D.resolutionOnFullPair_eq_of_glues bed h] at hp
  subst hp
  refine ⟨(h.some.glue.partIso i P hPi).inv, Iso.isIso_inv _, ?_⟩
  exact (h.some.glue.partIso_inv_comp_over i P hPi).symm.trans (Category.assoc _ _ _).symm

end Hironaka.Manifold.LocalEmbeddingData

namespace Hironaka.Manifold.BEDanFamStar

variable {𝕜 : Type} [RCLike 𝕜] (bed : BEDanFamStar.{u} 𝕜)
  (X : AnalyticSpace.{u} 𝕜)

/-- **The local model of the glued resolution** ([Wlo09, §4, (3)⇒(4)]; [Kol07, Theorem 36, proof];
with the independence of the local resolution as `hind`): at a point `x` of the base open of ANY
piece embedding `E` over `W`, the part of the glued space over a small open `P ∋ x` is the part of
`E`'s local resolution over `P`, over `X` — the exhaustion glue's `partIso` at `Uₙ ∋ x`,
`exists_isoOver_resolutionOn_localResolution` for the datum `Dₙ` at a piece containing `x`, and the
mixed local transition `exists_localTransition_pair` between that piece's embedding and `E`. -/
theorem ExhaustionGluing.exists_localModel (Ξ : bed.ExhaustionGluing X)
    (hbed : bed.IsEmbeddedDesing) (hind : LocalResolutionIndependentOn X bed) {n : ℕ} {O : Set X}
    (E : PieceEmbedding 𝕜 n X O) (hO : IsOpen O) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) (x : X) (hx : x ∈ E.domOpens W) :
    ∃ (P : Opens X) (_ : x ∈ P) (_ : P ≤ E.domOpens W),
      ∃ s : Ξ.glue.gluedOver.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap,
                Hom.continuous_toFun Ξ.glue.descMap⟩ P) ⟶
          (E.localResolution bed W hW).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (E.toSpaceMap bed W hW),
              Hom.continuous_toFun (E.toSpaceMap bed W hW)⟩ P),
        IsIso s ∧
          ofRestrict _ _ ≫ Ξ.glue.descMap = (s ≫ ofRestrict _ _) ≫ E.toSpaceMap bed W hW := by
  -- the exhaustion member and the piece containing `x`
  obtain ⟨m, hxm⟩ : ∃ m, x ∈ Ξ.U m :=
    Set.mem_iUnion.mp ((Set.ext_iff.mp Ξ.iUnion_U x).mpr (Set.mem_univ x))
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ (Ξ.D m).inner i := Set.mem_iUnion.mp ((Ξ.D m).subset_iUnion_inner hxm)
  have hxdom : x ∈ (Ξ.D m).pieceDom i ((Ξ.glues m).some.W i) :=
    (Ξ.glues m).some.closure_inner_subset_pieceDom i (subset_closure hxi)
  -- the mixed local transition between the piece's embedding and `E`
  obtain ⟨P, hxP, hPO', θ, hθ, hθc, -⟩ := ((Ξ.D m).embedding i).exists_localTransition_pair E
    ((Ξ.D m).isOpen_piece i) hO bed hbed hind ((Ξ.glues m).some.W i)
    ((Ξ.glues m).some.isCompact_closure_W i) W hW
    (Ξ.U m ⊓ ((Ξ.D m).pieceDom i ((Ξ.glues m).some.W i) ⊓ E.domOpens W)) inf_le_right
    ((Opens.mem_inf).mpr ⟨hxm, (Opens.mem_inf).mpr ⟨hxdom, hx⟩⟩)
  have hPU : P ≤ Ξ.U m := fun z hz => ((Opens.mem_inf).mp (hPO' hz)).1
  have hPi : P ≤ (Ξ.D m).pieceDom i ((Ξ.glues m).some.W i) :=
    fun z hz => ((Opens.mem_inf).mp ((Opens.mem_inf).mp (hPO' hz)).2).1
  -- the part of `resolutionOn Dₘ` at the piece, and the exhaustion glue's `partIso` at `P ≤ Uₘ`
  obtain ⟨s₁, hs₁, hs₁c⟩ := (Ξ.D m).exists_isoOver_resolutionOn_localResolution bed (Ξ.glues m)
    i P hPU hPi
  refine ⟨P, hxP, fun z hz => ((Opens.mem_inf).mp ((Opens.mem_inf).mp (hPO' hz)).2).2,
    (Ξ.glue.partIso ⟨m⟩ P hPU).inv ≫ s₁ ≫ θ,
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _) (@IsIso.comp_isIso _ _ _ _ _ _ _ hs₁ hθ),
    ?_⟩
  exact over_comp₃ (Ξ.glue.partIso ⟨m⟩ P hPU).inv s₁ θ _ _ _ _ _ _ _ _
    ((Ξ.glue.partIso_inv_comp_over ⟨m⟩ P hPU).symm.trans (Category.assoc _ _ _).symm) hs₁c hθc

/-- **The glued space has no non-trivial automorphism over `X` on any part** (Kollár's uniqueness,
[Kol07, Theorem 36, proof]; with the independence as `hind`): an isomorphism over `X` from the part
over `O` to itself is the identity — the assembly `exists_isoOver_of_localTransitions` for the
exhaustion glue against ITSELF, whose local transitions are the unique ones of
`exists_isoOver_resolutionOn (D n) (D n)` on `O' ⊓ Uₙ`; its uniqueness clause applied to `t` and
to `𝟙`. -/
theorem ExhaustionGluing.isoOver_eq_id (Ξ : bed.ExhaustionGluing X) (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) (O : Opens X)
    (t : Ξ.glue.gluedOver.toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap,
              Hom.continuous_toFun Ξ.glue.descMap⟩ O) ⟶
        Ξ.glue.gluedOver.toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun Ξ.glue.descMap,
              Hom.continuous_toFun Ξ.glue.descMap⟩ O))
    (ht : IsIso t)
    (hc : ofRestrict _ _ ≫ Ξ.glue.descMap = (t ≫ ofRestrict _ _) ≫ Ξ.glue.descMap) : t = 𝟙 _ := by
  obtain ⟨s, -, -, huniq⟩ := GlueOver.exists_isoOver_of_localTransitions Ξ.glue Ξ.glue O
    fun O' _ z hz => by
      obtain ⟨m, hzm⟩ : ∃ m, z ∈ Ξ.U m :=
        Set.mem_iUnion.mp ((Set.ext_iff.mp Ξ.iUnion_U z).mpr (Set.mem_univ z))
      obtain ⟨θ, hθ, hθc, hθu⟩ := (Ξ.D m).exists_isoOver_resolutionOn (Ξ.D m) bed hbed hind
        (O' ⊓ Ξ.U m) (fun y hy => ⟨((Opens.mem_inf).mp hy).2, ((Opens.mem_inf).mp hy).2⟩)
      exact ⟨⟨m⟩, ⟨m⟩, O' ⊓ Ξ.U m, (Opens.mem_inf).mpr ⟨hz, hzm⟩, inf_le_left, inf_le_right,
        inf_le_right, θ, hθ, hθc, hθu⟩
  exact (huniq t ht hc).trans (huniq (𝟙 _) inferInstance
    (congrArg (fun k => k ≫ Ξ.glue.descMap) (Category.id_comp _).symm)).symm

end Hironaka.Manifold.BEDanFamStar

end
