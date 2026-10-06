/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.Resolution
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueProof
import Hironaka.AnalyticSpace.Exhaustion
import Hironaka.AnalyticSpace.Glue.OverLemmas
import Hironaka.AnalyticSpace.Glue.OverPart
import Hironaka.AnalyticSpace.HomLocal
import Hironaka.AnalyticSpace.IsoOverOpen
import Hironaka.AnalyticSpace.RestrictOverLemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueDatum
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceModelPad
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceTransition
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceTransitionGlue
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The independence of the gluing from the data, and the exhaustion gluing

Włodarczyk: the canonical desingularization `Ỹ_Z → Y_Z` is independent of the choice of ambient
manifold, and an open embedding of germs induces an open embedding of the desingularizations
[Wlo09, §4, (3)⇒(4)]; Kollár: the local resolutions agree by the uniqueness of the comparison
[Kol07, Theorem 36, proof] — applied piecewise on the common refinement of two local embedding
data `D` (over `U`) and `D'` (over `U'`). The gluing along an exhaustion is Włodarczyk's
[Wlo09, §4.3] and Kollár's passage from neighbourhoods of compact sets to an increasing union of
compact subsets [Kol07, 44].

* `GlueOver.exists_localTransition_glued`, `GlueOver.exists_isoOver_of_localTransitions` (general,
  on two gluing data over the same base): local transitions between the pieces of two gluing data,
  each UNIQUE among the isomorphisms over `X` on its cover member, read into the glued spaces by
  `partIso` and glued by `exists_isIso_over_of_cover` — the uniqueness on every sub-open by
  `hom_ext_of_cover` and `uniq_of_conj`.
* `LocalEmbeddingData.exists_isoOver_resolutionOnFull`: for an open `O ⊆ U ∩ U'` the parts of the
  two glued spaces over `O` are isomorphic over `X` by a UNIQUE isomorphism — the mixed local
  transitions `exists_localTransition_pair` (the independence of the local resolution as `hind`)
  at the pieces `i` of `D`, `i'` of `D'` through `z`.
* `exists_isoOver_resolutionOn`: the same on the spaces `resolutionOn`, over `X` through
  `resolutionOnToSpace` (`exists_iso_restrictOpen_restrictOpen_comap`).
* `resolutionOn_indep_of_independent`: the independence of the glued resolution from the data,
  with `hind` — the core at `O := U` read into `restrictSet`/`Hom.restrictSet`.
* `BEDanFamStar.resolutionGlues_of_isEmbeddedDesing_of_independent`: the gluing along an
  exhaustion — the exhaustion, local embedding data over each member, the gluing data, and the
  gluing along the exhaustion from `GlueOver.exists_glueOver_of_transitions` with the transitions
  and the uniqueness of `exists_isoOver_resolutionOn`. The forms without `hind` are
  `resolutionOn_indep` and `resolutionGlues_of_isEmbeddedDesing` (`GluingProperties.lean`).

Not in the sources beyond the remarks cited; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace

universe u

namespace AnalyticSpace.GlueOver

variable {K : Type} [RCLike K] {X : AnalyticSpace.{u} K} {ι : Type u}
  {R : ι → AnalyticSpace.{u} K} {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace}
  {dom : ι → Opens X} (G : GlueOver X R π dom) [Countable ι]
  {ι' : Type u} {R' : ι' → AnalyticSpace.{u} K}
  {π' : ∀ i', (R' i').toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace} {dom' : ι' → Opens X}
  (G' : GlueOver X R' π' dom') [Countable ι']

/-- **A local transition between a piece of `G` and a piece of `G'` over `P`, unique among the
isomorphisms over `X`, read into the glued spaces**: conjugation by the identifications `partIso`
of the parts over `P` preserves isomorphism, "over `X`" (`over_of_conj_inv_hom`) and uniqueness
(`uniq_of_conj`). -/
theorem exists_localTransition_glued (i : ι) (i' : ι') (P : Opens X) (hPi : P ≤ dom i)
    (hPi' : P ≤ dom' i')
    (θ : (R i).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ P) ⟶
      (R' i').toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π' i'), Hom.continuous_toFun (π' i')⟩ P))
    (hθ : IsIso θ) (hθc : ofRestrict _ _ ≫ π i = (θ ≫ ofRestrict _ _) ≫ π' i')
    (hθu : ∀ s : (R i).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ P) ⟶
      (R' i').toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π' i'), Hom.continuous_toFun (π' i')⟩ P),
      IsIso s → ofRestrict _ _ ≫ π i = (s ≫ ofRestrict _ _) ≫ π' i' → s = θ) :
    ∃ σ : G.gluedOver.toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G.descMap,
              Hom.continuous_toFun G.descMap⟩ P) ⟶
        G'.gluedOver.toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G'.descMap,
              Hom.continuous_toFun G'.descMap⟩ P),
      IsIso σ ∧ ofRestrict _ _ ≫ G.descMap = (σ ≫ ofRestrict _ _) ≫ G'.descMap ∧
        ∀ s : G.gluedOver.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G.descMap,
                Hom.continuous_toFun G.descMap⟩ P) ⟶
          G'.gluedOver.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G'.descMap,
                Hom.continuous_toFun G'.descMap⟩ P),
          IsIso s → ofRestrict _ _ ≫ G.descMap = (s ≫ ofRestrict _ _) ≫ G'.descMap → s = σ := by
  have hσiso : IsIso ((G.partIso i P hPi).inv ≫ θ ≫ (G'.partIso i' P hPi').hom) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ hθ (Iso.isIso_hom _))
  have hσc : ofRestrict _ _ ≫ G.descMap =
      (((G.partIso i P hPi).inv ≫ θ ≫ (G'.partIso i' P hPi').hom) ≫ ofRestrict _ _) ≫
        G'.descMap :=
    (over_of_conj_inv_hom (G.partIso i P hPi) (G'.partIso i' P hPi') (ofRestrict _ _ ≫ π i)
      (ofRestrict _ _ ≫ G.descMap) (ofRestrict _ _ ≫ π' i') (ofRestrict _ _ ≫ G'.descMap)
      (G.partIso_inv_comp_over i P hPi)
      ((Category.assoc _ _ _).symm.trans (G'.partIso_over i' P hPi').symm) θ
      (hθc.trans (Category.assoc _ _ _))).trans (Category.assoc _ _ _).symm
  refine ⟨(G.partIso i P hPi).inv ≫ θ ≫ (G'.partIso i' P hPi').hom, hσiso, hσc, fun s hs hsc => ?_⟩
  exact uniq_of_conj (ofRestrict _ _ ≫ G.descMap) (ofRestrict _ _ ≫ π i)
    (ofRestrict _ _ ≫ G'.descMap) (ofRestrict _ _ ≫ π' i') (G.partIso i P hPi).symm
    (G'.partIso i' P hPi').symm (G.partIso_inv_comp_over i P hPi)
    (G'.partIso_inv_comp_over i' P hPi')
    (fun t t' ht ht' hc hc' =>
      (hθu t ht (hc.symm.trans (Category.assoc _ _ _).symm)).trans
        (hθu t' ht' (hc'.symm.trans (Category.assoc _ _ _).symm)).symm)
    s _ hs hσiso (hsc.trans (Category.assoc _ _ _)).symm (hσc.trans (Category.assoc _ _ _)).symm

/-- **Two gluing data over `X` whose pieces carry unique local transitions on a cover of every
sub-open of `O` have isomorphic parts over `O`, uniquely over `X`**: `exists_isIso_over_of_cover`
on the cover of `O` by the members, the local transitions read into the glued spaces
(`exists_localTransition_glued`); the uniqueness on a sub-open `O'` by `hom_ext_of_cover` on its
members (every isomorphism over `X` restricts to the unique local one). -/
theorem exists_isoOver_of_localTransitions (O : Opens X)
    (hloc : ∀ O' : Opens X, O' ≤ O → ∀ z ∈ O',
      ∃ (i : ι) (i' : ι') (P : Opens X) (_ : z ∈ P) (_ : P ≤ O') (_ : P ≤ dom i)
        (_ : P ≤ dom' i'),
        ∃ θ : (R i).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ P) ⟶
          (R' i').toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π' i'), Hom.continuous_toFun (π' i')⟩ P),
          IsIso θ ∧ ofRestrict _ _ ≫ π i = (θ ≫ ofRestrict _ _) ≫ π' i' ∧
            ∀ s : (R i).toKLocallyRingedSpace.restrictOpen
                (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ P) ⟶
              (R' i').toKLocallyRingedSpace.restrictOpen
                (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π' i'), Hom.continuous_toFun
                    (π' i')⟩ P),
              IsIso s → ofRestrict _ _ ≫ π i = (s ≫ ofRestrict _ _) ≫ π' i' → s = θ) :
    ∃ s : G.gluedOver.toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G.descMap,
              Hom.continuous_toFun G.descMap⟩ O) ⟶
        G'.gluedOver.toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G'.descMap,
              Hom.continuous_toFun G'.descMap⟩ O),
      IsIso s ∧ ofRestrict _ _ ≫ G.descMap = (s ≫ ofRestrict _ _) ≫ G'.descMap ∧
        ∀ s' : G.gluedOver.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G.descMap,
                Hom.continuous_toFun G.descMap⟩ O) ⟶
          G'.gluedOver.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G'.descMap,
                Hom.continuous_toFun G'.descMap⟩ O),
          IsIso s' → ofRestrict _ _ ≫ G.descMap = (s' ≫ ofRestrict _ _) ≫ G'.descMap → s' = s := by
  -- the glued local transitions on every sub-open
  have hglued : ∀ O' : Opens X, O' ≤ O → ∀ z ∈ O', ∃ (P : Opens X) (_ : z ∈ P) (_ : P ≤ O'),
      ∃ σ : G.gluedOver.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G.descMap,
                Hom.continuous_toFun G.descMap⟩ P) ⟶
          G'.gluedOver.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G'.descMap,
                Hom.continuous_toFun G'.descMap⟩ P),
        IsIso σ ∧ ofRestrict _ _ ≫ G.descMap = (σ ≫ ofRestrict _ _) ≫ G'.descMap ∧
          ∀ s : G.gluedOver.toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G.descMap,
                  Hom.continuous_toFun G.descMap⟩ P) ⟶
            G'.gluedOver.toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G'.descMap,
                  Hom.continuous_toFun G'.descMap⟩ P),
            IsIso s → ofRestrict _ _ ≫ G.descMap = (s ≫ ofRestrict _ _) ≫ G'.descMap → s = σ := by
    intro O' hO' z hz
    obtain ⟨i, i', P, hzP, hPO', hPi, hPi', θ, hθ, hθc, hθu⟩ := hloc O' hO' z hz
    exact ⟨P, hzP, hPO', G.exists_localTransition_glued G' i i' P hPi hPi' θ hθ hθc hθu⟩
  -- the uniqueness over every sub-open: two isomorphisms over `X` restrict to the unique local
  -- transition on every member of the cover, and morphisms agreeing on a cover agree
  have huniq : ∀ O' : Opens X, O' ≤ O →
      ∀ s s' : G.gluedOver.toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G.descMap,
              Hom.continuous_toFun G.descMap⟩ O') ⟶
        G'.gluedOver.toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G'.descMap,
              Hom.continuous_toFun G'.descMap⟩ O'),
        IsIso s → IsIso s' → ofRestrict _ _ ≫ G.descMap = (s ≫ ofRestrict _ _) ≫ G'.descMap →
          ofRestrict _ _ ≫ G.descMap = (s' ≫ ofRestrict _ _) ≫ G'.descMap → s = s' := by
    intro O' hO' s s' hs hs' hc hc'
    have hloc' : ∀ z ∈ O', ∃ (P : Opens X) (_ : z ∈ P) (hPO' : P ≤ O'),
        restrictOver G.descMap G'.descMap hPO' s hc =
          restrictOver G.descMap G'.descMap hPO' s' hc' := by
      intro z hz
      obtain ⟨P, hzP, hPO', σ, -, -, hσu⟩ := hglued O' hO' z hz
      refine ⟨P, hzP, hPO', ?_⟩
      exact (hσu _ (@isIso_restrictOver _ _ _ _ _ _ _ _ _ hPO' s hc hs)
          (restrictOver_over _ _ hPO' s hc)).trans
        (hσu _ (@isIso_restrictOver _ _ _ _ _ _ _ _ _ hPO' s' hc' hs')
          (restrictOver_over _ _ hPO' s' hc')).symm
    choose P hzP hPO' hEq using hloc'
    refine hom_ext_of_cover s s'
      (fun z : O' => glueCoverOpens G.descMap O' (fun w : O' => P w.1 w.2) z)
      (fun x => glueCoverOpens_cover _ O' _ (fun w hw => ⟨⟨w, hw⟩, hzP w hw⟩) x) fun z => ?_
    exact CategoryTheory.comp_eq_of_restrict_eq _ _ _ s s' _ _ _
      (pieceIncl_comp_restrictIncl _ O' (fun w : O' => P w.1 w.2) (fun w => hPO' w.1 w.2) z)
      (restrictOver_comp_restrictIncl _ _ (hPO' z.1 z.2) s hc)
      (restrictOver_comp_restrictIncl _ _ (hPO' z.1 z.2) s' hc') (hEq z.1 z.2)
  -- the gluing of local isomorphisms on the cover of `O`
  have hloc0 := fun z (hz : z ∈ O) => hglued O le_rfl z hz
  choose P hzP hPO σ hσ using hloc0
  obtain ⟨s, hs, hsc⟩ := exists_isIso_over_of_cover G.descMap G'.descMap O
    (fun w : O => P w.1 w.2) (fun w => hPO w.1 w.2) (fun z hz => ⟨⟨z, hz⟩, hzP z hz⟩)
    (fun w => ⟨σ w.1 w.2, (hσ w.1 w.2).1, (hσ w.1 w.2).2.1⟩) huniq
  exact ⟨s, hs, hsc, fun s' hs' hsc' => huniq O le_rfl s' s hs' hs hsc' hsc⟩

end AnalyticSpace.GlueOver

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U U' : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (D' : LocalEmbeddingData 𝕜 X U') (bed : BEDanFamStar.{u} 𝕜)

/-- **The mixed local transitions of two gluing data, in the form the assembly wants** (with the
independence of the local resolution as `hind`): for `z` in an open `O' ⊆ U ∩ U'`,
pieces `i` of `D`, `i'` of `D'` with `z` in their base opens (the inner opens cover `U`, their
closures lie in the base opens) and a cover member `P ∋ z`, `P ≤ O'`, inside both base opens,
carrying the unique local transition (`exists_localTransition_pair`). -/
theorem exists_localTransition_of_glues (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) (Gd : D.ResolutionGluing bed)
    (Gd' : D'.ResolutionGluing bed) (O' : Opens X) (hO' : (O' : Set X) ⊆ U ∩ U') {z : X}
    (hz : z ∈ O') :
    ∃ (i : D.ι) (i' : D'.ι) (P : Opens X) (_ : z ∈ P) (_ : P ≤ O')
      (_ : P ≤ D.pieceDom i (Gd.W i)) (_ : P ≤ D'.pieceDom i' (Gd'.W i')),
      ∃ θ : ((D.embedding i).localResolution bed (Gd.W i)
              (Gd.isCompact_closure_W i)).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.pieceToSpace bed i (Gd.W i)
                (Gd.isCompact_closure_W i)),
              Hom.continuous_toFun
                (D.pieceToSpace bed i (Gd.W i) (Gd.isCompact_closure_W i))⟩ P) ⟶
          ((D'.embedding i').localResolution bed (Gd'.W i')
              (Gd'.isCompact_closure_W i')).toKLocallyRingedSpace.restrictOpen
            (Opens.comap
              ⟨KLocallyRingedSpace.Hom.toFun (D'.pieceToSpace bed i' (Gd'.W i')
                  (Gd'.isCompact_closure_W i')),
              Hom.continuous_toFun
                (D'.pieceToSpace bed i' (Gd'.W i') (Gd'.isCompact_closure_W i'))⟩ P),
        IsIso θ ∧
          ofRestrict _ _ ≫ D.pieceToSpace bed i (Gd.W i) (Gd.isCompact_closure_W i) =
            (θ ≫ ofRestrict _ _) ≫ D'.pieceToSpace bed i' (Gd'.W i') (Gd'.isCompact_closure_W i') ∧
          ∀ s : ((D.embedding i).localResolution bed (Gd.W i)
                (Gd.isCompact_closure_W i)).toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.pieceToSpace bed i (Gd.W i)
                  (Gd.isCompact_closure_W i)),
                Hom.continuous_toFun
                  (D.pieceToSpace bed i (Gd.W i) (Gd.isCompact_closure_W i))⟩ P) ⟶
            ((D'.embedding i').localResolution bed (Gd'.W i')
                (Gd'.isCompact_closure_W i')).toKLocallyRingedSpace.restrictOpen
              (Opens.comap
                ⟨KLocallyRingedSpace.Hom.toFun (D'.pieceToSpace bed i' (Gd'.W i')
                    (Gd'.isCompact_closure_W i')),
                Hom.continuous_toFun
                  (D'.pieceToSpace bed i' (Gd'.W i') (Gd'.isCompact_closure_W i'))⟩ P),
            IsIso s →
              ofRestrict _ _ ≫ D.pieceToSpace bed i (Gd.W i) (Gd.isCompact_closure_W i) =
                (s ≫ ofRestrict _ _) ≫
                  D'.pieceToSpace bed i' (Gd'.W i') (Gd'.isCompact_closure_W i') → s = θ := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (D.subset_iUnion_inner (hO' hz).1)
  obtain ⟨i', hi'⟩ := mem_iUnion.mp (D'.subset_iUnion_inner (hO' hz).2)
  have hzi : z ∈ D.pieceDom i (Gd.W i) := Gd.closure_inner_subset_pieceDom i (subset_closure hi)
  have hzi' : z ∈ D'.pieceDom i' (Gd'.W i') :=
    Gd'.closure_inner_subset_pieceDom i' (subset_closure hi')
  obtain ⟨P, hzP, hPO'', θ, hθ⟩ := (D.embedding i).exists_localTransition_pair (D'.embedding i')
    (D.isOpen_piece i) (D'.isOpen_piece i') bed hbed hind (Gd.W i) (Gd.isCompact_closure_W i)
    (Gd'.W i') (Gd'.isCompact_closure_W i')
    (O' ⊓ (D.pieceDom i (Gd.W i) ⊓ D'.pieceDom i' (Gd'.W i'))) inf_le_right
    ((Opens.mem_inf).mpr ⟨hz, (Opens.mem_inf).mpr ⟨hzi, hzi'⟩⟩)
  exact ⟨i, i', P, hzP, hPO''.trans inf_le_left, (hPO''.trans inf_le_right).trans inf_le_left,
    (hPO''.trans inf_le_right).trans inf_le_right, θ, hθ⟩

/-- **The unique isomorphism over `X` between the parts of the two glued spaces over an open
`O ⊆ U ∩ U'`** ([Wlo09, §4, (3)⇒(4)]; [Kol07, Theorem 36, proof]) — the assembly
`exists_isoOver_of_localTransitions` for the two chosen gluing data with the mixed local
transitions `exists_localTransition_of_glues`; the spaces `resolutionOnFull` unfold to the chosen
data's glued spaces (`resolutionOnFullPair_eq_of_glues`). -/
theorem exists_isoOver_resolutionOnFull (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) (O : Opens X) (hO : (O : Set X) ⊆ U ∩ U') :
    ∃ s : (D.resolutionOnFull bed).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
            Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ O) ⟶
        (D'.resolutionOnFull bed).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D'.resolutionOnFullMap bed),
            Hom.continuous_toFun (D'.resolutionOnFullMap bed)⟩ O),
      IsIso s ∧
        ofRestrict _ _ ≫ D.resolutionOnFullMap bed =
          (s ≫ ofRestrict _ _) ≫ D'.resolutionOnFullMap bed ∧
        ∀ s' : (D.resolutionOnFull bed).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
              Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ O) ⟶
          (D'.resolutionOnFull bed).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D'.resolutionOnFullMap bed),
              Hom.continuous_toFun (D'.resolutionOnFullMap bed)⟩ O),
          IsIso s' →
            ofRestrict _ _ ≫ D.resolutionOnFullMap bed =
              (s' ≫ ofRestrict _ _) ≫ D'.resolutionOnFullMap bed → s' = s := by
  have h := D.resolutionGluesOn_of_isEmbeddedDesing_of_independent bed hbed hind
  have h' := D'.resolutionGluesOn_of_isEmbeddedDesing_of_independent bed hbed hind
  suffices key :
      ∀
          (p p' : Σ R :
              AnalyticSpace.{u} 𝕜, (R ⟶ X)),
      p = D.resolutionOnFullPair bed → p' = D'.resolutionOnFullPair bed →
      ∃ s : p.1.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun p.2, Hom.continuous_toFun p.2⟩ O) ⟶
          p'.1.toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun p'.2, Hom.continuous_toFun p'.2⟩ O),
        IsIso s ∧ ofRestrict _ _ ≫ p.2 = (s ≫ ofRestrict _ _) ≫ p'.2 ∧
          ∀ s' : p.1.toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun p.2, Hom.continuous_toFun p.2⟩ O) ⟶
            p'.1.toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun p'.2, Hom.continuous_toFun p'.2⟩ O),
            IsIso s' → ofRestrict _ _ ≫ p.2 = (s' ≫ ofRestrict _ _) ≫ p'.2 → s' = s from
    key _ _ rfl rfl
  intro p p' hp hp'
  rw [D.resolutionOnFullPair_eq_of_glues bed h] at hp
  rw [D'.resolutionOnFullPair_eq_of_glues bed h'] at hp'
  subst hp
  subst hp'
  exact GlueOver.exists_isoOver_of_localTransitions h.some.glue h'.some.glue O
    fun O' hO' z hz =>
      D.exists_localTransition_of_glues D' bed hbed hind h.some h'.some O'
        (fun x hx => hO (hO' hx)) hz

/-- **The same on the spaces `resolutionOn`**, over `X` through `resolutionOnToSpace`: the parts of
`resolutionOn D bed = Ṽ_D|Π⁻¹U` over `O ⊆ U ∩ U'` are
the parts of the full glued spaces (`exists_iso_restrictOpen_restrictOpen_comap`), and the
isomorphism, its compatibility and its uniqueness transport by conjugation. -/
theorem exists_isoOver_resolutionOn (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) (O : Opens X) (hO : (O : Set X) ⊆ U ∩ U') :
    ∃ s : (D.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
            Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ O) ⟶
        (D'.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D'.resolutionOnToSpace bed),
            Hom.continuous_toFun (D'.resolutionOnToSpace bed)⟩ O),
      IsIso s ∧
        ofRestrict _ _ ≫ D.resolutionOnToSpace bed =
          (s ≫ ofRestrict _ _) ≫ D'.resolutionOnToSpace bed ∧
        ∀ s' : (D.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
              Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ O) ⟶
          (D'.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D'.resolutionOnToSpace bed),
              Hom.continuous_toFun (D'.resolutionOnToSpace bed)⟩ O),
          IsIso s' →
            ofRestrict _ _ ≫ D.resolutionOnToSpace bed =
              (s' ≫ ofRestrict _ _) ≫ D'.resolutionOnToSpace bed → s' = s := by
  obtain ⟨t, ht, htc, huniq⟩ := D.exists_isoOver_resolutionOnFull D' bed hbed hind O hO
  obtain ⟨e, he, hec⟩ := exists_iso_restrictOpen_restrictOpen_comap
    (D.resolutionOnFullMap bed : (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶
      X.toKLocallyRingedSpace)
    (openOf (D.resolutionOnFull bed)
      (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))
    (openOf X U)
    (Hom.mapsTo_openOf (D.resolutionOnFullMap bed) U) O
    (fun a ha => mem_openOf_of_subset Set.Subset.rfl (hO ha).1)
  obtain ⟨e', he', hec'⟩ := exists_iso_restrictOpen_restrictOpen_comap
    (D'.resolutionOnFullMap bed : (D'.resolutionOnFull bed).toKLocallyRingedSpace ⟶
      X.toKLocallyRingedSpace)
    (openOf (D'.resolutionOnFull bed)
      (KLocallyRingedSpace.Hom.toFun (D'.resolutionOnFullMap bed) ⁻¹' U'))
    (openOf X U')
    (Hom.mapsTo_openOf (D'.resolutionOnFullMap bed) U') O
    (fun a ha => mem_openOf_of_subset Set.Subset.rfl (hO ha).2)
  -- `e` and `e'` are the identifications; the isomorphism over `X` is `e ≫ t ≫ e'⁻¹`
  have hsiso : IsIso (e ≫ t ≫ @inv _ _ _ _ e' he') :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ he
      (@IsIso.comp_isIso _ _ _ _ _ _ _ ht (@IsIso.inv_isIso _ _ _ _ e' he'))
  have hinv : ofRestrict _ _ ≫ D'.resolutionOnFullMap bed =
      (@inv _ _ _ _ e' he' ≫ ofRestrict _ _) ≫ D'.resolutionOnToSpace bed :=
    @over_inv_of_over _ _ _ _ _ _ _ e' he' _ _ _ _ hec'
  have hsc : ofRestrict _ _ ≫ D.resolutionOnToSpace bed =
      ((e ≫ t ≫ @inv _ _ _ _ e' he') ≫ ofRestrict _ _) ≫ D'.resolutionOnToSpace bed :=
    over_comp₃ e t (@inv _ _ _ _ e' he') _ _ _ _ _ _ _ _ hec htc hinv
  refine ⟨e ≫ t ≫ @inv _ _ _ _ e' he', hsiso, hsc, fun s' hs' hs'c => ?_⟩
  exact uniq_of_conj (ofRestrict _ _ ≫ D.resolutionOnToSpace bed)
    (ofRestrict _ _ ≫ D.resolutionOnFullMap bed) (ofRestrict _ _ ≫ D'.resolutionOnToSpace bed)
    (ofRestrict _ _ ≫ D'.resolutionOnFullMap bed) (@asIso _ _ _ _ e he) (@asIso _ _ _ _ e' he')
    ((Category.assoc _ _ _).symm.trans hec.symm) ((Category.assoc _ _ _).symm.trans hec'.symm)
    (fun r r' hr hr' hc hc' =>
      (huniq r hr (hc.symm.trans (Category.assoc _ _ _).symm)).trans
        (huniq r' hr' (hc'.symm.trans (Category.assoc _ _ _).symm)).symm)
    s' _ hs' hsiso (hs'c.trans (Category.assoc _ _ _)).symm (hsc.trans (Category.assoc _ _ _)).symm

/-- **The independence of the glued resolution from the local embedding data**
([Wlo09, §4, (3)⇒(4)]; [Kol07, Theorem 36, proof]), with the independence of the local resolution
as the hypothesis `hind`: for data `D` over the OPEN `U` and `D'` over `U' ⊇ U`, a UNIQUE
isomorphism of `resolutionOn D bed` with the resolution of `D'` restricted over `U`, over `X|U` —
`exists_isoOver_resolutionOnFull` at `O := U` read into the spaces (`restrictOpenIsoOfSetEq`
between the spelling `openOf (Π⁻¹U)` and `comap Π U`; the composite `≫` and `Hom.restrictSet`
through `Hom.restrictTo_comp_ofRestrict` and `Hom.ext_of_comp_ofRestrict`). The form without
`hind` is `resolutionOn_indep` (`GluingProperties.lean`). -/
theorem resolutionOn_indep_of_independent (hU : IsOpen U) (hUU' : U ⊆ U')
    (hbed : bed.IsEmbeddedDesing) (hind : LocalResolutionIndependentOn X bed) :
    ∃! ψ : D.resolutionOn bed ⟶ (D'.resolutionOnFull bed).restrictSet
        (D'.resolutionOnFullMap bed ⁻¹' U),
      IsIso ψ ∧ ψ ≫ (D'.resolutionOnFullMap bed).restrictSet U = D.resolutionOnMap bed := by
  obtain ⟨s, hs, hsc, huniq⟩ := D.exists_isoOver_resolutionOnFull D' bed hbed hind ⟨U, hU⟩
    (fun x hx => ⟨hx, hUU' hx⟩)
  have hpre : IsOpen (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U) :=
    hU.preimage (Hom.continuous_toFun (D.resolutionOnFullMap bed))
  have hpre' : IsOpen (KLocallyRingedSpace.Hom.toFun (D'.resolutionOnFullMap bed) ⁻¹' U) :=
    hU.preimage (Hom.continuous_toFun (D'.resolutionOnFullMap bed))
  -- the `openOf` spelling of the parts over `U` against `comap`
  have hset : ((openOf (D.resolutionOnFull bed)
        (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U) :
          Opens (D.resolutionOnFull bed).toKLocallyRingedSpace) :
        Set (D.resolutionOnFull bed).toKLocallyRingedSpace) =
      ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
        Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ ⟨U, hU⟩ :
          Opens (D.resolutionOnFull bed).toKLocallyRingedSpace) :
        Set (D.resolutionOnFull bed).toKLocallyRingedSpace) :=
    (congrArg (fun V : Opens (D.resolutionOnFull bed).toKLocallyRingedSpace =>
        (V : Set (D.resolutionOnFull bed).toKLocallyRingedSpace))
      (openOf_of_isOpen (D.resolutionOnFull bed) hpre)).trans
      (Set.ext fun _ => Iff.rfl)
  have hset' : ((openOf (D'.resolutionOnFull bed)
        (KLocallyRingedSpace.Hom.toFun (D'.resolutionOnFullMap bed) ⁻¹' U) :
          Opens (D'.resolutionOnFull bed).toKLocallyRingedSpace) :
        Set (D'.resolutionOnFull bed).toKLocallyRingedSpace) =
      ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D'.resolutionOnFullMap bed),
        Hom.continuous_toFun (D'.resolutionOnFullMap bed)⟩ ⟨U, hU⟩ :
          Opens (D'.resolutionOnFull bed).toKLocallyRingedSpace) :
        Set (D'.resolutionOnFull bed).toKLocallyRingedSpace) :=
    (congrArg (fun V : Opens (D'.resolutionOnFull bed).toKLocallyRingedSpace =>
        (V : Set (D'.resolutionOnFull bed).toKLocallyRingedSpace))
      (openOf_of_isOpen (D'.resolutionOnFull bed) hpre')).trans
      (Set.ext fun _ => Iff.rfl)
  -- the restrictions of record, followed by the open immersion into `X`
  have hr : AnalyticSpace.Hom.restrictSet (D.resolutionOnFullMap bed) U ≫
      ofRestrict X.toKLocallyRingedSpace (openOf X U) =
      ofRestrict (D.resolutionOnFull bed).toKLocallyRingedSpace
        (openOf (D.resolutionOnFull bed)
          (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U)) ≫
              D.resolutionOnFullMap bed :=
    Hom.restrictTo_comp_ofRestrict (D.resolutionOnFullMap bed :
        (D.resolutionOnFull bed).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace)
      (openOf (D.resolutionOnFull bed)
        (KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed) ⁻¹' U))
      (openOf X U)
      (Hom.mapsTo_openOf (D.resolutionOnFullMap bed) U)
  have hr' : AnalyticSpace.Hom.restrictSet (D'.resolutionOnFullMap bed) U ≫
      ofRestrict X.toKLocallyRingedSpace (openOf X U) =
      ofRestrict (D'.resolutionOnFull bed).toKLocallyRingedSpace
        (openOf (D'.resolutionOnFull bed)
          (KLocallyRingedSpace.Hom.toFun (D'.resolutionOnFullMap bed) ⁻¹' U)) ≫
              D'.resolutionOnFullMap bed :=
    Hom.restrictTo_comp_ofRestrict (D'.resolutionOnFullMap bed :
        (D'.resolutionOnFull bed).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace)
      (openOf (D'.resolutionOnFull bed)
        (KLocallyRingedSpace.Hom.toFun (D'.resolutionOnFullMap bed) ⁻¹' U))
      (openOf X U)
      (Hom.mapsTo_openOf (D'.resolutionOnFullMap bed) U)
  have hK : IsIso (C := KLocallyRingedSpace.{u} 𝕜)
      ((restrictOpenIsoOfSetEq hset).hom ≫ s ≫ (restrictOpenIsoOfSetEq hset').inv) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ hs (Iso.isIso_inv _))
  -- the witness, elaborated as a `K`-morphism (against the An-typed expected type the `≫` would
  -- be read in `An` and the unifier sent to invert `?m.toKLocallyRingedSpace`)
  refine ⟨((restrictOpenIsoOfSetEq hset).hom ≫ s ≫ (restrictOpenIsoOfSetEq hset').inv :
      (D.resolutionOn bed).toKLocallyRingedSpace ⟶
        ((D'.resolutionOnFull bed).restrictSet
          (D'.resolutionOnFullMap bed ⁻¹' U)).toKLocallyRingedSpace),
    ⟨show CategoryTheory.IsIso (C := AnalyticSpace.{u} 𝕜) _ from by
      obtain ⟨⟨g, h1, h2⟩⟩ := hK
      exact ⟨⟨g, h1, h2⟩⟩, ?_⟩, ?_⟩
  · -- over `X|U`: after the open immersion into `X`, both sides are `Π` on the part over `U`
    change ((restrictOpenIsoOfSetEq hset).hom ≫ s ≫ (restrictOpenIsoOfSetEq hset').inv) ≫
        AnalyticSpace.Hom.restrictSet (D'.resolutionOnFullMap bed) U =
      AnalyticSpace.Hom.restrictSet (D.resolutionOnFullMap bed) U
    apply Hom.ext_of_comp_ofRestrict
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => ((restrictOpenIsoOfSetEq hset).hom ≫ s ≫
          (restrictOpenIsoOfSetEq hset').inv) ≫ k) hr').trans
        ((conj_over_eq _ s _ _ _ _ _ _ _ (restrictOpenIsoOfSetEq_hom_comp hset)
          (restrictOpenIsoOfSetEq_inv_comp hset') hsc).trans hr.symm))
  · -- uniqueness: any such `ψ'` transports to an isomorphism over `X` on the parts, hence to `s`
    rintro ψ' ⟨hψ'iso, hψ'c⟩
    -- read `ψ'` as a `K`-morphism (the An-typed morphism inside `≫` sends the unifier chasing
    -- `?Z.toKLocallyRingedSpace`)
    obtain ⟨ψK, hψK⟩ : ∃ ψK : (D.resolutionOn bed).toKLocallyRingedSpace ⟶
        ((D'.resolutionOnFull bed).restrictSet
          (D'.resolutionOnFullMap bed ⁻¹' U)).toKLocallyRingedSpace, ψK = ψ' := ⟨ψ', rfl⟩
    subst hψK
    have hψ'K : IsIso (C := KLocallyRingedSpace.{u} 𝕜) ψK := by
      obtain ⟨⟨g, h1, h2⟩⟩ := hψ'iso
      exact ⟨⟨g, h1, h2⟩⟩
    have hc1 : ψK ≫
        (AnalyticSpace.Hom.restrictSet (D'.resolutionOnFullMap bed) U ≫
        ofRestrict X.toKLocallyRingedSpace (openOf X U)) =
        AnalyticSpace.Hom.restrictSet (D.resolutionOnFullMap bed) U ≫
          ofRestrict X.toKLocallyRingedSpace (openOf X U) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun k : (D.resolutionOn bed).toKLocallyRingedSpace ⟶
            (X.restrictSet U).toKLocallyRingedSpace =>
          k ≫ ofRestrict X.toKLocallyRingedSpace (openOf X U))
          hψ'c)
    have hc2 : ofRestrict _ _ ≫ D.resolutionOnFullMap bed =
        ψK ≫ (ofRestrict _ _ ≫ D'.resolutionOnFullMap bed) :=
      (hr.symm.trans hc1.symm).trans
        (congrArg (fun k : (D'.resolutionOnFull bed).toKLocallyRingedSpace.restrictOpen
            (openOf (D'.resolutionOnFull bed)
              (KLocallyRingedSpace.Hom.toFun (D'.resolutionOnFullMap bed) ⁻¹' U)) ⟶
                  X.toKLocallyRingedSpace =>
          ψK ≫ k) hr')
    have hs'c : ofRestrict _ _ ≫ D.resolutionOnFullMap bed =
        (((restrictOpenIsoOfSetEq hset).inv ≫ ψK ≫ (restrictOpenIsoOfSetEq hset').hom) ≫
          ofRestrict _ _) ≫ D'.resolutionOnFullMap bed :=
      (over_of_conj_inv_hom (restrictOpenIsoOfSetEq hset) (restrictOpenIsoOfSetEq hset') _ _ _ _
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k : (D.resolutionOnFull bed).toKLocallyRingedSpace.restrictOpen
              (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnFullMap bed),
                Hom.continuous_toFun (D.resolutionOnFullMap bed)⟩ ⟨U, hU⟩) ⟶
              (D.resolutionOnFull bed).toKLocallyRingedSpace => k ≫ D.resolutionOnFullMap bed)
            (restrictOpenIsoOfSetEq_inv_comp hset)))
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k : (D'.resolutionOnFull bed).toKLocallyRingedSpace.restrictOpen
              (openOf (D'.resolutionOnFull bed)
                (KLocallyRingedSpace.Hom.toFun (D'.resolutionOnFullMap bed) ⁻¹' U)) ⟶
              (D'.resolutionOnFull bed).toKLocallyRingedSpace => k ≫ D'.resolutionOnFullMap bed)
            (restrictOpenIsoOfSetEq_hom_comp hset'))) ψK hc2).trans (Category.assoc _ _ _).symm
    have hs'K : IsIso (C := KLocallyRingedSpace.{u} 𝕜)
        ((restrictOpenIsoOfSetEq hset).inv ≫ ψK ≫ (restrictOpenIsoOfSetEq hset').hom) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _)
        (@IsIso.comp_isIso _ _ _ _ _ _ _ hψ'K (Iso.isIso_hom _))
    have heq := huniq _ hs'K hs'c
    exact (conj_conj_inv (restrictOpenIsoOfSetEq hset) (restrictOpenIsoOfSetEq hset') ψK).symm.trans
      (congrArg (fun k => (restrictOpenIsoOfSetEq hset).hom ≫ k ≫
        (restrictOpenIsoOfSetEq hset').inv) heq)

end Hironaka.Manifold.LocalEmbeddingData

namespace Hironaka.Manifold.BEDanFamStar

variable {𝕜 : Type} [RCLike 𝕜]

/-- **The resolution glues along an exhaustion** ([Wlo09, §4.3]; [Kol07, 44]; an analytic space is
countable at infinity, [Hir64, Ch. 0, §1, p. 120]), with the independence of the local resolution
as the hypothesis `hind` — an exhaustion `U_0 ⋐ U_1 ⋐ ⋯` of `X`, local embedding data `D_n` over
each `U_n` (`exists_localEmbeddingData_of_padTools`), their gluing data, and the gluing over `X` of
the `resolutionOn (D n) bed` along `U_n ∩ U_m` by `GlueOver.exists_glueOver_of_transitions`, whose
transitions and uniqueness hypothesis are `exists_isoOver_resolutionOn` at `U_n ⊓ U_m` (resp. at
every sub-open). The form without `hind` is `resolutionGlues_of_isEmbeddedDesing`
(`GluingProperties.lean`). -/
theorem resolutionGlues_of_isEmbeddedDesing_of_independent
    (X : AnalyticSpace.{u} 𝕜)
    (hX : X.IsReduced) (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) : bed.ResolutionGlues X := by
  -- the exhaustion, its opens read on the carrier of `X`
  have hex : ∃ U : ℕ → Opens X, (∀ n, IsCompact (closure (U n : Set X))) ∧
      (∀ n, closure (U n : Set X) ⊆ U (n + 1)) ∧ ⋃ n, (U n : Set X) = univ :=
    exists_exhaustion X
  obtain ⟨U, hUc, hUsucc, hUunion⟩ := hex
  have hD : ∀ n, Nonempty (LocalEmbeddingData 𝕜 X (U n)) := fun n =>
    exists_localEmbeddingData_of_padTools (padTools 𝕜) hX (U n : Set X) (hUc n)
  let D : ∀ n, LocalEmbeddingData 𝕜 X (U n) := fun n => (hD n).some
  -- the pieces lie over the members of the exhaustion
  have hrange : ∀ n : ULift.{u} ℕ,
      range (KLocallyRingedSpace.Hom.toFun ((D n.down).resolutionOnToSpace bed)) ⊆
          (U n.down : Set X) := by
    rintro n _ ⟨r, rfl⟩
    exact (SetLike.ext_iff.mp
      (openOf_of_isOpen X (U n.down).isOpen) _).mp
      (KLocallyRingedSpace.Hom.toFun ((D n.down).resolutionOnMap bed) r).2
  -- the transitions on the overlaps, read onto the gluing opens (`inf_comm` on the `m` side)
  have htrans : ∀ n m : ULift.{u} ℕ,
      ∃ t : ((D n.down).resolutionOn bed).toKLocallyRingedSpace.restrictOpen
            (GlueOver.glueOpens X (fun n : ULift.{u} ℕ => (D n.down).resolutionOn bed)
              (fun n => (D n.down).resolutionOnToSpace bed) (fun n => U n.down) n m) ⟶
          ((D m.down).resolutionOn bed).toKLocallyRingedSpace.restrictOpen
            (GlueOver.glueOpens X (fun n : ULift.{u} ℕ => (D n.down).resolutionOn bed)
              (fun n => (D n.down).resolutionOnToSpace bed) (fun n => U n.down) m n),
        IsIso t ∧
          ofRestrict _ _ ≫ (D n.down).resolutionOnToSpace bed =
            (t ≫ ofRestrict _ _) ≫ (D m.down).resolutionOnToSpace bed := by
    intro n m
    obtain ⟨s, hs, hsc, -⟩ := (D n.down).exists_isoOver_resolutionOn (D m.down) bed hbed hind
      (U n.down ⊓ U m.down)
      (fun x hx => ⟨((Opens.mem_inf).mp hx).1, ((Opens.mem_inf).mp hx).2⟩)
    have hseti : ((GlueOver.glueOpens X (fun n : ULift.{u} ℕ => (D n.down).resolutionOn bed)
          (fun n => (D n.down).resolutionOnToSpace bed) (fun n => U n.down) n m :
          Opens ((D n.down).resolutionOn bed).toKLocallyRingedSpace) :
          Set ((D n.down).resolutionOn bed).toKLocallyRingedSpace) =
        ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D n.down).resolutionOnToSpace bed),
          Hom.continuous_toFun ((D n.down).resolutionOnToSpace bed)⟩ (U n.down ⊓ U m.down) :
          Opens ((D n.down).resolutionOn bed).toKLocallyRingedSpace) :
          Set ((D n.down).resolutionOn bed).toKLocallyRingedSpace) := rfl
    have hsetj : ((Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D m.down).resolutionOnToSpace bed),
          Hom.continuous_toFun ((D m.down).resolutionOnToSpace bed)⟩ (U n.down ⊓ U m.down) :
          Opens ((D m.down).resolutionOn bed).toKLocallyRingedSpace) :
          Set ((D m.down).resolutionOn bed).toKLocallyRingedSpace) =
        ((GlueOver.glueOpens X (fun n : ULift.{u} ℕ => (D n.down).resolutionOn bed)
          (fun n => (D n.down).resolutionOnToSpace bed) (fun n => U n.down) m n :
          Opens ((D m.down).resolutionOn bed).toKLocallyRingedSpace) :
          Set ((D m.down).resolutionOn bed).toKLocallyRingedSpace) :=
      Set.ext fun q => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    refine ⟨(restrictOpenIsoOfSetEq hseti).inv ≫ s ≫ (restrictOpenIsoOfSetEq hsetj).hom,
      @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _)
        (@IsIso.comp_isIso _ _ _ _ _ _ _ hs (Iso.isIso_hom _)), ?_⟩
    exact CategoryTheory.over_of_conj _ _ s _ _ _ _ _ _ (restrictOpenIsoOfSetEq_inv_comp hseti)
      (restrictOpenIsoOfSetEq_hom_comp hsetj) hsc
  choose t htiso htc using htrans
  refine ⟨{ U := U
            isCompact_closure_U := hUc
            closure_U_subset_succ := hUsucc
            iUnion_U := hUunion
            D := D
            glues := fun n =>
              (D n).resolutionGluesOn_of_isEmbeddedDesing_of_independent bed hbed hind
            glue := (GlueOver.exists_glueOver_of_transitions hrange t htiso htc
              (fun n m O hO s s' hs hs' hc hc' => ?_)).some }⟩
  obtain ⟨t₀, -, -, hu⟩ := (D n.down).exists_isoOver_resolutionOn (D m.down) bed hbed hind O
    (fun x hx => ⟨((Opens.mem_inf).mp (hO hx)).1, ((Opens.mem_inf).mp (hO hx)).2⟩)
  exact (hu s hs hc).trans (hu s' hs' hc').symm

end Hironaka.Manifold.BEDanFamStar

end
