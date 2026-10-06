/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceIndependence
public import Hironaka.Resolution.Analytic.OrderReduction.ConcatPullback
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.AnalyticSpace.Manifold.Chart
import Hironaka.AnalyticSpace.SigmaLemmas
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Kol07Thm45.OpenEmbeddingLift
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Hom
import Hironaka.Resolution.Analytic.OrderReduction.ChainTransportPrep
import Hironaka.Resolution.Analytic.OrderReduction.ValueTransport
import Hironaka.Resolution.Analytic.Restrict.StrictSubspaceSeqTransport
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The local resolution over a smaller open, and the relation "isomorphic over `N`"

Kollár's proof of Theorem 36 compares the local resolutions of a piece for two embeddings NEAR a
point [Kol07, Theorem 36, proof]: `localResolution_independent_local`
(`LocalResolutionShear.lean`) asks for an open `N` of the piece and an isomorphism of the two local
resolutions restricted over `N`, compatible with the maps to the piece — the relation
`LocIso N (A, pA) (B, pB) :≡ ∃ ψ : A|pA⁻¹N ≅ B|pB⁻¹N, pB|N ∘ ψ = pA|N` (not given a name: the
theorems state it in full). This module provides:

* the relation is an equivalence — `AnalyticSpace.exists_restrictSet_isIso_trans`,
  `exists_restrictSet_isIso_symm` — and `exists_restrictSet_isIso_of_comp_eq` feeds it every global
  isomorphism over the piece; its open-immersion form
  `exists_restrictSet_isIso_of_comp_eq_of_isOpenImmersion` (an open immersion `A → B` over the piece
  whose range covers `pB⁻¹ N` restricts to an isomorphism over `N`; the `isoOfRangeEq` mechanism
  with the isomorphism hypothesis weakened to the range condition, for OPEN `N` — the restriction
  of a space to a non-open set is by convention the whole space, `openOf`);
* the morphism `homOfPullbackEq` of closed subspaces induced by an identity `J' = f^* J` along an
  INJECTIVE local analytic isomorphism `f` is an open immersion with range the points over
  `range f` (`isOpenImmersion_homOfPullbackEq_of_injective`, `range_toFun_homOfPullbackEq`) —
  `isIso_homOfPullbackEq_of_diffeomorph`'s mechanism minus surjectivity;
* the preimage of a relatively compact open under the zero extension is relatively compact
  (`isCompact_closure_preimage_padExt`);
* **restriction to a smaller open**: for relatively compact opens `W' ≤ W` of the ambient, the
  compatibility field `compat` of the family (`Functor/Family.lean`; the restriction of the
  factorization to a smaller open determines the factorization, [Wlo09, Theorem 2.0.2(5)]) gives
  the sequence over `W'` as the pull-back of the sequence over `W` along the open inclusion with
  empty centres erased (`localResolutionSeq_of_le`); the last-stage lift `liftOfLe` (the lift of
  [Kol07, Definition 30.1], through `stageOfEq`, `eraseEmptyLast`, `pullbackLiftLast`) is an
  injective local isomorphism over the inclusion with range the part over `W'`; the final strict
  transforms correspond (`strictTransformSubspaceSeq_last_liftOfLe`); so the induced morphism of
  closed subspaces is an open immersion `localResolutionHomOfLe : Ỹ(W') → Ỹ(W)` over the piece
  (`localResolutionToPiece_comp_localResolutionHomOfLe`) whose range covers everything over an
  open `N ⊆ embPreimage W'`, and `exists_restrictSet_isIso_localResolution_of_le` is the
  open-immersion form of the relation at it.

Not in the sources beyond Kollár's comparison; bookkeeping (the lift of [Kol07, Definition 30.1]
at an open inclusion; the functoriality of quotients).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff Topology

universe u

/-! ### The relation "isomorphic over `N`" is an equivalence -/

namespace AnalyticSpace

variable {𝕜 : Type} [RCLike 𝕜]

/-- The relation "`(A, pA)` and `(B, pB)` over `Z` are isomorphic over `N` compatibly with the
maps" is transitive: compose the two isomorphisms of the restrictions. -/
theorem exists_restrictSet_isIso_trans {A B C Z : AnalyticSpace.{u} 𝕜} (pA : A ⟶ Z) (pB : B ⟶ Z)
    (pC : C ⟶ Z) (N : Set Z)
    (h₁ : ∃ ψ : A.restrictSet (pA ⁻¹' N) ⟶ B.restrictSet (pB ⁻¹' N),
      IsIso ψ ∧ ψ ≫ pB.restrictSet N = pA.restrictSet N)
    (h₂ : ∃ ψ : B.restrictSet (pB ⁻¹' N) ⟶ C.restrictSet (pC ⁻¹' N),
      IsIso ψ ∧ ψ ≫ pC.restrictSet N = pB.restrictSet N) :
    ∃ ψ : A.restrictSet (pA ⁻¹' N) ⟶ C.restrictSet (pC ⁻¹' N),
      IsIso ψ ∧ ψ ≫ pC.restrictSet N = pA.restrictSet N := by
  obtain ⟨ψ₁, h₁i, h₁c⟩ := h₁
  obtain ⟨ψ₂, h₂i, h₂c⟩ := h₂
  have i₁ : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _ ψ₁ := h₁i
  have i₂ : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _ ψ₂ := h₂i
  refine ⟨ψ₁ ≫ ψ₂, ?_, ?_⟩
  · exact @IsIso.comp_isIso (AnalyticSpace.{u} 𝕜) _ _ _ _ ψ₁ ψ₂ i₁ i₂
  · calc (ψ₁ ≫ ψ₂) ≫ pC.restrictSet N
        = ψ₁ ≫ (ψ₂ ≫ pC.restrictSet N) := Category.assoc _ _ _
      _ = ψ₁ ≫ pB.restrictSet N := congrArg (fun k => ψ₁ ≫ k) h₂c
      _ = pA.restrictSet N := h₁c

/-- The relation is symmetric: the inverse isomorphism. -/
theorem exists_restrictSet_isIso_symm {A B Z : AnalyticSpace.{u} 𝕜} (pA : A ⟶ Z) (pB : B ⟶ Z)
    (N : Set Z)
    (h : ∃ ψ : A.restrictSet (pA ⁻¹' N) ⟶ B.restrictSet (pB ⁻¹' N),
      IsIso ψ ∧ ψ ≫ pB.restrictSet N = pA.restrictSet N) :
    ∃ ψ : B.restrictSet (pB ⁻¹' N) ⟶ A.restrictSet (pA ⁻¹' N),
      IsIso ψ ∧ ψ ≫ pA.restrictSet N = pB.restrictSet N := by
  obtain ⟨ψ, hi, hc⟩ := h
  have i : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _ ψ := hi
  refine ⟨inv ψ, @IsIso.inv_isIso (AnalyticSpace.{u} 𝕜) _ _ _ ψ i, ?_⟩
  have e : inv ψ ≫ ψ = 𝟙 _ := IsIso.inv_hom_id ψ
  calc (inv ψ) ≫ pA.restrictSet N
      = inv ψ ≫ (ψ ≫ pB.restrictSet N) := congrArg (fun k => inv ψ ≫ k) hc.symm
    _ = (inv ψ ≫ ψ) ≫ pB.restrictSet N := (Category.assoc _ _ _).symm
    _ = 𝟙 _ ≫ pB.restrictSet N := congrArg (· ≫ pB.restrictSet N) e
    _ = pB.restrictSet N := Category.id_comp _

/-! ### The open-immersion form of the restriction lemma -/

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- An OPEN IMMERSION `χ : A → B` over `Z` (`χ ≫ pB = pA`) whose range contains `pB⁻¹ N`, for an
OPEN `N`, restricts to an isomorphism `A|pA⁻¹N ≅ B|pB⁻¹N` over `Z|N` — `isoOfRangeEq` of the two
open immersions `A|pA⁻¹N → B` and `B|pB⁻¹N → B` with equal ranges, the compatibility by
`lift_uniq`/`lift_fac`; the isomorphism hypothesis of `exists_restrictSet_isIso_of_comp_eq`
weakened to the range condition. -/
theorem exists_restrictSet_isIso_of_comp_eq_of_isOpenImmersion {A B Z : AnalyticSpace.{u} K}
    (χ : A.toKLocallyRingedSpace ⟶ B.toKLocallyRingedSpace)
    [hχ : LocallyRingedSpace.IsOpenImmersion χ.1]
    (pA : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace)
    (pB : B.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace) (h : χ ≫ pB = pA) (N : Set Z)
    (hNo : IsOpen N)
    (hN : KLocallyRingedSpace.Hom.toFun pB ⁻¹' N ⊆ Set.range (KLocallyRingedSpace.Hom.toFun χ)) :
    ∃ ψ' : A.toKLocallyRingedSpace.restrictOpen
          (openOf A (KLocallyRingedSpace.Hom.toFun pA ⁻¹' N)) ⟶
        B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun pB ⁻¹' N)),
      IsIso ψ' ∧ ψ' ≫ Hom.restrictSet pB N = Hom.restrictSet pA N := by
  -- the preimages of `N` correspond under `χ`
  have hpre : KLocallyRingedSpace.Hom.toFun pA ⁻¹' N =
      KLocallyRingedSpace.Hom.toFun χ ⁻¹' (KLocallyRingedSpace.Hom.toFun pB ⁻¹' N) := by
    rw [← h]; rfl
  have hoB : IsOpen (KLocallyRingedSpace.Hom.toFun pB ⁻¹' N) :=
    hNo.preimage (KLocallyRingedSpace.Hom.continuous_toFun pB)
  have hoA : IsOpen (KLocallyRingedSpace.Hom.toFun pA ⁻¹' N) :=
    hNo.preimage (KLocallyRingedSpace.Hom.continuous_toFun pA)
  let UA : Opens A.toKLocallyRingedSpace := openOf A (KLocallyRingedSpace.Hom.toFun pA ⁻¹' N)
  have hUA : UA = openOf A (KLocallyRingedSpace.Hom.toFun pA ⁻¹' N) := rfl
  let UB : Opens B.toKLocallyRingedSpace := openOf B (KLocallyRingedSpace.Hom.toFun pB ⁻¹' N)
  have hUB : UB = openOf B (KLocallyRingedSpace.Hom.toFun pB ⁻¹' N) := rfl
  have hsets : SetLike.coe UA = KLocallyRingedSpace.Hom.toFun χ ⁻¹' SetLike.coe UB := by
    rw [hUA, hUB, openOf_of_isOpen _ hoA, openOf_of_isOpen _ hoB]
    exact hpre
  -- the two open immersions into `B` with the same range
  have ha : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict A.toKLocallyRingedSpace UA ≫ χ).1 := by
    rw [KLocallyRingedSpace.Hom.comp_val]
    infer_instance
  have hb : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict B.toKLocallyRingedSpace UB).1 := inferInstance
  have hrange : Set.range (KLocallyRingedSpace.Hom.toFun
        (ofRestrict A.toKLocallyRingedSpace UA ≫ χ)) =
      Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict B.toKLocallyRingedSpace UB)) := by
    rw [KLocallyRingedSpace.Hom.range_toFun_comp, range_toFun_ofRestrict, range_toFun_ofRestrict,
      hsets, Set.image_preimage_eq_inter_range, hUB, openOf_of_isOpen _ hoB]
    exact Set.inter_eq_left.mpr hN
  refine ⟨(isoOfRangeEq _ _ hrange).hom, inferInstance, ?_⟩
  -- the compatibility: both sides are the lift of `A|_{Π_A⁻¹N} → A → Z` through `Z|_N → Z`
  have hZ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict Z.toKLocallyRingedSpace (openOf Z N)).1 := inferInstance
  apply KLocallyRingedSpace.Hom.ext
  refine AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_uniq (H := hZ)
    (ofRestrict Z.toKLocallyRingedSpace (openOf Z N)).1
    (ofRestrict A.toKLocallyRingedSpace UA ≫ pA).1
    (range_toFun_ofRestrict_comp_subset pA N) _ ?_
  have hB : (Hom.restrictSet pB N).1 ≫ (ofRestrict Z.toKLocallyRingedSpace (openOf Z N)).1 =
      (ofRestrict B.toKLocallyRingedSpace UB ≫ pB).1 :=
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac (H := hZ) _ _
      (range_toFun_ofRestrict_comp_subset pB N)
  have hE : (isoOfRangeEq _ _ hrange).hom.1 ≫ (ofRestrict B.toKLocallyRingedSpace UB).1 =
      (ofRestrict A.toKLocallyRingedSpace UA ≫ χ).1 :=
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (le_of_eq hrange)
  calc ((isoOfRangeEq _ _ hrange).hom ≫ Hom.restrictSet pB N).1 ≫
        (ofRestrict Z.toKLocallyRingedSpace (openOf Z N)).1
      = (isoOfRangeEq _ _ hrange).hom.1 ≫ ((Hom.restrictSet pB N).1 ≫
          (ofRestrict Z.toKLocallyRingedSpace (openOf Z N)).1) := Category.assoc _ _ _
    _ = (isoOfRangeEq _ _ hrange).hom.1 ≫ (ofRestrict B.toKLocallyRingedSpace UB ≫ pB).1 :=
          congrArg _ hB
    _ = ((isoOfRangeEq _ _ hrange).hom.1 ≫ (ofRestrict B.toKLocallyRingedSpace UB).1) ≫ pB.1 :=
          (Category.assoc _ _ _).symm
    _ = (ofRestrict A.toKLocallyRingedSpace UA ≫ χ).1 ≫ pB.1 := congrArg (· ≫ pB.1) hE
    _ = (ofRestrict A.toKLocallyRingedSpace UA).1 ≫ (χ ≫ pB).1 := Category.assoc _ _ _
    _ = (ofRestrict A.toKLocallyRingedSpace UA ≫ pA).1 := by
          rw [h, KLocallyRingedSpace.Hom.comp_val]

end KLocallyRingedSpace

/-- The relation "isomorphic over `N`" from an open immersion over the piece whose range covers
`pB⁻¹ N`, `N` open — the analytic-space form of
`KLocallyRingedSpace.exists_restrictSet_isIso_of_comp_eq_of_isOpenImmersion`. -/
theorem exists_restrictSet_isIso_of_comp_eq_of_isOpenImmersion {A B Z : AnalyticSpace.{u} 𝕜}
    (χ : A ⟶ B) (hχ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion χ.1) (pA : A ⟶ Z)
    (pB : B ⟶ Z) (h : χ ≫ pB = pA) (N : Set Z) (hNo : IsOpen N)
    (hN : pB ⁻¹' N ⊆ Set.range χ) :
    ∃ ψ : A.restrictSet (pA ⁻¹' N) ⟶ B.restrictSet (pB ⁻¹' N),
      IsIso ψ ∧ ψ ≫ pB.restrictSet N = pA.restrictSet N := by
  obtain ⟨ψ', hiso, hc⟩ :=
    KLocallyRingedSpace.exists_restrictSet_isIso_of_comp_eq_of_isOpenImmersion
      (hχ := hχ) χ pA pB h N hNo hN
  exact ⟨ψ', AnalyticSpace.isIso_of_isIso_toKLocallyRingedSpace _ hiso, hc⟩

end AnalyticSpace

namespace Hironaka.Manifold

open _root_.Manifold

open AnalyticSpace KLocallyRingedSpace

variable {𝕜 : Type} [RCLike 𝕜]

/-! ### The preimage of a relatively compact open under the zero extension -/

section Pad

variable {n n' : ℕ} (σ : Fin n ↪ Fin n') (G : Opens (Fin n → 𝕜))

/-- The zero extension `s : G → padOpens σ G` is a closed embedding: a homeomorphism onto the
closed slice (`padExtDiffeomorph`, `isClosed_padSlice`). Internal. -/
theorem isClosedEmbedding_padExt :
    Topology.IsClosedEmbedding
      (padExt σ G : pieceAmbient.{u} 𝕜 G → pieceAmbient.{u} 𝕜 (padOpens σ G)) := by
  have h1 : Topology.IsClosedEmbedding
      (Subtype.val : padSlice.{u} σ G → pieceAmbient.{u} 𝕜 (padOpens σ G)) :=
    (isClosed_padSlice σ G).isClosedEmbedding_subtypeVal
  have h2 : Topology.IsClosedEmbedding ⇑(padExtDiffeomorph σ G).toHomeomorph :=
    (padExtDiffeomorph σ G).toHomeomorph.isClosedEmbedding
  exact h1.comp h2

/-- The preimage under the zero extension of a relatively compact open is relatively compact:
`closure (s⁻¹ U) ⊆ s⁻¹ (closure U)`, the preimage of a compact set under a closed embedding
(`Topology.IsClosedEmbedding.isCompact_preimage`). -/
theorem isCompact_closure_preimage_padExt (U : Opens (pieceAmbient.{u} 𝕜 (padOpens σ G)))
    (hU : IsCompact (closure (U : Set (pieceAmbient 𝕜 (padOpens σ G))))) :
    IsCompact (closure (padExt σ G ⁻¹' (U : Set (pieceAmbient 𝕜 (padOpens σ G))))) :=
  ((isClosedEmbedding_padExt σ G).isCompact_preimage hU).of_isClosed_subset isClosed_closure
    ((contMDiff_padExt σ G).continuous.closure_preimage_subset _)

end Pad

/-! ### The induced morphism of closed subspaces along an injective local isomorphism -/

section HomOfPullbackOpen

variable {n : ℕ} {A A' : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (f : AnalyticMap A' A)
  (hf : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω f)
  {J' : AnalyticManifold.IdealSheaf A'} {J : AnalyticManifold.IdealSheaf A}

include hf in
/-- The morphism of closed subspaces induced by `J' = f^* J` along an INJECTIVE local analytic
isomorphism `f` is an open immersion: the base map is the restriction of the open embedding `f` to
the cosupports (`cosupport_pullback_of_bijective` with `germMap_bijective_of_isLocalDiffeomorphAt`,
`Set.restrictPreimage_isOpenEmbedding`), the fibre maps are bijective
(`isIso_map_stalkMap_of_bijective`), Mathlib's `LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` —
`isIso_homOfPullbackEq_of_diffeomorph`'s mechanism minus surjectivity. -/
theorem isOpenImmersion_homOfPullbackEq_of_injective (hi : Function.Injective f)
    (h : J' = J.pullback f f.contMDiff) :
    LocallyRingedSpace.IsOpenImmersion (IdealSheaf.homOfPullbackEq f f.contMDiff h).1 := by
  subst h
  have hbij : ∀ z, Function.Bijective (germMap ⇑f f.contMDiff z) := fun z =>
    germMap_bijective_of_isLocalDiffeomorphAt ⇑f f.contMDiff (hf z)
  change LocallyRingedSpace.IsOpenImmersion (QuotientSpace.map (ofManifoldHom ⇑f f.contMDiff).1
    (J.pullback ⇑f f.contMDiff) J (compat_ofManifoldHom_of_eq ⇑f f.contMDiff rfl))
  let F := QuotientSpace.map (ofManifoldHom ⇑f f.contMDiff).1 (J.pullback ⇑f f.contMDiff) J
    (compat_ofManifoldHom_of_eq ⇑f f.contMDiff rfl)
  have hopen : Topology.IsOpenEmbedding ⇑f := AnalyticMap.isOpenEmbedding_of_injective f hf hi
  have hcos : (J.pullback ⇑f f.contMDiff).support = ⇑f ⁻¹' J.support :=
    cosupport_pullback_of_bijective ⇑f f.contMDiff hbij
  -- the base map is the restriction of `f` to the cosupports
  have hbase : (F.base : (J.pullback ⇑f f.contMDiff).support → J.support) =
      Set.restrictPreimage J.support ⇑f ∘ Homeomorph.setCongr hcos :=
    funext fun _ => Subtype.ext rfl
  have hemb : Topology.IsOpenEmbedding
      (F.base : (J.pullback ⇑f f.contMDiff).support → J.support) :=
    hbase ▸ (Set.restrictPreimage_isOpenEmbedding _ hopen).comp
      (Homeomorph.setCongr hcos).isOpenEmbedding
  have : ∀ z, IsIso (F.stalkMap z) := fun z => by
    refine QuotientSpace.isIso_map_stalkMap_of_bijective _ _ _ _ z ?_
    obtain ⟨hinj, hsurj'⟩ := hbij z.1
    refine ⟨Ideal.quotientMap_injective' ?_, Ideal.quotientMap_surjective ?_⟩
    · change (IdealSheaf.stalkIdeal _ z.1).comap ((ofManifoldHom ⇑f f.contMDiff).1.stalkMap
        z.1).hom ≤ _
      rw [stalkMap_ofManifoldHom_hom, IdealSheaf.stalkIdeal_pullback]
      exact (Ideal.comap_map_of_bijective _ ⟨hinj, hsurj'⟩).le
    · rw [stalkMap_ofManifoldHom_hom]
      exact hsurj'
  exact LocallyRingedSpace.IsOpenImmersion.of_stalk_iso F hemb

include hf in
/-- The range of the induced morphism along a local analytic isomorphism: the points of `Sp(A)/J`
over the range of `f` (the cosupport of `f^* J` is the preimage of the cosupport of `J`,
`cosupport_pullback_of_bijective`). -/
theorem range_toFun_homOfPullbackEq (h : J' = J.pullback f f.contMDiff) :
    Set.range
        ⇑(IdealSheaf.homOfPullbackEq f f.contMDiff h)
            =
      {z : J.toAnalyticSpace |
        J.toAnalyticSpaceι z ∈ Set.range f} := by
  subst h
  have hcos : (J.pullback ⇑f f.contMDiff).support = ⇑f ⁻¹' J.support :=
    cosupport_pullback_of_bijective ⇑f f.contMDiff fun z =>
      germMap_bijective_of_isLocalDiffeomorphAt ⇑f f.contMDiff (hf z)
  ext z
  constructor
  · rintro ⟨z', rfl⟩
    exact ⟨z'.1, rfl⟩
  · rintro ⟨a, ha⟩
    have haC : a ∈ (J.pullback ⇑f f.contMDiff).support := by
      rw [hcos]
      exact (show f a ∈ J.support from ha ▸ z.2)
    exact ⟨⟨a, haC⟩, Subtype.ext ha⟩

end HomOfPullbackOpen

end Hironaka.Manifold

/-! ### The local resolution over a smaller open -/

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold
open AnalyticSpace.KLocallyRingedSpace

variable {𝕜 : Type} [RCLike 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}
  {M N : AnalyticManifold.{u} 𝕜 E}

/-- `strictTransformSubspaceSeq_last_pullback_eraseEmpty'` read through a sequence EQUAL to the
erased pull-back and an ideal EQUAL to the pulled-back ideal: the final strict transform of `J'`
along `L'` is the pull-back of the final strict transform of `J` along `L` under the lift
`pullbackLiftLast ∘ eraseEmptyLast⁻¹ ∘ stageOfEq e` (the lift of [Kol07, Definition 30.1]; `subst`
on both equalities, `stageOfEq rfl` the identity). Internal. -/
theorem strictTransformSubspaceSeq_last_of_eq_pullback_eraseEmpty (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (L' : BlowUpSequence ψ₀ N)
    (e : L' = (L.pullback h hh).eraseEmpty) (J' : IdealSheaf N)
    (J : IdealSheaf M) (hJ : J' = J.pullback h h.contMDiff) :
    L'.toSuccession.strictTransformSubspaceSeq J' (Fin.last _) =
      Manifold.IdealSheaf.pullback _ ((L.pullbackLiftLast h hh).comp
        ((Diffeomorph.toAnalyticMap (L.pullback h hh).eraseEmptyLast.symm).comp
          (Diffeomorph.toAnalyticMap (stageOfEq e)))).contMDiff
        (L.toSuccession.strictTransformSubspaceSeq J (Fin.last _)) := by
  have := Manifold.finiteDimensional_of_chartIso ψ₀
  subst e hJ
  rw [strictTransformSubspaceSeq_last_pullback_eraseEmpty' L h hh J,
    IdealSheaf.pullback_comp]
  exact Manifold.IdealSheaf.pullback_congr _ _ _ (funext fun _ => rfl)

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open AnalyticSpace.KLocallyRingedSpace

variable {𝕜 : Type} [RCLike 𝕜]

local notation:80 g:81 " ⊚ " f:80 => CategoryTheory.CategoryStruct.comp (obj := AnalyticSpace _) f g

namespace PieceEmbedding

open _root_.Manifold

variable {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)
  (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
  (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) (W' : Opens (pieceAmbient.{u} 𝕜 E.G))
  (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 E.G))))

/-- The compatibility field `compat` of the family (`Functor/Family.lean`) at the piece's triple
([Wlo09, Theorem 2.0.2(5)]): the sequence over `W'` is the pull-back of the sequence over `W`
along the open inclusion, empty centres erased. -/
theorem localResolutionSeq_of_le (hle : W' ≤ W) :
    E.localResolutionSeq bed W' hW' =
      ((E.localResolutionSeq bed W hW).pullback ((pieceAmbient 𝕜 E.G).restrictLE hle)
        (isLocalDiffeomorph_restrictLE hle)).eraseEmpty :=
  ((bed.fam n).fam E.ambientTriple E.domBEDan_ambientTriple).compat W' W hW' hW hle

/-- **The last-stage lift of the open inclusion** `W' ↪ W` (the lift of [Kol07, Definition 30.1]
at an open inclusion): the transport `stageOfEq` along `localResolutionSeq_of_le`, then
`eraseEmptyLast⁻¹`, then `pullbackLiftLast` — an analytic map from the last stage of the sequence
over `W'` to the last stage of the sequence over `W`. -/
def liftOfLe (hle : W' ≤ W) :
    AnalyticMap ((E.localResolutionSeq bed W' hW').stage (Fin.last _))
      ((E.localResolutionSeq bed W hW).stage (Fin.last _)) :=
  ((E.localResolutionSeq bed W hW).pullbackLiftLast ((pieceAmbient 𝕜 E.G).restrictLE hle)
      (isLocalDiffeomorph_restrictLE hle)).comp
    ((Diffeomorph.toAnalyticMap (((E.localResolutionSeq bed W hW).pullback
        ((pieceAmbient 𝕜 E.G).restrictLE hle)
        (isLocalDiffeomorph_restrictLE hle)).eraseEmptyLast.symm)).comp
      (Diffeomorph.toAnalyticMap
        (AnalyticManifold.BlowUpSequence.stageOfEq (E.localResolutionSeq_of_le bed W hW W' hW'
            hle))))

/-- The lift is a local analytic isomorphism (`isLocalDiffeomorph_pullbackLiftLast`, two
diffeomorphisms). -/
theorem isLocalDiffeomorph_liftOfLe (hle : W' ≤ W) :
    IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (E.liftOfLe bed W hW W' hW' hle) :=
  AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (Diffeomorph.isLocalDiffeomorph _)
      (Diffeomorph.isLocalDiffeomorph _))

/-- The lift is injective (`injective_pullbackLiftLast`, the inclusion injective). -/
theorem injective_liftOfLe (hle : W' ≤ W) :
    Function.Injective (E.liftOfLe bed W hW W' hW' hle) :=
  (AnalyticManifold.BlowUpSequence.injective_pullbackLiftLast _ _ _
      (Set.inclusion_injective hle)).comp
    ((((E.localResolutionSeq bed W hW).pullback ((pieceAmbient 𝕜 E.G).restrictLE hle)
        (isLocalDiffeomorph_restrictLE hle)).eraseEmptyLast.symm.toEquiv.injective).comp
      (AnalyticManifold.BlowUpSequence.stageOfEq (E.localResolutionSeq_of_le bed W hW W' hW'
          hle)).toEquiv.injective)

/-- The lift lies over the open inclusion (`stageMap_last_pullbackLiftLast`,
`stageMap_last_eraseEmptyLast_symm`, `stageMap_last_stageOfEq`). -/
theorem stageMap_last_liftOfLe (hle : W' ≤ W)
    (q : (E.localResolutionSeq bed W' hW').stage (Fin.last _)) :
    (E.localResolutionSeq bed W hW).toSuccession.stageMap (Fin.last _)
        (E.liftOfLe bed W hW W' hW' hle q) =
      (pieceAmbient 𝕜 E.G).restrictLE hle
        ((E.localResolutionSeq bed W' hW').toSuccession.stageMap (Fin.last _) q) := by
  let L := E.localResolutionSeq bed W hW
  let r := (pieceAmbient 𝕜 E.G).restrictLE hle
  let pb := L.pullback r (isLocalDiffeomorph_restrictLE hle)
  let e := E.localResolutionSeq_of_le bed W hW W' hW' hle
  change L.toSuccession.stageMap (Fin.last _)
    (L.pullbackLiftLast r (isLocalDiffeomorph_restrictLE hle)
      (pb.eraseEmptyLast.symm (AnalyticManifold.BlowUpSequence.stageOfEq e q))) = _
  rw [AnalyticManifold.BlowUpSequence.stageMap_last_pullbackLiftLast,
      AnalyticManifold.BlowUpSequence.stageMap_last_eraseEmptyLast_symm,
    AnalyticManifold.BlowUpSequence.stageMap_last_stageOfEq]

/-- The range of the lift is the part of the last stage over `W'` (`range_pullbackLiftLast`). -/
theorem range_liftOfLe (hle : W' ≤ W) :
    Set.range (E.liftOfLe bed W hW W' hW' hle) =
      (E.localResolutionSeq bed W hW).toSuccession.stageMap (Fin.last _) ⁻¹'
        Set.range ((pieceAmbient 𝕜 E.G).restrictLE hle) := by
  let L := E.localResolutionSeq bed W hW
  let r := (pieceAmbient 𝕜 E.G).restrictLE hle
  let pb := L.pullback r (isLocalDiffeomorph_restrictLE hle)
  let e := E.localResolutionSeq_of_le bed W hW W' hW' hle
  have hs : Function.Surjective (⇑pb.eraseEmptyLast.symm ∘
      ⇑(AnalyticManifold.BlowUpSequence.stageOfEq e)) :=
    pb.eraseEmptyLast.symm.toEquiv.surjective.comp (AnalyticManifold.BlowUpSequence.stageOfEq
        e).toEquiv.surjective
  change Set.range (⇑(L.pullbackLiftLast r (isLocalDiffeomorph_restrictLE hle)) ∘
    (⇑pb.eraseEmptyLast.symm ∘ ⇑(AnalyticManifold.BlowUpSequence.stageOfEq e))) = _
  rw [hs.range_comp, AnalyticManifold.BlowUpSequence.range_pullbackLiftLast]

/-- **The final strict transforms correspond under the lift**:
`strictTransformSubspaceSeq_last_pullback_eraseEmpty'` with
`strictTransformSubspaceSeq_last_stageOfEq` and `𝓘|W' = (𝓘|W).comap (W' ↪ W)` (`pullback_comp`). -/
theorem strictTransformSubspaceSeq_last_liftOfLe (hle : W' ≤ W) :
    (E.localResolutionSeq bed W' hW').toSuccession.strictTransformSubspaceSeq (E.restrictedIdeal W')
        (Fin.last _) =
      ((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq (E.restrictedIdeal W)
        (Fin.last _)).pullback (E.liftOfLe bed W hW W' hW' hle)
        (E.liftOfLe bed W hW W' hW' hle).contMDiff :=
  -- the restricted ideal over `W'` is the pull-back of the one over `W` along the inclusion
  have hI' : E.restrictedIdeal W' =
      (E.restrictedIdeal W).pullback _ ((pieceAmbient 𝕜 E.G).restrictLE hle).contMDiff :=
    ((IdealSheaf.pullback_pullback E.ideal ⇑(AnalyticManifold.inclusion _ W)
        (AnalyticManifold.inclusion _ W).contMDiff
        ⇑((pieceAmbient 𝕜 E.G).restrictLE hle)
        ((pieceAmbient 𝕜 E.G).restrictLE hle).contMDiff).trans
      (IdealSheaf.pullback_congr E.ideal _
          (AnalyticManifold.inclusion _ W').contMDiff
        (funext fun _ => rfl))).symm
  AnalyticManifold.BlowUpSequence.strictTransformSubspaceSeq_last_of_eq_pullback_eraseEmpty _ _ _ _
    (E.localResolutionSeq_of_le bed W hW W' hW' hle) _ _ hI'

/-- **The local resolution over `W'` maps into the local resolution over `W`** ([Kol07, Theorem
36, proof]): the morphism of closed subspaces induced along the lift by
`strictTransformSubspaceSeq_last_liftOfLe`. -/
def localResolutionHomOfLe (hle : W' ≤ W) :
    E.localResolution bed W' hW' ⟶ E.localResolution bed W hW :=
  IdealSheaf.homOfPullbackEq (E.liftOfLe bed W hW W' hW' hle)
    (E.liftOfLe bed W hW W' hW' hle).contMDiff
    (E.strictTransformSubspaceSeq_last_liftOfLe bed W hW W' hW' hle)

/-- It is an open immersion (`isOpenImmersion_homOfPullbackEq_of_injective` at the injective local
isomorphism `liftOfLe`). -/
theorem isOpenImmersion_localResolutionHomOfLe (hle : W' ≤ W) :
    LocallyRingedSpace.IsOpenImmersion (E.localResolutionHomOfLe bed W hW W' hW' hle).1 :=
  isOpenImmersion_homOfPullbackEq_of_injective _ (E.isLocalDiffeomorph_liftOfLe bed W hW W' hW' hle)
    (E.injective_liftOfLe bed W hW W' hW' hle) _

local notation "𝕊" => AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))

/-- **It lies over the piece**: `Π_W ∘ χ = Π_{W'}` — `Hom.ext_of_comp_quotientι` on the square of
the composites through `localResolutionMap_comp_ι`, `stageMap_last_liftOfLe`,
`homOfPullbackEq_comp_toAnalyticSpaceι` and `inclusion W ∘ restrictLE = inclusion W'`. -/
theorem localResolutionToPiece_comp_localResolutionHomOfLe (hle : W' ≤ W) :
    E.localResolutionHomOfLe bed W hW W' hW' hle ≫ E.localResolutionToPiece bed W hW =
      E.localResolutionToPiece bed W' hW' := by
  -- the identities of the layer, on the raw terms (no `set` variable enters an elaboration)
  have e0 : E.embInv ⊚ E.emb = 𝟙 _ := E.embInv_comp_emb
  have e1 := E.toAnalyticSpaceι_comp_restrictedIdealHom W
  have e1' := E.toAnalyticSpaceι_comp_restrictedIdealHom W'
  have e2 := E.localResolutionMap_comp_ι bed W hW
  have e2' := E.localResolutionMap_comp_ι bed W' hW'
  have e3 : ((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq
        (E.restrictedIdeal W) (Fin.last _)).toAnalyticSpaceι ⊚
        E.localResolutionHomOfLe bed W hW W' hW' hle =
      (show 𝕊 ((E.localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
          𝕊 ((E.localResolutionSeq bed W hW).stage (Fin.last _)) from
        ofManifoldHom (E.liftOfLe bed W hW W' hW' hle) (E.liftOfLe bed W hW W' hW' hle).contMDiff) ⊚
      ((E.localResolutionSeq bed W' hW').toSuccession.strictTransformSubspaceSeq
        (E.restrictedIdeal W') (Fin.last _)).toAnalyticSpaceι :=
    homOfPullbackEq_comp_toAnalyticSpaceι _ _
      (E.strictTransformSubspaceSeq_last_liftOfLe bed W hW W' hW' hle)
  -- the square of the ambient maps: `incl W ∘ σ_W ∘ lift = incl W' ∘ σ_{W'}`
  have hfun : ⇑(AnalyticManifold.inclusion _ W) ∘
        (⇑(E.localResolutionSeq bed W hW).toSuccession.composite ∘
          ⇑(E.liftOfLe bed W hW W' hW' hle)) =
      ⇑(AnalyticManifold.inclusion _ W') ∘
        ⇑(E.localResolutionSeq bed W' hW').toSuccession.composite :=
    funext fun q => congrArg Subtype.val (E.stageMap_last_liftOfLe bed W hW W' hW' hle q)
  have s1 : AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (E.localResolutionSeq bed W hW).toSuccession.composite ⊚
        (show 𝕊 ((E.localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
            𝕊 ((E.localResolutionSeq bed W hW).stage (Fin.last _)) from
        ofManifoldHom (E.liftOfLe bed W hW W' hW' hle) (E.liftOfLe bed W hW W' hW' hle).contMDiff) =
      (show 𝕊 ((E.localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
          𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict W) from
        ofManifoldHom (⇑(E.localResolutionSeq bed W hW).toSuccession.composite ∘
          ⇑(E.liftOfLe bed W hW W' hW' hle))
        ((E.localResolutionSeq bed W hW).toSuccession.composite.contMDiff.comp
          (E.liftOfLe bed W hW W' hW' hle).contMDiff)) :=
    (ofManifoldHom_comp _ _ _ _).symm
  have s2 : (show 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict W) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (AnalyticManifold.inclusion _ W)
          (AnalyticManifold.inclusion _ W).contMDiff) ⊚
        (show 𝕊 ((E.localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
            𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict W) from
        ofManifoldHom (⇑(E.localResolutionSeq bed W hW).toSuccession.composite ∘
            ⇑(E.liftOfLe bed W hW W' hW' hle))
          ((E.localResolutionSeq bed W hW).toSuccession.composite.contMDiff.comp
            (E.liftOfLe bed W hW W' hW' hle).contMDiff)) =
      (show 𝕊 ((E.localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
          𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (⇑(AnalyticManifold.inclusion _ W) ∘
          (⇑(E.localResolutionSeq bed W hW).toSuccession.composite ∘
            ⇑(E.liftOfLe bed W hW W' hW' hle)))
        ((AnalyticManifold.inclusion _ W).contMDiff.comp
          ((E.localResolutionSeq bed W hW).toSuccession.composite.contMDiff.comp
            (E.liftOfLe bed W hW W' hW' hle).contMDiff))) :=
    (ofManifoldHom_comp _ _ _ _).symm
  have s3 : (show 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict W') ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (AnalyticManifold.inclusion _ W')
          (AnalyticManifold.inclusion _ W').contMDiff) ⊚
        AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (E.localResolutionSeq bed W' hW').toSuccession.composite =
      (show 𝕊 ((E.localResolutionSeq bed W' hW').stage (Fin.last _)) ⟶
          𝕊 (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (⇑(AnalyticManifold.inclusion _ W') ∘
          ⇑(E.localResolutionSeq bed W' hW').toSuccession.composite)
        ((AnalyticManifold.inclusion _ W').contMDiff.comp
          (E.localResolutionSeq bed W' hW').toSuccession.composite.contMDiff)) :=
    (ofManifoldHom_comp _ _ _ _).symm
  have e4 := (congrArg
      (fun k => (show 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict W) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G)
      from
        ofManifoldHom (AnalyticManifold.inclusion _ W)
          (AnalyticManifold.inclusion _ W).contMDiff) ⊚ k) s1).trans
    (s2.trans ((ofManifoldHom_congr hfun _).trans s3.symm))
  -- the abbreviations
  let χ := E.localResolutionHomOfLe bed W hW W' hW' hle
  let L := E.localResolutionSeq bed W hW
  let L' := E.localResolutionSeq bed W' hW'
  let qW := (E.restrictedIdeal W).toAnalyticSpaceι
  let qW' := (E.restrictedIdeal W').toAnalyticSpaceι
  let ιW :
      E.localResolution bed W hW ⟶ 𝕊 (L.stage (Fin.last _)) :=
    (L.toSuccession.strictTransformSubspaceSeq (E.restrictedIdeal W)
      (Fin.last _)).toAnalyticSpaceι
  let ιW' : E.localResolution bed W' hW' ⟶ 𝕊 (L'.stage (Fin.last _)) :=
    (L'.toSuccession.strictTransformSubspaceSeq (E.restrictedIdeal W')
      (Fin.last _)).toAnalyticSpaceι
  let PW := E.localResolutionMap bed W hW
  let PW' := E.localResolutionMap bed W' hW'
  let ρW := E.restrictedIdealHom W
  let ρW' := E.restrictedIdealHom W'
  let SpιW : 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict W) ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) :=
    ofManifoldHom (AnalyticManifold.inclusion _ W)
      (AnalyticManifold.inclusion _ W).contMDiff
  let SpιW' : 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict W') ⟶ 𝕊 (pieceAmbient.{u} 𝕜 E.G) :=
    ofManifoldHom (AnalyticManifold.inclusion _ W')
      (AnalyticManifold.inclusion _ W').contMDiff
  let SpcW : 𝕊 (L.stage (Fin.last _)) ⟶ 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict W) :=
    AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      L.toSuccession.composite
  let SpcW' : 𝕊 (L'.stage (Fin.last _)) ⟶ 𝕊 ((pieceAmbient.{u} 𝕜 E.G).restrict W') :=
    AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      L'.toSuccession.composite
  let SpL :
      𝕊 (L'.stage (Fin.last _)) ⟶ 𝕊 (L.stage (Fin.last _)) :=
    ofManifoldHom (E.liftOfLe bed W hW W' hW' hle) (E.liftOfLe bed W hW W' hW' hle).contMDiff
  -- the two composites into `Sp(G)/𝓘` agree after `ι`
  have key :
      E.ideal.toAnalyticSpaceι ⊚ (ρW ⊚ (PW ⊚ χ)) = E.ideal.toAnalyticSpaceι ⊚ (ρW' ⊚ PW') :=
    calc E.ideal.toAnalyticSpaceι ⊚ (ρW ⊚ (PW ⊚ χ))
        = (E.ideal.toAnalyticSpaceι ⊚ ρW) ⊚ (PW ⊚ χ) := Category.assoc _ _ _
      _ = (SpιW ⊚ qW) ⊚ (PW ⊚ χ) := congrArg (fun k => k ⊚ (PW ⊚ χ)) e1
      _ = SpιW ⊚ (qW ⊚ (PW ⊚ χ)) := (Category.assoc _ _ _).symm
      _ = SpιW ⊚ ((qW ⊚ PW) ⊚ χ) := congrArg (fun k => SpιW ⊚ k) (Category.assoc _ _ _)
      _ = SpιW ⊚ ((SpcW ⊚ ιW) ⊚ χ) := congrArg (fun k => SpιW ⊚ (k ⊚ χ)) e2
      _ = SpιW ⊚ (SpcW ⊚ (ιW ⊚ χ)) := congrArg (fun k => SpιW ⊚ k) (Category.assoc _ _ _).symm
      _ = SpιW ⊚ (SpcW ⊚ (SpL ⊚ ιW')) := congrArg (fun k => SpιW ⊚ (SpcW ⊚ k)) e3
      _ = SpιW ⊚ ((SpcW ⊚ SpL) ⊚ ιW') := congrArg (fun k => SpιW ⊚ k) (Category.assoc _ _ _)
      _ = (SpιW ⊚ (SpcW ⊚ SpL)) ⊚ ιW' := Category.assoc _ _ _
      _ = (SpιW' ⊚ SpcW') ⊚ ιW' := congrArg (fun k => k ⊚ ιW') e4
      _ = SpιW' ⊚ (SpcW' ⊚ ιW') := (Category.assoc _ _ _).symm
      _ = SpιW' ⊚ (qW' ⊚ PW') := congrArg (fun k => SpιW' ⊚ k) e2'.symm
      _ = (SpιW' ⊚ qW') ⊚ PW' := Category.assoc _ _ _
      _ = (E.ideal.toAnalyticSpaceι ⊚ ρW') ⊚ PW' := congrArg (fun k => k ⊚ PW') e1'.symm
      _ = E.ideal.toAnalyticSpaceι ⊚ (ρW' ⊚ PW') := (Category.assoc _ _ _).symm
  have key' : ρW ⊚ (PW ⊚ χ) = ρW' ⊚ PW' :=
    Hom.ext_of_comp_quotientι (X := ofManifold 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 E.G)) E.ideal key
  change (E.embInv ⊚ (ρW ⊚ PW)) ⊚ χ = E.embInv ⊚ (ρW' ⊚ PW')
  calc (E.embInv ⊚ (ρW ⊚ PW)) ⊚ χ
      = E.embInv ⊚ ((ρW ⊚ PW) ⊚ χ) := (Category.assoc _ _ _).symm
    _ = E.embInv ⊚ (ρW ⊚ (PW ⊚ χ)) := congrArg (fun k => E.embInv ⊚ k) (Category.assoc _ _ _).symm
    _ = E.embInv ⊚ (ρW' ⊚ PW') := congrArg (fun k => E.embInv ⊚ k) key'

/-- **Its range covers the part over `N`** for `N ⊆ embPreimage W'`: a point of `Ỹ(W)` over `N`
lies over `W'` (`range_toFun_homOfPullbackEq`, `range_liftOfLe`, the ambient point of `Π_W q` is
the composite of `q`). -/
theorem preimage_subset_range_localResolutionHomOfLe (hle : W' ≤ W) (N : Set (X.restrictSet V))
    (hN : N ⊆ E.embPreimage W') :
    E.localResolutionToPiece bed W hW ⁻¹' N ⊆
      Set.range (E.localResolutionHomOfLe bed W hW W' hW' hle) := by
  intro q hq
  have hq' :
      E.ambientPoint
          ((E.localResolutionToPiece bed W hW)
      q) ∈ W' := hN hq
  change q ∈ Set.range ⇑(IdealSheaf.homOfPullbackEq (E.liftOfLe bed W hW W' hW' hle)
      (E.liftOfLe bed W hW W' hW' hle).contMDiff (E.strictTransformSubspaceSeq_last_liftOfLe bed W
      hW W' hW' hle))
  rw [range_toFun_homOfPullbackEq _ (E.isLocalDiffeomorph_liftOfLe bed W hW W' hW' hle),
    E.range_liftOfLe bed W hW W' hW' hle, range_restrictLE]
  -- the ambient point of `Π_W q` is the composite of the point of `q`
  have hE : IsIso E.emb := E.emb_isIso
  have h1 : ∀ z, E.emb
      ((inv E.emb (I := hE)) z) = z := fun z =>
    congrArg
        (fun k => k z)
      (IsIso.inv_hom_id E.emb (I := hE))
  have h2 :
      E.ambientPoint
          ((E.localResolutionToPiece bed W hW)
      q) = (((E.restrictedIdeal W).toAnalyticSpaceι
        (E.localResolutionMap bed W hW q)).1 :
          pieceAmbient.{u} 𝕜 E.G) := by
    change E.ambientPoint ((inv E.emb (I := hE))
      ((E.restrictedIdealHom W)
        (E.localResolutionMap bed W hW q))) = _
    unfold ambientPoint
    rw [h1, toFun_toAnalyticSpaceι_restrictedIdealHom]
  have h3 : (E.restrictedIdeal W).toAnalyticSpaceι
      (E.localResolutionMap bed W hW q) =
        (E.localResolutionSeq bed W hW).toSuccession.stageMap (Fin.last _)
          (((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq
              (E.restrictedIdeal W) (Fin.last _)).toAnalyticSpaceι q) :=
    congrArg
        (fun k => k q)
      (E.localResolutionMap_comp_ι bed W hW)
  change ((E.localResolutionSeq bed W hW).toSuccession.stageMap (Fin.last _)
    (((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq
        (E.restrictedIdeal W) (Fin.last _)).toAnalyticSpaceι q)).1 ∈
    (W' : Set (pieceAmbient 𝕜 E.G))
  rw [← h3, ← h2]
  exact hq'

/-- **Restriction to a smaller open** (the value over `W` read over `W' ⊆ W`, [Kol07, Theorem 36,
proof]; the compatibility `compat` of the family, [Wlo09, Theorem 2.0.2(5)]): for relatively
compact opens `W' ≤ W` of the ambient and an open `N` of the piece lying over `W'`, the local
resolutions over `W` and over `W'` are isomorphic over `N` compatibly with the maps to the piece —
`exists_restrictSet_isIso_of_comp_eq_of_isOpenImmersion` at the open immersion
`localResolutionHomOfLe` over the piece whose range covers the part over `N`, then
`exists_restrictSet_isIso_symm` for the orientation. -/
theorem exists_restrictSet_isIso_localResolution_of_le (bed : BEDanFamStar.{u} 𝕜)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))
    (W' : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 E.G)))) (hle : W' ≤ W)
    (N : Set (X.restrictSet V)) (hNo : IsOpen N) (hN : N ⊆ E.embPreimage W') :
    ∃ ψ : (E.localResolution bed W hW).restrictSet (E.localResolutionToPiece bed W hW ⁻¹'
        N) ⟶ (E.localResolution bed W' hW').restrictSet (E.localResolutionToPiece bed W' hW' ⁻¹' N),
      IsIso ψ ∧
      ψ ≫ (E.localResolutionToPiece bed W' hW').restrictSet N =
        (E.localResolutionToPiece bed W hW).restrictSet N :=
  AnalyticSpace.exists_restrictSet_isIso_symm _ _ N
    (AnalyticSpace.exists_restrictSet_isIso_of_comp_eq_of_isOpenImmersion
      (E.localResolutionHomOfLe bed W hW W' hW' hle)
      (E.isOpenImmersion_localResolutionHomOfLe bed W hW W' hW' hle)
      (E.localResolutionToPiece bed W' hW') (E.localResolutionToPiece bed W hW)
      (E.localResolutionToPiece_comp_localResolutionHomOfLe bed W hW W' hW' hle) N hNo
      (E.preimage_subset_range_localResolutionHomOfLe bed W hW W' hW' hle N hN))

end PieceEmbedding

end Hironaka.Manifold

end
