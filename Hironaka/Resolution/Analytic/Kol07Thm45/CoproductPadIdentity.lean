/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductExceptionalFamily
public import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientLift
public import Hironaka.Resolution.Analytic.Kol07Thm45.PadSliceDiffeomorph
public import Hironaka.Resolution.Analytic.Kol07Thm45.SigmaSubmanifold
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.StrictSubspaceSeqCompat
import Hironaka.Resolution.Analytic.Kol07Thm45.ExceptionalFamilyGlue
import Hironaka.Resolution.Analytic.Kol07Thm45.ExceptionalTransitionRestrict
import Hironaka.Resolution.Analytic.Kol07Thm45.HomOfPullbackEqCalculus
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionPad
import Hironaka.Resolution.Analytic.Kol07Thm45.PushforwardFamily
import Hironaka.Resolution.Analytic.Kol07Thm45.RestrictInclusion
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Hironaka.Resolution.Analytic.Principalization.ClauseOne
import Hironaka.Resolution.Analytic.Restrict.StrictSubspaceSeqTransport
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductSumData

/-!
# The padding identity of a datum at the coproduct

The padding comparison at the level of a whole datum: Kollár's commutation of the functor with
closed embeddings, `j^* B(X, I_X, E) = B(Y, I_Y, E|_Y)` [Kol07, 34.4], read at the coproduct slice
(compare [Wlo09, §7.1]). A local embedding datum `D` padded along a coordinate embedding
`σ : Fin n ↪ Fin n′` (`padAlongData`: every piece embedding padded by `PieceEmbedding.padAlong σ`)
has the coproduct local resolution, labels and members of `D` — read over the padded reading opens
`Wp` and the reading opens they carry along the slice (`padPreimageOpens`):

* the statement: `padAlongData`, `padPreimageOpens`, `isCompact_closure_padPreimageOpens`,
  `PadIdentityOn` — an order isomorphism `o` of the label sets, an isomorphism `ψ` of the
  coproduct local resolutions with `comap ψ (members (o σp)) = members⁺ σp` for every label, and on
  every piece an isomorphism over the piece;
* the cast leg with an order isomorphism:
  `BlowUpSequence.exists_diffeomorph_last_of_pullback_bijective_iso` (list level) and
  `BEDanFamStar.exists_diffeomorph_last_of_cast_iso` (functor level), with an order ISOMORPHISM
  of the label sets: a diffeomorphism pulls back no empty centre, so the erasure of empty blow-ups
  is the identity (`eraseEmpty_pullback_of_surjective`) and the last-stage map is
  `pullbackLiftLastDiffeomorphOfBijective`;
* the coproduct slice `S* := ⋃ᵢ sigmaMk⁺ i '' padSlice σ Gᵢ` (`sigmaPadSlice`,
  `isClosedSubmanifold_sigmaPadSlice`); `sigmaPadSliceDiffeomorph`: the datum's coproduct ambient
  IS the slice, across the models `Fin n` and `Fin (n′ − (n′ − n))` (the sigma of the per-piece
  `padExtDiffeomorph` followed by `sigmaSubmanifoldDiffeomorph` of
  `Hironaka/Resolution/Analytic/Kol07Thm45/SigmaSubmanifold.lean`), with
  `inclusionMap_sigmaPadSliceDiffeomorph`; `pullback_inclusionMap_sigmaPadSlice`: the padded ideal
  restricted to the slice is the datum's ideal transported (`IdealSheaf.ext_of_comap_sigmaMk`,
  `pullback_inclusionMap_padIdeal` per piece), and `idealSheaf_sigmaPadSlice_le`;
  `preimage_sigmaPadSliceDiffeomorph_preimageOpens_ambImage`: the datum's reading open is the
  trace of the padded one on the slice; the restricted slice map `padRestrictMap : N|U → N⁺|U⁺`
  (`incl_{S*} ∘ Φ` on the reading opens), analytic (`contMDiff_padRestrictMap`), with
  `I|U = m^*(I⁺|U⁺)` (`restrictOpens_eq_pullback_padRestrictMap`);
* THE CORE `exists_padIdentityCore`: `bed.closedEmbedding` at `(S*, I⁺, J*)` makes the padded run
  the push-forward of the slice run ([Kol07, 34.4]; [Wlo09, Theorem 2.0.2(4)]),
  `exists_closedSubmanifold_last_pushforwardRestrict_boundary` (`LocalResolutionPad.lean`) gives
  the carried slice `S*_r`, `G₁`, the ideal identity, the composite square and the order
  isomorphism `o₁` with the trace identity; the cast leg at `(Φ, I, J*)` gives `G₀` and `ε₀`; then
  `o := o₁.symm.trans ε₀.symm`, `ψ := inv (homOfPullbackEq (incl_{S*_r} ∘ (G₁ ∘ G₀)))` (the two
  isomorphisms of `exists_isIso_localResolution_padAlong`), the member identity in EQUALITY form
  for every label from the ideal-level trace identity
  (`pullback_idealSheaf_inclusionMap_comp_of_hasSncWithProper`, the cast helper at `G₀`) through
  the generic member transport, and `ψ` over the ambients in MORPHISM form —
  `localResolutionMapOn⁺ ∘ ψ⁻¹ = homOfPullbackEq (padRestrictMap) ∘ localResolutionMapOn` (the
  generic quotient square);
* the data exposed as definitions by choice from the core — `padIdentityOrderIso` (`o`),
  `padIdentityIso` (`ψ`) — with `padIdentityIso_isIso`, `comap_padIdentityIso_sigmaMembers`,
  `localResolutionMapOn_comp_inv_padIdentityIso` and its point form
  `localResolutionMapOn_inv_padIdentityIso_apply`, and the ASSEMBLY
  `padIdentityOn_of_forall_piece`: the padding identity from the core and the piece clause stated
  against the NAMED `ψ` (`CoproductPadIdentityPiece.lean` proves that clause).

Nothing here is new mathematics: the argument is the padding leg of the comparison of two
embeddings (`LocalResolutionPad.lean`) at the coproduct slice, with an order isomorphism where the
piece case had an embedding. The generic `homOfPullbackEq` tools live in
`HomOfPullbackEqCalculus.lean`.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set AnalyticManifold AnalyticSpace
open KLocallyRingedSpace Hironaka.Manifold BlowUpSequence
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-! ### The cast leg with an order ISOMORPHISM (a diffeomorphism erases no centre) -/

section CastIso

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The list-level cast leg, for the plain pull-back along a BIJECTIVE local isomorphism: the
last-stage diffeomorphism is `pullbackLiftLastDiffeomorphOfBijective`, the strict transforms
correspond (`strictTransformSubspaceSeq_last_pullbackLiftLast`), and the last boundary families
correspond through an order ISOMORPHISM (`totalTransformSeqFrom_last_pullbackLiftLast` at the
empty family, `exists_orderIso_of_eq`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.exists_diffeomorph_last_of_pullback_bijective_iso
    {N N' : AnalyticManifold.{u} 𝕜 E} (g : N' → N) {U : Opens N}
        {U' : Opens N'}
    (L : BlowUpSequence ψ₀ (N.restrict U))
        (h : AnalyticMap (N'.restrict U') (N.restrict U))
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hb : Function.Bijective h)
    (hsq : ∀ p, N.inclusion U (h p) = g (N'.inclusion U' p))
    (J : AnalyticManifold.IdealSheaf (N.restrict U))
        (J' : AnalyticManifold.IdealSheaf (N'.restrict U'))
    (hJ' : J' = J.pullback h h.contMDiff) :
    ∃ G : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ((L.pullback h hh).stage (Fin.last _))
        (L.stage (Fin.last _)) ω,
      (∀ p, N.inclusion U (L.toSuccession.composite (G p)) =
        g (N'.inclusion U' ((L.pullback h hh).toSuccession.composite p))) ∧
      (L.pullback h hh).toSuccession.strictTransformSubspaceSeq J' (Fin.last _) =
        (L.toSuccession.strictTransformSubspaceSeq J (Fin.last _)).pullback ⇑G G.contMDiff ∧
      ∃ ε : ((L.pullback h hh).toSuccession.totalTransformSeq (Fin.last _)).ι ≃o
          (L.toSuccession.totalTransformSeq (Fin.last _)).ι,
        ∀ i, ⇑G ⁻¹' (L.toSuccession.totalTransformSeq (Fin.last _)).hyp (ε i) =
          ((L.pullback h hh).toSuccession.totalTransformSeq (Fin.last _)).hyp i := by
  have := finiteDimensional_of_chartIso ψ₀
  refine ⟨L.pullbackLiftLastDiffeomorphOfBijective h hh hb, fun p => ?_, ?_, ?_⟩
  · rw [coe_pullbackLiftLastDiffeomorphOfBijective, FiniteSuccession.composite_eq,
      FiniteSuccession.composite_eq, stageMap_last_pullbackLiftLast, hsq]
  · subst hJ'
    rw [strictTransformSubspaceSeq_last_pullbackLiftLast L h hh hb.2]
    exact IdealSheaf.pullback_congr _ _ _ rfl
  · have hcast : (L.pullback h hh).toSuccession.totalTransformSeqFrom
        ((HypersurfaceFamily.empty _).comap ⇑h) (Fin.last _) =
        (L.pullback h hh).toSuccession.totalTransformSeq (Fin.last _) := by
      rw [HypersurfaceFamily.empty_comap]
      rfl
    have e : (L.pullback h hh).toSuccession.totalTransformSeq (Fin.last _) =
        (L.toSuccession.totalTransformSeq (Fin.last _)).comap ⇑(L.pullbackLiftLast h hh) :=
      hcast.symm.trans (totalTransformSeqFrom_last_pullbackLiftLast L h hh
        (HypersurfaceFamily.empty _))
    obtain ⟨o, ho⟩ := HypersurfaceFamily.exists_orderIso_of_eq e
    refine ⟨o, fun i => ?_⟩
    rw [coe_pullbackLiftLastDiffeomorphOfBijective]
    exact (ho i).symm

end CastIso

/-- The functor-level cast leg, with an order ISOMORPHISM of the label sets: along a
DIFFEOMORPHISM `g` (a surjective local isomorphism) the pulled-back list has no empty centre
(`noEmptyCenters_pullback_of_surjective`), so the erasure of empty blow-ups in the functor's value
is the identity (`eraseEmpty_pullback_of_surjective`) and the list-level leg applies. -/
theorem BEDanFamStar.exists_diffeomorph_last_of_cast_iso (bed : BEDanFamStar.{u} 𝕜)
    (hcomm : ∀ m : ℕ, (bed.fam m).CommutesWithLocalIsos) {k n : ℕ} (hk : k = n)
    {N : AnalyticManifold.{u} 𝕜 (Fin k → 𝕜)}
    {N' : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (g : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜) N' N ω)
    (I : AnalyticManifold.IdealSheaf N)
        (hI : I.IsNonzeroEverywhere)
    (I' : AnalyticManifold.IdealSheaf N')
        (hI' : I'.IsNonzeroEverywhere)
    (hII' : I' = I.pullback ⇑g g.contMDiff)
    (hT : DomBEDan 𝕜 ⟨I, hI, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩)
    (hT' : DomBEDan 𝕜 ⟨I', hI', HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩)
    (U : Opens N) (hU : IsCompact (closure (U : Set N))) (U' : Opens N')
    (hU' : IsCompact (closure (U' : Set N'))) (hUU' : (U' : Set N') = ⇑g ⁻¹' (U : Set N)) :
    ∃ G : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜)
        ((((bed.fam n).fam _ hT').seqOn U' hU').stage (Fin.last _))
        ((((bed.fam k).fam _ hT).seqOn U hU).stage (Fin.last _)) ω,
      (∀ p, N.inclusion U ((((bed.fam k).fam _ hT).seqOn U hU).toSuccession.composite (G p)) =
        g (N'.inclusion U' ((((bed.fam n).fam _ hT').seqOn U' hU').toSuccession.composite p))) ∧
      (((bed.fam n).fam _ hT').seqOn U' hU').toSuccession.strictTransformSubspaceSeq
          (I'.restrict U') (Fin.last _) =
        ((((bed.fam k).fam _ hT).seqOn U hU).toSuccession.strictTransformSubspaceSeq
          (I.restrict U) (Fin.last _)).pullback ⇑G G.contMDiff ∧
      ∃ ε : ((((bed.fam n).fam _ hT').seqOn U' hU').toSuccession.totalTransformSeq
            (Fin.last _)).ι ≃o
          ((((bed.fam k).fam _ hT).seqOn U hU).toSuccession.totalTransformSeq (Fin.last _)).ι,
        ∀ i, ⇑G ⁻¹' ((((bed.fam k).fam _ hT).seqOn U hU).toSuccession.totalTransformSeq
            (Fin.last _)).hyp (ε i) =
          ((((bed.fam n).fam _ hT').seqOn U' hU').toSuccession.totalTransformSeq
            (Fin.last _)).hyp i := by
  subst hk
  have himg : AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph U' = U := by
    ext x
    change x ∈ ⇑g '' (U' : Set N') ↔ x ∈ (U : Set N)
    rw [hUU', Set.image_preimage_eq _ fun y => ⟨g.symm y, g.apply_symm_apply y⟩]
  have h4 := hcomm _ ⟨I, hI, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩
    ⟨I', hI', HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩
    (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph
    ⟨hII', (HypersurfaceFamily.empty_comap ⇑g).symm⟩ hT hT' U' hU'
  obtain rfl := himg.symm
  have hsurj : Function.Surjective (AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap g) U'
      (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph U')
      Set.Subset.rfl) :=
    AnalyticMap.surjective_restrictMap (g := Diffeomorph.toAnalyticMap g) rfl
  have h5 : ((bed.fam _).fam _ hT').seqOn U' hU' =
      (((bed.fam _).fam _ hT).seqOn
        (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph U')
        (AnalyticMap.isCompact_closure_image _ hU')).pullback
        (AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap g) U'
          (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph U')
          Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap g.isLocalDiffeomorph U' _ Set.Subset.rfl) :=
    h4.trans (eraseEmpty_pullback_of_surjective _
      (((bed.fam _).fam _ hT).noEmptyCenters _ _) _ _ hsurj)
  clear h4
  generalize hL' : ((bed.fam _).fam _ hT').seqOn U' hU' = L' at h5 ⊢
  subst h5
  have hinj : Function.Injective (AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap g) U'
      (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph U')
      Set.Subset.rfl) := fun p q hpq =>
    Subtype.ext (g.injective (congrArg Subtype.val hpq))
  have hJ' : I'.restrict U' = Manifold.IdealSheaf.pullback _ (AnalyticMap.restrictMap
      (Diffeomorph.toAnalyticMap g) U'
        (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph U')
        Set.Subset.rfl).contMDiff
      (I.restrict (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap g)
        g.isLocalDiffeomorph U')) := by
    dsimp only
        [IdealSheaf.restrict]
    rw [IdealSheaf.pullback_pullback, hII', IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr I _ _
      (funext fun p => (AnalyticMap.restrictMap_apply (Diffeomorph.toAnalyticMap g) U' _
        Set.Subset.rfl p).symm)
  exact exists_diffeomorph_last_of_pullback_bijective_iso ⇑g _ _ _ ⟨hinj, hsurj⟩
    (fun p => AnalyticMap.restrictMap_apply _ _ _ _ p) _ _ hJ'

namespace LocalEmbeddingData

open _root_.Manifold

variable {X : AnalyticSpace.{u} 𝕜}

section Pad

variable {U : Set X} (D : LocalEmbeddingData 𝕜 X U) {n' : ℕ} (σ : Fin D.n ↪ Fin n')

/-- **The datum padded along a coordinate embedding** — every piece embedding padded by
`PieceEmbedding.padAlong σ`; `padLeftData`/`padRightData` (`CoproductSumData.lean`) are its
instances by `rfl`. -/
abbrev padAlongData : LocalEmbeddingData 𝕜 X U where
  n := n'
  ι := D.ι
  finite := D.finite
  piece := D.piece
  isOpen_piece := D.isOpen_piece
  inner := D.inner
  isOpen_inner := D.isOpen_inner
  isCompact_closure_inner := D.isCompact_closure_inner
  closure_inner_subset := D.closure_inner_subset
  subset_iUnion_inner := D.subset_iUnion_inner
  embedding := fun i => (D.embedding i).padAlong σ

example (m : ℕ) : D.padLeftData m = D.padAlongData (Fin.castAddEmb m) := rfl
example (m : ℕ) : D.padRightData m = D.padAlongData (Fin.natAddEmb m) := rfl

variable (Wp : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G))
  (hWp : ∀ i, IsCompact (closure (Wp i : Set (pieceAmbient.{u} 𝕜
    ((D.padAlongData σ).embedding i).G))))

/-- The reading opens of the datum carried by the padded reading opens along the slice
(`preimageOpens (padExt σ G)`). -/
def padPreimageOpens : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G) :=
  fun i => preimageOpens (padExt σ (D.embedding i).G) (contMDiff_padExt σ (D.embedding i).G) (Wp i)

include hWp in
/-- The reading opens read back through the padding slice are relatively compact
(`isCompact_closure_preimage_padExt`). -/
theorem isCompact_closure_padPreimageOpens :
    ∀ i, IsCompact (closure (D.padPreimageOpens σ Wp i : Set (pieceAmbient.{u} 𝕜
      (D.embedding i).G))) :=
  fun i => isCompact_closure_preimage_padExt σ (D.embedding i).G (Wp i) (hWp i)

variable (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)

/-- **The padding identity of a datum at the coproduct** ([Kol07, 34.4] at the coproduct slice):
an order isomorphism of the padded datum's label set onto the datum's (the padded run
is the run of the coproduct slice, stage by stage), an isomorphism of the coproduct local
resolutions carrying the datum's member of label `o σp` to the padded datum's member of label `σp`,
restricting on every piece to an isomorphism of the piece's local resolutions over the piece. -/
def PadIdentityOn : Prop :=
  ∃ (o : (D.padAlongData σ).sigmaIndex bed Wp hWp ≃o
        D.sigmaIndex bed (D.padPreimageOpens σ Wp) (D.isCompact_closure_padPreimageOpens σ Wp hWp))
    (ψ : bed.localResolutionOn (D.padAlongData σ).sigmaTriple
        (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
        ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp) ⟶
        bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple
        (D.ambImage (D.padPreimageOpens σ Wp))
        (D.isCompact_closure_ambImage _ (D.isCompact_closure_padPreimageOpens σ Wp hWp))),
    IsIso ψ ∧
    (∀ σp, QuotientSpace.comap ψ.1
        (D.sigmaMembers bed (D.padPreimageOpens σ Wp)
          (D.isCompact_closure_padPreimageOpens σ Wp hWp) hbed (o σp)) =
      (D.padAlongData σ).sigmaMembers bed Wp hWp hbed σp) ∧
    ∀ i, ∃ ψᵢ : ((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp i) ⟶
        (D.embedding i).localResolution bed (D.padPreimageOpens σ Wp i)
        (D.isCompact_closure_padPreimageOpens σ Wp hWp i),
      IsIso ψᵢ ∧
      ψᵢ ≫ (D.embedding i).localResolutionToPiece bed (D.padPreimageOpens σ Wp i)
          (D.isCompact_closure_padPreimageOpens σ Wp hWp i) =
        ((D.padAlongData σ).embedding i).localResolutionToPiece bed (Wp i) (hWp i) ∧
      (D.padAlongData σ).resIn bed Wp hWp hbed i ≫ ψ =
        ψᵢ ≫ D.resIn bed (D.padPreimageOpens σ Wp)
          (D.isCompact_closure_padPreimageOpens σ Wp hWp) hbed i

/-! #### The coproduct slice of the padding and its identification with the datum's ambient -/

/-- The coproduct slice `S* = ⋃ᵢ sigmaMk⁺ i '' padSlice σ Gᵢ` inside the padded coproduct
ambient. -/
def sigmaPadSlice : Set (D.padAlongData σ).sigmaAmbient :=
  ⋃ i, ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i) ''
    padSlice σ (D.embedding i).G

/-- It is a closed submanifold of codimension `n′ − n` (`isClosedSubmanifold_sigmaUnion` at the pad
slices, `isClosedSubmanifold_padSlice`). -/
theorem isClosedSubmanifold_sigmaPadSlice :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜)) (D.sigmaPadSlice σ)
      (n' - D.n) :=
  isClosedSubmanifold_sigmaUnion fun i => isClosedSubmanifold_padSlice σ (D.embedding i).G

/-- **The datum's coproduct ambient IS the coproduct slice** — across models (`Fin n` against
`Fin (n′ − (n′ − n))`): the sigma of the per-piece `padExtDiffeomorph` followed by
`sigmaSubmanifoldDiffeomorph`. -/
def sigmaPadSliceDiffeomorph :
    Diffeomorph 𝓘(𝕜, Fin D.n → 𝕜) 𝓘(𝕜, Fin (n' - (n' - D.n)) → 𝕜) D.sigmaAmbient
      (D.isClosedSubmanifold_sigmaPadSlice σ).toAnalyticManifold ω :=
  (sigmaMapDiffeomorph fun i => padExtDiffeomorph σ (D.embedding i).G).trans
    (sigmaSubmanifoldDiffeomorph fun i => isClosedSubmanifold_padSlice σ (D.embedding i).G)

/-- On points: `incl_{S*} (Φ (sigmaMk i x)) = sigmaMk⁺ i (padExt σ Gᵢ x)`. -/
theorem inclusionMap_sigmaPadSliceDiffeomorph (i : D.ι) (x : pieceAmbient.{u} 𝕜 (D.embedding i).G) :
    (D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap
        (D.sigmaPadSliceDiffeomorph σ
          (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i x)) =
      sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i
        (padExt σ (D.embedding i).G x) :=
  (congrArg (D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap
      (congrArg
        (sigmaSubmanifoldDiffeomorph fun i => isClosedSubmanifold_padSlice σ (D.embedding i).G)
        (sigmaMapDiffeomorph_mk (fun i => padExtDiffeomorph σ (D.embedding i).G) i x))).trans
    ((inclusionMap_sigmaSubmanifoldDiffeomorph_mk
      (fun i => isClosedSubmanifold_padSlice σ (D.embedding i).G) i _).trans
      (congrArg (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i)
        (inclusionMap_padExtDiffeomorph σ (D.embedding i).G x)))

/-- **The slice ideal is the datum's ideal transported**: the padded coproduct
ideal restricted to the coproduct slice is `D.sigmaTriple.I` pulled back along `Φ⁻¹`
(`IdealSheaf.ext_of_comap_sigmaMk`, `pullback_inclusionMap_padIdeal` per piece). -/
theorem pullback_inclusionMap_sigmaPadSlice :
    (D.padAlongData σ).sigmaTriple.I.pullback ⇑(D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap
        (D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap.contMDiff =
      D.sigmaTriple.I.pullback ⇑(D.sigmaPadSliceDiffeomorph σ).symm
        (D.sigmaPadSliceDiffeomorph σ).symm.contMDiff := by
  set hS := fun i => isClosedSubmanifold_padSlice.{u} σ (D.embedding i).G with hhS
  set Φ₀ := sigmaSubmanifoldDiffeomorph hS with hΦ₀
  set e := fun i => padExtDiffeomorph σ (D.embedding i).G with he
  -- the point identity `Φ.symm (Φ₀ (sigmaMk_sl i p)) = sigmaMk i ((e i).symm p)`
  have hpt : ∀ (i : D.ι) (p : (hS i).toAnalyticManifold),
      (D.sigmaPadSliceDiffeomorph σ).symm (Φ₀ (sigmaMk (fun i => (hS i).toAnalyticManifold) i p)) =
        sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i ((e i).symm p) := by
    intro i p
    have h1 : D.sigmaPadSliceDiffeomorph σ
        (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i ((e i).symm p)) =
        Φ₀ (sigmaMk (fun i => (hS i).toAnalyticManifold) i p) := by
      change Φ₀ (sigmaMapDiffeomorph e (sigmaMk _ i ((e i).symm p))) = _
      rw [sigmaMapDiffeomorph_mk, Diffeomorph.apply_symm_apply]
    rw [← h1, Diffeomorph.symm_apply_apply]
  -- both sides agree after pulling back along `Φ₀`, summand by summand
  have key : ((D.padAlongData σ).sigmaTriple.I.pullback
        ⇑(D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap
        (D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap.contMDiff).pullback ⇑Φ₀ Φ₀.contMDiff =
      (D.sigmaTriple.I.pullback ⇑(D.sigmaPadSliceDiffeomorph σ).symm
        (D.sigmaPadSliceDiffeomorph σ).symm.contMDiff).pullback ⇑Φ₀ Φ₀.contMDiff := by
    refine IdealSheaf.ext_of_comap_sigmaMk _ _ _ fun i => ?_
    have hL : (⇑(D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap ∘
        (⇑Φ₀ ∘ ⇑(sigmaMk (fun i => (hS i).toAnalyticManifold) i))) =
        ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i) ∘
          ⇑(hS i).inclusionMap :=
      funext fun p => inclusionMap_sigmaSubmanifoldDiffeomorph_mk hS i p
    have hR : (⇑(D.sigmaPadSliceDiffeomorph σ).symm ∘
        (⇑Φ₀ ∘ ⇑(sigmaMk (fun i => (hS i).toAnalyticManifold) i))) =
        ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) ∘ ⇑(e i).symm :=
      funext fun p => hpt i p
    have hIp : (D.padAlongData σ).sigmaTriple.I.pullback
        ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i)
        (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i).contMDiff =
          padIdeal σ (D.embedding i).ideal :=
      IdealSheaf.comap_sigmaMk_sigmaOf _
        (fun i => ((D.padAlongData σ).embedding i).ambientTriple.I) i
    have hI : D.sigmaTriple.I.pullback
        ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)
        (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i).contMDiff =
          (D.embedding i).ideal :=
      IdealSheaf.comap_sigmaMk_sigmaOf _ (fun i => (D.embedding i).ambientTriple.I) i
    -- the left side, summand `i`
    have L1 := IdealSheaf.pullback_pullback ((D.padAlongData σ).sigmaTriple.I.pullback
      ⇑(D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap
      (D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap.contMDiff) ⇑Φ₀ Φ₀.contMDiff
      ⇑(sigmaMk (fun i => (hS i).toAnalyticManifold) i)
      (sigmaMk (fun i => (hS i).toAnalyticManifold) i).contMDiff
    have L2 := IdealSheaf.pullback_pullback (D.padAlongData σ).sigmaTriple.I
      ⇑(D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap
      (D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap.contMDiff
      (⇑Φ₀ ∘ ⇑(sigmaMk (fun i => (hS i).toAnalyticManifold) i))
      (Φ₀.contMDiff.comp (sigmaMk (fun i => (hS i).toAnalyticManifold) i).contMDiff)
    have L3 := IdealSheaf.pullback_congr (D.padAlongData σ).sigmaTriple.I
      ((D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap.contMDiff.comp
        (Φ₀.contMDiff.comp (sigmaMk (fun i => (hS i).toAnalyticManifold) i).contMDiff))
      ((sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i).contMDiff.comp
        (hS i).inclusionMap.contMDiff) hL
    have L4 := (IdealSheaf.pullback_pullback (D.padAlongData σ).sigmaTriple.I
      ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i)
      (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i).contMDiff
      ⇑(hS i).inclusionMap (hS i).inclusionMap.contMDiff).symm
    have L5 := congrArg (fun J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜
      ((D.padAlongData σ).embedding i).G) => J.pullback ⇑(hS i).inclusionMap
        (hS i).inclusionMap.contMDiff) hIp
    have L6 := pullback_inclusionMap_padIdeal σ (D.embedding i).G (D.embedding i).ideal
    -- the right side, summand `i`
    have R1 := IdealSheaf.pullback_pullback (D.sigmaTriple.I.pullback
      ⇑(D.sigmaPadSliceDiffeomorph σ).symm (D.sigmaPadSliceDiffeomorph σ).symm.contMDiff)
      ⇑Φ₀ Φ₀.contMDiff ⇑(sigmaMk (fun i => (hS i).toAnalyticManifold) i)
      (sigmaMk (fun i => (hS i).toAnalyticManifold) i).contMDiff
    have R2 := IdealSheaf.pullback_pullback D.sigmaTriple.I ⇑(D.sigmaPadSliceDiffeomorph σ).symm
      (D.sigmaPadSliceDiffeomorph σ).symm.contMDiff
      (⇑Φ₀ ∘ ⇑(sigmaMk (fun i => (hS i).toAnalyticManifold) i))
      (Φ₀.contMDiff.comp (sigmaMk (fun i => (hS i).toAnalyticManifold) i).contMDiff)
    have R3 := IdealSheaf.pullback_congr D.sigmaTriple.I
      ((D.sigmaPadSliceDiffeomorph σ).symm.contMDiff.comp
        (Φ₀.contMDiff.comp (sigmaMk (fun i => (hS i).toAnalyticManifold) i).contMDiff))
      ((sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i).contMDiff.comp
        (e i).symm.contMDiff) hR
    have R4 := (IdealSheaf.pullback_pullback D.sigmaTriple.I
      ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)
      (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i).contMDiff ⇑(e i).symm
      (e i).symm.contMDiff).symm
    have R5 :=
        congrArg (fun J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 (D.embedding i).G) =>
      J.pullback ⇑(e i).symm (e i).symm.contMDiff) hI
    exact (L1.trans (L2.trans (L3.trans (L4.trans (L5.trans L6))))).trans
      (R1.trans (R2.trans (R3.trans (R4.trans R5)))).symm
  exact (IdealSheaf.pullback_pullback_symm Φ₀ ((D.padAlongData σ).sigmaTriple.I.pullback
      ⇑(D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap
      (D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap.contMDiff)).symm.trans
    ((congrArg
        (fun J :
            AnalyticManifold.IdealSheaf (sigmaManifold fun i => (hS i).toAnalyticManifold) =>
        J.pullback ⇑Φ₀.symm Φ₀.symm.contMDiff) key).trans
      (IdealSheaf.pullback_pullback_symm Φ₀ (D.sigmaTriple.I.pullback
        ⇑(D.sigmaPadSliceDiffeomorph σ).symm (D.sigmaPadSliceDiffeomorph σ).symm.contMDiff)))

/-- The slice lies in the zero set of the padded coproduct ideal (the hypothesis `hSI` of the
push-forward; `idealSheaf_padSlice_le_padIdeal` per piece). -/
theorem idealSheaf_sigmaPadSlice_le :
    (D.isClosedSubmanifold_sigmaPadSlice σ).idealSheaf ≤ (D.padAlongData σ).sigmaTriple.I := by
  have h1 : (D.isClosedSubmanifold_sigmaPadSlice σ).idealSheaf =
      IdealSheaf.sigmaOf (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G)
        fun i => (isClosedSubmanifold_padSlice.{u} σ (D.embedding i).G).idealSheaf :=
    (IsClosedSubmanifold.idealSheaf_congr _
      (isClosedSubmanifold_sigmaUnion fun i => isClosedSubmanifold_padSlice.{u} σ (D.embedding i).G)
      rfl).trans (idealSheaf_sigmaUnion _)
  rw [h1]
  exact IdealSheaf.sigmaOf_mono _ fun i =>
    idealSheaf_padSlice_le_padIdeal σ (D.embedding i).G (D.embedding i).ideal

/-- The datum's reading open is the trace of the padded one on the slice: `Φ⁻¹(S* ∩ U⁺) = U` for
`U⁺ = ambImage Wp`, `U = ambImage (padPreimageOpens σ Wp)` (`inclusionMap_sigmaPadSliceDiffeomorph`,
`coe_sigmaCoordImage`, `preimage_sigmaMk_iUnion_image`). -/
theorem preimage_sigmaPadSliceDiffeomorph_preimageOpens_ambImage :
    (D.ambImage (D.padPreimageOpens σ Wp) : Set D.sigmaAmbient) =
      ⇑(D.sigmaPadSliceDiffeomorph σ) ⁻¹'
        ((D.isClosedSubmanifold_sigmaPadSlice σ).preimageOpens ((D.padAlongData σ).ambImage Wp) :
          Set _) := by
  ext x
  obtain ⟨i, w⟩ := x
  change sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i w ∈
      (sigmaCoordImage (fun i => (D.embedding i).G) (D.padPreimageOpens σ Wp) : Set _) ↔
    (D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap
      (D.sigmaPadSliceDiffeomorph σ (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i w)) ∈
      (sigmaCoordImage (fun i => ((D.padAlongData σ).embedding i).G) Wp : Set _)
  rw [D.inclusionMap_sigmaPadSliceDiffeomorph σ i w, coe_sigmaCoordImage, coe_sigmaCoordImage]
  constructor
  · intro h
    have h1 : w ∈ (D.padPreimageOpens σ Wp i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)) := by
      rw [← preimage_sigmaMk_iUnion_image (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G)
        (fun i => (D.padPreimageOpens σ Wp i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))) i]
      exact h
    exact sigmaMk_mem_iUnion_image (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G)
      (fun i => (Wp i : Set (pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G))) i
      (padExt σ (D.embedding i).G w) h1
  · intro h
    have h1 : padExt σ (D.embedding i).G w ∈
        (Wp i : Set (pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G)) := by
      rw [← preimage_sigmaMk_iUnion_image
        (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G)
        (fun i => (Wp i : Set (pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G))) i]
      exact h
    exact sigmaMk_mem_iUnion_image (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G)
      (fun i => (D.padPreimageOpens σ Wp i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))) i w h1

/-! #### The restricted slice map `U → U⁺` -/

/-- **The restricted slice map** `m : N|U → N⁺|U⁺`, `incl_{S*} ∘ Φ` on the reading opens (lands in
`U⁺` by `preimage_sigmaPadSliceDiffeomorph_preimageOpens_ambImage`). -/
def padRestrictMap : D.sigmaAmbient.restrict (D.ambImage (D.padPreimageOpens σ Wp)) →
    (D.padAlongData σ).sigmaAmbient.restrict ((D.padAlongData σ).ambImage Wp) :=
  fun p => ⟨(D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap (D.sigmaPadSliceDiffeomorph σ p.1),
    (Set.ext_iff.mp (D.preimage_sigmaPadSliceDiffeomorph_preimageOpens_ambImage σ Wp) p.1).mp p.2⟩

/-- It lies over `incl_{S*} ∘ Φ` (definitional). -/
theorem inclusion_padRestrictMap
    (p : D.sigmaAmbient.restrict (D.ambImage (D.padPreimageOpens σ Wp))) :
    (D.padAlongData σ).sigmaAmbient.inclusion ((D.padAlongData σ).ambImage Wp)
        (D.padRestrictMap σ Wp p) =
      (D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap (D.sigmaPadSliceDiffeomorph σ
        (D.sigmaAmbient.inclusion (D.ambImage (D.padPreimageOpens σ Wp)) p)) :=
  rfl

/-- It is analytic (`ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff`, as
`AnalyticMap.restrictMap`). -/
theorem contMDiff_padRestrictMap :
    ContMDiff 𝓘(𝕜, Fin D.n → 𝕜) 𝓘(𝕜, Fin n' → 𝕜) ω (D.padRestrictMap σ Wp) := fun p => by
  have hval : ContMDiffAt 𝓘(𝕜, Fin D.n → 𝕜) 𝓘(𝕜, Fin n' → 𝕜) ω
      ((Subtype.val : (D.padAlongData σ).sigmaAmbient.restrict ((D.padAlongData σ).ambImage Wp) →
        (D.padAlongData σ).sigmaAmbient) ∘ D.padRestrictMap σ Wp) p :=
    (((D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap.contMDiff.comp
      (D.sigmaPadSliceDiffeomorph σ).contMDiff).comp contMDiff_subtype_val).contMDiffAt
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (P := ContDiffWithinAtProp 𝓘(𝕜, Fin D.n → 𝕜) 𝓘(𝕜, Fin n' → 𝕜) ω) _ univ p).mp hval

/-- **The restricted ideals correspond along it**: `I|U = m^*(I⁺|U⁺)`
(`pullback_inclusionMap_sigmaPadSlice` and `pullback_symm_pullback`, then `pullback_pullback`
along the inclusions). -/
theorem restrictOpens_eq_pullback_padRestrictMap :
    D.sigmaTriple.I.restrict (D.ambImage (D.padPreimageOpens σ Wp)) =
      ((D.padAlongData σ).sigmaTriple.I.restrict ((D.padAlongData σ).ambImage Wp)).pullback
        (D.padRestrictMap σ Wp) (D.contMDiff_padRestrictMap σ Wp) := by
  have hII' : D.sigmaTriple.I =
      ((D.padAlongData σ).sigmaTriple.I.pullback
        ⇑(D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap
        (D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap.contMDiff).pullback
        ⇑(D.sigmaPadSliceDiffeomorph σ) (D.sigmaPadSliceDiffeomorph σ).contMDiff :=
    ((congrArg (fun K : AnalyticManifold.IdealSheaf
          (D.isClosedSubmanifold_sigmaPadSlice σ).toAnalyticManifold =>
        K.pullback ⇑(D.sigmaPadSliceDiffeomorph σ) (D.sigmaPadSliceDiffeomorph σ).contMDiff)
      (D.pullback_inclusionMap_sigmaPadSlice σ)).trans
      (IdealSheaf.pullback_symm_pullback (D.sigmaPadSliceDiffeomorph σ) D.sigmaTriple.I)).symm
  change D.sigmaTriple.I.pullback ⇑(D.sigmaAmbient.inclusion (D.ambImage (D.padPreimageOpens σ Wp)))
      (D.sigmaAmbient.inclusion (D.ambImage (D.padPreimageOpens σ Wp))).contMDiff =
    ((D.padAlongData σ).sigmaTriple.I.pullback
      ⇑((D.padAlongData σ).sigmaAmbient.inclusion ((D.padAlongData σ).ambImage Wp))
      ((D.padAlongData σ).sigmaAmbient.inclusion
        ((D.padAlongData σ).ambImage Wp)).contMDiff).pullback
      (D.padRestrictMap σ Wp) (D.contMDiff_padRestrictMap σ Wp)
  rw [hII', IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback,
    IdealSheaf.pullback_pullback]
  exact IdealSheaf.pullback_congr _ _ _ (funext fun _ => rfl)

/-! #### The core: the order isomorphism and the isomorphism of the coproduct local resolutions -/

/-- **The padding identity at the coproduct, its data** ([Kol07, 34.4] at the coproduct slice): an
order isomorphism of the label sets and an isomorphism `ψ` of the coproduct local resolutions
carrying the datum's member of label `o σp` to the padded datum's member of label `σp`, and lying
over the ambients — the padded coproduct's map to its closed subspace, after `ψ⁻¹`, is the datum's
map followed by the slice identification. The argument: `bed.closedEmbedding` at `(S*, I⁺, J*)`,
`exists_closedSubmanifold_last_pushforwardRestrict_boundary` (the carried slice `S*_r`, `G₁`, the
ideal identity, the composite square, the order isomorphism `o₁`), the cast leg at `(Φ, I, J*)`
(`G₀`, `ε₀`), `ψ := inv (homOfPullbackEq (incl_{S*_r} ∘ (G₀.trans G₁)))`, the member identity from
`pullback_idealSheaf_inclusionMap_comp_of_hasSncWithProper` in equality form. -/
theorem exists_padIdentityCore :
    ∃ (o : (D.padAlongData σ).sigmaIndex bed Wp hWp ≃o
        D.sigmaIndex bed (D.padPreimageOpens σ Wp) (D.isCompact_closure_padPreimageOpens σ Wp hWp))
      (ψ : bed.localResolutionOn (D.padAlongData σ).sigmaTriple
          (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
          ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp) ⟶
          bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple
          (D.ambImage (D.padPreimageOpens σ Wp))
          (D.isCompact_closure_ambImage _ (D.isCompact_closure_padPreimageOpens σ Wp hWp)))
      (hψ : IsIso ψ),
      (∀ σp, QuotientSpace.comap ψ.1
          (D.sigmaMembers bed (D.padPreimageOpens σ Wp)
            (D.isCompact_closure_padPreimageOpens σ Wp hWp) hbed (o σp)) =
        (D.padAlongData σ).sigmaMembers bed Wp hWp hbed σp) ∧
      (@inv (AnalyticSpace.{u} 𝕜) _ _ _ ψ hψ) ≫
          bed.localResolutionMapOn (D.padAlongData σ).sigmaTriple
          (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
          ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp) =
        bed.localResolutionMapOn D.sigmaTriple D.domBEDan_sigmaTriple
            (D.ambImage (D.padPreimageOpens σ Wp))
            (D.isCompact_closure_ambImage _ (D.isCompact_closure_padPreimageOpens σ Wp hWp)) ≫
            IdealSheaf.homOfPullbackEq (D.padRestrictMap σ Wp) (D.contMDiff_padRestrictMap σ Wp)
            (D.restrictOpens_eq_pullback_padRestrictMap σ Wp) := by
  -- the slice, its identification with the datum's ambient, the slice ideal
  set hS := D.isClosedSubmanifold_sigmaPadSlice σ with hhS
  set Φ := D.sigmaPadSliceDiffeomorph σ with hΦ
  set J := (D.padAlongData σ).sigmaTriple.I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff
    with hJ
  have hJeq : J = D.sigmaTriple.I.pullback ⇑Φ.symm Φ.symm.contMDiff :=
    D.pullback_inclusionMap_sigmaPadSlice σ
  have hJnz : J.IsNonzeroEverywhere := by
    rw [hJeq]
    exact IdealSheaf.isNonzeroEverywhere_pullback_diffeomorph Φ.symm
      D.sigmaTriple.isNonzeroEverywhere
  have hJred : IdealSheaf.IsReduced J := by
    rw [hJeq]
    exact IdealSheaf.isReduced_pullback_diffeomorph Φ.symm D.domBEDan_sigmaTriple.2
  have hT' : DomBEDan 𝕜 ⟨J, hJnz, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩ :=
    ⟨⟨fun x => PEmpty.elim x⟩, hJred⟩
  -- the reading opens
  have hUp := (D.padAlongData σ).isCompact_closure_ambImage Wp hWp
  have hU := D.isCompact_closure_ambImage _ (D.isCompact_closure_padPreimageOpens σ Wp hWp)
  -- first, `bed.closedEmbedding` at the coproduct slice: the padded run is the push-forward of the
  -- slice run
  have hA : bed.seqOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
        ((D.padAlongData σ).ambImage Wp) hUp =
      pushforwardRestrict hS ((D.padAlongData σ).ambImage Wp)
        (((bed.fam (n' - (n' - D.n))).fam _ hT').seqOn
          (hS.preimageOpens ((D.padAlongData σ).ambImage Wp))
          (hS.isCompact_closure_preimageOpens _ hUp)) :=
    bed.closedEmbedding n' (n' - D.n) hS (D.padAlongData σ).sigmaTriple.I
      (D.padAlongData σ).sigmaTriple.isNonzeroEverywhere J hJnz (D.idealSheaf_sigmaPadSlice_le σ)
      rfl (D.padAlongData σ).domBEDan_sigmaTriple hT' _ hUp
  -- second, the carried slice at the last stage, with the boundary clause
  obtain ⟨S_r, hS_r, G₁, hle, hideal, hsq, hbdry⟩ :=
    exists_closedSubmanifold_last_pushforwardRestrict_boundary hS
      ((D.padAlongData σ).ambImage Wp) _ (D.padAlongData σ).sigmaTriple.I
      (((bed.fam _).fam _ hT').noEmptyCenters _ _) (D.idealSheaf_sigmaPadSlice_le σ) _ hA
  have h3 : ∀ i : Fin (bed.seqOn (D.padAlongData σ).sigmaTriple
      (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
        hUp).toSuccession.length,
      ((bed.seqOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
        ((D.padAlongData σ).ambImage Wp) hUp).toSuccession.boundarySeq (⊤)
          i.castSucc).HasOnlyNormalCrossingsWith
        ((bed.seqOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
          ((D.padAlongData σ).ambImage Wp) hUp).toSuccession.center i) := by
    intro i
    have h1 := hbed.1 n' (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
      ((D.padAlongData σ).ambImage Wp) hUp
    have h :=
      FiniteSuccession.hasOnlyNormalCrossingsWith_boundarySeq_of_forall_hasSncWith
        (ψ := ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜))
        (bed.seqOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
          ((D.padAlongData σ).ambImage Wp) hUp).toSuccession
        (HypersurfaceFamily.isSnc_empty (ψ := ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜)))
        (fun i => h1.2.1 i) (i.1 + 1) i (Nat.lt_succ_self _)
    rw [HypersurfaceFamily.idealSheaf_empty (ψ := ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜))] at h
    exact h
  have hb3 := hbdry h3
  -- third, the cast leg: the slice run is the datum's run transported along `Φ`
  have hn : D.n ≤ n' := by simpa using Fintype.card_le_of_embedding σ
  have hII' : D.sigmaTriple.I = J.pullback ⇑Φ Φ.contMDiff := by
    rw [hJeq]
    exact (IdealSheaf.pullback_symm_pullback Φ D.sigmaTriple.I).symm
  obtain ⟨G₀, hG₀sq, hG₀ideal, ε₀, hε₀⟩ := bed.exists_diffeomorph_last_of_cast_iso hbed.2
    (Nat.sub_sub_self hn) Φ J hJnz D.sigmaTriple.I D.sigmaTriple.isNonzeroEverywhere hII'
    hT' D.domBEDan_sigmaTriple (hS.preimageOpens ((D.padAlongData σ).ambImage Wp))
    (hS.isCompact_closure_preimageOpens _ hUp) (D.ambImage (D.padPreimageOpens σ Wp)) hU
    (D.preimage_sigmaPadSliceDiffeomorph_preimageOpens_ambImage σ Wp)
  -- fourth, the ideal-level member identity along `incl_{S_r} ∘ G₁` and the label isomorphism
  have hsncP : ((bed.seqOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
      ((D.padAlongData σ).ambImage Wp) hUp).toSuccession.totalTransformSeq (Fin.last _)).IsSnc
      (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜)) :=
    (hbed.1 n' (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
      ((D.padAlongData σ).ambImage Wp) hUp).1 (Fin.last _)
  have hsncS : ((((bed.fam (n' - (n' - D.n))).fam _ hT').seqOn
      (hS.preimageOpens ((D.padAlongData σ).ambImage Wp))
      (hS.isCompact_closure_preimageOpens _ hUp)).toSuccession.totalTransformSeq
        (Fin.last _)).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin (n' - (n' - D.n)) → 𝕜)) :=
    (hbed.1 _ ⟨J, hJnz, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩ hT'
      (hS.preimageOpens ((D.padAlongData σ).ambImage Wp))
      (hS.isCompact_closure_preimageOpens _ hUp)).1 (Fin.last _)
  have hsncL : ((bed.seqOn D.sigmaTriple D.domBEDan_sigmaTriple
      (D.ambImage (D.padPreimageOpens σ Wp)) hU).toSuccession.totalTransformSeq
        (Fin.last _)).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜)) :=
    (hbed.1 D.n D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage (D.padPreimageOpens σ Wp))
      hU).1 (Fin.last _)
  obtain ⟨o₁, ho₁⟩ := hb3.2
  have he : ∀ j, IdealSheaf.pullback (⇑hS_r.inclusionMap ∘ ⇑G₁)
      (hS_r.inclusionMap.contMDiff.comp G₁.contMDiff) (hsncP.1 j).idealSheaf =
      (hsncS.1 (o₁.symm j)).idealSheaf := fun j =>
    hS_r.pullback_idealSheaf_inclusionMap_comp_of_hasSncWithProper hsncP hb3.1 G₁ j
      (hsncS.1 (o₁.symm j))
      ((ho₁ (o₁.symm j)).symm.trans (congrArg (fun k => (⇑hS_r.inclusionMap ∘ ⇑G₁) ⁻¹'
        ((bed.seqOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
          ((D.padAlongData σ).ambImage Wp) hUp).toSuccession.totalTransformSeq (Fin.last _)).hyp k)
        (OrderIso.apply_symm_apply o₁ j)))
  -- fifth, the isomorphism `φ := m₂ ∘ m₁` and `ψ := φ⁻¹`
  have hideal' : (((bed.fam (n' - (n' - D.n))).fam _ hT').seqOn
        (hS.preimageOpens ((D.padAlongData σ).ambImage Wp))
        (hS.isCompact_closure_preimageOpens _ hUp)).toSuccession.strictTransformSubspaceSeq
        (IdealSheaf.restrict J _) (Fin.last _) =
      ((bed.lastIdealOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
        ((D.padAlongData σ).ambImage Wp) hUp).pullback ⇑hS_r.inclusionMap
          hS_r.inclusionMap.contMDiff).pullback ⇑G₁ G₁.contMDiff :=
    hideal.trans (IdealSheaf.pullback_pullback _ _ _ _ _).symm
  let m₁ : bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple
      (D.ambImage (D.padPreimageOpens σ Wp)) hU ⟶
      IdealSheaf.toAnalyticSpace
      ((((bed.fam (n' - (n' - D.n))).fam _ hT').seqOn
          (hS.preimageOpens ((D.padAlongData σ).ambImage Wp))
          (hS.isCompact_closure_preimageOpens _ hUp)).toSuccession.strictTransformSubspaceSeq
        (IdealSheaf.restrict J _) (Fin.last _)) :=
    IdealSheaf.homOfPullbackEq ⇑G₀ G₀.contMDiff hG₀ideal
  let mI : IdealSheaf.toAnalyticSpace
      ((bed.lastIdealOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
          ((D.padAlongData σ).ambImage Wp) hUp).pullback ⇑hS_r.inclusionMap
        hS_r.inclusionMap.contMDiff) ⟶ bed.localResolutionOn (D.padAlongData σ).sigmaTriple
      (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp) hUp :=
    IdealSheaf.homOfPullbackEq ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff rfl
  let mG : IdealSheaf.toAnalyticSpace
      ((((bed.fam (n' - (n' - D.n))).fam _ hT').seqOn
          (hS.preimageOpens ((D.padAlongData σ).ambImage Wp))
          (hS.isCompact_closure_preimageOpens _ hUp)).toSuccession.strictTransformSubspaceSeq
        (IdealSheaf.restrict J _) (Fin.last _)) ⟶
      IdealSheaf.toAnalyticSpace
      ((bed.lastIdealOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
          ((D.padAlongData σ).ambImage Wp) hUp).pullback ⇑hS_r.inclusionMap
        hS_r.inclusionMap.contMDiff) :=
    IdealSheaf.homOfPullbackEq ⇑G₁ G₁.contMDiff hideal'
  have hm₁ : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _ m₁ :=
    isIso_homOfPullbackEq_of_diffeomorph G₀ hG₀ideal
  have hmI : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _ mI :=
    isIso_homOfPullbackEq_inclusionMap hS_r hle rfl
  have hmG : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _ mG :=
    isIso_homOfPullbackEq_of_diffeomorph G₁ hideal'
  let φ : bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage
      (D.padPreimageOpens σ
      Wp)) hU ⟶ bed.localResolutionOn (D.padAlongData σ).sigmaTriple
      (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp) hUp :=
    (m₁ ≫ mG) ≫ mI
  have hφ : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _ φ :=
    @IsIso.comp_isIso (AnalyticSpace.{u} 𝕜) _ _ _ _ _ _
      (@IsIso.comp_isIso (AnalyticSpace.{u} 𝕜) _ _ _ _ _ _ hm₁ hmG) hmI
  -- `φ` as ONE `homOfPullbackEq`, along the composite `incl_{S*_r} ∘ (G₁ ∘ G₀)`
  have hG' : bed.lastIdealOn D.sigmaTriple D.domBEDan_sigmaTriple
        (D.ambImage (D.padPreimageOpens σ Wp)) hU =
      (bed.lastIdealOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
        ((D.padAlongData σ).ambImage Wp) hUp).pullback (⇑hS_r.inclusionMap ∘ (⇑G₁ ∘ ⇑G₀))
        (hS_r.inclusionMap.contMDiff.comp (G₁.contMDiff.comp G₀.contMDiff)) :=
    hG₀ideal.trans
        ((congrArg (fun K : AnalyticManifold.IdealSheaf _ => K.pullback ⇑G₀ G₀.contMDiff)
      hideal').trans ((IdealSheaf.pullback_pullback _ _ _ _ _).trans
        (IdealSheaf.pullback_pullback _ _ _ _ _)))
  have hmid : bed.lastIdealOn D.sigmaTriple D.domBEDan_sigmaTriple
        (D.ambImage (D.padPreimageOpens σ Wp)) hU =
      ((bed.lastIdealOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
        ((D.padAlongData σ).ambImage Wp) hUp).pullback ⇑hS_r.inclusionMap
          hS_r.inclusionMap.contMDiff).pullback (⇑G₁ ∘ ⇑G₀) (G₁.contMDiff.comp G₀.contMDiff) :=
    hG₀ideal.trans
        ((congrArg (fun K : AnalyticManifold.IdealSheaf _ => K.pullback ⇑G₀ G₀.contMDiff)
      hideal').trans (IdealSheaf.pullback_pullback _ _ _ _ _))
  let φ' : bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage
      (D.padPreimageOpens σ
      Wp)) hU ⟶ bed.localResolutionOn (D.padAlongData σ).sigmaTriple
      (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp) hUp :=
    IdealSheaf.homOfPullbackEq (⇑hS_r.inclusionMap ∘ (⇑G₁ ∘ ⇑G₀))
      (hS_r.inclusionMap.contMDiff.comp (G₁.contMDiff.comp G₀.contMDiff)) hG'
  have hφ'eq : φ' = φ := by
    have h1 := IdealSheaf.homOfPullbackEq_comp_fun ⇑G₀ G₀.contMDiff ⇑G₁ G₁.contMDiff hG₀ideal
      hideal' hmid
    have h2 := IdealSheaf.homOfPullbackEq_comp_fun (⇑G₁ ∘ ⇑G₀) (G₁.contMDiff.comp G₀.contMDiff)
      ⇑hS_r.inclusionMap hS_r.inclusionMap.contMDiff hmid rfl hG'
    exact h2.symm.trans (congrArg (· ≫ mI) h1.symm)
  have hφ' : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _ φ' := hφ'eq ▸ hφ
  -- the members at the ideal level along the ONE map `incl_{S_r} ∘ (G₁ ∘ G₀)`:
  -- `pullback_idealSheaf_inclusionMap_comp_of_hasSncWithProper` (`he`), then the cast helper at
  -- `G₀`; then the generic member transport along `homOfPullbackEq`
  have hYY : ∀ j, (hsncP.1 j).idealSheaf.pullback (⇑hS_r.inclusionMap ∘ (⇑G₁ ∘ ⇑G₀))
        (hS_r.inclusionMap.contMDiff.comp (G₁.contMDiff.comp G₀.contMDiff)) =
      (hsncL.1 (ε₀.symm (o₁.symm j))).idealSheaf := fun j =>
    (IdealSheaf.pullback_pullback (hsncP.1 j).idealSheaf (⇑hS_r.inclusionMap ∘ ⇑G₁)
      (hS_r.inclusionMap.contMDiff.comp G₁.contMDiff) ⇑G₀ G₀.contMDiff).symm.trans
      ((congrArg (IdealSheaf.pullback ⇑G₀ G₀.contMDiff) (he j)).trans
        (IsClosedSubmanifold.pullback_idealSheaf_diffeomorph_of_eq (Nat.sub_sub_self hn) G₀
          (hsncS.1 (o₁.symm j)) (hsncL.1 (ε₀.symm (o₁.symm j)))
          ((congrArg (fun k => ⇑G₀ ⁻¹' ((((bed.fam (n' - (n' - D.n))).fam _ hT').seqOn
              (hS.preimageOpens ((D.padAlongData σ).ambImage Wp))
              (hS.isCompact_closure_preimageOpens _ hUp)).toSuccession.totalTransformSeq
                (Fin.last _)).hyp k)
            (OrderIso.apply_symm_apply ε₀ (o₁.symm j)).symm).trans
            (hε₀ (ε₀.symm (o₁.symm j))))))
  have hb :
      ∀ j, (AnalyticSpace.ClosedSubspace.comap
          (X := AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 _) _) (hsncP.1 j).idealSheaf
          (IdealSheaf.toAnalyticSpaceι
          (bed.lastIdealOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
          ((D.padAlongData σ).ambImage Wp) hUp))).comap φ' =
      AnalyticSpace.ClosedSubspace.comap
          (X := AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 _) _)
          (hsncL.1 (ε₀.symm (o₁.symm j))).idealSheaf (IdealSheaf.toAnalyticSpaceι
          (bed.lastIdealOn D.sigmaTriple D.domBEDan_sigmaTriple
          (D.ambImage (D.padPreimageOpens σ Wp)) hU)) := fun j =>
    comap_homOfPullbackEq_comap_toAnalyticSpaceι_idealSheaf (⇑hS_r.inclusionMap ∘ (⇑G₁ ∘ ⇑G₀))
      (hS_r.inclusionMap.contMDiff.comp (G₁.contMDiff.comp G₀.contMDiff)) hG' (hsncP.1 j)
      (hsncL.1 (ε₀.symm (o₁.symm j))) (hYY j)
  -- the square over the restricted slice map `m`
  have hcomm : ⇑(bed.seqOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
        ((D.padAlongData σ).ambImage Wp) hUp).toSuccession.composite ∘
        (⇑hS_r.inclusionMap ∘ (⇑G₁ ∘ ⇑G₀)) =
      D.padRestrictMap σ Wp ∘ ⇑(bed.seqOn D.sigmaTriple D.domBEDan_sigmaTriple
        (D.ambImage (D.padPreimageOpens σ Wp)) hU).toSuccession.composite :=
    funext fun p => Subtype.ext ((hsq (G₀ p)).symm.trans (congrArg hS.inclusionMap (hG₀sq p)))
  have hsquare := quotientMap_toSpaceHom_comp_homOfPullbackEq
    (bed.seqOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
      ((D.padAlongData σ).ambImage Wp) hUp).toSuccession.composite
    (bed.seqOn D.sigmaTriple D.domBEDan_sigmaTriple
      (D.ambImage (D.padPreimageOpens σ Wp)) hU).toSuccession.composite
    (⇑hS_r.inclusionMap ∘ (⇑G₁ ∘ ⇑G₀))
    (hS_r.inclusionMap.contMDiff.comp (G₁.contMDiff.comp G₀.contMDiff)) (D.padRestrictMap σ Wp)
    (D.contMDiff_padRestrictMap σ Wp) hcomm
    ((bed.seqOn (D.padAlongData σ).sigmaTriple (D.padAlongData σ).domBEDan_sigmaTriple
      ((D.padAlongData σ).ambImage Wp) hUp).toSuccession.compat_composite_strictTransformSubspaceSeq
      (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜))
      (BEDanFamStar.restrictedIdealOn (D.padAlongData σ).sigmaTriple
        ((D.padAlongData σ).ambImage Wp)))
    ((bed.seqOn D.sigmaTriple D.domBEDan_sigmaTriple
      (D.ambImage (D.padPreimageOpens σ Wp))
        hU).toSuccession.compat_composite_strictTransformSubspaceSeq
      (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
      (BEDanFamStar.restrictedIdealOn D.sigmaTriple (D.ambImage (D.padPreimageOpens σ Wp))))
    hG' (D.restrictOpens_eq_pullback_padRestrictMap σ Wp)
  -- the data
  refine ⟨o₁.symm.trans ε₀.symm, @inv (AnalyticSpace.{u} 𝕜) _ _ _ φ' hφ',
    @IsIso.inv_isIso (AnalyticSpace.{u} 𝕜) _ _ _ φ' hφ', fun j => ?_, ?_⟩
  · -- the members: `comap φ'⁻¹ (members (o j)) = comap φ'⁻¹ (comap φ' (members⁺ j)) = members⁺ j`
    exact (congrArg (AnalyticSpace.ClosedSubspace.comap · (@inv (AnalyticSpace.{u} 𝕜) _ _ _ φ' hφ'))
        (hb j).symm).trans
      ((ClosedSubspace.comap_comp_hom φ'
        (@inv (AnalyticSpace.{u} 𝕜) _ _ _ φ' hφ') _).symm.trans
        ((congrArg
            (fun k : _ ⟶ _ => AnalyticSpace.ClosedSubspace.comap _ k)
          (@IsIso.inv_hom_id (AnalyticSpace.{u} 𝕜) _ _ _ φ' hφ')).trans
          (ClosedSubspace.comap_id_hom _)))
  · -- over the ambients: `inv (inv φ') = φ'` and the generic quotient square
    exact (congrArg
        (fun k => k ≫
        (bed.localResolutionMapOn (D.padAlongData σ).sigmaTriple
            (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
            ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp)))
      (@IsIso.inv_inv (AnalyticSpace.{u} 𝕜) _ _ _ φ' hφ')).trans hsquare

/-! #### The data exposed: `o` and `ψ` by choice from the core, with their clauses; the assembly -/

include hbed in
/-- **The order isomorphism of the label sets** `o : ι⁺ ≃o ι`, chosen from the core
`exists_padIdentityCore` (the padded run is the run of the coproduct slice, stage by stage). -/
def padIdentityOrderIso : (D.padAlongData σ).sigmaIndex bed Wp hWp ≃o
    D.sigmaIndex bed (D.padPreimageOpens σ Wp) (D.isCompact_closure_padPreimageOpens σ Wp hWp) :=
  (D.exists_padIdentityCore σ Wp hWp bed hbed).choose

include hbed in
/-- **The isomorphism `ψ` of the coproduct local resolutions**, chosen from the core
`exists_padIdentityCore`; the piece clause (`CoproductPadIdentityPiece.lean`) is stated against
this NAMED `ψ`. -/
def padIdentityIso : bed.localResolutionOn (D.padAlongData σ).sigmaTriple
    (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
    ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp) ⟶
    bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple
    (D.ambImage (D.padPreimageOpens σ Wp))
    (D.isCompact_closure_ambImage _ (D.isCompact_closure_padPreimageOpens σ Wp hWp)) :=
  (D.exists_padIdentityCore σ Wp hWp bed hbed).choose_spec.choose

/-- `ψ` is an isomorphism (`ψ = inv (homOfPullbackEq (incl_{S*_r} ∘ (G₁ ∘ G₀)))`, the inverse of an
isomorphism). -/
theorem padIdentityIso_isIso : IsIso (D.padIdentityIso σ Wp hWp bed hbed) :=
  (D.exists_padIdentityCore σ Wp hWp bed hbed).choose_spec.choose_spec.choose

/-- **The members correspond, in equality form for EVERY label**: `ψ` carries the datum's member
of label `o σp` to the padded datum's member of label `σp` (the ideal-level trace identity
`pullback_idealSheaf_inclusionMap_comp_of_hasSncWithProper` along `incl_{S*_r} ∘ G₁`, the cast
helper at `G₀`, the generic member transport). -/
theorem comap_padIdentityIso_sigmaMembers (σp : (D.padAlongData σ).sigmaIndex bed Wp hWp) :
    QuotientSpace.comap (D.padIdentityIso σ Wp hWp bed hbed).1
        (D.sigmaMembers bed (D.padPreimageOpens σ Wp)
          (D.isCompact_closure_padPreimageOpens σ Wp hWp) hbed
          (D.padIdentityOrderIso σ Wp hWp bed hbed σp)) =
      (D.padAlongData σ).sigmaMembers bed Wp hWp hbed σp :=
  (D.exists_padIdentityCore σ Wp hWp bed hbed).choose_spec.choose_spec.choose_spec.1 σp

/-- **`ψ` lies over the ambients, in MORPHISM form**: the padded coproduct's map to its restricted
closed subspace, after `ψ⁻¹`, is the datum's
map followed by the closed-subspace morphism over the restricted slice map `padRestrictMap : N|U →
N⁺|U⁺` (`incl_{S*} ∘ Φ` on the reading opens) — the generic quotient square along `incl_{S*_r} ∘ (G₁
∘ G₀)` and `padRestrictMap`. -/
theorem localResolutionMapOn_comp_inv_padIdentityIso :
    (@inv (AnalyticSpace.{u} 𝕜) _ _ _ (D.padIdentityIso σ Wp hWp bed hbed)
          (D.padIdentityIso_isIso σ Wp hWp bed hbed)) ≫
        bed.localResolutionMapOn (D.padAlongData σ).sigmaTriple
        (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
        ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp) =
      bed.localResolutionMapOn D.sigmaTriple D.domBEDan_sigmaTriple
          (D.ambImage (D.padPreimageOpens σ Wp))
          (D.isCompact_closure_ambImage _ (D.isCompact_closure_padPreimageOpens σ Wp hWp)) ≫
          IdealSheaf.homOfPullbackEq (D.padRestrictMap σ Wp) (D.contMDiff_padRestrictMap σ Wp)
          (D.restrictOpens_eq_pullback_padRestrictMap σ Wp) :=
  (D.exists_padIdentityCore σ Wp hWp bed hbed).choose_spec.choose_spec.choose_spec.2

/-- **`ψ` lies over the ambients, in POINT form** (the corollary of the morphism form through
`toFun_homOfPullbackEq_val` and `inclusion_padRestrictMap`): on points,
`localResolutionMapOn⁺ (ψ⁻¹ z)` lies over `incl_{S*} (Φ (localResolutionMapOn z))` in the padded
coproduct ambient. -/
theorem localResolutionMapOn_inv_padIdentityIso_apply
    (z : bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple
      (D.ambImage (D.padPreimageOpens σ Wp))
      (D.isCompact_closure_ambImage _ (D.isCompact_closure_padPreimageOpens σ Wp hWp))) :
    ((bed.localResolutionMapOn (D.padAlongData σ).sigmaTriple
        (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
        ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp))
        ((@inv (AnalyticSpace.{u} 𝕜) _ _ _ (D.padIdentityIso σ Wp hWp bed hbed)
            (D.padIdentityIso_isIso σ Wp hWp bed hbed)) z)).1.1 =
      (D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap
        (D.sigmaPadSliceDiffeomorph σ
          (((bed.localResolutionMapOn D.sigmaTriple D.domBEDan_sigmaTriple
              (D.ambImage (D.padPreimageOpens σ Wp)) (D.isCompact_closure_ambImage _
              (D.isCompact_closure_padPreimageOpens σ Wp hWp)))
            z).1.1)) := by
  have e :
      (bed.localResolutionMapOn (D.padAlongData σ).sigmaTriple
        (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
        ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp))
        ((@inv (AnalyticSpace.{u} 𝕜) _ _ _ (D.padIdentityIso σ Wp hWp bed hbed)
            (D.padIdentityIso_isIso σ Wp hWp bed hbed)) z) =
      (IdealSheaf.homOfPullbackEq (D.padRestrictMap σ Wp)
          (D.contMDiff_padRestrictMap σ Wp) (D.restrictOpens_eq_pullback_padRestrictMap σ Wp))
        ((bed.localResolutionMapOn D.sigmaTriple D.domBEDan_sigmaTriple
            (D.ambImage (D.padPreimageOpens σ Wp)) (D.isCompact_closure_ambImage _
            (D.isCompact_closure_padPreimageOpens σ Wp hWp))) z) :=
    congrArg (fun k => k z)
      (D.localResolutionMapOn_comp_inv_padIdentityIso σ Wp hWp bed hbed)
  rw [e]
  exact congrArg Subtype.val (toFun_homOfPullbackEq_val (D.padRestrictMap σ Wp)
    (D.contMDiff_padRestrictMap σ Wp) (D.restrictOpens_eq_pullback_padRestrictMap σ Wp) _)

/-- **The padding identity from its core and the piece clause**: given, on every piece `i`, an
isomorphism `ψᵢ` over the piece with `resIn⁺ i ≫ ψ = ψᵢ ≫ resIn i` for the NAMED
`ψ = padIdentityIso` (the piece clause, `CoproductPadIdentityPiece.lean`),
`D.PadIdentityOn σ Wp hWp bed hbed` holds with the data `o`, `ψ` and their clauses. -/
theorem padIdentityOn_of_forall_piece
    (hc : ∀ i, ∃ ψᵢ : ((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp i) ⟶
          (D.embedding i).localResolution bed (D.padPreimageOpens σ Wp i)
            (D.isCompact_closure_padPreimageOpens σ Wp hWp i),
        IsIso ψᵢ ∧
        ψᵢ ≫ (D.embedding i).localResolutionToPiece bed (D.padPreimageOpens σ Wp i)
            (D.isCompact_closure_padPreimageOpens σ Wp hWp i) =
          ((D.padAlongData σ).embedding i).localResolutionToPiece bed (Wp i) (hWp i) ∧
        (D.padAlongData σ).resIn bed Wp hWp hbed i ≫ D.padIdentityIso σ Wp hWp bed hbed =
          ψᵢ ≫ D.resIn bed (D.padPreimageOpens σ Wp)
            (D.isCompact_closure_padPreimageOpens σ Wp hWp) hbed i) :
    D.PadIdentityOn σ Wp hWp bed hbed :=
  ⟨D.padIdentityOrderIso σ Wp hWp bed hbed, D.padIdentityIso σ Wp hWp bed hbed,
    D.padIdentityIso_isIso σ Wp hWp bed hbed, D.comap_padIdentityIso_sigmaMembers σ Wp hWp bed hbed,
    hc⟩

end Pad

end LocalEmbeddingData

end Hironaka.Manifold

end
