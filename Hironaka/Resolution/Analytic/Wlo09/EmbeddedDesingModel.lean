/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Concrete
public import Hironaka.Resolution.Analytic.Wlo09.FamilyExt
public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs
public import Hironaka.Manifold.Resolution.Defs
public import Hironaka.Resolution.Analytic.Principalization.IsoOff
public import Hironaka.Resolution.Analytic.Wlo09.FunctorialPrincipalization
public import Hironaka.Resolution.Analytic.Wlo09.ZeroStalks
public import Hironaka.Resolution.Analytic.Wlo09.CenterCodim
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.Functor.EndResultEmbeddingLemmas
import Hironaka.Resolution.Analytic.Functor.LimitGluing
import Hironaka.Resolution.Analytic.Functor.PullbackUpToEmpty
import Hironaka.Resolution.Analytic.Functor.LimitProperties
import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientTransport
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionShear
import Hironaka.Resolution.Analytic.Principalization.ClauseOne
import Hironaka.Resolution.Analytic.Principalization.ClauseThree
import Hironaka.Resolution.Analytic.Wlo09.Clauses
import Hironaka.Resolution.Analytic.Wlo09.HironakaClauses
import Hironaka.Resolution.Analytic.Wlo09.IsoOverReg
import Hironaka.Resolution.Analytic.Wlo09.PreimageSing
import Hironaka.Resolution.Analytic.Wlo09.ProperSncOfEmbeddedDesing

/-!
# Włodarczyk's embedded desingularization on the standard model

The analytic embedded desingularization of a reduced closed subspace `Y` of an analytic manifold
`M` modelled on the standard space `𝕜ⁿ` [Wlo09, Theorem 2.0.2], as one extension-compatible
family over `M`, with its clauses per compact and its commutation with local analytic
isomorphisms. The main theorem `AnalyticManifold.exists_embeddedDesingularization` is in
`Hironaka/Resolution/Analytic/Wlo09/EmbeddedDesingularization.lean`; the global objects on the
glued space, in `Hironaka/Resolution/Analytic/Wlo09/EmbeddedDesingGlobal.lean`.

For an ideal sheaf with nonzero stalks, the family is the concrete embedded desingularization
functor `concreteBEDanFamStar` (`Hironaka/Resolution/Analytic/Wlo09/Concrete.lean`) at the triple
`(M, 𝓘_Y, ∅)` (`embeddedTriple`), a compatible family of successions over the relatively compact
opens (`embeddedDesingPiecesOfNonzero`), glued along the exhaustion of `M`
(`CompatibleFamily.toExtensionCompatibleFamily`, the gluing of `resolveFamExt`,
`Hironaka/Resolution/Analytic/Wlo09/FamilyExt.lean`; `embeddedDesingFamOfNonzero`):

* `isProperMap_embeddedDesingFamOfNonzero_map`: the glued blow-down is proper
  (`CompatibleFamily.isProperMap_limitBlowDown`);
* `isAnalyticIsoOver_embeddedDesingFamOfNonzero_map`: it is an isomorphism off the singular locus
  `Sing(Y) = Y ∖ Reg(Y)`: the centres lie over `Y` (the order clause of the modified marked
  resolution, `bedanFamOfInput_isOfOrderGe`, read by `CentersOver.of_isOfOrderGe`) and avoid
  `Reg(Y)` (clause (2) of `IsEmbeddedDesing`), so every blow-down of a piece is an isomorphism over
  the complement of `Sing(Y)` (`isAnalyticIsoOver_stageMap`), and these glue
  (`CompatibleFamily.isAnalyticIsoOver_limitBlowDown`);
* `isDesingularizedBy_seqOn_embeddedDesingPiecesOfNonzero`: over every relatively compact open
  the succession desingularizes the restriction of `Y` (`IdealSheaf.IsDesingularizedBy`). Clauses
  (1), (2), (3) and (6) are those of `concreteBEDanFamStar_isEmbeddedDesing`, (1) read in
  Hironaka's boundary form (`hasOnlyNormalCrossingsWith_boundarySeq_of_forall_hasSncWith`,
  `boundarySeq_eq_idealSheaf_totalTransformSeq_of_forall_lt`;
  `boundarySeq_seqOn_embeddedDesingPiecesOfNonzero`), (3) in its transversal form
  (`IsEmbeddedDesing.isProperSnc`); the support of the last exceptional divisor is the preimage of
  `Sing(Y)`: it lies over the centres, hence over `Sing(Y)`
  (`support_totalTransformSeq_subset_preimage_of_centersOver`), and off it the composite
  blow-down is an isomorphism near the point, carrying the smooth strict transform onto `Y`
  (`isRegularLocalRing_quotient_strictTransformSubspaceSeq_iff_of_notMem_support`).

For an arbitrary reduced `𝓘_Y`, which may vanish on some connected components of `M` (those
contained in `Y`), the family `embeddedDesingFam` is the one of `𝓘_Y` made the unit ideal on
those components (`IdealSheaf.unitOnZeroStalks`,
`Hironaka/Resolution/Analytic/Wlo09/ZeroStalks.lean`; the pieces `embeddedDesingPieces`), whose
singular locus is that of `Y`; over the components where `𝓘_Y` vanishes nothing is blown up, and
the clauses transfer (`IsDesingularizedBy.of_eq_off_clopen`,
`isDesingularizedBy_seqOn_embeddedDesingPieces`): there the strict transform is the component
itself, smooth, and the exceptional divisor is empty. The transversal chart clause (3) and the
monomial clause (6) are also recorded with the last exceptional family named explicitly
(`exists_adaptedChart_seqOn_embeddedDesingPieces`, `exists_monomial_seqOn_embeddedDesingPieces`),
the form in which the global objects are glued.

The family commutes with local analytic isomorphisms over every pair of compacts
(`isPullbackUpToEmptyAlong_embeddedDesingFam`): for a local analytic isomorphism `g : N → M` and
`J = g^*I`, the triple of `J` carries the pull-back data of the triple of `I` (making the unit
ideal on the zero components commutes with the pull-back,
`unitOnZeroStalks_pullback_of_isLocalDiffeomorph`), so the values of the functor correspond
(`CommutesWithLocalIsos`, the last clause of `IsEmbeddedDesing`) and the succession over a compact
of `N` is the pull-back up to empty blow-ups of the succession over every compact of `M` whose
neighbourhood contains its image (`CompatibleFamily.isPullbackUpToEmptyAlong_seqOn`).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

/-! ### The triple of a closed subspace -/

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- The triple `(M, 𝓘_Y, ∅)` of the ideal sheaf `𝓘_Y` of a closed subspace with nonzero stalks and
the empty boundary, the input of the embedded desingularization functor. -/
def embeddedTriple {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (I : IdealSheaf M)
    (hI₀ : I.IsNonzeroEverywhere) :
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M :=
  ⟨I, hI₀, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩

/-- The triple `(M, 𝓘_Y, ∅)` of a reduced `Y` is in the class `DomBEDan` of the embedded
desingularization functor. -/
theorem domBEDan_embeddedTriple {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (I : IdealSheaf M)
    (hI : I.IsReduced) (hI₀ : I.IsNonzeroEverywhere) : DomBEDan 𝕜 (embeddedTriple I hI₀) :=
  ⟨inferInstanceAs (IsEmpty PEmpty), hI⟩

/-! ### The family of an ideal sheaf with nonzero stalks -/

variable (M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)) (I : IdealSheaf M) (hI : I.IsReduced)
  (hI₀ : I.IsNonzeroEverywhere)

/-- **The pieces of the embedded desingularization of `Y`**, for an ideal sheaf `𝓘_Y` with
nonzero stalks: the value of the concrete embedded desingularization functor
`concreteBEDanFamStar` at `(M, 𝓘_Y, ∅)`, a compatible family of successions over the relatively
compact opens of `M`. -/
abbrev embeddedDesingPiecesOfNonzero : CompatibleFamily (embeddedTriple I hI₀) :=
  ((concreteBEDanFamStar.{u} 𝕜).fam n).fam (embeddedTriple I hI₀) (domBEDan_embeddedTriple I hI hI₀)

/-- **The embedded desingularization of `Y` as one family over `M`**, for an ideal sheaf `𝓘_Y`
with nonzero stalks: the pieces glued along the exhaustion of `M`
([Wlo09, Theorem 2.0.2]; the gluing of [Wlo09, §4.2]). -/
def embeddedDesingFamOfNonzero : ExtensionCompatibleFamily M :=
  (embeddedDesingPiecesOfNonzero M I hI hI₀).toExtensionCompatibleFamily

/-- The blow-down of the embedded desingularization is proper. -/
theorem isProperMap_embeddedDesingFamOfNonzero_map :
    IsProperMap (embeddedDesingFamOfNonzero M I hI hI₀).map :=
  CompatibleFamily.isProperMap_toExtensionCompatibleFamily_map _

/-- The centres of the succession on a relatively compact open lie over `Sing(Y) = Y ∖ Reg(Y)` of
`Y ∩ U`: over `Y` by the order clause of the modified marked resolution
(`bedanFamOfInput_isOfOrderGe`, `CentersOver.of_isOfOrderGe` at mark `1`), and off `Reg(Y)` by
clause (2) of `IsEmbeddedDesing`. -/
theorem centersOver_embeddedTriple (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((embeddedDesingPiecesOfNonzero M I hI hI₀).seqOn U hU).toSuccession.CentersOver
      ((I.restrict U).support \ (I.restrict U).regularLocus) := by
  set T := embeddedTriple I hI₀
  have hT : DomBEDan 𝕜 T := domBEDan_embeddedTriple I hI hI₀
  obtain ⟨-, -, h2, -, -, -⟩ := (concreteBEDanFamStar_isEmbeddedDesing.{u} 𝕜).1 n T hT U hU
  have hov := FiniteSuccession.CentersOver.of_isOfOrderGe _
    (bedanFamOfInput_isOfOrderGe 𝕜 (concreteBMOmodFam.{u} 𝕜) n T hT U hU) le_rfl
  intro i x hx
  have hq := hov i hx
  exact ⟨hq, fun hreg => h2 i x hx ⟨⟨_, hq⟩, (mem_reg_toAnalyticSpace_iff _ ⟨_, hq⟩).mpr hreg,
    rfl⟩⟩

/-- **The blow-down of the embedded desingularization is an isomorphism off `Sing(Y)`**,
Włodarczyk's bimeromorphy: every blow-down of a piece is an isomorphism over the complement of
`Sing(Y)`, the centres lying over it (`centersOver_embeddedTriple`, `isAnalyticIsoOver_stageMap`),
and these glue (`CompatibleFamily.isAnalyticIsoOver_limitBlowDown`). -/
theorem isAnalyticIsoOver_embeddedDesingFamOfNonzero_map :
    (embeddedDesingFamOfNonzero M I hI hI₀).map.IsIsoOver (I.support \ I.regularLocus)ᶜ := by
  set C := embeddedDesingPiecesOfNonzero M I hI hI₀
  refine CompatibleFamily.isAnalyticIsoOver_limitBlowDown C (exhaustion M)
    (fun _ _ hU₁ hU₂ h => C.isAnalyticOpenEmbedding_endResultEmbedding hU₁ hU₂ h)
    (fun _ _ hU₁ hU₂ h p => C.composite_endResultEmbedding hU₁ hU₂ h p) _ fun m => ?_
  set U : Opens M := relCompactOpen (exhaustion M) m
  have hU : IsCompact (closure (U : Set M)) := isCompact_closure_relCompactOpen _ _
  refine FiniteSuccession.isAnalyticIsoOver_stageMap (fun i x hx => ?_) _
  obtain ⟨hq, hreg⟩ := centersOver_embeddedTriple M I hI hI₀ U hU i hx
  exact ⟨(mem_cosupport_comap_iff I (M.inclusion U) (isLocalDiffeomorph_inclusion M U) _).mp hq,
    fun h => hreg ((isRegularLocalRing_quotient_stalkIdeal_comap_iff I (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U) _).mpr h)⟩

omit hI hI₀ in
/-- **The exceptional divisors of a succession whose centres have simple normal crossings with
the exceptional families are the reduced ideal sheaves of those families**: every boundary
started at the empty boundary is the reduced ideal sheaf of the total transform of the empty
family at that stage (the chart form read in Hironaka's boundary form by
`hasOnlyNormalCrossingsWith_boundarySeq_of_forall_hasSncWith` and
`boundarySeq_eq_idealSheaf_totalTransformSeq_of_forall_lt`). -/
theorem boundarySeq_top_eq_idealSheaf_totalTransformSeq_of_forall_hasSncWith
    {M' : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (S : FiniteSuccession M')
    (h1b : ∀ i : Fin S.length, (S.totalTransformSeq i.castSucc).HasSncWith
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (S.center i).support (S.codim i))
    (i : Fin (S.length + 1)) : S.boundarySeq ⊤ i = (S.totalTransformSeq i).idealSheaf := by
  have h3' : ∀ (k : ℕ) (i : Fin S.length), i.1 < k →
      (S.boundarySeq (⊤ : M'.IdealSheaf) i.castSucc).HasOnlyNormalCrossingsWith (S.center i) := by
    have h := FiniteSuccession.hasOnlyNormalCrossingsWith_boundarySeq_of_forall_hasSncWith
      (ψ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (S := S)
      (HypersurfaceFamily.isSnc_empty (ψ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
      (fun i => h1b i)
    rwa [HypersurfaceFamily.idealSheaf_empty (ψ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))]
      at h
  exact FiniteSuccession.boundarySeq_eq_idealSheaf_totalTransformSeq_of_forall_lt
    (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) i fun i' _ => h3' (S.length + 1) i' (by omega)

/-- **The exceptional divisors are the reduced ideal sheaves of the exceptional families**: on
every relatively compact open, every boundary started at the empty boundary is the reduced ideal
sheaf of the total transform of the empty family at that stage, since every centre has simple
normal crossings with the exceptional family in the chart form (clause (1) of
`concreteBEDanFamStar_isEmbeddedDesing`;
`boundarySeq_top_eq_idealSheaf_totalTransformSeq_of_forall_hasSncWith`). -/
theorem boundarySeq_seqOn_embeddedDesingPiecesOfNonzero (U : Opens M)
    (hU : IsCompact (closure (U : Set M)))
    (i : Fin (((embeddedDesingPiecesOfNonzero M I hI hI₀).seqOn U hU).toSuccession.length + 1)) :
    ((embeddedDesingPiecesOfNonzero M I hI hI₀).seqOn U hU).toSuccession.boundarySeq ⊤ i =
      (((embeddedDesingPiecesOfNonzero M I hI hI₀).seqOn U hU).toSuccession.totalTransformSeq
        i).idealSheaf :=
  boundarySeq_top_eq_idealSheaf_totalTransformSeq_of_forall_hasSncWith _
    ((concreteBEDanFamStar_isEmbeddedDesing.{u} 𝕜).1 n (embeddedTriple I hI₀)
      (domBEDan_embeddedTriple I hI hI₀) U hU).2.1 i

/-- **Every centre of codimension at most one of a piece lies in the exceptional divisor of its
stage, and has codimension one** ([Wlo09, Remarks (1) and (2) after Theorem 2.0.3]): the centres
lie over `Sing(Y)` (`centersOver_embeddedTriple`), have simple normal crossings with the
exceptional families (clause (1) of `concreteBEDanFamStar_isEmbeddedDesing`) and are nonempty
(`CompatibleFamily.noEmptyCenters`); `boundarySeq_le_center_of_codim_le_one`. -/
theorem boundarySeq_le_center_of_codim_le_one_seqOn_embeddedDesingPiecesOfNonzero (U : Opens M)
    (hU : IsCompact (closure (U : Set M)))
    (i : Fin ((embeddedDesingPiecesOfNonzero M I hI hI₀).seqOn U hU).toSuccession.length)
    {n' c : ℕ} (ψ' : (Fin n → 𝕜) ≃L[𝕜] (Fin n' → 𝕜)) (hc : c ≤ 1)
    (hC : IsClosedSubmanifold ψ'
      (((embeddedDesingPiecesOfNonzero M I hI hI₀).seqOn U hU).toSuccession.center i).support c) :
    c = 1 ∧ ∀ x,
      (((embeddedDesingPiecesOfNonzero M I hI hI₀).seqOn U hU).toSuccession.boundarySeq ⊤
        i.castSucc).stalkIdeal x ≤
      (((embeddedDesingPiecesOfNonzero M I hI hI₀).seqOn U hU).toSuccession.center i).stalkIdeal
        x := by
  have hbed := (concreteBEDanFamStar_isEmbeddedDesing.{u} 𝕜).1 n (embeddedTriple I hI₀)
    (domBEDan_embeddedTriple I hI hI₀) U hU
  have hne : (((embeddedDesingPiecesOfNonzero M I hI hI₀).seqOn U hU).toSuccession.center
      i).support.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply (embeddedDesingPiecesOfNonzero M I hI hI₀).noEmptyCenters U hU i
    refine Manifold.IdealSheaf.ext fun x => ?_
    rw [Manifold.IdealSheaf.stalkIdeal_top]
    by_contra hx
    exact (Set.eq_empty_iff_forall_notMem.mp h) x hx
  exact FiniteSuccession.boundarySeq_le_center_of_codim_le_one _ (I.restrict U)
    (Manifold.IdealSheaf.isReduced_pullback_of_isLocalDiffeomorph _
      (isLocalDiffeomorph_inclusion M U) hI)
    (centersOver_embeddedTriple M I hI hI₀ U hU) i (hbed.1 i.castSucc) (hbed.2.1 i)
    (boundarySeq_seqOn_embeddedDesingPiecesOfNonzero M I hI hI₀ U hU i.castSucc) hne ψ' hc hC

/-- **Over every relatively compact open the embedded desingularization desingularizes `Y`**
(`IdealSheaf.IsDesingularizedBy`, [Wlo09, Theorem 2.0.2 (1)–(3), (6)]): clauses (1), (2), (3)
and (6) of `concreteBEDanFamStar_isEmbeddedDesing` on the open, (1) read in Hironaka's boundary
form and (3) in its transversal form (`IsEmbeddedDesing.isProperSnc`); the support of the last
exceptional divisor is the preimage of `Sing(Y)`: it lies over the centres, hence over `Sing(Y)`,
and at a point off it of the preimage of `Y` the strict transform passes and the composite
blow-down is an isomorphism near the point, so the point maps to a simple point of `Y` exactly
when the strict transform, which is smooth, is non-singular there. -/
theorem isDesingularizedBy_seqOn_embeddedDesingPiecesOfNonzero (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    (I.restrict U).IsDesingularizedBy
      ((embeddedDesingPiecesOfNonzero M I hI hI₀).seqOn U hU).toSuccession := by
  set T := embeddedTriple I hI₀
  have hT : DomBEDan 𝕜 T := domBEDan_embeddedTriple I hI hI₀
  have hbed := concreteBEDanFamStar_isEmbeddedDesing.{u} 𝕜
  obtain ⟨h1a, -, h2, h3a, -, h6⟩ := hbed.1 n T hT U hU
  obtain ⟨-, hps⟩ := BEDanFamStar.IsEmbeddedDesing.isProperSnc hbed n T hT U hU
  set S := ((((concreteBEDanFamStar.{u} 𝕜).fam n).fam T hT).seqOn U hU).toSuccession with hS
  change (I.restrict U).IsDesingularizedBy S
  have hZ := centersOver_embeddedTriple M I hI hI₀ U hU
  -- the exceptional divisors are the reduced ideal sheaves of the total transforms
  have hbd : ∀ i : Fin (S.length + 1),
      S.boundarySeq (⊤ : (M.restrict U).IdealSheaf) i = (S.totalTransformSeq i).idealSheaf :=
    boundarySeq_seqOn_embeddedDesingPiecesOfNonzero M I hI hI₀ U hU
  have h1b : ∀ i : Fin S.length, (S.totalTransformSeq i.castSucc).HasSncWith
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (S.center i).support (S.codim i) :=
    (hbed.1 n T hT U hU).2.1
  refine ⟨fun i => FiniteSuccession.center_isNonsingular S i,
    ⟨fun i => ⟨n, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜), S.totalTransformSeq i.castSucc,
      S.codim i, h1a i.castSucc, (hbd i.castSucc).symm, h1b i⟩,
    ⟨n, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜), S.totalTransformSeq (Fin.last _),
      h1a (Fin.last _), (hbd (Fin.last _)).symm⟩⟩, fun i x hx => (hZ i hx).2, ?_,
    IdealSheaf.isNonsingular_of_isNonsingular_toAnalyticSpace _ h3a,
    ⟨n, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜), S.totalTransformSeq (Fin.last _),
      h1a (Fin.last _), (hbd (Fin.last _)).symm, hps⟩,
    ⟨n, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜), S.totalTransformSeq (Fin.last _),
      h1a (Fin.last _), (hbd (Fin.last _)).symm, h6⟩⟩
  -- the support of the last exceptional divisor is the preimage of `Sing(Y)`
  rw [hbd (Fin.last _), (h1a (Fin.last _)).cosupport_idealSheaf]
  refine Set.Subset.antisymm
    (S.support_totalTransformSeq_subset_preimage_of_centersOver hZ (Fin.last _)) ?_
  rintro z ⟨hzY, hzreg⟩
  by_contra hzE
  -- off `E_r`, `z` lies on `Ỹ`, which is non-singular, so `σ z` is a simple point of `Y`
  have hzY' : z ∈ (S.strictTransformSubspaceSeq (I.restrict U) (Fin.last _)).support := by
    change (S.strictTransformSubspaceSeq (I.restrict U) (Fin.last _)).stalkIdeal z ≠ ⊤
    rw [S.stalkIdeal_strictTransformSubspaceSeq_eq_map_of_notMem_support _ _ hzE, Ne,
      Ideal.map_eq_top_iff_of_bijective _ (S.germMap_stageMap_bijective_of_notMem_support _ hzE)]
    exact hzY
  exact hzreg ((S.isRegularLocalRing_quotient_strictTransformSubspaceSeq_iff_of_notMem_support
    (I.restrict U) (Fin.last _) hzE).mp
    (IdealSheaf.isNonsingular_of_isNonsingular_toAnalyticSpace _ h3a z hzY'))

/-- Over every compact the embedded desingularization desingularizes `Y`: the case of the
neighbourhood of the compact (`isDesingularizedBy_seqOn_embeddedDesingPiecesOfNonzero`). -/
theorem isDesingularizedBy_embeddedDesingFamOfNonzero (K : Compacts M) :
    (I.restrict ((embeddedDesingFamOfNonzero M I hI hI₀).nhd K)).IsDesingularizedBy
      ((embeddedDesingFamOfNonzero M I hI hI₀).seq K) :=
  isDesingularizedBy_seqOn_embeddedDesingPiecesOfNonzero M I hI hI₀ _ _

/-! ### The restriction of an ideal sheaf made the unit ideal on its zero components -/

omit hI hI₀ in
/-- On the preimage of the zero components, the restriction of `𝓘_Y` to an open vanishes. -/
theorem stalkIdeal_restrict_of_mem_zeroLocus (U : Opens M) (x : M.restrict U)
    (hx : M.inclusion U x ∈ I.zeroLocus) : (I.restrict U).stalkIdeal x = ⊥ := by
  change (I.pullback (M.inclusion U) (M.inclusion U).contMDiff).stalkIdeal x = ⊥
  rw [Manifold.IdealSheaf.stalkIdeal_pullback, show I.stalkIdeal (M.inclusion U x) = ⊥ from hx,
    Ideal.map_bot]

omit hI hI₀ in
/-- On the preimage of the zero components, the restriction of `𝓘_Y` made the unit ideal there
is the unit ideal. -/
theorem stalkIdeal_restrict_unitOnZeroStalks_of_mem_zeroLocus (U : Opens M) (x : M.restrict U)
    (hx : M.inclusion U x ∈ I.zeroLocus) : (I.unitOnZeroStalks.restrict U).stalkIdeal x = ⊤ := by
  change (I.unitOnZeroStalks.pullback (M.inclusion U) (M.inclusion U).contMDiff).stalkIdeal x = ⊤
  rw [Manifold.IdealSheaf.stalkIdeal_pullback, I.stalkIdeal_unitOnZeroStalks_of_eq_bot hx,
    Ideal.map_top]

omit hI hI₀ in
/-- Off the preimage of the zero components, the restrictions of `𝓘_Y` and of `𝓘_Y` made the
unit ideal on its zero components agree. -/
theorem stalkIdeal_restrict_eq_restrict_unitOnZeroStalks_of_notMem_zeroLocus (U : Opens M)
    (x : M.restrict U) (hx : M.inclusion U x ∉ I.zeroLocus) :
    (I.restrict U).stalkIdeal x = (I.unitOnZeroStalks.restrict U).stalkIdeal x := by
  change (I.pullback (M.inclusion U) (M.inclusion U).contMDiff).stalkIdeal x =
    (I.unitOnZeroStalks.pullback (M.inclusion U) (M.inclusion U).contMDiff).stalkIdeal x
  rw [Manifold.IdealSheaf.stalkIdeal_pullback, Manifold.IdealSheaf.stalkIdeal_pullback,
    I.stalkIdeal_unitOnZeroStalks_of_ne_bot hx]

/-! ### The embedded desingularization of an arbitrary reduced closed subspace -/

omit hI₀ in
/-- **The pieces of the embedded desingularization of a reduced closed subspace `Y`**: those of
`𝓘_Y` made the unit ideal on the connected components of `M` where it vanishes
(`IdealSheaf.unitOnZeroStalks`), which is reduced with nonzero stalks. -/
abbrev embeddedDesingPieces :
    CompatibleFamily (embeddedTriple I.unitOnZeroStalks I.isNonzeroEverywhere_unitOnZeroStalks) :=
  embeddedDesingPiecesOfNonzero M I.unitOnZeroStalks (I.isReduced_unitOnZeroStalks hI)
    I.isNonzeroEverywhere_unitOnZeroStalks

omit hI₀ in
/-- **The embedded desingularization of a reduced closed subspace `Y` as one family over `M`**
([Wlo09, Theorem 2.0.2]): the pieces of `Y` (`embeddedDesingPieces`) glued along the exhaustion
of `M`. -/
def embeddedDesingFam : ExtensionCompatibleFamily M :=
  embeddedDesingFamOfNonzero M I.unitOnZeroStalks (I.isReduced_unitOnZeroStalks hI)
    I.isNonzeroEverywhere_unitOnZeroStalks

omit hI₀ in
/-- The blow-down of the embedded desingularization is proper. -/
theorem isProperMap_embeddedDesingFam_map : IsProperMap (embeddedDesingFam M I hI).map :=
  isProperMap_embeddedDesingFamOfNonzero_map _ _ _ _

omit hI₀ in
/-- **The blow-down of the embedded desingularization is an isomorphism off `Sing(Y)`**: the
singular locus of `𝓘_Y` made the unit ideal on its zero components is that of `Y`
(`support_diff_regularLocus_unitOnZeroStalks`). -/
theorem isAnalyticIsoOver_embeddedDesingFam_map :
    (embeddedDesingFam M I hI).map.IsIsoOver (I.support \ I.regularLocus)ᶜ := by
  have h := isAnalyticIsoOver_embeddedDesingFamOfNonzero_map M I.unitOnZeroStalks
    (I.isReduced_unitOnZeroStalks hI) I.isNonzeroEverywhere_unitOnZeroStalks
  rwa [I.support_diff_regularLocus_unitOnZeroStalks] at h

omit hI₀ in
/-- **Over every relatively compact open the embedded desingularization desingularizes `Y`**
(`IdealSheaf.IsDesingularizedBy`, [Wlo09, Theorem 2.0.2 (1)–(3), (6)]): the clauses for `𝓘_Y`
made the unit ideal on its zero components
(`isDesingularizedBy_seqOn_embeddedDesingPiecesOfNonzero`) transfer to `𝓘_Y`
(`IsDesingularizedBy.of_eq_off_clopen`): the two ideal sheaves agree off the clopen set of zero
components, where the one is zero and the other the unit ideal, and the centres lie over the
singular locus (`centersOver_embeddedTriple`). -/
theorem isDesingularizedBy_seqOn_embeddedDesingPieces (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    (I.restrict U).IsDesingularizedBy ((embeddedDesingPieces M I hI).seqOn U hU).toSuccession :=
  IdealSheaf.IsDesingularizedBy.of_eq_off_clopen (I' := I.unitOnZeroStalks.restrict U)
    (Z := ⇑(M.inclusion U) ⁻¹' I.zeroLocus)
    (I.isClopen_zeroLocus.preimage (M.inclusion U).contMDiff.continuous)
    (fun x hx => stalkIdeal_restrict_of_mem_zeroLocus M I U x hx)
    (fun x hx => stalkIdeal_restrict_unitOnZeroStalks_of_mem_zeroLocus M I U x hx)
    (fun x hx => stalkIdeal_restrict_eq_restrict_unitOnZeroStalks_of_notMem_zeroLocus M I U x hx)
    (isDesingularizedBy_seqOn_embeddedDesingPiecesOfNonzero M I.unitOnZeroStalks
      (I.isReduced_unitOnZeroStalks hI) I.isNonzeroEverywhere_unitOnZeroStalks U hU)
    (centersOver_embeddedTriple M I.unitOnZeroStalks (I.isReduced_unitOnZeroStalks hI)
      I.isNonzeroEverywhere_unitOnZeroStalks U hU)

omit hI₀ in
/-- Over every compact the embedded desingularization desingularizes `Y`: the case of the
neighbourhood of the compact (`isDesingularizedBy_seqOn_embeddedDesingPieces`). -/
theorem isDesingularizedBy_embeddedDesingFam (K : Compacts M) :
    (I.restrict ((embeddedDesingFam M I hI).nhd K)).IsDesingularizedBy
      ((embeddedDesingFam M I hI).seq K) :=
  isDesingularizedBy_seqOn_embeddedDesingPieces M I hI _ _

omit hI₀ in
/-- **No centre of the succession over a compact is empty**: the pieces are produced with the
empty blow-ups erased (`CompatibleFamily.noEmptyCenters`). -/
theorem center_ne_top_seq_embeddedDesingFam (K : Compacts M)
    (i : Fin ((embeddedDesingFam M I hI).seq K).length) :
    ((embeddedDesingFam M I hI).seq K).center i ≠ ⊤ :=
  (embeddedDesingPieces M I hI).noEmptyCenters _ _ i

omit hI₀ in
/-- **Every centre of codimension at most one of the succession over a compact lies in the
exceptional divisor of its stage, and has codimension one**
(`boundarySeq_le_center_of_codim_le_one_seqOn_embeddedDesingPiecesOfNonzero` for `𝓘_Y` made the unit
ideal on its
zero components, whose family the family of `𝓘_Y` is). -/
theorem boundarySeq_le_center_of_codim_le_one_embeddedDesingFam (K : Compacts M)
    (i : Fin ((embeddedDesingFam M I hI).seq K).length) {n' c : ℕ}
    (ψ' : (Fin n → 𝕜) ≃L[𝕜] (Fin n' → 𝕜)) (hc : c ≤ 1)
    (hC : IsClosedSubmanifold ψ' (((embeddedDesingFam M I hI).seq K).center i).support c) :
    c = 1 ∧ ∀ x, (((embeddedDesingFam M I hI).seq K).boundarySeq ⊤ i.castSucc).stalkIdeal x ≤
      (((embeddedDesingFam M I hI).seq K).center i).stalkIdeal x :=
  boundarySeq_le_center_of_codim_le_one_seqOn_embeddedDesingPiecesOfNonzero M I.unitOnZeroStalks
    (I.isReduced_unitOnZeroStalks hI) I.isNonzeroEverywhere_unitOnZeroStalks _ _ i ψ' hc hC

omit hI₀ in
/-- **The transversal chart clause (3) with the last exceptional family named**: at every point
of the last strict transform of `Y ∩ U` there is a chart adapted to it which is a simple normal
crossings chart of the last exceptional family, the coordinates of the strict transform among
those of no member (`IsEmbeddedDesing.isProperSnc` for `𝓘_Y` made the unit ideal on its zero
components, transferred by `exists_adaptedChart_strictTransformSubspaceSeq_of_eq_off_clopen`). -/
theorem exists_adaptedChart_seqOn_embeddedDesingPieces (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    ∀ a ∈ (((embeddedDesingPieces M I hI).seqOn U hU).toSuccession.strictTransformSubspaceSeq
        (I.restrict U) (Fin.last _)).support,
      ∃ (c : ℕ) (φ : OpenPartialHomeomorph (((embeddedDesingPieces M I hI).seqOn U hU).stage
          (Fin.last _)) (Fin n → 𝕜)) (σ : Fin c ↪ Fin n)
        (cidx : {j // a ∈ (((embeddedDesingPieces M I hI).seqOn U hU).toSuccession.totalTransformSeq
          (Fin.last _)).hyp j} → Fin n),
        IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (((embeddedDesingPieces M I hI).seqOn U hU).toSuccession.strictTransformSubspaceSeq
            (I.restrict U) (Fin.last _)).support φ σ ∧
        (((embeddedDesingPieces M I hI).seqOn U hU).toSuccession.totalTransformSeq
          (Fin.last _)).IsSncChartAt (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ a cidx ∧
        ∀ j, cidx j ∉ Set.range σ := by
  set I' := I.unitOnZeroStalks with hI'def
  have hI' : I'.IsReduced := I.isReduced_unitOnZeroStalks hI
  have hI'₀ : I'.IsNonzeroEverywhere := I.isNonzeroEverywhere_unitOnZeroStalks
  set T := embeddedTriple I' hI'₀
  have hT : DomBEDan 𝕜 T := domBEDan_embeddedTriple I' hI' hI'₀
  have hbed := concreteBEDanFamStar_isEmbeddedDesing.{u} 𝕜
  obtain ⟨h1a, -, -, -, -, -⟩ := hbed.1 n T hT U hU
  obtain ⟨-, hps⟩ := BEDanFamStar.IsEmbeddedDesing.isProperSnc hbed n T hT U hU
  exact FiniteSuccession.exists_adaptedChart_strictTransformSubspaceSeq_of_eq_off_clopen _
    (I.isClopen_zeroLocus.preimage (M.inclusion U).contMDiff.continuous)
    (fun x hx => stalkIdeal_restrict_of_mem_zeroLocus M I U x hx)
    (fun x hx => stalkIdeal_restrict_unitOnZeroStalks_of_mem_zeroLocus M I U x hx)
    (fun x hx => stalkIdeal_restrict_eq_restrict_unitOnZeroStalks_of_notMem_zeroLocus M I U x hx)
    (centersOver_embeddedTriple M I' hI' hI'₀ U hU) (h1a (Fin.last _)) hps

omit hI₀ in
/-- **The monomial clause (6) with the last exceptional family named**: at every point of the
last stage, `σ^*(𝓘_Y) = I_Ỹ · ∏ I_{E^j}^{α_j}` over the members of the last exceptional family
through the point (clause (6) of `concreteBEDanFamStar_isEmbeddedDesing` for `𝓘_Y` made the unit
ideal on its zero components, transferred by
`exists_monomial_strictTransformSubspaceSeq_of_eq_off_clopen`). -/
theorem exists_monomial_seqOn_embeddedDesingPieces (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    ∀ x : ((embeddedDesingPieces M I hI).seqOn U hU).stage (Fin.last _),
      ∃ (s : Finset (((embeddedDesingPieces M I hI).seqOn U hU).toSuccession.totalTransformSeq
          (Fin.last _)).ι)
        (α : (((embeddedDesingPieces M I hI).seqOn U hU).toSuccession.totalTransformSeq
          (Fin.last _)).ι → ℕ),
        (∀ j ∈ s, x ∈ (((embeddedDesingPieces M I hI).seqOn U hU).toSuccession.totalTransformSeq
          (Fin.last _)).hyp j) ∧
        ((I.restrict U).pullback ((embeddedDesingPieces M I hI).seqOn U hU).toSuccession.composite
            ((embeddedDesingPieces M I hI).seqOn U hU).toSuccession.composite.contMDiff).stalkIdeal
            x =
          (((embeddedDesingPieces M I hI).seqOn U hU).toSuccession.strictTransformSubspaceSeq
              (I.restrict U) (Fin.last _)).stalkIdeal x *
            ∏ j ∈ s, Manifold.vanishingStalk
              ((((embeddedDesingPieces M I hI).seqOn U hU).toSuccession.totalTransformSeq
                (Fin.last _)).hyp j) x ^ α j := by
  set I' := I.unitOnZeroStalks with hI'def
  have hI' : I'.IsReduced := I.isReduced_unitOnZeroStalks hI
  have hI'₀ : I'.IsNonzeroEverywhere := I.isNonzeroEverywhere_unitOnZeroStalks
  set T := embeddedTriple I' hI'₀
  have hT : DomBEDan 𝕜 T := domBEDan_embeddedTriple I' hI' hI'₀
  obtain ⟨-, -, -, -, -, h6⟩ := (concreteBEDanFamStar_isEmbeddedDesing.{u} 𝕜).1 n T hT U hU
  exact FiniteSuccession.exists_monomial_strictTransformSubspaceSeq_of_eq_off_clopen _
    (fun x hx => stalkIdeal_restrict_of_mem_zeroLocus M I U x hx)
    (fun x hx => stalkIdeal_restrict_unitOnZeroStalks_of_mem_zeroLocus M I U x hx)
    (fun x hx => stalkIdeal_restrict_eq_restrict_unitOnZeroStalks_of_notMem_zeroLocus M I U x hx)
    (centersOver_embeddedTriple M I' hI' hI'₀ U hU) h6

omit hI₀ in
/-- **The embedded desingularization on the standard model commutes with local analytic
isomorphisms**, over every pair of compacts ([Wlo09, Theorem 2.0.2 (4)]; the form of
[Wlo09, Theorem 3.5.1 (2)]): for a local analytic isomorphism `g : N → M` and `J = g^* I`, the
succession over `U_{K'}` is the pull-back along `g` of the succession over `U_K` up to empty
blow-ups whenever `g(U_{K'}) ⊆ U_K`. The triple of `J` made the unit ideal on its zero components
carries the pull-back data of that of `I` (`unitOnZeroStalks_pullback_of_isLocalDiffeomorph`),
so the values of the functor correspond (`CommutesWithLocalIsos`), and
`CompatibleFamily.isPullbackUpToEmptyAlong_seqOn` reads the pull-back predicate. -/
theorem isPullbackUpToEmptyAlong_embeddedDesingFam {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g)
    (J : IdealSheaf N) (hJ : J.IsReduced) (hIJ : J = I.pullback g g.contMDiff)
    (K' : Compacts N) (K : Compacts M)
    (hK : ⇑g '' ((embeddedDesingFam N J hJ).nhd K' : Set N) ⊆ (embeddedDesingFam M I hI).nhd K) :
    ((embeddedDesingFam N J hJ).seq K').IsPullbackUpToEmptyAlong
      ((embeddedDesingFam M I hI).seq K) g := by
  have hpb : (embeddedTriple J.unitOnZeroStalks J.isNonzeroEverywhere_unitOnZeroStalks).IsPullbackOf
      (embeddedTriple I.unitOnZeroStalks I.isNonzeroEverywhere_unitOnZeroStalks) g := by
    refine ⟨?_, (HypersurfaceFamily.empty_comap ⇑g).symm⟩
    subst hIJ
    exact I.unitOnZeroStalks_pullback_of_isLocalDiffeomorph g hg
  exact CompatibleFamily.isPullbackUpToEmptyAlong_seqOn
    (((concreteBEDanFamStar.{u} 𝕜).fam n).fam
      (embeddedTriple I.unitOnZeroStalks I.isNonzeroEverywhere_unitOnZeroStalks)
      (domBEDan_embeddedTriple _ (I.isReduced_unitOnZeroStalks hI) _))
    (((concreteBEDanFamStar.{u} 𝕜).fam n).fam
      (embeddedTriple J.unitOnZeroStalks J.isNonzeroEverywhere_unitOnZeroStalks)
      (domBEDan_embeddedTriple _ (J.isReduced_unitOnZeroStalks hJ) _))
    g hg _ (isCompact_closure_relCompactOpen (exhaustion N) _)
    ((concreteBEDanFamStar_isEmbeddedDesing.{u} 𝕜).2 n _ _ g hg hpb _ _ _ _) _
    (isCompact_closure_relCompactOpen (exhaustion M) _) hK

end Hironaka.Manifold

end

end
