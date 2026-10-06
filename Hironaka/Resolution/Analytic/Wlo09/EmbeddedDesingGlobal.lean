/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.EmbeddedDesingModel
public import Hironaka.Resolution.Analytic.Wlo09.GlobalObjects
public import Hironaka.Resolution.Analytic.ModelTransport.Family
import Hironaka.Resolution.Analytic.Wlo09.Clauses

/-!
# Włodarczyk's divisor `E` and strict transform `Ỹ` for the embedded desingularization

The global objects of [Wlo09, Theorem 2.0.2] for the embedded desingularization of a reduced
closed subspace `Y` on the standard model (`embeddedDesingFam`,
`Hironaka/Resolution/Analytic/Wlo09/EmbeddedDesingModel.lean`): the exceptional divisor
`embeddedDesingExceptional` and the strict transform `embeddedDesingStrictTransform` on the glued
space `M̃`, the glued objects of `Hironaka/Resolution/Analytic/Wlo09/GlobalObjects.lean` for the
pieces `embeddedDesingPieces` of the family. The per-piece hypotheses of that module are the
clauses of the concrete functor on the pieces (`concreteBEDanFamStar_isEmbeddedDesing`), the
identification of the boundaries with the reduced ideal sheaves of the exceptional families
(`boundarySeq_seqOn_embeddedDesingPiecesOfNonzero`), the desingularization clauses for `𝓘_Y`
(`isDesingularizedBy_seqOn_embeddedDesingPieces`) and the transversal chart and monomial clauses
with the last exceptional family named (`exists_adaptedChart_seqOn_embeddedDesingPieces`,
`exists_monomial_seqOn_embeddedDesingPieces`):

* `isGloballyDesingularizedBy_embeddedDesingFam`: `E` and `Ỹ` are the exceptional divisor and the
  strict transform of the embedded desingularization of `Y` by the family
  (`IdealSheaf.IsGloballyDesingularizedBy`, defined in
  `Hironaka/Resolution/Analytic/ModelTransport/Family.lean`), with the clauses (1), (3), (6) on
  `M̃`, restricting over every compact to the last exceptional divisor and the last strict
  transform;
* `isLocallyFinitelyDesingularizedBy_embeddedDesingFam`: the family is a locally finite embedded
  desingularization of `Y` (`IdealSheaf.IsLocallyFinitelyDesingularizedBy`).

For any compatible family whose successions desingularize `Y` over every compact, divisors `E`
and `Ỹ` on `M̃` with the clauses of `IsGloballyDesingularizedBy` have the remaining properties of
[Wlo09, Theorem 2.0.2] on `M̃`, read on the pieces through `toSpace`: `E` is a simple normal
crossings divisor (`IsGloballyDesingularizedBy.isSncBoundary`) with support `res_{Y,M}⁻¹(Sing Y)`
(`IsGloballyDesingularizedBy.support_eq`), and `Ỹ` is smooth
(`IsGloballyDesingularizedBy.isNonsingular`).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.IdealSheaf.IsGloballyDesingularizedBy

/-! ### The divisor and the strict transform on the glued space, from their restrictions -/

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} {I : IdealSheaf M} {F : ExtensionCompatibleFamily M}
  {D Y : IdealSheaf F.space}

/-- **`E` is a simple normal crossings divisor on `M̃`**: the hypersurface family of the transversal
clause. -/
theorem isSncBoundary (h : I.IsGloballyDesingularizedBy F D Y) : D.IsSncBoundary :=
  let ⟨n, ψ, G, hG, hGD, _⟩ := h.isSncBoundaryTransversalTo
  ⟨n, ψ, G, hG, hGD⟩

/-- **The support of `E` is `res_{Y,M}⁻¹(Sing Y)`**, the exceptional locus of
[Wlo09, Theorem 2.0.2], when the successions desingularize `Y` over every compact: a point `q` of
`M̃` lies in the image of the last stage over the singleton compact of `res_{Y,M}(q)`
(`exists_toSpace_eq`), where `E` is `E_r` (`pullback_toSpace_eq_boundarySeq`, read along the local
analytic isomorphism `toSpace`, `mem_cosupport_comap_iff`) and `|E_r| = σ_K⁻¹(Sing Y)`. -/
theorem support_eq (h : I.IsGloballyDesingularizedBy F D Y)
    (hdes : ∀ K : Compacts M, (I.restrict (F.nhd K)).IsDesingularizedBy (F.seq K)) :
    D.support = F.map ⁻¹' (I.support \ I.regularLocus) := by
  ext q
  have hq := F.map_mem_nhd_singletonCompact q
  generalize ExtensionCompatibleFamily.singletonCompact (F.map q) = K at hq
  obtain ⟨x, rfl⟩ := F.exists_toSpace_eq K hq
  set U := F.nhd K
  have h1 : F.toSpace K x ∈ D.support ↔
      x ∈ ((F.seq K).boundarySeq ⊤ (Fin.last _)).support := by
    rw [← h.pullback_toSpace_eq_boundarySeq K]
    exact (mem_cosupport_comap_iff D (F.toSpace K) (F.isLocalDiffeomorph_toSpace K) x).symm
  rw [h1, (hdes K).support_boundarySeq_last, Set.mem_preimage, Set.mem_preimage,
    F.map_toSpace_apply]
  have key : ∀ y : M.restrict U, y ∈ (I.restrict U).support \ (I.restrict U).regularLocus ↔
      M.inclusion U y ∈ I.support \ I.regularLocus := fun y =>
    have hU := Manifold.isLocalDiffeomorph_inclusion M U
    and_congr (mem_cosupport_comap_iff I (M.inclusion U) hU y)
      (not_congr (isRegularLocalRing_quotient_stalkIdeal_comap_iff I (M.inclusion U) hU y))
  exact key ((F.seq K).composite x)

/-- **`Ỹ` is smooth**, when the successions desingularize `Y` over every compact: at a point `q`
of `Ỹ`, in the image of the last stage over the singleton compact of `res_{Y,M}(q)`
(`exists_toSpace_eq`), the local ring of `Ỹ` is that of the smooth `Y_r`
(`pullback_toSpace_eq_strictTransform`, `isRegularLocalRing_quotient_stalkIdeal_comap_iff`). -/
theorem isNonsingular (h : I.IsGloballyDesingularizedBy F D Y)
    (hdes : ∀ K : Compacts M, (I.restrict (F.nhd K)).IsDesingularizedBy (F.seq K)) :
    Y.IsNonsingular := by
  intro q hq
  have hqK := F.map_mem_nhd_singletonCompact q
  generalize ExtensionCompatibleFamily.singletonCompact (F.map q) = K at hqK
  obtain ⟨x, rfl⟩ := F.exists_toSpace_eq K hqK
  have hx : x ∈ ((F.seq K).strictTransformSubspaceSeq (I.restrict (F.nhd K))
      (Fin.last _)).support := by
    rw [← h.pullback_toSpace_eq_strictTransform K]
    exact (mem_cosupport_comap_iff Y (F.toSpace K) (F.isLocalDiffeomorph_toSpace K) x).mpr hq
  have key := (isRegularLocalRing_quotient_stalkIdeal_comap_iff Y (F.toSpace K)
    (F.isLocalDiffeomorph_toSpace K) x).mp
  rw [h.pullback_toSpace_eq_strictTransform K] at key
  exact key ((hdes K).isNonsingular_strictTransform x hx)

end AnalyticManifold.IdealSheaf.IsGloballyDesingularizedBy

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜))
  (I : IdealSheaf M) (hI : I.IsReduced)

/-- **Włodarczyk's exceptional divisor `E` on `M̃`** for the embedded desingularization of `Y`:
the reduced ideal sheaf of the exceptional families of the pieces, glued along the exhaustion
(`CompatibleFamily.gluedExceptionalIdeal`). -/
def embeddedDesingExceptional : IdealSheaf (embeddedDesingFam M I hI).space :=
  (embeddedDesingPieces M I hI).gluedExceptionalIdeal

/-- **Włodarczyk's strict transform `Ỹ` on `M̃`** for the embedded desingularization of `Y`: the
saturation of the total transform of `𝓘_Y` by the exceptional divisor
(`CompatibleFamily.globalStrictTransform`). -/
def embeddedDesingStrictTransform : IdealSheaf (embeddedDesingFam M I hI).space :=
  (embeddedDesingPieces M I hI).globalStrictTransform I

/-- **`E` and `Ỹ` are the exceptional divisor and the strict transform of the embedded
desingularization of `Y`** (`IdealSheaf.IsGloballyDesingularizedBy`,
[Wlo09, Theorem 2.0.2 (1), (3), (6)]): the clauses of the glued objects
(`isSncBoundaryTransversalTo_globalStrictTransform`, `isMulBoundaryMonomial_globalStrictTransform`)
and their identifications on the pieces
(`gluedExceptionalIdeal_pullback_toLimitMap`, `globalStrictTransform_pullback_toLimitMap`),
from the clauses of the concrete functor on the pieces. -/
theorem isGloballyDesingularizedBy_embeddedDesingFam :
    I.IsGloballyDesingularizedBy (embeddedDesingFam M I hI) (embeddedDesingExceptional M I hI)
      (embeddedDesingStrictTransform M I hI) := by
  have hI' : I.unitOnZeroStalks.IsReduced := I.isReduced_unitOnZeroStalks hI
  have hI'₀ : I.unitOnZeroStalks.IsNonzeroEverywhere := I.isNonzeroEverywhere_unitOnZeroStalks
  have hbed := concreteBEDanFamStar_isEmbeddedDesing.{u} 𝕜
  have hsnc : ∀ m, ((embeddedDesingPieces M I hI).excLevel m).IsSnc
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := fun m =>
    (hbed.1 n (embeddedTriple I.unitOnZeroStalks hI'₀) (domBEDan_embeddedTriple _ hI' hI'₀)
      (relCompactOpen (exhaustion M) m) (isCompact_closure_relCompactOpen _ _)).1 (Fin.last _)
  have hbd : ∀ m, ((embeddedDesingPieces M I hI).seqLevel m).boundarySeq ⊤ (Fin.last _) =
      ((embeddedDesingPieces M I hI).excLevel m).idealSheaf := fun m =>
    boundarySeq_seqOn_embeddedDesingPiecesOfNonzero M I.unitOnZeroStalks hI' hI'₀ _ _ (Fin.last _)
  have hdes : ∀ m, (I.restrict (relCompactOpen (exhaustion M) m)).IsDesingularizedBy
      ((embeddedDesingPieces M I hI).seqLevel m) := fun m =>
    isDesingularizedBy_seqOn_embeddedDesingPieces M I hI _ _
  have htr := fun m => exists_adaptedChart_seqOn_embeddedDesingPieces M I hI
    (relCompactOpen (exhaustion M) m) (isCompact_closure_relCompactOpen _ _)
  have hmon := fun m => exists_monomial_seqOn_embeddedDesingPieces M I hI
    (relCompactOpen (exhaustion M) m) (isCompact_closure_relCompactOpen _ _)
  exact ⟨(embeddedDesingPieces M I hI).isSncBoundaryTransversalTo_globalStrictTransform hsnc hbd I
      hdes htr,
    (embeddedDesingPieces M I hI).isMulBoundaryMonomial_globalStrictTransform hsnc hbd I hdes
      hmon,
    fun K => (embeddedDesingPieces M I hI).gluedExceptionalIdeal_pullback_toLimitMap hsnc hbd _,
    fun K => (embeddedDesingPieces M I hI).globalStrictTransform_pullback_toLimitMap hsnc hbd I
      hdes _⟩

/-- **The family is a locally finite embedded desingularization of `Y`**
(`IdealSheaf.IsLocallyFinitelyDesingularizedBy`): the three clauses per compact, the absence of
empty centres, the codimension of the centres
(`FiniteSuccession.two_le_codim_or_boundarySeq_le_center_iff`) and the global objects. -/
theorem isLocallyFinitelyDesingularizedBy_embeddedDesingFam :
    I.IsLocallyFinitelyDesingularizedBy (embeddedDesingFam M I hI) :=
  ⟨isProperMap_embeddedDesingFam_map M I hI, isAnalyticIsoOver_embeddedDesingFam_map M I hI,
    isDesingularizedBy_embeddedDesingFam M I hI, center_ne_top_seq_embeddedDesingFam M I hI,
    fun K i => (FiniteSuccession.two_le_codim_or_boundarySeq_le_center_iff _ i
      (center_ne_top_seq_embeddedDesingFam M I hI K i)).mpr
        (boundarySeq_le_center_of_codim_le_one_embeddedDesingFam M I hI K i),
    ⟨_, _, IdealSheaf.isGloballyDesingularizedBy_iff_and.mp
      (isGloballyDesingularizedBy_embeddedDesingFam M I hI)⟩⟩

end Hironaka.Manifold

end

end
