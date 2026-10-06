/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs
public import Hironaka.Manifold.Jacobian.Defs
public import Hironaka.Manifold.Resolution.Defs
public import Hironaka.Resolution.Analytic.ModelTransport.Succession
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.ModelTransport.SncFamily
public import Hironaka.Resolution.Analytic.ModelTransport.Square
public import Hironaka.Resolution.Analytic.ModelTransport.SuccessionExtension
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# A compatible family over the re-modelled manifold, read back on the manifold

Włodarczyk's compatible family of finite successions (`ExtensionCompatibleFamily`;
[Wlo09, Theorem 2.0.3 (1), (4); Definition 3.2.6])
constructed over the re-modelled manifold `M.transport ψ` (in the analytic main theorems the
standard model `Fin n → ℝ`, where the resolution `resolveFam` lives) is read back on `M`
(`transportBack`): the space
re-modelled along `ψ⁻¹`, the same map and the same neighbourhoods, each succession carried along the
identity of its neighbourhood (`transportAlong` of `Succession.lean` at the stage-`0` identification
`restrictTransportDiffeomorph`), the identification of the end results conjugated by the
identities, and the compatibility by `isExtensionOf_restrict_transportAlong`
(`SuccessionExtension.lean`). Every clause of the two manifold-level main theorems (Hironaka's
Main Theorem II''(N) and the real-analytic principalization with the Jacobian clause, at the ends
of `Hironaka/Resolution/Analytic/Wlo09/HironakaAssembly.lean` and
`Hironaka/Resolution/Analytic/BM97/JacobianAssembly.lean`) then transports, word for word:

* the map: properness (`isProperMap_map_transportBack_iff`, definitional), the divisor clause on
  `J.comap map` (`isNormalCrossingsDivisor_comap_map_transportBack_iff`), the Jacobian clause
  (`isNormalCrossingsDivisor_jacobianIdeal_mul_pullback_map_transportBack_iff`:
  `jacobianIdeal_of_square` on the square of `F.map` with the two identities — the Jacobian ideal
  of the transported map is the pull-back of the Jacobian ideal, no unit germ) and the isomorphism
  off the cosupport (`isAnalyticIsoOver_map_transportBack_iff`);
* per compact: the centres are non-singular (`isNonsingular_center_seq_transportBack_iff`), the
  boundaries have only normal crossings with the centres (the stalk-local forms
  `hasOnlyNormalCrossingsWith_boundarySeq_center_seq_transportBack_iff`,
  `hasOnlyNormalCrossings_boundarySeq_last_seq_transportBack_iff`, kept as general tools), the last
  weak transform is the unit ideal (`weakTransformSeq_last_seq_transportBack_eq_unit_iff`), the
  order of a weak transform at a point (`ord_weakTransformSeq_seq_transportBack`) and the support
  of a centre (`support_center_seq_transportBack`) — all through the pull-back identities
  `center_seq_transportBack`, `weakTransformSeq_seq_transportBack`, `boundarySeq_seq_transportBack`
  (the identities of `Succession.lean` with the restriction of the re-modelled sheaves,
  `restrictOpens_eq_pullbackDiffeomorph_transport`) and the predicate transports of
  `Hironaka/Resolution/Analytic/ModelTransport/IdealSheaf.lean`;
* the boundary clauses in the simple-normal-crossings family form: for fixed chart isomorphisms on
  the two models (`exists_isSnc_boundarySeq_hasSncWith_center_seq_transportBack_iff`,
  `exists_isSnc_boundarySeq_last_seq_transportBack_iff`, from `SncFamily.lean` along the stage
  identification) and in the predicates `IsSncBoundaryWith`/`IsSncBoundary` of the main theorems
  (`isSncBoundaryWith_boundarySeq_center_seq_transportBack_iff`,
  `isSncBoundary_boundarySeq_last_seq_transportBack_iff`, at the model isomorphism `ψ⁻¹`), the
  forms the proofs of the main theorems read;
* Włodarczyk's embedded desingularization ([Wlo09, Theorem 2.0.2]): the strict transforms of a
  closed subspace (`strictTransformSubspaceSeq_seq_transportBack`), the isomorphism off its
  singular locus (`isAnalyticIsoOver_compl_sing_map_transportBack_iff`), and all its clauses on the
  succession over a compact at once (`isDesingularizedBy_seq_transportBack`), and its divisor and
  strict transform on the glued space (`IdealSheaf.IsGloballyDesingularizedBy`, the clause
  `exists_divisor_strictTransform` of `IdealSheaf.IsLocallyFinitelyDesingularizedBy` as a
  structure, defined here; `isGloballyDesingularizedBy_transportBack`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Filter Topology Hironaka.Manifold Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.IdealSheaf

/-! ### The divisor and the strict transform of an embedded desingularization on `M̃` -/

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E}

/-- The ideal sheaves `E` and `Ỹ` on the space `M̃` of the compatible family `F` are **the
exceptional divisor and the strict transform of an embedded desingularization** of the closed
subspace `Y` of `M` with ideal sheaf `I` by `F` [Wlo09, Theorem 2.0.2]: with
`res_{Y,M} = F.map : M̃ → M`, `E` is the reduced ideal sheaf of a simple normal crossings family of
hypersurfaces of `M̃` with which `Ỹ` has simple normal crossings, transversally;
`res_{Y,M}^*(I_Y) = I_Ỹ · I_Ẽ` with `Ẽ` near every point an effective combination of the components
of `E`; and over the neighbourhood `U_K` of every compact `K ⊆ M`, read through the identification
`toSpace K` of the last stage `U_r` of the succession `F.seq K` with `res_{Y,M}⁻¹(U_K)`, `E` is the
last exceptional divisor `E_r` and `Ỹ` the last strict transform `Y_r` of `Y ∩ U_K`. The clause
`exists_divisor_strictTransform` of `IsLocallyFinitelyDesingularizedBy` as a structure
(`isGloballyDesingularizedBy_iff_and`). -/
@[mk_iff]
structure IsGloballyDesingularizedBy (I : IdealSheaf M) (F : ExtensionCompatibleFamily M)
    (E Y : IdealSheaf F.space) : Prop where
  /-- (1), (3) `E` is the reduced ideal sheaf of a simple normal crossings hypersurface family,
  with which `Ỹ` has simple normal crossings, transversally. -/
  isSncBoundaryTransversalTo : E.IsSncBoundaryTransversalTo Y
  /-- (6) `res_{Y,M}^*(I_Y) = I_Ỹ · I_Ẽ`, `Ẽ` a combination of the components of `E` near every
  point. -/
  isMulBoundaryMonomial : IsMulBoundaryMonomial (I.pullback F.map F.map.contMDiff) Y E
  /-- Over every compact `K`, `E` read on the last stage `U_r` of the succession over `U_K` is the
  last exceptional divisor `E_r`. -/
  pullback_toSpace_eq_boundarySeq : ∀ K : Compacts M,
    E.pullback (F.toSpace K) (F.toSpace K).contMDiff =
      (F.seq K).boundarySeq ⊤ (Fin.last (F.seq K).length)
  /-- Over every compact `K`, `Ỹ` read on the last stage `U_r` of the succession over `U_K` is the
  last strict transform `Y_r` of `Y ∩ U_K`. -/
  pullback_toSpace_eq_strictTransform : ∀ K : Compacts M,
    Y.pullback (F.toSpace K) (F.toSpace K).contMDiff =
      (F.seq K).strictTransformSubspaceSeq (I.restrict (F.nhd K)) (Fin.last (F.seq K).length)

/-- `IsGloballyDesingularizedBy` is the conjunction of the clause
`exists_divisor_strictTransform` of `IsLocallyFinitelyDesingularizedBy`, in its order: the
identifications over the compacts, then (1), (3) and (6) on `M̃`. -/
theorem isGloballyDesingularizedBy_iff_and {I : IdealSheaf M} {F : ExtensionCompatibleFamily M}
    {E Y : IdealSheaf F.space} :
    I.IsGloballyDesingularizedBy F E Y ↔
      (∀ K : Compacts M,
        E.pullback (F.toSpace K) (F.toSpace K).contMDiff =
            (F.seq K).boundarySeq ⊤ (Fin.last (F.seq K).length) ∧
          Y.pullback (F.toSpace K) (F.toSpace K).contMDiff =
            (F.seq K).strictTransformSubspaceSeq (I.restrict (F.nhd K))
              (Fin.last (F.seq K).length)) ∧
      E.IsSncBoundaryTransversalTo Y ∧
      IsMulBoundaryMonomial (I.pullback F.map F.map.contMDiff) Y E :=
  ⟨fun h => ⟨fun K => ⟨h.pullback_toSpace_eq_boundarySeq K,
      h.pullback_toSpace_eq_strictTransform K⟩, h.isSncBoundaryTransversalTo,
      h.isMulBoundaryMonomial⟩,
    fun h => ⟨h.2.1, h.2.2, fun K => (h.1 K).1, fun K => (h.1 K).2⟩⟩

/-- A locally finite embedded desingularization has a divisor and a strict transform on `M̃`
(`IsGloballyDesingularizedBy`). -/
theorem IsLocallyFinitelyDesingularizedBy.exists_isGloballyDesingularizedBy
    {I : IdealSheaf M} {F : ExtensionCompatibleFamily M}
    (h : I.IsLocallyFinitelyDesingularizedBy F) :
    ∃ E Y : IdealSheaf F.space, I.IsGloballyDesingularizedBy F E Y :=
  let ⟨E, Y, hEY⟩ := h.exists_divisor_strictTransform
  ⟨E, Y, isGloballyDesingularizedBy_iff_and.mpr hEY⟩
end AnalyticManifold.IdealSheaf

namespace AnalyticManifold.ExtensionCompatibleFamily

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : AnalyticManifold.{u} 𝕜 E} (ψ : E ≃L[𝕜] E')
  (F : ExtensionCompatibleFamily (M.transport ψ))

/-! ### Helpers on the re-modelled base -/

/-- An ideal sheaf restricted to an open, read through the stage-`0` identification of the
transport: the restriction of `J` is the pull-back of the restriction of the re-modelled `J` (every
map in sight is the identity on points). -/
theorem _root_.AnalyticManifold.IdealSheaf.restrictOpens_eq_pullbackDiffeomorph_transport
    (J : IdealSheaf M) (U : Opens M) :
    J.restrict U =
      IdealSheaf.pullbackDiffeomorph (M.restrictTransportDiffeomorph ψ U)
        ((J.transport ψ).restrict (M.transportOpens ψ U)) := by
  change IdealSheaf.pullback ⇑(M.inclusion U) (M.inclusion U).contMDiff J =
    IdealSheaf.pullback ⇑(M.restrictTransportDiffeomorph ψ U)
      (M.restrictTransportDiffeomorph ψ U).contMDiff
      (IdealSheaf.pullback ⇑((M.transport ψ).inclusion (M.transportOpens ψ U))
        ((M.transport ψ).inclusion (M.transportOpens ψ U)).contMDiff
        (IdealSheaf.pullback ⇑(M.transportDiffeomorph ψ).symm
          (M.transportDiffeomorph ψ).symm.contMDiff J))
  rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
  exact IdealSheaf.pullback_congr _ _ _ (funext fun _ => rfl)

/-- The support of the re-modelled ideal sheaf, read back on `M`. -/
theorem _root_.AnalyticManifold.IdealSheaf.preimage_support_transport (J : IdealSheaf M) :
    ⇑(M.transportDiffeomorph ψ) ⁻¹' (J.transport ψ).support = J.support := by
  rw [IdealSheaf.support_pullbackDiffeomorph, Set.preimage_preimage]
  simp only [Diffeomorph.symm_apply_apply, Set.preimage_id']

/-- The simple locus of the re-modelled ideal sheaf, read back on `M`. -/
theorem _root_.AnalyticManifold.IdealSheaf.preimage_regularLocus_transport (J : IdealSheaf M) :
    ⇑(M.transportDiffeomorph ψ) ⁻¹' (J.transport ψ).regularLocus = J.regularLocus := by
  rw [IdealSheaf.regularLocus_pullbackDiffeomorph, Set.preimage_preimage]
  simp only [Diffeomorph.symm_apply_apply, Set.preimage_id']

/-! ### The family read back on `M` -/

/-- **A compatible family over the re-modelled `M`, read back on `M`**: the space re-modelled along
`ψ⁻¹`, the same map and neighbourhoods, each succession carried along the identity of its
neighbourhood (`transportAlong`), the identification of the end results conjugated by the
identities; `map_toSpace` by `composite_transportAlong`, `toSpace_isIso` by
`isAnalyticIsoOver_of_square_iff` on the square of the identities, the compatibility by
`isExtensionOf_restrict_transportAlong`. -/
def transportBack : ExtensionCompatibleFamily M where
  space := F.space.transport ψ.symm
  map := ⟨fun p => F.map ((F.space.transportDiffeomorph ψ.symm).symm p),
    (M.contMDiff_ofTransport ψ).comp (F.map.contMDiff.comp (F.space.contMDiff_ofTransport ψ.symm))⟩
  nhd := F.nhd
  subset_nhd := F.subset_nhd
  nhd_mono := F.nhd_mono
  seq K := (F.seq K).transportAlong (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm
  toSpace K := ⟨⇑(F.space.transportDiffeomorph ψ.symm) ∘ ⇑(F.toSpace K) ∘
    ⇑((F.seq K).transportAlongStage (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm
      (Fin.last _)),
    (F.space.transportDiffeomorph ψ.symm).contMDiff.comp ((F.toSpace K).contMDiff.comp
      ((F.seq K).transportAlongStage (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm
        (Fin.last _)).contMDiff)⟩
  map_toSpace K := ContMDiffMap.ext fun p =>
    (congrArg (fun f : AnalyticMap (F.seq K).last (M.transport ψ) =>
        f ((F.seq K).transportAlongStage (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm
          (Fin.last _) p)) (F.map_toSpace K)).trans
      (congrArg Subtype.val
        ((F.seq K).composite_transportAlong (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm p))
  toSpace_isIso K :=
    (AnalyticMap.isAnalyticIsoOver_of_square_iff (F.space.transportDiffeomorph ψ.symm).symm
      ((F.seq K).transportAlongStage (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm
        (Fin.last _))
      (F.toSpace K)
      ⟨⇑(F.space.transportDiffeomorph ψ.symm) ∘ ⇑(F.toSpace K) ∘
        ⇑((F.seq K).transportAlongStage (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm
          (Fin.last _)),
        (F.space.transportDiffeomorph ψ.symm).contMDiff.comp ((F.toSpace K).contMDiff.comp
          ((F.seq K).transportAlongStage (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm
            (Fin.last _)).contMDiff)⟩
      (fun _ => rfl) (⇑F.map ⁻¹' (F.nhd K : Set (M.transport ψ)))).mpr (F.toSpace_isIso K)
  isExtensionOf_restrict K₁ K₂ h :=
    FiniteSuccession.isExtensionOf_restrict_transportAlong ψ (F.nhd_mono h) (F.seq K₂) (F.seq K₁)
      (F.isExtensionOf_restrict K₁ K₂ h)

/-- The transported map is the map after the identity of the space. -/
theorem coe_map_transportBack :
    ⇑(F.transportBack ψ).map = ⇑F.map ∘ ⇑(F.space.transportDiffeomorph ψ.symm).symm := rfl

/-- The same neighbourhoods. -/
theorem nhd_transportBack (K : Compacts M) : (F.transportBack ψ).nhd K = F.nhd K := rfl

/-- The succession of `K`, carried along the identity of `U_K`. -/
theorem seq_transportBack (K : Compacts M) :
    (F.transportBack ψ).seq K =
      (F.seq K).transportAlong (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm := rfl

/-- The identification of the end result, conjugated by the identities. -/
theorem coe_toSpace_transportBack (K : Compacts M) :
    ⇑((F.transportBack ψ).toSpace K) = ⇑(F.space.transportDiffeomorph ψ.symm) ∘ ⇑(F.toSpace K) ∘
      ⇑((F.seq K).transportAlongStage (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm
        (Fin.last _)) := rfl

/-- **Properness of the transported map**: the same map on the same topologies, definitionally. -/
theorem isProperMap_map_transportBack_iff :
    IsProperMap ⇑(F.transportBack ψ).map ↔ IsProperMap ⇑F.map := Iff.rfl

/-! ### The per-compact clauses -/

/-- The stage identification of the transported succession of `K`. -/
abbrev stageEquiv (K : Compacts M) (i : Fin ((F.seq K).length + 1)) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') (((F.transportBack ψ).seq K).stage i) ((F.seq K).stage i) ω :=
  (F.seq K).transportAlongStage (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm i

/-- The centres of the transported family are the pull-backs of `F`'s along the stage
identifications (`center_transportAlong`). -/
theorem center_seq_transportBack (K : Compacts M) (i : Fin (F.seq K).length) :
    ((F.transportBack ψ).seq K).center i =
      IdealSheaf.pullbackDiffeomorph (F.stageEquiv ψ K i.castSucc) ((F.seq K).center i) :=
  (F.seq K).center_transportAlong (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm i

/-- The weak transforms of `J|_{U_K}` along the transported succession are the pull-backs of those
of the re-modelled `J` along `F`'s (`weakTransformSeq_transportAlong` with the restriction of the
re-modelled sheaf). -/
theorem weakTransformSeq_seq_transportBack (J : IdealSheaf M) (K : Compacts M)
    (i : Fin ((F.seq K).length + 1)) :
    ((F.transportBack ψ).seq K).weakTransformSeq (J.restrict ((F.transportBack ψ).nhd K)) i =
      IdealSheaf.pullbackDiffeomorph (F.stageEquiv ψ K i)
        ((F.seq K).weakTransformSeq ((J.transport ψ).restrict (F.nhd K)) i) :=
  (congrArg (fun B => ((F.transportBack ψ).seq K).weakTransformSeq B i)
    (J.restrictOpens_eq_pullbackDiffeomorph_transport ψ (F.nhd K))).trans
    ((F.seq K).weakTransformSeq_transportAlong (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm
      ((J.transport ψ).restrict (F.nhd K)) i)

/-- The boundaries started with `E₀|_{U_K}` along the transported succession are the pull-backs of
those started with the re-modelled `E₀` along `F`'s (`boundarySeq_transportAlong`). -/
theorem boundarySeq_seq_transportBack (E₀ : IdealSheaf M) (K : Compacts M)
    (i : Fin ((F.seq K).length + 1)) :
    ((F.transportBack ψ).seq K).boundarySeq (E₀.restrict ((F.transportBack ψ).nhd K)) i =
      IdealSheaf.pullbackDiffeomorph (F.stageEquiv ψ K i)
        ((F.seq K).boundarySeq ((E₀.transport ψ).restrict (F.nhd K)) i) :=
  (congrArg (fun B => ((F.transportBack ψ).seq K).boundarySeq B i)
    (E₀.restrictOpens_eq_pullbackDiffeomorph_transport ψ (F.nhd K))).trans
    ((F.seq K).boundarySeq_transportAlong (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm
      ((E₀.transport ψ).restrict (F.nhd K)) i)

/-- The strict transforms of the closed subspace `J|_{U_K}` along the transported succession are
the pull-backs of those of the re-modelled `J` along `F`'s
(`strictTransformSubspaceSeq_transportAlong` with the restriction of the re-modelled sheaf). -/
theorem strictTransformSubspaceSeq_seq_transportBack (J : IdealSheaf M) (K : Compacts M)
    (i : Fin ((F.seq K).length + 1)) :
    ((F.transportBack ψ).seq K).strictTransformSubspaceSeq
        (J.restrict ((F.transportBack ψ).nhd K)) i =
      IdealSheaf.pullbackDiffeomorph (F.stageEquiv ψ K i)
        ((F.seq K).strictTransformSubspaceSeq ((J.transport ψ).restrict (F.nhd K)) i) :=
  (congrArg (fun B => ((F.transportBack ψ).seq K).strictTransformSubspaceSeq B i)
    (J.restrictOpens_eq_pullbackDiffeomorph_transport ψ (F.nhd K))).trans
    ((F.seq K).strictTransformSubspaceSeq_transportAlong
      (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm ((J.transport ψ).restrict (F.nhd K)) i)

/-- **The non-singularity of the centres, per compact** (clause (i) of the main theorems): the
centres of the transported family are non-singular iff `F`'s are
(`isNonsingular_pullbackDiffeomorph_iff` along the stage identification). -/
theorem isNonsingular_center_seq_transportBack_iff (K : Compacts M) (i : Fin (F.seq K).length) :
    (((F.transportBack ψ).seq K).center i).IsNonsingular ↔ ((F.seq K).center i).IsNonsingular :=
  (Iff.of_eq (congrArg IdealSheaf.IsNonsingular
    (F.center_seq_transportBack ψ K i))).trans
    (IdealSheaf.isNonsingular_pullbackDiffeomorph_iff _ _)

/-- The stalk-local boundary clause per compact, for any boundary `E₀` on `M` — a general tool (the
main theorems read the family form below). -/
theorem hasOnlyNormalCrossingsWith_boundarySeq_center_seq_transportBack_iff (E₀ : IdealSheaf M)
    (K : Compacts M) (i : Fin (F.seq K).length) :
    (((F.transportBack ψ).seq K).boundarySeq (E₀.restrict ((F.transportBack ψ).nhd K))
        i.castSucc).HasOnlyNormalCrossingsWith (((F.transportBack ψ).seq K).center i) ↔
      ((F.seq K).boundarySeq ((E₀.transport ψ).restrict (F.nhd K))
        i.castSucc).HasOnlyNormalCrossingsWith ((F.seq K).center i) :=
  (Iff.of_eq (congr_arg₂ IdealSheaf.HasOnlyNormalCrossingsWith
    (F.boundarySeq_seq_transportBack ψ E₀ K i.castSucc) (F.center_seq_transportBack ψ K i))).trans
    (IdealSheaf.hasOnlyNormalCrossingsWith_pullbackDiffeomorph_iff _ _ _)

/-- The stalk-local last-boundary clause per compact — a general tool. -/
theorem hasOnlyNormalCrossings_boundarySeq_last_seq_transportBack_iff (E₀ : IdealSheaf M)
    (K : Compacts M) :
    (((F.transportBack ψ).seq K).boundarySeq (E₀.restrict ((F.transportBack ψ).nhd K))
        (Fin.last _)).HasOnlyNormalCrossings ↔
      ((F.seq K).boundarySeq ((E₀.transport ψ).restrict (F.nhd K))
        (Fin.last _)).HasOnlyNormalCrossings :=
  (Iff.of_eq (congrArg IdealSheaf.HasOnlyNormalCrossings
    (F.boundarySeq_seq_transportBack ψ E₀ K (Fin.last _)))).trans
    (IdealSheaf.hasOnlyNormalCrossings_pullbackDiffeomorph_iff _ _)

/-- **The last weak transform is the unit ideal, per compact** (clause (iv) of Main Theorem
II''(N)): the last weak transform of `J|_{U_K}` along the transported succession is the unit ideal
iff that of the re-modelled `J` is (the pull-back of the unit is the unit, and pull-back along an
isomorphism is injective). -/
theorem weakTransformSeq_last_seq_transportBack_eq_unit_iff (J : IdealSheaf M) (K : Compacts M) :
    ((F.transportBack ψ).seq K).weakTransformSeq (J.restrict ((F.transportBack ψ).nhd K))
        (Fin.last _) = (⊤ : ((F.transportBack ψ).seq K).last.IdealSheaf) ↔
      (F.seq K).weakTransformSeq ((J.transport ψ).restrict (F.nhd K)) (Fin.last _) =
        (⊤ : (F.seq K).last.IdealSheaf) := by
  rw [F.weakTransformSeq_seq_transportBack ψ J K (Fin.last ((F.transportBack ψ).seq K).length)]
  exact ⟨fun h => IdealSheaf.pullbackDiffeomorph_injective _
      (h.trans (IdealSheaf.pullbackDiffeomorph_top _).symm),
    fun h => (congrArg _ h).trans (IdealSheaf.pullbackDiffeomorph_top _)⟩

/-- **The order of the weak transforms, per compact** (clause (ii) of Main Theorem II''(N)): the
order of the weak transform at a point of a stage of the transported succession is its order at the
identified point (`ord_pullbackDiffeomorph` along the stage identification). -/
theorem ord_weakTransformSeq_seq_transportBack (J : IdealSheaf M) (K : Compacts M)
    (i : Fin ((F.seq K).length + 1)) (y : ((F.transportBack ψ).seq K).stage i) :
    (((F.transportBack ψ).seq K).weakTransformSeq (J.restrict ((F.transportBack ψ).nhd K))
        i).ord y =
      ((F.seq K).weakTransformSeq ((J.transport ψ).restrict (F.nhd K)) i).ord
        ((F.seq K).transportAlongStage (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm i y) :=
  (congrArg (fun B : IdealSheaf (((F.transportBack ψ).seq K).stage i) => B.ord y)
    (F.weakTransformSeq_seq_transportBack ψ J K i)).trans
    (IdealSheaf.ord_pullbackDiffeomorph _ _ y)

/-- The support of a centre of the transported succession is the preimage of the support of `F`'s
under the stage identification. -/
theorem support_center_seq_transportBack (K : Compacts M) (i : Fin (F.seq K).length) :
    (((F.transportBack ψ).seq K).center i).support =
      ⇑((F.seq K).transportAlongStage (M.restrictTransportDiffeomorph ψ (F.nhd K)) ψ.symm
        i.castSucc) ⁻¹' ((F.seq K).center i).support :=
  (congrArg IdealSheaf.support (F.center_seq_transportBack ψ K i)).trans
    (IdealSheaf.support_pullbackDiffeomorph _ _)

/-! ### The global clauses -/

/-- The pull-back of `J` along the transported map is the pull-back, along the identity of the
space, of the pull-back of the re-modelled `J` along `F.map`. -/
theorem comap_map_transportBack (J : IdealSheaf M) :
    J.pullback _ (F.transportBack ψ).map.contMDiff =
      IdealSheaf.pullbackDiffeomorph (F.space.transportDiffeomorph ψ.symm).symm
        ((J.transport ψ).pullback F.map F.map.contMDiff) := by
  change IdealSheaf.pullback ⇑(F.transportBack ψ).map (F.transportBack ψ).map.contMDiff J =
    IdealSheaf.pullback ⇑(F.space.transportDiffeomorph ψ.symm).symm
      (F.space.transportDiffeomorph ψ.symm).symm.contMDiff
      (IdealSheaf.pullback ⇑F.map F.map.contMDiff
        (IdealSheaf.pullback ⇑(M.transportDiffeomorph ψ).symm
          (M.transportDiffeomorph ψ).symm.contMDiff J))
  rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
  exact IdealSheaf.pullback_congr _ _ _ (funext fun _ => rfl)

/-- The Jacobian ideal of the transported map is the pull-back of the Jacobian ideal of `F.map`
along the identity of the space: `jacobianIdeal_of_square` on the square of `F.map` with the two
identities; no unit germ. -/
theorem jacobianIdeal_map_transportBack :
    AnalyticMap.jacobianIdeal (F.transportBack ψ).map =
      IdealSheaf.pullbackDiffeomorph (F.space.transportDiffeomorph ψ.symm).symm
        (AnalyticMap.jacobianIdeal F.map) :=
  AnalyticMap.jacobianIdeal_of_square (M.transportDiffeomorph ψ)
    (F.space.transportDiffeomorph ψ.symm).symm F.map (F.transportBack ψ).map fun _ => rfl

/-- **The divisor clause of the principalization theorem**: `J.pullback map map.contMDiff` is a
normal-crossings divisor iff the re-modelled `J`'s pull-back along `F.map` is. -/
theorem isNormalCrossingsDivisor_comap_map_transportBack_iff (J : IdealSheaf M) :
    AnalyticManifold.IdealSheaf.IsNormalCrossingsDivisor (J.pullback _ (F.transportBack
        ψ).map.contMDiff) ↔
      AnalyticManifold.IdealSheaf.IsNormalCrossingsDivisor
        ((J.transport ψ).pullback F.map F.map.contMDiff) :=
  (Iff.of_eq (congrArg IdealSheaf.IsNormalCrossingsDivisor
    (F.comap_map_transportBack ψ J))).trans
    (IdealSheaf.isNormalCrossingsDivisor_pullbackDiffeomorph_iff _ _)

/-- **The Jacobian clause of the principalization theorem** [BM97, Theorem 1.10, the sentence
after it]: the product of the Jacobian ideal of the transported map with `J.pullback map
map.contMDiff` is a
normal-crossings divisor iff the product for `F.map` and the re-modelled `J` is
(`jacobianIdeal_map_transportBack`, `comap_map_transportBack`, `pullbackDiffeomorph_mul`,
`isNormalCrossingsDivisor_pullbackDiffeomorph_iff`). -/
theorem isNormalCrossingsDivisor_jacobianIdeal_mul_pullback_map_transportBack_iff
    (J : IdealSheaf M) :
    AnalyticManifold.IdealSheaf.IsNormalCrossingsDivisor (AnalyticMap.jacobianIdeal
        (F.transportBack ψ).map *
        J.pullback _ (F.transportBack ψ).map.contMDiff) ↔
      (AnalyticMap.jacobianIdeal F.map * (J.transport ψ).pullback F.map
          F.map.contMDiff).IsNormalCrossingsDivisor := by
  exact (Iff.of_eq (congrArg IdealSheaf.IsNormalCrossingsDivisor
    ((congr_arg₂ (· * ·) (F.jacobianIdeal_map_transportBack ψ)
      (F.comap_map_transportBack ψ J)).trans
      (IdealSheaf.pullbackDiffeomorph_mul _ _ _).symm))).trans
    (IdealSheaf.isNormalCrossingsDivisor_pullbackDiffeomorph_iff _ _)

/-- **The isomorphism off the cosupport**: the transported map is an analytic isomorphism off the
cosupport of `J` iff `F.map` is off the cosupport of the re-modelled `J`
(`isAnalyticIsoOver_of_square_iff` on the square of `F.map` with the two identities;
`preimage_support_transport`). -/
theorem isAnalyticIsoOver_map_transportBack_iff (J : IdealSheaf M) :
    (F.transportBack ψ).map.IsIsoOver (J.support)ᶜ ↔
      F.map.IsIsoOver ((J.transport ψ).support)ᶜ := by
  have hset : (J.support)ᶜ = ⇑(M.transportDiffeomorph ψ) ⁻¹' ((J.transport ψ).support)ᶜ := by
    rw [Set.preimage_compl, J.preimage_support_transport ψ]
  rw [hset]
  exact AnalyticMap.isAnalyticIsoOver_of_square_iff (M.transportDiffeomorph ψ)
    (F.space.transportDiffeomorph ψ.symm).symm F.map (F.transportBack ψ).map (fun _ => rfl) _

/-- **The isomorphism off the singular locus**, Włodarczyk's bimeromorphy of the embedded
desingularization: the transported map is an isomorphism off `Sing(Y) = Y ∖ Reg(Y)` of the
subspace `Y` with ideal sheaf `J` iff `F.map` is off that of the re-modelled `J`
(`isAnalyticIsoOver_of_square_iff` on the square of `F.map` with the two identities;
`preimage_support_transport`, `preimage_regularLocus_transport`). -/
theorem isAnalyticIsoOver_compl_sing_map_transportBack_iff (J : IdealSheaf M) :
    (F.transportBack ψ).map.IsIsoOver (J.support \ J.regularLocus)ᶜ ↔
      F.map.IsIsoOver ((J.transport ψ).support \ (J.transport ψ).regularLocus)ᶜ := by
  have hset : (J.support \ J.regularLocus)ᶜ = ⇑(M.transportDiffeomorph ψ) ⁻¹'
      ((J.transport ψ).support \ (J.transport ψ).regularLocus)ᶜ := by
    rw [Set.preimage_compl, Set.preimage_sdiff, J.preimage_support_transport ψ,
      J.preimage_regularLocus_transport ψ]
  rw [hset]
  exact AnalyticMap.isAnalyticIsoOver_of_square_iff (M.transportDiffeomorph ψ)
    (F.space.transportDiffeomorph ψ.symm).symm F.map (F.transportBack ψ).map (fun _ => rfl) _

/-! ### The boundary clauses in the simple-normal-crossings family form -/

variable {n : ℕ} (ψE : E ≃L[𝕜] (Fin n → 𝕜)) (ψS : E' ≃L[𝕜] (Fin n → 𝕜))

/-- **The boundary clause per compact in the family form**, for fixed chart isomorphisms `ψE` of
the model of `M` and `ψS` of the standard model: the stage-`i` boundary of the transported
succession is the reduced ideal sheaf of an snc family having snc with the centre iff `F`'s is — the
transports of `SncFamily.lean` along the stage identification (any two chart isomorphisms), the
boundary and the centre being pull-backs. -/
theorem exists_isSnc_boundarySeq_hasSncWith_center_seq_transportBack_iff (E₀ : IdealSheaf M)
    (K : Compacts M) (i : Fin (F.seq K).length) :
    (∃ (G : HypersurfaceFamily (((F.transportBack ψ).seq K).stage i.castSucc)) (c : ℕ),
        G.IsSnc ψE ∧
        G.idealSheaf = ((F.transportBack ψ).seq K).boundarySeq
          (E₀.restrict ((F.transportBack ψ).nhd K)) i.castSucc ∧
        G.HasSncWith ψE (((F.transportBack ψ).seq K).center i).support c) ↔
      (∃ (G : HypersurfaceFamily ((F.seq K).stage i.castSucc)) (c : ℕ), G.IsSnc ψS ∧
        G.idealSheaf = (F.seq K).boundarySeq ((E₀.transport ψ).restrict (F.nhd K)) i.castSucc ∧
        G.HasSncWith ψS ((F.seq K).center i).support c) := by
  have hB := F.boundarySeq_seq_transportBack ψ E₀ K i.castSucc
  have hC := F.support_center_seq_transportBack ψ K i
  constructor
  · rintro ⟨G, c, hG, hGB, hGD⟩
    refine ⟨G.comap ⇑(F.stageEquiv ψ K i.castSucc).symm, c,
      HypersurfaceFamily.isSnc_comap_diffeomorph (F.stageEquiv ψ K i.castSucc).symm ψE ψS G hG,
      ?_, ?_⟩
    · rw [HypersurfaceFamily.idealSheaf_comap_diffeomorph, hGB, hB,
        IdealSheaf.pullbackDiffeomorph_symm_pullbackDiffeomorph]
    · have h1 := HypersurfaceFamily.hasSncWith_comap_diffeomorph (F.stageEquiv ψ K i.castSucc).symm
        ψE ψS G hGD
      have h2 : ⇑(F.stageEquiv ψ K i.castSucc).symm ⁻¹'
            (((F.transportBack ψ).seq K).center i).support = ((F.seq K).center i).support :=
        (congrArg (fun s => ⇑(F.stageEquiv ψ K i.castSucc).symm ⁻¹' s) hC).trans
          (Diffeomorph.symm_preimage_preimage (F.stageEquiv ψ K i.castSucc) _)
      exact (congrArg (fun s => (G.comap ⇑(F.stageEquiv ψ K i.castSucc).symm).HasSncWith ψS s c)
        h2).mp h1
  · rintro ⟨G, c, hG, hGB, hGD⟩
    refine ⟨G.comap ⇑(F.stageEquiv ψ K i.castSucc), c,
      HypersurfaceFamily.isSnc_comap_diffeomorph (F.stageEquiv ψ K i.castSucc) ψS ψE G hG, ?_, ?_⟩
    · rw [HypersurfaceFamily.idealSheaf_comap_diffeomorph, hGB, hB]
    · rw [hC]
      exact HypersurfaceFamily.hasSncWith_comap_diffeomorph (F.stageEquiv ψ K i.castSucc) ψS ψE G
        hGD

/-- **The last-boundary clause per compact in the family form** (Main Theorem II''(N) (iv); the
principalization theorem has no such clause), for fixed chart isomorphisms:
`isSnc_comap_diffeomorph_iff` and `idealSheaf_comap_diffeomorph` along the identification of the
end results. -/
theorem exists_isSnc_boundarySeq_last_seq_transportBack_iff (E₀ : IdealSheaf M)
    (K : Compacts M) :
    (∃ G : HypersurfaceFamily ((F.transportBack ψ).seq K).last, G.IsSnc ψE ∧
        G.idealSheaf = ((F.transportBack ψ).seq K).boundarySeq
          (E₀.restrict ((F.transportBack ψ).nhd K)) (Fin.last _)) ↔
      (∃ G : HypersurfaceFamily (F.seq K).last, G.IsSnc ψS ∧
        G.idealSheaf = (F.seq K).boundarySeq ((E₀.transport ψ).restrict (F.nhd K))
          (Fin.last _)) := by
  have hB := F.boundarySeq_seq_transportBack ψ E₀ K (Fin.last ((F.transportBack ψ).seq K).length)
  constructor
  · rintro ⟨G, hG, hGB⟩
    exact ⟨G.comap ⇑(F.stageEquiv ψ K (Fin.last ((F.transportBack ψ).seq K).length)).symm,
      HypersurfaceFamily.isSnc_comap_diffeomorph
        (F.stageEquiv ψ K (Fin.last ((F.transportBack ψ).seq K).length)).symm ψE ψS G hG,
      (HypersurfaceFamily.idealSheaf_comap_diffeomorph
        (F.stageEquiv ψ K (Fin.last ((F.transportBack ψ).seq K).length)).symm G).trans
        ((congrArg (IdealSheaf.pullbackDiffeomorph
            (F.stageEquiv ψ K (Fin.last ((F.transportBack ψ).seq K).length)).symm)
          (hGB.trans hB)).trans
          (IdealSheaf.pullbackDiffeomorph_symm_pullbackDiffeomorph
            (F.stageEquiv ψ K (Fin.last ((F.transportBack ψ).seq K).length)) _))⟩
  · rintro ⟨G, hG, hGB⟩
    exact ⟨G.comap ⇑(F.stageEquiv ψ K (Fin.last ((F.transportBack ψ).seq K).length)),
      HypersurfaceFamily.isSnc_comap_diffeomorph
        (F.stageEquiv ψ K (Fin.last ((F.transportBack ψ).seq K).length)) ψS ψE G hG,
      (HypersurfaceFamily.idealSheaf_comap_diffeomorph
        (F.stageEquiv ψ K (Fin.last ((F.transportBack ψ).seq K).length)) G).trans
        ((congrArg (IdealSheaf.pullbackDiffeomorph
            (F.stageEquiv ψ K (Fin.last ((F.transportBack ψ).seq K).length))) hGB).trans hB.symm)⟩

/-- **The boundary-with-centre clause per compact in the predicate `IsSncBoundaryWith`** of the
main theorems: the boundary and the centre are pull-backs along the stage identification, then
`isSncBoundaryWith_pullbackDiffeomorph_iff` at the model isomorphism `ψ⁻¹`. -/
theorem isSncBoundaryWith_boundarySeq_center_seq_transportBack_iff (E₀ : IdealSheaf M)
    (K : Compacts M) (i : Fin (F.seq K).length) :
    IdealSheaf.IsSncBoundaryWith
        (((F.transportBack ψ).seq K).boundarySeq (E₀.restrict ((F.transportBack ψ).nhd K))
          i.castSucc)
        (((F.transportBack ψ).seq K).center i) ↔
      IdealSheaf.IsSncBoundaryWith
        ((F.seq K).boundarySeq ((E₀.transport ψ).restrict (F.nhd K)) i.castSucc)
        ((F.seq K).center i) := by
  rw [F.boundarySeq_seq_transportBack ψ E₀ K i.castSucc, F.center_seq_transportBack ψ K i]
  exact IdealSheaf.isSncBoundaryWith_pullbackDiffeomorph_iff _ ψ.symm _ _

/-- **The last-boundary clause per compact in the predicate `IsSncBoundary`** of Main Theorem
II''(N): `isSncBoundary_pullbackDiffeomorph_iff` at `ψ⁻¹`. -/
theorem isSncBoundary_boundarySeq_last_seq_transportBack_iff (E₀ : IdealSheaf M) (K : Compacts M) :
    IdealSheaf.IsSncBoundary
        (((F.transportBack ψ).seq K).boundarySeq (E₀.restrict ((F.transportBack ψ).nhd K))
          (Fin.last _)) ↔
      IdealSheaf.IsSncBoundary
        ((F.seq K).boundarySeq ((E₀.transport ψ).restrict (F.nhd K)) (Fin.last _)) := by
  rw [F.boundarySeq_seq_transportBack ψ E₀ K (Fin.last ((F.transportBack ψ).seq K).length)]
  exact IdealSheaf.isSncBoundary_pullbackDiffeomorph_iff _ ψ.symm _

/-! ### Włodarczyk's embedded desingularization per compact -/

/-- **The clauses of Włodarczyk's embedded desingularization per compact**
(`IdealSheaf.IsDesingularizedBy`, [Wlo09, Theorem 2.0.2 (1)–(3), (6)]) carry over from the
successions of `F` and the re-modelled `J` to those of the transported family and `J`: every
object of the clauses — centres, exceptional divisors, strict transforms, the pull-back of `J` —
is the pull-back of `F`'s along the stage identification, which commutes with the blow-downs
(`stageMap_transportAlong`, `composite_transportAlong`), and each predicate pulls back
(`regularLocus_pullbackDiffeomorph`, `isSncBoundaryWith_pullbackDiffeomorph_iff`,
`IsSncBoundaryTransversalTo.pullbackDiffeomorph`, `IsMulBoundaryMonomial.pullbackDiffeomorph`, at
the model isomorphism `ψ⁻¹`). -/
theorem isDesingularizedBy_seq_transportBack (J : IdealSheaf M) (K : Compacts M)
    (h : ((J.transport ψ).restrict (F.nhd K)).IsDesingularizedBy (F.seq K)) :
    (J.restrict ((F.transportBack ψ).nhd K)).IsDesingularizedBy ((F.transportBack ψ).seq K) := by
  set g := M.restrictTransportDiffeomorph ψ (F.nhd K) with hg
  set J' := (J.transport ψ).restrict (F.nhd K) with hJ'
  have hJ : J.restrict ((F.transportBack ψ).nhd K) = IdealSheaf.pullbackDiffeomorph g J' :=
    J.restrictOpens_eq_pullbackDiffeomorph_transport ψ (F.nhd K)
  -- the unit ideal on the two sides
  have hu' : (⊤ : (M.transport ψ).IdealSheaf).restrict (F.nhd K) =
      (⊤ : ((M.transport ψ).restrict (F.nhd K)).IdealSheaf) := Manifold.IdealSheaf.pullback_top _ _
  have hu : ((⊤ : M.IdealSheaf)).restrict ((F.transportBack ψ).nhd K) =
      (⊤ : (M.restrict ((F.transportBack ψ).nhd K)).IdealSheaf) :=
    Manifold.IdealSheaf.pullback_top _ _
  have hunit : ((⊤ : M.IdealSheaf)).transport ψ = ⊤ := IdealSheaf.pullbackDiffeomorph_top _
  -- the last exceptional divisor
  have hb := F.boundarySeq_seq_transportBack ψ ⊤ K (Fin.last ((F.transportBack ψ).seq K).length)
  rw [hu, hunit, hu'] at hb
  -- the last strict transform
  have hst := F.strictTransformSubspaceSeq_seq_transportBack ψ J K
    (Fin.last ((F.transportBack ψ).seq K).length)
  -- the points of the composite blow-down, through the stage identification
  have hcomp : ∀ z, (F.seq K).composite (F.stageEquiv ψ K (Fin.last _) z) =
      g (((F.transportBack ψ).seq K).composite z) :=
    fun z => (F.seq K).composite_transportAlong g ψ.symm z
  refine ⟨fun i => (F.isNonsingular_center_seq_transportBack_iff ψ K i).mpr
      (h.isNonsingular_center i), ⟨fun i => ?_, ?_⟩, fun i x hx => ?_, ?_, ?_, ?_, ?_⟩
  · -- (1), the boundaries with the centres
    have h1 := (F.isSncBoundaryWith_boundarySeq_center_seq_transportBack_iff ψ ⊤ K i).mpr
      (by rw [hunit, hu']; exact h.hasSncBoundaries.isSncBoundaryWith_center i)
    rwa [hu] at h1
  · -- (1), the last boundary
    have h1 := (F.isSncBoundary_boundarySeq_last_seq_transportBack_iff ψ ⊤ K).mpr
      (by rw [hunit, hu']; exact h.hasSncBoundaries.isSncBoundary_last)
    rwa [hu] at h1
  · -- (2): the stage identification maps the centre to the centre, over `g`
    rw [F.support_center_seq_transportBack ψ K i] at hx
    have key := (F.seq K).stageMap_transportAlong g ψ.symm i.castSucc x
    have hmem : ∀ {p q : (M.transport ψ).restrict (F.nhd K)}, p = q → q ∈ J'.regularLocus →
        p ∈ J'.regularLocus := fun e hq => e ▸ hq
    intro hreg
    rw [hJ] at hreg
    exact h.stageMap_notMem_regularLocus i _ hx (hmem key
      ((Set.ext_iff.mp (IdealSheaf.regularLocus_pullbackDiffeomorph g J') _).mp hreg))
  · -- the support of the last exceptional divisor
    rw [hb, IdealSheaf.support_pullbackDiffeomorph, hJ]
    ext z
    have e1 := Set.ext_iff.mp h.support_boundarySeq_last (F.stageEquiv ψ K (Fin.last _) z)
    have e2 := Set.ext_iff.mp (IdealSheaf.support_pullbackDiffeomorph g J')
      (((F.transportBack ψ).seq K).composite z)
    have e3 := Set.ext_iff.mp (IdealSheaf.regularLocus_pullbackDiffeomorph g J')
      (((F.transportBack ψ).seq K).composite z)
    have hmem : ∀ {T : Set ((M.transport ψ).restrict (F.nhd K))} {p q}, p = q → (p ∈ T ↔ q ∈ T) :=
      fun e => e ▸ Iff.rfl
    exact e1.trans (and_congr ((hmem (hcomp z)).trans e2.symm)
      (not_congr ((hmem (hcomp z)).trans e3.symm)))
  · -- (3), the strict transform is smooth
    rw [hst]
    exact (IdealSheaf.isNonsingular_pullbackDiffeomorph_iff _ _).mpr h.isNonsingular_strictTransform
  · -- (3), transversal simple normal crossings with the last exceptional divisor
    rw [hb, hst]
    exact h.isSncBoundaryTransversalTo_strictTransform.pullbackDiffeomorph _ ψ.symm
  · -- (6): the pull-back of `J` is the pull-back of the pull-back of `J'`
    have hpb : (J.restrict ((F.transportBack ψ).nhd K)).pullback _
        ((F.transportBack ψ).seq K).composite.contMDiff =
        IdealSheaf.pullbackDiffeomorph (F.stageEquiv ψ K (Fin.last _))
          (J'.pullback _ (F.seq K).composite.contMDiff) := by
      rw [hJ]
      exact (IdealSheaf.pullbackDiffeomorph_comap g (F.stageEquiv ψ K (Fin.last _))
        (F.seq K).composite ((F.transportBack ψ).seq K).composite hcomp J').symm
    rw [hb, hst, hpb]
    exact h.isMulBoundaryMonomial_pullback.pullbackDiffeomorph _ ψ.symm

/-- **No empty centre, along the transport**: the centres of the transported succession are the
pull-backs of `F`'s along the stage identifications (`center_seq_transportBack`), and the
pull-back along an analytic isomorphism is the unit ideal exactly when the ideal sheaf is
(`pullbackDiffeomorph_top`, `pullbackDiffeomorph_injective`). -/
theorem center_ne_top_seq_transportBack (K : Compacts M)
    (h : ∀ i : Fin (F.seq K).length, (F.seq K).center i ≠ ⊤)
    (i : Fin ((F.transportBack ψ).seq K).length) :
    ((F.transportBack ψ).seq K).center i ≠ ⊤ := fun hi =>
  h i (IdealSheaf.pullbackDiffeomorph_injective (F.stageEquiv ψ K i.castSucc)
    ((F.center_seq_transportBack ψ K i).symm.trans
      (hi.trans (IdealSheaf.pullbackDiffeomorph_top _).symm)))

/-- **The centres of codimension at most one, along the transport**: a centre of the transported
succession which is a closed submanifold of codimension `c ≤ 1` is the pull-back of `F`'s centre
along the stage identification (`support_center_seq_transportBack`), a closed submanifold of the
same codimension for the chart read through the model isomorphism
(`IsClosedSubmanifold.preimage_of_square`); the containment of the boundary in the centre's ideal
sheaf is the pull-back of `F`'s (`boundarySeq_seq_transportBack`, `center_seq_transportBack`). -/
theorem boundarySeq_le_center_of_codim_le_one_seq_transportBack (K : Compacts M)
    (h : ∀ (i : Fin (F.seq K).length) {n' c : ℕ} (ψ' : E' ≃L[𝕜] (Fin n' → 𝕜)), c ≤ 1 →
      IsClosedSubmanifold ψ' ((F.seq K).center i).support c →
        c = 1 ∧ ∀ x, ((F.seq K).boundarySeq ⊤ i.castSucc).stalkIdeal x ≤
          ((F.seq K).center i).stalkIdeal x)
    (i : Fin ((F.transportBack ψ).seq K).length) {n' c : ℕ} (ψ' : E ≃L[𝕜] (Fin n' → 𝕜))
    (hc : c ≤ 1)
    (hC : IsClosedSubmanifold ψ' (((F.transportBack ψ).seq K).center i).support c) :
    c = 1 ∧ ∀ x, (((F.transportBack ψ).seq K).boundarySeq ⊤ i.castSucc).stalkIdeal x ≤
      (((F.transportBack ψ).seq K).center i).stalkIdeal x := by
  have hset : ⇑(F.stageEquiv ψ K i.castSucc).symm ⁻¹'
      (((F.transportBack ψ).seq K).center i).support = ((F.seq K).center i).support :=
    (congrArg (fun S => ⇑(F.stageEquiv ψ K i.castSucc).symm ⁻¹' S)
      (F.support_center_seq_transportBack ψ K i)).trans (Diffeomorph.symm_preimage_preimage _ _)
  have hC' : IsClosedSubmanifold (ψ.symm.trans ψ') ((F.seq K).center i).support c :=
    hset ▸ hC.preimage_of_square (F.stageEquiv ψ K i.castSucc).symm ψ
  obtain ⟨h1, hle⟩ := h i (ψ.symm.trans ψ') hc hC'
  refine ⟨h1, ?_⟩
  have hu : ((⊤ : M.IdealSheaf)).restrict ((F.transportBack ψ).nhd K) =
      (⊤ : (M.restrict ((F.transportBack ψ).nhd K)).IdealSheaf) :=
    Manifold.IdealSheaf.pullback_top _ _
  have hu' : (⊤ : (M.transport ψ).IdealSheaf).restrict (F.nhd K) =
      (⊤ : ((M.transport ψ).restrict (F.nhd K)).IdealSheaf) :=
    Manifold.IdealSheaf.pullback_top _ _
  have hunit : ((⊤ : M.IdealSheaf)).transport ψ = ⊤ := IdealSheaf.pullbackDiffeomorph_top _
  have hb := F.boundarySeq_seq_transportBack ψ ⊤ K i.castSucc
  rw [hu, hunit, hu'] at hb
  rw [hb, F.center_seq_transportBack ψ K i]
  exact Manifold.IdealSheaf.le_def.mp
    (Manifold.IdealSheaf.pullback_le_pullback _ _ (Manifold.IdealSheaf.le_def.mpr hle))

/-- **The global objects of the embedded desingularization along the transport**: if `E` and
`Ỹ` on the space of `F` are the exceptional divisor and the strict transform of the embedded
desingularization of the re-modelled `J` by `F` (`IsGloballyDesingularizedBy`), their pull-backs
along the identity of the space are those of `J` by the transported family: the predicates along
the identity (`IsSncBoundaryTransversalTo.pullbackDiffeomorph`,
`IsMulBoundaryMonomial.pullbackDiffeomorph`), the pull-back of `J` along the transported map
being the pull-back of the pull-back of the re-modelled `J` (`pullbackDiffeomorph_comap` on the
square of `F.map` with the two identities), and the identifications over a compact through the
stage identification (`boundarySeq_seq_transportBack`,
`strictTransformSubspaceSeq_seq_transportBack`). -/
theorem isGloballyDesingularizedBy_transportBack (J : IdealSheaf M) {E₁ Y₁ : IdealSheaf F.space}
    (h : (J.transport ψ).IsGloballyDesingularizedBy F E₁ Y₁) :
    J.IsGloballyDesingularizedBy (F.transportBack ψ)
      (IdealSheaf.pullbackDiffeomorph (F.space.transportDiffeomorph ψ.symm).symm E₁)
      (IdealSheaf.pullbackDiffeomorph (F.space.transportDiffeomorph ψ.symm).symm Y₁) := by
  set g := (F.space.transportDiffeomorph ψ.symm).symm with hg
  -- the pull-back of `J` along the transported map
  have hpb : J.pullback (F.transportBack ψ).map (F.transportBack ψ).map.contMDiff =
      IdealSheaf.pullbackDiffeomorph g ((J.transport ψ).pullback F.map F.map.contMDiff) :=
    (IdealSheaf.pullbackDiffeomorph_symm_pullbackDiffeomorph (F.space.transportDiffeomorph ψ.symm)
      _).symm.trans (congrArg (IdealSheaf.pullbackDiffeomorph g)
        (IdealSheaf.pullbackDiffeomorph_comap (M.transportDiffeomorph ψ).symm
          (F.space.transportDiffeomorph ψ.symm) (F.transportBack ψ).map F.map (fun _ => rfl) J))
  -- an ideal sheaf on the space of `F`, pulled back to the last stage over a compact through the
  -- transported identification, is its pull-back through `F`'s, carried along the stage
  -- identification: the identities of the space cancel
  have hpull : ∀ (K : Compacts M) (A : IdealSheaf F.space),
      (IdealSheaf.pullbackDiffeomorph g A).pullback ((F.transportBack ψ).toSpace K)
          ((F.transportBack ψ).toSpace K).contMDiff =
        IdealSheaf.pullbackDiffeomorph (F.stageEquiv ψ K (Fin.last _))
          (A.pullback (F.toSpace K) (F.toSpace K).contMDiff) := fun K A =>
    (IdealSheaf.pullback_pullback A ⇑g g.contMDiff ⇑((F.transportBack ψ).toSpace K)
      ((F.transportBack ψ).toSpace K).contMDiff).trans
      ((IdealSheaf.pullback_congr A _ _ (funext fun _ => rfl)).trans
        (IdealSheaf.pullback_pullback A ⇑(F.toSpace K) (F.toSpace K).contMDiff
          ⇑(F.stageEquiv ψ K (Fin.last _)) (F.stageEquiv ψ K (Fin.last _)).contMDiff).symm)
  refine ⟨h.isSncBoundaryTransversalTo.pullbackDiffeomorph g ψ.symm, ?_, fun K => ?_,
    fun K => ?_⟩
  · -- (6)
    rw [hpb]
    exact h.isMulBoundaryMonomial.pullbackDiffeomorph g ψ.symm
  · -- `E` over a compact
    have hu : ((⊤ : M.IdealSheaf)).restrict ((F.transportBack ψ).nhd K) =
        (⊤ : (M.restrict ((F.transportBack ψ).nhd K)).IdealSheaf) :=
      Manifold.IdealSheaf.pullback_top _ _
    have hu' : (⊤ : (M.transport ψ).IdealSheaf).restrict (F.nhd K) =
        (⊤ : ((M.transport ψ).restrict (F.nhd K)).IdealSheaf) :=
      Manifold.IdealSheaf.pullback_top _ _
    have hunit : ((⊤ : M.IdealSheaf)).transport ψ = ⊤ := IdealSheaf.pullbackDiffeomorph_top _
    have hb := F.boundarySeq_seq_transportBack ψ ⊤ K (Fin.last ((F.transportBack ψ).seq K).length)
    rw [hu, hunit, hu'] at hb
    rw [hb]
    exact (hpull K E₁).trans (congrArg (IdealSheaf.pullbackDiffeomorph _)
      (h.pullback_toSpace_eq_boundarySeq K))
  · -- `Ỹ` over a compact
    have hst := F.strictTransformSubspaceSeq_seq_transportBack ψ J K
      (Fin.last ((F.transportBack ψ).seq K).length)
    rw [hst]
    exact (hpull K Y₁).trans (congrArg (IdealSheaf.pullbackDiffeomorph _)
      (h.pullback_toSpace_eq_strictTransform K))

end AnalyticManifold.ExtensionCompatibleFamily

end
