/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Resolution.Defs
public import Hironaka.Resolution.Analytic.ModelTransport.Family
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Hom
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.ModelTransport.SncFamily
import Hironaka.Resolution.Analytic.ModelTransport.SuccessionExtension
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Włodarczyk's principalization and its functoriality along the re-modelling

The clauses of Włodarczyk's locally finite principalization [Wlo09, Theorem 2.0.3] and of its
commutation with local analytic isomorphisms carry over from a compatible family over the
re-modelled manifold `M.transport ψ` (the standard model `𝕜ⁿ`, where the resolution family
`resolveFam` lives) to the family read back on `M` (`ExtensionCompatibleFamily.transportBack`,
`Hironaka/Resolution/Analytic/ModelTransport/Family.lean`):

* `AnalyticMap.transport ψ g`: an analytic map `g : N → M` read between the re-modelled manifolds
  (the same map on points), a local analytic isomorphism when `g` is
  (`isLocalDiffeomorph_transport`), along which the re-modelled ideal sheaves pull back
  (`IdealSheaf.transport_pullback`);
* `FiniteSuccession.IsPullbackUpToEmptyAlong.transportAlong`: the pull-back predicate
  ([Wlo09, Theorem 3.5.1 (2)]) between two successions over opens of the re-modelled manifolds,
  along the re-modelled map, gives the predicate between the successions carried back
  (`transportAlong` at the identities of the opens) along `g`: the same block index, the lifts
  conjugated by the stage identifications, every clause from the identities of
  `Hironaka/Resolution/Analytic/ModelTransport/Succession.lean` (`stageMap_transportAlong`,
  `map_transportAlong`, `stageMapLE_transportAlong`, `center_transportAlong`), as
  `IsExtensionOf.transportAlong` (`SuccessionExtension.lean`);
* `ExtensionCompatibleFamily.isLocallyFinitelyPrincipalizedBy_transportBack`: the clauses of
  `IdealSheaf.IsLocallyFinitelyPrincipalizedBy`, each by the transport lemma of `Family.lean` for
  it, the monomial clause (3) by `IsMulBoundaryMonomial.pullbackDiffeomorph` along the stage
  identification, as in `isDesingularizedBy_seq_transportBack`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Hironaka.Manifold Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

/-! ### Analytic maps between the re-modelled manifolds -/

/-- **An analytic map `g : N → M` read between the re-modelled manifolds** `N.transport ψ` and
`M.transport ψ`: the same map on points, analytic as `M.transportDiffeomorph ψ ∘ g ∘
(N.transportDiffeomorph ψ)⁻¹`. -/
def AnalyticMap.transport {M N : AnalyticManifold.{u} 𝕜 E} (ψ : E ≃L[𝕜] E')
    (g : AnalyticMap N M) : AnalyticMap (N.transport ψ) (M.transport ψ) :=
  ⟨fun x => M.toTransport ψ (g (N.ofTransport ψ x)),
    (M.contMDiff_toTransport ψ).comp (g.contMDiff.comp (N.contMDiff_ofTransport ψ))⟩

/-- The re-modelled map is the map on points. -/
theorem AnalyticMap.transport_apply {M N : AnalyticManifold.{u} 𝕜 E} (ψ : E ≃L[𝕜] E')
    (g : AnalyticMap N M) (x : N) :
    AnalyticMap.transport ψ g (N.toTransport ψ x) = M.toTransport ψ (g x) := rfl

/-- The re-modelled map of a local analytic isomorphism is a local analytic isomorphism: a
composite of `g` with the two identities, which are analytic isomorphisms across the models. -/
theorem AnalyticMap.isLocalDiffeomorph_transport {M N : AnalyticManifold.{u} 𝕜 E}
    (ψ : E ≃L[𝕜] E') {g : AnalyticMap N M} (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) :
    IsLocalDiffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E') ω (AnalyticMap.transport ψ g) := fun x =>
  IsLocalDiffeomorphAt.comp (hf := (N.transportDiffeomorph ψ).symm.isLocalDiffeomorph x)
    (hg := IsLocalDiffeomorphAt.comp (hf := hg _)
      (hg := (M.transportDiffeomorph ψ).isLocalDiffeomorph _))

/-- The re-modelled pull-back is the pull-back of the re-modelled ideal sheaf along the
re-modelled map (both are the pull-back of `J` along the same map on points). -/
theorem IdealSheaf.transport_pullback {M N : AnalyticManifold.{u} 𝕜 E} (ψ : E ≃L[𝕜] E')
    (g : AnalyticMap N M) (J : IdealSheaf M) :
    IdealSheaf.transport ψ (J.pullback g g.contMDiff) =
      (J.transport ψ).pullback (AnalyticMap.transport ψ g)
        (AnalyticMap.transport ψ g).contMDiff := by
  change IdealSheaf.pullback _ _ (IdealSheaf.pullback _ _ J) =
    IdealSheaf.pullback _ _ (IdealSheaf.pullback _ _ J)
  rw [Manifold.IdealSheaf.pullback_pullback, Manifold.IdealSheaf.pullback_pullback]
  exact Manifold.IdealSheaf.pullback_congr _ _ _ (funext fun _ => rfl)

/-! ### The pull-back predicate along the re-modelling -/

namespace FiniteSuccession

/-- **Włodarczyk's pull-back up to empty blow-ups [Wlo09, Theorem 3.5.1 (2)] carries back from the
re-modelled manifolds**: if the succession `R` over an open `U'` of `N.transport ψ` is the
pull-back of the succession `S` over an open `U` of `M.transport ψ` along the re-modelled map
`gT` of `g`, then the successions carried back to `N` and `M` (`transportAlong` at the identities
of the opens) are related in the same way along `g`. The block index is kept and every lift is
conjugated by the stage identifications of the two transports. -/
theorem IsPullbackUpToEmptyAlong.transportAlong {M N : AnalyticManifold.{u} 𝕜 E}
    (ψ : E ≃L[𝕜] E') {U : Opens M} {U' : Opens N}
    {S : FiniteSuccession ((M.transport ψ).restrict (M.transportOpens ψ U))}
    {R : FiniteSuccession ((N.transport ψ).restrict (N.transportOpens ψ U'))}
    (g : AnalyticMap N M) (gT : AnalyticMap (N.transport ψ) (M.transport ψ))
    (hg : ∀ x, gT (N.toTransport ψ x) = M.toTransport ψ (g x))
    (h : R.IsPullbackUpToEmptyAlong S gT) :
    (R.transportAlong (N.restrictTransportDiffeomorph ψ U') ψ.symm).IsPullbackUpToEmptyAlong
      (S.transportAlong (M.restrictTransportDiffeomorph ψ U) ψ.symm) g := by
  obtain ⟨blk, f, h0, hl, hs, hld, hov, hm, hcj, hcn⟩ := isPullbackUpToEmptyAlong_iff.mp h
  set aS := M.restrictTransportDiffeomorph ψ U with haS
  set aR := N.restrictTransportDiffeomorph ψ U' with haR
  -- the lifts conjugated by the stage identifications of the two transports
  let f₀ : ∀ k, AnalyticMap ((R.transportAlong aR ψ.symm).stage (blk k))
      ((S.transportAlong aS ψ.symm).stage k) := fun k =>
    ⟨fun p => (S.transportAlongStage aS ψ.symm k).symm
        (f k (R.transportAlongStage aR ψ.symm (blk k) p)),
      (S.transportAlongStage aS ψ.symm k).symm.contMDiff.comp
        ((f k).contMDiff.comp (R.transportAlongStage aR ψ.symm (blk k)).contMDiff)⟩
  have hf₀ : ∀ k p, S.transportAlongStage aS ψ.symm k (f₀ k p) =
      f k (R.transportAlongStage aR ψ.symm (blk k) p) := fun k p =>
    (S.transportAlongStage aS ψ.symm k).apply_symm_apply _
  refine isPullbackUpToEmptyAlong_iff.mpr ⟨blk, f₀, h0, hl, hs, ?_, ?_, ?_, ?_, ?_⟩
  · -- local analytic isomorphisms
    intro k x
    exact IsLocalDiffeomorphAt.comp
      (hf := (R.transportAlongStage aR ψ.symm (blk k)).isLocalDiffeomorph x)
      (hg := IsLocalDiffeomorphAt.comp (hf := hld k _)
        (hg := (S.transportAlongStage aS ψ.symm k).symm.isLocalDiffeomorph _))
  · -- over `g`: the points of the composite blow-downs, through the stage identifications
    intro k p
    have h1 := (congrArg (S.stageMap k) (hf₀ k p)).symm.trans
      (S.stageMap_transportAlong aS ψ.symm k (f₀ k p))
    have h2 := R.stageMap_transportAlong aR ψ.symm (blk k) p
    have h3 := hov k (R.transportAlongStage aR ψ.symm (blk k) p)
    have key : M.toTransport ψ (M.inclusion U ((S.transportAlong aS ψ.symm).stageMap k (f₀ k p))) =
        M.toTransport ψ (g (N.inclusion U' ((R.transportAlong aR ψ.symm).stageMap (blk k) p))) :=
      ((congrArg ((M.transport ψ).inclusion (M.transportOpens ψ U)) h1).symm.trans
        (h3.trans (congrArg (fun q => gT ((N.transport ψ).inclusion (N.transportOpens ψ U') q))
          h2))).trans (hg _)
    exact key
  · -- the blow-downs
    intro (k : Fin S.length) hle p
    have key : S.transportAlongStage aS ψ.symm k.castSucc
          ((S.transportAlong aS ψ.symm).map k (f₀ k.succ p)) =
        S.transportAlongStage aS ψ.symm k.castSucc
          (f₀ k.castSucc ((R.transportAlong aR ψ.symm).stageMapLE hle p)) :=
      (S.map_transportAlong aS ψ.symm k (f₀ k.succ p)).symm.trans
        ((congrArg (S.map k) (hf₀ k.succ p)).trans
          ((hm k hle (R.transportAlongStage aR ψ.symm (blk k.succ) p)).trans
            ((congrArg (f k.castSucc) (R.stageMapLE_transportAlong aR ψ.symm hle p)).trans
              (hf₀ k.castSucc _).symm)))
    exact (S.transportAlongStage aS ψ.symm k.castSucc).injective key
  · -- the centres at a jump
    intro (k : Fin S.length) ha hj
    have e1 : (R.transportAlong aR ψ.symm).centerAt (blk k.castSucc) ha =
        IdealSheaf.pullbackDiffeomorph (R.transportAlongStage aR ψ.symm (blk k.castSucc))
          (R.centerAt (blk k.castSucc) ha) :=
      R.center_transportAlong aR ψ.symm ⟨(blk k.castSucc).1, ha⟩
    have e2 := S.center_transportAlong aS ψ.symm k
    have hfun : ⇑(f k.castSucc) ∘ ⇑(R.transportAlongStage aR ψ.symm (blk k.castSucc)) =
        ⇑(S.transportAlongStage aS ψ.symm k.castSucc) ∘ ⇑(f₀ k.castSucc) :=
      funext fun p => (hf₀ k.castSucc p).symm
    refine e1.trans ((congrArg (IdealSheaf.pullbackDiffeomorph
      (R.transportAlongStage aR ψ.symm (blk k.castSucc))) (hcj k ha hj)).trans ?_)
    refine (Manifold.IdealSheaf.pullback_pullback _ _ _ _ _).trans ?_
    refine (Manifold.IdealSheaf.pullback_congr _ _
      ((S.transportAlongStage aS ψ.symm k.castSucc).contMDiff.comp (f₀ k.castSucc).contMDiff)
      hfun).trans ?_
    refine (Manifold.IdealSheaf.pullback_pullback (S.center k)
      (S.transportAlongStage aS ψ.symm k.castSucc)
      (S.transportAlongStage aS ψ.symm k.castSucc).contMDiff (f₀ k.castSucc)
      (f₀ k.castSucc).contMDiff).symm.trans ?_
    exact congrArg
      (fun J : AnalyticManifold.IdealSheaf ((S.transportAlong aS ψ.symm).stage k.castSucc) =>
      IdealSheaf.pullback (f₀ k.castSucc) (f₀ k.castSucc).contMDiff J) e2.symm
  · -- the empty centres at a non-jump
    intro (k : Fin S.length) hj
    have hc := hcn k hj
    rw [IdealSheaf.support_pullback] at hc
    have e2 := S.center_transportAlong aS ψ.symm k
    refine (IdealSheaf.support_pullback _ _ _).trans ?_
    refine (congrArg (fun J => ⇑(f₀ k.castSucc) ⁻¹' IdealSheaf.support J) e2).trans ?_
    refine (congrArg (fun s => ⇑(f₀ k.castSucc) ⁻¹' s)
      (IdealSheaf.support_pullbackDiffeomorph _ _)).trans ?_
    refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
    have hp1 : S.transportAlongStage aS ψ.symm k.castSucc (f₀ k.castSucc p) ∈
        (S.center k).support := hp
    rw [hf₀ k.castSucc p] at hp1
    have hp' : R.transportAlongStage aR ψ.symm (blk k.castSucc) p ∈
        ⇑(f k.castSucc) ⁻¹' (S.center k).support := hp1
    rw [hc] at hp'
    exact hp'

end FiniteSuccession

/-! ### The principalization clauses along the re-modelling -/

namespace ExtensionCompatibleFamily

variable {M : AnalyticManifold.{u} 𝕜 E} (ψ : E ≃L[𝕜] E')
  (F : ExtensionCompatibleFamily (M.transport ψ))

/-- **The clauses of Włodarczyk's principalization**
(`IdealSheaf.IsLocallyFinitelyPrincipalizedBy`, [Wlo09, Theorem 2.0.3 (1)–(3)]) carry over from
the family `F` over the re-modelled `M` and the re-modelled ideal sheaf to the family read back on
`M` and the ideal sheaf: the properness, the divisor clause on `M̃` and the isomorphism off the
support by the global transport lemmas of `Family.lean`; the centres and the boundaries by their
transport lemmas per compact; and the monomial clause (3) by
`IsMulBoundaryMonomial.pullbackDiffeomorph` along the stage identification of the last stage,
which carries the pull-back of the ideal sheaf (`pullbackDiffeomorph_comap`), the unit ideal and
the last exceptional divisor (`boundarySeq_seq_transportBack`) to those of `F`. -/
theorem isLocallyFinitelyPrincipalizedBy_transportBack (I : IdealSheaf M)
    (h : (I.transport ψ).IsLocallyFinitelyPrincipalizedBy F) :
    I.IsLocallyFinitelyPrincipalizedBy (F.transportBack ψ) := by
  -- the unit ideal on the two sides
  have hu' : ∀ K : Compacts (M.transport ψ),
      (⊤ : (M.transport ψ).IdealSheaf).restrict (F.nhd K) =
        (⊤ : ((M.transport ψ).restrict (F.nhd K)).IdealSheaf) := fun _ =>
    Manifold.IdealSheaf.pullback_top _ _
  have hu : ∀ K : Compacts M, ((⊤ : M.IdealSheaf)).restrict ((F.transportBack ψ).nhd K) =
      (⊤ : (M.restrict ((F.transportBack ψ).nhd K)).IdealSheaf) := fun _ =>
    Manifold.IdealSheaf.pullback_top _ _
  have hunit : ((⊤ : M.IdealSheaf)).transport ψ = ⊤ := IdealSheaf.pullbackDiffeomorph_top _
  refine ⟨(F.isProperMap_map_transportBack_iff ψ).mpr h.isProperMap,
    fun K => h.isCompact_closure_nhd K,
    fun K i => (F.isNonsingular_center_seq_transportBack_iff ψ K i).mpr
      (h.isNonsingular_center K i),
    fun K => ⟨fun i => ?_, ?_⟩, fun K => ?_,
    (F.isNormalCrossingsDivisor_comap_map_transportBack_iff ψ I).mpr
      h.isNormalCrossingsDivisor_pullback,
    (F.isAnalyticIsoOver_map_transportBack_iff ψ I).mpr h.isIsoOver_compl_support⟩
  · -- (2), the boundaries with the centres
    have h1 := (F.isSncBoundaryWith_boundarySeq_center_seq_transportBack_iff ψ ⊤ K i).mpr
      (by rw [hunit, hu' K]; exact (h.hasSncBoundaries K).isSncBoundaryWith_center i)
    rwa [hu] at h1
  · -- (2), the last boundary
    have h1 := (F.isSncBoundary_boundarySeq_last_seq_transportBack_iff ψ ⊤ K).mpr
      (by rw [hunit, hu' K]; exact (h.hasSncBoundaries K).isSncBoundary_last)
    rwa [hu] at h1
  · -- (3), the total transform near every point
    set g := M.restrictTransportDiffeomorph ψ (F.nhd K) with hg
    set J' := (I.transport ψ).restrict (F.nhd K) with hJ'
    have hJ : I.restrict ((F.transportBack ψ).nhd K) = IdealSheaf.pullbackDiffeomorph g J' :=
      I.restrictOpens_eq_pullbackDiffeomorph_transport ψ (F.nhd K)
    -- the last exceptional divisor
    have hb := F.boundarySeq_seq_transportBack ψ ⊤ K (Fin.last ((F.transportBack ψ).seq K).length)
    rw [hu, hunit, hu' K] at hb
    -- the points of the composite blow-down, through the stage identification
    have hcomp : ∀ z, (F.seq K).composite (F.stageEquiv ψ K (Fin.last _) z) =
        g (((F.transportBack ψ).seq K).composite z) :=
      fun z => (F.seq K).composite_transportAlong g ψ.symm z
    have hpb : (I.restrict ((F.transportBack ψ).nhd K)).pullback _
        ((F.transportBack ψ).seq K).composite.contMDiff =
        IdealSheaf.pullbackDiffeomorph (F.stageEquiv ψ K (Fin.last _))
          (J'.pullback _ (F.seq K).composite.contMDiff) := by
      rw [hJ]
      exact (IdealSheaf.pullbackDiffeomorph_comap g (F.stageEquiv ψ K (Fin.last _))
        (F.seq K).composite ((F.transportBack ψ).seq K).composite hcomp J').symm
    have htop : IdealSheaf.pullbackDiffeomorph (F.stageEquiv ψ K (Fin.last _))
        (⊤ : ((F.seq K).stage (Fin.last _)).IdealSheaf) = ⊤ :=
      IdealSheaf.pullbackDiffeomorph_top _
    have h3 := (h.isMulBoundaryMonomial_pullback K).pullbackDiffeomorph
      (F.stageEquiv ψ K (Fin.last _)) ψ.symm
    rw [htop] at h3
    rw [hb, hpb]
    exact h3

end ExtensionCompatibleFamily

end AnalyticManifold

end
