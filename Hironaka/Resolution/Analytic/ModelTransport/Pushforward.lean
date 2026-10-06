/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.ModelTransport.Principalization
import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Hom
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The push-forward relation along the re-modelling

Kollár's push-forward relation up to empty blow-ups
(`FiniteSuccession.IsPushforwardUpToEmptyAlong`, the form of the commutation of a principalization
with closed embeddings over the compact sets) carries back from the re-modelled manifolds
(`IsPushforwardUpToEmptyAlong.transportAlong`): if the succession `S` over an open `U` of
`M.transport ψ` is the push-forward of the succession `R` over an open `U'` of `N.transport ψ'`
along the re-modelled map `τT` of `τ : N → M`, then the successions carried back to `M` and `N`
(`transportAlong` at the identities of the opens,
`Hironaka/Resolution/Analytic/ModelTransport/Succession.lean`) are related in the same way along
`τ`. The block index is kept, and every embedding is conjugated by the stage identifications of the
two transports, which carry the embeddings, the closures of their images, the composite
blow-downs, the blow-downs and the supports of the centres — the counterpart for closed embeddings
of `IsPullbackUpToEmptyAlong.transportAlong` for local analytic isomorphisms.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E E' E₁ E₁' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₁'] [NormedSpace 𝕜 E₁']

/-- **Kollár's push-forward relation up to empty blow-ups carries back from the re-modelled
manifolds**: if the succession `S` over an open `U` of `M.transport ψ` is the push-forward of the
succession `R` over an open `U'` of `N.transport ψ'` along the re-modelled map `τT` of `τ`, then
the successions carried back to `M` and `N` (`transportAlong` at the identities of the opens) are
related in the same way along `τ`. The block index is kept and every embedding is conjugated by
the stage identifications of the two transports. -/
theorem IsPushforwardUpToEmptyAlong.transportAlong {M : AnalyticManifold.{u} 𝕜 E}
    {N : AnalyticManifold.{u} 𝕜 E'} (ψ : E ≃L[𝕜] E₁) (ψ' : E' ≃L[𝕜] E₁') {U : Opens M}
    {U' : Opens N} {S : FiniteSuccession ((M.transport ψ).restrict (M.transportOpens ψ U))}
    {R : FiniteSuccession ((N.transport ψ').restrict (N.transportOpens ψ' U'))}
    (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯)
    (τT : C^ω⟮𝓘(𝕜, E₁'), N.transport ψ'; 𝓘(𝕜, E₁), M.transport ψ⟯)
    (hτ : ∀ x, τT (N.toTransport ψ' x) = M.toTransport ψ (τ x))
    (h : S.IsPushforwardUpToEmptyAlong R τT) :
    (S.transportAlong (M.restrictTransportDiffeomorph ψ U) ψ.symm).IsPushforwardUpToEmptyAlong
      (R.transportAlong (N.restrictTransportDiffeomorph ψ' U') ψ'.symm) τ := by
  obtain ⟨blk, f, h0, hl, hs, hemb, hcl, hov, hm, hcj, hcn, hin⟩ :=
    isPushforwardUpToEmptyAlong_iff.mp h
  set aS := M.restrictTransportDiffeomorph ψ U with haS
  set aR := N.restrictTransportDiffeomorph ψ' U' with haR
  -- the embeddings conjugated by the stage identifications of the two transports
  let f₀ : ∀ k, C^ω⟮𝓘(𝕜, E'), (R.transportAlong aR ψ'.symm).stage (blk k);
      𝓘(𝕜, E), (S.transportAlong aS ψ.symm).stage k⟯ := fun k =>
    ⟨fun p => (S.transportAlongStage aS ψ.symm k).symm
        (f k (R.transportAlongStage aR ψ'.symm (blk k) p)),
      (S.transportAlongStage aS ψ.symm k).symm.contMDiff.comp
        ((f k).contMDiff.comp (R.transportAlongStage aR ψ'.symm (blk k)).contMDiff)⟩
  have hf₀ : ∀ k p, S.transportAlongStage aS ψ.symm k (f₀ k p) =
      f k (R.transportAlongStage aR ψ'.symm (blk k) p) := fun k p =>
    (S.transportAlongStage aS ψ.symm k).apply_symm_apply _
  have hf₀' : ∀ k r, f₀ k ((R.transportAlongStage aR ψ'.symm (blk k)).symm r) =
      (S.transportAlongStage aS ψ.symm k).symm (f k r) := fun k r => by
    change (S.transportAlongStage aS ψ.symm k).symm
      (f k (R.transportAlongStage aR ψ'.symm (blk k)
        ((R.transportAlongStage aR ψ'.symm (blk k)).symm r))) = _
    rw [(R.transportAlongStage aR ψ'.symm (blk k)).apply_symm_apply]
  -- the range of the conjugated embedding is the image of the range under the identification
  have hrange : ∀ k, Set.range (f₀ k) =
      ⇑(S.transportAlongStage aS ψ.symm k).symm '' Set.range (f k) := fun k => by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨f k (R.transportAlongStage aR ψ'.symm (blk k) p), ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨(R.transportAlongStage aR ψ'.symm (blk k)).symm r, hf₀' k r⟩
  -- a point over `τ(U')` is, through the identification, a point over `τT(U')`
  have hover : ∀ (k : Fin (S.length + 1)) (q : (S.transportAlong aS ψ.symm).stage k),
      M.inclusion U ((S.transportAlong aS ψ.symm).stageMap k q) ∈ ⇑τ '' (U' : Set N) →
      (M.transport ψ).inclusion (M.transportOpens ψ U)
          (S.stageMap k (S.transportAlongStage aS ψ.symm k q)) ∈
        ⇑τT '' (N.transportOpens ψ' U' : Set (N.transport ψ')) := by
    rintro k q ⟨y, hy, hyq⟩
    refine ⟨N.toTransport ψ' y, hy, ?_⟩
    rw [hτ y, hyq, S.stageMap_transportAlong aS ψ.symm k q]
    rfl
  -- the supports of the transported centres
  have hsuppS : ∀ k : Fin S.length,
      Manifold.IdealSheaf.support ((S.transportAlong aS ψ.symm).center k) =
        ⇑(S.transportAlongStage aS ψ.symm k.castSucc) ⁻¹'
          Manifold.IdealSheaf.support (S.center k) := fun k =>
    (congrArg Manifold.IdealSheaf.support (S.center_transportAlong aS ψ.symm k)).trans
      (IdealSheaf.support_pullbackDiffeomorph _ _)
  have hfun : ∀ k : Fin S.length,
      ⇑(S.transportAlongStage aS ψ.symm k.castSucc) ∘ ⇑(f₀ k.castSucc) =
        ⇑(f k.castSucc) ∘ ⇑(R.transportAlongStage aR ψ'.symm (blk k.castSucc)) := fun k =>
    funext fun p => hf₀ k.castSucc p
  refine isPushforwardUpToEmptyAlong_iff.mpr ⟨blk, f₀, h0, hl, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- embeddings
    intro k
    exact (S.transportAlongStage aS ψ.symm k).symm.toHomeomorph.isEmbedding.comp
      ((hemb k).comp (R.transportAlongStage aR ψ'.symm (blk k)).toHomeomorph.isEmbedding)
  · -- the range is closed in the part over `τ(U')`
    intro k q hq hqU
    have hcls : closure (⇑(S.transportAlongStage aS ψ.symm k).symm '' Set.range (f k)) =
        ⇑(S.transportAlongStage aS ψ.symm k).symm '' closure (Set.range (f k)) :=
      ((S.transportAlongStage aS ψ.symm k).symm.toHomeomorph.image_closure _).symm
    rw [hrange k, hcls] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    have hzU := hover k _ hqU
    rw [(S.transportAlongStage aS ψ.symm k).apply_symm_apply] at hzU
    obtain ⟨r, hr⟩ := hcl k z hz hzU
    exact ⟨(R.transportAlongStage aR ψ'.symm (blk k)).symm r, by rw [hf₀' k r, hr]⟩
  · -- over `τ`: the points of the composite blow-downs, through the stage identifications
    intro k p
    have h1 := (congrArg (S.stageMap k) (hf₀ k p)).symm.trans
      (S.stageMap_transportAlong aS ψ.symm k (f₀ k p))
    have h2 := R.stageMap_transportAlong aR ψ'.symm (blk k) p
    have h3 := hov k (R.transportAlongStage aR ψ'.symm (blk k) p)
    have key : M.toTransport ψ (M.inclusion U ((S.transportAlong aS ψ.symm).stageMap k (f₀ k p))) =
        M.toTransport ψ (τ (N.inclusion U' ((R.transportAlong aR ψ'.symm).stageMap (blk k) p))) :=
      ((congrArg ((M.transport ψ).inclusion (M.transportOpens ψ U)) h1).symm.trans
        (h3.trans (congrArg (fun q => τT ((N.transport ψ').inclusion (N.transportOpens ψ' U') q))
          h2))).trans (hτ _)
    exact key
  · -- the blow-downs
    intro (k : Fin S.length) hle p
    have key : S.transportAlongStage aS ψ.symm k.castSucc
          ((S.transportAlong aS ψ.symm).map k (f₀ k.succ p)) =
        S.transportAlongStage aS ψ.symm k.castSucc
          (f₀ k.castSucc ((R.transportAlong aR ψ'.symm).stageMapLE hle p)) :=
      (S.map_transportAlong aS ψ.symm k (f₀ k.succ p)).symm.trans
        ((congrArg (S.map k) (hf₀ k.succ p)).trans
          ((hm k hle (R.transportAlongStage aR ψ'.symm (blk k.succ) p)).trans
            ((congrArg (f k.castSucc) (R.stageMapLE_transportAlong aR ψ'.symm hle p)).trans
              (hf₀ k.castSucc _).symm)))
    exact (S.transportAlongStage aS ψ.symm k.castSucc).injective key
  · -- the centres at a jump
    intro (k : Fin S.length) ha hj
    have hsuppR : Manifold.IdealSheaf.support
          ((R.transportAlong aR ψ'.symm).centerAt (blk k.castSucc) ha) =
        ⇑(R.transportAlongStage aR ψ'.symm (blk k.castSucc)) ⁻¹'
          Manifold.IdealSheaf.support (R.centerAt (blk k.castSucc) ha) :=
      (congrArg Manifold.IdealSheaf.support
        (R.center_transportAlong aR ψ'.symm ⟨(blk k.castSucc).1, ha⟩)).trans
        (IdealSheaf.support_pullbackDiffeomorph _ _)
    refine (congrArg (fun Z => ⇑(f₀ k.castSucc) ⁻¹' Z) (hsuppS k)).trans (Eq.trans ?_ hsuppR.symm)
    rw [← hcj k ha hj, ← Set.preimage_comp, ← Set.preimage_comp, hfun k]
  · -- the centres at a non-jump
    intro (k : Fin S.length) hj
    refine (congrArg (fun Z => ⇑(f₀ k.castSucc) ⁻¹' Z) (hsuppS k)).trans ?_
    rw [← Set.preimage_comp, hfun k, Set.preimage_comp, hcn k hj]
    exact Set.preimage_empty
  · -- the centre points over `τ(U')` lie in the range
    intro (k : Fin S.length) q hq hqU
    have hq' : S.transportAlongStage aS ψ.symm k.castSucc q ∈
        Manifold.IdealSheaf.support (S.center k) :=
      (Set.ext_iff.mp (hsuppS k) q).mp hq
    obtain ⟨r, hr⟩ := hin k _ hq' (hover k.castSucc q hqU)
    exact ⟨(R.transportAlongStage aR ψ'.symm (blk k.castSucc)).symm r,
      (hf₀' k.castSucc r).trans
        ((congrArg (S.transportAlongStage aS ψ.symm k.castSucc).symm hr).trans
          ((S.transportAlongStage aS ψ.symm k.castSucc).symm_apply_apply q))⟩

end AnalyticManifold.FiniteSuccession

end

end
