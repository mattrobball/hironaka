/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Defs
public import Hironaka.Resolution.Analytic.ModelTransport.IdealSheaf
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Resolution.Analytic.ModelTransport.Square
import Hironaka.Resolution.Analytic.ModelTransport.SquareChart
import Hironaka.Resolution.Analytic.Restrict.StrictSubspaceSeqTransport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# A finite succession carried along an analytic isomorphism across the models

A finite succession of monoidal transformations (`FiniteSuccession`; Hironaka's succession
[Hir64, p. 155], Włodarczyk's
finite sequence of blow-ups [Wlo09, Theorem 2.0.3 (1)]) over a manifold `N` modelled on `E'` is
carried to a manifold `N₀` modelled on `E` along an analytic isomorphism `g : N₀ ≃ N` across the
models and a linear isomorphism `ψ : E' ≃L[𝕜] E` of the models: `S.transportAlong g ψ` has the same
length, its later stages are `S`'s re-modelled along `ψ` (`AnalyticManifold.transport`,
`Hironaka/Resolution/Analytic/ModelTransport/Manifold.lean`), its first centre is pulled back along
`g` and its first blow-down is followed by `g⁻¹`, and from stage `1` on its centres and blow-downs
are `S`'s own read on the re-modelled stages — the same-model base change `transportBase` of
`Hironaka/Resolution/Analytic/TransportBase.lean` with the models freed. Each transported
blow-down is a monoidal transformation with the transported centre by
`AnalyticMap.IsMonoidalTransformation.of_square` (`SquareChart.lean`) on the square of the stage
identifications, whose model isomorphism is `ψ` at stage `0` and the identity of the re-modelled
stage afterwards.

* `transportAlongStage i : (S.transportAlong g ψ).stage i ≃ S.stage i` — `g` at stage `0`, the
  identity of the re-modelled stage (`transportDiffeomorph.symm`) at the later stages; the
  identifications commute with the blow-downs (`map_transportAlong`: the square at each step) and
  with the composite blow-downs (`stageMap_transportAlong`, `composite_transportAlong`).
* The centres, the weak transforms (clause (ii) of [Hir64, Main Theorem II'(N), p. 156]) and the
  boundaries (clause (iii)) of the transported succession are the pull-backs of `S`'s along the
  stage identifications (`center_transportAlong`, `weakTransformSeq_transportAlong`,
  `boundarySeq_transportAlong`) — by recursion on the stage, `weakTransform_of_square` and
  `reducedTransform_of_square` (`Square.lean`) on the square at each step; so are the strict
  transforms of a closed subspace (`strictTransformSubspaceSeq_transportAlong`; Kollár's restricted
  sequence [Kol07, Definition 30.2]), by `strictTransformSubspace_of_square` on each square: the
  strict transform along a blowing-up commutes with a square of analytic isomorphisms across the
  models.

Włodarczyk's extension relation along the transport is in
`Hironaka/Resolution/Analytic/ModelTransport/SuccessionExtension.lean`; the transported families in
`Family.lean`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Filter Topology Hironaka.Manifold
open scoped Manifold ContDiff

universe u

/-! ### The strict transform of a closed subspace along a square -/

namespace Manifold

section StrictTransformSquare

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M M' : AnalyticManifold.{u} 𝕜 E}
  {N N' : AnalyticManifold.{u} 𝕜 E'}

/-- **The strict transform of a closed subspace along a square of analytic isomorphisms across the
models** (the counterpart of `IdealSheaf.weakTransform_of_square` for `strictTransformSubspace`):
for blowings-up `π : M' → M` along `Y` and `π' : N' → N` along `g⁻¹(Y)` with `π ∘ g' = g ∘ π'`,
the strict transform of `g^* I` is the pull-back along `g'` of the strict transform of `I`. Both
sides are the saturations of the total transforms by the exceptional ideals
(`strictTransformSubspace_eq_ofStalks`); the total transforms and the exceptional ideals
correspond under `g'` (`IsClosedSubmanifold.idealSheaf_pullbackDiffeomorph`), and the stalk
isomorphism of `g'` carries the colon ideals (`Ideal.map_colon_pow_equiv`). -/
theorem strictTransformSubspace_of_square (g : Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E) N M ω)
    (g' : Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E) N' M' ω) (ψ : E ≃L[𝕜] E')
    {n n' c c' : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {ψ₁ : E' ≃L[𝕜] (Fin n' → 𝕜)}
    {Y : Set M} {Y' : Set N} {π : M' → M} {π' : N' → N}
    (hY : IsClosedSubmanifold ψ₀ Y c) (h : IsBlowUp ψ₀ Y c π)
    (hY' : IsClosedSubmanifold ψ₁ Y' c') (h' : IsBlowUp ψ₁ Y' c' π') (e : Y' = ⇑g ⁻¹' Y)
    (hsq : ∀ x, π (g' x) = g (π' x)) (I : AnalyticManifold.IdealSheaf M) :
    AnalyticManifold.IdealSheaf.pullbackDiffeomorph g' (strictTransformSubspace hY h I) =
      strictTransformSubspace hY' h' (I.pullbackDiffeomorph g) := by
  -- the total transforms and the exceptional ideals correspond under `g'`
  have hT : ∀ J : AnalyticManifold.IdealSheaf M,
      AnalyticManifold.IdealSheaf.pullbackDiffeomorph g' (J.pullback π h.contMDiff) =
        (J.pullbackDiffeomorph g).pullback π' h'.contMDiff := by
    intro J
    change (J.pullback π h.contMDiff).pullback ⇑g' g'.contMDiff =
      (J.pullback ⇑g g.contMDiff).pullback π' h'.contMDiff
    rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr J _ _ (funext hsq)
  have hE : AnalyticManifold.IdealSheaf.pullbackDiffeomorph g'
      (IdealSheaf.pullback π h.contMDiff hY.idealSheaf) =
      IdealSheaf.pullback π' h'.contMDiff hY'.idealSheaf := by
    rw [hT, hY.idealSheaf_pullbackDiffeomorph g ψ ψ₀ hY' e]
  rw [strictTransformSubspace_eq_ofStalks, strictTransformSubspace_eq_ofStalks]
  refine IdealSheaf.ext fun p => ?_
  rw [AnalyticManifold.IdealSheaf.stalkIdeal_pullbackDiffeomorph, IdealSheaf.stalkIdeal_ofStalks,
    IdealSheaf.stalkIdeal_ofStalks]
  unfold saturationStalk
  rw [Ideal.map_iSup]
  refine iSup_congr fun k => ?_
  refine (Ideal.map_colon_pow_equiv (g'.stalkRingEquiv p) _ _ k).trans ?_
  rw [← hT, ← hE, AnalyticManifold.IdealSheaf.stalkIdeal_pullbackDiffeomorph,
    AnalyticManifold.IdealSheaf.stalkIdeal_pullbackDiffeomorph]
  rfl

end StrictTransformSquare

end Manifold

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {N₀ : AnalyticManifold.{u} 𝕜 E}
  {N : AnalyticManifold.{u} 𝕜 E'} (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') N₀ N ω) (ψ : E' ≃L[𝕜] E)
  (S : FiniteSuccession N)

/-! ### The transported succession -/

/-- The later stages of the transported succession: `S`'s, re-modelled along `ψ`. -/
abbrev transportAlongLater (j : Fin S.length) : AnalyticManifold.{u} 𝕜 E := (S.later j).transport ψ

/-- The centres of the transported succession: the first pulled back along `g`, the others `S`'s
read on the re-modelled stages. -/
def transportAlongCenter :
    ∀ i : Fin S.length, IdealSheaf (finStages N₀ (S.transportAlongLater ψ) i.castSucc)
  | ⟨0, h⟩ => IdealSheaf.pullbackDiffeomorph g (S.center ⟨0, h⟩)
  | ⟨k + 1, h⟩ => IdealSheaf.transport ψ (S.center ⟨k + 1, h⟩)

/-- The blow-downs of the transported succession: the first followed by `g⁻¹`, the others `S`'s own
on the re-modelled stages (analytic by the typed identities of
`Hironaka/Resolution/Analytic/ModelTransport/Manifold.lean`). -/
def transportAlongMap :
    ∀ i : Fin S.length,
      AnalyticMap (finStages N₀ (S.transportAlongLater ψ) i.succ)
        (finStages N₀ (S.transportAlongLater ψ) i.castSucc)
  | ⟨0, h⟩ => ⟨fun p => g.symm (S.map ⟨0, h⟩ p),
      g.symm.contMDiff.comp ((S.map ⟨0, h⟩).contMDiff.comp
        ((S.later ⟨0, h⟩).contMDiff_ofTransport ψ))⟩
  | ⟨k + 1, h⟩ => ⟨fun p => S.map ⟨k + 1, h⟩ p,
      ((S.later ⟨k, Nat.lt_of_succ_lt h⟩).contMDiff_toTransport ψ).comp
        ((S.map ⟨k + 1, h⟩).contMDiff.comp
          ((S.later ⟨k + 1, h⟩).contMDiff_ofTransport ψ))⟩

/-- Each transported blow-down is a monoidal transformation with the transported centre:
`AnalyticMap.IsMonoidalTransformation.of_square` on the square of the stage identifications — at
stage `0` the model isomorphism is `ψ` and the square is `σ_1 = g ∘ (g⁻¹ ∘ σ_1)`; at a later stage
both isomorphisms are the identity of the re-modelled stage. -/
theorem transportAlong_isMonoidal :
    ∀ i : Fin S.length,
      (S.transportAlongMap g ψ i).IsMonoidalTransformation (S.transportAlongCenter g ψ i)
  | ⟨0, h⟩ =>
    AnalyticMap.IsMonoidalTransformation.of_square g ψ
      ((S.later ⟨0, h⟩).transportDiffeomorph ψ).symm (S.map ⟨0, h⟩)
      (S.transportAlongMap g ψ ⟨0, h⟩) (fun x => (g.apply_symm_apply (S.map ⟨0, h⟩ x)).symm)
      (S.isMonoidal ⟨0, h⟩)
  | ⟨k + 1, h⟩ =>
    AnalyticMap.IsMonoidalTransformation.of_square
      ((S.later ⟨k, Nat.lt_of_succ_lt h⟩).transportDiffeomorph ψ).symm ψ
      ((S.later ⟨k + 1, h⟩).transportDiffeomorph ψ).symm (S.map ⟨k + 1, h⟩)
      (S.transportAlongMap g ψ ⟨k + 1, h⟩) (fun _ => rfl) (S.isMonoidal ⟨k + 1, h⟩)

/-- **The succession `S` over `N` carried to `N₀` along `g` with the later stages re-modelled on `E`
along `ψ`**: stage `0` is `N₀`, the first centre is pulled back along `g`, the first blow-down is
followed by `g⁻¹`, the later data are `S`'s own read on the re-modelled stages (the base change
`transportBase` with the models freed). -/
def transportAlong : FiniteSuccession N₀ where
  length := S.length
  later := S.transportAlongLater ψ
  center := S.transportAlongCenter g ψ
  map := S.transportAlongMap g ψ
  isMonoidal := S.transportAlong_isMonoidal g ψ

/-! ### The stage identifications -/

/-- The stage identification, by recursion on the index (as `stageMapAux`): `g` at stage `0`, the
identity of the re-modelled stage afterwards. -/
def transportAlongStageAux :
    ∀ (i : ℕ) (h : i < S.length + 1),
      Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') (finStages N₀ (S.transportAlongLater ψ) ⟨i, h⟩)
        (finStages N S.later ⟨i, h⟩) ω
  | 0, _ => g
  | k + 1, h => ((S.later ⟨k, Nat.lt_of_succ_lt_succ h⟩).transportDiffeomorph ψ).symm

/-- **The identification of the stages** of the transported succession with those of `S`: `g` at
stage `0`, the identity of the re-modelled stage at the later ones. -/
def transportAlongStage (i : Fin (S.length + 1)) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') ((S.transportAlong g ψ).stage i) (S.stage i) ω :=
  S.transportAlongStageAux g ψ i.1 i.2

/-- The transported succession has the length of `S`. -/
theorem transportAlong_length : (S.transportAlong g ψ).length = S.length := rfl

/-- At stage `0` the identification is `g`. -/
theorem coe_transportAlongStage_zero : ⇑(S.transportAlongStage g ψ 0) = ⇑g := rfl

/-- At a later stage the identification is the identity on points. -/
theorem coe_transportAlongStage_succ (k : ℕ) (h : k + 1 < S.length + 1) :
    ⇑(S.transportAlongStage g ψ ⟨k + 1, h⟩) = id := rfl

/-- The square at each step, on the auxiliary indices:
`σ_{k+1} ∘ (stage k+1) = (stage k) ∘ σ'_{k+1}`; at `k = 0` it is `g (g⁻¹ y) = y`, afterwards
definitional. -/
theorem map_transportAlongStageAux :
    ∀ (k : ℕ) (h : k + 1 < S.length + 1) (p : finStages N₀ (S.transportAlongLater ψ) ⟨k + 1, h⟩),
      S.map ⟨k, Nat.lt_of_succ_lt_succ h⟩ (S.transportAlongStageAux g ψ (k + 1) h p) =
        S.transportAlongStageAux g ψ k (Nat.lt_of_succ_lt h)
          ((S.transportAlong g ψ).map ⟨k, Nat.lt_of_succ_lt_succ h⟩ p)
  | 0, _, _ => (g.apply_symm_apply _).symm
  | _ + 1, _, _ => rfl

/-- **The stage identifications commute with the blow-downs**: the square
`σ_{i+1} ∘ e_{i+1} = e_i ∘ σ'_{i+1}` at each step. -/
theorem map_transportAlong (i : Fin S.length) (p : (S.transportAlong g ψ).stage i.succ) :
    S.map i (S.transportAlongStage g ψ i.succ p) =
      S.transportAlongStage g ψ i.castSucc ((S.transportAlong g ψ).map i p) :=
  S.map_transportAlongStageAux g ψ i.1 (Nat.succ_lt_succ i.2) p

/-- The composite blow-downs commute with the identifications, on the auxiliary indices: by
recursion, the square at each step. -/
theorem stageMapAux_transportAlong :
    ∀ (i : ℕ) (h : i < S.length + 1) (p : finStages N₀ (S.transportAlongLater ψ) ⟨i, h⟩),
      S.stageMapAux i h (S.transportAlongStageAux g ψ i h p) =
        g ((S.transportAlong g ψ).stageMapAux i h p)
  | 0, _, _ => rfl
  | k + 1, h, p => by
    change S.stageMapAux k (Nat.lt_of_succ_lt h)
        (S.map ⟨k, Nat.lt_of_succ_lt_succ h⟩ (S.transportAlongStageAux g ψ (k + 1) h p)) =
      g ((S.transportAlong g ψ).stageMapAux k (Nat.lt_of_succ_lt h)
        ((S.transportAlong g ψ).map ⟨k, Nat.lt_of_succ_lt_succ h⟩ p))
    rw [S.map_transportAlongStageAux g ψ k h p]
    exact stageMapAux_transportAlong k (Nat.lt_of_succ_lt h) _

/-- **The composite blow-downs commute with the identifications**: `σ^i ∘ e_i = g ∘ σ'^i`
(Włodarczyk's `σ^i`, [Wlo09, Theorem 2.0.3 (2)]). -/
theorem stageMap_transportAlong (i : Fin (S.length + 1)) (p : (S.transportAlong g ψ).stage i) :
    S.stageMap i (S.transportAlongStage g ψ i p) = g ((S.transportAlong g ψ).stageMap i p) :=
  S.stageMapAux_transportAlong g ψ i.1 i.2 p

/-! ### The centres, the weak transforms and the boundaries -/

/-- **The centres of the transported succession are the pull-backs of `S`'s along the stage
identifications.** -/
theorem center_transportAlong (i : Fin S.length) :
    (S.transportAlong g ψ).center i =
      IdealSheaf.pullbackDiffeomorph (S.transportAlongStage g ψ i.castSucc) (S.center i) := by
  obtain ⟨k, hk⟩ := i
  cases k with
  | zero => rfl
  | succ k => rfl

/-- The centre identity on the auxiliary indices, in the syntactic form of the recursions below. -/
theorem center_transportAlongAux (k : ℕ) (h : k + 1 < S.length + 1) :
    (S.transportAlong g ψ).center ⟨k, Nat.lt_of_succ_lt_succ h⟩ =
      IdealSheaf.pullbackDiffeomorph (S.transportAlongStageAux g ψ k (Nat.lt_of_succ_lt h))
        (S.center ⟨k, Nat.lt_of_succ_lt_succ h⟩) := by
  cases k with
  | zero => rfl
  | succ k => rfl

/-- The weak transforms along the transported succession, on the auxiliary indices: by recursion,
`weakTransform_of_square` on the square at each step. -/
theorem weakTransformSeqAux_transportAlong (J : IdealSheaf N) :
    ∀ (i : ℕ) (h : i < S.length + 1),
      (S.transportAlong g ψ).weakTransformSeqAux (IdealSheaf.pullbackDiffeomorph g J) i h =
        IdealSheaf.pullbackDiffeomorph (S.transportAlongStageAux g ψ i h)
          (S.weakTransformSeqAux J i h)
  | 0, _ => rfl
  | k + 1, h => by
    change IdealSheaf.weakTransform ((S.transportAlong g ψ).map ⟨k, Nat.lt_of_succ_lt_succ h⟩)
        ((S.transportAlong g ψ).weakTransformSeqAux (IdealSheaf.pullbackDiffeomorph g J) k
          (Nat.lt_of_succ_lt h))
        ((S.transportAlong g ψ).center ⟨k, Nat.lt_of_succ_lt_succ h⟩) =
      IdealSheaf.pullbackDiffeomorph (S.transportAlongStageAux g ψ (k + 1) h)
        (IdealSheaf.weakTransform (S.map ⟨k, Nat.lt_of_succ_lt_succ h⟩)
          (S.weakTransformSeqAux J k (Nat.lt_of_succ_lt h))
          (S.center ⟨k, Nat.lt_of_succ_lt_succ h⟩))
    rw [weakTransformSeqAux_transportAlong J k (Nat.lt_of_succ_lt h),
      S.center_transportAlongAux g ψ k h]
    exact IdealSheaf.weakTransform_of_square (S.transportAlongStageAux g ψ k (Nat.lt_of_succ_lt h))
      (S.transportAlongStageAux g ψ (k + 1) h) (S.map ⟨k, Nat.lt_of_succ_lt_succ h⟩)
      ((S.transportAlong g ψ).map ⟨k, Nat.lt_of_succ_lt_succ h⟩)
      (S.map_transportAlongStageAux g ψ k h) _ _

/-- **The weak transforms (clause (ii) of [Hir64, Main Theorem II'(N), p. 156]) along the
transported succession, started with `g^* J`, are the pull-backs of `S`'s along the stage
identifications.** -/
theorem weakTransformSeq_transportAlong (J : IdealSheaf N) (i : Fin (S.length + 1)) :
    (S.transportAlong g ψ).weakTransformSeq (IdealSheaf.pullbackDiffeomorph g J) i =
      IdealSheaf.pullbackDiffeomorph (S.transportAlongStage g ψ i) (S.weakTransformSeq J i) :=
  S.weakTransformSeqAux_transportAlong g ψ J i.1 i.2

/-- The boundaries along the transported succession, on the auxiliary indices: by recursion,
`reducedTransform_of_square` on the square at each step. -/
theorem boundarySeqAux_transportAlong (E₀ : IdealSheaf N) :
    ∀ (i : ℕ) (h : i < S.length + 1),
      (S.transportAlong g ψ).boundarySeqAux (IdealSheaf.pullbackDiffeomorph g E₀) i h =
        IdealSheaf.pullbackDiffeomorph (S.transportAlongStageAux g ψ i h) (S.boundarySeqAux E₀ i h)
  | 0, _ => rfl
  | k + 1, h => by
    change IdealSheaf.reducedTransform ((S.transportAlong g ψ).map ⟨k, Nat.lt_of_succ_lt_succ h⟩)
        ((S.transportAlong g ψ).boundarySeqAux (IdealSheaf.pullbackDiffeomorph g E₀) k
          (Nat.lt_of_succ_lt h))
        ((S.transportAlong g ψ).center ⟨k, Nat.lt_of_succ_lt_succ h⟩) =
      IdealSheaf.pullbackDiffeomorph (S.transportAlongStageAux g ψ (k + 1) h)
        (IdealSheaf.reducedTransform (S.map ⟨k, Nat.lt_of_succ_lt_succ h⟩)
          (S.boundarySeqAux E₀ k (Nat.lt_of_succ_lt h))
          (S.center ⟨k, Nat.lt_of_succ_lt_succ h⟩))
    rw [boundarySeqAux_transportAlong E₀ k (Nat.lt_of_succ_lt h),
      S.center_transportAlongAux g ψ k h]
    exact IdealSheaf.reducedTransform_of_square
      (S.transportAlongStageAux g ψ k (Nat.lt_of_succ_lt h))
      (S.transportAlongStageAux g ψ (k + 1) h) (S.map ⟨k, Nat.lt_of_succ_lt_succ h⟩)
      ((S.transportAlong g ψ).map ⟨k, Nat.lt_of_succ_lt_succ h⟩)
      (S.map_transportAlongStageAux g ψ k h) _ _

/-- **The boundaries (clause (iii) of [Hir64, Main Theorem II'(N), p. 156]) along the transported
succession, started with `g^* E₀`, are the pull-backs of `S`'s along the stage
identifications.** -/
theorem boundarySeq_transportAlong (E₀ : IdealSheaf N) (i : Fin (S.length + 1)) :
    (S.transportAlong g ψ).boundarySeq (IdealSheaf.pullbackDiffeomorph g E₀) i =
      IdealSheaf.pullbackDiffeomorph (S.transportAlongStage g ψ i) (S.boundarySeq E₀ i) :=
  S.boundarySeqAux_transportAlong g ψ E₀ i.1 i.2

/-- The strict transforms along the transported succession, on the auxiliary indices: by
recursion, `strictTransformSubspace_of_square` on the square at each step. -/
theorem strictTransformSubspaceSeqAux_transportAlong (J : IdealSheaf N) :
    ∀ (i : ℕ) (h : i < S.length + 1),
      (S.transportAlong g ψ).strictTransformSubspaceSeqAux (IdealSheaf.pullbackDiffeomorph g J) i
          h =
        IdealSheaf.pullbackDiffeomorph (S.transportAlongStageAux g ψ i h)
          (S.strictTransformSubspaceSeqAux J i h)
  | 0, _ => rfl
  | k + 1, h => by
    change Manifold.strictTransformSubspace
        ((S.transportAlong g ψ).isClosedSubmanifold_center ⟨k, Nat.lt_of_succ_lt_succ h⟩)
        ((S.transportAlong g ψ).isBlowUp_map ⟨k, Nat.lt_of_succ_lt_succ h⟩)
        ((S.transportAlong g ψ).strictTransformSubspaceSeqAux
          (IdealSheaf.pullbackDiffeomorph g J) k (Nat.lt_of_succ_lt h)) =
      IdealSheaf.pullbackDiffeomorph (S.transportAlongStageAux g ψ (k + 1) h)
        (Manifold.strictTransformSubspace
          (S.isClosedSubmanifold_center ⟨k, Nat.lt_of_succ_lt_succ h⟩)
          (S.isBlowUp_map ⟨k, Nat.lt_of_succ_lt_succ h⟩)
          (S.strictTransformSubspaceSeqAux J k (Nat.lt_of_succ_lt h)))
    rw [strictTransformSubspaceSeqAux_transportAlong J k (Nat.lt_of_succ_lt h)]
    have e : ((S.transportAlong g ψ).center ⟨k, Nat.lt_of_succ_lt_succ h⟩).support =
        ⇑(S.transportAlongStageAux g ψ k (Nat.lt_of_succ_lt h)) ⁻¹'
          (S.center ⟨k, Nat.lt_of_succ_lt_succ h⟩).support := by
      rw [S.center_transportAlongAux g ψ k h]
      exact IdealSheaf.support_pullbackDiffeomorph _ _
    exact (Manifold.strictTransformSubspace_of_square
      (S.transportAlongStageAux g ψ k (Nat.lt_of_succ_lt h))
      (S.transportAlongStageAux g ψ (k + 1) h) ψ (S.isClosedSubmanifold_center _)
      (S.isBlowUp_map _) ((S.transportAlong g ψ).isClosedSubmanifold_center _)
      ((S.transportAlong g ψ).isBlowUp_map _) e (S.map_transportAlongStageAux g ψ k h) _).symm

/-- **The strict transforms of a closed subspace along the transported succession, started with
`g^* J`, are the pull-backs of `S`'s along the stage identifications** (Kollár's restricted
sequence [Kol07, Definition 30.2]; Włodarczyk's strict transforms `Y_i` [Wlo09, Theorem 2.0.2
(2)]). -/
theorem strictTransformSubspaceSeq_transportAlong (J : IdealSheaf N) (i : Fin (S.length + 1)) :
    (S.transportAlong g ψ).strictTransformSubspaceSeq (IdealSheaf.pullbackDiffeomorph g J) i =
      IdealSheaf.pullbackDiffeomorph (S.transportAlongStage g ψ i)
        (S.strictTransformSubspaceSeq J i) :=
  S.strictTransformSubspaceSeqAux_transportAlong g ψ J i.1 i.2

/-- **The composite blow-down of the transported succession is `g⁻¹ ∘ σ^r` through the
identification of the end results** (Włodarczyk's `σ^r` [Wlo09, Theorem 2.0.3]; Hironaka's
canonical modification [Hir64, p. 155]). -/
theorem composite_transportAlong (p : (S.transportAlong g ψ).last) :
    S.composite (S.transportAlongStage g ψ (Fin.last _) p) =
      g ((S.transportAlong g ψ).composite p) :=
  S.stageMap_transportAlong g ψ (Fin.last _) p

end AnalyticManifold.FiniteSuccession

end
