/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Finite successions of monoidal transformations

Włodarczyk's finite sequence of blow-ups with smooth centres [Wlo09, Theorem 2.0.3 (1);
Theorem 3.6.1] — in Hironaka's words [Hir64, p. 155] a succession of monoidal transformations
indexed by the finite well-ordered set `Λ = {0 < 1 < ⋯ < r}`. A `FiniteSuccession M` has stages
`U_0 = M, U_1, …, U_r` (`finStages`), centres `C_i ⊆ U_i` given by ideal sheaves, and maps
`σ_{i+1} : U_{i+1} → U_i`, each the monoidal transformation of `U_i` with centre `C_i`
(`AnalyticMap.IsMonoidalTransformation`: the centre is a closed submanifold, Włodarczyk's "smooth
centers"). Local finiteness is automatic for a finite `Λ`; empty centres are admitted (a monoidal
transformation with empty centre is an isomorphism).

* `stage`, `stageMap` (the composite `σ^i : U_i → M`), `last` and `composite` (`σ^r`), by
  recursion on the stage;
* `weakTransformSeq` (Hironaka's weak transforms `J_i`) and `boundarySeq` (his boundaries `E_i`),
  by recursion from the one-step `IdealSheaf.weakTransform` and `IdealSheaf.reducedTransform`
  (clauses (ii) and (iii) of [Hir64, Main Theorem II'(N), p. 156]);
* the data witnessing that each step is a monoidal transformation, extracted by choice: `dimAt`,
  `chartAt`, `codim`, with the centre a closed submanifold (`isClosedSubmanifold_center`) and the
  map a blowing-up along it (`isBlowUp_map`).
* `strictTransformSubspaceSeq` (the strict transforms `Y_i` of a closed subspace `Y`, Kollár's
  restricted sequence [Kol07, Definition 30.2]), by recursion from the one-step
  `strictTransformSubspace` at those witnesses.

The analytic main theorems assert, for the succession over each compact set of a compatible
family (`ExtensionCompatibleFamily`), Hironaka's clauses on the centres, the weak transforms and the
boundaries.
-/

@[expose] public section

universe u

open scoped Manifold ContDiff
open TopologicalSpace

namespace AnalyticManifold

noncomputable section

section General

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- The stages of a finite succession from the data of the later stages: `U_0 = M`,
`U_{i+1} = later i`. -/
def finStages (M : AnalyticManifold.{u} 𝕜 E) {r : ℕ} (later : Fin r → AnalyticManifold.{u} 𝕜 E) :
    Fin (r + 1) → AnalyticManifold.{u} 𝕜 E
  | ⟨0, _⟩ => M
  | ⟨i + 1, h⟩ => later ⟨i, Nat.lt_of_succ_lt_succ h⟩

end General

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### Finite successions of monoidal transformations -/

/-- Włodarczyk's finite sequence of blow-ups with smooth centres [Wlo09, Theorem 2.0.3 (1);
Theorem 3.6.1]: Hironaka's succession of monoidal transformations `{f_λ : X_{λ+1} → X_λ}_{λ ∈ Λ}`
[Hir64, p. 155] for the finite well-ordered set `Λ = {0 < 1 < ⋯ < r}` — stages `U_i` with
`U_0 = M`, centres `C_i ⊆ U_i` and maps `σ_{i+1} : U_{i+1} → U_i` for `0 ≤ i < r`, each the
monoidal transformation of `U_i` with centre `C_i`. The empty succession (`length = 0`) is
`Λ = {0}`. Empty centres are admitted (a monoidal transformation with empty centre is an
isomorphism: Włodarczyk's "isomorphisms" in [Wlo09, Definitions 3.2.5, 3.2.6]). -/
structure FiniteSuccession (M : AnalyticManifold.{u} 𝕜 E) where
  /-- The length `r`: the number of blow-ups. -/
  length : ℕ
  /-- The later stages `U_1, …, U_r`. -/
  later : Fin length → AnalyticManifold.{u} 𝕜 E
  /-- The centre `C_i ⊆ U_i` of the blow-up `σ_{i+1}`, `0 ≤ i < r`. -/
  center : ∀ i : Fin length, IdealSheaf (finStages M later i.castSucc)
  /-- The blow-up `σ_{i+1} : U_{i+1} → U_i`. -/
  map : ∀ i : Fin length, AnalyticMap (finStages M later i.succ) (finStages M later i.castSucc)
  /-- `σ_{i+1}` is the monoidal transformation of `U_i` with centre `C_i` (the centre is a closed
submanifold: Włodarczyk's "smooth centers"). -/
  isMonoidal : ∀ i, AnalyticMap.IsMonoidalTransformation (map i) (center i)

namespace FiniteSuccession

section Accessors

variable {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The stage `U_i`, `0 ≤ i ≤ r`, with `U_0 = M`. -/
abbrev stage (i : Fin (S.length + 1)) : AnalyticManifold.{u} 𝕜 E := finStages M S.later i

/-- The composite `σ^i = σ_1 ∘ ⋯ ∘ σ_i : U_i → U_0 = M` (Włodarczyk's `σ^i`,
[Wlo09, Theorem 2.0.3 (2)]; Hironaka's canonical morphism `X_λ → X_0` [Hir64, p. 155]), by
recursion on `i`. -/
def stageMapAux : ∀ (i : ℕ) (h : i < S.length + 1), AnalyticMap (finStages M S.later ⟨i, h⟩) M
  | 0, _ => ContMDiffMap.id
  | i + 1, h =>
    (stageMapAux i (Nat.lt_of_succ_lt h)).comp (S.map ⟨i, Nat.lt_of_succ_lt_succ h⟩)

/-- The composite `σ^i : U_i → M`. -/
def stageMap (i : Fin (S.length + 1)) : AnalyticMap (S.stage i) M := S.stageMapAux i.1 i.2

/-- The end result `U_r`. -/
abbrev last : AnalyticManifold.{u} 𝕜 E := S.stage (Fin.last S.length)

/-- The composite `σ^r = σ_1 ∘ ⋯ ∘ σ_r : U_r → M` of the whole succession (Włodarczyk's `σ^r`;
Hironaka's canonical modification `X_γ → X` [Hir64, p. 155]). -/
def composite : AnalyticMap S.last M := S.stageMap (Fin.last S.length)

/-- The weak transforms `J_i` along the succession: `J_0 = J`, `J_{i+1}` the weak transform of
`J_i` by `σ_{i+1}` (clause (ii) of [Hir64, Main Theorem II'(N), p. 156]), by recursion on `i`. -/
def weakTransformSeqAux (J : IdealSheaf M) :
    ∀ (i : ℕ) (h : i < S.length + 1), IdealSheaf (finStages M S.later ⟨i, h⟩)
  | 0, _ => J
  | i + 1, h =>
    AnalyticManifold.IdealSheaf.weakTransform (S.map ⟨i, Nat.lt_of_succ_lt_succ h⟩)
      (weakTransformSeqAux J i (Nat.lt_of_succ_lt h)) (S.center ⟨i, Nat.lt_of_succ_lt_succ h⟩)

/-- The weak transform `J_i` on the stage `U_i`. -/
def weakTransformSeq (J : IdealSheaf M) (i : Fin (S.length + 1)) : IdealSheaf (S.stage i) :=
  S.weakTransformSeqAux J i.1 i.2

/-- The boundaries `E_i` along the succession: `E_0 = E`,
`E_{i+1} = red(σ_{i+1}⁻¹(E_i) ∪ σ_{i+1}⁻¹(C_i))` (clause (iii) of [Hir64, Main Theorem II'(N),
p. 156]), by recursion on `i`. -/
def boundarySeqAux (E₀ : IdealSheaf M) :
    ∀ (i : ℕ) (h : i < S.length + 1), IdealSheaf (finStages M S.later ⟨i, h⟩)
  | 0, _ => E₀
  | i + 1, h =>
    AnalyticManifold.IdealSheaf.reducedTransform (S.map ⟨i, Nat.lt_of_succ_lt_succ h⟩)
      (boundarySeqAux E₀ i (Nat.lt_of_succ_lt h)) (S.center ⟨i, Nat.lt_of_succ_lt_succ h⟩)

/-- The boundary `E_i` on the stage `U_i`. -/
def boundarySeq (E₀ : IdealSheaf M) (i : Fin (S.length + 1)) : IdealSheaf (S.stage i) :=
  S.boundarySeqAux E₀ i.1 i.2

end Accessors

/-! ### The witnesses of `isMonoidal`: every step is a blowing-up with a specified centre -/

section Witnesses

open Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M) (i : Fin S.length)

/-- The dimension `n` of the model space in the chart data of the `i`-th blow-up (a witness of
`isMonoidal i`, chosen). -/
def dimAt : ℕ := (S.isMonoidal i).choose

/-- The chart `E ≃ 𝕜ⁿ` of the `i`-th blow-up (chosen). -/
def chartAt : E ≃L[𝕜] (Fin (S.dimAt i) → 𝕜) := (S.isMonoidal i).choose_spec.choose

/-- The codimension `c_i` of the centre `Z_i` (chosen). -/
def codim : ℕ := (S.isMonoidal i).choose_spec.choose_spec.choose

/-- The centre `Z_i ⊂ X_i` of the `i`-th blow-up, the cosupport of the ideal sheaf `C_i`, is a
closed submanifold. -/
theorem isClosedSubmanifold_center :
    IsClosedSubmanifold (S.chartAt i) (S.center i).support (S.codim i) :=
  (S.isMonoidal i).choose_spec.choose_spec.choose_spec.1

/-- `π_i` is a blow-up with centre `Z_i` [Kol07, Definition 29], in the sense of
[BM88, Definition 4.1]. -/
theorem isBlowUp_map : IsBlowUp (S.chartAt i) (S.center i).support (S.codim i) (S.map i) :=
  (S.isMonoidal i).choose_spec.choose_spec.choose_spec.2.2

end Witnesses

/-! ### The strict transforms of a closed subspace -/

section StrictTransform

open Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The ideal-theoretic strict transforms `Y_i ⊆ U_i` of the closed subspace `J ⊆ 𝒪_M` along
the succession, indexed by a natural number together with a proof that it is a stage: `Y_0 = J`,
`Y_{i+1}` the strict transform (`strictTransformSubspace`) of `Y_i` under the `i`-th blow-up at
its witnesses. -/
def strictTransformSubspaceSeqAux (J : IdealSheaf M) :
    ∀ (i : ℕ) (h : i < S.length + 1), IdealSheaf (finStages M S.later ⟨i, h⟩)
  | 0, _ => J
  | i + 1, h =>
    strictTransformSubspace (S.isClosedSubmanifold_center ⟨i, Nat.lt_of_succ_lt_succ h⟩)
      (S.isBlowUp_map ⟨i, Nat.lt_of_succ_lt_succ h⟩)
      (strictTransformSubspaceSeqAux J i (Nat.lt_of_succ_lt h))

/-- **The strict transform `Y_i ⊆ U_i` of the closed subspace `J` at stage `i`** of the
succession ([Kol07, Definition 30.2]; the chain `Ỹ_Z` of [Wlo09, §4, (3)⇒(4)]): `Y_0 = J` and
`Y_{i+1}` the strict transform of `Y_i` under the `i`-th blow-up, the saturation of its total
transform by the exceptional divisor ([BM97, §3, Proposition 3.13]). -/
def strictTransformSubspaceSeq (J : IdealSheaf M) (i : Fin (S.length + 1)) :
    IdealSheaf (S.stage i) :=
  S.strictTransformSubspaceSeqAux J i.1 i.2

end StrictTransform

end FiniteSuccession

end

end AnalyticManifold
