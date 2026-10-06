/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictSubspaceSeq
public import Hironaka.AnalyticSpace.Manifold.Defs
public import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.AnalyticSpace.Manifold.Comap
import Hironaka.Manifold.BlowUp.Transform.StrictSubspace
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The composite of a blow-up sequence carries a closed subspace into its strict transform

For a closed subspace `Y ⊆ M` with ideal sheaf `J` and a finite blow-up sequence
`π_0, …, π_{r-1}` with smooth centres, the ideal-theoretic strict transforms `Y_i` of
`FiniteSuccession.strictTransformSubspaceSeq` (`StrictSubspaceSeq.lean`) contain the inverse
images of `J`: `σ^{i*}(J) · 𝒪_{U_i} ⊆ 𝓘_{Y_i}` for the composite `σ^i : U_i → M`. At each step
the strict transform contains the total transform (`totalTransform_le_strictTransformSubspace`):
the strict transform is the saturation of the total transform by the exceptional divisor
[BM97, §3, Proposition 3.13], the total transform being the subspace defined by the inverse image
ideal [Hir64, Ch. 0, §5, pp. 141–142]; compare `σ^*(I_Y) = I_Ỹ I_Ẽ` in [Wlo09, Theorem 2.0.2(6)].
Inverse images compose along the composite (`IdealSheaf.pullback_comp`). Read on the analytic
spaces `Sp(U_i)`, `Sp(M)`, this is exactly the compatibility `QuotientSpace.Compat` that
`KLocallyRingedSpace.quotientMap` needs to induce the morphism of closed subspaces `Y_r → Y_0`
over `σ^r`: the local resolution map `Ỹ_Z → Y_Z` of Włodarczyk's canonical desingularization of a
germ [Wlo09, §4, (3)⇒(4)] (which, as Kollár warns, need not itself be a composite of smooth
blow-ups [Kol07, Warning 23]), and the fields `map`/`map_comp` of `AmbientBlowUpFactorization`.

* `FiniteSuccession.comap_stageMap_le_strictTransformSubspaceSeq S J i`: `σ^{i*}J ≤ 𝓘_{Y_i}`.
* `FiniteSuccession.compat_composite_strictTransformSubspaceSeq S ψ J`: the `Compat` of
  `Sp(σ^r)` between `𝓘_{Y_r}` and `J`.
-/

public section

noncomputable section

open TopologicalSpace Manifold AnalyticSpace
open scoped Manifold ContDiff Topology

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- Along the succession the inverse image of the closed subspace `J` under the composite
`σ^i : U_i → M` lies in the strict transform `Y_i`: by induction on the stage, each step being
`totalTransform_le_strictTransformSubspace` at the succession's witnesses (the strict transform is
the saturation of the total transform, [BM97, §3, Proposition 3.13]; the total transform is
[Hir64, Ch. 0, §5, pp. 141–142]). -/
theorem comap_stageMap_le_strictTransformSubspaceSeq (J : IdealSheaf M) :
    ∀ i : Fin (S.length + 1), J.pullback _ (S.stageMap i).contMDiff ≤ S.strictTransformSubspaceSeq
        J i := by
  intro i
  induction i using Fin.induction with
  | zero =>
    rw [strictTransformSubspaceSeq_zero, stageMap_zero]
    change J.pullback (id : M → M) contMDiff_id ≤ J
    rw [IdealSheaf.pullback_id_eq_self]
  | succ i ih =>
    rw
        [stageMap_succ, ← IdealSheaf.pullback_comp,
            strictTransformSubspaceSeq_succ]
    exact le_trans (IdealSheaf.pullback_le_pullback _ _ ih)
      (totalTransform_le_strictTransformSubspace (S.isClosedSubmanifold_center i)
        (S.isBlowUp_map i) (S.strictTransformSubspaceSeq J i.castSucc))

/-- The composite `Sp(σ^r) : Sp(U_r) → Sp(M)` is compatible (`QuotientSpace.Compat`) with the
final strict transform `𝓘_{Y_r}` and `J`: the hypothesis under which
`KLocallyRingedSpace.quotientMap` induces the morphism of closed subspaces
`Sp(U_r)/𝓘_{Y_r} → Sp(M)/J` over `Sp(σ^r)`, the local resolution map `Ỹ_Z → Y_Z` of
[Wlo09, §4, (3)⇒(4)] and the fields `map`/`map_comp` of `AmbientBlowUpFactorization`. -/
theorem compat_composite_strictTransformSubspaceSeq (ψ : E ≃L[𝕜] (Fin n → 𝕜))
    (J : IdealSheaf M) :
    QuotientSpace.Compat (toSpaceHom ψ S.composite).1
      (S.strictTransformSubspaceSeq J (Fin.last S.length)) J := by
  intro z'
  have h := (IdealSheaf.le_def.mp
    (S.comap_stageMap_le_strictTransformSubspaceSeq J (Fin.last S.length))) z'
  have e := QuotientSpace.stalkIdeal_comap (toSpaceHom ψ S.composite).1 J z'
  have e2 : QuotientSpace.comap (toSpaceHom ψ S.composite).1 J =
      J.pullback S.composite S.composite.contMDiff :=
    KLocallyRingedSpace.comap_ofManifoldHom_eq_pullback S.composite S.composite.contMDiff J
  exact le_of_eq_of_le (e.symm.trans (congrArg (fun K => K.stalkIdeal z') e2)) h

end AnalyticManifold.FiniteSuccession

end
