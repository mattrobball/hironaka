/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
public import Hironaka.Manifold.FiniteSuccession.Restrict.RestrictBundle
public import Hironaka.Manifold.Snc.Proper
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Resolution.Analytic.Kol07Thm45.PushforwardBoundaryTrace
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Hironaka.Resolution.Analytic.Functor.Family
import Mathlib.Topology.Gluing
import Mathlib.Topology.Sets.Opens

/-!
# The exceptional family of a restricted push-forward, read on the carried slice

Kollár pushes a blow-up sequence `L_S` of the slice `S ∩ U` forward to the padded sequence
`L_P = pushforwardRestrict hS U L_S` of `U` [Kol07, Definition 30.3]; the carried slice `S_r` of
the last stage, with the identification `G : (L_S)_r ≃ S_r`, is where the padded local resolution
is read (`exists_closedSubmanifold_last_pushforwardRestrict`, `LocalResolutionPad.lean`).
`PushforwardBoundaryTrace.lean` and `exists_closedSubmanifold_last_pushforwardRestrict_boundary`
(`LocalResolutionPad.lean`) add, under the normal-crossings clause (3′) of [Kol07, Definition 66]
for `L_P`: the last-stage exceptional family of `L_P` has simple normal crossings with `S_r`
properly, and an order isomorphism `o` of the stage sets with `(j_r ∘ G)⁻¹(H^P_{o j}) = H^S_j` —
the set-level statement that the padded run's exceptional divisors trace to the slice run's,
stage for stage. This module provides the ideal-level form for the gluing of the exceptional
families: the padded members restrict to the slice members as closed subspaces. Two theorems, of
which the first is what `CoproductPadIdentity.lean` uses, while the second packages it along the
order isomorphism `o` and has no other user:

* `IsClosedSubmanifold.pullback_idealSheaf_inclusionMap_comp_of_hasSncWithProper`: the ideal
  sheaf of a member of a family having simple normal crossings with `S` properly, pulled back along
  `incl_S ∘ G` for a diffeomorphism `G` onto the bundled `S`, is the ideal sheaf of its preimage —
  `pullback_idealSheaf_inclusionMap_of_hasSncWithProper` along the inclusion, then the pull-back
  along `G` as a local diffeomorphism (`comap_idealSheaf_of_isLocalDiffeomorph`);
* `BlowUpSequence.exists_orderIso_pullback_idealSheaf_pushFamily`: with the boundary data of
  `exists_closedSubmanifold_last_pushforwardRestrict_boundary` as binders, an order isomorphism
  `e := o.symm` of the stage sets along which every padded member pulls back, as a reduced ideal
  sheaf, to the slice member — for any closed-submanifold witnesses of the members (the witnesses
  are proofs of propositions).

Sources: the counterpart, for the boundary, of the restriction `Z_i ∩ S_i` of
[Kol07, Definition 30.2], at the level of ideals, along the push-forward of
[Kol07, Definition 30.3]. The proofs are routine.
-/

public section

noncomputable section

open TopologicalSpace Set Hironaka.Manifold Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

section R1

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}

/-- **The ideal sheaf of a member of a family having simple normal crossings with `S` properly,
pulled back along `incl_S ∘ G` for a diffeomorphism `G : X ≃ S`, is the ideal sheaf of its
preimage** (any closed-submanifold witness of that preimage; the counterpart, for the boundary, of
the restriction `Z_i ∩ S_i` of [Kol07, Definition 30.2], in the transverse case) — the
composite-map form of
`pullback_idealSheaf_inclusionMap_of_hasSncWithProper`: that theorem along the inclusion, then the
pull-back along `G` as a local diffeomorphism (`comap_idealSheaf_of_isLocalDiffeomorph`) and the
preimage read through `G`. -/
theorem IsClosedSubmanifold.pullback_idealSheaf_inclusionMap_comp_of_hasSncWithProper
    (hS : IsClosedSubmanifold ψ S s) {F : HypersurfaceFamily M} (hF : F.IsSnc ψ)
    (hFS : F.HasSncWithProper ψ S s) {X : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
    (G : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) X hS.toAnalyticManifold ω)
    (j : F.ι) {H : Set X}
    (hH : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) H 1)
    (hHj : H = (⇑hS.inclusionMap ∘ ⇑G) ⁻¹' F.hyp j) :
    IdealSheaf.pullback (⇑hS.inclusionMap ∘ ⇑G) (hS.inclusionMap.contMDiff.comp G.contMDiff)
        (hF.1 j).idealSheaf = hH.idealSheaf := by
  refine (IdealSheaf.pullback_pullback (hF.1 j).idealSheaf ⇑hS.inclusionMap
    hS.inclusionMap.contMDiff ⇑G G.contMDiff).symm.trans ?_
  rw [hS.pullback_idealSheaf_inclusionMap_of_hasSncWithProper hF hFS j]
  have h := comap_idealSheaf_of_isLocalDiffeomorph
    (ψ := ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) (Diffeomorph.toAnalyticMap G)
    G.isLocalDiffeomorph ((hS.isSnc_traceFamily hF hFS).1 j)
  exact h.trans (IsClosedSubmanifold.idealSheaf_congr _ hH (by rw [hHj]; rfl))

end R1

end Manifold

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}
  (hS : IsClosedSubmanifold ψ S s) (U : Opens M)
  (L_S : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
    ((hS.toAnalyticManifold).restrict (hS.preimageOpens U)))

/-- **The padded run's last-stage exceptional members pull back along the carried-slice
identification `incl_{S_r} ∘ G` to the slice run's, as reduced ideal sheaves, through an order
isomorphism of the stage sets** ([Kol07, Definitions 30.2–30.3]). The binders `hprop` (the proper
simple normal crossings) and `o`/`ho` (the trace identity) are the fourth conjunct of
`exists_closedSubmanifold_last_pushforwardRestrict_boundary` and determine `G`; `hsncP` is clause
(1) of `IsEmbeddedDesing` (the exceptional divisors have simple normal crossings) for the padded
run at its last stage; `hclP`/`hclS` are any witnesses of the members (proofs of propositions).
Then `e := o.symm` and, per member,
`pullback_idealSheaf_inclusionMap_comp_of_hasSncWithProper` at the set identity `ho`. -/
theorem exists_orderIso_pullback_idealSheaf_pushFamily
    {S_r : Set ((pushforwardRestrict hS U L_S).toSuccession.stage (Fin.last _))}
    (hS_r : IsClosedSubmanifold ψ S_r s)
    (G : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜)
      (L_S.toSuccession.stage (Fin.last _)) hS_r.toAnalyticManifold ω)
    (hsncP : ((pushforwardRestrict hS U L_S).toSuccession.totalTransformSeq
      (Fin.last _)).IsSnc ψ)
    (hprop : ((pushforwardRestrict hS U L_S).toSuccession.totalTransformSeq
      (Fin.last _)).HasSncWithProper ψ S_r s)
    (o : (L_S.toSuccession.totalTransformSeq (Fin.last _)).ι ≃o
      ((pushforwardRestrict hS U L_S).toSuccession.totalTransformSeq (Fin.last _)).ι)
    (ho : ∀ j, (⇑hS_r.inclusionMap ∘ ⇑G) ⁻¹'
        ((pushforwardRestrict hS U L_S).toSuccession.totalTransformSeq
          (Fin.last _)).hyp (o j) =
      (L_S.toSuccession.totalTransformSeq (Fin.last _)).hyp j)
    (hcont : ContMDiff 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, E) ω (⇑hS_r.inclusionMap ∘ ⇑G))
    (hclP : ∀ j, IsClosedSubmanifold ψ
      (((pushforwardRestrict hS U L_S).toSuccession.totalTransformSeq
        (Fin.last _)).hyp j) 1)
    (hclS : ∀ j, IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      ((L_S.toSuccession.totalTransformSeq (Fin.last _)).hyp j) 1) :
    ∃ e : ((pushforwardRestrict hS U L_S).toSuccession.totalTransformSeq
        (Fin.last _)).ι ≃o (L_S.toSuccession.totalTransformSeq (Fin.last _)).ι,
      ∀ j, IdealSheaf.pullback (⇑hS_r.inclusionMap ∘ ⇑G) hcont (hclP j).idealSheaf =
        (hclS (e j)).idealSheaf := by
  refine ⟨o.symm, fun j => ?_⟩
  have hset : (L_S.toSuccession.totalTransformSeq (Fin.last _)).hyp (o.symm j) =
      (⇑hS_r.inclusionMap ∘ ⇑G) ⁻¹'
        ((pushforwardRestrict hS U L_S).toSuccession.totalTransformSeq
          (Fin.last _)).hyp j := by
    have h := ho (o.symm j)
    rw [o.apply_symm_apply] at h
    exact h.symm
  exact IsClosedSubmanifold.pullback_idealSheaf_inclusionMap_comp_of_hasSncWithProper hS_r hsncP
    hprop G j (hclS (o.symm j)) hset

end AnalyticManifold.BlowUpSequence

end
