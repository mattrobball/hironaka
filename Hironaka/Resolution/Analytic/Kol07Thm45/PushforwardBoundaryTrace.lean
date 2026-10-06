/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Pushforward
public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
public import Hironaka.Manifold.Snc.Trace
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Restrict.BoundaryTrace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The boundary of a push-forward traces to the boundary of the given sequence

Kollár pushes a blow-up sequence `T` of a closed submanifold `S ⊆ M` forward to a sequence
`Π = j_* T` of `M` with the same centres, and reads the boundary of `Π` back on the carried strict
transforms `S_i` through the inclusions `j_i : T_i → X_i` [Kol07, Definitions 30.2–30.3].
`BoundaryTrace.lean` provides the invariant that the boundary family `F_i^X` of `Π` has simple
normal crossings with `S_i` PROPERLY
(`hasSncWithProper_totalTransformSeq_strictTransformSeq_of_forall_lt`) and the UNION-level
identification of its trace with the boundary of `Π|_S` (`traceFamily`;
`boundarySeq_pushforwardStageIso` of `GoingUp/StageIso.lean`). The gluing of the exceptional
families along the padding needs the MEMBER-level trace identity — which exceptional divisor of
`Π` traces to which of `T` — and the ideal-theoretic form of the trace of a transverse member.
This file proves both, with no blow-up-chart computation on the slice: the proper
simple-normal-crossings chart of the AMBIENT stage and a one-coordinate density argument suffice.

* `preimage_pushforwardIncl_preimage_center`, `preimage_pushforwardIncl_preimage_diff_center`,
  `preimage_pushforwardIncl_strictTransformSet`: the three steps of the induction.
* `exists_orderIso_totalTransformSeq_pushforward`: the trace identity at every stage — an order
  isomorphism of the index types with `j_i⁻¹(H^X_{i, o j}) = H_{i, j}`.
* `IsClosedSubmanifold.pullback_idealSheaf_inclusionMap_of_hasSncWithProper`: the ideal sheaf of a
  member pulled back along the inclusion of a closed submanifold having simple normal crossings
  with the family properly is the ideal sheaf of its trace.

Used by `LocalResolutionPad.lean` (`exists_closedSubmanifold_last_pushforwardRestrict_boundary`)
and `PushforwardFamily.lean`. Not in the sources; routine.
-/

public section

noncomputable section
open TopologicalSpace Set Manifold Topology Filter
open CategoryTheory Opposite
open scoped Manifold ContDiff
universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}
  (hS : IsClosedSubmanifold ψ S s) (T : FiniteSuccession hS.toAnalyticManifold)

/-- The NEW member: the exceptional divisor of the push-forward's step traces on the slice to the
exceptional divisor of the given step ([Kol07, Definition 30.3]): `j_{i+1}⁻¹(π⁻¹ Z^X) = π_T⁻¹ Z` —
the square `pushforwardIncl_map`, the centre `Z^X = j_i(Z)` (`support_center_pushforward`) and the
injectivity of `j_i`. -/
theorem preimage_pushforwardIncl_preimage_center (i : Fin T.length) :
    ⇑(T.pushforwardIncl hS i.succ) ⁻¹'
        (⇑((T.pushforward hS).map i) ⁻¹' ((T.pushforward hS).center i).support) =
      ⇑(T.map i) ⁻¹' (T.center i).support := by
  ext p
  change (T.pushforward hS).map i (T.pushforwardIncl hS i.succ p) ∈
      ((T.pushforward hS).center i).support ↔ T.map i p ∈ (T.center i).support
  rw [← T.pushforwardIncl_map hS i p, T.support_center_pushforward hS i]
  exact (T.isClosedEmbedding_pushforwardIncl hS i.castSucc).injective.mem_set_image

/-- The part of a member off the centre traces to the part of its trace off the centre:
`j_{i+1}⁻¹(π⁻¹(A ∖ Z^X)) = π_T⁻¹(B ∖ Z)` when `j_i⁻¹ A = B`. -/
theorem preimage_pushforwardIncl_preimage_diff_center (i : Fin T.length)
    {A : Set ((T.pushforward hS).stage i.castSucc)} {B : Set (T.stage i.castSucc)}
    (hAB : ⇑(T.pushforwardIncl hS i.castSucc) ⁻¹' A = B) :
    ⇑(T.pushforwardIncl hS i.succ) ⁻¹'
        (⇑((T.pushforward hS).map i) ⁻¹' (A \ ((T.pushforward hS).center i).support)) =
      ⇑(T.map i) ⁻¹' (B \ (T.center i).support) := by
  subst hAB
  ext p
  change ((T.pushforward hS).map i (T.pushforwardIncl hS i.succ p) ∈ A ∧
      (T.pushforward hS).map i (T.pushforwardIncl hS i.succ p) ∉
        ((T.pushforward hS).center i).support) ↔
    (T.pushforwardIncl hS i.castSucc (T.map i p) ∈ A ∧ T.map i p ∉ (T.center i).support)
  rw [← T.pushforwardIncl_map hS i p, T.support_center_pushforward hS i]
  exact and_congr Iff.rfl
    (not_congr (T.isClosedEmbedding_pushforwardIncl hS i.castSucc).injective.mem_set_image)

/-- An OLD member ([Kol07, Definition 30.2]): **the strict transform commutes with the trace on
the carried slice** — for a member `A` of the push-forward's boundary at stage `i` whose trace on
`T_i` is `B`, the trace on `T_{i+1}` of the strict transform of `A` is the strict transform of `B`.
`⊇` by continuity of `j_{i+1}` and `preimage_pushforwardIncl_preimage_diff_center`. `⊆`: at
`x = j_{i+1} q'` on the strict transform of `A`, if `x` is off the exceptional divisor `E'` then
`x ∈ π⁻¹(A ∖ Z^X)` itself; if `x ∈ E'`, the proper simple-normal-crossings chart of the boundary at
`x` along `S_{i+1}` (`hasSncWithProper_totalTransform`) has the member as `{y_c = 0}` and `E'` as
`{y_d = 0}`, `c ≠ d`, both off the `S_{i+1}`-block; moving the
`d`-coordinate alone, `y_t := φ⁻¹(ψ⁻¹(update (ψ (φ x)) d t))`, `t ≠ 0`, lies on `S_{i+1}` and on the
member and off `E'`, so in `π⁻¹(A ∖ Z^X) ∩ S_{i+1}`, and `y_t → x` — `x` is in the closure, and
`q'` is in the closure of the trace by `IsInducing.closure_eq_preimage_closure_image`. -/
theorem preimage_pushforwardIncl_strictTransformSet (i : Fin T.length)
    (hsnc₀ : ((T.pushforward hS).totalTransformSeq i.castSucc).IsSnc ψ)
    (hprop : ((T.pushforward hS).totalTransformSeq i.succ).HasSncWithProper ψ
      ((T.pushforward hS).strictTransformSeq S i.succ) s)
    (k₀ : ((T.pushforward hS).totalTransformSeq i.castSucc).ι) {B : Set (T.stage i.castSucc)}
    (hAB : ⇑(T.pushforwardIncl hS i.castSucc) ⁻¹'
      ((T.pushforward hS).totalTransformSeq i.castSucc).hyp k₀ = B) :
    ⇑(T.pushforwardIncl hS i.succ) ⁻¹'
        strictTransformSet ((T.pushforward hS).map i) ((T.pushforward hS).center i).support
          (((T.pushforward hS).totalTransformSeq i.castSucc).hyp k₀) =
      strictTransformSet (T.map i) (T.center i).support B := by
  have hπc : Continuous ((T.pushforward hS).map i) :=
    ((T.pushforward hS).map i).contMDiff.continuous
  have hA : IsClosed (((T.pushforward hS).totalTransformSeq i.castSucc).hyp k₀) :=
    (hsnc₀.1 k₀).isClosed
  have hdiff := T.preimage_pushforwardIncl_preimage_diff_center hS i hAB
  have hj : IsClosedEmbedding (T.pushforwardIncl hS i.succ) :=
    T.isClosedEmbedding_pushforwardIncl hS i.succ
  apply Set.Subset.antisymm
  · intro q' hq'
    rw [strictTransformSet, hj.isInducing.closure_eq_preimage_closure_image, ← hdiff,
      Set.image_preimage_eq_inter_range, Set.mem_preimage]
    have hxS : T.pushforwardIncl hS i.succ q' ∈ (T.pushforward hS).strictTransformSeq S i.succ := by
      rw [← T.range_pushforwardIncl hS i.succ]
      exact ⟨q', rfl⟩
    by_cases hxZ : (T.pushforward hS).map i (T.pushforwardIncl hS i.succ q') ∈
        ((T.pushforward hS).center i).support
    · -- over the centre: the proper snc chart at `x := j q'`
      obtain ⟨φ, σ, cidx, hφ, hc, hproper⟩ := hprop _ hxS
      have hxA : T.pushforwardIncl hS i.succ q' ∈
          ((T.pushforward hS).totalTransformSeq i.succ).hyp (toLex (Sum.inl k₀)) := hq'
      have hxE : T.pushforwardIncl hS i.succ q' ∈
          ((T.pushforward hS).totalTransformSeq i.succ).hyp (toLex (Sum.inr PUnit.unit)) := hxZ
      have hcd : cidx ⟨_, hxA⟩ ≠ cidx ⟨_, hxE⟩ := fun h => by
        have h' := congrArg Subtype.val (hc.injective h)
        exact Sum.inl_ne_inr (show Sum.inl k₀ = Sum.inr PUnit.unit from congrArg ofLex h')
      have hx0 : ψ (φ (T.pushforwardIncl hS i.succ q')) (cidx ⟨_, hxE⟩) = 0 :=
        (hc.mem_iff ⟨_, hxE⟩ hc.2.1).mp hxE
      have hcont : Continuous fun t : 𝕜 =>
          ψ.symm (Function.update (ψ (φ (T.pushforwardIncl hS i.succ q'))) (cidx ⟨_, hxE⟩) t) :=
        ψ.symm.continuous.comp (continuous_const.update _ continuous_id)
      have hlim0 : Tendsto (fun t : 𝕜 =>
          ψ.symm (Function.update (ψ (φ (T.pushforwardIncl hS i.succ q'))) (cidx ⟨_, hxE⟩) t))
          (𝓝 0) (𝓝 (φ (T.pushforwardIncl hS i.succ q'))) := by
        have h := hcont.tendsto 0
        rwa [Function.update_eq_self_iff.mpr hx0.symm, ψ.symm_apply_apply] at h
      have hev_target : ∀ᶠ t in 𝓝 (0 : 𝕜),
          ψ.symm (Function.update (ψ (φ (T.pushforwardIncl hS i.succ q'))) (cidx ⟨_, hxE⟩) t) ∈
            φ.target :=
        hlim0 (φ.open_target.mem_nhds (φ.map_source hc.2.1))
      have hy_lim : Tendsto (fun t : 𝕜 => φ.symm
          (ψ.symm (Function.update (ψ (φ (T.pushforwardIncl hS i.succ q'))) (cidx ⟨_, hxE⟩) t)))
          (𝓝[≠] 0) (𝓝 (T.pushforwardIncl hS i.succ q')) := by
        have h1 : Tendsto φ.symm (𝓝 (φ (T.pushforwardIncl hS i.succ q')))
            (𝓝 (T.pushforwardIncl hS i.succ q')) := by
          have := φ.continuousAt_symm (φ.map_source hc.2.1)
          rwa [ContinuousAt, φ.left_inv hc.2.1] at this
        exact (h1.comp hlim0).mono_left nhdsWithin_le_nhds
      have : (𝓝[≠] (0 : 𝕜)).NeBot := NormedField.nhdsNE_neBot 0
      refine mem_closure_of_tendsto hy_lim ?_
      filter_upwards [hev_target.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
      have ht0' : t ≠ 0 := fun h => ht0 (by rw [h]; exact Set.mem_singleton 0)
      have hyt_src : φ.symm (ψ.symm (Function.update (ψ (φ (T.pushforwardIncl hS i.succ q')))
          (cidx ⟨_, hxE⟩) t)) ∈ φ.source := φ.map_target ht
      have hyt_coord : ψ (φ (φ.symm (ψ.symm (Function.update
          (ψ (φ (T.pushforwardIncl hS i.succ q'))) (cidx ⟨_, hxE⟩) t)))) =
          Function.update (ψ (φ (T.pushforwardIncl hS i.succ q'))) (cidx ⟨_, hxE⟩) t := by
        rw [φ.right_inv ht, ψ.apply_symm_apply]
      -- `y t` lies on the strict transform `S_{i+1}`
      have hytS : φ.symm (ψ.symm (Function.update (ψ (φ (T.pushforwardIncl hS i.succ q')))
          (cidx ⟨_, hxE⟩) t)) ∈ (T.pushforward hS).strictTransformSeq S i.succ := by
        refine (hφ.2 _ hyt_src).mpr fun l => ?_
        rw [hyt_coord, Function.update_of_ne (fun h => hproper ⟨_, hxE⟩ ⟨l, h⟩)]
        exact (hφ.2 _ hc.2.1).mp hxS l
      -- `y t` lies on the strict transform of the member
      have hytA : φ.symm (ψ.symm (Function.update (ψ (φ (T.pushforwardIncl hS i.succ q')))
          (cidx ⟨_, hxE⟩) t)) ∈
          ((T.pushforward hS).totalTransformSeq i.succ).hyp (toLex (Sum.inl k₀)) := by
        refine (hc.mem_iff ⟨_, hxA⟩ hyt_src).mpr ?_
        rw [hyt_coord, Function.update_of_ne hcd]
        exact (hc.mem_iff ⟨_, hxA⟩ hc.2.1).mp hxA
      -- `y t` is off the exceptional divisor
      have hytE : φ.symm (ψ.symm (Function.update (ψ (φ (T.pushforwardIncl hS i.succ q')))
          (cidx ⟨_, hxE⟩) t)) ∉
          ((T.pushforward hS).totalTransformSeq i.succ).hyp (toLex (Sum.inr PUnit.unit)) := by
        intro h
        have h' := (hc.mem_iff ⟨_, hxE⟩ hyt_src).mp h
        rw [hyt_coord, Function.update_self] at h'
        exact ht0' h'
      refine ⟨⟨(mem_strictTransformSet_iff_of_notMem hπc hA hytE).mp hytA, hytE⟩, ?_⟩
      rw [T.range_pushforwardIncl hS i.succ]
      exact hytS
    · -- off the centre: `x` itself lies in the set
      apply subset_closure
      exact ⟨⟨(mem_strictTransformSet_iff_of_notMem hπc hA hxZ).mp hq', hxZ⟩, ⟨q', rfl⟩⟩
  · intro q' hq'
    have h1 : (T.pushforwardIncl hS i.succ) '' closure (⇑(T.map i) ⁻¹' (B \ (T.center i).support)) ⊆
        closure ((T.pushforwardIncl hS i.succ) '' (⇑(T.map i) ⁻¹' (B \ (T.center i).support))) :=
      image_closure_subset_closure_image hj.continuous
    refine closure_mono ?_ (h1 ⟨q', hq', rfl⟩)
    rw [← hdiff]
    exact Set.image_preimage_subset _ _

/-- **The boundary family of the push-forward traces, member by member and in order, to the
boundary family of the given sequence** ([Kol07, Definitions 30.2–30.3]): an order isomorphism `o`
of the last-stage index types (`OrderIso.sumLexCongr` on the `⊕ₗ PUnit` towers) with
`j_i⁻¹(H^X_{i, o j}) = H_{i, j}` at every stage, under the normal-crossings clause (3′) of
[Kol07, Definition 66] for the push-forward (the input of
`hasSncWithProper_totalTransformSeq_strictTransformSeq` in its prefix-bounded form). Induction on
the stage: the new member by `preimage_pushforwardIncl_preimage_center`, an old member by
`preimage_pushforwardIncl_strictTransformSet`. -/
theorem exists_orderIso_totalTransformSeq_pushforward
    (h3 : ∀ i : Fin T.length, ((T.pushforward hS).boundarySeq (⊤)
      i.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i))
    (i : Fin (T.length + 1)) :
    ∃ o : (T.totalTransformSeq i).ι ≃o ((T.pushforward hS).totalTransformSeq i).ι,
      ∀ j, ⇑(T.pushforwardIncl hS i) ⁻¹' ((T.pushforward hS).totalTransformSeq i).hyp (o j) =
        (T.totalTransformSeq i).hyp j := by
  induction i using Fin.induction with
  | zero => exact ⟨OrderIso.refl _, fun j => PEmpty.elim j⟩
  | succ i ih =>
    obtain ⟨o, ho⟩ := ih
    have hsnc₀ : ((T.pushforward hS).totalTransformSeq i.castSucc).IsSnc ψ :=
      isSnc_totalTransformSeq_of_forall_lt (S := T.pushforward hS) i.castSucc fun i' _ => h3 i'
    have hprop : ((T.pushforward hS).totalTransformSeq i.succ).HasSncWithProper ψ
        ((T.pushforward hS).strictTransformSeq S i.succ) s :=
      (T.pushforward hS).hasSncWithProper_totalTransformSeq_strictTransformSeq_of_forall_lt hS
        (T.centersIn_pushforward hS) i.succ fun i' _ => h3 i'
    refine ⟨OrderIso.sumLexCongr o (OrderIso.refl PUnit), fun j => ?_⟩
    obtain j₀ | u := j
    · exact T.preimage_pushforwardIncl_strictTransformSet hS i hsnc₀ hprop (o j₀) (ho j₀)
    · exact T.preimage_pushforwardIncl_preimage_center hS i

end AnalyticManifold.FiniteSuccession

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}

/-- **The ideal sheaf of a member of a family having simple normal crossings with the closed
submanifold `S` PROPERLY, pulled back along the inclusion of `S`, is the ideal sheaf of its trace**
(the boundary `E_i ∩ S_i` of [Kol07, Definition 30.2] at the level of ideals) — the counterpart of
`idealSheaf_preimageVal_eq_pullback` (`GermRestrict.lean`) for a TRANSVERSE hypersurface.
Stalkwise: on the trace, the member is `{y_c = 0}` in the proper chart
with `c` off the `S`-block (`ker_restrictStalk_eq_span` at the `singleEmb` adapted chart), the
trace is `{y_c|_S = 0}` in the induced chart (`isSncChartAt_inducedChart`), and the coordinate germ
`y_c` restricts along the inclusion to the induced coordinate (`germMap_germ`, `germ_ext`); off the
trace both stalks are the unit ideal. -/
theorem IsClosedSubmanifold.pullback_idealSheaf_inclusionMap_of_hasSncWithProper
    (hS : IsClosedSubmanifold ψ S s) {F : HypersurfaceFamily M} (hF : F.IsSnc ψ)
    (hFS : F.HasSncWithProper ψ S s) (j : F.ι) :
    (hF.1 j).idealSheaf.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff =
      ((hS.isSnc_traceFamily hF hFS).1 j).idealSheaf := by
  refine IdealSheaf.ext fun p => ?_
  rw [IdealSheaf.stalkIdeal_pullback]
  by_cases hp : p ∈ hS.preimageVal (F.hyp j)
  · have hpj : hS.inclusionMap p ∈ F.hyp j := hp
    obtain ⟨φ, σ, cidx, hφS, hc, hproper⟩ := hFS (hS.inclusionMap p) (p : S).2
    -- the member is `{y_c = 0}` in the proper chart, `c` off the `S`-block
    have hadH : IsAdaptedChart ψ (F.hyp j) φ (singleEmb (cidx ⟨j, hpj⟩)) :=
      isAdaptedChart_singleIdx hc.1 fun x hx => hc.mem_iff ⟨j, hpj⟩ hx
    -- the trace is `{y_c|_S = 0}` in the induced chart
    have hct := hS.isSncChartAt_inducedChart hφS (b := p) hc hproper
    have hpsrc : p ∈ (hS.inducedChart hφS (p : S).2).source :=
      (hS.mem_inducedChart_source hφS _ p).mpr hc.2.1
    have hadT : IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
        (hS.preimageVal (F.hyp j)) (hS.inducedChart hφS (p : S).2)
        (singleEmb (complEquiv σ ⟨cidx ⟨j, hpj⟩, hproper _⟩)) :=
      isAdaptedChart_singleIdx hct.1 fun x hx => hct.mem_iff ⟨j, hpj⟩ hx
    rw [(hF.1 j).stalkIdeal_idealSheaf_of_mem hpj,
      (hF.1 j).ker_restrictStalk_eq_span hpj hadH hc.2.1,
      ((hS.isSnc_traceFamily hF hFS).1 j).stalkIdeal_idealSheaf_of_mem hp,
      ((hS.isSnc_traceFamily hF hFS).1 j).ker_restrictStalk_eq_span hp hadT hpsrc,
      Ideal.map_span, Set.range_unique, Set.range_unique, Set.image_singleton]
    refine congrArg (fun x => Ideal.span {x}) ?_
    -- the coordinate germ `y_c` restricts along the inclusion to the induced coordinate
    change germMap ⇑hS.inclusionMap hS.inclusionMap.contMDiff p
        ((structureSheaf 𝕜 E M).presheaf.germ ⟨φ.source, φ.open_source⟩ (hS.inclusionMap p)
          hc.2.1 (chartSection E ψ φ hadH.1 (cidx ⟨j, hpj⟩))) =
      (structureSheaf 𝕜 (Fin (n - s) → 𝕜) hS.toAnalyticManifold).presheaf.germ
        ⟨(hS.inducedChart hφS (p : S).2).source, (hS.inducedChart hφS (p : S).2).open_source⟩ p
        hpsrc (chartSection (Fin (n - s) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
          (hS.inducedChart hφS (p : S).2) hadT.1 (complEquiv σ ⟨cidx ⟨j, hpj⟩, hproper _⟩))
    rw [germMap_germ]
    have hle : (⟨(hS.inducedChart hφS (p : S).2).source,
        (hS.inducedChart hφS (p : S).2).open_source⟩ : Opens hS.toAnalyticManifold) ≤
        preimageOpens ⇑hS.inclusionMap hS.inclusionMap.contMDiff
          ⟨φ.source, φ.open_source⟩ :=
      fun x hx => (mem_preimageOpens ⇑hS.inclusionMap
        hS.inclusionMap.contMDiff).mpr ((hS.mem_inducedChart_source hφS (p : S).2 x).mp hx)
    refine TopCat.Presheaf.germ_ext
      (structureSheaf 𝕜 (Fin (n - s) → 𝕜) hS.toAnalyticManifold).presheaf
      ⟨(hS.inducedChart hφS (p : S).2).source, (hS.inducedChart hφS (p : S).2).open_source⟩ hpsrc
      (homOfLE hle : (⟨(hS.inducedChart hφS (p : S).2).source,
          (hS.inducedChart hφS (p : S).2).open_source⟩ : Opens hS.toAnalyticManifold) ⟶
        preimageOpens ⇑hS.inclusionMap hS.inclusionMap.contMDiff
          ⟨φ.source, φ.open_source⟩)
      (homOfLE le_rfl : (⟨(hS.inducedChart hφS (p : S).2).source,
          (hS.inducedChart hφS (p : S).2).open_source⟩ : Opens hS.toAnalyticManifold) ⟶
        ⟨(hS.inducedChart hφS (p : S).2).source, (hS.inducedChart hφS (p : S).2).open_source⟩) ?_
    refine Subtype.ext (funext fun z => ?_)
    have hk : ((complEquiv σ).symm (complEquiv σ ⟨cidx ⟨j, hpj⟩, hproper _⟩)).1 = cidx ⟨j, hpj⟩ :=
      congrArg Subtype.val (Equiv.symm_apply_apply _ _)
    change comapSection ⇑hS.inclusionMap hS.inclusionMap.contMDiff
        (chartSection E ψ φ hadH.1 (cidx ⟨j, hpj⟩)) ⟨(z : hS.toAnalyticManifold), hle z.2⟩ =
      ψ (φ ((z : hS.toAnalyticManifold) : S).1)
        ((complEquiv σ).symm (complEquiv σ ⟨cidx ⟨j, hpj⟩, hproper _⟩)).1
    rw [comapSection_apply, hk]
    rfl
  · have hpj : hS.inclusionMap p ∉ F.hyp j := hp
    rw [(hF.1 j).stalkIdeal_idealSheaf_of_notMem hpj, Ideal.map_top,
      ((hS.isSnc_traceFamily hF hFS).1 j).stalkIdeal_idealSheaf_of_notMem hp]

end Manifold

end
