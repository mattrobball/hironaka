/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseTools
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Resolution.Analytic.GoingUp.Corollary85
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.GoingUp.PushforwardTransform
import Hironaka.Resolution.Analytic.GoingUp.StageIso
import Hironaka.Resolution.Analytic.MaximalContactTheorem
import Hironaka.Resolution.Analytic.OrderReduction.BDCosupp
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseBridge
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StopPersistence
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StopRestrict
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Hironaka.Resolution.Analytic.Restrict.BoundaryTrace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial


/-!
# The two stop clauses along a push-forward from a hypersurface of maximal contact

Kollár's going-up theorem, [Kol07, Corollary 85], transports the order clause of a blow-up sequence
on a hypersurface `S` of maximal contact to its push-forward
(`pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily`). The modified core of the modified first
step is such a push-forward (the run of the functor one dimension down on the trace of the triple
to `H⁺`, `coreModOn`), and the output clause and the stopped clause of `ClauseTools.lean` have to
be transported the same way. This module is that transport, for a general push-forward
`FiniteSuccession.pushforward` along a closed hypersurface `S`, given a hypersurface `H` of maximal
contact (`𝓘_H ≤ J`) of which `S` is a clopen piece. The maximal contact of `H⁺` itself fails where
stopped components remain, so it is the maximal contact of `H` that is used, localised to `S`.

* `isClosed_strictTransformSeq_diff` (with `strictTransformSeq_mono`): a clopen piece `S ⊆ H`
  stays clopen in the strict transforms along a succession whose centres lie in the strict
  transforms of `S` (the strict transform of `H` at every stage is the strict transform of `S`
  together with the closed set of points over the stopped piece `H ∖ S`).
* `eventually_stalkIdeal_idealSheaf_le_of_isClosed_diff`: the maximal contact of the piece near
  each of its points, and at each point, from the global maximal contact of `H` (the hypotheses of
  `restrict_maximalContact_of_stalkIdeal_le` and `of_restrict_maximalContact_of_eventually_le` of
  `StopRestrict.lean`; off `H` both sides read `J_x = ⊤`).
* `notMem_strictTransformSeq_of_stageMapAdd`: a point off the strict transform stays off it along
  its fibre (`strictTransformSeq_succ_subset_preimage`); `pushforwardIncl_stageMapAdd`: the squares
  of the push-forward iterated along the composite blow-downs.
* `support_totalTransformSeqFrom_traceFamily_eq_preimage`: the support of the boundary of the lower
  run is the trace of the ambient boundary's (`E_i ∩ S_i`, [Kol07, Definition 30, 30.2]), through
  the identification at the level of reduced ideal sheaves
  (`isSnc_totalTransformSeqFrom_and_boundarySeq_eq`, `boundarySeq_pushforwardStageIso`,
  `support_traceFamilyFrom_eq_support_boundarySeq`).
* `isSmoothTransversalIdealAt_pullback_pushforwardIncl`,
  `isSmoothTransversalIdealAt_of_pullback_pushforwardIncl`: the predicate descends to and lifts
  from the lower stage, by the descent and lift of `StopRestrict.lean` at the strict transform of
  `S`, the stage isomorphism `pushforwardStageIso`, `markedTransformSeq_pullback_pushforwardIncl`
  for the ideal, and `IsSmoothTransversalIdealAt.of_support_eq_nhds` for the boundary.
* `StoppedClause.pushforward`: the stopped clause along the push-forward. A predicate point off the
  boundary is off the strict transform of `S` (no centre reaches its fibre), or of order `0`
  (`notMem_center_of_ord_eq_zero`), or the image of a lower predicate point, whose fibre the lower
  clause keeps off the lower centres.
* `OutputClause.pushforward_of_mem_strictTransformSeq`: the output clause along the push-forward at
  the points of the strict transform of `S`; the stopped piece is treated by
  `OutputClause.pushforward` in `ClausePhaseBCore.lean`.

The sources are [Kol07, Corollary 85], [Kol07, Definition 30, 30.2–30.3] and the modified first
step of [Wlo09, Theorem 7.4.1]; the statements themselves are not in the sources.
-/

public section


noncomputable section

open Set Topology TopologicalSpace Hironaka.Manifold Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

section Generic

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- **A clopen piece stays clopen along a succession with centres inside it**: for `S ⊆ H` closed
with `H \ S` closed and every centre inside the strict transform of `S`, the strict transform of
`H` at every stage is the strict transform of `S` together with the (closed) preimage of `H \ S`,
disjoint from it. The strict transform of a union is the union, and that of a set the centre misses
is its preimage (`strictTransformSeq_succ`, `strictTransformSeq_succ_subset_preimage`,
`strictTransformSeq_mono`). -/
theorem isClosed_strictTransformSeq_diff (B : FiniteSuccession M) {S H : Set M} (hSc : IsClosed S)
    (hSH : S ⊆ H) (hcl : IsClosed (H \ S)) (hc : B.CentersIn S) (i : Fin (B.length + 1)) :
    IsClosed (B.strictTransformSeq H i \ B.strictTransformSeq S i) := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact hcl
  | succ i ih =>
    have hi' : i < B.length + 1 := Nat.lt_of_succ_lt hi
    have hi'' : i < B.length := Nat.lt_of_succ_lt_succ hi
    set A := B.strictTransformSeq H ⟨i, hi'⟩ with hA
    set Si := B.strictTransformSeq S ⟨i, hi'⟩ with hSi
    set C := (B.center ⟨i, hi''⟩).support with hC
    set π := B.map ⟨i, hi''⟩ with hπ
    have hD : IsClosed (A \ Si) := ih hi'
    have hSiA : Si ⊆ A := B.strictTransformSeq_mono hSH _
    have hCS : C ⊆ Si := hc ⟨i, hi''⟩
    have hunion : A \ C = (Si \ C) ∪ (A \ Si) := by
      ext a
      constructor
      · rintro ⟨haA, haC⟩
        by_cases haS : a ∈ Si
        · exact Or.inl ⟨haS, haC⟩
        · exact Or.inr ⟨haA, haS⟩
      · rintro (⟨haS, haC⟩ | ⟨haA, haS⟩)
        · exact ⟨hSiA haS, haC⟩
        · exact ⟨haA, fun haC => haS (hCS haC)⟩
    have e1 : B.strictTransformSeq H ⟨i + 1, hi⟩ = closure (π ⁻¹' (A \ C)) := rfl
    have e2 : B.strictTransformSeq S ⟨i + 1, hi⟩ = closure (π ⁻¹' (Si \ C)) := rfl
    have hpre : IsClosed (π ⁻¹' (A \ Si)) := hD.preimage π.contMDiff.continuous
    have hsub : B.strictTransformSeq S ⟨i + 1, hi⟩ ⊆ π ⁻¹' Si :=
      B.strictTransformSeq_succ_subset_preimage S hSc ⟨i, hi''⟩
    have heq : B.strictTransformSeq H ⟨i + 1, hi⟩ \ B.strictTransformSeq S ⟨i + 1, hi⟩ =
        π ⁻¹' (A \ Si) := by
      rw [e1, e2, hunion, Set.preimage_union, closure_union, hpre.closure_eq]
      ext z
      constructor
      · rintro ⟨hz1 | hz1, hz2⟩
        · exact absurd hz1 hz2
        · exact hz1
      · intro hz
        exact ⟨Or.inr hz, fun hzS => hz.2 (hsub hzS)⟩
    rw [heq]
    exact hpre

/-- **The maximal contact of the clopen piece near each of its points**: for `S ⊆ H` closed
hypersurfaces with `H \ S` closed and `𝓘_H ≤ J`, at every point `y ∈ S` the stalks of `𝓘_S` and
`𝓘_H` agree on the open `(H \ S)ᶜ ∋ y` (the vanishing ideal depends on the germ of the set,
`vanishingStalk_inter_of_mem_nhds`), and off `H` both read `J_x = ⊤`; so `𝓘_S ≤ J` holds stalkwise
on a neighbourhood of `y`, which is the hypothesis of `of_restrict_maximalContact_of_eventually_le`,
and at `y` that of `restrict_maximalContact_of_stalkIdeal_le`. -/
theorem eventually_stalkIdeal_idealSheaf_le_of_isClosed_diff {S H : Set M}
    (hS : IsClosedSubmanifold ψ S 1) (hH : IsClosedSubmanifold ψ H 1) (hSH : S ⊆ H)
    (hcl : IsClosed (H \ S)) {J : IdealSheaf M} (hle : hH.idealSheaf ≤ J) {y : M} (hy : y ∈ S) :
    ∀ᶠ x in 𝓝 y, hS.idealSheaf.stalkIdeal x ≤ J.stalkIdeal x := by
  have hN : (H \ S)ᶜ ∈ 𝓝 y := hcl.isOpen_compl.mem_nhds fun h => h.2 hy
  filter_upwards [hN] with x hx
  by_cases hxS : x ∈ S
  · have h1 : hS.idealSheaf.stalkIdeal x = hH.idealSheaf.stalkIdeal x := by
      rw [hS.stalkIdeal_idealSheaf_eq_vanishingStalk, hH.stalkIdeal_idealSheaf_eq_vanishingStalk]
      have hSN : S = H ∩ (H \ S)ᶜ := by
        ext a
        constructor
        · intro ha
          exact ⟨hSH ha, fun h => h.2 ha⟩
        · rintro ⟨haH, haN⟩
          by_contra haS
          exact haN ⟨haH, haS⟩
      conv_lhs => rw [hSN]
      exact vanishingStalk_inter_of_mem_nhds (hcl.isOpen_compl.mem_nhds hx)
    rw [h1]
    exact IdealSheaf.le_def.mp hle x
  · have hxH : x ∉ H := fun hxH => hx ⟨hxH, hxS⟩
    rw [hS.stalkIdeal_idealSheaf_of_notMem hxS]
    have := IdealSheaf.le_def.mp hle x
    rw [hH.stalkIdeal_idealSheaf_of_notMem hxH] at this
    exact this

/-- **A point off the strict transform stays off it along its fibre**: the strict transform of a
closed set at a stage lies in the preimage of the strict transform at the stage before
(`strictTransformSeq_succ_subset_preimage`), iterated along `stageMapAdd`. -/
theorem notMem_strictTransformSeq_of_stageMapAdd (B : FiniteSuccession M) {S : Set M}
    (hSc : IsClosed S) (i k : ℕ) (h : i + k < B.length + 1)
    {x : B.stage ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩}
    (hx : x ∉ B.strictTransformSeq S ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩)
    (y : B.stage ⟨i + k, h⟩) (hy : B.stageMapAdd i k h y = x) :
    y ∉ B.strictTransformSeq S ⟨i + k, h⟩ := by
  have key : ∀ (k : ℕ) (h : i + k < B.length + 1) (y : B.stage ⟨i + k, h⟩),
      B.stageMapAdd i k h y = x → y ∉ B.strictTransformSeq S ⟨i + k, h⟩ := by
    intro k
    induction k with
    | zero =>
      intro h y hy
      have hyx : y = x := hy
      subst hyx
      exact hx
    | succ k ih =>
      intro h y hy hmem
      have hk : i + k < B.length + 1 := Nat.lt_of_succ_lt h
      have hk' : i + k < B.length := Nat.lt_of_succ_lt_succ h
      have hzx : B.stageMapAdd i k hk (B.map ⟨i + k, hk'⟩ y) = x := hy
      exact ih hk _ hzx (B.strictTransformSeq_succ_subset_preimage S hSc ⟨i + k, hk'⟩ hmem)
  exact key k h y hy

end Generic

section Pushforward

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {S : Set M} (hS : IsClosedSubmanifold ψ S 1) (T : FiniteSuccession hS.toAnalyticManifold)

omit [FiniteDimensional 𝕜 E] in
/-- The inclusions of the stages commute with the composite blow-downs (the squares
`pushforwardIncl_map` iterated along `stageMapAdd`). -/
theorem pushforwardIncl_stageMapAdd (i k : ℕ) (h : i + k < T.length + 1) (y : T.stage ⟨i + k, h⟩) :
    T.pushforwardIncl hS ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩ (T.stageMapAdd i k h y) =
      (T.pushforward hS).stageMapAdd i k h (T.pushforwardIncl hS ⟨i + k, h⟩ y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : i + k < T.length + 1 := Nat.lt_of_succ_lt h
    have hk' : i + k < T.length := Nat.lt_of_succ_lt_succ h
    have e1 : T.stageMapAdd i (k + 1) h y = T.stageMapAdd i k hk (T.map ⟨i + k, hk'⟩ y) := rfl
    have e2 : (T.pushforward hS).stageMapAdd i (k + 1) h (T.pushforwardIncl hS ⟨i + (k + 1), h⟩ y) =
        (T.pushforward hS).stageMapAdd i k hk
          ((T.pushforward hS).map ⟨i + k, hk'⟩ (T.pushforwardIncl hS ⟨i + (k + 1), h⟩ y)) := rfl
    have e3 : T.pushforwardIncl hS ⟨i + k, hk⟩ (T.map ⟨i + k, hk'⟩ y) =
        (T.pushforward hS).map ⟨i + k, hk'⟩ (T.pushforwardIncl hS ⟨i + (k + 1), h⟩ y) :=
      T.pushforwardIncl_map hS ⟨i + k, hk'⟩ y
    rw [e1, e2, ih hk (T.map ⟨i + k, hk'⟩ y), e3]

omit [FiniteDimensional 𝕜 E] in
/-- The stage of the lower sequence is diffeomorphic to the bundled strict transform of `S` through
the inclusion of the stage (`pushforwardStageIso`, carried across the identity of sets
`range (pushforwardIncl i) = strictTransformSeq S i` by `IsClosedSubmanifold.diffeomorphOfEq`). -/
theorem exists_diffeomorph_inclusionMap_pushforwardIncl (i : Fin (T.length + 1))
    (hSi : IsClosedSubmanifold ψ ((T.pushforward hS).strictTransformSeq S i) 1) :
    ∃ e : Diffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) (T.stage i)
        hSi.toAnalyticManifold ω,
      ∀ x', hSi.inclusionMap (e x') = T.pushforwardIncl hS i x' := by
  obtain ⟨k, hk⟩ := i
  cases k with
  | zero =>
    have hset : (T.pushforwardAux hS 0 hk).sub = (T.pushforward hS).strictTransformSeq S ⟨0, hk⟩ :=
      ((T.pushforwardAux hS 0 hk).range_incl).symm.trans (T.range_pushforwardIncl hS ⟨0, hk⟩)
    refine ⟨(T.pushforwardAux hS 0 hk).iso.trans
      ((T.pushforwardAux hS 0 hk).isClosedSubmanifold.diffeomorphOfEq hSi hset), fun x' => ?_⟩
    exact IsClosedSubmanifold.diffeomorphOfEq_apply_val _ _ hset ((T.pushforwardAux hS 0 hk).iso x')
  | succ k =>
    have hset : (T.pushforwardAux hS (k + 1) hk).sub =
        (T.pushforward hS).strictTransformSeq S ⟨k + 1, hk⟩ :=
      ((T.pushforwardAux hS (k + 1) hk).range_incl).symm.trans
        (T.range_pushforwardIncl hS ⟨k + 1, hk⟩)
    refine ⟨(T.pushforwardAux hS (k + 1) hk).iso.trans
      ((T.pushforwardAux hS (k + 1) hk).isClosedSubmanifold.diffeomorphOfEq hSi hset),
      fun x' => ?_⟩
    exact IsClosedSubmanifold.diffeomorphOfEq_apply_val _ _ hset
      ((T.pushforwardAux hS (k + 1) hk).iso x')

variable {J : IdealSheaf M} {F : HypersurfaceFamily M}

/-- **The support of the boundary of the lower run is the trace of the ambient boundary's** (the
`E_i ∩ S_i` of [Kol07, Definition 30, 30.2] at the level of supports): the lower boundary's support
is that of its reduced ideal sheaf (`isSnc_totalTransformSeqFrom_and_boundarySeq_eq`), which pulls
back along the stage isomorphism from the boundary of `Π|_S` (`boundarySeq_pushforwardStageIso`),
whose support is the trace of the ambient boundary's
(`support_traceFamilyFrom_eq_support_boundarySeq`, `support_traceFamilyFrom`). -/
theorem support_totalTransformSeqFrom_traceFamily_eq_preimage (hF : F.IsSnc ψ)
    (hFS : F.HasSncWithProper ψ S 1) (hmax : ∀ y, J.ord y ≤ 1)
    (hT : T.IsOfOrderGe (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) 1
      ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)))
    (i : Fin (T.length + 1)) :
    (T.totalTransformSeqFrom (hS.traceFamily F) i).support =
      ⇑(T.pushforwardIncl hS i) ⁻¹' ((T.pushforward hS).totalTransformSeqFrom F i).support := by
  have hge : (T.pushforward hS).IsOfOrderGe J 1 (F.idealSheaf (𝕜 := 𝕜) (E := E)) :=
    T.pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily hS J.isDBalanced_one hmax hF hFS hT
  have h3 : ∀ i' : Fin (T.pushforward hS).length, i'.1 < i.1 →
      ((T.pushforward hS).boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E))
        i'.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i') :=
    fun i' _ => hge.hasOnlyNormalCrossingsWith i'
  have hTsnc := T.isSnc_totalTransformSeqFrom_and_boundarySeq_eq
    (ψ := ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) (hS.isSnc_traceFamily hF hFS)
    (fun j => hT.hasOnlyNormalCrossingsWith j) i
  -- the lower boundary's support is the cosupport of the boundary ideal of `T`, pulled back from
  -- the boundary of `Π|_S` along the stage isomorphism
  rw [← hTsnc.1.cosupport_idealSheaf, ← hTsnc.2, ← T.boundarySeq_pushforwardStageIso hS i,
    IdealSheaf.support_pullback]
  have htr := (T.pushforward hS).support_traceFamilyFrom_eq_support_boundarySeq hS
    (T.centersIn_pushforward hS) hF hFS i h3
  have htr' := (T.pushforward hS).support_traceFamilyFrom hS (T.centersIn_pushforward hS) F i
  change ⇑(T.pushforwardStageIso hS i) ⁻¹'
    (((T.pushforward hS).restrictSubmanifold hS (T.centersIn_pushforward hS)).boundarySeq
      ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)) i).support = _
  rw [← htr, htr', ← Set.preimage_comp]
  congr 1
  funext x'
  exact T.restrictIncl_pushforwardStageIso hS i x'

/-- **The predicate descends from the ambient stage to the lower stage**:
`restrict_maximalContact_of_stalkIdeal_le` on the ambient stage at the strict transform `S_i`, with
the maximal contact at the point `hle`, transported along the stage isomorphism
`pushforwardStageIso` (`IsSmoothTransversalIdealAt.comap`, `restrictIncl_pushforwardStageIso`); the
ideal is the lower marked transform by `markedTransformSeq_pullback_pushforwardIncl`; the boundary
by `IsSmoothTransversalIdealAt.of_support_eq_nhds` with
`support_totalTransformSeqFrom_traceFamily_eq_preimage`, both families having simple normal
crossings (`isSnc_traceFamilyFrom`, `isSnc_comap`,
`isSnc_totalTransformSeqFrom_and_boundarySeq_eq`). -/
theorem isSmoothTransversalIdealAt_pullback_pushforwardIncl (hF : F.IsSnc ψ)
    (hFS : F.HasSncWithProper ψ S 1) (hmax : ∀ y, J.ord y ≤ 1)
    (hT : T.IsOfOrderGe (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) 1
      ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)))
    (i : Fin (T.length + 1)) {x' : T.stage i}
    (hSi : IsClosedSubmanifold ψ ((T.pushforward hS).strictTransformSeq S i) 1)
    (hle : hSi.idealSheaf.stalkIdeal (T.pushforwardIncl hS i x') ≤
      ((T.pushforward hS).markedTransformSeq J 1 i).stalkIdeal (T.pushforwardIncl hS i x'))
    (hJ : ((T.pushforward hS).markedTransformSeq J 1 i).stalkIdeal (T.pushforwardIncl hS i x') ≠ ⊤)
    (h : ((T.pushforward hS).totalTransformSeqFrom F i).IsSmoothTransversalIdealAt ψ
      ((T.pushforward hS).markedTransformSeq J 1 i) (T.pushforwardIncl hS i x')) :
    (T.totalTransformSeqFrom (hS.traceFamily F) i).IsSmoothTransversalIdealAt
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (T.markedTransformSeq (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) 1 i) x' := by
  obtain ⟨e, he⟩ := T.exists_diffeomorph_inclusionMap_pushforwardIncl hS i hSi
  have hge : (T.pushforward hS).IsOfOrderGe J 1 (F.idealSheaf (𝕜 := 𝕜) (E := E)) :=
    T.pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily hS J.isDBalanced_one hmax hF hFS hT
  have h3 : ∀ i' : Fin (T.pushforward hS).length, i'.1 < i.1 →
      ((T.pushforward hS).boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E))
        i'.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i') :=
    fun i' _ => hge.hasOnlyNormalCrossingsWith i'
  -- the ambient boundary at stage `i` has simple normal crossings and proper normal crossings
  -- with `S_i`
  have hGsnc : ((T.pushforward hS).totalTransformSeqFrom F i).IsSnc ψ :=
    ((T.pushforward hS).isSnc_totalTransformSeqFrom_and_boundarySeq_eq hF
      (fun j => hge.hasOnlyNormalCrossingsWith j) i).1
  have hprop : ((T.pushforward hS).totalTransformSeqFrom F i).HasSncWithProper ψ
      ((T.pushforward hS).strictTransformSeq S i) 1 :=
    (T.pushforward hS).hasSncWithProper_totalTransformSeqFrom_strictTransformSeq_of_forall_lt hS
      (T.centersIn_pushforward hS) hF hFS i h3
  -- the descent of the predicate on the ambient stage at `S_i`
  have hmem : T.pushforwardIncl hS i x' ∈ (T.pushforward hS).strictTransformSeq S i := by
    rw [← T.range_pushforwardIncl hS i]
    exact ⟨x', rfl⟩
  have h1 := HypersurfaceFamily.IsSmoothTransversalIdealAt.restrict_maximalContact_of_stalkIdeal_le
    ψ hSi hle hmem hJ h
  -- the point `⟨incl x', _⟩` of the bundled `S_i` is `e x'`
  have hex : (⟨T.pushforwardIncl hS i x', hmem⟩ : hSi.toAnalyticManifold) = e x' :=
    Subtype.ext (he x').symm
  rw [hex] at h1
  have h2 := HypersurfaceFamily.IsSmoothTransversalIdealAt.comap
    (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) _ _ ⟨e, e.contMDiff⟩
    (e.isLocalDiffeomorph x') h1
  -- the ideal is the lower marked transform (`markedTransformSeq_pullback_pushforwardIncl`)
  have hideal : (((T.pushforward hS).markedTransformSeq J 1 i).pullback ⇑hSi.inclusionMap
        hSi.inclusionMap.contMDiff).pullback e e.contMDiff =
      T.markedTransformSeq (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) 1 i := by
    rw [← T.markedTransformSeq_pullback_pushforwardIncl hS J hge i]
    rw [IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr _ _ _ (funext he)
  erw [hideal] at h2
  -- the boundary: both families have simple normal crossings, with the same support
  have hsnc₁ : ((hSi.traceFamily ((T.pushforward hS).totalTransformSeqFrom F i)).comap ⇑e).IsSnc
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) :=
    HypersurfaceFamily.isSnc_comap (hSi.isSnc_traceFamily hGsnc hprop) ⟨e, e.contMDiff⟩
      e.isLocalDiffeomorph
  have hsnc₂ : (T.totalTransformSeqFrom (hS.traceFamily F) i).IsSnc
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) :=
    (T.isSnc_totalTransformSeqFrom_and_boundarySeq_eq (hS.isSnc_traceFamily hF hFS)
      (fun j => hT.hasOnlyNormalCrossingsWith j) i).1
  have hsupp : ((hSi.traceFamily ((T.pushforward hS).totalTransformSeqFrom F i)).comap ⇑e).support ∩
        Set.univ = (T.totalTransformSeqFrom (hS.traceFamily F) i).support ∩ Set.univ := by
    rw [Set.inter_univ, Set.inter_univ, HypersurfaceFamily.support_comap, hSi.traceFamily_support,
      T.support_totalTransformSeqFrom_traceFamily_eq_preimage hS hF hFS hmax hT i]
    ext x''
    have hval : hSi.inclusionMap (e x'') = T.pushforwardIncl hS i x'' := he x''
    change hSi.inclusionMap (e x'') ∈ ((T.pushforward hS).totalTransformSeqFrom F i).support ↔
      T.pushforwardIncl hS i x'' ∈ ((T.pushforward hS).totalTransformSeqFrom F i).support
    rw [hval]
  exact HypersurfaceFamily.IsSmoothTransversalIdealAt.of_support_eq_nhds hsnc₁ hsnc₂ isOpen_univ
    (Set.mem_univ x') hsupp h2

/-- **The predicate lifts from the lower stage to the ambient stage** (the converse of
`isSmoothTransversalIdealAt_pullback_pushforwardIncl`, for the output clause): the lower predicate
transported to the trace family (the stage isomorphism,
`IsSmoothTransversalIdealAt.of_support_eq_nhds` with
`support_totalTransformSeqFrom_traceFamily_eq_preimage`), then
`of_restrict_maximalContact_of_eventually_le` with the ambient boundary in proper normal crossings
with `S_i` (`hasSncWithProper_totalTransformSeqFrom_strictTransformSeq_of_forall_lt`) and the
maximal contact on a neighbourhood. -/
theorem isSmoothTransversalIdealAt_of_pullback_pushforwardIncl (hF : F.IsSnc ψ)
    (hFS : F.HasSncWithProper ψ S 1) (hmax : ∀ y, J.ord y ≤ 1)
    (hT : T.IsOfOrderGe (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) 1
      ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)))
    (i : Fin (T.length + 1)) {x' : T.stage i}
    (hSi : IsClosedSubmanifold ψ ((T.pushforward hS).strictTransformSeq S i) 1)
    (hle : ∀ᶠ x in 𝓝 (T.pushforwardIncl hS i x'),
      hSi.idealSheaf.stalkIdeal x ≤ ((T.pushforward hS).markedTransformSeq J 1 i).stalkIdeal x)
    (hJ : ((T.pushforward hS).markedTransformSeq J 1 i).stalkIdeal (T.pushforwardIncl hS i x') ≠ ⊤)
    (h : (T.totalTransformSeqFrom (hS.traceFamily F) i).IsSmoothTransversalIdealAt
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (T.markedTransformSeq (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) 1 i) x') :
    ((T.pushforward hS).totalTransformSeqFrom F i).IsSmoothTransversalIdealAt ψ
      ((T.pushforward hS).markedTransformSeq J 1 i) (T.pushforwardIncl hS i x') := by
  obtain ⟨e, he⟩ := T.exists_diffeomorph_inclusionMap_pushforwardIncl hS i hSi
  have hge : (T.pushforward hS).IsOfOrderGe J 1 (F.idealSheaf (𝕜 := 𝕜) (E := E)) :=
    T.pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily hS J.isDBalanced_one hmax hF hFS hT
  have h3 : ∀ i' : Fin (T.pushforward hS).length, i'.1 < i.1 →
      ((T.pushforward hS).boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E))
        i'.castSucc).HasOnlyNormalCrossingsWith ((T.pushforward hS).center i') :=
    fun i' _ => hge.hasOnlyNormalCrossingsWith i'
  have hGsnc : ((T.pushforward hS).totalTransformSeqFrom F i).IsSnc ψ :=
    ((T.pushforward hS).isSnc_totalTransformSeqFrom_and_boundarySeq_eq hF
      (fun j => hge.hasOnlyNormalCrossingsWith j) i).1
  have hprop : ((T.pushforward hS).totalTransformSeqFrom F i).HasSncWithProper ψ
      ((T.pushforward hS).strictTransformSeq S i) 1 :=
    (T.pushforward hS).hasSncWithProper_totalTransformSeqFrom_strictTransformSeq_of_forall_lt hS
      (T.centersIn_pushforward hS) hF hFS i h3
  have hmem : T.pushforwardIncl hS i x' ∈ (T.pushforward hS).strictTransformSeq S i := by
    rw [← T.range_pushforwardIncl hS i]
    exact ⟨x', rfl⟩
  -- the lower predicate, read for the trace family pulled back along `e` (the two families have
  -- the same support)
  have hsnc₁ : ((hSi.traceFamily ((T.pushforward hS).totalTransformSeqFrom F i)).comap ⇑e).IsSnc
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) :=
    HypersurfaceFamily.isSnc_comap (hSi.isSnc_traceFamily hGsnc hprop) ⟨e, e.contMDiff⟩
      e.isLocalDiffeomorph
  have hsnc₂ : (T.totalTransformSeqFrom (hS.traceFamily F) i).IsSnc
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) :=
    (T.isSnc_totalTransformSeqFrom_and_boundarySeq_eq (hS.isSnc_traceFamily hF hFS)
      (fun j => hT.hasOnlyNormalCrossingsWith j) i).1
  have hsupp : (T.totalTransformSeqFrom (hS.traceFamily F) i).support ∩ Set.univ =
      ((hSi.traceFamily ((T.pushforward hS).totalTransformSeqFrom F i)).comap ⇑e).support ∩
        Set.univ := by
    rw [Set.inter_univ, Set.inter_univ, HypersurfaceFamily.support_comap, hSi.traceFamily_support,
      T.support_totalTransformSeqFrom_traceFamily_eq_preimage hS hF hFS hmax hT i]
    ext x''
    have hval : hSi.inclusionMap (e x'') = T.pushforwardIncl hS i x'' := he x''
    change T.pushforwardIncl hS i x'' ∈ ((T.pushforward hS).totalTransformSeqFrom F i).support ↔
      hSi.inclusionMap (e x'') ∈ ((T.pushforward hS).totalTransformSeqFrom F i).support
    rw [hval]
  have hideal : (((T.pushforward hS).markedTransformSeq J 1 i).pullback ⇑hSi.inclusionMap
        hSi.inclusionMap.contMDiff).pullback e e.contMDiff =
      T.markedTransformSeq (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) 1 i := by
    rw [← T.markedTransformSeq_pullback_pushforwardIncl hS J hge i]
    rw [IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr _ _ _ (funext he)
  have h1 : ((hSi.traceFamily ((T.pushforward hS).totalTransformSeqFrom F i)).comap
      ⇑e).IsSmoothTransversalIdealAt (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      ((((T.pushforward hS).markedTransformSeq J 1 i).pullback ⇑hSi.inclusionMap
          hSi.inclusionMap.contMDiff).pullback e e.contMDiff) x'
              := by
    rw [hideal]
    exact HypersurfaceFamily.IsSmoothTransversalIdealAt.of_support_eq_nhds hsnc₂ hsnc₁ isOpen_univ
      (Set.mem_univ x') hsupp h
  -- transport to the bundled `S_i` at `e x' = ⟨incl x', _⟩`, then the lift of the predicate
  let g : AnalyticMap (T.stage i) hSi.toAnalyticManifold := ⟨e, e.contMDiff⟩
  have h2 := HypersurfaceFamily.IsSmoothTransversalIdealAt.of_comap
    (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) _ _ g (e.isLocalDiffeomorph x') h1
  have hex : g x' = (⟨T.pushforwardIncl hS i x', hmem⟩ : hSi.toAnalyticManifold) :=
    Subtype.ext (he x')
  rw [hex] at h2
  exact HypersurfaceFamily.IsSmoothTransversalIdealAt.of_restrict_maximalContact_of_eventually_le ψ
    hSi hprop hle hmem hJ h2

variable {H : Set M}

/-- **The stopped clause along a push-forward** ([Kol07, Corollary 85] for the stopped clause): the
push-forward of a sequence with the stopped clause for the trace triple has the stopped clause,
given a hypersurface `H` of maximal contact (`𝓘_H ≤ J`) of which `S` is a clopen piece. At a
predicate point `x` of a stage off the boundary: if `x ∉ S_i`, no centre reaches its fibre
(`notMem_strictTransformSeq_of_stageMapAdd`, `centersIn_pushforward`); if `x = incl x'` and
`ord 𝓘_i x = 0`, no centre reaches its fibre (`notMem_center_of_ord_eq_zero`); otherwise the
maximal contact of `S_i` at `x` (from that of `H`, `isClosed_strictTransformSeq_diff`,
`eventually_stalkIdeal_idealSheaf_le_of_isClosed_diff`) lets
`isSmoothTransversalIdealAt_pullback_pushforwardIncl` descend the predicate to `x'`, off the lower
boundary (`support_totalTransformSeqFrom_traceFamily_eq_preimage`), the lower clause keeps its fibre
off the lower centres, and a point of the ambient fibre is either off `S_{i+k}` (no centre) or the
image of a lower fibre point (`pushforwardIncl_stageMapAdd`, the injectivity of the inclusions,
`support_center_pushforward`). -/
theorem StoppedClause.pushforward (hF : F.IsSnc ψ) (hFS : F.HasSncWithProper ψ S 1)
    (hmax : ∀ y, J.ord y ≤ 1)
    (hT : T.IsOfOrderGe (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) 1
      ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)))
    (hH : IsClosedSubmanifold ψ H 1) (hSH : S ⊆ H) (hcl : IsClosed (H \ S))
    (hle : hH.idealSheaf ≤ J)
    (hP : T.StoppedClause (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (hS.traceFamily F)) :
    (T.pushforward hS).StoppedClause ψ J F := by
  have hge : (T.pushforward hS).IsOfOrderGe J 1 (F.idealSheaf (𝕜 := 𝕜) (E := E)) :=
    T.pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily hS J.isDBalanced_one hmax hF hFS hT
  have hordP : (T.pushforward hS).IsOfOrder J (F.idealSheaf (𝕜 := 𝕜) (E := E)) 1 :=
    isOfOrder_of_isOfOrderGe_of_ord_le (T.pushforward hS) hge hmax
  have hle' : hH.idealSheaf ≤ J.iteratedDeriv (1 - 1) := hle
  intro i k h x hPx hx y hy
  have hi : i < (T.pushforward hS).length + 1 :=
    Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) h)
  by_cases hxS : x ∈ (T.pushforward hS).strictTransformSeq S ⟨i, hi⟩
  · -- `x` lies on the strict transform of `S`: it is the image of a lower point `x'`
    have hxr : x ∈ Set.range (T.pushforwardIncl hS ⟨i, hi⟩) := by
      rw [T.range_pushforwardIncl hS ⟨i, hi⟩]
      exact hxS
    obtain ⟨x', rfl⟩ := hxr
    by_cases hord0 : ((T.pushforward hS).markedTransformSeq J 1 ⟨i, hi⟩).ord
        (T.pushforwardIncl hS ⟨i, hi⟩ x') = 0
    · -- the `⊤`-case: a point of order `0` is never blown up
      exact (T.pushforward hS).notMem_center_of_ord_eq_zero hge i k h hord0 y hy
    · -- the pointwise maximal contact of `S_i` from the global one of `H`
      have hSi : IsClosedSubmanifold ψ ((T.pushforward hS).strictTransformSeq S ⟨i, hi⟩) 1 :=
        (T.pushforward hS).isClosedSubmanifold_strictTransformSeq S hS
          (T.centersIn_pushforward hS) ⟨i, hi⟩
      have hHi : IsClosedSubmanifold ψ ((T.pushforward hS).strictTransformSeq H ⟨i, hi⟩) 1 :=
        hordP.isClosedSubmanifold_strictTransformSeq_of_le le_rfl hH hle' ⟨i, hi⟩
      have hleH : hHi.idealSheaf ≤ (T.pushforward hS).markedTransformSeq J 1 ⟨i, hi⟩ :=
        hordP.idealSheaf_strictTransformSeq_le_markedTransformSeq le_rfl hH hle' ⟨i, hi⟩ hHi
      have hcl' : IsClosed ((T.pushforward hS).strictTransformSeq H ⟨i, hi⟩ \
          (T.pushforward hS).strictTransformSeq S ⟨i, hi⟩) :=
        (T.pushforward hS).isClosed_strictTransformSeq_diff hS.isClosed hSH hcl
          (T.centersIn_pushforward hS) ⟨i, hi⟩
      have hev := eventually_stalkIdeal_idealSheaf_le_of_isClosed_diff hSi hHi
        ((T.pushforward hS).strictTransformSeq_mono hSH ⟨i, hi⟩) hcl' hleH hxS
      have hJ : ((T.pushforward hS).markedTransformSeq J 1 ⟨i, hi⟩).stalkIdeal
          (T.pushforwardIncl hS ⟨i, hi⟩ x') ≠ ⊤ := fun htop =>
        hord0 ((IdealSheaf.ord_eq_zero_iff _).mpr fun hc => hc htop)
      -- descend the predicate to `x'`, off the lower boundary
      have hP' := T.isSmoothTransversalIdealAt_pullback_pushforwardIncl hS hF hFS hmax hT
        ⟨i, hi⟩ hSi hev.self_of_nhds hJ hPx
      have hx' : ∀ j, x' ∉ (T.totalTransformSeqFrom (hS.traceFamily F) ⟨i, hi⟩).hyp j := by
        intro j hj
        have hmem : x' ∈ (T.totalTransformSeqFrom (hS.traceFamily F) ⟨i, hi⟩).support :=
          Set.mem_iUnion.mpr ⟨j, hj⟩
        rw [T.support_totalTransformSeqFrom_traceFamily_eq_preimage hS hF hFS hmax hT ⟨i, hi⟩]
          at hmem
        obtain ⟨j', hj'⟩ := Set.mem_iUnion.mp hmem
        exact hx j' hj'
      -- a point of the fibre over `incl x'`
      intro hymem
      by_cases hyS : y ∈ (T.pushforward hS).strictTransformSeq S ⟨i + k, Nat.lt_succ_of_lt h⟩
      · have hyr : y ∈ Set.range (T.pushforwardIncl hS ⟨i + k, Nat.lt_succ_of_lt h⟩) := by
          rw [T.range_pushforwardIncl hS]
          exact hyS
        obtain ⟨y', rfl⟩ := hyr
        have hsq := T.pushforwardIncl_stageMapAdd hS i k (Nat.lt_succ_of_lt h) y'
        have hy'x : T.stageMapAdd i k (Nat.lt_succ_of_lt h) y' = x' := by
          apply (T.isClosedEmbedding_pushforwardIncl hS ⟨i, hi⟩).injective
          rw [hsq]
          exact hy
        have hnot := hP i k h x' hP' hx' y' hy'x
        -- the index `⟨i + k, h⟩` lives in `Fin T.length` (the push-forward has `T`'s length)
        have hymem' := (T.support_center_pushforward hS ⟨i + k, h⟩).subset hymem
        obtain ⟨z, hz, hzy⟩ := hymem'
        have hzy' : z = y' := (T.isClosedEmbedding_pushforwardIncl hS _).injective hzy
        exact hnot (hzy' ▸ hz)
      · exact hyS ((T.centersIn_pushforward hS ⟨i + k, h⟩) hymem)
  · -- `x` off the strict transform of `S`: so is its whole fibre, which the centres lie in
    intro hymem
    exact (T.pushforward hS).notMem_strictTransformSeq_of_stageMapAdd hS.isClosed i k
      (Nat.lt_succ_of_lt h) hxS y hy ((T.centersIn_pushforward hS ⟨i + k, h⟩) hymem)

/-- **The output clause along a push-forward, at the points of the strict transform of `S`**
([Kol07, Corollary 85] for the output clause; the stopped piece `H_last \ S_last` is treated by
`OutputClause.pushforward` in `ClausePhaseBCore.lean`): at a support point `x = incl x'` of the last
stage the lower marked transform has order `≥ 1` at `x'` (`ord_le_ord_pullback` through
`markedTransformSeq_pullback_pushforwardIncl`), the lower clause gives the predicate at `x'`, and
`isSmoothTransversalIdealAt_of_pullback_pushforwardIncl` lifts it with the maximal contact on a
neighbourhood (`eventually_stalkIdeal_idealSheaf_le_of_isClosed_diff`). -/
theorem OutputClause.pushforward_of_mem_strictTransformSeq (hF : F.IsSnc ψ)
    (hFS : F.HasSncWithProper ψ S 1) (hmax : ∀ y, J.ord y ≤ 1)
    (hT : T.IsOfOrderGe (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) 1
      ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)))
    (hH : IsClosedSubmanifold ψ H 1) (hSH : S ⊆ H) (hcl : IsClosed (H \ S))
    (hle : hH.idealSheaf ≤ J)
    (hO : T.OutputClause (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (hS.traceFamily F))
    {x : (T.pushforward hS).stage (Fin.last _)}
    (hx : x ∈ (T.pushforward hS).strictTransformSeq S (Fin.last _))
    (hord : (1 : ℕ∞) ≤ ((T.pushforward hS).markedTransformSeq J 1 (Fin.last _)).ord x) :
    ((T.pushforward hS).totalTransformSeqFrom F (Fin.last _)).IsSmoothTransversalIdealAt ψ
      ((T.pushforward hS).markedTransformSeq J 1 (Fin.last _)) x := by
  have hge : (T.pushforward hS).IsOfOrderGe J 1 (F.idealSheaf (𝕜 := 𝕜) (E := E)) :=
    T.pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily hS J.isDBalanced_one hmax hF hFS hT
  have hordP : (T.pushforward hS).IsOfOrder J (F.idealSheaf (𝕜 := 𝕜) (E := E)) 1 :=
    isOfOrder_of_isOfOrderGe_of_ord_le (T.pushforward hS) hge hmax
  have hle' : hH.idealSheaf ≤ J.iteratedDeriv (1 - 1) := hle
  have hxr : x ∈ Set.range (T.pushforwardIncl hS (Fin.last _)) := by
    rw [T.range_pushforwardIncl hS]
    exact hx
  obtain ⟨x', rfl⟩ := hxr
  have hSi : IsClosedSubmanifold ψ ((T.pushforward hS).strictTransformSeq S (Fin.last _)) 1 :=
    (T.pushforward hS).isClosedSubmanifold_strictTransformSeq S hS (T.centersIn_pushforward hS) _
  have hHi : IsClosedSubmanifold ψ ((T.pushforward hS).strictTransformSeq H (Fin.last _)) 1 :=
    hordP.isClosedSubmanifold_strictTransformSeq_of_le le_rfl hH hle' (Fin.last _)
  have hleH : hHi.idealSheaf ≤ (T.pushforward hS).markedTransformSeq J 1 (Fin.last _) :=
    hordP.idealSheaf_strictTransformSeq_le_markedTransformSeq le_rfl hH hle' (Fin.last _) hHi
  have hcl' : IsClosed ((T.pushforward hS).strictTransformSeq H (Fin.last _) \
      (T.pushforward hS).strictTransformSeq S (Fin.last _)) :=
    (T.pushforward hS).isClosed_strictTransformSeq_diff hS.isClosed hSH hcl
      (T.centersIn_pushforward hS) _
  have hev := eventually_stalkIdeal_idealSheaf_le_of_isClosed_diff hSi hHi
    ((T.pushforward hS).strictTransformSeq_mono hSH _) hcl' hleH hx
  have hJ : ((T.pushforward hS).markedTransformSeq J 1 (Fin.last _)).stalkIdeal
      (T.pushforwardIncl hS (Fin.last _) x') ≠ ⊤ := by
    intro htop
    have h0 : ((T.pushforward hS).markedTransformSeq J 1 (Fin.last _)).ord
        (T.pushforwardIncl hS (Fin.last _) x') = 0 :=
      (IdealSheaf.ord_eq_zero_iff _).mpr fun hc => hc htop
    rw [h0] at hord
    exact absurd hord (by simp)
  -- the lower marked transform has order `≥ 1` at `x'`: the order does not drop under pull-back
  have hord' : (1 : ℕ∞) ≤ (T.markedTransformSeq
      (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) 1 (Fin.last _)).ord x' := by
    rw [← T.markedTransformSeq_pullback_pushforwardIncl hS J hge (Fin.last _)]
    exact hord.trans (IdealSheaf.ord_le_ord_pullback _ _ _ x')
  exact T.isSmoothTransversalIdealAt_of_pullback_pushforwardIncl hS hF hFS hmax hT (Fin.last _)
    hSi hev hJ (hO x' hord')

end Pushforward

end AnalyticManifold.FiniteSuccession

end
