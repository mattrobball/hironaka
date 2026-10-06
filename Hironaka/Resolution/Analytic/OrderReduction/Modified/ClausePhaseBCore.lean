/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBData
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseTools
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBComm
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Resolution.Analytic.GoingUp.Corollary85
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.MaximalContactTheorem
import Hironaka.Resolution.Analytic.OrderReduction.BDBridge
import Hironaka.Resolution.Analytic.OrderReduction.BDCosupp
import Hironaka.Resolution.Analytic.OrderReduction.BDFamOrder
import Hironaka.Resolution.Analytic.OrderReduction.LocalFunctorComm
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClausePushforward
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBOrder
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepCExit
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StopPersistence
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-!
# The two stop clauses of the modified core of the modified first step

The modified first step of [Wlo09, Theorem 7.4.1] restricts `(𝓘, 1)` to the hypersurface of
maximal contact `H⁺` (the member `Eʲ` without its stopped components) and runs the modified
resolution one dimension down there; the value is pushed forward (`coreModOn`, `StepBCore.lean`).
Its order clause is [Kol07, Corollary 85] (`coreModOn_isOfOrderGe`, `StepBOrder.lean`). This
module proves the two remaining clauses of the modified core, the stopped clause and the output
clause of `ClauseTools.lean`, from the clauses `hR8` and `hR1` of the functor one dimension down,
with respect to the boundary without the member, `(E − Eʲ)|_U`. This is the form the link of
Step 2.2 uses, since `E − Eʲ = E^{exc}` is a sub-family both of the boundary of the triple of
[Kol07, Theorem 103, Step 2.2], `E^{exc} + H_r`, and of the full transformed boundary
(`ClauseBridge.lean`).

* `strictTransformSeq_diff_succ_eq_preimage`, `strictTransformSeq_diff_stageMapAdd_eq_preimage`:
  the stopped piece `H_k \ S_k` is the preimage of `H \ S` (the step of the induction of
  `isClosed_strictTransformSeq_diff`, iterated).
* `ord_markedTransformSeq_stageMapAdd_eq_zero`: the order `0` propagates along the fibre (the inner
  induction of `notMem_center_of_ord_eq_zero`, stated on its own).
* `IsSmoothTransversalIdealAt.stageMapAdd_of_notMem_center`: the predicate transports along a fibre
  no centre meets, without the hypothesis that the point is off the boundary.
* `isSmoothTransversalIdealAt_of_eq_idealSheaf_of_hasSncWithProper`: where `J` is the ideal sheaf
  of `H` and `F` has proper normal crossings with `H`, the predicate holds (the stopped case at a
  point of the boundary).
* `OutputClause.pushforward`: [Kol07, Corollary 85] for the output clause, complete:
  `OutputClause.pushforward_of_mem_strictTransformSeq` on the strict transform of `S`; off the
  strict transform of `H` the order is `0` (the ideal of the strict transform of `H` lies in the
  transform, `idealSheaf_strictTransformSeq_le_markedTransformSeq`); on the stopped piece the point
  lies over `H \ S`, where `J` is the ideal sheaf of `H`, and the predicate transports along the
  fibre.
* `HFamData.StoppedClauseFam`, `HFamData.OutputClauseFam`: the clauses for the data of the step at a
  member of maximal contact, with respect to the boundary without the member.
* `coreModTraceLift`, `restrictedTripleMod_pullback_bundle_eq`, `coreModTraceLift_isOfOrderGe`,
  `coreModTraceLift_stoppedClause`, `coreModTraceLift_outputClause`: the lower run on the trace,
  lifted along the bundle isomorphism, with its three clauses for the restricted triple of `T|_U`.
* `coreModOn_stoppedClause`, `coreModOn_outputClause`: the stopped clause of the modified core
  (`StoppedClause.pushforward`) and its output clause (`OutputClause.pushforward`, the stopped
  piece being `Z_{-1} ∩ U`, where `𝓘` is the ideal sheaf of `Eʲ` by
  `mem_Zminus1_one_iff_isHypersurfaceIdealAt`), through `pushforwardBridge` and the deletion of the
  empty blow-ups (`stoppedClause_eraseEmpty`, `outputClause_eraseEmpty`, with the order clause of
  [Kol07, Corollary 85] with respect to `E − Eʲ`).
* `hFamDataMod_stoppedClauseFam`, `hFamDataMod_outputClauseFam`: the data of the modified first
  step has both clauses.

Sources: the modified first step and the stop rule of [Wlo09, Theorem 7.4.1];
[Kol07, Corollary 85]; the proof of [Kol07, Lemma 102]. The statements themselves are not in the
sources.
-/

@[expose] public section


noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Hironaka.Manifold Manifold Hironaka.Local
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

section Generic

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- **The stopped piece is the preimage of the stopped piece one stage down** (the step of the
induction of `isClosed_strictTransformSeq_diff`, stated on its own): for `S ⊆ H` closed with `H \ S`
closed and the centres inside the strict transforms of `S`, `H_{i+1} \ S_{i+1} = π_i⁻¹(H_i \ S_i)`.
-/
theorem strictTransformSeq_diff_succ_eq_preimage (B : FiniteSuccession M) {S H : Set M}
    (hSc : IsClosed S) (hSH : S ⊆ H) (hcl : IsClosed (H \ S)) (hc : B.CentersIn S)
    (i : Fin B.length) :
    B.strictTransformSeq H i.succ \ B.strictTransformSeq S i.succ =
      ⇑(B.map i) ⁻¹' (B.strictTransformSeq H i.castSucc \ B.strictTransformSeq S i.castSucc) := by
  have hD : IsClosed (B.strictTransformSeq H i.castSucc \ B.strictTransformSeq S i.castSucc) :=
    B.isClosed_strictTransformSeq_diff hSc hSH hcl hc i.castSucc
  set A := B.strictTransformSeq H i.castSucc with hA
  set Si := B.strictTransformSeq S i.castSucc with hSi
  set C := (B.center i).support with hC
  set π := B.map i with hπ
  have hSiA : Si ⊆ A := B.strictTransformSeq_mono hSH _
  have hCS : C ⊆ Si := hc i
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
  have e1 : B.strictTransformSeq H i.succ = closure (π ⁻¹' (A \ C)) := rfl
  have e2 : B.strictTransformSeq S i.succ = closure (π ⁻¹' (Si \ C)) := rfl
  have hpre : IsClosed (π ⁻¹' (A \ Si)) := hD.preimage π.contMDiff.continuous
  have hsub : B.strictTransformSeq S i.succ ⊆ π ⁻¹' Si :=
    B.strictTransformSeq_succ_subset_preimage S hSc i
  rw [e1, e2, hunion, Set.preimage_union, closure_union, hpre.closure_eq]
  ext z
  constructor
  · rintro ⟨hz1 | hz1, hz2⟩
    · exact absurd hz1 hz2
    · exact hz1
  · intro hz
    exact ⟨Or.inr hz, fun hzS => hz.2 (hsub hzS)⟩

/-- `strictTransformSeq_diff_succ_eq_preimage` iterated along `stageMapAdd`: the stopped piece at
stage `i + k` is the preimage of the stopped piece at stage `i`. -/
theorem strictTransformSeq_diff_stageMapAdd_eq_preimage (B : FiniteSuccession M) {S H : Set M}
    (hSc : IsClosed S) (hSH : S ⊆ H) (hcl : IsClosed (H \ S)) (hc : B.CentersIn S) (i k : ℕ)
    (h : i + k < B.length + 1) :
    B.strictTransformSeq H ⟨i + k, h⟩ \ B.strictTransformSeq S ⟨i + k, h⟩ =
      B.stageMapAdd i k h ⁻¹'
        (B.strictTransformSeq H ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩ \
          B.strictTransformSeq S ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩) := by
  induction k with
  | zero =>
    ext y
    exact Iff.rfl
  | succ k ih =>
    have hk : i + k < B.length + 1 := Nat.lt_of_succ_lt h
    have hk' : i + k < B.length := Nat.lt_of_succ_lt_succ h
    have e := B.strictTransformSeq_diff_succ_eq_preimage hSc hSH hcl hc ⟨i + k, hk'⟩
    change B.strictTransformSeq H (⟨i + k, hk'⟩ : Fin B.length).succ \
      B.strictTransformSeq S (⟨i + k, hk'⟩ : Fin B.length).succ = _
    rw [e]
    change ⇑(B.map ⟨i + k, hk'⟩) ⁻¹'
      (B.strictTransformSeq H ⟨i + k, hk⟩ \ B.strictTransformSeq S ⟨i + k, hk⟩) = _
    rw [ih hk, ← Set.preimage_comp]
    rfl

/-- **The order `0` propagates along the fibre** (the inner induction of
`notMem_center_of_ord_eq_zero`, stated on its own): over a point of order `0` at stage `i`, every
point of stage `i + k` has order `0`. A centre point has order `≥ 1`
(`ordAlongIdeal_le_ord_of_mem_support`), so the blow-ups are local isomorphisms along the fibre and
the marked transform is the pull-back there (`birationalTransform_stalkIdeal_of_notMem`,
`ord_pullback_of_isLocalDiffeomorphAt`). -/
theorem ord_markedTransformSeq_stageMapAdd_eq_zero (S : FiniteSuccession M)
    {I E₀ : IdealSheaf M} (hge : S.IsOfOrderGe I 1 E₀) (i k : ℕ) (h : i + k < S.length + 1)
    {x : S.stage ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩}
    (hx : (S.markedTransformSeq I 1 ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩).ord x = 0)
    (y : S.stage ⟨i + k, h⟩) (hy : S.stageMapAdd i k h y = x) :
    (S.markedTransformSeq I 1 ⟨i + k, h⟩).ord y = 0 := by
  induction k with
  | zero =>
    have hyx : y = x := hy
    subst hyx
    exact hx
  | succ k ih =>
    have hk : i + k < S.length + 1 := Nat.lt_of_succ_lt h
    have hk' : i + k < S.length := Nat.lt_of_succ_lt_succ h
    have hzx : S.stageMapAdd i k hk (S.map ⟨i + k, hk'⟩ y) = x := hy
    have hz := ih hk hx _ hzx
    -- the image of `y` is not in the centre: a centre point has order `≥ 1`
    have hzc : S.map ⟨i + k, hk'⟩ y ∉ (S.center ⟨i + k, hk'⟩).support := by
      intro hmem
      have h1 := (hge ⟨i + k, hk'⟩).2 _ hmem
      have h2 := BMOmod.ordAlongIdeal_le_ord_of_mem_support (S.center ⟨i + k, hk'⟩)
        (S.markedTransformSeq I 1 ⟨i + k, hk⟩) hmem
      rw [hz] at h2
      exact absurd (h1.trans h2) (by simp)
    have hJ : ∀ a ∈ (S.center ⟨i + k, hk'⟩).support,
        ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
          (S.isClosedSubmanifold_center ⟨i + k, hk'⟩).idealSheaf
          (S.markedTransformSeq I 1 ⟨i + k, hk⟩) a := by
      intro a ha
      rw [S.idealSheaf_center]
      exact (hge ⟨i + k, hk'⟩).2 a ha
    have hstalk := birationalTransform_stalkIdeal_of_notMem
      (S.isClosedSubmanifold_center ⟨i + k, hk'⟩) (S.isBlowUp_map ⟨i + k, hk'⟩) hJ hzc
    have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (S.map ⟨i + k, hk'⟩) y :=
      (S.isBlowUp_map ⟨i + k, hk'⟩).isLocalDiffeomorphOn_compl ⟨y, hzc⟩
    have e : S.markedTransformSeq I 1 ⟨i + (k + 1), h⟩ =
        (MarkedIdealSheaf.birationalTransform (S.isClosedSubmanifold_center ⟨i + k, hk'⟩)
          (S.isBlowUp_map ⟨i + k, hk'⟩) ⟨S.markedTransformSeq I 1 ⟨i + k, hk⟩, 1⟩).I :=
      S.markedTransformSeq_succ I 1 ⟨i + k, hk'⟩
    rw [e, BMOmod.ord_congr_stalk hstalk]
    exact (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _ hloc).trans hz

end Generic

end AnalyticManifold.FiniteSuccession

namespace Manifold

section Transport

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- **The predicate transports along a fibre no centre meets**, without the hypothesis that the
point is off the boundary: the predicate at a point `x` of stage `i` whose images at the stages
`i, …, i + k − 1` miss the centres blown up there transports to every point over it at stage
`i + k` (`totalTransform_of_notMem` at each step). The hypothesis of
`stageMapAdd_of_forall_notMem_center` that the point is off the boundary is present there so that
the two persistence statements, for the predicate and for the boundary
(`notMem_totalTransformSeqFrom_of_forall_notMem_center`, which needs it), have the same hypotheses
and are applied together from those of the stopped clause; its proof does not need it, since
`totalTransform_of_notMem` transports the predicate at every point off the centre. This form drops
it, as the stopped piece lies on the other members of the boundary. -/
theorem HypersurfaceFamily.IsSmoothTransversalIdealAt.stageMapAdd_of_notMem_center
    (S : FiniteSuccession M) {I : AnalyticManifold.IdealSheaf M} {F : HypersurfaceFamily M}
    (hge : S.IsOfOrderGe I 1 F.idealSheaf) (hF : F.IsSnc ψ) (i k : ℕ) (h : i + k < S.length + 1)
    {x : S.stage ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩}
    (hP : (S.totalTransformSeqFrom F
        ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩).IsSmoothTransversalIdealAt ψ
      (S.markedTransformSeq I 1 ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩) x)
    (hcen : ∀ (l : ℕ) (hl : l < k)
      (z : S.stage ⟨i + l, Nat.lt_of_le_of_lt (Nat.add_le_add_left hl.le i) h⟩),
      S.stageMapAdd i l (Nat.lt_of_le_of_lt (Nat.add_le_add_left hl.le i) h) z = x →
      z ∉ (S.center ⟨i + l, Nat.lt_of_lt_of_le (Nat.add_lt_add_left hl i)
        (Nat.lt_succ_iff.mp h)⟩).support)
    (y : S.stage ⟨i + k, h⟩) (hy : S.stageMapAdd i k h y = x) :
    (S.totalTransformSeqFrom F ⟨i + k, h⟩).IsSmoothTransversalIdealAt ψ
      (S.markedTransformSeq I 1 ⟨i + k, h⟩) y := by
  induction k with
  | zero =>
    have hyx : y = x := hy
    subst hyx
    exact hP
  | succ k ih =>
    have hk : i + k < S.length + 1 := Nat.lt_of_succ_lt h
    have hk' : i + k < S.length := Nat.lt_of_succ_lt_succ h
    have hzx : S.stageMapAdd i k hk (S.map ⟨i + k, hk'⟩ y) = x := hy
    have hz := ih hk hP (fun l hl z hz => hcen l (Nat.lt_succ_of_lt hl) z hz) _ hzx
    have hzc : S.map ⟨i + k, hk'⟩ y ∉ (S.center ⟨i + k, hk'⟩).support :=
      hcen k (Nat.lt_succ_self k) _ hzx
    have hFk : (S.totalTransformSeqFrom F ⟨i + k, hk⟩).IsSnc ψ :=
      (S.isSnc_totalTransformSeqFrom_and_boundarySeq_eq (ψ := ψ) hF
        (fun j => hge.hasOnlyNormalCrossingsWith j) ⟨i + k, hk⟩).1
    have hJ : ∀ a ∈ (S.center ⟨i + k, hk'⟩).support,
        (1 : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.isClosedSubmanifold_center ⟨i + k, hk'⟩).idealSheaf
          (S.markedTransformSeq I 1 ⟨i + k, hk⟩) a := by
      intro a ha
      rw [S.idealSheaf_center]
      have := hge.le_ordAlong ⟨i + k, hk'⟩ ha
      rwa [Nat.cast_one] at this
    exact HypersurfaceFamily.IsSmoothTransversalIdealAt.totalTransform_of_notMem ψ
      (S.isClosedSubmanifold_center ⟨i + k, hk'⟩) (S.isBlowUp_map ⟨i + k, hk'⟩) hFk hJ hzc hz

/-- **The predicate at a point where the ideal is the ideal of a hypersurface in proper normal
crossings with the boundary** (the stopped case of [Wlo09, Theorem 7.4.1] at a point of the
boundary): if `J` is the ideal sheaf of the smooth hypersurface `H` near `y ∈ H` and `F` has simple
normal crossings with `H` properly, the predicate holds at `y` with `c = 1`. The chart of `F` at
`y` adapted to `H` with proper normal crossings (`hFH y hy`) is restricted to where the two ideal
sheaves agree; `J_a = (z_{σ 0})` at the points of `H` (`stalkIdeal_idealSheaf_eq_span`) and
`J_a = ⊤ = (z_{σ 0})` off `H`; the members' coordinates avoid `σ` by properness. -/
theorem HypersurfaceFamily.isSmoothTransversalIdealAt_of_eq_idealSheaf_of_hasSncWithProper
    {H : Set M} (hH : IsClosedSubmanifold ψ H 1) {F : HypersurfaceFamily M}
    {J : AnalyticManifold.IdealSheaf M} {y : M} (hy : y ∈ H)
    (hJ : ∀ᶠ a in 𝓝 y, J.stalkIdeal a = hH.idealSheaf.stalkIdeal a)
    (hFH : F.HasSncWithProper ψ H 1) : F.IsSmoothTransversalIdealAt ψ J y := by
  obtain ⟨φ₀, σ, cidx, hφ₀, hc₀, hproper⟩ := hFH y hy
  obtain ⟨U, hUJ, hUo, hyU⟩ := eventually_nhds_iff.mp hJ
  have hφ : IsAdaptedChart ψ H (φ₀.restrOpen U hUo) σ := hφ₀.restrOpen' U hUo
  have hc : F.IsSncChartAt ψ (φ₀.restrOpen U hUo) y cidx := hc₀.restrOpen hUo hyU
  refine ⟨1, φ₀.restrOpen U hUo, σ, cidx, hc, fun a ha => ?_,
    fun j i hji => hproper j ⟨i, hji.symm⟩⟩
  rw [hUJ a ha.2]
  by_cases haH : a ∈ H
  · exact hH.stalkIdeal_idealSheaf_eq_span haH hφ ha
  · rw [hH.stalkIdeal_idealSheaf_of_notMem haH]
    have hne : ψ (φ₀.restrOpen U hUo a) (σ 0) ≠ 0 := by
      intro h0
      refine haH ((hφ.2 a ha).mpr fun i => ?_)
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact h0
    symm
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_range_self 0)) ?_
    exact isUnit_coord_of_ne_zero (φ₀.restrOpen U hUo) hc.mem_maximalAtlas ha hne

end Transport

end Manifold

namespace AnalyticManifold.FiniteSuccession

section Pushforward

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {S : Set M} (hS : IsClosedSubmanifold ψ S 1) (T : FiniteSuccession hS.toAnalyticManifold)
  {J : IdealSheaf M} {F : HypersurfaceFamily M} {H : Set M}

/-- **[Kol07, Corollary 85] for the output clause, complete**: at a point `x` of the last stage with
`1 ≤ ord`: on the strict transform of `S`, `OutputClause.pushforward_of_mem_strictTransformSeq`;
off the strict transform of `H`, the order is `0` (`𝓘_{H_last} ≤ I_last` by
`idealSheaf_strictTransformSeq_le_markedTransformSeq`), a contradiction; on the stopped piece
`H_last \ S_last = g⁻¹(H \ S)` (`strictTransformSeq_diff_stageMapAdd_eq_preimage`), `x` lies over a
stopped point `z` where `J` is the ideal sheaf of `H` (`hstop`), the predicate holds at `z`
(`isSmoothTransversalIdealAt_of_eq_idealSheaf_of_hasSncWithProper`) and transports along the
fibre, which no centre meets (`stageMapAdd_of_notMem_center`,
`notMem_strictTransformSeq_of_stageMapAdd`, `centersIn_pushforward`). -/
theorem OutputClause.pushforward (hF : F.IsSnc ψ) (hFS : F.HasSncWithProper ψ S 1)
    (hmax : ∀ y, J.ord y ≤ 1)
    (hT : T.IsOfOrderGe (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) 1
      ((hS.traceFamily F).idealSheaf (𝕜 := 𝕜) (E := Fin (n - 1) → 𝕜)))
    (hH : IsClosedSubmanifold ψ H 1) (hSH : S ⊆ H) (hcl : IsClosed (H \ S))
    (hle : hH.idealSheaf ≤ J) (hFH : F.HasSncWithProper ψ H 1)
    (hstop : ∀ z ∈ H \ S, ∀ᶠ a in 𝓝 z, J.stalkIdeal a = hH.idealSheaf.stalkIdeal a)
    (hO : T.OutputClause (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (hS.traceFamily F)) :
    (T.pushforward hS).OutputClause ψ J F := by
  intro x hord
  have hge : (T.pushforward hS).IsOfOrderGe J 1 (F.idealSheaf (𝕜 := 𝕜) (E := E)) :=
    T.pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily hS J.isDBalanced_one hmax hF hFS hT
  have hordP : (T.pushforward hS).IsOfOrder J (F.idealSheaf (𝕜 := 𝕜) (E := E)) 1 :=
    isOfOrder_of_isOfOrderGe_of_ord_le (T.pushforward hS) hge hmax
  have hle' : hH.idealSheaf ≤ J.iteratedDeriv (1 - 1) := hle
  by_cases hxS : x ∈ (T.pushforward hS).strictTransformSeq S (Fin.last _)
  · -- on the strict transform of `S`: PU6
    exact OutputClause.pushforward_of_mem_strictTransformSeq hS T hF hFS hmax hT hH hSH hcl hle
      hO hxS hord
  by_cases hxH : x ∈ (T.pushforward hS).strictTransformSeq H (Fin.last _)
  · -- the stopped piece: `x` lies over a point of `H \ S`, where `J` is the ideal sheaf of `H`
    have hlast : (Fin.last (T.pushforward hS).length : Fin ((T.pushforward hS).length + 1)) =
        ⟨0 + (T.pushforward hS).length, by omega⟩ :=
      Fin.ext (Nat.zero_add _).symm
    clear hord
    revert x
    rw [hlast]
    intro x hxS hxH
    have hlt : 0 + (T.pushforward hS).length < (T.pushforward hS).length + 1 := by omega
    have hmem := (T.pushforward hS).strictTransformSeq_diff_stageMapAdd_eq_preimage hS.isClosed
      hSH hcl (T.centersIn_pushforward hS) 0 (T.pushforward hS).length hlt
    have hz : (T.pushforward hS).stageMapAdd 0 _ hlt x ∈ H \ S := by
      have hx : x ∈ (T.pushforward hS).strictTransformSeq H ⟨0 + _, hlt⟩ \
          (T.pushforward hS).strictTransformSeq S ⟨0 + _, hlt⟩ := ⟨hxH, hxS⟩
      rw [hmem] at hx
      exact hx
    have hPz : F.IsSmoothTransversalIdealAt ψ J ((T.pushforward hS).stageMapAdd 0 _ hlt x) :=
      HypersurfaceFamily.isSmoothTransversalIdealAt_of_eq_idealSheaf_of_hasSncWithProper hH hz.1
        (hstop _ hz) hFH
    refine HypersurfaceFamily.IsSmoothTransversalIdealAt.stageMapAdd_of_notMem_center
      (T.pushforward hS) hge hF 0 _ hlt hPz ?_ x rfl
    intro l hl w hw hwc
    exact (T.pushforward hS).notMem_strictTransformSeq_of_stageMapAdd hS.isClosed 0 l _ hz.2 w hw
      (T.centersIn_pushforward hS _ hwc)
  · -- off the strict transform of `H`: the marked transform is the unit ideal there
    exfalso
    have hHi : IsClosedSubmanifold ψ ((T.pushforward hS).strictTransformSeq H (Fin.last _)) 1 :=
      hordP.isClosedSubmanifold_strictTransformSeq_of_le le_rfl hH hle' (Fin.last _)
    have hleH : hHi.idealSheaf ≤ (T.pushforward hS).markedTransformSeq J 1 (Fin.last _) :=
      hordP.idealSheaf_strictTransformSeq_le_markedTransformSeq le_rfl hH hle' (Fin.last _) hHi
    have htop : ((T.pushforward hS).markedTransformSeq J 1 (Fin.last _)).stalkIdeal x = ⊤ :=
      top_le_iff.mp ((hHi.stalkIdeal_idealSheaf_of_notMem hxH).symm.le.trans
        (IdealSheaf.le_def.mp hleH x))
    have h0 : ((T.pushforward hS).markedTransformSeq J 1 (Fin.last _)).ord x = 0 :=
      (IdealSheaf.ord_eq_zero_iff _).mpr fun hc => hc htop
    rw [h0] at hord
    exact absurd hord (by simp)

end Pushforward

end AnalyticManifold.FiniteSuccession

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- **The stopped clause for the data of the step at a member of maximal contact** (the field
`stopped_never_blownUp` of `BMOmodFam` for the value at a member of maximal contact, with respect
to the boundary without the member): for a triple of the class, a member `j` with
`𝓘_{Eʲ} ≤ 𝓘^{(s-1)}` and a relatively compact open, the value has the stopped clause for
`(𝓘|_U, (E − Eʲ)|_U)`. This is the form the link of Step 2.2 uses: the boundary of the triple of
[Kol07, Theorem 103, Step 2.2], `E^{exc} + H_r`, and the full transformed boundary both contain
`E − Eʲ = E^{exc}` as a sub-family. -/
def HFamData.StoppedClauseFam {s : ℕ} (hf : HFamData ψ₀ s) : Prop :=
  ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N) (hT : AnalyticTriple.BOClass s T)
    (j : T.F.ι) (_hle : (T.isSnc.1 j).idealSheaf ≤ T.I.iteratedDeriv (s - 1)) (U : Opens N)
    (hU : IsCompact (closure (U : Set N))),
    ((hf.fam T hT j).seqOn U hU).toSuccession.StoppedClause ψ₀
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I
      ((T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).F.emptyMember j)

/-- **The order clause for the data of the step with respect to the boundary without the member**
([Kol07, Corollary 85] at `E − Eʲ`): the value at a member of maximal contact is of order `≥ s` for
`(𝓘|_U, (E − Eʲ)|_U)`. The normal-crossings clause is what `StoppedClause.of_membersSubset` and
`OutputClause.of_forall_mem` need to change the boundary of the two clauses. -/
def HFamData.IsOfOrderGeEmptyMemberFam {s : ℕ} (hf : HFamData ψ₀ s) : Prop :=
  ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N) (hT : AnalyticTriple.BOClass s T)
    (j : T.F.ι) (_hle : (T.isSnc.1 j).idealSheaf ≤ T.I.iteratedDeriv (s - 1)) (U : Opens N)
    (hU : IsCompact (closure (U : Set N))),
    ((hf.fam T hT j).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I s
      (((T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).F.emptyMember
        j).idealSheaf (𝕜 := 𝕜) (E := E))

/-- **The output clause for the data of the step at a member of maximal contact** (the field
`output_isSmoothSubmanifoldIdeal` of `BMOmodFam` at a member of maximal contact, with respect to
the boundary without the member). -/
def HFamData.OutputClauseFam {s : ℕ} (hf : HFamData ψ₀ s) : Prop :=
  ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N) (hT : AnalyticTriple.BOClass s T)
    (j : T.F.ι) (_hle : (T.isSnc.1 j).idealSheaf ≤ T.I.iteratedDeriv (s - 1)) (U : Opens N)
    (hU : IsCompact (closure (U : Set N))),
    ((hf.fam T hT j).seqOn U hU).toSuccession.OutputClause ψ₀
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I
      ((T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).F.emptyMember j)

end Hironaka.Manifold

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
  (R : AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (AnalyticTriple.BMOClass 1))
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (j : T.F.ι)
  (hT : AnalyticTriple.BMOClass 1 T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- The lower run on the trace `U ∩ H⁺`, read on the bundled trace of `U` in `H⁺` through the bundle
isomorphism (the list `pushforwardRestrict_eq` pushes forward). -/
def coreModTraceLift :
    BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      ((isClosedSubmanifold_hplus T j).restrictOpen U).toAnalyticManifold :=
  (coreModTrace R T j hT U hU).pullback
    ⟨((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm,
      ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.contMDiff⟩
    ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.isLocalDiffeomorph

/-- The restricted triple on `H⁺`, pulled back to the trace of `U` and along the bundle isomorphism,
is the restricted triple of `T|_U` on the trace of `H⁺` (the identification `htr` inside
`coreModOn_isOfOrderGe`, stated on its own: `restrictedTripleModOf_isPullbackOf` with
`hplusRestrictMap_inclusion_eq`). -/
theorem restrictedTripleMod_pullback_bundle_eq :
    ((restrictedTripleMod T j).pullback
        ((isClosedSubmanifold_hplus T j).toAnalyticManifold.inclusion
          ((isClosedSubmanifold_hplus T j).preimageOpens U))
        (isLocalDiffeomorph_inclusion _ _)).pullback
        ⟨((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm,
          ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.contMDiff⟩
        ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.isLocalDiffeomorph =
      restrictedTripleModOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) j
        (isClosedSubmanifold_preimage_hplus T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
        (hplus_pullback T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).symm := by
  refine AnalyticTriple.IsPullbackOf.eq
    (((restrictedTripleMod T j).isPullbackOf_pullback _ _).comp
      (((restrictedTripleMod T j).pullback _ _).isPullbackOf_pullback _ _)) ?_
  have h := restrictedTripleModOf_isPullbackOf T j (M.inclusion U)
    (isLocalDiffeomorph_inclusion M U)
  rw [hplusRestrictMap_inclusion_eq T j U] at h
  exact h

variable (hRo : ∀ {N : AnalyticManifold.{u} 𝕜 (Fin (n - 1) → 𝕜)}
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) N)
    (hT' : AnalyticTriple.BMOClass 1 T') (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
    ((R.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)

include hRo in
/-- The lifted lower run is of order `≥ 1` for the restricted triple of `T|_U` on the trace of `H⁺`
(the fact `hL'` inside `coreModOn_isOfOrderGe`, stated on its own: the order clause of the functor
one dimension down pulled back along the bundle isomorphism, the triple identified by
`restrictedTripleMod_pullback_bundle_eq`). -/
theorem coreModTraceLift_isOfOrderGe :
    (coreModTraceLift R T j hT U hU).toSuccession.IsOfOrderGe
      (restrictedTripleModOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) j
        (isClosedSubmanifold_preimage_hplus T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
        (hplus_pullback T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).symm).I 1
      (restrictedTripleModOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) j
        (isClosedSubmanifold_preimage_hplus T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
        (hplus_pullback T j (M.inclusion U)
          (isLocalDiffeomorph_inclusion M U)).symm).F.idealSheaf := by
  have hL := hRo (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT)
    ((isClosedSubmanifold_hplus T j).preimageOpens U)
    ((isClosedSubmanifold_hplus T j).isCompact_closure_preimageOpens U hU)
  have hL' := AnalyticTriple.isOfOrderGe_pullback _ 1 _ hL
    ⟨((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm,
      ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.contMDiff⟩
    ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.isLocalDiffeomorph
  exact (restrictedTripleMod_pullback_bundle_eq T j U) ▸ hL'

include hRo in
/-- The lifted lower run has the stopped clause for that restricted triple (the clause `hR8` of the
functor one dimension down on the trace, pulled back along the bundle isomorphism by
`stoppedClause_pullback`). -/
theorem coreModTraceLift_stoppedClause
    (hR8 : R.StoppedClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))) :
    (coreModTraceLift R T j hT U hU).toSuccession.StoppedClause
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (restrictedTripleModOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) j
        (isClosedSubmanifold_preimage_hplus T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
        (hplus_pullback T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).symm).I
      (restrictedTripleModOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) j
        (isClosedSubmanifold_preimage_hplus T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
        (hplus_pullback T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).symm).F := by
  unfold AnalyticFamilyFunctor.StoppedClauseFam at hR8
  have hL := hRo (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT)
    ((isClosedSubmanifold_hplus T j).preimageOpens U)
    ((isClosedSubmanifold_hplus T j).isCompact_closure_preimageOpens U hU)
  have hP := hR8 (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT)
    ((isClosedSubmanifold_hplus T j).preimageOpens U)
    ((isClosedSubmanifold_hplus T j).isCompact_closure_preimageOpens U hU)
  have hP' := BlowUpSequence.stoppedClause_pullback (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (coreModTrace R T j hT U hU)
    ⟨((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm,
      ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.contMDiff⟩
    ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.isLocalDiffeomorph _ hL hP
  exact (restrictedTripleMod_pullback_bundle_eq T j U) ▸ hP'

include hRo in
/-- The lifted lower run has the output clause for that restricted triple (`hR1` on the trace,
pulled back by `outputClause_pullback`). -/
theorem coreModTraceLift_outputClause
    (hR1 : R.OutputClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))) :
    (coreModTraceLift R T j hT U hU).toSuccession.OutputClause
      (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (restrictedTripleModOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) j
        (isClosedSubmanifold_preimage_hplus T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
        (hplus_pullback T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).symm).I
      (restrictedTripleModOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) j
        (isClosedSubmanifold_preimage_hplus T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
        (hplus_pullback T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).symm).F := by
  unfold AnalyticFamilyFunctor.OutputClauseFam at hR1
  have hL := hRo (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT)
    ((isClosedSubmanifold_hplus T j).preimageOpens U)
    ((isClosedSubmanifold_hplus T j).isCompact_closure_preimageOpens U hU)
  have hO := hR1 (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT)
    ((isClosedSubmanifold_hplus T j).preimageOpens U)
    ((isClosedSubmanifold_hplus T j).isCompact_closure_preimageOpens U hU)
  have hO' := BlowUpSequence.outputClause_pullback (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (coreModTrace R T j hT U hU)
    ⟨((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm,
      ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.contMDiff⟩
    ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.isLocalDiffeomorph _ hL hO
  exact (restrictedTripleMod_pullback_bundle_eq T j U) ▸ hO'

variable (hmax : ∀ y, T.I.ord y ≤ 1)

include hRo hmax in
/-- **The modified core is of order `≥ 1` with respect to `(𝓘|_U, (E − Eʲ)|_U)`** ([Kol07,
Corollary 85], `pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily`, at the boundary `E − Eʲ` on the
lifted lower run; the deletion of the empty blow-ups by `isOfOrderGe_eraseEmpty`).
`coreModOn_isOfOrderGe` is the same clause with the full boundary. -/
theorem coreModOn_isOfOrderGe_emptyMember :
    (coreModOn R T j hT U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.emptyMember
        j).idealSheaf (𝕜 := 𝕜) (E := Fin n → 𝕜)) := by
  have hSU : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (⇑(M.inclusion U) ⁻¹' hplus T j) 1 :=
    isClosedSubmanifold_preimage_hplus T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)
  have hL' := coreModTraceLift_isOfOrderGe R T j hT U hU hRo
  have hmax' : ∀ y, (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I.ord y ≤ 1 :=
    fun y => (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ T.I
      (isLocalDiffeomorph_inclusion M U y)).trans_le (hmax _)
  have hI : (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I.IsDBalanced 1 :=
    IdealSheaf.isDBalanced_one _
  have hF₀ : ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.emptyMember j).IsSnc
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) :=
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc.emptyMember j
  have hFS₀ : ((T.pullback (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U)).F.emptyMember j).HasSncWithProper
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (⇑(M.inclusion U) ⁻¹' hplus T j) 1 := by
    have h := hasSncWithProper_hplus
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) j
    rw [hplus_pullback T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)] at h
    exact h
  have hge₀ := FiniteSuccession.pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily
    (T := (coreModTraceLift R T j hT U hU).toSuccession) hSU hI hmax' hF₀ hFS₀ hL'
  have hLne : (coreModTraceLift R T j hT U hU).NoEmptyCenters :=
    BlowUpSequence.noEmptyCenters_pullback_of_surjective _ _ _
      ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.surjective
      ((R.fam (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT)).noEmptyCenters _ _)
  unfold coreModOn
  rw [BlowUpSequence.pushforwardRestrict_eq]
  change ((coreModTraceLift R T j hT U hU).pushforward
    ((isClosedSubmanifold_hplus T j).restrictOpen U)).eraseEmpty.toSuccession.IsOfOrderGe _ 1 _
  have hbr := pushforwardBridge (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    ((isClosedSubmanifold_hplus T j).restrictOpen U) (coreModTraceLift R T j hT U hU) hLne
  refine BlowUpSequence.isOfOrderGe_eraseEmpty _ _ 1 hF₀ ?_
  rw [hbr]
  exact hge₀

variable (hle : (T.isSnc.1 j).idealSheaf ≤ T.I)

include hRo hmax hle in
/-- **The stopped clause of the modified core** with respect to `(𝓘|_U, (E − Eʲ)|_U)` (the stop
rule of the modified first step of [Wlo09, Theorem 7.4.1]): `StoppedClause.pushforward` on the
lifted lower run with `S := H⁺ ∩ U` and `H := Eʲ ∩ U` (the stopped locus is closed; `𝓘_{Eʲ} ≤ 𝓘` is
the maximal contact of the member), the order clause of [Kol07, Corollary 85] with respect to
`E − Eʲ` for the deletion of the empty blow-ups (`stoppedClause_eraseEmpty`), the list push-forward
read through `pushforwardBridge` and `pushforwardRestrict_eq`. -/
theorem coreModOn_stoppedClause
    (hR8 : R.StoppedClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))) :
    (coreModOn R T j hT U hU).toSuccession.StoppedClause (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.emptyMember j) := by
  have hSU : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (⇑(M.inclusion U) ⁻¹' hplus T j) 1 :=
    isClosedSubmanifold_preimage_hplus T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)
  have hL' := coreModTraceLift_isOfOrderGe R T j hT U hU hRo
  have hP' := coreModTraceLift_stoppedClause R T j hT U hU hRo hR8
  -- the data of `StoppedClause.pushforward` on `U`, with the boundary `E − Eʲ`
  have hmax' : ∀ y, (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I.ord y ≤ 1 :=
    fun y => (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ T.I
      (isLocalDiffeomorph_inclusion M U y)).trans_le (hmax _)
  have hI : (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I.IsDBalanced 1 :=
    IdealSheaf.isDBalanced_one _
  have hF₀ : ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.emptyMember j).IsSnc
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) :=
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc.emptyMember j
  have hFS₀ : ((T.pullback (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U)).F.emptyMember j).HasSncWithProper
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (⇑(M.inclusion U) ⁻¹' hplus T j) 1 := by
    have h := hasSncWithProper_hplus
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) j
    rw [hplus_pullback T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)] at h
    exact h
  have hH : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (⇑(M.inclusion U) ⁻¹' T.F.hyp j) 1 :=
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc.1 j
  have hSH : ⇑(M.inclusion U) ⁻¹' hplus T j ⊆ ⇑(M.inclusion U) ⁻¹' T.F.hyp j :=
    Set.preimage_mono (hplus_subset T j)
  have hcl : IsClosed (⇑(M.inclusion U) ⁻¹' T.F.hyp j \ ⇑(M.inclusion U) ⁻¹' hplus T j) := by
    have e : ⇑(M.inclusion U) ⁻¹' T.F.hyp j \ ⇑(M.inclusion U) ⁻¹' hplus T j =
        ⇑(M.inclusion U) ⁻¹' stopLocus T j := by
      rw [← Set.preimage_sdiff]
      unfold hplus
      rw [Set.sdiff_sdiff_cancel_left (stopLocus_subset T j)]
    rw [e]
    exact (isClosed_stopLocus T j).preimage (M.inclusion U).contMDiff.continuous
  have hle' : (T.isSnc.1 j).idealSheaf ≤ T.I.iteratedDeriv (1 - 1) := hle
  have hleU : hH.idealSheaf ≤ (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I :=
    T.idealSheaf_preimage_le_iteratedDeriv_pullback (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U) (T.isSnc.1 j) hle'
  -- `StoppedClause.pushforward` on the lifted lower run
  have hP := FiniteSuccession.StoppedClause.pushforward hSU
    (coreModTraceLift R T j hT U hU).toSuccession hF₀ hFS₀ hmax' hL' hH hSH hcl hleU hP'
  have hge₀ := FiniteSuccession.pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily
    (T := (coreModTraceLift R T j hT U hU).toSuccession) hSU hI hmax' hF₀ hFS₀ hL'
  have hLne : (coreModTraceLift R T j hT U hU).NoEmptyCenters :=
    BlowUpSequence.noEmptyCenters_pullback_of_surjective _ _ _
      ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.surjective
      ((R.fam (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT)).noEmptyCenters _ _)
  -- the list push-forward's succession is the succession's push-forward; the deletion of the empty
  -- blow-ups
  unfold coreModOn
  rw [BlowUpSequence.pushforwardRestrict_eq]
  change ((coreModTraceLift R T j hT U hU).pushforward
    ((isClosedSubmanifold_hplus T j).restrictOpen U)).eraseEmpty.toSuccession.StoppedClause _ _ _
  have hbr := pushforwardBridge (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    ((isClosedSubmanifold_hplus T j).restrictOpen U) (coreModTraceLift R T j hT U hU) hLne
  exact BlowUpSequence.stoppedClause_eraseEmpty (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) _
    (⟨(T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I,
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isNonzeroEverywhere,
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.emptyMember j, hF₀⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict U))
    (by rw [hbr]; exact hge₀) (by rw [hbr]; exact hP)

include hRo hmax hle in
/-- **The output clause of the modified core** with respect to `(𝓘|_U, (E − Eʲ)|_U)`:
`OutputClause.pushforward` on the lifted lower run. The stopped piece is `Z_{-1} ∩ U`, where `𝓘` is
the ideal sheaf of `Eʲ` (`mem_Zminus1_one_iff_isHypersurfaceIdealAt`) and `E − Eʲ` has proper
normal crossings with `Eʲ` (`hasSncWithProper_emptyMember`); `outputClause_eraseEmpty` for the
deletion of the empty blow-ups. -/
theorem coreModOn_outputClause
    (hR1 : R.OutputClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))) :
    (coreModOn R T j hT U hU).toSuccession.OutputClause (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.emptyMember j) := by
  have hSU : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (⇑(M.inclusion U) ⁻¹' hplus T j) 1 :=
    isClosedSubmanifold_preimage_hplus T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)
  have hL' := coreModTraceLift_isOfOrderGe R T j hT U hU hRo
  have hO' := coreModTraceLift_outputClause R T j hT U hU hRo hR1
  -- the data of `OutputClause.pushforward` on `U`, with the boundary `E − Eʲ`
  have hmax' : ∀ y, (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I.ord y ≤ 1 :=
    fun y => (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ T.I
      (isLocalDiffeomorph_inclusion M U y)).trans_le (hmax _)
  have hI : (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I.IsDBalanced 1 :=
    IdealSheaf.isDBalanced_one _
  have hF₀ : ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.emptyMember j).IsSnc
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) :=
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc.emptyMember j
  have hFS₀ : ((T.pullback (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U)).F.emptyMember j).HasSncWithProper
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (⇑(M.inclusion U) ⁻¹' hplus T j) 1 := by
    have h := hasSncWithProper_hplus
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) j
    rw [hplus_pullback T j (M.inclusion U) (isLocalDiffeomorph_inclusion M U)] at h
    exact h
  have hH : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (⇑(M.inclusion U) ⁻¹' T.F.hyp j) 1 :=
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc.1 j
  have hSH : ⇑(M.inclusion U) ⁻¹' hplus T j ⊆ ⇑(M.inclusion U) ⁻¹' T.F.hyp j :=
    Set.preimage_mono (hplus_subset T j)
  have hcl : IsClosed (⇑(M.inclusion U) ⁻¹' T.F.hyp j \ ⇑(M.inclusion U) ⁻¹' hplus T j) := by
    have e : ⇑(M.inclusion U) ⁻¹' T.F.hyp j \ ⇑(M.inclusion U) ⁻¹' hplus T j =
        ⇑(M.inclusion U) ⁻¹' stopLocus T j := by
      rw [← Set.preimage_sdiff]
      unfold hplus
      rw [Set.sdiff_sdiff_cancel_left (stopLocus_subset T j)]
    rw [e]
    exact (isClosed_stopLocus T j).preimage (M.inclusion U).contMDiff.continuous
  have hle' : (T.isSnc.1 j).idealSheaf ≤ T.I.iteratedDeriv (1 - 1) := hle
  have hleU : hH.idealSheaf ≤ (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I :=
    T.idealSheaf_preimage_le_iteratedDeriv_pullback (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U) (T.isSnc.1 j) hle'
  -- the stopped piece is `Z_{-1} ∩ U`, where `𝓘` is the ideal sheaf of `Eʲ`
  have hFH : ((T.pullback (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U)).F.emptyMember j).HasSncWithProper
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (⇑(M.inclusion U) ⁻¹' T.F.hyp j) 1 :=
    (T.pullback (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U)).isSnc.hasSncWithProper_emptyMember j
  have hstop : ∀ z ∈ ⇑(M.inclusion U) ⁻¹' T.F.hyp j \ ⇑(M.inclusion U) ⁻¹' hplus T j,
      ∀ᶠ a in 𝓝 z, (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I.stalkIdeal a =
        hH.idealSheaf.stalkIdeal a := by
    intro z hz
    have hzZ : z ∈ BD.Zminus1 (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
        ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.hyp j) := by
      rw [← BDan.Zminus1_restrict T 1 j U]
      exact mem_stopLocus_of_notMem_hplus T j hz.1 hz.2
    exact (BD.mem_Zminus1_one_iff_isHypersurfaceIdealAt (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      hH hleU hz.1).mp hzZ
  -- `OutputClause.pushforward` on the lifted lower run
  have hP := FiniteSuccession.OutputClause.pushforward hSU
    (coreModTraceLift R T j hT U hU).toSuccession hF₀ hFS₀ hmax' hL' hH hSH hcl hleU hFH hstop
    hO'
  have hge₀ := FiniteSuccession.pushforward_isOfOrderGe_of_isOfOrderGe_traceFamily
    (T := (coreModTraceLift R T j hT U hU).toSuccession) hSU hI hmax' hF₀ hFS₀ hL'
  have hLne : (coreModTraceLift R T j hT U hU).NoEmptyCenters :=
    BlowUpSequence.noEmptyCenters_pullback_of_surjective _ _ _
      ((isClosedSubmanifold_hplus T j).restrictBundleDiffeomorph U).symm.surjective
      ((R.fam (restrictedTripleMod T j) (bmoClass_restrictedTripleMod T j hT)).noEmptyCenters _ _)
  -- the list push-forward's succession is the succession's push-forward; the deletion of the empty
  -- blow-ups
  unfold coreModOn
  rw [BlowUpSequence.pushforwardRestrict_eq]
  change ((coreModTraceLift R T j hT U hU).pushforward
    ((isClosedSubmanifold_hplus T j).restrictOpen U)).eraseEmpty.toSuccession.OutputClause _ _ _
  have hbr := pushforwardBridge (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    ((isClosedSubmanifold_hplus T j).restrictOpen U) (coreModTraceLift R T j hT U hU) hLne
  exact BlowUpSequence.outputClause_eraseEmpty (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) _
    (⟨(T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I,
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isNonzeroEverywhere,
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.emptyMember j, hF₀⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict U))
    (by rw [hbr]; exact hge₀) (by rw [hbr]; exact hP)

variable {T j U hU} (hRc : R.CommutesWithLocalIsos) (hRi : R.IndifferentToEmptyMembers)

/-- **The order clause of the data of the modified first step with respect to `E − Eʲ`**
(`hFamDataMod`). -/
theorem hFamDataMod_isOfOrderGeEmptyMemberFam :
    (hFamDataMod R hRo hRc hRi).IsOfOrderGeEmptyMemberFam := by
  unfold HFamData.IsOfOrderGeEmptyMemberFam
  intro N T hT j _hle U hU
  exact coreModOn_isOfOrderGe_emptyMember R T j ⟨hT.1, hT.2.2⟩ U hU hRo hT.2.1

/-- **The stopped clause of the data of the modified first step** (`hFamDataMod`, from the clause
`hR8` of the functor one dimension down). -/
theorem hFamDataMod_stoppedClauseFam
    (hR8 : R.StoppedClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))) :
    (hFamDataMod R hRo hRc hRi).StoppedClauseFam := by
  unfold HFamData.StoppedClauseFam
  intro N T hT j hle U hU
  exact coreModOn_stoppedClause R T j ⟨hT.1, hT.2.2⟩ U hU hRo hT.2.1 hle hR8

/-- **The output clause of the data of the modified first step** (`hFamDataMod`, from the clause
`hR1` of the functor one dimension down). -/
theorem hFamDataMod_outputClauseFam
    (hR1 : R.OutputClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))) :
    (hFamDataMod R hRo hRc hRi).OutputClauseFam := by
  unfold HFamData.OutputClauseFam
  intro N T hT j hle U hU
  exact coreModOn_outputClause R T j ⟨hT.1, hT.2.2⟩ U hU hRo hT.2.1 hle hR1

end Hironaka.Manifold.BMOmod

end
