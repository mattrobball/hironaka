/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.ModifiedMarkedFam
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.FiniteSuccession.Restrict.GermRestrict
import Hironaka.Manifold.IdealSheaf.Identity
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Snc.Proper
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Manifold.Submanifold.Components
import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Resolution.Analytic.MaximalContact.CommonCharts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial


/-!
# The stop predicate: persistence off the centres, and the stopped germ

The structure `BMOmodFam` carries two clauses about the predicate
`IsSmoothTransversalIdealAt ψ F J x`, "`J` is at `x` locally the ideal of a smooth submanifold with
coordinates transversal to `F`" (the output of the modified algorithm, locally equal to
`I″ = (u₁, …, u_k)` "where `u_i` are coordinates transversal to exceptional divisors",
[Wlo09, Theorem 7.4.1]): the output of the modified functor satisfies it at every point of the
support, and a point at which it holds and which lies on no boundary member is never blown up
again. Both proofs walk the succession past the point: one needs to know that the predicate, once
true at a point off the centres, stays true at the points over it, and that no exceptional divisor
ever passes through them. This module proves those persistence facts and the two germ facts of the
stopped case, at a general model `ψ`:

* Locality and transport. `IsSmoothTransversalIdealAt.congr_nhds`: the predicate at `x` depends
  only on the members through `x` near `x` and on the stalks near `x`; the chart with simple normal
  crossings is restricted to the open set where the data agree (`IsSncChartAt.restrOpen`), its
  coordinate germs unchanged (`coord_eq_coord_of_eventuallyEq`).
  `IsSmoothTransversalIdealAt.comap`: the predicate transports along a local analytic isomorphism
  `g` at `y`; the chart at `g y` is composed with the local inverse (`transportChart`), the
  coordinate germs pulled back (`germMap_coord_eq_coord_transportChart`), the stalks of `comap g J`
  the images of the stalks of `J` (`stalkIdeal_comap_eq_map_germMap`).
* One blow-up off the centre (a blow-up is an isomorphism off its centre, and the exceptional
  divisor lies over the centre). `IsSmoothTransversalIdealAt.totalTransform_of_notMem`: for
  `π y ∉ Y` and `𝓘` of order `≥ 1` along `Y`, the predicate for `(E, 𝓘)` at `π y` gives it for the
  total transform of `E` and the marked transform of `(𝓘, 1)` at `y`; transport along
  `IsBlowUp.isLocalDiffeomorphOn_compl`, then locality on `π⁻¹(Yᶜ)`, where the marked transform is
  the pull-back (`birationalTransform_stalkIdeal_of_notMem`) and the strict transforms of the
  members through `π y` are their preimages (`mem_strictTransformSet_iff_of_notMem`), the
  exceptional member missing `y`. `notMem_totalTransform_of_notMem`: a point off the exceptional
  divisor whose image is on no member is on no member of the total transform.
* Along a succession. `FiniteSuccession.notMem_totalTransformSeqFrom_of_forall_notMem_center`: a
  point `y` at stage `i + k` over `x` at stage `i` (`stageMapAdd`), with `x` on no member of `E_i`
  and no intermediate centre containing a point over `x`, is on no member of `E_{i+k}`; induction on
  `k` with the previous fact at each stage, the boundaries having simple normal crossings by
  `isSnc_totalTransformSeqFrom_and_boundarySeq_eq` from the normal-crossings clause of
  `IsOfOrderGe`. The hypothesis quantifies over all points over `x` at the intermediate stages, the
  form the induction for the second clause produces.
* The stopped germ ("if `I′ = (u)` is the ideal of smooth hypersurface … the algorithm is stopped",
  [Wlo09, Theorem 7.4.1]). `ord_le_one_of_isSmoothTransversalIdealAt`: at a point where the
  predicate holds with nonzero stalk, `ord J ≤ 1`, a coordinate germ lying in `J_x ∖ 𝔪_x²`
  (`coord_notMem_maximalIdeal_sq`). `isSmoothTransversalIdealAt_of_eq_idealSheaf`: if `𝓘` is the
  ideal sheaf of the smooth hypersurface `H` near `y ∈ H` and no member passes through `y`, the
  predicate holds with `c = 1`; an adapted chart of `H` restricted to where the sheaves agree,
  `𝓘_a = (z_{σ 0})` on `H` (`stalkIdeal_idealSheaf_eq_span`), `= ⊤` off `H` (the coordinate a unit
  there).
* The stopped locus. `BD.mem_Zminus1_one_iff_isHypersurfaceIdealAt`: for `H` of maximal contact at
  the mark `1` (`𝓘_H ≤ 𝓘`, [Wlo09, Lemma 5.5.1 (1)]) and `x ∈ H`, `x ∈ Z_{-1}(𝓘, 1, H)` (the
  component of `x` in `H` lies in `{ord 𝓘 ≥ 1}`, `BD.Zminus1`) iff `𝓘 = 𝓘_H` stalkwise near `x`, the
  germ characterisation which the previous fact uses. Both directions read the stalks of `𝓘|_H`
  through `IsClosedSubmanifold.stalkIdeal_pullback_inclusionMap_eq_bot_iff` (the restriction of
  germs: `(𝓘|_H)_a = 0 ⇔ 𝓘_a ≤ (𝓘_H)_a`) and
  `IdealSheaf.stalkIdeal_eq_bot_of_eventually_mem_support` (a cosupport containing a neighbourhood
  of `a` forces a zero stalk). Backwards, `{(𝓘|_H)_a = 0}` is clopen in `H`
  (`isClopen_setOf_stalkIdeal_eq_bot`, the identity theorem) and contains the component; forwards,
  on an adapted chart of `H` at `x` meeting `H` inside the component
  (`exists_adaptedChart_source_inter_subset`), `ord 𝓘 ≥ 1` on `H` puts a whole neighbourhood into
  the cosupport of `𝓘|_H`.

The restriction of the predicate to the hypersurface of maximal contact and back
(`restrict_maximalContact`, `of_restrict_maximalContact`) is `StopRestrict.lean`.
-/

public section


noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Filter
open scoped Manifold ContDiff

universe u

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M N : AnalyticManifold.{u} 𝕜 E}

/-! ### Locality and transport of the predicate -/

/-- **The locality of the predicate**: the predicate at `x` depends only on the members through `x`
near `x` (an equivalence `e` of the members through `x`, equal on an open `U ∋ x`) and on the stalks
of the ideal on `U`; the chart with simple normal crossings is restricted to `U`
(`IsSncChartAt.restrOpen`), its coordinate germs are those of the chart
(`coord_eq_coord_of_eventuallyEq`). -/
theorem HypersurfaceFamily.IsSmoothTransversalIdealAt.congr_nhds {F₁ F₂ : HypersurfaceFamily M}
    {J₁ J₂ : AnalyticManifold.IdealSheaf M} {x : M} {U : Set M} (hU : IsOpen U) (hxU : x ∈ U)
    (e : {j // x ∈ F₁.hyp j} ≃ {j // x ∈ F₂.hyp j})
    (he : ∀ j, F₂.hyp (e j).1 ∩ U = F₁.hyp j.1 ∩ U)
    (hJ : ∀ a ∈ U, J₁.stalkIdeal a = J₂.stalkIdeal a)
    (h : F₁.IsSmoothTransversalIdealAt ψ J₁ x) : F₂.IsSmoothTransversalIdealAt ψ J₂ x := by
  obtain ⟨c, φ, σ, cidx, hφ, hJ₁, hne⟩ := h
  have hφ' : F₁.IsSncChartAt ψ (φ.restrOpen U hU) x cidx := hφ.restrOpen hU hxU
  refine ⟨c, φ.restrOpen U hU, σ, cidx ∘ e.symm,
    ⟨hφ'.1, hφ'.2.1, fun j a ha => ?_, hφ'.2.2.2.comp e.symm.injective⟩, fun a ha => ?_,
    fun j i => hne (e.symm j) i⟩
  · have hs : F₂.hyp j.1 ∩ U = F₁.hyp (e.symm j).1 ∩ U := by
      have := he (e.symm j)
      rwa [Equiv.apply_symm_apply] at this
    have h1 : a ∈ F₂.hyp j.1 ↔ a ∈ F₁.hyp (e.symm j).1 :=
      ⟨fun hj => ((Set.ext_iff.mp hs a).mp ⟨hj, ha.2⟩).1,
        fun hj => ((Set.ext_iff.mp hs a).mpr ⟨hj, ha.2⟩).1⟩
    rw [h1]
    exact hφ'.2.2.1 (e.symm j) a ha
  · rw [← hJ a ha.2, hJ₁ a ha.1]
    refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
    exact coord_eq_coord_of_eventuallyEq E hφ.1 ha.1 hφ'.1 ha
      (Filter.Eventually.of_forall fun _ => rfl)

/-- The predicate transports along a local analytic isomorphism `g` at `y`: the chart at `g y`
composed with the local inverse (`transportChart`, `transportChart_mem_maximalAtlas`), the
coordinate germs pulled back (`germMap_coord_eq_coord_transportChart`), the stalks of `comap g J`
the images of the stalks of `J` (`stalkIdeal_comap_eq_map_germMap`, `Ideal.map_span`); the members
through `y` of `F.comap g` are those of `F` through `g y`. -/
theorem HypersurfaceFamily.IsSmoothTransversalIdealAt.comap (F : HypersurfaceFamily M)
    (J : AnalyticManifold.IdealSheaf M) (g : AnalyticMap N M) {y : N}
    (hg : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω g y)
    (h : F.IsSmoothTransversalIdealAt ψ J (g y)) :
    (F.comap ⇑g).IsSmoothTransversalIdealAt ψ (J.pullback g g.contMDiff) y := by
  obtain ⟨Φ, hyΦ, hΦ⟩ := hg.exists_partialDiffeomorph
  obtain ⟨c, φ, σ, cidx, hφ, hJ, hne⟩ := h
  have hgy : g y ∈ φ.source := hφ.2.1
  have hφ' : transportChart Φ.symm φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω N :=
    transportChart_mem_maximalAtlas Φ.symm hφ.1
  have hsrc : ∀ a, a ∈ (transportChart Φ.symm φ).source ↔ a ∈ Φ.source ∧ g a ∈ φ.source := by
    intro a
    rw [transportChart_source]
    change a ∈ Φ.source ∧ Φ a ∈ φ.source ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [hΦ h1]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [← hΦ h1]⟩
  have hy' : y ∈ (transportChart Φ.symm φ).source := (hsrc y).mpr ⟨hyΦ, hgy⟩
  refine ⟨c, transportChart Φ.symm φ, σ, cidx, ⟨hφ', hy', fun j a ha => ?_, hφ.2.2.2⟩,
    fun a ha => ?_, hne⟩
  · obtain ⟨haΦ, hga⟩ := (hsrc a).mp ha
    change g a ∈ F.hyp j.1 ↔ ψ (φ (Φ a)) (cidx j) = 0
    rw [← hΦ haΦ]
    exact hφ.2.2.1 j (g a) hga
  · obtain ⟨haΦ, hga⟩ := (hsrc a).mp ha
    rw [stalkIdeal_comap_eq_map_germMap, hJ (g a) hga, Ideal.map_span, ← Set.range_comp]
    refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
    exact germMap_coord_eq_coord_transportChart ψ g Φ hΦ haΦ φ hφ.1 hga hφ' ha (σ i)

/-- One blow-up, off the centre: for a blow-up `π` with centre `Y` (any model `ψ₁`), an ideal sheaf
`𝓘` of order `≥ 1` along `Y` (the hypothesis `hJ`, the standing condition for the marked transform
of `(𝓘, 1)`) and a point `y` with `π y ∉ Y`, the predicate for `(E, 𝓘)` at `π y` gives the predicate
for the total transform of `E` and the marked transform of `(𝓘, 1)` at `y`. The blow-up is a local
analytic isomorphism at `y` (`IsBlowUp.isLocalDiffeomorphOn_compl`), the marked transform is the
pull-back off the centre (`birationalTransform_stalkIdeal_of_notMem`), the strict transforms of the
members through `π y` are their preimages near `y` (`mem_strictTransformSet_iff_of_notMem`) and the
exceptional member misses `y`: transport, then locality. -/
theorem HypersurfaceFamily.IsSmoothTransversalIdealAt.totalTransform_of_notMem {n₁ : ℕ}
    {ψ₁ : E ≃L[𝕜] (Fin n₁ → 𝕜)} {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₁ Y c)
    {M' : AnalyticManifold.{u} 𝕜 E} {π : M' → M} (h : IsBlowUp ψ₁ Y c π)
    {F : HypersurfaceFamily M} (hF : F.IsSnc ψ) {J : AnalyticManifold.IdealSheaf M}
    (hJ : ∀ a ∈ Y, (1 : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a) {y : M'} (hy : π y ∉ Y)
    (hP : F.IsSmoothTransversalIdealAt ψ J (π y)) :
    (F.totalTransform π Y).IsSmoothTransversalIdealAt ψ
      (MarkedIdealSheaf.birationalTransform hY h ⟨J, 1⟩).I y := by
  let g : AnalyticMap M' M := ⟨π, h.contMDiff⟩
  have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω g y :=
    h.isLocalDiffeomorphOn_compl ⟨y, hy⟩
  have hP' := HypersurfaceFamily.IsSmoothTransversalIdealAt.comap ψ F J g hloc hP
  have hU : IsOpen (π ⁻¹' Yᶜ) := hY.isClosed.isOpen_compl.preimage h.contMDiff.continuous
  have hst : ∀ (j : F.ι) {a : M'}, π a ∉ Y →
      (a ∈ strictTransformSet π Y (F.hyp j) ↔ π a ∈ F.hyp j) := fun j _ ha =>
    mem_strictTransformSet_iff_of_notMem h.contMDiff.continuous (hF.1 j).isClosed ha
  let f : {j // y ∈ (F.comap ⇑g).hyp j} → {j // y ∈ (F.totalTransform π Y).hyp j} :=
    fun j => ⟨toLex (Sum.inl j.1), (hst j.1 hy).mpr j.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro j j' hjj'
      exact Subtype.ext (Sum.inl_injective (toLex.injective (congrArg Subtype.val hjj')))
    · rintro ⟨k, hk⟩
      obtain ⟨k, rfl⟩ : ∃ k' : F.ι ⊕ PUnit.{u + 1}, toLex k' = k := ⟨ofLex k, toLex_ofLex k⟩
      rcases k with j | u
      · exact ⟨⟨j, (hst j hy).mp hk⟩, rfl⟩
      · exact absurd hk hy
  have hJ' : ∀ a ∈ Y, ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a := fun a ha => by
    rw [Nat.cast_one]
    exact hJ a ha
  refine HypersurfaceFamily.IsSmoothTransversalIdealAt.congr_nhds ψ hU hy (Equiv.ofBijective f hf)
    (fun j => ?_) (fun a ha => ?_) hP'
  · change strictTransformSet π Y (F.hyp j.1) ∩ π ⁻¹' Yᶜ = π ⁻¹' F.hyp j.1 ∩ π ⁻¹' Yᶜ
    ext a
    exact ⟨fun ha => ⟨(hst j.1 ha.2).mp ha.1, ha.2⟩, fun ha => ⟨(hst j.1 ha.2).mpr ha.1, ha.2⟩⟩
  · exact (birationalTransform_stalkIdeal_of_notMem hY h hJ' ha).symm

/-- One step along a succession: a point `y` off the exceptional divisor whose image lies on no
member of `E` lies on no member of the total transform of `E`; the strict transform of a member is
its preimage off the centre (`mem_strictTransformSet_iff_of_notMem`), the exceptional member is
`π⁻¹(Y)`. -/
theorem HypersurfaceFamily.notMem_totalTransform_of_notMem {n₁ : ℕ} {ψ₁ : E ≃L[𝕜] (Fin n₁ → 𝕜)}
    {Y : Set M} {c : ℕ} {M' : AnalyticManifold.{u} 𝕜 E} {π : M' → M} (h : IsBlowUp ψ₁ Y c π)
    {F : HypersurfaceFamily M} (hF : F.IsSnc ψ) {y : M'} (hy : π y ∉ Y)
    (hx : ∀ j, π y ∉ F.hyp j) : ∀ j, y ∉ (F.totalTransform π Y).hyp j := by
  intro j
  obtain ⟨j, rfl⟩ : ∃ j' : F.ι ⊕ PUnit.{u + 1}, toLex j' = j := ⟨ofLex j, toLex_ofLex j⟩
  rcases j with k | u
  · change y ∉ strictTransformSet π Y (F.hyp k)
    rw [mem_strictTransformSet_iff_of_notMem h.contMDiff.continuous (hF.1 k).isClosed hy]
    exact hx k
  · exact hy

end Manifold

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E}

/-- Along a succession, a point `y` at stage `i + k` over `x` (`stageMapAdd`), with `x` on no member
of the boundary `E_i` and no intermediate centre containing a point over `x`, lies on no member of
`E_{i+k}`: induction on `k` with `notMem_totalTransform_of_notMem` at each stage
(`totalTransformSeqFrom_succ`, `stageMapAdd_succ`; the boundaries have simple normal crossings by
`isSnc_totalTransformSeqFrom_and_boundarySeq_eq` from the normal-crossings clause `h3`). -/
theorem notMem_totalTransformSeqFrom_of_forall_notMem_center
    (S : FiniteSuccession M) {F : HypersurfaceFamily M} (hF : F.IsSnc ψ)
    (h3 : ∀ i : Fin S.length, (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E))
      i.castSucc).HasOnlyNormalCrossingsWith (S.center i))
    (i k : ℕ) (h : i + k < S.length + 1)
    {x : S.stage ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩}
    (hx : ∀ j,
      x ∉ (S.totalTransformSeqFrom F ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩).hyp j)
    (hcen : ∀ (l : ℕ) (hl : l < k)
      (z : S.stage ⟨i + l, Nat.lt_of_le_of_lt (Nat.add_le_add_left hl.le i) h⟩),
      S.stageMapAdd i l (Nat.lt_of_le_of_lt (Nat.add_le_add_left hl.le i) h) z = x →
        z ∉ (S.center ⟨i + l, Nat.lt_of_lt_of_le (Nat.add_lt_add_left hl i)
          (Nat.lt_succ_iff.mp h)⟩).support)
    (y : S.stage ⟨i + k, h⟩) (hy : S.stageMapAdd i k h y = x) :
    ∀ j, y ∉ (S.totalTransformSeqFrom F ⟨i + k, h⟩).hyp j := by
  induction k with
  | zero =>
    intro j hj
    apply hx j
    rw [← hy]
    exact hj
  | succ k ih =>
    have hk : i + k < S.length + 1 := Nat.lt_of_succ_lt h
    have hk' : i + k < S.length := Nat.lt_of_succ_lt_succ h
    have hzx : S.stageMapAdd i k hk (S.map ⟨i + k, hk'⟩ y) = x := hy
    have hz : ∀ j, S.map ⟨i + k, hk'⟩ y ∉ (S.totalTransformSeqFrom F ⟨i + k, hk⟩).hyp j :=
      ih hk hx (fun l hl z hz => hcen l (Nat.lt_succ_of_lt hl) z hz) _ hzx
    have hzc : S.map ⟨i + k, hk'⟩ y ∉ (S.center ⟨i + k, hk'⟩).support :=
      hcen k (Nat.lt_succ_self k) _ hzx
    exact HypersurfaceFamily.notMem_totalTransform_of_notMem ψ (S.isBlowUp_map ⟨i + k, hk'⟩)
      (S.isSnc_totalTransformSeqFrom_and_boundarySeq_eq (ψ := ψ) hF h3 ⟨i + k, hk⟩).1 hzc hz

end AnalyticManifold.FiniteSuccession

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M N : AnalyticManifold.{u} 𝕜 E}

/-- At a point where the predicate holds the ideal is spanned by coordinates of a chart (`c = 0`
excluded by a nonzero stalk), so its order is at most `1`: the coordinate `z_{σ 0}` lies in
`J_x ∖ 𝔪_x²` (`coord_notMem_maximalIdeal_sq`). -/
theorem _root_.Hironaka.Manifold.ord_le_one_of_isSmoothTransversalIdealAt {F : HypersurfaceFamily M}
    {J : AnalyticManifold.IdealSheaf M} {x : M} (hJ : J.stalkIdeal x ≠ ⊥)
    (h : F.IsSmoothTransversalIdealAt ψ J x) : J.ord x ≤ 1 := by
  obtain ⟨c, φ, σ, cidx, hφ, hJx, -⟩ := h
  have hx : J.stalkIdeal x = Ideal.span (Set.range fun i => coord E ψ φ hφ.1 hφ.2.1 (σ i)) :=
    hJx x hφ.2.1
  rcases c with _ | c
  · rw [Set.range_eq_empty, Ideal.span_empty] at hx
    exact absurd hx hJ
  · by_contra hlt
    rw [not_le] at hlt
    have h2 : (2 : ℕ∞) ≤ J.ord x := by
      have h11 : (1 : ℕ∞) + 1 ≤ J.ord x := Order.add_one_le_of_lt hlt
      rwa [one_add_one_eq_two] at h11
    have hle : J.stalkIdeal x ≤ IsLocalRing.maximalIdeal _ ^ 2 :=
      (IsLocalRing.le_ord_iff (r := 2)).mp h2
    have hmem : coord E ψ φ hφ.1 hφ.2.1 (σ 0) ∈ J.stalkIdeal x :=
      hx ▸ Ideal.subset_span ⟨0, rfl⟩
    exact coord_notMem_maximalIdeal_sq φ hφ.1 hφ.2.1 (hle hmem)

/-! ### The stopped case and the germ characterisation of the stopped locus -/

/-- The stopped case ("if `I′ = (u)` is the ideal of smooth hypersurface … the algorithm is
stopped", [Wlo09, Theorem 7.4.1]): if `𝓘` is the ideal sheaf of the smooth hypersurface `H` near
`y ∈ H` and no member of `E` passes through `y`, the predicate holds at `y` with `c = 1`. An adapted
chart of `H` at `y` (`exists_adaptedChart`) is restricted to where the two ideal sheaves agree
(`IsAdaptedChart.restrOpen'`); `𝓘_a = (z_{σ 0})` at the points of `H`
(`IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_span`) and `= ⊤ = (z_{σ 0})` off `H` (the coordinate
a unit there, `isUnit_coord_of_ne_zero`); no member passes through `y`, so the clause on the
members of the chart has nothing to check. -/
theorem HypersurfaceFamily.isSmoothTransversalIdealAt_of_eq_idealSheaf {H : Set M}
    (hH : IsClosedSubmanifold ψ H 1) {F : HypersurfaceFamily M}
        {J : AnalyticManifold.IdealSheaf M}
    {y : M} (hy : y ∈ H) (hJ : ∀ᶠ a in 𝓝 y, J.stalkIdeal a = hH.idealSheaf.stalkIdeal a)
    (hF : ∀ j, y ∉ F.hyp j) : F.IsSmoothTransversalIdealAt ψ J y := by
  obtain ⟨φ₀, σ, hyφ, hφ₀⟩ := hH.exists_adaptedChart y hy
  obtain ⟨U, hUJ, hUo, hyU⟩ := eventually_nhds_iff.mp hJ
  have hφ : IsAdaptedChart ψ H (φ₀.restrOpen U hUo) σ := hφ₀.restrOpen' U hUo
  have hyφ' : y ∈ (φ₀.restrOpen U hUo).source := ⟨hyφ, hyU⟩
  refine ⟨1, φ₀.restrOpen U hUo, σ, fun j => (hF j.1 j.2).elim,
    ⟨hφ.1, hyφ', fun j => (hF j.1 j.2).elim, fun j => (hF j.1 j.2).elim⟩, fun a ha => ?_,
    fun j => (hF j.1 j.2).elim⟩
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
    exact isUnit_coord_of_ne_zero (φ₀.restrOpen U hUo) hφ.1 ha hne

variable {ψ} in
/-- The restriction of germs to a closed submanifold: the pull-back of `J` to the bundled closed
submanifold `S` has zero stalk at `a ∈ S` iff the stalk of `J` at `a` lies in the vanishing ideal of
`S` there (`stalkIdeal_pullback`, `Ideal.map_eq_bot_iff_le_ker`, `germMap_inclusionMap`, the germ
map of the inclusion being `restrictStalk`; `stalkIdeal_idealSheaf_of_mem`, the kernel form of
`𝓘_S`). -/
theorem IsClosedSubmanifold.stalkIdeal_pullback_inclusionMap_eq_bot_iff {S : Set M} {s : ℕ}
    (hS : IsClosedSubmanifold ψ S s) (J : AnalyticManifold.IdealSheaf M) {a : M} (ha : a ∈ S) :
    (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).stalkIdeal
        ((⟨a, ha⟩ : S) : hS.toAnalyticManifold) = ⊥ ↔
      J.stalkIdeal a ≤ hS.idealSheaf.stalkIdeal a := by
  set p : hS.toAnalyticManifold := ((⟨a, ha⟩ : S) : hS.toAnalyticManifold) with hp
  rw [IdealSheaf.stalkIdeal_pullback, Ideal.map_eq_bot_iff_le_ker, hS.germMap_inclusionMap p,
    hS.stalkIdeal_idealSheaf_of_mem ha]
  exact Iff.rfl

/-- The identity of germs, in neighbourhood form: an ideal sheaf whose cosupport contains a
neighbourhood of `a` has zero stalk at `a`; its local generators vanish at every point near `a`
(`mem_cosupport_iff_forall_eq_zero`), so their germs are zero (`germ_eq_zero_iff`). -/
theorem IdealSheaf.stalkIdeal_eq_bot_of_eventually_mem_support {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {X : Type u} [TopologicalSpace X]
    [ChartedSpace E' X] (J : IdealSheaf (structureSheaf 𝕜 E' X)) {a : X}
    (h : ∀ᶠ b in 𝓝 a, b ∈ J.support) : J.stalkIdeal a = ⊥ := by
  obtain ⟨U, ha, k, f, -, hgen⟩ := J.exists_generators a
  rw [hgen a ha, Ideal.span_eq_bot]
  rintro _ ⟨i, rfl⟩
  rw [germ_eq_zero_iff]
  filter_upwards [h, U.2.mem_nhds ha] with b hb hbU
  rw [extendSection_of_mem 𝕜 E' _ hbU]
  exact (J.mem_support_iff_forall_eq_zero hgen hbU).mp hb i

/-- **The germ characterisation of the stopped locus at the mark `1`** ([Wlo09, Theorem 7.4.1],
"the algorithm is stopped"; the maximal-contact element lies in the ideal at `µ = 1`,
[Wlo09, Lemma 5.5.1 (1)]): for a smooth hypersurface `H` of maximal contact at the mark `1`
(`𝓘_H ≤ 𝓘`) and `x ∈ H`, `x ∈ Z_{-1}` (the connected component of `x` in `H` lies in `{ord 𝓘 ≥ 1}`,
`BD.Zminus1`) iff `𝓘` is the ideal sheaf of `H` near `x`. Both directions read the stalks of `𝓘|_H`
through `stalkIdeal_pullback_inclusionMap_eq_bot_iff` (`(𝓘|_H)_a = 0 ⇔ 𝓘_a ≤ 𝓘_{H,a}`, hence
`⇔ 𝓘_a = 𝓘_{H,a}` under `𝓘_H ≤ 𝓘`). Forwards, an adapted chart of `H` at `x` whose source meets `H`
inside the component (`exists_adaptedChart_source_inter_subset`): on the source, off `H` both stalks
are the unit ideal, and at `a ∈ H` every point of `H` near `a` has `ord 𝓘 ≥ 1`, so `𝓘|_H` has the
whole neighbourhood in its cosupport and zero stalk at `a`
(`stalkIdeal_eq_bot_of_eventually_mem_cosupport`). Backwards, `(𝓘|_H)_x = 0`, and `{(𝓘|_H)_a = 0}`
is clopen in `H` (`isClopen_setOf_stalkIdeal_eq_bot`, the identity theorem), so it contains the
component, along which `𝓘_a = 𝓘_{H,a} ≠ 𝒪_a` gives `ord 𝓘 ≥ 1`. -/
theorem _root_.Hironaka.Manifold.BD.mem_Zminus1_one_iff_isHypersurfaceIdealAt {H : Set M}
    (hH : IsClosedSubmanifold ψ H 1)
    {J : AnalyticManifold.IdealSheaf M} (hle : hH.idealSheaf ≤ J) {x : M} (hx : x ∈ H) :
    x ∈ BD.Zminus1 J 1 H ↔ ∀ᶠ a in 𝓝 x, J.stalkIdeal a = hH.idealSheaf.stalkIdeal a := by
  have key : ∀ a (ha : a ∈ H),
      (J.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff).stalkIdeal
          ((⟨a, ha⟩ : H) : hH.toAnalyticManifold) = ⊥ ↔
        J.stalkIdeal a = hH.idealSheaf.stalkIdeal a := fun a ha =>
    (hH.stalkIdeal_pullback_inclusionMap_eq_bot_iff J ha).trans
      ⟨fun h => le_antisymm h (IdealSheaf.le_def.mp hle a), fun h => h.le⟩
  have hord : ∀ a ∈ H, J.stalkIdeal a = hH.idealSheaf.stalkIdeal a →
      ((1 : ℕ) : ℕ∞) ≤ J.ord a := by
    intro a ha heq
    rw [Nat.cast_one]
    refine Order.one_le_iff_ne_zero.mpr fun h0 => (IdealSheaf.ord_eq_zero_iff J).mp h0 ?_
    rw [IdealSheaf.mem_support, heq, ← IdealSheaf.mem_support, hH.cosupport_idealSheaf]
    exact ha
  constructor
  · rintro ⟨-, hZ⟩
    obtain ⟨φ, -, hxφ, -, hsub⟩ := hH.exists_adaptedChart_source_inter_subset hx
    refine Filter.eventually_of_mem (φ.open_source.mem_nhds hxφ) fun a ha => ?_
    by_cases haH : a ∈ H
    · refine (key a haH).mp ?_
      apply IdealSheaf.stalkIdeal_eq_bot_of_eventually_mem_support
      have hopen : IsOpen (⇑hH.inclusionMap ⁻¹' φ.source) :=
        φ.open_source.preimage hH.inclusionMap.contMDiff.continuous
      refine Filter.eventually_of_mem (hopen.mem_nhds ha) fun q hq => ?_
      rw [IdealSheaf.support_pullback]
      have h1 : (1 : ℕ∞) ≤ J.ord (hH.inclusionMap q) := by
        have := hZ (hsub ⟨hq, (q : H).2⟩)
        simpa using this
      exact not_not.mp fun hc =>
        Order.one_le_iff_ne_zero.mp h1 ((IdealSheaf.ord_eq_zero_iff J).mpr hc)
    · rw [hH.stalkIdeal_idealSheaf_of_notMem haH]
      refine top_le_iff.mp ?_
      rw [← hH.stalkIdeal_idealSheaf_of_notMem haH]
      exact IdealSheaf.le_def.mp hle a
  · intro hev
    refine ⟨hx, fun y hy => ?_⟩
    have hp := (key x hx).mpr hev.self_of_nhds
    have hcomp :=
      (J.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff).isClopen_setOf_stalkIdeal_eq_bot
        |>.connectedComponent_subset hp
    rw [connectedComponentIn_eq_image hx] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    exact hord q.1 q.2 ((key q.1 q.2).mp (hcomp hq))

end Manifold

end
