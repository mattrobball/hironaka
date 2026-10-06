/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.BlowUp.CoordGerm
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.StrictCharts
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.OrderReduction.BMO.SplitOrder
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial formula at a stalk, for one blow-up

Kollár's explicit formula for the principalization, `Π^* I = 𝒪(−∑ Π^*_{r,j+1} F_j)` [Kol07, 72],
is assembled stage by stage in `MonomialSeq.lean`; this module holds the facts about one
blowing-up `π : M' → M` along a centre `Y` having simple normal crossings with the boundary `F`:

* **exact division at mark `1`** ([Kol07, (60.1)]): the total transform of an ideal sheaf `J` of
  order `≥ 1` along `Y` is the exceptional ideal times the marked transform,
  `π⁻¹(J) = I_F · π_*^{-1}(J, 1)` at every stalk
  (`stalkIdeal_totalTransform_eq_mul_birationalTransform`) — the marked transform's stalk is the
  colon `(π⁻¹(J)_p : I_{F,p})` and `π⁻¹(J)_p ⊆ I_{F,p}` because `J_a ⊆ I_{Y,a}` on the centre, so
  the colon by the principal ideal `I_{F,p} = (u)` divides exactly
  (`Ideal.span_singleton_mul_colon_of_le`);
* the stalks of the exceptional ideal are the vanishing ideals of the exceptional divisor
  (`IsBlowUp.stalkIdeal_exceptionalIdealSheaf_eq_vanishingStalk`; more generally an ideal sheaf of
  a closed submanifold has its vanishing ideals as stalks,
  `IsIdealSheafOf.stalkIdeal_eq_vanishingStalk`);
* **the transport of a boundary member**: the vanishing ideal of a member `E^j` through `π p`
  pulls back along `π` to `I_{F,p}^ε` times the vanishing ideal of its strict transform,
  `ε ∈ {0, 1}` (`exists_map_germMap_vanishingStalk_hyp_eq'`). In a blow-up chart of index `i` over
  an adapted chart (`germMap_coord_self`, `germMap_coord_of_ne`, `germMap_coord_off`): the
  coordinate `z_{c j}` of the member pulls back to `u_i` when `c j = σ i` (the strict transform
  misses the chart, `ε = 1`), to `u_i · u_{c j}` for a block coordinate `c j = σ k`, `k ≠ i`
  (`ε = 1`), and to `u_{c j}` off the block (`ε = 0`); in each case the strict transform is the
  zero set of `u_{c j}` in the chart (`strictTransform_inter_source_self`, `_of_ne`, `_off`), so
  its vanishing ideal is `(u_{c j})`. Off the exceptional divisor the blowing-up is a local
  isomorphism (condition (1) of [BM88, Definition 4.1]), the strict transform is the preimage there
  and the vanishing ideal pulls back along the bijective germ map (`ε = 0`).

This is the computation behind Bierstone–Milman's remark that when the centre and the boundary
"simultaneously have only normal crossings", the transformed boundary is again a collection of
smooth hypersurfaces having only normal crossings [BM97, (1.2)], and behind the total transform of
a divisor in [Kol07, Definition 25].
-/

public section

universe u

open TopologicalSpace Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Vanishing ideals of closed hypersurfaces -/

section Vanishing

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- The vanishing ideal at `x` sees only the germ of the set: `Z ∩ t = Z` near `x` for a
neighbourhood `t` of `x`. -/
theorem vanishingStalk_inter_of_mem_nhds {Z t : Set M} {x : M} (ht : t ∈ 𝓝 x) :
    vanishingStalk (𝕜 := 𝕜) (E := E) (Z ∩ t) x = vanishingStalk (𝕜 := 𝕜) (E := E) Z x := by
  ext s
  rw [mem_vanishingStalk_iff, mem_vanishingStalk_iff]
  generalize stalkToGerm 𝓘(𝕜, E) ω M x s = g
  induction g using Filter.Germ.inductionOn with
  | h f =>
    rw [Germ.vanishesOn_coe, Germ.vanishesOn_coe,
      nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds ht)]

/-- Off a closed set the vanishing ideal is the unit ideal. -/
theorem vanishingStalk_eq_top_of_notMem {Z : Set M} (hZ : IsClosed Z) {x : M} (hx : x ∉ Z) :
    vanishingStalk (𝕜 := 𝕜) (E := E) Z x = ⊤ :=
  vanishingStalk_eq_top_of_notMem_closure (by rwa [hZ.closure_eq])

/-- In a chart adapted to a closed hypersurface `Z`, the vanishing ideal of `Z` at a point of the
chart is spanned by the adapted coordinate — also off `Z`, where the coordinate is a unit and both
sides are the unit ideal. -/
theorem _root_.Manifold.IsClosedSubmanifold.vanishingStalk_eq_span_coord {Z : Set M}
    (hZ : IsClosedSubmanifold ψ Z 1) {φ : OpenPartialHomeomorph M E} {σ : Fin 1 ↪ Fin n}
    (hφ : IsAdaptedChart ψ Z φ σ) {p : M} (hp : p ∈ φ.source) :
    vanishingStalk (𝕜 := 𝕜) (E := E) Z p = Ideal.span {coord E ψ φ hφ.1 hp (σ 0)} := by
  by_cases hpZ : p ∈ Z
  · rw [← hZ.ker_restrictStalk_eq_vanishingStalk hpZ, hZ.ker_restrictStalk_eq_span hpZ hφ hp,
      Set.range_unique]
    rfl
  · rw [vanishingStalk_eq_top_of_notMem hZ.isClosed hpZ, eq_comm, Ideal.span_singleton_eq_top]
    refine isUnit_coord_of_ne_zero φ hφ.1 hp fun h0 => hpZ ((hφ.2 p hp).mpr fun i => ?_)
    rw [Subsingleton.elim i 0]
    exact h0

/-- The vanishing ideal of a closed hypersurface `Z` at a point of a chart in which `Z` is the zero
set of the coordinate `k`. -/
theorem _root_.Manifold.IsClosedSubmanifold.vanishingStalk_eq_span_coord_of_inter_source {Z : Set M}
    (hZ : IsClosedSubmanifold ψ Z 1) {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {k : Fin n}
    (hS : ∀ x ∈ φ.source, x ∈ Z ↔ ψ (φ x) k = 0) {p : M} (hp : p ∈ φ.source) :
    vanishingStalk (𝕜 := 𝕜) (E := E) Z p = Ideal.span {coord E ψ φ hφ hp k} :=
  hZ.vanishingStalk_eq_span_coord (isAdaptedChart_singleIdx hφ hS) hp

/-- An ideal sheaf of the closed submanifold `Y` (`IsIdealSheafOf`) has the vanishing ideals of `Y`
as stalks: the span of the adapted coordinates is the kernel of the restriction of germs, the unit
ideal off `Y`. -/
theorem _root_.Manifold.IsIdealSheafOf.stalkIdeal_eq_vanishingStalk {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) {J : IdealSheaf (structureSheaf 𝕜 E M)}
    (hJ : IsIdealSheafOf ψ Y c J) (a : M) :
    J.stalkIdeal a = vanishingStalk (𝕜 := 𝕜) (E := E) Y a := by
  by_cases ha : a ∈ Y
  · obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
    rw [hJ.2 φ σ hφ a haφ ha, ← hY.ker_restrictStalk_eq_span ha hφ haφ,
      hY.ker_restrictStalk_eq_vanishingStalk ha]
  · rw [hJ.stalkIdeal_of_notMem ha, vanishingStalk_eq_top_of_notMem hY.isClosed ha]

/-- The ideal sheaf of a closed submanifold has the vanishing ideals as stalks. -/
theorem _root_.Manifold.IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_vanishingStalk
    {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c) (a : M) :
    hY.idealSheaf.stalkIdeal a = vanishingStalk (𝕜 := 𝕜) (E := E) Y a :=
  hY.isIdealSheafOf_idealSheaf.stalkIdeal_eq_vanishingStalk hY a

/-- A closed hypersurface has principal vanishing ideals (the adapted coordinate on it, `1` off
it). -/
theorem _root_.Manifold.IsClosedSubmanifold.exists_vanishingStalk_eq_span_singleton {Z : Set M}
    (hZ : IsClosedSubmanifold ψ Z 1) (p : M) :
    ∃ u, vanishingStalk (𝕜 := 𝕜) (E := E) Z p = Ideal.span {u} := by
  by_cases hp : p ∈ Z
  · obtain ⟨φ, σ, hpφ, hφ⟩ := hZ.exists_adaptedChart p hp
    exact ⟨_, hZ.vanishingStalk_eq_span_coord hφ hpφ⟩
  · exact ⟨1, by rw [vanishingStalk_eq_top_of_notMem hZ.isClosed hp, Ideal.span_singleton_one]⟩

end Vanishing

/-! ### One blowing-up: exact division at mark `1` and the transport of the members -/

section BlowUp

variable {M M' : AnalyticManifold.{u} 𝕜 E} {π : M' → M} {Y : Set M} {c : ℕ}
  {F : HypersurfaceFamily M}

/-- The stalks of the exceptional ideal `I_F = π^*I_Y` are the vanishing ideals of the exceptional
divisor `π⁻¹(Y)`. -/
theorem _root_.Manifold.IsBlowUp.stalkIdeal_exceptionalIdealSheaf_eq_vanishingStalk
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (p : M') :
    (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p =
      vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' Y) p :=
  (isIdealSheafOf_exceptionalIdealSheaf hY h).stalkIdeal_eq_vanishingStalk
    (h.isClosedSubmanifold_preimage hY) p

/-- Kollár's (60.1) at mark `1`, in its exact form [Kol07, (60.1)]: when `ord_Y J ≥ 1`, the total
transform of `J` is the exceptional ideal times the marked transform at every stalk,
`π⁻¹(J)_p = I_{F,p} · π_*^{-1}(J, 1)_p` — the marked transform's stalk is the colon
`(π⁻¹(J)_p : I_{F,p})` (`isDivExceptional_birationalTransform`), `π⁻¹(J)_p ⊆ I_{F,p}` because
`J_a ⊆ I_{Y,a}` on the centre, and `I_{F,p}` is principal. -/
theorem stalkIdeal_totalTransform_eq_mul_birationalTransform (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (J : AnalyticManifold.IdealSheaf M)
    (hm : ∀ a ∈ Y, ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a) (p : M') :
    (J.pullback π h.contMDiff).stalkIdeal p =
      (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p *
        (MarkedIdealSheaf.birationalTransform hY h ⟨J, 1⟩).I.stalkIdeal p := by
  have hdiv := isDivExceptional_birationalTransform hY h ⟨J, 1⟩ hm p
  simp only [pow_one] at hdiv
  obtain ⟨u, hu⟩ :=
    (h.isClosedSubmanifold_preimage hY).exists_vanishingStalk_eq_span_singleton p
  have hexc : (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p = Ideal.span {u} :=
    (h.stalkIdeal_exceptionalIdealSheaf_eq_vanishingStalk hY p).trans hu
  have hle : (J.pullback π h.contMDiff).stalkIdeal p ≤ Ideal.span {u} := by
    rw [← hexc]
    by_cases hpY : π p ∈ Y
    · rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_pullback]
      refine Ideal.map_mono ?_
      have := (IdealSheaf.le_ordAlongIdeal_iff hY.idealSheaf J (π p) 1).mp (hm (π p) hpY)
      rwa [pow_one] at this
    · rw [stalkIdeal_exceptionalIdealSheaf_of_notMem hY h hpY]
      exact le_top
  rw [hdiv, hexc]
  exact (Ideal.span_singleton_mul_colon_of_le hle).symm

/-- The chart formulas for a boundary member: in a blow-up chart `Φ` of index `i` over a chart `φ`
adapted to `Y` which is an snc chart of `F` at `π p`, the vanishing ideal of the member `E^j`
through `π p` pulls back to `I_{F,p}^ε · (vanishing ideal of its strict transform)`, `ε = 1` iff the
member's coordinate `c j` lies in the centre's block `σ`: `z_{σ i} ∘ π = u_i` (the strict
transform misses the chart), `z_{σ k} ∘ π = u_i · u_{σ k}` for `k ≠ i`, and `z_j ∘ π = u_j` off the
block, the strict transform being `{u_{c j} = 0}` in the chart in the last two cases. -/
theorem exists_map_germMap_vanishingStalk_hyp_eq (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) (hsnc : F.HasSncWith ψ Y c)
    {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} (hφ : IsAdaptedChart ψ Y φ σ) {p : M'}
    {cidx : {j // π p ∈ F.hyp j} → Fin n} (hc : F.IsSncChartAt ψ φ (π p) cidx) {i : Fin c}
    {Φ : OpenPartialHomeomorph M' E} (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hp : p ∈ Φ.source)
    (j : {j // π p ∈ F.hyp j}) :
    ∃ ε ≤ 1, Ideal.map (germMap π h.contMDiff p)
        (vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j.1) (π p)) =
      vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' Y) p ^ ε *
        vanishingStalk (𝕜 := 𝕜) (E := E)
          ((F.totalTransform π Y).hyp (toLex (Sum.inl j.1))) p := by
  have hπp : π p ∈ φ.source := hΦ.source_subset hp
  have hT := HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc
  have hstrict : IsClosedSubmanifold ψ (strictTransformSet π Y (F.hyp j.1)) 1 :=
    hT.1 (toLex (Sum.inl j.1))
  have hexc : vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' Y) p =
      Ideal.span {coord E ψ Φ hΦ.mem_maximalAtlas hp (σ i)} :=
    (h.isClosedSubmanifold_preimage hY).vanishingStalk_eq_span_coord
      (hΦ.isAdaptedChart_preimage hφ) hp
  have hvS : vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j.1) (π p) =
      Ideal.span {coord E ψ φ hφ.1 hπp (cidx j)} :=
    (hF.1 j.1).vanishingStalk_eq_span_coord (hc.isAdaptedChart_hyp j) hπp
  have hH : ∀ x ∈ φ.source, x ∈ F.hyp j.1 ↔ ψ (φ x) (cidx j) = 0 := fun x hx => hc.mem_iff j hx
  rw [hvS, Ideal.map_span, Set.image_singleton]
  change ∃ ε ≤ 1, _ = _ ^ ε *
    vanishingStalk (𝕜 := 𝕜) (E := E) (strictTransformSet π Y (F.hyp j.1)) p
  by_cases hin : ∃ k, σ k = cidx j
  · obtain ⟨k, hk⟩ := hin
    have hH' : ∀ x ∈ φ.source, x ∈ F.hyp j.1 ↔ ψ (φ x) (σ k) = 0 := fun x hx => by
      rw [hk]
      exact hH x hx
    by_cases hki : k = i
    · subst hki
      refine ⟨1, le_rfl, ?_⟩
      have e := strictTransform_inter_source_self hφ hΦ hH'
      rw [pow_one, ← hk, hΦ.germMap_coord_self h.contMDiff hφ.1 hp,
        vanishingStalk_eq_top_of_notMem hstrict.isClosed
          (fun hps => absurd ((Set.ext_iff.mp e p).mp ⟨hps, hp⟩) (Set.notMem_empty p)),
        Ideal.mul_top, hexc]
    · refine ⟨1, le_rfl, ?_⟩
      have e := strictTransform_inter_source_of_ne hφ hΦ hH' (Ne.symm hki)
      have hS : ∀ x ∈ Φ.source, x ∈ strictTransformSet π Y (F.hyp j.1) ↔ ψ (Φ x) (σ k) = 0 :=
        fun x hx => ⟨fun hxs => ((Set.ext_iff.mp e x).mp ⟨hxs, hx⟩).2,
          fun hx0 => ((Set.ext_iff.mp e x).mpr ⟨hx, hx0⟩).1⟩
      rw [pow_one, ← hk, hΦ.germMap_coord_of_ne h.contMDiff hφ.1 hp hki,
        ← Ideal.span_singleton_mul_span_singleton, hexc,
        hstrict.vanishingStalk_eq_span_coord_of_inter_source hΦ.mem_maximalAtlas hS hp]
  · refine ⟨0, zero_le_one, ?_⟩
    have hj : ∀ k, σ k ≠ cidx j := fun k hk => hin ⟨k, hk⟩
    have e := strictTransform_inter_source_off hφ hΦ hj hH
    have hS : ∀ x ∈ Φ.source, x ∈ strictTransformSet π Y (F.hyp j.1) ↔ ψ (Φ x) (cidx j) = 0 :=
      fun x hx => ⟨fun hxs => ((Set.ext_iff.mp e x).mp ⟨hxs, hx⟩).2,
        fun hx0 => ((Set.ext_iff.mp e x).mpr ⟨hx, hx0⟩).1⟩
    rw [pow_zero, one_mul, hΦ.germMap_coord_off h.contMDiff hφ.1 hp hj,
      hstrict.vanishingStalk_eq_span_coord_of_inter_source hΦ.mem_maximalAtlas hS hp]

/-- The member transport at a point over the centre: the charts of `HasSncWith` and a blow-up
chart through the point (condition (2) of [BM88, Definition 4.1]). -/
theorem exists_map_germMap_vanishingStalk_hyp_eq_of_mem (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) (hsnc : F.HasSncWith ψ Y c) {p : M'} (hpY : π p ∈ Y)
    (j : {j // π p ∈ F.hyp j}) :
    ∃ ε ≤ 1, Ideal.map (germMap π h.contMDiff p)
        (vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j.1) (π p)) =
      vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' Y) p ^ ε *
        vanishingStalk (𝕜 := 𝕜) (E := E) ((F.totalTransform π Y).hyp (toLex (Sum.inl j.1))) p := by
  obtain ⟨φ, σ, cidx, hφ, hc⟩ := hsnc (π p) hpY
  obtain ⟨i, Φ, hΦ, hp⟩ := h.cover φ σ hφ p hc.2.1
  exact exists_map_germMap_vanishingStalk_hyp_eq hY h hF hsnc hφ hc hΦ hp j

/-- Off the exceptional divisor the blowing-up is a local analytic isomorphism (condition (1) of
[BM88, Definition 4.1]): the vanishing ideal of a member pulls back along the bijective germ map
to the vanishing ideal of its preimage, which is the strict transform there. -/
theorem map_germMap_vanishingStalk_hyp_of_notMem (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) {p : M'} (hpY : π p ∉ Y) (j : F.ι) :
    Ideal.map (germMap π h.contMDiff p) (vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j) (π p)) =
      vanishingStalk (𝕜 := 𝕜) (E := E) ((F.totalTransform π Y).hyp (toLex (Sum.inl j))) p := by
  have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω π p := h.isLocalDiffeomorphOn_compl ⟨p, hpY⟩
  have e := vanishingStalk_preimage_of_isLocalDiffeomorphAt (⟨π, h.contMDiff⟩ : AnalyticMap M' M)
    hloc (F.hyp j)
  change vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' F.hyp j) p =
    Ideal.map (germMap π h.contMDiff p) (vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j) (π p)) at e
  rw [← e]
  change _ = vanishingStalk (𝕜 := 𝕜) (E := E) (strictTransformSet π Y (F.hyp j)) p
  have hopen : π ⁻¹' Yᶜ ∈ 𝓝 p :=
    (hY.isClosed.isOpen_compl.preimage h.contMDiff.continuous).mem_nhds hpY
  have hset : π ⁻¹' F.hyp j ∩ π ⁻¹' Yᶜ = strictTransformSet π Y (F.hyp j) ∩ π ⁻¹' Yᶜ := by
    ext x
    constructor
    · rintro ⟨hx, hxY⟩
      exact ⟨(HypersurfaceFamily.mem_strictTransform_iff_of_notMem h hF hxY j).mpr hx, hxY⟩
    · rintro ⟨hx, hxY⟩
      exact ⟨(HypersurfaceFamily.mem_strictTransform_iff_of_notMem h hF hxY j).mp hx, hxY⟩
  rw [← vanishingStalk_inter_of_mem_nhds (Z := π ⁻¹' F.hyp j) hopen, hset,
    vanishingStalk_inter_of_mem_nhds hopen]

/-- The member transport at every point: over the centre by the chart formulas, off it by the
local isomorphism (with `ε = 0`). -/
theorem exists_map_germMap_vanishingStalk_hyp_eq' (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) (hsnc : F.HasSncWith ψ Y c) (p : M')
    (j : {j // π p ∈ F.hyp j}) :
    ∃ ε ≤ 1, Ideal.map (germMap π h.contMDiff p)
        (vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j.1) (π p)) =
      vanishingStalk (𝕜 := 𝕜) (E := E) (π ⁻¹' Y) p ^ ε *
        vanishingStalk (𝕜 := 𝕜) (E := E) ((F.totalTransform π Y).hyp (toLex (Sum.inl j.1))) p := by
  by_cases hpY : π p ∈ Y
  · exact exists_map_germMap_vanishingStalk_hyp_eq_of_mem hY h hF hsnc hpY j
  · refine ⟨0, zero_le_one, ?_⟩
    rw [pow_zero, one_mul]
    exact map_germMap_vanishingStalk_hyp_of_notMem hY h hF hpY j.1

end BlowUp

end Hironaka.Manifold
