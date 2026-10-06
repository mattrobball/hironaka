/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Defs
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Pieces
import Hironaka.Manifold.BlowUp.Transition
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Center
import Hironaka.Resolution.Analytic.Principalization.MeetLocusChart
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Charts at a point of a centre of the monomial procedure

The nerve after the blow-up of a centre (`BMO/Step3Monomial/Kernel.lean`) is computed in
coordinates. At a point `x` of the locus of a face `P` of the centre, this file provides a chart of
simple normal crossings for the boundary family, shrunk so that every piece through `x` is a
coordinate hyperplane `{z_{κ c} = 0}` (a piece is a clopen part of its member), every piece not
through `x` misses the chart, and the centre is the coordinate subspace cut out by the coordinates
of the pieces of `P`; the chart is then adapted to the centre with block `σ` the coordinates of the
pieces of `P` (`Realizes.exists_chart_of_mem_faceSet`). Over such a chart the blow-up has its charts
of every index `i` ([BM88, Definition 4.1]), and the point of the chart of index `i` with the same
coordinates as `x` lies over `x` (`IsBlowUpChart.exists_mem_source_of_mem_center`): this is the
point at which the intersections after the blow-up, "`E^{i₁} ∩ ⋯ ∩ E^{i_{r-1}} ∩ E^{jℓ}` for certain
values of `i`" in [Kol07, 111, Step 3], are read off.
-/

public section

open Set Topology Hironaka.Monomial
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- Over a chart adapted to the centre, the point of the blow-up chart of index `i` with the same
coordinates as a point `x` of the centre lies over `x` ([BM88, Definition 4.1 (2)]). -/
theorem IsBlowUpChart.exists_mem_source_of_mem_center {M : Type u} [TopologicalSpace M]
    [ChartedSpace E M] {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] {Y : Set M} {c : ℕ}
    {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} {i : Fin c} {π : M' → M}
    {Φ : OpenPartialHomeomorph M' E} (hφ : IsAdaptedChart ψ Y φ σ)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) {x : M} (hxY : x ∈ Y) (hxφ : x ∈ φ.source) :
    ∃ p ∈ Φ.source, π p = x ∧ ψ (Φ p) = ψ (φ x) := by
  have hcen : ψ (φ x) ∈ blowUpCenter σ := fun k => (hφ.2 x hxφ).mp hxY k
  have hmem : ψ.symm (ψ (φ x)) ∈ Φ.target := by
    rw [hΦ.mem_target_iff, ContinuousLinearEquiv.apply_symm_apply,
      BlowUpGlue.blowUpChartMap_of_mem_center hcen]
    exact ⟨φ x, φ.map_source hxφ, rfl⟩
  refine ⟨Φ.symm (ψ.symm (ψ (φ x))), Φ.map_target hmem, ?_, ?_⟩
  · have h1 : ψ (φ (π (Φ.symm (ψ.symm (ψ (φ x)))))) = ψ (φ x) := by
      rw [hΦ.comm _ (Φ.map_target hmem), Φ.right_inv hmem,
        ContinuousLinearEquiv.apply_symm_apply, BlowUpGlue.blowUpChartMap_of_mem_center hcen]
    exact φ.injOn (hΦ.source_subset (Φ.map_target hmem)) hxφ (ψ.injective h1)
  · rw [Φ.right_inv hmem, ContinuousLinearEquiv.apply_symm_apply]

end Manifold

namespace Hironaka.Manifold.BMO.PieceFamily

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {N : AnalyticManifold.{u} 𝕜 E} {Φ : PieceFamily N}
  {F : HypersurfaceFamily N} {e : Fin Φ.nextLabel ↪o F.ι} {m : ℕ} {hV : Φ.IsValid n m}
  {S : Finset (Finset ℕ)}

/-- At a point `x` of the locus of the face `P ∈ S` of a centre there is a chart `φ` of simple
normal crossings for the boundary family ([Kol07, Definition 24]) with coordinates `κ` for the
pieces through `x`, such that on the chart every piece through `x` is its coordinate hyperplane,
every piece not through `x` misses the chart, the coordinates of distinct pieces through `x` are
distinct, and the chart is adapted to the centre with block `σ` the coordinates of the pieces of
`P`; `κ` is the index function of the chart on the members of the pieces. -/
theorem Realizes.exists_chart_of_mem_faceSet (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) {P : Finset ℕ} (hP : P ∈ S) {x : N}
    (hxP : x ∈ Φ.faceSet P) :
    ∃ (φ : OpenPartialHomeomorph N E) (σ : Fin (faceCard S) ↪ Fin n)
      (κ : {c : Fin Φ.nextComp // x ∈ Φ.piece c} → Fin n),
      x ∈ φ.source ∧ IsAdaptedChart ψ₀ (Φ.centerOf S) φ σ ∧ Function.Injective κ ∧
      (∀ c, ∀ y ∈ φ.source, (y ∈ Φ.piece c.1 ↔ ψ₀ (φ y) (κ c) = 0)) ∧
      (∀ c : Fin Φ.nextComp, x ∉ Φ.piece c → ∀ y ∈ φ.source, y ∉ Φ.piece c) ∧
      (∀ c, c.1.1 ∈ P ↔ κ c ∈ Set.range σ) ∧ (∀ k, ∃ c, c.1.1 ∈ P ∧ κ c = σ k) ∧
      ∃ cidx : {j // x ∈ F.hyp j} → Fin n, F.IsSncChartAt ψ₀ φ x cidx ∧
        ∀ c, κ c = cidx ⟨e ⟨Φ.label c.1, Φ.label_lt c.1 c.1.2⟩, hΦ.piece_subset_hyp c.1.2 c.2⟩ := by
  classical
  have hPn : ∀ c ∈ P, c < Φ.nextComp := fun c hc =>
    Φ.lt_nextComp_of_mem_nerve (subset_nerve_of_isCenter hS hP) hc
  -- the snc chart at `x`
  obtain ⟨φ₀, cidx, hφ₀⟩ := hF.2.2 x
  -- the member of a live piece through `x`
  let mem : {c : Fin Φ.nextComp // x ∈ Φ.piece c} → {j // x ∈ F.hyp j} := fun c =>
    ⟨e ⟨Φ.label c.1, Φ.label_lt c.1 c.1.2⟩, hΦ.piece_subset_hyp c.1.2 c.2⟩
  have hmem_inj : Function.Injective mem := by
    intro c c' h
    have h1 := congrArg Subtype.val h
    have h2 : Φ.label c.1 = Φ.label c'.1 := Fin.mk.inj_iff.mp (e.injective h1)
    exact Subtype.ext (Fin.ext (hΦ.eq_of_label_eq_of_mem c.1.2 c'.1.2 h2 c.2 c'.2))
  let κ : {c : Fin Φ.nextComp // x ∈ Φ.piece c} → Fin n := fun c => cidx (mem c)
  have hκ_inj : Function.Injective κ := fun c c' h => hmem_inj (hφ₀.injective h)
  -- the opens: the pieces through `x` are traces of their members, the others are missed
  choose O hO hpiece using fun c : {c : Fin Φ.nextComp // x ∈ Φ.piece c} =>
    hΦ.exists_isOpen_piece_eq c.1.2
  obtain ⟨U, hU, hUP⟩ := hΦ.exists_mem_nhds_centerOf_inter_subset hS hP hxP
  obtain ⟨U', hU'U, hU'o, hxU'⟩ := mem_nhds_iff.mp hU
  let B : Set N := ⋃ c ∈ (Finset.univ.filter fun c : Fin Φ.nextComp => x ∉ Φ.piece c), Φ.piece c
  have hB : IsClosed B := isClosed_biUnion_finset fun c _ => Φ.isClosed_piece c
  have hxB : x ∉ B := by
    simp only [B, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
    exact fun c hc hx => hc hx
  let V : Set N := φ₀.source ∩ U' ∩ (⋂ c, O c) ∩ Bᶜ
  have hVo : IsOpen V :=
    ((φ₀.open_source.inter hU'o).inter (isOpen_iInter_of_finite hO)).inter hB.isOpen_compl
  have hxV : x ∈ V :=
    ⟨⟨⟨hφ₀.mem_source, hxU'⟩, Set.mem_iInter.mpr fun c => ((hpiece c) ▸ c.2).2⟩, hxB⟩
  set φ := φ₀.restrOpen V hVo with hφdef
  have hφ : F.IsSncChartAt ψ₀ φ x cidx := hφ₀.restrOpen_of_isOpen hVo hxV
  have hsrc : φ.source = φ₀.source ∩ V := OpenPartialHomeomorph.restrOpen_source _ _ _
  have hsrcV : ∀ y ∈ φ.source, y ∈ V := fun y hy => (hsrc ▸ hy).2
  -- every live piece through `x` is its coordinate hyperplane on the chart
  have hcoord : ∀ c, ∀ y ∈ φ.source, (y ∈ Φ.piece c.1 ↔ ψ₀ (φ y) (κ c) = 0) := by
    intro c y hy
    have hyO : y ∈ O c := Set.mem_iInter.mp (hsrcV y hy).1.2 c
    rw [hpiece c]
    constructor
    · intro hyc
      exact (hφ.mem_iff (mem c) hy).mp hyc.1
    · intro hyc
      exact ⟨(hφ.mem_iff (mem c) hy).mpr hyc, hyO⟩
  -- the live pieces not through `x` miss the chart
  have hmiss : ∀ c : Fin Φ.nextComp, x ∉ Φ.piece c → ∀ y ∈ φ.source, y ∉ Φ.piece c := by
    intro c hc y hy hyc
    apply (hsrcV y hy).2
    simp only [B, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨c, hc, hyc⟩
  -- the block: the coordinates of the pieces of `P`
  let PS : Finset {c : Fin Φ.nextComp // x ∈ Φ.piece c} := Finset.univ.filter fun c => c.1.1 ∈ P
  let idx : Finset (Fin n) := PS.image κ
  have hPS_card : PS.card = P.card := by
    have himg : PS.image (fun c => c.1.1) = P := by
      ext c
      simp only [PS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact hd
      · intro hc
        exact ⟨⟨⟨c, hPn c hc⟩, Φ.mem_faceSet.mp hxP c hc⟩, hc, rfl⟩
    rw [← himg, Finset.card_image_of_injective _ fun d d' h => Subtype.ext (Fin.ext h)]
  have hidx_card : idx.card = faceCard S := by
    rw [Finset.card_image_of_injective _ hκ_inj, hPS_card, hΦ.card_eq_faceCard_of_isCenter hS hP]
  let σ : Fin (faceCard S) ↪ Fin n := (idx.orderEmbOfFin hidx_card).toEmbedding
  have hrange : Set.range σ = ↑idx := Finset.range_orderEmbOfFin idx hidx_card
  have hidx : ∀ c, κ c ∈ idx ↔ c.1.1 ∈ P := by
    intro c
    simp only [idx, PS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨d, hd, hdc⟩
      exact hκ_inj hdc ▸ hd
    · intro hc
      exact ⟨c, hc, rfl⟩
  refine ⟨φ, σ, κ, ?_, ⟨hφ.mem_maximalAtlas, fun y hy => ?_⟩, hκ_inj, hcoord, hmiss, fun c => ?_,
    fun k => ?_, ⟨cidx, hφ, fun c => rfl⟩⟩
  · exact hφ.mem_source
  · -- adapted to the centre: on the chart the centre is the locus of `P`
    have hyU : y ∈ U := hU'U (hsrcV y hy).1.1.2
    constructor
    · intro hyZ k
      have hyP : y ∈ Φ.faceSet P := hUP ⟨hyZ, hyU⟩
      have hk : σ k ∈ idx := by
        rw [← Finset.mem_coe, ← hrange]
        exact ⟨k, rfl⟩
      obtain ⟨c, hc, hck⟩ := Finset.mem_image.mp hk
      rw [← hck]
      exact (hcoord c y hy).mp (Φ.mem_faceSet.mp hyP c.1.1 (Finset.mem_filter.mp hc).2)
    · intro hall
      refine Φ.faceSet_subset_centerOf hP (Φ.mem_faceSet.mpr fun c hc => ?_)
      let c' : {c : Fin Φ.nextComp // x ∈ Φ.piece c} :=
        ⟨⟨c, hPn c hc⟩, Φ.mem_faceSet.mp hxP c hc⟩
      have hκc : κ c' ∈ Set.range σ := by
        rw [hrange, Finset.mem_coe]
        exact (hidx c').mpr hc
      obtain ⟨k, hk⟩ := hκc
      exact (hcoord c' y hy).mpr (hk ▸ hall k)
  · rw [hrange, Finset.mem_coe, hidx]
  · have hk : σ k ∈ idx := by
      rw [← Finset.mem_coe, ← hrange]
      exact ⟨k, rfl⟩
    obtain ⟨c, hc, hck⟩ := Finset.mem_image.mp hk
    exact ⟨c, (Finset.mem_filter.mp hc).2, hck⟩

end Hironaka.Manifold.BMO.PieceFamily

