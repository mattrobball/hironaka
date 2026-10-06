/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceProp313
public import Hironaka.Algebra.Local.ChartHom
public import Hironaka.Manifold.Germ.TaylorCompletion
import Hironaka.Algebra.Local.ChartCompletion
import Hironaka.Algebra.Local.ChartCompletionHom
import Hironaka.Algebra.Local.CompletionCoords
import Hironaka.Manifold.BlowUp.Charts
import Hironaka.Manifold.BlowUp.Divisor
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.KollarPerm
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.Germ.TaylorIdeal
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# The flat descent datum at a point of the exceptional divisor: the completion identification

At a point `a'` of a blow-up chart `Φ` of index `i` over the centre, the chart ring
`R' = R[x_j/x_r]` of `R = 𝒪_{M,π(a')}` maps to `𝒪_{M',a'}` by the chart-ring map `χ`, and **the
flat descent datum** of `Algebra.HasFlatDescentDatum` for `χ` is the completion
`𝒪̂_{M',a'}`. This is the input to the proof of [BM97, Proposition 3.13] by the flatness route
(`Hironaka.Manifold.BlowUp.Transform.StrictSubspaceProp313`).

* **Kollár's coordinates at `a'`** (`kollarCoords`): the adapted coordinates of `φ` centred at
  `π(a')` and permuted by `τ` (`τ r = σ i` the divisor coordinate, the `τ j`, `j < r`, the other
  centre coordinates), with the centre coordinates `x_j` (`j < r`) shifted by `u_{τ j}(a') · x_r`
  (`shiftCoords`) so that the ratio coordinates `x_j / x_r ↦ u_{τ j} − u_{τ j}(a')` vanish at
  `a'`: the chart ring of the shifted coordinates is `R'` and its **chart origin** is
  `χ⁻¹(𝔪_{a'})` (`IsLocalRing.comap_maximalIdeal_eq_chartOrigin`). The pullback relations
  `germMap π (x_j) = u_{σ i} · (u_{τ j} − u_{τ j}(a'))`, `germMap π (x_r) = u_{σ i}`,
  `germMap π (x_j) = u_{τ j} − u_{τ j}(a')` (`j > r`, transversal coordinates:
  `IsBlowUpChart.germMap_coord_of_forall_ne`) give `χ` by
  `IsLocalRing.exists_chartRing_hom_of_mul_eq` (`exists_isChartRingHom`). These are the
  coordinates of [Kol07, Definition 60, (60.2)], as used in the proof of [Kol07, Lemma 62].
* **The completion identification** (`IsChartRingHom.hasFlatDescentDatum`): the local map
  `χ_loc : R'_{𝔪'} → 𝒪_{M',a'}` induces a bijection of completions `(R'_{𝔪'})^ → 𝒪̂_{M',a'}`
  (`IsLocalRing.completionMap_bijective_of_cohen`), with the analytic constants
  `𝕜 → R → R' → R'_{𝔪'}` as the coefficient field of `(R'_{𝔪'})^` (a coefficient field since
  `ev_{a'} ∘ χ_loc` identifies `R'_{𝔪'}/𝔪' ≅ 𝕜`), the regular system of parameters
  `y_m = x_{τ⁻¹ m} / x_r`-or-`x_{τ⁻¹ m}` of `R'_{𝔪'}`, and the Taylor isomorphism
  `𝒪̂_{M',a'} ≅ 𝕜⟦X⟧` under which `χ_loc(y_m) ↦ X_m` (`taylorHom_coord_sub`). Hence
  `R' → 𝒪̂_{M',a'}` is flat (`IsLocalRing.flat_comp_algebraMap_adicCompletion`) and
  `J 𝒪̂ ∩ 𝒪 = J`. Completions of local rings enter Kollár's treatment in [Kol07, Definition 55].
* **Proposition 3.13 at every point** (`saturationStalk_eq_span_strictTransformElems`): over the
  centre through the datum and the pointwise theorem of
  `Hironaka.Manifold.BlowUp.Transform.StrictSubspaceProp313`, off the centre directly.
-/

@[expose] public section

open TopologicalSpace Opposite CategoryTheory IsLocalRing Filter
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M} {φ : OpenPartialHomeomorph M E}
  {σ : Fin c ↪ Fin n} {i : Fin c} {Φ : OpenPartialHomeomorph M' E}

/-! ### Pullbacks of constants and of transversal coordinates -/

omit [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
/-- The germ of a constant pulls back to the germ of the constant. -/
theorem germMap_const (hπ : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω π) (p : M') (a : 𝕜) :
    germMap π hπ p (const 𝕜 E M (π p) a) = const 𝕜 E M' p a := by
  apply stalkToGerm_injective 𝓘(𝕜, E) ω M' p
  rw [stalkToGerm_germMap, stalkToGerm_const, stalkToGerm_const, Germ.coe_compTendsto]
  rfl

omit [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
/-- `z_m ∘ π = u_m` for a coordinate `m` transversal to the centre (the blow-up chart map is the
identity off the block `σ`). -/
theorem IsBlowUpChart.germMap_coord_of_forall_ne (hπ : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω π)
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (hΦ : IsBlowUpChart ψ π φ σ i Φ) {p : M'}
    (hp : p ∈ Φ.source) {m : Fin n} (hm : ∀ k, σ k ≠ m) :
    germMap π hπ p (coord E ψ φ hφ (hΦ.source_subset hp) m) =
      coord E ψ Φ hΦ.mem_maximalAtlas hp m := by
  apply stalkToGerm_injective 𝓘(𝕜, E) ω M' p
  rw [stalkToGerm_germMap, stalkToGerm_coord, stalkToGerm_coord, Germ.coe_compTendsto,
    Germ.coe_eq]
  filter_upwards [Φ.open_source.mem_nhds hp] with x hx
  rw [Function.comp_apply, extendSection_of_mem 𝕜 E _ (hΦ.source_subset hx),
    extendSection_of_mem 𝕜 E _ hx]
  change ψ (φ (π x)) m = ψ (Φ x) m
  rw [hΦ.comm x hx, blowUpChartMap_apply_off _ _ hm]

omit [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
/-- The value at `π p` of a transversal coordinate is its value at `p` in the blow-up chart. -/
theorem IsBlowUpChart.eval_coord_of_forall_ne (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) {p : M'} (hp : p ∈ Φ.source) {m : Fin n}
    (hm : ∀ k, σ k ≠ m) :
    eval 𝕜 E M (π p) (coord E ψ φ hφ (hΦ.source_subset hp) m) =
      eval 𝕜 E M' p (coord E ψ Φ hΦ.mem_maximalAtlas hp m) := by
  rw [eval_coord, eval_coord, hΦ.comm p hp, blowUpChartMap_apply_off _ _ hm]

/-! ### Kollár's coordinates at a point of the exceptional divisor -/

section Coords

variable (hφ : IsAdaptedChart ψ Y φ σ) (hΦ : IsBlowUpChart ψ π φ σ i Φ) {a' : M'}
  (ha' : a' ∈ Φ.source) (r : Fin n) (τ : Fin n ≃ Fin n)

/-- **Kollár's coordinates at `a'`**: the centred adapted coordinates `centredCoords` (permuted by
`τ`), with the centre coordinates `x_j`, `j < r`, shifted by `u_{τ j}(a') · x_r` (`shiftCoords`),
so that the ratio coordinates `x_j / x_r` of the chart ring vanish at `a'`. -/
noncomputable def kollarCoords : Fin n → (structureSheaf 𝕜 E M).presheaf.stalk (π a') :=
  shiftCoords (centredCoords hφ hΦ ha' τ) r
    fun j => const 𝕜 E M (π a') (eval 𝕜 E M' a' (coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)))

omit [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
theorem kollarCoords_of_lt {j : Fin n} (hj : j < r) :
    kollarCoords hφ hΦ ha' r τ j = centredCoords hφ hΦ ha' τ j -
      const 𝕜 E M (π a') (eval 𝕜 E M' a' (coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j))) *
        centredCoords hφ hΦ ha' τ r :=
  shiftCoords_of_lt _ _ _ hj

omit [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
theorem kollarCoords_of_not_lt {j : Fin n} (hj : ¬ j < r) :
    kollarCoords hφ hΦ ha' r τ j = centredCoords hφ hΦ ha' τ j :=
  shiftCoords_of_not_lt _ _ _ hj

omit [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
/-- The centred coordinates generate `𝔪_{π(a')}` (reindexed by `τ`). -/
theorem maximalIdeal_eq_span_centredCoords :
    maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) =
      Ideal.span (Set.range (centredCoords hφ hΦ ha' τ)) := by
  rw [maximalIdeal_eq_span_coord' E ψ φ (hΦ.source_subset ha') hφ.1]
  congr 1
  exact (τ.surjective.range_comp _).symm

omit [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
/-- Kollár's coordinates at `a'` generate `𝔪_{π(a')}`. -/
theorem maximalIdeal_eq_span_kollarCoords :
    maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) =
      Ideal.span (Set.range (kollarCoords hφ hΦ ha' r τ)) :=
  span_range_shiftCoords _ _ _ (maximalIdeal_eq_span_centredCoords hφ hΦ ha' τ)

variable (haY : π a' ∈ Y) (hτr : τ r = σ i) (hlt : ∀ j, j < r ↔ ∃ k, k ≠ i ∧ τ j = σ k)

omit [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
include haY hτr hlt in
/-- Over the centre the centre coordinates are already centred: `x_j = z_{τ j}` for `j ≤ r`. -/
theorem centredCoords_of_le {j : Fin n} (hj : j ≤ r) :
    centredCoords hφ hΦ ha' τ j = coord E ψ φ hφ.1 (hΦ.source_subset ha') (τ j) := by
  obtain ⟨k, hk⟩ : ∃ k, τ j = σ k := by
    rcases lt_or_eq_of_le hj with hj' | rfl
    · obtain ⟨k, -, hk⟩ := (hlt j).mp hj'
      exact ⟨k, hk⟩
    · exact ⟨i, hτr⟩
  unfold centredCoords
  rw [hk, eval_coord, (hφ.2 _ (hΦ.source_subset ha')).1 haY k, map_zero, sub_zero]

include haY hτr hlt in
/-- `x_r ∘ π = u_{σ i}`, the divisor coordinate. -/
theorem germMap_kollarCoords_self (h : IsBlowUp ψ Y c π) :
    germMap π h.contMDiff a' (kollarCoords hφ hΦ ha' r τ r) =
      coord E ψ Φ hΦ.mem_maximalAtlas ha' (σ i) := by
  rw [kollarCoords_of_not_lt hφ hΦ ha' r τ (lt_irrefl r),
    centredCoords_of_le hφ hΦ ha' r τ haY hτr hlt le_rfl, hτr]
  exact hΦ.germMap_coord_self h.contMDiff hφ.1 ha'

include haY hτr hlt in
/-- `x_j ∘ π = u_{σ i} · (u_{τ j} − u_{τ j}(a'))` for `j < r`: the shifted centre coordinates. -/
theorem germMap_kollarCoords_of_lt (h : IsBlowUp ψ Y c π) {j : Fin n} (hj : j < r) :
    germMap π h.contMDiff a' (kollarCoords hφ hΦ ha' r τ j) =
      coord E ψ Φ hΦ.mem_maximalAtlas ha' (σ i) * (coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) -
        const 𝕜 E M' a' (eval 𝕜 E M' a' (coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)))) := by
  obtain ⟨k, hki, hk⟩ := (hlt j).mp hj
  rw [kollarCoords_of_lt hφ hΦ ha' r τ hj,
    centredCoords_of_le hφ hΦ ha' r τ haY hτr hlt (le_of_lt hj),
    centredCoords_of_le hφ hΦ ha' r τ haY hτr hlt le_rfl, hτr, map_sub, map_mul, germMap_const, hk,
    hΦ.germMap_coord_of_ne h.contMDiff hφ.1 ha' hki, hΦ.germMap_coord_self h.contMDiff hφ.1 ha']
  ring

include hτr hlt in
/-- `x_j ∘ π = u_{τ j} − u_{τ j}(a')` for `j > r`: the transversal coordinates. -/
theorem germMap_kollarCoords_of_gt (h : IsBlowUp ψ Y c π) {j : Fin n} (hj : r < j) :
    germMap π h.contMDiff a' (kollarCoords hφ hΦ ha' r τ j) =
      coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) -
        const 𝕜 E M' a' (eval 𝕜 E M' a' (coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j))) := by
  have hm : ∀ k, σ k ≠ τ j := by
    intro k hk
    by_cases hki : k = i
    · subst hki
      exact ne_of_lt hj (τ.injective (hτr.trans hk))
    · exact lt_asymm hj ((hlt j).mpr ⟨k, hki, hk.symm⟩)
  rw [kollarCoords_of_not_lt hφ hΦ ha' r τ (lt_asymm hj)]
  unfold centredCoords
  rw [map_sub, germMap_const, hΦ.germMap_coord_of_forall_ne h.contMDiff hφ.1 ha' hm,
    hΦ.eval_coord_of_forall_ne hφ.1 ha' hm]

include haY hτr hlt in
/-- `exists_chartRing_hom` for Kollár's coordinates at `a'`: the chart-ring map
`χ : R' → 𝒪_{M',a'}` exists (`IsLocalRing.exists_chartRing_hom_of_mul_eq` on the pullback
relations above). -/
theorem exists_isChartRingHom (h : IsBlowUp ψ Y c π) :
    ∃ χ : chartRing (kollarCoords hφ hΦ ha' r τ) r →+*
        (structureSheaf 𝕜 E M').presheaf.stalk a',
      IsChartRingHom h hΦ ha' (kollarCoords hφ hΦ ha' r τ) r τ χ := by
  have := isDomain_stalk ψ hΦ.mem_maximalAtlas ha'
  obtain ⟨χ, h₁, h₂, h₃⟩ := exists_chartRing_hom_of_mul_eq
    (kollarCoords hφ hΦ ha' r τ) r (germMap π h.contMDiff a')
    (coord_ne_zero hΦ.mem_maximalAtlas ha' (σ i))
    (fun j => coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) -
      const 𝕜 E M' a' (eval 𝕜 E M' a' (coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j))))
    (germMap_kollarCoords_self hφ hΦ ha' r τ haY hτr hlt h)
    (fun j hj => germMap_kollarCoords_of_lt hφ hΦ ha' r τ haY hτr hlt h hj)
  exact ⟨χ, haY, hτr, hlt, h₁, h₂, h₃⟩

end Coords

/-! ### The flat descent datum: the completion identification -/

omit [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
/-- Evaluation at a point is a local homomorphism (`𝔪_a = ker ev_a`). -/
theorem isLocalHom_eval (a : M') : IsLocalHom (eval 𝕜 E M' a) :=
  ⟨fun s hs => notMem_maximalIdeal.mp fun hm =>
    hs.ne_zero ((mem_maximalIdeal_iff_eval E s).mp hm)⟩

section Datum

variable (h : IsBlowUp ψ Y c π) (hφ : IsAdaptedChart ψ Y φ σ) (hΦ : IsBlowUpChart ψ π φ σ i Φ)
  {a' : M'} (ha' : a' ∈ Φ.source) {x : Fin n → (structureSheaf 𝕜 E M).presheaf.stalk (π a')}
  {r : Fin n} {τ : Fin n ≃ Fin n}
  {χ : chartRing x r →+* (structureSheaf 𝕜 E M').presheaf.stalk a'}
  (hχ : IsChartRingHom h hΦ ha' x r τ χ)

include hχ in
/-- A chart-ring map carries the constants to the constants. -/
theorem IsChartRingHom.map_algebraMap_const (b : 𝕜) :
    χ (algebraMap _ _ (const 𝕜 E M (π a') b)) = const 𝕜 E M' a' b := by
  rw [hχ.algebraMap_eq, germMap_const]

include hφ hχ in
/-- `χ⁻¹(𝔪_{a'})` is the chart origin of `x` when `x` generates `𝔪_{π(a')}`: the ratio coordinates
`x_j / x_r` map to germs vanishing at `a'`, the `x_i` to `𝔪_{π(a')} ∘ π ⊆ 𝔪_{a'}`. -/
theorem IsChartRingHom.comap_maximalIdeal_eq_chartOrigin
    (hx : maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) =
      Ideal.span (Set.range x)) :
    (maximalIdeal ((structureSheaf 𝕜 E M').presheaf.stalk a')).comap χ =
      chartOrigin x r := by
  have haφ : π a' ∈ φ.source := hΦ.source_subset ha'
  have hRreg : IsRegularLocalRing ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) :=
    isRegularLocalRing_stalk_of_chart E ψ φ haφ hφ.1
  have hn : (n : WithBot ℕ∞) = ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) :=
    (ringKrullDim_stalk_of_chart E ψ φ haφ hφ.1).symm
  refine IsLocalRing.comap_maximalIdeal_eq_chartOrigin x r hx hn χ (fun j hj => ?_)
    fun i' => ?_
  · rw [hχ.chartYR_eq j hj, mem_maximalIdeal_iff_eval, map_sub, eval_const, sub_self]
  · rw [hχ.algebraMap_eq, mem_maximalIdeal_iff_eval, eval_germMapOn, ← mem_maximalIdeal_iff_eval,
      hx]
    exact Ideal.subset_span ⟨i', rfl⟩

include hφ hχ in
/-- The Taylor series at `a'` of `χ(y_m)`, for the regular system of parameters
`y_m = x_{τ⁻¹ m}/x_r` (`τ⁻¹ m < r`), `x_r`, `x_{τ⁻¹ m}` (`τ⁻¹ m > r`), is the variable `X_m` —
given the transversal
relations `x_j ∘ π = u_{τ j} − u_{τ j}(a')` for `j > r`. -/
theorem IsChartRingHom.taylorHom_chartYR
    (hgt : ∀ j, r < j → germMap π h.contMDiff a' (x j) =
      coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) -
        const 𝕜 E M' a' (eval 𝕜 E M' a' (coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j))))
    (m : Fin n) :
    taylorHom E ψ Φ ha' hΦ.mem_maximalAtlas (χ (chartYR x r (τ.symm m))) =
      MvPowerSeries.X m := by
  rcases lt_trichotomy (τ.symm m) r with hlt' | heq | hgt'
  · rw [hχ.chartYR_eq _ hlt', Equiv.apply_symm_apply, taylorHom_coord_sub]
  · have hm : σ i = m := by
      rw [← hχ.apply_eq, ← heq]
      exact τ.apply_symm_apply m
    have hyr : chartYR x r r = algebraMap _ _ (x r) :=
      Subtype.ext (by
        rw [coe_chartYROf, chartYOf_self, Subalgebra.coe_algebraMap])
    rw [heq, hyr, hχ.xr_eq, taylorHom_coord, (hΦ.mem_preimage_iff hφ ha').mp hχ.mem_center,
      map_zero, add_zero, hm]
  · have hyj : chartYR x r (τ.symm m) = algebraMap _ _ (x (τ.symm m)) :=
      Subtype.ext (by
        rw [coe_chartYROf,
          chartYOf_of_not_lt x r (x r) (lt_asymm hgt'), Subalgebra.coe_algebraMap])
    rw [hyj, hχ.algebraMap_eq, hgt _ hgt', Equiv.apply_symm_apply, taylorHom_coord_sub]

include hφ hχ in
/-- **The completion identification** (the flatness route to [BM97, Proposition 3.13]): the map of
completions induced by the local homomorphism `R'_{𝔪'} → 𝒪_{a'}` of the chart-ring map `χ` is
bijective — the Taylor expansions at `a'` of the chart coordinates `χ(y_j)` are the variables
(`IsChartRingHom.taylorHom_chartYR`), so both completions are `𝕜⟦u_1, …, u_n⟧` on the same
coefficient field (`IsLocalRing.completionMap_bijective_of_cohen`). Extracted from
`IsChartRingHom.hasFlatDescentDatum` for order transport
(`IsLocalRing.ordFaithful_chartLocalHom`). -/
theorem IsChartRingHom.completionMap_bijective [(chartOrigin x r).IsPrime]
    (hx : maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) =
      Ideal.span (Set.range x))
    (hgt : ∀ j, r < j → germMap π h.contMDiff a' (x j) =
      coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) -
        const 𝕜 E M' a' (eval 𝕜 E M' a' (coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)))) :
    Function.Bijective
      (haveI := isLocalHom_chartLocalHom x r χ
        (hχ.comap_maximalIdeal_eq_chartOrigin h hφ hΦ ha' hx);
      completionMap (chartLocalHom x r χ
        (hχ.comap_maximalIdeal_eq_chartOrigin h hφ hΦ ha' hx))) := by
  classical
  have haφ : π a' ∈ φ.source := hΦ.source_subset ha'
  have hRreg : IsRegularLocalRing ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) :=
    isRegularLocalRing_stalk_of_chart E ψ φ haφ hφ.1
  have hRnoeth : IsNoetherianRing ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) :=
    isNoetherianRing_stalk_of_chart E ψ φ haφ hφ.1
  have hn : (n : WithBot ℕ∞) = ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) :=
    (ringKrullDim_stalk_of_chart E ψ φ haφ hφ.1).symm
  have hcomap := hχ.comap_maximalIdeal_eq_chartOrigin h hφ hΦ ha' hx
  let f := chartLocalHom x r χ hcomap
  have hfloc : IsLocalHom f := isLocalHom_chartLocalHom x r χ hcomap
  have := isLocalHom_eval (𝕜 := 𝕜) (E := E) (M' := M') a'
  let ev : Localization.AtPrime (chartOrigin x r) →+* 𝕜 := (eval 𝕜 E M' a').comp f
  let cA : 𝕜 →+* Localization.AtPrime (chartOrigin x r) :=
    (algebraMap (chartRing x r) _).comp
      ((algebraMap _ (chartRing x r)).comp (const 𝕜 E M (π a')))
  have hfc : ∀ b, f (cA b) = const 𝕜 E M' a' b := fun b => by
    simp only [cA, RingHom.comp_apply]
    rw [chartLocalHom_algebraMap, hχ.map_algebraMap_const]
  have hevc : ∀ b, ev (cA b) = b := fun b => by
    simp only [ev, RingHom.comp_apply]
    rw [hfc, eval_const]
  let e₀ : ResidueField (Localization.AtPrime (chartOrigin x r)) →+* 𝕜 :=
    ResidueField.lift ev
  have he₀ : Function.Bijective e₀ :=
    ⟨e₀.injective, fun b => ⟨residue _ (cA b), by
      simp only [e₀]
      rw [ResidueField.lift_residue_apply, hevc]⟩⟩
  let : Algebra (ResidueField (Localization.AtPrime (chartOrigin x r)))
      (AdicCompletion (maximalIdeal (Localization.AtPrime (chartOrigin x r)))
        (Localization.AtPrime (chartOrigin x r))) :=
    (((algebraMap _ _).comp cA).comp e₀).toAlgebra
  have hι := isCoefficientAlgebra_of_section ev cA hevc fun _ => rfl
  let Θ := taylorCompletionEquiv E ψ Φ ha' hΦ.mem_maximalAtlas
  let y : Fin n → Localization.AtPrime (chartOrigin x r) := fun m =>
    algebraMap _ _ (chartYR x r (τ.symm m))
  have hy : maximalIdeal (Localization.AtPrime (chartOrigin x r)) =
      Ideal.span (Set.range y) := by
    rw [maximalIdeal_localization_chartOrigin]
    congr 1
    exact (τ.symm.surjective.range_comp _).symm
  have hd : (n : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime (chartOrigin x r)) :=
    (ringKrullDim_localization_chartOrigin x r hx hn).symm
  have hΘy : ∀ m, Θ (algebraMap _ _ (f (y m))) = MvPowerSeries.X m := fun m => by
    simp only [y, Θ]
    rw [taylorCompletionEquiv_algebraMap, chartLocalHom_algebraMap]
    exact hχ.taylorHom_chartYR h hφ hΦ ha' hgt m
  have hΘk : ∀ k, Θ (completionMap f (algebraMap (ResidueField _) _ k)) =
      MvPowerSeries.C (e₀ k) := fun k => by
    have hk : algebraMap (ResidueField (Localization.AtPrime (chartOrigin x r)))
        (AdicCompletion (maximalIdeal (Localization.AtPrime (chartOrigin x r)))
          (Localization.AtPrime (chartOrigin x r))) k =
        algebraMap _ _ (cA (e₀ k)) := rfl
    rw [hk, completionMap_algebraMap]
    simp only [Θ]
    rw [taylorCompletionEquiv_algebraMap, hfc, taylorHom_const]
  have hSnoeth : IsNoetherianRing ((structureSheaf 𝕜 E M').presheaf.stalk a') :=
    isNoetherianRing_stalk_of_chart E ψ Φ ha' hΦ.mem_maximalAtlas
  exact completionMap_bijective_of_cohen f y hy hd hι Θ e₀ he₀ hΘy hΘk

include hφ hχ in
/-- **The flat descent datum for a chart-ring map**: for
coordinates `x` generating `𝔪_{π(a')}` whose ratio coordinates vanish at `a'` and with the
transversal relations, the completion `𝒪̂_{M',a'}` receives `𝒪_{M',a'}` faithfully flatly (`J 𝒪̂ ∩
𝒪 = J`) and `R' → 𝒪̂_{M',a'}` is flat — `χ_loc : R'_{𝔪'} → 𝒪_{M',a'}` induces an isomorphism of
completions, both being `𝕜⟦X_1, …, X_n⟧` through Cohen structure
(`IsLocalRing.completionMap_bijective_of_cohen`, with the analytic constants as coefficient
field and the Taylor isomorphism on the analytic side). -/
theorem IsChartRingHom.hasFlatDescentDatum
    (hx : maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) =
      Ideal.span (Set.range x))
    (hgt : ∀ j, r < j → germMap π h.contMDiff a' (x j) =
      coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j) -
        const 𝕜 E M' a' (eval 𝕜 E M' a' (coord E ψ Φ hΦ.mem_maximalAtlas ha' (τ j)))) :
    Algebra.HasFlatDescentDatum χ := by
  have haφ : π a' ∈ φ.source := hΦ.source_subset ha'
  have hRreg : IsRegularLocalRing ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) :=
    isRegularLocalRing_stalk_of_chart E ψ φ haφ hφ.1
  have hn : (n : WithBot ℕ∞) = ringKrullDim ((structureSheaf 𝕜 E M).presheaf.stalk (π a')) :=
    (ringKrullDim_stalk_of_chart E ψ φ haφ hφ.1).symm
  have hcomap := hχ.comap_maximalIdeal_eq_chartOrigin h hφ hΦ ha' hx
  have hprime : (chartOrigin x r).IsPrime :=
    (chartOrigin_isMaximal x r hx hn).isPrime
  have hSnoeth : IsNoetherianRing ((structureSheaf 𝕜 E M').presheaf.stalk a') :=
    isNoetherianRing_stalk_of_chart E ψ Φ ha' hΦ.mem_maximalAtlas
  exact ⟨_, inferInstance, algebraMap _ _,
    flat_comp_algebraMap_adicCompletion x r χ hcomap
      (hχ.completionMap_bijective h hφ hΦ ha' hx hgt),
    fun J => comap_map_adicCompletion J⟩

end Datum

/-! ### Proposition 3.13 at every point -/

variable (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
  (I : IdealSheaf (structureSheaf 𝕜 E M))

/-- **BM97 Proposition 3.13** ([BM97, Proposition 3.13], by the flatness route): at every point `a'`
of the blowing-up, the saturation `⋃_k (π⁻¹(I)_{a'} : I_{F,a'}^k)` — the stalk of the strict
transform, is the ideal generated by the strict transforms `y^{-d}(f ∘ π)` of the
elements `f` of `I_{π(a')}`. Over the centre: an adapted chart and a blow-up chart at `a'`,
Kollár's coordinates at `a'`, the chart-ring map and its flat descent datum, then the pointwise
theorem of `Hironaka.Manifold.BlowUp.Transform.StrictSubspaceProp313`; off the centre directly.
-/
theorem saturationStalk_eq_span_strictTransformElems (a' : M') :
    saturationStalk hY h I a' = Ideal.span (strictTransformElems hY h I a') := by
  by_cases haY : π a' ∈ Y
  · obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart (π a') haY
    obtain ⟨i, Φ, hΦ, ha'⟩ := h.cover φ σ hφ a' haφ
    obtain ⟨r, τ, hτr, hlt⟩ := exists_kollarPerm σ i
    obtain ⟨χ, hχ⟩ := exists_isChartRingHom hφ hΦ ha' r τ haY hτr hlt h
    exact saturationStalk_eq_span_strictTransformElems_of_hasFlatDescentDatum hY h I hφ hΦ ha' _
      r τ χ hχ (hχ.hasFlatDescentDatum h hφ hΦ ha' (maximalIdeal_eq_span_kollarCoords hφ hΦ ha' r τ)
        fun j hj => germMap_kollarCoords_of_gt hφ hΦ ha' r τ hτr hlt h hj)
  · exact saturationStalk_eq_span_strictTransformElems_of_notMem hY h I haY

end Manifold
