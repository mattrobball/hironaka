/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Basic
public import Hironaka.Manifold.BlowUp.Transform.Strict
import Hironaka.Manifold.BlowUp.Transform.StrictCharts
import Hironaka.Manifold.Chart.Transport
import Hironaka.Manifold.LocalDiffeomorph
import Hironaka.Manifold.Submanifold.Charts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The total transform of a simple normal crossings divisor is snc

Kollár: if the centre has simple normal crossings with `E`, then
`Π⁻¹_tot(E) := Π⁻¹_*(E) + Ex_tot(Π)` "is a simple normal crossing divisor, called the total
transform of `E`" [Kol07, Definition 25]; Bierstone–Milman: the admissibility condition
"guarantees that `E_{i+1}` is a collection of smooth hypersurfaces having only normal crossings"
[BM97, (1.2)]. Over a point `a` of the centre, a chart adapted to `Y` that is an snc chart of `F`
at `a` lifts to blow-up charts of every index `i` ([BM88, Definition 4.1 (2)]); in the blow-up
chart of index `i` the exceptional divisor is `{u_i = 0}` and the strict transform of the component
`{z_{c j} = 0}` is `{u_{c j} = 0}` when `c j ≠ σ i` (both a block coordinate `u_k`, `k ≠ i`, and a
coordinate off the block) and misses the chart when `c j = σ i` — so the adapted coordinates of the
total transform are `(u_i, (u_k)_{k ≠ i}, w)`, with the indices `c` on the strict transforms and
`σ i` on the exceptional divisor (`totalTransformIdx`). Off the exceptional divisor the blowing-up
is a local isomorphism ([BM88, Definition 4.1 (1)]), the strict transforms coincide with the
preimages there, and the snc chart of `F` at `π p` transports along a local inverse
(`transportChart`). Each strict transform is a closed smooth hypersurface (from the charts over
`H ∩ Y`, `isClosedSubmanifold_strictTransform_of_charts`), and the family stays locally finite
because each strict transform lies in the preimage of its component. This is the boundary step of
every blow-up of the resolution algorithm (Hironaka's `E_{λ+1} = red(f⁻¹(E_λ) ∪ f⁻¹(D_λ))`,
[Hir64, Main Theorem II'(N) (iii), p. 156]).
-/

@[expose] public section

open TopologicalSpace Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

namespace Manifold

universe u

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M} {Y : Set M} {c : ℕ} {F : HypersurfaceFamily M}

/-- The coordinate indices of the total transform at a point `p` over `a`, from the indices `cidx`
of an snc chart at `a` and the block coordinate `σ i` of the blow-up chart: the strict transform of
a component through `p` (which lies over a component through `a`) keeps its index, the exceptional
divisor gets `σ i`. -/
def HypersurfaceFamily.totalTransformIdx {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M']
    [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] {π : M' → M} {Y : Set M}
    {c : ℕ} (h : IsBlowUp ψ Y c π) {F : HypersurfaceFamily M} (hF : F.IsSnc ψ) {p : M'} {a : M}
    (hpa : π p = a) (cidx : {j // a ∈ F.hyp j} → Fin n) (σ : Fin c ↪ Fin n) (i : Fin c) :
    {k // p ∈ (F.totalTransform π Y).hyp k} → Fin n := fun k =>
  Sum.rec (motive := fun s => p ∈ (F.totalTransform π Y).hyp (toLex s) → Fin n)
    (fun j hk => cidx ⟨j, hpa ▸
      strictTransform_subset_preimage h.contMDiff.continuous (hF.1 j).isClosed hk⟩)
    (fun _ _ => σ i) (ofLex k.1) k.2

namespace HypersurfaceFamily

/-- A point of the strict transform of a component lies over the component. -/
theorem mem_hyp_of_mem_strictTransform (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) {p : M'} {j : F.ι}
    (hp : p ∈ strictTransformSet π Y (F.hyp j)) : π p ∈ F.hyp j :=
  strictTransform_subset_preimage h.contMDiff.continuous (hF.1 j).isClosed hp

/-- Off the exceptional divisor the strict transform of a component is its preimage. -/
theorem mem_strictTransform_iff_of_notMem (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) {p : M'}
    (hpY : π p ∉ Y) (j : F.ι) : p ∈ strictTransformSet π Y (F.hyp j) ↔ π p ∈ F.hyp j := by
  refine ⟨mem_hyp_of_mem_strictTransform h hF, fun hpj => ?_⟩
  rcases preimage_subset_strictTransform_union (π := π) (Y := Y) (H := F.hyp j) hpj with h' | h'
  · exact h'
  · exact absurd h' hpY

/-- The index of a strict-transform component of the total transform is the index of its
component. -/
theorem totalTransformIdx_inl (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) {p : M'} {a : M}
    (hpa : π p = a) (cidx : {j // a ∈ F.hyp j} → Fin n) (σ : Fin c ↪ Fin n) (i : Fin c) {j : F.ι}
    (hk : p ∈ (F.totalTransform π Y).hyp (toLex (Sum.inl j))) :
    totalTransformIdx h hF hpa cidx σ i ⟨toLex (Sum.inl j), hk⟩ =
      cidx ⟨j, hpa ▸
        strictTransform_subset_preimage h.contMDiff.continuous (hF.1 j).isClosed hk⟩ :=
  rfl

/-- The index of the exceptional component of the total transform in the blow-up chart of index
`i` is `σ i`. -/
theorem totalTransformIdx_inr (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) {p : M'} {a : M}
    (hpa : π p = a) (cidx : {j // a ∈ F.hyp j} → Fin n) (σ : Fin c ↪ Fin n) (i : Fin c)
    (hk : p ∈ (F.totalTransform π Y).hyp (toLex (Sum.inr PUnit.unit))) :
    totalTransformIdx h hF hpa cidx σ i ⟨toLex (Sum.inr PUnit.unit), hk⟩ = σ i :=
  rfl

/-- The adapted coordinates `(u_i, (u_k)_{k ≠ i}, w)` of the total transform: over `a ∈ Y`, a
blow-up chart `Φ` of index `i` over a chart `φ` adapted to `Y` which is an snc chart of `F` at `a`
is an snc chart of the total transform at every point of its source over `a`, with the indices
`cidx` on the strict transforms and `σ i` on the exceptional divisor. -/
theorem totalTransform_isSncChartAt (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ)
    {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} (hφ : IsAdaptedChart ψ Y φ σ) {a : M}
    {cidx : {j // a ∈ F.hyp j} → Fin n} (hc : F.IsSncChartAt ψ φ a cidx) {i : Fin c}
    {Φ : OpenPartialHomeomorph M' E} (hΦ : IsBlowUpChart ψ π φ σ i Φ) {p : M'} (hp : p ∈ Φ.source)
    (hpa : π p = a) :
    (F.totalTransform π Y).IsSncChartAt ψ Φ p (totalTransformIdx h hF hpa cidx σ i) := by
  -- the component through `a` under a component through `p`, and its chart identity
  have hover : ∀ j : F.ι, p ∈ strictTransformSet π Y (F.hyp j) → a ∈ F.hyp j := fun j hpj =>
    hpa ▸ mem_hyp_of_mem_strictTransform h hF hpj
  have key : ∀ (j : F.ι) (hpj : p ∈ strictTransformSet π Y (F.hyp j)), ∀ x ∈ Φ.source,
      x ∈ strictTransformSet π Y (F.hyp j) ↔ ψ (Φ x) (cidx ⟨j, hover j hpj⟩) = 0 := by
    intro j hpj x hx
    have hH : ∀ x ∈ φ.source, x ∈ F.hyp j ↔ ψ (φ x) (cidx ⟨j, hover j hpj⟩) = 0 := fun x hx =>
      hc.mem_iff ⟨j, hover j hpj⟩ hx
    by_cases hin : ∃ k, σ k = cidx ⟨j, hover j hpj⟩
    · obtain ⟨k, hk⟩ := hin
      rw [← hk] at hH ⊢
      by_cases hik : i = k
      · subst hik
        have e := strictTransform_inter_source_self hφ hΦ hH
        exact absurd ((Set.ext_iff.mp e p).mp ⟨hpj, hp⟩) (Set.notMem_empty p)
      · have e := strictTransform_inter_source_of_ne hφ hΦ hH hik
        exact ⟨fun hxj => ((Set.ext_iff.mp e x).mp ⟨hxj, hx⟩).2,
          fun hxc => ((Set.ext_iff.mp e x).mpr ⟨hx, hxc⟩).1⟩
    · have hj : ∀ k, σ k ≠ cidx ⟨j, hover j hpj⟩ := fun k hk => hin ⟨k, hk⟩
      have e := strictTransform_inter_source_off hφ hΦ hj hH
      exact ⟨fun hxj => ((Set.ext_iff.mp e x).mp ⟨hxj, hx⟩).2,
        fun hxc => ((Set.ext_iff.mp e x).mpr ⟨hx, hxc⟩).1⟩
  -- a component through `p` has index different from `σ i`
  have hne : ∀ (j : F.ι) (hpj : p ∈ strictTransformSet π Y (F.hyp j)),
      cidx ⟨j, hover j hpj⟩ ≠ σ i := by
    intro j hpj hij
    have hH : ∀ x ∈ φ.source, x ∈ F.hyp j ↔ ψ (φ x) (σ i) = 0 := fun x hx => by
      rw [← hij]; exact hc.mem_iff ⟨j, hover j hpj⟩ hx
    have e := strictTransform_inter_source_self hφ hΦ hH
    exact absurd ((Set.ext_iff.mp e p).mp ⟨hpj, hp⟩) (Set.notMem_empty p)
  refine ⟨hΦ.mem_maximalAtlas, hp, ?_, ?_⟩
  · rintro ⟨k, hk⟩ x hx
    obtain j | u := k
    · exact key j hk x hx
    · exact hΦ.mem_preimage_iff hφ hx
  · rintro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ heq
    obtain j₁ | u₁ := k₁ <;> obtain j₂ | u₂ := k₂
    · have : (⟨j₁, hover j₁ hk₁⟩ : {j // a ∈ F.hyp j}) = ⟨j₂, hover j₂ hk₂⟩ := hc.injective heq
      have hj : j₁ = j₂ := congrArg Subtype.val this
      subst hj
      rfl
    · exact absurd heq (hne j₁ hk₁)
    · exact absurd heq.symm (hne j₂ hk₂)
    · rfl

/-- Off the exceptional divisor, the snc chart of `F` at `π p` transported along a local inverse
of `π` is an snc chart of the total transform at `p`. -/
theorem exists_isSncChartAt_totalTransform_of_notMem
    (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) {p : M'}
    (hpY : π p ∉ Y) :
    ∃ (Φ : OpenPartialHomeomorph M' E) (c' : {k // p ∈ (F.totalTransform π Y).hyp k} → Fin n),
      (F.totalTransform π Y).IsSncChartAt ψ Φ p c' := by
  have hπc : Continuous π := h.contMDiff.continuous
  obtain ⟨Ψ, hpΨ, hEq⟩ := (h.isLocalDiffeomorphOn_compl ⟨p, hpY⟩).exists_partialDiffeomorph
  obtain ⟨φ, cidx, hc⟩ := hF.exists_isSncChartAt (π p)
  have hopen : IsOpen (π ⁻¹' Yᶜ) := hY.isClosed.isOpen_compl.preimage hπc
  -- the transported chart, restricted off the exceptional divisor
  set e₀ := transportChart Ψ.symm φ with he₀
  have he₀mem : e₀ ∈ maximalAtlas 𝓘(𝕜, E) ω M' := transportChart_mem_maximalAtlas Ψ.symm hc.1
  set e := e₀.restrOpen (π ⁻¹' Yᶜ) hopen with he
  have hemem : e ∈ maximalAtlas 𝓘(𝕜, E) ω M' := by
    rw [he, OpenPartialHomeomorph.restrOpen_eq_restr]
    exact restr_mem_maximalAtlas _ he₀mem hopen
  -- points of the source lie off `F`, in `Ψ.source`, with `Ψ x = π x` and `e x = φ (π x)`
  have hsrc : ∀ x ∈ e.source, x ∈ Ψ.source ∧ π x ∉ Y ∧ π x ∈ φ.source ∧ e x = φ (π x) := by
    intro x hx
    have hx' : x ∈ e₀.source ∧ x ∈ π ⁻¹' Yᶜ := by
      simpa [he, OpenPartialHomeomorph.restrOpen_source] using hx
    have hx₀ := hx'.1
    rw [he₀, transportChart_source] at hx₀
    have hxΨ : x ∈ Ψ.source := hx₀.1
    have hΨx : Ψ.symm.invFun x = π x := by
      change Ψ x = π x
      exact (hEq hxΨ).symm
    refine ⟨hxΨ, hx'.2, ?_, ?_⟩
    · have := hx₀.2
      rwa [Set.mem_preimage, hΨx] at this
    · change e₀ x = φ (π x)
      rw [he₀, transportChart_apply, hΨx]
  have hpe : p ∈ e.source := by
    simp only [he, OpenPartialHomeomorph.restrOpen_source, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff]
    refine ⟨?_, hpY⟩
    rw [he₀, transportChart_source]
    refine ⟨hpΨ, ?_⟩
    change Ψ p ∈ φ.source
    rw [← hEq hpΨ]
    exact hc.2.1
  -- the components through `p` lie over the components through `π p`
  have hover : ∀ k : {k // p ∈ (F.totalTransform π Y).hyp k}, ∃ j : {j // π p ∈ F.hyp j},
      k.1 = toLex (Sum.inl j.1) := by
    rintro ⟨k, hk⟩
    obtain j | u := k
    · exact ⟨⟨j, mem_hyp_of_mem_strictTransform h hF hk⟩, rfl⟩
    · exact absurd hk hpY
  choose idx hidx using hover
  refine ⟨e, fun k => cidx (idx k), hemem, hpe, ?_, ?_⟩
  · rintro ⟨k, hk⟩ x hx
    obtain ⟨hxΨ, hxY, hxφ, hex⟩ := hsrc x hx
    obtain j | u := k
    · have h0 : toLex (Sum.inl j) = toLex (Sum.inl (idx ⟨toLex (Sum.inl j), hk⟩).1) :=
        hidx ⟨toLex (Sum.inl j), hk⟩
      have hj : (idx ⟨toLex (Sum.inl j), hk⟩).1 = j := (Sum.inl_injective (toLex.injective h0)).symm
      have hm := hc.mem_iff (idx ⟨toLex (Sum.inl j), hk⟩) hxφ
      rw [hj] at hm
      change x ∈ strictTransformSet π Y (F.hyp j) ↔
        ψ (e x) (cidx (idx ⟨toLex (Sum.inl j), hk⟩)) = 0
      rw [mem_strictTransform_iff_of_notMem h hF hxY, hex]
      exact hm
    · exact absurd (hk : π p ∈ Y) hpY
  · intro k₁ k₂ heq
    have h1 := hidx k₁
    have h2 := hidx k₂
    have : idx k₁ = idx k₂ := hc.injective heq
    exact Subtype.ext (h1.trans (by rw [this, ← h2]))

/-- If `Y` has simple normal crossings with the snc divisor `F`, the total transform of `F` under
the blowing-up along `Y` is a simple normal crossings divisor ([Kol07, Definition 25];
[BM97, (1.2)]). -/
theorem isSnc_totalTransform (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) (hsnc : F.HasSncWith ψ Y c) :
    (F.totalTransform π Y).IsSnc ψ := by
  have hπc : Continuous π := h.contMDiff.continuous
  refine ⟨?_, ?_, ?_⟩
  · -- the components are closed smooth hypersurfaces
    intro k
    obtain j | u := k
    · change IsClosedSubmanifold ψ (strictTransformSet π Y (F.hyp j)) 1
      refine isClosedSubmanifold_strictTransform_of_charts hY h (hF.1 j) ?_
      rintro a ⟨haj, haY⟩
      obtain ⟨φ, σ, cidx, hφ, hc⟩ := hsnc a haY
      exact ⟨φ, σ, cidx ⟨j, haj⟩, hc.2.1, hφ, fun x hx => hc.mem_iff ⟨j, haj⟩ hx⟩
    · change IsClosedSubmanifold ψ (π ⁻¹' Y) 1
      exact h.isClosedSubmanifold_preimage hY
  · -- local finiteness: each strict transform lies in the preimage of its component
    intro p
    obtain ⟨U, hU, hfin⟩ := hF.2.1 (π p)
    refine ⟨π ⁻¹' U, hπc.continuousAt.preimage_mem_nhds hU, ?_⟩
    have hsub : {k : (F.totalTransform π Y).ι | ((F.totalTransform π Y).hyp k ∩ π ⁻¹' U).Nonempty}
        ⊆ (fun j => toLex (Sum.inl j)) '' {j | (F.hyp j ∩ U).Nonempty} ∪
          {toLex (Sum.inr PUnit.unit)} := by
      intro k hk
      obtain j | u := k
      · obtain ⟨q, hq, hqU⟩ := hk
        exact Or.inl ⟨j, ⟨π q, mem_hyp_of_mem_strictTransform h hF hq, hqU⟩, rfl⟩
      · exact Or.inr rfl
    exact ((hfin.image _).union (Set.finite_singleton _)).subset hsub
  · -- an snc chart at every point
    intro p
    by_cases hpY : π p ∈ Y
    · obtain ⟨φ, σ, cidx, hφ, hc⟩ := hsnc (π p) hpY
      obtain ⟨i, Φ, hΦ, hp⟩ := h.cover φ σ hφ p hc.2.1
      exact ⟨Φ, _, totalTransform_isSncChartAt h hF hφ hc hΦ hp rfl⟩
    · exact exists_isSncChartAt_totalTransform_of_notMem hY h hF hpY

end HypersurfaceFamily

end Manifold
