/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Charts
import Hironaka.Analytic.Germ.CoordDiv
import Hironaka.Manifold.BlowUp.Transition
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The lifting lemma: chart changes lift to the blow-up charts

Conditions (1) and (2) of [BM88, Definition 4.1] determine the blowing-up uniquely up to an
isomorphism commuting with the blow-down map. This rests on lifting a centre-preserving analytic
isomorphism `g` between open subsets of `𝕜ⁿ` to the blow-up charts, the analytic heart of the
construction of the blowing-up of a manifold and of its uniqueness. This file proves that lifting
lemma in coordinates.

* **Coordinate division on an open set.** For `F` analytic on an open set `N` and vanishing on
  the hyperplane `{x_k = 0}`, the canonical quotient `coordQuot k F` (`F x / x_k` off the
  hyperplane, `∂_k F x` on it) is analytic on `N` with `F = x_k · coordQuot k F`. This is
  coordinate division on a polydisc at the origin (`exists_eq_mul_coord_of_vanish`) translated to
  each point of the hyperplane, the quotient being canonical.
* **The direction vector.** `g_normal(π_i u) = u_{σ i} · D(u)`, where `D_k` is the canonical
  quotient by `u_{σ i}` of the normal components of `g ∘ π_i`. The vector `D(u)` is nonzero: off
  the exceptional hyperplane because `g` preserves the centre; on it because
  `D(u) = Dg(π_i u) d` with `d = ∂_{u_{σ i}} π_i(u)` a vector with `d_{σ i} = 1`, and a
  centre-preserving isomorphism has a derivative mapping the tangent space of the centre onto
  itself (tangency of `Dg` and `Dg⁻¹`, chain rule).
* **The lift.** Where `D_k ≠ 0`, `G(v) = (v_{σ i} D_k(v); D_l(v)/D_k(v); g(π_i v)_off)` is
  analytic and `π_k ∘ G = g ∘ π_i`; two continuous lifts through the same chart agree, by
  continuity from the dense set `{u_{σ i} ≠ 0}` where `π_k` is injective.
* **Two block embeddings.** The source chart's centre is `{x_σ = 0}` and the target chart's is
  `{x_τ = 0}` for two embeddings `σ, τ : Fin c ↪ Fin n` of the same codimension: the situation
  of two adapted charts of the same submanifold, whose coordinate blocks need not occupy the same
  slots.
* **Congruence, the identity and the cocycle** for the direction quotients (`liftDir_congr`,
  `liftDir_self_of_eqOn_id`, `liftDir_of_eqOn_id`, `liftDir_comp`), all by the same density
  argument, and the identification of the lift of the identity with the transition map `T_ik`
  (`liftMap_eq_blowUpTransition`).

These are the inputs of the gluing of the blow-up charts into the blown-up manifold
(`Hironaka.Manifold.BlowUp.Atlas` and the modules gluing the atlas). The lifting lemma is
not proved in the source; the argument above is elementary.
-/

@[expose] public section

open scoped ContDiff Topology
open Filter Analytic

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- The coordinate projection `Fin n → 𝕜 →L[𝕜] 𝕜` with its ring and fibre fixed. -/
local notation "pr" => ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜)

/-! ### Coordinate division on an open set -/

section CoordQuot

variable (k : Fin n) (F : (Fin n → 𝕜) → 𝕜)

/-- The canonical quotient of `F` by the coordinate `x_k`: `F x / x_k` off the hyperplane
`{x_k = 0}`, the partial derivative `∂_k F x` on it. -/
noncomputable def coordQuot (x : Fin n → 𝕜) : 𝕜 :=
  if x k = 0 then fderiv 𝕜 F x (Pi.single k 1) else F x / x k

/-- The quotient off the hyperplane is the literal quotient. -/
theorem coordQuot_of_ne {x : Fin n → 𝕜} (hx : x k ≠ 0) : coordQuot k F x = F x / x k := by
  simp [coordQuot, hx]

/-- The quotient on the hyperplane is the partial derivative. -/
theorem coordQuot_of_eq {x : Fin n → 𝕜} (hx : x k = 0) :
    coordQuot k F x = fderiv 𝕜 F x (Pi.single k 1) := by
  simp [coordQuot, hx]

/-- `x_k · coordQuot k F x = F x` for `F` vanishing on the hyperplane. -/
theorem mul_coordQuot {N : Set (Fin n → 𝕜)} (h0 : ∀ x ∈ N, x k = 0 → F x = 0) {x : Fin n → 𝕜}
    (hx : x ∈ N) : x k * coordQuot k F x = F x := by
  by_cases hxk : x k = 0
  · rw [hxk, zero_mul, h0 x hx hxk]
  · rw [coordQuot_of_ne k F hxk]
    field_simp

/-- If `G = x_k · Q` on an open set with `Q` analytic, then `Q` is the partial derivative of `G`
on the hyperplane. -/
theorem eq_fderiv_of_eq_mul {G Q : (Fin n → 𝕜) → 𝕜} {U : Set (Fin n → 𝕜)} (hU : IsOpen U)
    (hQ : AnalyticOnNhd 𝕜 Q U) (h : ∀ y ∈ U, G y = y k * Q y) {y : Fin n → 𝕜} (hy : y ∈ U)
    (hyk : y k = 0) : fderiv 𝕜 G y (Pi.single k 1) = Q y := by
  have h1 : HasFDerivAt (fun y : Fin n → 𝕜 => y k * Q y)
      (y k • fderiv 𝕜 Q y + Q y • pr k) y :=
    (hasFDerivAt_apply (𝕜 := 𝕜) k y).mul (hQ y hy).differentiableAt.hasFDerivAt
  have hG : HasFDerivAt G (y k • fderiv 𝕜 Q y + Q y • pr k) y :=
    h1.congr_of_eventuallyEq (eventuallyEq_of_mem (hU.mem_nhds hy) fun z hz => h z hz)
  rw [hG.fderiv]
  simp [hyk]

/-- Coordinate division on an open set: the canonical quotient of an analytic function vanishing
on the hyperplane `{x_k = 0}` is analytic. The division on a polydisc at the origin is translated
to each point of the hyperplane. -/
theorem analyticOnNhd_coordQuot {N : Set (Fin n → 𝕜)} (hN : IsOpen N) (hF : AnalyticOnNhd 𝕜 F N)
    (h0 : ∀ x ∈ N, x k = 0 → F x = 0) : AnalyticOnNhd 𝕜 (coordQuot k F) N := by
  intro p hp
  by_cases hpk : p k = 0
  · -- translate `F` to the origin and divide there on a polydisc ℝ
    have hev : ∀ᶠ y in 𝓝 (0 : Fin n → 𝕜), p + y ∈ N := by
      have ht : Tendsto (fun y : Fin n → 𝕜 => p + y) (𝓝 0) (𝓝 p) :=
        (continuous_const.add continuous_id).tendsto' 0 p (by simp)
      exact ht (hN.mem_nhds hp)
    obtain ⟨ρ, hρ⟩ := exists_polydisc_of_eventually hev
    have hopen : IsOpen (polydisc 𝕜 ρ) := isOpen_polydisc ρ
    have hGan : AnalyticOnNhd 𝕜 (fun y => F (p + y)) (polydisc 𝕜 ρ) := fun y hy =>
      (hF _ (hρ y hy)).comp_of_eq (analyticAt_const.add analyticAt_id) rfl
    have hG0 : ∀ y ∈ polydisc 𝕜 ρ, y k = 0 → F (p + y) = 0 := fun y hy hyk =>
      h0 _ (hρ y hy) (by simp [hpk, hyk])
    obtain ⟨Q, hQ, hGQ⟩ := exists_eq_mul_coord_of_vanish k hGan hG0
    have key : ∀ y ∈ polydisc 𝕜 ρ, coordQuot k F (p + y) = Q y := by
      intro y hy
      by_cases hyk : y k = 0
      · rw [coordQuot_of_eq k F (by simp [hpk, hyk])]
        have hd : HasFDerivAt (fun y : Fin n → 𝕜 => F (p + y)) (fderiv 𝕜 F (p + y)) y := by
          have h1 : HasFDerivAt (fun y : Fin n → 𝕜 => p + y) (ContinuousLinearMap.id 𝕜 _) y :=
            (hasFDerivAt_id y).const_add p
          have h2 := (hF _ (hρ y hy)).differentiableAt.hasFDerivAt.comp y h1
          rw [ContinuousLinearMap.comp_id] at h2
          exact h2
        rw [← hd.fderiv]
        exact eq_fderiv_of_eq_mul k hopen hQ hGQ hy hyk
      · rw [coordQuot_of_ne k F (by simpa [hpk] using hyk), hGQ y hy]
        simp only [Pi.add_apply, hpk, zero_add]
        field_simp
    have h0ρ : (0 : Fin n → 𝕜) ∈ polydisc 𝕜 ρ := fun j => by
      rw [Pi.zero_apply, norm_zero]; exact_mod_cast ρ.2 j
    have hQp : AnalyticAt 𝕜 (fun x => Q (x - p)) p :=
      (hQ 0 h0ρ).comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self p)
    refine hQp.congr ?_
    have hmem : ∀ᶠ x in 𝓝 p, x - p ∈ polydisc 𝕜 ρ := by
      have ht : Tendsto (fun x : Fin n → 𝕜 => x - p) (𝓝 p) (𝓝 0) :=
        (continuous_id.sub continuous_const).tendsto' p 0 (by simp)
      exact ht (hopen.mem_nhds h0ρ)
    filter_upwards [hmem] with x hx
    have := key (x - p) hx
    rw [add_sub_cancel] at this
    exact this.symm
  · have hev : ∀ᶠ x in 𝓝 p, x k ≠ 0 := (continuous_apply k).continuousAt.eventually_ne hpk
    refine ((hF p hp).div (analyticAt_apply k p) hpk).congr ?_
    filter_upwards [hev] with x hx
    exact (coordQuot_of_ne k F hx).symm

end CoordQuot

/-! ### Tangency and the chain rule for centre-preserving maps -/

section Tangency

variable {c : ℕ} (σ τ : Fin c ↪ Fin n)

/-- A map carrying the coordinate subspace `{x_σ = 0}` into `{x_τ = 0}` near `x` has a derivative
mapping the tangent vectors of the first into those of the second. -/
theorem fderiv_apply_mem_of_preserves_center {h : (Fin n → 𝕜) → (Fin n → 𝕜)} {U : Set (Fin n → 𝕜)}
    (hU : IsOpen U) (hh : AnalyticOnNhd 𝕜 h U) (hpres : ∀ y ∈ U, y ∈ blowUpCenter σ →
      h y ∈ blowUpCenter τ) {x : Fin n → 𝕜} (hx : x ∈ U) (hxc : x ∈ blowUpCenter σ)
    {t : Fin n → 𝕜} (ht : ∀ k, t (σ k) = 0) (k : Fin c) : fderiv 𝕜 h x t (τ k) = 0 := by
  -- the curve `s ↦ x + s • t` stays in the centre and, near `0`, in `U`
  have hline : HasDerivAt (fun s : 𝕜 => x + s • t) t 0 := by
    simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const t).const_add x
  have hcurve : HasDerivAt (fun s : 𝕜 => h (x + s • t) (τ k)) (fderiv 𝕜 h x t (τ k)) 0 := by
    have h1 : HasDerivAt (fun s : 𝕜 => h (x + s • t)) (fderiv 𝕜 h x t) 0 := by
      exact (hh x hx).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (0 : 𝕜) hline (by simp)
    exact (pr (τ k)).hasFDerivAt.comp_hasDerivAt (0 : 𝕜) h1
  have hev : ∀ᶠ s : 𝕜 in 𝓝 0, h (x + s • t) (τ k) = 0 := by
    have hU' : ∀ᶠ s : 𝕜 in 𝓝 0, x + s • t ∈ U := by
      have ht0 : Tendsto (fun s : 𝕜 => x + s • t) (𝓝 0) (𝓝 x) := by
        simpa using hline.continuousAt.tendsto
      exact ht0 (hU.mem_nhds hx)
    filter_upwards [hU'] with s hs
    have hmem : x + s • t ∈ blowUpCenter σ := fun l => by
      simp [Pi.add_apply, Pi.smul_apply, hxc l, ht l]
    exact hpres _ hs hmem k
  have h0 : HasDerivAt (fun s : 𝕜 => h (x + s • t) (τ k)) 0 0 :=
    (hasDerivAt_const (0 : 𝕜) (0 : 𝕜)).congr_of_eventuallyEq
      (by filter_upwards [hev] with s hs; simpa using hs)
  exact hcurve.unique h0

/-- Chain rule for a two-sided inverse on an open set: `Dg'(g x) ∘ Dg(x) = id`. -/
theorem fderiv_comp_fderiv_eq_id {g g' : (Fin n → 𝕜) → (Fin n → 𝕜)} {V₁ V₂ : Set (Fin n → 𝕜)}
    (hV₁ : IsOpen V₁) (hg : AnalyticOnNhd 𝕜 g V₁) (hg' : AnalyticOnNhd 𝕜 g' V₂)
    (hmaps : ∀ x ∈ V₁, g x ∈ V₂) (hgg' : ∀ x ∈ V₁, g' (g x) = x) {x : Fin n → 𝕜} (hx : x ∈ V₁) :
    (fderiv 𝕜 g' (g x)).comp (fderiv 𝕜 g x) = ContinuousLinearMap.id 𝕜 (Fin n → 𝕜) := by
  rw [← fderiv_comp x (hg' _ (hmaps x hx)).differentiableAt (hg x hx).differentiableAt]
  have : (g' ∘ g) =ᶠ[𝓝 x] id := eventuallyEq_of_mem (hV₁.mem_nhds hx) fun z hz => hgg' z hz
  rw [this.fderiv_eq, fderiv_id]

end Tangency

/-! ### The direction vector and the lift -/

section Lift

variable {c : ℕ} (σ τ : Fin c ↪ Fin n) (i : Fin c) (g : (Fin n → 𝕜) → (Fin n → 𝕜))

/-- The normal components of `g ∘ π_i` in the target block `τ`. -/
noncomputable def normalComp (k : Fin c) (u : Fin n → 𝕜) : 𝕜 := g (blowUpChartMap σ i u) (τ k)

/-- The direction quotient `D_k = (g ∘ π_i)_{τ k} / u_{σ i}`, canonical across `{u_{σ i} = 0}`. -/
noncomputable def liftDir (k : Fin c) : (Fin n → 𝕜) → 𝕜 :=
  coordQuot (σ i) (normalComp σ τ i g k)

/-- The lift of `g` from chart `i` (block `σ`) to chart `k` (block `τ`): `u'_{τ k} = u_{σ i} D_k`,
`u'_{τ l} = D_l / D_k`, the coordinates off the block `τ` those of `g ∘ π_i`. -/
noncomputable def liftMap (k : Fin c) (v : Fin n → 𝕜) : Fin n → 𝕜 := by
  classical
  exact fun j => if h : ∃ l, τ l = j then
      (if h.choose = k then v (σ i) * liftDir σ τ i g k v
        else liftDir σ τ i g h.choose v / liftDir σ τ i g k v)
    else g (blowUpChartMap σ i v) j

variable {σ τ i g}

/-- The lift at the target scaling slot: `u'_{τ k} = u_{σ i} D_k`. -/
theorem liftMap_apply_k (k : Fin c) (v : Fin n → 𝕜) :
    liftMap σ τ i g k v (τ k) = v (σ i) * liftDir σ τ i g k v := by
  classical
  simp [liftMap]

/-- The lift at a target ratio slot: `u'_{τ l} = D_l / D_k`. -/
theorem liftMap_apply_block {k l : Fin c} (hlk : l ≠ k) (v : Fin n → 𝕜) :
    liftMap σ τ i g k v (τ l) = liftDir σ τ i g l v / liftDir σ τ i g k v := by
  classical
  simp [liftMap, hlk]

/-- The lift off the target block: the coordinates of `g ∘ π_i`. -/
theorem liftMap_apply_off (k : Fin c) (v : Fin n → 𝕜) {j : Fin n} (hj : ∀ l, τ l ≠ j) :
    liftMap σ τ i g k v j = g (blowUpChartMap σ i v) j := by
  classical
  have h : ¬ ∃ l, τ l = j := fun ⟨l, hl⟩ => hj l hl
  simp [liftMap, h]

variable {V₁ V₂ : Set (Fin n → 𝕜)} (hV₁ : IsOpen V₁) (hg : AnalyticOnNhd 𝕜 g V₁)
  (hc : ∀ x ∈ V₁, x ∈ blowUpCenter σ ↔ g x ∈ blowUpCenter τ)

include hc in
/-- The normal components of `g ∘ π_i` vanish on `{u_{σ i} = 0}`. -/
theorem normalComp_eq_zero (k : Fin c) {u : Fin n → 𝕜} (hu : blowUpChartMap σ i u ∈ V₁)
    (h0 : u (σ i) = 0) : normalComp σ τ i g k u = 0 := by
  have hmem : blowUpChartMap σ i u ∈ blowUpCenter σ := (blowUpChartMap_mem_center_iff σ u).mpr h0
  exact (hc _ hu).mp hmem k

include hg in
/-- The normal components of `g ∘ π_i` are analytic. -/
theorem analyticOnNhd_normalComp (k : Fin c) :
    AnalyticOnNhd 𝕜 (normalComp σ τ i g k) (blowUpChartMap σ i ⁻¹' V₁) := fun u hu =>
  (analyticAt_apply (τ k) _).comp ((hg _ hu).comp
    ((contDiff_blowUpChartMap σ).contDiffAt.analyticAt (x := u)))

include hV₁ hg hc in
/-- The direction quotients are analytic on `π_i⁻¹(V₁)`. -/
theorem analyticOnNhd_liftDir (k : Fin c) :
    AnalyticOnNhd 𝕜 (liftDir σ τ i g k) (blowUpChartMap σ i ⁻¹' V₁) :=
  analyticOnNhd_coordQuot (σ i) _ (hV₁.preimage (contDiff_blowUpChartMap σ).continuous)
    (analyticOnNhd_normalComp hg k) fun _ hu h0 => normalComp_eq_zero hc k hu h0

include hc in
/-- `u_{σ i} · D_k(u) = (g ∘ π_i)(u)_{τ k}`. -/
theorem mul_liftDir (k : Fin c) {u : Fin n → 𝕜} (hu : blowUpChartMap σ i u ∈ V₁) :
    u (σ i) * liftDir σ τ i g k u = g (blowUpChartMap σ i u) (τ k) :=
  mul_coordQuot (σ i) _ (fun _ hv h0 => normalComp_eq_zero hc k hv h0) hu

variable (hV₂ : IsOpen V₂) {g' : (Fin n → 𝕜) → (Fin n → 𝕜)} (hg₁ : Set.BijOn g V₁ V₂)
  (hg' : AnalyticOnNhd 𝕜 g' V₂) (hgg' : ∀ x ∈ V₁, g' (g x) = x)

include hV₁ hg hc hV₂ hg₁ hg' hgg' in
/-- The direction vector is nonzero: some `D_k(u) ≠ 0`. -/
theorem exists_liftDir_ne_zero {u : Fin n → 𝕜} (hu : blowUpChartMap σ i u ∈ V₁) :
    ∃ k, liftDir σ τ i g k u ≠ 0 := by
  by_cases h0 : u (σ i) = 0
  · -- on the exceptional hyperplane: `D(u) = Dg(x₀) d` with `d_{σ i} = 1`
    set x₀ := blowUpChartMap σ i u with hx₀
    have hx₀c : x₀ ∈ blowUpCenter σ := (blowUpChartMap_mem_center_iff σ u).mpr h0
    set d := fderiv 𝕜 (blowUpChartMap σ i) u (Pi.single (σ i) 1) with hd
    have hπ : HasFDerivAt (blowUpChartMap σ i) (fderiv 𝕜 (blowUpChartMap σ i) u) u :=
      ((contDiff_blowUpChartMap (𝕜 := 𝕜) σ (i := i)).contDiffAt.differentiableAt
        (by simp)).hasFDerivAt
    -- `d_{σ i} = 1`
    have hdi : d (σ i) = 1 := by
      have h1 : HasFDerivAt (fun v : Fin n → 𝕜 => blowUpChartMap σ i v (σ i))
          ((pr (σ i)).comp (fderiv 𝕜 (blowUpChartMap σ i) u)) u :=
        (pr (σ i)).hasFDerivAt.comp u hπ
      have h2 : HasFDerivAt (fun v : Fin n → 𝕜 => blowUpChartMap σ i v (σ i))
          (pr (σ i)) u := by
        have := hasFDerivAt_apply (𝕜 := 𝕜) (σ i) u
        refine this.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
        exact blowUpChartMap_apply_scaling σ (i := i) v
      have := congrArg (fun L => L (Pi.single (σ i) 1)) (h1.unique h2)
      simpa [d] using this
    -- `D_k(u) = (Dg(x₀) d)_{τ k}`
    have hDk : ∀ k, liftDir σ τ i g k u = fderiv 𝕜 g x₀ d (τ k) := by
      intro k
      rw [liftDir, coordQuot_of_eq _ _ h0]
      have hF : HasFDerivAt (normalComp σ τ i g k)
          ((pr (τ k)).comp ((fderiv 𝕜 g x₀).comp
            (fderiv 𝕜 (blowUpChartMap σ i) u))) u := by
        have hgx : HasFDerivAt g (fderiv 𝕜 g x₀) x₀ := (hg _ hu).differentiableAt.hasFDerivAt
        exact (pr (τ k)).hasFDerivAt.comp u (hgx.comp u hπ)
      rw [hF.fderiv]
      rfl
    by_contra hcon
    push Not at hcon
    -- `Dg(x₀) d` is tangent to the centre, hence so is `d = Dg'(g x₀) (Dg(x₀) d)`
    have hmaps : ∀ x ∈ V₁, g x ∈ V₂ := fun x hx => hg₁.mapsTo hx
    have hpres' : ∀ y ∈ V₂, y ∈ blowUpCenter τ → g' y ∈ blowUpCenter σ := by
      intro y hy hyc
      obtain ⟨x, hx, rfl⟩ := hg₁.surjOn hy
      rw [hgg' x hx]
      exact (hc x hx).mpr hyc
    have hw : ∀ k, fderiv 𝕜 g x₀ d (τ k) = 0 := fun k => by rw [← hDk k]; exact hcon k
    have hgx₀ : g x₀ ∈ V₂ := hmaps x₀ hu
    have hgx₀c : g x₀ ∈ blowUpCenter τ := (hc x₀ hu).mp hx₀c
    have hdt : fderiv 𝕜 g' (g x₀) (fderiv 𝕜 g x₀ d) (σ i) = 0 :=
      fderiv_apply_mem_of_preserves_center τ σ hV₂ hg' hpres' hgx₀ hgx₀c hw i
    have hid := congrArg (fun L => L d (σ i)) (fderiv_comp_fderiv_eq_id hV₁ hg hg' hmaps hgg' hu)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hid
    rw [hid, hdi] at hdt
    exact one_ne_zero hdt
  · -- off the hyperplane: `g(π_i u)` is off the centre
    have hnot : g (blowUpChartMap σ i u) ∉ blowUpCenter τ := fun hmem =>
      h0 ((blowUpChartMap_mem_center_iff σ u).mp ((hc _ hu).mpr hmem))
    obtain ⟨k, hk⟩ : ∃ k, g (blowUpChartMap σ i u) (τ k) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hnot hall
    refine ⟨k, fun hD => hk ?_⟩
    rw [← mul_liftDir hc k hu, hD, mul_zero]

include hc in
/-- The lift commutes with the blow-down: `π_k ∘ G = g ∘ π_i` where `D_k ≠ 0`. -/
theorem blowUpChartMap_liftMap (k : Fin c) {v : Fin n → 𝕜} (hv : blowUpChartMap σ i v ∈ V₁)
    (hk : liftDir σ τ i g k v ≠ 0) :
    blowUpChartMap τ k (liftMap σ τ i g k v) = g (blowUpChartMap σ i v) := by
  funext j
  rcases exists_eq_or_forall_ne τ j with ⟨l, rfl⟩ | hj
  · by_cases hlk : l = k
    · subst hlk
      rw [blowUpChartMap_apply_scaling, liftMap_apply_k, mul_liftDir hc _ hv]
    · rw [blowUpChartMap_apply_ratio τ _ hlk, liftMap_apply_k, liftMap_apply_block hlk,
        ← mul_liftDir hc l hv]
      field_simp
  · rw [blowUpChartMap_apply_off τ _ hj, liftMap_apply_off k v hj]

include hV₁ hg hc in
/-- The lift is analytic where `D_k ≠ 0`. -/
theorem analyticOnNhd_liftMap (k : Fin c) :
    AnalyticOnNhd 𝕜 (liftMap σ τ i g k)
      (blowUpChartMap σ i ⁻¹' V₁ ∩ {v | liftDir σ τ i g k v ≠ 0}) := by
  rintro v ⟨hv, hk⟩
  refine analyticAt_pi_of_forall fun j => ?_
  rcases exists_eq_or_forall_ne τ j with ⟨l, rfl⟩ | hj
  · by_cases hlk : l = k
    · subst hlk
      refine ((analyticAt_apply (σ i) v).mul (analyticOnNhd_liftDir hV₁ hg hc l v hv)).congr ?_
      exact Eventually.of_forall fun w => (liftMap_apply_k l w).symm
    · refine ((analyticOnNhd_liftDir hV₁ hg hc l v hv).div
        (analyticOnNhd_liftDir hV₁ hg hc k v hv) hk).congr ?_
      exact Eventually.of_forall fun w => (liftMap_apply_block hlk w).symm
  · refine ((analyticAt_apply j _).comp ((hg _ hv).comp
      ((contDiff_blowUpChartMap σ).contDiffAt.analyticAt (x := v)))).congr ?_
    exact Eventually.of_forall fun w => (liftMap_apply_off k w hj).symm

include hV₁ hg hc hV₂ hg₁ hg' hgg' in
/-- **The lifting lemma**, local form: every point of `π_i⁻¹(V₁)` has a neighbourhood on which
`g ∘ π_i` factors analytically through some chart `k` of the target block. This is the analytic
content of the uniqueness clause of [BM88, Definition 4.1]. -/
theorem exists_lift_blowUpChartMap {u : Fin n → 𝕜} (hu : blowUpChartMap σ i u ∈ V₁) :
    ∃ (k : Fin c) (N : Set (Fin n → 𝕜)) (G : (Fin n → 𝕜) → (Fin n → 𝕜)), IsOpen N ∧ u ∈ N ∧
      AnalyticOnNhd 𝕜 G N ∧ ∀ v ∈ N, blowUpChartMap τ k (G v) = g (blowUpChartMap σ i v) := by
  obtain ⟨k, hk⟩ := exists_liftDir_ne_zero hV₁ hg hc hV₂ hg₁ hg' hgg' hu
  refine ⟨k, blowUpChartMap σ i ⁻¹' V₁ ∩ {v | liftDir σ τ i g k v ≠ 0}, liftMap σ τ i g k, ?_,
    ⟨hu, hk⟩, analyticOnNhd_liftMap hV₁ hg hc k, fun v ⟨hv, hvk⟩ =>
      blowUpChartMap_liftMap hc k hv hvk⟩
  have hpre : IsOpen (blowUpChartMap σ i ⁻¹' V₁) :=
    hV₁.preimage (contDiff_blowUpChartMap σ).continuous
  exact (analyticOnNhd_liftDir hV₁ hg hc k).continuousOn.isOpen_inter_preimage hpre
    isOpen_compl_singleton

end Lift

/-! ### Uniqueness of lifts by density -/

section Uniqueness

variable {c : ℕ} (σ : Fin c ↪ Fin n) {i k : Fin c}

/-- The complement of the exceptional hyperplane is dense in every open set: a point with
`v_{σ i} = 0` is a limit of points `v + s e_{σ i}`, `s ≠ 0`. -/
theorem subset_closure_ne {N : Set (Fin n → 𝕜)} (hN : IsOpen N) :
    N ⊆ closure {v ∈ N | v (σ i) ≠ 0} := by
  intro v hv
  rw [mem_closure_iff_nhds]
  intro U hU
  have hline : Tendsto (fun s : 𝕜 => v + s • Pi.single (σ i) (1 : 𝕜)) (𝓝 0) (𝓝 v) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 v (by simp)
  have hmem : ∀ᶠ s : 𝕜 in 𝓝[≠] 0, v + s • Pi.single (σ i) (1 : 𝕜) ∈ U ∩ N :=
    nhdsWithin_le_nhds (hline (Filter.inter_mem hU (hN.mem_nhds hv)))
  have hne : ∀ᶠ s : 𝕜 in 𝓝[≠] 0, v (σ i) + s ≠ 0 := by
    by_cases hvi : v (σ i) = 0
    · filter_upwards [self_mem_nhdsWithin] with s hs
      rw [hvi, zero_add]; exact hs
    · exact nhdsWithin_le_nhds
        ((continuous_const.add continuous_id).continuousAt.eventually_ne (by simpa using hvi))
  obtain ⟨s, hsU, hs⟩ := (hmem.and hne).exists
  refine ⟨v + s • Pi.single (σ i) (1 : 𝕜), hsU.1, hsU.2, ?_⟩
  simpa using hs

/-- Uniqueness of the lift: two continuous lifts of `g` through chart `k` on an open set agree.
They agree off the exceptional hyperplane, where `π_k` is injective (the lifts have
`G_v(τ k) ≠ 0` there because `g` carries the points off the centre off the centre), and the
complement is dense. -/
theorem eqOn_of_lift_blowUpChartMap {τ : Fin c ↪ Fin n} {N : Set (Fin n → 𝕜)} (hN : IsOpen N)
    {g G₁ G₂ : (Fin n → 𝕜) → (Fin n → 𝕜)} (h₁ : ContinuousOn G₁ N) (h₂ : ContinuousOn G₂ N)
    (hG₁ : ∀ v ∈ N, blowUpChartMap τ k (G₁ v) = g (blowUpChartMap σ i v))
    (hG₂ : ∀ v ∈ N, blowUpChartMap τ k (G₂ v) = g (blowUpChartMap σ i v))
    (hinj : ∀ v ∈ N, v (σ i) ≠ 0 → g (blowUpChartMap σ i v) ∉ blowUpCenter τ) :
    Set.EqOn G₁ G₂ N := by
  have hS : Set.EqOn G₁ G₂ {v ∈ N | v (σ i) ≠ 0} := by
    rintro v ⟨hv, hvi⟩
    have hk₁ : G₁ v (τ k) ≠ 0 := fun h0 => hinj v hv hvi (by
      rw [← hG₁ v hv]; exact (blowUpChartMap_mem_center_iff τ (G₁ v)).mpr h0)
    have hk₂ : G₂ v (τ k) ≠ 0 := fun h0 => hinj v hv hvi (by
      rw [← hG₂ v hv]; exact (blowUpChartMap_mem_center_iff τ (G₂ v)).mpr h0)
    exact blowUpChartMap_injOn τ hk₁ hk₂ ((hG₁ v hv).trans (hG₂ v hv).symm)
  exact hS.of_subset_closure h₁ h₂ (fun v hv => hv.1) (subset_closure_ne σ hN)

end Uniqueness

/-! ### Congruence, the identity and the cocycle for the direction quotients -/

section Cocycle

variable {c : ℕ} {σ τ ρ : Fin c ↪ Fin n} {i : Fin c}

/-- The direction quotients depend on `g` only near `π_i u`. -/
theorem liftDir_congr {g₁ g₂ : (Fin n → 𝕜) → (Fin n → 𝕜)} {V : Set (Fin n → 𝕜)} (hV : IsOpen V)
    (h : ∀ x ∈ V, g₁ x = g₂ x) (k : Fin c) {u : Fin n → 𝕜} (hu : blowUpChartMap σ i u ∈ V) :
    liftDir σ τ i g₁ k u = liftDir σ τ i g₂ k u := by
  have hev : normalComp σ τ i g₁ k =ᶠ[𝓝 u] normalComp σ τ i g₂ k := by
    have hpre : ∀ᶠ v in 𝓝 u, blowUpChartMap σ i v ∈ V :=
      (contDiff_blowUpChartMap σ).continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hu)
    filter_upwards [hpre] with v hv
    simp only [normalComp, h _ hv]
  simp only [liftDir, coordQuot, hev.fderiv_eq, hev.eq_of_nhds]

/-- The lift depends on `g` only near `π_i v`. -/
theorem liftMap_congr {g₁ g₂ : (Fin n → 𝕜) → (Fin n → 𝕜)} {V : Set (Fin n → 𝕜)} (hV : IsOpen V)
    (h : ∀ x ∈ V, g₁ x = g₂ x) (k : Fin c) {v : Fin n → 𝕜} (hv : blowUpChartMap σ i v ∈ V) :
    liftMap σ τ i g₁ k v = liftMap σ τ i g₂ k v := by
  funext j
  rcases exists_eq_or_forall_ne τ j with ⟨l, rfl⟩ | hj
  · by_cases hlk : l = k
    · subst hlk
      rw [liftMap_apply_k, liftMap_apply_k, liftDir_congr hV h l hv]
    · rw [liftMap_apply_block hlk, liftMap_apply_block hlk, liftDir_congr hV h l hv,
        liftDir_congr hV h k hv]
  · rw [liftMap_apply_off k v hj, liftMap_apply_off k v hj, h _ hv]

variable {g : (Fin n → 𝕜) → (Fin n → 𝕜)} {V : Set (Fin n → 𝕜)}

/-- A map equal to the identity on an open set is analytic there. -/
theorem analyticOnNhd_of_eqOn_id (hV : IsOpen V) (hid : ∀ x ∈ V, g x = x) :
    AnalyticOnNhd 𝕜 g V := fun _ hx =>
  analyticAt_id.congr (eventuallyEq_of_mem (hV.mem_nhds hx) fun y hy => (hid y hy).symm)

/-- A map equal to the identity on an open set preserves the centre there. -/
theorem mem_center_iff_of_eqOn_id (hid : ∀ x ∈ V, g x = x) :
    ∀ x ∈ V, x ∈ blowUpCenter σ ↔ g x ∈ blowUpCenter σ := by
  intro x hx
  rw [hid x hx]

/-- Where `g` is the identity, `D_i = 1`. -/
theorem liftDir_self_of_eqOn_id (hV : IsOpen V) (hid : ∀ x ∈ V, g x = x) {u : Fin n → 𝕜}
    (hu : blowUpChartMap σ i u ∈ V) : liftDir σ σ i g i u = 1 := by
  have hg := analyticOnNhd_of_eqOn_id hV hid
  have hc := mem_center_iff_of_eqOn_id (σ := σ) hid
  have hN : IsOpen (blowUpChartMap σ i ⁻¹' V) :=
    hV.preimage (contDiff_blowUpChartMap σ).continuous
  have hS : Set.EqOn (liftDir σ σ i g i) (fun _ => 1)
      {v ∈ blowUpChartMap σ i ⁻¹' V | v (σ i) ≠ 0} := by
    rintro v ⟨hv, hvi⟩
    have := mul_liftDir hc i hv
    rw [hid _ hv, blowUpChartMap_apply_scaling] at this
    exact mul_left_cancel₀ hvi (this.trans (mul_one _).symm)
  exact hS.of_subset_closure (analyticOnNhd_liftDir hV hg hc i).continuousOn continuousOn_const
    (fun v hv => hv.1) (subset_closure_ne σ hN) hu

/-- Where `g` is the identity, `D_k = u_{σ k}` for `k ≠ i`. -/
theorem liftDir_of_eqOn_id (hV : IsOpen V) (hid : ∀ x ∈ V, g x = x) {k : Fin c} (hk : k ≠ i)
    {u : Fin n → 𝕜} (hu : blowUpChartMap σ i u ∈ V) : liftDir σ σ i g k u = u (σ k) := by
  have hg := analyticOnNhd_of_eqOn_id hV hid
  have hc := mem_center_iff_of_eqOn_id (σ := σ) hid
  have hN : IsOpen (blowUpChartMap σ i ⁻¹' V) :=
    hV.preimage (contDiff_blowUpChartMap σ).continuous
  have hS : Set.EqOn (liftDir σ σ i g k) (fun v => v (σ k))
      {v ∈ blowUpChartMap σ i ⁻¹' V | v (σ i) ≠ 0} := by
    rintro v ⟨hv, hvi⟩
    have := mul_liftDir hc k hv
    rw [hid _ hv, blowUpChartMap_apply_ratio σ _ hk] at this
    exact mul_left_cancel₀ hvi this
  exact hS.of_subset_closure (analyticOnNhd_liftDir hV hg hc k).continuousOn
    (continuous_apply (σ k)).continuousOn (fun v hv => hv.1) (subset_closure_ne σ hN) hu

/-- The lift of (a map equal to) the identity from chart `i` to chart `k` is the transition map
`T_ik` of `Hironaka.Manifold.BlowUp.Charts`. -/
theorem liftMap_eq_blowUpTransition (hV : IsOpen V) (hid : ∀ x ∈ V, g x = x) (k : Fin c)
    {u : Fin n → 𝕜} (hu : blowUpChartMap σ i u ∈ V) (hk : liftDir σ σ i g k u ≠ 0) :
    liftMap σ σ i g k u = blowUpTransition σ i k u := by
  have hg := analyticOnNhd_of_eqOn_id hV hid
  have hc := mem_center_iff_of_eqOn_id (σ := σ) hid
  have hpre : IsOpen (blowUpChartMap σ i ⁻¹' V) :=
    hV.preimage (contDiff_blowUpChartMap σ).continuous
  have hNo : IsOpen (blowUpChartMap σ i ⁻¹' V ∩ {v | liftDir σ σ i g k v ≠ 0}) :=
    (analyticOnNhd_liftDir hV hg hc k).continuousOn.isOpen_inter_preimage hpre
      isOpen_compl_singleton
  have hdom : ∀ v ∈ blowUpChartMap σ i ⁻¹' V ∩ {v | liftDir σ σ i g k v ≠ 0},
      v ∈ blowUpTransitionDomain σ i k := by
    rintro v ⟨hv, hvk⟩
    by_cases hik : i = k
    · subst hik
      rw [blowUpTransitionDomain_self]
      exact Set.mem_univ v
    · rw [mem_blowUpTransitionDomain σ v hik, ← liftDir_of_eqOn_id hV hid (Ne.symm hik) hv]
      exact hvk
  refine eqOn_of_lift_blowUpChartMap (τ := σ) (i := i) (k := k) (g := g) σ hNo
    (analyticOnNhd_liftMap hV hg hc k).continuousOn
    ((analyticOnNhd_blowUpTransition σ).continuousOn.mono hdom) ?_ ?_ ?_ ⟨hu, hk⟩
  · rintro v ⟨hv, hvk⟩
    exact blowUpChartMap_liftMap hc k hv hvk
  · intro v hv
    rw [blowUpChartMap_blowUpTransition σ v (hdom v hv), hid _ hv.1]
  · rintro v ⟨hv, -⟩ hvi hmem
    rw [hid _ hv] at hmem
    exact hvi ((blowUpChartMap_mem_center_iff σ v).mp hmem)

/-- The cocycle of the direction quotients: for `g` followed by `g'`,
`D^{g' ∘ g}_l(u) = D^g_k(u) · D^{g'}_l(G_k u)` with `G_k` the lift of `g` to chart `k`. -/
theorem liftDir_comp {g' : (Fin n → 𝕜) → (Fin n → 𝕜)} {W : Set (Fin n → 𝕜)} (hV : IsOpen V)
    (hg : AnalyticOnNhd 𝕜 g V) (hc : ∀ x ∈ V, x ∈ blowUpCenter σ ↔ g x ∈ blowUpCenter τ)
    (hW : IsOpen W) (hg' : AnalyticOnNhd 𝕜 g' W)
    (hc' : ∀ x ∈ W, x ∈ blowUpCenter τ ↔ g' x ∈ blowUpCenter ρ) (hmaps : ∀ x ∈ V, g x ∈ W)
    (k l : Fin c) {u : Fin n → 𝕜} (hu : blowUpChartMap σ i u ∈ V) (hk : liftDir σ τ i g k u ≠ 0) :
    liftDir σ ρ i (g' ∘ g) l u =
      liftDir σ τ i g k u * liftDir τ ρ k g' l (liftMap σ τ i g k u) := by
  have hgg : AnalyticOnNhd 𝕜 (g' ∘ g) V := fun x hx => (hg' _ (hmaps x hx)).comp (hg x hx)
  have hcc : ∀ x ∈ V, x ∈ blowUpCenter σ ↔ (g' ∘ g) x ∈ blowUpCenter ρ := fun x hx =>
    (hc x hx).trans (hc' _ (hmaps x hx))
  have hpre : IsOpen (blowUpChartMap σ i ⁻¹' V) :=
    hV.preimage (contDiff_blowUpChartMap σ).continuous
  have hNo : IsOpen (blowUpChartMap σ i ⁻¹' V ∩ {v | liftDir σ τ i g k v ≠ 0}) :=
    (analyticOnNhd_liftDir hV hg hc k).continuousOn.isOpen_inter_preimage hpre
      isOpen_compl_singleton
  have hmapsN : Set.MapsTo (liftMap σ τ i g k)
      (blowUpChartMap σ i ⁻¹' V ∩ {v | liftDir σ τ i g k v ≠ 0}) (blowUpChartMap τ k ⁻¹' W) := by
    rintro v ⟨hv, hvk⟩
    change blowUpChartMap τ k (liftMap σ τ i g k v) ∈ W
    rw [blowUpChartMap_liftMap hc k hv hvk]
    exact hmaps _ hv
  have h1 : ContinuousOn (liftDir σ ρ i (g' ∘ g) l)
      (blowUpChartMap σ i ⁻¹' V ∩ {v | liftDir σ τ i g k v ≠ 0}) :=
    (analyticOnNhd_liftDir hV hgg hcc l).continuousOn.mono Set.inter_subset_left
  have h2 : ContinuousOn
      (fun v => liftDir σ τ i g k v * liftDir τ ρ k g' l (liftMap σ τ i g k v))
      (blowUpChartMap σ i ⁻¹' V ∩ {v | liftDir σ τ i g k v ≠ 0}) := by
    refine ((analyticOnNhd_liftDir hV hg hc k).continuousOn.mono Set.inter_subset_left).mul ?_
    exact (analyticOnNhd_liftDir hW hg' hc' l).continuousOn.comp
      (analyticOnNhd_liftMap hV hg hc k).continuousOn hmapsN
  have hS : Set.EqOn (liftDir σ ρ i (g' ∘ g) l)
      (fun v => liftDir σ τ i g k v * liftDir τ ρ k g' l (liftMap σ τ i g k v))
      {v ∈ blowUpChartMap σ i ⁻¹' V ∩ {v | liftDir σ τ i g k v ≠ 0} | v (σ i) ≠ 0} := by
    rintro v ⟨⟨hv, hvk⟩, hvi⟩
    have e1 := mul_liftDir hcc l hv
    have e2 := mul_liftDir hc' l (hmapsN ⟨hv, hvk⟩)
    rw [liftMap_apply_k, blowUpChartMap_liftMap hc k hv hvk] at e2
    apply mul_left_cancel₀ hvi
    rw [e1, ← mul_assoc, e2]
    rfl
  exact hS.of_subset_closure h1 h2 (fun v hv => hv.1) (subset_closure_ne σ hNo) ⟨hu, hk⟩

end Cocycle

end Manifold
