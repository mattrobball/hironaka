/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.LocalIsoEquiv
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Manifold.IdealSheaf.Vanishing
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Bookkeeping for the one-step descent of agreement

Small lemmas used by the proof of `agreeOnSubspace_blowUpLift`
(`Hironaka/Resolution/Analytic/MaximalContact/OneStepDescent.lean`):

* `stalkCast`: the transport `𝒪_{M,x} ≃ 𝒪_{M,y}` along an equality of points `x = y` (a ring
  homomorphism, the identity after `subst`), with its behaviour on germs of sections, constants,
  coordinate germs and pulled-back germs — all by `subst`. It lets the two lifts `f' q = g' q` be
  compared without rewriting under dependent types.
* `germMap_germMap_germ`: functoriality of the stalk maps for a commuting square
  `π ∘ f' = f ∘ π'`, on germs of sections (no cast: the two membership proofs are separate).
* `eval_map_of_isLocalHom`: a local stalk homomorphism fixing the constants preserves values.
* `stalkIdeal_le_vanishingStalk_of_subset_cosupport`: if `Z ⊆ cosupp J` then every germ of `J`
  vanishes on `Z` — the bridge from Kollár's "`Z_i^U ⊆ W_i`" [Kol07, Theorem 97, proof] to
  `J ⊆ I_Z` (the hypothesis `1 ≤ ν_Z(J)` of the marked transform with mark `1`).
* `Ideal.mem_colon_span_singleton_iff`: the colon by a principal ideal (the stalk of the marked
  transform on the exceptional divisor; off it the colon is by the unit ideal,
  `Ideal.colon_coe_top` of `Hironaka/Scheme/Snc/TotalTransformOffCentre.lean`).
* `agreeOnSubspace_of_forall_sub_mem`: the pointwise criterion for `AgreeOnSubspace f' g' K` —
  at every `q` with `K_q ≠ ⊤`, `f' q = g' q` and `f'^* s − g'^* s ∈ K_q` for every germ `s`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u v

/-! ### The colon by a principal ideal -/

theorem Ideal.mem_colon_span_singleton_iff {R : Type*} [CommRing R] (I : Ideal R) (e x : R) :
    x ∈ I.colon ↑(Ideal.span {e}) ↔ x * e ∈ I := by
  rw [Submodule.mem_colon]
  constructor
  · intro h
    exact h e (Ideal.mem_span_singleton_self e)
  · rintro h s hs
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ _ h

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### Values through local homomorphisms; germs of an ideal vanish on its cosupport -/

section Unbundled

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {N : Type u} [TopologicalSpace N]
  [ChartedSpace E N]

/-- A local ring homomorphism of stalks fixing the constants preserves the values of germs. -/
theorem eval_map_of_isLocalHom {a : M} {b : N}
    (G : (structureSheaf 𝕜 E M).presheaf.stalk a →+* (structureSheaf 𝕜 E N).presheaf.stalk b)
    [IsLocalHom G] (hG : ∀ c : 𝕜, G (const 𝕜 E M a c) = const 𝕜 E N b c)
    (s : (structureSheaf 𝕜 E M).presheaf.stalk a) : Manifold.eval 𝕜 E N b
        (G s) = Manifold.eval 𝕜 E M a s := by
  have h1 : s - const 𝕜 E M a (Manifold.eval 𝕜 E M a s) ∈ maximalIdeal _ :=
    (mem_maximalIdeal_iff_eval E _).mpr (by rw [map_sub, eval_const, sub_self])
  have h2 := map_nonunit G _ h1
  rwa [mem_maximalIdeal_iff_eval, map_sub, hG, map_sub, eval_const, sub_eq_zero] at h2

/-- Kollár's "`Z_i^U ⊆ W_i`" [Kol07, Theorem 97, proof] read at the level of ideals: if the closed
set `Z` lies in the cosupport of `J`, every germ of `J` vanishes on `Z` — `J_a ⊆ I_{Z,a}` for the
vanishing ideal of `Z` (`vanishingStalk`). -/
theorem stalkIdeal_le_vanishingStalk_of_subset_cosupport {Z : Set M}
    (J : IdealSheaf (structureSheaf 𝕜 E M)) (hZ : Z ⊆ J.support) (a : M) :
    J.stalkIdeal a ≤ vanishingStalk (𝕜 := 𝕜) (E := E) Z a := by
  intro s hs
  have hs' : ∃ (V : Opens M) (hb : a ∈ V) (g : (structureSheaf 𝕜 E M).presheaf.obj (op V)),
      g ∈ J.carrier V ∧ (structureSheaf 𝕜 E M).presheaf.germ V a hb g = s := hs
  obtain ⟨V, ha, g, hg, rfl⟩ := hs'
  rw [mem_vanishingStalk_iff, stalkToGerm_structureSheaf_germ, Germ.vanishesOn_coe]
  have hV : ∀ᶠ y in 𝓝[Z] a, y ∈ V := nhdsWithin_le_nhds (V.2.mem_nhds ha)
  filter_upwards [hV, self_mem_nhdsWithin] with y hyV hyZ
  have hmem : (structureSheaf 𝕜 E M).presheaf.germ V y hyV g ∈ J.stalkIdeal y :=
    J.germ_mem_stalkIdeal hyV hg
  have hne : J.stalkIdeal y ≠ ⊤ := hZ hyZ
  have h3 := IsLocalRing.le_maximalIdeal hne hmem
  rwa [mem_maximalIdeal_iff_eval, eval_germ'] at h3

end Unbundled

/-! ### Transport of stalks along an equality of points -/

section Cast

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-- The transport `𝒪_{M,x} → 𝒪_{M,y}` along `x = y` (the identity after `subst`). -/
def stalkCast {x y : M} (h : x = y) :
    (structureSheaf 𝕜 E M).presheaf.stalk x →+* (structureSheaf 𝕜 E M).presheaf.stalk y := by
  subst h
  exact RingHom.id _

omit ψ in
theorem stalkCast_germ {x y : M} (h : x = y) {W : Opens M} (hx : x ∈ W) (hy : y ∈ W)
    (s : (structureSheaf 𝕜 E M).presheaf.obj (op W)) :
    stalkCast h ((structureSheaf 𝕜 E M).presheaf.germ W x hx s) =
      (structureSheaf 𝕜 E M).presheaf.germ W y hy s := by
  subst h
  rfl

omit ψ in
theorem stalkCast_const {x y : M} (h : x = y) (c : 𝕜) :
    stalkCast h (const 𝕜 E M x c) = const 𝕜 E M y c := by
  subst h
  rfl

theorem stalkCast_coord {x y : M} (h : x = y) {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (hx : x ∈ φ.source) (hy : y ∈ φ.source) (i : Fin n) :
    stalkCast h (coord E ψ φ hφ hx i) = coord E ψ φ hφ hy i := by
  subst h
  rfl

omit ψ in
instance isLocalHom_stalkCast {x y : M} (h : x = y) :
    IsLocalHom (stalkCast (𝕜 := 𝕜) (E := E) h) := by
  subst h
  exact ⟨fun _ ha => ha⟩

end Cast

/-! ### Functoriality of the stalk maps on a commuting square; the pointwise criterion -/

section Bundled

variable {U U' M M' : AnalyticManifold.{u} 𝕜 E}

/-- The transport commutes with the stalk map of `π` on germs of sections. -/
theorem stalkCast_germMap_germ (π : AnalyticMap M' M) {x y : M'} (h : x = y) {V : Opens M}
    (hV : π x ∈ V) (hV' : π y ∈ V) (t : (structureSheaf 𝕜 E M).presheaf.obj (op V)) :
    stalkCast h (germMap (⇑π) π.contMDiff x ((structureSheaf 𝕜 E M).presheaf.germ V (π x) hV t)) =
      germMap (⇑π) π.contMDiff y ((structureSheaf 𝕜 E M).presheaf.germ V (π y) hV' t) := by
  subst h
  rfl

/-- Functoriality of the stalk maps on a commuting square `π ∘ f' = f ∘ π'`, on the germ of a
section `h` at the common image point (the two membership proofs are separate, so no transport of
stalks is needed). -/
theorem germMap_germMap_germ (f' : AnalyticMap U' M') (π : AnalyticMap M' M) (π' : AnalyticMap U' U)
    (f : AnalyticMap U M) (hcomm : ∀ x, π (f' x) = f (π' x)) (q : U') {W : Opens M}
    (hW : π (f' q) ∈ W) (hW' : f (π' q) ∈ W) (h : (structureSheaf 𝕜 E M).presheaf.obj (op W)) :
    germMap (⇑f') f'.contMDiff q (germMap (⇑π) π.contMDiff (f' q)
        ((structureSheaf 𝕜 E M).presheaf.germ W (π (f' q)) hW h)) =
      germMap (⇑π') π'.contMDiff q (germMap (⇑f) f.contMDiff (π' q)
        ((structureSheaf 𝕜 E M).presheaf.germ W (f (π' q)) hW' h)) := by
  apply stalkToGerm_injective 𝓘(𝕜, E) ω U' q
  rw [stalkToGerm_germMap, stalkToGerm_germMap, stalkToGerm_germMap, stalkToGerm_germMap,
    stalkToGerm_structureSheaf_germ, stalkToGerm_structureSheaf_germ, Germ.coe_compTendsto,
    Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto]
  refine Germ.coe_eq.mpr (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, hcomm x]

/-- The pointwise criterion for `AgreeOnSubspace f' g' K`: at every point `q` where `K_q ≠ ⊤`, the
two maps agree, `f' q = g' q`, and their stalk maps agree modulo `K_q` on every germ at that point
(the second read through the transport along `f' q = g' q`). -/
theorem agreeOnSubspace_of_forall_sub_mem (f' g' : AnalyticMap U' M')
    (K : AnalyticManifold.IdealSheaf U')
    (h : ∀ q : U', K.stalkIdeal q ≠ ⊤ → ∃ hpp' : f' q = g' q,
      ∀ s : (structureSheaf 𝕜 E M').presheaf.stalk (f' q),
        germMap (⇑f') f'.contMDiff q s - germMap (⇑g') g'.contMDiff q (stalkCast hpp' s) ∈
          K.stalkIdeal q) :
    AgreeOnSubspace f' g' K := by
  intro q W hq₁ hq₂ h'
  by_cases hK : K.stalkIdeal q = ⊤
  · rw [hK]
    exact Submodule.mem_top
  obtain ⟨hpp', hs⟩ := h q hK
  have := hs ((structureSheaf 𝕜 E M').presheaf.germ W (f' q) hq₁ h')
  rwa [stalkCast_germ hpp' hq₁ hq₂] at this

end Bundled

end Hironaka.Manifold

end
