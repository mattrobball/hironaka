/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Basic
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.Lift
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The fibre product lifts to the blowings-up

The proof of [Kol07, Proposition 37] blows up the descended centre and repeats the argument on
`X₁' = X' ×_X X₁`. On manifolds: given a surjective local analytic isomorphism `g : N → M`, a fibre
product `(P, p₁, p₂)` of `g` with itself, and a closed submanifold `Z ⊆ M`, the lifts
`g₁ : Bl_{g⁻¹Z} N → Bl_Z M` and `q₁, q₂ : Bl_{p₁⁻¹g⁻¹Z} P → Bl_{g⁻¹Z} N` of `g`, `p₁`, `p₂`
(`blowUpLift`; `q₂` the lift of `p₂` over the blowing-up of `P` along `p₁⁻¹g⁻¹Z = p₂⁻¹g⁻¹Z`) form
again a fibre product of `g₁` with itself: `g₁ ∘ q₁ = g₁ ∘ q₂` by the uniqueness of lifts, and the
bijection onto the set-theoretic fibre product comes from the local bijections of the lifts over
local inverses (`liftPartialDiffeomorph`: over a local inverse `Φ` of `h` at `b`, a continuous map
over `h` is a bijection `π'⁻¹(Φ.source) → π⁻¹(Φ.target)`). The pull-backs of a list along two
lifts of the same map from blowings-up along the same set agree (`pullback_heq_of_comm`).
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Local bijections of a map over a local analytic isomorphism -/

section LocalBijection

variable {M₀ N₀ N' M' : AnalyticManifold.{u} 𝕜 E} {h : AnalyticMap N₀ M₀}
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M₀} {c : ℕ}
  (hY : IsClosedSubmanifold ψ₀ Y c) {π : M' → M₀} {π' : N' → N₀} (hπ : IsBlowUp ψ₀ Y c π)
  (hπ' : IsBlowUp ψ₀ (h ⁻¹' Y) c π') {G : N' → M'} (hG : Continuous G)
  (hGπ : ∀ q, π (G q) = h (π' q)) {Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N₀ M₀ ω}
  (hΦ : EqOn h Φ Φ.source)

include hh hY hπ hπ' hG hGπ hΦ in
/-- A continuous map over `h` is injective over the source of a local inverse of `h`. -/
theorem injOn_of_comm_local [Nonempty N'] [Nonempty M'] : InjOn G (π' ⁻¹' Φ.source) := by
  intro u₁ h₁ u₂ h₂ heq
  have e := eqOn_liftPartialDiffeomorph_of_comm hY hh hπ hπ' hG hGπ hΦ
  exact (liftPartialDiffeomorph Φ (image_preimage_eq_of_eqOn Φ hΦ)
    (hY.preimage_of_isLocalDiffeomorph hh) hπ' hπ hY).toPartialEquiv.injOn h₁ h₂
    (by rw [← e h₁, ← e h₂, heq])

include hh hY hπ hπ' hG hGπ hΦ in
/-- A continuous map over `h` maps `π'⁻¹(Φ.source)` onto `π⁻¹(Φ.target)` for a local inverse `Φ` of
`h`. -/
theorem exists_eq_of_comm_local [Nonempty N'] [Nonempty M'] {q : M'} (hq : π q ∈ Φ.target) :
    ∃ u ∈ π' ⁻¹' Φ.source, G u = q := by
  set L := liftPartialDiffeomorph Φ (image_preimage_eq_of_eqOn Φ hΦ)
    (hY.preimage_of_isLocalDiffeomorph hh) hπ' hπ hY
  have hq' : q ∈ L.target := hq
  refine ⟨L.toPartialEquiv.symm q, L.toPartialEquiv.map_target hq', ?_⟩
  have e := eqOn_liftPartialDiffeomorph_of_comm hY hh hπ hπ' hG hGπ hΦ
    (L.toPartialEquiv.map_target hq')
  exact e.trans (L.toPartialEquiv.right_inv hq')

end LocalBijection

/-! ### Two lifts of the same map from blowings-up along the same set -/

section Heq

variable {N P : AnalyticManifold.{u} 𝕜 E} {p : AnalyticMap P N} {Y : Set N} {c : ℕ}
  (hY : IsClosedSubmanifold ψ₀ Y c)

/-- Two continuous maps over `p` from the chosen blowing-up of `P` along `p⁻¹(Y)` to the
chosen blowing-up of `N` along `Y` agree (uniqueness of lifts). -/
theorem eq_of_comm_blowUp {Y₁ : Set P} (hY₁ : IsClosedSubmanifold ψ₀ Y₁ c) (hY₁p : Y₁ = p ⁻¹' Y)
    {G₁ G₂ : blowUp ψ₀ hY₁ → blowUp ψ₀ hY} (hG₁ : Continuous G₁) (hG₂ : Continuous G₂)
    (hc₁ : ∀ u, blowUpπ ψ₀ hY (G₁ u) = p (blowUpπ ψ₀ hY₁ u))
    (hc₂ : ∀ u, blowUpπ ψ₀ hY (G₂ u) = p (blowUpπ ψ₀ hY₁ u)) : G₁ = G₂ := by
  subst hY₁p
  have hd0 := (isBlowUp_blowUpπ ψ₀ hY₁).dense_preimage_compl hY₁
  have hd : Dense ((fun u => p (blowUpπ ψ₀ hY₁ u)) ⁻¹' Yᶜ) := hd0
  funext u
  exact eqOn_of_comp_eq_of_dense (isBlowUp_blowUpπ ψ₀ hY).bijOn_compl.injOn hd isOpen_univ
    hG₁.continuousOn hG₂.continuousOn (fun u _ => hc₁ u) (fun u _ => hc₂ u) (mem_univ u)

/-- The pull-backs of a list along two lifts of `p` from blowings-up along (propositionally) the
same set are heterogeneously equal. -/
theorem _root_.AnalyticManifold.BlowUpSequence.pullback_heq_of_comm {Y₁ Y₂ : Set P}
    (hY₁ : IsClosedSubmanifold ψ₀ Y₁ c)
    (hY₂ : IsClosedSubmanifold ψ₀ Y₂ c) (hYY : Y₁ = Y₂) (hY₁p : Y₁ = p ⁻¹' Y)
    (G₁ : AnalyticMap (blowUp ψ₀ hY₁) (blowUp ψ₀ hY))
    (G₂ : AnalyticMap (blowUp ψ₀ hY₂) (blowUp ψ₀ hY))
    (hG₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω G₁) (hG₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω G₂)
    (hc₁ : ∀ u, blowUpπ ψ₀ hY (G₁ u) = p (blowUpπ ψ₀ hY₁ u))
    (hc₂ : ∀ u, blowUpπ ψ₀ hY (G₂ u) = p (blowUpπ ψ₀ hY₂ u)) (L : AnalyticManifold.BlowUpSequence
        ψ₀ (blowUp ψ₀ hY)) :
    HEq (L.pullback G₁ hG₁) (L.pullback G₂ hG₂) := by
  subst hYY
  have hG : G₁ = G₂ := ContMDiffMap.ext fun u => congrFun
    (eq_of_comm_blowUp hY hY₁ hY₁p G₁.contMDiff.continuous G₂.contMDiff.continuous hc₁ hc₂) u
  exact heq_of_eq (AnalyticManifold.BlowUpSequence.pullback_congr L hG hG₁ hG₂)

end Heq

/-! ### The lifted fibre product -/

section Lifted

variable {M N P : AnalyticManifold.{u} 𝕜 E} {g : AnalyticMap N M}
  (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) {p₁ p₂ : AnalyticMap P N}
  (hp : IsFibreProduct g g p₁ p₂) {Z : Set M} {c : ℕ} (hZ : IsClosedSubmanifold ψ₀ Z c)

include hp in
/-- The centre `p₂⁻¹(g⁻¹Z)` of the second lift is the centre `p₁⁻¹(g⁻¹Z)` of the first. -/
theorem preimage_eq_of_isFibreProduct : p₂ ⁻¹' (g ⁻¹' Z) = p₁ ⁻¹' (g ⁻¹' Z) := by
  ext w
  change g (p₂ w) ∈ Z ↔ g (p₁ w) ∈ Z
  rw [hp.2.2.1 w]

include hp in
/-- The chosen blowing-up of `P` along `p₁⁻¹(g⁻¹Z)`, read as a blowing-up along
`p₂⁻¹(g⁻¹Z)`. -/
theorem isBlowUp_blowUpπ_lifted :
    IsBlowUp ψ₀ (p₂ ⁻¹' (g ⁻¹' Z)) c (blowUpπ ψ₀
      ((hZ.preimage_of_isLocalDiffeomorph hg).preimage_of_isLocalDiffeomorph hp.1)) := by
  rw [preimage_eq_of_isFibreProduct hp]
  exact isBlowUp_blowUpπ ψ₀ _

/-- The lift of the second projection, over the blowing-up of `P` along `p₁⁻¹(g⁻¹Z)`. -/
def liftedSnd :
    blowUp ψ₀ ((hZ.preimage_of_isLocalDiffeomorph hg).preimage_of_isLocalDiffeomorph hp.1) →
      blowUp ψ₀ (hZ.preimage_of_isLocalDiffeomorph hg) :=
  blowUpLift (hZ.preimage_of_isLocalDiffeomorph hg) hp.2.1
    (isBlowUp_blowUpπ ψ₀ (hZ.preimage_of_isLocalDiffeomorph hg)) (isBlowUp_blowUpπ_lifted hg hp hZ)

theorem contMDiff_liftedSnd : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω (liftedSnd hg hp hZ) :=
  contMDiff_blowUpLift _ _ _ _

theorem isLocalDiffeomorph_liftedSnd :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (liftedSnd hg hp hZ) :=
  isLocalDiffeomorph_blowUpLift _ _ _ _

theorem blowUpπ_liftedSnd (u) :
    blowUpπ ψ₀ (hZ.preimage_of_isLocalDiffeomorph hg) (liftedSnd hg hp hZ u) =
      p₂ (blowUpπ ψ₀ _ u) :=
  blowDown_blowUpLift _ _ _ _ u

/-- The lifted second projection as an analytic map. -/
def liftedSndMap :
    AnalyticMap
      (blowUp ψ₀ ((hZ.preimage_of_isLocalDiffeomorph hg).preimage_of_isLocalDiffeomorph hp.1))
      (blowUp ψ₀ (hZ.preimage_of_isLocalDiffeomorph hg)) :=
  ⟨liftedSnd hg hp hZ, contMDiff_liftedSnd hg hp hZ⟩

/-- The two lifted composites `g₁ ∘ q₁` and `g₁ ∘ q₂` agree (uniqueness of lifts over
`g ∘ p₁ = g ∘ p₂`). -/
theorem liftStep_comp_liftStep_eq_liftStep_comp_liftedSnd :
    (AnalyticManifold.BlowUpSequence.liftStep g hg hZ) ∘
        (AnalyticManifold.BlowUpSequence.liftStep p₁ hp.1 (hZ.preimage_of_isLocalDiffeomorph hg)) =
      (AnalyticManifold.BlowUpSequence.liftStep g hg hZ) ∘ liftedSnd hg hp hZ := by
  have hZ' := hZ.preimage_of_isLocalDiffeomorph hg
  have hd0 := (isBlowUp_blowUpπ ψ₀ (hZ'.preimage_of_isLocalDiffeomorph hp.1)).dense_preimage_compl
    (hZ'.preimage_of_isLocalDiffeomorph hp.1)
  have hd : Dense ((fun u => g (p₁ (blowUpπ ψ₀ (hZ'.preimage_of_isLocalDiffeomorph hp.1) u))) ⁻¹'
    Zᶜ) := hd0
  funext u
  refine eqOn_of_comp_eq_of_dense (isBlowUp_blowUpπ ψ₀ hZ).bijOn_compl.injOn hd isOpen_univ
    ((AnalyticManifold.BlowUpSequence.liftStep g hg hZ).contMDiff.continuous.comp
      (AnalyticManifold.BlowUpSequence.liftStep p₁ hp.1 hZ').contMDiff.continuous).continuousOn
    ((AnalyticManifold.BlowUpSequence.liftStep g hg hZ).contMDiff.continuous.comp
      (contMDiff_liftedSnd hg hp hZ).continuous).continuousOn
    (fun u _ => ?_) (fun u _ => ?_) (mem_univ u)
  · change blowUpπ ψ₀ hZ (AnalyticManifold.BlowUpSequence.liftStep g hg hZ
      (AnalyticManifold.BlowUpSequence.liftStep p₁ hp.1 hZ' u)) = _
    rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep,
        AnalyticManifold.BlowUpSequence.blowUpπ_liftStep]
  · change blowUpπ ψ₀ hZ (AnalyticManifold.BlowUpSequence.liftStep g hg hZ
      (liftedSnd hg hp hZ u)) = _
    rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep, blowUpπ_liftedSnd, hp.2.2.1]

/-- [Kol07, Proposition 37] ("`X₁' = X' ×_X X₁`"): the lifts of the two projections
form a fibre product of the lifted cover `g₁` with itself — `g₁ ∘ q₁ = g₁ ∘ q₂` by uniqueness of
lifts, and over a pair `x, y` with `g₁ x = g₁ y` the point `w` over the unique `z` with
`p₁ z = π x`, `p₂ z = π y` is found (and is unique) through the local bijections of the lifts over
local inverses of `p₁` and of `g`. -/
theorem isFibreProduct_lifted :
    IsFibreProduct (AnalyticManifold.BlowUpSequence.liftStep g hg hZ)
        (AnalyticManifold.BlowUpSequence.liftStep g hg hZ)
      (AnalyticManifold.BlowUpSequence.liftStep p₁ hp.1 (hZ.preimage_of_isLocalDiffeomorph hg))
      (liftedSndMap hg hp hZ) := by
  have hZ' := hZ.preimage_of_isLocalDiffeomorph hg
  have hZ'' := hZ'.preimage_of_isLocalDiffeomorph hp.1
  have hcomm := liftStep_comp_liftStep_eq_liftStep_comp_liftedSnd hg hp hZ
  refine ⟨AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep p₁ hp.1 hZ',
      isLocalDiffeomorph_liftedSnd hg hp hZ,
    fun w => congrFun hcomm w, fun x y hxy => ?_⟩
  have hb : g (blowUpπ ψ₀ hZ' x) = g (blowUpπ ψ₀ hZ' y) := by
    rw [← AnalyticManifold.BlowUpSequence.blowUpπ_liftStep g hg hZ x,
        ← AnalyticManifold.BlowUpSequence.blowUpπ_liftStep g hg hZ y, hxy]
  obtain ⟨z, ⟨hz₁, hz₂⟩, hzu⟩ := hp.2.2.2 _ _ hb
  obtain ⟨Φ, hzΦ, hΦ⟩ := (hp.1 z).exists_partialDiffeomorph
  obtain ⟨q₀, -⟩ := exists_blowDown_eq_of_blowDown_eq hZ' hp.1 (isBlowUp_blowUpπ ψ₀ hZ')
    (isBlowUp_blowUpπ ψ₀ hZ'') z hz₁.symm
  have : Nonempty (blowUp ψ₀ hZ'') := ⟨q₀⟩
  have : Nonempty (blowUp ψ₀ hZ') := ⟨x⟩
  have : Nonempty (blowUp ψ₀ hZ) := ⟨AnalyticManifold.BlowUpSequence.liftStep g hg hZ x⟩
  have hq₁ : ∀ u, blowUpπ ψ₀ hZ' (AnalyticManifold.BlowUpSequence.liftStep p₁ hp.1 hZ' u) = p₁
      (blowUpπ ψ₀ hZ'' u) :=
    AnalyticManifold.BlowUpSequence.blowUpπ_liftStep p₁ hp.1 hZ'
  have hq₂ : ∀ u, blowUpπ ψ₀ hZ' (liftedSnd hg hp hZ u) = p₂ (blowUpπ ψ₀ hZ'' u) :=
    blowUpπ_liftedSnd hg hp hZ
  have hinj₁ := injOn_of_comm_local hp.1 hZ' (isBlowUp_blowUpπ ψ₀ hZ') (isBlowUp_blowUpπ ψ₀ hZ'')
    (AnalyticManifold.BlowUpSequence.liftStep p₁ hp.1 hZ').contMDiff.continuous hq₁ hΦ
  obtain ⟨w, hwΦ, hw₁⟩ := exists_eq_of_comm_local hp.1 hZ' (isBlowUp_blowUpπ ψ₀ hZ')
    (isBlowUp_blowUpπ ψ₀ hZ'') (AnalyticManifold.BlowUpSequence.liftStep p₁ hp.1
        hZ').contMDiff.continuous hq₁ hΦ
    (q := x) (by rw [← hz₁, hΦ hzΦ]; exact Φ.map_source hzΦ)
  have hwz : blowUpπ ψ₀ hZ'' w = z := by
    refine Φ.toPartialEquiv.injOn hwΦ hzΦ ?_
    rw [← hΦ hwΦ, ← hΦ hzΦ, ← hq₁ w, hw₁, hz₁]
  have hw₂ : liftedSnd hg hp hZ w = y := by
    obtain ⟨Ψ, hyΨ, hΨ⟩ := (hg (blowUpπ ψ₀ hZ' y)).exists_partialDiffeomorph
    have hπ : blowUpπ ψ₀ hZ' (liftedSnd hg hp hZ w) = blowUpπ ψ₀ hZ' y := by
      rw [hq₂, hwz, hz₂]
    refine injOn_of_comm_local hg hZ (isBlowUp_blowUpπ ψ₀ hZ) (isBlowUp_blowUpπ ψ₀ hZ')
      (AnalyticManifold.BlowUpSequence.liftStep g hg hZ).contMDiff.continuous
          (AnalyticManifold.BlowUpSequence.blowUpπ_liftStep g hg hZ) hΨ
      (show blowUpπ ψ₀ hZ' (liftedSnd hg hp hZ w) ∈ Ψ.source by rw [hπ]; exact hyΨ) hyΨ ?_
    have hc : AnalyticManifold.BlowUpSequence.liftStep g hg hZ
        (AnalyticManifold.BlowUpSequence.liftStep p₁ hp.1 hZ' w) =
        AnalyticManifold.BlowUpSequence.liftStep g hg hZ (liftedSnd hg hp hZ w) := congrFun hcomm w
    change AnalyticManifold.BlowUpSequence.liftStep g hg hZ (liftedSnd hg hp hZ w) =
        AnalyticManifold.BlowUpSequence.liftStep g hg hZ y
    rw [← hc, hw₁, hxy]
  refine ⟨w, ⟨hw₁, hw₂⟩, fun w' ⟨hw'₁, hw'₂⟩ => ?_⟩
  have hw'z : blowUpπ ψ₀ hZ'' w' = z := by
    refine hzu _ ⟨?_, ?_⟩
    · rw [← hq₁ w']
      exact congrArg _ hw'₁
    · rw [← hq₂ w']
      exact congrArg _ hw'₂
  refine hinj₁ (show blowUpπ ψ₀ hZ'' w' ∈ Φ.source by rw [hw'z]; exact hzΦ) hwΦ ?_
  change AnalyticManifold.BlowUpSequence.liftStep p₁ hp.1 hZ' w' =
      AnalyticManifold.BlowUpSequence.liftStep p₁ hp.1 hZ' w
  rw [hw₁]
  exact hw'₁

end Lifted

end Manifold

end
