/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.CenterList
import Hironaka.Manifold.FiniteSuccession.Restrict.Lift
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Functoriality and injectivity of the pull-back of lists of centres

The pull-back `h^* B` of a blow-up sequence is functorial in the smooth morphism `h`
[Kol07, Definition 30, 30.1], and a surjective `h` determines `B` from `h^* B`; this is the
uniqueness of [Kol07, Proposition 37]: pull-back along a surjective `g` is injective, so
`g^* B̄'(X) = B(X') = g^* B̄(X)` forces `B̄'(X) = B̄(X)`, and "hence the existence is a local
question" [Kol07, 34]. On lists of centres:

* `BlowUpSequence.liftStep_unique`: a continuous map over `h` between the chosen blowings-up is the
  lift `liftStep` (uniqueness of lifts: two continuous maps over `h` agree off the exceptional
  divisor, which is dense, `eqOn_of_comp_eq_of_dense`);
* `pullback_congr`, `pullback_id`, `pullback_comp` (the lift of the identity is the identity, the
  lift of a composite is the composite of the lifts);
* `noEmptyCenters_pullback_of_surjective`, `eraseEmpty_pullback_of_surjective` (the lift of a
  surjective local isomorphism is surjective, `surjective_blowUpLift`, so preimages of nonempty
  centres are nonempty);
* `pullback_injective_of_surjective` (centres are recovered as images under the surjective lifts),
  `eq_of_pullback_openCover`.

The last two groups are proved in `Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj` and
`Hironaka.Manifold.FiniteSuccession.Functor.PullbackCover`.
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N P : AnalyticManifold.{u} 𝕜 E}

/-- Uniqueness of lifts ([Kol07, Definition 30, 30.1]): a continuous map between the chosen
blowings-up over the local analytic isomorphism `h` is the lift `liftStep h hh hY` — the two agree
off the exceptional divisor, where the blow-down is injective, and that set is dense. -/
theorem liftStep_unique (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    {G : blowUp ψ₀ (hY.preimage_of_isLocalDiffeomorph hh) → blowUp ψ₀ hY} (hG : Continuous G)
    (hcomm : ∀ q, blowUpπ ψ₀ hY (G q) = h (blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh) q)) :
    G = liftStep h hh hY := by
  have hY' : IsClosedSubmanifold ψ₀ (h ⁻¹' Y) c := hY.preimage_of_isLocalDiffeomorph hh
  have hd0 := (isBlowUp_blowUpπ ψ₀ hY').dense_preimage_compl hY'
  have hd : Dense ((fun q => h (blowUpπ ψ₀ hY' q)) ⁻¹' Yᶜ) := hd0
  funext q
  exact eqOn_of_comp_eq_of_dense (isBlowUp_blowUpπ ψ₀ hY).bijOn_compl.injOn hd isOpen_univ
    hG.continuousOn (liftStep h hh hY).contMDiff.continuous.continuousOn (fun q _ => hcomm q)
    (fun q _ => blowUpπ_liftStep h hh hY q) (mem_univ q)

/-- Local analytic isomorphisms compose (Mathlib's `IsLocalDiffeomorphAt.comp`, pointwise). -/
theorem isLocalDiffeomorph_comp {h : AnalyticMap N M} (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    {k : AnalyticMap P N} (hk : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω k) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (h.comp k) :=
  fun x => (hk x).comp 𝓘(𝕜, E) M (hh (k x))

theorem pullback_congr (L : BlowUpSequence ψ₀ M) {f g : AnalyticMap N M} (hfg : f = g)
    (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) :
    L.pullback f hf = L.pullback g hg := by
  subst hfg
  rfl

/-- The identity is a local analytic isomorphism (`Diffeomorph.refl`). -/
theorem isLocalDiffeomorph_id (M : AnalyticManifold.{u} 𝕜 E) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (ContMDiffMap.id : AnalyticMap M M) :=
  (Diffeomorph.refl 𝓘(𝕜, E) M ω).isLocalDiffeomorph

/-- The lift of the identity is the identity. -/
theorem liftStep_id {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) :
    liftStep ContMDiffMap.id (isLocalDiffeomorph_id M) hY = ContMDiffMap.id := by
  refine ContMDiffMap.ext fun q => ?_
  have := (liftStep_unique ContMDiffMap.id (isLocalDiffeomorph_id M) hY (G := id) continuous_id
    fun q => rfl)
  exact (congrFun this q).symm

/-- [Kol07, Definition 30, 30.1] (`pullback_id`): the pull-back along the identity is
the identity. -/
@[simp]
theorem pullback_id : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M),
    L.pullback ContMDiffMap.id (isLocalDiffeomorph_id M) = L
  | _, nil _ => rfl
  | _, cons hY rest => by
    rw [pullback_cons]
    change cons hY (rest.pullback (liftStep ContMDiffMap.id (isLocalDiffeomorph_id _) hY) _) =
      cons hY rest
    congr 1
    exact (pullback_congr rest (liftStep_id hY) (isLocalDiffeomorph_liftStep _ _ hY)
      (isLocalDiffeomorph_id _)).trans (pullback_id rest)

/-- The lift of a composite is the composite of the lifts (uniqueness of lifts). -/
theorem liftStep_comp (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (k : AnalyticMap P N) (hk : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω k) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) :
    liftStep (h.comp k) (isLocalDiffeomorph_comp hh hk) hY =
      (liftStep h hh hY).comp (liftStep k hk (hY.preimage_of_isLocalDiffeomorph hh)) := by
  refine ContMDiffMap.ext fun q => ?_
  have := liftStep_unique (h.comp k) (isLocalDiffeomorph_comp hh hk) hY
    (G := (liftStep h hh hY) ∘ (liftStep k hk (hY.preimage_of_isLocalDiffeomorph hh)))
    ((liftStep h hh hY).contMDiff.continuous.comp
      (liftStep k hk (hY.preimage_of_isLocalDiffeomorph hh)).contMDiff.continuous)
    (fun q => by
      change blowUpπ ψ₀ hY (liftStep h hh hY (liftStep k hk _ q)) = h (k (blowUpπ ψ₀ _ q))
      exact (blowUpπ_liftStep h hh hY _).trans
        (congrArg h (blowUpπ_liftStep k hk (hY.preimage_of_isLocalDiffeomorph hh) q)))
  exact (congrFun this q).symm

/-- [Kol07, Definition 30, 30.1] (`pullback_comp`): the pull-back along a composite is
the composite of the pull-backs. -/
theorem pullback_comp : ∀ {M N P : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (k : AnalyticMap P N)
    (hk : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω k),
    (L.pullback h hh).pullback k hk = L.pullback (h.comp k) (isLocalDiffeomorph_comp hh hk)
  | _, _, _, nil _, _, _, _, _ => rfl
  | _, _, _, cons hY rest, h, hh, k, hk => by
    rw [pullback_cons, pullback_cons, pullback_cons]
    congr 1
    rw [pullback_comp rest (liftStep h hh hY) _ (liftStep k hk _) _]
    exact pullback_congr rest (liftStep_comp h hh k hk hY).symm _ _

end AnalyticManifold.BlowUpSequence

end
