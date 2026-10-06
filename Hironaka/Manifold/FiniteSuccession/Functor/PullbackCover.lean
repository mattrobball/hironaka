/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.CenterList
public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lists of centres are determined locally

The isomorphism of [Kol07, 34] is unique, so its existence is a local question, as the proof of
[Kol07, Theorem 36] puts it ("(34.1) is a local property"). On lists of
centres: two lists on `M` whose pull-backs along every member of a family of local analytic
isomorphisms with covering ranges agree are equal (`eq_of_pullback_cover`; the form
`eq_of_pullback_openCover` for a nonempty open cover by analytic open embeddings): the centres
are recovered from their preimages, and the lifts of the family to the chosen blowing-up again
have covering ranges (`exists_liftStep_eq`: a point over `h b` is in the range of the lift, by the
lift of a local inverse of `h` at `b`, `Hironaka.Manifold.BlowUp.Functor`).
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- A point of `Bl_Y M` over a point `h b` of the range of the local analytic isomorphism `h` is in
the range of the lift of `h` (lift of a local inverse of `h` at `b` maps `π'⁻¹(Φ.source)`
onto `π⁻¹(Φ.target)`; the body of `surjective_of_comm`, without the surjectivity of `h`). -/
theorem exists_liftStep_eq (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) (p : blowUp ψ₀ hY) {b : N}
    (hb : h b = blowUpπ ψ₀ hY p) : ∃ q, liftStep h hh hY q = p := by
  have hπ := isBlowUp_blowUpπ ψ₀ hY
  have hπ' := isBlowUp_blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
  obtain ⟨q₀, -⟩ := exists_blowDown_eq_of_blowDown_eq hY hh hπ hπ' b hb.symm
  have : Nonempty (blowUp ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)) := ⟨q₀⟩
  have : Nonempty (blowUp ψ₀ hY) := ⟨p⟩
  obtain ⟨Φ, hbΦ, hΦ⟩ := (hh b).exists_partialDiffeomorph
  set L := liftPartialDiffeomorph Φ (image_preimage_eq_of_eqOn Φ hΦ)
    (hY.preimage_of_isLocalDiffeomorph hh) hπ' hπ hY
  have hp : p ∈ L.target := by
    change blowUpπ ψ₀ hY p ∈ Φ.target
    rw [← hb, hΦ hbΦ]
    exact Φ.map_source hbΦ
  refine ⟨L.toPartialEquiv.symm p, ?_⟩
  have e := eqOn_liftPartialDiffeomorph_of_comm hY hh hπ hπ'
    (liftStep h hh hY).contMDiff.continuous (blowUpπ_liftStep h hh hY) hΦ (L.map_target hp)
  exact e.trans (L.right_inv hp)

/-- [Kol07, 34], the general form: two lists on `M` whose pull-backs along every
member of a family of local analytic isomorphisms with covering ranges agree are equal. -/
theorem eq_of_pullback_cover : ∀ {M : AnalyticManifold.{u} 𝕜 E} {σ : Type u} [Nonempty σ]
    {N : σ → AnalyticManifold.{u} 𝕜 E} (ι : ∀ i, AnalyticMap (N i) M)
    (hι : ∀ i, IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (ι i)), (∀ x : M, ∃ i, x ∈ range (ι i)) →
    ∀ (L L' : BlowUpSequence ψ₀ M), (∀ i, L.pullback (ι i) (hι i) = L'.pullback (ι i)
        (hι i)) → L = L'
  | _, _, _, _, _, _, _, nil _, nil _, _ => rfl
  | _, σ, _, _, ι, hι, _, nil _, cons hY' rest', h => by
    have hi := h (Classical.arbitrary σ)
    rw [pullback_nil, pullback_cons] at hi
    cases hi
  | _, σ, _, _, ι, hι, _, cons hY rest, nil _, h => by
    have hi := h (Classical.arbitrary σ)
    rw [pullback_nil, pullback_cons] at hi
    cases hi
  | _, σ, _, _, ι, hι, hcov, @cons _ _ _ _ _ _ _ _ Y c hY rest,
      @cons _ _ _ _ _ _ _ _ Y' c' hY' rest', h => by
    have hYY : Y = Y' := by
      ext x
      obtain ⟨i, y, rfl⟩ := hcov x
      have hi := h i
      rw [pullback_cons, pullback_cons] at hi
      have hYY' : ι i ⁻¹' Y = ι i ⁻¹' Y' := (cons.inj hi).1
      exact ⟨fun hx => (hYY' ▸ (show y ∈ ι i ⁻¹' Y from hx) : y ∈ ι i ⁻¹' Y'),
        fun hx => (hYY'.symm ▸ (show y ∈ ι i ⁻¹' Y' from hx) : y ∈ ι i ⁻¹' Y)⟩
    subst hYY
    have hcc : c = c' := by
      have hi := h (Classical.arbitrary σ)
      rw [pullback_cons, pullback_cons] at hi
      exact (cons.inj hi).2.1
    subst hcc
    have hr : rest = rest' := by
      refine eq_of_pullback_cover (fun i => liftStep (ι i) (hι i) hY)
        (fun i => isLocalDiffeomorph_liftStep (ι i) (hι i) hY) ?_ rest rest' fun i => ?_
      · intro p
        obtain ⟨i, b, hb⟩ := hcov (blowUpπ ψ₀ hY p)
        obtain ⟨q, hq⟩ := exists_liftStep_eq (ι i) (hι i) hY p hb
        exact ⟨i, q, hq⟩
      · have hi := h i
        rw [pullback_cons, pullback_cons] at hi
        exact eq_of_heq (cons.inj hi).2.2
    subst hr
    rfl

/-- [Kol07, 34] (`eq_of_pullback_openCover`): two lists on `M` that
agree after pull-back to every member of a nonempty open cover by analytic open embeddings are
equal. -/
theorem eq_of_pullback_openCover {σ : Type u} [Nonempty σ] {N : σ → AnalyticManifold.{u} 𝕜 E}
    (ι : ∀ i, AnalyticMap (N i) M) (hι : ∀ i, IsAnalyticOpenEmbedding (ι i))
    (hcov : (⋃ i, range (ι i)) = univ) {L L' : BlowUpSequence ψ₀ M}
    (h : ∀ i, L.pullback (ι i) (hι i).1 = L'.pullback (ι i) (hι i).1) : L = L' :=
  eq_of_pullback_cover ι (fun i => (hι i).1)
    (fun x => mem_iUnion.mp (hcov ▸ mem_univ x)) L L' h

end AnalyticManifold.BlowUpSequence

end
