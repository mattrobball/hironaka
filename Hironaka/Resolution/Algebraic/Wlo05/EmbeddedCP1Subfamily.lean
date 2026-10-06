/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP1 and sub-families of the boundary

Step 2.2 of the proof of [Kol07, Theorem 103] (item 104, Step 2.2) runs Lemma 102 on the triple
`(X_r, I_r, F_r + H_r)` whose boundary is the exceptional sub-family `F_r` of the total transform
`E_r` of the original boundary. The statement CP1 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) for that run speaks about the
transforms of `F_r`, while CP1 along the whole run of `BO_{n,1}` speaks about the transforms of
`E_r`. The two agree at the points of the component's strict transform because the missing members —
the birational transforms of the original members — miss `V(I_r)` from the end of Step 2.1 on, hence
miss `c̃`.

This module holds the bookkeeping. The chain form at `p` only sees the members through `p`, so an
injection of index types with equal members whose complement misses `p` does not change it
(`chainRelativeAt_iff_of_embeds`, the common generalisation of `chainRelativeAt_of_extendsByEmpty`
and `chainRelativeAt_subfamily_iff`). Such an injection propagates along a blow-up sequence to the
total transforms, with complement the transforms of the missing originals
(`exists_embeds_totalTransformSeq`, by recursion on the sequence; the total transform is that of
[Kol07, Definition 25]). CP1 carries from the sub-family to the family when those transforms miss
`c̃` below the first containing stage (`cp1For_of_embeds`; the stop rule does not involve the
boundary). Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step22`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- The common generalisation of `chainRelativeAt_of_extendsByEmpty` and
`chainRelativeAt_subfamily_iff`: for an injection `e` of index types carrying the members of `E₁`
to members of `E₂` with the same ideal sheaves, such that every member of `E₂` outside its range
misses `p`, the chain forms along `Γ` at `p` for `E₁` and `E₂` agree — the members through `p`
correspond. -/
theorem chainRelativeAt_iff_of_embeds {E₁ E₂ : DivisorFamily X} (e : E₁.ι → E₂.ι)
    (he : Function.Injective e) (hcomp : ∀ a, E₂.component (e a) = E₁.component a) {p : X}
    (hmiss : ∀ b, b ∉ Set.range e → p ∉ (E₂.component b).support) {I Γ : X.IdealSheafData} :
    ChainRelativeAt E₁ I Γ p ↔ ChainRelativeAt E₂ I Γ p := by
  classical
  -- the correspondence of the members through `p`
  let θ : {i : E₁.ι // p ∈ (E₁.component i).support} →
      {j : E₂.ι // p ∈ (E₂.component j).support} :=
    fun i => ⟨e i.1, by rw [hcomp]; exact i.2⟩
  have hpre : ∀ j : {j : E₂.ι // p ∈ (E₂.component j).support},
      ∃ i : {i : E₁.ι // p ∈ (E₁.component i).support}, θ i = j := by
    intro j
    obtain ⟨i, hi⟩ : j.1 ∈ Set.range e := by
      by_contra hj
      exact hmiss j.1 hj j.2
    refine ⟨⟨i, ?_⟩, Subtype.ext hi⟩
    rw [← hcomp, hi]
    exact j.2
  let θ' : {j : E₂.ι // p ∈ (E₂.component j).support} →
      {i : E₁.ι // p ∈ (E₁.component i).support} := fun j => Classical.choose (hpre j)
  have hθθ' : ∀ j, θ (θ' j) = j := fun j => Classical.choose_spec (hpre j)
  have hθinj : Function.Injective θ := fun i i' h =>
    Subtype.ext (he (Subtype.mk.inj h))
  have hθ'θ : ∀ i, θ' (θ i) = i := fun i => hθinj (hθθ' (θ i))
  have hθ'inj : Function.Injective θ' := fun j j' h => by
    rw [← hθθ' j, ← hθθ' j', h]
  have hcompθ : ∀ i : {i : E₁.ι // p ∈ (E₁.component i).support},
      E₂.component (θ i).1 = E₁.component i.1 := fun i => hcomp i.1
  constructor
  · rintro ⟨n, z, c, r, σ, a, b, ⟨hz, hcinj, hcmem, hσinj, hσc, ha, hΓ⟩, hb, hI⟩
    refine ⟨n, z, c ∘ θ', r, σ, a, b, ⟨hz, hcinj.comp hθ'inj, fun j => ?_, hσinj,
      fun i j => hσc i (θ' j), fun i k hk => ?_, hΓ⟩, fun k hk => ?_, hI⟩
    · have h1 := hcmem (θ' j)
      rw [← hcompθ (θ' j), hθθ' j] at h1
      exact h1
    · obtain ⟨i, hi⟩ := ha i k hk
      exact ⟨θ i, by rw [Function.comp_apply, hθ'θ, hi]⟩
    · obtain ⟨i, hi⟩ := hb k hk
      exact ⟨θ i, by rw [Function.comp_apply, hθ'θ, hi]⟩
  · rintro ⟨n, z, c, r, σ, a, b, ⟨hz, hcinj, hcmem, hσinj, hσc, ha, hΓ⟩, hb, hI⟩
    refine ⟨n, z, c ∘ θ, r, σ, a, b, ⟨hz, hcinj.comp hθinj, fun i => ?_, hσinj,
      fun i j => hσc i (θ j), fun i k hk => ?_, hΓ⟩, fun k hk => ?_, hI⟩
    · rw [← hcompθ i]
      exact hcmem (θ i)
    · obtain ⟨j, hj⟩ := ha i k hk
      exact ⟨θ' j, by rw [Function.comp_apply, hθθ', hj]⟩
    · obtain ⟨j, hj⟩ := hb k hk
      exact ⟨θ' j, by rw [Function.comp_apply, hθθ', hj]⟩

/-- An injection of families with equal members (a sub-family) induces, at every stage of a
blow-up sequence, an injection of the total transforms with equal members whose complement
consists of the birational transforms of the original members outside the range (`originalIdx`).
By recursion on the sequence, the injection carried through a blow-up as `Sum.map e₀ id` on the
lexicographic sum. -/
theorem exists_embeds_totalTransformSeq : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    {E₁ E₂ : DivisorFamily X} (e₀ : E₁.ι → E₂.ι) (_ : Function.Injective e₀)
    (_ : ∀ a, E₂.component (e₀ a) = E₁.component a) (i : Fin (S.length + 1)),
    ∃ e : (S.totalTransformSeq E₁ i).ι → (S.totalTransformSeq E₂ i).ι, Function.Injective e ∧
      (∀ b, (S.totalTransformSeq E₂ i).component (e b) =
        (S.totalTransformSeq E₁ i).component b) ∧
      ∀ b, b ∉ Set.range e → ∃ a, a ∉ Set.range e₀ ∧ b = S.originalIdx E₂ i a
  | _, nil _, _, _, e₀, he₀, hcomp₀, _ => ⟨e₀, he₀, hcomp₀, fun b hb => ⟨b, hb, rfl⟩⟩
  | _, cons _ _ _, _, _, e₀, he₀, hcomp₀, ⟨0, _⟩ => ⟨e₀, he₀, hcomp₀, fun b hb => ⟨b, hb, rfl⟩⟩
  | _, cons X D rest, E₁, E₂, e₀, he₀, hcomp₀, ⟨j + 1, h⟩ => by
    -- the injection carried through the blow-up of `D`
    let e₁ : (E₁.totalTransform D).ι → (E₂.totalTransform D).ι :=
      fun b => toLex (Sum.map e₀ id (ofLex b))
    have he₁ : Function.Injective e₁ := fun b b' hbb' => by
      have h2 : Sum.map e₀ id (ofLex b) = Sum.map e₀ id (ofLex b') := toLex_inj.mp hbb'
      exact ofLex.injective (Sum.map_injective.mpr ⟨he₀, Function.injective_id⟩ h2)
    have hcomp₁ : ∀ b, (E₂.totalTransform D).component (e₁ b) =
        (E₁.totalTransform D).component b := by
      intro b
      rcases hb : ofLex b with a | u
      · have hb' : b = toLex (Sum.inl a) := by
          rw [← toLex_ofLex b, hb]
          rfl
        subst hb'
        change (E₂.component (e₀ a)).strictTransform D = (E₁.component a).strictTransform D
        rw [hcomp₀]
      · have hb' : b = toLex (Sum.inr u) := by
          rw [← toLex_ofLex b, hb]
          rfl
        subst hb'
        rfl
    obtain ⟨e, he, hcomp, hmiss⟩ :=
      exists_embeds_totalTransformSeq rest e₁ he₁ hcomp₁ ⟨j, Nat.lt_of_succ_lt_succ h⟩
    refine ⟨e, he, hcomp, fun b hb => ?_⟩
    obtain ⟨a₁, ha₁, rfl⟩ := hmiss b hb
    rcases ha₁' : ofLex a₁ with a | u
    · have ha : a ∉ Set.range e₀ := by
        rintro ⟨a', rfl⟩
        refine ha₁ ⟨toLex (Sum.inl a'), ?_⟩
        rw [← toLex_ofLex a₁, ha₁']
        rfl
      refine ⟨a, ha, ?_⟩
      change rest.originalIdx (E₂.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩ a₁ =
        rest.originalIdx (E₂.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩ (toLex (Sum.inl a))
      rw [← toLex_ofLex a₁, ha₁']
    · exfalso
      refine ha₁ ⟨toLex (Sum.inr u), ?_⟩
      rw [← toLex_ofLex a₁, ha₁']
      rfl

/-- **The family bridge of Step 2.2.** CP1 for the run with the sub-family `E₁` of `E₂` gives CP1
with `E₂`, provided that at every stage below the first containing one the transforms of the
members of `E₂` outside `E₁` miss the strict transform of `c̄`: the stop rule does not involve the
boundary, and at the first containing stage the two total transforms have the same members
through every point of `c̃`. -/
theorem cp1For_of_embeds (S : BlowUpSequence X) (I : X.IdealSheafData) {E₁ E₂ : DivisorFamily X}
    (e₀ : E₁.ι → E₂.ι) (he₀ : Function.Injective e₀)
    (hcomp₀ : ∀ a, E₂.component (e₀ a) = E₁.component a) {η : X}
    (hmiss : ∀ i : Fin S.length,
      (∀ l < i.val, ¬ CenterContains S (vanishingIdeal (Closeds.closure {η})) l) →
      ∀ a, a ∉ Set.range e₀ →
      ∀ p ∈ (S.strictTransformSeq (vanishingIdeal (Closeds.closure {η})) i.castSucc).support,
        p ∉ ((S.totalTransformSeq E₂ i.castSucc).component
          (S.originalIdx E₂ i.castSucc a)).support)
    (h : CP1For S I E₁ η) : CP1For S I E₂ η := by
  intro i hi hmin p hp
  obtain ⟨e, he, hcomp, hm⟩ := exists_embeds_totalTransformSeq S e₀ he₀ hcomp₀ i.castSucc
  refine (chainRelativeAt_iff_of_embeds e he hcomp ?_).mp (h i hi hmin p hp)
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hm b hb
  exact hmiss i hmin a ha p hp

end Hironaka.Resolution
