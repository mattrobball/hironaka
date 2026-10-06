/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.Collapse
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Correspondences of boundary families across a map

A *correspondence* between two hypersurface families across a map `g : B → A` (the boundary
correspondence of `Functor/EraseEmptyBoundary.lean` is the case of a diffeomorphism): an order
embedding `e₀ : GA.ι ↪o GB.ι` such that the member `e₀ k` of `GB` is the inverse image of the
member `k` of `GA`, the members of `GB` outside the range of `e₀` are empty, and the original
members are matched. It is the relation between the boundary families at the last stages of two
disjoining lists related by a local analytic isomorphism, possibly with extra empty exceptional
divisors (the padding by empty blow-ups; [Kol07, 34.1], [Kol07, 32]). This module proves that the
relation passes to the collapsed families (`collapse`, the original members collapsed into one
first member): the collapsed boundary of the one list is an empty extension of the inverse image
of the collapsed boundary of the other (`PullbackCorr.exists_isEmptyExtension_collapse`) — the
hypothesis of the input family's `IndifferentToEmptyMembers`. Used by `DisjoinedNatural.lean` for
the independence of the shrinking open.
-/

@[expose] public section

universe u

open Set

namespace Manifold

namespace HypersurfaceFamily

variable {A B : Type u}

/-- A correspondence across a map `g : B → A`: an order embedding `e₀ : GA.ι ↪o GB.ι` matching the
members through `g` (`GB.hyp (e₀ k) = g⁻¹(GA.hyp k)`), the members of `GB` outside its range empty,
and the original members (indexed by `ι₀`) matched. -/
def PullbackCorr (g : B → A) (GA : HypersurfaceFamily A) (GB : HypersurfaceFamily B) {ι₀ : Type u}
    (oA : ι₀ → GA.ι) (oB : ι₀ → GB.ι) : Prop :=
  ∃ e₀ : GA.ι ↪o GB.ι, (∀ k, GB.hyp (e₀ k) = g ⁻¹' GA.hyp k) ∧
    (∀ b, b ∉ Set.range e₀ → GB.hyp b = ∅) ∧ ∀ j, e₀ (oA j) = oB j

namespace PullbackCorr

/-- The identity correspondence between `GA` and its inverse image `g⁻¹(GA)`. -/
theorem refl_comap (g : B → A) (GA : HypersurfaceFamily A) {ι₀ : Type u} (oA : ι₀ → GA.ι) :
    PullbackCorr g GA (GA.comap g) oA oA :=
  ⟨(OrderIso.refl GA.ι).toOrderEmbedding, fun _ => rfl, fun b hb => absurd ⟨b, rfl⟩ hb,
    fun _ => rfl⟩

/-- Transport along equalities of the families (heterogeneously for the original members). -/
theorem congr {g : B → A} {GA GA' : HypersurfaceFamily A} {GB GB' : HypersurfaceFamily B}
    {ι₀ : Type u} {oA : ι₀ → GA.ι} {oB : ι₀ → GB.ι} {oA' : ι₀ → GA'.ι} {oB' : ι₀ → GB'.ι}
    (hA : GA = GA') (hB : GB = GB') (hoA : ∀ j, HEq (oA j) (oA' j))
    (hoB : ∀ j, HEq (oB j) (oB' j)) (h : PullbackCorr g GA GB oA oB) :
    PullbackCorr g GA' GB' oA' oB' := by
  subst hA
  subst hB
  obtain rfl : oA = oA' := funext fun j => eq_of_heq (hoA j)
  obtain rfl : oB = oB' := funext fun j => eq_of_heq (hoB j)
  exact h

/-- Composition with an empty extension (the same nonempty members plus extra empty ones) on the
target side, the original members matched along it. -/
theorem trans_isEmptyExtension {g : B → A} {GA : HypersurfaceFamily A}
    {GB GB' : HypersurfaceFamily B} {ι₀ : Type u} {oA : ι₀ → GA.ι} {oB : ι₀ → GB.ι}
    {oB' : ι₀ → GB'.ι} (h : PullbackCorr g GA GB oA oB) {e : GB.ι ↪o GB'.ι}
    (he : IsEmptyExtension e) (hoB : ∀ j, e (oB j) = oB' j) :
    PullbackCorr g GA GB' oA oB' := by
  obtain ⟨e₀, h1, h2, h3⟩ := h
  refine ⟨e₀.trans e, fun k => ?_, fun b hb => ?_, fun j => ?_⟩
  · change GB'.hyp (e (e₀ k)) = _
    rw [he.1, h1]
  · by_cases hb' : b ∈ Set.range e
    · obtain ⟨b₀, rfl⟩ := hb'
      have hb₀ : b₀ ∉ Set.range e₀ := fun ⟨k, hk⟩ => hb ⟨k, by
        change e (e₀ k) = e b₀
        rw [hk]⟩
      rw [he.1, h2 b₀ hb₀]
    · exact he.2 b hb'
  · change e (e₀ (oA j)) = _
    rw [h3, hoB]

end PullbackCorr

/-! ### The collapsed families -/

/-- The lift of an order embedding of the right summands to the lexicographic sums with a common
left summand (`Sum.map id e`) — the index sets of the collapsed families, whose first member is the
collapsed one. -/
def sumLexMapRightEmb {α γ δ : Type*} [LinearOrder α] [LinearOrder γ] [LinearOrder δ]
    (e : γ ↪o δ) : α ⊕ₗ γ ↪o α ⊕ₗ δ :=
  OrderEmbedding.ofMapLEIff (fun x => toLex (Sum.map id e (ofLex x))) (by
    intro x y
    obtain ⟨x, rfl⟩ := toLex.surjective x
    obtain ⟨y, rfl⟩ := toLex.surjective y
    rcases x with a | c <;> rcases y with b | d
    · simp only [ofLex_toLex, Sum.map_inl, id_eq, Sum.Lex.inl_le_inl_iff]
    · simp only [ofLex_toLex, Sum.map_inl, Sum.map_inr, Sum.Lex.inl_le_inr]
    · simp only [ofLex_toLex, Sum.map_inl, Sum.map_inr, Sum.Lex.not_inr_le_inl]
    · simp only [ofLex_toLex, Sum.map_inr, Sum.Lex.inr_le_inr_iff, e.le_iff_le])

/-- An order embedding restricted to the members outside the originals. -/
def notOriginalEmb {GA : HypersurfaceFamily A} {GB : HypersurfaceFamily B} (e₀ : GA.ι ↪o GB.ι)
    {pA : GA.ι → Prop} {pB : GB.ι → Prop} (hp : ∀ k, ¬ pA k → ¬ pB (e₀ k)) :
    {k // ¬ pA k} ↪o {k // ¬ pB k} :=
  OrderEmbedding.ofMapLEIff (fun k => ⟨e₀ k.1, hp k.1 k.2⟩) (fun _ _ => e₀.le_iff_le)

/-- The collapsed families of a correspondence: a correspondence across `g` with matched original
members induces an empty extension of the inverse image of the collapsed family of `GA` into the
collapsed family of `GB`, the collapsed members being the unions of the originals. -/
theorem PullbackCorr.exists_isEmptyExtension_collapse {g : B → A} {GA : HypersurfaceFamily A}
    {GB : HypersurfaceFamily B} {ι₀ : Type u} {oA : ι₀ → GA.ι} {oB : ι₀ → GB.ι}
    (h : PullbackCorr g GA GB oA oB) :
    ∃ e : ((GA.collapse (fun k => k ∈ Set.range oA)).comap g).ι ↪o
        (GB.collapse (fun k => k ∈ Set.range oB)).ι, IsEmptyExtension e := by
  obtain ⟨e₀, h1, h2, h3⟩ := h
  have hp : ∀ k, k ∉ Set.range oA → e₀ k ∉ Set.range oB :=
    fun k hk ⟨j, hj⟩ => hk ⟨j, e₀.injective (by rw [h3, hj])⟩
  refine ⟨sumLexMapRightEmb (notOriginalEmb e₀ hp), fun k => ?_, fun b hb => ?_⟩
  · obtain ⟨k', rfl⟩ : ∃ k', toLex k' = k := ⟨ofLex k, rfl⟩
    rcases k' with u | ⟨k, hk⟩
    · change (GB.collapse _).hyp (toLex (Sum.inl u)) = g ⁻¹' (GA.collapse _).hyp (toLex (Sum.inl u))
      rw [collapse_hyp_inl, collapse_hyp_inl, Set.preimage_iUnion]
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨⟨_, j, rfl⟩, hx⟩
        refine ⟨⟨oA j, j, rfl⟩, ?_⟩
        change x ∈ g ⁻¹' GA.hyp (oA j)
        rw [← h1, h3]
        exact hx
      · rintro ⟨⟨_, j, rfl⟩, hx⟩
        refine ⟨⟨oB j, j, rfl⟩, ?_⟩
        change x ∈ GB.hyp (oB j)
        rw [← h3, h1]
        exact hx
    · change (GB.collapse _).hyp (toLex (Sum.inr ⟨e₀ k, hp k hk⟩)) =
        g ⁻¹' (GA.collapse _).hyp (toLex (Sum.inr ⟨k, hk⟩))
      rw [collapse_hyp_inr, collapse_hyp_inr]
      exact h1 k
  · obtain ⟨b', rfl⟩ : ∃ b', toLex b' = b := ⟨ofLex b, rfl⟩
    rcases b' with u | ⟨k', hk'⟩
    · exact absurd ⟨toLex (Sum.inl u), rfl⟩ hb
    · rw [collapse_hyp_inr]
      refine h2 k' ?_
      rintro ⟨k, hk⟩
      have hkA : k ∉ Set.range oA := fun ⟨j, hj⟩ => hk' ⟨j, by rw [← h3, hj, hk]⟩
      refine hb ⟨toLex (Sum.inr ⟨k, hkA⟩), ?_⟩
      change toLex (Sum.inr (⟨e₀ k, hp k hkA⟩ : {k // ¬ k ∈ Set.range oB})) =
        toLex (Sum.inr ⟨k', hk'⟩)
      exact congrArg (fun x : {k // ¬ k ∈ Set.range oB} => toLex (Sum.inr x)) (Subtype.ext hk)

end HypersurfaceFamily

end Manifold
