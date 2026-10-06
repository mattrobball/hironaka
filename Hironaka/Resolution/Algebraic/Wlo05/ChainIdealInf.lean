/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColonRegular
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColon
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The intersection form of a chain ideal

In a regular local ring `R` with a regular system of parameters `z`, chain equations `f = z ∘ σ`
(part of the parameters) and monomials `M_i = ∏_k z_k^{a_{ik}}` in the coordinates OFF the chain,
the chain ideal `I(f; a) = (f₀, M₀ f₁, …, (∏_{i<r} M_i) f_r)` is the intersection of the chain's
prime `(f)` with the K-shape `K(f; a) = (f₀, M₀ f₁, …, ∏_{i<r} M_i)`
(`chainIdeal_eq_span_inf_chainKIdeal`) — the counterpart of the colon identity of
`Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColonRegular` (`chainIdeal_colon_span_eq`), and the
algebra behind the un-isolated ideal `I_Γ ⊓ K` in the statement CP6 of the embedded
desingularization (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`): the ideal of the
loop near an isolated component is recovered from the isolated ideal `K` and the component's ideal.

The proof is an induction on the length of the chain through the quotient by `f₀`, as for the
colon, with the single algebraic input that every monomial `M_i` is a nonzerodivisor modulo the
chain's prime — a monomial in parameters outside a coordinate prime lies outside it
(`monomialOf_notMem_span_chainSeg`, `isPrime_span_image_finset`). The pure form
`chainIdeal_eq_span_inf_chainKIdeal_of_cancel` isolates that input as a hypothesis over any
commutative ring; `cancel_monomialOf_span_range` supplies it in the regular local ring;
`span_mul_chainIdeal_eq_span_inf` is the form with the top-level monomial `M⁰`, through
`P ∩ mA = m (P ∩ A)` for `m` a product of parameters outside the prime `P`. The identities are
used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4Sheaf` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Tools`.
-/

public section

universe u

open Ideal CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Scheme.BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Resolution

/-! ### Chain ideals over any commutative ring -/

section Pure

variable {R : Type u} [CommRing R]

/-- The chain ideal lies in the K-shape: the generators agree except the last, whose K-shape
generator divides it. -/
theorem chainIdeal_le_chainKIdeal {r : ℕ} (f M : Fin (r + 1) → R) :
    chainIdeal f M ≤ chainKIdeal f M := by
  rw [chainIdeal_eq_span_range_chainGen, span_le]
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = Fin.last r
  · subst hi
    have h : chainGen f M (Fin.last r) =
        chainGen (Function.update f (Fin.last r) 1) M (Fin.last r) * f (Fin.last r) := by
      simp [chainGen]
    rw [h]
    exact mul_mem_right _ _ (chainGen_mem _ _ _)
  · have h : chainGen f M i = chainGen (Function.update f (Fin.last r) 1) M i := by
      simp [chainGen, Function.update_of_ne hi]
    rw [h]
    exact chainGen_mem _ _ _

/-- The ideal of a chain of length `r + 2` is the ideal of its head and its tail. -/
theorem span_range_eq_sup_tail {r : ℕ} (f : Fin (r + 2) → R) :
    span (Set.range f) = span {f 0} ⊔ span (Set.range (Fin.tail f)) := by
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact mem_sup_left (subset_span (Set.mem_singleton _))
    · exact mem_sup_right (subset_span ⟨j, rfl⟩)
  · refine sup_le ?_ ?_
    · rw [span_le, Set.singleton_subset_iff]
      exact subset_span (Set.mem_range_self 0)
    · rw [span_le]
      rintro _ ⟨j, rfl⟩
      exact subset_span ⟨j.succ, rfl⟩

/-- The chain of length one: the chain ideal is the ideal of its equation. -/
theorem chainIdeal_zero_eq_span (f M : Fin 1 → R) : chainIdeal f M = span (Set.range f) := by
  rw [chainIdeal_eq_span_range_chainGen]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨0, by rw [Fin.fin_one_eq_zero i, chainGen_zero]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨0, by rw [Fin.fin_one_eq_zero i, chainGen_zero]⟩

/-- The chain's ideal is the ideal of the full chain segment (all indices `≤ r`). -/
theorem span_range_comp_eq_span_image_chainSeg {n r : ℕ} (z : Fin n → R)
    (σ : Fin (r + 1) → Fin n) :
    span (Set.range (z ∘ σ)) = span (z '' ↑(chainSeg σ r)) := by
  rw [← image_comp_le_eq, ← Set.image_univ]
  congr 2
  ext j
  simp [Fin.is_le]

/-- The algebraic core of the intersection form: when every monomial `M i` is a nonzerodivisor
modulo the chain's ideal `(f)`, the chain ideal is the intersection of `(f)` with the K-shape.
Induction on the length through the quotient by `f₀`, as for the colon
(`colon_chainIdeal_eq_chainKIdeal`). -/
theorem chainIdeal_eq_span_inf_chainKIdeal_of_cancel :
    ∀ (r : ℕ) (R : Type u) [CommRing R] (f M : Fin (r + 1) → R),
      (∀ (i : Fin (r + 1)) (y : R), M i * y ∈ span (Set.range f) → y ∈ span (Set.range f)) →
      chainIdeal f M = span (Set.range f) ⊓ chainKIdeal f M := by
  intro r
  induction r with
  | zero =>
    intro R _ f M _
    rw [chainKIdeal_zero, inf_top_eq, chainIdeal_zero_eq_span]
  | succ r ih =>
    intro R _ f M hC
    refine le_antisymm (le_inf (chainIdeal_le_span f M) (chainIdeal_le_chainKIdeal f M)) ?_
    intro x hx
    obtain ⟨hxP, hxK⟩ := Submodule.mem_inf.mp hx
    have hP : span (Set.range f) = span {f 0} ⊔ span (Set.range (Fin.tail f)) :=
      span_range_eq_sup_tail f
    have hle : span {f 0} ≤ span (Set.range f) :=
      span_le.mpr (Set.singleton_subset_iff.mpr (subset_span (Set.mem_range_self 0)))
    -- membership modulo `f₀`
    have hmem : ∀ (J : Ideal R) (y : R), Ideal.Quotient.mk (span {f 0}) y ∈
        J.map (Ideal.Quotient.mk (span {f 0})) ↔ y ∈ J ⊔ span {f 0} :=
      fun J y => Ideal.mem_quotient_iff_mem_sup
    have hrange : span (Set.range (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f)) =
        (span (Set.range f)).map (Ideal.Quotient.mk (span {f 0})) := by
      rw [hP, Ideal.map_sup, map_span, map_span, Set.image_singleton,
        Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self _), span_singleton_zero,
        bot_sup_eq, Set.range_comp]
    have hPmem : ∀ y : R, Ideal.Quotient.mk (span {f 0}) y ∈
        span (Set.range (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f)) ↔
          y ∈ span (Set.range f) := by
      intro y
      rw [hrange, hmem, sup_eq_left.mpr hle]
    -- the cancellation clause for the tail, in the quotient
    have hC' : ∀ (i : Fin (r + 1)) (y : R ⧸ span {f 0}),
        (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail M) i * y ∈
            span (Set.range (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f)) →
          y ∈ span (Set.range (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f)) := by
      intro i y hy
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Function.comp_apply, ← map_mul, hPmem] at hy
      rw [hPmem]
      exact hC i.succ y hy
    have hIH := ih (R ⧸ span {f 0}) (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f)
      (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail M) hC'
    -- `x ≡ M₀ · k` modulo `f₀` with `k` in the tail's K-shape
    rw [chainKIdeal_succ] at hxK
    have hmap : (span {M 0} * chainKIdeal (Fin.tail f) (Fin.tail M)).map
          (Ideal.Quotient.mk (span {f 0})) =
        span {Ideal.Quotient.mk (span {f 0}) (M 0)} *
          chainKIdeal (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f)
            (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail M) := by
      rw [Ideal.map_mul, map_span, Set.image_singleton, chainKIdeal_comp]
    have hxK' : Ideal.Quotient.mk (span {f 0}) x ∈
        span {Ideal.Quotient.mk (span {f 0}) (M 0)} *
          chainKIdeal (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f)
            (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail M) := by
      rw [← hmap, hmem, sup_comm]
      exact hxK
    obtain ⟨k, hk, hxk⟩ := Ideal.mem_span_singleton_mul.mp hxK'
    -- `x ∈ (f)` gives `M₀ k ∈ (f̄')`, hence `k ∈ (f̄')` by the clause at level `0`
    have hkP : k ∈ span (Set.range (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f)) := by
      obtain ⟨k, rfl⟩ := Ideal.Quotient.mk_surjective k
      have hxP' : Ideal.Quotient.mk (span {f 0}) (M 0 * k) ∈
          span (Set.range (Ideal.Quotient.mk (span {f 0}) ∘ Fin.tail f)) := by
        rw [map_mul, hxk, hPmem]
        exact hxP
      rw [hPmem] at hxP' ⊢
      exact hC 0 k hxP'
    -- so `k` lies in the tail's chain ideal, and `x` in the chain ideal
    have hkI : k ∈
        (chainIdeal (Fin.tail f) (Fin.tail M)).map (Ideal.Quotient.mk (span {f 0})) := by
      rw [← chainIdeal_comp, hIH]
      exact Submodule.mem_inf.mpr ⟨hkP, hk⟩
    have hxI : Ideal.Quotient.mk (span {f 0}) x ∈
        (span {M 0} * chainIdeal (Fin.tail f) (Fin.tail M)).map
          (Ideal.Quotient.mk (span {f 0})) := by
      rw [Ideal.map_mul, map_span, Set.image_singleton, ← hxk]
      exact Ideal.mul_mem_mul (mem_span_singleton_self _) hkI
    rw [hmem, sup_comm, ← chainIdeal_succ] at hxI
    exact hxI

end Pure

/-! ### The intersection form in a regular local ring -/

section IntersectionAlgebra

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
  (hz : IsRegularSystemOfParameters z) {r : ℕ} {σ : Fin (r + 1) → Fin n}
  (hσ : Function.Injective σ) {a : Fin (r + 1) → Fin n → ℕ}
  (ha : ∀ i k, k ∈ Set.range σ → a i k = 0)

include hz ha in
/-- A monomial in the coordinates off the chain is a nonzerodivisor modulo the chain's prime. -/
theorem cancel_monomialOf_span_range (i : Fin (r + 1)) (y : R)
    (hy : monomialOf z (a i) * y ∈ span (Set.range (z ∘ σ))) :
    y ∈ span (Set.range (z ∘ σ)) := by
  rw [span_range_comp_eq_span_image_chainSeg] at hy ⊢
  have hP := isPrime_span_image_finset hz.1.symm hz.2 (chainSeg σ r)
  exact (hP.mem_or_mem hy).resolve_left (monomialOf_notMem_span_chainSeg ha hz.1.symm hz.2 i r)

include hz ha in
/-- The intersection form (the counterpart of the colon identity `chainIdeal_colon_span_eq`): in
a regular local ring with a regular system of parameters `z`, chain equations `f = z ∘ σ` and
monomials `M_i = ∏_k z_k^{a_{ik}}` in the coordinates off the chain, the chain ideal is the
intersection of the chain's prime with the K-shape:
`(f₀, M₀ f₁, …, (∏_{i<r} M_i) f_r) = (f₀, …, f_r) ⊓ (f₀, M₀ f₁, …, ∏_{i<r} M_i)`. -/
theorem chainIdeal_eq_span_inf_chainKIdeal :
    chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) =
      Ideal.span (Set.range (z ∘ σ)) ⊓ chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i)) :=
  chainIdeal_eq_span_inf_chainKIdeal_of_cancel r R (z ∘ σ) (fun i => monomialOf z (a i))
    (fun i y hy => cancel_monomialOf_span_range hz ha i y hy)

include hz ha in
/-- The intersection form with the top-level monomial factor `M⁰ = ∏_k z_k^{b_k}` in the
coordinates off the chain, through `P ∩ mA = m (P ∩ A)` for `m` a product of parameters outside
the prime `P`: `M⁰ · I(f; a) = (f) ⊓ M⁰ · K(f; a)`. -/
theorem span_mul_chainIdeal_eq_span_inf (b : Fin n → ℕ) (hb : ∀ k, k ∈ Set.range σ → b k = 0) :
    Ideal.span {monomialOf z b} * chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) =
      Ideal.span (Set.range (z ∘ σ)) ⊓
        (Ideal.span {monomialOf z b} * chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i))) := by
  apply le_antisymm
  · refine le_inf ?_ (Ideal.mul_mono_right (chainIdeal_le_chainKIdeal _ _))
    exact Ideal.mul_le_right.trans (chainIdeal_le_span _ _)
  · intro x hx
    obtain ⟨hxP, hxK⟩ := Submodule.mem_inf.mp hx
    obtain ⟨k, hk, rfl⟩ := Ideal.mem_span_singleton_mul.mp hxK
    have hkP : k ∈ span (Set.range (z ∘ σ)) := by
      rw [span_range_comp_eq_span_image_chainSeg] at hxP ⊢
      have hP := isPrime_span_image_finset hz.1.symm hz.2 (chainSeg σ r)
      exact (hP.mem_or_mem hxP).resolve_left
        (monomialOf_notMem_span_chainSeg (a := fun _ : Fin (r + 1) => b)
          (fun _ k hk => hb k hk) hz.1.symm hz.2 0 r)
    have hkI : k ∈ chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) := by
      rw [chainIdeal_eq_span_inf_chainKIdeal hz ha]
      exact Submodule.mem_inf.mpr ⟨hkP, hk⟩
    exact Ideal.mul_mem_mul (mem_span_singleton_self _) hkI

end IntersectionAlgebra

end Hironaka.Resolution
