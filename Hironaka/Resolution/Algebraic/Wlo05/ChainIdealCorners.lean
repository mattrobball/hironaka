/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColon
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Two ring-level corners of the chain form

Two elementary facts about the chain ideal
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) used in the proof of the statement CP1
of the embedded desingularization, the local form of the ideal at the absorbing stage:

* **A prime containing the chain form contains the chain.** A prime ideal containing
  `M⁰ · chainIdeal f M` and none of the monomials `M⁰, M_i` contains every chain equation `f_i`
  (`span_range_le_of_mul_chainIdeal_le_prime`): the generator `(∏_{i'<i} M_{i'}) f_i` lies in the
  prime and its monomial factor does not. Geometrically, another component's strict transform
  through a point of `Γ̃` would contain `Γ̃` near the point — impossible for strict transforms of
  distinct components (the disjointness clause of the protected state); used in
  `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Absorbed`.
* **The hypersurface case.** In a local ring, an ideal inside a principal prime `(g)`, `g ∈ 𝔪`,
  that contains an element outside `𝔪²` equals `(g)`
  (`eq_span_singleton_of_le_of_exists_notMem_sq`): the element is `g y` with `y` a unit. This is
  the local form at the absorbing stage when the absorbed component is a hypersurface (the chain
  has length one, `J_p = (g)`, no monomial); used in
  `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainCaseA`.
-/

public section

universe u

open Ideal

namespace Hironaka.Resolution

variable {R : Type*} [CommRing R]

/-- A finite product of elements outside a prime ideal is outside it. -/
theorem prod_notMem_of_forall_notMem {P : Ideal R} (hP : P.IsPrime) {ι : Type*} (s : Finset ι)
    (g : ι → R) (hg : ∀ i ∈ s, g i ∉ P) : ∏ i ∈ s, g i ∉ P := by
  intro h
  obtain ⟨i, hi, hgi⟩ := hP.prod_mem_iff.mp h
  exact hg i hi hgi

/-- A prime containing `M⁰ · chainIdeal f M` and none of the monomials contains every chain
equation. -/
theorem span_range_le_of_mul_chainIdeal_le_prime {P : Ideal R} (hP : P.IsPrime) {r : ℕ}
    (f M : Fin r → R) (hM : ∀ i, M i ∉ P) (m₀ : R) (hm₀ : m₀ ∉ P)
    (h : span {m₀} * chainIdeal f M ≤ P) : span (Set.range f) ≤ P := by
  rw [span_le]
  rintro _ ⟨i, rfl⟩
  have hgen : m₀ * chainGen f M i ∈ P :=
    h (Ideal.mul_mem_mul (mem_span_singleton_self m₀) (chainGen_mem f M i))
  have h1 : chainGen f M i ∈ P := (hP.mem_or_mem hgen).resolve_left hm₀
  have h2 : (∏ i' ∈ Finset.univ.filter (fun i' : Fin r => i' < i), M i') ∉ P :=
    prod_notMem_of_forall_notMem hP _ M fun i' _ => hM i'
  exact (hP.mem_or_mem h1).resolve_left h2

/-- The hypersurface case: in a local ring, an ideal inside `(g)`, `g ∈ 𝔪`, containing an element
outside `𝔪²` is `(g)`. -/
theorem eq_span_singleton_of_le_of_exists_notMem_sq [IsLocalRing R] {g : R}
    (hg : g ∈ IsLocalRing.maximalIdeal R) {J : Ideal R} (hJ : J ≤ span {g})
    (hx : ∃ x ∈ J, x ∉ IsLocalRing.maximalIdeal R ^ 2) : J = span {g} := by
  refine le_antisymm hJ ?_
  obtain ⟨x, hxJ, hx2⟩ := hx
  obtain ⟨y, rfl⟩ := mem_span_singleton'.mp (hJ hxJ)
  -- `x = y * g`; `y` is a unit, else `x ∈ 𝔪²`
  have hy : IsUnit y := by
    by_contra hy
    apply hx2
    rw [pow_two]
    exact Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hy)) hg
  rw [span_singleton_le_iff_mem]
  obtain ⟨u, rfl⟩ := hy
  have : ((u⁻¹ : Rˣ) : R) * (↑u * g) = g := by rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [← this]
  exact mul_mem_left _ _ hxJ

/-- The chain ideal of a chain of length one is the principal ideal of its equation. -/
theorem chainIdeal_one_eq_span (g : R) (M : Fin 1 → R) :
    chainIdeal (fun _ : Fin 1 => g) M = span {g} := by
  rw [chainIdeal_eq_span_range_chainGen]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rw [Fin.fin_one_eq_zero i, chainGen_zero]
  · rintro rfl
    exact ⟨0, chainGen_zero _ _⟩

end Hironaka.Resolution
