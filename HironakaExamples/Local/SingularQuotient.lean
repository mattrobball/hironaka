/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Algebra.Local.QuotientParameters
import Hironaka.Algebra.Local.RegularSystem

/-!
# The quotient of a regular local ring by a nonzero element of `𝔪²` is not regular

The algebra behind the example showing that "the restriction of a smooth blow-up sequence need
not be a smooth blow-up sequence" [Kol07, 30.2]: the cuspidal cubic `V(y² − x³) ⊂ 𝔸²` is
singular at the origin (`HironakaExamples/Sequence/CuspWitness.lean`).  Its local ring there is
`R/(g)` with `R = k[x, y]_{(x, y)}` regular and `g = y² − x³ ∈ 𝔪²`.  If `R/(g)` were regular,
`IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt` ([Sta, Tag 00NR]) would make
`(g)` the ideal of an initial segment `x_0, …, x_{c-1}` of a regular system of parameters of `R`:
for `c = 0` this forces `g = 0`, and for `c ≥ 1` it puts `x_0 ∈ (g) ⊆ 𝔪²`, against
`notMem_sq_of_span_eq` (no member of a regular system of parameters lies in `𝔪²`).  Standard; also
used for the real circle example of the analytic part (`HironakaExamples/RealPlaneCircle.lean`).
-/

public section

namespace Hironaka.Local

open IsLocalRing

open IsLocalRing _root_.Ideal

universe u

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A regular local ring modulo a nonzero element of `𝔪²` is not a regular local ring
([Sta, Tag 00NR] would make the element part of a regular system of parameters, which never lies
in `𝔪²`). -/
theorem not_isRegularLocalRing_quotient_span_singleton {g : R} (hg0 : g ∈ nonZeroDivisors R)
    (hg : g ∈ maximalIdeal R ^ 2) : ¬ IsRegularLocalRing (R ⧸ Ideal.span {g}) := by
  intro hQ
  obtain ⟨n, c, x, hcn, hn, hx, hI⟩ :=
    IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt (Ideal.span {g})
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    rw [span_image_lt_zero] at hI
    have hg' : g = 0 := (Submodule.mem_bot R).mp (hI ▸ Ideal.mem_span_singleton_self g)
    exact nonZeroDivisors.ne_zero hg0 hg'
  · have h0n : 0 < n := lt_of_lt_of_le hc hcn
    have h0 : (⟨0, h0n⟩ : Fin n) ∈ {j : Fin n | j.val < c} := hc
    have hmem : x ⟨0, h0n⟩ ∈ Ideal.span {g} := hI ▸ Ideal.subset_span ⟨_, h0, rfl⟩
    exact notMem_sq_of_span_eq x hx hn ⟨0, h0n⟩ ((Ideal.span_singleton_le_iff_mem _).mpr hg hmem)

end Hironaka.Local
