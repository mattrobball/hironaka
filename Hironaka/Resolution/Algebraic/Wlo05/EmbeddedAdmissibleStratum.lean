/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Admissible chain strata

The hypothesis of the one-blow-up statement CP4 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4`) and the conclusion of CP3. A centre `Z = (f₀ = ⋯
= f_{l−1} = 0, e_j = 0 (j ∈ s))`, a chain stratum at `p` through the protected component `Γ`, is
**admissible** when the exponent of the stratum's OWN level along the members `s` is positive (the
condition (★) below): `∃ k ∈ s, b k ≠ 0` at level `l = 0`, `∃ k ∈ s, a (l − 1) k ≠ 0` at level `l ≥
1`. The weaker condition `K ≤ Z` (the centre lies in `V(K)`) is the CUMULATIVE condition `M⁰ M₀ ⋯
M_{l−1} ∈ (e_s)` (`span_mul_chainKIdeal_le_stratum_iff` in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4Algebra`) and does NOT suffice: for `K = e·(f₁, e′)`
along `Γ = V(f₁, g)` and `Z = V(f₁, e)`, `K ≤ Z` holds but the mark-`1` transform in the chart `e =
ε, f₁ = ε f₁′` is `(ε f₁′, e′)`, which is no K-shape at the points of `Γ′ ∩ F`. CP3 derives (★) for
every centre of a run on a protected state
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates`); CP4 consumes it.

A third predicate covers the un-isolated run: the **terminal-normal strata**
`Z = V(f₀, …, f_r, e_j : j ∈ s)`, `s ≠ ∅` — ALL of `Γ`'s equations plus boundary equations, so
`Z ⊆ Γ` locally without containing `Γ` — arise as the pushed-forward centres of a boundary pass on
an un-isolated state (in `𝔸²` with coordinates `g, e`, boundary `V(e)` and ideal `(g)`, the pass
over `V(e)` produces the centre `V(g, e)`); their transform needs no (★) and consumes no unit. They
never occur in a run on an isolated (protected) state, whose centres never contain all of `Γ`'s
equations at once.

The predicates package the stratum with the chain data in ONE existential: the stratum, the
K-shape (or the un-isolated chain form) and the exponent condition are read in the SAME chain
coordinates. Conventions: the chain index `i` is the level `i + 1`; the top-level exponents `b`
are the level `0` (`M⁰`); the stratum's level is `l ≤ r`, so the last chain equation `g = f_r` is
never among the stratum's equations (`Γ ⊄ Z` locally). These statements are not in the literature.
-/

@[expose] public section

universe u

open AlgebraicGeometry Scheme Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- **`Z` is an admissible chain stratum for the K-shape `K` along `Γ` at `p`** (the conclusion of
CP3 and the hypothesis of CP4, isolated form) — in chain coordinates shared with the K-shape of
`K`, `Z_p = (f₀, …, f_{l−1}, z_s)` with `l ≤ r` and `s` among the members' coordinates, and (★):
the stratum's own level carries an exponent along `s` (`b` at level `0`, `a (l − 1)` at level
`l ≥ 1`). -/
def AdmissibleChainStratumKAt (E : DivisorFamily X) (K Γ Z : X.IdealSheafData) (p : X) : Prop :=
  ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk p)
    (c : {j : E.ι // p ∈ (E.component j).support} → Fin n) (r : ℕ) (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) (b : Fin n → ℕ) (l : ℕ) (hl : l ≤ r) (s : Finset (Fin n)),
    ChainCoords E Γ p z c σ a ∧ (∀ k, b k ≠ 0 → k ∈ Set.range c) ∧
      K.stalkIdeal p =
        Ideal.span {monomialOf z b} * chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i)) ∧
      ↑s ⊆ Set.range c ∧
      Z.stalkIdeal p = Ideal.span ((z ∘ σ) '' {i | i.val < l}) ⊔ Ideal.span (z '' ↑s) ∧
      (l = 0 → ∃ k ∈ s, b k ≠ 0) ∧ (0 < l → ∃ k ∈ s, a ⟨l - 1, by omega⟩ k ≠ 0)

/-- **`Z` is an admissible chain stratum for the un-isolated chain form of `I` along `Γ` at `p`**
(the hypothesis of CP4 for the un-isolated ideal) — the same data with `chainIdeal` (the last
generator `M⁰ M₀ ⋯ M_{r−1} g`) in place of `chainKIdeal`. -/
def AdmissibleChainStratumAt (E : DivisorFamily X) (I Γ Z : X.IdealSheafData) (p : X) : Prop :=
  ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk p)
    (c : {j : E.ι // p ∈ (E.component j).support} → Fin n) (r : ℕ) (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) (b : Fin n → ℕ) (l : ℕ) (hl : l ≤ r) (s : Finset (Fin n)),
    ChainCoords E Γ p z c σ a ∧ (∀ k, b k ≠ 0 → k ∈ Set.range c) ∧
      I.stalkIdeal p =
        Ideal.span {monomialOf z b} * chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) ∧
      ↑s ⊆ Set.range c ∧
      Z.stalkIdeal p = Ideal.span ((z ∘ σ) '' {i | i.val < l}) ⊔ Ideal.span (z '' ↑s) ∧
      (l = 0 → ∃ k ∈ s, b k ≠ 0) ∧ (0 < l → ∃ k ∈ s, a ⟨l - 1, by omega⟩ k ≠ 0)

/-- **`Z` is a terminal-normal stratum for the un-isolated chain form of `I` along `Γ` at `p`** —
in chain coordinates shared with the chain form of `I`, `Z_p = (f₀, …, f_r, z_s)` with `s` a
NONEMPTY set of the members' coordinates: all of `Γ`'s equations plus boundary equations, no
exponent condition. -/
def TerminalNormalStratumAt (E : DivisorFamily X) (I Γ Z : X.IdealSheafData) (p : X) : Prop :=
  ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk p)
    (c : {j : E.ι // p ∈ (E.component j).support} → Fin n) (r : ℕ) (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) (b : Fin n → ℕ) (s : Finset (Fin n)),
    ChainCoords E Γ p z c σ a ∧ (∀ k, b k ≠ 0 → k ∈ Set.range c) ∧
      I.stalkIdeal p =
        Ideal.span {monomialOf z b} * chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) ∧
      ↑s ⊆ Set.range c ∧ s.Nonempty ∧
      Z.stalkIdeal p = Ideal.span (Set.range (z ∘ σ)) ⊔ Ideal.span (z '' ↑s)

/-- A terminal-normal stratum contains `Γ` locally (`Γ_p ≤ Z_p`), and `I` has the chain form at
`p`. -/
theorem TerminalNormalStratumAt.le_and_chainRelativeAt {E : DivisorFamily X}
    {I Γ Z : X.IdealSheafData} {p : X} (h : TerminalNormalStratumAt E I Γ Z p) :
    Γ.stalkIdeal p ≤ Z.stalkIdeal p ∧ ChainRelativeAt E I Γ p := by
  obtain ⟨n, z, c, r, σ, a, b, s, hcc, hb, hI, -, -, hZ⟩ := h
  refine ⟨?_, ⟨n, z, c, r, σ, a, b, hcc, hb, hI⟩⟩
  rw [hZ, hcc.2.2.2.2.2.2]
  exact le_sup_left

/-- An admissible stratum for the K-shape is in particular a chain-relative stratum
(`IsChainStratumAt`), and `K` has the K-shape at `p`. -/
theorem AdmissibleChainStratumKAt.isChainStratumAt {E : DivisorFamily X} {K Γ Z : X.IdealSheafData}
    {p : X} (h : AdmissibleChainStratumKAt E K Γ Z p) :
    IsChainStratumAt E Γ Z p ∧ ChainRelativeKAt E K Γ p := by
  obtain ⟨n, z, c, r, σ, a, b, l, -, s, hcc, hb, hK, hs, hZ, -, -⟩ := h
  exact ⟨⟨n, z, c, r, σ, a, hcc, l, s, hs, hZ⟩, ⟨n, z, c, r, σ, a, b, hcc, hb, hK⟩⟩

/-- An admissible stratum for the un-isolated form is a chain-relative stratum, and `I` has the
chain form at `p`. -/
theorem AdmissibleChainStratumAt.isChainStratumAt {E : DivisorFamily X} {I Γ Z : X.IdealSheafData}
    {p : X} (h : AdmissibleChainStratumAt E I Γ Z p) :
    IsChainStratumAt E Γ Z p ∧ ChainRelativeAt E I Γ p := by
  obtain ⟨n, z, c, r, σ, a, b, l, -, s, hcc, hb, hI, hs, hZ, -, -⟩ := h
  exact ⟨⟨n, z, c, r, σ, a, hcc, l, s, hs, hZ⟩, ⟨n, z, c, r, σ, a, b, hcc, hb, hI⟩⟩

end Hironaka.Resolution
