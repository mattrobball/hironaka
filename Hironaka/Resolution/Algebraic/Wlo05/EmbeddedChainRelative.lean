/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.Embedded
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Chain-relative monomial ideals and the protected state

The local form of the ideal of the embedded desingularization loop
(`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) near an isolated component. It replaces
Włodarczyk's Claim of the proof of [Wlo05, Theorem 4.7.1] — that at the absorbing moment the
controlled transform of `I_Y` agrees with the ideal of the strict transform `Γ̃` of the absorbed
component near `Γ̃` — which is false for the order of the steps used here
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`). Near every point `p` of `Γ̃`, with `H¹ ⊃
H² ⊃ … ⊃ H^{(r)} ⊃ Γ̃` the maximal-contact chain of the absorbing round and `f₀, …, f_r` its
equations (`Γ̃ = V(f₀, …, f_r)`), the ideal is

  `I_p = M⁰ · (f₀, M₀ f₁, M₀ M₁ f₂, …, (M₀ ⋯ M_{r−1}) f_r)`

with `M_i` a monomial in the boundary members through `p`, the monomial factor contributed by the
round at level `i + 1` of the chain, and `M⁰` a top-level monomial (`1` when the top level has no
round of order `≥ 2` near `Γ̃`); the bracket is the **chain ideal** `chainIdeal f M`. The isolated
ideal `K = I : I_{Γ̃}` is the same with the last `f_r` replaced by `1` (the **K-shape**
`chainKIdeal`; `K = ⊤` when every monomial is `1`), and every later state of the loop near `Γ̃` is
again of this shape with peeled monomials. For example, in three coordinates with one boundary
member `e`, the ideal `(x, e a, e² y)` has chain `x, a, y` and monomials `M₀ = M₁ = e`, and its
colon by `(x, a, y)` is `(x, e a, e²)`.

This module holds the definitions: the chain ideal and the K-shape, the local predicates
`ChainRelativeAt` (for `I`) and `ChainRelativeKAt` (for `K`), the shape `IsChainStratumAt` of a
chain-relative stratum, and the invariant `ProtectedState` of the loop for an absorbed component,
in the template of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedSmoothWindow`. The coordinates are
those of [Kol07, Definition 24] at `p` (`DivisorFamily.IsSncAt`: a regular system of parameters `z`
with each member through `p` given by one `z_{c(j)}`); the chain equations are `z ∘ σ` for an
injection `σ` avoiding the members' coordinates, and the exponent vectors `a i` are supported on the
members' coordinates. `M_i = 1` is allowed at every level (the corners `(1, e)` and `(e, 1)`).

## The six statements CP1–CP6

The clauses of [Wlo05, Theorem 1.0.2] for `BED` rest on six statements about the loop, proved in
the modules `EmbeddedCP1*` to `EmbeddedCP6*`; they are not in the literature, and they replace
Włodarczyk's Claim.

* **CP1 (the local form at the absorbing stage).** Along a run of `BMO_1`, at the FIRST stage whose
  centre contains the strict transform `Γ̃` of a component of `V(I)`, the marked transform of `I`
  is chain-relative monomial along `Γ̃` at every point of `Γ̃` (`ChainRelativeAt`; the predicate
  `CP1For` of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For`), and the strict transforms of
  the other components are disjoint from `Γ̃` there. Proved by descending the maximal-contact chain
  of the round one hypersurface at a time (`Hironaka.Resolution.Algebraic.Wlo05.ChainRelativeLift`).
* **CP2 (the isolated ideal).** The colon of a chain-relative monomial ideal by the ideal of `Γ̃`
  has the K-shape (`ChainRelativeKAt`; `chainIdeal_colon_span_eq` of
  `Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColonRegular`), so at the absorbing stage the
  isolated marked triple is in the protected state for the absorbed component
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry`).
* **CP3 (the centres of the continuation).** Every centre of a run of `BMO_1` on a state whose
  ideal has the K-shape, or the un-isolated form, along a protected `Γ̃` is, at each of its points
  on `Γ̃`, a chain-relative stratum in the chain coordinates: an initial segment `f₀, …, f_{l−1}`
  of the chain together with some boundary members (`IsChainStratumAt`; `CP3For` of
  `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates`).
* **CP4 (one blow-up).** Blowing up such a stratum keeps `Γ̃` smooth and with simple normal
  crossings with the total transform of the boundary, and transports the K-shape of `K` (and the
  un-isolated form of `I`) to the mark-`1` transforms along `Γ̃`
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4`).
* **CP5 (the protected state through the loop).** Once a component is absorbed and isolated, every
  later state of the loop is protected for it — `Γ̃` smooth, integral, with simple normal crossings
  with the boundary, disjoint from the remaining components, and `K` in the K-shape along it — and
  at the end the isolated ideal is the unit ideal near `Γ̃` (`ProtectedState`; `protected_bedAux`
  of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5`).
* **CP6 (the end identity).** Following the un-isolated ideal `I_{Γ̃} ⊓ K` through the loop
  (`Hironaka.Resolution.Algebraic.Wlo05.ChainIdealInf`), at the end of the loop the transform of
  `I_Y` is the product of the components' final strict transforms, which are pairwise disjoint
  (`markedTransformSeq_bedAux_last_eq_prod` of
  `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop`); with CP5 this gives the final strict
  transform smooth and snc with the boundary, and the fine form of the full transform
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCPBridge`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka IsLocalRing BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Resolution

/-! ### The chain ideal (pure algebra) -/

section Algebra

variable {R : Type*} [CommRing R]

/-- The **chain ideal** of the equations `f` and the monomials `M`,
`(f₀, M₀ f₁, M₀ M₁ f₂, …, (∏_{i' < i} M_{i'}) f_i, …)` — the local form of the ideal at the
absorbing stage (CP1). -/
def chainIdeal {r : ℕ} (f M : Fin r → R) : Ideal R :=
  Ideal.span (Set.range fun i : Fin r =>
    (∏ i' ∈ Finset.univ.filter (fun i' : Fin r => i' < i), M i') * f i)

/-- The monomial `∏ z_k^{a_k}` in the coordinates `z` with exponent vector `a`. -/
def monomialOf {n : ℕ} (z : Fin n → R) (a : Fin n → ℕ) : R :=
  ∏ k, z k ^ a k

/-- With all monomials `1` the chain ideal is the ideal of the chain's equations. -/
theorem chainIdeal_one {r : ℕ} (f : Fin r → R) :
    chainIdeal f (fun _ => (1 : R)) = Ideal.span (Set.range f) := by
  simp [chainIdeal]

/-- The chain ideal lies in the ideal of the chain's equations. -/
theorem chainIdeal_le_span {r : ℕ} (f M : Fin r → R) :
    chainIdeal f M ≤ Ideal.span (Set.range f) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The **K-shape** — the chain ideal with the last equation replaced by `1`,
`(f₀, M₀ f₁, …, (∏_{i<r} M_i))`, the shape of the isolated ideal (CP2); it is `⊤` when every
`M_i = 1` (`chainIdeal_one`; the branch of the invariant that the last round uses through
`bmoOneRun_eq_nil_of_eq_top`). -/
def chainKIdeal {r : ℕ} (f M : Fin (r + 1) → R) : Ideal R :=
  chainIdeal (Function.update f (Fin.last r) 1) M

/-- The `⊤` convention: with all monomials `1` the K-shape is the unit ideal. -/
theorem chainKIdeal_one {r : ℕ} (f : Fin (r + 1) → R) : chainKIdeal f (fun _ => (1 : R)) = ⊤ := by
  rw [chainKIdeal, chainIdeal_one]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨Fin.last r, by simp⟩) isUnit_one

end Algebra

/-! ### The local predicates -/

variable {X : Scheme.{u}}

/-- **Chain coordinates** at `p` for the family `E` and the closed subscheme `Γ` (the coordinates
of [Kol07, Definition 24] at `p`) — a regular system of parameters `z`, the members of `E` through
`p` given by the coordinates `z (c j)` (`c` injective; `DivisorFamily.IsSncAt`), the chain
equations `z ∘ σ` (`σ` injective, avoiding the members' coordinates) with `Γ_p = (z ∘ σ)`, and
exponent vectors `a i` supported on the members' coordinates. The data are existential in the
predicates below, so they are choice-independent. -/
def ChainCoords (E : DivisorFamily X) (Γ : X.IdealSheafData) (p : X) {n : ℕ}
    (z : Fin n → X.presheaf.stalk p) (c : {j : E.ι // p ∈ (E.component j).support} → Fin n)
    {r : ℕ} (σ : Fin (r + 1) → Fin n) (a : Fin (r + 1) → Fin n → ℕ) : Prop :=
  IsRegularSystemOfParameters z ∧ Function.Injective c ∧
    (∀ j, (E.component j.1).stalkIdeal p = Ideal.span {z (c j)}) ∧
    Function.Injective σ ∧ (∀ i j, σ i ≠ c j) ∧ (∀ i k, a i k ≠ 0 → k ∈ Set.range c) ∧
    Γ.stalkIdeal p = Ideal.span (Set.range (z ∘ σ))

/-- Chain coordinates realise `E` at `p` in the sense of Kollár Definition 24 (1)–(3). -/
theorem ChainCoords.toIsSncAt {E : DivisorFamily X} {Γ : X.IdealSheafData} {p : X} {n : ℕ}
    {z : Fin n → X.presheaf.stalk p} {c : {j : E.ι // p ∈ (E.component j).support} → Fin n}
    {r : ℕ} {σ : Fin (r + 1) → Fin n} {a : Fin (r + 1) → Fin n → ℕ}
    (h : ChainCoords E Γ p z c σ a) : E.IsSncAt p z :=
  ⟨h.1, c, h.2.1, h.2.2.1⟩

/-- **`I` is chain-relative monomial along `Γ` at `p`** (the local form of CP1 at the absorbing
stage, and the un-isolated ideal at every later stage) — in chain coordinates,
`I_p = M⁰ · chainIdeal (z ∘ σ) (M)` with `M⁰ = ∏_k z_k^{b_k}` the top-level monomial factor (the
exponents of `I` along the members through `p`; `1` when the top level of the run had no round of
order `≥ 2` near `Γ`) and `M_i = ∏_k z_k^{a i k}` the monomial factors of the levels (units
allowed). -/
def ChainRelativeAt (E : DivisorFamily X) (I Γ : X.IdealSheafData) (p : X) : Prop :=
  ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk p)
    (c : {j : E.ι // p ∈ (E.component j).support} → Fin n) (r : ℕ) (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) (b : Fin n → ℕ), ChainCoords E Γ p z c σ a ∧
      (∀ k, b k ≠ 0 → k ∈ Set.range c) ∧
      I.stalkIdeal p =
        Ideal.span {monomialOf z b} * chainIdeal (z ∘ σ) fun i => monomialOf z (a i)

/-- **`K` has the K-shape along `Γ` at `p`** (CP2; the invariant of CP5) — in chain coordinates,
`K_p = M⁰ · chainKIdeal (z ∘ σ) (M)`; `K_p = ⊤` when `M⁰` and every `M_i` are units. -/
def ChainRelativeKAt (E : DivisorFamily X) (K Γ : X.IdealSheafData) (p : X) : Prop :=
  ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk p)
    (c : {j : E.ι // p ∈ (E.component j).support} → Fin n) (r : ℕ) (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) (b : Fin n → ℕ), ChainCoords E Γ p z c σ a ∧
      (∀ k, b k ≠ 0 → k ∈ Set.range c) ∧
      K.stalkIdeal p =
        Ideal.span {monomialOf z b} * chainKIdeal (z ∘ σ) fun i => monomialOf z (a i)

/-- **`Z` is a chain-relative stratum along `Γ` at `p`** (the shape of the centres of the
continuation, CP3) — in chain coordinates, `Z_p` is generated by an initial segment `f₀, …, f_{l−1}`
of the chain equations together with some members' coordinates (the strata `H^{(l)} ∩ E^{j₁} ∩ …`;
`l = 0` allowed: a stratum of the boundary). -/
def IsChainStratumAt (E : DivisorFamily X) (Γ Z : X.IdealSheafData) (p : X) : Prop :=
  ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk p)
    (c : {j : E.ι // p ∈ (E.component j).support} → Fin n) (r : ℕ) (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ), ChainCoords E Γ p z c σ a ∧
      ∃ (l : ℕ) (s : Finset (Fin n)), ↑s ⊆ Set.range c ∧
        Z.stalkIdeal p =
          Ideal.span ((z ∘ σ) '' {i | i.val < l}) ⊔ Ideal.span (z '' ↑s)

/-! ### The protected state (the invariant of CP5) -/

variable {k : Type u} [Field k] [CharZero k]

/-- **The protected state** of the loop for an absorbed component `Γ` (the invariant of CP5, in the
template of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedSmoothWindow`) — `Γ` is smooth over `k` and
integral, has simple normal crossings with the boundary, meets no remaining component, and the
(isolated) ideal has the K-shape along `Γ` at every point of `Γ` (the `⊤` branch included). -/
structure ProtectedState (T : MarkedTriple k) (C : Finset T.X.left.IdealSheafData)
    (Γ : T.X.left.IdealSheafData) : Prop where
  smooth : Smooth (Γ.subschemeι ≫ (T.X.left ↘ Spec (CommRingCat.of k)))
  integral : IsIntegral Γ.subscheme
  snc : T.E.HasSncWith Γ
  disjoint : ∀ c ∈ C, Disjoint c.support Γ.support
  chain : ∀ p ∈ Γ.support, ChainRelativeKAt T.E T.I Γ p

open Classical in
/-- The strict transforms, at stage `n` of the run of `BMO_1` on `T` truncated at `n`, of ALL the
members of `C` (the round lemma's component set; `remainingComponents` is its restriction to the
members not absorbed at `n`). -/
noncomputable def transportedComponents (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData)
    (n : ℕ) : Finset (stageTriple T hm n).X.left.IdealSheafData :=
  C.image fun c => ((bmoOneRun T hm).take n).strictTransformSeq c (Fin.last _)

end Hironaka.Resolution
