/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedAdmissibleStratum
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimAt
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Algebra
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The predicates of CP3: the classification of the centres, universal over the coordinates

The statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) classifies the centres of a run of
`BMO_1` on a protected state. This module states it in a form universal over the chain-coordinate
systems: chain coordinates without the tracked subvariety (`ChainCoordsFree`); the classification of
one centre at one of its points — in EVERY chain-coordinate system at the point in which the current
ideal has the K-shape the centre is an admissible stratum, and in every system in which it has the
un-isolated form it is an admissible stratum, a terminal-normal stratum, or the absorption `(f)`
(`CenterClassifiedAt`); its form along a run (`CP3For`) and along the tower of order reductions
(`CP3BOAt`, `CP3BMOAt`, `CP3BOFor`); and the bridges to the existential predicates of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedAdmissibleStratum` (`AdmissibleChainStratumKAt`,
`AdmissibleChainStratumAt`, `TerminalNormalStratumAt`), which are the universal ones instantiated at
the coordinates that the persistence of the chain form provides. The coordinates are those of
[Kol07, Definition 24]. The predicates are proved along the tower in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step1` to
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Tower` and consumed by CP5
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka IsLocalRing BlowUpSequence
  Scheme.IdealSheafData Hironaka.BO

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- Chain coordinates at `p` for the family `E` WITHOUT the tracked subvariety (the coordinates of
[Kol07, Definition 24] at `p`) — `ChainCoords` minus its last clause: a regular system of
parameters `z`, the members through `p` given by `z (c j)`, the chain coordinates `z ∘ σ` off the
members, the exponents supported on the members' coordinates. -/
def ChainCoordsFree (E : DivisorFamily X) (p : X) {n : ℕ} (z : Fin n → X.presheaf.stalk p)
    (c : {j : E.ι // p ∈ (E.component j).support} → Fin n) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (a : Fin (r + 1) → Fin n → ℕ) : Prop :=
  IsRegularSystemOfParameters z ∧ Function.Injective c ∧
    (∀ j, (E.component j.1).stalkIdeal p = Ideal.span {z (c j)}) ∧
    Function.Injective σ ∧ (∀ i j, σ i ≠ c j) ∧ (∀ i k, a i k ≠ 0 → k ∈ Set.range c)

/-- `ChainCoords` is `ChainCoordsFree` together with the tracked subvariety's stalk being the
chain's span. -/
theorem chainCoords_iff_free {E : DivisorFamily X} {Γ : X.IdealSheafData} {p : X} {n : ℕ}
    {z : Fin n → X.presheaf.stalk p} {c : {j : E.ι // p ∈ (E.component j).support} → Fin n}
    {r : ℕ} {σ : Fin (r + 1) → Fin n} {a : Fin (r + 1) → Fin n → ℕ} :
    ChainCoords E Γ p z c σ a ↔
      ChainCoordsFree E p z c σ a ∧ Γ.stalkIdeal p = Ideal.span (Set.range (z ∘ σ)) :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩,
    fun ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ => ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩

/-- Admissibility in given K-shape coordinates gives the existential predicate
`AdmissibleChainStratumKAt`. -/
theorem admissibleChainStratumKAt_of_stratumIn {E : DivisorFamily X} {K Γ Z : X.IdealSheafData}
    {p : X} {n : ℕ} {z : Fin n → X.presheaf.stalk p}
    {c : {j : E.ι // p ∈ (E.component j).support} → Fin n} {r : ℕ} {σ : Fin (r + 1) → Fin n}
    {a : Fin (r + 1) → Fin n → ℕ} {b : Fin n → ℕ} (hc : ChainCoords E Γ p z c σ a)
    (hb : ∀ k, b k ≠ 0 → k ∈ Set.range c)
    (hK : K.stalkIdeal p =
      Ideal.span {monomialOf z b} * chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i)))
    (h : StratumIn z (Set.range c) σ a b (Z.stalkIdeal p)) :
    AdmissibleChainStratumKAt E K Γ Z p := by
  obtain ⟨l, hl, s, hsC, hZ, h0, hpos⟩ := h
  exact ⟨n, z, c, r, σ, a, b, l, hl, s, hc, hb, hK, hsC, hZ, h0, hpos⟩

/-- The same for the un-isolated form. -/
theorem admissibleChainStratumAt_of_stratumIn {E : DivisorFamily X} {I Γ Z : X.IdealSheafData}
    {p : X} {n : ℕ} {z : Fin n → X.presheaf.stalk p}
    {c : {j : E.ι // p ∈ (E.component j).support} → Fin n} {r : ℕ} {σ : Fin (r + 1) → Fin n}
    {a : Fin (r + 1) → Fin n → ℕ} {b : Fin n → ℕ} (hc : ChainCoords E Γ p z c σ a)
    (hb : ∀ k, b k ≠ 0 → k ∈ Set.range c)
    (hI : I.stalkIdeal p =
      Ideal.span {monomialOf z b} * chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)))
    (h : StratumIn z (Set.range c) σ a b (Z.stalkIdeal p)) :
    AdmissibleChainStratumAt E I Γ Z p := by
  obtain ⟨l, hl, s, hsC, hZ, h0, hpos⟩ := h
  exact ⟨n, z, c, r, σ, a, b, l, hl, s, hc, hb, hI, hsC, hZ, h0, hpos⟩

/-- A terminal-normal stratum in given coordinates gives `TerminalNormalStratumAt`. -/
theorem terminalNormalStratumAt_of_terminalIn {E : DivisorFamily X} {I Γ Z : X.IdealSheafData}
    {p : X} {n : ℕ} {z : Fin n → X.presheaf.stalk p}
    {c : {j : E.ι // p ∈ (E.component j).support} → Fin n} {r : ℕ} {σ : Fin (r + 1) → Fin n}
    {a : Fin (r + 1) → Fin n → ℕ} {b : Fin n → ℕ} (hc : ChainCoords E Γ p z c σ a)
    (hb : ∀ k, b k ≠ 0 → k ∈ Set.range c)
    (hI : I.stalkIdeal p =
      Ideal.span {monomialOf z b} * chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)))
    (h : TerminalIn z (Set.range c) σ (Z.stalkIdeal p)) :
    TerminalNormalStratumAt E I Γ Z p := by
  obtain ⟨s, hsC, hne, hZ⟩ := h
  exact ⟨n, z, c, r, σ, a, b, s, hc, hb, hI, hsC, hne, hZ⟩

/-- **CP3's classification at a point**, universal over the coordinates: for the current ideal `K`,
the boundary `E` and a centre `Z` at a point `q ∈ Z`, in EVERY chain-coordinate system at `q` in
which `K_q` has the K-shape, `Z_q` is an admissible stratum in those coordinates; in every system
in which it has the un-isolated form, `Z_q` is an admissible stratum, a terminal-normal stratum,
or the absorption `(f)`. -/
def CenterClassifiedAt (E : DivisorFamily X) (K Z : X.IdealSheafData) (q : X) : Prop :=
  ∀ {n : ℕ} (z : Fin n → X.presheaf.stalk q) (c : {j : E.ι // q ∈ (E.component j).support} → Fin n)
    {r : ℕ} (σ : Fin (r + 1) → Fin n) (a : Fin (r + 1) → Fin n → ℕ) (b : Fin n → ℕ),
    ChainCoordsFree E q z c σ a → (∀ κ, b κ ≠ 0 → κ ∈ Set.range c) →
    (K.stalkIdeal q =
        Ideal.span {monomialOf z b} * chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i)) →
      StratumIn z (Set.range c) σ a b (Z.stalkIdeal q)) ∧
    (K.stalkIdeal q =
        Ideal.span {monomialOf z b} * chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) →
      StratumIn z (Set.range c) σ a b (Z.stalkIdeal q) ∨
        TerminalIn z (Set.range c) σ (Z.stalkIdeal q) ∨
        Z.stalkIdeal q = Ideal.span (Set.range (z ∘ σ)))

/-- CP3 along a run: every centre of `S` (for the input `(I, E)` at mark `1`) is classified at each
of its points, for the mark-`1` transforms and the total transform of the boundary at its
stage. -/
def CP3For (S : BlowUpSequence X) (I : X.IdealSheafData) (E : DivisorFamily X) : Prop :=
  ∀ (i : Fin S.length) (q : S.stage i.castSucc), q ∈ (S.center i).support →
    CenterClassifiedAt (S.totalTransformSeq E i.castSucc) (S.markedTransformSeq I 1 i.castSucc)
      (S.center i) q

variable {k : Type u} [Field k] [CharZero k]

variable (k) in
/-- CP3 along the stage-`n` order reduction `BO_{n,1}` of the tower ([Kol07, 70]) on every triple
of its class. -/
def CP3BOAt (n : ℕ) : Prop :=
  ∀ (T : Triple k) (hT : T.BOClass n 1), CP3For (boRun k n T hT) T.I T.E

variable (k) in
/-- CP3 along the stage-`n` marked order reduction `BMO_{n,1}` on every marked triple of its
class. -/
def CP3BMOAt (n : ℕ) : Prop :=
  ∀ (T : MarkedTriple k) (hT : T.BMOClass n 1), CP3For (bmoRun k n T hT) T.I T.E

variable (k) in
/-- CP3 along the value of the order-`1` reduction `bo 1` on every triple of class `BOClass n 1`
(the hypothesis for the reduction through Step 1). -/
def CP3BOFor {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d) : Prop :=
  ∀ (T : Triple k) (hT : T.BOClass n 1), CP3For (((bo 1).functor k).seq T hT) T.I T.E

end Hironaka.Resolution
