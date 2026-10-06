/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Basic
public import Hironaka.Manifold.FiniteSuccession.Functor.Pullback
public import Hironaka.Manifold.IdealSheaf.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Order reduction on analytic manifolds: the classes and the first centre

Kollár's order reduction for ideals, Theorem 103, and its ingredient Lemma 102 are stated for
triples `(X, I, E)` with `dim X = n` and `max-ord I ≤ m` ([Kol07, Lemma 102], [Kol07, Theorem 103]).
This module fixes the analytic form of their hypotheses on an analytic triple `T = (M, 𝓘, E)`
(a manifold `M` modelled on `E ≃ 𝕜ⁿ`, an ideal sheaf `𝓘` nonzero at every point, a boundary `E`
with simple normal crossings and ordered index set) and defines the first centre of Lemma 102.

* `AnalyticTriple.BOClass m` — the class on which the order-reduction functors `BO_{n,m}` are
  defined: `1 ≤ m`, the order of `𝓘` is at most `m` at every point (the pointwise form of
  `max-ord I ≤ m`), and only finitely many members of the boundary are nonempty (Kollár's finite
  index set `E = ∑_{i=1}^s E^i`; on a manifold this replaces quasi-compactness, and it is
  restored on every relatively compact open subset in `Finiteness.lean`). The dimension is that of
  the model space and needs no clause.
* `AnalyticTriple.HasMaximalContact m` — the hypothesis of Step 2 of the proof of Theorem 103,
  "there is a smooth hypersurface of maximal contact `H ⊂ X`", in the static form of
  [Kol07, Theorem 80]: a closed hypersurface whose ideal sheaf lies in the maximal contact ideal
  `MC(𝓘) = D^{m-1} 𝓘` of [Kol07, Definition 79].
* `AnalyticTriple.ClosedUnderLocalIsoPullbackOverCosupp Dom m` — a class `Dom` of triples is
  closed under pull-back along local analytic isomorphisms whose image contains `cosupp(𝓘, m)`;
  this is the hypothesis on the class in Step 2.3 of [Kol07, 104], the independence of the
  hypersurface of maximal contact.
* `AnalyticTriple.LocalMCClass m` — the class on which Step 2 of the proof of Theorem 103 defines
  the functor: the triples of `BOClass m` with a global hypersurface of maximal contact (the pieces
  `X^{(j)}` of Step 3).
* `BD.Zminus1 𝓘 m Y` — the first centre `Z_{-1}` of the proof of [Kol07, Lemma 102]: the union of
  the irreducible components of the hypersurface `Y = E^j` contained in `cosupp(𝓘, m)`; on a
  manifold the irreducible components of a smooth hypersurface are its connected components.
* `AnalyticBlowUpSequenceAssignment.IndifferentToEmptyMembers` — deleting empty members from the
  boundary does not change the value of the functor; not in the sources, the counterpart for the
  members of the boundary of Kollár's empty blow-up convention [Kol07, 32], which concerns centres.

These definitions are the vocabulary of the whole of `OrderReduction/`: Lemma 102's functor
(`BD*.lean`), Steps 2.1–2.2 of the proof of Theorem 103 (`Step21*.lean`, `Step22*.lean`), its
globalization (`Globalize*.lean`) and the assembled structure `BOanFam`.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace AnalyticTriple

/-- The class of the order-reduction functors `BO_{n,m}` ([Kol07, Lemma 102] and
[Kol07, Theorem 103]: triples `(X, I, E)` with `dim X = n` and `max-ord I ≤ m`): `1 ≤ m`, the order
of `𝓘` is at most `m` at every point, and only finitely many members of the boundary are nonempty
(Kollár's finite index set; the substitute for quasi-compactness on a manifold). The dimension is
that of the model space, so no dimension clause is stated. -/
def BOClass (m : ℕ) : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop :=
  fun T => 1 ≤ m ∧ (∀ x, T.I.ord x ≤ (m : ℕ∞)) ∧ Finite {j // T.F.hyp j ≠ ∅}

/-- The hypothesis of Step 2 of the proof of [Kol07, Theorem 103], "there is a smooth hypersurface
of maximal contact `H ⊂ X`", in the static form of [Kol07, Theorem 80]: a closed hypersurface of
`M` whose ideal sheaf lies in `MC(𝓘) = D^{m-1} 𝓘` ([Kol07, Definition 79]). -/
def HasMaximalContact (m : ℕ) : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop :=
  fun {M} T =>
    haveI := finiteDimensional_of_chartIso ψ₀
    ∃ (H : Set M) (hH : IsClosedSubmanifold ψ₀ H 1), hH.idealSheaf ≤ T.I.iteratedDeriv (m - 1)

/-- The class on which Step 2 of the proof of [Kol07, Theorem 103] defines the order-reduction
functor (the "maximal contact case"; the pieces `X^{(j)}` of Step 3): the triples of `BOClass m`
with a global hypersurface of maximal contact. -/
def LocalMCClass (m : ℕ) : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop :=
  fun T => BOClass m T ∧ HasMaximalContact m T

/-- The class `Dom` is closed under pull-back along local analytic isomorphisms covering the
cosupport `cosupp(𝓘, m) = {ord 𝓘 ≥ m}`: a triple carrying the pull-back data of a member of the
class along a local analytic isomorphism whose image contains `cosupp(𝓘, m)` is a member. This is
the hypothesis on the class in Step 2.3 of [Kol07, 104], where the functor is evaluated on
pull-backs covering the cosupport. -/
def ClosedUnderLocalIsoPullbackOverCosupp
    (Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop) (m : ℕ) : Prop :=
  ∀ {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (T' : AnalyticTriple ψ₀ N)
    (g : AnalyticMap N M), IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g →
    {x | (m : ℕ∞) ≤ T.I.ord x} ⊆ Set.range g → T'.IsPullbackOf T g → Dom T → Dom T'

end AnalyticTriple

end Manifold

namespace Hironaka.Manifold.BD

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The first centre of the proof of [Kol07, Lemma 102], "let `Z_{-1}` be the union of those
irreducible components `E^{jk} ⊂ E^j` that are contained in `cosupp(I, m)`", with the irreducible
components of the smooth hypersurface `Y = E^j` read as its connected components: the points of
`Y` whose connected component in `Y` lies in `{ord 𝓘 ≥ m}`. -/
def Zminus1 {M : AnalyticManifold.{u} 𝕜 E} (I : AnalyticManifold.IdealSheaf M) (m : ℕ)
    (Y : Set M) :
    Set M :=
  {x | x ∈ Y ∧ connectedComponentIn Y x ⊆ {y | (m : ℕ∞) ≤ I.ord y}}

end Hironaka.Manifold.BD

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace AnalyticBlowUpSequenceAssignment

variable {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}

/-- A blow-up sequence functor on a class of analytic triples is **indifferent to empty boundary
members** when deleting empty members does not change its value: for every triple `T`, every
boundary `F'` on `M` with simple normal crossings embedding order-preservingly into `T.F` along
`e`, with the members matched along `e` and the empty hypersurface at every index outside the range
of `e`, the values at `T` and at `T` with boundary `F'` agree. Not in the sources: the counterpart,
for the members of the boundary, of Kollár's convention that empty blow-ups are ignored
([Kol07, 32]; [Kol07, 34.1]). Only the deletion of empty members is covered; no invariance under
permutations of the index set is asserted. -/
def IndifferentToEmptyMembers (B : AnalyticBlowUpSequenceAssignment ψ₀ Dom) : Prop :=
  ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (F' : HypersurfaceFamily M)
    (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι),
    (∀ i, T.F.hyp (e i) = F'.hyp i) → (∀ b, b ∉ Set.range e → T.F.hyp b = ∅) →
    ∀ (hT : Dom T) (hT' : Dom (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M)),
      B.seq T hT = B.seq ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ hT'

end AnalyticBlowUpSequenceAssignment

end Manifold

end
