/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmpty
public import Hironaka.Manifold.FiniteSuccession.Functor.Pushforward
public import Hironaka.Manifold.Snc.Basic
public import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Blow-up sequence functors on analytic triples and their functoriality clauses

A blow-up sequence functor is a functor `B` whose inputs are triples `(X, I, E)` and whose
outputs are blow-up sequences with specified centres; the length of the sequence `r`, the schemes
`X_i` and the centres `Z_i` all depend on `(X, I, E)` [Kol07, Definition 31]. The functors on
analytic manifolds are valued in lists of centres `CenterList ψ₀ M`, their `toSuccession` being what
the main theorems use; "commutes with `h`" as in [Kol07, 34.1], with the class of `h` restricted
to surjective local analytic isomorphisms (first bullet) and open embeddings (second bullet:
delete empty blow-ups and reindex); the clause 34.2 (change of fields) has no counterpart on
manifolds; 34.3 and 34.4 are kept in the form used by [Kol07, Theorem 103, (3)]. The corresponding
definitions for schemes are `AlgebraicGeometry.BlowUpSequenceAssignment` and its clauses; every
definition below is its analogue on manifolds.

* `AnalyticBlowUpSequenceFunctor ψ₀ Dom`: `seq T h : CenterList ψ₀ M` for every triple of the
  class `Dom`, whose outputs contain no empty blow-ups ([Kol07, 32], the field `noEmptyCenters`).
  One functor per model `(E, ψ₀)`, as one functor per field for schemes: Kollár's named functors
  are indexed by the dimension (`BO_{n,m}`, `BD_{n,m,0}`).
* `CommutesWith B T T' h hh` ([Kol07, 34.1]): `B(N, h^* 𝓘, h⁻¹(E)) = h^* B(M, 𝓘, E)`, an equality
  of lists, `h^*` the canonical pull-back `BlowUpSequence.pullback` along the local analytic
  isomorphism `h`; `CommutesWithSurjectiveLocalIsos B` (first bullet);
  `CommutesWithOpenEmbeddings B` (second bullet: the value on the open piece is the pull-back with
  its empty blow-ups deleted, `BlowUpSequence.eraseEmpty`); `CommutesWithLocalIsos B` = both.
* `CommutesWithSurjectionsIn B 𝓜` ([Kol07, Theorem 105, (3)]): `B` commutes with every surjective
  member of the class `𝓜` of analytic maps.
* `CommutesWithClosedEmbeddingsOfEmptyDivisor B' B` ([Kol07, 34.3] in the form of
  [Kol07, Theorem 103, (3)]): for a closed submanifold `τ : S ↪ M` of codimension `s` and ideal
  sheaves `𝓘` on `M`, `J` on `S` with `𝒪_M/𝓘 = τ_*(𝒪_S/J)` (`𝓘 ⊇ I_S` and `J = τ^* 𝓘`),
  `B(M, 𝓘, ∅) = τ_* B'(S, J, ∅)`, with `B'` a functor at the model `𝕜^{n−s}` of the
  submanifolds (the `BMO_{n−1,1}(Y, J, 1, ∅)` of Theorem 103 (3), the mark `1` absorbed into
  `B'`) and `τ_*` the push-forward of lists `BlowUpSequence.pushforward`.
* The vocabulary of [Kol07, Theorem 105]: `GlobalizationData GT LT` (clause (2): (i) every point
  of a global triple lies in the range of an open embedding from a local triple carrying the
  pullback data, (ii) `LT` closed under countable disjoint unions); `IsLocalCover GT LT T T' g`
  (the proof's `g : X' → X`: a surjective coproduct of open embeddings from a local triple
  carrying the pullback data of a global one); `IsFibreProduct g₁ g₂ p₁ p₂` (the proof's
  `X'' := X' ×_X X'` with its projections `τ₁, τ₂`: local analytic isomorphisms `p₁, p₂` with
  `g₁ ∘ p₁ = g₂ ∘ p₂`, jointly a bijection onto the set-theoretic fibre product);
  `LocalCoversFibreClosed GT LT` (a hypothesis the proof of Theorem 105 uses tacitly: a fibre
  product of two local covers carrying the pullback data is in `LT`).

The globalization is carried out, in the compatible-family form, in
`Hironaka.Resolution.Analytic.OrderReduction.GlobalizeFam`.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-- A **blow-up sequence
functor** on the class `Dom` of analytic triples at the model `(E, ψ₀)` — the list of centres
`B(M, 𝓘, E) : CenterList ψ₀ M` assigned to every triple of the class, "with specified centers" (the
list carries them; the length of the sequence, the stages and the centres all depend on the
triple), whose outputs contain no empty blow-ups ([Kol07, 32]). The functoriality clauses of [Kol07,
34] are separate predicates. -/
structure AnalyticBlowUpSequenceAssignment (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜))
    (Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop) where
  /-- The list of centres `B(M, 𝓘, E)` assigned to a triple of the class. -/
  seq : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M),
      Dom T → AnalyticManifold.BlowUpSequence ψ₀ M
  /-- [Kol07, 32]: the output contains no empty blow-ups. -/
  noEmptyCenters : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (h : Dom T),
    (seq T h).NoEmptyCenters

namespace AnalyticBlowUpSequenceAssignment

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}
  {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
  (B : AnalyticBlowUpSequenceAssignment ψ₀ Dom)

/-- `B` **commutes with `h`** when `B(Y, h^* I, h⁻¹(E)) = h^* B(X, I, E)` [Kol07, 34.1]: for
triples `T` on `M`, `T'` on `N` of the class and a local analytic isomorphism `h : N → M`, the
value on `T'` is the pull-back ([Kol07, Definition 30, 30.1], `BlowUpSequence.pullback`) of the
value on `T`; an equality of lists of centres. Used with `T'.IsPullbackOf T h`. -/
def CommutesWith {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (T' : AnalyticTriple ψ₀ N) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) : Prop :=
  ∀ (hT : Dom T) (hT' : Dom T'), B.seq T' hT' = (B.seq T hT).pullback h hh

/-- [Kol07, 34.1], first bullet, with this class: `B` **commutes with
surjective local analytic isomorphisms** — with every surjective local analytic isomorphism
`h : N → M` between triples of which `T'` carries the pullback data of `T`. -/
def CommutesWithSurjectiveLocalIsos : Prop :=
  ∀ {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (T' : AnalyticTriple ψ₀ N)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    Function.Surjective h → T'.IsPullbackOf T h → B.CommutesWith T T' h hh

/-- [Kol07, 34.1], second bullet, with this class: `B` **commutes with open
embeddings** — for every analytic open embedding `h : N → M` with `T'` carrying the pullback data
of `T`, the value on `T'` is the pull-back `h^* B(X, I, E)` with every blow-up whose centre is
empty deleted and the sequence reindexed (`BlowUpSequence.eraseEmpty`). -/
def CommutesWithOpenEmbeddings : Prop :=
  ∀ {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (T' : AnalyticTriple ψ₀ N)
    (h : AnalyticMap N M) (hh : IsAnalyticOpenEmbedding h), T'.IsPullbackOf T h →
    ∀ (hT : Dom T) (hT' : Dom T'), B.seq T' hT' = ((B.seq T hT).pullback h hh.1).eraseEmpty

/-- [Kol07, 34.1], both bullets with these classes ("smooth morphism" →
"local analytic isomorphism"): `B` **commutes with local analytic isomorphisms** — with the
surjective ones, and with open embeddings up to the deletion of empty blow-ups. -/
def CommutesWithLocalIsos : Prop :=
  B.CommutesWithSurjectiveLocalIsos ∧ B.CommutesWithOpenEmbeddings

/-- `B` **commutes with surjections in `𝓜`** [Kol07, Theorem 105, (3)]: `B.CommutesWith` for every
surjective local analytic isomorphism `h` of the class `𝓜` between triples of which the source
carries the pullback data of the target. -/
def CommutesWithSurjectionsIn
    (𝓜 : ∀ {M N : AnalyticManifold.{u} 𝕜 E}, AnalyticMap N M → Prop) : Prop :=
  ∀ {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (T' : AnalyticTriple ψ₀ N)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h), 𝓜 h →
    Function.Surjective h → T'.IsPullbackOf T h → B.CommutesWith T T' h hh

/-- [Kol07, 34.3] in the form used by Theorem 103 (3) ("`BO_{n,1}(X, I, ∅) = τ_* BMO_{n−1,1}(Y, J,
1, ∅)`"): the functor `B` at the model `(E, ψ₀)`
**commutes with closed embeddings whenever `E = ∅`, through the functor `B'`** at the model
`𝕜^{n−s}` of the closed submanifolds of codimension `s` — for every closed submanifold
`τ : S ↪ M` of codimension `s` and ideal sheaves `𝓘` on `M`, `J` on the bundled `S` with nonzero
stalks and `O_M/𝓘 = τ_*(O_S/J)` (`𝓘` contains the ideal sheaf of `S` and `J = τ^* 𝓘`),
`B(M, 𝓘, ∅) = τ_* B'(S, J, ∅)` with `τ_*` the push-forward of lists (`BlowUpSequence.pushforward`).
Theorem 103 (3)'s mark `1` on `J` is absorbed into `B'`. -/
def CommutesWithClosedEmbeddingsOfEmptyDivisor {s : ℕ}
    {Dom' : ∀ {M' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)},
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) M' → Prop}
    (B' : AnalyticBlowUpSequenceAssignment (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Dom') :
    Prop :=
  ∀ {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} (hS : IsClosedSubmanifold ψ₀ S s)
    (I : AnalyticManifold.IdealSheaf M) (hI : I.IsNonzeroEverywhere)
    (J : AnalyticManifold.IdealSheaf hS.toAnalyticManifold) (hJ : J.IsNonzeroEverywhere),
    hS.idealSheaf ≤ I → J = I.pullback hS.inclusionMap hS.inclusionMap.contMDiff →
    ∀ (hT : Dom ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩)
      (hT' : Dom' ⟨J, hJ, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩),
      B.seq _ hT = (B'.seq _ hT').pushforward hS

end AnalyticBlowUpSequenceAssignment

/-! ### The vocabulary of [Kol07, Theorem 105] on manifolds -/

/-- The fibre product `X'' := X' ×_X X'` with its two projections in the proof of
[Kol07, Theorem 105], and `X'' := ∐_{i≤j} Uᵢ ∩ Uⱼ` in the proof of [Kol07, Proposition 37]:
`(P, p₁, p₂)` is a **fibre product** of `g₁ : N₁ → M` and `g₂ : N₂ → M` — `p₁, p₂` local analytic
isomorphisms with `g₁ ∘ p₁ = g₂ ∘ p₂`, jointly a bijection onto the set-theoretic fibre product
`{(x, y) | g₁ x = g₂ y}`. -/
def IsFibreProduct {M N₁ N₂ P : AnalyticManifold.{u} 𝕜 E} (g₁ : AnalyticMap N₁ M)
    (g₂ : AnalyticMap N₂ M) (p₁ : AnalyticMap P N₁) (p₂ : AnalyticMap P N₂) : Prop :=
  IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω p₁ ∧ IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω p₂ ∧
    (∀ z, g₁ (p₁ z) = g₂ (p₂ z)) ∧ ∀ x y, g₁ x = g₂ y → ∃! z, p₁ z = x ∧ p₂ z = y

namespace AnalyticTriple

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- Clause (2) of [Kol07, Theorem 105] asks for two classes of triples, `GT` (global) and `LT`
(local), such that (i) every point of a triple of `GT` lies in the image of an `𝓜`-morphism
`gₓ : Uₓ → X` whose pulled-back triple `(Uₓ, g^* I, g⁻¹ E)` is in `LT`, and (ii) `LT` is closed
under disjoint unions. Here, with `𝓜` the open embeddings: (i) every point of a global
triple lies in the range of an analytic open embedding from a local triple carrying the pullback
data; (ii) `LT` is closed under countable disjoint unions (Warning 38). No inclusion `LT ⊆ GT` is
assumed; Theorem 105's "extension" is agreement on `LT ∩ GT`. -/
structure GlobalizationData (GT LT : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop) :
    Prop where
  /-- Clause (2)(i) of [Kol07, Theorem 105]: every point of a global triple has a local triple over
  it along an open embedding. -/
  exists_isPullbackOf : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M), GT T →
    ∀ x : M, ∃ (N : AnalyticManifold.{u} 𝕜 E) (T' : AnalyticTriple ψ₀ N) (g : AnalyticMap N M),
      IsAnalyticOpenEmbedding g ∧ x ∈ range g ∧ T'.IsPullbackOf T g ∧ LT T'
  /-- Clause (2)(ii) of [Kol07, Theorem 105]: `LT` is closed under countable disjoint unions. -/
  closedUnderSigma : ClosedUnderSigma LT

/-- The proof of [Kol07, Theorem 105] chooses `𝓜`-morphisms `gₓᵢ : Uₓᵢ → X` whose images cover
`X`, forms the disjoint union `X' := ∐ᵢ Uₓᵢ` with the induced `g : X' → X`, and uses that
`(X', g^* I, g⁻¹ E) ∈ LT`: `g : N → M` is a **local cover** of the
global triple `T` by the local triple `T'` — `T ∈ GT`, `T' ∈ LT`, `g` a surjective coproduct of
open embeddings, and `T'` carries the pullback data of `T` along `g`. -/
def IsLocalCover (GT LT : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop)
    {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (T' : AnalyticTriple ψ₀ N)
    (g : AnalyticMap N M) : Prop :=
  GT T ∧ LT T' ∧ IsCoprodOfOpenEmbeddings g ∧ Function.Surjective g ∧ T'.IsPullbackOf T g

/-- A hypothesis the proof of Theorem 105 uses tacitly: Kollár applies `B` to `X'' := X' ×_X X'`,
which requires `X''` with the pullback data to be a local triple although (1)–(3) state no such
clause. The class `LT` is
**closed under fibre products of local covers**: for two local covers `g₁ : N₁ → M`, `g₂ : N₂ → M`
of a global triple, a triple on a fibre product `(P, p₁, p₂)` of `g₁` and `g₂` carrying the
pullback data of `T₁` along `p₁` is in `LT`. -/
def LocalCoversFibreClosed
    (GT LT : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop) : Prop :=
  ∀ {M N₁ N₂ P : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M} {T₁ : AnalyticTriple ψ₀ N₁}
    {T₂ : AnalyticTriple ψ₀ N₂} {g₁ : AnalyticMap N₁ M} {g₂ : AnalyticMap N₂ M},
    IsLocalCover GT LT T T₁ g₁ → IsLocalCover GT LT T T₂ g₂ →
    ∀ {p₁ : AnalyticMap P N₁} {p₂ : AnalyticMap P N₂} (T₁₂ : AnalyticTriple ψ₀ P),
      IsFibreProduct g₁ g₂ p₁ p₂ → T₁₂.IsPullbackOf T₁ p₁ → LT T₁₂

end AnalyticTriple

end Manifold

end
