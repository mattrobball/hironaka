/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The embedded desingularization functor in every dimension

The all-dimensions embedded desingularization functor `BEDanFamStarOfInput bmod hbmod`: the functors
`bedanFamOfInput bmod n` of `Hironaka/Resolution/Analytic/Wlo09/Basic.lean` in every dimension `n`,
together with the commutation with closed embeddings of the ambient manifold that clause (4) of
[Wlo09, Theorem 2.0.2] requires, which is proved from the corresponding commutation `hbmod` of the
modified marked resolution `bmod`.

* `AnalyticFamilyFunctor.CommutesWithLocalIsos.restrictDomain` and
  `AnalyticFamilyFunctor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam.restrictDomain`: the two
  functoriality predicates descend from a family functor `B` on a class `Dom` to any family
  functor `B₀` on a sub-class `Dom₀ ⊆ Dom` that agrees with `B` there; the triples and their class
  proofs are hypotheses of both predicates, so the descent is the transport of the agreements.
* `bedanFamOfInput_commutesWithClosedEmbeddings bmod hbmod n s`: the embedded desingularization
  in dimension `n` commutes with closed embeddings of empty divisor through the one in dimension
  `n − s`, the restriction of `hbmod n s` to the class `DomBEDan ⊆ BMOClass 1`
  (`DomBEDan.bmoClass_one`).
* `BEDanFamStarOfInput bmod hbmod : BEDanFamStar 𝕜`: the functors of every dimension with the
  closed-embedding field; `BEDanFamStarOfInput_fam`: the dimension-wise functors unfolded (`rfl`).

**Why the field holds.** Resolving `(M', I', ∅, 1)` for a closed embedding `M ↪ M'` of ambient
manifolds is equivalent to resolving `(M, I, ∅, 1)` [Wlo09, §7.1]: the coordinates `u₁, …, u_k` of
`M` in `M'` define tangent directions of `I'`, the algorithm passes to the hypersurface `V(u₁)` and
repeats `k` times (this is clause (3) of [Wlo09, Theorem 3.5.1] for the canonical resolution of
marked ideals). That commutation is a property of the modified marked resolution `bmod`, taken here
as the hypothesis `hbmod` (proved for the concrete resolution in
`Hironaka/Resolution/Analytic/Wlo09/Concrete.lean`). The embedded desingularization is the
restriction of that resolution to the class `DomBEDan`, so the commutation descends: the predicate's
triples and their class proofs are its own hypotheses, and `bedanFamOfInput bmod n` agrees with
`(bmod n).functor` on the class by definition.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

namespace AnalyticFamilyFunctor

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}
  {Dom Dom₀ : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
  {B : AnalyticFamilyFunctor ψ₀ Dom} {B₀ : AnalyticFamilyFunctor ψ₀ Dom₀}

/-- The predicate `CommutesWithLocalIsos` descends to a sub-class: if `B` commutes with local
analytic isomorphisms on `Dom` and `B₀` on `Dom₀ ⊆ Dom` agrees with `B` there, then `B₀` commutes
with local analytic isomorphisms. Not in the sources; bookkeeping. -/
theorem CommutesWithLocalIsos.restrictDomain
    (h : ∀ {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}, Dom₀ T → Dom T)
    (hB₀ : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₀ T),
      B₀.fam T hT = B.fam T (h hT))
    (hB : B.CommutesWithLocalIsos) : B₀.CommutesWithLocalIsos := by
  intro M N T T' g hg hpb hT hT' U' hU'
  rw [hB₀ T' hT', hB₀ T hT]
  exact hB T T' g hg hpb (h hT) (h hT') U' hU'

/-- The predicate `CommutesWithClosedEmbeddingsOfEmptyDivisorFam` descends to sub-classes: if `B`
commutes with closed embeddings of empty divisor through `B'` and `B₀`, `B₀'` agree with `B`, `B'`
on the sub-classes `Dom₀ ⊆ Dom`, `Dom₀' ⊆ Dom'`, then `B₀` commutes with closed embeddings of empty
divisor through `B₀'`. Not in the sources; bookkeeping. -/
theorem CommutesWithClosedEmbeddingsOfEmptyDivisorFam.restrictDomain {s : ℕ}
    {Dom' Dom₀' : ∀ {M' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)},
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) M' → Prop}
    {B' : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Dom'}
    {B₀' : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Dom₀'}
    (h : ∀ {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}, Dom₀ T → Dom T)
    (h' : ∀ {M' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
      {T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) M'},
      Dom₀' T' → Dom' T')
    (hB₀ : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₀ T),
      B₀.fam T hT = B.fam T (h hT))
    (hB₀' : ∀ {M' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
      (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) M') (hT' : Dom₀' T'),
      B₀'.fam T' hT' = B'.fam T' (h' hT'))
    (hB : B.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s) B') :
    B₀.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s) B₀' := by
  intro M S hS I hI J hJ hle hJI hT hT' U hU
  rw [hB₀ _ hT, hB₀' _ hT']
  exact hB hS I hI J hJ hle hJI (h hT) (h' hT') U hU

end AnalyticFamilyFunctor

variable (𝕜 : Type) [RCLike 𝕜]

/-- The embedded desingularization in dimension `n` commutes with closed embeddings of empty
divisor through the one in dimension `n − s` (the embeddings of ambient manifolds in clause (4) of
[Wlo09, Theorem 2.0.2]; [Wlo09, §7.1]): the restriction to the class `DomBEDan ⊆ BMOClass 1`
(`DomBEDan.bmoClass_one`) of the commutation `hbmod n s` of the modified marked resolution. The
larger functors `(bmod n).functor`, `(bmod (n - s)).functor` are passed by name, since the
predicate's hypothesis alone does not determine them for the unifier. -/
theorem bedanFamOfInput_commutesWithClosedEmbeddings (bmod : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n)
    (hbmod : ∀ (n s : ℕ),
      (bmod n).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s)
        (bmod (n - s)).functor) (n s : ℕ) :
    (bedanFamOfInput 𝕜 bmod n).CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s)
      (bedanFamOfInput 𝕜 bmod (n - s)) :=
  AnalyticFamilyFunctor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam.restrictDomain
    (B := (bmod n).functor) (B' := (bmod (n - s)).functor)
    (fun hT => DomBEDan.bmoClass_one 𝕜 hT) (fun hT' => DomBEDan.bmoClass_one 𝕜 hT')
    (fun _ _ => rfl) (fun _ _ => rfl) (hbmod n s)

/-- **The embedded desingularization functor in every dimension** ([Wlo09, Theorem 2.0.2], with the
commutation with embeddings of ambient manifolds of its clause (4), [Wlo09, §7.1] and
[Wlo09, Theorem 3.5.1 (3)]), from a modified marked resolution `bmod : ∀ n, BMOmodFam 𝕜 n` in every
dimension and its commutation `hbmod` with closed embeddings of empty divisor. The dimension-wise
functors are `bedanFamOfInput bmod n` by definition, and the closed-embedding field is
`bedanFamOfInput_commutesWithClosedEmbeddings`, the restriction of `hbmod n s` to the class
`DomBEDan ⊆ BMOClass 1`. -/
def BEDanFamStarOfInput (bmod : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n)
    (hbmod : ∀ (n s : ℕ),
      (bmod n).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s)
        (bmod (n - s)).functor) :
    BEDanFamStar.{u} 𝕜 where
  fam n := bedanFamOfInput 𝕜 bmod n
  closedEmbedding n s := bedanFamOfInput_commutesWithClosedEmbeddings 𝕜 bmod hbmod n s

/-- The dimension-wise functors of `BEDanFamStarOfInput`, unfolded (`rfl`). -/
theorem BEDanFamStarOfInput_fam (bmod : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n)
    (hbmod : ∀ (n s : ℕ),
      (bmod n).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s)
        (bmod (n - s)).functor)
    (n : ℕ) :
    (BEDanFamStarOfInput 𝕜 bmod hbmod).fam n = bedanFamOfInput 𝕜 bmod n :=
  rfl

end Hironaka.Manifold

end
