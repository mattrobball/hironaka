/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.Family
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lemma 102's functor as compatible families

The order-reduction functors of this library, in the form suited to non-compact analytic
manifolds, take their values in compatible families ([Wlo09, Theorem 2.0.3 (1), (4)]; also the
remark after [BM97, Theorem 1.6] on locally finite sequences of blowings-up): a finite blow-up
sequence on every relatively compact open subset, the sequence on a smaller open being the
restriction of the sequence on a larger one once empty blow-ups are deleted (`CompatibleFamily`,
`Functor/Family.lean`). The assembly of Theorem 103 in this form (Steps 2.1 and 2.2 of the proof
and the local functor: `step21Fam`, `step22TripleFam`, `step2SeqFam`, `localFunctorFam` in
`Step21Fam.lean`, `Step22Fam.lean`, `LocalFunctorFam.lean`) is stated over abstract data for
Lemma 102 at every mark:

* `BDanFamData ψ₀ s` — the data of Lemma 102's functor `BD_{n,s,j}` ([Kol07, Lemma 102]) as
  compatible families: on every triple `T` of the class of `BO_{n,s}` and every member `j` of its
  boundary a `CompatibleFamily T`, with the clauses of Lemma 102 read on every relatively compact
  open `U` for the restricted triple `T.pullback (M.inclusion U) _`: the order clause
  ([Kol07, Definition 66]) and Lemma 102 (1) on the restricted triple; Lemma 102 (2), the
  commutation with local analytic isomorphisms in the one-clause form of `AnalyticFamilyFunctor`
  (both bullets of [Kol07, 34.1] at once: the value on a relatively compact open of the source is
  the pull-back of the value on its image, with empty blow-ups deleted); and the indifference to
  empty boundary members per open. The absence of empty centres is a field of the family itself.

The concrete instance, Lemma 102's family built from the marked families one dimension down, is
`bdanFamDataOfInput` in `BOanFamOfInput.lean`; `HFamData.lean` extracts from `BDanFamData` the
four clauses Step 2.2 uses.
-/

@[expose] public section

universe u

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-- The data of Lemma 102's functor `BD_{n,s,j}` ([Kol07, Lemma 102]) as compatible families: on
every triple `T` of the class of `BO_{n,s}` and every member `j` of the boundary, a
`CompatibleFamily T` whose values on the relatively compact opens `U` satisfy, for the restricted
triple, the order clause ([Kol07, Definition 66]) and Lemma 102 (1), which commute with local
analytic isomorphisms (Lemma 102 (2), both bullets of [Kol07, 34.1] in one clause per open) and
are indifferent to empty boundary members. The absence of empty centres is a field of the
family. -/
structure BDanFamData (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) (s : ℕ) where
  /-- The value `BD_{n,s,j}(M, 𝓘, E)` as a compatible family. -/
  fam : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M), AnalyticTriple.BOClass s T →
    T.F.ι → CompatibleFamily T
  /-- [Kol07, Definition 66] per open: the value on `U` is a smooth blow-up sequence of order `s`
starting with the restricted triple `(U, 𝓘|_U, E|_U)`. -/
  isOfOrder : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass s T) (j : T.F.ι) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))),
    ((fam T hT j).seqOn U hU).toSuccession.IsOfOrder
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf s
  /-- [Kol07, Lemma 102 (1)] per open: at the last stage, `cosupp(I_r, s)` is disjoint from the
strict transform of the member `E^j`, over `U`. -/
  cosupp_disjoint : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass s T) (j : T.F.ι) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))),
    Disjoint {x | (s : ℕ∞) ≤ (((fam T hT j).seqOn U hU).toSuccession.weakTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I (Fin.last _)).ord x}
      (((fam T hT j).seqOn U hU).toSuccession.strictTransformSeq
        ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.hyp j) (Fin.last _))
  /-- [Kol07, Lemma 102 (2)], both bullets of [Kol07, 34.1] in one clause per open (the form of
`AnalyticFamilyFunctor.CommutesWithLocalIsos`, with the member index kept): along a local analytic
isomorphism `g : N → M`, the value of the pulled-back triple on a relatively compact `U'` is the
pull-back along `g|_{U'}` of the value on the image open `g(U')`, with empty blow-ups deleted. -/
  commutesWithLocalIsos : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (hT : AnalyticTriple.BOClass s T) (hT' : AnalyticTriple.BOClass s (T.pullback g hg))
    (j : T.F.ι) (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
    (fam (T.pullback g hg) hT' j).seqOn U' hU' =
      (((fam T hT j).seqOn (AnalyticMap.imageOpens g hg U')
            (AnalyticMap.isCompact_closure_image g hU')).pullback
          (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
          (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
            Set.Subset.rfl)).eraseEmpty
  /-- Indifference to empty boundary members, per open: deleting empty members of the boundary along
an order embedding of index types does not change the value at a kept member on any open. -/
  indifferentToEmptyMembers : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι),
    (∀ i, T.F.hyp (e i) = F'.hyp i) → (∀ b, b ∉ Set.range e → T.F.hyp b = ∅) →
    ∀ (hT : AnalyticTriple.BOClass s T)
      (hT' : AnalyticTriple.BOClass s
        (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M))
      (i : F'.ι) (U : Opens M) (hU : IsCompact (closure (U : Set M))),
      (fam T hT (e i)).seqOn U hU =
        (fam ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ hT' i).seqOn U hU

end Hironaka.Manifold
