/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.Family
public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The modified marked resolution as its own object: `BMOmodFam`

The proof of [Wlo09, Theorem 7.4.1] runs the marked resolution of `(M, I_Y, ∅, 1)` with a
modified algorithm: in its second step the monomial part `(M(I), 1)` is resolved first, by
blow-ups at exceptional divisors of maximal `ρ`; in its first step the run is stopped at a germ
where the current controlled transform is the ideal `(u)` of a smooth hypersurface of maximal
contact, and otherwise restricted to a hypersurface of maximal contact and repeated; it
terminates with the controlled transform of `(I, 1)` locally equal to `I″ = (u₁, …, u_k)`, the
`u_i` coordinates transversal to the exceptional divisors; the procedure is canonical and glues
from germs at compact sets (compare the proof of [Wlo05, Theorem 4.7.1]). This library makes the
modified run its own object: the structure `BMOmodFam 𝕜 n`, in the family form of
`Hironaka.Resolution.Analytic.Functor.Family` (a `CompatibleFamily` on every relatively compact
open), whose fields are the clauses of that proof read per open on the restricted marked triple,
and its instance `concreteBMOmodFam`
(`Hironaka.Resolution.Analytic.Wlo09.Concrete`); the
embedded-desingularization functor `bedanFamOfInput` is the restriction of its functor to the
class of reduced closed subspaces with empty boundary.

This file provides the two tools the clauses need and the structure:

* `HypersurfaceFamily.IsSmoothTransversalIdealAt ψ F J x`: `J` is at `x` locally the ideal of a
  smooth submanifold with coordinates transversal to `F` (on the source of a chart `φ` through
  `x`, `J = (u₁, …, u_k)` for `k` of the coordinates `ψ ∘ φ`, and `φ` is an snc chart of `F` at
  `x` none of whose component coordinates is one of the `u_i`);
* `FiniteSuccession.stageMapAdd S i k h`: the composite `σ_{i+1} ∘ ⋯ ∘ σ_{i+k} : U_{i+k} → U_i`
  of the blow-downs between two stages (the stage-`i` reading of `stageMap`), with its two
  unfolding lemmas;
* `BMOmodFam 𝕜 n`: `functor` on `BMOClass 1`; `isOfOrderGe` ([Kol07, Definition 66, (2′)–(4′)]
  at mark `1`); `center_mem_support` ([Wlo09, Definition 3.2.4, (1)]);
  `output_isSmoothSubmanifoldIdeal` (the output of the run, with the total boundary);
  `stopped_never_blownUp` (the stop rule read globally, at points off the boundary);
  `commutesWithLocalIsos` ([Wlo09, Theorem 6.0.6, (2)]) and `indifferentToEmptyMembers`. There is
  no `ord_lt` (the modified run does not reach order `< 1`), no descent identity (it is the
  construction's definition) and no monomial-first trigger.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

/-! ### The composite of blow-downs between two stages (the vocabulary of the stop rule) -/

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- **The composite `σ_{i+1} ∘ ⋯ ∘ σ_{i+k} : U_{i+k} → U_i`** of the blow-downs between the
stages `i` and `i + k`, by recursion on `k` exactly as `stageMapAux` (the case `i = 0` is
`stageMap`, up to `0 + k = k`). A point `y ∈ U_{i+k}` lies over `x ∈ U_i` when
`S.stageMapAdd i k h y = x`. -/
def stageMapAdd (i : ℕ) : ∀ (k : ℕ) (h : i + k < S.length + 1),
    AnalyticMap (S.stage ⟨i + k, h⟩) (S.stage ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩)
  | 0, _ => ContMDiffMap.id
  | k + 1, h =>
    (stageMapAdd i k (Nat.lt_of_succ_lt h)).comp (S.map ⟨i + k, Nat.lt_of_succ_lt_succ h⟩)

/-- The composite over no blow-down is the identity of the stage. -/
@[simp] theorem stageMapAdd_zero (i : ℕ) (h : i + 0 < S.length + 1) :
    S.stageMapAdd i 0 h = ContMDiffMap.id := rfl

/-- One more blow-down: `σ_{i+1} ∘ ⋯ ∘ σ_{i+k+1} = (σ_{i+1} ∘ ⋯ ∘ σ_{i+k}) ∘ σ_{i+k+1}`. -/
theorem stageMapAdd_succ (i k : ℕ) (h : i + (k + 1) < S.length + 1) :
    S.stageMapAdd i (k + 1) h =
      (S.stageMapAdd i k (Nat.lt_of_succ_lt h)).comp (S.map ⟨i + k, Nat.lt_of_succ_lt_succ h⟩) :=
  rfl

end AnalyticManifold.FiniteSuccession

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-! ### Locally the ideal of a smooth submanifold transversal to the boundary -/

section Predicate

variable (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M]

/-- **`J`
is at `x` locally the ideal of a smooth submanifold with coordinates transversal to `F`** — there
are a chart `φ` of the maximal atlas through `x` which is an snc chart of `F` at `x` with component
coordinates `cidx` (`IsSncChartAt`: the components of `F` through `x` are the coordinate
hyperplanes `z_{cidx j} = 0` on `φ.source`), and `k = c` coordinate indices `σ`, such that on the
whole source of `φ` the stalks of `J` are spanned by the coordinate germs `u_i = z_{σ i} ∘ φ`
(`coord`; the vocabulary of `IsIdealSheafOf`) and no `u_i` is a component
coordinate (`cidx j ≠ σ i`: the `u_i` are transversal to the components through `x`). The zero set
of `J` on `φ.source` is then the coordinate subspace `{z_σ = 0}`, smooth of codimension `c`, and
`{z_σ = 0} ∪ ⋃ F` has simple normal crossings there. Membership of `x` in the zero set is not
demanded by a separate clause: at `c = 0` the equation reads `J = 0` on `φ.source` (the zero ideal,
excluded by the triples' `isNonzeroEverywhere`), and a point OFF the zero set satisfies the
predicate only with `c ≥ 1` through a chart whose source misses `{z_σ = 0}` (there `J = 𝒪` is
spanned by the unit `u₁`) — the germ with nothing left to resolve. The output clause quantifies
over the support `1 ≤ ord`, and in the stop rule the predicate is the hypothesis. -/
def HypersurfaceFamily.IsSmoothTransversalIdealAt (F : HypersurfaceFamily M)
    (J : IdealSheaf (structureSheaf 𝕜 E M)) (x : M) : Prop :=
  ∃ (c : ℕ) (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n)
    (cidx : {j // x ∈ F.hyp j} → Fin n) (hφ : F.IsSncChartAt ψ φ x cidx),
    (∀ a (ha : a ∈ φ.source),
      J.stalkIdeal a = Ideal.span (Set.range fun i => coord E ψ φ hφ.1 ha (σ i))) ∧
    ∀ (j : {j // x ∈ F.hyp j}) (i : Fin c), cidx j ≠ σ i

end Predicate

/-! ### The structure `BMOmodFam` at the standard model -/

/-- **The modified marked resolution of the proof of [Wlo09, Theorem 7.4.1] as its own object**
(compare the proof of [Wlo05, Theorem 4.7.1]; the family record `BMOanFam` is the template): a
family functor on the marked class `BMOClass 1` at the standard model `𝕜ⁿ` with the clauses of
that proof read per relatively compact open `U` on the restricted marked triple
`T.pullback (M.inclusion U) _` along the value `L := (functor.fam T hT).seqOn U hU`: the run is a
blow-up sequence of order `≥ 1` for `(𝓘, 1)` ([Kol07, Definition 66, (2′)–(4′)], kept from
`BMOanFam`); every centre lies in the support of the current controlled transform
([Wlo09, Definition 3.2.4, (1)]); the final controlled transform is, at every point of its
support, locally the ideal of a smooth submanifold with coordinates transversal to the
exceptional divisors (the output of the run; not a marked-resolution clause, since the modified
run does not reach order `< 1`, so the `ord_lt` of `BMOanFam` is the one clause dropped); the
stop rule read globally, for a run canonical and glued from germs: at a point of a stage where
the current controlled transform is locally the ideal of a smooth submanifold transversal to the
exceptional divisors, no later centre contains the images of that point; commutation with local
analytic isomorphisms ([Wlo09, Theorem 6.0.6, (2)]) and indifference to empty boundary members.
The value's `noEmptyCenters` and `compat` are `CompatibleFamily`'s own. Not fields: the descent
identity of the maximal-contact recursion (the definition of the run), the monomial-first
trigger, and the identification of the components of the final support with the strict
transforms of the components of `Y`. Its functor restricted to `DomBEDan` is `bedanFamOfInput`.
`Type (u+1)` as `BMOanFam`. -/
structure _root_.Hironaka.Manifold.BMOmodFam (𝕜 : Type) [RCLike 𝕜] (n : ℕ) where
  /-- The family functor of the modified marked resolution on the marked class of mark `1` at the
  standard model `𝕜ⁿ` (the proof of [Wlo09, Theorem 7.4.1] treats `(X, I_Y, ∅, 1)` and, in
  general, `(X, I, E, µ)`; here `µ = 1`). -/
  functor : Hironaka.Manifold.AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (AnalyticTriple.BMOClass 1)
  /-- [Kol07, Definition 66, (2′)–(4′)] at mark `1`, per open: the value on `U` is a smooth
  blow-up sequence of order `≥ 1` starting with the restricted `(M, 𝓘, 1, E)`; this is
  `BMOanFam.isOfOrderGe` at `m := 1`. -/
  isOfOrderGe : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass 1 T) (U : Opens M) (hU : IsCompact (closure (U : Set M))),
    ((functor.fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf
  /-- [Wlo09, Definition 3.2.4, (1)] (`C_i ⊂ supp(M_i, Z_i, I_i, E_i, µ)`) at `µ = 1`, per open:
  every centre `C_i` lies in the support `supp(𝓘_i, 1) = {x | ord_x 𝓘_i ≥ 1}` of the current
  controlled transform `𝓘_i` (the marked transform chain of `isOfOrderGe`). Kept beside
  `isOfOrderGe`, with which it coincides at mark `1`, as both are printed in the source. -/
  center_mem_support : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass 1 T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (i : Fin ((functor.fam T hT).seqOn U hU).toSuccession.length),
    (((functor.fam T hT).seqOn U hU).toSuccession.center i).support ⊆
      {x | (1 : ℕ∞) ≤ (((functor.fam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 i.castSucc).ord x}
  /-- The output of the run (the proof of [Wlo09, Theorem 7.4.1]: the resulting controlled
  transform of `(I, 1)` is locally `(u₁, …, u_k)` with the `u_i` coordinates transversal to the
  exceptional divisors), per open: at every point of the support `supp(𝓘_r, 1)` of the final
  controlled transform `𝓘_r` (stage `r = Fin.last _`), `𝓘_r` is locally the ideal of a smooth
  submanifold with coordinates transversal to the divisors of `E_r`. Here `E_r` is the total
  boundary at the last stage (old divisors and exceptional divisors, `totalTransformSeqFrom`):
  the source says "exceptional divisors" for its start `E = ∅`, while on the class `BMOClass 1`
  (any `E`) the total boundary is the form the recursion needs at the lower levels (the upper
  level's exceptional divisors are the lower level's `E`), and at the end every divisor through a
  support point has been made transversal by the first step of the run, so the clause with the
  total boundary is what the construction proves. Which components are strict transforms of the
  components of `Y` is a separate statement. -/
  output_isSmoothSubmanifoldIdeal : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass 1 T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (x : ((functor.fam T hT).seqOn U hU).toSuccession.stage (Fin.last _)),
    (1 : ℕ∞) ≤ (((functor.fam T hT).seqOn U hU).toSuccession.markedTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 (Fin.last _)).ord x →
    HypersurfaceFamily.IsSmoothTransversalIdealAt (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (((functor.fam T hT).seqOn U hU).toSuccession.totalTransformSeqFrom
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F (Fin.last _))
      (((functor.fam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1 (Fin.last _)) x
  /-- The stop rule of the proof of [Wlo09, Theorem 7.4.1] (the algorithm stops where the current
  ideal is the ideal of a smooth hypersurface of maximal contact), as a property of the whole
  sequence, for a run canonical and glued from germs, per open: at a point `x` of the stage `U_i`
  which lies on no divisor of the boundary `E_i` and where the current controlled transform `𝓘_i`
  satisfies `IsSmoothTransversalIdealAt` (the hypothesis is stated with the predicate of the output
  clause, so that the two clauses speak of one notion; off the boundary its transversality part
  carries no content, since no divisor of `E_i` passes through `x`, and only the smooth-submanifold
  part remains), no later centre `C_{i+k}` (`k = 0` the point's own stage) contains a point
  `y ∈ U_{i+k}` lying over `x` (`stageMapAdd i k _ y = x`). The boundary is excluded because the
  first step of the modified run moves the old divisors apart from the support (it blows up the
  strata of the boundary contained in the support and resolves the restrictions to them) before
  the stop rule is tested: a support point on a divisor is blown up there even where `𝓘_i` is a
  smooth submanifold ideal transversal to the divisor. At a point off the boundary nothing is
  moved and the run stops. The global presentation of the same rule in the proof of
  [Wlo05, Theorem 4.7.1] ignores the isolated components. -/
  stopped_never_blownUp : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass 1 T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (i k : ℕ) (h : i + k < ((functor.fam T hT).seqOn U hU).toSuccession.length)
    (x : ((functor.fam T hT).seqOn U hU).toSuccession.stage
      ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) h)⟩),
    HypersurfaceFamily.IsSmoothTransversalIdealAt (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (((functor.fam T hT).seqOn U hU).toSuccession.totalTransformSeqFrom
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F
        ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) h)⟩)
      (((functor.fam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
        ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) h)⟩) x →
    (∀ j, x ∉ (((functor.fam T hT).seqOn U hU).toSuccession.totalTransformSeqFrom
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F
        ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) h)⟩).hyp j) →
    ∀ y : ((functor.fam T hT).seqOn U hU).toSuccession.stage ⟨i + k, Nat.lt_succ_of_lt h⟩,
      ((functor.fam T hT).seqOn U hU).toSuccession.stageMapAdd i k (Nat.lt_succ_of_lt h) y = x →
      y ∉ (((functor.fam T hT).seqOn U hU).toSuccession.center ⟨i + k, h⟩).support
  /-- [Wlo09, Theorem 6.0.6, (2)] ([Kol07, 34.1] per open): the functor commutes with local
  analytic isomorphisms. -/
  commutesWithLocalIsos : functor.CommutesWithLocalIsos
  /-- The functor is indifferent to empty boundary members. -/
  indifferentToEmptyMembers : functor.IndifferentToEmptyMembers

end Manifold

end
