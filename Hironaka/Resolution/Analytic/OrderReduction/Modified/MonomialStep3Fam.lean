/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.Family
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.MonomialPart
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial procedure as an interface: `MonomialStep3Fam`

The last step of Kollár's proof of the marked order reduction theorem [Kol07, Theorem 107] is
the monomial procedure [Kol07, 111, Step 3]: with `E = ∪ Eʲ` a simple normal crossing divisor
with ordered index set and `M(I) = 𝒪(−∑ aⱼ Eʲ)` the monomial part of `I`, it blows up, in an
order dictated by the indices, the intersections of members along which the sum of the
coefficients is at least `m`, until every such sum is below `m` ("at the end of Step 3.n we are
done" [Kol07, 111, Step 3]).

This module states the properties of that procedure which the assembly of the theorem on an
analytic manifold uses, as a structure `MonomialStep3Fam 𝕜 n m`: a family functor on the marked
class `BMOClass m` at the standard model `Fin n → 𝕜` whose value on a relatively compact open `U`
is a smooth blow-up sequence of order `≥ m` for `(M(𝓘|U), m)` [Kol07, Definition 66 (2′)–(4′)],
whose last marked transform of `(M(𝓘|U), m)` has order `< m` at every point, and which commutes
with local analytic isomorphisms [Kol07, Theorem 107 (2)] and is indifferent to empty boundary
members (the counterpart, for boundary members, of [Kol07, 32]). The monomial part is the fine one,
`Hironaka.Manifold.BMO.monomialPart`,
the product over the connected components of the boundary members.

The structure is inhabited by `Hironaka.Manifold.BMO.monomialStep3Fam`, which realises the
combinatorial run `Hironaka.Monomial.MonomialState.step3` on the piece families of the boundary;
the assembly (`SState.step3Link`) takes an arbitrary inhabitant as a parameter. This module holds
only the structure, so that both sides can import it.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Filter
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

/-- **The monomial procedure in family form.** A family functor on the marked class `BMOClass m`
at the standard model whose values are read on the fine monomial part
`M(𝓘) = monomialPart T.F T.isSnc T.I` of the restricted triple in place of `𝓘`: on a relatively
compact open `U` the value is a smooth blow-up sequence of order `≥ m` for `(M(𝓘|U), m)`, the
marked transform of `(M(𝓘|U), m)` at its last stage has order `< m` at every point (the exit
condition of the procedure, [Kol07, 111, Step 3]), and the functor commutes with local analytic
isomorphisms [Kol07, Theorem 107 (2)] and is indifferent to empty boundary members (the counterpart,
for boundary members, of [Kol07, 32]).

In the assembly of the theorem the procedure runs on `(M(𝓘), m, E)` on the whole last stage of
the separation step, and clause (1) of the theorem for `𝓘` itself follows in
`SState.step3Link_ord_lt`. -/
structure MonomialStep3Fam (𝕜 : Type) [RCLike 𝕜] (n m : ℕ) where
  /-- The family functor of the monomial procedure on the marked class at the standard model. -/
  functor : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (AnalyticTriple.BMOClass m)
  /-- On every relatively compact open `U` the value is a smooth blow-up sequence of order `≥ m`
  for the monomial part of the restricted triple, with respect to its boundary
  [Kol07, Definition 66 (2′)–(4′)]. -/
  isOfOrderGe : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))),
    ((functor.fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (monomialPart (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I) m
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf
  /-- The exit condition of the monomial procedure ("at the end of Step 3.n we are done",
  [Kol07, 111, Step 3]): the marked transform of `(M(𝓘|U), m)` at the last stage of the value over
  `U` has order `< m` at every point. -/
  ord_lt : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (x : ((functor.fam T hT).seqOn U hU).toSuccession.stage (Fin.last _)),
    (((functor.fam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (monomialPart (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F
          (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
          (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I) m (Fin.last _)).ord x
      < (m : ℕ∞)
  /-- The functor commutes with local analytic isomorphisms [Kol07, Theorem 107 (2)]. -/
  commutesWithLocalIsos : functor.CommutesWithLocalIsos
  /-- The counterpart, for boundary members, of the empty blow-up convention [Kol07, 32]: deleting
  or adding empty members of the boundary does not change the value. -/
  indifferentToEmptyMembers : functor.IndifferentToEmptyMembers

end Hironaka.Manifold.BMO

end
