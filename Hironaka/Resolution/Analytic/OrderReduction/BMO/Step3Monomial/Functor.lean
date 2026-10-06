/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Naturality
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.MonomialStep3Fam
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial procedure as a family functor

The monomial procedure of [Kol07, 111, Step 3] on the marked class `BMOClass m` at the standard
model, packaged as a family functor (`monomialStep3Functor`): on a triple of the class, the
compatible family whose value on a relatively compact open `U` is `monomialStep3SeqOn`
(`BMO/Step3Monomial/Value.lean`), with no empty centres and compatible under restriction up to empty
blow-ups (`monomialStep3SeqOn_compat`, [Wlo09, Theorem 2.0.3 (4)]). The structure
`MonomialStep3Fam 𝕜 n m` of `Modified/MonomialStep3Fam.lean` is then inhabited (`monomialStep3Fam`)
by this functor together with its two order properties, its commutation with local analytic
isomorphisms (`monomialStep3SeqOn_pullback`, [Kol07, 34.1]) and its indifference to empty boundary
members (`monomialStep3SeqOn_indiff`). This inhabitant is the monomial step of the analytic marked
order reduction (`Modified/Step3Link.lean`).
-/

@[expose] public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- The family functor of the monomial procedure on the marked class at the standard model: on each
triple of the class, the compatible family of the values `monomialStep3SeqOn`, with no empty centres
and compatible under restriction up to empty blow-ups. -/
noncomputable def monomialStep3Functor (m : ℕ) :
    AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (AnalyticTriple.BMOClass m) where
  fam T hT :=
    { seqOn := fun U hU => monomialStep3SeqOn T m hT U hU
      noEmptyCenters := fun U hU => monomialStep3SeqOn_noEmptyCenters T m hT U hU
      compat := fun U V hU hV hUV => monomialStep3SeqOn_compat T m hT U hU V hV hUV }

@[simp] theorem monomialStep3Functor_fam_seqOn (m : ℕ) {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((monomialStep3Functor m).fam T hT).seqOn U hU = monomialStep3SeqOn T m hT U hU := rfl

/-- The inhabitant of `MonomialStep3Fam 𝕜 n m`: the functor of the monomial procedure with the order
clauses of [Kol07, Definition 66 (2′)–(4′)] for `(M(𝓘|_U), m)`, the terminal bound of
[Kol07, 111, Step 3], the commutation with local analytic isomorphisms of [Kol07, Theorem 107 (2)]
and the indifference to empty boundary members. -/
noncomputable def monomialStep3Fam (𝕜 : Type) [RCLike 𝕜] (n m : ℕ) :
    MonomialStep3Fam.{u} 𝕜 n m where
  functor := monomialStep3Functor m
  isOfOrderGe := fun T hT U hU => monomialStep3SeqOn_isOfOrderGe T m hT U hU
  ord_lt := fun T hT U hU x => ord_lt_monomialStep3SeqOn T m hT U hU x
  commutesWithLocalIsos := fun T T' g hg hT'T hT hT' U' hU' =>
    monomialStep3SeqOn_pullback T m hT T' g hg hT'T hT' U' hU'
  indifferentToEmptyMembers := fun T F' hsnc' e h1 h2 hT hT' U hU =>
    monomialStep3SeqOn_indiff T m hT U hU F' hsnc' e h1 h2 hT'

end Hironaka.Manifold.BMO
