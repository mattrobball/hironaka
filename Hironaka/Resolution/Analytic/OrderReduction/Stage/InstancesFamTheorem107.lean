/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.BMOanFamOfInput
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.NonmonomialComapInhabit
public import Hironaka.Resolution.Analytic.OrderReduction.Stage.Family
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Theorem 107 as the second reduction step

The order-reduction tower on the compatible-family structures (`Stage/Family.lean`) takes the two
reduction steps of [Kol07, 70] as parameters. This module supplies the second one, order reduction
for marked ideals from order reduction for ideals in the same dimension ([Kol07, Theorem 107]).
The construction `BMO.BMOanFamOfInput_of_hid` of `Functor/BMOanFamOfInput.lean` builds the marked
family `BMOanFam 𝕜 n m` in one dimension `n` from the order-reduction families `bo : ∀ d, BOanFam
𝕜 n d`
of that dimension, following the three steps of the proof of Theorem 107 ([Kol07, 111]); it takes
as arguments the ingredients of that proof which are established separately:

* the monomial procedure of Step 3 of the proof, as a family functor on the marked class with the
  clauses of Theorem 107 for the monomial part of the ideal (`BMO.MonomialStep3Fam`);
* the identity of Step 1 of the proof, that along a blow-up sequence of order `≥ d` for the
  nonmonomial part `(N(𝓘), d)` the controlled transform of `(𝓘, m)` and that of `(N(𝓘), d)`
  differ only in their monomial part (`BMOmod.NonmonomialTransformIdentity`), and the same identity
  read modulo the monomial part along a sequence of order `≥ m` for `(𝓘, m)` and `≥ s` for
  `(N(𝓘), s)` (`BMO.NonmonomialTransformIdentityMod`);
* the commutation of the nonmonomial part with pull-back along local analytic isomorphisms
  (`BMOmod.NonmonomialComap`), supplied here by `BMOmod.nonmonomialComap_inhabitant`.

`theorem107FamStarOf 𝕜 st3 hid hidN : BMOanFamStep 𝕜` bundles the construction over every
dimension, with the first three ingredients as arguments given in every dimension. The library
proves them in `BMO/Step3Monomial/Functor.lean` (`BMO.monomialStep3Fam`) and
`Modified/NonmonomialTransformMod.lean` (`nonmonomialTransformIdentity_inhabitant`,
`nonmonomialTransformIdentityMod_inhabitant`); `Stage/Concrete.lean` applies this step to them.
-/

@[expose] public section

noncomputable section

universe u

namespace Hironaka.Manifold

/-- Order reduction for marked ideals from order reduction for ideals in the same dimension
([Kol07, Theorem 107]), as the second reduction step of the tower on the compatible-family
structures, given in every dimension `n` the monomial procedure `st3 n m` of Step 3 of the proof
and the two transform identities `hid n`, `hidN n` for the nonmonomial part: in dimension `n` the
step is `BMO.BMOanFamOfInput_of_hid` at these arguments, the commutation of the nonmonomial part
with pull-back being `BMOmod.nonmonomialComap_inhabitant`. -/
def theorem107FamStarOf (𝕜 : Type) [RCLike 𝕜]
    (st3 : ∀ n m : ℕ, BMO.MonomialStep3Fam.{u} 𝕜 n m)
    (hid : ∀ n : ℕ,
      BMOmod.NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
    (hidN : ∀ n : ℕ,
      BMO.NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) :
    BMOanFamStep.{u} 𝕜 :=
  ⟨fun n bo m =>
    BMO.BMOanFamOfInput_of_hid BMOmod.nonmonomialComap_inhabitant (hid n) (hidN n) m (st3 n m) bo⟩

/-- The value of the step in dimension `n`, on the order-reduction families `bo` and at the mark
`m`, unfolds to `BMO.BMOanFamOfInput_of_hid` at the given arguments. -/
theorem theorem107FamStarOf_bmo (𝕜 : Type) [RCLike 𝕜]
    (st3 : ∀ n m : ℕ, BMO.MonomialStep3Fam.{u} 𝕜 n m)
    (hid : ∀ n : ℕ,
      BMOmod.NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
    (hidN : ∀ n : ℕ,
      BMO.NonmonomialTransformIdentityMod.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
    (n : ℕ) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d) (m : ℕ) :
    (theorem107FamStarOf 𝕜 st3 hid hidN).bmo n bo m =
      BMO.BMOanFamOfInput_of_hid BMOmod.nonmonomialComap_inhabitant (hid n) (hidN n) m (st3 n m)
        bo :=
  rfl

end Hironaka.Manifold

end
