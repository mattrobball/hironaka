/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Realize
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Input
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.InputMonomial
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The value of the monomial procedure on a relatively compact open set

The value of the monomial procedure of [Kol07, 111, Step 3] on a relatively compact open `U` of a
triple `T` of the class `BMOClass m` (`monomialStep3SeqOn`) is the realisation, on `M.restrict U`,
of the combinatorial run from the state of the input piece family of the traces
(`BMO/Step3Monomial/Input.lean`, `BMO/Step3Monomial/Realize.lean`). Its three properties are stated
in the form the interface `MonomialStep3Fam` of `Modified/MonomialStep3Fam.lean` reads: no empty
centre ([Kol07, 32]); a smooth blow-up sequence of order `≥ m` for the monomial part `M(𝓘|_U)` of
the restricted triple with the restricted boundary ([Kol07, Definition 66 (2′)–(4′)]); and order
`< m` of the last marked transform of `(M(𝓘|_U), m)` at every point ("at the end of Step 3.n we are
done"). The realisation's properties are stated for the monomial ideal of the input family, which is
the monomial part of the restricted triple (`BMO/Step3Monomial/InputMonomial.lean`).
-/

@[expose] public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- The value of the monomial procedure on `U`: Kollár's Step 3 [Kol07, 111, Step 3] on the traces
of the ambient boundary components meeting `closure U`, read on `M.restrict U` — the realisation of
the combinatorial run from the state of the input family. -/
noncomputable def monomialStep3SeqOn
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
    (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict U) :=
  (inputFamily T U hU).realize
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
    (inputFamily_realizes T U hU) (inputFamily_isValid T U hU hT)

/-- No centre of the value is empty ([Kol07, 32]): the loci are nonempty by construction. -/
theorem monomialStep3SeqOn_noEmptyCenters
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
    (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (monomialStep3SeqOn T m hT U hU).NoEmptyCenters :=
  PieceFamily.realize_noEmptyCenters
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
    (inputFamily_realizes T U hU) (inputFamily_isValid T U hU hT)

/-- The value is a smooth blow-up sequence of order `≥ m` for the monomial part of the restricted
triple with the restricted boundary ([Kol07, Definition 66 (2′)–(4′)]). -/
theorem monomialStep3SeqOn_isOfOrderGe
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
    (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (monomialStep3SeqOn T m hT U hU).toSuccession.IsOfOrderGe
      (monomialPart (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I) m
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf := by
  rw [← monomialIdeal_inputFamily T U hU]
  exact PieceFamily.realize_isOfOrderGe
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
    (inputFamily_realizes T U hU) (inputFamily_isValid T U hU hT)

/-- At every point of the last stage the marked transform of `(M(𝓘|_U), m)` has order `< m`
([Kol07, 111, Step 3]: "at the end of Step 3.n we are done"). -/
theorem ord_lt_monomialStep3SeqOn
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
    (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (x : (monomialStep3SeqOn T m hT U hU).toSuccession.stage (Fin.last _)) :
    ((monomialStep3SeqOn T m hT U hU).toSuccession.markedTransformSeq
        (monomialPart (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F
          (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
          (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I) m (Fin.last _)).ord x
      < (m : ℕ∞) := by
  rw [← monomialIdeal_inputFamily T U hU]
  exact PieceFamily.realize_ord_lt
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
    (inputFamily_realizes T U hU) (inputFamily_isValid T U hU hT) x

end Hironaka.Manifold.BMO
