/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAFamily
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepACompat
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The rounds on the nonmonomial part: the compatible family

With `stepAFamOn_compat` and `stepAFamOn_noEmptyCenters` the values of the rounds on the
nonmonomial part form **the compatible family of the rounds**,
`stepAFam : CompatibleFamily T` ([Wlo09, Theorem 2.0.3 (4)], [Wlo09, Definition 3.2.6];
[Kol07, 32]).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (t : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t)

/-- **The compatible family of the rounds on the nonmonomial part**: the value `stepAFamOn` on every
relatively compact open, no empty centres [Kol07, 32], compatible under restriction
([Wlo09, Theorem 2.0.3 (4)], [Wlo09, Definition 3.2.6]). -/
def stepAFam : CompatibleFamily T where
  seqOn U hU := stepAFamOn T m hT bo hcomp hid t hm hmt U hU
  noEmptyCenters U hU := stepAFamOn_noEmptyCenters T m hT bo hcomp hid t hm hmt U hU
  compat U V hU hV hUV := stepAFamOn_compat T m hT bo hcomp hid t hm hmt U hU V hV hUV

end Hironaka.Manifold.BMOmod

end
