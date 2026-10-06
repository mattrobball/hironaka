/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.LogDeriv
public import Hironaka.Algebra.Local.LogDeriv
public import Hironaka.Manifold.Germ.StalkNoetherian
public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Manifold.IdealSheaf.Deriv
import Hironaka.Algebra.Local.LogDerivCoords
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Properties of the logarithmic derivative ideal sheaves

Properties of logarithmic derivations from [Kol07, 87]: the inclusions `I ⊂ D(−log S)(I) ⊂ D(I)`
and the second of Kollár's three properties, (87.2) — the filtration
`D^s(−log S)(I) ⊂ D^{s−1}(−log S)(D(I)) ⊂ ⋯ ⊂ D^s(I)` and, in local coordinates, the decomposition
`D^s(I) = D^s(−log S)(I) + D^{s−1}(−log S)(∂I/∂x₁) + ⋯ + (∂^s I/∂x₁^s)` whose first `j + 1`
summands span `D^{s−j}(−log S)(D^j(I))`. (The first property, (87.1), the restriction to `S`, is
`Hironaka/Manifold/IdealSheaf/LogDerivRestrict.lean`; the third, the transform under blow-ups,
is in `Hironaka/Manifold/BlowUp/Transform/`.) Everything is stalkwise through
`stalkIdeal_logDeriv` and the `Hironaka` library's lemmas on `Ideal.logDerivative`; the composition
rule `D^a(−log S)(D^b(−log S)(J)) = D^{a+b}(−log S)(J)` is the iterate law; off `S` the
logarithmic derivative is the plain derivative (`Ideal.logDerivative_top`); at a point of `S` with
regular coordinates of the stalk whose distinguished coordinate `x_h` generates `(I_S)_a`, the
stalk of `D^r(−log S)(J)` is the `Hironaka` library's `Dlogpow h r J_a` (`logDerivative_eq_Dlog`),
and the decomposition (87.2) is `Dlogpow_Dpow_eq_iSup` read through
`stalkIdeal_iteratedDeriv_eq_Dpow`. These are the properties used to transform the derivative
ideals under a blow-up with centre inside `S`
(`Hironaka/Manifold/BlowUp/Transform/LogDerivBlowUp.lean`).
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))
  [IsManifold 𝓘(𝕜, E) ω M] {S : Set M} (hS : IsClosedSubmanifold ψ S 1)

namespace IdealSheaf

/-- `I ⊂ D(−log S)(I)` [Kol07, 87]. -/
theorem le_logDeriv (J : IdealSheaf (structureSheaf 𝕜 E M)) : J ≤ IdealSheaf.logDeriv E ψ hS J := by
  rw [IdealSheaf.le_def]
  intro a
  rw [IdealSheaf.stalkIdeal_logDeriv]
  exact Ideal.le_logDerivative (k := 𝕜) _ _

/-- `D(−log S)` is monotone. -/
theorem logDeriv_mono {J K : IdealSheaf (structureSheaf 𝕜 E M)} (hJK : J ≤ K) :
    IdealSheaf.logDeriv E ψ hS J ≤ IdealSheaf.logDeriv E ψ hS K := by
  rw [IdealSheaf.le_def]
  intro a
  rw [IdealSheaf.stalkIdeal_logDeriv, IdealSheaf.stalkIdeal_logDeriv]
  exact Ideal.logDerivative_mono (k := 𝕜) (IdealSheaf.le_def.mp hJK a)

/-- The iterates are monotone. -/
theorem logDerivIter_mono (r : ℕ) {J K : IdealSheaf (structureSheaf 𝕜 E M)} (hJK : J ≤ K) :
    IdealSheaf.logDerivIter E ψ hS r J ≤ IdealSheaf.logDerivIter E ψ hS r K := by
  induction r with
  | zero => simpa using hJK
  | succ r ih =>
    rw [IdealSheaf.logDerivIter_succ, IdealSheaf.logDerivIter_succ]
    exact logDeriv_mono E ψ hS ih

/-- The composition rule `D^a(−log S)(D^b(−log S)(J)) = D^{a+b}(−log S)(J)` (as used in the proof
of [Kol07, Theorem 88]). -/
theorem logDerivIter_logDerivIter (a b : ℕ) (J : IdealSheaf (structureSheaf 𝕜 E M)) :
    IdealSheaf.logDerivIter E ψ hS a (IdealSheaf.logDerivIter E ψ hS b J) =
      IdealSheaf.logDerivIter E ψ hS (a + b) J :=
  (Function.iterate_add_apply _ a b J).symm

variable [FiniteDimensional 𝕜 E]

/-- Off `S`, `D^r(−log S)(J)` is `D^r(J)` stalk by stalk. -/
theorem stalkIdeal_logDerivIter_of_notMem (r : ℕ) (J : IdealSheaf (structureSheaf 𝕜 E M)) {a : M}
    (ha : a ∉ S) :
    (IdealSheaf.logDerivIter E ψ hS r J).stalkIdeal a = (J.iteratedDeriv r).stalkIdeal a := by
  induction r with
  | zero => rw [IdealSheaf.logDerivIter_zero, IdealSheaf.iteratedDeriv_zero]
  | succ r ih =>
    rw [IdealSheaf.logDerivIter_succ, IdealSheaf.stalkIdeal_logDeriv,
      hS.stalkIdeal_idealSheaf_of_notMem ha, Ideal.logDerivative_top, ih,
      IdealSheaf.iteratedDeriv_succ, IdealSheaf.stalkIdeal_deriv]

/-- `D(−log S)(I) ⊂ D(I)` [Kol07, 87]. -/
theorem logDeriv_le_deriv (J : IdealSheaf (structureSheaf 𝕜 E M)) :
    IdealSheaf.logDeriv E ψ hS J ≤ J.deriv := by
  rw [IdealSheaf.le_def]
  intro a
  rw [IdealSheaf.stalkIdeal_logDeriv, IdealSheaf.stalkIdeal_deriv]
  exact Ideal.logDerivative_le_derivative (k := 𝕜) _ _

/-- One step of the filtration (87.2), in the form `D^{k+1}(−log S)(X) ⊆ D^k(−log S)(D(X))`. -/
theorem logDerivIter_succ_le_logDerivIter_deriv (k : ℕ)
    (X : IdealSheaf (structureSheaf 𝕜 E M)) :
    IdealSheaf.logDerivIter E ψ hS (k + 1) X ≤ IdealSheaf.logDerivIter E ψ hS k X.deriv := by
  rw [IdealSheaf.logDerivIter_succ']
  exact logDerivIter_mono E ψ hS k (logDeriv_le_deriv E ψ hS X)

/-- One step of the filtration (87.2) [Kol07, 87]: for `j < s`,
`D^{s−j}(−log S)(D^j J) ⊆ D^{s−(j+1)}(−log S)(D^{j+1} J)`. -/
theorem logDerivIter_iteratedDeriv_le {s j : ℕ} (hj : j < s)
    (J : IdealSheaf (structureSheaf 𝕜 E M)) :
    IdealSheaf.logDerivIter E ψ hS (s - j) (J.iteratedDeriv j) ≤
      IdealSheaf.logDerivIter E ψ hS (s - (j + 1)) (J.iteratedDeriv (j + 1)) := by
  have hsj : s - j = (s - (j + 1)) + 1 := by omega
  have e1 : IdealSheaf.logDerivIter E ψ hS (s - j) (J.iteratedDeriv j) =
      IdealSheaf.logDerivIter E ψ hS ((s - (j + 1)) + 1) (J.iteratedDeriv j) := by rw [hsj]
  have e2 : IdealSheaf.logDerivIter E ψ hS (s - (j + 1)) (J.iteratedDeriv (j + 1)) =
      IdealSheaf.logDerivIter E ψ hS (s - (j + 1)) (J.iteratedDeriv j).deriv := by
    rw [IdealSheaf.iteratedDeriv_succ]
  rw [e1, e2]
  exact logDerivIter_succ_le_logDerivIter_deriv E ψ hS _ _

/-- The end of the filtration (87.2) [Kol07, 87]: `D^r(−log S)(J) ⊆ D^r(J)`. -/
theorem logDerivIter_le_iteratedDeriv (r : ℕ) (J : IdealSheaf (structureSheaf 𝕜 E M)) :
    IdealSheaf.logDerivIter E ψ hS r J ≤ J.iteratedDeriv r := by
  induction r with
  | zero => rw [IdealSheaf.logDerivIter_zero, IdealSheaf.iteratedDeriv_zero]
  | succ r ih =>
    rw [IdealSheaf.logDerivIter_succ, IdealSheaf.iteratedDeriv_succ]
    exact (logDeriv_le_deriv E ψ hS _).trans (IdealSheaf.deriv_mono ih)

/-- In coordinates: at a point `a` with regular coordinates `κ` of the stalk whose `𝕜`-linear
derivations span the `𝕜`-derivations and with `(I_S)_a = (κ.x h)`,
`(D^r(−log S)(J))_a = D^r(−log x_h)(J_a)` (the `Hironaka` library's `Dlogpow`). -/
theorem stalkIdeal_logDerivIter_eq_Dlogpow {a : M}
    (κ : IsLocalRing.RegularCoords ((structureSheaf 𝕜 E M).presheaf.stalk a) n)
    (hk : κ.IsLinearOver 𝕜) (hs : κ.SpansDerivations 𝕜) (h : Fin n)
    (hSa : hS.idealSheaf.stalkIdeal a = Ideal.span {κ.x h}) (r : ℕ)
    (J : IdealSheaf (structureSheaf 𝕜 E M)) :
    (IdealSheaf.logDerivIter E ψ hS r J).stalkIdeal a = κ.Dlogpow h r (J.stalkIdeal a) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [IdealSheaf.logDerivIter_succ, IdealSheaf.stalkIdeal_logDeriv, hSa, ih,
      κ.logDerivative_eq_Dlog hk hs h, IsLocalRing.RegularCoords.Dlogpow_succ]

/-- Kollár's decomposition (87.2) [Kol07, 87]: the decomposition of `(D^s J)_a` by the order of
differentiation in the direction `x_h` — `Dlogpow_Dpow_eq_iSup` at `j = s` through
`stalkIdeal_iteratedDeriv_eq_Dpow`. -/
theorem stalkIdeal_iteratedDeriv_eq_iSup_Dlogpow {a : M}
    (κ : IsLocalRing.RegularCoords ((structureSheaf 𝕜 E M).presheaf.stalk a) n)
    (hk : κ.IsLinearOver 𝕜) (hs : κ.SpansDerivations 𝕜) (h : Fin n) (s : ℕ)
    (J : IdealSheaf (structureSheaf 𝕜 E M)) :
    (J.iteratedDeriv s).stalkIdeal a =
      ⨆ j ≤ s, κ.Dlogpow h (s - j) (κ.iterPderivIdeal h j (J.stalkIdeal a)) := by
  rw [J.stalkIdeal_iteratedDeriv_eq_Dpow κ hk hs s, ← κ.Dlogpow_Dpow_eq_iSup h le_rfl,
    Nat.sub_self, IsLocalRing.RegularCoords.Dlogpow_zero]

end IdealSheaf

end Manifold

end
