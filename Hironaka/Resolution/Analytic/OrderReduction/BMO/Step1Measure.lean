/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.NonmonomialPart
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.IdealSheaf.Monoid
import Hironaka.Manifold.StructureSheaf
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Split
import Hironaka.Resolution.Analytic.OrderReduction.BMO.SplitOrder
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The decomposition `𝓘 = M(𝓘) · N(𝓘)` as ideal sheaves

The stalkwise statements of `BMO/Split.lean` and `BMO/SplitOrder.lean` lifted to ideal sheaves: the
containment `𝓘 ≤ M(𝓘)` and the identity `M(𝓘) · N(𝓘) = 𝓘` of [Kol07, Definition–Lemma 110], together
with the elementary facts that products and powers of ideal sheaves that are nonzero at every point
are again nonzero at every point (the stalks of the structure sheaf are domains), and that a factor
of such a product is nonzero at every point. These are the forms in which Step 1 of the proof of
[Kol07, Theorem 107] compares the nonmonomial part of a marked transform with the transform of the
nonmonomial part (`BMO/Step1Transform.lean`, `BMO/Step1PerBlowUp.lean`).
-/

public section

open Set
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M]

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The ideal `𝓘` is contained in its monomial part `M(𝓘)` as ideal sheaves, the sheaf-level form of
`stalkIdeal_le_monomialPart`; the counterpart of `le_nonmonomialPart` on the other side of the
decomposition `𝓘 = M(𝓘) · N(𝓘)`. -/
theorem le_monomialPart (F : HypersurfaceFamily M) (hF : F.IsSnc ψ)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) :
    I ≤ monomialPart F hF I :=
  IdealSheaf.le_def.mpr (stalkIdeal_le_monomialPart F hF I)

/-- The decomposition `M(𝓘) · N(𝓘) = 𝓘` of [Kol07, Definition–Lemma 110] as an identity of ideal
sheaves: the stalk of a product of ideal sheaves is the product of the stalks, and stalkwise the
identity is `stalkIdeal_monomialPart_mul_nonmonomialPart`. -/
theorem monomialPart_mul_nonmonomialPart (F : HypersurfaceFamily M) (hF : F.IsSnc ψ)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) :
    monomialPart F hF I * nonmonomialPart F hF I = I :=
  IdealSheaf.ext fun x => by
    rw [IdealSheaf.stalkIdeal_mul, stalkIdeal_monomialPart_mul_nonmonomialPart F hF I x]

include ψ in
/-- The product of two ideal sheaves that are nonzero at every point is nonzero at every point: the
stalks of the structure sheaf are domains, so a product of stalks is zero only if a factor is. -/
theorem isNonzeroEverywhere_mul (I J : IdealSheaf (structureSheaf 𝕜 E M))
    (hI : I.IsNonzeroEverywhere) (hJ : J.IsNonzeroEverywhere) :
    (I * J).IsNonzeroEverywhere := by
  intro x hIJ
  rw [IdealSheaf.stalkIdeal_mul] at hIJ
  have _hdom : IsDomain ((structureSheaf 𝕜 E M).presheaf.stalk x) :=
    isDomain_stalk ψ (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source E x)
  rcases Ideal.mul_eq_bot.mp hIJ with h | h
  · exact hI x h
  · exact hJ x h

include ψ in
/-- A power of an ideal sheaf that is nonzero at every point is nonzero at every point (the zeroth
power is the unit ideal). -/
theorem isNonzeroEverywhere_pow (I : IdealSheaf (structureSheaf 𝕜 E M))
    (hI : I.IsNonzeroEverywhere) (k : ℕ) : (I ^ k).IsNonzeroEverywhere := by
  induction k with
  | zero =>
    rw [pow_zero]; intro x hx
    have _hdom : IsDomain ((structureSheaf 𝕜 E M).presheaf.stalk x) :=
      isDomain_stalk ψ (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source E x)
    rw [IdealSheaf.stalkIdeal_one] at hx
    exact absurd hx top_ne_bot
  | succ k ih => rw [pow_succ]; exact isNonzeroEverywhere_mul (ψ := ψ) _ _ ih hI

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- A right factor of a product that is nonzero at every point is nonzero at every point: a zero
stalk of `J` would make the stalk of `I · J` zero. This lets a product of monomial factors be peeled
off one factor at a time while the remaining product stays nonzero. -/
theorem isNonzeroEverywhere_of_mul_right {I J : IdealSheaf (structureSheaf 𝕜 E M)}
    (h : (I * J).IsNonzeroEverywhere) : J.IsNonzeroEverywhere :=
  fun x hJ => h x (by rw [IdealSheaf.stalkIdeal_mul, hJ, Ideal.mul_bot])

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- A left factor of a product that is nonzero at every point is nonzero at every point. -/
theorem isNonzeroEverywhere_of_mul_left {I J : IdealSheaf (structureSheaf 𝕜 E M)}
    (h : (I * J).IsNonzeroEverywhere) : I.IsNonzeroEverywhere :=
  fun x hI => h x (by rw [IdealSheaf.stalkIdeal_mul, hI, Ideal.bot_mul])

end Hironaka.Manifold.BMO
