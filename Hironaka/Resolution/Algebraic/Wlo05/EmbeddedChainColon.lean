/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColonRegular
import Hironaka.Scheme.BlowUp.FlatColon
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The isolated ideal has the K-shape

The scheme form of the statement CP2 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`): on a scheme smooth over `k` (locally
Noetherian, with regular local stalks), if `I` is chain-relative monomial along `Γ` at `p`
(`ChainRelativeAt`), then the colon `I : Γ` has the K-shape along `Γ` at `p` (`ChainRelativeKAt`).
The stalk of the colon is the colon of the stalks on a locally Noetherian scheme
(`stalkIdeal_colon_of_isLocallyNoetherian`), and in the regular local stalk the colon of the chain
ideal by the chain is the K-shape (`chainIdeal_colon_span_eq'`,
`Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColonRegular`). This is what the isolation of the
loop (`isolatedTriple`, `Hironaka.Resolution.Algebraic.Wlo05.Embedded`: the colon by the reduced
ideal of the absorbed strict transforms, which is `Γ`'s ideal near `Γ` by CP1) produces at the entry
into the protected state (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

/-- The exponent vectors of chain coordinates vanish on the chain's own coordinates. -/
theorem ChainCoords.apply_eq_zero_of_mem_range {E : DivisorFamily X} {Γ : X.IdealSheafData}
    {p : X} {n : ℕ} {z : Fin n → X.presheaf.stalk p}
    {c : {j : E.ι // p ∈ (E.component j).support} → Fin n} {r : ℕ} {σ : Fin (r + 1) → Fin n}
    {a : Fin (r + 1) → Fin n → ℕ} (h : ChainCoords E Γ p z c σ a) (i : Fin (r + 1)) (k : Fin n)
    (hk : k ∈ Set.range σ) : a i k = 0 := by
  obtain ⟨i', rfl⟩ := hk
  by_contra hne
  obtain ⟨j, hj⟩ := h.2.2.2.2.2.1 i _ hne
  exact h.2.2.2.2.1 i' j hj.symm

omit [CharZero k] in
/-- **CP2 on the scheme**: on a scheme smooth over `k`, the colon by `Γ` of an ideal chain-relative
monomial along `Γ` at `p` has the K-shape along `Γ` at `p`. -/
theorem chainRelativeKAt_colon (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] {E : DivisorFamily X} {I Γ : X.IdealSheafData} {p : X}
    (h : ChainRelativeAt E I Γ p) : ChainRelativeKAt E (I.colon Γ) Γ p := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨n, z, c, r, σ, a, b, hcc, hb, hI⟩ := h
  refine ⟨n, z, c, r, σ, a, b, hcc, hb, ?_⟩
  have := isRegularLocalRing_stalk f p
  rw [IdealSheafData.stalkIdeal_colon_of_isLocallyNoetherian, hI, hcc.2.2.2.2.2.2]
  refine chainIdeal_colon_span_eq' hcc.1 hcc.2.2.2.1 hcc.apply_eq_zero_of_mem_range b ?_
  rintro k ⟨i, rfl⟩
  by_contra hne
  obtain ⟨j, hj⟩ := hb _ hne
  exact hcc.2.2.2.2.1 i j hj.symm

end Hironaka.Resolution
