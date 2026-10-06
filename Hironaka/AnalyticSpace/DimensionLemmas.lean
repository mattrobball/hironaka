/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Dimension
import Hironaka.AnalyticSpace.ConvDimension
import Hironaka.AnalyticSpace.Jacobian
import Hironaka.AnalyticSpace.RegularStalk
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# Dimension of an analytic space at a point: local models and charts

`dimAt X x = ringKrullDim 𝒪_{X,x}` (`Hironaka/AnalyticSpace/Dimension.lean`; [Fre17, II 5.2]) is
read on the local model at `x` (the local-model clause of `AnalyticSpace` and the stalk transports
`ringKrullDim_stalk_restrictOpen`, `ringKrullDim_stalk_of_kIso` of
`Hironaka/AnalyticSpace/RegularStalk.lean`), where the stalk is `𝒪_n/(f)_z`
(`ringKrullDim_stalk_localModel_eq`, through `stalkEquivQuotientF` of
`Hironaka/AnalyticSpace/Jacobian.lean` and the Taylor isomorphism `taylorAffine`); hence the
dimension is a natural number (`exists_dimAt_eq_natCast`, from `dim (𝒪_n/I) ≤ n` and the
nontriviality of a local ring), and at a point with a manifold chart `X|V ≅ (G', 𝒜_{G'})`, `G' ⊆
K^d`, it is `d` (`dimAt_eq_of_kIso_analyticSpaceOfOpen`; with
`isRegular_stalk_iff_exists_manifold_nhd` this is Freitag's remark that for complex manifolds the
Krull dimension is the usual dimension, at a simple point). Upper semicontinuity is in
`Hironaka/AnalyticSpace/Semicontinuity.lean`, which imports this module.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open AnalyticSpace.KLocallyRingedSpace Analytic Filter Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- An element of `WithBot ℕ∞` between `0` and a natural number is a natural number. -/
theorem exists_natCast_eq_of_nonneg_of_le_natCast {x : WithBot ℕ∞} (h0 : 0 ≤ x) {n : ℕ}
    (hn : x ≤ (n : WithBot ℕ∞)) : ∃ d : ℕ, x = (d : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      have h' : (⊤ : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hn
      exact absurd (top_le_iff.mp h') (ENat.natCast_ne_top n)
    | coe d => exact ⟨d, by simp⟩

/-- The bridge between the two levels: the stalk of the local model `V(f) ⊆ G ⊆ Kⁿ` at `z` is
`𝒜_{Kⁿ,z}/(f)_z` (`stalkEquivQuotientF`), read as `𝒪_n/(f)_z` through the Taylor isomorphism
`taylorAffine` at `z`. -/
theorem ringKrullDim_stalk_localModel_eq {n : ℕ} (G : Opens (Kn.{u} K n)) {k : ℕ}
    (f : Fin k → AnalyticFun K n G) (z : localModel K n G f) :
    ringKrullDim ((localModel K n G f).toLocallyRingedSpace.presheaf.stalk z) =
      ringKrullDim (Analytic.Conv K n ⧸ Ideal.map (taylorAffine K n z.1.1) (Ideal.span
          (Set.range fun j =>
        (affine K n).toLocallyRingedSpace.presheaf.germ G z.1.1 z.1.2 (f j)))) := by
  rw [ringKrullDim_eq_of_ringEquiv (stalkEquivQuotientF z)]
  exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ (taylorAffine K n z.1.1) rfl)

/-- At a point with a manifold chart `X|V ≅ (G', 𝒜_{G'})`, `G' ⊆ K^d`, the dimension is `d` (the
stalk transports of `Hironaka/AnalyticSpace/RegularStalk.lean`; for complex manifolds the Krull
dimension is the usual dimension, [Fre17, II 5.2]). -/
theorem dimAt_eq_of_kIso_analyticSpaceOfOpen {X : AnalyticSpace.{u} K} {V : Opens X} {x : X}
    (hx : x ∈ V) {d : ℕ} {G' : Opens (Kn.{u} K d)}
    (e : KIso (X.toKLocallyRingedSpace.restrictOpen V) (analyticSpaceOfOpen K d G')) :
    AnalyticSpace.dimAt X x = (d : WithBot ℕ∞) := by
  unfold AnalyticSpace.dimAt
  rw [← ringKrullDim_stalk_restrictOpen X.toKLocallyRingedSpace V ⟨x, hx⟩,
    ringKrullDim_stalk_of_kIso e ⟨x, hx⟩, ringKrullDim_stalk_analyticSpaceOfOpen]

/-- The dimension of an analytic `K`-space at a point is a natural number — through the local
model at the point the stalk is `𝒪_n/(f)_z`, of dimension between `0` (a local ring is
nontrivial) and `n`. -/
theorem exists_dimAt_eq_natCast (X : AnalyticSpace.{u} K) (x : X) :
    ∃ d : ℕ, AnalyticSpace.dimAt X x = (d : WithBot ℕ∞) := by
  obtain ⟨U, hxU, n, k, G, f, W, ⟨e⟩⟩ := X.locallyModel x
  have h1 : AnalyticSpace.dimAt X x = ringKrullDim
      ((localModel K n G f).toLocallyRingedSpace.presheaf.stalk (e.hom.1.base ⟨x, hxU⟩).1) := by
    unfold AnalyticSpace.dimAt
    rw [← ringKrullDim_stalk_restrictOpen X.toKLocallyRingedSpace U ⟨x, hxU⟩,
      ringKrullDim_stalk_of_kIso e ⟨x, hxU⟩, ringKrullDim_stalk_restrictOpen]
  have h2 : AnalyticSpace.dimAt X x ≤ (n : WithBot ℕ∞) := by
    rw [h1, ringKrullDim_stalk_localModel_eq]
    exact (ringKrullDim_quotient_le _).trans_eq (ringKrullDim_conv K n)
  have h0 : 0 ≤ AnalyticSpace.dimAt X x := ringKrullDim_nonneg_of_nontrivial
  exact exists_natCast_eq_of_nonneg_of_le_natCast h0 h2

end AnalyticSpace

end
