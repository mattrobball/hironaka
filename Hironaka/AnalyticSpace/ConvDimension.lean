/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.NoetherNormalization
public import Hironaka.Analytic.Rueckert.ZeroSet
public import Mathlib.RingTheory.KrullDimension.Basic
import Hironaka.Algebra.Local.IntegralKrullDim
import Hironaka.Algebra.Local.QuotientParameters
import Hironaka.Analytic.Germ.CoordDiv
import Hironaka.Analytic.Rueckert.Noetherian
import Hironaka.AnalyticSpace.Dimension
import Hironaka.AnalyticSpace.RegularStalk
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# The dimension of an analytic germ on the germ ring `𝒪_n`

The Krull dimension of `𝒪_n/I`, `𝒪_n = Conv K n` the ring of convergent power series
(`Hironaka/Analytic/ConvSeries/`), is the `d` of every Noether normalization `𝒪_d ↪ 𝒪_n/I`
([Fre17, I 7.2]: the number `d` is unique, it is the Krull dimension — by the theorem of
Cohen–Seidenberg, [Fre17, VII 5.7], `Hironaka/Algebra/Local/IntegralKrullDim.lean`), so the Krull
dimension is the unique — hence the largest — `d` with a coordinate projection finite and
surjective on germs (`ringKrullDim_quotient_eq_of_normMap`, `exists_normMap_injective_finite_iff`;
Noether normalization `exists_noetherNormalization_analytic`, `normMap` of
`Hironaka/Analytic/Rueckert/NoetherNormalization.lean`); `dim (𝒪_n/I) ≤ n = dim 𝒪_n`
([Fre17, VII 5.6]; `ringKrullDim_conv` through the Taylor isomorphism `taylorAffine` and
`ringKrullDim_stalk_affine`), with equality iff `I = 0` ([Fre17, II 5.11] for `X = Kⁿ`;
`Ideal.eq_bot_of_ringKrullDim_quotient_eq` of `Hironaka/Algebra/Local/QuotientParameters.lean` in
the Noetherian local domain `𝒪_n`), and `I = 0` iff `V(I)` is a neighbourhood of `0` (the identity
theorem, `span_eq_bot_iff_eventually_mem_zeroSet`). Every statement holds over `K = ℝ` and `ℂ`.
Used by `Hironaka/AnalyticSpace/DimensionLemmas.lean`.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open AnalyticSpace.KLocallyRingedSpace Analytic Filter Topology
open scoped Manifold ContDiff

namespace AnalyticSpace

variable (K : Type) [RCLike K] (n : ℕ)

/-- The germ ring has Krull dimension `n` ([Fre17, VII 5.6]: `ℂ{z₁, …, z_n}` has Krull dimension
`n`): it is `𝒜_{Kⁿ,0}` through the Taylor isomorphism `taylorAffine`, of Krull dimension `n`
(`ringKrullDim_stalk_affine`). -/
theorem ringKrullDim_conv : ringKrullDim (Analytic.Conv K n) = (n : WithBot ℕ∞) :=
  (ringKrullDim_eq_of_ringEquiv (taylorAffine.{0} K n (ULift.up 0)).symm).trans
    (ringKrullDim_stalk_affine.{0} K n (ULift.up 0))

/-- Every Noether normalization `𝒪_d ↪ 𝒪_n/I` (injective and finite) has `d = ringKrullDim (𝒪_n/I)`
([Fre17, I 7.2, VII 5.7]) — Cohen–Seidenberg for the finite injective `normMap`. The hypothesis
`_hI : I ≠ ⊤` is part of Freitag's statement (the ideal is proper) and is kept so that the theorem
reads as printed and takes the same hypotheses as `exists_normMap_injective_finite_iff` below; the
proof does not need it, because a finite injective ring map into the trivial ring `𝒪_n/⊤` does
not exist, so `I ≠ ⊤` follows from `hinj`. -/
theorem ringKrullDim_quotient_eq_of_normMap {n d : ℕ} (I : Ideal (Analytic.Conv K n)) (_hI : I ≠ ⊤)
    (e : Fin d ↪ Fin n) (L : (Fin n → K) ≃L[K] (Fin n → K))
    (hinj : Function.Injective (normMap K I e L))
    (hfin : RingHom.Finite (A := Analytic.Conv K d) (B := Analytic.Conv K n ⧸ I)
      (normMap K I e L : Analytic.Conv K d →+* Analytic.Conv K n ⧸ I)) :
    ringKrullDim (Analytic.Conv K n ⧸ I) = d :=
  (IsLocalRing.ringKrullDim_eq_of_finite_of_injective _ hfin hinj).trans (ringKrullDim_conv K d)

/-- `d` admits an injective finite normalization map iff `d = ringKrullDim (𝒪_n/I)` — existence by
Noether normalization (`exists_noetherNormalization_analytic`), uniqueness by Cohen–Seidenberg. -/
theorem exists_normMap_injective_finite_iff {n : ℕ} (I : Ideal (Analytic.Conv K n)) (hI : I ≠ ⊤)
    (d : ℕ) :
    (∃ (e : Fin d ↪ Fin n) (L : (Fin n → K) ≃L[K] (Fin n → K)),
      Function.Injective (normMap K I e L) ∧
        RingHom.Finite (A := Analytic.Conv K d) (B := Analytic.Conv K n ⧸ I)
          (normMap K I e L : Analytic.Conv K d →+* Analytic.Conv K n ⧸ I)) ↔
      ringKrullDim (Analytic.Conv K n ⧸ I) = d := by
  constructor
  · rintro ⟨e, L, hinj, hfin⟩
    exact ringKrullDim_quotient_eq_of_normMap K I hI e L hinj hfin
  · intro hd
    obtain ⟨d', e, L, hinj, hfin⟩ := exists_noetherNormalization_analytic I hI
    have h := (ringKrullDim_quotient_eq_of_normMap K I hI e L hinj hfin).symm.trans hd
    have hdd : d' = d := by exact_mod_cast h
    subst hdd
    exact ⟨e, L, hinj, hfin⟩

/-- `dim (𝒪_n/I) ≤ n`. -/
theorem ringKrullDim_quotient_le_natCast {n : ℕ} (I : Ideal (Analytic.Conv K n)) :
    ringKrullDim (Analytic.Conv K n ⧸ I) ≤ (n : WithBot ℕ∞) :=
  (ringKrullDim_quotient_le I).trans_eq (ringKrullDim_conv K n)

/-- `dim (𝒪_n/I) = n` iff `I = 0` ([Fre17, II 5.11] for `X = Kⁿ`): a nonzero ideal of the Noetherian
local domain `𝒪_n` drops the dimension (`Ideal.eq_bot_of_ringKrullDim_quotient_eq`). -/
theorem ringKrullDim_quotient_eq_natCast_iff {n : ℕ} (I : Ideal (Analytic.Conv K n)) (hI : I ≠ ⊤) :
    ringKrullDim (Analytic.Conv K n ⧸ I) = (n : WithBot ℕ∞) ↔ I = ⊥ := by
  constructor
  · intro h
    exact Ideal.eq_bot_of_ringKrullDim_quotient_eq (IsLocalRing.le_maximalIdeal hI)
      (h.trans (ringKrullDim_conv K n).symm)
  · rintro rfl
    exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (Analytic.Conv K n))).trans
      (ringKrullDim_conv K n)

/-- `(S) = 0` iff `V(S)` is a neighbourhood of `0` — the identity theorem
`Conv.ext_of_evalSeries_eventuallyEq`. -/
theorem span_eq_bot_iff_eventually_mem_zeroSet {n : ℕ} (S : Finset (Analytic.Conv K n)) :
    Ideal.span (S : Set (Analytic.Conv K n)) = ⊥ ↔ ∀ᶠ x in 𝓝 (0 : Fin n → K), x ∈ zeroSet S := by
  rw [Ideal.span_eq_bot]
  simp only [mem_zeroSet_iff, Finset.mem_coe]
  rw [Filter.eventually_all_finset]
  refine forall₂_congr fun g _ => ?_
  constructor
  · rintro rfl
    exact Eventually.of_forall fun x => by simp
  · intro h
    refine Conv.ext_of_evalSeries_eventuallyEq ?_
    filter_upwards [h] with x hx
    rw [hx, Subalgebra.coe_zero, evalSeries_zero]

end AnalyticSpace

end
