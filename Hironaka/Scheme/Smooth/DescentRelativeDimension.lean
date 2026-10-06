/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Descent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.RingTheory.Etale.Descent

/-!
# Smoothness of relative dimension `m` is fpqc local on the base

Smoothness of relative dimension `m` descends along surjective, flat, quasi-compact morphisms of
schemes. For smoothness itself this is [Sta, Tag 02VL] ("the property `f` is smooth is fpqc local
on the base"); the relative dimension is the addition made here. Mathlib descends `Smooth`
through `HasRingHomProperty.descendsAlong_flat`, whose input is the codescent of the ring-hom
property along faithfully flat ring maps (`RingHom.Smooth.codescendsAlong_faithfullyFlat`); the
same route gives the relative dimension once the ring-level codescent is proved, which is the
content of this file.

**Why it holds.** Let `R → S` be faithfully flat and `R → T` a ring map whose base change
`S → S ⊗_R T` is locally standard smooth of relative dimension `n`. Then `S → S ⊗_R T` is smooth,
so `R → T` is smooth (Mathlib's descent of smoothness), hence `T` is covered by basic opens
`T[1/t]` standard smooth over `R`, with `Ω[T[1/t]⁄R]` free of some rank `d`. Base change to
`B = S ⊗_R T[1/t] = (S ⊗_R T)[1/(1 ⊗ t)]`: `Ω[B⁄S] = B ⊗ Ω[T[1/t]⁄R]` is free of rank `d`
(Kähler differentials commute with base change), `B` is nontrivial when `T[1/t]` is (faithful
flatness), and `S → B` is locally standard smooth of relative dimension `n` (localization of the
hypothesis), so on some nontrivial basic open `B[1/v]` the differentials are free of rank `n`
while also being the localization of `Ω[B⁄S]`, free of rank `d`; hence `d = n` and `T[1/t]` is
standard smooth of relative dimension `n` (Mathlib's characterization by the rank of the
differentials for a standard smooth algebra). Discarding the nilpotent `t` (which generate no
part of the unit ideal) gives the cover witnessing `Locally (IsStandardSmoothOfRelativeDimension n)`
for `R → T`.

## Main declarations

* `AlgebraicGeometry.rank_kaehlerDifferential_eq_of_locally`: a nontrivial algebra with free
  Kähler differentials that is locally standard smooth of relative dimension `n` has
  differentials of rank `n`.
* `AlgebraicGeometry.codescendsAlong_locally_isStandardSmoothOfRelativeDimension`: the ring-level
  codescent along faithfully flat maps.
* `AlgebraicGeometry.descendsAlong_smoothOfRelativeDimension`: the scheme statement, used to
  descend the relative dimension of a smooth morphism along an fpqc cover
  (`Hironaka/Scheme/Smooth/ExceptionalDivisorSmooth.lean`).
-/

public section

universe u

open TensorProduct

namespace AlgebraicGeometry

section Rank

variable (S : Type u) [CommRing S] {B : Type u} [CommRing B] [Algebra S B]

/-- The Kähler differentials of `B[1/t]` over `S` are the base change of those of `B`; when the
latter are free, the rank is unchanged. -/
theorem rank_kaehlerDifferential_localizationAway [Nontrivial B] [Module.Free B Ω[B⁄S]] (t : B)
    [Nontrivial (Localization.Away t)] :
    Module.rank (Localization.Away t) Ω[Localization.Away t⁄S] = Module.rank B Ω[B⁄S] := by
  have h := (isLocalizedModule_iff_isBaseChange (Submonoid.powers t) (Localization.Away t)
    (KaehlerDifferential.map S S B (Localization.Away t))).mp inferInstance
  rw [← h.equiv.rank_eq, Module.rank_baseChange, Cardinal.lift_id]

omit [Algebra S B] in
/-- A generating set of the unit ideal of a nontrivial ring contains a non-nilpotent element. -/
theorem exists_not_isNilpotent_of_span_eq_top [Nontrivial B] {s : Set B}
    (hs : Ideal.span s = ⊤) : ∃ t ∈ s, ¬ IsNilpotent t := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have h : Ideal.span s ≤ nilradical B :=
    Ideal.span_le.mpr fun t ht => mem_nilradical.mpr (hcon t ht)
  rw [hs, top_le_iff] at h
  obtain ⟨m, hm⟩ : IsNilpotent (1 : B) := mem_nilradical.mp (h.symm ▸ Submodule.mem_top)
  rw [one_pow] at hm
  exact one_ne_zero hm

omit [Algebra S B] in
/-- `B[1/t]` is nontrivial when `t` is not nilpotent. -/
theorem nontrivial_localizationAway_of_not_isNilpotent {t : B} (ht : ¬ IsNilpotent t) :
    Nontrivial (Localization.Away t) :=
  not_subsingleton_iff_nontrivial.mp fun h =>
    ht ((Submonoid.mem_powers_iff _ _).mp
      ((IsLocalization.subsingleton_iff (M := Submonoid.powers t)
        (S := Localization.Away t)).mp h))

/-- If `S → B` is locally standard smooth of relative dimension `n`, `B` is nontrivial and
`Ω[B⁄S]` is free, then `Ω[B⁄S]` has rank `n`: on a nontrivial basic open `B[1/t]` of the cover the
differentials are free of rank `n` (Mathlib's `rank_kaehlerDifferential`) and are the base change
of `Ω[B⁄S]`. -/
theorem rank_kaehlerDifferential_eq_of_locally [Nontrivial B] [Module.Free B Ω[B⁄S]] (n : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap S B)) :
    Module.rank B Ω[B⁄S] = n := by
  obtain ⟨s, hs, hP⟩ := h
  obtain ⟨t, hts, hnil⟩ := exists_not_isNilpotent_of_span_eq_top hs
  have hnt := nontrivial_localizationAway_of_not_isNilpotent hnil
  have hP' := hP t hts
  beta_reduce at hP'
  rw [← IsScalarTower.algebraMap_eq S B (Localization.Away t),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hP'
  rw [← rank_kaehlerDifferential_localizationAway S t]
  exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n

end Rank

section Codescent

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- `S ⊗[R] T[1/t]` is the localization of `S ⊗[R] T` at `1 ⊗ t`, so a property that holds locally
for `S → S ⊗[R] T` holds locally for `S → S ⊗[R] T[1/t]`. -/
theorem locally_tensorProduct_localizationAway (n : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap S (S ⊗[R] T))) (t : T) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap S (S ⊗[R] Localization.Away t)) := by
  let _ : Algebra (S ⊗[R] T) (S ⊗[R] Localization.Away t) :=
    (Algebra.TensorProduct.map (AlgHom.id R S)
      (IsScalarTower.toAlgHom R T (Localization.Away t))).toAlgebra
  have : IsScalarTower S (S ⊗[R] T) (S ⊗[R] Localization.Away t) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right R S (Submonoid.powers t)
    (Localization.Away t) (by ext; simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers] at hloc
  have hcomp := RingHom.locally_stableUnderCompositionWithLocalizationAwayTarget
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
  have := hcomp (R := S) (S := S ⊗[R] T) (T := S ⊗[R] Localization.Away t)
    (Algebra.TensorProduct.includeRight (R := R) (A := S) t) (algebraMap S (S ⊗[R] T)) h
  rwa [← IsScalarTower.algebraMap_eq] at this

/-- Being locally standard smooth of relative dimension `n` codescends along faithfully flat ring
maps: the ring-level form of the descent ([Sta, Tag 02VL] for smoothness alone, Mathlib's
`RingHom.Smooth.codescendsAlong_faithfullyFlat`). -/
theorem codescendsAlong_locally_isStandardSmoothOfRelativeDimension (n : ℕ) :
    RingHom.CodescendsAlong (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
      RingHom.FaithfullyFlat := by
  refine RingHom.CodescendsAlong.mk _
    (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso) ?_
  intro R S T _ _ _ _ _ hff hloc
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hff
  have hsm : Algebra.Smooth S (S ⊗[R] T) := by
    rw [← RingHom.smooth_algebraMap, RingHom.smooth_iff_locally_isStandardSmooth]
    exact RingHom.locally_of_locally
      (fun h => RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth _ _ h) hloc
  have hT : Algebra.Smooth R T := Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat S
  have hT' : RingHom.Locally RingHom.IsStandardSmooth (algebraMap R T) :=
    RingHom.smooth_iff_locally_isStandardSmooth.mp (RingHom.smooth_algebraMap.mpr hT)
  obtain ⟨s, hs, hsP⟩ := hT'
  refine ⟨{t ∈ s | ¬ IsNilpotent t}, ?_, fun t ht => ?_⟩
  · by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hsub : s ⊆ m := fun t ht => by
      by_cases hnil : IsNilpotent t
      · exact nilradical_le_prime m (mem_nilradical.mpr hnil)
      · exact hle (Ideal.subset_span ⟨ht, hnil⟩)
    exact hm.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hsub))
  · beta_reduce
    rw [← IsScalarTower.algebraMap_eq R T (Localization.Away t),
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    have hst : Algebra.IsStandardSmooth R (Localization.Away t) := by
      have := hsP t ht.1
      beta_reduce at this
      rwa [← IsScalarTower.algebraMap_eq R T (Localization.Away t),
        RingHom.isStandardSmooth_algebraMap] at this
    have hnt : Nontrivial (Localization.Away t) :=
      nontrivial_localizationAway_of_not_isNilpotent ht.2
    rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
    let _ : Algebra (Localization.Away t) (S ⊗[R] Localization.Away t) :=
      Algebra.TensorProduct.rightAlgebra
    have e := KaehlerDifferential.tensorKaehlerEquiv R S (Localization.Away t)
      (S ⊗[R] Localization.Away t)
    have hfree : Module.Free (S ⊗[R] Localization.Away t)
        Ω[S ⊗[R] Localization.Away t⁄S] := Module.Free.of_equiv e
    have hntB : Nontrivial (S ⊗[R] Localization.Away t) :=
      (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right (R := R) (M := S)
        (N := Localization.Away t)).mpr hnt
    have hrank := rank_kaehlerDifferential_eq_of_locally S n
      (locally_tensorProduct_localizationAway n hloc t)
    rw [← e.rank_eq, Module.rank_baseChange, Cardinal.lift_id] at hrank
    exact hrank

end Codescent

section Scheme

open AlgebraicGeometry CategoryTheory

/-- Smoothness of relative dimension `m` descends along surjective, flat, quasi-compact morphisms:
it is fpqc local on the base ([Sta, Tag 02VL] for smoothness alone). Mathlib's `descendsAlong_flat`
applied to the ring-level codescent above. -/
theorem descendsAlong_smoothOfRelativeDimension (m : ℕ) :
    MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension.{u} m)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{u} (n := m)
  HasRingHomProperty.descendsAlong_flat
    (codescendsAlong_locally_isStandardSmoothOfRelativeDimension m)

end Scheme

end AlgebraicGeometry
