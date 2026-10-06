/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Pullback
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.Globalization
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Stalks along a coproduct of open immersions

The local cover `g : X' → X` of [Kol07, Theorem 105] (the globalization of blow-up sequences: the
run of the order reduction `BO_{n,1}` is assembled from runs on the pieces of an open cover through
the coproduct of the inclusions) is a coproduct of open immersions (`openImmersionCoprods`), so its
stalk maps are isomorphisms, and so are those of its stage lifts along a blow-up sequence (base
change, `isPullback_pullbackStageHom`). A stalkwise identity of pulled-back ideal sheaves descends
along such a map (`stalkIdeal_comap`), and the reduced ideal of the closure of a point specializing
to `q` agrees at `q` with the pullback of the reduced ideal of the closure of its image when that
pullback's support has the point as a generic point (a minimal prime over a prime is that prime).
Bookkeeping for the descent of the local form of the ideal along the local cover
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimCover`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Cover`).
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

variable {X Y : Scheme.{u}}

/-- The stalk maps of a coproduct of open immersions are isomorphisms: at `y = ι i u`, the stalk
map of the open immersion `ι i ≫ g` factors through that of the open immersion `ι i`. -/
theorem openImmersionCoprods.isIso_stalkMap {g : Y ⟶ X} (hg : openImmersionCoprods g) (y : Y) :
    IsIso (g.stalkMap y) := by
  obtain ⟨σ, U, ι, hc, hι⟩ := hg
  obtain ⟨i, u, rfl⟩ := exists_eq_of_isColimit_cofan ι hc y
  have hoι : IsOpenImmersion (ι i) := isOpenImmersion_of_isColimit_cofan ι hc i
  have hoc : IsOpenImmersion (ι i ≫ g) := hι i
  have h1 : IsIso ((ι i ≫ g).stalkMap u) := inferInstance
  have hιiso : IsIso ((ι i).stalkMap u) := inferInstance
  have h2 : IsIso (g.stalkMap (ι i u) ≫ (ι i).stalkMap u) := by
    rwa [← Scheme.Hom.stalkMap_comp]
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g.stalkMap (ι i u)) ((ι i).stalkMap u) hιiso h2

/-- The stage lifts of a coproduct of open immersions along a blow-up sequence are coproducts of
open immersions (the class is stable under base change, and the stage lifts are base changes). -/
theorem openImmersionCoprods_pullbackStageHom (S : BlowUpSequence X) {g : Y ⟶ X}
    (hg : openImmersionCoprods g) (i : Fin (S.length + 1)) :
    openImmersionCoprods (S.pullbackStageHom g i) := by
  have := Hironaka.Sequence.openImmersionCoprods.flat hg
  have := isStableUnderBaseChange_openImmersionCoprods
  exact property_of_isPullback _ (isPullback_pullbackStageHom S g i) hg

/-- A stalkwise identity of two pull-backs descends along a morphism whose stalk map at the point
is an isomorphism. -/
theorem stalkIdeal_eq_of_comap_eq_of_isIso_stalkMap (φ : Y ⟶ X) {A B : X.IdealSheafData} {q : Y}
    [IsIso (φ.stalkMap q)] (h : (A.comap φ).stalkIdeal q = (B.comap φ).stalkIdeal q) :
    A.stalkIdeal (φ q) = B.stalkIdeal (φ q) := by
  rw [IdealSheafData.stalkIdeal_comap, IdealSheafData.stalkIdeal_comap] at h
  have hbij : Function.Bijective (φ.stalkMap q).hom :=
    (asIso (φ.stalkMap q)).commRingCatIsoToRingEquiv.bijective
  have := congrArg (Ideal.comap (φ.stalkMap q).hom) h
  rwa [Ideal.comap_map_of_bijective _ hbij, Ideal.comap_map_of_bijective _ hbij] at this

/-- The stalk of the reduced ideal of the closure of `η` at a point `x` it specializes to is
prime: it is a minimal prime over itself (`stalkIdeal_vanishingIdeal_mem_minimalPrimes`). -/
theorem isPrime_stalkIdeal_vanishingIdeal_closure {η x : X} (hηx : η ⤳ x) :
    ((IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x).IsPrime :=
  (stalkIdeal_vanishingIdeal_mem_minimalPrimes (IdealSheafData.vanishingIdeal (Closeds.closure
      {η})) (by
      rw [Hironaka.Sequence.support_vanishingIdeal_eq]
      exact ⟨subset_closure (Set.mem_singleton η),
        fun ζ hζ hsp => (hsp.antisymm (specializes_iff_mem_closure.mpr hζ)).eq⟩) hηx).1.1

/-- The stalk at `q` of the pull-back of the reduced ideal of `closure {φ ζ}` along `φ` with an
isomorphic stalk map at `q` is the stalk of the reduced ideal of `closure {ζ}`, provided `ζ` is a
generic point of the pull-back's support: the latter is a minimal prime over the former, which is
prime (the image of a prime under an isomorphism). -/
theorem stalkIdeal_comap_vanishingIdeal_closure_eq (φ : Y ⟶ X) {ζ q : Y} (hζq : ζ ⤳ q)
    [IsIso (φ.stalkMap q)]
    (hgen : ζ ∈ ((IdealSheafData.vanishingIdeal (Closeds.closure
        {φ ζ})).comap φ).support.genericPoints) :
    ((IdealSheafData.vanishingIdeal (Closeds.closure {φ ζ})).comap φ).stalkIdeal q =
      (IdealSheafData.vanishingIdeal (Closeds.closure {ζ})).stalkIdeal q := by
  have hmin := stalkIdeal_vanishingIdeal_mem_minimalPrimes
    ((IdealSheafData.vanishingIdeal (Closeds.closure {φ ζ})).comap φ) hgen hζq
  have hprime : (((IdealSheafData.vanishingIdeal (Closeds.closure
      {φ ζ})).comap φ).stalkIdeal q).IsPrime := by
    rw [IdealSheafData.stalkIdeal_comap]
    have := isPrime_stalkIdeal_vanishingIdeal_closure (hζq.map φ.continuous)
    have hbij : Function.Bijective (φ.stalkMap q).hom :=
      (asIso (φ.stalkMap q)).commRingCatIsoToRingEquiv.bijective
    refine Ideal.map_isPrime_of_surjective hbij.2 ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hbij.1]
    exact bot_le
  rw [Ideal.minimalPrimes_eq_subsingleton_self] at hmin
  exact (Set.mem_singleton_iff.mp hmin).symm

end Hironaka.Resolution
