/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.CenterList
public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The pull-back of a list of centres, stage by stage

For a list of centres `L` on `M` and a local analytic isomorphism `h : N → M`,
`BlowUpSequence.pullback` is the list of the preimage centres under the successive lifts
`h_i : N_i → M_i` (`pullbackLiftAux`), the pull-back of a blow-up sequence along a smooth
morphism [Kol07, Definition 30, 30.1]. This file records, by induction on the list, what the
succession of `h^* L` carries at each stage in terms of `L`'s data pulled back along the lifts:

* the lifts are local analytic isomorphisms, surjective when `h` is
  (`isLocalDiffeomorph_pullbackLiftAux`, `surjective_pullbackLiftAux`);
* the centres (`center_pullbackAux`), the weak transforms (`weakTransformSeqAux_pullback`), the
  boundaries (`boundarySeqAux_pullback`, along a surjective `h`: Hironaka's reduced transform is
  natural along surjective local isomorphisms, `reducedTransform_comap_liftStep`) and, along a
  sequence of order `≥ m` for `(I, m)`, the marked transforms (`markedTransformSeqAux_pullback`,
  the marking being legitimate at every stage), each the `comap` along the lift of the datum on
  `L`;
* **the descent of [Kol07, Definition 66]** (`isOfOrderGe_of_pullback`): if `h^* L` is a smooth
blow-up sequence of order `≥ m` for `(h^* I, m, h^* E)` [Kol07, Definition 66] and `h` is
surjective, then `L` is one for `(I, m, E)`: stage by stage, the normal-crossings clause and the
order clause come back along the bijective germ maps
  (`Hironaka.Resolution.Analytic.Functor.PullbackTransport`), the marking of the first transform
  being legitimate once the order clause at stage `0` is known.

This is how the clauses of the descended functor are read on the pull-back to the cover in the
global case of the proof of [Kol07, Theorem 103] (the functoriality package is local, as the
proof remarks at the end of its local case).
-/

public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The lifts -/

/-- The lifts of a local analytic isomorphism to the stages are local analytic isomorphisms. -/
theorem isLocalDiffeomorph_pullbackLiftAux : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (i : ℕ) (hi : i < L.length + 1) (hi' : i < (L.pullback h hh).length + 1),
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (L.pullbackLiftAux h hh i hi hi')
  | _, _, nil _, _, hh, 0, _, _ => hh
  | _, _, cons _ _, _, hh, 0, _, _ => hh
  | _, _, cons hY rest, h, hh, i + 1, hi, hi' =>
    isLocalDiffeomorph_pullbackLiftAux rest (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)
      i (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hi')
  | _, _, nil _, _, _, i + 1, hi, _ => absurd hi (by change ¬ i + 1 < 0 + 1; omega)

/-- The lifts of a surjective local analytic isomorphism to the stages are surjective
(`surjective_liftStep` at each step). -/
theorem surjective_pullbackLiftAux : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h), Function.Surjective h →
    ∀ (i : ℕ) (hi : i < L.length + 1) (hi' : i < (L.pullback h hh).length + 1),
    Function.Surjective (L.pullbackLiftAux h hh i hi hi')
  | _, _, nil _, _, _, hs, 0, _, _ => hs
  | _, _, cons _ _, _, _, hs, 0, _, _ => hs
  | _, _, cons hY rest, h, hh, hs, i + 1, hi, hi' =>
    surjective_pullbackLiftAux rest (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)
      (surjective_liftStep h hh hY hs) i (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hi')
  | _, _, nil _, _, _, _, i + 1, hi, _ => absurd hi (by change ¬ i + 1 < 0 + 1; omega)

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- The lift `h_i : N_i → M_i` of a
local analytic isomorphism to the stage `i` is a local analytic isomorphism. -/
theorem isLocalDiffeomorph_pullbackLift (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (i : Fin (L.length + 1)) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (L.pullbackLift h hh i) :=
  isLocalDiffeomorph_pullbackLiftAux L h hh i.1 i.2 _

/-- The lifts of a surjective local analytic isomorphism are surjective. -/
theorem surjective_pullbackLift (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hs : Function.Surjective h)
    (i : Fin (L.length + 1)) : Function.Surjective (L.pullbackLift h hh i) :=
  surjective_pullbackLiftAux L h hh hs i.1 i.2 _

/-! ### The stages of the pull-back -/

/-- The centres of `h^* L` are the pull-backs of the centres of `L` along the lifts. -/
theorem center_pullbackAux : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (i : ℕ) (hi : i < L.length) (hi' : i < (L.pullback h hh).length),
    (L.pullback h hh).toSuccession.center ⟨i, hi'⟩ =
      Manifold.IdealSheaf.pullback _ (L.pullbackLiftAux h hh i (Nat.lt_succ_of_lt hi)
          (Nat.lt_succ_of_lt hi')).contMDiff
        (L.toSuccession.center ⟨i, hi⟩)
  | _, _, nil _, _, _, i, hi, _ => absurd hi (by change ¬ i < 0; omega)
  | _, _, cons hY rest, h, hh, 0, _, _ =>
    have : FiniteDimensional 𝕜 E := ψ₀.symm.toLinearEquiv.finiteDimensional
    (comap_idealSheaf_of_isLocalDiffeomorph ψ₀ h hh hY).symm
  | _, _, cons hY rest, h, hh, i + 1, hi, hi' =>
    center_pullbackAux rest (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY) i
      (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hi')

/-- The weak transforms along `h^* L` are the pull-backs of the weak transforms along `L`
(`weakTransform_comap_liftStep` at each step). -/
theorem weakTransformSeqAux_pullback :
    ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (J : IdealSheaf M) (i : ℕ) (hi : i < L.length + 1)
    (hi' : i < (L.pullback h hh).length + 1),
    (L.pullback h hh).toSuccession.weakTransformSeqAux (J.pullback h h.contMDiff)
        i hi' =
      (L.toSuccession.weakTransformSeqAux J i hi).pullback _ (L.pullbackLiftAux h hh i hi
          hi').contMDiff
  | _, _, nil _, _, _, _, 0, _, _ => rfl
  | _, _, cons _ _, _, _, _, 0, _, _ => rfl
  | _, _, cons hY rest, h, hh, J, i + 1, hi, hi' => by
    have : FiniteDimensional 𝕜 E := ψ₀.symm.toLinearEquiv.finiteDimensional
    revert hi hi'
    change ∀ (hi : i + 1 < (FiniteSuccession.cons ψ₀ hY rest.toSuccession).length + 1)
      (hi' : i + 1 < (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).length + 1),
      (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).weakTransformSeqAux
        (J.pullback h h.contMDiff) (i + 1) hi' =
      Manifold.IdealSheaf.pullback _ (rest.pullbackLiftAux (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY) i (Nat.lt_of_succ_lt_succ hi)
          (Nat.lt_of_succ_lt_succ hi')).contMDiff
        ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).weakTransformSeqAux J (i + 1) hi)
    intro hi hi'
    rw [FiniteSuccession.cons_weakTransformSeqAux_succ,
      FiniteSuccession.cons_weakTransformSeqAux_succ, ← weakTransform_comap_liftStep h hh hY J]
    exact weakTransformSeqAux_pullback rest _ _ _ i _ _
  | _, _, nil _, _, _, _, i + 1, hi, _ => absurd hi (by change ¬ i + 1 < 0 + 1; omega)

/-- The boundaries along `h^* L`, for a SURJECTIVE `h`, are the pull-backs of the boundaries along
`L` (`reducedTransform_comap_liftStep` at each step). -/
theorem boundarySeqAux_pullback : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    Function.Surjective h →
        ∀ (E₀ : IdealSheaf M) (i : ℕ) (hi : i < L.length + 1)
    (hi' : i < (L.pullback h hh).length + 1),
    (L.pullback h hh).toSuccession.boundarySeqAux (E₀.pullback h h.contMDiff) i
        hi' =
      (L.toSuccession.boundarySeqAux E₀ i hi).pullback _ (L.pullbackLiftAux h hh i hi hi').contMDiff
  | _, _, nil _, _, _, _, _, 0, _, _ => rfl
  | _, _, cons _ _, _, _, _, _, 0, _, _ => rfl
  | _, _, cons hY rest, h, hh, hs, E₀, i + 1, hi, hi' => by
    have : FiniteDimensional 𝕜 E := ψ₀.symm.toLinearEquiv.finiteDimensional
    revert hi hi'
    change ∀ (hi : i + 1 < (FiniteSuccession.cons ψ₀ hY rest.toSuccession).length + 1)
      (hi' : i + 1 < (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).length + 1),
      (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).boundarySeqAux
        (E₀.pullback h h.contMDiff) (i + 1) hi' =
      Manifold.IdealSheaf.pullback _ (rest.pullbackLiftAux (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY) i (Nat.lt_of_succ_lt_succ hi)
          (Nat.lt_of_succ_lt_succ hi')).contMDiff
        ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).boundarySeqAux E₀ (i + 1) hi)
    intro hi hi'
    rw [FiniteSuccession.cons_boundarySeqAux_succ, FiniteSuccession.cons_boundarySeqAux_succ,
      ← reducedTransform_comap_liftStep h hh hY hs E₀]
    exact boundarySeqAux_pullback rest _ _ (surjective_liftStep h hh hY hs) _ i _ _
  | _, _, nil _, _, _, _, _, i + 1, hi, _ => absurd hi (by change ¬ i + 1 < 0 + 1; omega)

/-- Along a sequence of order `≥ m` for `(I, m, E₀)`, the marked transforms along `h^* L` are the
pull-backs of the marked transforms along `L` (`birationalTransform_comap_liftStep` at each step;
the marking is legitimate by the order clause of [Kol07, Definition 66] at that step). -/
theorem markedTransformSeqAux_pullback :
    ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (I E₀ : IdealSheaf M)
        (m : ℕ),
    L.toSuccession.IsOfOrderGe I m E₀ →
    ∀ (i : ℕ) (hi : i < L.length + 1) (hi' : i < (L.pullback h hh).length + 1),
    (L.pullback h hh).toSuccession.markedTransformSeqAux
        (I.pullback h h.contMDiff) m i
        hi' =
      (L.toSuccession.markedTransformSeqAux I m i hi).pullback _ (L.pullbackLiftAux h hh i hi
          hi').contMDiff
  | _, _, nil _, _, _, _, _, _, _, 0, _, _ => rfl
  | _, _, cons _ _, _, _, _, _, _, _, 0, _, _ => rfl
  | _, _, cons hY rest, h, hh, I, E₀, m, hge, i + 1, hi, hi' => by
    have : FiniteDimensional 𝕜 E := ψ₀.symm.toLinearEquiv.finiteDimensional
    revert hi hi'
    change ∀ (hi : i + 1 < (FiniteSuccession.cons ψ₀ hY rest.toSuccession).length + 1)
      (hi' : i + 1 < (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).length + 1),
      (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).markedTransformSeqAux
        (I.pullback h h.contMDiff) m (i + 1) hi' =
      Manifold.IdealSheaf.pullback _ (rest.pullbackLiftAux (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY) i (Nat.lt_of_succ_lt_succ hi)
          (Nat.lt_of_succ_lt_succ hi')).contMDiff
        ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).markedTransformSeqAux I m (i + 1) hi)
    intro hi hi'
    obtain ⟨⟨-, hm⟩, hrest⟩ := (FiniteSuccession.isOfOrderGe_cons_iff (I := I) (m := m) (E₀ := E₀)
      hY rest.toSuccession).mp hge
    rw [FiniteSuccession.cons_markedTransformSeqAux_succ (hY.preimage_of_isLocalDiffeomorph hh) _ _
        m i,
      FiniteSuccession.cons_markedTransformSeqAux_succ hY rest.toSuccession I m i]
    have e1 : (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).markedTransformSeq
          (I.pullback h h.contMDiff) m
              (Fin.succ (0 : Fin ((rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession.length + 1))) =
        ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).markedTransformSeq I m
            (Fin.succ (0 : Fin (rest.toSuccession.length + 1)))).pullback _ (liftStep h hh
                hY).contMDiff := by
      rw [FiniteSuccession.cons_markedTransformSeq_one,
        FiniteSuccession.cons_markedTransformSeq_one]
      exact (birationalTransform_comap_liftStep h hh hY ⟨I, m⟩ hm).symm
    rw [show (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).markedTransformSeqAux
          (I.pullback h h.contMDiff) m 1 (Nat.succ_lt_succ (Nat.succ_pos _)) =
        ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).markedTransformSeqAux I m 1
            (Nat.succ_lt_succ (Nat.succ_pos _))).pullback _ (liftStep h hh hY).contMDiff from e1]
    exact markedTransformSeqAux_pullback rest _ _ _ _ m hrest i _ _
  | _, _, nil _, _, _, _, _, _, _, i + 1, hi, _ => absurd hi (by change ¬ i + 1 < 0 + 1; omega)

/-! ### The stages of the pull-back, indexed by `Fin`, along the lifts `pullbackLift` -/

/-- The centres of `h^* L` along the lifts (`Fin`-indexed form of `center_pullbackAux`). -/
theorem center_pullback (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (i : Fin L.length) :
    (L.pullback h hh).toSuccession.center
        ⟨i.1, Nat.lt_of_lt_of_eq i.2 (length_pullback L h hh).symm⟩ =
      (L.toSuccession.center i).pullback _ (L.pullbackLift h hh i.castSucc).contMDiff :=
  center_pullbackAux L h hh i.1 i.2 _

/-- The weak transforms along `h^* L` along the lifts (`Fin`-indexed form of
`weakTransformSeqAux_pullback`). -/
theorem weakTransformSeq_pullback (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (J : IdealSheaf M) (i : Fin (L.length + 1)) :
    (L.pullback h hh).toSuccession.weakTransformSeq (J.pullback h h.contMDiff)
        ⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩ =
      (L.toSuccession.weakTransformSeq J i).pullback _ (L.pullbackLift h hh i).contMDiff :=
  weakTransformSeqAux_pullback L h hh J i.1 i.2 _

/-- The boundaries along `h^* L`, for a surjective `h`, along the lifts (`Fin`-indexed form of
`boundarySeqAux_pullback`). -/
theorem boundarySeq_pullback (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hs : Function.Surjective h)
    (E₀ : IdealSheaf M) (i : Fin (L.length + 1)) :
    (L.pullback h hh).toSuccession.boundarySeq (E₀.pullback h h.contMDiff)
        ⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩ =
      (L.toSuccession.boundarySeq E₀ i).pullback _ (L.pullbackLift h hh i).contMDiff :=
  boundarySeqAux_pullback L h hh hs E₀ i.1 i.2 _

/-- The marked transforms along `h^* L`, for `L` of order `≥ m` for `(I, m, E₀)`, along the lifts
(`Fin`-indexed form of `markedTransformSeqAux_pullback`). -/
theorem markedTransformSeq_pullback (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (I E₀ : IdealSheaf M) (m : ℕ)
    (hge : L.toSuccession.IsOfOrderGe I m E₀) (i : Fin (L.length + 1)) :
    (L.pullback h hh).toSuccession.markedTransformSeq (I.pullback h h.contMDiff) m
        ⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩ =
      (L.toSuccession.markedTransformSeq I m i).pullback _ (L.pullbackLift h hh i).contMDiff :=
  markedTransformSeqAux_pullback L h hh I E₀ m hge i.1 i.2 _

/-! ### The descent of [Kol07, Definition 66] -/

/-- **[Kol07, Definition 66] descends along a surjective local analytic isomorphism**: if `h^* L`
is a smooth blow-up sequence of order `≥ m` for `(h^* I, m, h^* E₀)` and `h` is surjective, then
`L` is one for `(I, m, E₀)`. Stage by stage: the normal-crossings clause and the order clause at
the first centre come back along the bijective germ maps
(`HasOnlyNormalCrossingsWith.of_comap_of_surjective`,
`ordAlongIdeal_comap_of_isLocalDiffeomorphAt`, every point of the centre having a preimage), and
the tail of `h^* L` is the pull-back of the tail of `L` along the surjective lift, for the first
marked transform and the first boundary (`birationalTransform_comap_liftStep` — the marking being
legitimate by the order clause just obtained — and `reducedTransform_comap_liftStep`). -/
theorem isOfOrderGe_of_pullback : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    Function.Surjective h → ∀ (I E₀ : IdealSheaf M) (m : ℕ),
    (L.pullback h hh).toSuccession.IsOfOrderGe (I.pullback h h.contMDiff) m
      (E₀.pullback h h.contMDiff) →
    L.toSuccession.IsOfOrderGe I m E₀
  | _, _, nil _, _, _, _, I, E₀, m, _ => FiniteSuccession.isOfOrderGe_nil I E₀ m
  | _, _, @cons _ _ _ _ _ _ _ _ Y _ hY rest, h, hh, hs, I, E₀, m, hge' => by
    have : FiniteDimensional 𝕜 E := ψ₀.symm.toLinearEquiv.finiteDimensional
    obtain ⟨⟨hnc', hm'⟩, hrest'⟩ := (FiniteSuccession.isOfOrderGe_cons_iff
      (I := I.pullback h h.contMDiff) (m := m)
          (E₀ := E₀.pullback h h.contMDiff)
      (hY.preimage_of_isLocalDiffeomorph hh)
      (rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).mp hge'
    have hnc : E₀.HasOnlyNormalCrossingsWith hY.idealSheaf := by
      refine HasOnlyNormalCrossingsWith.of_comap_of_surjective h hh hs ?_
      rwa [comap_idealSheaf_of_isLocalDiffeomorph ψ₀ h hh hY]
    have hm : ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a := by
      intro a ha
      obtain ⟨b, rfl⟩ := hs a
      have := hm' b ha
      rwa [← comap_idealSheaf_of_isLocalDiffeomorph ψ₀ h hh hY,
        IdealSheaf.ordAlongIdeal_comap_of_isLocalDiffeomorphAt h _ _ (hh b)] at this
    refine (FiniteSuccession.isOfOrderGe_cons_iff (I := I) (m := m) (E₀ := E₀) hY
      rest.toSuccession).mpr ⟨⟨hnc, hm⟩, ?_⟩
    refine isOfOrderGe_of_pullback rest (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)
      (surjective_liftStep h hh hY hs) _ _ m ?_
    have e1 : (FiniteSuccession.cons ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)
            (rest.pullback (liftStep h hh hY)
              (isLocalDiffeomorph_liftStep h hh hY)).toSuccession).markedTransformSeq
          (I.pullback h h.contMDiff) m
              (Fin.succ (0 : Fin ((rest.pullback (liftStep h hh hY)
            (isLocalDiffeomorph_liftStep h hh hY)).toSuccession.length + 1))) =
        ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).markedTransformSeq I m
            (Fin.succ (0 : Fin (rest.toSuccession.length + 1)))).pullback _ (liftStep h hh
                hY).contMDiff := by
      rw [FiniteSuccession.cons_markedTransformSeq_one,
        FiniteSuccession.cons_markedTransformSeq_one]
      exact (birationalTransform_comap_liftStep h hh hY ⟨I, m⟩ hm).symm
    rw [e1, ← reducedTransform_comap_liftStep h hh hY hs E₀] at hrest'
    exact hrest'

/-! ### Transfer of the clauses along an equality of lists -/

/-- The output clause of [Kol07, Theorem 103, (1)] transfers along an equality of lists (the points
of the last stage are transported by `subst`). -/
theorem forall_last_ord_lt_of_eq {L₁ L₂ : BlowUpSequence ψ₀ N} (e : L₁ = L₂)
    (I : IdealSheaf N) (m : ℕ)
    (H : ∀ x : L₁.toSuccession.stage (Fin.last _),
      (L₁.toSuccession.weakTransformSeq I (Fin.last _)).ord x < (m : ℕ∞)) :
    ∀ x : L₂.toSuccession.stage (Fin.last _),
      (L₂.toSuccession.weakTransformSeq I (Fin.last _)).ord x < (m : ℕ∞) := by
  subst e
  exact H

/-- The output clause at the last stage, read at any index `k` provably equal to the length. -/
theorem ord_lt_of_forall_last {L : BlowUpSequence ψ₀ N} (I : IdealSheaf N) (m : ℕ)
    (H : ∀ x : L.toSuccession.stage (Fin.last _),
      (L.toSuccession.weakTransformSeq I (Fin.last _)).ord x < (m : ℕ∞))
    (k : ℕ) (hk : k < L.length + 1) (e : k = L.length)
    (y : finStages N L.toSuccession.later ⟨k, hk⟩) :
    (L.toSuccession.weakTransformSeqAux I k hk).ord y < (m : ℕ∞) := by
  subst e
  exact H y

end AnalyticManifold.BlowUpSequence

end
