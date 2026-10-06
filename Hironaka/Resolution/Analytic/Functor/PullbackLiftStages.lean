/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
import Hironaka.Resolution.Analytic.Functor.LocalIsoTools
public import Hironaka.Resolution.Analytic.Functor.PullbackSequence
import Hironaka.Resolution.Analytic.Restrict.DiffeomorphTransport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The stage lifts of a pull-back, stage by stage

For a list of centres `L` on `M` and a local analytic isomorphism `h : N → M`, the stages of the
pull-back `h^* L` come with the lifts `h_i : N_i → M_i` (`pullbackLift`), the squares
`π ∘ h_{i+1} = h_i ∘ π'` of [Kol07, Definition 30, 30.1]. The lifts are local analytic
isomorphisms, surjective when `h` is, and the centres of `h^* L` are the preimages of those of `L`
under them (`Hironaka.Resolution.Analytic.Functor.PullbackSequence`); the last-stage lift lies
over `h` and has range `(σ^r)⁻¹(range h)` (`stageMap_last_pullbackLiftLast`,
`range_pullbackLiftLast`). This module states the same facts at every stage: over `h`
(`stageMap_pullbackLift`), intertwining the blow-downs (`map_pullbackLift`), injective when `h` is
(`injective_pullbackLift`), range `(σ^i)⁻¹(range h)` (`range_pullbackLift`); and, for an injective
`h`, the lift corestricted onto its range is a diffeomorphism onto the open submanifold
`(σ^i)⁻¹(range h)` of the stage (`pullbackLiftDiffeomorph`, by Mathlib's
`IsLocalDiffeomorph.toDiffeomorphOfBijective`). Through these diffeomorphisms the restriction of a
succession to an open `U₁ ⊆ U₂` ([Wlo09, Theorem 2.0.3, (4)]) is identified with the pull-back
along the open inclusion. The proofs are by recursion on the list, the pattern of
`stageMap_last_pullbackLiftLast` and `injective_pullbackLiftLast`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The stage lift at stage `0` is `h` itself (the `ℕ`-indexed form of `pullbackLift_zero`). -/
theorem pullbackLiftAux_zero {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hi : 0 < L.length + 1) (hi' : 0 < (L.pullback h hh).length + 1) :
    L.pullbackLiftAux h hh 0 hi hi' = h := by
  cases L <;> rfl

/-- The stage lifts lie over `h`: `σ^i ∘ h_i = h ∘ σ'^i`, `ℕ`-indexed (the stage-wise form of
`stageMap_last_pullbackLiftLast`). -/
theorem stageMapAux_pullbackLiftAux : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (i : ℕ)
    (hi : i < L.length + 1) (hi' : i < (L.pullback h hh).length + 1)
    (q : finStages N (L.pullback h hh).toSuccession.later ⟨i, hi'⟩),
    L.toSuccession.stageMapAux i hi (L.pullbackLiftAux h hh i hi hi' q) =
      h ((L.pullback h hh).toSuccession.stageMapAux i hi' q)
  | _, _, nil _, _, _, 0, _, _, _ => rfl
  | _, _, cons _ _, _, _, 0, _, _, _ => rfl
  | _, _, cons hY rest, h, hh, i + 1, hi, hi', q => by
    have ih := stageMapAux_pullbackLiftAux rest (liftStep h hh hY)
      (isLocalDiffeomorph_liftStep h hh hY) i (Nat.lt_of_succ_lt_succ hi)
      (Nat.lt_of_succ_lt_succ hi') q
    have h1 := stageMapAux_cons_succ hY rest i hi
      (rest.pullbackLiftAux (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY) i
        (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hi') q)
    have h2 := stageMapAux_cons_succ (hY.preimage_of_isLocalDiffeomorph hh)
      (rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)) i hi' q
    change (cons hY rest).toSuccession.stageMapAux (i + 1) hi
        (rest.pullbackLiftAux (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY) i
          (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hi') q) =
      h ((cons (hY.preimage_of_isLocalDiffeomorph hh)
        (rest.pullback (liftStep h hh hY)
          (isLocalDiffeomorph_liftStep h hh hY))).toSuccession.stageMapAux (i + 1) hi' q)
    rw [h1, h2]
    erw [ih]
    rw [blowUpπ_liftStep]
  | _, _, nil _, _, _, i + 1, hi, _, _ => absurd hi (by change ¬ i + 1 < 0 + 1; omega)

/-- The stage lifts intertwine the blow-downs, `ℕ`-indexed: `h_i ∘ π'_{i+1} = π_{i+1} ∘ h_{i+1}`
(`blowUpπ_liftStep` along the list). -/
theorem pullbackLiftAux_map : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (i : ℕ)
    (hi : i < L.length) (hi' : i < (L.pullback h hh).length)
    (q : (L.pullback h hh).toSuccession.stage ⟨i + 1, Nat.succ_lt_succ hi'⟩),
    L.pullbackLiftAux h hh i (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hi')
        ((L.pullback h hh).toSuccession.map ⟨i, hi'⟩ q) =
      L.toSuccession.map ⟨i, hi⟩
        (L.pullbackLiftAux h hh (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hi') q)
  | _, _, nil _, _, _, i, hi, _, _ => absurd hi (by change ¬ i < 0; omega)
  | _, _, cons hY rest, h, hh, 0, _, _, q => by
    change h (blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh) q) =
      blowUpπ ψ₀ hY (rest.pullbackLiftAux (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)
        0 _ _ q)
    rw [pullbackLiftAux_zero]
    exact (blowUpπ_liftStep h hh hY q).symm
  | _, _, cons hY rest, h, hh, i + 1, hi, hi', q =>
    pullbackLiftAux_map rest (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY) i
      (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hi') q

/-- The stage lifts of an injective `h` are injective, `ℕ`-indexed (`injective_liftStep` along the
list, the pattern of `isLocalDiffeomorph_pullbackLiftAux`). -/
theorem injective_pullbackLiftAux : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h), Function.Injective h →
    ∀ (i : ℕ) (hi : i < L.length + 1) (hi' : i < (L.pullback h hh).length + 1),
    Function.Injective (L.pullbackLiftAux h hh i hi hi')
  | _, _, nil _, _, _, hi, 0, _, _ => hi
  | _, _, cons _ _, _, _, hi, 0, _, _ => hi
  | _, _, cons hY rest, h, hh, hi, i + 1, hi₁, hi' =>
    injective_pullbackLiftAux rest (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)
      (injective_liftStep h hh hY hi) i (Nat.lt_of_succ_lt_succ hi₁) (Nat.lt_of_succ_lt_succ hi')
  | _, _, nil _, _, _, _, i + 1, hi₁, _ => absurd hi₁ (by change ¬ i + 1 < 0 + 1; omega)

variable {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)

/-- [Kol07, Definition 30, 30.1]: **the stage lifts lie over `h`**, `σ^i ∘ h_i = h ∘ σ'^i`. -/
theorem stageMap_pullbackLift (i : Fin (L.length + 1))
    (q : (L.pullback h hh).stage ⟨i.1,
      Nat.lt_of_lt_of_eq i.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩) :
    L.toSuccession.stageMap i (L.pullbackLift h hh i q) =
      h ((L.pullback h hh).toSuccession.stageMap
        ⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩ q) :=
  stageMapAux_pullbackLiftAux L h hh i.1 i.2 _ q

/-- [Kol07, Definition 30, 30.1]: **the stage lifts intertwine the blow-downs**,
`h_i ∘ π'_{i+1} = π_{i+1} ∘ h_{i+1}`. -/
theorem map_pullbackLift (i : Fin L.length)
    (q : (L.pullback h hh).stage ⟨i.1 + 1,
      Nat.lt_of_lt_of_eq (Nat.succ_lt_succ i.2) (congrArg (· + 1) (length_pullback L h hh).symm)⟩) :
    L.pullbackLift h hh i.castSucc
        ((L.pullback h hh).toSuccession.map
          ⟨i.1, Nat.lt_of_lt_of_eq i.2 (length_pullback L h hh).symm⟩ q) =
      L.toSuccession.map i (L.pullbackLift h hh i.succ q) :=
  pullbackLiftAux_map L h hh i.1 i.2 _ q

/-- [Kol07, Definition 30, 30.1] (the printed sentence is the surjective case): **the
stage lifts of an injective local analytic isomorphism are injective**. -/
theorem injective_pullbackLift (hi : Function.Injective h) (i : Fin (L.length + 1)) :
    Function.Injective (L.pullbackLift h hh i) :=
  injective_pullbackLiftAux L h hh hi i.1 i.2 _

/-- [Kol07, Definition 30, 30.1]: **the range of the stage lift `h_i` is the preimage of the range
of `h` under the composite blow-down `σ^i`** (the stage-wise form of `range_pullbackLiftLast`: `⊆`
from `stageMap_pullbackLift`, `⊇` is `mem_range_pullbackLift_of_stageMap_mem`). -/
theorem range_pullbackLift (i : Fin (L.length + 1)) :
    Set.range (L.pullbackLift h hh i) = ⇑(L.toSuccession.stageMap i) ⁻¹' Set.range h := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨q, rfl⟩
    exact ⟨_, (stageMap_pullbackLift L h hh i q).symm⟩
  · intro p hp
    exact mem_range_pullbackLift_of_stageMap_mem L h hh i.1 i.2 _ p hp

/-- The range of a stage lift lies in every open `V` of the stage carrying the preimage of the
range of `h`. -/
theorem range_pullbackLift_subset (i : Fin (L.length + 1)) {V : Opens (L.stage i)}
    (hV : (V : Set (L.stage i)) = ⇑(L.toSuccession.stageMap i) ⁻¹' Set.range h) :
    Set.range (L.pullbackLift h hh i) ⊆ V := by
  rw [hV, range_pullbackLift]

/-- [Kol07, Definition 30, 30.1] (the lift of an open immersion): **the stage lift of an
injective local analytic isomorphism, corestricted onto its range — an open `V` of the stage with
`V = (σ^i)⁻¹(range h)` — as a diffeomorphism onto that open submanifold**: the corestriction is a
bijective local analytic isomorphism (`isLocalDiffeomorph_corestrict`, `injective_pullbackLift`,
`range_pullbackLift`), hence a diffeomorphism by Mathlib's
`IsLocalDiffeomorph.toDiffeomorphOfBijective`. -/
def pullbackLiftDiffeomorph (hi : Function.Injective h) (i : Fin (L.length + 1))
    (V : Opens (L.stage i))
    (hV : (V : Set (L.stage i)) = ⇑(L.toSuccession.stageMap i) ⁻¹' Set.range h) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E)
      ((L.pullback h hh).stage ⟨i.1,
        Nat.lt_of_lt_of_eq i.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩)
      ((L.stage i).restrict V) ω :=
  (Hironaka.Manifold.isLocalDiffeomorph_corestrict (L.pullbackLift h hh i) V
    (isLocalDiffeomorph_pullbackLift L h hh i)
    (range_pullbackLift_subset L h hh i hV)).toDiffeomorphOfBijective
    ⟨fun a b hab => injective_pullbackLift L h hh hi i (congrArg Subtype.val hab),
      fun v => by
        have hv : v.1 ∈ (V : Set (L.stage i)) := v.2
        rw [hV, ← range_pullbackLift L h hh i] at hv
        obtain ⟨q, hq⟩ := hv
        exact ⟨q, Subtype.ext hq⟩⟩

/-- The diffeomorphism onto the trace is the stage lift, read in the stage. -/
theorem pullbackLiftDiffeomorph_apply (hi : Function.Injective h) (i : Fin (L.length + 1))
    (V : Opens (L.stage i))
    (hV : (V : Set (L.stage i)) = ⇑(L.toSuccession.stageMap i) ⁻¹' Set.range h)
    (q : (L.pullback h hh).stage ⟨i.1,
      Nat.lt_of_lt_of_eq i.2 (congrArg (· + 1) (length_pullback L h hh).symm)⟩) :
    (L.pullbackLiftDiffeomorph h hh hi i V hV q).1 = L.pullbackLift h hh i q :=
  rfl

end AnalyticManifold.BlowUpSequence

end
