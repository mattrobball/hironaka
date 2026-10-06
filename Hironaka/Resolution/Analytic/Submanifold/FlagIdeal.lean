/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Chart.Transport
public import Hironaka.Manifold.FiniteSuccession.Restrict.Restrict
public import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.FiniteSuccession.Restrict.GermRestrict
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Flags of closed submanifolds and their ideal sheaves

Ideal-sheaf bookkeeping along a flag `S ⊂ Y ⊂ M` of closed submanifolds, as in Kollár's reduction
of the functoriality for closed embeddings to the case of a hypersurface [Kol07, 108]: locally
there is a chain of smooth subvarieties `Y = Y_0 ⊂ Y_1 ⊂ ⋯ ⊂ Y_c = X` such that "each is a
hypersurface in the next one".

* `IsClosedSubmanifold.idealSheaf_le_of_subset`: a closed submanifold contained in another has
  the larger reduced ideal sheaf (both have the vanishing stalks, which are antitone in the set);
* `IsClosedSubmanifold.idealSheaf_preimage_of_isLocalDiffeomorph`: the ideal sheaf of the
  preimage of a closed submanifold under a local analytic isomorphism is the pull-back of its ideal
  sheaf (`comap_idealSheaf_of_isLocalDiffeomorph` read backwards; the pull-back of a blow-up centre
  along a smooth morphism, [Kol07, 30.1]);
* `IsAdaptedChart.exists_flag`: from one adapted chart of `S` of codimension `s + 1` whose source
  is the whole manifold, the zero set `Y` of the first `s` adapted coordinates is a closed
  submanifold of codimension `s` containing `S`, and `S` is a hypersurface of the bundled `Y`
  (`IsClosedSubmanifold.preimage_val_of_subset` at codimension `(s + 1) − s`);
* `IsClosedSubmanifold.pullback_idealSheaf_inclusionMap`: the pull-back to the bundled `Y` of the
  reduced ideal sheaf of `S ⊆ Y` is the reduced ideal sheaf of `S` in `Y`, for any
  closed-submanifold structure on `S` in `Y` (the hypothesis `S ⊆ Y` is needed: a hypersurface
  tangent to `Y` is a counterexample);
* `IdealSheaf.isNonzeroEverywhere_pullback_inclusionMap_of_le`: an ideal sheaf `I ⊇ 𝓘_S` whose
  pull-back to `S` is nonzero everywhere pulls back to `Y ⊇ S` nonzero everywhere — off `S` its
  stalk is the unit ideal; at a point of `S`, a zero pull-back to `Y` means every germ of `I` lies
  in the kernel of the germ map of `Y`, the stalk of `𝓘_Y ≤ 𝓘_S`, so the pull-back to `S` is zero
  too (the hypothesis `𝓘_S ≤ I` is needed: an `I` equal to `𝓘_Y` along a component of `Y` missing
  `S` is a counterexample).

Everything is assembled from the reduced ideal sheaf of a closed submanifold (vanishing stalks,
`stalkIdeal_idealSheaf_eq_vanishingStalk`), the germ map of the inclusion (onto, with kernel the
stalk of the reduced ideal, `germMap_inclusionMap`) and the relative closed-submanifold structure
(`IsClosedSubmanifold.preimage_val_of_subset`, `idealSheaf_preimageVal_eq_pullback`). These lemmas
are used for the commutation of the resolution with closed embeddings in general codimension
(`Hironaka/Resolution/Analytic/Functor/ChainClosedEmbeddingChain.lean`).
-/

public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- A closed submanifold contained in another has the larger reduced ideal sheaf (`𝓘_Y ⊆ 𝓘_S`
along the flag of [Kol07, 108]): both have the vanishing stalks, which are antitone in the set. -/
theorem IsClosedSubmanifold.idealSheaf_le_of_subset {Y S : Set M} {c c' : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (hS : IsClosedSubmanifold ψ S c') (hSY : S ⊆ Y) :
    hY.idealSheaf ≤ hS.idealSheaf := by
  rw [IdealSheaf.le_def]
  intro a
  rw [hY.stalkIdeal_idealSheaf_eq_vanishingStalk, hS.stalkIdeal_idealSheaf_eq_vanishingStalk]
  exact vanishingStalk_anti hSY a

/-- The ideal sheaf of the preimage of a closed submanifold under a local analytic isomorphism is
the pull-back of its ideal sheaf ([Kol07, 30.1]): `comap_idealSheaf_of_isLocalDiffeomorph` read
backwards (`comap` is the pull-back by definition). -/
theorem IsClosedSubmanifold.idealSheaf_preimage_of_isLocalDiffeomorph {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) {N : AnalyticManifold.{u} 𝕜 E} (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf = hY.idealSheaf.pullback h h.contMDiff :=
  (comap_idealSheaf_of_isLocalDiffeomorph ψ h hh hY).symm

/-- The flag `S ⊂ Y ⊂ M` from one adapted chart ([Kol07, 108], read from the bottom): from an
adapted chart of `S` (codimension `s + 1`) whose source is the whole manifold, the zero set `Y` of
the first `s` adapted coordinates is a closed submanifold of codimension `s` containing `S`, and
`S` is a hypersurface of the bundled `Y` (`IsClosedSubmanifold.preimage_val_of_subset` at
codimension `(s + 1) - s`). -/
theorem IsAdaptedChart.exists_flag {S : Set M} {s : ℕ} (hS : IsClosedSubmanifold ψ S (s + 1))
    {φ : OpenPartialHomeomorph M E} {σ : Fin (s + 1) ↪ Fin n} (hφ : IsAdaptedChart ψ S φ σ)
    (hsrc : φ.source = Set.univ) :
    ∃ (Y : Set M) (hY : IsClosedSubmanifold ψ Y s), S ⊆ Y ∧
      IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
        (⇑hY.inclusionMap ⁻¹' S) 1 := by
  -- the first `s` adapted coordinates
  let σ' : Fin s ↪ Fin n := ⟨fun j => σ (Fin.castSucc j),
    fun _ _ h => Fin.castSucc_injective _ (σ.injective h)⟩
  have hmem : ∀ x : M, x ∈ φ.source := fun x => by rw [hsrc]; exact Set.mem_univ x
  have hcont : Continuous φ := continuousOn_univ.mp (hsrc ▸ φ.continuousOn)
  have hY : IsClosedSubmanifold ψ {x : M | ∀ j : Fin s, ψ (φ x) (σ' j) = 0} s := by
    refine ⟨?_, fun a _ => ⟨φ, σ', hmem a, hφ.1, fun x _ => Iff.rfl⟩⟩
    have hset : {x : M | ∀ j : Fin s, ψ (φ x) (σ' j) = 0} =
        ⋂ j : Fin s, {x : M | ψ (φ x) (σ' j) = 0} := by
      ext x
      constructor
      · intro h
        exact Set.mem_iInter.mpr fun j => h j
      · intro h j
        exact Set.mem_iInter.mp h j
    rw [hset]
    exact isClosed_iInter fun j =>
      isClosed_eq ((continuous_apply (σ' j)).comp (ψ.continuous.comp hcont)) continuous_const
  have hSY : S ⊆ {x : M | ∀ j : Fin s, ψ (φ x) (σ' j) = 0} := fun x hx j =>
    (hφ.2 x (hmem x)).mp hx (Fin.castSucc j)
  refine ⟨_, hY, hSY, ?_⟩
  have h1 := hY.preimage_val_of_subset hS hSY
  rw [Nat.add_sub_cancel_left] at h1
  exact h1

/-- The pull-back to the bundled `Y` of the reduced ideal sheaf of `S ⊆ Y` is the reduced ideal
sheaf of `S` as a closed submanifold of `Y`, for any closed-submanifold structure on `S` in `Y`
(`idealSheaf_preimageVal_eq_pullback`; the two structures on the same set have the same reduced
ideal sheaf, both with the vanishing stalks). The hypothesis `S ⊆ Y` is needed: a hypersurface
tangent to `Y` is a counterexample. -/
theorem IsClosedSubmanifold.pullback_idealSheaf_inclusionMap {Y S : Set M} {c c' c'' : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (hS : IsClosedSubmanifold ψ S c') (hSY' : S ⊆ Y)
    (hSY : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - c) → 𝕜))
      (⇑hY.inclusionMap ⁻¹' S) c'') :
    hS.idealSheaf.pullback hY.inclusionMap hY.inclusionMap.contMDiff = hSY.idealSheaf := by
  rw [← idealSheaf_preimageVal_eq_pullback hY hS hSY']
  refine IdealSheaf.ext fun p => ?_
  rw [(hY.preimage_val_of_subset hS hSY').stalkIdeal_idealSheaf_eq_vanishingStalk,
    hSY.stalkIdeal_idealSheaf_eq_vanishingStalk]
  rfl

/-- The kernel of the germ map of the inclusion of a closed submanifold at `p` is the stalk of its
reduced ideal sheaf at `p` (`germMap_inclusionMap` and `stalkIdeal_idealSheaf_of_mem`, at a
general model). -/
theorem IsClosedSubmanifold.ker_germMap_inclusionMap' {S : Set M} {c : ℕ}
    (hS : IsClosedSubmanifold ψ S c) (p : hS.toAnalyticManifold) :
    RingHom.ker (germMap ⇑hS.inclusionMap hS.inclusionMap.contMDiff p) =
      hS.idealSheaf.stalkIdeal (hS.inclusionMap p) := by
  have h1 := hS.stalkIdeal_idealSheaf_of_mem (p : S).2
  rw [hS.germMap_inclusionMap p]
  exact h1.symm

/-- An ideal sheaf containing `𝓘_S` whose pull-back to `S` is nonzero everywhere pulls back to
`Y ⊇ S` nonzero everywhere: off `S` its stalk is the unit ideal; at a point of `S`, a zero
pull-back to `Y` means every germ of `I` lies in the kernel of the germ map of `Y`, the stalk of
`𝓘_Y ≤ 𝓘_S`, so the pull-back to `S` is zero too. The hypothesis `𝓘_S ≤ I` is needed: an `I`
equal to `𝓘_Y` along a component of `Y` missing `S` is a counterexample. -/
theorem IdealSheaf.isNonzeroEverywhere_pullback_inclusionMap_of_le {Y S : Set M} {c c' : ℕ}
    (hY : IsClosedSubmanifold ψ Y c) (hS : IsClosedSubmanifold ψ S c') (hSY : S ⊆ Y)
    (I : AnalyticManifold.IdealSheaf M) (hle : hS.idealSheaf ≤ I)
    (hJ : (I.pullback hS.inclusionMap hS.inclusionMap.contMDiff).IsNonzeroEverywhere) :
    (I.pullback hY.inclusionMap hY.inclusionMap.contMDiff).IsNonzeroEverywhere := by
  intro p
  rw [IdealSheaf.stalkIdeal_pullback]
  by_cases hp : hY.inclusionMap p ∈ S
  · intro hbot
    have hker : I.stalkIdeal (hY.inclusionMap p) ≤
        hY.idealSheaf.stalkIdeal (hY.inclusionMap p) := by
      rw [← hY.ker_germMap_inclusionMap' p]
      exact (Ideal.map_eq_bot_iff_le_ker _).mp hbot
    apply hJ (⟨hY.inclusionMap p, hp⟩ : S)
    refine (IdealSheaf.stalkIdeal_pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff I
      ((⟨hY.inclusionMap p, hp⟩ : S) : hS.toAnalyticManifold)).trans ?_
    rw [Ideal.map_eq_bot_iff_le_ker, hS.ker_germMap_inclusionMap' (⟨hY.inclusionMap p, hp⟩ : S)]
    exact hker.trans (IdealSheaf.le_def.mp (hY.idealSheaf_le_of_subset hS hSY) _)
  · have htop : I.stalkIdeal (hY.inclusionMap p) = ⊤ :=
      top_le_iff.mp ((hS.stalkIdeal_idealSheaf_of_notMem hp).symm.le.trans
        (IdealSheaf.le_def.mp hle _))
    rw [htop, Ideal.map_top]
    exact top_ne_bot

end Manifold
