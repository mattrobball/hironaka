/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
public import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
public import Hironaka.Resolution.Analytic.OrderReduction.ConcatPullback
import Hironaka.Manifold.FiniteSuccession.Restrict.Lift
import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Uniqueness of maps over the blow-down of a sequence of centres

A blow-up is an isomorphism off its centre, so a map into the blow-up is determined off the
exceptional divisor by its composite with the blow-down. Along a whole sequence of centres `L`:
**two continuous maps into the last stage of `L` that agree after the composite blow-down
`L.stage r → M` agree**, provided the first pulls dense open sets back to dense sets (a local
analytic isomorphism does, being an open map). The proof is the one-step uniqueness of lifts
(`liftStep_unique`) applied stage by stage: off the exceptional divisor the blow-down is injective,
the complement of the exceptional divisor is dense (`IsBlowUp.dense_preimage_compl`), and its
preimage under the tail's blow-down is again dense because a blow-down pulls dense open sets back to
dense sets (`dense_preimage_blowUpπ`: off the centre it is a local homeomorphism).

Consequences: the last-stage lift of a local analytic isomorphism `h` along `L`
(`pullbackLiftLast`, the map induced by the pull-back of blow-up sequences of
[Kol07, Definition 30 (30.1)]) is the unique continuous map over `h` pulling dense open sets back
to dense sets (`pullbackLiftLast_unique`), and the lift of a composite is the composite of the lifts
up to the identification `pullback_comp` of the pulled-back sequences
(`pullbackLiftLast_comp_apply`). Not in the sources as such; these are the identities the transport
of the chain of Step 2.1 (`ChainTransport.lean`) reads pointwise.
-/

public section

universe u

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

section BlowUpDense

variable {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)

/-- A blow-down pulls a dense set back to a dense set: off the centre it is a local homeomorphism
onto the open set `Yᶜ`, and the complement of the exceptional divisor is dense
(`IsBlowUp.dense_preimage_compl`). -/
theorem dense_preimage_blowUpπ {D : Set M} (hD : Dense D) :
    Dense (⇑(Manifold.blowUpπ ψ₀ hY) ⁻¹' D) := by
  have hπ := isBlowUp_blowUpπ ψ₀ hY
  rw [dense_iff_inter_open]
  intro V hV hVne
  obtain ⟨q, hqV, hqc⟩ := (dense_iff_inter_open.mp (hπ.dense_preimage_compl hY)) V hV hVne
  have hVc : IsOpen (V ∩ ⇑(Manifold.blowUpπ ψ₀ hY) ⁻¹' Yᶜ) :=
    hV.inter (hπ.contMDiff.continuous.isOpen_preimage _ hY.isClosed.isOpen_compl)
  have hopen : IsOpen (⇑(Manifold.blowUpπ ψ₀ hY) '' (V ∩ ⇑(Manifold.blowUpπ ψ₀ hY) ⁻¹' Yᶜ)) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨p, hp, rfl⟩
    rw [← hπ.isLocalDiffeomorphOn_compl.isLocalHomeomorphOn.map_nhds_eq hp.2]
    exact Filter.image_mem_map (hVc.mem_nhds hp)
  obtain ⟨_, ⟨p, hp, rfl⟩, hpD⟩ :=
    (dense_iff_inter_open.mp hD) _ hopen ⟨_, q, ⟨hqV, hqc⟩, rfl⟩
  exact ⟨p, hp.1, hpD⟩

end BlowUpDense

end Hironaka.Manifold

namespace AnalyticManifold.BlowUpSequence

open _root_.Manifold
open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The composite blow-down of a list pulls dense sets back to dense sets (one blow-down at a
time). -/
theorem dense_preimage_stageMap_last : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    {D : Set M}, Dense D → Dense (⇑(L.toSuccession.stageMap (Fin.last _)) ⁻¹' D)
  | _, nil _, _, hD => hD
  | _, cons hY rest, D, hD => by
    have h2 := rest.dense_preimage_stageMap_last (dense_preimage_blowUpπ hY hD)
    have heq : ⇑((cons hY rest).toSuccession.stageMap (Fin.last _)) ⁻¹' D =
        ⇑(rest.toSuccession.stageMap (Fin.last _)) ⁻¹' (⇑(Manifold.blowUpπ ψ₀ hY) ⁻¹' D) := by
      ext p
      exact Iff.of_eq (congrArg (· ∈ D) (stageMapAux_cons_succ hY rest _ _ p))
    rw [heq]
    exact h2

/-- **Two continuous maps into the last stage of `L` over the same map to `M` agree**, provided the
first pulls dense open sets of the last stage back to dense sets (an open map does). One blow-down
at a time: the two maps into the blow-up agree off the exceptional divisor, where the blow-down is
injective, and that set is dense in the source (`dense_preimage_stageMap_last`). -/
theorem eq_of_stageMap_last_comp_eq : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    {Z : Type u} [TopologicalSpace Z] {f g : Z → L.stage (Fin.last _)}, Continuous f →
    Continuous g → (∀ D : Set (L.stage (Fin.last _)), IsOpen D → Dense D → Dense (f ⁻¹' D)) →
    (∀ z, L.toSuccession.stageMap (Fin.last _) (f z) =
      L.toSuccession.stageMap (Fin.last _) (g z)) → f = g
  | _, nil _, _, _, _, _, _, _, _, hfg => funext fun z => hfg z
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest, Z, _, f, g, hf, hg, hfd, hfg => by
    have hπ := isBlowUp_blowUpπ ψ₀ hY
    have hβ : Continuous (rest.toSuccession.stageMap (Fin.last _)) :=
      (rest.toSuccession.stageMap (Fin.last _)).contMDiff.continuous
    have hcomm : ∀ z, Manifold.blowUpπ ψ₀ hY (rest.toSuccession.stageMap (Fin.last _) (f z)) =
        Manifold.blowUpπ ψ₀ hY (rest.toSuccession.stageMap (Fin.last _) (g z)) := fun z =>
      (stageMapAux_cons_succ hY rest _ _ (f z)).symm.trans
        ((hfg z).trans (stageMapAux_cons_succ hY rest _ _ (g z)))
    have h1 : IsOpen (⇑(Manifold.blowUpπ ψ₀ hY) ⁻¹' Yᶜ) :=
      hπ.contMDiff.continuous.isOpen_preimage _ hY.isClosed.isOpen_compl
    have hdense : Dense ((fun z => rest.toSuccession.stageMap (Fin.last _) (f z)) ⁻¹'
        (⇑(Manifold.blowUpπ ψ₀ hY) ⁻¹' Yᶜ)) :=
      hfd _ (hβ.isOpen_preimage _ h1) (rest.dense_preimage_stageMap_last
        (hπ.dense_preimage_compl hY))
    have hrest : ∀ z, rest.toSuccession.stageMap (Fin.last _) (f z) =
        rest.toSuccession.stageMap (Fin.last _) (g z) := fun z =>
      eqOn_of_comp_eq_of_dense
        (π₁ := fun z => Manifold.blowUpπ ψ₀ hY (rest.toSuccession.stageMap (Fin.last _) (f z)))
        hπ.bijOn_compl.injOn hdense isOpen_univ (hβ.comp hf).continuousOn
        (hβ.comp hg).continuousOn (fun _ _ => rfl) (fun z _ => (hcomm z).symm) (Set.mem_univ z)
    exact eq_of_stageMap_last_comp_eq rest hf hg hfd hrest

variable {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)

include hh in
/-- A local analytic isomorphism pulls dense sets back to dense sets (it is an open map). -/
theorem dense_preimage_of_isLocalDiffeomorph {D : Set M} (hD : Dense D) : Dense (⇑h ⁻¹' D) :=
  hD.preimage hh.isOpenMap

/-- **Uniqueness of the last-stage lift**: a continuous map over `h` between the last stages of
`h^* L` and `L` that pulls dense open sets back to dense sets is `pullbackLiftLast`. -/
theorem pullbackLiftLast_unique {G : (L.pullback h hh).stage (Fin.last _) → L.stage (Fin.last _)}
    (hG : Continuous G) (hGd : ∀ D : Set (L.stage (Fin.last _)), IsOpen D → Dense D →
      Dense (G ⁻¹' D))
    (hcomm : ∀ q, L.toSuccession.stageMap (Fin.last _) (G q) =
      h ((L.pullback h hh).toSuccession.stageMap (Fin.last _) q)) :
    G = L.pullbackLiftLast h hh :=
  eq_of_stageMap_last_comp_eq L hG (L.pullbackLiftLast h hh).contMDiff.continuous hGd fun q =>
    (hcomm q).trans (stageMap_last_pullbackLiftLast L h hh q).symm

/-- The last-stage lift of a composite is the composite of the last-stage lifts, up to the
identification `pullback_comp` of the pulled-back lists (uniqueness of lifts, read pointwise). -/
theorem pullbackLiftLast_comp_apply {P : AnalyticManifold.{u} 𝕜 E} (k : AnalyticMap P N)
    (hk : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω k)
    (q : ((L.pullback h hh).pullback k hk).stage (Fin.last _)) :
    L.pullbackLiftLast h hh ((L.pullback h hh).pullbackLiftLast k hk q) =
      L.pullbackLiftLast (h.comp k) (isLocalDiffeomorph_comp hh hk)
        (stageOfEq (pullback_comp L h hh k hk) q) := by
  have hf : IsOpenMap (⇑(L.pullbackLiftLast h hh) ∘ ⇑((L.pullback h hh).pullbackLiftLast k hk)) :=
    (isLocalDiffeomorph_pullbackLiftLast L h hh).isOpenMap.comp
      (isLocalDiffeomorph_pullbackLiftLast (L.pullback h hh) k hk).isOpenMap
  have e := eq_of_stageMap_last_comp_eq L
    (f := ⇑(L.pullbackLiftLast h hh) ∘ ⇑((L.pullback h hh).pullbackLiftLast k hk))
    (g := ⇑(L.pullbackLiftLast (h.comp k) (isLocalDiffeomorph_comp hh hk)) ∘
      ⇑(stageOfEq (pullback_comp L h hh k hk)))
    ((L.pullbackLiftLast h hh).contMDiff.continuous.comp
      ((L.pullback h hh).pullbackLiftLast k hk).contMDiff.continuous)
    ((L.pullbackLiftLast (h.comp k) (isLocalDiffeomorph_comp hh hk)).contMDiff.continuous.comp
      (stageOfEq (pullback_comp L h hh k hk)).continuous)
    (fun _ _ hD => hD.preimage hf) (fun q =>
      ((stageMap_last_pullbackLiftLast L h hh _).trans
        (congrArg h (stageMap_last_pullbackLiftLast (L.pullback h hh) k hk q))).trans
        ((stageMap_last_pullbackLiftLast L (h.comp k) _ _).trans
          (congrArg (h.comp k) (stageMap_last_stageOfEq _ q))).symm)
  exact congrFun e q

end AnalyticManifold.BlowUpSequence

