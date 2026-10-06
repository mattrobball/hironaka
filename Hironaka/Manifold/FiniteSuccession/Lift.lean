/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Functor
import Hironaka.Manifold.BlowUp.Restrict
public import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The lift of a local analytic isomorphism to the blowings-up

The pull-back of a blow-up sequence along a smooth morphism `h : Y → X` has the stages
`X_i ×_X Y` and the centres `Z_i ×_X Y`; if `h` is surjective the pull-back determines the
sequence, while for a non-surjective `h` the pull-back may contain empty blow-ups, and the
information about the centres above `X ∖ h(Y)` is lost [Kol07, 30.1]. On analytic
manifolds the fibre product `X_i ×_X Y` along a local analytic isomorphism is replaced by the
blowing-up of the preimage centre `h_i^{-1}(Z_i)`, which is identified with it by the uniqueness of
the blowing-up [BM88, Definition 4.1] (a local analytic isomorphism is flat, and blowing up
commutes with flat base change). The preimage `h⁻¹(Y)` of a closed submanifold of codimension `c`
under a local analytic isomorphism `h : N → M` is a closed submanifold of codimension `c`
(`IsClosedSubmanifold.preimage_of_isLocalDiffeomorph`, `Hironaka/Manifold/Chart/Transport.lean`).
This module provides the one-step lemmas, on manifolds that are not bundled:

* `blowUpLift`: for blowings-up `π : M' → M` of `M` along `Y` and `π' : N' → N` of `N` along
  `h⁻¹(Y)`, the lift `h' : N' → M'` of `h` over the blow-downs, `π ∘ h' = h ∘ π'`
  (`blowDown_blowUpLift`): the lifts `liftPointG` of the local inverses of `h` to the blowings-up,
  glued (well defined by the uniqueness of lifts, `IsBlowUp.eqOn_of_comp_eq_of_image_eq`); it is
  a local analytic isomorphism (`isLocalDiffeomorph_blowUpLift`);
* for any continuous `G : N' → M'` over `h` (in particular the lift): `G` agrees with the lift of
  every local inverse `Φ` of `h` on `π'⁻¹(Φ.source)` (`eqOn_liftPartialDiffeomorph_of_comm`), is
  surjective when `h` is (`surjective_of_comm`), injective when `h` is (`injective_of_comm`), and
  an open embedding when `h` is (`isOpenEmbedding_of_comm`, for a local analytic isomorphism `G`).

The empty cases need no positive-codimension proviso: a point of `N'` over `h (π' q)` produces a
point of `M'` (`exists_blowDown_eq_apply`), and conversely a point of `M'` over `h b` produces a
point of `N'` over `b` (`exists_blowDown_eq_of_blowDown_eq`), through the blow-up charts (which
exist exactly where the codimension is positive) off and on the centre.

These lemmas are the steps of the pull-back of a whole sequence of centres in `CenterList.lean`
(`BlowUpSequence.pullback`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M]
  {N : Type u} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(𝕜, E) ω N]
  {h : N → M} {Y : Set M} {c : ℕ}

/-! ### The lift of a local analytic isomorphism to the blowings-up -/

section Lift

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M']
  {N' : Type u} [TopologicalSpace N'] [ChartedSpace E N'] [IsManifold 𝓘(𝕜, E) ω N']
  [T2Space N'] [SecondCountableTopology N'] {π : M' → M} {π' : N' → N}
  (hY : IsClosedSubmanifold ψ Y c) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
  (hπ : IsBlowUp ψ Y c π) (hπ' : IsBlowUp ψ (h ⁻¹' Y) c π')

include hY hh hπ hπ' in
omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Over the image `h (π' q)` of a point of `N'` lies a point of `M'`: off the centre by the
bijection off the exceptional divisor, on the centre through a blow-up chart (whose existence,
`IsBlowUp.cover`, forces the codimension to be positive) and the surjectivity of `π`. -/
theorem exists_blowDown_eq_apply (q : N') : ∃ p : M', π p = h (π' q) := by
  by_cases hb : h (π' q) ∈ Y
  · obtain ⟨φ, σ, hqφ, hφ⟩ :=
      (hY.preimage_of_isLocalDiffeomorph hh).exists_adaptedChart (π' q) hb
    obtain ⟨i, -⟩ := hπ'.cover φ σ hφ q hqφ
    exact hπ.surjective hY i (h (π' q))
  · obtain ⟨p, -, hp⟩ := hπ.bijOn_compl.surjOn hb
    exact ⟨p, hp⟩

include hY hh hπ hπ' in
omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Over a point `b` of `N` whose image `h b` is a blow-down lies a point of `N'` (the converse of
`exists_blowDown_eq_apply`, by the same case distinction). -/
theorem exists_blowDown_eq_of_blowDown_eq (b : N) {p : M'} (hp : π p = h b) :
    ∃ q : N', π' q = b := by
  by_cases hb : h b ∈ Y
  · obtain ⟨φ, σ, hbφ, hφ⟩ := hY.exists_adaptedChart (h b) hb
    have hpφ : π p ∈ φ.source := by rw [hp]; exact hbφ
    obtain ⟨i, -⟩ := hπ.cover φ σ hφ p hpφ
    exact hπ'.surjective (hY.preimage_of_isLocalDiffeomorph hh) i b
  · obtain ⟨q, -, hq⟩ := hπ'.bijOn_compl.surjOn (show b ∈ (h ⁻¹' Y)ᶜ from hb)
    exact ⟨q, hq⟩

section Glue

variable [Nonempty M']

/-- The lift of `h` to the blowings-up, glued from the lifts `liftPointG` of the chosen local
inverses of `h` at the blow-downs of the points (`Classical.choose` on
`(hh (π' q)).exists_partialDiffeomorph`, the partial diffeomorphism agreeing with `h` near
`π' q`). -/
def blowUpLiftAux (q : N') : M' :=
  liftPointG (hh (π' q)).exists_partialDiffeomorph.choose
    (image_preimage_eq_of_eqOn _ (hh (π' q)).exists_partialDiffeomorph.choose_spec.2)
    (hY.preimage_of_isLocalDiffeomorph hh) hπ' hπ q

/-- The lifts of two local inverses of `h` agree at a point over both sources (uniqueness of
lifts, `IsBlowUp.eqOn_of_comp_eq_of_image_eq` on `π'⁻¹(Φ.source ∩ Ψ.source)`). -/
theorem liftPointG_eq_liftPointG {Φ Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω}
    (hΦ : EqOn h Φ Φ.source) (hΨ : EqOn h Ψ Ψ.source) {q : N'} (hqΦ : π' q ∈ Φ.source)
    (hqΨ : π' q ∈ Ψ.source) :
    liftPointG Ψ (image_preimage_eq_of_eqOn Ψ hΨ) (hY.preimage_of_isLocalDiffeomorph hh) hπ' hπ
        q =
      liftPointG Φ (image_preimage_eq_of_eqOn Φ hΦ) (hY.preimage_of_isLocalDiffeomorph hh) hπ' hπ
        q := by
  have hY' := hY.preimage_of_isLocalDiffeomorph hh
  have hN : IsOpen (π' ⁻¹' (Φ.source ∩ Ψ.source)) :=
    (Φ.open_source.inter Ψ.open_source).preimage hπ'.contMDiff.continuous
  refine hπ'.eqOn_of_comp_eq_of_image_eq Φ (image_preimage_eq_of_eqOn Φ hΦ) hY' hπ hN
    (fun _ hr => hr.1)
    ((contMDiffOn_liftPointG Ψ (image_preimage_eq_of_eqOn Ψ hΨ) hY' hπ' hπ).continuousOn.mono
      fun _ hr => hr.2)
    ((contMDiffOn_liftPointG Φ (image_preimage_eq_of_eqOn Φ hΦ) hY' hπ' hπ).continuousOn.mono
      fun _ hr => hr.1)
    (fun r hr => ?_)
    (fun r hr => blowDown_liftPointG Φ (image_preimage_eq_of_eqOn Φ hΦ) hY' hπ' hπ hr.1)
    ⟨hqΦ, hqΨ⟩
  rw [blowDown_liftPointG Ψ (image_preimage_eq_of_eqOn Ψ hΨ) hY' hπ' hπ hr.2, ← hΨ hr.2, hΦ hr.1]

/-- The glued lift agrees with the lift of any local inverse `Φ` of `h` over `Φ.source`. -/
theorem blowUpLiftAux_eq {Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω}
    (hΦ : EqOn h Φ Φ.source) {q : N'} (hq : π' q ∈ Φ.source) :
    blowUpLiftAux hY hh hπ hπ' q =
      liftPointG Φ (image_preimage_eq_of_eqOn Φ hΦ) (hY.preimage_of_isLocalDiffeomorph hh) hπ' hπ
        q :=
  liftPointG_eq_liftPointG hY hh hπ hπ' hΦ (hh (π' q)).exists_partialDiffeomorph.choose_spec.2 hq
    (hh (π' q)).exists_partialDiffeomorph.choose_spec.1

/-- The glued lift lies over `h`: `π ∘ h' = h ∘ π'`. -/
theorem blowDown_blowUpLiftAux (q : N') : π (blowUpLiftAux hY hh hπ hπ' q) = h (π' q) :=
  (blowDown_liftPointG (hh (π' q)).exists_partialDiffeomorph.choose
    (image_preimage_eq_of_eqOn _ (hh (π' q)).exists_partialDiffeomorph.choose_spec.2)
    (hY.preimage_of_isLocalDiffeomorph hh) hπ' hπ
    (hh (π' q)).exists_partialDiffeomorph.choose_spec.1).trans
    ((hh (π' q)).exists_partialDiffeomorph.choose_spec.2
      (hh (π' q)).exists_partialDiffeomorph.choose_spec.1).symm

/-- The glued lift is a local analytic isomorphism: at `q₀` it agrees with the partial
diffeomorphism `liftPartialDiffeomorph` lifting the local inverse chosen at `π' q₀`. -/
theorem isLocalDiffeomorph_blowUpLiftAux :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (blowUpLiftAux hY hh hπ hπ') := by
  intro q₀
  have : Nonempty N' := ⟨q₀⟩
  have hΦ := (hh (π' q₀)).exists_partialDiffeomorph.choose_spec
  refine IsLocalDiffeomorphAt.of_eqOn (liftPartialDiffeomorph
    (hh (π' q₀)).exists_partialDiffeomorph.choose (image_preimage_eq_of_eqOn _ hΦ.2)
    (hY.preimage_of_isLocalDiffeomorph hh) hπ' hπ hY) hΦ.1 fun q hq => ?_
  exact blowUpLiftAux_eq hY hh hπ hπ' hΦ.2 hq

end Glue

include hY hh hπ hπ' in
/-- A local analytic isomorphism `h : N → M` lifts to a local analytic isomorphism `h' : N' → M'`
of the blowings-up of `N` along `h⁻¹(Y)` and of `M` along `Y`, over the blow-downs (the lifts of
the local inverses, glued). If `M'` is empty so is `N'`, and the lift is the empty map. -/
theorem exists_blowUpLift :
    ∃ h' : N' → M', (∀ q, π (h' q) = h (π' q)) ∧ IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h' := by
  by_cases hne : Nonempty M'
  · exact ⟨blowUpLiftAux hY hh hπ hπ', blowDown_blowUpLiftAux hY hh hπ hπ',
      isLocalDiffeomorph_blowUpLiftAux hY hh hπ hπ'⟩
  · rw [not_nonempty_iff] at hne
    have hN' : IsEmpty N' := ⟨fun q => by
      obtain ⟨p, -⟩ := exists_blowDown_eq_apply hY hh hπ hπ' q
      exact hne.false p⟩
    exact ⟨fun q => hN'.elim q, fun q => hN'.elim q, fun q => hN'.elim q⟩

/-- **The lift `h' : N' → M'` of a local analytic isomorphism `h : N → M` to the blowings-up** of
`N` along `h⁻¹(Y)` and of `M` along `Y`, over the blow-downs (`π ∘ h' = h ∘ π'`,
`blowDown_blowUpLift`): the lifts of the local inverses of `h`, glued (chosen from
`exists_blowUpLift`). It plays the role of the map `X_{i+1} ×_X Y → X_{i+1}` of the pull-back
[Kol07, 30.1]. -/
def blowUpLift : N' → M' := (exists_blowUpLift hY hh hπ hπ').choose

/-- The lift lies over `h`: `π ∘ h' = h ∘ π'`, the commutative square of the pull-back. -/
theorem blowDown_blowUpLift (q : N') : π (blowUpLift hY hh hπ hπ' q) = h (π' q) :=
  (exists_blowUpLift hY hh hπ hπ').choose_spec.1 q

/-- The lift is a local analytic isomorphism. -/
theorem isLocalDiffeomorph_blowUpLift :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (blowUpLift hY hh hπ hπ') :=
  (exists_blowUpLift hY hh hπ hπ').choose_spec.2

/-- The lift is analytic. -/
theorem contMDiff_blowUpLift : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω (blowUpLift hY hh hπ hπ') :=
  (isLocalDiffeomorph_blowUpLift hY hh hπ hπ').contMDiff

/-! ### Properties transferred from `h` to any map over `h` (uniqueness of lifts) -/

variable {G : N' → M'}

include hY hh hπ hπ' in
/-- A continuous map `G : N' → M'` over `h` agrees with the lift of every local inverse `Φ` of `h`
on `π'⁻¹(Φ.source)` (uniqueness of lifts). -/
theorem eqOn_liftPartialDiffeomorph_of_comm [Nonempty N'] [Nonempty M'] (hG : Continuous G)
    (hGπ : ∀ q, π (G q) = h (π' q)) {Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω}
    (hΦ : EqOn h Φ Φ.source) :
    EqOn G (liftPartialDiffeomorph Φ (image_preimage_eq_of_eqOn Φ hΦ)
      (hY.preimage_of_isLocalDiffeomorph hh) hπ' hπ hY) (π' ⁻¹' Φ.source) := by
  have hY' := hY.preimage_of_isLocalDiffeomorph hh
  have hN : IsOpen (π' ⁻¹' Φ.source) := Φ.open_source.preimage hπ'.contMDiff.continuous
  exact hπ'.eqOn_of_comp_eq_of_image_eq Φ (image_preimage_eq_of_eqOn Φ hΦ) hY' hπ hN subset_rfl
    hG.continuousOn
    (contMDiffOn_liftPointG Φ (image_preimage_eq_of_eqOn Φ hΦ) hY' hπ' hπ).continuousOn
    (fun q hq => by rw [hGπ q]; exact hΦ hq)
    (fun q hq => blowDown_liftPointG Φ (image_preimage_eq_of_eqOn Φ hΦ) hY' hπ' hπ hq)

include hY hh hπ hπ' in
/-- A continuous map over a surjective `h` is surjective (the surjective case of
[Kol07, 30.1]): a point `p` of `M'` lies over `h b`, and the lift of the local
inverse of `h` at `b` maps `π'⁻¹(Φ.source)` onto `π⁻¹(Φ.target) ∋ p`. -/
theorem surjective_of_comm (hs : Function.Surjective h) (hG : Continuous G)
    (hGπ : ∀ q, π (G q) = h (π' q)) : Function.Surjective G := by
  intro p
  obtain ⟨b, hb⟩ := hs (π p)
  obtain ⟨q₀, -⟩ := exists_blowDown_eq_of_blowDown_eq hY hh hπ hπ' b hb.symm
  have : Nonempty N' := ⟨q₀⟩
  have : Nonempty M' := ⟨p⟩
  obtain ⟨Φ, hbΦ, hΦ⟩ := (hh b).exists_partialDiffeomorph
  set L := liftPartialDiffeomorph Φ (image_preimage_eq_of_eqOn Φ hΦ)
    (hY.preimage_of_isLocalDiffeomorph hh) hπ' hπ hY
  have hp : p ∈ L.target := by
    change π p ∈ Φ.target
    rw [← hb, hΦ hbΦ]
    exact Φ.map_source hbΦ
  refine ⟨L.toPartialEquiv.symm p, ?_⟩
  have e := eqOn_liftPartialDiffeomorph_of_comm hY hh hπ hπ' hG hGπ hΦ (L.map_target hp)
  exact e.trans (L.right_inv hp)

include hY hh hπ hπ' in
/-- A continuous map over an injective `h` is injective: two points with the same image lie over
the same `b`, and the lift of the local inverse at `b` is injective on `π'⁻¹(Φ.source)`. -/
theorem injective_of_comm (hi : Function.Injective h) (hG : Continuous G)
    (hGπ : ∀ q, π (G q) = h (π' q)) : Function.Injective G := by
  intro q₁ q₂ heq
  have hb : π' q₁ = π' q₂ := hi (by rw [← hGπ q₁, ← hGπ q₂, heq])
  have : Nonempty N' := ⟨q₁⟩
  have : Nonempty M' := ⟨G q₁⟩
  obtain ⟨Φ, hbΦ, hΦ⟩ := (hh (π' q₁)).exists_partialDiffeomorph
  set L := liftPartialDiffeomorph Φ (image_preimage_eq_of_eqOn Φ hΦ)
    (hY.preimage_of_isLocalDiffeomorph hh) hπ' hπ hY
  have h₁ : q₁ ∈ π' ⁻¹' Φ.source := hbΦ
  have h₂ : q₂ ∈ π' ⁻¹' Φ.source := by
    change π' q₂ ∈ Φ.source
    rw [← hb]
    exact hbΦ
  have e := eqOn_liftPartialDiffeomorph_of_comm hY hh hπ hπ' hG hGπ hΦ
  exact L.toPartialEquiv.injOn h₁ h₂ (by rw [← e h₁, ← e h₂, heq])

include hY hh hπ hπ' in
/-- A local analytic isomorphism `G` over an open embedding `h` is an open embedding (the
open-embedding case, the second of the two situations in which a blow-up sequence functor is
required to commute with smooth morphisms [Kol07, 34.1]). -/
theorem isOpenEmbedding_of_comm (he : IsOpenEmbedding h)
    (hG : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω G) (hGπ : ∀ q, π (G q) = h (π' q)) :
    IsOpenEmbedding G :=
  .of_continuous_injective_isOpenMap hG.contMDiff.continuous
    (injective_of_comm hY hh hπ hπ' he.injective hG.contMDiff.continuous hGπ) hG.isOpenMap

/-- The lift of a surjective local analytic isomorphism is surjective
[Kol07, 30.1]. -/
theorem surjective_blowUpLift (hs : Function.Surjective h) :
    Function.Surjective (blowUpLift hY hh hπ hπ') :=
  surjective_of_comm hY hh hπ hπ' hs (contMDiff_blowUpLift hY hh hπ hπ').continuous
    (blowDown_blowUpLift hY hh hπ hπ')

/-- The lift of an injective local analytic isomorphism is injective. -/
theorem injective_blowUpLift (hi : Function.Injective h) :
    Function.Injective (blowUpLift hY hh hπ hπ') :=
  injective_of_comm hY hh hπ hπ' hi (contMDiff_blowUpLift hY hh hπ hπ').continuous
    (blowDown_blowUpLift hY hh hπ hπ')

/-- The lift of an open embedding is an open embedding (the open-embedding case of
[Kol07, 34.1]). -/
theorem isOpenEmbedding_blowUpLift (he : IsOpenEmbedding h) :
    IsOpenEmbedding (blowUpLift hY hh hπ hπ') :=
  isOpenEmbedding_of_comm hY hh hπ hπ' he (isLocalDiffeomorph_blowUpLift hY hh hπ hπ')
    (blowDown_blowUpLift hY hh hπ hπ')

/-- The exceptional divisor pulls back: `h'⁻¹(π⁻¹(Y)) = π'⁻¹(h⁻¹(Y))` (Kollár's `F_{i+1} ×_X Y`).
-/
theorem preimage_blowUpLift_preimage :
    blowUpLift hY hh hπ hπ' ⁻¹' (π ⁻¹' Y) = π' ⁻¹' (h ⁻¹' Y) := by
  ext q
  change π (blowUpLift hY hh hπ hπ' q) ∈ Y ↔ h (π' q) ∈ Y
  rw [blowDown_blowUpLift hY hh hπ hπ' q]

end Lift

end Manifold

end
