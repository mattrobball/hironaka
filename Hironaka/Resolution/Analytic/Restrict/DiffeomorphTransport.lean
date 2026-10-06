/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.ConcatPullback
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
public import Hironaka.Resolution.Analytic.LocalIsoEquiv

/-!
# Transports along a diffeomorphism of two models; the last-stage lift of a diffeomorphism

The independence of the resolution of a piece from its embedding [Kol07, Theorem 36, proof]
compares the local resolutions for two embeddings by passing through the coordinate slice of a
padded embedding (Kollár's enlargement `𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ` of the ambient space and the weak commutation
with closed embeddings [Kol07, 34.4]; Włodarczyk's common ambient dimension [Wlo09, §7.1]). The
slice, read as a bundled submanifold (`IsClosedSubmanifold.toAnalyticManifold`, modelled on
`𝕜^{n' − (n' − n)}`), is diffeomorphic to the piece (modelled on `𝕜ⁿ`) ACROSS MODELS — the two
dimensions are propositionally, not definitionally, equal — so the transports of ideal-sheaf data
that the comparison needs are stated here for a diffeomorphism `g : M' → M` between manifolds on
ANY two models `E'`, `E`:

* `IdealSheaf.isReduced_pullback_diffeomorph`,
  `IdealSheaf.isNonzeroEverywhere_pullback_diffeomorph`: the germ map of a diffeomorphism is a ring
  isomorphism of stalks (`germMap_bijective_of_diffeomorph`, the two-model form of
  `germMap_bijective_of_isLocalDiffeomorphAt`), and the pull-back's stalks are its images
  (`IdealSheaf.stalkIdeal_pullback`), so radical ideals and nonzero ideals transport. They supply
  the hypotheses `DomBEDan` and `IsNonzeroEverywhere` for the slice triple.
* `IdealSheaf.pullback_symm_pullback`: pulling back along `g⁻¹` and then along `g` is the
  identity — the two-model form of the same-model `IdealSheaf.pullback_pullback_symm`
  (`TransportBase.lean`), by `pullback_pullback`, `pullback_congr` and `pullback_id_eq_self`, all
  of which already admit two models.
* `isCompact_closure_preimage_diffeomorph`: relatively compact opens pull back to relatively
  compact opens (a homeomorphism).
* The pull-back along `h` of a blow-up sequence is the fibre product `X_i ×_X Y`
  [Kol07, Definition 30.1], whose projections are injective when `h` is — `injective_liftStep`,
  `BlowUpSequence.injective_pullbackLiftLast`, the injective counterparts of `surjective_liftStep`
  and `surjective_pullbackLiftLast` (Kollár's printed remark concerns a surjective `h`; the
  injective case is immediate from the definition of the pull-back); hence the last-stage lift of a
  BIJECTIVE local analytic isomorphism is a diffeomorphism,
  `BlowUpSequence.pullbackLiftLastDiffeomorphOfBijective` (Mathlib's
  `IsLocalDiffeomorph.toDiffeomorphOfBijective`; the map `restrictMap g U' (imageOpens g hg U')`
  produced by the functoriality clause of `IsEmbeddedDesing` is the case used), and
  `BlowUpSequence.pullbackLiftLastDiffeomorph` for a diffeomorphism `g`, with their coercion lemmas
  `coe_…`.

Not in the sources; routine transports along the pull-back of ideal sheaves and the lift of a
local isomorphism to a blow-up sequence.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace Manifold

open Hironaka.Manifold

/-! ### Transports along a diffeomorphism of two models -/

section Transport

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : AnalyticManifold.{u} 𝕜 E}
  {M' : AnalyticManifold.{u} 𝕜 E'} (g : Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E) M' M ω)

/-- **The germ map of a diffeomorphism of two models is bijective** (the two-model form of
`germMap_bijective_of_isLocalDiffeomorphAt`): the germ map of the inverse, read at `g b` through
`g⁻¹(g b) = b`, is a two-sided inverse. -/
theorem _root_.Hironaka.Manifold.germMap_bijective_of_diffeomorph (b : M') :
    Function.Bijective (germMap ⇑g g.contMDiff b) := by
  have hinv : g.symm (g b) = b := g.symm_apply_apply b
  set ρ := germMapOn (⇑g.symm) (V := (⊤ : Opens M)) g.symm.contMDiff.contMDiffOn
    (Opens.mem_top _) hinv with hρ
  have hcomp : ρ.comp (germMap ⇑g g.contMDiff b) = RingHom.id _ := by
    refine RingHom.ext fun t => stalkToGerm_injective 𝓘(𝕜, E) ω M (g b) ?_
    rw [RingHom.comp_apply, hρ, stalkToGerm_germMapOn, stalkToGerm_germMap, RingHom.id_apply]
    induction stalkToGerm 𝓘(𝕜, E) ω M (g b) t using Germ.inductionOn with
    | h k =>
      rw [Germ.coe_compTendsto, Germ.coe_compTendsto]
      refine Germ.coe_eq.mpr ?_
      filter_upwards with y
      simp only [Function.comp_apply, Diffeomorph.apply_symm_apply]
  have hcomp' : (germMap ⇑g g.contMDiff b).comp ρ = RingHom.id _ := by
    refine RingHom.ext fun t => stalkToGerm_injective 𝓘(𝕜, E') ω M' b ?_
    rw [RingHom.comp_apply, stalkToGerm_germMap, hρ, stalkToGerm_germMapOn, RingHom.id_apply]
    induction stalkToGerm 𝓘(𝕜, E') ω M' b t using Germ.inductionOn with
    | h k =>
      rw [Germ.coe_compTendsto, Germ.coe_compTendsto]
      refine Germ.coe_eq.mpr ?_
      filter_upwards with y
      simp only [Function.comp_apply, Diffeomorph.symm_apply_apply]
  refine ⟨Function.LeftInverse.injective (g := ρ) fun t => ?_,
    Function.RightInverse.surjective (g := ρ) fun t => ?_⟩
  · rw [← RingHom.comp_apply, hcomp, RingHom.id_apply]
  · rw [← RingHom.comp_apply, hcomp', RingHom.id_apply]

/-- **Pulling back along `g⁻¹` and then along `g` is the identity**: the two-model form of
`IdealSheaf.pullback_pullback_symm` (`TransportBase.lean`), which is this statement at `g⁻¹` for a
same-model diffeomorphism. -/
theorem IdealSheaf.pullback_symm_pullback (J : AnalyticManifold.IdealSheaf M') :
    (J.pullback ⇑g.symm g.symm.contMDiff).pullback ⇑g g.contMDiff = J :=
  (IdealSheaf.pullback_pullback J _ _ _ _).trans
    ((IdealSheaf.pullback_congr J _ contMDiff_id
      (funext fun x => g.symm_apply_apply x)).trans (IdealSheaf.pullback_id_eq_self J))

/-- Reducedness of an ideal sheaf transports along a diffeomorphism of two models: the pull-back's
stalks are the images of the stalks under the ring isomorphisms `germMap`, and a radical ideal
maps to a radical ideal under a surjective ring homomorphism with trivial kernel
(`Ideal.map_radical_of_surjective`). -/
theorem IdealSheaf.isReduced_pullback_diffeomorph {J : AnalyticManifold.IdealSheaf M}
    (hJ : AnalyticManifold.IdealSheaf.IsReduced J) :
    AnalyticManifold.IdealSheaf.IsReduced (J.pullback ⇑g g.contMDiff) := by
  intro b
  rw [IdealSheaf.stalkIdeal_pullback]
  obtain ⟨hinj, hsurj⟩ := germMap_bijective_of_diffeomorph g b
  have hker : RingHom.ker (germMap ⇑g g.contMDiff b) ≤ J.stalkIdeal (g b) := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  rw [← Ideal.radical_eq_iff, ← Ideal.map_radical_of_surjective hsurj hker,
    Ideal.radical_eq_iff.mpr (hJ (g b))]

/-- Nonvanishing at every stalk transports along a diffeomorphism of two models: the image of a
nonzero ideal under an injective ring homomorphism is nonzero
(`Ideal.map_eq_bot_iff_of_injective`). -/
theorem IdealSheaf.isNonzeroEverywhere_pullback_diffeomorph {J : AnalyticManifold.IdealSheaf M}
    (hJ : J.IsNonzeroEverywhere) :
    (J.pullback ⇑g g.contMDiff).IsNonzeroEverywhere := by
  intro b
  rw [IdealSheaf.stalkIdeal_pullback]
  exact fun h => hJ (g b)
    ((Ideal.map_eq_bot_iff_of_injective (germMap_bijective_of_diffeomorph g b).1).mp h)

/-- The preimage of a relatively compact open under a diffeomorphism is relatively compact (a
homeomorphism carries closures to closures and compact sets to compact sets). -/
theorem _root_.Hironaka.Manifold.isCompact_closure_preimage_diffeomorph {U : Set M} (hU : IsCompact
    (closure U)) :
    IsCompact (closure (⇑g ⁻¹' U)) := by
  have h := g.toHomeomorph.isCompact_preimage.mpr hU
  rwa [g.toHomeomorph.preimage_closure, Diffeomorph.coe_toHomeomorph] at h

end Transport

end Manifold

/-! ### The last-stage lift of a diffeomorphism -/

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- The lift of an injective local analytic isomorphism to the blowings-up is injective
(`injective_blowUpLift`; the fibre product `X₁ ×_X Y` of [Kol07, Definition 30.1]) — the
counterpart of `surjective_liftStep`. -/
theorem injective_liftStep (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) (hi : Function.Injective h) :
    Function.Injective (liftStep h hh hY) :=
  injective_blowUpLift hY hh (isBlowUp_blowUpπ ψ₀ hY)
    (isBlowUp_blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)) hi

/-- **The last-stage lift of an injective local analytic isomorphism is injective**, by the list
recursion of `surjective_pullbackLiftLast` (immediate from the definition of the pull-back of a
blow-up sequence [Kol07, Definition 30.1], whose printed remark concerns a surjective `h`). -/
theorem injective_pullbackLiftLast : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    Function.Injective h → Function.Injective (L.pullbackLiftLast h hh)
  | _, _, nil _, _, _, hi => hi
  | _, _, cons hY rest, h, hh, hi =>
    injective_pullbackLiftLast rest (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)
      (injective_liftStep h hh hY hi)

/-- **The last-stage lift of a BIJECTIVE local analytic isomorphism, as a diffeomorphism**
([Kol07, Definition 30.1]): `pullbackLiftLast` is a bijective local analytic isomorphism
(`isLocalDiffeomorph_pullbackLiftLast`, `injective_pullbackLiftLast`,
`surjective_pullbackLiftLast`), hence a diffeomorphism by Mathlib's
`IsLocalDiffeomorph.toDiffeomorphOfBijective`. This is the form in which the functoriality clause of
`IsEmbeddedDesing` is used: `h` is `restrictMap g U' (imageOpens g hg U')`, onto its image and
injective when `g` is. -/
def pullbackLiftLastDiffeomorphOfBijective (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hb : Function.Bijective h) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ((L.pullback h hh).stage (Fin.last _)) (L.stage (Fin.last _)) ω :=
  (L.isLocalDiffeomorph_pullbackLiftLast h hh).toDiffeomorphOfBijective
    ⟨L.injective_pullbackLiftLast h hh hb.1, L.surjective_pullbackLiftLast h hh hb.2⟩

/-- The diffeomorphism of `pullbackLiftLastDiffeomorphOfBijective` is the lift on points
(definitional). -/
theorem coe_pullbackLiftLastDiffeomorphOfBijective (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hb : Function.Bijective h) :
    ⇑(L.pullbackLiftLastDiffeomorphOfBijective h hh hb) = ⇑(L.pullbackLiftLast h hh) :=
  rfl

/-- **The last-stage lift of a diffeomorphism, as a diffeomorphism** ([Kol07, Definition 30.1]):
`pullbackLiftLastDiffeomorphOfBijective` at `g` read as an analytic map. -/
def pullbackLiftLastDiffeomorph (L : BlowUpSequence ψ₀ M) (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E)
      ((L.pullback (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph).stage (Fin.last _))
      (L.stage (Fin.last _)) ω :=
  L.pullbackLiftLastDiffeomorphOfBijective (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph
    g.bijective

/-- The diffeomorphism is the lift on points (definitional). -/
theorem coe_pullbackLiftLastDiffeomorph (L : BlowUpSequence ψ₀ M)
    (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω) :
    ⇑(L.pullbackLiftLastDiffeomorph g) =
      ⇑(L.pullbackLiftLast (Diffeomorph.toAnalyticMap g) g.isLocalDiffeomorph) :=
  rfl

end AnalyticManifold.BlowUpSequence

end
