/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.EmbeddedDesingGlobal
public import Hironaka.Resolution.Analytic.Wlo09.FamilyPushforward
public import Hironaka.Resolution.Analytic.ModelTransport.Pushforward
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.Restrict.GermRestrict
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.ModelTransport.IdealSheaf
import Hironaka.Resolution.Analytic.Submanifold.FlagIdeal
import Hironaka.Resolution.Analytic.Wlo09.ZeroStalks

/-!
# The embedded desingularization and closed embeddings of ambient manifolds, on the model

The push-forward relation of [Wlo09, Theorem 2.0.2 (4)], "commutes with … embeddings of ambient
varieties", for the embedded desingularization `embeddedDesingFam` on the standard models: for a
closed embedding `τ : N → M` of manifolds modelled on `𝕜^{n−s}` and `𝕜ⁿ` whose image is a closed
submanifold of codimension `s`, identified with the bundled submanifold by `e` over `τ`, a reduced
`𝓘_Y` on `M` containing the ideal sheaf of `τ(N)` and `J = τ^* 𝓘_Y` with nonzero stalks, the
succession of the family of `Y ⊆ M` over `U_K` is the push-forward along `τ` of the succession of
the family of `Y ⊆ N` over `U_{K'}` whenever `τ(U_{K'}) ⊆ U_K`
(`isPushforwardUpToEmptyAlong_embeddedDesingFam`; the gluing is
`isPushforwardUpToEmptyAlong_toExtensionCompatibleFamily_of_dom` of
`Hironaka/Resolution/Analytic/Wlo09/FamilyPushforward.lean`, from the per-open commutation of
the concrete functor, `BEDanFamStar.closedEmbedding`).

The families of the theorem are those of the ideal sheaves made the unit ideal on the connected
components where they vanish (`unitOnZeroStalks`). Since `J` has nonzero stalks, `𝓘_Y` has nonzero
stalks along `τ(N)`, so the modified ideal sheaf pulls back along `τ` to `J`
(`unitOnZeroStalks_pullback_eq`) and `J` is unchanged (`unitOnZeroStalks_eq_self`); the modified
ideal sheaf still contains the ideal sheaf of `τ(N)` (`le_unitOnZeroStalks`). The class of the
functor is the reduced ideal sheaves with nonzero stalks, and the pull-back to a closed
submanifold of a reduced ideal sheaf containing its ideal sheaf is reduced
(`isReduced_pullback_inclusionMap`: the germ map of the inclusion is surjective with kernel the
stalk of the submanifold's ideal sheaf, and the image of a radical ideal containing the kernel is
radical); so `J` is reduced (`isReduced_pullback_of_diffeomorph_toAnalyticManifold`).

The variants for a nonempty `N` on any `𝕜^m` (`…_of_diffeomorph`, the identification `e` forcing
`m = n − s`) and for an empty `N` on any model (`…_of_isEmpty`) are the forms the assignment on
arbitrary models uses (`Hironaka/Resolution/Analytic/Wlo09/EmbeddedDesingularization.lean`).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

/-! ### Ideal sheaves made the unit ideal on their zero components, along maps -/

namespace AnalyticManifold.IdealSheaf

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (I : IdealSheaf M)

/-- An ideal sheaf lies in itself made the unit ideal on its zero components. -/
theorem le_unitOnZeroStalks : I ≤ I.unitOnZeroStalks :=
  Manifold.IdealSheaf.le_def.mpr fun x => by
    by_cases hx : I.stalkIdeal x = ⊥
    · rw [hx]
      exact bot_le
    · rw [I.stalkIdeal_unitOnZeroStalks_of_ne_bot hx]

/-- An ideal sheaf with nonzero stalks is unchanged by making it the unit ideal on its zero
components. -/
theorem unitOnZeroStalks_eq_self (hI : I.IsNonzeroEverywhere) : I.unitOnZeroStalks = I :=
  Manifold.IdealSheaf.ext fun x => I.stalkIdeal_unitOnZeroStalks_of_ne_bot (hI x)

/-- The pull-back along `τ` of an ideal sheaf made the unit ideal on its zero components is the
pull-back of the ideal sheaf, when the latter has nonzero stalks: the stalks of the ideal sheaf
at the image points are nonzero. -/
theorem unitOnZeroStalks_pullback_eq {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {N : AnalyticManifold.{u} 𝕜 E'} (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯)
    (h : (I.pullback τ τ.contMDiff).IsNonzeroEverywhere) :
    I.unitOnZeroStalks.pullback τ τ.contMDiff = I.pullback τ τ.contMDiff :=
  Manifold.IdealSheaf.ext fun x => by
    rw [Manifold.IdealSheaf.stalkIdeal_pullback, Manifold.IdealSheaf.stalkIdeal_pullback,
      I.stalkIdeal_unitOnZeroStalks_of_ne_bot]
    intro hbot
    apply h x
    rw [Manifold.IdealSheaf.stalkIdeal_pullback, hbot, Ideal.map_bot]

/-- **The pull-back to a closed submanifold of a reduced ideal sheaf containing the submanifold's
ideal sheaf is reduced**: the germ map of the inclusion is surjective
(`germMap_inclusionMap_surjective`) with kernel the stalk of the submanifold's ideal sheaf
(`ker_germMap_inclusionMap'`), and the image under a surjection of a radical ideal containing the
kernel is radical (`Ideal.map_radical_of_surjective`). -/
theorem isReduced_pullback_inclusionMap {n s : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {S : Set M}
    (hS : Manifold.IsClosedSubmanifold ψ S s) (hI : I.IsReduced)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x) :
    IdealSheaf.IsReduced (I.pullback hS.inclusionMap hS.inclusionMap.contMDiff) := by
  intro p
  rw [Manifold.IdealSheaf.stalkIdeal_pullback, ← Ideal.radical_eq_iff,
    ← Ideal.map_radical_of_surjective (hS.germMap_inclusionMap_surjective p)
      (by rw [hS.ker_germMap_inclusionMap' p]; exact hle _),
    Ideal.radical_eq_iff.mpr (hI _)]

end AnalyticManifold.IdealSheaf

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜))
  (I : IdealSheaf M) (hI : I.IsReduced)

/-! ### The reducedness of the pull-back along a closed embedding -/

include hI in
/-- The pull-back along `τ` of a reduced ideal sheaf containing the ideal sheaf of `τ(N)` is
reduced, for `N` identified with the bundled submanifold `τ(N)` by `e` over `τ`: it is the pull-back
along `e` of the reduced pull-back to the bundled submanifold
(`isReduced_pullback_inclusionMap`). -/
theorem isReduced_pullback_of_diffeomorph_toAnalyticManifold {s : ℕ}
    {N : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
    (τ : C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), N; 𝓘(𝕜, Fin n → 𝕜), M⟯)
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Set.range τ) s)
    (e : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) N hS.toAnalyticManifold ω)
    (he : ∀ x, (e x : Set.range τ).1 = τ x)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x) :
    IdealSheaf.IsReduced (I.pullback τ τ.contMDiff) := by
  have hτe : ⇑τ = ⇑hS.inclusionMap ∘ ⇑e := funext fun x => (he x).symm
  have heq : I.pullback τ τ.contMDiff = IdealSheaf.pullbackDiffeomorph e
      (I.pullback hS.inclusionMap hS.inclusionMap.contMDiff) := by
    change _ = Manifold.IdealSheaf.pullback ⇑e e.contMDiff
      (Manifold.IdealSheaf.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff I)
    rw [Manifold.IdealSheaf.pullback_pullback]
    exact Manifold.IdealSheaf.pullback_congr _ _ _ hτe
  rw [heq]
  exact (IdealSheaf.isReduced_pullbackDiffeomorph_iff e _).mpr
    (I.isReduced_pullback_inclusionMap hS hI hle)

include hI in
/-- `isReduced_pullback_of_diffeomorph_toAnalyticManifold` for a nonempty `N` modelled on any
`𝕜^m` (`dim_eq_of_diffeomorph`). -/
theorem isReduced_pullback_of_diffeomorph_toAnalyticManifold' {m s : ℕ}
    {N : AnalyticManifold.{u} 𝕜 (Fin m → 𝕜)} [Nonempty N]
    (τ : C^ω⟮𝓘(𝕜, Fin m → 𝕜), N; 𝓘(𝕜, Fin n → 𝕜), M⟯)
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Set.range τ) s)
    (e : Diffeomorph 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) N hS.toAnalyticManifold ω)
    (he : ∀ x, (e x : Set.range τ).1 = τ x)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x) :
    IdealSheaf.IsReduced (I.pullback τ τ.contMDiff) := by
  obtain ⟨x₀⟩ := ‹Nonempty N›
  obtain rfl : m = n - s := dim_eq_of_diffeomorph e x₀
  exact isReduced_pullback_of_diffeomorph_toAnalyticManifold M I hI τ hS e he hle

/-! ### The push-forward relation on the standard models -/

/-- **The embedded desingularization on the standard models commutes with closed embeddings**,
over every pair of compacts ([Wlo09, Theorem 2.0.2 (4)], "embeddings of ambient varieties", read
as [Kol07, 34.3]): for a closed embedding `τ : N → M` with image a closed submanifold of
codimension `s`, identified with the bundled submanifold by `e` over `τ`, a reduced `𝓘_Y`
containing the ideal sheaf of `τ(N)` and `J = τ^* 𝓘_Y` with nonzero stalks, the succession of the
family of `Y ⊆ M` over `U_K` is the push-forward along `τ` of that of `Y ⊆ N` over `U_{K'}`, up to
blow-ups whose centres lie outside the part over `τ(U_{K'})`, whenever `τ(U_{K'}) ⊆ U_K`. The
families are those of the ideal sheaves made the unit ideal on their zero components, which `J`
is already and which pull back to each other along `τ`; the gluing is
`isPushforwardUpToEmptyAlong_toExtensionCompatibleFamily_of_dom` from the per-open commutation
`BEDanFamStar.closedEmbedding` of the concrete functor. -/
theorem isPushforwardUpToEmptyAlong_embeddedDesingFam {s : ℕ}
    {N : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
    (τ : C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), N; 𝓘(𝕜, Fin n → 𝕜), M⟯)
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Set.range τ) s)
    (e : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) N hS.toAnalyticManifold ω)
    (he : ∀ x, (e x : Set.range τ).1 = τ x)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x)
    (J : IdealSheaf N) (hJ : J.IsNonzeroEverywhere) (hJI : J = I.pullback τ τ.contMDiff)
    (hJr : J.IsReduced) (K' : Compacts N) (K : Compacts M)
    (hK : ⇑τ '' ((embeddedDesingFam N J hJr).nhd K' : Set N) ⊆ (embeddedDesingFam M I hI).nhd K) :
    ((embeddedDesingFam M I hI).seq K).IsPushforwardUpToEmptyAlong
      ((embeddedDesingFam N J hJr).seq K') τ := by
  have hI' : I.unitOnZeroStalks.IsReduced := I.isReduced_unitOnZeroStalks hI
  have hI'₀ : I.unitOnZeroStalks.IsNonzeroEverywhere := I.isNonzeroEverywhere_unitOnZeroStalks
  have hJ'₀ : J.unitOnZeroStalks.IsNonzeroEverywhere := J.isNonzeroEverywhere_unitOnZeroStalks
  have hle' : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.unitOnZeroStalks.stalkIdeal x :=
    fun x => (hle x).trans (Manifold.IdealSheaf.le_def.mp I.le_unitOnZeroStalks x)
  have hJI' : J.unitOnZeroStalks = I.unitOnZeroStalks.pullback τ τ.contMDiff := by
    rw [J.unitOnZeroStalks_eq_self hJ, hJI, I.unitOnZeroStalks_pullback_eq τ (hJI ▸ hJ)]
  exact isPushforwardUpToEmptyAlong_toExtensionCompatibleFamily_of_dom
    ((concreteBEDanFamStar.{u} 𝕜).closedEmbedding n s)
    ((concreteBEDanFamStar_isEmbeddedDesing.{u} 𝕜).2 (n - s)) τ hS e he I.unitOnZeroStalks hI'₀
    hle' J.unitOnZeroStalks hJ'₀ hJI' (domBEDan_embeddedTriple _ hI' hI'₀)
    (domBEDan_embeddedTriple _ (J.isReduced_unitOnZeroStalks hJr) hJ'₀)
    (fun h => domBEDan_embeddedTriple _ (I.unitOnZeroStalks.isReduced_pullback_inclusionMap hS
      hI' hle') h) K' K hK

/-- `isPushforwardUpToEmptyAlong_embeddedDesingFam` for a nonempty `N` modelled on any `𝕜^m`: the
identification `e` of `N` with the bundled submanifold of codimension `s` forces `m = n − s`
(`dim_eq_of_diffeomorph`). -/
theorem isPushforwardUpToEmptyAlong_embeddedDesingFam_of_diffeomorph {m s : ℕ}
    {N : AnalyticManifold.{u} 𝕜 (Fin m → 𝕜)} [Nonempty N]
    (τ : C^ω⟮𝓘(𝕜, Fin m → 𝕜), N; 𝓘(𝕜, Fin n → 𝕜), M⟯)
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Set.range τ) s)
    (e : Diffeomorph 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) N hS.toAnalyticManifold ω)
    (he : ∀ x, (e x : Set.range τ).1 = τ x)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x)
    (J : IdealSheaf N) (hJ : J.IsNonzeroEverywhere) (hJI : J = I.pullback τ τ.contMDiff)
    (hJr : J.IsReduced) (K' : Compacts N) (K : Compacts M)
    (hK : ⇑τ '' ((embeddedDesingFam N J hJr).nhd K' : Set N) ⊆ (embeddedDesingFam M I hI).nhd K) :
    ((embeddedDesingFam M I hI).seq K).IsPushforwardUpToEmptyAlong
      ((embeddedDesingFam N J hJr).seq K') τ := by
  obtain ⟨x₀⟩ := ‹Nonempty N›
  obtain rfl : m = n - s := dim_eq_of_diffeomorph e x₀
  exact isPushforwardUpToEmptyAlong_embeddedDesingFam M I hI τ hS e he hle J hJ hJI hJr K' K hK

/-- `isPushforwardUpToEmptyAlong_embeddedDesingFam` for an empty `N` modelled on any space: both
successions are empty (`isPushforwardUpToEmptyAlong_seqOn_of_isEmpty_of_dom`). -/
theorem isPushforwardUpToEmptyAlong_embeddedDesingFam_of_isEmpty {s : ℕ} {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    {N : AnalyticManifold.{u} 𝕜 E'} [IsEmpty N]
    (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, Fin n → 𝕜), M⟯)
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Set.range τ) s)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x)
    (F : ExtensionCompatibleFamily N) (hF : ∀ K' : Compacts N, (F.seq K').NoEmptyCenters)
    (K' : Compacts N) (K : Compacts M) :
    ((embeddedDesingFam M I hI).seq K).IsPushforwardUpToEmptyAlong (F.seq K') τ := by
  have hI' : I.unitOnZeroStalks.IsReduced := I.isReduced_unitOnZeroStalks hI
  have hI'₀ : I.unitOnZeroStalks.IsNonzeroEverywhere := I.isNonzeroEverywhere_unitOnZeroStalks
  have hle' : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.unitOnZeroStalks.stalkIdeal x :=
    fun x => (hle x).trans (Manifold.IdealSheaf.le_def.mp I.le_unitOnZeroStalks x)
  exact isPushforwardUpToEmptyAlong_seqOn_of_isEmpty_of_dom
    ((concreteBEDanFamStar.{u} 𝕜).closedEmbedding n s) τ hS I.unitOnZeroStalks hI'₀ hle'
    (domBEDan_embeddedTriple _ hI' hI'₀)
    (fun h => domBEDan_embeddedTriple _ (I.unitOnZeroStalks.isReduced_pullback_inclusionMap hS
      hI' hle') h) (F.seq K') (hF K') _ _

end Hironaka.Manifold

end

end
