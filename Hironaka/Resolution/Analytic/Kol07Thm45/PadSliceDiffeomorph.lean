/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Restrict
public import Hironaka.Resolution.Analytic.Kol07Thm45.PadIdeal
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The coordinate slice of a padding is the piece: the slice diffeomorphism

Kollár's proof of Theorem 36 passes from an embedding `X ↪ 𝔸ⁿ` to its padding `X ↪ 𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ`
(the embedding `i'_1` of [Kol07, Lemma 39]) and back through the weak commutation with closed
embeddings [Kol07, 34.4]: the resolution of the padded ideal on the padded ambient is the
push-forward of the resolution on the coordinate slice `S = {z_j = 0, j ∉ range σ}`
([Kol07, Theorem 36, proof]; the common ambient dimension of [Wlo09, §7.1]). On the slice, read
as a bundled submanifold with its induced charts (`IsClosedSubmanifold.toAnalyticManifold`,
modelled on `𝕜^{n' − (n' − n)}`), the padded ideal restricts to the original ideal: this module
proves that identification.

* `padExtDiffeomorph σ G`: the zero extension `padExt` corestricted to the slice, as a
  DIFFEOMORPHISM of the piece onto the bundled slice — across the two models `𝕜ⁿ` and
  `𝕜^{n' − (n' − n)}` (`IsClosedSubmanifold.contMDiff_codRestrict` for the analyticity into the
  induced charts; inverse the coordinate projection after the inclusion);
  `inclusionMap_padExtDiffeomorph`, `padExtDiffeomorph_symm_apply` its point formulas.
* `pullback_padExt_padIdeal`: `s^*(p^* J + 𝓘_S) = J` — the padded ideal pulled back along the
  zero extension is the ideal (`stalkIdeal_padIdeal_padExt` with the surjectivity of the germ maps
  of `s`, `padExtStalk_padCoordProjStalk`).
* `pullback_inclusionMap_padIdeal`: the padded ideal restricted to the slice (the pull-back along
  the inclusion) is `J` transported along the inverse of the slice diffeomorphism — both sides
  pull back along the diffeomorphism to `J`, and pulling back along a diffeomorphism is injective
  (`IdealSheaf.pullback_symm_pullback`).
* `idealSheaf_padSlice_le_padIdeal`: `𝓘_S ≤ p^* J + 𝓘_S`.

Not in the sources; bookkeeping on the padding of `PadIdeal.lean` and the bundled submanifolds of
`Bundle.lean`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n n' : ℕ} (σ : Fin n ↪ Fin n') (G : Opens (Fin n → 𝕜))

/-- **The zero extension as a diffeomorphism of the piece onto the coordinate slice**
`S = {z_j = 0, j ∉ range σ}` with its induced structure (`IsClosedSubmanifold.toAnalyticManifold`,
modelled on `𝕜^{n' − (n' − n)}`) — ACROSS MODELS (`Fin n → 𝕜` against `Fin (n' − (n' − n)) → 𝕜`);
inverse the coordinate projection after the inclusion. The identification of `Y` with its copy in
`U × 𝕜ᵐ` of [Wlo09, §7.1], and of `X ↪ 𝔸ⁿ` with `X ↪ 𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ` in [Kol07, Theorem 36, proof]. -/
def padExtDiffeomorph :
    Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin (n' - (n' - n)) → 𝕜) (pieceAmbient.{u} 𝕜 G)
      (isClosedSubmanifold_padSlice.{u} σ G).toAnalyticManifold ω where
  toFun := Set.codRestrict (padExt σ G) (padSlice σ G) (padExt_mem_padSlice σ G)
  invFun p := padCoordProj σ G ((isClosedSubmanifold_padSlice σ G).inclusionMap p)
  left_inv w := padCoordProj_padExt σ G w
  right_inv p := Subtype.ext (padExt_padCoordProj_of_mem σ G p.2)
  contMDiff_toFun :=
    (isClosedSubmanifold_padSlice σ G).contMDiff_codRestrict (contMDiff_padExt σ G)
      (padExt_mem_padSlice σ G)
  contMDiff_invFun :=
    (contMDiff_padCoordProj σ G).comp (isClosedSubmanifold_padSlice σ G).inclusionMap.contMDiff

/-- The slice diffeomorphism followed by the inclusion is the zero extension. -/
theorem inclusionMap_padExtDiffeomorph (w : pieceAmbient.{u} 𝕜 G) :
    (isClosedSubmanifold_padSlice.{u} σ G).inclusionMap (padExtDiffeomorph σ G w) =
      padExt σ G w :=
  rfl

/-- The inverse of the slice diffeomorphism is the coordinate projection. -/
theorem padExtDiffeomorph_symm_apply
    (p : (isClosedSubmanifold_padSlice.{u} σ G).toAnalyticManifold) :
    (padExtDiffeomorph σ G).symm p =
      padCoordProj σ G ((isClosedSubmanifold_padSlice.{u} σ G).inclusionMap p) :=
  rfl

variable (J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 G))

/-- **The padded ideal pulled back along the zero extension is the ideal**: at `w`,
`s^*(p^* J + 𝓘_S)_{s w} = s^* (s^*)⁻¹ J_w = J_w` (`stalkIdeal_padIdeal_padExt`; the germ map of
`s` is onto, `p ∘ s = id`). -/
theorem pullback_padExt_padIdeal :
    (padIdeal σ J).pullback (padExt σ G) (contMDiff_padExt σ G) = J :=
  IdealSheaf.ext fun w => by
    rw [IdealSheaf.stalkIdeal_pullback, stalkIdeal_padIdeal_padExt]
    exact Ideal.map_comap_of_surjective _
      (fun x => ⟨padCoordProjStalk σ w x, padExtStalk_padCoordProjStalk σ w x⟩) _

/-- **The slice ideal is the piece ideal transported**: the padded ideal restricted to the slice
(the pull-back along the inclusion) is the pull-back of `J` along the inverse of the slice
diffeomorphism. Both sides pull back along `padExtDiffeomorph` to `J` (`pullback_padExt_padIdeal`,
`IdealSheaf.pullback_symm_pullback`), and pulling back along a diffeomorphism is injective. -/
theorem pullback_inclusionMap_padIdeal :
    (padIdeal σ J).pullback ⇑(isClosedSubmanifold_padSlice.{u} σ G).inclusionMap
        (isClosedSubmanifold_padSlice.{u} σ G).inclusionMap.contMDiff =
      J.pullback ⇑(padExtDiffeomorph σ G).symm (padExtDiffeomorph σ G).symm.contMDiff := by
  set g := padExtDiffeomorph σ G with hg
  -- pulling back along `g` and then along `g⁻¹` is the identity on the slice's ideal sheaves
  have hinv : ∀ A :
      AnalyticManifold.IdealSheaf (isClosedSubmanifold_padSlice.{u} σ G).toAnalyticManifold,
      (A.pullback ⇑g g.contMDiff).pullback ⇑g.symm g.symm.contMDiff = A := fun A =>
    (IdealSheaf.pullback_pullback A _ _ _ _).trans
      ((IdealSheaf.pullback_congr A _ contMDiff_id
        (funext fun x => g.apply_symm_apply x)).trans (IdealSheaf.pullback_id_eq_self A))
  -- the left-hand side pulled back along `g` is `J`
  have hL : ((padIdeal σ J).pullback ⇑(isClosedSubmanifold_padSlice.{u} σ G).inclusionMap
      (isClosedSubmanifold_padSlice.{u} σ G).inclusionMap.contMDiff).pullback ⇑g g.contMDiff = J :=
    (IdealSheaf.pullback_pullback (padIdeal σ J) _ _ _ _).trans
      ((IdealSheaf.pullback_congr (padIdeal σ J) _ (contMDiff_padExt σ G)
        (funext fun w => inclusionMap_padExtDiffeomorph σ G w)).trans
          (pullback_padExt_padIdeal σ G J))
  rw [← hinv ((padIdeal σ J).pullback _ _), hL]

/-- The ideal sheaf of the slice lies in the padded ideal (`padIdeal` is the sum `p^*J + 𝓘_S`). -/
theorem idealSheaf_padSlice_le_padIdeal :
    (isClosedSubmanifold_padSlice.{u} σ G).idealSheaf ≤ padIdeal σ J :=
  IdealSheaf.le_def.mpr fun x => by
    rw [stalkIdeal_padIdeal]
    exact le_sup_right

end Hironaka.Manifold

end
