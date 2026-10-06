/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceEmbedding
public import Hironaka.Manifold.Submanifold
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.Manifold.Comap
import Hironaka.AnalyticSpace.Manifold.Sigma
import Hironaka.AnalyticSpace.SigmaLemmas
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.StrictSmooth
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaDesc
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Padding a local model: the ideal of a piece in more variables

A closed analytic subset `Y ⊆ U ⊆ 𝕜ⁿ` is also a closed analytic subset of `U × 𝕜ᵐ ⊆ 𝕜ⁿ⁺ᵐ`, with
the equations `z_{n+1} = ⋯ = z_{n+m} = 0` added. This is how Włodarczyk brings the local models
of an analytic space to a common ambient dimension [Wlo09, §7.1], and how Kollár is free to
enlarge the affine space of an embedding, `𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ`, when proving that the resolution does not
depend on the embedding [Kol07, Theorem 36, proof]. The construction is used twice: the existence
proof of local embedding data (`PieceModel.lean`) pads local models whose ideal may be zero to a
common dimension, and the comparison of two embeddings of a piece pads a piece embedding on either
side (`PieceEmbedding.padLeft`, `PieceEmbedding.padRight` in `PieceIndependence.lean`). It is
therefore stated for an IDEAL sheaf on a one-piece ambient (`pieceAmbient`), not for a
`PieceEmbedding`, and indexed by an arbitrary embedding of coordinates `σ : Fin n ↪ Fin n'`
(`σ := Fin.castLEEmb` keeps the given coordinates as the first `n`, `σ := Fin.natAddEmb` as the
last `n`).

For `G ⊆ 𝕜ⁿ` open, `J` an ideal sheaf on `pieceAmbient 𝕜 G` and `σ : Fin n ↪ Fin n'`:

* `padOpens σ G := {z ∈ 𝕜ⁿ' | z ∘ σ ∈ G}` and `padIdeal σ J`, the pullback of `J` along the
  coordinate projection `p : z ↦ z ∘ σ` joined with the ideal sheaf `𝓘_S` of the coordinate slice
  `S := {z | z_j = 0 for j ∉ range σ}` — a closed submanifold of codimension `n' − n`
  (`isClosedSubmanifold_padSlice`; its ideal sheaf is `IsClosedSubmanifold.idealSheaf`, whose
  stalks are the germs vanishing on `S`, spanned by the complementary coordinates).
* The slice isomorphism `padSliceHom : Sp(padOpens σ G)/padIdeal σ J ≅ Sp(G)/J`
  (`isIso_padSliceHom`, `padSliceIso`): the functoriality of the closed subspace along `Sp(p)`
  (`p^*J ≤ padIdeal σ J`, `QuotientSpace.map`). It is an isomorphism because the zero extension
  `s : w ↦ (w on range σ, 0 off it)` is a section of `p` with image `S`: on points, `p` and `s`
  are inverse homeomorphisms between the two supports; on stalks, the fibre map
  `𝒪_{n,w}/J_w → 𝒪_{n',s(w)}/(p^*J + 𝓘_S)_{s(w)}` is bijective since
  `(p^*J + 𝓘_S)_{s(w)} = (s^*)⁻¹ J_w` (`stalkIdeal_padIdeal_padExt`): `s^* ∘ p^* = id`, `s^*` kills
  `𝓘_S`, and every germ `g` at `s(w)` is congruent to `p^*(s^* g)` modulo `𝓘_S` (the difference
  vanishes on `S`). This is the one piece of algebra of the padding; it is done once here.
* `isReduced_padIdeal`: `padIdeal σ J` is reduced when `J` is — its stalks on `S` are `(s^*)⁻¹` of
  radical ideals, off `S` the unit ideal.
* `isNonzeroEverywhere_padIdeal`: for `σ` not surjective, `padIdeal σ J` is nonzero at every
  stalk — a complementary coordinate germ lies in `𝓘_S ⊆ padIdeal σ J` and is nonzero
  (`coord_ne_zero`); `isNonzeroEverywhere_padIdeal_castLE` is the `Fin.castLEEmb` case for
  `n < n'`. This is how the padding coordinate supplies `PieceEmbedding.isNonzeroEverywhere` for a
  smooth piece with no equations.

Conventions: the one-piece ambient `pieceAmbient 𝕜 G` (points `⟨(), z⟩`); the linear chart of
`𝕜ⁿ'` is the identity (`ContinuousLinearEquiv.refl`). Boundary cases: `σ` surjective (`n = n'`)
gives a slice equal to the whole ambient, so that the complement of `S` is empty — the padded
open, the padded ideal, the slice isomorphism and the reducedness hold, the nonvanishing needs
`¬ Surjective σ`; `J = ⊥` (a smooth piece with no equations) is allowed, and the nonvanishing is
then the only source of `IsNonzeroEverywhere` for the padded ideal. Not in the sources beyond the
remarks cited; the algebra is elementary.
-/

@[expose] public section

open TopologicalSpace Filter CategoryTheory
open scoped Manifold ContDiff Topology

universe u

noncomputable section

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n n' : ℕ} (σ : Fin n ↪ Fin n') (G : Opens (Fin n → 𝕜))

/-! ### The padded open, the projection and the zero extension -/

/-- **The padded open** `{z ∈ 𝕜ⁿ' | z ∘ σ ∈ G}`, the preimage of `G` under the coordinate
projection along `σ` — for `σ = Fin.castLEEmb`, the `U × 𝕜ᵐ` of [Wlo09, §7.1]. -/
def padOpens : Opens (Fin n' → 𝕜) :=
  ⟨(fun z : Fin n' → 𝕜 => z ∘ σ) ⁻¹' (G : Set (Fin n → 𝕜)),
    G.isOpen.preimage (continuous_pi fun i => continuous_apply (σ i))⟩

theorem mem_padOpens {z : Fin n' → 𝕜} : z ∈ padOpens σ G ↔ z ∘ σ ∈ G := Iff.rfl

/-- The coordinate projection `p : z ↦ z ∘ σ` on the one-piece ambients. -/
def padCoordProj : pieceAmbient.{u} 𝕜 (padOpens σ G) → pieceAmbient.{u} 𝕜 G :=
  fun x => ⟨x.1, ⟨(x.2 : Fin n' → 𝕜) ∘ σ, x.2.2⟩⟩

theorem padCoordProj_snd (x : pieceAmbient.{u} 𝕜 (padOpens σ G)) :
    ((padCoordProj σ G x).2 : Fin n → 𝕜) = (x.2 : Fin n' → 𝕜) ∘ σ := rfl

theorem extend_comp (w : Fin n → 𝕜) : Function.extend σ w 0 ∘ σ = w :=
  funext fun i => σ.injective.extend_apply _ _ i

theorem extend_mem_padOpens (w : G) : Function.extend σ (w : Fin n → 𝕜) 0 ∈ padOpens σ G := by
  change Function.extend σ (w : Fin n → 𝕜) 0 ∘ σ ∈ G
  rw [extend_comp]
  exact w.2

/-- The zero extension `s : w ↦ (w on range σ, 0 off it)`, a section of `padCoordProj` with image
the coordinate slice `padSlice`. -/
def padExt : pieceAmbient.{u} 𝕜 G → pieceAmbient.{u} 𝕜 (padOpens σ G) :=
  fun w => ⟨w.1, ⟨Function.extend σ (w.2 : Fin n → 𝕜) 0, extend_mem_padOpens σ G w.2⟩⟩

theorem padExt_snd (w : pieceAmbient.{u} 𝕜 G) :
    ((padExt σ G w).2 : Fin n' → 𝕜) = Function.extend σ (w.2 : Fin n → 𝕜) 0 := rfl

theorem padExt_apply_of_notMem_range (w : pieceAmbient.{u} 𝕜 G) {j : Fin n'}
    (hj : j ∉ Set.range σ) : ((padExt σ G w).2 : Fin n' → 𝕜) j = 0 :=
  Function.extend_apply' _ _ _ hj

theorem padCoordProj_padExt (w : pieceAmbient.{u} 𝕜 G) : padCoordProj σ G (padExt σ G w) = w :=
  Sigma.ext rfl (heq_of_eq (Subtype.ext (extend_comp σ _)))

theorem padCoordProj_comp_padExt : padCoordProj.{u} σ G ∘ padExt σ G = id :=
  funext (padCoordProj_padExt σ G)

/-! ### The coordinate slice `S = {z_j = 0 for j ∉ range σ}` -/

/-- The coordinate slice: the points of the padded ambient whose coordinates off `range σ`
vanish — the image of the zero extension `padExt`. -/
def padSlice : Set (pieceAmbient.{u} 𝕜 (padOpens σ G)) :=
  {x | ∀ j, j ∉ Set.range σ → (x.2 : Fin n' → 𝕜) j = 0}

theorem padExt_mem_padSlice (w : pieceAmbient.{u} 𝕜 G) : padExt σ G w ∈ padSlice σ G :=
  fun _ hj => padExt_apply_of_notMem_range σ G w hj

theorem padExt_padCoordProj_of_mem {x : pieceAmbient.{u} 𝕜 (padOpens σ G)}
    (hx : x ∈ padSlice σ G) : padExt σ G (padCoordProj σ G x) = x := by
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext (funext fun j => ?_)))
  change Function.extend σ ((x.2 : Fin n' → 𝕜) ∘ σ) 0 j = (x.2 : Fin n' → 𝕜) j
  by_cases hj : j ∈ Set.range σ
  · obtain ⟨i, rfl⟩ := hj
    exact σ.injective.extend_apply _ _ i
  · rw [Function.extend_apply' _ _ _ hj]
    exact (hx j hj).symm

theorem isClosed_padSlice : IsClosed (padSlice.{u} σ G) := by
  have h : padSlice σ G = ⋂ j : {j : Fin n' // j ∉ Set.range σ},
      (fun x : pieceAmbient.{u} 𝕜 (padOpens σ G) => (x.2 : Fin n' → 𝕜) j.1) ⁻¹' {0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff, Subtype.forall]
    exact Iff.rfl
  rw [h]
  refine isClosed_iInter fun j => isClosed_singleton.preimage ?_
  exact (continuous_apply j.1).comp
    (continuous_subtype_val.comp (continuous_sigma fun _ => continuous_id))

/-- The complementary coordinates `Fin (n' - n) ↪ Fin n'`, enumerating `(range σ)ᶜ` through
`complEquiv`. -/
def padCompl : Fin (n' - n) ↪ Fin n' :=
  ⟨fun k => ((complEquiv σ).symm k).1, fun _ _ h => (complEquiv σ).symm.injective (Subtype.ext h)⟩

theorem padCompl_notMem_range (k : Fin (n' - n)) : padCompl σ k ∉ Set.range σ :=
  ((complEquiv σ).symm k).2

theorem forall_padCompl_iff {z : Fin n' → 𝕜} :
    (∀ k, z (padCompl σ k) = 0) ↔ ∀ j, j ∉ Set.range σ → z j = 0 := by
  constructor
  · intro h j hj
    have := h (complEquiv σ ⟨j, hj⟩)
    change z ((complEquiv σ).symm (complEquiv σ ⟨j, hj⟩)).1 = 0 at this
    rwa [Equiv.symm_apply_apply] at this
  · intro h k
    exact h _ (padCompl_notMem_range σ k)

/-- The chart of the padded one-piece ambient at any point is the coordinate inclusion
`⟨(), z⟩ ↦ z` (the lifted chart of the open `padOpens σ G ⊆ 𝕜ⁿ'`). -/
theorem chartAt_pieceAmbient_apply (x y : pieceAmbient.{u} 𝕜 (padOpens σ G)) :
    chartAt (Fin n' → 𝕜) x y = (y.2 : Fin n' → 𝕜) := by
  have e := ChartedSpace.sigma_chartAt (H := Fin n' → 𝕜)
    (M := fun _ : PUnit.{u + 1} => (padOpens σ G : Type))
    (⟨x.1, x.2⟩ : Σ _ : PUnit.{u + 1}, (padOpens σ G : Type))
  change chartAt (Fin n' → 𝕜) (⟨x.1, x.2⟩ : Σ _ : PUnit.{u + 1}, (padOpens σ G : Type))
    (⟨x.1, y.2⟩ : Σ _ : PUnit.{u + 1}, (padOpens σ G : Type)) = (y.2 : Fin n' → 𝕜)
  rw [e]
  exact (OpenPartialHomeomorph.lift_openEmbedding_apply _ _).trans rfl

/-- The chart at any point of the padded ambient is adapted to the slice, with the complementary
coordinates as the vanishing ones. -/
theorem isAdaptedChart_chartAt (x : pieceAmbient.{u} 𝕜 (padOpens σ G)) :
    IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜)) (padSlice σ G)
      (chartAt (Fin n' → 𝕜) x) (padCompl σ) := by
  refine ⟨IsManifold.chart_mem_maximalAtlas x, fun y _ => ?_⟩
  rw [chartAt_pieceAmbient_apply]
  exact (forall_padCompl_iff σ).symm

/-- **The coordinate slice is a closed submanifold** of codimension `n' − n` of the padded
ambient, with the coordinate charts as adapted charts. -/
theorem isClosedSubmanifold_padSlice :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜)) (padSlice.{u} σ G)
      (n' - n) where
  isClosed := isClosed_padSlice σ G
  exists_adaptedChart a _ :=
    ⟨chartAt (Fin n' → 𝕜) a, padCompl σ, mem_chart_source _ a, isAdaptedChart_chartAt σ G a⟩

/-! ### Analyticity of the projection and of the zero extension -/

theorem contMDiff_padCoordProj :
    ContMDiff 𝓘(𝕜, Fin n' → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (padCoordProj.{u} σ G) := by
  have h : ContMDiff 𝓘(𝕜, Fin n' → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      (fun z : padOpens σ G => (⟨(z : Fin n' → 𝕜) ∘ σ, z.2⟩ : G)) := by
    rw [← AnalyticSpace.KLocallyRingedSpace.contMDiff_subtypeVal_comp_iff']
    exact (contMDiff_iff_contDiff.mpr (contDiff_pi.mpr fun i => contDiff_apply 𝕜 _ (σ i))).comp
      contMDiff_subtype_val
  exact ContMDiff.sigmaDesc (M := fun _ : PUnit.{u + 1} => (padOpens σ G : Type))
    (P := Σ _ : PUnit.{u + 1}, (G : Type))
    (f := fun i => Sigma.mk i ∘ fun z : padOpens σ G => (⟨(z : Fin n' → 𝕜) ∘ σ, z.2⟩ : G))
    fun _ => contMDiff_sigmaMk_comp_iff.mpr h

theorem contDiff_extend : ContDiff 𝕜 ω fun w : Fin n → 𝕜 => Function.extend σ w 0 := by
  refine contDiff_pi.mpr fun j => ?_
  by_cases hj : ∃ i, σ i = j
  · obtain ⟨i, rfl⟩ := hj
    simp only [σ.injective.extend_apply]
    exact contDiff_apply 𝕜 _ i
  · simp only [Function.extend_apply' _ _ _ hj, Pi.zero_apply]
    exact contDiff_const

theorem contMDiff_padExt :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n' → 𝕜) ω (padExt.{u} σ G) := by
  have h : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n' → 𝕜) ω
      (fun w : G => (⟨Function.extend σ (w : Fin n → 𝕜) 0, extend_mem_padOpens σ G w⟩ :
        padOpens σ G)) := by
    rw [← AnalyticSpace.KLocallyRingedSpace.contMDiff_subtypeVal_comp_iff']
    exact (contMDiff_iff_contDiff.mpr (contDiff_extend σ)).comp contMDiff_subtype_val
  exact ContMDiff.sigmaDesc (M := fun _ : PUnit.{u + 1} => (G : Type))
    (P := Σ _ : PUnit.{u + 1}, (padOpens σ G : Type))
    (f := fun i => Sigma.mk i ∘ fun w : G =>
      (⟨Function.extend σ (w : Fin n → 𝕜) 0, extend_mem_padOpens σ G w⟩ : padOpens σ G))
    fun _ => contMDiff_sigmaMk_comp_iff.mpr h

/-! ### The padded ideal -/

variable {G} (J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 G))

/-- **The padded ideal** `p^*J + 𝓘_S` on `padOpens σ G`: the pullback of `J` along the
coordinate projection joined with the ideal sheaf of the coordinate slice (the equations `z_j = 0`,
`j ∉ range σ`) — the ideal of `Y ⊆ U × 𝕜ᵐ` in [Wlo09, §7.1]. -/
def padIdeal : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 (padOpens σ G)) :=
  J.pullback (padCoordProj σ G) (contMDiff_padCoordProj σ G) +
    (isClosedSubmanifold_padSlice σ G).idealSheaf

theorem stalkIdeal_padIdeal (x : pieceAmbient.{u} 𝕜 (padOpens σ G)) :
    (padIdeal σ J).stalkIdeal x =
      Ideal.map (germMap (padCoordProj σ G) (contMDiff_padCoordProj σ G) x)
          (J.stalkIdeal (padCoordProj σ G x)) ⊔
        (isClosedSubmanifold_padSlice σ G).idealSheaf.stalkIdeal x := by
  rw [padIdeal, IdealSheaf.stalkIdeal_add, IdealSheaf.stalkIdeal_pullback]

theorem pullback_le_padIdeal :
    J.pullback (padCoordProj σ G) (contMDiff_padCoordProj σ G) ≤ padIdeal σ J :=
  IdealSheaf.le_def.mpr fun x => by
    rw [stalkIdeal_padIdeal, IdealSheaf.stalkIdeal_pullback]
    exact le_sup_left

theorem mem_padSlice_of_mem_cosupport {x : pieceAmbient.{u} 𝕜 (padOpens σ G)}
    (hx : x ∈ (padIdeal σ J).support) : x ∈ padSlice σ G := by
  rw [IdealSheaf.mem_support] at hx
  by_contra h
  refine hx ?_
  rw [stalkIdeal_padIdeal, (isClosedSubmanifold_padSlice σ G).stalkIdeal_idealSheaf_of_notMem h,
    sup_top_eq]

theorem padCoordProj_mem_cosupport {x : pieceAmbient.{u} 𝕜 (padOpens σ G)}
    (hx : x ∈ (padIdeal σ J).support) : padCoordProj σ G x ∈ J.support := by
  rw [IdealSheaf.mem_support] at hx ⊢
  intro h
  refine hx (top_le_iff.mp ?_)
  rw [stalkIdeal_padIdeal, h, Ideal.map_top]
  exact le_sup_left

/-! ### The stalk maps `s^*`, `p^*` and the transport along `p (s w) = w` -/

section Stalks

variable (w : pieceAmbient.{u} 𝕜 G)

/-- `p^*` at `s w`, read at `w` through `p (s w) = w`: `𝒪_{n,w} →+* 𝒪_{n',s w}` (`germMapOn`
with a chosen target point). -/
def padCoordProjStalk :
    AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 G) w →+*
      AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 (padOpens σ G))
          (padExt σ G w) :=
  germMapOn (padCoordProj σ G) (contMDiff_padCoordProj σ G).contMDiffOn
    (Opens.mem_top (padExt σ G w)) (padCoordProj_padExt σ G w)

/-- The transport `𝒪_{n,w} →+* 𝒪_{n,p (s w)}` along `p (s w) = w` (the stalk map of the identity
with the chosen target point). -/
def padTransport :
    AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 G) w →+*
      AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 G)
          (padCoordProj σ G (padExt σ G w)) :=
  germMapOn (fun y => y) contMDiff_id.contMDiffOn (Opens.mem_top (padCoordProj σ G (padExt σ G w)))
    (padCoordProj_padExt σ G w)

/-- The inverse transport `𝒪_{n,p (s w)} →+* 𝒪_{n,w}`. -/
def padTransport' :
    AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 G)
        (padCoordProj σ G (padExt σ G w)) →+*
      AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 G) w :=
  germMapOn (fun y => y) contMDiff_id.contMDiffOn (Opens.mem_top w) (padCoordProj_padExt σ G w).symm

/-- `s^* ∘ p^* = id` on stalks (`p ∘ s = id`). -/
theorem padExtStalk_padCoordProjStalk
    (x : AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 G) w) :
    germMap (padExt σ G) (contMDiff_padExt σ G) w (padCoordProjStalk σ w x) = x :=
  (germMapOn_germMapOn (contMDiff_padCoordProj σ G).contMDiffOn (contMDiff_padExt σ G).contMDiffOn
    (Opens.mem_top w) rfl (Opens.mem_top _) (padCoordProj_padExt σ G w)
    ((contMDiff_padCoordProj σ G).comp (contMDiff_padExt σ G)).contMDiffOn (Opens.mem_top w)
    (padCoordProj_padExt σ G w) x).trans
  ((germMapOn_congr _ contMDiff_id.contMDiffOn (Opens.mem_top w) (padCoordProj_padExt σ G w) rfl
    (fun y _ => padCoordProj_padExt σ G y) x).trans (germMap_id w x))

/-- The two transports are inverse. -/
theorem padTransport_padTransport'
    (x :
        AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 G)
            (padCoordProj σ G (padExt σ G w))) :
    padTransport σ w (padTransport' σ w x) = x :=
  (germMapOn_germMapOn contMDiff_id.contMDiffOn contMDiff_id.contMDiffOn
    (Opens.mem_top (padCoordProj σ G (padExt σ G w))) (padCoordProj_padExt σ G w) (Opens.mem_top w)
    (padCoordProj_padExt σ G w).symm (contMDiff_id.comp contMDiff_id).contMDiffOn
    (Opens.mem_top _) rfl x).trans
  ((germMapOn_congr _ contMDiff_id.contMDiffOn (Opens.mem_top _) rfl rfl (fun _ _ => rfl) x).trans
    (germMap_id _ x))

/-- `p^*` at `s w` (`germMap`, landing at `p (s w)`) composed with the transport is
`padCoordProjStalk`. -/
theorem germMap_padCoordProj_padTransport
    (x : AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 G) w) :
    germMap (padCoordProj σ G) (contMDiff_padCoordProj σ G) (padExt σ G w) (padTransport σ w x) =
      padCoordProjStalk σ w x :=
  (germMapOn_germMapOn contMDiff_id.contMDiffOn (contMDiff_padCoordProj σ G).contMDiffOn
    (Opens.mem_top (padExt σ G w)) rfl (Opens.mem_top _) (padCoordProj_padExt σ G w)
    (contMDiff_id.comp (contMDiff_padCoordProj σ G)).contMDiffOn (Opens.mem_top _)
    (padCoordProj_padExt σ G w) x).trans
  (germMapOn_congr _ (contMDiff_padCoordProj σ G).contMDiffOn (Opens.mem_top _)
    (padCoordProj_padExt σ G w) (padCoordProj_padExt σ G w) (fun _ _ => rfl) x)

/-- The transport carries `J_w` onto `J_{p (s w)}` (the transport of stalk ideals along an
equality of points). -/
theorem map_padTransport_stalkIdeal :
    Ideal.map (padTransport σ w) (J.stalkIdeal w) =
      J.stalkIdeal (padCoordProj σ G (padExt σ G w)) := by
  have h1 := germMapOn_map_stalkIdeal_congr (φ := fun y : pieceAmbient.{u} 𝕜 G => y)
    contMDiff_id.contMDiffOn (Opens.mem_top (padCoordProj σ G (padExt σ G w)))
    (padCoordProj_padExt σ G w).symm (padCoordProj_padExt σ G w) rfl J
  have h2 : germMapOn (fun y : pieceAmbient.{u} 𝕜 G => y)
      (contMDiff_id (I := 𝓘(𝕜, Fin n → 𝕜))).contMDiffOn
      (Opens.mem_top (padCoordProj σ G (padExt σ G w))) rfl = RingHom.id _ :=
    RingHom.ext fun x => germMap_id (E := Fin n → 𝕜) (padCoordProj σ G (padExt σ G w)) x
  rw [h2, Ideal.map_id] at h1
  exact h1

/-- `s^*` kills the ideal of the slice: a germ vanishing on `S` composed with `s` is zero. -/
theorem germMap_padExt_eq_zero_of_mem
    {x :
        AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 (padOpens σ G))
            (padExt σ G w)}
    (hx : x ∈ (isClosedSubmanifold_padSlice σ G).idealSheaf.stalkIdeal (padExt σ G w)) :
    germMap (padExt σ G) (contMDiff_padExt σ G) w x = 0 := by
  obtain ⟨f₀, hf₀⟩ := Quotient.exists_rep (stalkToGerm 𝓘(𝕜, Fin n' → 𝕜) ω _ (padExt σ G w) x)
  have hev := ((isClosedSubmanifold_padSlice σ G).mem_stalkIdeal_idealSheaf_iff_eventually
    (padExt_mem_padSlice σ G w) x hf₀.symm).mp hx
  apply stalkToGerm_injective 𝓘(𝕜, Fin n → 𝕜) ω _ w
  rw [stalkToGerm_germMap, ← hf₀, map_zero]
  change (↑(f₀ ∘ padExt σ G) : Germ (𝓝 w) 𝕜) = ↑(0 : pieceAmbient.{u} 𝕜 G → 𝕜)
  rw [Germ.coe_eq]
  have hcont : Continuous fun y : pieceAmbient.{u} 𝕜 G =>
      (⟨padExt σ G y, padExt_mem_padSlice σ G y⟩ : padSlice σ G) :=
    (contMDiff_padExt σ G).continuous.subtype_mk _
  exact (hcont.tendsto w).eventually hev

/-- Every germ at `s w` is congruent to `p^*(s^* g)` modulo the ideal of the slice: the difference
vanishes on `S`, where `s ∘ p = id`. -/
theorem sub_padCoordProjStalk_mem
    (x :
        AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 (padOpens σ G))
            (padExt σ G w)) :
    x - padCoordProjStalk σ w (germMap (padExt σ G) (contMDiff_padExt σ G) w x) ∈
      (isClosedSubmanifold_padSlice σ G).idealSheaf.stalkIdeal (padExt σ G w) := by
  obtain ⟨f₀, hf₀⟩ := Quotient.exists_rep (stalkToGerm 𝓘(𝕜, Fin n' → 𝕜) ω _ (padExt σ G w) x)
  refine ((isClosedSubmanifold_padSlice σ G).mem_stalkIdeal_idealSheaf_iff_eventually
    (padExt_mem_padSlice σ G w) _ (f := f₀ - f₀ ∘ padExt σ G ∘ padCoordProj σ G) ?_).mpr ?_
  · rw [map_sub, padCoordProjStalk, stalkToGerm_germMapOn, stalkToGerm_germMap, ← hf₀]
    rfl
  · refine Eventually.of_forall fun y => ?_
    simp only [Pi.sub_apply, Function.comp_apply, padExt_padCoordProj_of_mem σ G y.2, sub_self]

/-- **The stalk of the padded ideal on the slice**: `(p^*J + 𝓘_S)_{s w} = (s^*)⁻¹ J_w`, the one
piece of algebra of the padding (`Y` is also a closed analytic subset of `U × 𝕜ᵐ`,
[Wlo09, §7.1]). -/
theorem stalkIdeal_padIdeal_padExt :
    (padIdeal σ J).stalkIdeal (padExt σ G w) =
      Ideal.comap (germMap (padExt σ G) (contMDiff_padExt σ G) w) (J.stalkIdeal w) := by
  apply le_antisymm
  · rw [stalkIdeal_padIdeal]
    refine sup_le ?_ ?_
    · rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
      have e : (germMap (padExt σ G) (contMDiff_padExt σ G) w).comp
          (germMap (padCoordProj σ G) (contMDiff_padCoordProj σ G) (padExt σ G w)) =
            germMap (padCoordProj σ G ∘ padExt σ G)
              ((contMDiff_padCoordProj σ G).comp (contMDiff_padExt σ G)) w :=
        RingHom.ext fun x => germMapOn_germMapOn (contMDiff_padCoordProj σ G).contMDiffOn
          (contMDiff_padExt σ G).contMDiffOn (Opens.mem_top w) rfl (Opens.mem_top _) rfl
          ((contMDiff_padCoordProj σ G).comp (contMDiff_padExt σ G)).contMDiffOn
          (Opens.mem_top w) rfl x
      rw [e]
      have h1 := IdealSheaf.stalkIdeal_pullback (padCoordProj σ G ∘ padExt σ G)
        ((contMDiff_padCoordProj σ G).comp (contMDiff_padExt σ G)) J w
      rw [IdealSheaf.pullback_congr J _ contMDiff_id (padCoordProj_comp_padExt σ G),
        IdealSheaf.pullback_id_eq_self] at h1
      exact h1.symm.le
    · intro x hx
      rw [Ideal.mem_comap, germMap_padExt_eq_zero_of_mem σ w hx]
      exact zero_mem _
  · intro x hx
    rw [Ideal.mem_comap] at hx
    have h1 : x - padCoordProjStalk σ w (germMap (padExt σ G) (contMDiff_padExt σ G) w x) ∈
        (padIdeal σ J).stalkIdeal (padExt σ G w) := by
      rw [stalkIdeal_padIdeal]
      exact Ideal.mem_sup_right (sub_padCoordProjStalk_mem σ w x)
    have h2 : padCoordProjStalk σ w (germMap (padExt σ G) (contMDiff_padExt σ G) w x) ∈
        (padIdeal σ J).stalkIdeal (padExt σ G w) := by
      rw [stalkIdeal_padIdeal]
      refine Ideal.mem_sup_left ?_
      rw [← germMap_padCoordProj_padTransport, ← map_padTransport_stalkIdeal σ J w]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)
    have := add_mem h1 h2
    rwa [sub_add_cancel] at this

theorem padExt_mem_cosupport {w : pieceAmbient.{u} 𝕜 G} (hw : w ∈ J.support) :
    padExt σ G w ∈ (padIdeal σ J).support := by
  rw [IdealSheaf.mem_support, stalkIdeal_padIdeal_padExt]
  exact Ideal.comap_ne_top _ hw

end Stalks

/-! ### Reducedness and nonvanishing -/

/-- The padded ideal is reduced when `J` is: on the slice its stalks are `(s^*)⁻¹` of the
radical ideals `J_w`, off the slice the unit ideal. -/
theorem isReduced_padIdeal (hJ : J.IsReduced) : (padIdeal σ J).IsReduced := by
  intro z
  by_cases hz : z ∈ padSlice σ G
  · obtain ⟨w, rfl⟩ : ∃ w, padExt σ G w = z := ⟨_, padExt_padCoordProj_of_mem σ G hz⟩
    rw [stalkIdeal_padIdeal_padExt]
    exact (hJ w).comap _
  · rw [stalkIdeal_padIdeal, (isClosedSubmanifold_padSlice σ G).stalkIdeal_idealSheaf_of_notMem hz,
      sup_top_eq]
    exact le_top

theorem exists_notMem_range_of_not_surjective (hσ : ¬ Function.Surjective σ) :
    ∃ j, j ∉ Set.range σ := by
  by_contra h
  exact hσ fun j => Classical.byContradiction fun hj => h ⟨j, hj⟩

/-- For `σ` not surjective the padded ideal is **nonzero at every stalk**: off the slice it is
the unit ideal, on the slice it contains a complementary coordinate germ, which is nonzero
(`coord_ne_zero`). The added coordinate of [Wlo09, §7.1] thus makes the ideal of a smooth piece
without equations nonzero. -/
theorem isNonzeroEverywhere_padIdeal (hσ : ¬ Function.Surjective σ) :
    (padIdeal σ J).IsNonzeroEverywhere := by
  intro z
  obtain ⟨j, hj⟩ := exists_notMem_range_of_not_surjective σ hσ
  rw [stalkIdeal_padIdeal]
  by_cases hz : z ∈ padSlice σ G
  · intro h
    have hbot : (isClosedSubmanifold_padSlice σ G).idealSheaf.stalkIdeal z = ⊥ :=
      le_bot_iff.mp (h ▸ le_sup_right)
    have hmem : coord (Fin n' → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜))
        (chartAt (Fin n' → 𝕜) z) (IsManifold.chart_mem_maximalAtlas z) (mem_chart_source _ z)
        (padCompl σ (complEquiv σ ⟨j, hj⟩)) ∈
          (isClosedSubmanifold_padSlice σ G).idealSheaf.stalkIdeal z := by
      rw [(isClosedSubmanifold_padSlice σ G).isIdealSheafOf_idealSheaf.2 (chartAt _ z)
        (padCompl σ) (isAdaptedChart_chartAt σ G z) z (mem_chart_source _ z) hz]
      exact Ideal.subset_span ⟨_, rfl⟩
    rw [hbot, Ideal.mem_bot] at hmem
    exact coord_ne_zero (ψ := ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜)) _ _ _ hmem
  · rw [(isClosedSubmanifold_padSlice σ G).stalkIdeal_idealSheaf_of_notMem hz, sup_top_eq]
    have :
        Nontrivial
            (AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 (padOpens σ G)) z) :=
      (Manifold.eval 𝕜 (Fin n' → 𝕜) _ z).domain_nontrivial
    exact top_ne_bot

/-- The nonvanishing for the padding `σ := Fin.castLEEmb h` with `n < n'` (the case of
`PieceEmbedding.padLeft`, and of the common dimension `n' := max nᵢ + 1` in the existence proof of
local embedding data). -/
theorem isNonzeroEverywhere_padIdeal_castLE {h : n ≤ n'} (hlt : n < n') :
    (padIdeal (Fin.castLEEmb h) J).IsNonzeroEverywhere :=
  isNonzeroEverywhere_padIdeal (Fin.castLEEmb h) J fun hs => by
    obtain ⟨i, hi⟩ := hs ⟨n, hlt⟩
    have := congrArg Fin.val hi
    change (i : ℕ) = n at this
    omega

/-! ### The slice isomorphism `Sp(padOpens σ G)/padIdeal σ J ≅ Sp(G)/J` -/

open AnalyticSpace KLocallyRingedSpace in
/-- Compatibility of the ideals with `Sp(p)`: `p^*J ≤ padIdeal σ J` (`QuotientSpace.Compat`). -/
theorem compat_padCoordProj :
    QuotientSpace.Compat (ofManifoldHom (padCoordProj σ G) (contMDiff_padCoordProj σ G)).1
      (padIdeal σ J) J := by
  intro z
  have hz : ((ofManifoldHom (padCoordProj σ G) (contMDiff_padCoordProj σ G)).1.stalkMap z).hom =
      germMap (padCoordProj σ G) (contMDiff_padCoordProj σ G)
        (z : pieceAmbient.{u} 𝕜 (padOpens σ G)) :=
    RingHom.ext (stalkMap_ofManifoldHom_eq_germMap (padCoordProj σ G) (contMDiff_padCoordProj σ G)
      (z : pieceAmbient.{u} 𝕜 (padOpens σ G)))
  change Ideal.map
    ((ofManifoldHom (padCoordProj σ G) (contMDiff_padCoordProj σ G)).1.stalkMap z).hom
    (J.stalkIdeal (padCoordProj σ G z)) ≤ (padIdeal σ J).stalkIdeal z
  rw [hz, stalkIdeal_padIdeal]
  exact le_sup_left

open AnalyticSpace KLocallyRingedSpace in
/-- **The slice morphism** `Sp(padOpens σ G)/padIdeal σ J ⟶ Sp(G)/J` over the coordinate
projection `z ↦ z ∘ σ`: the functoriality of the closed subspace along `Sp(p)`. It is an
isomorphism (`isIso_padSliceHom`); `padSliceIso` is the isomorphism. This is the identification of
`Y` with its copy in `U × 𝕜ᵐ` [Wlo09, §7.1]. -/
def padSliceHom :
    (padIdeal σ J).toAnalyticSpace ⟶ J.toAnalyticSpace :=
  quotientMap (ofManifoldHom (padCoordProj σ G) (contMDiff_padCoordProj σ G)) (padIdeal σ J) J
    (compat_padCoordProj σ J)

/-- The slice morphism on points is the coordinate projection. -/
theorem padSliceHom_apply_val (y : (padIdeal σ J).toAnalyticSpace) :
    (padSliceHom σ J y).1 = padCoordProj σ G y.1 :=
        rfl

/-- The projection and the zero extension are inverse homeomorphisms between the supports of the
padded ideal and of `J`. -/
def padSliceHomeo : (padIdeal σ J).support ≃ₜ J.support where
  toFun z := ⟨padCoordProj σ G z.1, padCoordProj_mem_cosupport σ J z.2⟩
  invFun w := ⟨padExt σ G w.1, padExt_mem_cosupport σ J w.2⟩
  left_inv z := Subtype.ext (padExt_padCoordProj_of_mem σ G (mem_padSlice_of_mem_cosupport σ J z.2))
  right_inv w := Subtype.ext (padCoordProj_padExt σ G w.1)
  continuous_toFun :=
    ((contMDiff_padCoordProj σ G).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((contMDiff_padExt σ G).continuous.comp continuous_subtype_val).subtype_mk _

open AnalyticSpace KLocallyRingedSpace in
/-- The fibre maps of the slice morphism are bijective: at a point `s w` of the slice,
`𝒪_{n,p (s w)}/J → 𝒪_{n',s w}/(p^*J + 𝓘_S)` — injective since `(p^*J + 𝓘_S)_{s w} = (s^*)⁻¹ J_w`
and `s^* ∘ p^* = id`, surjective since every germ is `p^*(s^* g)` modulo `𝓘_S`. -/
theorem bijective_fiberMap_padSliceHom (z : QuotientSpace.support
      (ofManifold 𝕜 (Fin n' → 𝕜) (pieceAmbient.{u} 𝕜 (padOpens σ G))).toLocallyRingedSpace
      (padIdeal σ J)) :
    Function.Bijective (QuotientSpace.fiberMap
      (ofManifoldHom (padCoordProj σ G) (contMDiff_padCoordProj σ G)).1 (padIdeal σ J) J
      (compat_padCoordProj σ J) z) := by
  obtain ⟨z, hz⟩ := z
  obtain ⟨w, rfl⟩ : ∃ w, padExt σ G w = z :=
    ⟨_, padExt_padCoordProj_of_mem σ G (mem_padSlice_of_mem_cosupport σ J hz)⟩
  have hstalk : ((ofManifoldHom (padCoordProj σ G) (contMDiff_padCoordProj σ G)).1.stalkMap
      (padExt σ G w)).hom =
        germMap (padCoordProj σ G) (contMDiff_padCoordProj σ G) (padExt σ G w) :=
    RingHom.ext (stalkMap_ofManifoldHom_eq_germMap _ _ _)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Ideal.Quotient.mk _ (((ofManifoldHom (padCoordProj σ G)
      (contMDiff_padCoordProj σ G)).1.stalkMap (padExt σ G w)).hom g) = 0 at ha
    rw [Ideal.Quotient.eq_zero_iff_mem, hstalk] at ha
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change germMap (padCoordProj σ G) (contMDiff_padCoordProj σ G) (padExt σ G w) g ∈
      (padIdeal σ J).stalkIdeal (padExt σ G w) at ha
    change g ∈ J.stalkIdeal (padCoordProj σ G (padExt σ G w))
    have h1 : padTransport' σ w g ∈ J.stalkIdeal w := by
      rw [← padTransport_padTransport' σ w g, germMap_padCoordProj_padTransport,
        stalkIdeal_padIdeal_padExt, Ideal.mem_comap, padExtStalk_padCoordProjStalk] at ha
      exact ha
    rw [← padTransport_padTransport' σ w g, ← map_padTransport_stalkIdeal σ J w]
    exact Ideal.mem_map_of_mem _ h1
  · intro b
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨x', rfl⟩ : ∃ x' :
        AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 (padOpens σ G))
        (padExt σ G w), x' = x := ⟨x, rfl⟩
    refine ⟨Ideal.Quotient.mk _ (padTransport σ w
      (germMap (padExt σ G) (contMDiff_padExt σ G) w x')), ?_⟩
    have key : germMap (padCoordProj σ G) (contMDiff_padCoordProj σ G) (padExt σ G w)
        (padTransport σ w (germMap (padExt σ G) (contMDiff_padExt σ G) w x')) - x' ∈
        (padIdeal σ J).stalkIdeal (padExt σ G w) := by
      rw [germMap_padCoordProj_padTransport, ← Ideal.neg_mem_iff, neg_sub, stalkIdeal_padIdeal]
      exact Ideal.mem_sup_right (sub_padCoordProjStalk_mem σ w x')
    change Ideal.Quotient.mk _ (((ofManifoldHom (padCoordProj σ G)
      (contMDiff_padCoordProj σ G)).1.stalkMap (padExt σ G w)).hom
        (padTransport σ w (germMap (padExt σ G) (contMDiff_padExt σ G) w x'))) =
      Ideal.Quotient.mk _ x'
    rw [Ideal.Quotient.eq, hstalk]
    exact key

open AnalyticSpace KLocallyRingedSpace in
/-- **The slice morphism is an isomorphism** of analytic `𝕜`-spaces: a homeomorphism on points
(`padSliceHomeo`) with bijective fibre maps (`bijective_fiberMap_padSliceHom`), hence an open
immersion onto the whole target (Mathlib's `LocallyRingedSpace.IsOpenImmersion.of_stalk_iso`,
`to_iso`). -/
theorem isIso_padSliceHom : IsIso (padSliceHom σ J) := by
  have hval : IsIso (padSliceHom σ J).1 := by
    change IsIso (QuotientSpace.map
      (ofManifoldHom (padCoordProj σ G) (contMDiff_padCoordProj σ G)).1
      (padIdeal σ J) J (compat_padCoordProj σ J))
    set f := QuotientSpace.map (ofManifoldHom (padCoordProj σ G) (contMDiff_padCoordProj σ G)).1
      (padIdeal σ J) J (compat_padCoordProj σ J) with hf
    have hbase : (f.base : (padIdeal σ J).support → J.support) = padSliceHomeo σ J :=
      funext fun _ => Subtype.ext rfl
    have hemb : Topology.IsOpenEmbedding (f.base : (padIdeal σ J).support → J.support) :=
      hbase ▸ (padSliceHomeo σ J).isOpenEmbedding
    have : ∀ z, IsIso (f.stalkMap z) := fun z =>
      QuotientSpace.isIso_map_stalkMap_of_bijective _ _ _ _ z
        (bijective_fiberMap_padSliceHom σ J z)
    have : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion f :=
      AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso f hemb
    have : Epi f.base := (TopCat.epi_iff_surjective f.base).mpr
      (hbase ▸ (padSliceHomeo σ J).surjective)
    exact AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.to_iso f
  change @IsIso (AnalyticSpace.{u} 𝕜) _ _ _ (padSliceHom σ J)
  exact AnalyticSpace.isIso_of_isIso_toKLocallyRingedSpace _ (isIso_of_isIso_val _)

/-- **The slice isomorphism** `Sp(padOpens σ G)/padIdeal σ J ≅ Sp(G)/J` of analytic `𝕜`-spaces,
over the coordinate projection (`hom := padSliceHom`). -/
def padSliceIso :
    @Iso (AnalyticSpace.{u} 𝕜) _ (padIdeal σ J).toAnalyticSpace
      J.toAnalyticSpace :=
  @asIso (AnalyticSpace.{u} 𝕜) _ _ _ (padSliceHom σ J) (isIso_padSliceHom σ J)

theorem padSliceIso_hom : (padSliceIso σ J).hom = padSliceHom σ J := rfl

end Hironaka.Manifold
