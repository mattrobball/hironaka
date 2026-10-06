/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PadIdeal
public import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrict
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-!
# The padded reading opens

Kollár's proof of Theorem 36 embeds `X ⊂ ℂⁿ ⊂ ℂᴺ` and passes to the ideal `(𝓘, z_{n+1}, …, z_N)`
[Kol07, Theorem 36, proof]; Włodarczyk's resolution of a marked ideal commutes with closed
embeddings of the ambient manifold [Wlo09, §7.1]. The padding identity of the local resolutions
(the value of the functor on the padded triple against its value on the original one) is read on
relatively compact opens, and the padded model must be read on an open `W⁺` of the padded ambient
`padOpens σ G` whose trace on the coordinate slice — the image of the zero extension
`padExt σ G : Sp(G) → Sp(padOpens σ G)` — is the given reading open `W` of `Sp(G)`. The choice made
here is the product of `W` with the open unit ball in the padding coordinates:

* `padReadingOpens σ G W := padCoordProj σ G ⁻¹' W ∩ {z_k ∈ 𝔻 for k ∉ range σ}`, with
  `mem_padReadingOpens`;
* `preimageOpens_padExt_padReadingOpens`: the zero extension reads it back as `W`
  (`padCoordProj ∘ padExt = id`, the padding coordinates of `padExt w` are `0`);
* `isCompact_closure_padReadingOpens`: relatively compact when `W` is — its closure lies in the
  preimage under the coordinate chart `pieceCoord` of the closed bounded box
  `{z | z ∘ σ ∈ pieceCoord '' closure W, ‖z_k‖ ≤ 1 off range σ}` of `𝕜ⁿ'`, compact by
  Heine–Borel and inside `padOpens σ G`, and `pieceCoord` is an open embedding;
* `exists_padOpens_preimage_eq`: the existence statement — a relatively compact open of the
  padded ambient reading back as `W`.

Not in the sources; bookkeeping.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Topology
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n n' : ℕ} (σ : Fin n ↪ Fin n') (G : Opens (Fin n → 𝕜))

/-! ### The open unit ball in the padding coordinates -/

/-- **The open unit ball in the padding coordinates** — the points of the padded ambient whose
coordinates off `range σ` have norm below `1`. -/
def padBall : Set (pieceAmbient.{u} 𝕜 (padOpens σ G)) :=
  {p | ∀ k, k ∉ range σ → ‖(p.2 : Fin n' → 𝕜) k‖ < 1}

/-- Membership in the padding ball, unfolded. -/
theorem mem_padBall {p : pieceAmbient.{u} 𝕜 (padOpens σ G)} :
    p ∈ padBall σ G ↔ ∀ k, k ∉ range σ → ‖(p.2 : Fin n' → 𝕜) k‖ < 1 :=
  Iff.rfl

/-- The ball in the padding coordinates is open — a finite intersection of the open conditions
`‖z_k‖ < 1`. -/
theorem isOpen_padBall : IsOpen (padBall.{u} σ G) := by
  have h : padBall.{u} σ G =
      ⋂ k ∈ {k : Fin n' | k ∉ range σ},
        {p : pieceAmbient.{u} 𝕜 (padOpens σ G) | ‖(p.2 : Fin n' → 𝕜) k‖ < 1} := by
    ext p
    simp only [padBall, Set.mem_ofPred_eq, Set.mem_iInter₂]
  rw [h]
  exact (Set.toFinite _).isOpen_biInter fun k _ =>
    isOpen_lt ((continuous_apply k).comp (contMDiff_pieceCoord (padOpens σ G)).continuous).norm
      continuous_const

/-- The zero extension lands in the ball — its padding coordinates are `0`. -/
theorem padExt_mem_padBall (w : pieceAmbient.{u} 𝕜 G) : padExt σ G w ∈ padBall σ G := fun _ hk => by
  rw [padExt_apply_of_notMem_range σ G w hk, norm_zero]
  exact zero_lt_one

/-! ### The padded reading open -/

/-- **The padded reading open** of a reading open `W ⊆ Sp(G)` — the product of `W` with the open
unit ball in the padding coordinates, `p⁻¹(W) ∩ {‖z_k‖ < 1, k ∉ range σ}`, an open of the padded
ambient of [Kol07, Theorem 36, proof]. -/
def padReadingOpens (W : Opens (pieceAmbient.{u} 𝕜 G)) :
    Opens (pieceAmbient.{u} 𝕜 (padOpens σ G)) :=
  ⟨padCoordProj σ G ⁻¹' (W : Set (pieceAmbient 𝕜 G)) ∩ padBall σ G,
    (W.isOpen.preimage (contMDiff_padCoordProj σ G).continuous).inter (isOpen_padBall σ G)⟩

/-- Membership in the padded reading open — the coordinate projection lies in `W` and the padding
coordinates have norm below `1`. -/
theorem mem_padReadingOpens {W : Opens (pieceAmbient.{u} 𝕜 G)}
    {p : pieceAmbient.{u} 𝕜 (padOpens σ G)} :
    p ∈ padReadingOpens σ G W ↔
      padCoordProj σ G p ∈ W ∧ ∀ k, k ∉ Set.range σ → ‖(p.2 : Fin n' → 𝕜) k‖ < 1 :=
  Iff.rfl

/-- **The zero extension reads the padded reading open back as `W`** — `p ∘ s = id`
(`padCoordProj_padExt`) and the padding coordinates of `s w` vanish
(`padExt_apply_of_notMem_range`). -/
theorem preimageOpens_padExt_padReadingOpens (W : Opens (pieceAmbient.{u} 𝕜 G)) :
    preimageOpens (padExt σ G) (contMDiff_padExt σ G) (padReadingOpens σ G W) = W := by
  ext x
  simp only [SetLike.mem_coe, mem_preimageOpens, mem_padReadingOpens, padCoordProj_padExt]
  exact ⟨fun h => h.1, fun h => ⟨h, padExt_mem_padBall σ G x⟩⟩

/-- **The padded reading open of a relatively compact open is relatively compact** — its closure
lies in the preimage under the coordinate chart `pieceCoord` of the closed bounded box
`{z | z ∘ σ ∈ K, ‖z_k‖ ≤ 1 off range σ}` (`K := pieceCoord '' closure W`, compact and inside `G`),
a compact set of `𝕜ⁿ'` inside `padOpens σ G` (Heine–Borel), and `pieceCoord` is an open
embedding. -/
theorem isCompact_closure_padReadingOpens (W : Opens (pieceAmbient.{u} 𝕜 G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 G)))) :
    IsCompact (closure (padReadingOpens σ G W : Set (pieceAmbient 𝕜 (padOpens σ G)))) := by
  -- the compact coordinate image of the closure of `W`, inside `G`
  set K : Set (Fin n → 𝕜) := pieceCoord G '' closure (W : Set (pieceAmbient 𝕜 G)) with hK
  have hKc : IsCompact K := hW.image (contMDiff_pieceCoord G).continuous
  have hKG : K ⊆ G := by
    rintro _ ⟨w, -, rfl⟩
    exact pieceCoord_mem G w
  -- the closed bounded box in the padded coordinates
  set B : Set (Fin n' → 𝕜) :=
    (fun z : Fin n' → 𝕜 => z ∘ σ) ⁻¹' K ∩ ⋂ k ∈ {k : Fin n' | k ∉ range σ}, {z | ‖z k‖ ≤ 1} with hB
  have hBcl : IsClosed B :=
    (hKc.isClosed.preimage (continuous_pi fun i => continuous_apply (σ i))).inter
      (isClosed_biInter fun k _ => isClosed_le (continuous_apply k).norm continuous_const)
  obtain ⟨C, hC⟩ := hKc.isBounded.exists_norm_le
  have hBbd : Bornology.IsBounded B := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin n' → 𝕜)) (r := max C 1)).subset ?_
    intro z hz
    rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter₂] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (le_max_of_le_right zero_le_one)).mpr fun k => ?_
    by_cases hk : k ∈ range σ
    · obtain ⟨i, rfl⟩ := hk
      exact ((norm_le_pi_norm (z ∘ σ) i).trans (hC _ hz.1)).trans (le_max_left _ _)
    · exact (show ‖z k‖ ≤ 1 from hz.2 k hk).trans (le_max_right _ _)
  have : ProperSpace (Fin n' → 𝕜) := FiniteDimensional.proper_rclike 𝕜 _
  have hBc : IsCompact B := Metric.isCompact_of_isClosed_isBounded hBcl hBbd
  have hBsub : B ⊆ (padOpens σ G : Set (Fin n' → 𝕜)) := fun z hz => hKG hz.1
  -- the coordinate chart of the padded ambient is an open embedding
  have hemb : IsOpenEmbedding (pieceCoord.{u} (padOpens σ G)) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap
      (contMDiff_pieceCoord (padOpens σ G)).continuous (pieceCoord_injective (padOpens σ G))
      (isOpenMap_pieceCoord (padOpens σ G))
  have hpre : IsCompact (pieceCoord.{u} (padOpens σ G) ⁻¹' B) := by
    rw [hemb.toIsEmbedding.toIsInducing.isCompact_iff, Set.image_preimage_eq_inter_range,
      range_pieceCoord, Set.inter_eq_left.mpr hBsub]
    exact hBc
  -- the reading open lies in this closed compact set, hence so does its closure
  refine hpre.of_isClosed_subset isClosed_closure
    (closure_minimal ?_ (hBcl.preimage (contMDiff_pieceCoord (padOpens σ G)).continuous))
  intro p hp
  rw [SetLike.mem_coe, mem_padReadingOpens] at hp
  refine ⟨⟨padCoordProj σ G p, subset_closure hp.1, rfl⟩, ?_⟩
  exact Set.mem_iInter₂.mpr fun k hk => (hp.2 k hk).le

/-- **The padded reading open exists** — for a relatively compact reading open `W` of `Sp(G)`
there is a relatively compact open `W⁺` of the padded ambient `Sp(padOpens σ G)` whose preimage
under the zero extension is `W` (the witness is `padReadingOpens σ G W`). -/
theorem exists_padOpens_preimage_eq (W : Opens (pieceAmbient.{u} 𝕜 G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 G)))) :
    ∃ Wp : Opens (pieceAmbient.{u} 𝕜 (padOpens σ G)),
      IsCompact (closure (Wp : Set (pieceAmbient 𝕜 (padOpens σ G)))) ∧
        preimageOpens (padExt σ G) (contMDiff_padExt σ G) Wp = W :=
  ⟨padReadingOpens σ G W, isCompact_closure_padReadingOpens σ G W hW,
    preimageOpens_padExt_padReadingOpens σ G W⟩

end Hironaka.Manifold

end
