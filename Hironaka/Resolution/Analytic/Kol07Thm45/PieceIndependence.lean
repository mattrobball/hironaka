/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PadIdeal
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceResolution
import Hironaka.AnalyticSpace.Manifold.Comap
import Hironaka.Manifold.BlowUp.Transform.Object
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Padded embeddings, shears, the transport of an embedding along an isomorphism, and the local
resolution map over the piece

Two closed embeddings `i₁ : X ↪ 𝕜ⁿ`, `i₂ : X ↪ 𝕜ᵐ` become equivalent under an analytic
automorphism of `𝕜ⁿ⁺ᵐ` after the coordinate inclusions: extend `i₁`, `i₂` (locally) to `j₁`, `j₂`,
shear by `(x, y) ↦ (x, y + j₂(x))`, shear by `(x, y) ↦ (x + j₁(y), y)`, compose
[Kol07, Lemma 39]; Włodarczyk's Lemma 4.8.1 is the same statement, with two explicit automorphisms
of the doubled affine space [Wlo05, Lemma 4.8.1]. The ambient dimension may be increased at any
time by `𝕜ⁿ ↪ 𝕜ⁿ⁺ᵐ` [Kol07, Theorem 36, proof], as in Włodarczyk's passage to a common ambient
dimension [Wlo09, §7.1]. The algebraic counterparts are `shearX`, `shearY`, `prodEmb` and
`coordInclFst` of `Hironaka/Resolution/Algebraic/Kol07/Thm36/AffineSpace.lean`. This module
constructs the analytic terms:

* **The paddings.** `PieceEmbedding.padAlong E σ` pads a piece embedding along an embedding of
  coordinates `σ : Fin n ↪ Fin n'` with the tools of `PadIdeal.lean`: the ambient `padOpens σ E.G`,
  the ideal `padIdeal σ E.ideal`, the embedding `X|V ≅ Sp(G)/𝓘 ≅ Sp(padOpens σ G)/padIdeal σ 𝓘` (the
  slice isomorphism inverted). `padLeft E m` (`σ := Fin.castAddEmb m`, the coordinate inclusion
  `x ↦ (x, 0)`) and `padRight E m` (`σ := Fin.natAddEmb m`, `y ↦ (0, y)`) are the two paddings of
  Lemma 39. `isNonzeroEverywhere_padIdeal_of_isNonzeroEverywhere` is the nonvanishing of the
  padded ideal for an ARBITRARY `σ` (the padding of a nonzero ideal is nonzero, no padding
  coordinate needed), so that the paddings are total in `m`.
* **The shears.** `shearSnd O j hj`, `shearFst O j hj`: the analytic automorphisms
  `(x, y) ↦ (x, y + j(x))` of `O × 𝕜ᵐ` and `(x, y) ↦ (x + j(y), y)` of `𝕜ⁿ × O`, for `j` analytic on
  the open `O` — Mathlib's `PartialDiffeomorph` of the model space `𝕜ⁿ⁺ᵐ` with source and target
  the cylinder over `O` (the two automorphisms of [Kol07, Lemma 39, proof]; the local extensions
  `j₁, j₂` are supplied where the two embeddings are compared, from the sheaf of germ families).
* **The transport.** `PieceEmbedding.transportAlongIso E h hh`: a piece embedding of `Y|U`
  composed with an isomorphism `X|V ≅ Y|U` is a piece embedding of `X|V` with the SAME ambient
  and ideal — the analytic form, for an isomorphism of open subspaces, of the compatible
  embeddings of [Kol07, Lemma 41] (the projection argument of that lemma is not needed).
* **The composite.** `PieceEmbedding.localResolutionToPiece E bed W hW`: the local resolution map
  `Π : Ỹ → Sp(W)/𝓘|W` (`PieceResolution.lean`) followed by the restriction-of-a-quotient map
  `Sp(W)/𝓘|W → Sp(G)/𝓘` (the functoriality of the closed subspace along `Sp(W ↪ G)`) and the
  inverse of the embedding `X|V ≅ Sp(G)/𝓘` — the map `Ỹ_Z → Y_Z` of Włodarczyk's canonical
  desingularization [Wlo09, §4, (3)⇒(4)], landing in the piece `X|V`, with image the open
  `embPreimage E W` of the points of `X|V` whose ambient point lies over `W` (`ambientPoint`).

Conventions: the one-piece ambient `pieceAmbient 𝕜 G`; the linear chart of `𝕜ⁿ` is the identity
(`ContinuousLinearEquiv.refl`). The map `localResolutionToPiece` lands in the piece itself rather
than in the open subspace `X | embPreimage E W`, so that its compositions with the transitions
between pieces take place in one space; the open subspace is reached by restricting along the
open set `embPreimage E W` (`Hom.restrictSet`). Not in the sources beyond the items cited;
bookkeeping.
-/

@[expose] public section

open TopologicalSpace CategoryTheory
open scoped Manifold ContDiff

universe u

noncomputable section

namespace Hironaka.Manifold

open _root_.Manifold

/-! ### The padding of a nonzero ideal is nonzero, for every `σ` -/

section PadNonzero

variable {𝕜 : Type} [RCLike 𝕜] {n n' : ℕ} (σ : Fin n ↪ Fin n') {G : Opens (Fin n → 𝕜)}
  (J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 G))

/-- **The padding of an ideal nonzero at every stalk is nonzero at every stalk**, for every
embedding of coordinates `σ` — off the slice the padded ideal is the unit ideal, on the slice
`(p^*J + 𝓘_S)_{s w} = (s^*)⁻¹ J_w` contains `p^* J_w`, and `s^* ∘ p^* = id`. -/
theorem isNonzeroEverywhere_padIdeal_of_isNonzeroEverywhere (hJ : J.IsNonzeroEverywhere) :
    (padIdeal σ J).IsNonzeroEverywhere := by
  intro z
  by_cases hz : z ∈ padSlice σ G
  · obtain ⟨w, rfl⟩ : ∃ w, padExt σ G w = z := ⟨_, padExt_padCoordProj_of_mem σ G hz⟩
    rw [stalkIdeal_padIdeal_padExt]
    intro h
    refine hJ w ((Submodule.eq_bot_iff _).mpr fun y hy => ?_)
    have h1 : padCoordProjStalk σ w y ∈
        Ideal.comap (germMap (padExt σ G) (contMDiff_padExt σ G) w) (J.stalkIdeal w) := by
      rw [Ideal.mem_comap, padExtStalk_padCoordProjStalk]
      exact hy
    rw [h, Ideal.mem_bot] at h1
    have h2 := padExtStalk_padCoordProjStalk σ w y
    rw [h1, map_zero] at h2
    exact h2.symm
  · rw [stalkIdeal_padIdeal, (isClosedSubmanifold_padSlice σ G).stalkIdeal_idealSheaf_of_notMem hz,
      sup_top_eq]
    have :
        Nontrivial
            (AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 (padOpens σ G)) z) :=
      (Manifold.eval 𝕜 (Fin n' → 𝕜) _ z).domain_nontrivial
    exact top_ne_bot

end PadNonzero

/-! ### The shears `(x, y) ↦ (x, y + j x)` and `(x, y) ↦ (x + j y, y)` -/

section Shear

variable {𝕜 : Type} [RCLike 𝕜] {n m : ℕ}

/-- The block inclusion `b ↦ (0, b)` of `𝕜ᵐ` into `𝕜ⁿ⁺ᵐ` is analytic. -/
theorem contDiff_append_zero_left :
    ContDiff 𝕜 ω fun b : Fin m → 𝕜 => Fin.append (0 : Fin n → 𝕜) b := by
  refine contDiff_pi.mpr fun i => ?_
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.append_left, Pi.zero_apply]
    exact contDiff_const
  | right i =>
    simp only [Fin.append_right]
    exact contDiff_apply 𝕜 _ i

/-- The block inclusion `a ↦ (a, 0)` of `𝕜ⁿ` into `𝕜ⁿ⁺ᵐ` is analytic. -/
theorem contDiff_append_zero_right :
    ContDiff 𝕜 ω fun a : Fin n → 𝕜 => Fin.append a (0 : Fin m → 𝕜) := by
  refine contDiff_pi.mpr fun i => ?_
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact contDiff_apply 𝕜 _ i
  | right i =>
    simp only [Fin.append_right, Pi.zero_apply]
    exact contDiff_const

/-- The projection `z ↦ z ∘ castAdd m` onto the first block is analytic. -/
theorem contDiff_comp_castAdd :
    ContDiff 𝕜 ω fun z : Fin (n + m) → 𝕜 => z ∘ Fin.castAdd m :=
  contDiff_pi.mpr fun i => contDiff_apply 𝕜 _ (Fin.castAdd m i)

/-- The projection `z ↦ z ∘ natAdd n` onto the second block is analytic. -/
theorem contDiff_comp_natAdd :
    ContDiff 𝕜 ω fun z : Fin (n + m) → 𝕜 => z ∘ Fin.natAdd n :=
  contDiff_pi.mpr fun i => contDiff_apply 𝕜 _ (Fin.natAdd n i)

/-- The first block of `(0, b)` is `0`. -/
theorem append_zero_left_comp_castAdd (b : Fin m → 𝕜) :
    Fin.append (0 : Fin n → 𝕜) b ∘ Fin.castAdd m = 0 :=
  funext fun i => Fin.append_left _ _ i

/-- The second block of `(a, 0)` is `0`. -/
theorem append_zero_right_comp_natAdd (a : Fin n → 𝕜) :
    Fin.append a (0 : Fin m → 𝕜) ∘ Fin.natAdd n = 0 :=
  funext fun i => Fin.append_right _ _ i

/-- **The shear** `(x, y) ↦ (x, y + j(x))`, an analytic automorphism of the cylinder
`O × 𝕜ᵐ ⊆ 𝕜ⁿ⁺ᵐ` over an open `O ⊆ 𝕜ⁿ` on which `j` is analytic; its inverse is the shear by `−j`.
It carries the coordinate inclusion `x ↦ (x, 0)` to the graph `x ↦ (x, j(x))`: the first
automorphism of [Kol07, Lemma 39, proof] (compare the automorphisms of
[Wlo05, Lemma 4.8.1]). -/
def shearSnd (O : Opens (Fin n → 𝕜)) (j : (Fin n → 𝕜) → (Fin m → 𝕜))
    (hj : ContDiffOn 𝕜 ω j O) :
    PartialDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) (Fin (n + m) → 𝕜)
      (Fin (n + m) → 𝕜) ω where
  toFun z := z + Fin.append 0 (j (z ∘ Fin.castAdd m))
  invFun z := z - Fin.append 0 (j (z ∘ Fin.castAdd m))
  source := {z | z ∘ Fin.castAdd m ∈ O}
  target := {z | z ∘ Fin.castAdd m ∈ O}
  map_source' z hz := by
    change (z + Fin.append 0 (j (z ∘ Fin.castAdd m))) ∘ Fin.castAdd m ∈ O
    rw [Pi.add_comp, append_zero_left_comp_castAdd, add_zero]
    exact hz
  map_target' z hz := by
    change (z - Fin.append 0 (j (z ∘ Fin.castAdd m))) ∘ Fin.castAdd m ∈ O
    rw [Pi.sub_comp, append_zero_left_comp_castAdd, sub_zero]
    exact hz
  left_inv' z _ := by
    rw [Pi.add_comp, append_zero_left_comp_castAdd, add_zero, add_sub_cancel_right]
  right_inv' z _ := by
    rw [Pi.sub_comp, append_zero_left_comp_castAdd, sub_zero, sub_add_cancel]
  open_source := O.isOpen.preimage contDiff_comp_castAdd.continuous
  open_target := O.isOpen.preimage contDiff_comp_castAdd.continuous
  contMDiffOn_toFun := by
    rw [contMDiffOn_iff_contDiffOn]
    exact contDiffOn_id.add (contDiff_append_zero_left.comp_contDiffOn
      (hj.comp contDiff_comp_castAdd.contDiffOn fun z hz => hz))
  contMDiffOn_invFun := by
    rw [contMDiffOn_iff_contDiffOn]
    exact contDiffOn_id.sub (contDiff_append_zero_left.comp_contDiffOn
      (hj.comp contDiff_comp_castAdd.contDiffOn fun z hz => hz))

/-- **The shear** `(x, y) ↦ (x + j(y), y)`, an analytic automorphism of the cylinder
`𝕜ⁿ × O ⊆ 𝕜ⁿ⁺ᵐ` over an open `O ⊆ 𝕜ᵐ` on which `j` is analytic; its inverse is the shear by `−j`.
It carries the coordinate inclusion `y ↦ (0, y)` to the graph `y ↦ (j(y), y)`: the second
automorphism of [Kol07, Lemma 39, proof] (compare the automorphisms of
[Wlo05, Lemma 4.8.1]). -/
def shearFst (O : Opens (Fin m → 𝕜)) (j : (Fin m → 𝕜) → (Fin n → 𝕜))
    (hj : ContDiffOn 𝕜 ω j O) :
    PartialDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) (Fin (n + m) → 𝕜)
      (Fin (n + m) → 𝕜) ω where
  toFun z := z + Fin.append (j (z ∘ Fin.natAdd n)) 0
  invFun z := z - Fin.append (j (z ∘ Fin.natAdd n)) 0
  source := {z | z ∘ Fin.natAdd n ∈ O}
  target := {z | z ∘ Fin.natAdd n ∈ O}
  map_source' z hz := by
    change (z + Fin.append (j (z ∘ Fin.natAdd n)) 0) ∘ Fin.natAdd n ∈ O
    rw [Pi.add_comp, append_zero_right_comp_natAdd, add_zero]
    exact hz
  map_target' z hz := by
    change (z - Fin.append (j (z ∘ Fin.natAdd n)) 0) ∘ Fin.natAdd n ∈ O
    rw [Pi.sub_comp, append_zero_right_comp_natAdd, sub_zero]
    exact hz
  left_inv' z _ := by
    rw [Pi.add_comp, append_zero_right_comp_natAdd, add_zero, add_sub_cancel_right]
  right_inv' z _ := by
    rw [Pi.sub_comp, append_zero_right_comp_natAdd, sub_zero, sub_add_cancel]
  open_source := O.isOpen.preimage contDiff_comp_natAdd.continuous
  open_target := O.isOpen.preimage contDiff_comp_natAdd.continuous
  contMDiffOn_toFun := by
    rw [contMDiffOn_iff_contDiffOn]
    exact contDiffOn_id.add (contDiff_append_zero_right.comp_contDiffOn
      (hj.comp contDiff_comp_natAdd.contDiffOn fun z hz => hz))
  contMDiffOn_invFun := by
    rw [contMDiffOn_iff_contDiffOn]
    exact contDiffOn_id.sub (contDiff_append_zero_right.comp_contDiffOn
      (hj.comp contDiff_comp_natAdd.contDiffOn fun z hz => hz))

/-- The value of the shear `(x, y) ↦ (x, y + j(x))` (rfl). -/
theorem shearSnd_apply (O : Opens (Fin n → 𝕜)) (j : (Fin n → 𝕜) → (Fin m → 𝕜))
    (hj : ContDiffOn 𝕜 ω j O) (z : Fin (n + m) → 𝕜) :
    shearSnd O j hj z = z + Fin.append 0 (j (z ∘ Fin.castAdd m)) := rfl

/-- The value of the shear `(x, y) ↦ (x + j(y), y)` (rfl). -/
theorem shearFst_apply (O : Opens (Fin m → 𝕜)) (j : (Fin m → 𝕜) → (Fin n → 𝕜))
    (hj : ContDiffOn 𝕜 ω j O) (z : Fin (n + m) → 𝕜) :
    shearFst O j hj z = z + Fin.append (j (z ∘ Fin.natAdd n)) 0 := rfl

end Shear

/-! ### The closed subspace along an analytic map with `J' = f^* J` -/

section HomOfPullback

open AnalyticSpace KLocallyRingedSpace

variable {𝕜 : Type} [RCLike 𝕜]

/-- The compatibility `Compat` for `Sp(f)` when the source ideal IS the pull-back of the target
one (`comap_ofManifoldHom_eq_pullback`, `compat_comap`). Any two models. -/
theorem compat_ofManifoldHom_of_eq {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : AnalyticManifold.{u} 𝕜 E}
    {N : AnalyticManifold.{u} 𝕜 E'} (f : M → N) (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') ω f)
    {J' : AnalyticManifold.IdealSheaf M} {J : AnalyticManifold.IdealSheaf N}
    (h : J' = J.pullback f hf) :
    QuotientSpace.Compat (ofManifoldHom f hf).1 J' J := by
  subst h
  have key := QuotientSpace.compat_comap (ofManifoldHom f hf).1 J
  rw [comap_ofManifoldHom_eq_pullback f hf J] at key
  exact key

/-- **The morphism of closed subspaces over `Sp(f)`** when `J' = f^* J`: `quotientMap` along
`Sp(f)`, for any analytic map between standard-model manifolds (two models allowed: `𝕜ⁿ → 𝕜ᵏ`);
`restrictedIdealHom` is its instance at an open inclusion. -/
def _root_.Manifold.IdealSheaf.homOfPullbackEq {k n : ℕ} {A : AnalyticManifold.{u} 𝕜 (Fin k → 𝕜)}
    {A' : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (f : A' → A)
    (hf : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜) ω f)
    {J' : AnalyticManifold.IdealSheaf A'} {J : AnalyticManifold.IdealSheaf A}
    (h : J' = J.pullback f hf) :
    J'.toAnalyticSpace ⟶ J.toAnalyticSpace :=
  quotientMap (ofManifoldHom f hf) J' J (compat_ofManifoldHom_of_eq f hf h)

end HomOfPullback

namespace PieceEmbedding

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-! ### The padded embeddings -/

/-- **The piece embedding padded along an embedding of coordinates** `σ : Fin n ↪ Fin n'` — the
ambient `padOpens σ G`, the ideal `padIdeal σ 𝓘`, the embedding `X|V ≅ Sp(G)/𝓘 ≅
Sp(padOpens σ G)/padIdeal σ 𝓘` through the slice isomorphism of `PadIdeal.lean` (the enlargement
of the ambient space in [Kol07, Theorem 36, proof]; the common ambient dimension of
[Wlo09, §7.1]). -/
def padAlong {n' : ℕ} (σ : Fin n ↪ Fin n') : PieceEmbedding 𝕜 n' X V where
  G := padOpens σ E.G
  ideal := padIdeal σ E.ideal
  isNonzeroEverywhere :=
    isNonzeroEverywhere_padIdeal_of_isNonzeroEverywhere σ E.ideal E.isNonzeroEverywhere
  isReduced := isReduced_padIdeal σ E.ideal E.isReduced
  emb := E.emb ≫ (padSliceIso σ E.ideal).inv
  emb_isIso := by
    have hE : IsIso E.emb := E.emb_isIso
    refine ⟨⟨(padSliceIso σ E.ideal).hom ≫ inv E.emb (I := hE), ?_, ?_⟩⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (fun k => E.emb ≫ k)
        ((padSliceIso σ E.ideal).inv_hom_id_assoc (inv E.emb (I := hE)))).trans
          (IsIso.hom_inv_id E.emb (I := hE)))
    · exact (Category.assoc _ _ _).trans ((congrArg (fun k => (padSliceIso σ E.ideal).hom ≫ k)
        (IsIso.inv_hom_id_assoc E.emb (I := hE) (padSliceIso σ E.ideal).inv)).trans
          (padSliceIso σ E.ideal).hom_inv_id)

/-- The ambient of the padded embedding is the padded open (rfl). -/
theorem padAlong_G {n' : ℕ} (σ : Fin n ↪ Fin n') : (E.padAlong σ).G = padOpens σ E.G := rfl

/-- The ideal of the padded embedding is the padded ideal (rfl). -/
theorem padAlong_ideal {n' : ℕ} (σ : Fin n ↪ Fin n') :
    (E.padAlong σ).ideal = padIdeal σ E.ideal := rfl

/-- **The left padding** `E.padLeft m : PieceEmbedding 𝕜 (n + m) X V` — the coordinate inclusion
`x ↦ (x, 0)` after `E` (the embedding `i'_1` of [Kol07, Lemma 39]). -/
def padLeft (m : ℕ) : PieceEmbedding 𝕜 (n + m) X V := E.padAlong (Fin.castAddEmb m)

/-- **The right padding** `E.padRight m : PieceEmbedding 𝕜 (m + n) X V` — the coordinate
inclusion `y ↦ (0, y)` after `E` (the embedding `i'_2` of [Kol07, Lemma 39]). -/
def padRight (m : ℕ) : PieceEmbedding 𝕜 (m + n) X V := E.padAlong (Fin.natAddEmb m)

/-- The ambient of the left padding, `G × 𝕜ᵐ` as `padOpens (castAddEmb m) G` (rfl). -/
theorem padLeft_G (m : ℕ) : (E.padLeft m).G = padOpens (Fin.castAddEmb m) E.G := rfl

/-- The ambient of the right padding, `𝕜ᵐ × G` as `padOpens (natAddEmb m) G` (rfl). -/
theorem padRight_G (m : ℕ) : (E.padRight m).G = padOpens (Fin.natAddEmb m) E.G := rfl

/-! ### The ambient point of an embedded point, and the points over an open -/

/-- **The ambient point** `i(y) ∈ G` of a point `y` of the piece `X|V`: the image of `y` under
the embedding followed by the closed-subspace inclusion `Sp(G)/𝓘 → Sp(G)`. -/
def ambientPoint (y : X.restrictSet V) : pieceAmbient.{u} 𝕜 E.G :=
  E.ideal.toAnalyticSpaceι
    (E.emb y)

/-- **The points of the piece over `W`** — the points of `X|V` whose ambient point lies in the
open `W ⊆ G`, the open subset of the piece over which the local resolution over `W` lives (the
part of the germ `Y_Z` over `W`, [Wlo09, §4, (3)⇒(4)]); the image of `localResolutionToPiece`. -/
def embPreimage (W : Opens (pieceAmbient.{u} 𝕜 E.G)) : Set (X.restrictSet V) :=
  {y | E.ambientPoint y ∈ W}

/-- The points over `W` form an open subset of the piece. -/
theorem isOpen_embPreimage (W : Opens (pieceAmbient.{u} 𝕜 E.G)) : IsOpen (E.embPreimage W) :=
  W.isOpen.preimage
    ((AnalyticSpace.KLocallyRingedSpace.Hom.continuous_toFun E.ideal.toAnalyticSpaceι).comp
      (AnalyticSpace.KLocallyRingedSpace.Hom.continuous_toFun E.emb))

/-! ### The transport of a piece embedding along an isomorphism of open subspaces -/

/-- **The transport of a piece embedding along an isomorphism** `h : X|V ≅ Y|U`: the same ambient
`G`, the same ideal `𝓘`, the embedding `E.emb ∘ h`. The analytic form, for an isomorphism of open
subspaces, of the compatible embeddings of [Kol07, Lemma 41]: the ambient and the ideal are
unchanged. -/
def transportAlongIso {Y : AnalyticSpace.{u} 𝕜} {U : Set Y}
    (E : PieceEmbedding 𝕜 n Y U)
    (h : X.restrictSet V ⟶ Y.restrictSet U) (hh : IsIso h) :
    PieceEmbedding 𝕜 n X V where
  G := E.G
  ideal := E.ideal
  isNonzeroEverywhere := E.isNonzeroEverywhere
  isReduced := E.isReduced
  emb := h ≫ E.emb
  emb_isIso := by
    have hE : IsIso E.emb := E.emb_isIso
    have hh' : IsIso h := hh
    refine ⟨⟨inv E.emb (I := hE) ≫ inv h (I := hh'), ?_, ?_⟩⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (fun k => h ≫ k)
        (IsIso.hom_inv_id_assoc E.emb (I := hE) (inv h (I := hh')))).trans
          (IsIso.hom_inv_id h (I := hh')))
    · exact (Category.assoc _ _ _).trans ((congrArg (fun k => inv E.emb (I := hE) ≫ k)
        (IsIso.inv_hom_id_assoc h (I := hh') E.emb)).trans (IsIso.inv_hom_id E.emb (I := hE)))

/-- The transport keeps the ambient open (rfl). -/
theorem transportAlongIso_G {Y : AnalyticSpace.{u} 𝕜} {U : Set Y}
    (E : PieceEmbedding 𝕜 n Y U)
    (h : X.restrictSet V ⟶ Y.restrictSet U) (hh : IsIso h) :
    (E.transportAlongIso h hh).G = E.G := rfl

/-- The transport keeps the ideal sheaf (rfl). -/
theorem transportAlongIso_ideal {Y : AnalyticSpace.{u} 𝕜} {U : Set Y}
    (E : PieceEmbedding 𝕜 n Y U)
    (h : X.restrictSet V ⟶ Y.restrictSet U) (hh : IsIso h) :
    (E.transportAlongIso h hh).ideal = E.ideal := rfl

/-- The transport's embedding is the composite `E.emb ∘ h` (rfl). -/
theorem transportAlongIso_emb {Y : AnalyticSpace.{u} 𝕜} {U : Set Y}
    (E : PieceEmbedding 𝕜 n Y U)
    (h : X.restrictSet V ⟶ Y.restrictSet U) (hh : IsIso h) :
    (E.transportAlongIso h hh).emb = h ≫ E.emb := rfl

/-- The ambient points correspond along `h` (rfl). -/
theorem ambientPoint_transportAlongIso {Y : AnalyticSpace.{u} 𝕜} {U : Set Y}
    (E : PieceEmbedding 𝕜 n Y U)
    (h : X.restrictSet V ⟶ Y.restrictSet U) (hh : IsIso h)
    (x : X.restrictSet V) :
    (E.transportAlongIso h hh).ambientPoint x =
      E.ambientPoint (h x) :=
  rfl

/-! ### The local resolution map over the piece -/

/-- **The restriction-of-a-quotient map** `Sp(W)/𝓘|W ⟶ Sp(G)/𝓘` along `Sp(W ↪ G)`: the morphism
of closed subspaces `homOfPullbackEq` at the open inclusion (the ideal `𝓘|W` is the pullback of
`𝓘` along the inclusion by definition, `restrictOpens`). -/
def restrictedIdealHom (W : Opens (pieceAmbient.{u} 𝕜 E.G)) :
    (E.restrictedIdeal W).toAnalyticSpace ⟶ E.ideal.toAnalyticSpace :=
  IdealSheaf.homOfPullbackEq (J' := E.restrictedIdeal W) (J := E.ideal)
    (AnalyticManifold.inclusion _ W)
    (AnalyticManifold.inclusion _ W).contMDiff rfl

/-- **The local resolution map over the piece** `Ỹ → X|V` — the local resolution map
`Π : Ỹ → Sp(W)/𝓘|W` of `PieceResolution.lean`, followed by the restriction-of-a-quotient map
`Sp(W)/𝓘|W → Sp(G)/𝓘` and the inverse of the embedding `X|V ≅ Sp(G)/𝓘`: Włodarczyk's `Ỹ_Z → Y_Z`
[Wlo09, §4, (3)⇒(4)], Kollár's resolution `g : g⁻¹(X) → X` [Kol07, Corollary 22, proof], which need
not be a composite of smooth blow-ups [Kol07, Warning 23]. Its image lies in the open
`embPreimage E W` of the piece (`range_localResolutionToPiece_subset`; over `ℂ` it is the closure
of the simple points of `Y ∩ W`, as in the clause `range Π = closure X.regularLocus` of the
resolution theorem — not all of the open over `ℝ`). -/
def localResolutionToPiece (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) :
    E.localResolution bed W hW ⟶ X.restrictSet V :=
  have : IsIso E.emb := E.emb_isIso
  (E.localResolutionMap bed W hW ≫ E.restrictedIdealHom W) ≫ inv E.emb

open AnalyticSpace KLocallyRingedSpace in
/-- The restriction-of-a-quotient map lies over `Sp(W ↪ G)`: `ι ∘ restrictedIdealHom = Sp(val) ∘
ι'` on points. -/
theorem toFun_toAnalyticSpaceι_restrictedIdealHom (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (w : (E.restrictedIdeal W).toAnalyticSpace) :
    E.ideal.toAnalyticSpaceι
        (E.restrictedIdealHom W w) =
      (((E.restrictedIdeal W).toAnalyticSpaceι w).1 :
        pieceAmbient.{u} 𝕜 E.G) :=
  rfl

/-- **The image of the local resolution map over the piece lies in the open `embPreimage E W`**:
every point of `Ỹ` maps to a point of the piece whose ambient point is in `W`. -/
theorem range_localResolutionToPiece_subset (bed : BEDanFamStar.{u} 𝕜)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) :
    Set.range ⇑(E.localResolutionToPiece bed W hW) ⊆
      E.embPreimage W := by
  rintro _ ⟨r, rfl⟩
  have hE : IsIso E.emb := E.emb_isIso
  change E.ambientPoint ((inv E.emb (I := hE))
    ((E.restrictedIdealHom W)
      (E.localResolutionMap bed W hW r))) ∈ W
  unfold ambientPoint
  have h1 : ∀ z, E.emb
      ((inv E.emb (I := hE)) z) = z := fun z =>
    congrArg
        (fun k => k z)
      (IsIso.inv_hom_id E.emb (I := hE))
  rw [h1, toFun_toAnalyticSpaceι_restrictedIdealHom]
  exact Subtype.mem _

end PieceEmbedding

end Hironaka.Manifold
