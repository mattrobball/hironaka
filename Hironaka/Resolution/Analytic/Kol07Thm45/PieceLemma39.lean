/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceIndependence
import Hironaka.AnalyticSpace.LiftRestrictStalk
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The algebra of the paddings and the stalk maps of a piece embedding

Two embeddings of one piece into `𝕜ⁿ` and `𝕜ᵐ`, padded to `x ↦ (x, 0)` and `y ↦ (0, y)` in `𝕜ⁿ⁺ᵐ`,
are carried into each other by the composite of two shears [Kol07, Lemma 39]. This module provides
the bookkeeping that the proof of that equivalence (`embeddings_equivalent_under_automorphism`,
`PieceLemma39Shear.lean`) uses:

* the paddings in `Fin.append` form — `Function.extend (Fin.castAddEmb m) v 0 = Fin.append v 0`,
  `Function.extend (Fin.natAddEmb n) w 0 = Fin.append 0 w` — and the shears on appended blocks:
  `shearSnd O j hj (append a b) = append a (b + j a)`, `(shearFst O j hj).symm (append a b) =
  append (a - j b) b` (the two automorphisms of [Kol07, Lemma 39, proof]);
* the ambient points of the padded embeddings: `(E.padAlong σ).ambientPoint y = padExt σ E.G
  (E.ambientPoint y)` (the slice isomorphism's inverse on points is the zero extension);
* **the stalk map of a piece embedding at an embedded point** `pieceStalkMap E y : 𝒪_{G, i(y)} →+*
  𝒪_{X|V, y}` (the stalk map of `X|V ≅ Sp(G)/𝓘 → Sp(G)` at `y`) and its transport
  `pieceStalkMapAt E y hq` to any point `q = i(y)`; **its kernel is the stalk of the ideal**
  (`stalkIdeal_eq_ker_pieceStalkMapAt`), the kernel of the stalk map of the inclusion of a closed
  subspace (`ker_stalkMap_ι`) read through the isomorphism `emb`. This is the form in which the
  ideal identity of Lemma 39 is proved: two ideals with the same restriction to the piece are
  equal, without passing through zero sets.

Not in the sources; bookkeeping.
-/

@[expose] public section

open TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff

universe u

noncomputable section

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-! ### The paddings in `Fin.append` form -/

section FinAppend

variable {n m : ℕ}

theorem natAdd_notMem_range_castAddEmb (i : Fin m) :
    Fin.natAdd n i ∉ Set.range (Fin.castAddEmb (n := n) m) := by
  rintro ⟨k, hk⟩
  have h := congrArg Fin.val hk
  change (k : ℕ) = n + i at h
  omega

theorem castAdd_notMem_range_natAddEmb (k : Fin n) :
    Fin.castAdd m k ∉ Set.range (Fin.natAddEmb (m := m) n) := by
  rintro ⟨i, hi⟩
  have h := congrArg Fin.val hi
  change n + (i : ℕ) = k at h
  omega

/-- The left padding in block form: `extend (castAddEmb m) v 0 = (v, 0)`. -/
theorem extend_castAddEmb (v : Fin n → 𝕜) :
    Function.extend (Fin.castAddEmb m) v 0 = Fin.append v 0 := by
  funext j
  induction j using Fin.addCases with
  | left k =>
    rw [Fin.append_left]
    exact (Fin.castAddEmb m).injective.extend_apply _ _ k
  | right i =>
    rw [Fin.append_right, Pi.zero_apply]
    exact Function.extend_apply' _ _ _ (natAdd_notMem_range_castAddEmb i)

/-- The right padding in block form: `extend (natAddEmb n) w 0 = (0, w)`. -/
theorem extend_natAddEmb (w : Fin m → 𝕜) :
    Function.extend (Fin.natAddEmb n) w 0 = Fin.append 0 w := by
  funext j
  induction j using Fin.addCases with
  | left k =>
    rw [Fin.append_left, Pi.zero_apply]
    exact Function.extend_apply' _ _ _ (castAdd_notMem_range_natAddEmb k)
  | right i =>
    rw [Fin.append_right]
    exact (Fin.natAddEmb n).injective.extend_apply _ _ i

omit [RCLike 𝕜] in
theorem append_comp_castAdd (a : Fin n → 𝕜) (b : Fin m → 𝕜) :
    Fin.append a b ∘ Fin.castAdd m = a :=
  funext fun i => Fin.append_left a b i

omit [RCLike 𝕜] in
theorem append_comp_natAdd (a : Fin n → 𝕜) (b : Fin m → 𝕜) :
    Fin.append a b ∘ Fin.natAdd n = b :=
  funext fun i => Fin.append_right a b i

theorem append_add_append (a a' : Fin n → 𝕜) (b b' : Fin m → 𝕜) :
    Fin.append a b + Fin.append a' b' = Fin.append (a + a') (b + b') := by
  funext j
  induction j using Fin.addCases with
  | left k => simp only [Pi.add_apply, Fin.append_left]
  | right i => simp only [Pi.add_apply, Fin.append_right]

theorem append_sub_append (a a' : Fin n → 𝕜) (b b' : Fin m → 𝕜) :
    Fin.append a b - Fin.append a' b' = Fin.append (a - a') (b - b') := by
  funext j
  induction j using Fin.addCases with
  | left k => simp only [Pi.sub_apply, Fin.append_left]
  | right i => simp only [Pi.sub_apply, Fin.append_right]

/-- The shear `(x, y) ↦ (x, y + j(x))` on a block pair [Kol07, Lemma 39, proof]. -/
theorem shearSnd_append (O : Opens (Fin n → 𝕜)) (j : (Fin n → 𝕜) → (Fin m → 𝕜))
    (hj : ContDiffOn 𝕜 ω j O) (a : Fin n → 𝕜) (b : Fin m → 𝕜) :
    shearSnd O j hj (Fin.append a b) = Fin.append a (b + j a) := by
  rw [shearSnd_apply, append_comp_castAdd, append_add_append, add_zero]

/-- The inverse shear `(x, y) ↦ (x - j(y), y)` on a block pair [Kol07, Lemma 39, proof]. -/
theorem shearFst_symm_append (O : Opens (Fin m → 𝕜)) (j : (Fin m → 𝕜) → (Fin n → 𝕜))
    (hj : ContDiffOn 𝕜 ω j O) (a : Fin n → 𝕜) (b : Fin m → 𝕜) :
    (shearFst O j hj).symm (Fin.append a b) = Fin.append (a - j b) b := by
  change Fin.append a b - Fin.append (j (Fin.append a b ∘ Fin.natAdd n)) 0 = _
  rw [append_comp_natAdd, append_sub_append, sub_zero]

theorem mem_source_shearSnd (O : Opens (Fin n → 𝕜)) (j : (Fin n → 𝕜) → (Fin m → 𝕜))
    (hj : ContDiffOn 𝕜 ω j O) (z : Fin (n + m) → 𝕜) :
    z ∈ (shearSnd O j hj).source ↔ z ∘ Fin.castAdd m ∈ O := Iff.rfl

theorem mem_source_shearFst (O : Opens (Fin m → 𝕜)) (j : (Fin m → 𝕜) → (Fin n → 𝕜))
    (hj : ContDiffOn 𝕜 ω j O) (z : Fin (n + m) → 𝕜) :
    z ∈ (shearFst O j hj).source ↔ z ∘ Fin.natAdd n ∈ O := Iff.rfl

end FinAppend

/-! ### The ambient points of the padded embeddings -/

section Points

variable {n n' : ℕ} (σ : Fin n ↪ Fin n') {G : Opens (Fin n → 𝕜)}
  (J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 G))

/-- The inverse of the slice isomorphism, on points, is the zero extension. -/
theorem padSliceIso_inv_val (y : J.toAnalyticSpace) :
    ((padSliceIso σ J).inv y).1 = padExt σ G y.1 := by
  set y' := (padSliceIso σ J).inv y with hy'
  have hS : y'.1 ∈ padSlice σ G := mem_padSlice_of_mem_cosupport σ J y'.2
  have h1 : padCoordProj σ G y'.1 = y.1 := by
    rw [← padSliceHom_apply_val σ J y']
    exact congrArg
        (fun k : J.toAnalyticSpace ⟶ J.toAnalyticSpace =>
      (k y).1) (padSliceIso σ J).inv_hom_id
  rw [← h1, padExt_padCoordProj_of_mem σ G hS]

end Points

namespace PieceEmbedding

variable {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-- The ambient point of the padded embedding is the zero extension of the ambient point. -/
theorem ambientPoint_padAlong {n' : ℕ} (σ : Fin n ↪ Fin n') (y : X.restrictSet V) :
    (E.padAlong σ).ambientPoint y = padExt σ E.G (E.ambientPoint y) :=
  padSliceIso_inv_val σ E.ideal (E.emb y)

/-- The left-padded ambient point in block form, `(i(y), 0)`. -/
theorem ambientPoint_padLeft_snd (m : ℕ) (y : X.restrictSet V) :
    (((E.padLeft m).ambientPoint y).2 : Fin (n + m) → 𝕜) =
      Fin.append (E.ambientPoint y).2 0 := by
  rw [padLeft, ambientPoint_padAlong, padExt_snd, extend_castAddEmb]

/-- The right-padded ambient point in block form, `(0, i(y))`. -/
theorem ambientPoint_padRight_snd (m : ℕ) (y : X.restrictSet V) :
    (((E.padRight m).ambientPoint y).2 : Fin (m + n) → 𝕜) =
      Fin.append 0 (E.ambientPoint y).2 := by
  rw [padRight, ambientPoint_padAlong, padExt_snd, extend_natAddEmb]

/-! ### The stalk map of a piece embedding at an embedded point, and its kernel -/

/-- **The stalk map of a piece embedding at an embedded point** `𝒪_{G, i(y)} →+* 𝒪_{X|V, y}`: the
stalk map at `y` of the composite `X|V ≅ Sp(G)/𝓘 → Sp(G)`. -/
def pieceStalkMap (y : X.restrictSet V) :
    AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 E.G) (E.ambientPoint y) →+*
      (X.restrictSet V).toLocallyRingedSpace.presheaf.stalk y :=
  ((E.emb ≫ E.ideal.toAnalyticSpaceι).1.stalkMap y).hom

/-- The stalk map of a piece embedding read at any point `q = i(y)` (transported along the
equation, Mathlib's `stalkCongr`). -/
def pieceStalkMapAt (y : X.restrictSet V) {q : pieceAmbient.{u} 𝕜 E.G} (hq : E.ambientPoint y = q) :
    AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 E.G) q →+*
      (X.restrictSet V).toLocallyRingedSpace.presheaf.stalk y :=
  (((AnalyticSpace.KLocallyRingedSpace.ofManifold 𝕜 (Fin n → 𝕜)
      (pieceAmbient.{u} 𝕜 E.G)).toLocallyRingedSpace.presheaf.stalkCongr
        (Inseparable.of_eq hq.symm)).hom ≫
    (E.emb ≫ E.ideal.toAnalyticSpaceι).1.stalkMap y).hom

theorem pieceStalkMapAt_rfl (y : X.restrictSet V) : E.pieceStalkMapAt y rfl = E.pieceStalkMap y :=
    by
  unfold pieceStalkMapAt pieceStalkMap
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
  exact congrArg CommRingCat.Hom.hom (Category.id_comp _)

/-- **The stalk of a piece embedding's ideal at an embedded point is the kernel of its stalk
map** (the kernel of the stalk map of the inclusion of a closed subspace, `ker_stalkMap_ι`, read
through the isomorphism `emb`): the germs of `G` vanishing on the piece are exactly those pulled
back to `0` on `X|V`. The device by which two ideals defining the same piece are shown equal in the
proof of [Kol07, Lemma 39]. -/
theorem stalkIdeal_eq_ker_pieceStalkMap (y : X.restrictSet V) :
    E.ideal.stalkIdeal (E.ambientPoint y) = RingHom.ker (E.pieceStalkMap y) := by
  have hE : IsIso E.emb := E.emb_isIso
  have hE' : @IsIso (AnalyticSpace.KLocallyRingedSpace.{u} 𝕜) _ _ _ E.emb :=
    ⟨⟨@inv (AnalyticSpace.{u} 𝕜) _ _ _ E.emb hE,
      @IsIso.hom_inv_id (AnalyticSpace.{u} 𝕜) _ _ _ E.emb hE,
      @IsIso.inv_hom_id (AnalyticSpace.{u} 𝕜) _ _ _ E.emb hE⟩⟩
  have hinj : Function.Injective (E.emb.1.stalkMap y).hom :=
    (@AnalyticSpace.KLocallyRingedSpace.bijective_stalkMap_of_isIso _ _ _ _ E.emb hE' y).1
  have hcomp : E.pieceStalkMap y = (E.emb.1.stalkMap y).hom.comp
      (E.ideal.toAnalyticSpaceι.1.stalkMap (E.emb.1.base y)).hom :=
    congrArg CommRingCat.Hom.hom
      (LocallyRingedSpace.stalkMap_comp E.emb.1 E.ideal.toAnalyticSpaceι.1 y)
  have hker : E.ideal.stalkIdeal (E.ambientPoint y) =
      RingHom.ker (E.ideal.toAnalyticSpaceι.1.stalkMap (E.emb.1.base y)).hom :=
    (AnalyticSpace.QuotientSpace.ker_stalkMap_ι _ _ (E.emb.1.base y)).symm
  refine hker.trans ((Ideal.ext fun s => ?_).trans (congrArg RingHom.ker hcomp.symm))
  constructor
  · intro h
    refine RingHom.mem_ker.mpr ?_
    change (E.emb.1.stalkMap y).hom
      ((E.ideal.toAnalyticSpaceι.1.stalkMap (E.emb.1.base y)).hom s) = 0
    rw [RingHom.mem_ker.mp h, map_zero]
  · intro h
    refine RingHom.mem_ker.mpr (hinj ?_)
    rw [map_zero]
    exact RingHom.mem_ker.mp h

theorem stalkIdeal_eq_ker_pieceStalkMapAt (y : X.restrictSet V) {q : pieceAmbient.{u} 𝕜 E.G}
    (hq : E.ambientPoint y = q) :
    E.ideal.stalkIdeal q = RingHom.ker (E.pieceStalkMapAt y hq) := by
  subst hq
  exact (E.stalkIdeal_eq_ker_pieceStalkMap y).trans
    (congrArg RingHom.ker (E.pieceStalkMapAt_rfl y).symm)

/-- A germ vanishes under the stalk map of the piece iff it lies in the ideal — the membership
form of `stalkIdeal_eq_ker_pieceStalkMapAt`. -/
theorem pieceStalkMapAt_eq_zero_iff (y : X.restrictSet V) {q : pieceAmbient.{u} 𝕜 E.G}
    (hq : E.ambientPoint y = q)
        (s : AnalyticManifold.IdealSheaf.stalkRing (pieceAmbient.{u} 𝕜 E.G) q) :
    E.pieceStalkMapAt y hq s = 0 ↔ s ∈ E.ideal.stalkIdeal q :=
  RingHom.mem_ker.symm.trans
    (Iff.of_eq (congrArg (s ∈ ·) (E.stalkIdeal_eq_ker_pieceStalkMapAt y hq).symm))

end PieceEmbedding

end Hironaka.Manifold
