/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Coherent
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Coherence under isomorphisms and restriction to opens

Coherence of a sheaf of rings ([Fre17, Ch. V, 7.2], in the shape of [Fre17, Ch. I, 10.3];
`Hironaka/AnalyticSpace/Coherent.lean`) is a statement about sections over opens, their germs and
the spans of germs at every point. It is therefore invariant under isomorphisms of locally ringed
spaces and local. This file records the three transport lemmas that the proof of
`isCoherent_analyticSpace` (`Hironaka/AnalyticSpace/CoherentAnalytic.lean`) needs to pass from Oka's
theorem on the model `(Kⁿ, 𝒜_{Kⁿ})` through a local model to an analytic `K`-space, which is by
definition locally `K`-isomorphic to an open subspace of a local model:

* `isCoherent_of_isIso`: an isomorphism `φ : X ≅ Y` of locally ringed spaces carries coherence of
  `𝒪_X` to coherence of `𝒪_Y` — sections are pulled back along the inverse and the stalk maps of
  the inverse are ring isomorphisms compatible with germs (`stalkMap_germ_apply`);
* `isCoherent_restrict`: coherence passes to the open subspace `X | U` — the sections of `X | U`
  over `V` are the sections of `X` over the image of `V`, with the same germs (`restrictStalkIso`);
* `isCoherent_of_forall_restrict`: coherence is local — it holds on `X` when every point has an
  open neighbourhood `U` with `𝒪_{X|U}` coherent.

The algebraic core is one lemma: a ring isomorphism `τ : R ≃+* S` carries `ker F = span (v)` to
`ker (τ F) = span (τ v)` (`relKer_eq_span_map`); every transport is this lemma applied to the stalk
isomorphism at each point with the germ identities of the sections. Routine; not stated in the
sources.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Manifold

section Algebra

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring isomorphism carries relations to relations. -/
theorem mem_relKer_map_iff (τ : R ≃+* S) {p q : ℕ} (F : Fin q → Fin p → R) (a : Fin p → R) :
    (fun j => τ (a j)) ∈ relKer (fun i j => τ (F i j)) ↔ a ∈ relKer F := by
  simp only [mem_relKer_iff]
  refine forall_congr' fun i => ?_
  have : ∑ j, τ (F i j) * τ (a j) = τ (∑ j, F i j * a j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => (map_mul τ _ _).symm
  rw [this, τ.map_eq_zero_iff]

/-- A ring isomorphism carries spans to spans. -/
theorem mem_span_range_map_iff (τ : R ≃+* S) {p k : ℕ} (v : Fin k → Fin p → R) (a : Fin p → R) :
    (fun j => τ (a j)) ∈ Submodule.span S (Set.range fun l j => τ (v l j)) ↔
      a ∈ Submodule.span R (Set.range v) := by
  simp only [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun l => τ.symm (c l), ?_⟩
    funext j
    have := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    apply τ.injective
    rw [map_sum]
    simp only [map_mul, RingEquiv.apply_symm_apply]
    exact this
  · rintro ⟨c, hc⟩
    refine ⟨fun l => τ (c l), ?_⟩
    funext j
    have := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this, map_sum]
    simp only [map_mul]

/-- The core of every transport: a ring isomorphism carries `ker F = span v` to
`ker (τ F) = span (τ v)`. -/
theorem relKer_eq_span_map (τ : R ≃+* S) {p q k : ℕ} (F : Fin q → Fin p → R)
    (v : Fin k → Fin p → R) (h : relKer F = Submodule.span R (Set.range v)) :
    relKer (fun i j => τ (F i j)) = Submodule.span S (Set.range fun l j => τ (v l j)) := by
  ext b
  obtain ⟨a, rfl⟩ : ∃ a : Fin p → R, b = fun j => τ (a j) :=
    ⟨fun j => τ.symm (b j), by funext j; simp⟩
  rw [mem_relKer_map_iff, mem_span_range_map_iff, h]

end Algebra

section Sheaf

variable {X X' : TopCat.{u}} {𝒪 : TopCat.Sheaf CommRingCat.{u} X}
  {𝒪' : TopCat.Sheaf CommRingCat.{u} X'}

/-- Transport of "the relations of `F` at `y` are spanned by the germs of `r`" along a ring
isomorphism of stalks compatible with the germs of `F` and of `r`. -/
theorem relationSubmodule_eq_span_of_ringEquiv {U V : Opens X} {U' V' : Opens X'} {y : X} {y' : X'}
    (hy : y ∈ U) (hy' : y' ∈ U') (hyV : y ∈ V) (hyV' : y' ∈ V')
    (τ : 𝒪.presheaf.stalk y ≃+* 𝒪'.presheaf.stalk y') {p q k : ℕ}
    (F : Fin q → Fin p → 𝒪.presheaf.obj (op U)) (F' : Fin q → Fin p → 𝒪'.presheaf.obj (op U'))
    (r : Fin k → Fin p → 𝒪.presheaf.obj (op V)) (r' : Fin k → Fin p → 𝒪'.presheaf.obj (op V'))
    (hF : ∀ i j, τ (𝒪.presheaf.germ U y hy (F i j)) = 𝒪'.presheaf.germ U' y' hy' (F' i j))
    (hr : ∀ l j, τ (𝒪.presheaf.germ V y hyV (r l j)) = 𝒪'.presheaf.germ V' y' hyV' (r' l j))
    (h : relationSubmodule 𝒪 F y hy =
      Submodule.span (𝒪.presheaf.stalk y) (Set.range fun l j => 𝒪.presheaf.germ V y hyV (r l j))) :
    relationSubmodule 𝒪' F' y' hy' =
      Submodule.span (𝒪'.presheaf.stalk y')
        (Set.range fun l j => 𝒪'.presheaf.germ V' y' hyV' (r' l j)) := by
  have h1 : (fun i j => 𝒪'.presheaf.germ U' y' hy' (F' i j)) =
      fun i j => τ (𝒪.presheaf.germ U y hy (F i j)) := by
    funext i j; rw [hF]
  have h2 : (fun l j => 𝒪'.presheaf.germ V' y' hyV' (r' l j)) =
      fun l j => τ (𝒪.presheaf.germ V y hyV (r l j)) := by
    funext l j; rw [hr]
  rw [relationSubmodule, h1, h2]
  exact relKer_eq_span_map τ _ _ h

end Sheaf

end Manifold

namespace AnalyticSpace

open Manifold

section LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}}

/-- Coherence of the structure sheaf transports along an isomorphism of locally ringed spaces
(sections pulled back along the inverse; the stalk maps of the inverse are ring isomorphisms
compatible with germs). -/
theorem isCoherent_of_isIso (φ : X ⟶ Y) [IsIso φ] (hX : IsCoherent X.𝒪) : IsCoherent Y.𝒪 := by
  intro U p q F y hyU
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Y ⟶ X, ψ = inv φ := ⟨_, rfl⟩
  have : IsIso ψ := hψ ▸ inferInstance
  have hc : IsIso ψ.toHom.c :=
    @PresheafedSpace.c_isIso_of_iso CommRingCat.{u} _ _ _ ψ.toHom
      (SheafedSpace.is_presheafedSpace_iso ψ.toShHom)
  have hψφ : ∀ y : Y, φ.base (ψ.base y) = y := fun y => by
    have := congrArg (fun f : Y ⟶ Y => f.base y) (hψ ▸ IsIso.inv_hom_id φ)
    simpa using this
  -- the pulled-back matrix over `W = φ⁻¹ U`
  obtain ⟨W, hW⟩ : ∃ W : Opens X, W = (Opens.map φ.base).obj U := ⟨_, rfl⟩
  have hxW : ψ.base y ∈ W := by
    rw [hW]; change φ.base (ψ.base y) ∈ U; rw [hψφ]; exact hyU
  have hUW : (Opens.map ψ.base).obj W = U := by
    ext y'
    rw [hW]
    change φ.base (ψ.base y') ∈ U ↔ y' ∈ U
    rw [hψφ]
  have hsurj : Function.Surjective (ψ.c.app (op W)) :=
    (ConcreteCategory.bijective_of_isIso (ψ.c.app (op W))).2
  choose F'' hF'' using fun ij : Fin q × Fin p =>
    hsurj (Y.presheaf.map (eqToHom hUW).op (F ij.1 ij.2))
  obtain ⟨V, hVW, hxV, k, r, hr⟩ := hX W p q (fun i j => F'' (i, j)) (ψ.base y) hxW
  have hVU : (Opens.map ψ.base).obj V ≤ U := by
    intro y' hy'
    have : ψ.base y' ∈ W := hVW hy'
    rw [hW] at this
    change φ.base (ψ.base y') ∈ U at this
    rwa [hψφ] at this
  -- the generators, pushed forward along `ψ`
  refine ⟨(Opens.map ψ.base).obj V, hVU, hxV, k, fun l j => ψ.c.app (op V) (r l j),
    fun y' hy' => ?_⟩
  have hx'V : ψ.base y' ∈ V := hy'
  obtain ⟨τ, hτ⟩ : ∃ τ : X.presheaf.stalk (ψ.base y') ≃+* Y.presheaf.stalk y',
      τ = (asIso (ψ.stalkMap y')).commRingCatIsoToRingEquiv := ⟨_, rfl⟩
  have hτs : ∀ s, τ s = ψ.stalkMap y' s := fun s => by rw [hτ]; rfl
  have hF : ∀ i j, τ (X.presheaf.germ W (ψ.base y') (hVW hx'V) (F'' (i, j))) =
      Y.presheaf.germ U y' (hVU hy') (F i j) := fun i j => by
    rw [hτs, LocallyRingedSpace.stalkMap_germ_apply, hF'' (i, j)]
    exact TopCat.Presheaf.germ_res_apply Y.presheaf (eqToHom hUW) y' (hVW hx'V) (F i j)
  have hr' : ∀ l j, τ (X.presheaf.germ V (ψ.base y') hx'V (r l j)) =
      Y.presheaf.germ ((Opens.map ψ.base).obj V) y' hy' (ψ.c.app (op V) (r l j)) := fun l j => by
    rw [hτs]
    exact LocallyRingedSpace.stalkMap_germ_apply ψ V y' hx'V (r l j)
  exact relationSubmodule_eq_span_of_ringEquiv (hVW hx'V) (𝒪' := Y.𝒪) (hVU hy') hx'V hy' τ
    (fun i j => F'' (i, j)) F r _ hF hr' (hr (ψ.base y') hx'V)

variable (X)

/-- The image of the preimage of an open is contained in the open. -/
theorem functor_obj_map_obj_le (U W : Opens X) :
    (Opens.isOpenEmbedding U).functor.obj ((Opens.map U.inclusion').obj W) ≤ W := by
  rintro y ⟨w, hw, rfl⟩
  exact hw

/-- Coherence of the structure sheaf passes to the open subspaces `X | U`. -/
theorem isCoherent_restrict (hX : IsCoherent X.𝒪) (U : Opens X) :
    IsCoherent (X.restrict (Opens.isOpenEmbedding U)).𝒪 := by
  intro V p q F x hxV
  have hxV' : (U.inclusion' x : X) ∈ (Opens.isOpenEmbedding U).functor.obj V := ⟨x, hxV, rfl⟩
  obtain ⟨W, hWV, hxW, k, r, hr⟩ := hX ((Opens.isOpenEmbedding U).functor.obj V) p q F _ hxV'
  have hW'V : (Opens.map U.inclusion').obj W ≤ V := by
    intro y hy
    obtain ⟨v, hv, hvy⟩ := hWV hy
    have hvy' : v = y := Subtype.val_injective hvy
    rw [← hvy']
    exact hv
  have hle := functor_obj_map_obj_le X U W
  refine ⟨(Opens.map U.inclusion').obj W, hW'V, hxW, k,
    fun l j => X.presheaf.map (homOfLE hle).op (r l j), fun y hy => ?_⟩
  have hyW : (U.inclusion' y : X) ∈ W := hy
  obtain ⟨τ, hτ⟩ : ∃ τ : X.presheaf.stalk (U.inclusion' y) ≃+*
      (X.restrict (Opens.isOpenEmbedding U)).presheaf.stalk y,
      τ = (X.restrictStalkIso (Opens.isOpenEmbedding U) y).symm.commRingCatIsoToRingEquiv :=
    ⟨_, rfl⟩
  have hτs : ∀ s, τ s = (X.restrictStalkIso (Opens.isOpenEmbedding U) y).inv s := fun s => by
    rw [hτ]; rfl
  have hF : ∀ i j, τ (X.presheaf.germ _ _ (hWV hyW) (F i j)) =
      (X.restrict (Opens.isOpenEmbedding U)).presheaf.germ V y (hW'V hy) (F i j) := fun i j => by
    rw [hτs]
    exact LocallyRingedSpace.restrictStalkIso_inv_eq_germ_apply X _ V y (hW'V hy) (F i j)
  have hr' : ∀ l j, τ (X.presheaf.germ W _ hyW (r l j)) =
      (X.restrict (Opens.isOpenEmbedding U)).presheaf.germ _ y hy
        (X.presheaf.map (homOfLE hle).op (r l j)) := fun l j => by
    rw [hτs]
    exact (congrArg (fun s => (X.restrictStalkIso (Opens.isOpenEmbedding U) y).inv s)
      (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hle) _ ⟨y, hy, rfl⟩ (r l j)).symm).trans
      (LocallyRingedSpace.restrictStalkIso_inv_eq_germ_apply X _ _ y hy _)
  exact relationSubmodule_eq_span_of_ringEquiv (𝒪 := X.𝒪)
    (𝒪' := (X.restrict (Opens.isOpenEmbedding U)).𝒪) (hWV hyW) (hW'V hy) hyW hy τ F F r _ hF hr'
    (hr _ hyW)

/-- Coherence of the structure sheaf is local: it holds when every point has an open
neighbourhood `U` with `𝒪_{X|U}` coherent. -/
theorem isCoherent_of_forall_restrict
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ IsCoherent (X.restrict (Opens.isOpenEmbedding U)).𝒪) :
    IsCoherent X.𝒪 := by
  intro V p q F x hxV
  obtain ⟨U, hxU, hU⟩ := h x
  have hle := functor_obj_map_obj_le X U V
  obtain ⟨W', hW'V', hxW', k, r', hr'⟩ := hU ((Opens.map U.inclusion').obj V) p q
    (fun i j => X.presheaf.map (homOfLE hle).op (F i j)) ⟨x, hxU⟩ hxV
  have hxW'' : x ∈ (Opens.isOpenEmbedding U).functor.obj W' := ⟨⟨x, hxU⟩, hxW', rfl⟩
  have hW'V : (Opens.isOpenEmbedding U).functor.obj W' ≤ V := by
    rintro y ⟨w, hw, rfl⟩
    exact hW'V' hw
  refine ⟨(Opens.isOpenEmbedding U).functor.obj W', hW'V, hxW'', k, r', ?_⟩
  rintro y ⟨w, hw, rfl⟩
  have hw1 : (U.inclusion' w : X) ∈ (Opens.isOpenEmbedding U).functor.obj W' := ⟨w, hw, rfl⟩
  have hw2 : (U.inclusion' w : X) ∈
      (Opens.isOpenEmbedding U).functor.obj ((Opens.map U.inclusion').obj V) :=
    ⟨w, hW'V' hw, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : (X.restrict (Opens.isOpenEmbedding U)).presheaf.stalk w ≃+*
      X.presheaf.stalk (U.inclusion' w),
      τ = (X.restrictStalkIso (Opens.isOpenEmbedding U) w).commRingCatIsoToRingEquiv := ⟨_, rfl⟩
  have hτs : ∀ s, τ s = (X.restrictStalkIso (Opens.isOpenEmbedding U) w).hom s := fun s => by
    rw [hτ]; rfl
  have hF : ∀ i j, τ ((X.restrict (Opens.isOpenEmbedding U)).presheaf.germ _ w (hW'V' hw)
      (X.presheaf.map (homOfLE hle).op (F i j))) = X.presheaf.germ V _ (hle hw2) (F i j) :=
    fun i j => by
      rw [hτs]
      exact (LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply X _ _ w (hW'V' hw) _).trans
        (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hle) _ hw2 (F i j))
  have hr'' : ∀ l j, τ ((X.restrict (Opens.isOpenEmbedding U)).presheaf.germ W' w hw (r' l j)) =
      X.presheaf.germ _ _ hw1 (r' l j) := fun l j => by
    rw [hτs]
    exact LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply X _ W' w hw (r' l j)
  exact relationSubmodule_eq_span_of_ringEquiv (𝒪 := (X.restrict (Opens.isOpenEmbedding U)).𝒪)
    (𝒪' := X.𝒪) (hW'V' hw) (hle hw2) hw hw1 τ _ F r' r' hF hr'' (hr' w hw)

end LocallyRingedSpace

section KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- Coherence passes to the open subspaces `X | U` of a `K`-local-ringed space. -/
theorem KLocallyRingedSpace.isCoherent_restrictOpen (X : KLocallyRingedSpace.{u} K)
    (hX : IsCoherent X.toLocallyRingedSpace.𝒪) (U : Opens X) :
    IsCoherent (X.restrictOpen U).toLocallyRingedSpace.𝒪 :=
  isCoherent_restrict X.toLocallyRingedSpace hX U

/-- Coherence transports along a `K`-isomorphism. -/
theorem KLocallyRingedSpace.isCoherent_of_kIso {A B : KLocallyRingedSpace.{u} K} (e : KIso A B)
    (hB : IsCoherent B.toLocallyRingedSpace.𝒪) : IsCoherent A.toLocallyRingedSpace.𝒪 :=
  haveI := KLocallyRingedSpace.KIso.isIso_hom_val e.symm
  isCoherent_of_isIso e.symm.hom.1 hB

/-- Coherence of a `K`-local-ringed space is local. -/
theorem KLocallyRingedSpace.isCoherent_of_forall_restrictOpen (X : KLocallyRingedSpace.{u} K)
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ IsCoherent (X.restrictOpen U).toLocallyRingedSpace.𝒪) :
    IsCoherent X.toLocallyRingedSpace.𝒪 :=
  isCoherent_of_forall_restrict X.toLocallyRingedSpace h

end KLocallyRingedSpace

end AnalyticSpace
