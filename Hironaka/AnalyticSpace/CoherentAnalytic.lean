/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Coherent
import Hironaka.AnalyticSpace.CoherentLemmas
import Hironaka.AnalyticSpace.CoherentQuotient
import Hironaka.AnalyticSpace.CoherentTransport
import Hironaka.AnalyticSpace.Oka.Main
import Hironaka.AnalyticSpace.Oka.Transport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# Coherence of the structure sheaf of an analytic `K`-space

The structure sheaf of an analytic space is coherent ([BM97, (3.8)(3)]; [Fre17, Ch. V, 7.3]): Oka's
theorem on the model `(Kⁿ, 𝒜_{Kⁿ})` (`oka_coherent`, `Hironaka/AnalyticSpace/Oka/`) passes to the
open subspace `(G, 𝒜_G)` (`isCoherent_restrict`), to the local model `(S(𝓘), (𝒜_G/𝓘)|_{S(𝓘)})`
(`isCoherent_quotientSpace`), to its open subspaces, and along the `K`-isomorphisms of Hironaka's
clause (i) to an open cover of any analytic `K`-space (`isCoherent_of_kIso`,
`isCoherent_of_forall_restrictOpen`): `isCoherent_analyticSpace`. Serre's form for every ideal
sheaf (`isCoherent_idealSheaf`) is the `q = 1` slice through
`isCoherent_iff_forall_isCoherent_idealSheaf`.

The intersection of two ideal sheaves of finite type is of finite type ([Fre17, Ch. I, 10.7]): the
relations of the one-row matrix `(e₁, …, e_k, f₁, …, f_l)` of local generators of `E` and `F` are
locally generated (coherence), and `E_x ∩ F_x` is the image of the relation module under
`(a, b) ↦ Σ a_i e_i` — so the sections `Σ_i R_{n,i} e_i` for the generators `R_n` of the relations
generate `E_x ∩ F_x` at every point near `x` (`hasLocalGenerators_inf`). The bridge between
`IdealSheaf.HasLocalGenerators` (one generator per section, on the whole space) and
`HasLocalGeneratorsOn` with `p = 1` is `hasLocalGenerators_iff_hasLocalGeneratorsOn_top`. The
radical and the saturation of an ideal sheaf are treated in
`Hironaka/AnalyticSpace/CoherentColon.lean`, `Hironaka/AnalyticSpace/NoetherDerived.lean` and
`Hironaka/AnalyticSpace/ModelTransport.lean`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Manifold

section Bridge

variable {R : Type*} [CommRing R]

/-- An ideal of `R`, read as a submodule of `Fin 1 → R`. -/
def idealRow (I : Ideal R) : Submodule R (Fin 1 → R) :=
  Submodule.comap (LinearEquiv.funUnique (Fin 1) R R).toLinearMap I

theorem mem_idealRow_iff (I : Ideal R) (a : Fin 1 → R) : a ∈ idealRow I ↔ a 0 ∈ I := by
  rw [idealRow, Submodule.mem_comap]
  rfl

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf CommRingCat.{u} X}

/-- Local generation of a family of stalk ideals (`IdealSheaf.HasLocalGenerators`) is the `p = 1`
case of `HasLocalGeneratorsOn` over `⊤`. -/
theorem hasLocalGenerators_iff_hasLocalGeneratorsOn_top (I : ∀ x : X, Ideal (𝒪.presheaf.stalk x)) :
    IdealSheaf.HasLocalGenerators I ↔ HasLocalGeneratorsOn 𝒪 ⊤ 1 fun x _ => idealRow (I x) := by
  constructor
  · intro h x _
    obtain ⟨U, hxU, k, f, hf⟩ := h.exists_fin x
    refine ⟨U, le_top, hxU, k, fun l _ => f l, fun y hy => ?_⟩
    ext a
    rw [mem_idealRow_iff, hf y hy, Ideal.mem_span_range_iff_exists_fun,
      Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, funext fun i => ?_⟩
      rw [Fin.fin_one_eq_zero i, Finset.sum_apply]
      simpa using hc
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have := congrFun hc 0
      simpa [Finset.sum_apply] using this
  · intro h x
    obtain ⟨V, hVU, hxV, k, r, hr⟩ := h x trivial
    refine ⟨V, hxV, Fin k, inferInstance, fun l => r l 0, fun y hy => ?_⟩
    ext s
    have h1 : s ∈ I y ↔ (fun _ : Fin 1 => s) ∈ idealRow (I y) :=
      (mem_idealRow_iff (I y) fun _ => s).symm
    have h2 : idealRow (I y) = Submodule.span _
        (Set.range fun l j => 𝒪.presheaf.germ V y hy (r l j)) := hr y hy
    rw [h1, h2, Submodule.mem_span_range_iff_exists_fun, Ideal.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have := congrFun hc 0
      simpa [Finset.sum_apply] using this
    · rintro ⟨c, hc⟩
      refine ⟨c, funext fun i => ?_⟩
      rw [Fin.fin_one_eq_zero i, Finset.sum_apply]
      simpa using hc

end Bridge

section Row

variable {A B : Type*} [CommRing A] [CommRing B]

/-- A sum over the concatenated row `(u | v)`, split. -/
theorem sum_elim_finSumFinEquiv_mul (φ : A →+* B) {k₁ k₂ : ℕ} (u : Fin k₁ → A) (v : Fin k₂ → A)
    (a : Fin (k₁ + k₂) → B) :
    ∑ x, φ (Sum.elim u v (finSumFinEquiv.symm x)) * a x =
      ∑ i, φ (u i) * a (finSumFinEquiv (Sum.inl i)) +
        ∑ j, φ (v j) * a (finSumFinEquiv (Sum.inr j)) := by
  rw [← Equiv.sum_comp finSumFinEquiv (fun x => φ (Sum.elim u v (finSumFinEquiv.symm x)) * a x)]
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

end Row

end Manifold

namespace AnalyticSpace

open Manifold

variable {K : Type} [RCLike K]

/-- Oka's theorem on the open subspace `(G, 𝒜_G)` of `(Kⁿ, 𝒜_{Kⁿ})`. -/
theorem isCoherent_analyticSpaceOfOpen (n : ℕ) (G : Opens (Kn.{u} K n)) :
    IsCoherent (analyticSpaceOfOpen K n G).toLocallyRingedSpace.𝒪 :=
  KLocallyRingedSpace.isCoherent_restrictOpen (affine K n) (oka_coherent n) G

/-- The structure sheaf of a local model `(S(𝓘), (𝒜_G/𝓘)|_{S(𝓘)})` is coherent
([Fre17, Ch. V, 7.3]; [BM97, (3.8)(3)]). -/
theorem isCoherent_localModel (n : ℕ) (G : Opens (Kn.{u} K n)) {k : ℕ}
    (f : Fin k → AnalyticFun K n G) :
    IsCoherent (localModel K n G f).toLocallyRingedSpace.𝒪 :=
  QuotientSpace.isCoherent_quotientSpace _ (modelIdeal K n G f) (isCoherent_analyticSpaceOfOpen n G)

/-- The structure sheaf of an analytic `K`-space is coherent [BM97, (3.8)(3)]. -/
theorem isCoherent_analyticSpace (X : AnalyticSpace.{u} K) :
    IsCoherent X.toLocallyRingedSpace.𝒪 := by
  refine KLocallyRingedSpace.isCoherent_of_forall_restrictOpen X.toKLocallyRingedSpace fun x => ?_
  obtain ⟨U, hxU, n, k, G, f, W, ⟨e⟩⟩ := X.locallyModel x
  exact ⟨U, hxU, KLocallyRingedSpace.isCoherent_of_kIso e
    (KLocallyRingedSpace.isCoherent_restrictOpen _ (isCoherent_localModel n G f) W)⟩

/-- Serre's form [BM97, (3.8)(3)]: every ideal sheaf on an analytic `K`-space is coherent. -/
theorem isCoherent_idealSheaf (X : AnalyticSpace.{u} K) (J : IdealSheaf X.toLocallyRingedSpace.𝒪) :
    J.IsCoherent :=
  isCoherent_iff_forall_isCoherent_idealSheaf.mp (isCoherent_analyticSpace X) J

/-- The intersection of two ideal sheaves of finite type on an analytic `K`-space is locally
finitely generated [Fre17, Ch. I, 10.7]. -/
theorem hasLocalGenerators_inf (X : AnalyticSpace.{u} K)
    (E F : IdealSheaf X.toLocallyRingedSpace.𝒪) :
    IdealSheaf.HasLocalGenerators (𝒪 := X.toLocallyRingedSpace.𝒪)
      fun x : X => E.stalkIdeal x ⊓ F.stalkIdeal x := by
  intro a
  obtain ⟨U₁, haU₁, k₁, e, -, he⟩ := E.exists_generators a
  obtain ⟨U₂, haU₂, k₂, f, -, hf⟩ := F.exists_generators a
  obtain ⟨U, hU⟩ : ∃ U, U = U₁ ⊓ U₂ := ⟨_, rfl⟩
  have hUU₁ : U ≤ U₁ := hU ▸ inf_le_left
  have hUU₂ : U ≤ U₂ := hU ▸ inf_le_right
  have haU : a ∈ U := by
    rw [hU, ← SetLike.mem_coe, Opens.coe_inf]
    exact ⟨haU₁, haU₂⟩
  obtain ⟨row, hrow⟩ : ∃ row : Fin (k₁ + k₂) → X.toLocallyRingedSpace.𝒪.presheaf.obj (op U),
      row = fun x => Sum.elim
        (fun i => X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE hUU₁).op (e i))
        (fun j => X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE hUU₂).op (f j))
        (finSumFinEquiv.symm x) := ⟨_, rfl⟩
  obtain ⟨V, hVU, haV, k, R, hR⟩ :=
    isCoherent_analyticSpace X U (k₁ + k₂) 1 (fun _ : Fin 1 => row) a haU
  have hVU₁ : V ≤ U₁ := hVU.trans hUU₁
  have hVU₂ : V ≤ U₂ := hVU.trans hUU₂
  refine ⟨V, haV, Fin k, inferInstance, fun n => ∑ i, R n (finSumFinEquiv (Sum.inl i)) *
    X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE hVU₁).op (e i), fun b hb => ?_⟩
  -- the germs at `b`
  have hge : ∀ i, X.toLocallyRingedSpace.𝒪.presheaf.germ U b (hVU hb)
      (X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE hUU₁).op (e i)) =
        X.toLocallyRingedSpace.𝒪.presheaf.germ U₁ b (hVU₁ hb) (e i) := fun i =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hgf : ∀ j, X.toLocallyRingedSpace.𝒪.presheaf.germ U b (hVU hb)
      (X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE hUU₂).op (f j)) =
        X.toLocallyRingedSpace.𝒪.presheaf.germ U₂ b (hVU₂ hb) (f j) := fun j =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hrel : ∀ v : Fin (k₁ + k₂) → X.toLocallyRingedSpace.𝒪.presheaf.stalk b,
      v ∈ relationSubmodule X.toLocallyRingedSpace.𝒪 (fun _ : Fin 1 => row) b (hVU hb) ↔
        ∑ i, v (finSumFinEquiv (Sum.inl i)) *
            X.toLocallyRingedSpace.𝒪.presheaf.germ U₁ b (hVU₁ hb) (e i) +
          ∑ j, v (finSumFinEquiv (Sum.inr j)) *
            X.toLocallyRingedSpace.𝒪.presheaf.germ U₂ b (hVU₂ hb) (f j) = 0 := by
    intro v
    rw [mem_relationSubmodule_row_iff]
    subst hrow
    rw [sum_elim_finSumFinEquiv_mul (X.toLocallyRingedSpace.𝒪.presheaf.germ U b (hVU hb)).hom]
    simp only [hge, hgf, mul_comm _ (v _)]
  have hRw : relationSubmodule X.toLocallyRingedSpace.𝒪 (fun _ : Fin 1 => row) b (hVU hb) =
      Submodule.span _ (Set.range fun n x =>
        X.toLocallyRingedSpace.𝒪.presheaf.germ V b hb (R n x)) := hR b hb
  have hgen : ∀ n, X.toLocallyRingedSpace.𝒪.presheaf.germ V b hb
      (∑ i, R n (finSumFinEquiv (Sum.inl i)) *
        X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE hVU₁).op (e i)) =
      ∑ i, X.toLocallyRingedSpace.𝒪.presheaf.germ V b hb (R n (finSumFinEquiv (Sum.inl i))) *
        X.toLocallyRingedSpace.𝒪.presheaf.germ U₁ b (hVU₁ hb) (e i) := fun n => by
    rw [map_sum]
    simp only [map_mul, TopCat.Presheaf.germ_res_apply]
  ext s
  constructor
  · intro hs
    rw [Submodule.mem_inf] at hs
    obtain ⟨hsE, hsF⟩ := hs
    rw [he b (hVU₁ hb), Ideal.mem_span_range_iff_exists_fun] at hsE
    rw [hf b (hVU₂ hb), Ideal.mem_span_range_iff_exists_fun] at hsF
    obtain ⟨c, hc⟩ := hsE
    obtain ⟨d, hd⟩ := hsF
    have hw : (fun x => Sum.elim c (fun j => -d j) (finSumFinEquiv.symm x)) ∈
        relationSubmodule X.toLocallyRingedSpace.𝒪 (fun _ : Fin 1 => row) b (hVU hb) := by
      rw [hrel]
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, neg_mul,
        Finset.sum_neg_distrib]
      rw [hc, hd, add_neg_cancel]
    rw [hRw, Submodule.mem_span_range_iff_exists_fun] at hw
    obtain ⟨lam, hlam⟩ := hw
    have hci : ∀ i, c i = ∑ n, lam n *
        X.toLocallyRingedSpace.𝒪.presheaf.germ V b hb (R n (finSumFinEquiv (Sum.inl i))) := by
      intro i
      have := congrFun hlam (finSumFinEquiv (Sum.inl i))
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply,
        Sum.elim_inl] at this
      exact this.symm
    rw [Ideal.mem_span_range_iff_exists_fun]
    refine ⟨lam, ?_⟩
    simp only [hgen]
    rw [← hc]
    simp only [hci, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  · intro hs
    rw [Ideal.mem_span_range_iff_exists_fun] at hs
    obtain ⟨lam, rfl⟩ := hs
    refine Submodule.sum_mem _ fun n _ => Ideal.mul_mem_left _ _ ?_
    rw [Submodule.mem_inf, hgen n]
    constructor
    · rw [he b (hVU₁ hb)]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · have hRn : (fun x => X.toLocallyRingedSpace.𝒪.presheaf.germ V b hb (R n x)) ∈
          relationSubmodule X.toLocallyRingedSpace.𝒪 (fun _ : Fin 1 => row) b (hVU hb) := by
        rw [hRw]
        exact Submodule.subset_span ⟨n, rfl⟩
      rw [hrel] at hRn
      rw [eq_neg_of_add_eq_zero_left hRn, hf b (hVU₂ hb)]
      exact neg_mem_iff.mpr
        (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩))

end AnalyticSpace
