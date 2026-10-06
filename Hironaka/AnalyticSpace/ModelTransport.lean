/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.QuotientLift
public import Hironaka.AnalyticSpace.Coherent
import Hironaka.AnalyticSpace.NoetherDerived
import Hironaka.AnalyticSpace.OpenSubspaceLemmas
import Hironaka.AnalyticSpace.Quotient
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Transport from the local models: the Noether lemma and Cartan's radical theorem

Two statements about ideal sheaves are available on the models `(G, 𝒜_G)`, `G ⊆ Kⁿ` open: the
Noether lemma (every increasing sequence of ideal sheaves of finite type is locally stationary) and
Cartan's theorem on radicals (the radical of an ideal sheaf of finite type is of finite type). This
file carries
them to an arbitrary analytic `K`-space `X`. Near `x ∈ X` Hironaka's clause (i) gives a
`K`-isomorphism `e : X|U ≅ localModel K n G f` (`exists_kIso_localModel`); an ideal sheaf on `X`
restricts to `X|U` (`restrictIdeal`, the pull-back along the open immersion), is pulled back
along `e⁻¹` to the local model (`QuotientSpace.comap`), and is lifted to `(G, 𝒜_G)`
(`QuotientSpace.liftIdeal`: the preimage of the stalk ideal under the surjective stalk map of the
quotient at the points of the support, the unit ideal elsewhere). All three steps are monotone
(`comap_mono`, `liftIdeal_mono`), and each is injective on stalk ideals — `Ideal.comap` along a
surjection and `Ideal.map` along a bijection — so a stalkwise equality on `G` descends to `X`. The
points of the neighbourhood in `X` are parametrized from the model side, `y = incl (e⁻¹ z)`, so
that no round trip `e⁻¹ (e y') = y'` is needed.

Each theorem takes the model statement as an explicit argument (`hK1` for the Noether lemma,
`hK2` for Cartan's theorem), so that the transport is separate from the analysis.

* `locallyStationary_of_noether`: the Noether lemma on the models gives local stationarity of
  every increasing sequence of ideal sheaves of finite type on `X`;
* `stabilizes_of_isCompact_closure_of_noether`, `isNoetherian_of_compactSpace_of_noether`,
  `hasLocalGenerators_iSup_colon_pow_of_noether`: the derivations of
  `Hironaka/AnalyticSpace/NoetherDerived.lean` with that hypothesis discharged from `hK1`;
* `hasLocalGenerators_radical_of_cartan`: the radical of an ideal sheaf of finite type on `X` has
  local generators, from `hK2`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u

namespace AnalyticSpace

/-- `Ideal.map` along a bijective ring homomorphism is injective. -/
theorem ideal_map_injective_of_bijective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Bijective f) : Function.Injective (Ideal.map f) := by
  intro I₁ I₂ h
  have := congrArg (Ideal.comap f) h
  rwa [Ideal.comap_map_of_bijective f hf, Ideal.comap_map_of_bijective f hf] at this

namespace QuotientSpace

/-- The pull-back of ideal sheaves along a morphism is monotone. -/
theorem comap_mono {X' X : LocallyRingedSpace.{u}} (φ : X' ⟶ X) {J J' : IdealSheaf X.𝒪}
    (h : J ≤ J') : comap φ J ≤ comap φ J' := by
  intro z'
  rw [stalkIdeal_comap, stalkIdeal_comap]
  exact Ideal.map_mono (IdealSheaf.le_def.mp h _)

/-- The lift of ideal sheaves from the quotient is monotone. -/
theorem liftIdeal_mono (X : LocallyRingedSpace.{u}) (J : IdealSheaf X.𝒪)
    {J' J'' : IdealSheaf (quotientSpace X J).𝒪} (h : J' ≤ J'') :
    liftIdeal X J J' ≤ liftIdeal X J J'' := by
  intro x
  rw [stalkIdeal_liftIdeal, stalkIdeal_liftIdeal]
  by_cases hx : x ∈ J.support
  · rw [liftStalk_of_mem X J J' hx, liftStalk_of_mem X J J'' hx]
    exact Ideal.comap_mono (IdealSheaf.le_def.mp h _)
  · rw [liftStalk_of_notMem X J J' hx, liftStalk_of_notMem X J J'' hx]
    exact le_rfl

end QuotientSpace

variable {K : Type} [RCLike K]

/-- Local stationarity on an analytic `K`-space of an increasing sequence of ideal sheaves of
finite type, from the Noether lemma on the models (the hypothesis `hK1`). -/
theorem locallyStationary_of_noether (X : AnalyticSpace.{u} K)
    (hK1 : ∀ (n : ℕ) (G : Opens (Kn.{u} K n))
      (J : ℕ → IdealSheaf (analyticSpaceOfOpen K n G).toLocallyRingedSpace.𝒪),
      (∀ m, J m ≤ J (m + 1)) → ∀ x : analyticSpaceOfOpen K n G,
        ∃ (U : Opens (analyticSpaceOfOpen K n G)) (_ : x ∈ U) (N : ℕ),
          ∀ m ≥ N, ∀ y ∈ U, (J m).stalkIdeal y = (J N).stalkIdeal y)
    (C : ℕ → IdealSheaf X.toLocallyRingedSpace.𝒪) (hC : ∀ m, C m ≤ C (m + 1)) (x : X) :
    ∃ (V : Opens X) (_ : x ∈ V) (N : ℕ), ∀ m ≥ N, ∀ y ∈ V,
      (C m).stalkIdeal y = (C N).stalkIdeal y := by
  obtain ⟨U, hxU, n, k, G, f, ⟨e⟩⟩ := AnalyticSpace.exists_kIso_localModel X x
  -- the sequences on `X | U`, on the local model, on `(G, 𝒜_G)`
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℕ →
      IdealSheaf (X.toKLocallyRingedSpace.restrictOpen U).toLocallyRingedSpace.𝒪,
      C₁ = fun m => KLocallyRingedSpace.restrictIdeal X.toKLocallyRingedSpace (C m) U := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℕ → IdealSheaf (QuotientSpace.quotientSpace
      (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f)).𝒪,
      C₂ = fun m => QuotientSpace.comap e.inv.1 (C₁ m) := ⟨_, rfl⟩
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℕ → IdealSheaf (analyticSpaceOfOpen K n G).toLocallyRingedSpace.𝒪,
      C₃ = fun m => QuotientSpace.liftIdeal _ (modelIdeal K n G f) (C₂ m) := ⟨_, rfl⟩
  have hmono₃ : ∀ m, C₃ m ≤ C₃ (m + 1) := fun m => by
    rw [hC₃]
    refine QuotientSpace.liftIdeal_mono _ _ ?_
    rw [hC₂]
    refine QuotientSpace.comap_mono _ ?_
    rw [hC₁]
    exact QuotientSpace.comap_mono _ (hC m)
  -- the Noether lemma at the point of `G` under `x`
  obtain ⟨U', hp₀, N, hN⟩ := hK1 n G C₃ hmono₃ (e.hom.1.base ⟨x, hxU⟩).1
  -- the open of the local model over `U'`, and its image in `X | U` under `e⁻¹`
  obtain ⟨Wm, hWm⟩ : ∃ Wm : Opens (localModel K n G f),
      Wm = QuotientSpace.preimage _ (modelIdeal K n G f) U' := ⟨_, rfl⟩
  have : IsIso e.inv.1 := KLocallyRingedSpace.KIso.isIso_hom_val e.symm
  have hopen : IsOpenMap e.inv.1.base :=
    (PresheafedSpace.IsOpenImmersion.base_open (f := e.inv.1.toShHom.hom)).isOpenMap
  refine ⟨(Opens.isOpenEmbedding U).functor.obj
    ⟨e.inv.1.base '' (Wm : Set (localModel K n G f)), hopen _ Wm.isOpen⟩, ?_, N, ?_⟩
  · refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    refine ⟨e.hom.1.base ⟨x, hxU⟩, ?_, ?_⟩
    · rw [hWm]
      exact hp₀
    · have h := congrArg (fun g : X.toKLocallyRingedSpace.restrictOpen U ⟶
        X.toKLocallyRingedSpace.restrictOpen U => g.1.base ⟨x, hxU⟩) e.hom_inv_id
      exact h
  · rintro m hm y ⟨y', ⟨z, hz, rfl⟩, rfl⟩
    have hz' : z.1 ∈ U' := by rw [hWm] at hz; exact hz
    have h3 := hN m hm z.1 hz'
    rw [hC₃] at h3
    dsimp only at h3
    rw [QuotientSpace.stalkIdeal_liftIdeal, QuotientSpace.stalkIdeal_liftIdeal,
      QuotientSpace.liftStalk_of_mem _ _ _ z.2, QuotientSpace.liftStalk_of_mem _ _ _ z.2] at h3
    have h2 := Ideal.comap_injective_of_surjective _ (QuotientSpace.stalkMap_surjective _ _ _) h3
    rw [hC₂] at h2
    have h2' := (QuotientSpace.stalkIdeal_comap e.inv.1 (C₁ m) ⟨z.1, z.2⟩).symm.trans
      (h2.trans (QuotientSpace.stalkIdeal_comap e.inv.1 (C₁ N) ⟨z.1, z.2⟩))
    have hiso₁ : IsIso e.inv.1.toShHom.hom :=
      SheafedSpace.is_presheafedSpace_iso e.inv.1.toShHom
    have hiso₂ : IsIso (e.inv.1.stalkMap ⟨z.1, z.2⟩) :=
      PresheafedSpace.stalkMap.isIso e.inv.1.toShHom.hom _
    have h1 := ideal_map_injective_of_bijective _ (ConcreteCategory.bijective_of_isIso _) h2'
    rw [hC₁] at h1
    have h1' := (QuotientSpace.stalkIdeal_comap (X.toKLocallyRingedSpace.ofRestrict U).1 (C m)
      _).symm.trans (h1.trans
        (QuotientSpace.stalkIdeal_comap (X.toKLocallyRingedSpace.ofRestrict U).1 (C N) _))
    have hiso₃ : IsIso ((X.toKLocallyRingedSpace.ofRestrict U).1.stalkMap
        (e.inv.1.base ⟨z.1, z.2⟩)) :=
      LocallyRingedSpace.ofRestrict_stalkMap_isIso X.toLocallyRingedSpace
        (Opens.isOpenEmbedding U) _
    exact ideal_map_injective_of_bijective _ (ConcreteCategory.bijective_of_isIso _) h1'

/-- On a set with compact closure every decreasing sequence of closed subspaces stabilizes, from
the Noether lemma on the models ([BM97, 3.9]). -/
theorem stabilizes_of_isCompact_closure_of_noether (X : AnalyticSpace.{u} K)
    (hK1 : ∀ (n : ℕ) (G : Opens (Kn.{u} K n))
      (J : ℕ → IdealSheaf (analyticSpaceOfOpen K n G).toLocallyRingedSpace.𝒪),
      (∀ m, J m ≤ J (m + 1)) → ∀ x : analyticSpaceOfOpen K n G,
        ∃ (U : Opens (analyticSpaceOfOpen K n G)) (_ : x ∈ U) (N : ℕ),
          ∀ m ≥ N, ∀ y ∈ U, (J m).stalkIdeal y = (J N).stalkIdeal y)
    (W : ℕ → ClosedSubspace X) (hW : ∀ m, ClosedSubspace.le (W (m + 1)) (W m)) (U : Set X)
    (hU : IsCompact (closure U)) :
    ∃ N, ∀ m ≥ N, ∀ x ∈ U, (W m).stalkIdeal x = (W N).stalkIdeal x :=
  stabilizes_of_isCompact_closure_of_locallyStationary X W
    (locallyStationary_of_noether X hK1 W hW) U hU

/-- A compact analytic `K`-space is Noetherian, from the Noether lemma on the models
([BM97, 3.9]). -/
theorem isNoetherian_of_compactSpace_of_noether (X : AnalyticSpace.{u} K) [CompactSpace X]
    (hK1 : ∀ (n : ℕ) (G : Opens (Kn.{u} K n))
      (J : ℕ → IdealSheaf (analyticSpaceOfOpen K n G).toLocallyRingedSpace.𝒪),
      (∀ m, J m ≤ J (m + 1)) → ∀ x : analyticSpaceOfOpen K n G,
        ∃ (U : Opens (analyticSpaceOfOpen K n G)) (_ : x ∈ U) (N : ℕ),
          ∀ m ≥ N, ∀ y ∈ U, (J m).stalkIdeal y = (J N).stalkIdeal y) :
    X.IsNoetherian :=
  isNoetherian_of_compactSpace_of_locallyStationary X (locallyStationary_of_noether X hK1)

/-- The saturation `⨆_k (J : I^k)` has local generators, from the Noether lemma on the models. -/
theorem hasLocalGenerators_iSup_colon_pow_of_noether (X : AnalyticSpace.{u} K)
    (hK1 : ∀ (n : ℕ) (G : Opens (Kn.{u} K n))
      (J : ℕ → IdealSheaf (analyticSpaceOfOpen K n G).toLocallyRingedSpace.𝒪),
      (∀ m, J m ≤ J (m + 1)) → ∀ x : analyticSpaceOfOpen K n G,
        ∃ (U : Opens (analyticSpaceOfOpen K n G)) (_ : x ∈ U) (N : ℕ),
          ∀ m ≥ N, ∀ y ∈ U, (J m).stalkIdeal y = (J N).stalkIdeal y)
    (J I : IdealSheaf X.toLocallyRingedSpace.𝒪) :
    IdealSheaf.HasLocalGenerators (𝒪 := X.toLocallyRingedSpace.𝒪)
      fun x : X => ⨆ k : ℕ,
        Submodule.colon (J.stalkIdeal x) (SetLike.coe (I.stalkIdeal x ^ k)) :=
  hasLocalGenerators_iSup_colon_pow_of_locallyStationary X J I
    (locallyStationary_of_noether X hK1)

/-- The radical of an ideal sheaf of finite type on an analytic `K`-space has local generators,
from Cartan's theorem on the models (the hypothesis `hK2`): the radical of the lifted ideal is the
preimage of the radical, so the local generators on the model map to local generators of the
radical on `X`. -/
theorem hasLocalGenerators_radical_of_cartan (X : AnalyticSpace.{u} K)
    (hK2 : ∀ (n : ℕ) (G : Opens (Kn.{u} K n))
      (J : IdealSheaf (analyticSpaceOfOpen K n G).toLocallyRingedSpace.𝒪),
      IdealSheaf.HasLocalGenerators (𝒪 := (analyticSpaceOfOpen K n G).toLocallyRingedSpace.𝒪)
        fun x => (J.stalkIdeal x).radical)
    (J : IdealSheaf X.toLocallyRingedSpace.𝒪) :
    IdealSheaf.HasLocalGenerators (𝒪 := X.toLocallyRingedSpace.𝒪)
      fun x : X => (J.stalkIdeal x).radical := by
  intro x
  obtain ⟨U, hxU, n, k, G, f, ⟨e⟩⟩ := AnalyticSpace.exists_kIso_localModel X x
  obtain ⟨J₁, hJ₁⟩ : ∃ J₁ :
      IdealSheaf (X.toKLocallyRingedSpace.restrictOpen U).toLocallyRingedSpace.𝒪,
      J₁ = KLocallyRingedSpace.restrictIdeal X.toKLocallyRingedSpace J U := ⟨_, rfl⟩
  obtain ⟨J₂, hJ₂⟩ : ∃ J₂ : IdealSheaf (QuotientSpace.quotientSpace
      (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f)).𝒪,
      J₂ = QuotientSpace.comap e.inv.1 J₁ := ⟨_, rfl⟩
  obtain ⟨J₃, hJ₃⟩ : ∃ J₃ : IdealSheaf (analyticSpaceOfOpen K n G).toLocallyRingedSpace.𝒪,
      J₃ = QuotientSpace.liftIdeal _ (modelIdeal K n G f) J₂ := ⟨_, rfl⟩
  obtain ⟨U', hp₀, ι, hι, g, hg⟩ := hK2 n G J₃ (e.hom.1.base ⟨x, hxU⟩).1
  obtain ⟨Wm, hWm⟩ : ∃ Wm : Opens (localModel K n G f),
      Wm = QuotientSpace.preimage _ (modelIdeal K n G f) U' := ⟨_, rfl⟩
  have : IsIso e.inv.1 := KLocallyRingedSpace.KIso.isIso_hom_val e.symm
  have hiso₁ : IsIso e.inv.1.toShHom.hom := SheafedSpace.is_presheafedSpace_iso e.inv.1.toShHom
  have hc : IsIso e.inv.1.toHom.c :=
    @PresheafedSpace.c_isIso_of_iso CommRingCat.{u} _ _ _ e.inv.1.toHom hiso₁
  have hopen : IsOpenMap e.inv.1.base :=
    (PresheafedSpace.IsOpenImmersion.base_open (f := e.inv.1.toShHom.hom)).isOpenMap
  have hinj : Function.Injective e.inv.1.base :=
    (PresheafedSpace.IsOpenImmersion.base_open (f := e.inv.1.toShHom.hom)).injective
  -- the image `V₁` of the model open over `U'` in `X | U`, and its preimage under `e⁻¹`
  obtain ⟨V₁, hV₁⟩ : ∃ V₁ : Opens (X.toKLocallyRingedSpace.restrictOpen U),
      V₁ = ⟨e.inv.1.base '' (Wm : Set (localModel K n G f)), hopen _ Wm.isOpen⟩ := ⟨_, rfl⟩
  have hmemV : ∀ z ∈ Wm, e.inv.1.base z ∈ V₁ := by
    intro z hz
    rw [hV₁]
    exact ⟨z, hz, rfl⟩
  have hWV : (Opens.map e.inv.1.base).obj V₁ = Wm := by
    ext z
    rw [hV₁]
    constructor
    · rintro ⟨z', hz', hzz'⟩
      rwa [hinj hzz'] at hz'
    · intro hz
      exact ⟨z, hz, rfl⟩
  -- sections of `X | U` over `V₁` pulling back to the classes of the generators on the model
  have hsurj : Function.Surjective (e.inv.1.c.app (op V₁)) :=
    (ConcreteCategory.bijective_of_isIso (e.inv.1.c.app (op V₁))).2
  choose s hs using fun i => hsurj ((localModel K n G f).toLocallyRingedSpace.presheaf.map
    (eqToHom (hWV.trans hWm)).op (QuotientSpace.classFamily _ (modelIdeal K n G f) U' (g i)))
  refine ⟨(Opens.isOpenEmbedding U).functor.obj V₁, ⟨⟨x, hxU⟩, ?_, rfl⟩, ι, hι, fun i => s i, ?_⟩
  · have h := congrArg (fun g : X.toKLocallyRingedSpace.restrictOpen U ⟶
      X.toKLocallyRingedSpace.restrictOpen U => g.1.base ⟨x, hxU⟩) e.hom_inv_id
    have hmem : e.hom.1.base ⟨x, hxU⟩ ∈ Wm := by rw [hWm]; exact hp₀
    have := hmemV _ hmem
    rwa [show e.inv.1.base (e.hom.1.base ⟨x, hxU⟩) = ⟨x, hxU⟩ from h] at this
  · rintro y ⟨y', hy', rfl⟩
    rw [hV₁] at hy'
    obtain ⟨z, hz, rfl⟩ := hy'
    have hz' : z.1 ∈ U' := by rw [hWm] at hz; exact hz
    have hiso₂ : IsIso (e.inv.1.stalkMap z) :=
      PresheafedSpace.stalkMap.isIso e.inv.1.toShHom.hom _
    have hbij : Function.Bijective (e.inv.1.stalkMap z).hom := ConcreteCategory.bijective_of_isIso _
    have hker : RingHom.ker (e.inv.1.stalkMap z).hom = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp hbij.1
    -- (1) the generators on the model at `z.1`, read through the lift
    have h1 := hg z.1 hz'
    dsimp only at h1
    rw [hJ₃, QuotientSpace.stalkIdeal_liftIdeal, QuotientSpace.liftStalk_of_mem _ _ _ z.2] at h1
    replace h1 : Ideal.comap ((QuotientSpace.ι (analyticSpaceOfOpen K n G).toLocallyRingedSpace
        (modelIdeal K n G f)).stalkMap ⟨z.1, z.2⟩).hom
        (Ideal.radical (QuotientSpace.stalkIdeal (QuotientSpace.quotientSpace
          (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f)) J₂ ⟨z.1, z.2⟩)) =
        Ideal.span (Set.range fun i =>
          (analyticSpaceOfOpen K n G).toLocallyRingedSpace.𝒪.presheaf.germ U' z.1 hz' (g i)) := by
      rw [Ideal.comap_radical]
      exact h1
    -- (2) the radical of `J₂` at `z` is generated by the classes of the generators
    have hsurjσ : Function.Surjective ((QuotientSpace.ι
        (analyticSpaceOfOpen K n G).toLocallyRingedSpace (modelIdeal K n G f)).stalkMap
          ⟨z.1, z.2⟩).hom :=
      QuotientSpace.stalkMap_surjective _ _ _
    have h2 : (J₂.stalkIdeal z).radical = Ideal.span (Set.range fun i =>
        (localModel K n G f).toLocallyRingedSpace.presheaf.germ Wm z hz
          ((localModel K n G f).toLocallyRingedSpace.presheaf.map (eqToHom hWm).op
            (QuotientSpace.classFamily _ (modelIdeal K n G f) U' (g i)))) := by
      have h := congrArg (Ideal.map ((QuotientSpace.ι _ (modelIdeal K n G f)).stalkMap
        ⟨z.1, z.2⟩).hom) h1
      rw [Ideal.map_comap_of_surjective _ hsurjσ] at h
      refine h.trans ((Ideal.map_span _ _).trans (congrArg Ideal.span ?_))
      refine (Set.range_comp _ _).symm.trans (congrArg Set.range (funext fun i => ?_))
      exact (QuotientSpace.stalkMap_ι_germ _ _ U' ⟨z.1, z.2⟩ hz' (g i)).trans
        (TopCat.Presheaf.germ_res_apply _ (eqToHom hWm) z hz _).symm
    -- (3) the classes are the pull-backs of the sections `s i`
    have h3 : ∀ i, (localModel K n G f).toLocallyRingedSpace.presheaf.germ Wm z hz
        ((localModel K n G f).toLocallyRingedSpace.presheaf.map (eqToHom hWm).op
          (QuotientSpace.classFamily _ (modelIdeal K n G f) U' (g i))) =
        e.inv.1.stalkMap z
          ((X.toKLocallyRingedSpace.restrictOpen U).toLocallyRingedSpace.presheaf.germ V₁
            (e.inv.1.base z) (hmemV z hz) (s i)) := by
      intro i
      rw [LocallyRingedSpace.stalkMap_germ_apply, hs i]
      exact (TopCat.Presheaf.germ_res_apply _ (eqToHom hWm) z hz _).trans
        (TopCat.Presheaf.germ_res_apply _ (eqToHom (hWV.trans hWm)) z (hmemV z hz) _).symm
    -- (4) descend to `X | U` along the bijective stalk map of `e⁻¹`
    have h5 : Ideal.map (e.inv.1.stalkMap z).hom (J₁.stalkIdeal (e.inv.1.base z)) =
        J₂.stalkIdeal z := by
      rw [hJ₂]
      exact (QuotientSpace.stalkIdeal_comap e.inv.1 J₁ z).symm
    have h4 : (J₁.stalkIdeal (e.inv.1.base z)).radical = Ideal.span (Set.range fun i =>
        (X.toKLocallyRingedSpace.restrictOpen U).toLocallyRingedSpace.presheaf.germ V₁
          (e.inv.1.base z) (hmemV z hz) (s i)) := by
      apply ideal_map_injective_of_bijective _ hbij
      exact (Ideal.map_radical_of_surjective hbij.2 (hker.le.trans bot_le)).trans
        ((congrArg Ideal.radical h5).trans (h2.trans
          ((congrArg Ideal.span (congrArg Set.range (funext h3))).trans
            ((congrArg Ideal.span (Set.range_comp _ _)).trans (Ideal.map_span _ _).symm))))
    -- (5) descend to `X` along the bijective stalk map of the open immersion
    have hiso₃ :
        IsIso ((X.toKLocallyRingedSpace.ofRestrict U).1.stalkMap (e.inv.1.base z)) :=
      LocallyRingedSpace.ofRestrict_stalkMap_isIso X.toLocallyRingedSpace
        (Opens.isOpenEmbedding U) _
    have hbij' : Function.Bijective ((X.toKLocallyRingedSpace.ofRestrict U).1.stalkMap
        (e.inv.1.base z)).hom := ConcreteCategory.bijective_of_isIso _
    have hker' : RingHom.ker ((X.toKLocallyRingedSpace.ofRestrict U).1.stalkMap
        (e.inv.1.base z)).hom = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp hbij'.1
    have h6 : Ideal.map ((X.toKLocallyRingedSpace.ofRestrict U).1.stalkMap (e.inv.1.base z)).hom
        (J.stalkIdeal (U.inclusion' (e.inv.1.base z))) = J₁.stalkIdeal (e.inv.1.base z) := by
      rw [hJ₁]
      exact (QuotientSpace.stalkIdeal_comap (X.toKLocallyRingedSpace.ofRestrict U).1 J _).symm
    have h7 : ∀ i, (X.toKLocallyRingedSpace.restrictOpen U).toLocallyRingedSpace.presheaf.germ V₁
        (e.inv.1.base z) (hmemV z hz) (s i) =
        (X.toKLocallyRingedSpace.ofRestrict U).1.stalkMap (e.inv.1.base z)
          (X.toLocallyRingedSpace.presheaf.germ ((Opens.isOpenEmbedding U).functor.obj V₁)
            (U.inclusion' (e.inv.1.base z)) ⟨e.inv.1.base z, hmemV z hz, rfl⟩ (s i)) := fun i =>
      (LocallyRingedSpace.restrictStalkIso_inv_eq_germ_apply X.toLocallyRingedSpace
        (Opens.isOpenEmbedding U) V₁ (e.inv.1.base z) (hmemV z hz) (s i)).symm.trans
        (congrArg (fun φ : X.toLocallyRingedSpace.presheaf.stalk (U.inclusion' (e.inv.1.base z)) ⟶
            (X.toKLocallyRingedSpace.restrictOpen U).toLocallyRingedSpace.presheaf.stalk
              (e.inv.1.base z) =>
          φ (X.toLocallyRingedSpace.presheaf.germ ((Opens.isOpenEmbedding U).functor.obj V₁)
            (U.inclusion' (e.inv.1.base z)) ⟨e.inv.1.base z, hmemV z hz, rfl⟩ (s i)))
          (LocallyRingedSpace.restrictStalkIso_inv_eq_ofRestrict X.toLocallyRingedSpace
            (Opens.isOpenEmbedding U) (e.inv.1.base z)))
    dsimp only
    apply ideal_map_injective_of_bijective _ hbij'
    exact (Ideal.map_radical_of_surjective hbij'.2 (hker'.le.trans bot_le)).trans
      ((congrArg Ideal.radical h6).trans (h4.trans
        ((congrArg Ideal.span (congrArg Set.range (funext h7))).trans
          ((congrArg Ideal.span (Set.range_comp _ _)).trans (Ideal.map_span _ _).symm))))

end AnalyticSpace
