/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Resolution.Defs
public import Hironaka.Manifold.FiniteSuccession.Restrict.RestrictBundle
public import Hironaka.Resolution.Analytic.ModelTransport.Principalization
public import Hironaka.Resolution.Analytic.ModelTransport.SquareChart
import Hironaka.Manifold.BlowUp.Restrict
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.Chart.Transport
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Closed embeddings of analytic manifolds

A closed embedding `τ : N → M` of analytic manifolds
(`AnalyticManifold.IsClosedAnalyticEmbedding`: an analytic embedding, Mathlib's
`IsSmoothEmbedding` at `ω`, with closed image — the first two clauses of
`IdealSheaf.IsPushforwardAlong`, `IdealSheaf.IsPushforwardAlong.isClosedAnalyticEmbedding`) has
the universal property of the subspace `τ(N)`: every analytic map
into `M` with values in `τ(N)` factors analytically through `τ`
(`IsClosedAnalyticEmbedding.exists_comp_eq`). When its image is a closed submanifold it identifies
`N` with the bundled submanifold `IsClosedSubmanifold.toAnalyticManifold` of its image
(`IsClosedAnalyticEmbedding.toDiffeomorph`): the corestriction of `τ` is analytic into the bundled
submanifold, and its inverse is the factorization of the inclusion of the submanifold through `τ`.
Conversely a closed embedding of the spaces onto a closed submanifold, through which the inclusion
of the submanifold factors analytically, is an immersion, so a closed embedding of analytic
manifolds (`IsClosedAnalyticEmbedding.of_isClosedSubmanifold`, through the splitting `splitEquiv`
of the coordinates along the adapted indices); so the push-forward of ideal sheaves may equally be
stated with the universal property (`IdealSheaf.isPushforwardAlong_iff_exists_comp_eq`). The
dimensions of two analytically isomorphic nonempty manifolds agree (`dim_eq_of_diffeomorph`: the
differential at a point is a linear isomorphism of the models).

The re-modelling of `τ` between manifolds on different model spaces (`transportBetween`, the
two-model form of `AnalyticMap.transport`) keeps the closed embedding onto a closed submanifold
(`IsClosedAnalyticEmbedding.transportBetween`), the closed submanifold `τ(N)` with its codimension
(`IsClosedSubmanifold.range_transportBetween`), the containment of its ideal sheaf in an ideal
sheaf (`stalkIdeal_idealSheaf_range_transportBetween_le`) and the pull-back of ideal sheaves
along `τ` (`IdealSheaf.transport_pullback_transportBetween`); these carry the hypotheses of the
commutation of a principalization with closed embeddings to the standard models. The restriction
of `τ` between opens `U' ⊆ N`, `U ⊆ M` with `τ(U') ⊆ U` is `restrictBetween`.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n s : ℕ}

/-- The coordinates of `𝕜ⁿ` split into those outside the range of `σ` and those on it. -/
noncomputable def splitCoordₗ (σ : Fin s ↪ Fin n) :
    (Fin n → 𝕜) →ₗ[𝕜] (Fin (n - s) → 𝕜) × (Fin s → 𝕜) where
  toFun y := (projCompl σ y, fun i => y (σ i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The splitting of the coordinates is bijective: injective, and `𝕜ⁿ` and `𝕜^{n-s} × 𝕜^s` have
the same dimension. -/
theorem splitCoordₗ_bijective (σ : Fin s ↪ Fin n) :
    Function.Bijective (splitCoordₗ (𝕜 := 𝕜) σ) := by
  have hinj : Function.Injective (splitCoordₗ (𝕜 := 𝕜) σ) := by
    refine (injective_iff_map_eq_zero _).mpr fun y hy => ?_
    have h1 : projCompl σ y = 0 := congrArg Prod.fst hy
    have h2 : ∀ i, y (σ i) = 0 := fun i => congrFun (congrArg Prod.snd hy) i
    rw [← embedCompl_projCompl σ h2, h1]
    funext j
    simp [embedCompl]
  have hsn : s ≤ n := by simpa using Fintype.card_le_of_embedding σ
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  simp [Module.finrank_prod, Nat.sub_add_cancel hsn]

/-- The linear isomorphism `𝕜^{n-s} × 𝕜^s ≃ E` of the coordinates `ψ` split along `σ`: it sends
`(w, 0)` to the point of the coordinate subspace `{z_σ = 0}` with the other coordinates `w`
(`splitEquiv_apply_zero`). -/
noncomputable def splitEquiv (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (σ : Fin s ↪ Fin n) :
    ((Fin (n - s) → 𝕜) × (Fin s → 𝕜)) ≃L[𝕜] E :=
  (LinearEquiv.ofBijective _ (splitCoordₗ_bijective σ)).symm.toContinuousLinearEquiv.trans ψ.symm

theorem splitEquiv_apply_zero (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (σ : Fin s ↪ Fin n)
    (w : Fin (n - s) → 𝕜) : splitEquiv ψ σ (w, 0) = ψ.symm (embedCompl σ w) := by
  simp only [splitEquiv, ContinuousLinearEquiv.trans_apply,
    LinearEquiv.coe_toContinuousLinearEquiv']
  congr 1
  rw [LinearEquiv.symm_apply_eq]
  ext1
  · exact (projCompl_embedCompl σ w).symm
  · funext i
    exact (embedCompl_apply_range σ w i).symm

end Manifold

namespace AnalyticManifold

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : AnalyticManifold.{u} 𝕜 E}
  {N : AnalyticManifold.{u} 𝕜 E'}

/-- The analytic map `τ : N → M`, between analytic manifolds modelled on `E'` and on `E`, is a
**closed embedding of analytic manifolds**: an analytic embedding (Mathlib's `IsSmoothEmbedding` at
`ω`: an analytic immersion, of the form `u ↦ (u, 0)` in suitable charts near every point, which is a
homeomorphism onto its image) with closed image. -/
def IsClosedAnalyticEmbedding (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯) : Prop :=
  Manifold.IsSmoothEmbedding 𝓘(𝕜, E') 𝓘(𝕜, E) ω τ ∧ IsClosed (Set.range τ)

/-! ### The factorization through a closed embedding -/

section Factorization

variable {τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯} (hτ : IsClosedAnalyticEmbedding τ)
include hτ

/-- A closed embedding of analytic manifolds is a closed embedding of the underlying spaces. -/
theorem IsClosedAnalyticEmbedding.isClosedEmbedding : Topology.IsClosedEmbedding τ :=
  ⟨hτ.1.isEmbedding, hτ.2⟩

/-- **Every analytic map into `M` with values in `τ(N)` factors analytically through `τ`**: the
factor is continuous since `τ` is a topological embedding, and analytic since `τ` is an analytic
immersion (`ContMDiff.iff_comp_isImmersion`). -/
theorem IsClosedAnalyticEmbedding.exists_comp_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {P : AnalyticManifold.{u} 𝕜 F} (h : C^ω⟮𝓘(𝕜, F), P; 𝓘(𝕜, E), M⟯)
    (hh : Set.range h ⊆ Set.range τ) :
    ∃ h' : C^ω⟮𝓘(𝕜, F), P; 𝓘(𝕜, E'), N⟯, ∀ x, τ (h' x) = h x := by
  choose g hg using fun x => hh ⟨x, rfl⟩
  have hcomp : ⇑τ ∘ g = h := funext hg
  have hc : Continuous g := hτ.1.isEmbedding.continuous_iff.mpr (hcomp ▸ h.contMDiff.continuous)
  exact ⟨⟨g, (ContMDiff.iff_comp_isImmersion hτ.1.isImmersion).mpr ⟨hc, hcomp ▸ h.contMDiff⟩⟩, hg⟩

/-- **The image of a closed embedding of analytic manifolds is a closed submanifold**, for a
finite-dimensional model `E` of `M`, in the coordinates `ψ : E ≃ 𝕜ⁿ` of any basis, of codimension
the dimension `s` of the complement of the immersion. At `τ x`, in the charts `c` of `N` and `d` of
`M` in which `τ` reads `u ↦ ε(u, 0)` (`ε : E' × F ≃ E`), the chart `d` read through the linear
automorphism `ψ⁻¹ ∘ A ∘ ε⁻¹` of `E`, with `A : E' × F ≃ 𝕜ⁿ` sending `F` onto the last `s`
coordinates, and restricted to the open set where `ε⁻¹ ∘ d` has its first component in the target
of `c` and over which the image of the source of `c` is the trace of `τ(N)` (`τ` being a
topological embedding), is adapted to `τ(N)`. -/
theorem IsClosedAnalyticEmbedding.exists_isClosedSubmanifold [FiniteDimensional 𝕜 E] :
    ∃ (n s : ℕ) (ψ : E ≃L[𝕜] (Fin n → 𝕜)), IsClosedSubmanifold ψ (Set.range τ) s := by
  set n := Module.finrank 𝕜 E with hn
  let ψ : E ≃L[𝕜] (Fin n → 𝕜) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  rcases isEmpty_or_nonempty N with hN | ⟨⟨x₀⟩⟩
  · refine ⟨n, 0, ψ, ⟨?_, fun a ha => ?_⟩⟩
    · rw [Set.range_eq_empty]
      exact isClosed_empty
    · obtain ⟨x, -⟩ := ha
      exact isEmptyElim x
  have hI := hτ.1.isImmersion
  set F := hI.complement
  have hF : IsImmersionOfComplement F 𝓘(𝕜, E') 𝓘(𝕜, E) ω τ := hI.isImmersionOfComplement_complement
  -- the dimensions
  have hfin : FiniteDimensional 𝕜 (E' × F) := (hF x₀).equiv.symm.toLinearEquiv.finiteDimensional
  have hfinE' : FiniteDimensional 𝕜 E' :=
    Module.Finite.of_surjective (LinearMap.fst 𝕜 E' F) LinearMap.fst_surjective
  have hfinF : FiniteDimensional 𝕜 F :=
    Module.Finite.of_surjective (LinearMap.snd 𝕜 E' F) LinearMap.snd_surjective
  set s := Module.finrank 𝕜 F with hs
  have hdim : Module.finrank 𝕜 E' + s = n := by
    rw [hn, ← (hF x₀).equiv.toLinearEquiv.finrank_eq, Module.finrank_prod]
  have hsn : s ≤ n := hdim ▸ Nat.le_add_left s _
  let σ : Fin s ↪ Fin n := Fin.castLEEmb hsn
  let Q := LinearEquiv.ofBijective _ (splitCoordₗ_bijective (𝕜 := 𝕜) σ)
  let bE' : E' ≃L[𝕜] (Fin (n - s) → 𝕜) := ContinuousLinearEquiv.ofFinrankEq (by simp; omega)
  let bF : F ≃L[𝕜] (Fin s → 𝕜) := ContinuousLinearEquiv.ofFinrankEq (by simp [s])
  let A : (E' × F) ≃L[𝕜] (Fin n → 𝕜) := (bE'.prodCongr bF).trans Q.symm.toContinuousLinearEquiv
  have hA : ∀ z i, A z (σ i) = bF z.2 i := fun z i => by
    have := congrArg (fun w => w.2 i) (Q.apply_symm_apply (bE' z.1, bF z.2))
    exact this
  refine ⟨n, s, ψ, hτ.2, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx := hF x
  set c := hx.domChart
  set d := hx.codChart
  set eq := hx.equiv
  have hw : ∀ u ∈ c.target, d (τ (c.symm u)) = eq (u, 0) := fun u hu => by
    have hu' : u ∈ (c.extend 𝓘(𝕜, E')).target := by simpa using hu
    simpa using hx.writtenInCharts hu'
  have hcx : x ∈ c.source := hx.mem_domChart_source
  have hdx : τ x ∈ d.source := hx.mem_codChart_source
  have hsub : c.source ⊆ τ ⁻¹' d.source := hx.source_subset_preimage_source
  have hdA : d ∈ maximalAtlas 𝓘(𝕜, E) ω M := hx.codChart_mem_maximalAtlas
  have hwp : ∀ p ∈ c.source, eq.symm (d (τ p)) = (c p, 0) := fun p hp => by
    rw [ContinuousLinearEquiv.symm_apply_eq, ← hw _ (c.map_source hp), c.left_inv hp]
  -- an open `W` of `M` whose trace on `τ(N)` is the image of the source of `c`
  obtain ⟨W, hWo, hW⟩ := hτ.1.isEmbedding.isInducing.isOpen_iff.mp c.open_source
  let g : M → E' := fun y => (eq.symm (d y)).1
  have hg : ContinuousOn g d.source :=
    (continuous_fst.comp eq.symm.continuous).comp_continuousOn d.continuousOn
  set V := W ∩ (d.source ∩ g ⁻¹' c.target) with hV
  have hVo : IsOpen V := hWo.inter (hg.isOpen_inter_preimage d.open_source c.open_target)
  let B : E ≃L[𝕜] E := eq.symm.trans (A.trans ψ.symm)
  let φ0 : OpenPartialHomeomorph M E := d.trans B.toHomeomorph.toOpenPartialHomeomorph
  have hφ0 : φ0 ∈ maximalAtlas 𝓘(𝕜, E) ω M := by
    refine mem_maximalAtlas_of_contMDiffOn φ0 ?_ ?_
    · exact (B.contDiff.contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas hdA)).mono
        fun y hy => by simpa [φ0] using hy
    · exact ((contMDiffOn_symm_of_mem_maximalAtlas hdA).comp
        B.symm.contDiff.contMDiff.contMDiffOn fun _ hy => hy).mono
        fun y hy => by simpa [φ0] using hy
  refine ⟨φ0.restr V, σ, ?_, restr_mem_maximalAtlas _ hφ0 hVo, fun y hy => ?_⟩
  · rw [OpenPartialHomeomorph.restr_source, hVo.interior_eq]
    refine ⟨by simpa [φ0] using hdx, ?_, hdx, ?_⟩
    · have : x ∈ τ ⁻¹' W := hW ▸ hcx
      exact this
    · change (eq.symm (d (τ x))).1 ∈ c.target
      rw [hwp x hcx]
      exact c.map_source hcx
  rw [OpenPartialHomeomorph.restr_source, hVo.interior_eq] at hy
  obtain ⟨-, hyW, hyd, hyg⟩ := hy
  have key : (∀ i, ψ ((φ0.restr V) y) (σ i) = 0) ↔ (eq.symm (d y)).2 = 0 := by
    have h1 : ∀ i, ψ ((φ0.restr V) y) (σ i) = bF (eq.symm (d y)).2 i := fun i => by
      change ψ (ψ.symm (A (eq.symm (d y)))) (σ i) = _
      rw [ψ.apply_symm_apply, hA]
    simp only [h1]
    constructor
    · intro h
      exact bF.injective ((funext h).trans bF.map_zero.symm)
    · intro h i
      rw [h, map_zero]
      rfl
  rw [key]
  constructor
  · rintro ⟨p, rfl⟩
    have hp : p ∈ c.source := hW ▸ hyW
    rw [hwp p hp]
  · intro h0
    have hu : g y ∈ c.target := hyg
    have h1 : eq.symm (d y) = (g y, 0) := Prod.ext rfl h0
    have h2 : d y = d (τ (c.symm (g y))) := by rw [hw _ hu, ← h1, eq.apply_symm_apply]
    exact ⟨c.symm (g y), (d.injOn hyd (hsub (c.map_target hu)) h2).symm⟩

end Factorization

/-! ### The identification of `N` with the bundled submanifold `τ(N)` -/

section Diffeomorph

variable {n s : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯}
  (hτ : IsClosedAnalyticEmbedding τ) (hS : IsClosedSubmanifold ψ (Set.range τ) s)

/-- The range of the inclusion of the bundled submanifold `τ(N)` lies in the range of `τ`. -/
theorem range_inclusionMap_subset_range : Set.range hS.inclusionMap ⊆ Set.range τ := by
  rintro _ ⟨p, rfl⟩
  exact p.2

/-- An injective analytic map `τ` with an analytic section `h' : τ(N) → N` over the inclusion of the
bundled closed submanifold `τ(N)` is an analytic isomorphism of `N` with `τ(N)`: the corestriction
of `τ`, analytic into the bundled submanifold (`IsClosedSubmanifold.contMDiff_codRestrict`), with
inverse `h'`. -/
def diffeomorphOfSection (hinj : Function.Injective τ)
    (h' : C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), hS.toAnalyticManifold; 𝓘(𝕜, E'), N⟯)
    (hh' : ∀ p, τ (h' p) = (p : Set.range τ).1) :
    Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, Fin (n - s) → 𝕜) N hS.toAnalyticManifold ω where
  toFun x := ⟨τ x, x, rfl⟩
  invFun := h'
  left_inv x := hinj (hh' ⟨τ x, x, rfl⟩)
  right_inv p := Subtype.ext (hh' p)
  contMDiff_toFun := hS.contMDiff_codRestrict τ.contMDiff fun x => ⟨x, rfl⟩
  contMDiff_invFun := h'.contMDiff

/-- The factorization of the inclusion of the bundled submanifold `τ(N)` through `τ`, an analytic
map `τ(N) → N` (`IsClosedAnalyticEmbedding.exists_comp_eq`). -/
def IsClosedAnalyticEmbedding.ofSub :
    C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), hS.toAnalyticManifold; 𝓘(𝕜, E'), N⟯ :=
  (hτ.exists_comp_eq hS.inclusionMap (range_inclusionMap_subset_range hS)).choose

/-- `τ` after the factorization is the inclusion of the submanifold. -/
theorem IsClosedAnalyticEmbedding.apply_ofSub (p : hS.toAnalyticManifold) :
    τ (hτ.ofSub hS p) = (p : Set.range τ).1 :=
  (hτ.exists_comp_eq hS.inclusionMap (range_inclusionMap_subset_range hS)).choose_spec p

/-- **The closed embedding `τ` as an analytic isomorphism of `N` with the bundled closed
submanifold `τ(N)`** (`diffeomorphOfSection`), with inverse the factorization of the inclusion
through `τ` (`IsClosedAnalyticEmbedding.ofSub`). -/
def IsClosedAnalyticEmbedding.toDiffeomorph :
    Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, Fin (n - s) → 𝕜) N hS.toAnalyticManifold ω :=
  diffeomorphOfSection hS hτ.isClosedEmbedding.injective (hτ.ofSub hS) (hτ.apply_ofSub hS)

/-- The isomorphism is `τ` on points. -/
theorem IsClosedAnalyticEmbedding.coe_toDiffeomorph_apply (x : N) :
    (hτ.toDiffeomorph hS x : Set.range τ).1 = τ x :=
  rfl

/-- **An analytic map identified with the inclusion of a closed submanifold of its image is an
immersion**: if an analytic isomorphism `e : N ≃ τ(N)` onto the bundled closed submanifold `τ(N)`
of codimension `s` is `τ` on points, then `τ` is an analytic immersion with complement `𝕜^s`. At
`x`, with the adapted chart `φ` (indices `σ`) of the chosen chart of `τ(N)` at `e x` and the
differential `L : 𝕜^{n-s} ≃ E'` of `e⁻¹` at `e x`, `τ` reads `u ↦ ψ⁻¹(embedCompl σ (L⁻¹ u))` in the
chart `L ∘ chartAt ∘ e` of `N` and the chart `φ` of `M`, a linear map `u ↦ (u, 0)` up to the
splitting `splitEquiv ψ σ` of the coordinates. -/
theorem isImmersionOfComplement_of_diffeomorph
    (e : Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, Fin (n - s) → 𝕜) N hS.toAnalyticManifold ω)
    (he : ∀ x, (e x : Set.range τ).1 = τ x) :
    IsImmersionOfComplement (Fin s → 𝕜) 𝓘(𝕜, E') 𝓘(𝕜, E) ω τ := by
  intro x
  set p : hS.toAnalyticManifold := e x with hp
  set φ := hS.adaptedChartAt p with hφdef
  set σ := hS.adaptedIdx p with hσdef
  have hφ : IsAdaptedChart ψ (Set.range τ) φ σ := hS.isAdaptedChart_adaptedChartAt p
  have hc : chartAt (Fin (n - s) → 𝕜) p = hφ.chartOn p.2 := rfl
  let L : (Fin (n - s) → 𝕜) ≃L[𝕜] E' := (e.mfderivToContinuousLinearEquiv (by simp) x).symm
  -- the chart of `N` at `x`: the chart of `τ(N)` at `e x` after `e`, read in `E'` through `L`
  let c : OpenPartialHomeomorph N E' :=
    (e.toHomeomorph.toOpenPartialHomeomorph.trans (chartAt (Fin (n - s) → 𝕜) p)).trans
      L.toHomeomorph.toOpenPartialHomeomorph
  have hτe : ∀ y, τ (e.symm y) = (y : Set.range τ).1 := fun y => by
    rw [← he, e.apply_symm_apply]
  refine IsImmersionAtOfComplement.mk_of_continuousAt τ.contMDiff.continuous.continuousAt
    ((L.symm.prodCongr (ContinuousLinearEquiv.refl 𝕜 (Fin s → 𝕜))).trans (splitEquiv ψ σ))
    c φ ?_ ?_ ?_ hφ.1 ?_
  · simp only [c, mfld_simps]
    exact mem_chart_source (Fin (n - s) → 𝕜) p
  · rw [← he x]
    exact hS.mem_source_adaptedChartAt p
  · refine mem_maximalAtlas_of_contMDiffOn c ?_ ?_
    · have h1 : ContMDiffOn 𝓘(𝕜, E') 𝓘(𝕜, Fin (n - s) → 𝕜) ω
          (fun y => chartAt (Fin (n - s) → 𝕜) p (e y))
          (e ⁻¹' (chartAt (Fin (n - s) → 𝕜) p).source) :=
        contMDiffOn_chart.comp e.contMDiff.contMDiffOn fun _ hy => hy
      exact (L.contDiff.contMDiff.comp_contMDiffOn h1).mono fun y hy => by simpa [c] using hy
    · have h1 : ContMDiffOn 𝓘(𝕜, E') 𝓘(𝕜, Fin (n - s) → 𝕜) ω
          (fun u => (chartAt (Fin (n - s) → 𝕜) p).symm (L.symm u))
          (L.symm ⁻¹' (chartAt (Fin (n - s) → 𝕜) p).target) :=
        contMDiffOn_chart_symm.comp L.symm.contDiff.contMDiff.contMDiffOn fun _ hy => hy
      exact (e.symm.contMDiff.comp_contMDiffOn h1).mono fun y hy => by simpa [c] using hy
  · intro u hu
    simp only [mfld_simps] at hu ⊢
    have hu' : L.symm u ∈ (chartAt (Fin (n - s) → 𝕜) p).target := by
      simp only [c, mfld_simps] at hu
      exact hu
    rw [hc, hφ.chartOn_target] at hu'
    have hw : ψ.symm (embedCompl σ (L.symm u)) ∈ φ.target := hu'
    calc φ (τ (c.symm u)) = φ (τ (e.symm ((chartAt (Fin (n - s) → 𝕜) p).symm (L.symm u)))) := rfl
      _ = φ (((chartAt (Fin (n - s) → 𝕜) p).symm (L.symm u) : Set.range τ).1) := by rw [hτe]
      _ = φ (φ.symm (ψ.symm (embedCompl σ (L.symm u)))) := by
        rw [hc]
        exact congrArg φ (hφ.coe_symmAux p.2 hw)
      _ = ψ.symm (embedCompl σ (L.symm u)) := φ.right_inv hw
      _ = _ := by simp [splitEquiv_apply_zero]

/-- **A closed embedding of the spaces whose image is a closed submanifold, through which the
inclusion of the submanifold factors analytically, is a closed embedding of analytic manifolds**:
the factorization identifies `N` with the bundled submanifold (`diffeomorphOfSection`), so `τ` is
an immersion (`isImmersionOfComplement_of_diffeomorph`). -/
theorem IsClosedAnalyticEmbedding.of_isClosedSubmanifold (hτc : Topology.IsClosedEmbedding τ)
    (h' : C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), hS.toAnalyticManifold; 𝓘(𝕜, E'), N⟯)
    (hh' : ∀ p, τ (h' p) = (p : Set.range τ).1) : IsClosedAnalyticEmbedding τ :=
  ⟨⟨(isImmersionOfComplement_of_diffeomorph hS (diffeomorphOfSection hS hτc.injective h' hh')
    fun _ => rfl).isImmersion, hτc.isEmbedding⟩, hτc.isClosed_range⟩

end Diffeomorph

/-! ### The push-forward of ideal sheaves through a closed submanifold -/

section Pushforward

variable {I : IdealSheaf M} {J : IdealSheaf N} {τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯}

/-- Along a push-forward of ideal sheaves, `τ` is a closed embedding of analytic manifolds. -/
theorem IdealSheaf.IsPushforwardAlong.isClosedAnalyticEmbedding (h : I.IsPushforwardAlong J τ) :
    IsClosedAnalyticEmbedding τ :=
  ⟨h.isSmoothEmbedding, h.isClosed_range⟩

/-- The ideal sheaf of the closed submanifold `τ(N)`, in any coordinates, lies in `I` when the ideal
of `τ(N)` does: its stalks are the vanishing ideals
(`IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_vanishingStalk`). -/
theorem IdealSheaf.IsPushforwardAlong.stalkIdeal_idealSheaf_le (h : I.IsPushforwardAlong J τ)
    {n s : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)} (hS : IsClosedSubmanifold ψ (Set.range τ) s) (x : M) :
    hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x := by
  rw [hS.stalkIdeal_idealSheaf_eq_vanishingStalk]
  exact h.vanishingStalk_le x

/-- For a finite-dimensional model `E` of `M`, the image of `τ` is a closed submanifold whose ideal
sheaf lies in `I` (`IsClosedAnalyticEmbedding.exists_isClosedSubmanifold`). -/
theorem IdealSheaf.IsPushforwardAlong.exists_isClosedSubmanifold_stalkIdeal_le
    [FiniteDimensional 𝕜 E] (h : I.IsPushforwardAlong J τ) :
    ∃ (n s : ℕ) (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (hS : IsClosedSubmanifold ψ (Set.range τ) s),
      ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x := by
  obtain ⟨n, s, ψ, hS⟩ := h.isClosedAnalyticEmbedding.exists_isClosedSubmanifold
  exact ⟨n, s, ψ, hS, h.stalkIdeal_idealSheaf_le hS⟩

variable (I J τ) in
/-- **The push-forward of ideal sheaves through the closed submanifold and the universal property
of the embedding**, for a finite-dimensional model `E` of `M`: `I.IsPushforwardAlong J τ` holds
exactly when `τ` is a closed embedding of the spaces through which every analytic map into `M`
with values in `τ(N)` factors analytically, `τ(N)` is a closed submanifold whose ideal sheaf lies in
`I`, and `J = τ^*I`. Given the closed submanifold, the factorization of its inclusion makes `τ` an
immersion (`IsClosedAnalyticEmbedding.of_isClosedSubmanifold`), and the stalks of its ideal sheaf
are the vanishing ideals; conversely a closed embedding of analytic manifolds has the universal
property (`IsClosedAnalyticEmbedding.exists_comp_eq`) and its image is a closed submanifold
(`IsClosedAnalyticEmbedding.exists_isClosedSubmanifold`). -/
theorem IdealSheaf.isPushforwardAlong_iff_exists_comp_eq [FiniteDimensional 𝕜 E] :
    I.IsPushforwardAlong J τ ↔
      (Topology.IsClosedEmbedding τ ∧
        ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (P : AnalyticManifold.{u} 𝕜 F)
          (h : C^ω⟮𝓘(𝕜, F), P; 𝓘(𝕜, E), M⟯), Set.range h ⊆ Set.range τ →
            ∃ h' : C^ω⟮𝓘(𝕜, F), P; 𝓘(𝕜, E'), N⟯, ∀ x, τ (h' x) = h x) ∧
      (∃ (n s : ℕ) (ψ : E ≃L[𝕜] (Fin n → 𝕜))
        (hS : Manifold.IsClosedSubmanifold ψ (Set.range τ) s),
        ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x) ∧
      J = I.pullback τ τ.contMDiff := by
  refine ⟨fun h => ⟨⟨h.isClosedAnalyticEmbedding.isClosedEmbedding,
    fun F _ _ P g hg => h.isClosedAnalyticEmbedding.exists_comp_eq g hg⟩,
    h.exists_isClosedSubmanifold_stalkIdeal_le, h.pullback_eq⟩, fun ⟨⟨hc, hfac⟩, hS, hJ⟩ => ?_⟩
  obtain ⟨n, s, ψ, hS, hle⟩ := hS
  obtain ⟨h', hh'⟩ := hfac _ hS.toAnalyticManifold hS.inclusionMap
    (range_inclusionMap_subset_range hS)
  have hτ : IsClosedAnalyticEmbedding τ := .of_isClosedSubmanifold hS hc h' hh'
  refine ⟨hτ.1, hτ.2, fun x => ?_, hJ⟩
  rw [← hS.stalkIdeal_idealSheaf_eq_vanishingStalk]
  exact hle x

end Pushforward

/-! ### The dimensions of isomorphic manifolds -/

/-- Two analytically isomorphic manifolds modelled on `𝕜^m` and `𝕜^k`, one of them nonempty, have
`m = k`: the differential of the isomorphism at a point is a linear isomorphism of the models. -/
theorem dim_eq_of_diffeomorph {m k : ℕ} {X : AnalyticManifold.{u} 𝕜 (Fin m → 𝕜)}
    {Y : AnalyticManifold.{u} 𝕜 (Fin k → 𝕜)}
    (e : Diffeomorph 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin k → 𝕜) X Y ω) (x : X) : m = k := by
  have h := (e.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.finrank_eq
  have h2 : Module.finrank 𝕜 (Fin m → 𝕜) = Module.finrank 𝕜 (Fin k → 𝕜) := h
  rwa [Module.finrank_fin_fun, Module.finrank_fin_fun] at h2

/-! ### The restriction of `τ` between opens -/

/-- The restriction `U' → U` of an analytic map `τ : N → M` to opens with `τ(U') ⊆ U`. -/
def restrictBetween (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯) (U' : Opens N) (U : Opens M)
    (h : ⇑τ '' (U' : Set N) ⊆ U) :
    C^ω⟮𝓘(𝕜, E'), N.restrict U'; 𝓘(𝕜, E), M.restrict U⟯ :=
  ⟨fun p => ⟨τ p.1, h ⟨p.1, p.2, rfl⟩⟩, contMDiff_codRestrict_opens τ.contMDiff fun _ => rfl⟩

/-- The restriction is `τ` on points. -/
theorem coe_restrictBetween_apply (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯) {U' : Opens N} {U : Opens M}
    (h : ⇑τ '' (U' : Set N) ⊆ U) (p : N.restrict U') :
    (restrictBetween τ U' U h p).1 = τ p.1 :=
  rfl

/-! ### The re-modelling of `τ` -/

section Transport

variable {E₁ E₁' : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [NormedAddCommGroup E₁']
  [NormedSpace 𝕜 E₁'] (ψ : E ≃L[𝕜] E₁) (ψ' : E' ≃L[𝕜] E₁') (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯)

/-- **An analytic map `τ : N → M` read between the re-modelled manifolds** `N.transport ψ'` and
`M.transport ψ`, for two model changes: the same map on points (the two-model form of
`AnalyticMap.transport`). -/
def transportBetween :
    C^ω⟮𝓘(𝕜, E₁'), N.transport ψ'; 𝓘(𝕜, E₁), M.transport ψ⟯ :=
  ⟨fun x => M.toTransport ψ (τ (N.ofTransport ψ' x)),
    (M.contMDiff_toTransport ψ).comp (τ.contMDiff.comp (N.contMDiff_ofTransport ψ'))⟩

/-- The re-modelled map is the map on points. -/
theorem transportBetween_apply (x : N) :
    transportBetween ψ ψ' τ (N.toTransport ψ' x) = M.toTransport ψ (τ x) :=
  rfl

/-- The range of the re-modelled map is the preimage of the range of `τ` under the identity
`M.transport ψ → M`. -/
theorem range_transportBetween :
    Set.range (transportBetween ψ ψ' τ) = ⇑(M.transportDiffeomorph ψ).symm ⁻¹' Set.range τ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨N.ofTransport ψ' y, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨N.toTransport ψ' y, hy⟩

variable {τ}

variable {n₀ s : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n₀ → 𝕜)}

/-- The range of the re-modelled map is a closed submanifold of the re-modelled `M` of the same
codimension, for the chart read through `ψ` (`IsClosedSubmanifold.preimage_of_square` along the
identity `M.transport ψ → M`). -/
theorem IsClosedSubmanifold.range_transportBetween (hS : IsClosedSubmanifold ψ₀ (Set.range τ) s) :
    IsClosedSubmanifold (ψ.symm.trans ψ₀) (Set.range (AnalyticManifold.transportBetween ψ ψ' τ))
      s := by
  rw [AnalyticManifold.range_transportBetween]
  exact hS.preimage_of_square (M.transportDiffeomorph ψ).symm ψ

/-- The re-modelled map of a closed embedding of analytic manifolds whose image is a closed
submanifold is a closed embedding: the same map of the same spaces, whose image is the closed
submanifold `IsClosedSubmanifold.range_transportBetween`, through which the inclusion of that
submanifold factors (through `τ`, after the identity `M.transport ψ → M`;
`IsClosedAnalyticEmbedding.of_isClosedSubmanifold`). -/
theorem IsClosedAnalyticEmbedding.transportBetween (hτ : IsClosedAnalyticEmbedding τ)
    (hS : IsClosedSubmanifold ψ₀ (Set.range τ) s) :
    IsClosedAnalyticEmbedding (AnalyticManifold.transportBetween ψ ψ' τ) := by
  have hST := AnalyticManifold.IsClosedSubmanifold.range_transportBetween ψ ψ' hS
  obtain ⟨h', hh'⟩ := hτ.exists_comp_eq
    ⟨fun x => M.ofTransport ψ (hST.inclusionMap x),
      (M.contMDiff_ofTransport ψ).comp hST.inclusionMap.contMDiff⟩ (by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := (x : Set.range (AnalyticManifold.transportBetween ψ ψ' τ)).2
      exact ⟨N.ofTransport ψ' y, congrArg (M.ofTransport ψ) hy⟩)
  exact .of_isClosedSubmanifold hST hτ.isClosedEmbedding
    ⟨fun x => N.toTransport ψ' (h' x), (N.contMDiff_toTransport ψ').comp h'.contMDiff⟩
    fun x => congrArg (M.toTransport ψ) (hh' x)

/-- The containment of the ideal sheaf of `τ(N)` in an ideal sheaf `I`, stalk by stalk, carries to
the re-modelled manifold (`IsClosedSubmanifold.idealSheaf_pullbackDiffeomorph`). -/
theorem stalkIdeal_idealSheaf_range_transportBetween_le {n₁ : ℕ} {ψ₁ : E₁ ≃L[𝕜] (Fin n₁ → 𝕜)}
    (hS : IsClosedSubmanifold ψ₀ (Set.range τ) s)
    (hS₁ : IsClosedSubmanifold ψ₁ (Set.range (AnalyticManifold.transportBetween ψ ψ' τ)) s)
    (I : IdealSheaf M) (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x)
    (x : M.transport ψ) :
    hS₁.idealSheaf.stalkIdeal x ≤ (I.transport ψ).stalkIdeal x := by
  have h1 := hS.idealSheaf_pullbackDiffeomorph (M.transportDiffeomorph ψ).symm ψ ψ₀ hS₁
    (range_transportBetween ψ ψ' τ)
  rw [← h1]
  have h2 : AnalyticManifold.IdealSheaf.pullbackDiffeomorph (M.transportDiffeomorph ψ).symm
      hS.idealSheaf ≤ I.pullbackDiffeomorph (M.transportDiffeomorph ψ).symm :=
    Manifold.IdealSheaf.pullback_le_pullback _ _ (Manifold.IdealSheaf.le_def.mpr hle)
  exact h2 x

/-- The re-modelled pull-back of an ideal sheaf along `τ` is the pull-back of the re-modelled ideal
sheaf along the re-modelled map (both are the pull-back along the same map on points). -/
theorem IdealSheaf.transport_pullback_transportBetween (I : IdealSheaf M) :
    IdealSheaf.transport ψ' (I.pullback τ τ.contMDiff) =
      (I.transport ψ).pullback (AnalyticManifold.transportBetween ψ ψ' τ)
        (AnalyticManifold.transportBetween ψ ψ' τ).contMDiff := by
  change Manifold.IdealSheaf.pullback _ _ (Manifold.IdealSheaf.pullback _ _ I) =
    Manifold.IdealSheaf.pullback _ _ (Manifold.IdealSheaf.pullback _ _ I)
  rw [Manifold.IdealSheaf.pullback_pullback, Manifold.IdealSheaf.pullback_pullback]
  exact Manifold.IdealSheaf.pullback_congr _ _ _ (funext fun _ => rfl)

end Transport

end AnalyticManifold

end

end
