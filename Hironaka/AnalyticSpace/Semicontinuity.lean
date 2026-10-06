/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Dimension
public import Hironaka.Analytic.Rueckert.Reexpansion
public import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Analytic.ConvSeries.Rescale
public import Hironaka.Analytic.Germ.CoordDiv
import Hironaka.AnalyticSpace.ConvDimension
import Hironaka.AnalyticSpace.DimensionLemmas
import Hironaka.AnalyticSpace.Jacobian
import Hironaka.AnalyticSpace.Propagation
import Hironaka.AnalyticSpace.RegularStalk
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Upper semicontinuity of the dimension

[Fre17, II 5.4]: for a pointed complex space `(X, a)` there is a neighbourhood `U` of `a` with
`dim_b X ≤ dim_a X` for all `b ∈ U` — here for analytic `K`-spaces and the dimension
`AnalyticSpace.dimAt` (`Hironaka/AnalyticSpace/Dimension.lean`): `eventually_dimAt_le`,
`dimAt_upperSemicontinuous`.

The proof follows Freitag's, with two replacements named below. Reduce to a local model
`V(f) ⊆ G ⊆ Kⁿ` through the local-model isomorphism of the definition (`eventually_dimAt_le`). At a
point `z` of the model, the stalk is `𝒪_n/(f)_z` through the Taylor isomorphism
(`ringKrullDim_stalk_localModel_eq`); Noether normalization of `(f)_z`
(`exists_noetherNormalization_analytic`) gives base coordinates `e : Fin d ↪ Fin n` and a linear
change `σ = substEquiv L` with `d = dim_z` (Cohen–Seidenberg,
`ringKrullDim_quotient_eq_of_normMap`) and, by module-finiteness, a monic relation
`σ (X_i^D + ∑_k c_k(X ∘ e) X_i^k) ∈ (f)_z` for every coordinate (`exists_monic_relation_of_finite`).
Each relation is a convergent series; it is realized as the section `y ↦ g(y − z)` of a polydisc
(`sectionOfConv`, `convAt_germ_sectionOfConv`), which lies in `(f)` on an open `W ∋ z` (the
spreading lemma `exists_forall_germ_mem_span` of `Hironaka/AnalyticSpace/Propagation.lean`,
`exists_opens_forall_convAt_germ_sectionOfConv_mem`); at a nearby point `z'` its germ is the
translated relation `σ (shape a c')`, `a = (L (z' − z)) i`, with re-expanded coefficients `c'`
(`Hironaka/Analytic/Rueckert/Reexpansion.lean`, `eventually_exists_shape_mem`). So every
coordinate satisfies a relation modulo `(f)_{z'} ⊔ (σ X_{e j})_j` that is monic with constant
coefficients, and the parameter bound (Krull's height theorem, [Fre17, VII 5.6])
`ringKrullDim_quotient_le_of_forall_exists_shape_mem` gives `dim_{z'} ≤ d = dim_z`
(`eventually_ringKrullDim_stalk_localModel_le`).

The two replacements: (i) Freitag translates a Weierstrass polynomial `Q` to the nearby centre and
uses the module-finiteness of `f_a^* : 𝒪_{Y,f(a)} → 𝒪_{X,a}` with Cohen–Seidenberg's
`dim 𝒪_{Y,f(a)} ≥ dim 𝒪_{X,a}`; here the translated monic relations give the bound directly through
the generator count of Krull's height theorem, so no division at moving centres is needed. (ii) The
spreading of `g ∈ (f)_z` to a neighbourhood is the sheaf-theoretic content of Freitag's "a polydisc
which contains `Y`". Every other step is an item of [Fre17, II 5.4] or of the theory of convergent
series (`Conv`, `evalSeries`, `substEquiv`; `Hironaka/Analytic/`). Used by
`Hironaka/AnalyticSpace/RegDensityLemmas.lean`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open Analytic Filter Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

open KLocallyRingedSpace

variable {K : Type} [RCLike K] {n : ℕ}

/-- The open polydisc of radius `ρ` about `q` in `Kⁿ`. -/
def polydiscOpens (q : Kn.{u} K n) (ρ : Radius n) : Opens (Kn.{u} K n) :=
  ⟨{y | y.down - q.down ∈ polydisc K ρ}, (isOpen_polydisc ρ).preimage
    (((ContinuousLinearEquiv.ulift : Kn.{u} K n ≃L[K] (Fin n → K)).continuous).sub
      continuous_const)⟩

/-- The centre lies in its polydisc. -/
theorem mem_polydiscOpens_self (q : Kn.{u} K n) (ρ : Radius n) : q ∈ polydiscOpens q ρ := by
  change q.down - q.down ∈ polydisc K ρ
  rw [sub_self]
  intro k
  simpa using ρ.pos k

/-- The function `y ↦ T(y − q)` of a convergent series `T` of radius `ρ` is analytic on the
polydisc of radius `ρ` about `q` (`analyticOnNhd_evalSeries` of
`Hironaka/Analytic/ConvSeries/Rescale.lean`). -/
theorem contMDiffOn_evalSeries_sub {T : MvPowerSeries (Fin n) K} {ρ : Radius n}
    (hT : ConvNorm ρ T ≠ ⊤) (q : Kn.{u} K n) :
    ContMDiffOn 𝓘(K, Kn.{u} K n) 𝓘(K) ω (fun y : Kn.{u} K n => evalSeries T (y.down - q.down))
      (polydiscOpens q ρ) := by
  rw [contMDiffOn_iff_contDiffOn]
  refine AnalyticOnNhd.contDiffOn ?_ (polydiscOpens q ρ).isOpen.uniqueDiffOn
  have hg : AnalyticOnNhd K (fun y : Kn.{u} K n => y.down - q.down) (polydiscOpens q ρ) :=
    ((ContinuousLinearEquiv.ulift : Kn.{u} K n ≃L[K] (Fin n → K)).toContinuousLinearMap
      |>.analyticOnNhd _).sub analyticOnNhd_const
  exact (analyticOnNhd_evalSeries hT).comp hg fun y hy => hy

/-- The section `y ↦ T(y − q)` of `𝒜_{Kⁿ}` over the polydisc about `q` (the realization of a
convergent series as an analytic function near `q`). -/
def sectionOfConv {T : MvPowerSeries (Fin n) K} {ρ : Radius n}
    (hT : ConvNorm ρ T ≠ ⊤) (q : Kn.{u} K n) :
    (affine K n).toLocallyRingedSpace.presheaf.obj (op (polydiscOpens q ρ)) :=
  sectionOfContMDiffOn _ _ (contMDiffOn_evalSeries_sub hT q)

/-- The values of `sectionOfConv`. -/
theorem extendSection_sectionOfConv {T : MvPowerSeries (Fin n) K} {ρ : Radius n}
    (hT : ConvNorm ρ T ≠ ⊤) (q : Kn.{u} K n) {y : Kn.{u} K n} (hy : y ∈ polydiscOpens q ρ) :
    extendSection K (Kn.{u} K n) (sectionOfConv hT q) y = evalSeries T (y.down - q.down) := by
  rw [extendSection_of_mem K (Kn.{u} K n) _ hy]
  rfl

/-- The Taylor series at `q` (identity chart; the specification `IsTaylorHom` of the Taylor
homomorphism, `Hironaka/Manifold/StructureSheaf.lean`) of the germ of a section `F` is the
convergent series `T` when `F(y) = T(y − q)` for `y` near `q`. -/
theorem convAt_germ_eq_of_eventuallyEq (q : Kn.{u} K n) {U : Opens (Kn.{u} K n)} (hq : q ∈ U)
    (F : (affine K n).toLocallyRingedSpace.presheaf.obj (op U)) (T : Analytic.Conv K n)
    (h : ∀ᶠ y in 𝓝 q.down, extendSection K (Kn.{u} K n) F (ULift.up y) =
      evalSeries (T : MvPowerSeries (Fin n) K) (y - q.down)) :
    taylorAffine K n q ((affine K n).toLocallyRingedSpace.presheaf.germ U q hq F) = T := by
  apply Subtype.ext
  have h1 := (isTaylorHom_taylorHom (Kn.{u} K n) ContinuousLinearEquiv.ulift
    (chartAt (Kn.{u} K n) q) (mem_chart_source _ q) (IsManifold.chart_mem_maximalAtlas q)).2 U hq F
  refine eq_of_evalSeries_sub_eventuallyEq ContinuousLinearEquiv.ulift ((chartAt (Kn.{u} K n) q) q)
    (taylorHom_mem_conv _ _ _ _ _ _) T.2 ?_
  refine h1.symm.trans ?_
  exact h

/-- Points near `q` lie in an open neighbourhood of `q`, read in the coordinates `Fin n → K`. -/
theorem eventually_up_mem (q : Kn.{u} K n) {U : Opens (Kn.{u} K n)} (hq : q ∈ U) :
    ∀ᶠ y in 𝓝 q.down, ULift.up.{u} y ∈ U := by
  have hc : Continuous fun y : Fin n → K => (ULift.up.{u} y : Kn.{u} K n) :=
    (ContinuousLinearEquiv.ulift : Kn.{u} K n ≃L[K] (Fin n → K)).symm.continuous
  exact hc.continuousAt.preimage_mem_nhds (U.isOpen.mem_nhds hq)

/-- The germ at `q` of `sectionOfConv T` is `T` under the Taylor isomorphism. -/
theorem convAt_germ_sectionOfConv (T : Analytic.Conv K n) {ρ : Radius n}
    (hT : ConvNorm ρ (T : MvPowerSeries (Fin n) K) ≠ ⊤) (q : Kn.{u} K n) :
    taylorAffine K n q ((affine K n).toLocallyRingedSpace.presheaf.germ (polydiscOpens q ρ) q
      (mem_polydiscOpens_self q ρ) (sectionOfConv hT q)) = T := by
  refine convAt_germ_eq_of_eventuallyEq q _ _ T ?_
  filter_upwards [eventually_up_mem q (mem_polydiscOpens_self q ρ)] with y hy
  exact extendSection_sectionOfConv hT q hy

/-- Membership in an ideal of the stalk, read through the Taylor isomorphism `taylorAffine`. -/
theorem germ_mem_of_convAt_mem_map {q : Kn.{u} K n} {U : Opens (Kn.{u} K n)} (hq : q ∈ U)
    (F : (affine K n).toLocallyRingedSpace.presheaf.obj (op U))
    {J : Ideal ((affine K n).toLocallyRingedSpace.presheaf.stalk q)}
    (h : taylorAffine K n q ((affine K n).toLocallyRingedSpace.presheaf.germ U q hq F) ∈
      Ideal.map (taylorAffine K n q) J) :
    (affine K n).toLocallyRingedSpace.presheaf.germ U q hq F ∈ J := by
  obtain ⟨x, hx, hx1⟩ := (Ideal.mem_map_iff_of_surjective _ (taylorAffine K n q).surjective).mp h
  rwa [(taylorAffine K n q).injective hx1] at hx

variable (G : Opens (Kn.{u} K n)) {k : ℕ} (f : Fin k → AnalyticFun K n G)

/-- The ideal `(f)_z` of a point of the local model, read in `Conv K n`. -/
def modelIdealAt (z : localModel K n G f) : Ideal (Analytic.Conv K n) :=
  Ideal.map (taylorAffine K n z.1.1) (Ideal.span (Set.range fun j =>
    (affine K n).toLocallyRingedSpace.presheaf.germ G z.1.1 z.1.2 (f j)))

/-- `(f)_z` is proper: the `f_j` vanish at the points of the model (`span_germ_le_maximalIdeal` of
`Hironaka/AnalyticSpace/Jacobian.lean`). -/
theorem modelIdealAt_ne_top (z : localModel K n G f) : modelIdealAt G f z ≠ ⊤ := by
  intro htop
  have h1 : (1 : Analytic.Conv K n) ∈ modelIdealAt G f z := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨x, hx, hx1⟩ :=
    (Ideal.mem_map_iff_of_surjective _ (taylorAffine K n z.1.1).surjective).mp h1
  have hx' : x = 1 := by
    apply (taylorAffine K n z.1.1).injective
    rw [hx1, map_one]
  rw [hx'] at hx
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    ((Ideal.eq_top_iff_one _).mpr (span_germ_le_maximalIdeal z hx))

/-- The underlying point of `Kⁿ` of a point of the local model depends continuously on it. -/
theorem continuous_localModel_pt : Continuous fun z' : localModel K n G f => z'.1.1 :=
  continuous_subtype_val.comp continuous_subtype_val

/-- The displacement `z' − z` in the coordinates of `Kⁿ` tends to `0` as `z' → z` in the model. -/
theorem tendsto_localModel_sub (z : localModel K n G f) :
    Tendsto (fun z' : localModel K n G f => z'.1.1.down - z.1.1.down) (𝓝 z) (𝓝 0) := by
  have hc : Continuous fun z' : localModel K n G f => z'.1.1.down - z.1.1.down :=
    ((ContinuousLinearEquiv.ulift : Kn.{u} K n ≃L[K] (Fin n → K)).continuous.comp
      (continuous_localModel_pt G f)).sub continuous_const
  exact hc.tendsto' z 0 (sub_self _)

/-- Points of the model near `z` lie in an open neighbourhood of `z` in `Kⁿ`. -/
theorem eventually_localModel_pt_mem (z : localModel K n G f) {W : Opens (Kn.{u} K n)}
    (hz : z.1.1 ∈ W) : ∀ᶠ z' in 𝓝 z, z'.1.1 ∈ W :=
  ((continuous_localModel_pt G f).tendsto z).eventually (W.isOpen.mem_nhds hz)

/-- Spreading ([Fre17, II 5.4], "a polydisc which contains `Y`"): an element `g ∈ (f)_z` (read in
`Conv K n`) of radius `ρ` is the germ at `z` of the section `y ↦ g(y − z)` of the polydisc, and by
`exists_forall_germ_mem_span` this section lies in `(f)` at every point of an open `W ∋ z` of the
polydisc — so its germ at every nearby point `z'`, read through the Taylor isomorphism at `z'`,
lies in `(f)_{z'}`. -/
theorem exists_opens_forall_convAt_germ_sectionOfConv_mem (z : localModel K n G f)
    {g : Analytic.Conv K n}
    (hg : g ∈ modelIdealAt G f z) {ρ : Radius n}
    (hρ : ConvNorm ρ (g : MvPowerSeries (Fin n) K) ≠ ⊤) :
    ∃ (W : Opens (Kn.{u} K n)) (_ : z.1.1 ∈ W) (hWP : W ≤ polydiscOpens z.1.1 ρ),
      ∀ z' : localModel K n G f, (hz' : z'.1.1 ∈ W) →
        taylorAffine K n z'.1.1
          ((affine K n).toLocallyRingedSpace.presheaf.germ (polydiscOpens z.1.1 ρ)
          z'.1.1 (hWP hz') (sectionOfConv hρ z.1.1)) ∈ modelIdealAt G f z' := by
  let 𝒜 := (affine K n).toLocallyRingedSpace.presheaf
  have hF := convAt_germ_sectionOfConv g hρ z.1.1
  have hmem : 𝒜.germ (polydiscOpens z.1.1 ρ) z.1.1 (mem_polydiscOpens_self z.1.1 ρ)
      (sectionOfConv hρ z.1.1) ∈ Ideal.span (Set.range fun j => 𝒜.germ G z.1.1 z.1.2 (f j)) :=
    germ_mem_of_convAt_mem_map _ _ (by rw [hF]; exact hg)
  set U : Opens (Kn.{u} K n) := polydiscOpens z.1.1 ρ ⊓ G with hU
  have hqU : z.1.1 ∈ U := ⟨mem_polydiscOpens_self z.1.1 ρ, z.1.2⟩
  have hUP : U ≤ polydiscOpens z.1.1 ρ := inf_le_left
  have hUG : U ≤ G := inf_le_right
  have hmem' : 𝒜.germ U z.1.1 hqU (𝒜.map (homOfLE hUP).op (sectionOfConv hρ z.1.1)) ∈
      Ideal.span (Set.range fun j => 𝒜.germ U z.1.1 hqU (𝒜.map (homOfLE hUG).op (f j))) := by
    simp only [𝒜.germ_res_apply]
    exact hmem
  obtain ⟨W, hqW, hWU, hW⟩ := exists_forall_germ_mem_span 𝒜 hqU _ _ hmem'
  refine ⟨W, hqW, hWU.trans hUP, fun z' hz' => ?_⟩
  have h := hW z'.1.1 hz'
  simp only [𝒜.germ_res_apply] at h
  exact Ideal.mem_map_of_mem _ h

/-- Translation of a monic relation ([Fre17, II 5.4]: the Weierstrass polynomial
`Q(a₁, …, a_{n−1}, z_n − a_n)` general in `ℂ{z₁ − a₁, …}[z_n − a_n]`): a monic relation
`σ (shape 0 c) ∈ (f)_z` for the coordinate `X i` yields, at every point `z'` near `z`, a relation
`σ (shape a c') ∈ (f)_{z'}` of the same shape — the germ at `z'` of the realized section is the
translated series (`exists_substEquiv_shapeSeries_translate`), by the uniqueness of Taylor series
(`convAt_germ_eq_of_eventuallyEq`). -/
theorem eventually_exists_shape_mem (z : localModel K n G f) (L : (Fin n → K) ≃L[K] (Fin n → K))
    {d : ℕ} (e : Fin d ↪ Fin n) (i : Fin n) {D : ℕ} (c : Fin D → Analytic.Conv K d)
    (hc : substEquiv L (shapeSeries K i e 0 c) ∈ modelIdealAt G f z) :
    ∀ᶠ z' in 𝓝 z, ∃ (a : K) (c' : Fin D → Analytic.Conv K d),
      substEquiv L (shapeSeries K i e a c') ∈ modelIdealAt G f z' := by
  obtain ⟨ρ, hρ⟩ := (substEquiv L (shapeSeries K i e 0 c)).2
  obtain ⟨W, hqW, hWP, hW⟩ := exists_opens_forall_convAt_germ_sectionOfConv_mem G f z hc hρ
  have h1 := eventually_localModel_pt_mem G f z hqW
  have h2 := (tendsto_localModel_sub G f z).eventually
    (exists_substEquiv_shapeSeries_translate L i e c)
  filter_upwards [h1, h2] with z' hz'W hz'2
  obtain ⟨c', hc'⟩ := hz'2
  refine ⟨L (z'.1.1.down - z.1.1.down) i, c', ?_⟩
  have hgerm := hW z' hz'W
  have heq : taylorAffine K n z'.1.1 ((affine K n).toLocallyRingedSpace.presheaf.germ
      (polydiscOpens z.1.1 ρ) z'.1.1 (hWP hz'W) (sectionOfConv hρ z.1.1)) =
      substEquiv L (shapeSeries K i e (L (z'.1.1.down - z.1.1.down) i) c') := by
    refine convAt_germ_eq_of_eventuallyEq z'.1.1 (hWP hz'W) _ _ ?_
    have ht : Tendsto (fun y : Fin n → K => y - z'.1.1.down) (𝓝 z'.1.1.down) (𝓝 0) :=
      (continuous_id.sub continuous_const).tendsto' _ _ (sub_self _)
    filter_upwards [eventually_up_mem z'.1.1 (hWP hz'W), ht.eventually hc'] with y hyP hy
    rw [extendSection_sectionOfConv hρ z.1.1 hyP]
    dsimp only at hy ⊢
    rw [← hy]
    congr 1
    abel
  rw [heq] at hgerm
  exact hgerm

/-- [Fre17, II 5.4] on a local model, `dim_{z'} ≤ dim_z` for `z'` near `z`: Noether normalization
at `z` gives `d = dim 𝒪_{z}` (`ringKrullDim_quotient_eq_of_normMap`, Cohen–Seidenberg) and monic
relations for all coordinates (`exists_monic_relation_of_finite`); the relations persist at nearby
points (`eventually_exists_shape_mem`, finitely many coordinates), where the parameter bound
`ringKrullDim_quotient_le_of_forall_exists_shape_mem` (in place of Freitag's use of
Cohen–Seidenberg for `dim 𝒪_{Y,f(a)} ≥ dim 𝒪_{X,a}`; Krull's height theorem, [Fre17, VII 5.6])
gives `dim 𝒪_{z'} ≤ d`. The bridge `ringKrullDim_stalk_localModel_eq` reads both stalks in
`Conv K n`. -/
theorem eventually_ringKrullDim_stalk_localModel_le (z : localModel K n G f) :
    ∀ᶠ z' in 𝓝 z, ringKrullDim ((localModel K n G f).toLocallyRingedSpace.presheaf.stalk z') ≤
      ringKrullDim ((localModel K n G f).toLocallyRingedSpace.presheaf.stalk z) := by
  have hI : modelIdealAt G f z ≠ ⊤ := modelIdealAt_ne_top G f z
  obtain ⟨d, e, L, hinj, hfin⟩ := exists_noetherNormalization_analytic (modelIdealAt G f z) hI
  have hd : ringKrullDim (Analytic.Conv K n ⧸ modelIdealAt G f z) = d :=
    ringKrullDim_quotient_eq_of_normMap K _ hI e L hinj hfin
  choose D c hc using fun i => exists_monic_relation_of_finite (modelIdealAt G f z) e L hfin i
  have h : ∀ᶠ z' in 𝓝 z, ∀ i : Fin n, ∃ (a : K) (c' : Fin (D i) → Analytic.Conv K d),
      substEquiv L (shapeSeries K i e a c') ∈ modelIdealAt G f z' :=
    eventually_all.mpr fun i => eventually_exists_shape_mem G f z L e i (c i) (hc i)
  filter_upwards [h] with z' hz'
  rw [ringKrullDim_stalk_localModel_eq, ringKrullDim_stalk_localModel_eq]
  change ringKrullDim (Analytic.Conv K n ⧸ modelIdealAt G f z') ≤
    ringKrullDim (Analytic.Conv K n ⧸ modelIdealAt G f z)
  rw [hd]
  exact ringKrullDim_quotient_le_of_forall_exists_shape_mem _ L e fun i =>
    let ⟨a, c', h⟩ := hz' i
    ⟨D i, a, c', h⟩

/-- `dimAt X y` at any point of the chart `X|U ≅ (localModel)|W` is the Krull dimension of the stalk
of the local model at the image point (the stalk transports of
`Hironaka/AnalyticSpace/RegularStalk.lean`). -/
theorem dimAt_eq_ringKrullDim_stalk_localModel {X : AnalyticSpace.{u} K} {U : Opens X} {n k : ℕ}
    {G : Opens (Kn.{u} K n)} {f : Fin k → AnalyticFun K n G} {W : Opens (localModel K n G f)}
    (e : KIso (X.toKLocallyRingedSpace.restrictOpen U) ((localModel K n G f).restrictOpen W))
    {y : X} (hy : y ∈ U) :
    AnalyticSpace.dimAt X y = ringKrullDim
      ((localModel K n G f).toLocallyRingedSpace.presheaf.stalk (e.hom.1.base ⟨y, hy⟩).1) := by
  unfold AnalyticSpace.dimAt
  rw [← ringKrullDim_stalk_restrictOpen X.toKLocallyRingedSpace U ⟨y, hy⟩,
    ringKrullDim_stalk_of_kIso e ⟨y, hy⟩, ringKrullDim_stalk_restrictOpen]

/-- [Fre17, II 5.4]: `dim_y X ≤ dim_x X` for `y` near `x` — transport of the local-model statement
along the local-model isomorphism of the definition, which is a homeomorphism of the open `U ∋ x`
onto an open of the model. -/
theorem eventually_dimAt_le (X : AnalyticSpace.{u} K) (x : X) :
    ∀ᶠ y in 𝓝 x, AnalyticSpace.dimAt X y ≤ AnalyticSpace.dimAt X x := by
  obtain ⟨U, hxU, n, k, G, f, W, ⟨e⟩⟩ := X.locallyModel x
  have hφ : Continuous fun y : U => (e.hom.1.base y).1 :=
    continuous_subtype_val.comp (KIso.homeomorph e).continuous
  have h := (hφ.tendsto ⟨x, hxU⟩).eventually
    (eventually_ringKrullDim_stalk_localModel_le G f (e.hom.1.base ⟨x, hxU⟩).1)
  rw [nhds_subtype, Filter.eventually_comap] at h
  filter_upwards [h, U.isOpen.mem_nhds hxU] with y hy hyU
  rw [dimAt_eq_ringKrullDim_stalk_localModel e hyU, dimAt_eq_ringKrullDim_stalk_localModel e hxU]
  exact hy ⟨y, hyU⟩ rfl

/-- **The dimension is upper semicontinuous** [Fre17, II 5.4]: `x ↦ dim_x X`. -/
theorem dimAt_upperSemicontinuous (X : AnalyticSpace.{u} K) :
    UpperSemicontinuous (AnalyticSpace.dimAt X) :=
  fun x _ hb => (eventually_dimAt_le X x).mono fun _ hy => lt_of_le_of_lt hy hb

end AnalyticSpace

end
