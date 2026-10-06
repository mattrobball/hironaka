/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Reduced.StdModel
import Hironaka.Manifold.BlowUp.Restrict
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceReduced
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The model statement over `ℂ`: the saturation of a reduced pull-back is radical

On the model `Kn 𝕜 n` of `Hironaka.Manifold.BlowUp.Transform.Reduced.StdModel`: for an open
`V` and an ideal sheaf `I` on `V` with radical stalks, the pull-back `π_i^* I` along the standard
blow-up chart map `π_i : π_i⁻¹(V) → V` has radical saturation `⋃_k (π_i^* I : x_{σ i}^k)` at
every point. Over `ℂ` this is the Rückert core `mem_iSup_colon_pow_of_pow_mem` of
`Hironaka.Manifold.BlowUp.Transform.StrictSubspaceReduced` (Rückert's Nullstellensatz through
the colon sheaf) applied on the open submanifold `π_i⁻¹(V)`: the pull-back is radical off the
hyperplane `{x_{σ i} = 0}` because `π_i` is a local diffeomorphism there
(`germMap_stdBlowUpMap_bijective`) and `I` is radical. This is the case over `ℂ` of
[BM97, Remark 3.14] on the model.

A general tool is proved along the way: the germ map of a composite is the composite of the germ
maps (`germMap_germMap`).
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped Manifold ContDiff
open AnalyticSpace

universe u

namespace Manifold

section Tools

variable {𝕜 : Type} [RCLike 𝕜] {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {N : Type u} [TopologicalSpace N]
  [ChartedSpace E' N] {P : Type u} [TopologicalSpace P] [ChartedSpace E'' P]

/-- The germ map of a composite is the composite of the germ maps (`germMap`). -/
theorem germMap_germMap {φ : N → M} (hφ : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E) ω φ) {ψ : P → N}
    (hψ : ContMDiff 𝓘(𝕜, E'') 𝓘(𝕜, E') ω ψ) (b : P)
    (s : (structureSheaf 𝕜 E M).presheaf.stalk (φ (ψ b))) :
    germMap ψ hψ b (germMap φ hφ (ψ b) s) = germMap (φ ∘ ψ) (hφ.comp hψ) b s := by
  apply stalkToGerm_injective 𝓘(𝕜, E'') ω P b
  rw [stalkToGerm_germMap, stalkToGerm_germMap, stalkToGerm_germMap]
  simp only [Function.comp_apply]
  induction stalkToGerm 𝓘(𝕜, E) ω M (φ (ψ b)) s using Filter.Germ.inductionOn with
  | h f =>
    rw [Filter.Germ.coe_compTendsto, Filter.Germ.coe_compTendsto, Filter.Germ.coe_compTendsto]
    rfl

/-- The image of a radical ideal under a bijective ring homomorphism is
radical. -/
theorem _root_.Ideal.IsRadical.map_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S}
    (hf : Function.Bijective f) {J : Ideal R} (hJ : J.IsRadical) : (J.map f).IsRadical := by
  have hker : RingHom.ker f ≤ J := by
    rw [(RingHom.injective_iff_ker_eq_bot f).mp hf.injective]
    exact bot_le
  have hJr : J.radical = J := le_antisymm hJ Ideal.le_radical
  change (J.map f).radical ≤ J.map f
  rw [← Ideal.map_radical_of_surjective hf.surjective hker, hJr]

end Tools

variable {𝕜 : Type} [RCLike 𝕜] {n c : ℕ} (σ : Fin c ↪ Fin n) (i : Fin c)

/-! ## The model map restricted over an open `V` -/

variable (𝕜) in
/-- The open `π_i⁻¹(V)` of the model. -/
abbrev stdPreimage (V : Opens (Kn.{u} 𝕜 n)) : Opens (Kn.{u} 𝕜 n) :=
  preimageOpens (stdBlowUpMap 𝕜 σ i) (contMDiff_stdBlowUpMap σ i) V

variable (𝕜) in
/-- The standard blow-up chart map restricted to `π_i⁻¹(V) → V`. -/
def stdBlowUpMapRestrict (V : Opens (Kn.{u} 𝕜 n)) : stdPreimage 𝕜 σ i V → V :=
  fun x => ⟨stdBlowUpMap 𝕜 σ i x.1, (mem_preimageOpens _ _).mp x.2⟩

/-- The restricted map, as a map of the ambient space. -/
@[simp] theorem val_stdBlowUpMapRestrict (V : Opens (Kn.{u} 𝕜 n)) (x : stdPreimage 𝕜 σ i V) :
    (stdBlowUpMapRestrict 𝕜 σ i V x : Kn.{u} 𝕜 n) = stdBlowUpMap 𝕜 σ i x := rfl

/-- The restricted map is analytic. -/
theorem contMDiff_stdBlowUpMapRestrict (V : Opens (Kn.{u} 𝕜 n)) :
    ContMDiff 𝓘(𝕜, Kn.{u} 𝕜 n) 𝓘(𝕜, Kn.{u} 𝕜 n) ω (stdBlowUpMapRestrict 𝕜 σ i V) :=
  contMDiff_codRestrict_opens (contMDiff_stdBlowUpMap σ i) fun _ => rfl

/-- Off the hyperplane `{x_{σ i} = 0}` the germ maps of the restricted model map are bijective
(the square with the two open inclusions and `germMap_stdBlowUpMap_bijective`). -/
theorem germMap_stdBlowUpMapRestrict_bijective (V : Opens (Kn.{u} 𝕜 n))
    {x : stdPreimage 𝕜 σ i V} (hx : (x : Kn.{u} 𝕜 n).down (σ i) ≠ 0) :
    Function.Bijective
      (germMap (stdBlowUpMapRestrict 𝕜 σ i V) (contMDiff_stdBlowUpMapRestrict σ i V) x) := by
  -- `germMap π_V x ∘ germMap val_V (π_V x) = germMap val_W x ∘ germMap π x`
  have hsq : ∀ s : (structureSheaf 𝕜 (Kn.{u} 𝕜 n) (Kn.{u} 𝕜 n)).presheaf.stalk
        (stdBlowUpMap 𝕜 σ i x),
      germMap (stdBlowUpMapRestrict 𝕜 σ i V) (contMDiff_stdBlowUpMapRestrict σ i V) x
        (germMap (Subtype.val : V → Kn.{u} 𝕜 n) contMDiff_subtype_val
          (stdBlowUpMapRestrict 𝕜 σ i V x) s) =
      germMap (Subtype.val : stdPreimage 𝕜 σ i V → Kn.{u} 𝕜 n) contMDiff_subtype_val x
        (germMap (stdBlowUpMap 𝕜 σ i) (contMDiff_stdBlowUpMap σ i) x s) := fun s =>
    (germMap_germMap contMDiff_subtype_val (contMDiff_stdBlowUpMapRestrict σ i V) x s).trans
      (germMap_germMap (contMDiff_stdBlowUpMap σ i) contMDiff_subtype_val x s).symm
  have hcomp : Function.Bijective
      ((germMap (stdBlowUpMapRestrict 𝕜 σ i V) (contMDiff_stdBlowUpMapRestrict σ i V) x) ∘
        (germMap (Subtype.val : V → Kn.{u} 𝕜 n) contMDiff_subtype_val
          (stdBlowUpMapRestrict 𝕜 σ i V x))) := by
    rw [show ((germMap (stdBlowUpMapRestrict 𝕜 σ i V) (contMDiff_stdBlowUpMapRestrict σ i V) x) ∘
        (germMap (Subtype.val : V → Kn.{u} 𝕜 n) contMDiff_subtype_val
          (stdBlowUpMapRestrict 𝕜 σ i V x))) =
        (germMap (Subtype.val : stdPreimage 𝕜 σ i V → Kn.{u} 𝕜 n) contMDiff_subtype_val x) ∘
          (germMap (stdBlowUpMap 𝕜 σ i) (contMDiff_stdBlowUpMap σ i) x) from funext hsq]
    exact (germMap_val_bijective _ x).comp (germMap_stdBlowUpMap_bijective σ i hx)
  exact (Function.Bijective.of_comp_iff _ (germMap_val_bijective V _)).mp hcomp

/-- The exceptional ideal sheaf of the model restricted to `π_i⁻¹(V)`. -/
abbrev stdExceptionalRestrict (V : Opens (Kn.{u} 𝕜 n)) :
    IdealSheaf (structureSheaf 𝕜 (Kn.{u} 𝕜 n) (stdPreimage 𝕜 σ i V)) :=
  (stdExceptional 𝕜 σ i).pullback (Subtype.val : stdPreimage 𝕜 σ i V → Kn.{u} 𝕜 n)
    contMDiff_subtype_val

/-- The cosupport of the restricted exceptional ideal sheaf is the
hyperplane `{x_{σ i} = 0}`. -/
theorem mem_cosupport_stdExceptionalRestrict (V : Opens (Kn.{u} 𝕜 n)) (x : stdPreimage 𝕜 σ i V) :
    x ∈ (stdExceptionalRestrict σ i V).support ↔ (x : Kn.{u} 𝕜 n).down (σ i) = 0 := by
  rw [IdealSheaf.support_pullback, Set.mem_preimage, mem_cosupport_stdExceptional]

/-- The pull-back of a reduced ideal sheaf is radical off the hyperplane (there `π_i` is a local
diffeomorphism). -/
theorem isRadical_stalkIdeal_pullback_stdBlowUpMapRestrict (V : Opens (Kn.{u} 𝕜 n))
    (I : IdealSheaf (structureSheaf 𝕜 (Kn.{u} 𝕜 n) V)) (hI : ∀ x, (I.stalkIdeal x).IsRadical)
    {x : stdPreimage 𝕜 σ i V} (hx : x ∉ (stdExceptionalRestrict σ i V).support) :
    ((I.pullback (stdBlowUpMapRestrict 𝕜 σ i V) (contMDiff_stdBlowUpMapRestrict σ i V)).stalkIdeal
      x).IsRadical := by
  rw [IdealSheaf.stalkIdeal_pullback]
  exact Ideal.IsRadical.map_of_bijective (germMap_stdBlowUpMapRestrict_bijective σ i V
    ((mem_cosupport_stdExceptionalRestrict σ i V x).not.mp hx)) (hI _)

/-! ## The model statement over `ℂ` -/

/-- On the model, the saturation of the pull-back of a reduced ideal sheaf along the standard
blow-up chart map is radical at every point of `π_i⁻¹(V)`. -/
theorem isRadical_iSup_colon_pullback_complex (V : Opens (Kn.{u} ℂ n))
    (I : IdealSheaf (structureSheaf ℂ (Kn.{u} ℂ n) V)) (hI : ∀ x, (I.stalkIdeal x).IsRadical)
    (u : stdPreimage ℂ σ i V) :
    (⨆ k : ℕ, Submodule.colon
      ((I.pullback (stdBlowUpMapRestrict ℂ σ i V) (contMDiff_stdBlowUpMapRestrict σ i V)).stalkIdeal
        u)
      (SetLike.coe ((stdExceptionalRestrict σ i V).stalkIdeal u ^ k))).IsRadical := by
  intro g hg
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hg
  exact mem_iSup_colon_pow_of_pow_mem (knCoord.{u} ℂ n) _ _
    (fun x hx => isRadical_stalkIdeal_pullback_stdBlowUpMapRestrict σ i V I hI hx) hm

end Manifold
