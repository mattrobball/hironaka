/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictTransformSeq
public import Hironaka.Manifold.Chart.Transport
public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Bundled
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.GoingUp.Naturality
import Hironaka.Resolution.Analytic.GoingUp.NormalCrossingsTransport
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Base transport of a blow-up sequence along a diffeomorphism

A smooth blow-up sequence `B` of `M` and a diffeomorphism `g : M' ≃ M` give a smooth blow-up
sequence of `M'` with the same later stages: the first centre is pulled back along `g` and the
first blow-down is followed by `g⁻¹` (`IsBlowUp.diffeomorph_comp`); everything from stage `1` on
is the data of `B` itself. The marked transforms, the boundaries and the strict transforms of a
subset agree with those of `B` from stage `1` on (the base change of the marked transform along a
diffeomorphism, the naturality of the reduced transform, the preimage of the strict transform), so
the order and normal-crossings clauses of [Kol07, Definition 66] transport, and the centres lie in
the strict transforms of `g⁻¹(H)` iff those of `B` lie in the strict transforms of `H`. The
construction stays at the level of data: no equality or isomorphism of sequences is used.

* `FiniteSuccession.firstCenter`, `firstMap`, `firstCenterSub`, `firstIsBlowUp`: the stage-`0`
  data read on `M` (stage `0` is `finStages M later (castSucc 0)`, definitionally `M`).
* `FiniteSuccession.transportBase g B`: the transported sequence.
* `markedTransformSeqAux_transportBase`, `boundarySeqAux_transportBase`,
  `strictTransformSeqAux_transportBase`: the identities from stage `1` on.
* `IdealSheaf.ordAlongIdeal_pullback_diffeomorph`: the order along a centre transports.
* `isOfOrderGe_transportBase`, `isOfOrder_transportBase`, `centersIn_transportBase_iff`.
* `AnalyticManifold.restrictTopDiffeomorph`: `M.restrict ⊤ ≃ M`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M' M : AnalyticManifold.{u} 𝕜 E} (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' M ω)

/-- The order of `J` along the centre `D` transports along a diffeomorphism: the stalk ideals are
carried by the bijective germ map, which preserves inclusions and powers. -/
theorem IdealSheaf.ordAlongIdeal_pullback_diffeomorph (D J : AnalyticManifold.IdealSheaf M)
    (a : M') :
    IdealSheaf.ordAlongIdeal (D.pullback ⇑g g.contMDiff) (J.pullback ⇑g g.contMDiff) a =
      IdealSheaf.ordAlongIdeal D J (g a) := by
  have hbij : Function.Bijective (germMap ⇑g g.contMDiff a) :=
    germMap_bijective_of_isLocalDiffeomorphAt ⇑g g.contMDiff (g.isLocalDiffeomorph a)
  have hiff : ∀ (A C : Ideal ((structureSheaf 𝕜 E M).presheaf.stalk (g a))),
      Ideal.map (germMap ⇑g g.contMDiff a) A ≤ Ideal.map (germMap ⇑g g.contMDiff a) C ↔ A ≤ C :=
    fun A C => by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _ hbij]
  simp only [IdealSheaf.ordAlongIdeal, IdealSheaf.stalkIdeal_pullback]
  refine iSup_congr fun p => ?_
  rw [← Ideal.map_pow]
  exact iSup_congr_Prop (hiff _ _) fun _ => rfl

/-- Pulling back along `g` and then along `g⁻¹` is the identity. -/
theorem IdealSheaf.pullback_pullback_symm (J : AnalyticManifold.IdealSheaf M) :
    (J.pullback ⇑g g.contMDiff).pullback ⇑g.symm g.symm.contMDiff = J :=
  (IdealSheaf.pullback_pullback J _ _ _ _).trans
    ((IdealSheaf.pullback_congr J _ contMDiff_id (funext fun x => g.apply_symm_apply x)).trans
      (IdealSheaf.pullback_id_eq_self J))

/-- The open subset `⊤ ⊆ M` as a manifold is `M`: the inclusion is an analytic isomorphism. -/
def _root_.AnalyticManifold.restrictTopDiffeomorph
    (M : AnalyticManifold.{u} 𝕜 E) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (M.restrict ⊤) M ω where
  toFun := Subtype.val
  invFun := fun x => ⟨x, trivial⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := fun x =>
    (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (fun x : M => (⟨x, trivial⟩ : (⊤ : Opens M))) Set.univ x).mp (contMDiff_id x)

theorem _root_.AnalyticManifold.coe_restrictTopDiffeomorph
    (M : AnalyticManifold.{u} 𝕜 E) : ⇑M.restrictTopDiffeomorph = ⇑(M.inclusion ⊤) := rfl

end Manifold

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M' M : AnalyticManifold.{u} 𝕜 E} (B : FiniteSuccession M)

/-! ### The stage-`0` data, read on `M` -/

/-- The first centre `C_0` as an ideal sheaf on `M` (the structure types it on
`finStages M later (castSucc 0)`, which is `M` definitionally but not syntactically). -/
def firstCenter (h : 0 < B.length) : IdealSheaf M := B.center ⟨0, h⟩

/-- The first blow-down `σ_1 : U_1 → M`. -/
def firstMap (h : 0 < B.length) : AnalyticMap (B.later ⟨0, h⟩) M := B.map ⟨0, h⟩

/-- `Z_0 ⊆ M` is a closed submanifold. -/
theorem firstCenterSub (h : 0 < B.length) :
    IsClosedSubmanifold (B.chartAt ⟨0, h⟩) (B.firstCenter h).support (B.codim ⟨0, h⟩) :=
  B.isClosedSubmanifold_center ⟨0, h⟩

/-- `σ_1` is a blowing-up of `M` along `Z_0`. -/
theorem firstIsBlowUp (h : 0 < B.length) :
    IsBlowUp (B.chartAt ⟨0, h⟩) (B.firstCenter h).support (B.codim ⟨0, h⟩) ⇑(B.firstMap h) :=
  B.isBlowUp_map ⟨0, h⟩

theorem idealSheaf_firstCenterSub (h : 0 < B.length) :
    (B.firstCenterSub h).idealSheaf = B.firstCenter h :=
  B.idealSheaf_center ⟨0, h⟩

variable (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' M ω)

/-- The pulled-back first centre is the ideal sheaf of the closed submanifold `g⁻¹(Z_0)`
(`comap_idealSheaf_of_isLocalDiffeomorph`). -/
theorem pullback_firstCenter_eq_idealSheaf (h : 0 < B.length) :
    (B.firstCenter h).pullback ⇑g g.contMDiff =
      ((B.firstCenterSub h).preimage_of_isLocalDiffeomorph g.isLocalDiffeomorph).idealSheaf := by
  have := comap_idealSheaf_of_isLocalDiffeomorph (B.chartAt ⟨0, h⟩)
    (⟨⇑g, g.contMDiff⟩ : AnalyticMap M' M) g.isLocalDiffeomorph (B.firstCenterSub h)
  rw [B.idealSheaf_firstCenterSub h] at this
  exact this

theorem support_pullback_firstCenter (h : 0 < B.length) :
    IdealSheaf.support ((B.firstCenter h).pullback ⇑g g.contMDiff) =
      ⇑g ⁻¹' (B.firstCenter h).support :=
  IdealSheaf.support_pullback ⇑g g.contMDiff _

/-! ### The transported sequence -/

/-- The centres of the transported sequence: the first pulled back along `g`, the others `B`'s. -/
def transportBaseCenter : ∀ i : Fin B.length, IdealSheaf (finStages M' B.later i.castSucc)
  | ⟨0, h⟩ => (B.firstCenter h).pullback ⇑g g.contMDiff
  | ⟨k + 1, h⟩ => B.center ⟨k + 1, h⟩

/-- The blow-downs of the transported sequence: the first followed by `g⁻¹`, the others `B`'s. -/
def transportBaseMap :
    ∀ i : Fin B.length, AnalyticMap (finStages M' B.later i.succ) (finStages M' B.later i.castSucc)
  | ⟨0, h⟩ => ⟨⇑g.symm ∘ ⇑(B.firstMap h), g.symm.contMDiff.comp (B.firstMap h).contMDiff⟩
  | ⟨k + 1, h⟩ => B.map ⟨k + 1, h⟩

/-- Each transported blow-down is a monoidal transformation with the transported centre: at stage
`0`, the centre `g⁻¹(Z_0)` is a closed submanifold with the pulled-back ideal sheaf
(`comap_idealSheaf_of_isLocalDiffeomorph`) and `g⁻¹ ∘ σ_1` is a blowing-up along it
(`IsBlowUp.diffeomorph_comp`); from stage `1` on the data are those of `B`. -/
theorem transportBase_isMonoidal :
    ∀ i : Fin B.length,
      (B.transportBaseMap g i).IsMonoidalTransformation (B.transportBaseCenter g i)
  | ⟨0, h⟩ => by
    have hZ' : IsClosedSubmanifold (B.chartAt ⟨0, h⟩)
        (IdealSheaf.support ((B.firstCenter h).pullback ⇑g g.contMDiff))
        (B.codim ⟨0, h⟩) := by
      rw [B.support_pullback_firstCenter g h]
      exact (B.firstCenterSub h).preimage_of_isLocalDiffeomorph g.isLocalDiffeomorph
    refine ⟨B.dimAt ⟨0, h⟩, B.chartAt ⟨0, h⟩, B.codim ⟨0, h⟩, hZ', ?_, ?_⟩
    · have hJ : (B.firstCenter h).pullback ⇑g g.contMDiff = hZ'.idealSheaf :=
        (B.pullback_firstCenter_eq_idealSheaf g h).trans
          (IsClosedSubmanifold.idealSheaf_congr _ hZ' (B.support_pullback_firstCenter g h).symm)
      exact (congrArg (fun J => IsIdealSheafOf (B.chartAt ⟨0, h⟩)
        (IdealSheaf.support ((B.firstCenter h).pullback ⇑g g.contMDiff))
        (B.codim ⟨0, h⟩) J) hJ).mpr hZ'.isIdealSheafOf_idealSheaf
    · have hb : IsBlowUp (B.chartAt ⟨0, h⟩) (⇑g.symm '' (B.firstCenter h).support) (B.codim ⟨0, h⟩)
          (⇑g.symm ∘ ⇑(B.firstMap h)) := (B.firstIsBlowUp h).diffeomorph_comp g.symm
      rw [g.symm_image_eq_preimage, ← B.support_pullback_firstCenter g h] at hb
      exact hb
  | ⟨k + 1, h⟩ => B.isMonoidal ⟨k + 1, h⟩

/-- **The sequence `B` carried to `M'` along the diffeomorphism `g : M' ≃ M`**: the same length
and later stages, the first centre pulled back along `g`, the first blow-down followed by `g⁻¹`.
A blow-up sequence in the sense of [Kol07, Definition 29]; not in the sources, an auxiliary
construction. -/
def transportBase : FiniteSuccession M' where
  length := B.length
  later := B.later
  center := B.transportBaseCenter g
  map := B.transportBaseMap g
  isMonoidal := B.transportBase_isMonoidal g

theorem transportBase_length : (B.transportBase g).length = B.length := rfl

theorem transportBase_firstCenter (h : 0 < (B.transportBase g).length) :
    (B.transportBase g).firstCenter h = (B.firstCenter h).pullback ⇑g g.contMDiff := rfl

theorem transportBase_center_succ (k : ℕ) (h : k + 1 < B.length) :
    (B.transportBase g).center ⟨k + 1, h⟩ = B.center ⟨k + 1, h⟩ := rfl

theorem transportBase_map_succ (k : ℕ) (h : k + 1 < B.length) :
    (B.transportBase g).map ⟨k + 1, h⟩ = B.map ⟨k + 1, h⟩ := rfl

theorem transportBase_firstMap_apply (h : 0 < (B.transportBase g).length) (p : B.later ⟨0, h⟩) :
    (B.transportBase g).firstMap h p = g.symm (B.firstMap h p) := rfl

/-! ### The stage-`≥ 1` identities -/

/-- The strict transforms of `g⁻¹(H)` along the transported sequence are those of `H` along `B`
from stage `1` on. -/
theorem strictTransformSeqAux_transportBase (H : Set M) :
    ∀ (k : ℕ) (h : k + 1 < B.length + 1),
      (B.transportBase g).strictTransformSeqAux (⇑g ⁻¹' H) (k + 1) h =
        B.strictTransformSeqAux H (k + 1) h
  | 0, h => by
    have h0 : 0 < B.length := Nat.lt_of_succ_lt_succ h
    change strictTransformSet (⇑g.symm ∘ ⇑(B.firstMap h0))
      (IdealSheaf.support ((B.firstCenter h0).pullback ⇑g g.contMDiff))
          (⇑g ⁻¹' H) =
      strictTransformSet ⇑(B.firstMap h0) (B.firstCenter h0).support H
    rw [B.support_pullback_firstCenter g h0]
    unfold strictTransformSet
    congr 1
    ext p
    simp only [Set.mem_preimage, Set.mem_sdiff, Function.comp_apply, Diffeomorph.apply_symm_apply]
  | k + 1, h => by
    change strictTransformSet ⇑(B.map ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩)
        (B.center ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩).support
        ((B.transportBase g).strictTransformSeqAux (⇑g ⁻¹' H) (k + 1) (Nat.lt_of_succ_lt h)) =
      strictTransformSet ⇑(B.map ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩)
        (B.center ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩).support
        (B.strictTransformSeqAux H (k + 1) (Nat.lt_of_succ_lt h))
    exact congrArg _ (strictTransformSeqAux_transportBase H k (Nat.lt_of_succ_lt h))

/-- The centres of the transported sequence lie in the strict transforms of `g⁻¹(H)` iff the
centres of `B` lie in those of `H`. -/
theorem centersIn_transportBase_iff (H : Set M) :
    (B.transportBase g).CentersIn (⇑g ⁻¹' H) ↔ B.CentersIn H := by
  have hpre : ∀ h0 : 0 < B.length,
      (IdealSheaf.support ((B.firstCenter h0).pullback ⇑g g.contMDiff) ⊆
          ⇑g ⁻¹' H ↔
        (B.firstCenter h0).support ⊆ H) := fun h0 => by
    rw [B.support_pullback_firstCenter g h0]
    exact Set.preimage_subset_preimage_iff fun x _ => ⟨g.symm x, g.apply_symm_apply x⟩
  have hsucc : ∀ (k : ℕ) (hk : k + 1 < B.length),
      (B.transportBase g).strictTransformSeq (⇑g ⁻¹' H) (Fin.castSucc ⟨k + 1, hk⟩) =
        B.strictTransformSeq H (Fin.castSucc ⟨k + 1, hk⟩) := fun k hk =>
    B.strictTransformSeqAux_transportBase g H k (Nat.lt_succ_of_lt hk)
  constructor
  · intro hc i
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero => exact (hpre hk).mp (hc ⟨0, hk⟩)
    | succ k =>
      have hk' : k + 1 < B.length := hk
      have h0 := hc ⟨k + 1, hk'⟩
      rw [hsucc k hk'] at h0
      exact h0
  · intro hc i
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero => exact (hpre hk).mpr (hc ⟨0, hk⟩)
    | succ k =>
      have hk' : k + 1 < B.length := hk
      have h0 := hc ⟨k + 1, hk'⟩
      change ((B.transportBase g).center ⟨k + 1, hk'⟩).support ⊆
        (B.transportBase g).strictTransformSeq (⇑g ⁻¹' H) (Fin.castSucc ⟨k + 1, hk'⟩)
      rw [hsucc k hk']
      exact h0

/-- The boundaries of the transported sequence started with `g^* E₀` are those of `B` started with
`E₀` from stage `1` on (the naturality of the reduced transform on the square
`σ_1 = g ∘ (g⁻¹ ∘ σ_1)` with the identity of stage `1`). -/
theorem boundarySeqAux_transportBase (E₀ : IdealSheaf M) :
    ∀ (k : ℕ) (h : k + 1 < B.length + 1),
      (B.transportBase g).boundarySeqAux (E₀.pullback ⇑g g.contMDiff) (k + 1) h =
        B.boundarySeqAux E₀ (k + 1) h
  | 0, h => by
    have h0 : 0 < B.length := Nat.lt_of_succ_lt_succ h
    have h0' : 0 < (B.transportBase g).length := h0
    change IdealSheaf.reducedTransform ((B.transportBase g).firstMap
        h0') (E₀.pullback ⇑g g.contMDiff) ((B.firstCenter h0).pullback ⇑g g.contMDiff) =
      IdealSheaf.reducedTransform (B.firstMap h0) E₀ (B.firstCenter h0)
    have hsq : ⇑(B.firstMap h0) ∘ ⇑(Diffeomorph.refl 𝓘(𝕜, E) (B.later ⟨0, h0⟩) ω) =
        ⇑g ∘ ⇑((B.transportBase g).firstMap h0') :=
      funext fun p => show B.firstMap h0 p = g (g.symm (B.firstMap h0 p)) from
        (g.apply_symm_apply _).symm
    have hnat := reducedTransform_pullback_of_comp_eq g ((B.transportBase g).firstMap h0')
      (B.firstMap h0) (Diffeomorph.refl 𝓘(𝕜, E) (B.later ⟨0, h0⟩) ω) hsq (B.firstCenter h0) E₀
    have hrefl : (IdealSheaf.reducedTransform (B.firstMap h0) E₀ (B.firstCenter h0)).pullback
        ⇑(Diffeomorph.refl 𝓘(𝕜, E) (B.later ⟨0, h0⟩) ω)
        (Diffeomorph.refl 𝓘(𝕜, E) (B.later ⟨0, h0⟩) ω).contMDiff =
        IdealSheaf.reducedTransform (B.firstMap h0) E₀ (B.firstCenter h0) :=
      (IdealSheaf.pullback_congr _ _ contMDiff_id (funext fun _ => rfl)).trans
        (IdealSheaf.pullback_id_eq_self _)
    exact hnat.symm.trans hrefl
  | k + 1, h => by
    change IdealSheaf.reducedTransform (B.map ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩)
        ((B.transportBase g).boundarySeqAux (E₀.pullback ⇑g g.contMDiff) (k + 1)
          (Nat.lt_of_succ_lt h))
        (B.center ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩) =
      IdealSheaf.reducedTransform (B.map ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩)
        (B.boundarySeqAux E₀ (k + 1) (Nat.lt_of_succ_lt h))
        (B.center ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩)
    rw [boundarySeqAux_transportBase E₀ k (Nat.lt_of_succ_lt h)]

variable {I E₀ : IdealSheaf M} {m : ℕ}

/-- The marked transforms of `(g^* I, m)` along the transported sequence are those of `(I, m)`
along `B` from stage `1` on, for `B` of order `≥ m` (so that the mark is legitimate at stage `0`):
the base change of the marked transform along a diffeomorphism
(`birationalTransform_image_diffeomorph`), with the congruence of the blow-up witnesses
(`MarkedIdealSheaf.birationalTransform_congr`). -/
theorem markedTransformSeqAux_transportBase (hB : B.IsOfOrderGe I m E₀) :
    ∀ (k : ℕ) (h : k + 1 < B.length + 1),
      (B.transportBase g).markedTransformSeqAux (I.pullback ⇑g g.contMDiff) m (k + 1) h =
        B.markedTransformSeqAux I m (k + 1) h
  | 0, h => by
    have h0 : 0 < B.length := Nat.lt_of_succ_lt_succ h
    have h0' : 0 < (B.transportBase g).length := h0
    have hsupp : ((B.transportBase g).firstCenter h0').support =
        ⇑g.symm '' (B.firstCenter h0).support := by
      change IdealSheaf.support ((B.firstCenter h0).pullback ⇑g g.contMDiff) =
          _
      rw [B.support_pullback_firstCenter g h0, g.symm_image_eq_preimage]
    have hb' : IsBlowUp ((B.transportBase g).chartAt ⟨0, h0'⟩)
        ((B.transportBase g).firstCenter h0').support ((B.transportBase g).codim ⟨0, h0'⟩)
        (⇑g.symm ∘ ⇑(B.firstMap h0)) := (B.transportBase g).firstIsBlowUp h0'
    have hcongr := MarkedIdealSheaf.birationalTransform_congr
      ((B.transportBase g).firstCenterSub h0') ((B.firstCenterSub h0).image_diffeomorph g.symm)
      hsupp hb' ((B.firstIsBlowUp h0).diffeomorph_comp g.symm) ⟨I.pullback ⇑g g.contMDiff, m⟩
    have hk : ∀ a ∈ ⇑g.symm '' (B.firstCenter h0).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        ((B.firstCenterSub h0).image_diffeomorph g.symm).idealSheaf (I.pullback ⇑g g.contMDiff)
        a := by
      rintro a ⟨b, hb, rfl⟩
      rw [IsClosedSubmanifold.idealSheaf_congr _
          ((B.firstCenterSub h0).preimage_of_isLocalDiffeomorph g.isLocalDiffeomorph)
          (g.symm_image_eq_preimage _),
        ← B.pullback_firstCenter_eq_idealSheaf g h0, IdealSheaf.ordAlongIdeal_pullback_diffeomorph,
        g.apply_symm_apply]
      exact (hB ⟨0, h0⟩).2 b hb
    have hbase := birationalTransform_image_diffeomorph g.symm (B.firstCenterSub h0)
      (B.firstIsBlowUp h0) (I.pullback ⇑g g.contMDiff) m hk
    change (MarkedIdealSheaf.birationalTransform ((B.transportBase g).firstCenterSub h0') hb'
        ⟨I.pullback ⇑g g.contMDiff, m⟩).I =
      (MarkedIdealSheaf.birationalTransform (B.firstCenterSub h0) (B.firstIsBlowUp h0) ⟨I, m⟩).I
    rw [hcongr, hbase, IdealSheaf.pullback_pullback_symm]
  | k + 1, h => by
    change (MarkedIdealSheaf.birationalTransform
        ((B.transportBase g).isClosedSubmanifold_center ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩)
        ((B.transportBase g).isBlowUp_map ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩)
        ⟨(B.transportBase g).markedTransformSeqAux (I.pullback ⇑g g.contMDiff) m (k + 1)
          (Nat.lt_of_succ_lt h), m⟩).I =
      (MarkedIdealSheaf.birationalTransform
        (B.isClosedSubmanifold_center ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩)
        (B.isBlowUp_map ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩)
        ⟨B.markedTransformSeqAux I m (k + 1) (Nat.lt_of_succ_lt h), m⟩).I
    exact congrArg (fun J => (MarkedIdealSheaf.birationalTransform
        (B.isClosedSubmanifold_center ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩)
        (B.isBlowUp_map ⟨k + 1, Nat.lt_of_succ_lt_succ h⟩) ⟨J, m⟩).I)
      (markedTransformSeqAux_transportBase hB k (Nat.lt_of_succ_lt h))

/-- A sequence of order `≥ m` for `(I, m)` with the boundary `E₀` transports to one of order `≥ m`
for `(g^* I, m)` with the boundary `g^* E₀`: stage `0` by the transport of clause (3′) along `g`
(`HasOnlyNormalCrossingsWith.pullback_diffeomorph`) and of the order along the centre, the later
stages by the identities of the marked transforms and boundaries. -/
theorem isOfOrderGe_transportBase (hB : B.IsOfOrderGe I m E₀) :
    (B.transportBase g).IsOfOrderGe (I.pullback ⇑g g.contMDiff) m (E₀.pullback ⇑g g.contMDiff) := by
  intro i
  obtain ⟨k, hk⟩ := i
  cases k with
  | zero =>
    have hk' : 0 < B.length := hk
    refine ⟨(hB ⟨0, hk'⟩).1.pullback_diffeomorph g, ?_⟩
    change ∀ a : M',
      a ∈ IdealSheaf.support ((B.firstCenter hk').pullback ⇑g g.contMDiff) →
        (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal ((B.firstCenter hk').pullback ⇑g g.contMDiff)
          (I.pullback ⇑g g.contMDiff) a
    intro a ha
    rw [B.support_pullback_firstCenter g hk'] at ha
    rw [IdealSheaf.ordAlongIdeal_pullback_diffeomorph]
    exact (hB ⟨0, hk'⟩).2 (g a) ha
  | succ k =>
    have hk' : k + 1 < B.length := hk
    have hbd := B.boundarySeqAux_transportBase g E₀ k (Nat.lt_succ_of_lt hk')
    have hmt := B.markedTransformSeqAux_transportBase g hB k (Nat.lt_succ_of_lt hk')
    refine ⟨?_, ?_⟩
    · change IdealSheaf.HasOnlyNormalCrossingsWith
        ((B.transportBase g).boundarySeqAux (E₀.pullback ⇑g g.contMDiff) (k + 1)
          (Nat.lt_succ_of_lt hk')) (B.center ⟨k + 1, hk'⟩)
      rw [hbd]
      exact (hB ⟨k + 1, hk'⟩).1
    · change ∀ a ∈ (B.center ⟨k + 1, hk'⟩).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        (B.center ⟨k + 1, hk'⟩) ((B.transportBase g).markedTransformSeqAux
          (I.pullback ⇑g g.contMDiff) m (k + 1) (Nat.lt_succ_of_lt hk')) a
      rw [hmt]
      exact (hB ⟨k + 1, hk'⟩).2

/-- A sequence of order exactly `m` transports to one of order exactly `m`. The proof passes
through the `≥ m` form and [Kol07, Remark 67] (`ord` being invariant under a diffeomorphism)
rather than transporting the weak transforms directly, which is why the hypothesis
`hmax : ∀ y, I.ord y ≤ m` is carried. -/
theorem isOfOrder_transportBase (hB : B.IsOfOrder I E₀ m)
    (hmax : ∀ y, I.ord y ≤ m) :
    (B.transportBase g).IsOfOrder (I.pullback ⇑g g.contMDiff) (E₀.pullback ⇑g g.contMDiff)
      m :=
  isOfOrder_of_isOfOrderGe_of_ord_le (B.transportBase g)
    (B.isOfOrderGe_transportBase g hB.isOfOrderGe) fun y => by
      rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt ⇑g g.contMDiff I
        (g.isLocalDiffeomorph y)]
      exact hmax (g y)

end AnalyticManifold.FiniteSuccession

end
