/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BDFam
public import Hironaka.Resolution.Analytic.OrderReduction.BDOf
import Hironaka.Manifold.BlowUp.Restrict
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
public import Hironaka.Manifold.FiniteSuccession.Functor.PushforwardPullback
import Hironaka.Resolution.Analytic.OrderReduction.BDBridge
import Hironaka.Resolution.Analytic.OrderReduction.BDCosupp
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Hironaka.Resolution.Algebraic.Tuning.Parameter
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Gluing

/-!
# The core on an open as a core over a transported sequence

The core on a relatively compact open `U` (`BDan.coreFamOn`, `BDFam.lean`) reads the input family
at the trace of `π_{-1}^{-1}(U)` on `S_0`, pushes the value forward to the open `π_{-1}^{-1}(U)`
and pulls it back along the corestricted lift `liftIncl` of the inclusion `U ⊆ M`. This module
identifies it with a core over a sequence (`coreOfListOf`, `BD.lean`) on the restricted data, the
manifold `U`, its centre `Z_{-1} ∩ U`, the transform of `E^j ∩ U` and the input's value transported
to it (`coreFamOn_eq_coreOfListOf`): the push-forward to the open is the push-forward along the
bundle diffeomorphism of the restricted hypersurface (`BlowUpSequence.pushforwardRestrictOf_eq`),
and the push-forward commutes with pull-back along a local analytic isomorphism
(`BlowUpSequence.pushforward_pullback`; the proof of [Kol07, Lemma 102]: pulling back and
restricting commute). Kollár's `S_0` and centre are here those of the restricted data,
propositionally rather than definitionally, so the two clauses of the core over a sequence
(`BDCore.lean`, `BDCosupp.lean`) are first restated over an arbitrary closed hypersurface `Z` and a
closed hypersurface `S'` of its blowing-up equal to `Z_{-1}` and `S_0` (`coreOfListOf_isOfOrderGe`,
`coreOfListOf_cosupp_disjoint`).

The corestricted lift is surjective onto `π_{-1}^{-1}(U)` (`surjective_liftIncl`): the blowing-up
of `Z_{-1}` restricted over `U` is a blowing-up of `U` along `Z_{-1} ∩ U` ([BM88, Definition 4.1]: a
blowing-up
is determined by its restrictions to charts; `IsBlowUp.restrictOpens'`), and a map over the
identity between two blowings-up of the same centre is surjective (`surjective_of_comm`).

* `piRestrict`, `isBlowUp_piRestrict`, `surjective_liftIncl`;
* `coreOfListOf_isOfOrderGe`, `coreOfListOf_cosupp_disjoint`;
* `bundleInvOf`, `isClosedSubmanifold_transformSUOf`, `liftInclSOf`, `transportedValueOf` — the
  transport of the input's value from the trace of `π^{-1}(U)` on `S'` to the transform of `E^j`
  in the restricted blowing-up, along the inverse of the bundle diffeomorphism and the restriction
  of the corestricted lift, over an arbitrary centre `Z` and transform `S'`; `bundleInv`,
  `isClosedSubmanifold_transformSU`, `liftInclS`, `transportedValue` at `Z_{-1}` and `S_0`;
* `coreFamOn_eq_coreOfListOf` — the identification.

With it, the order clause and clause (1) of Lemma 102 for `BDanFam` reduce to the transport of the
input family's clauses along two local analytic isomorphisms (`BDFamOrder.lean`), and the
compatibility and commutation clauses to the behaviour of the core over a sequence under pull-back
(`BDFamPullback.lean`, `BDFamCompat.lean`, `BDFamComm.lean`).
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace Hironaka.Local
open scoped Manifold ContDiff

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace BDan

open _root_.Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ)
  (j : T.F.ι)

/-! ### The corestricted lift is surjective -/

/-- The blowing-up `π_{-1}` restricted over `U`, as a map `π_{-1}^{-1}(U) → U`. -/
noncomputable def piRestrict (U : Opens M) :
    (Manifold.blowUp ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)).restrict
        (piOpen T s j U) → M.restrict U :=
  fun q => ⟨piMinusOne T s j q.1, q.2⟩

/-- The blowing-up of `Z_{-1}` restricted over `U` is a blowing-up of `U` along `Z_{-1} ∩ U`
([BM88, Definition 4.1]: a blowing-up is characterised by its restrictions to charts). -/
theorem isBlowUp_piRestrict (U : Opens M) :
    IsBlowUp ψ₀ (⇑(M.inclusion U) ⁻¹' BD.Zminus1 T.I s (T.F.hyp j)) 1 (piRestrict T s j U) :=
  IsBlowUp.restrictOpens' (U := U) (U' := piOpen T s j U) rfl (fun _ => rfl)
    (BD.isClosedSubmanifold_Zminus1 T s j) (isBlowUp_blowUpπ ψ₀ _)

/-- The corestricted lift `liftIncl` of the inclusion `U ⊆ M` is surjective onto `π_{-1}^{-1}(U)`:
it is a map over the identity of `U` between two blowings-up of `U` along `Z_{-1} ∩ U`, and such a
map is surjective (`surjective_of_comm`; the pull-back of a blow-up sequence along an open
embedding in [Kol07, Definition 30 (1)]). -/
theorem surjective_liftIncl (U : Opens M) : Function.Surjective (liftIncl T s j U) := by
  refine surjective_of_comm
    ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
      (isLocalDiffeomorph_inclusion M U))
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id (M.restrict U))
        (isBlowUp_piRestrict T s j U)
    (isBlowUp_blowUpπ ψ₀ _) Function.surjective_id (liftIncl T s j U).contMDiff.continuous
    fun q => ?_
  exact Subtype.ext (AnalyticManifold.BlowUpSequence.blowUpπ_liftStep (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U)
    (BD.isClosedSubmanifold_Zminus1 T s j) q)

/-! ### The core over a sequence, with an arbitrary centre and transform -/

variable {Z : Set M} (hZ : IsClosedSubmanifold ψ₀ Z 1) {S' : Set (Manifold.blowUp ψ₀ hZ)}
  (hS' : IsClosedSubmanifold ψ₀ S' 1)

/-- The order clause `coreOfListOf_isOfOrderGe_of_bridge` over an arbitrary centre and transform
equal to `Z_{-1}` and `S_0`. -/
theorem coreOfListOf_isOfOrderGe (hT : BDClass s T) (hZeq : Z = BD.Zminus1 T.I s (T.F.hyp j))
    (hSeq : S' = transformSOf T j hZ)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin
        (n - 1) → 𝕜)) hS'.toAnalyticManifold)
    (hLne : L.NoEmptyCenters)
    (hL : L.toSuccession.IsOfOrderGe (restrictedTripleOf T s j hZ hS' hT hZeq hSeq).I s
      (restrictedTripleOf T s j hZ hS' hT hZeq hSeq).F.idealSheaf) :
    (coreOfListOf hZ hS' L).toSuccession.IsOfOrderGe T.I s T.F.idealSheaf := by
  subst hZeq
  subst hSeq
  exact coreOfListOf_isOfOrderGe_of_bridge T s j hT L (pushforwardBridge ψ₀) hLne hL

/-- Clause (1) `coreOfListOf_cosupp_disjoint_of_bridge` over an arbitrary centre and transform
equal to `Z_{-1}` and `S_0`. -/
theorem coreOfListOf_cosupp_disjoint (hT : BDClass s T) (hZeq : Z = BD.Zminus1 T.I s (T.F.hyp j))
    (hSeq : S' = transformSOf T j hZ)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin
        (n - 1) → 𝕜)) hS'.toAnalyticManifold)
    (hLne : L.NoEmptyCenters)
    (hL : L.toSuccession.IsOfOrderGe (restrictedTripleOf T s j hZ hS' hT hZeq hSeq).I s
      (restrictedTripleOf T s j hZ hS' hT hZeq hSeq).F.idealSheaf)
    (hlt : ∀ y, (L.toSuccession.markedTransformSeq (restrictedTripleOf T s j hZ hS' hT hZeq hSeq).I
      s (Fin.last _)).ord y < (s : ℕ∞)) :
    Disjoint
      {x | (s : ℕ∞) ≤
        ((coreOfListOf hZ hS' L).toSuccession.weakTransformSeq T.I (Fin.last _)).ord x}
      ((coreOfListOf hZ hS' L).toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _)) := by
  subst hZeq
  subst hSeq
  exact coreOfListOf_cosupp_disjoint_of_bridge T s j (pushforwardBridge ψ₀) hT L hLne hL hlt

/-! ### The transport over an arbitrary centre and transform -/

section Of

variable (U : Opens M)

/-- The inverse of the bundle diffeomorphism (`bundleInv`) over an arbitrary closed hypersurface `Z`
and a closed hypersurface `S'` of its blowing-up. -/
noncomputable def bundleInvOf :
    AnalyticMap ((hS'.restrictOpen (piOpenOf hZ U)).toAnalyticManifold)
      (hS'.toAnalyticManifold.restrict (hS'.preimageOpens (piOpenOf hZ U))) :=
  ⟨(hS'.restrictBundleDiffeomorphOf (piOpenOf hZ U) (hS'.preimageOpens (piOpenOf hZ U)) rfl).symm,
    (hS'.restrictBundleDiffeomorphOf (piOpenOf hZ U) (hS'.preimageOpens (piOpenOf hZ U))
      rfl).symm.contMDiff⟩

omit [FiniteDimensional 𝕜 E] in
include hS' in
/-- The transform `S'` pulled back along the corestricted lift of the inclusion of `U`, over an
arbitrary centre, is a closed hypersurface (`isClosedSubmanifold_transformSU` in general). -/
theorem isClosedSubmanifold_transformSUOf :
    IsClosedSubmanifold ψ₀
      (⇑(liftInclOf hZ U) ⁻¹' (⇑((Manifold.blowUp ψ₀ hZ).inclusion (piOpenOf hZ U)) ⁻¹' S')) 1 :=
  (hS'.restrictOpen (piOpenOf hZ U)).preimage_of_isLocalDiffeomorph
    (isLocalDiffeomorph_liftInclOf hZ U)

/-- The corestricted lift of the inclusion of `U` restricted to the transforms (`liftInclS`), over
an arbitrary centre and transform. -/
noncomputable def liftInclSOf :
    AnalyticMap (isClosedSubmanifold_transformSUOf hZ hS' U).toAnalyticManifold
      ((hS'.restrictOpen (piOpenOf hZ U)).toAnalyticManifold) :=
  (isClosedSubmanifold_transformSUOf hZ hS' U).restrictMap (hS'.restrictOpen (piOpenOf hZ U))
    (liftInclOf hZ U) (liftInclOf hZ U).contMDiff fun _ hx => hx

omit [FiniteDimensional 𝕜 E] in
/-- The transform over the restriction to `U` is the transform of the restricted data
(`transformSU_eq` over an arbitrary centre). -/
theorem transformSUOf_eq (hSeq : S' = transformSOf T j hZ) :
    ⇑(liftInclOf hZ U) ⁻¹' (⇑((Manifold.blowUp ψ₀ hZ).inclusion (piOpenOf hZ U)) ⁻¹' S') =
      transformSOf (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) j
        (hZ.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M U)) := by
  subst hSeq
  ext q
  change Manifold.blowUpπ ψ₀ hZ (AnalyticManifold.BlowUpSequence.liftStep (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U) hZ
      q) ∈ T.F.hyp j ↔
    M.inclusion U (Manifold.blowUpπ ψ₀ (hZ.preimage_of_isLocalDiffeomorph
        (isLocalDiffeomorph_inclusion M U))
      q) ∈ T.F.hyp j
  rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep]

/-- The transported value of the input (`transportedValue`) over an arbitrary centre and
transform. -/
noncomputable def transportedValueOf (inp : BMOanFam 𝕜 (n - 1) s) (hT : BDClass s T)
    (hZeq : Z = BD.Zminus1 T.I s (T.F.hyp j)) (hSeq : S' = transformSOf T j hZ)
    (hU : IsCompact (closure (U : Set M))) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (isClosedSubmanifold_transformSUOf hZ hS' U).toAnalyticManifold :=
  (((inp.functor.fam (restrictedTripleOf T s j hZ hS' hT hZeq hSeq)
        (bmoClass_restrictedTripleOf T s j hZ hS' hT hZeq hSeq)).seqOn
      (hS'.preimageOpens (piOpenOf hZ U))
      (hS'.isCompact_closure_preimageOpens _ (isCompact_closure_piOpenOf hZ U hU))).pullback
    (bundleInvOf hZ hS' U)
    (hS'.restrictBundleDiffeomorphOf (piOpenOf hZ U) (hS'.preimageOpens (piOpenOf hZ U))
      rfl).symm.isLocalDiffeomorph).pullback
    (liftInclSOf hZ hS' U)
    (IsClosedSubmanifold.isLocalDiffeomorph_restrictMap (liftInclOf hZ U)
      (isLocalDiffeomorph_liftInclOf hZ U) _)

end Of

/-! ### The core on an open as a core over the transported sequence -/

variable (inp : BMOanFam 𝕜 (n - 1) s) (hT : BDClass s T) (U : Opens M)
  (hU : IsCompact (closure (U : Set M)))

/-- The inverse of the bundle diffeomorphism between the restriction of `S_0` over `π_{-1}^{-1}(U)`
and the open `U_S` of the hypersurface `S_0` regarded as a manifold, as an analytic map from the
former to the latter. -/
noncomputable def bundleInv :
    AnalyticMap
      (((isClosedSubmanifold_transformS T s j).restrictOpen (piOpen T s j U)).toAnalyticManifold)
      ((isClosedSubmanifold_transformS T s j).toAnalyticManifold.restrict
        ((isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j U))) :=
  bundleInvOf _ (isClosedSubmanifold_transformS T s j) U

theorem isLocalDiffeomorph_bundleInv :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω (bundleInv T s j U) :=
  ((isClosedSubmanifold_transformS T s j).restrictBundleDiffeomorphOf (piOpen T s j U)
    ((isClosedSubmanifold_transformS T s j).preimageOpens
      (piOpen T s j U)) rfl).symm.isLocalDiffeomorph

theorem surjective_bundleInv : Function.Surjective (bundleInv T s j U) :=
  ((isClosedSubmanifold_transformS T s j).restrictBundleDiffeomorphOf (piOpen T s j U)
    ((isClosedSubmanifold_transformS T s j).preimageOpens
      (piOpen T s j U)) rfl).symm.toEquiv.surjective

/-- The transform of `E^j` inside the restricted blowing-up: the preimage under the corestricted
lift of `S_0 ∩ π_{-1}^{-1}(U)`, a closed hypersurface. -/
theorem isClosedSubmanifold_transformSU :
    IsClosedSubmanifold ψ₀ (⇑(liftIncl T s j U) ⁻¹'
      (⇑((Manifold.blowUp ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)).inclusion (piOpen T s j U)) ⁻¹'
        transformS T s j)) 1 :=
  isClosedSubmanifold_transformSUOf _ (isClosedSubmanifold_transformS T s j) U

/-- The corestricted lift of the inclusion restricted to the transforms of `E^j`. -/
noncomputable def liftInclS :
    AnalyticMap (isClosedSubmanifold_transformSU T s j U).toAnalyticManifold
      (((isClosedSubmanifold_transformS T s j).restrictOpen (piOpen T s j U)).toAnalyticManifold) :=
  liftInclSOf _ (isClosedSubmanifold_transformS T s j) U

/-- The input family's value at the trace of `π_{-1}^{-1}(U)` on `S_0`, transported to the transform
of `E^j` in the restricted blowing-up along the inverse of the bundle diffeomorphism and the
restricted lift. -/
noncomputable def transportedValue :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (isClosedSubmanifold_transformSU T s j U).toAnalyticManifold :=
  transportedValueOf T s j _ (isClosedSubmanifold_transformS T s j) U inp hT rfl rfl hU

/-- The core on `U` is the core over the transported value, on the restricted data: the
push-forward to the open `π_{-1}^{-1}(U)` is the push-forward along the bundle diffeomorphism
(`BlowUpSequence.pushforwardRestrictOf_eq`), and the push-forward commutes with the pull-back along
the corestricted lift (`BlowUpSequence.pushforward_pullback`; "we get the same result" whether one
first pulls back or first restricts, the proof of [Kol07, Lemma 102]). -/
theorem coreFamOn_eq_coreOfListOf :
    coreFamOn T s j inp hT U hU =
      coreOfListOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
        (isLocalDiffeomorph_inclusion M U)) (isClosedSubmanifold_transformSU T s j U)
        (transportedValue T s j inp hT U hU) := by
  unfold coreFamOn coreOfListOf transportedValue transportedValueOf liftInclSOf bundleInvOf
  simp only [AnalyticManifold.BlowUpSequence.pushforwardRestrict]
  rw [AnalyticManifold.BlowUpSequence.pushforwardRestrictOf_eq
      (isClosedSubmanifold_transformS T s j) (piOpen T s j U)
    ((isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j U)) rfl,
    AnalyticManifold.BlowUpSequence.pushforward_pullback ((isClosedSubmanifold_transformS T s
        j).restrictOpen
      (piOpen T s j U)) (liftIncl T s j U) (isLocalDiffeomorph_liftInclOf _ U)]
  rfl

end BDan

end Hironaka.Manifold
