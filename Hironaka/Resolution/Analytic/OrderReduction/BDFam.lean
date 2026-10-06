/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BD
public import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
public import Hironaka.Manifold.FiniteSuccession.Restrict.RestrictBundle
public import Hironaka.Resolution.Analytic.Functor.Family
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Lemma 102 in the compatible-family form: the construction

The functor `BD_{n,m,j}` of [Kol07, Lemma 102] is built in `BD.lean` from the marked
order-reduction functor `BMO_{n-1,m}` one dimension down: blow up the union `Z_{-1}` of the
components of `E^j` inside `cosupp(I, m)`, restrict the weak transform `I_0` and the boundary
`E - E^j` to the transform `S_0` of `E^j`, apply the input functor to the restricted triple and push
the result forward, `BD_{n,m,j}(X, I, E) := τ_* BMO_{n-1,m}(S, I_0|_S, m, E_S) ∘ π_{-1}`. This
module
repeats the construction with the input in the compatible-family form: `inp : BMOanFam 𝕜 (n - 1) s`
(`Functor/Family.lean`), whose values are finite blow-up sequences on the relatively compact open
subsets, compatible under inclusion ([Wlo09, Theorem 2.0.3 (1), (4)]; the remark after
[BM97, Theorem 1.6] on locally finite sequences), in place of the structure `BMOanData`. The
constructions of `BD.lean` on the whole manifold are reused: the centre `Z_{-1}` and its blowing-up
`π_{-1}` (`BD.Zminus1`, `BDan.piMinusOne`), the transform `S_0 = π_{-1}^{-1}(E^j)`
(`BDan.transformS`), the restricted triple `(S_0, I_0|_{S_0}, E_S)` (`BDan.restrictedTriple`).

* `isCompact_closure_preimageOpens_of_isProperMap` — the preimage of a relatively compact open
  under a proper analytic map is relatively compact.
* `BDan.piOpenOf`, `BDan.isCompact_closure_piOpenOf` — the preimage `π^{-1}(U)` of an open `U`
  under the blowing-up of a closed hypersurface `Z`, relatively compact when `U` is (the
  blowing-up is proper); `BDan.piOpen` at `Z = Z_{-1}`.
* `BDan.liftInclOf`, `BDan.isLocalDiffeomorph_liftInclOf` — the lift of the inclusion `U ⊆ M` to
  the blowing-up of `Z ∩ U`, corestricted onto `π^{-1}(U)`: a local analytic isomorphism onto that
  open, since the restriction of a blowing-up over an open is the blowing-up of the restricted
  centre; `BDan.liftIncl` at `Z = Z_{-1}`.
* `BDan.coreFamOn T s j inp hT U hU` — the core on the relatively compact open `U`, for a triple
  whose ideal sheaf is D-balanced: the blowing-up of `Z_{-1} ∩ U`, followed by the value of the
  input family on the restricted triple read at the trace of `π_{-1}^{-1}(U)` on `S_0`, pushed
  forward to the open `π_{-1}^{-1}(U)` of the blown-up manifold ([Kol07, Definition 30 (3)]) and
  pulled back along the corestricted lift of the inclusion, with empty blow-ups deleted
  ([Kol07, 32]).
* `BDanFam m inp T hT j U hU` — **the value of `BD_{n,m,j}` on `U`** for a triple of the class
  `BOClass m`: the core at the mark `s = tuningParam m` applied to the tuned triple `(M, W_s(𝓘), E)`
  (Step 1 of Kollár's proof, "by (101) … we assume that `I` is D-balanced"; `Tuned.lean`), the
  input being the marked family at the mark `s`.

The clauses of Lemma 102 for these values (the order clause, clause (1), the commutation with local
analytic isomorphisms, the indifference to empty members, the value at an empty member) and the
compatibility under restriction are proved in `BDFamClauses.lean`, `BDFamOrder.lean`,
`BDFamCompat.lean`, `BDFamIndiff.lean` and `BDFamComm.lean`, and assembled into the compatible
family `bdanFam` and the data `bdanFamDataOfInput : BDanFamData ψ₀ (tuningParam m)` in
`BOanFamOfInput.lean`, the input of Steps 2.1 and 2.2 of the proof of Theorem 103 in this form.
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The preimage of a relatively compact open under a proper analytic map is relatively compact:
the closure of the preimage lies in the preimage of the closure, which is compact. -/
theorem isCompact_closure_preimageOpens_of_isProperMap {M N : AnalyticManifold.{u} 𝕜 E}
    (f : AnalyticMap N M) (hf : IsProperMap f) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    IsCompact (closure (preimageOpens f f.contMDiff U : Set N)) :=
  (hf.isCompact_preimage hU).of_isClosed_subset isClosed_closure
    (hf.continuous.closure_preimage_subset _)

namespace BDan

open _root_.Manifold

variable [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ)
  (j : T.F.ι)

/-! ### The preimage of an open and the corestricted lift over an arbitrary closed hypersurface -/

section Of

variable {Z : Set M} (hZ : IsClosedSubmanifold ψ₀ Z 1)

/-- The preimage `π^{-1}(U)` of an open under the blowing-up of a closed hypersurface `Z` (`piOpen`
at `Z = Z_{-1}`). -/
noncomputable def piOpenOf (U : Opens M) : Opens (Manifold.blowUp ψ₀ hZ) :=
  preimageOpens (Manifold.blowUpπ ψ₀ hZ) (Manifold.blowUpπ ψ₀ hZ).contMDiff U

omit [FiniteDimensional 𝕜 E] in
/-- `π^{-1}(U)` is relatively compact when `U` is: the blowing-up is a proper map. -/
theorem isCompact_closure_piOpenOf (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    IsCompact (closure (piOpenOf hZ U : Set (Manifold.blowUp ψ₀ hZ))) :=
  isCompact_closure_preimageOpens_of_isProperMap _ (isBlowUp_blowUpπ ψ₀ hZ).isProperMap U hU

omit [FiniteDimensional 𝕜 E] in
/-- The lift of the inclusion `U ⊆ M` to the blowing-ups of `Z` (`BlowUpSequence.liftStep`) lands in
`π^{-1}(U)`. -/
theorem range_liftStep_inclusion_subsetOf (U : Opens M) :
    Set.range (AnalyticManifold.BlowUpSequence.liftStep (M.inclusion U)
        (isLocalDiffeomorph_inclusion M U) hZ) ⊆
      piOpenOf hZ U := by
  rintro _ ⟨q, rfl⟩
  change Manifold.blowUpπ ψ₀ hZ (AnalyticManifold.BlowUpSequence.liftStep (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U)
    hZ q) ∈ (U : Set M)
  rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep]
  exact (Manifold.blowUpπ ψ₀ _ q).2

/-- The lift of the inclusion `U ⊆ M` to the blowing-up of `Z ∩ U`, corestricted onto the open
`π^{-1}(U)` of the blowing-up of `Z` (`liftIncl` at `Z = Z_{-1}`). It is a local analytic
isomorphism onto that open (`isLocalDiffeomorph_liftInclOf`; surjective by `surjective_liftIncl` in
`BDFamTransport.lean`): the restriction of a blowing-up over an open is the blowing-up of the
restricted centre. -/
noncomputable def liftInclOf (U : Opens M) :
    AnalyticMap (Manifold.blowUp ψ₀ (hZ.preimage_of_isLocalDiffeomorph
        (isLocalDiffeomorph_inclusion M U)))
      ((Manifold.blowUp ψ₀ hZ).restrict (piOpenOf hZ U)) :=
  AnalyticMap.corestrict
    (AnalyticManifold.BlowUpSequence.liftStep (M.inclusion U)
        (isLocalDiffeomorph_inclusion M U) hZ) (piOpenOf hZ U)
    (range_liftStep_inclusion_subsetOf hZ U)

omit [FiniteDimensional 𝕜 E] in
/-- The corestricted lift of the inclusion is a local analytic isomorphism. -/
theorem isLocalDiffeomorph_liftInclOf (U : Opens M) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (liftInclOf hZ U) :=
  isLocalDiffeomorph_corestrict _ _ (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep _
      _ _) _

end Of

/-- The preimage `π_{-1}^{-1}(U)` of an open `U` of `M` in the blowing-up of `Z_{-1}`. -/
noncomputable def piOpen (U : Opens M) : Opens (Manifold.blowUp ψ₀
    (BD.isClosedSubmanifold_Zminus1 T s j)) :=
  piOpenOf (BD.isClosedSubmanifold_Zminus1 T s j) U

/-- The lift of the inclusion `U ⊆ M` to the blowing-up of `Z_{-1} ∩ U`, corestricted onto the open
`π_{-1}^{-1}(U)` of the blowing-up of `Z_{-1}` (`liftInclOf` at `Z_{-1}`). -/
noncomputable def liftIncl (U : Opens M) :
    AnalyticMap
      (Manifold.blowUp ψ₀ ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
        (isLocalDiffeomorph_inclusion M U)))
      ((Manifold.blowUp ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)).restrict (piOpen T s j U)) :=
  liftInclOf (BD.isClosedSubmanifold_Zminus1 T s j) U

/-- The core of the proof of [Kol07, Lemma 102] on a relatively compact open `U`, for a triple of
`BOClass s` with D-balanced ideal sheaf and the input `BMO_{n-1,s}` in the compatible-family form:
the blowing-up of `Z_{-1} ∩ U`, then the input family's value on the restricted triple
`(S_0, I_0|_{S_0}, E_S)` read at the trace of `π_{-1}^{-1}(U)` on `S_0`, pushed forward to the open
`π_{-1}^{-1}(U)` ([Kol07, Definition 30 (3)]; `BlowUpSequence.pushforwardRestrict`) and pulled back
along
the corestricted lift of the inclusion, with empty blow-ups deleted ([Kol07, 32]). -/
noncomputable def coreFamOn (inp : BMOanFam 𝕜 (n - 1) s) (hT : BDClass s T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) : AnalyticManifold.BlowUpSequence ψ₀ (M.restrict U) :=
  (AnalyticManifold.BlowUpSequence.cons
    ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
      (isLocalDiffeomorph_inclusion M U))
    ((AnalyticManifold.BlowUpSequence.pushforwardRestrict (isClosedSubmanifold_transformS T s j)
        (piOpen T s j U)
      ((inp.functor.fam (restrictedTriple T s j hT) (bmoClass_restrictedTriple T s j hT)).seqOn
        ((isClosedSubmanifold_transformS T s j).preimageOpens (piOpen T s j U))
        ((isClosedSubmanifold_transformS T s j).isCompact_closure_preimageOpens _
          (isCompact_closure_piOpenOf _ U hU)))).pullback (liftIncl T s j U)
      (isLocalDiffeomorph_liftInclOf _ U))).eraseEmpty

/-- The core on `U` has no empty centres ([Kol07, 32]): they are deleted. -/
theorem noEmptyCenters_coreFamOn (inp : BMOanFam 𝕜 (n - 1) s) (hT : BDClass s T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) : (coreFamOn T s j inp hT U hU).NoEmptyCenters :=
  AnalyticManifold.BlowUpSequence.noEmptyCenters_eraseEmpty _

end BDan

/-- **The value of `BD_{n,m,j}` on a relatively compact open `U`** ([Kol07, Lemma 102], in the
compatible-family form): for a triple of the class `BOClass m`, the core at the mark
`s = tuningParam m` applied to the tuned triple `(M, W_s(𝓘), E)` (the tuning that opens the proof of
Lemma 102, `Tuned.lean`), with the input `BMO_{n-1,s}` in the compatible-family form. The member
`E^j` is named
by its index `j`. -/
noncomputable def BDanFam [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} (m : ℕ)
    (inp : BMOanFam 𝕜 (n - 1) (tuningParam m)) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass m T) (j : T.F.ι) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) : AnalyticManifold.BlowUpSequence ψ₀ (M.restrict U) :=
  BDan.coreFamOn (T.tuned m hT.1) (tuningParam m) j inp
    ⟨AnalyticTriple.boClass_tuned hT, AnalyticTriple.isDBalanced_tuned hT⟩ U hU

/-- The value of `BD_{n,m,j}` on `U` has no empty centres ([Kol07, 32]). -/
theorem noEmptyCenters_BDanFam [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} (m : ℕ)
    (inp : BMOanFam 𝕜 (n - 1) (tuningParam m)) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass m T) (j : T.F.ι) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) : (BDanFam m inp T hT j U hU).NoEmptyCenters :=
  BDan.noEmptyCenters_coreFamOn _ _ _ _ _ _ _

end Hironaka.Manifold
