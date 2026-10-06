/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.GlobalizeFamCover
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.PullbackSequence
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.OrderReduction.GlobalizeFam
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 3 of Theorem 103 in the compatible-family form: the existence statement and the descent
of the clauses

Two consequences of the descended family functor of `GlobalizeFam.lean`:

* `AnalyticFamilyFunctor.BO_globalizeFam` — Step 3 of the proof of [Kol07, Theorem 103] as an
  existence statement: a family functor on the class `LocalMCClass m` commuting with local analytic
  isomorphisms extends to one on `BOClass m` agreeing with it on `LocalMCClass m` and commuting with
  local analytic isomorphisms (witnessed by `globalizeFam`).
* `isOfOrderGe_of_agreeFam`, `ord_lt_of_agreeFam`, `indifferentToEmptyMembers_of_agreeFam` — the
  descent of the clauses of Theorem 103 along the cover of Step 3, per relatively compact open
  ("the functoriality package is local", [Kol07, 104, Step 2.3]). For a relatively compact open
  `U` of a triple `T` of the class, a finite cover `C` of the closure of `U` by pieces with maximal
  contact (`GlobalizeFamCover.lean`) gives the surjective local analytic isomorphism
  `k : ⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U) → U`; for any extension `B'` agreeing with `B` on the local class and
  commuting with local analytic isomorphisms, the pull-back along `k` of the value of `B'` on `U`
  is the value of `B` on the cover (`ShrunkMCCover.seqOn_coverList_eq`), and the two restricted
  triples agree (`triple_pullback_inclusion_eq`). The order clause ([Kol07, Definition 66]) and the
  conclusion `max-ord I_r < m` ([Kol07, Theorem 103 (1)]) then descend along the surjective `k`
  pointwise, and the indifference to empty boundary members descends because the
  triple with the smaller boundary has the same cover (maximal contact depends only on the ideal
  sheaf), `B` is indifferent on the cover, and pull-back along `k` is injective.

They give the order-reduction family assembled in `BOanFamOfInput.lean` its clauses.
-/

public section

noncomputable section

open Set Topology TopologicalSpace Function
open scoped Manifold ContDiff

universe u

namespace Manifold.AnalyticTriple

open Hironaka.Manifold
open AnalyticManifold.BlowUpSequence

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [hfd : FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {m : ℕ}

namespace ShrunkMCCover

open Hironaka.Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M} {U : Opens M}
  (C : ShrunkMCCover T m U)

omit hfd in
/-- The two restrictions agree: the restriction of the coproduct triple to the open
`⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U)` is the pull-back of the restriction `T|_U` along the cover map (both carry the
pull-back data of `T` along the same map `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U) → M`). -/
theorem triple_pullback_inclusion_eq :
    C.triple.pullback (C.sigma.inclusion C.opens) (isLocalDiffeomorph_inclusion C.sigma C.opens) =
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).pullback C.coverMap
        C.isLocalDiffeomorph_coverMap := by
  have hk : C.desc.comp (C.sigma.inclusion C.opens) = (M.inclusion U).comp C.coverMap :=
    ContMDiffMap.ext fun _ => rfl
  have h₁ : (C.triple.pullback (C.sigma.inclusion C.opens)
      (isLocalDiffeomorph_inclusion C.sigma C.opens)).IsPullbackOf T
        (C.desc.comp (C.sigma.inclusion C.opens)) :=
    (T.isPullbackOf_pullback C.desc C.isLocalDiffeomorph_desc).comp
      (C.triple.isPullbackOf_pullback _ _)
  have h₂ : ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).pullback C.coverMap
      C.isLocalDiffeomorph_coverMap).IsPullbackOf T ((M.inclusion U).comp C.coverMap) :=
    (T.isPullbackOf_pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).comp
      ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isPullbackOf_pullback
        C.coverMap C.isLocalDiffeomorph_coverMap)
  rw [hk] at h₁
  exact IsPullbackOf.eq h₁ h₂

omit hfd in
/-- For an extension `B'` of `B` (agreeing on the local class, commuting with local analytic
isomorphisms), the value of `B` on the open `⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U)` of the coproduct is the pull-back
of the value of `B'` on `U` along the cover map; no empty blow-up is deleted, the cover map being
onto `U`. -/
theorem seqOn_coverList_eq (B : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.LocalMCClass m))
    (B' : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.BOClass m))
    (hagree : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N)
      (hL : AnalyticTriple.LocalMCClass m T), B'.fam T hL.1 = B.fam T hL)
    (hB' : B'.CommutesWithLocalIsos) (hG : AnalyticTriple.BOClass m T)
    (hU : IsCompact (closure (U : Set M))) :
    (B.fam C.triple (C.localMCClass_triple hG)).seqOn C.opens C.isCompact_closure_opens =
      ((B'.fam T hG).seqOn U hU).pullback C.coverMap C.isLocalDiffeomorph_coverMap := by
  have hTσ := C.localMCClass_triple hG
  have h := hB'.seqOn_eq_of_image_eq C.isLocalDiffeomorph_desc
    (T.isPullbackOf_pullback C.desc C.isLocalDiffeomorph_desc) hG hTσ.1 C.isCompact_closure_opens hU
    C.image_opens_eq
  rw [hagree C.triple hTσ] at h
  rw [h]
  exact eraseEmpty_pullback_of_surjective _ ((B'.fam T hG).noEmptyCenters U hU) _ _
    C.surjective_coverMap

end ShrunkMCCover

end Manifold.AnalyticTriple

namespace Hironaka.Manifold

open AnalyticManifold.BlowUpSequence

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [hfd : FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {m : ℕ}

namespace AnalyticFamilyFunctor

open _root_.Manifold

/-- Step 3 of the proof of [Kol07, Theorem 103] in the compatible-family form, as an existence
statement: a family functor `B` on the class `LocalMCClass m` of triples with a global hypersurface
of maximal contact, commuting with local analytic isomorphisms, extends to a family functor on
`BOClass m` which agrees with `B` on `LocalMCClass m` and commutes with local analytic isomorphisms.
The witness is `globalizeFam B hB` (`GlobalizeFam.lean`). -/
theorem BO_globalizeFam (B : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.LocalMCClass m))
    (hB : B.CommutesWithLocalIsos) :
    ∃ B' : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.BOClass m),
      (∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N)
        (hL : AnalyticTriple.LocalMCClass m T), B'.fam T hL.1 = B.fam T hL) ∧
        B'.CommutesWithLocalIsos := by
  have _hfd := hfd
  exact ⟨globalizeFam B hB, fun T hL => globalizeFam_fam_eq B hB T hL,
    globalizeFam_commutesWithLocalIsos B hB⟩

omit hfd in
/-- The order clause ([Kol07, Definition 66]) descends along the cover of Step 3 of the proof of
[Kol07, Theorem 103], per relatively compact open: on the cover `k : ⊔ᵢ ιᵢ^{-1}(Wᵢ ∩ U) → U` of the
closure of `U` by pieces with maximal contact, the pull-back along `k` of the value of `B'` on `U`
is the value of `B` on the cover, which is of order `≥ m` for the pulled-back data, and being a
smooth blow-up sequence of order `≥ m` descends along a surjective local analytic isomorphism
(`BlowUpSequence.isOfOrderGe_of_pullback`). -/
theorem isOfOrderGe_of_agreeFam (B : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.LocalMCClass m))
    (B' : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.BOClass m))
    (hagree : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N)
      (hL : AnalyticTriple.LocalMCClass m T), B'.fam T hL.1 = B.fam T hL)
    (hB' : B'.CommutesWithLocalIsos)
    (hord : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N)
      (hL : AnalyticTriple.LocalMCClass m T) (U : Opens N)
      (hU : IsCompact (closure (U : Set N))),
      ((B.fam T hL).seqOn U hU).toSuccession.IsOfOrderGe
        (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I m
        (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).F.idealSheaf)
    {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N) (hG : AnalyticTriple.BOClass m T)
    (U : Opens N) (hU : IsCompact (closure (U : Set N))) :
    ((B'.fam T hG).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I m
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).F.idealSheaf := by
  obtain ⟨C⟩ := AnalyticTriple.exists_shrunkMCCover hG hU
  set TU := T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U) with hTU
  have h := hord C.triple (C.localMCClass_triple hG) C.opens C.isCompact_closure_opens
  rw [C.seqOn_coverList_eq B B' hagree hB' hG hU, C.triple_pullback_inclusion_eq,
    (TU.isPullbackOf_pullback C.coverMap C.isLocalDiffeomorph_coverMap).1,
    (TU.isPullbackOf_pullback C.coverMap C.isLocalDiffeomorph_coverMap).2,
    HypersurfaceFamily.idealSheaf_comap_of_surjective C.coverMap C.isLocalDiffeomorph_coverMap
      C.surjective_coverMap] at h
  exact isOfOrderGe_of_pullback _ C.coverMap C.isLocalDiffeomorph_coverMap C.surjective_coverMap
    TU.I TU.F.idealSheaf m h

omit hfd in
/-- The conclusion `max-ord I_r < m` of [Kol07, Theorem 103 (1)] descends along the cover of Step 3,
per relatively compact open: a point of the last stage over `U` is the image of a point of the last
stage of the pull-back along the surjective cover map `k`, where the value of `B` on the cover has
order `< m`, and the order of a pull-back along a local analytic isomorphism at a point is the order
at its image. -/
theorem ord_lt_of_agreeFam (B : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.LocalMCClass m))
    (B' : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.BOClass m))
    (hagree : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N)
      (hL : AnalyticTriple.LocalMCClass m T), B'.fam T hL.1 = B.fam T hL)
    (hB' : B'.CommutesWithLocalIsos)
    (hlt : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N)
      (hL : AnalyticTriple.LocalMCClass m T) (U : Opens N)
      (hU : IsCompact (closure (U : Set N)))
      (x : ((B.fam T hL).seqOn U hU).toSuccession.stage (Fin.last _)),
      (((B.fam T hL).seqOn U hU).toSuccession.weakTransformSeq
        (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I (Fin.last _)).ord x <
        (m : ℕ∞))
    {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N) (hG : AnalyticTriple.BOClass m T)
    (U : Opens N) (hU : IsCompact (closure (U : Set N)))
    (x : ((B'.fam T hG).seqOn U hU).toSuccession.stage (Fin.last _)) :
    (((B'.fam T hG).seqOn U hU).toSuccession.weakTransformSeq
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I (Fin.last _)).ord x <
      (m : ℕ∞) := by
  obtain ⟨C⟩ := AnalyticTriple.exists_shrunkMCCover hG hU
  have hkl := C.isLocalDiffeomorph_coverMap
  have hks := C.surjective_coverMap
  have e := C.seqOn_coverList_eq B B' hagree hB' hG hU
  have H := forall_last_ord_lt_of_eq e
    (C.triple.pullback (C.sigma.inclusion C.opens) (isLocalDiffeomorph_inclusion C.sigma C.opens)).I
    m (hlt C.triple (C.localMCClass_triple hG) C.opens C.isCompact_closure_opens)
  rw [C.triple_pullback_inclusion_eq,
    ((T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).isPullbackOf_pullback
      C.coverMap hkl).1] at H
  have hk' : ((B'.fam T hG).seqOn U hU).length <
      (((B'.fam T hG).seqOn U hU).pullback C.coverMap hkl).length + 1 := by
    rw [length_pullback]
    exact Nat.lt_succ_self _
  obtain ⟨x', rfl⟩ := surjective_pullbackLiftAux ((B'.fam T hG).seqOn U hU) C.coverMap hkl hks
    ((B'.fam T hG).seqOn U hU).length (Nat.lt_succ_self _) hk' x
  have hx' := ord_lt_of_forall_last
    ((T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I.pullback C.coverMap
        C.coverMap.contMDiff) m H
    ((B'.fam T hG).seqOn U hU).length hk'
    (length_pullback ((B'.fam T hG).seqOn U hU) C.coverMap hkl).symm x'
  rw [weakTransformSeqAux_pullback ((B'.fam T hG).seqOn U hU) C.coverMap hkl
    (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I
    ((B'.fam T hG).seqOn U hU).length (Nat.lt_succ_self _) hk'] at hx'
  have hord := IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt
    ⇑(((B'.fam T hG).seqOn U hU).pullbackLiftAux C.coverMap hkl ((B'.fam T hG).seqOn U hU).length
      (Nat.lt_succ_self _) hk')
    (((B'.fam T hG).seqOn U hU).pullbackLiftAux C.coverMap hkl ((B'.fam T hG).seqOn U hU).length
      (Nat.lt_succ_self _) hk').contMDiff
    (((B'.fam T hG).seqOn U hU).toSuccession.weakTransformSeqAux
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I
      ((B'.fam T hG).seqOn U hU).length (Nat.lt_succ_self _))
    (isLocalDiffeomorph_pullbackLiftAux ((B'.fam T hG).seqOn U hU) C.coverMap hkl
      ((B'.fam T hG).seqOn U hU).length (Nat.lt_succ_self _) hk' x')
  exact lt_of_eq_of_lt hord.symm hx'

/-- The indifference to empty boundary members descends along the cover of Step 3:
the triple with the smaller boundary has the same finite cover by pieces with maximal contact
(maximal contact depends only on the ideal sheaf), `B` is indifferent on the cover, and pull-back
along the surjective cover map is injective. -/
theorem indifferentToEmptyMembers_of_agreeFam
    (B : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.LocalMCClass m))
    (B' : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.BOClass m))
    (hagree : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N)
      (hL : AnalyticTriple.LocalMCClass m T), B'.fam T hL.1 = B.fam T hL)
    (hB' : B'.CommutesWithLocalIsos) (hind : B.IndifferentToEmptyMembers) :
    B'.IndifferentToEmptyMembers := by
  have _hfd := hfd
  intro N T F' hsnc' e hhyp hempty hT hT₂ U hU
  obtain ⟨C⟩ := AnalyticTriple.exists_shrunkMCCover hT hU
  set T₂ : AnalyticTriple ψ₀ N := ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ with hT₂def
  have hmc₂ : ∀ i, AnalyticTriple.HasMaximalContact m (T₂.pullback (C.ι i) (C.hι i).1) :=
    fun i => C.hmc i
  let C₂ : AnalyticTriple.ShrunkMCCover T₂ m U :=
    ⟨C.t, C.N, C.ι, C.hι, C.W, hmc₂, C.hWc, C.hWr, C.hcov⟩
  have hTσ := C.localMCClass_triple hT
  have hTσ₂ := C₂.localMCClass_triple hT₂
  have hBind : (B.fam C.triple hTσ).seqOn C.opens C.isCompact_closure_opens =
      (B.fam C₂.triple hTσ₂).seqOn C₂.opens C₂.isCompact_closure_opens :=
    hind C.triple (F'.comap C.desc) (HypersurfaceFamily.isSnc_comap hsnc' C.desc
      C.isLocalDiffeomorph_desc) e
      (fun i => by
        change ⇑C.desc ⁻¹' T.F.hyp (e i) = ⇑C.desc ⁻¹' F'.hyp i
        rw [hhyp i])
      (fun b hb => by
        change ⇑C.desc ⁻¹' T.F.hyp b = ∅
        rw [hempty b hb, Set.preimage_empty])
      hTσ hTσ₂ C.opens C.isCompact_closure_opens
  have e₁ := C.seqOn_coverList_eq B B' hagree hB' hT hU
  have e₂ := C₂.seqOn_coverList_eq B B' hagree hB' hT₂ hU
  refine pullback_injective_of_surjective C.coverMap C.isLocalDiffeomorph_coverMap
    C.surjective_coverMap _ _ ?_
  exact e₁.symm.trans (hBind.trans e₂)

end AnalyticFamilyFunctor

end Hironaka.Manifold

end
