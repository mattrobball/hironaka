/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BDFamTransport
import Hironaka.Manifold.FiniteSuccession.Functor.LiftedFibre
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackCover
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BDFamPullback
import Hironaka.Resolution.Analytic.OrderReduction.TunedLemmas
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Lemma 102 in the compatible-family form: commutation with local analytic isomorphisms

Clause (2) of [Kol07, Lemma 102], the commutation of `BD_{n,m,j}` with smooth morphisms, for the
values on relatively compact opens (`BDanFam`, `BDFam.lean`), in the one-clause form of the family
functors (`AnalyticFamilyFunctor.CommutesWithLocalIsos`, both clauses of [Kol07, 34.1] at once):
for a local analytic isomorphism `g : N → M`, the value of the pulled-back data on `U' ⊆ N` is the
value on the image `g(U') ⊆ M` pulled back along `g|_{U'}`, with its empty blow-ups deleted
(`BDanFam_commutesWithLocalIsos`). Kollár's argument, that pulling back by `h` and then restricting
to `E^j_Y` gives "the same result" as restricting to `E^j` and then pulling back by `h|_{E^j_Y}`, is
carried out on the cores.

Both sides are cores over transported values (`BDFamTransport.lean`). The left side is first
rewritten over the centre `g^{-1}(Z_{-1})` and the transform `(lift g)^{-1}(S_0)`
(`coreFamOn_eq_coreOfListOf_of_eq`, along `BD.Zminus1_comap`); the restricted triple there is the
pull-back of the restricted triple of `T` along the restricted lift `g|_S`
(`restrictedTripleOf_isPullbackOf`, `BDOf.lean`), so the input family's own commutation applies at
the trace `U'_S`. The image of `U'_S` under `g|_S` is the trace `g(U')_S`
(`imageOpens_liftRestrictS_eq`: the lift of `g|_{U'}` is surjective, and a point over `g(U')` is in
the range of the lift of the inclusion), the lift of `g ∘ (U' ⊆ N)` is the lift of
`(g(U') ⊆ M) ∘ g|_{U'}` (uniqueness of lifts, `liftStep_restrictMap_comm`), and the behaviour of the
core over a sequence under pull-back (`BDFamPullback.lean`) identifies the two cores.

* `coreFamOn_eq_coreOfListOf_of_eq` — the core on an open over the transported value
  (`transportedValueOf`, `BDFamTransport.lean`) over an arbitrary centre and transform;
* `heq_pullback_seqOn_of_eq` — pull-backs of the values of a compatible family on equal opens
  along pointwise equal maps agree;
* `liftRestrictS`, `liftStep_restrictMap_comm`, `imageOpens_liftRestrictS_eq`,
  `transformSU_restrictMap_eq` — the restricted lift of `g` and the bookkeeping of the two lifts;
* `coreFamOn_commutesWithLocalIsos`, `coreFamOn_congr`, `BDanFam_commutesWithLocalIsos`.

This is the `commutesWithLocalIsos` field of Lemma 102's family data `bdanFamDataOfInput` in
`BOanFamOfInput.lean`.
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace BDan

open _root_.Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ)
  (j : T.F.ι)

/-! ### The transported value over an arbitrary centre and transform -/

section Of

variable {Z : Set M} (hZ : IsClosedSubmanifold ψ₀ Z 1) {S' : Set (Manifold.blowUp ψ₀ hZ)}
  (hS' : IsClosedSubmanifold ψ₀ S' 1) (U : Opens M)

/-- The core on an open is the core over the transported value, read over any centre `Z = Z_{-1}`
and transform `S' = S_0` (`coreFamOn_eq_coreOfListOf` over an arbitrary centre). -/
theorem coreFamOn_eq_coreOfListOf_of_eq (inp : BMOanFam 𝕜 (n - 1) s) (hT : BDClass s T)
    (hZeq : Z = BD.Zminus1 T.I s (T.F.hyp j)) (hSeq : S' = transformSOf T j hZ)
    (hU : IsCompact (closure (U : Set M))) :
    coreFamOn T s j inp hT U hU =
      coreOfListOf (hZ.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M U))
        (isClosedSubmanifold_transformSUOf hZ hS' U)
        (transportedValueOf T s j hZ hS' U inp hT hZeq hSeq hU) := by
  subst hZeq
  subst hSeq
  exact coreFamOn_eq_coreOfListOf T s j inp hT U hU

end Of

/-! ### Two pull-backs of a family value on equal opens -/

omit [FiniteDimensional 𝕜 E] in
/-- Pull-backs of the values of a compatible family on two equal opens, along maps from two equal
closed hypersurfaces agreeing pointwise, are equal (as heterogeneous equality, the domains being
equal only propositionally). -/
theorem heq_pullback_seqOn_of_eq {X : AnalyticManifold.{u} 𝕜 E}
    {A : AnalyticManifold.{u} 𝕜 (Fin (n - 1) → 𝕜)}
    {R : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) A} (C : CompatibleFamily R)
    {V₁ V₂ : Opens A} (e : V₁ = V₂) (hV₁ : IsCompact (closure (V₁ : Set A)))
    (hV₂ : IsCompact (closure (V₂ : Set A))) {S₁ S₂ : Set X} (eS : S₁ = S₂)
    (h₁ : IsClosedSubmanifold ψ₀ S₁ 1) (h₂ : IsClosedSubmanifold ψ₀ S₂ 1)
    (f₁ : AnalyticMap h₁.toAnalyticManifold (A.restrict V₁))
    (f₂ : AnalyticMap h₂.toAnalyticManifold (A.restrict V₂))
    (hf₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω f₁)
    (hf₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω f₂)
    (hf : ∀ (x : X) (hx₁ : x ∈ S₁) (hx₂ : x ∈ S₂), (f₁ ⟨x, hx₁⟩).1 = (f₂ ⟨x, hx₂⟩).1) :
    HEq ((C.seqOn V₁ hV₁).pullback f₁ hf₁) ((C.seqOn V₂ hV₂).pullback f₂ hf₂) := by
  subst e
  subst eS
  have hfe : f₁ = f₂ := ContMDiffMap.ext fun p => Subtype.ext (hf p.1 p.2 p.2)
  subst hfe
  rfl

/-! ### Commutation of the core on an open with a local analytic isomorphism -/

section Comm

variable {N : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
  (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (U' : Opens N)

/-- The restriction `g|_S : (lift g)^{-1}(S_0) → S_0` of the lift of `g` to the transforms of `E^j`
(Kollár's `h|_{E^j_Y}` in the proof of [Kol07, Lemma 102]). -/
noncomputable def liftRestrictS :
    AnalyticMap
      ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
          (BD.isClosedSubmanifold_Zminus1 T s j))).toAnalyticManifold
      (isClosedSubmanifold_transformS T s j).toAnalyticManifold :=
  ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
        (BD.isClosedSubmanifold_Zminus1 T s j))).restrictMap
    (isClosedSubmanifold_transformS T s j)
    (AnalyticManifold.BlowUpSequence.liftStep g hg (BD.isClosedSubmanifold_Zminus1 T s j))
    (AnalyticManifold.BlowUpSequence.liftStep g hg (BD.isClosedSubmanifold_Zminus1 T s
        j)).contMDiff fun _ hx => hx

/-- The restricted lift `g|_S` is a local analytic isomorphism. -/
theorem isLocalDiffeomorph_liftRestrictS :
    IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω (liftRestrictS T s j g hg) :=
  IsClosedSubmanifold.isLocalDiffeomorph_restrictMap
    (AnalyticManifold.BlowUpSequence.liftStep g hg (BD.isClosedSubmanifold_Zminus1 T s j))
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
        (BD.isClosedSubmanifold_Zminus1 T s j)) _

/-- The lift of `g ∘ (U' ⊆ N)` to the blowings-up is the lift of `(g(U') ⊆ M) ∘ g|_{U'}`
(uniqueness of lifts, `eq_of_comm_blowUp`). -/
theorem liftStep_restrictMap_comm :
    ⇑(AnalyticManifold.BlowUpSequence.liftStep g hg (BD.isClosedSubmanifold_Zminus1 T s j)) ∘
        ⇑(AnalyticManifold.BlowUpSequence.liftStep (N.inclusion U')
            (isLocalDiffeomorph_inclusion N U')
          ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg)) =
      ⇑(AnalyticManifold.BlowUpSequence.liftStep (M.inclusion (AnalyticMap.imageOpens g hg U'))
          (isLocalDiffeomorph_inclusion M _) (BD.isClosedSubmanifold_Zminus1 T s j)) ∘
        ⇑(AnalyticManifold.BlowUpSequence.liftStep
          (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
          (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
            Set.Subset.rfl)
          ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
            (isLocalDiffeomorph_inclusion M _))) :=
  eq_of_comm_blowUp (p := g.comp (N.inclusion U')) (BD.isClosedSubmanifold_Zminus1 T s j)
    (((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
      hg).preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion N U')) rfl
    ((AnalyticManifold.BlowUpSequence.liftStep _ _ _).contMDiff.continuous.comp
      (AnalyticManifold.BlowUpSequence.liftStep _ _ _).contMDiff.continuous)
    ((AnalyticManifold.BlowUpSequence.liftStep _ _ _).contMDiff.continuous.comp
      (AnalyticManifold.BlowUpSequence.liftStep _ _ _).contMDiff.continuous)
    (fun u => by
      change Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)
          (AnalyticManifold.BlowUpSequence.liftStep g hg (BD.isClosedSubmanifold_Zminus1 T s j)
            (AnalyticManifold.BlowUpSequence.liftStep (N.inclusion U')
                (isLocalDiffeomorph_inclusion N U')
              ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg) u)) =
        g (N.inclusion U' (Manifold.blowUpπ ψ₀ (((BD.isClosedSubmanifold_Zminus1 T s
          j).preimage_of_isLocalDiffeomorph hg).preimage_of_isLocalDiffeomorph
            (isLocalDiffeomorph_inclusion N U')) u))
      rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep,
          AnalyticManifold.BlowUpSequence.blowUpπ_liftStep])
    (fun u => by
      change Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)
          (AnalyticManifold.BlowUpSequence.liftStep (M.inclusion (AnalyticMap.imageOpens g hg U'))
            (isLocalDiffeomorph_inclusion M _) (BD.isClosedSubmanifold_Zminus1 T s j)
            (AnalyticManifold.BlowUpSequence.liftStep
              (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
              (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
                Set.Subset.rfl)
              ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
                (isLocalDiffeomorph_inclusion M _)) u)) =
        g (N.inclusion U' (Manifold.blowUpπ ψ₀ (((BD.isClosedSubmanifold_Zminus1 T s
          j).preimage_of_isLocalDiffeomorph hg).preimage_of_isLocalDiffeomorph
            (isLocalDiffeomorph_inclusion N U')) u))
      rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep]
      exact congrArg (M.inclusion (AnalyticMap.imageOpens g hg U'))
        (AnalyticManifold.BlowUpSequence.blowUpπ_liftStep
          (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
          (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
            Set.Subset.rfl)
          ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
            (isLocalDiffeomorph_inclusion M _)) u))

/-- `liftStep_restrictMap_comm`, pointwise. -/
theorem liftStep_restrictMap_comm_apply
    (x : Manifold.blowUp ψ₀ (((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
      hg).preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion N U'))) :
    AnalyticManifold.BlowUpSequence.liftStep g hg (BD.isClosedSubmanifold_Zminus1 T s j)
        (AnalyticManifold.BlowUpSequence.liftStep (N.inclusion U')
            (isLocalDiffeomorph_inclusion N U')
          ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg) x) =
      AnalyticManifold.BlowUpSequence.liftStep (M.inclusion (AnalyticMap.imageOpens g hg U'))
        (isLocalDiffeomorph_inclusion M _) (BD.isClosedSubmanifold_Zminus1 T s j)
        (AnalyticManifold.BlowUpSequence.liftStep
          (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
          (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
            Set.Subset.rfl)
          ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
            (isLocalDiffeomorph_inclusion M _)) x) :=
  congrFun (liftStep_restrictMap_comm T s j g hg U') x

/-- The image of the trace `U'_S` under the restricted lift `g|_S` is the trace `g(U')_S`: the lift
of `g|_{U'}` is surjective (`surjective_liftStep`), and a point of `S_0` over `g(U')` is in the
range
of the lift of the inclusion (`exists_liftStep_eq`). -/
theorem imageOpens_liftRestrictS_eq :
    AnalyticMap.imageOpens (liftRestrictS T s j g hg) (isLocalDiffeomorph_liftRestrictS T s j g hg)
        (((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
            (BD.isClosedSubmanifold_Zminus1 T s j))).preimageOpens
          (piOpenOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg)
            U')) =
      (isClosedSubmanifold_transformS T s j).preimageOpens
        (piOpen T s j (AnalyticMap.imageOpens g hg U')) := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    change Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)
      (AnalyticManifold.BlowUpSequence.liftStep g hg (BD.isClosedSubmanifold_Zminus1 T s j) x.1) ∈
          ⇑g '' (U' : Set N)
    rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep]
    exact ⟨_, hx, rfl⟩
  · intro hp
    change Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j) p.1 ∈ ⇑g '' (U' : Set N) at hp
    obtain ⟨u, hu, hgu⟩ := hp
    obtain ⟨q, hq⟩ := AnalyticManifold.BlowUpSequence.exists_liftStep_eq (M.inclusion
        (AnalyticMap.imageOpens g hg U'))
      (isLocalDiffeomorph_inclusion M _) (BD.isClosedSubmanifold_Zminus1 T s j) p.1
      (b := ⟨g u, ⟨u, hu, rfl⟩⟩) hgu
    obtain ⟨x, hx⟩ := AnalyticManifold.BlowUpSequence.surjective_liftStep
      (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
        Set.Subset.rfl)
      ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
        (isLocalDiffeomorph_inclusion M _))
      (AnalyticMap.surjective_restrictMap rfl) q
    have hcomm := liftStep_restrictMap_comm_apply T s j g hg U' x
    have hπ := AnalyticManifold.BlowUpSequence.blowUpπ_liftStep (N.inclusion U')
        (isLocalDiffeomorph_inclusion N U')
      ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg) x
    refine ⟨⟨AnalyticManifold.BlowUpSequence.liftStep (N.inclusion U')
        (isLocalDiffeomorph_inclusion N U')
      ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg) x, ?_⟩, ?_, ?_⟩
    · change AnalyticManifold.BlowUpSequence.liftStep g hg (BD.isClosedSubmanifold_Zminus1 T s j)
        (AnalyticManifold.BlowUpSequence.liftStep (N.inclusion U')
            (isLocalDiffeomorph_inclusion N U')
          ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg) x) ∈
        transformS T s j
      rw [hcomm, hx, hq]
      exact p.2
    · change Manifold.blowUpπ ψ₀ ((BD.isClosedSubmanifold_Zminus1 T s
        j).preimage_of_isLocalDiffeomorph hg)
        (AnalyticManifold.BlowUpSequence.liftStep (N.inclusion U')
            (isLocalDiffeomorph_inclusion N U')
          ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg) x) ∈
        (U' : Set N)
      rw [hπ]
      exact (Manifold.blowUpπ ψ₀ _ x).2
    · exact Subtype.ext (hcomm.trans ((congrArg (AnalyticManifold.BlowUpSequence.liftStep
        (M.inclusion (AnalyticMap.imageOpens g hg U')) (isLocalDiffeomorph_inclusion M _)
        (BD.isClosedSubmanifold_Zminus1 T s j)) hx).trans hq))

/-- The transform of `E^j` pulled back along the lift of `g|_{U'}` is the transform of the
restricted
pulled-back data (`transformSU_pullback_eq` along `g`). -/
theorem transformSU_restrictMap_eq :
    ⇑(AnalyticManifold.BlowUpSequence.liftStep
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)
        ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
          (isLocalDiffeomorph_inclusion M _))) ⁻¹'
        (⇑(liftIncl T s j (AnalyticMap.imageOpens g hg U')) ⁻¹'
          (⇑((Manifold.blowUp ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)).inclusion
            (piOpen T s j (AnalyticMap.imageOpens g hg U'))) ⁻¹' transformS T s j)) =
      ⇑(Manifold.blowUpπ ψ₀ (((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
          (isLocalDiffeomorph_inclusion M (AnalyticMap.imageOpens g hg
            U'))).preimage_of_isLocalDiffeomorph
          (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
            Set.Subset.rfl))) ⁻¹'
        (⇑(N.inclusion U') ⁻¹' (⇑g ⁻¹' T.F.hyp j)) := by
  ext q
  change Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)
      (AnalyticManifold.BlowUpSequence.liftStep (M.inclusion (AnalyticMap.imageOpens g hg U'))
        (isLocalDiffeomorph_inclusion M _) (BD.isClosedSubmanifold_Zminus1 T s j)
        (AnalyticManifold.BlowUpSequence.liftStep
          (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
          (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
            Set.Subset.rfl)
          ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
            (isLocalDiffeomorph_inclusion M _)) q)) ∈ T.F.hyp j ↔
    g (N.inclusion U' (Manifold.blowUpπ ψ₀ (((BD.isClosedSubmanifold_Zminus1 T s
      j).preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M (AnalyticMap.imageOpens g hg
        U'))).preimage_of_isLocalDiffeomorph
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)) q)) ∈ T.F.hyp j
  rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep,
      AnalyticManifold.BlowUpSequence.blowUpπ_liftStep]
  exact Iff.rfl

variable (inp : BMOanFam 𝕜 (n - 1) s) (hT : BDClass s T) (hT' : BDClass s (T.pullback g hg))
  (hU' : IsCompact (closure (U' : Set N)))

/-- Clause (2) of [Kol07, Lemma 102] for the core on an open: the core of the pulled-back data on
`U'` is the core on `g(U')` pulled back along `g|_{U'}`, with its empty blow-ups deleted. Both sides
are cores over transported values on the same centre and transform; the transported values agree
because the input family commutes with the restricted lift `g|_S` at the trace `U'_S`, whose image
is the trace `g(U')_S`, and the two lifts compose as `liftStep_restrictMap_comm` says. -/
theorem coreFamOn_commutesWithLocalIsos :
    coreFamOn (T.pullback g hg) s j inp hT' U' hU' =
      ((coreFamOn T s j inp hT (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty := by
  -- the right side: the core on the image, pulled back along the lift of `g|_{U'}` (`erw`: the
  -- goal reads `j : T.F.ι` at the pulled-back triple, whose index type unfolds to `T.F.ι` only at
  -- default transparency)
  erw [coreFamOn_eq_coreOfListOf T s j inp hT _ _, coreOfListOf_pullback_eraseEmpty]
  -- the left side: the core over the centre `g⁻¹(Z_{-1})` and the transform `(lift g)⁻¹(S_0)`
  erw [coreFamOn_eq_coreOfListOf_of_eq (T.pullback g hg) s j
    ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg)
    ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
          (BD.isClosedSubmanifold_Zminus1 T s j)))
    U' inp hT' (BD.Zminus1_comap g hg T.I s (T.isSnc.1 j)).symm
    (preimage_liftStep_transformS T s j g hg) hU']
  -- the trace `U'_S` of `π⁻¹(U')` on `(lift g)⁻¹(S_0)` is relatively compact
  have hU'S :=
    ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
        (BD.isClosedSubmanifold_Zminus1 T s j))).isCompact_closure_preimageOpens _
      (isCompact_closure_piOpenOf _ U' hU')
  -- the input family commutes with the restricted lift `g|_{S}` at the trace `U'_S`
  have hcomm := inp.commutesWithLocalIsos (restrictedTriple T s j hT)
    (restrictedTripleOf (T.pullback g hg) s j
      ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg)
      ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
            (BD.isClosedSubmanifold_Zminus1 T s j))) hT'
      (BD.Zminus1_comap g hg T.I s (T.isSnc.1 j)).symm (preimage_liftStep_transformS T s j g hg))
    (liftRestrictS T s j g hg) (isLocalDiffeomorph_liftRestrictS T s j g hg)
    (restrictedTripleOf_isPullbackOf T s j g hg hT hT') (bmoClass_restrictedTriple T s j hT)
    (bmoClass_restrictedTripleOf (T.pullback g hg) s j _ _ hT' _ _)
    (((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
        (BD.isClosedSubmanifold_Zminus1 T s j))).preimageOpens
      (piOpenOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg) U'))
    hU'S
  -- the transported values, with the local-isomorphism proofs stated at the maps as named
  have hl : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (liftInclSOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg)
        ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
              (BD.isClosedSubmanifold_Zminus1 T s j)))
        U') :=
    IsClosedSubmanifold.isLocalDiffeomorph_restrictMap (liftInclOf _ U')
      (isLocalDiffeomorph_liftInclOf _ U') _
  have hb : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (bundleInvOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg)
        ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
              (BD.isClosedSubmanifold_Zminus1 T s j)))
        U') :=
    (IsClosedSubmanifold.restrictBundleDiffeomorphOf _ _ _ rfl).symm.isLocalDiffeomorph
  have hlW : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (liftInclS T s j (AnalyticMap.imageOpens g hg U')) :=
    IsClosedSubmanifold.isLocalDiffeomorph_restrictMap (liftIncl T s j _)
      (isLocalDiffeomorph_liftInclOf _ _) _
  have hL' : transportedValueOf (T.pullback g hg) s j
      ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg)
      ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
            (BD.isClosedSubmanifold_Zminus1 T s j)))
      U' inp hT' (BD.Zminus1_comap g hg T.I s (T.isSnc.1 j)).symm
      (preimage_liftStep_transformS T s j g hg) hU' =
      ((((inp.functor.fam (restrictedTriple T s j hT) (bmoClass_restrictedTriple T s j hT)).seqOn
            (AnalyticMap.imageOpens (liftRestrictS T s j g hg)
              (isLocalDiffeomorph_liftRestrictS T s j g hg)
              (((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
                (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
                  (BD.isClosedSubmanifold_Zminus1 T s j))).preimageOpens
                (piOpenOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
                  hg) U')))
            (AnalyticMap.isCompact_closure_image (liftRestrictS T s j g hg) hU'S)).pullback
          (AnalyticMap.restrictMap (liftRestrictS T s j g hg) _ _ Set.Subset.rfl)
          (AnalyticMap.isLocalDiffeomorph_restrictMap (isLocalDiffeomorph_liftRestrictS T s j g hg)
            _ _ Set.Subset.rfl)).eraseEmpty.pullback (bundleInvOf _ _ U') hb).pullback
        (liftInclSOf _ _ U') hl := by
    unfold transportedValueOf
    exact congrArg
      (fun L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
          (((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
              (BD.isClosedSubmanifold_Zminus1 T s j))).toAnalyticManifold.restrict
            (((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
              (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
                (BD.isClosedSubmanifold_Zminus1 T s j))).preimageOpens
              (piOpenOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg)
                U'))) =>
        (L.pullback (bundleInvOf _ _ U') hb).pullback (liftInclSOf _ _ U') hl) hcomm
  have hW' : transportedValue T s j inp hT (AnalyticMap.imageOpens g hg U')
      (AnalyticMap.isCompact_closure_image g hU') =
      (((inp.functor.fam (restrictedTriple T s j hT) (bmoClass_restrictedTriple T s j hT)).seqOn
            ((isClosedSubmanifold_transformS T s j).preimageOpens
              (piOpen T s j (AnalyticMap.imageOpens g hg U')))
            ((isClosedSubmanifold_transformS T s j).isCompact_closure_preimageOpens _
              (isCompact_closure_piOpenOf _ _
                (AnalyticMap.isCompact_closure_image g hU')))).pullback
          (bundleInv T s j (AnalyticMap.imageOpens g hg U'))
          (isLocalDiffeomorph_bundleInv T s j _)).pullback
        (liftInclS T s j (AnalyticMap.imageOpens g hg U')) hlW := rfl
  erw [hL']
  rw [hW', coreOfListOf_pullback_pullback_eraseEmpty]
  -- both transported lists as one pull-back of the input value on the trace `g(U')_S`
  have hab₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      ((AnalyticMap.restrictMap (liftRestrictS T s j g hg)
            (((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
              (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
                (BD.isClosedSubmanifold_Zminus1 T s j))).preimageOpens
              (piOpenOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
                hg) U'))
            (AnalyticMap.imageOpens (liftRestrictS T s j g hg)
              (isLocalDiffeomorph_liftRestrictS T s j g hg)
              (((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
              (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
                (BD.isClosedSubmanifold_Zminus1 T s j))).preimageOpens
              (piOpenOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
                hg) U'))) Set.Subset.rfl).comp
        (bundleInvOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg)
          ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
                (BD.isClosedSubmanifold_Zminus1 T s j)))
          U')) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
      (AnalyticMap.isLocalDiffeomorph_restrictMap (isLocalDiffeomorph_liftRestrictS T s j g hg)
        _ _ Set.Subset.rfl) hb
  have habc₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (((AnalyticMap.restrictMap (liftRestrictS T s j g hg)
            (((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
              (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
                (BD.isClosedSubmanifold_Zminus1 T s j))).preimageOpens
              (piOpenOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
                hg) U'))
            (AnalyticMap.imageOpens (liftRestrictS T s j g hg)
              (isLocalDiffeomorph_liftRestrictS T s j g hg)
              (((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
              (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
                (BD.isClosedSubmanifold_Zminus1 T s j))).preimageOpens
              (piOpenOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
                hg) U'))) Set.Subset.rfl).comp
        (bundleInvOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg)
          ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
                (BD.isClosedSubmanifold_Zminus1 T s j)))
          U')).comp
        (liftInclSOf ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph hg)
          ((isClosedSubmanifold_transformS T s j).preimage_of_isLocalDiffeomorph
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep g hg
                (BD.isClosedSubmanifold_Zminus1 T s j)))
          U')) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hab₁ hl
  have hab₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      ((bundleInv T s j (AnalyticMap.imageOpens g hg U')).comp
        (liftInclS T s j (AnalyticMap.imageOpens g hg U'))) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_bundleInv T s j _)
        hlW
  have habc₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - 1) → 𝕜) 𝓘(𝕜, Fin (n - 1) → 𝕜) ω
      (((bundleInv T s j (AnalyticMap.imageOpens g hg U')).comp
        (liftInclS T s j (AnalyticMap.imageOpens g hg U'))).comp
        (((isClosedSubmanifold_transformSU T s j
          (AnalyticMap.imageOpens g hg U')).preimage_of_isLocalDiffeomorph
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep
            (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
            (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
              Set.Subset.rfl)
            ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
              (isLocalDiffeomorph_inclusion M _)))).restrictMap
          (isClosedSubmanifold_transformSU T s j (AnalyticMap.imageOpens g hg U'))
          (AnalyticManifold.BlowUpSequence.liftStep
            (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
            (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
              Set.Subset.rfl)
            ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
              (isLocalDiffeomorph_inclusion M _)))
          (AnalyticManifold.BlowUpSequence.liftStep
            (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
            (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
              Set.Subset.rfl)
            ((BD.isClosedSubmanifold_Zminus1 T s j).preimage_of_isLocalDiffeomorph
              (isLocalDiffeomorph_inclusion M _))).contMDiff fun _ hx => hx)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hab₂
      (IsClosedSubmanifold.isLocalDiffeomorph_restrictMap _
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep _ _ _) _)
  rw [AnalyticManifold.BlowUpSequence.pullback_comp, AnalyticManifold.BlowUpSequence.pullback_comp,
    AnalyticManifold.BlowUpSequence.pullback_comp, AnalyticManifold.BlowUpSequence.pullback_comp]
  -- the two cores: the same centre and the same transform of `Eʲ` as sets, and transported lists
  -- agreeing pointwise (`liftStep_restrictMap_comm`) on the same trace
  -- (`imageOpens_liftRestrictS_eq`)
  refine coreOfListOf_congr _ _ _ _ rfl rfl
    (transformSUOf_eq (T.pullback g hg) j _ U' (preimage_liftStep_transformS T s j g hg))
    (transformSU_restrictMap_eq T s j g hg U') _ _ ?_
  exact heq_pullback_seqOn_of_eq _ (imageOpens_liftRestrictS_eq T s j g hg U') _ _
    ((transformSUOf_eq (T.pullback g hg) j _ U' (preimage_liftStep_transformS T s j g hg)).trans
      (transformSU_restrictMap_eq T s j g hg U').symm) _ _ _ _ habc₁ habc₂
    fun x _ _ => Subtype.ext (liftStep_restrictMap_comm_apply T s j g hg U' x)

end Comm

/-- The core on an open depends only on the triple (used to pass between the tuning of a pull-back
and the pull-back of the tuning). -/
theorem coreFamOn_congr {T₁ T₂ : AnalyticTriple ψ₀ M} (h : T₁ = T₂) (j₁ : T₁.F.ι) (j₂ : T₂.F.ι)
    (hj : HEq j₁ j₂) (inp : BMOanFam 𝕜 (n - 1) s) (hT₁ : BDClass s T₁) (hT₂ : BDClass s T₂)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    coreFamOn T₁ s j₁ inp hT₁ U hU = coreFamOn T₂ s j₂ inp hT₂ U hU := by
  subst h
  cases hj
  rfl

end BDan

section Assembly

variable {M : AnalyticManifold.{u} 𝕜 E} {m : ℕ}

/-- Clause (2) of [Kol07, Lemma 102], "`BD_{n,m,j}` commutes with smooth morphisms", for the values
on relatively compact opens: for a local analytic isomorphism `g : N → M`, the value of the
pulled-back data on `U'` is the value on `g(U')` pulled back along `g|_{U'}` with its empty
blow-ups deleted (both clauses of [Kol07, 34.1] in the one-clause form of the family functors).
This is `coreFamOn_commutesWithLocalIsos` at the tuned triple, the tuning commuting with pull-back
(`tuned_pullback`). -/
theorem BDanFam_commutesWithLocalIsos (inp : BMOanFam 𝕜 (n - 1) (tuningParam m))
    {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hT : AnalyticTriple.BOClass m T)
    (hT' : AnalyticTriple.BOClass m (T.pullback g hg)) (j : T.F.ι) (U' : Opens N)
    (hU' : IsCompact (closure (U' : Set N))) :
    BDanFam m inp (T.pullback g hg) hT' j U' hU' =
      ((BDanFam m inp T hT j (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty := by
  unfold BDanFam
  have hTt : BDan.BDClass (tuningParam m) ((T.tuned m hT.1).pullback g hg) := by
    rw [← AnalyticTriple.tuned_pullback]
    exact ⟨AnalyticTriple.boClass_tuned hT', AnalyticTriple.isDBalanced_tuned hT'⟩
  exact (BDan.coreFamOn_congr (tuningParam m) (AnalyticTriple.tuned_pullback T hT'.1 g hg) j j
    HEq.rfl inp _ hTt U' hU').trans
    (BDan.coreFamOn_commutesWithLocalIsos (T.tuned m hT.1) (tuningParam m) j g hg U' inp _ hTt hU')

end Assembly

end Hironaka.Manifold
