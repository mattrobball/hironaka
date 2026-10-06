/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.RefineStep
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Realize
public import Hironaka.Resolution.Algebraic.Monomial.Geometric.ChainRunErase
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Center
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Kernel
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.RealizesBlowUp
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial procedure commutes with local analytic isomorphisms up to empty blow-ups

For a piece family `Ψ` on `X` refining a piece family `Φ` on `Y` along a local analytic isomorphism
`ρ : X → Y` (`BMO/Step3Monomial/RefinesAlong.lean`), the run of the monomial procedure on `Ψ` is the
pull-back along `ρ` of the run on `Φ` with its empty blow-ups erased
(`RefinesAlong.realize_pullback_eraseEmpty`), and step for step when `ρ` is surjective
(`realize_pullback_of_surjective`). This is the functoriality of [Kol07, 111, Step 3] under smooth
morphisms in the sense of [Kol07, 34.1], with empty blow-ups deleted as in [Kol07, 32]; on
manifolds it is the compatibility of [Wlo09, Theorem 3.5.1 (1)–(2)]. The three properties of the
value of the procedure on an open set (`BMO/Step3Monomial/Naturality.lean`) are instances of it.

The proof has a combinatorial half and a geometric half.

* The combinatorial half. The state of `Ψ` is related to the state of `Φ` by a renaming of labels
  (the relabelling `relabel Ψ σ`), a refinement of the state of the pull-back family
  `pullbackFamily Φ ρ`, and the inclusion of that state in the state of `Φ`. The combinatorial model
  (`Hironaka.Monomial.MonomialState.step3_chainE`) then writes the run of the relabelled state as
  the run of the state of `Φ` with skips (`MonomialState.chainRunE`): the steps whose centre has no
  face over `X` are skipped, the others are performed on the faces over them. The run of the state
  of `Ψ` itself is the same list, since a renaming of the labels does not change the run
  (`step3_snd_eq_of_rel_id`).
* The geometric half. `realizeAux_pullback_eraseEmpty` is an induction along the run on `Y`,
  carrying a shadow state with the pieces and nerve of `Ψ`: at a centre with no face of `Ψ` over it
  the preimage of the centre is empty, the pulled-back blow-up is erased, and `Ψ` refines the
  transformed family along the lift composed with the identification of the empty blow-up with its
  base (`RefinesAlong.of_empty_step`); at a centre with faces over it both sides blow up the same
  centre, the transformed families refine one another along the transported lift
  (`RefinesAlong.blowUpPieces`, `BMO/Step3Monomial/RefineStep.lean`), and the two tails are
  identified through the equality of the centres. The nerve rule of `BMO/Step3Monomial/Kernel.lean`
  keeps the shadow state in step with the transitions of `Ψ`.

The statements assume no relation between the member embeddings of the two families and the label
map `σ`: the run depends on the pieces, their exponents and the order of the labels alone. Two
general facts on the combinatorial relations (`Refines.refl`, `Sub.refl`) and two transports of
blow-ups along equal centres of possibly differently stated codimensions (`blowUp_congr'`,
`blowUpπ_castDom_liftStep'`) sit here beside their use.
-/

public section

open Set Topology TopologicalSpace Hironaka.Monomial
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Transport along equal centres of possibly different stated codimensions -/

/-- `cons_congr_heq` with the codimensions identified by an equation as well. -/
theorem cons_congr_heq_of_eq {M : AnalyticManifold.{u} 𝕜 E} {Y₁ Y₂ : Set M} {c₁ c₂ : ℕ}
    (e : Y₁ = Y₂) (hc : c₁ = c₂) (h₁ : IsClosedSubmanifold ψ₀ Y₁ c₁)
    (h₂ : IsClosedSubmanifold ψ₀ Y₂ c₂) (r₁ : BlowUpSequence ψ₀ (Manifold.blowUp ψ₀ h₁))
    (r₂ : BlowUpSequence ψ₀ (Manifold.blowUp ψ₀ h₂)) (hr : HEq r₁ r₂) : cons h₁ r₁ = cons h₂ r₂ :=
        by
  subst e
  subst hc
  obtain rfl := eq_of_heq hr
  rfl

/-- Erasing the empty blow-ups respects heterogeneous equality over equal manifolds. -/
theorem eraseEmpty_heq {M₁ M₂ : AnalyticManifold.{u} 𝕜 E} (e : M₁ = M₂) (L₁ : BlowUpSequence ψ₀ M₁)
    (L₂ : BlowUpSequence ψ₀ M₂) (h : HEq L₁ L₂) : HEq L₁.eraseEmpty L₂.eraseEmpty := by
  subst e
  obtain rfl := eq_of_heq h
  rfl

/-- `blowUp_congr` with the codimensions identified by an equation as well; the same statement as
`blowUp_congr` with an extra hypothesis, used where the codimension is given by an equation. -/
theorem blowUp_congr' {M : AnalyticManifold.{u} 𝕜 E} {Z Z' : Set M} {c c' : ℕ} (hZZ' : Z = Z')
    (hc : c = c') (hZ : IsClosedSubmanifold ψ₀ Z c) (hZ' : IsClosedSubmanifold ψ₀ Z' c') :
    Manifold.blowUp ψ₀ hZ = Manifold.blowUp ψ₀ hZ' := by
  subst hZZ'
  subst hc
  rfl

/-- `blowUpπ_castDom_liftStep` with the codimensions identified by an equation as well. -/
theorem blowUpπ_castDom_liftStep' {M N : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {Z : Set N}
    {c c' : ℕ} (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (hY : IsClosedSubmanifold ψ₀ Y c) (hZ : IsClosedSubmanifold ψ₀ Z c') (hZg : Z = ⇑g ⁻¹' Y)
    (hc : c' = c) (q : Manifold.blowUp ψ₀ hZ) :
    Manifold.blowUpπ ψ₀ hY (Hironaka.Manifold.AnalyticMap.castDom
      (blowUp_congr' hZg hc hZ (hY.preimage_of_isLocalDiffeomorph hg)) (liftStep g hg hY) q) =
      g (Manifold.blowUpπ ψ₀ hZ q) := by
  subst hZg
  subst hc
  exact blowUpπ_liftStep g hg hY q

end AnalyticManifold.BlowUpSequence

/-! ### The combinatorial glue: a renaming of labels alone does not change the run -/

namespace Hironaka.Monomial.MonomialState

/-- Every state refines itself along the identity. -/
theorem Refines.refl (D : MonomialState) : Refines id D D where
  n_eq := rfl
  m_eq := rfl
  nextLabel_eq := rfl
  lt _ hc := hc
  label_eq _ _ := rfl
  a_eq _ _ := rfl
  injOn _ _ := Set.injOn_id _
  image_mem T hT := by rw [Finset.image_id]; exact hT
  exists_lift T' hT' := ⟨T', hT', Finset.image_id⟩

/-- Every state is a sub-state of itself. -/
theorem Sub.refl (D : MonomialState) : Sub D D :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, Finset.Subset.refl _⟩

/-- The run with skips of a run, along a parent map that is the identity on the pieces, from a state
with the same pieces and nerve, is the run itself: no step is skipped and every centre is its own
set of faces over itself. -/
theorem chainRunE_eq_self {N st' : MonomialState} {L : List (Finset (Finset ℕ))}
    (h : IsRun N L st') :
    ∀ (ρ : ℕ → ℕ) (D : MonomialState), (∀ c, c < D.nextComp → ρ c = c) →
      D.nextComp = N.nextComp → D.nerve = N.nerve → chainRunE ρ D N L = L := by
  induction h with
  | nil st => intros; rfl
  | @cons N st' L r _ _ hne _ ih =>
    intro ρ D hρ hnc hnv
    have hSn : N.choice r ⊆ D.nerve := fun P hP => by
      rw [hnv]
      exact N.mem_nerve_of_mem_choice hP
    have himg : ∀ Q ∈ D.nerve, Q.image ρ = Q := fun Q hQ => by
      rw [Finset.image_congr (g := id) fun c hc => hρ c (D.lt_nextComp_of_mem hQ hc),
        Finset.image_id]
    have hfil : (D.nerve.filter fun Q => Q.image ρ ∈ N.choice r) = N.choice r := by
      ext Q
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hQ, hQS⟩
        rwa [himg Q hQ] at hQS
      · intro hQ
        exact ⟨hSn hQ, by rw [himg Q (hSn hQ)]; exact hQ⟩
    have hne' : (D.nerve.filter fun Q => Q.image ρ ∈ N.choice r) ≠ ∅ := by
      rw [hfil]
      exact Finset.nonempty_iff_ne_empty.mp hne
    rw [chainRunE_cons_of_ne_empty _ _ _ _ hne', hfil]
    congr 1
    refine ih _ _ ?_ ?_ ?_
    · intro c hc
      rw [blowUp_nextComp] at hc
      rcases lt_or_exists_newComp D (N.choice r) hc with hlt | ⟨Q, hQ, rfl⟩
      · rw [extendComp_of_lt _ _ _ _ _ hlt]
        exact hρ c hlt
      · rw [extendComp_newComp _ _ _ _ _ hQ, himg Q (hSn hQ)]
        simp only [newComp, hnc]
    · simp only [blowUp_nextComp, hnc]
    · rw [blowUp_nerve, blowUp_nerve, hnv]
      congr 1
      funext P
      simp only [newComp, hnc]

/-- A renaming of the labels alone does not change the run of the monomial procedure: two states
related by `Rel id σ` with the same pieces have the same list of centres. -/
theorem step3_snd_eq_of_rel_id {σ : ℕ → ℕ} {D P : MonomialState} (h : Rel id σ D P)
    (hnc : D.nextComp = P.nextComp) : (step3 D).2 = (step3 P).2 := by
  obtain ⟨-, hrun⟩ := step3_chainE (ρ := id) (Refines.refl D) h (Sub.refl P) fun _ _ => rfl
  rw [hrun]
  refine chainRunE_eq_self (step3_isRun P) id D (fun _ _ => rfl) hnc ?_
  rw [h.nerve_eq]
  ext T
  simp only [Finset.mem_image]
  constructor
  · intro hT
    exact ⟨T, hT, Finset.image_id⟩
  · rintro ⟨T', hT', rfl⟩
    rw [Finset.image_id]
    exact hT'

end Hironaka.Monomial.MonomialState

namespace Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace PieceFamily

open _root_.Manifold

/-! ### Relabelling, centres over a centre, the parent maps -/

variable {X Y : AnalyticManifold.{u} 𝕜 E} {Ψ : PieceFamily X} {Φ : PieceFamily Y}
  {ρ : AnalyticMap X Y} {p σ : ℕ → ℕ}

/-- The relabelled family satisfies the invariants of the state when the label map is injective on
the labels in use. -/
theorem isValid_relabel (Ψ : PieceFamily X) (σ : ℕ → ℕ) (L : ℕ)
    (hσ : ∀ ℓ, ℓ < Ψ.nextLabel → σ ℓ < L) (hinj : Set.InjOn σ (Set.Iio Ψ.nextLabel)) {n m : ℕ}
    (hV : Ψ.IsValid n m) : (Ψ.relabel σ L hσ).IsValid n m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hV
  refine ⟨h1, h2, h3, fun c _ hc => hσ _ (Ψ.label_lt c hc), h5, h6, fun T hT c hc c' hc' hl => ?_⟩
  exact h7 T hT hc hc' (hinj (Ψ.label_lt _ (h3 T hT c hc)) (Ψ.label_lt _ (h3 T hT c' hc')) hl)

/-- The extension of the parent map on the combinatorial model, from a shadow state with the pieces
of `Ψ`, is `extendParent`. -/
theorem extendComp_eq_extendParent (Ψ : PieceFamily X) (Φ : PieceFamily Y) (p : ℕ → ℕ)
    (D : MonomialState) (hnc : D.nextComp = Ψ.nextComp) {n m : ℕ} (hVΦ : Φ.IsValid n m)
    (S' S : Finset (Finset ℕ)) :
    MonomialState.extendComp p D (Φ.toState n m hVΦ) S' S = Ψ.extendParent Φ p S' S := by
  funext c
  have hnew : ∀ Q, D.newComp S' Q = Ψ.newComp S' Q := fun Q => by
    simp only [MonomialState.newComp, newComp, hnc]
  have hfil : (S'.filter fun Q => D.newComp S' Q = c) = S'.filter fun Q => Ψ.newComp S' Q = c :=
    Finset.filter_congr fun Q _ => by rw [hnew]
  have hsup : (fun Q : Finset ℕ => (Φ.toState n m hVΦ).newComp S (Q.image p)) =
      fun Q => Φ.newComp S (Q.image p) := rfl
  unfold MonomialState.extendComp extendParent
  rw [hnc, hfil, hsup]

namespace RefinesAlong

open _root_.Manifold

variable (h : Ψ.RefinesAlong ρ p σ Φ)
include h

/-- The faces of `Ψ` over a centre of the state of `Φ` form a centre of the state of `Ψ`: they are
faces, and two of them have equal label sets because their images do and `σ` is injective on the
labels. -/
theorem isCenter_preimageFaces {n m : ℕ} (hVΨ : Ψ.IsValid n m) (hVΦ : Φ.IsValid n m)
    (S : Finset (Finset ℕ)) (hS : (Φ.toState n m hVΦ).IsCenter S) :
    (Ψ.toState n m hVΨ).IsCenter (Ψ.preimageFaces p S) := by
  refine ⟨fun Q hQ => (mem_preimageFaces.mp hQ).1, fun Q₁ hQ₁ Q₂ hQ₂ => ?_⟩
  obtain ⟨hQ₁n, hQ₁S⟩ := mem_preimageFaces.mp hQ₁
  obtain ⟨hQ₂n, hQ₂S⟩ := mem_preimageFaces.mp hQ₂
  have hlab : Φ.labels (Q₁.image p) = Φ.labels (Q₂.image p) := hS.2 _ hQ₁S _ hQ₂S
  have key : ∀ Q ∈ Ψ.nerve, Φ.labels (Q.image p) = (Ψ.labels Q).image σ := fun Q hQ => by
    unfold labels
    rw [Finset.image_image, Finset.image_image]
    exact Finset.image_congr fun c hc => h.label_eq c (Ψ.lt_nextComp_of_mem_nerve hQ hc)
  have hsub : ∀ Q ∈ Ψ.nerve, (↑(Ψ.labels Q) : Set ℕ) ⊆ Set.Iio Ψ.nextLabel := fun Q hQ ℓ hℓ => by
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hℓ)
    exact Ψ.label_lt c (Ψ.lt_nextComp_of_mem_nerve hQ hc)
  rw [key Q₁ hQ₁n, key Q₂ hQ₂n] at hlab
  change Ψ.labels Q₁ = Ψ.labels Q₂
  refine Finset.coe_injective ((h.σ_strictMonoOn.injOn.image_eq_image_iff (hsub Q₁ hQ₁n)
    (hsub Q₂ hQ₂n)).mp ?_)
  rw [← Finset.coe_image, ← Finset.coe_image, hlab]

/-- The faces over a centre have the centre's face size: the parent map is injective on a face and
all faces of a centre have the same size. -/
theorem faceCard_preimageFaces {F : HypersurfaceFamily Y} {e : Fin Φ.nextLabel ↪o F.ι}
    (hΦ : Φ.Realizes F e) {n m : ℕ} {hVΦ : Φ.IsValid n m} {S : Finset (Finset ℕ)}
    (hS : (Φ.toState n m hVΦ).IsCenter S) (hne : (Ψ.preimageFaces p S).Nonempty) :
    faceCard (Ψ.preimageFaces p S) = faceCard S := by
  obtain ⟨Q₀, hQ₀⟩ := hne
  have hcard : ∀ Q ∈ Ψ.preimageFaces p S, Q.card = faceCard S := fun Q hQ => by
    obtain ⟨hQn, hQS⟩ := mem_preimageFaces.mp hQ
    rw [← hΦ.card_eq_faceCard_of_isCenter hS hQS,
      Finset.card_image_of_injOn (h.image_mem_nerve hQn).2]
  unfold faceCard
  apply le_antisymm
  · exact Finset.sup_le fun Q hQ => (hcard Q hQ).le
  · exact (hcard Q₀ hQ₀).symm.le.trans (Finset.le_sup hQ₀)

/-- The step of the comparison in which no face of `Ψ` maps into the centre `S` of `Φ`: the preimage
of the centre is empty, the corresponding blow-up is deleted from the run over `X` ([Kol07, 32]),
and `Ψ` itself refines the transformed family of `Φ` along any map over `ρ`, with the same parent
and label maps (the label map now into the larger label range). -/
theorem of_empty_step (S : Finset (Finset ℕ)) (hS : ∀ P ∈ S, P ∈ Φ.nerve)
    (hno : ∀ Q ∈ Ψ.nerve, Q.image p ∉ S) (m : ℕ) {r : ℕ}
    (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r) (ℓ : AnalyticMap X (Manifold.blowUp ψ₀ hZ))
    (hsq : ∀ x, Manifold.blowUpπ ψ₀ hZ (ℓ x) = ρ x) :
    Ψ.RefinesAlong ℓ p σ (Φ.blowUpPieces S m hZ) := by
  classical
  have hpre : ⇑ρ ⁻¹' Φ.centerOf S = ∅ := h.preimage_centerOf_eq_empty S hS hno
  have hnot : ∀ x, ρ x ∉ Φ.centerOf S := fun x hx =>
    Set.eq_empty_iff_forall_notMem.mp hpre x hx
  have hπ : Continuous (Manifold.blowUpπ ψ₀ hZ) := (isBlowUp_blowUpπ ψ₀ hZ).contMDiff.continuous
  have hold : ∀ c, c < Φ.nextComp →
      ⇑ℓ ⁻¹' (Φ.blowUpPieces S m hZ).piece c = ⇑ρ ⁻¹' Φ.piece c := by
    intro c hc
    rw [Φ.blowUpPieces_piece_of_lt S m hZ hc]
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro hx
      have hx' := strictTransform_subset_preimage (Y := Φ.centerOf S) hπ (Φ.isClosed_piece c) hx
      rw [Set.mem_preimage, hsq] at hx'
      exact hx'
    · intro hx
      refine subset_closure ?_
      rw [Set.mem_preimage, hsq]
      exact ⟨hx, hnot x⟩
  have hnew : ∀ P ∈ S, ⇑ℓ ⁻¹' (Φ.blowUpPieces S m hZ).piece (Φ.newComp S P) = ∅ := by
    intro P hP
    rw [Φ.blowUpPieces_piece_newComp S m hZ hP]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    rw [Set.mem_preimage, Set.mem_preimage, hsq] at hx
    exact hnot x (Φ.faceSet_subset_centerOf hP hx)
  refine
    { p_lt := fun c hc => (h.p_lt c hc).trans_le (Nat.le_add_right _ _)
      σ_lt := fun l hl => (h.σ_lt l hl).trans (Nat.lt_succ_self _)
      σ_strictMonoOn := h.σ_strictMonoOn
      label_eq := fun c hc => by
        rw [Φ.blowUpPieces_label_of_lt S m hZ (h.p_lt c hc)]
        exact h.label_eq c hc
      a_eq := fun c hc => by
        rw [Φ.blowUpPieces_a_of_lt S m hZ (h.p_lt c hc)]
        exact h.a_eq c hc
      piece_subset := fun c hc => by
        rw [hold (p c) (h.p_lt c hc)]
        exact h.piece_subset c hc
      preimage_eq := fun c hc => ?_
      disjoint := h.disjoint }
  by_cases hlt : c < Φ.nextComp
  · rw [hold c hlt]
    exact h.preimage_eq c hlt
  · obtain ⟨P, hP, rfl⟩ := Φ.exists_newComp_eq S (not_lt.mp hlt) hc
    rw [hnew P hP]
    refine (Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_).symm
    obtain ⟨c', hc', -⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hc'r, hc'p⟩ := Finset.mem_filter.mp hc'
    have hlt' := h.p_lt c' (Finset.mem_range.mp hc'r)
    rw [hc'p] at hlt'
    exact absurd hlt' (not_lt.mpr (Φ.nextComp_le_newComp' S P))

/-- `RefinesAlong.blowUpPieces` with the codimension of the centre of `Ψ` given by an equation. -/
theorem blowUpPieces' (S : Finset (Finset ℕ)) (hS : ∀ P ∈ S, P ∈ Φ.nerve) (m : ℕ) {r r' : ℕ}
    (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r)
    (hZ' : IsClosedSubmanifold ψ₀ (Ψ.centerOf (Ψ.preimageFaces p S)) r') (hr : r' = r)
    (ℓ : AnalyticMap (Manifold.blowUp ψ₀ hZ') (Manifold.blowUp ψ₀ hZ))
        (hℓ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ℓ)
    (hsq : ∀ q, Manifold.blowUpπ ψ₀ hZ (ℓ q) = ρ (Manifold.blowUpπ ψ₀ hZ' q)) :
    (Ψ.blowUpPieces (Ψ.preimageFaces p S) m hZ').RefinesAlong ℓ
      (Ψ.extendParent Φ p (Ψ.preimageFaces p S) S) (Ψ.extendLabel Φ σ) (Φ.blowUpPieces S m hZ) := by
  subst hr
  exact h.blowUpPieces S hS m hZ hZ' ℓ hℓ hsq

end RefinesAlong

/-! ### The realisation of equal lists -/

/-- The realisation depends on the list of centres, not on the smoothness proof. -/
theorem realizeAux_congr {X : AnalyticManifold.{u} 𝕜 E} (Ψ : PieceFamily X) (m : ℕ)
    {L₁ L₂ : List (Finset (Finset ℕ))} (e : L₁ = L₂) (h₁ : SmoothCenters ψ₀ Ψ m L₁) :
    realizeAux ψ₀ Ψ m L₁ h₁ = realizeAux ψ₀ Ψ m L₂ (e ▸ h₁) := by
  subst e
  rfl

/-- `realizeAux_congr` with both smoothness proofs given. -/
theorem realizeAux_congr' {X : AnalyticManifold.{u} 𝕜 E} (Ψ : PieceFamily X) (m : ℕ)
    {L₁ L₂ : List (Finset (Finset ℕ))} (e : L₁ = L₂) (h₁ : SmoothCenters ψ₀ Ψ m L₁)
    (h₂ : SmoothCenters ψ₀ Ψ m L₂) : realizeAux ψ₀ Ψ m L₁ h₁ = realizeAux ψ₀ Ψ m L₂ h₂ := by
  subst e
  rfl

/-! ### The induction along the run -/

/-- The induction along a run `L` of the state of `Φ`: for `Ψ` refining `Φ` along `ρ` and a shadow
state `D` carrying the pieces and nerve of `Ψ`, the realisation on `Ψ` of the run with skips is the
pull-back of the realisation on `Φ` with its empty blow-ups erased. -/
theorem realizeAux_pullback_eraseEmpty (L : List (Finset (Finset ℕ))) :
    ∀ {X Y : AnalyticManifold.{u} 𝕜 E} (Φ : PieceFamily Y) {F : HypersurfaceFamily Y}
      {e : Fin Φ.nextLabel ↪o F.ι}, F.IsSnc ψ₀ → Φ.Realizes F e →
      ∀ {m : ℕ} (hV : Φ.IsValid n m) {st' : MonomialState},
      MonomialState.IsRun (Φ.toState n m hV) L st' →
      ∀ (Ψ : PieceFamily X) {F' : HypersurfaceFamily X} {e' : Fin Ψ.nextLabel ↪o F'.ι},
      F'.IsSnc ψ₀ → Ψ.Realizes F' e' → Ψ.IsValid n m → ∀ (ρ : AnalyticMap X Y)
      (hρ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ) {p σ : ℕ → ℕ}, Ψ.RefinesAlong ρ p σ Φ →
      ∀ (D : MonomialState), D.nextComp = Ψ.nextComp → D.nerve = Ψ.nerve →
      ∀ (hL : SmoothCenters ψ₀ Φ m L)
        (hL' : SmoothCenters ψ₀ Ψ m (MonomialState.chainRunE p D (Φ.toState n m hV) L)),
      realizeAux ψ₀ Ψ m _ hL' = ((realizeAux ψ₀ Φ m L hL).pullback ρ hρ).eraseEmpty := by
  induction L with
  | nil =>
    intro X Y Φ F e _ _ m hV st' _ Ψ F' e' _ _ hVΨ ρ hρ p σ _ D _ _ hL hL'
    rfl
  | cons S L ih =>
    intro X Y Φ F e hF hΦ m hV st' hrun Ψ F' e' hF' hΨ hVΨ ρ hρ p σ h D hnc hnv hL hL'
    cases hrun with
    | cons r hr hrn hne hL₀ =>
      -- the data at the next stage on `Y`
      set N := Φ.toState n m hV with hNdef
      have hS : N.IsCenter (N.choice r) := N.isCenter_choice r
      have hSn : ∀ P ∈ N.choice r, P ∈ Φ.nerve := fun P hP => hS.1 hP
      have hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf (N.choice r)) (faceCard (N.choice r)) :=
        hL.head
      have hF₁ : (F.totalTransform (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf (N.choice r))).IsSnc ψ₀ :=
        HypersurfaceFamily.isSnc_totalTransform hZ (isBlowUp_blowUpπ ψ₀ hZ) hF
          (hΦ.hasSncWith_centerOf hF hS)
      have hΦ₁ := hΦ.realizes_blowUpPieces hS hZ
      have hV₁ : (Φ.blowUpPieces (N.choice r) m hZ).IsValid n m := hΦ.valid_blowUpPieces hF hS hZ
      have hst₁ : (Φ.blowUpPieces (N.choice r) m hZ).toState n m hV₁ = N.blowUp (N.choice r) :=
        hΦ.toState_blowUpPieces hF hS hZ hV₁
      have hrun₁ : MonomialState.IsRun ((Φ.blowUpPieces (N.choice r) m hZ).toState n m hV₁) L
          st' := by
        rw [hst₁]
        exact hL₀
      -- the faces of `Ψ` over the centre
      have hfil : (D.nerve.filter fun Q => Q.image p ∈ N.choice r) =
          Ψ.preimageFaces p (N.choice r) := by
        ext Q
        rw [Finset.mem_filter, hnv, mem_preimageFaces]
      have hZeq : Ψ.centerOf (Ψ.preimageFaces p (N.choice r)) = ⇑ρ ⁻¹' Φ.centerOf (N.choice r) :=
        (h.preimage_centerOf _ hSn).symm
      by_cases hemp : Ψ.preimageFaces p (N.choice r) = ∅
      · -- the EMPTY step: `Ψ` is untouched, the pulled-back cell is erased
        have hpre : ⇑ρ ⁻¹' Φ.centerOf (N.choice r) = ∅ := by
          rw [← hZeq, hemp, centerOf_empty]
        have hno : ∀ Q ∈ Ψ.nerve, Q.image p ∉ N.choice r := fun Q hQ hQS =>
          Finset.notMem_empty Q (hemp ▸ mem_preimageFaces.mpr ⟨hQ, hQS⟩)
        have hfil0 : (D.nerve.filter fun Q => Q.image p ∈ N.choice r) = ∅ := hfil.trans hemp
        have hρ₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
            ((AnalyticManifold.BlowUpSequence.liftStep ρ hρ hZ).comp (Diffeomorph.toAnalyticMap
              (AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph
                  (hZ.preimage_of_isLocalDiffeomorph hρ)
                hpre).symm)) :=
          AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
              (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep ρ hρ hZ)
            (AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph _ hpre).symm.isLocalDiffeomorph
        have hsq₁ : ∀ x, Manifold.blowUpπ ψ₀ hZ ((AnalyticManifold.BlowUpSequence.liftStep ρ hρ
            hZ).comp
            (Diffeomorph.toAnalyticMap (AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph
              (hZ.preimage_of_isLocalDiffeomorph hρ) hpre).symm) x) = ρ x := fun x => by
          change Manifold.blowUpπ ψ₀ hZ (AnalyticManifold.BlowUpSequence.liftStep ρ hρ hZ
            ((AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph
                (hZ.preimage_of_isLocalDiffeomorph hρ) hpre).symm
              x)) = ρ x
          rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep,
              ← AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph_apply
            (hZ.preimage_of_isLocalDiffeomorph hρ) hpre, Diffeomorph.apply_symm_apply]
        have h₁ := h.of_empty_step _ hSn hno m hZ _ hsq₁
        have hlist : MonomialState.chainRunE p D N (N.choice r :: L) =
            MonomialState.chainRunE p D ((Φ.blowUpPieces (N.choice r) m hZ).toState n m hV₁) L := by
          rw [MonomialState.chainRunE_cons_of_eq_empty _ _ _ _ hfil0, hst₁]
        rw [realizeAux_congr Ψ m hlist hL',
          ih (Φ.blowUpPieces (N.choice r) m hZ) hF₁ hΦ₁ hV₁ hrun₁ Ψ hF' hΨ hVΨ _ hρ₁ h₁ D hnc hnv
            hL.tail _]
        change _ = ((AnalyticManifold.BlowUpSequence.cons hZ
          (realizeAux ψ₀ (Φ.blowUpPieces (N.choice r) m hZ) m L hL.tail)).pullback ρ hρ).eraseEmpty
        rw [AnalyticManifold.BlowUpSequence.pullback_cons,
            AnalyticManifold.BlowUpSequence.eraseEmpty_cons_of_eq_empty _ _ hpre,
          AnalyticManifold.BlowUpSequence.map_eq_pullback_symm,
              AnalyticManifold.BlowUpSequence.eraseEmpty_pullback _ _ _
            (AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph _ hpre).symm.toEquiv.surjective,
          AnalyticManifold.BlowUpSequence.pullback_comp]
      · -- the SHARED step: both sides blow up the same centre
        have hne' : (Ψ.preimageFaces p (N.choice r)).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hemp
        have hfilne : (D.nerve.filter fun Q => Q.image p ∈ N.choice r) ≠ ∅ := hfil.trans_ne hemp
        have hS' : (Ψ.toState n m hVΨ).IsCenter (Ψ.preimageFaces p (N.choice r)) :=
          h.isCenter_preimageFaces hVΨ hV _ hS
        have hcard : faceCard (Ψ.preimageFaces p (N.choice r)) = faceCard (N.choice r) :=
          h.faceCard_preimageFaces hΦ hS hne'
        have hlist : MonomialState.chainRunE p D N (N.choice r :: L) =
            Ψ.preimageFaces p (N.choice r) :: MonomialState.chainRunE
              (Ψ.extendParent Φ p (Ψ.preimageFaces p (N.choice r)) (N.choice r))
              (D.blowUp (Ψ.preimageFaces p (N.choice r)))
              ((Φ.blowUpPieces (N.choice r) m hZ).toState n m hV₁) L := by
          rw [MonomialState.chainRunE_cons_of_ne_empty _ _ _ _ hfilne, hfil,
            extendComp_eq_extendParent Ψ Φ p D hnc hV, hst₁]
        have hL'' : SmoothCenters ψ₀ Ψ m (Ψ.preimageFaces p (N.choice r) ::
            MonomialState.chainRunE
              (Ψ.extendParent Φ p (Ψ.preimageFaces p (N.choice r)) (N.choice r))
              (D.blowUp (Ψ.preimageFaces p (N.choice r)))
              ((Φ.blowUpPieces (N.choice r) m hZ).toState n m hV₁) L) := hlist ▸ hL'
        rw [realizeAux_congr' Ψ m hlist hL' hL'']
        have hpre_ne : ⇑ρ ⁻¹' Φ.centerOf (N.choice r) ≠ ∅ := by
          rw [← hZeq]
          exact (centerOf_nonempty hS' hne').ne_empty
        change AnalyticManifold.BlowUpSequence.cons hL''.head
            (realizeAux ψ₀ (Ψ.blowUpPieces _ m hL''.head) m _ hL''.tail) =
          ((AnalyticManifold.BlowUpSequence.cons hZ
            (realizeAux ψ₀ (Φ.blowUpPieces (N.choice r) m hZ) m L hL.tail)).pullback ρ
            hρ).eraseEmpty
        rw [AnalyticManifold.BlowUpSequence.pullback_cons,
            AnalyticManifold.BlowUpSequence.eraseEmpty_cons_of_ne_empty _ _ hpre_ne]
        -- the lift, transported to `Ψ`'s own centre
        have hρ₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (AnalyticMap.castDom
            (AnalyticManifold.BlowUpSequence.blowUp_congr' hZeq hcard hL''.head
                (hZ.preimage_of_isLocalDiffeomorph hρ))
            (AnalyticManifold.BlowUpSequence.liftStep ρ hρ hZ)) :=
          AnalyticMap.isLocalDiffeomorph_castDom _
              (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep ρ hρ hZ)
        have hsq₁ : ∀ q, Manifold.blowUpπ ψ₀ hZ (AnalyticMap.castDom
            (AnalyticManifold.BlowUpSequence.blowUp_congr' hZeq hcard hL''.head
                (hZ.preimage_of_isLocalDiffeomorph hρ))
            (AnalyticManifold.BlowUpSequence.liftStep ρ hρ hZ) q) = ρ
                (Manifold.blowUpπ ψ₀ hL''.head q) := fun q =>
          AnalyticManifold.BlowUpSequence.blowUpπ_castDom_liftStep' ρ hρ hZ hL''.head hZeq hcard q
        have h₁ := h.blowUpPieces' _ hSn m hZ hL''.head hcard _ hρ₁ hsq₁
        have hF'₁ : (F'.totalTransform (Manifold.blowUpπ ψ₀ hL''.head)
            (Ψ.centerOf (Ψ.preimageFaces p (N.choice r)))).IsSnc ψ₀ :=
          HypersurfaceFamily.isSnc_totalTransform hL''.head (isBlowUp_blowUpπ ψ₀ hL''.head) hF'
            (hΨ.hasSncWith_centerOf hF' hS')
        have hΨ₁ := hΨ.realizes_blowUpPieces hS' hL''.head
        have hVΨ₁ := hΨ.valid_blowUpPieces hF' hS' hL''.head
        have hnc₁ : (D.blowUp (Ψ.preimageFaces p (N.choice r))).nextComp =
            (Ψ.blowUpPieces _ m hL''.head).nextComp := by
          simp only [MonomialState.blowUp_nextComp, blowUpPieces_nextComp, hnc]
        have hnv₁ : (D.blowUp (Ψ.preimageFaces p (N.choice r))).nerve =
            (Ψ.blowUpPieces _ m hL''.head).nerve := by
          rw [MonomialState.blowUp_nerve, hΨ.nerve_blowUpPieces hF' hS' hL''.head, hnv]
          congr 1
          funext P
          simp only [MonomialState.newComp, newComp, hnc]
        have hIH := ih (Φ.blowUpPieces (N.choice r) m hZ) hF₁ hΦ₁ hV₁ hrun₁
          (Ψ.blowUpPieces _ m hL''.head) hF'₁ hΨ₁ hVΨ₁ _ hρ₁ h₁ _ hnc₁ hnv₁ hL.tail hL''.tail
        refine AnalyticManifold.BlowUpSequence.cons_congr_heq_of_eq hZeq hcard hL''.head _ _ _ ?_
        rw [hIH]
        exact AnalyticManifold.BlowUpSequence.eraseEmpty_heq
            (AnalyticManifold.BlowUpSequence.blowUp_congr' hZeq hcard hL''.head _) _ _
          (AnalyticManifold.BlowUpSequence.pullback_castDom_heq _ _ _ _)

/-! ### The pull-back of the run -/

/-- The run of the monomial procedure on a refining family is the pull-back of the run, with its
empty blow-ups erased ([Kol07, 34.1], [Kol07, 32]). The statement holds for any boundary family
realised by `Ψ`: the run depends on the pieces, their exponents and the order of the labels alone.
-/
theorem RefinesAlong.realize_pullback_eraseEmpty {F : HypersurfaceFamily Y}
    {e : Fin Φ.nextLabel ↪o F.ι} (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e) {m : ℕ}
    (hVΦ : Φ.IsValid n m) {F' : HypersurfaceFamily X} {e' : Fin Ψ.nextLabel ↪o F'.ι}
    (hF' : F'.IsSnc ψ₀) (hΨ : Ψ.Realizes F' e') (hVΨ : Ψ.IsValid n m)
    (hρ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ) (h : Ψ.RefinesAlong ρ p σ Φ) :
    Ψ.realize hF' hΨ hVΨ = ((Φ.realize hF hΦ hVΦ).pullback ρ hρ).eraseEmpty := by
  have hVσ : (Ψ.relabel σ Φ.nextLabel h.σ_lt).IsValid n m :=
    Ψ.isValid_relabel σ Φ.nextLabel h.σ_lt h.σ_strictMonoOn.injOn hVΨ
  have hrel := rel_toState_relabel h hVΨ hVσ
  have href := refines_toState_relabel h hVσ hVΦ
  have hsub := Φ.sub_toState_pullbackFamily ρ hVΦ
  obtain ⟨-, hrun⟩ :=
    MonomialState.step3_chainE href (MonomialState.Rel.refl _) hsub fun _ _ => rfl
  have hR := MonomialState.step3_snd_eq_of_rel_id hrel rfl
  unfold realize
  rw [realizeAux_congr Ψ m (hR.trans hrun)]
  exact realizeAux_pullback_eraseEmpty _ Φ hF hΦ hVΦ (MonomialState.step3_isRun _) Ψ hF' hΨ hVΨ ρ
    hρ h _ rfl (Ψ.nerve_relabel σ Φ.nextLabel h.σ_lt) _ _

/-- Along a surjective local analytic isomorphism the run of a refining family is the pull-back of
the run step for step, no blow-up being empty. -/
theorem RefinesAlong.realize_pullback_of_surjective {F : HypersurfaceFamily Y}
    {e : Fin Φ.nextLabel ↪o F.ι} (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e) {m : ℕ}
    (hVΦ : Φ.IsValid n m) {F' : HypersurfaceFamily X} {e' : Fin Ψ.nextLabel ↪o F'.ι}
    (hF' : F'.IsSnc ψ₀) (hΨ : Ψ.Realizes F' e') (hVΨ : Ψ.IsValid n m)
    (hρ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ) (hs : Function.Surjective ρ)
    (h : Ψ.RefinesAlong ρ p σ Φ) :
    Ψ.realize hF' hΨ hVΨ = (Φ.realize hF hΦ hVΦ).pullback ρ hρ := by
  rw [h.realize_pullback_eraseEmpty hF hΦ hVΦ hF' hΨ hVΨ hρ]
  exact AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_of_surjective _
      (Φ.realize_noEmptyCenters hF hΦ hVΦ) ρ hρ hs

end PieceFamily

end Hironaka.Manifold.BMO
