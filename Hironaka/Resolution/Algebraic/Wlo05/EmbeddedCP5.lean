/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.StrictTransformSupport
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SncPreimageSingular
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedBridge
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Remaining
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3EraseEmpty
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Tower
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4Sheaf
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Isolation
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6LoopTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Tools
import Hironaka.Resolution.Algebraic.Wlo05.OffCentreTransport
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.FlatColon
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Hironaka.Scheme.BlowUpSequence.TakeLast
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.HasSncWith
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP5: the protected state through the run, the truncations, the isolations and the loop

The statement CP5 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`): once a component is absorbed and
isolated, the loop keeps its strict transform `Γ̃` smooth, integral, snc with the boundary and off
the other members, and keeps the isolated ideal in the K-shape along it; at the end the isolated
ideal is trivial near `Γ̃_end`.

* The round (`protectedData_seq`, `protectedData_blowUp`): along a smooth sequence of order `≥ 1`
  whose centres are classified at their points (CP3, `cp3For_bmoOneRun`), each blow-up is along an
  admissible chain stratum at the points of `Γ̃` (`admissibleChainStratumKAt_of_centerClassifiedAt`,
  the K-shape read in its own chain coordinates), so CP4 (`chainRelativeKAt_strictTransform`) gives
  the snc and the K-shape after the blow-up; the strict transform stays integral because an
  admissible stratum never contains `Γ̃` (`not_le_of_admissibleChainStratumKAt`: the condition (★)
  forces a member's coordinate into the ideal of the stratum, which the span of the chain does not
  contain) and stays off the strict transforms of the members
  (`disjoint_strictTransform_support_of_disjoint`).
* The truncation (`protectedState_stageTriple`) reads the data of the run at the stage `n` on the
  truncated run (`stage_take_last` and the casts of the truncation); the classification of the
  centres of a run on a protected state (`admissibleChainStratumKAt_center_of_protectedState`) is
  CP3 at a stage.
* The isolation (`protectedState_isolatedTriple`): the strict transforms of the absorbed members
  miss `Γ̃`, so the colon by their reduced ideal has the stalk of `K` at every point of `Γ̃`
  (`stalkIdeal_isolatedTriple_I_eq_of_protectedState`, `stalkIdeal_colon_eq_of_notMem_support`).
* The last round (`stalkIdeal_markedTransformSeq_bmoOneRun_last_eq_top`, [Kol07, Theorem 69 (1)]):
  the untruncated run ends with `max-ord < 1`, the unit ideal at every point (the stalk form of
  `markedTransformSeq_bmoOneRun_last_eq_top`).
* The loop (`protected_bedAux`): strong induction on the number of members along `bedAux`
  (`bedAux_of_exists`, `bedAux_of_not_exists`); the data of the concatenation are read through the
  casts (`last_concat`, `strictTransformSeq_concat_last_heq`, `composite_concat`), and the
  transform of the ideal of the state along the rest of the loop agrees with that of the isolated
  ideal at the points of `Γ̃` (`stalkIdeal_markedTransformSeq_eq_of_forall_stalkIdeal_eq`, the
  locality of the marked transform iterated).

This is the isolation passage of the proof of [Wlo05, Theorem 4.7.1] ("ignoring these isolated
components"), proved from CP3 and CP4 in place of Włodarczyk's invariant; the argument is not in
the literature. Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCPBridge`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme Hironaka BlowUpSequence Hironaka.Sequence Hironaka.Stage

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

section Cast

variable {Y Y' : Scheme.{u}}

/-- Smoothness of a closed subscheme over a base transports across a cast of the ambient scheme,
the structure map carried whole. -/
theorem smooth_subschemeι_comp_of_heq_map (h : Y = Y') {Γ : Y.IdealSheafData}
    {Γ' : Y'.IdealSheafData} (hΓ : HEq Γ Γ') {W : Scheme.{u}} {g : Y ⟶ W} {g' : Y' ⟶ W}
    (hg : HEq g g') (hs : Smooth (Γ'.subschemeι ≫ g')) : Smooth (Γ.subschemeι ≫ g) := by
  subst h
  rw [eq_of_heq hΓ, eq_of_heq hg]
  exact hs

/-- "The unit stalk at every point of a closed subscheme" transports across a cast. -/
theorem forall_stalkIdeal_eq_top_of_heq (h : Y = Y') {Γ M : Y.IdealSheafData}
    {Γ' M' : Y'.IdealSheafData} (hΓ : HEq Γ Γ') (hM : HEq M M')
    (hs : ∀ p ∈ Γ'.support, M'.stalkIdeal p = ⊤) : ∀ p ∈ Γ.support, M.stalkIdeal p = ⊤ := by
  subst h
  rw [eq_of_heq hΓ, eq_of_heq hM]
  exact hs

/-- A cast composed with a morphism is heterogeneously the morphism. -/
theorem heq_eqToHom_comp {Z : Scheme.{u}} (e : Y = Y') (φ : Y' ⟶ Z) : HEq (eqToHom e ≫ φ) φ := by
  subst e
  rw [eqToHom_refl, Category.id_comp]

end Cast

/-! ### The one-blow-up step and the run -/

/-- At a point of the centre on the protected component, the classification of the centre (CP3) in
the chain coordinates of the K-shape is admissibility. -/
theorem admissibleChainStratumKAt_of_centerClassifiedAt {E : DivisorFamily X}
    {K Γ Z : X.IdealSheafData} {p : X} (hK : ChainRelativeKAt E K Γ p)
    (hcl : CenterClassifiedAt E K Z p) : AdmissibleChainStratumKAt E K Γ Z p := by
  obtain ⟨n, z, c, r, σ, a, b, hcc, hb, hKp⟩ := hK
  exact admissibleChainStratumKAt_of_stratumIn hcc hb hKp
    ((hcl z c σ a b (chainCoords_iff_free.mp hcc).1 hb).1 hKp)

/-- An admissible chain stratum at a point of `Γ` does not contain `Γ` (as ideal sheaves): the
condition (★) puts a member's coordinate `z k`, `k ∈ s`, into its stalk, and that coordinate lies
outside the span of the chain. -/
theorem not_le_of_admissibleChainStratumKAt {E : DivisorFamily X} {K Γ Z : X.IdealSheafData} {p : X}
    [IsRegularLocalRing (X.presheaf.stalk p)] (h : AdmissibleChainStratumKAt E K Γ Z p) :
    ¬ Z ≤ Γ := by
  classical
  intro hle
  obtain ⟨n, z, c, r, σ, a, b, l, hl, s, hcc, hb, hK, hsC, hZ, h0, hpos⟩ := h
  have hle' : Z.stalkIdeal p ≤ Γ.stalkIdeal p := stalkIdeal_mono hle p
  obtain ⟨k, hks⟩ : ∃ k, k ∈ s := by
    rcases Nat.eq_zero_or_pos l with hl0 | hl0
    · obtain ⟨k, hk, -⟩ := h0 hl0
      exact ⟨k, hk⟩
    · obtain ⟨k, hk, -⟩ := hpos hl0
      exact ⟨k, hk⟩
  have hkZ : z k ∈ Z.stalkIdeal p := by
    rw [hZ]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, Finset.mem_coe.mpr hks, rfl⟩)
  have hkΓ : z k ∈ Ideal.span (z '' ↑(Finset.univ.image σ)) := by
    have h1 := hle' hkZ
    rw [hcc.2.2.2.2.2.2] at h1
    rwa [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Set.range_comp]
  refine notMem_span_image_of_notMem hcc.1.1.symm hcc.1.2 ?_ hkΓ
  intro hk
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hk
  obtain ⟨j, rfl⟩ := hsC (Finset.mem_coe.mpr hks)
  exact hcc.2.2.2.2.1 i j hi

variable {k : Type u} [Field k] [CharZero k]

/-- **One blow-up of a protected state** (CP3 with CP4): along the blow-up of a centre classified
at each of its points, the strict transform of `Γ` stays snc with the boundary, integral and
disjoint from the strict transforms of the members, and the transform of `K` keeps the K-shape
along it. -/
theorem protectedData_blowUp (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (E : DivisorFamily X) (K Γ Z : X.IdealSheafData) (C : Set X.IdealSheafData) (hE : E.IsSnc)
    (hΓ : E.HasSncWith Γ) (hint : IsIntegral Γ.subscheme)
    (hdisj : ∀ c ∈ C, Disjoint c.support Γ.support)
    (hK : ∀ p ∈ Γ.support, ChainRelativeKAt E K Γ p)
    (hcl : ∀ q ∈ Z.support, CenterClassifiedAt E K Z q) :
    (E.totalTransform Z).HasSncWith (Γ.strictTransform Z) ∧
      IsIntegral (Γ.strictTransform Z).subscheme ∧
      (∀ c ∈ C, Disjoint (c.strictTransform Z).support (Γ.strictTransform Z).support) ∧
      ∀ q ∈ (Γ.strictTransform Z).support,
        ChainRelativeKAt (E.totalTransform Z) (K.markedTransform Z 1) (Γ.strictTransform Z) q := by
  have := f.isLocallyNoetherian_of_field
  have hPF : PerfectField k := PerfectField.ofCharZero
  have hZ : ∀ p ∈ Z.support ⊓ Γ.support, AdmissibleChainStratumKAt E K Γ Z p := fun p hp =>
    admissibleChainStratumKAt_of_centerClassifiedAt (hK p hp.2) (hcl p hp.1)
  obtain ⟨-, hsnc, hchain⟩ :=
    chainRelativeKAt_strictTransform f E K Γ Z hE hΓ (HasSncWith.smooth f hΓ) hK hZ
  refine ⟨hsnc, ?_, fun c hc => disjoint_strictTransform_support_of_disjoint Z c Γ (hdisj c hc),
    hchain⟩
  have hnot : ¬ Z ≤ Γ := by
    obtain ⟨η, hη⟩ := exists_isGenericPoint_support Γ
    intro hle
    have hηΓ : η ∈ Γ.support := hη.mem
    have hreg := isRegularLocalRing_stalk f η
    exact not_le_of_admissibleChainStratumKAt (hZ η ⟨support_antitone hle hηΓ, hηΓ⟩) hle
  exact isIntegral_strictTransform_subscheme Z Γ hnot

/-- **The protected data along a run**, stage by stage: along a smooth sequence of order `≥ 1` for
`(K, 1)` whose centres are classified at each of their points (CP3), from a protected input — `Γ`
snc with the boundary, integral, disjoint from the members `C`, `K` in the K-shape along it — the
strict transform of `Γ` at every stage is snc with the total transform of the boundary, integral
and disjoint from the strict transforms of the members, and the mark-`1` transform of `K` keeps
the K-shape along it. -/
theorem protectedData_seq : ∀ {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (S : BlowUpSequence X) (E : DivisorFamily X) (K Γ : X.IdealSheafData)
    (C : Set X.IdealSheafData), S.IsOrderGeSeq f K 1 E → CP3For S K E → E.IsSnc →
    E.HasSncWith Γ → IsIntegral Γ.subscheme → (∀ c ∈ C, Disjoint c.support Γ.support) →
    (∀ p ∈ Γ.support, ChainRelativeKAt E K Γ p) → ∀ i : Fin (S.length + 1),
    (S.totalTransformSeq E i).HasSncWith (S.strictTransformSeq Γ i) ∧
      IsIntegral (S.strictTransformSeq Γ i).subscheme ∧
      (∀ c ∈ C, Disjoint (S.strictTransformSeq c i).support (S.strictTransformSeq Γ i).support) ∧
      ∀ p ∈ (S.strictTransformSeq Γ i).support,
        ChainRelativeKAt (S.totalTransformSeq E i) (S.markedTransformSeq K 1 i)
          (S.strictTransformSeq Γ i) p
  | _, _, _, _, nil _, _, _, _, _, _, _, _, hΓ, hint, hdisj, hK, _ => ⟨hΓ, hint, hdisj, hK⟩
  | _, _, _, _, cons _ _ _, _, _, _, _, _, _, _, hΓ, hint, hdisj, hK, ⟨0, _⟩ =>
    ⟨hΓ, hint, hdisj, hK⟩
  | X, f, n, _, cons _ D rest, E, K, Γ, C, hS, hcp3, hE, hΓ, hint, hdisj, hK, ⟨j + 1, h⟩ => by
    have := isLocallyNoetherian_of_smoothOfRelativeDimension f n
    obtain ⟨⟨hD, hsnc, -⟩, ht⟩ := (isOrderGeSeq_cons_iff f K E 1 D rest).1 hS
    obtain ⟨h0, hr⟩ := (cp3For_cons_iff D rest K E).1 hcp3
    have hPF : PerfectField k := PerfectField.ofCharZero
    have hsmf : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have hLN' : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
    have hE' : (E.totalTransform D).IsSnc := totalTransform_isSnc f E D hE hsnc
    obtain ⟨hΓ', hint', hdisj', hK'⟩ := protectedData_blowUp f E K Γ D C hE hΓ hint hdisj hK h0
    have hdisj'' : ∀ c' ∈ (·.strictTransform D) '' C,
        Disjoint c'.support (Γ.strictTransform D).support := by
      rintro c' ⟨c, hc, rfl⟩
      exact hdisj' c hc
    obtain ⟨h1, h2, h3, h4⟩ := protectedData_seq (D.blowUpπ ≫ f) n rest
        (E.totalTransform D)
      (K.markedTransform D 1) (Γ.strictTransform D) ((·.strictTransform D) '' C) ht hr hE' hΓ' hint'
      hdisj'' hK' ⟨j, Nat.lt_of_succ_lt_succ h⟩
    exact ⟨h1, h2, fun c hc => h3 _ ⟨c, hc, rfl⟩, h4⟩

/-- The locality of the marked transform iterated: two ideals with the same stalks at every point
of `Γ` have mark-`1` transforms with the same stalks at every point of the strict transform of
`Γ`, at every stage (the strict transform lies over `Γ`; the stalk of the transform at a point
depends only on the stalk of the ideal at its image). -/
theorem stalkIdeal_markedTransformSeq_eq_of_forall_stalkIdeal_eq : ∀ {X : Scheme.{u}}
    [IsLocallyNoetherian X] (S : BlowUpSequence X) (I K Γ : X.IdealSheafData),
    (∀ p ∈ Γ.support, I.stalkIdeal p = K.stalkIdeal p) → ∀ (i : Fin (S.length + 1)) (q : S.stage i),
    q ∈ (S.strictTransformSeq Γ i).support →
    (S.markedTransformSeq I 1 i).stalkIdeal q = (S.markedTransformSeq K 1 i).stalkIdeal q
  | _, _, nil _, _, _, _, h, _, q, hq => h q hq
  | _, _, cons _ _ _, _, _, _, h, ⟨0, _⟩, q, hq => h q hq
  | _, _, cons X D rest, I, K, Γ, h, ⟨j + 1, hj⟩, q, hq => by
    have hLN' : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
    exact stalkIdeal_markedTransformSeq_eq_of_forall_stalkIdeal_eq rest (I.markedTransform D 1)
      (K.markedTransform D 1) (Γ.strictTransform D)
      (fun q' hq' => stalkIdeal_markedTransform_eq_of_stalkIdeal_eq D I K 1
        (h _ (blowUpπ_mem_support_of_mem_support_strictTransform D Γ hq')))
      ⟨j, Nat.lt_of_succ_lt_succ hj⟩ q hq

/-! ### The protected state along the loop -/

section Loop

variable (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData)
  (Γ : T.X.left.IdealSheafData)

/-- The data of the run at every stage of `bmoOneRun`, from a protected state: `protectedData_seq`
with `cp3For_bmoOneRun`. -/
theorem protectedData_bmoOneRun (hP : ProtectedState T C Γ)
    (i : Fin ((bmoOneRun T hm).length + 1)) :
    ((bmoOneRun T hm).totalTransformSeq T.E i).HasSncWith
        ((bmoOneRun T hm).strictTransformSeq Γ i) ∧
      IsIntegral ((bmoOneRun T hm).strictTransformSeq Γ i).subscheme ∧
      (∀ c ∈ C, Disjoint ((bmoOneRun T hm).strictTransformSeq c i).support
        ((bmoOneRun T hm).strictTransformSeq Γ i).support) ∧
      ∀ p ∈ ((bmoOneRun T hm).strictTransformSeq Γ i).support,
        ChainRelativeKAt ((bmoOneRun T hm).totalTransformSeq T.E i)
          ((bmoOneRun T hm).markedTransformSeq T.I 1 i) ((bmoOneRun T hm).strictTransformSeq Γ i)
          p := by
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  have hsmd : SmoothOfRelativeDimension d (T.X.left ↘ Spec (.of k)) := hd
  have hrun : (bmoOneRun T hm).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E := by
    have h0 := isOrderGeSeq_bmoOneRun T hm
    rwa [hm] at h0
  exact protectedData_seq (T.X.left ↘ Spec (.of k)) d (bmoOneRun T hm) T.E T.I Γ (↑C) hrun
    (cp3For_bmoOneRun T hm) T.isSnc hP.snc hP.integral (fun c hc => hP.disjoint c hc) hP.chain i

/-- **The centres of a run on a protected state are admissible chain strata** (CP3 at a stage):
every centre meeting the protected component is an ADMISSIBLE chain stratum for the isolated ideal
of the run — the stratum, the K-shape and (★) in shared chain coordinates. -/
theorem admissibleChainStratumKAt_center_of_protectedState (hP : ProtectedState T C Γ)
    (i : Fin (bmoOneRun T hm).length) :
    ∀ p ∈ ((bmoOneRun T hm).center i).support ⊓
        ((bmoOneRun T hm).strictTransformSeq Γ i.castSucc).support,
      AdmissibleChainStratumKAt ((bmoOneRun T hm).totalTransformSeq T.E i.castSucc)
        ((bmoOneRun T hm).markedTransformSeq T.I 1 i.castSucc)
        ((bmoOneRun T hm).strictTransformSeq Γ i.castSucc) ((bmoOneRun T hm).center i) p := by
  intro p hp
  exact admissibleChainStratumKAt_of_centerClassifiedAt
    ((protectedData_bmoOneRun T hm C Γ hP i.castSucc).2.2.2 p hp.2)
    (cp3For_bmoOneRun T hm i p hp.1)

/-- **The round lemma** (CP3 with CP4): the protected state persists along the run truncated
anywhere (the isolation passage of the proof of [Wlo05, Theorem 4.7.1]). -/
theorem protectedState_stageTriple (hP : ProtectedState T C Γ) (n : ℕ)
    (hn : n ≤ (bmoOneRun T hm).length) :
    ProtectedState (stageTriple T hm n) (transportedComponents T hm C n)
      (((bmoOneRun T hm).take n).strictTransformSeq Γ (Fin.last _)) := by
  classical
  have hPF : PerfectField k := PerfectField.ofCharZero
  obtain ⟨hsnc, hint, hdisj, hK⟩ :=
    protectedData_bmoOneRun T hm C Γ hP ⟨n, Nat.lt_succ_of_le hn⟩
  have e := stage_take_last (bmoOneRun T hm) hn
  have hsnc' : (((bmoOneRun T hm).take n).totalTransformSeq T.E (Fin.last _)).HasSncWith
      (((bmoOneRun T hm).take n).strictTransformSeq Γ (Fin.last _)) :=
    hasSncWith_of_heq e.symm (totalTransformSeq_take_last_heq _ T.E hn).symm
      (strictTransformSeq_take_last_heq _ Γ hn).symm hsnc
  refine ⟨?_, isIntegral_of_heq e (strictTransformSeq_take_last_heq _ Γ hn) hint, hsnc', ?_, ?_⟩
  · have := (stageTriple T hm n).smooth
    exact HasSncWith.smooth ((stageTriple T hm n).X.left ↘ Spec (.of k)) hsnc'
  · intro c' hc'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    exact disjoint_support_of_heq e.symm (strictTransformSeq_take_last_heq _ c hn).symm
      (strictTransformSeq_take_last_heq _ Γ hn).symm (hdisj c hc)
  · rw [stageTriple_I]
    exact forall_chainRelativeKAt_of_heq e.symm (totalTransformSeq_take_last_heq _ T.E hn).symm
      (markedTransformSeq_take_last_heq _ T.I 1 hn).symm
      (strictTransformSeq_take_last_heq _ Γ hn).symm hK

/-- The stalk of a colon at a point off the support of the divisor is the stalk of the ideal
(`stalkIdeal_colon_of_isLocallyNoetherian`, the colon by the unit ideal). -/
theorem stalkIdeal_colon_eq_of_notMem_support {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I K : X.IdealSheafData) {p : X} (hp : p ∉ K.support) :
    (I.colon K).stalkIdeal p = I.stalkIdeal p := by
  rw [stalkIdeal_colon_of_isLocallyNoetherian, stalkIdeal_eq_top_of_notMem_support K hp,
    Submodule.top_coe, Submodule.colon_univ]

open Classical in
/-- The isolation is the identity near `Γ̃`: at a point of the strict transform of the protected
component, the isolated ideal has the stalk of the ideal of the stage — the strict transforms of
the absorbed members miss `Γ̃`, so the reduced ideal of their union has the unit stalk there. -/
theorem stalkIdeal_isolatedTriple_I_eq_of_protectedState (n : ℕ)
    (hP : ProtectedState (stageTriple T hm n) (transportedComponents T hm C n)
      (((bmoOneRun T hm).take n).strictTransformSeq Γ (Fin.last _)))
    {p : ((bmoOneRun T hm).take n).stage (Fin.last _)}
    (hp : p ∈ (((bmoOneRun T hm).take n).strictTransformSeq Γ (Fin.last _)).support) :
    (isolatedTriple T hm C n).I.stalkIdeal p = (stageTriple T hm n).I.stalkIdeal p := by
  have hLN : IsLocallyNoetherian (stageTriple T hm n).X.left :=
    ((stageTriple T hm n).X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hnot : p ∉ (vanishingIdeal (⨆ c ∈ C.filter (fun c => CenterContains (bmoOneRun T hm) c n),
      (((bmoOneRun T hm).take n).strictTransformSeq c (Fin.last _)).support)).support := by
    rw [support_vanishingIdeal_eq, mem_biSup_closeds_iff]
    rintro ⟨c, hc, hpc⟩
    exact notMem_of_disjoint_closeds
      (hP.disjoint _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mp hc).1)) hpc hp
  change ((stageTriple T hm n).I.colon (vanishingIdeal _)).stalkIdeal p = _
  exact stalkIdeal_colon_eq_of_notMem_support _ _ hnot

open Classical in
/-- **The isolation lemma**: the protected state passes through the isolation of the loop (the
isolation passage of the proof of [Wlo05, Theorem 4.7.1]). -/
theorem protectedState_isolatedTriple (hP : ProtectedState T C Γ)
    (h : ∃ n, HasAbsorptionAt T hm C n) :
    ProtectedState (isolatedTriple T hm C (Nat.find h)) (remainingComponents T hm C (Nat.find h))
      (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq Γ (Fin.last _)) := by
  have hP' := protectedState_stageTriple T hm C Γ hP (Nat.find h) (find_lt_length T hm C h).le
  refine ⟨hP'.smooth, hP'.integral, hP'.snc, ?_, ?_⟩
  · intro c' hc'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    exact hP'.disjoint _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mp hc).1)
  · intro p hp
    exact (chainRelativeKAt_congr_stalkIdeal_K
      (stalkIdeal_isolatedTriple_I_eq_of_protectedState T hm C Γ (Nat.find h) hP' hp).symm).mp
      (hP'.chain p hp)

/-- **The last-round lemma** ([Kol07, Theorem 69 (1)]): the untruncated run of `BMO_1` ends with
the ideal trivial at EVERY point — `max-ord < 1` means order `0` everywhere — the stalk form of
`markedTransformSeq_bmoOneRun_last_eq_top`. -/
theorem stalkIdeal_markedTransformSeq_bmoOneRun_last_eq_top (p : (bmoOneRun T hm).last) :
    ((bmoOneRun T hm).markedTransformSeq T.I 1 (Fin.last _)).stalkIdeal p = ⊤ := by
  rw [markedTransformSeq_bmoOneRun_last_eq_top T hm]
  exact stalkIdeal_top p

end Loop

open Classical in
/-- **The loop theorem, CP5**: strong induction on `C.card` — from a protected state, the loop ends
with the component smooth, snc with the boundary, and the isolated ideal trivial along it (the
proof of [Wlo05, Theorem 4.7.1]). -/
theorem protected_bedAux (N : ℕ) : ∀ (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData)
    (Γ : T.X.left.IdealSheafData), C.card = N → ProtectedState T C Γ →
    Smooth (((bedAux T hm C).strictTransformSeq Γ (Fin.last _)).subschemeι ≫
        (bedAux T hm C).composite ≫ (T.X.left ↘ Spec (CommRingCat.of k))) ∧
      ((bedAux T hm C).totalTransformSeq T.E (Fin.last _)).HasSncWith
        ((bedAux T hm C).strictTransformSeq Γ (Fin.last _)) ∧
      ∀ p ∈ ((bedAux T hm C).strictTransformSeq Γ (Fin.last _)).support,
        ((bedAux T hm C).markedTransformSeq T.I 1 (Fin.last _)).stalkIdeal p = ⊤ := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro T hm C Γ hcard hP
  have hPF : PerfectField k := PerfectField.ofCharZero
  by_cases h : ∃ n, HasAbsorptionAt T hm C n
  · rw [bedAux_of_exists T hm C h]
    set n₀ := Nat.find h with hn₀
    have hlt : (remainingComponents T hm C n₀).card < N := by
      rw [← hcard]
      exact card_remainingComponents_lt T hm C h
    have hn₀le : n₀ ≤ (bmoOneRun T hm).length := (find_lt_length T hm C h).le
    have hP' := protectedState_stageTriple T hm C Γ hP n₀ hn₀le
    obtain ⟨hsm, hsnc, htop⟩ := ih _ hlt (isolatedTriple T hm C n₀) hm
      (remainingComponents T hm C n₀) (((bmoOneRun T hm).take n₀).strictTransformSeq Γ (Fin.last _))
      rfl (protectedState_isolatedTriple T hm C Γ hP h)
    set R := bedAux (isolatedTriple T hm C n₀) hm (remainingComponents T hm C n₀) with hR
    have e := last_concat ((bmoOneRun T hm).take n₀) R
    have hΓ := strictTransformSeq_concat_last_heq ((bmoOneRun T hm).take n₀) R Γ
    refine ⟨?_, hasSncWith_of_heq e.symm
      (totalTransformSeq_concat_last_heq ((bmoOneRun T hm).take n₀) R T.E).symm hΓ.symm hsnc, ?_⟩
    · -- smoothness over the base: the composite of the concatenation
      have hcomp : HEq (((bmoOneRun T hm).take n₀).concat R).composite
          (R.composite ≫ ((bmoOneRun T hm).take n₀).composite) := by
        rw [composite_concat ((bmoOneRun T hm).take n₀) R]
        exact heq_eqToHom_comp e _
      have hf : HEq ((((bmoOneRun T hm).take n₀).concat R).composite ≫ (T.X.left ↘ Spec (.of k)))
          (R.composite ≫ ((bmoOneRun T hm).take n₀).composite ≫ (T.X.left ↘ Spec (.of k))) :=
        (heq_comp_right e hcomp (T.X.left ↘ Spec (.of k))).trans
          (heq_of_eq (Category.assoc R.composite ((bmoOneRun T hm).take n₀).composite _))
      exact smooth_subschemeι_comp_of_heq_map e hΓ hf hsm
    · -- the unit stalk along `Γ̃_end`: the isolated and the un-isolated ideals agree near `Γ̃`
      refine forall_stalkIdeal_eq_top_of_heq e hΓ
        (markedTransformSeq_concat_last_heq ((bmoOneRun T hm).take n₀) R T.I 1) ?_
      intro p hp
      rw [← stageTriple_I T hm n₀]
      have hLN' : IsLocallyNoetherian (isolatedTriple T hm C n₀).X.left :=
        ((isolatedTriple T hm C n₀).X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
      exact (stalkIdeal_markedTransformSeq_eq_of_forall_stalkIdeal_eq R (stageTriple T hm n₀).I
        (isolatedTriple T hm C n₀).I (((bmoOneRun T hm).take n₀).strictTransformSeq Γ (Fin.last _))
        (fun q hq => (stalkIdeal_isolatedTriple_I_eq_of_protectedState T hm C Γ n₀ hP' hq).symm)
        (Fin.last _) p hp).trans (htop p hp)
  · rw [bedAux_of_not_exists T hm C h]
    obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
    have hsmd : SmoothOfRelativeDimension d (T.X.left ↘ Spec (.of k)) := hd
    have hrun : (bmoOneRun T hm).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E := by
      have h0 := isOrderGeSeq_bmoOneRun T hm
      rwa [hm] at h0
    obtain ⟨hsnc, -, -, -⟩ := protectedData_bmoOneRun T hm C Γ hP (Fin.last _)
    have hsm : Smooth ((bmoOneRun T hm).composite ≫ (T.X.left ↘ Spec (.of k))) :=
      IsSmooth.smooth_stageMap (n := d) hrun.1 (Fin.last _)
    exact ⟨HasSncWith.smooth ((bmoOneRun T hm).composite ≫ (T.X.left ↘ Spec (.of k))) hsnc, hsnc,
      fun p _ => stalkIdeal_markedTransformSeq_bmoOneRun_last_eq_top T hm p⟩

end Hironaka.Resolution
