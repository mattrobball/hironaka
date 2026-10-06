/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Algebra.Util.OpenMapGenericPoints
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Kol07.Thm36.EraseEmptyIndex
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Functorial
import Hironaka.Resolution.Algebraic.Smooth.GeometricallyReduced
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullback
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow
import Hironaka.Scheme.BlowUp.FlatColon
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.RestrictedCenters
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# `BED` commutes with smooth morphisms up to empty blow-ups

Clause (d) of [Wlo05, Theorem 1.0.2] ([Wlo05, 4.1]) and the second bullet of [Kol07, 34.1]
(Kollár's "deleting every blow-up `h^* π_i` whose center is empty") for the loop `BED` of
`Hironaka.Resolution.Algebraic.Wlo05.Embedded`, under the hypothesis that the image of the smooth `h
: X' → X` meets every irreducible component of `Y = V(I_Y)`: then `BED(X', h^* I_Y, ∅)` is the
pull-back `h^* BED(X, I_Y, ∅)` with its empty blow-ups deleted (`bed_pullback_eraseEmpty`).

**The mechanism** is the transport of the loop along a smooth surjection
(`bedAux_pullback_of_surjective`, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullback`) with two
changes, both coming from Kollár's deletion of the empty blow-ups and the reindexing:

* the invariant of the loop is the pull-back relation UP TO UNIT BOUNDARY MEMBERS
  (`MarkedTriple.IsPullbackOfUpToUnits`,
  `Hironaka.Resolution.Algebraic.MarkedOrderReduction.UpToUnits`): the deleted empty blow-ups leave
  unit members in the boundary of the pulled-back data, so the isolated marked triple upstairs is
  the pull-back of the one downstairs only up to those members. The run of `BMO_1` does not see them
  (`dimFreeBMO_indifferentToEmptyMembers`), so the second bullet of [Kol07, 34.1] for `BMO_1`
  ([Kol07, Theorem 69 (2)]) gives the run upstairs as the ERASED pull-back of the run downstairs
  (`bmoOneRun_eraseEmpty_pullback`);
* the stop rule is transported across `eraseEmpty` by the reindexing of
  `Hironaka.Resolution.Algebraic.Kol07.Thm36.EraseEmptyIndex`: the stages of the erased run are the
  nonempty stages of the pulled-back run (`exists_eraseIdx_eq`), and an empty centre absorbs nothing
  alive — the first absorbing stage downstairs absorbs a component upstairs (the image hypothesis
  `hmeets` gives one), whose strict transform is nonempty, so the pulled-back centre there is
  nonempty and survives the erasure (`centerContains_eraseEmpty_iff`). Surjectivity of `h` entered
  the surjective case only there (a component of `h⁻¹(V(c))` exists) and in the identity of the
  runs.

The round is then assembled by `pullback_concat`, `eraseEmpty_concat` (the erasure of a
concatenation, the second piece carried along the last-stage isomorphism `eraseEmptyLastHom`) and
`eraseEmpty_pullback_of_flat_surjective` along that isomorphism; the isolated triple and the
remaining components are transported along `eraseEmptyLastHom ≫ pullbackLastHom`
(`IsPullbackOfUpToUnits.induced_eraseEmpty`, `strictTransformSeq_eraseEmpty_last`,
`isPullbackComponents_comp`, `isPullbackComponents_image_comap_of_isIso`), and the image hypothesis
propagates to the remaining components (the generic point of a component upstairs lies over the
strict transform downstairs). This transport is not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.Stage

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-! ### The run of `BMO_1` on a pull-back up to unit members -/

/-- The second bullet of [Kol07, 34.1] for `BMO_1` on a pull-back up to unit boundary members: the
run of `BMO_1` on `T'` is the erased pull-back of the run on `T` — `T'` and its full pull-back have
the same run (`dimFreeBMO_indifferentToEmptyMembers`), and the full pull-back is an exact pull-back
(`dimFreeBMO_commutesWithSmooth`, [Kol07, Theorem 69 (2)]). -/
theorem bmoOneRun_eraseEmpty_pullback (T T' : MarkedTriple k) (hm : T.m = 1) (hm' : T'.m = 1)
    (h : T'.X.left ⟶ T.X.left) [Smooth h] (hp : T'.IsPullbackOfUpToUnits T h) :
    bmoOneRun T' hm' = ((bmoOneRun T hm).pullback h).eraseEmpty := by
  have hpf : (MarkedTriple.fullPullback T' T h).IsPullbackOf T h :=
    MarkedTriple.fullPullback_isPullbackOf hp
  have hsm : @Smooth (MarkedTriple.fullPullback T' T h).X.left T.X.left h := ‹Smooth h›
  obtain ⟨e, he⟩ := MarkedTriple.isTopErasure_fullPullback hp
  have hind := dimFreeBMO_indifferentToEmptyMembers stage0 1 (k := k)
    (MarkedTriple.fullPullback T' T h)
    T'.E T'.isSnc e he.1 he.2 ⟨le_rfl, hm'⟩ ⟨le_rfl, hm'⟩
  have hce := (dimFreeBMO_commutesWithSmooth stage0 1 (k := k)).2
  have hR : (dimFreeBMO stage0 1 k).seq (MarkedTriple.fullPullback T' T h) ⟨le_rfl, hm'⟩ =
      ((bmoOneRun T hm).pullback h).eraseEmpty :=
    @hce T (MarkedTriple.fullPullback T' T h) h hsm hpf ⟨le_rfl, hm⟩ ⟨le_rfl, hm'⟩
  exact hind.symm.trans hR

/-- The pull-back of a run of order `≥ m` is a run of order `≥ m` for the pull-back data up to unit
members (the run of the full pull-back with the deleted members restored,
`ExtendsByEmpty.isOrderGeSeq`). -/
theorem isOrderGeSeq_pullback_of_upToUnits {T T' : MarkedTriple k}
    {h : T'.X.left ⟶ T.X.left} [Smooth h]
    (hp : T'.IsPullbackOfUpToUnits T h) {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E) :
    (S.pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E := by
  have hpf : (MarkedTriple.fullPullback T' T h).IsPullbackOf T h :=
    MarkedTriple.fullPullback_isPullbackOf hp
  have hsm : @Smooth (MarkedTriple.fullPullback T' T h).X.left T.X.left h := ‹Smooth h›
  obtain ⟨e, he⟩ := hp.2.2.2
  have hPf : (S.pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m (T.E.comap h) :=
    hpf.isOrderGeSeq_pullback hS
  exact he.extendsByEmpty.isOrderGeSeq hPf

/-- The erased pull-back of a run of order `≥ m` is a run of order `≥ m` for the pull-back data up
to unit members (`IsOrderGeSeq.eraseEmpty`). -/
theorem isOrderGeSeq_pullback_eraseEmpty_of_upToUnits {T T' : MarkedTriple k}
    {h : T'.X.left ⟶ T.X.left}
    [Smooth h] (hp : T'.IsPullbackOfUpToUnits T h) {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E) :
    (S.pullback h).eraseEmpty.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E := by
  obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
  exact IsOrderGeSeq.eraseEmpty (T'.X.left ↘ Spec (.of k)) n'
    (isOrderGeSeq_pullback_of_upToUnits hp hS)

/-! ### Components of preimages along a composite and along an isomorphism -/

/-- The preimage of a closed set along a composite. -/
theorem closeds_preimage_comp {X X' X'' : Scheme.{u}} (g : X' ⟶ X) (e : X'' ⟶ X') (Z : Closeds X) :
    (Z.preimage g.continuous).preimage e.continuous = Z.preimage (e ≫ g).continuous := by
  apply SetLike.coe_injective
  ext x
  change e x ∈ g ⁻¹' (Z : Set X) ↔ (e ≫ g) x ∈ (Z : Set X)
  rw [Set.mem_preimage, Scheme.Hom.comp_apply]

/-- The components of the preimages compose ([Kol07, Definition 30, 30.1] twice): the components
of `e⁻¹(V(b))`, `b` a component of `g⁻¹(V(c))`, are the components of `(e ≫ g)⁻¹(V(c))`
(`mem_genericPoints_preimage_iff` for the open map `e`). -/
theorem isPullbackComponents_comp {X X' X'' : Scheme.{u}} [NoetherianSpace X''] (g : X' ⟶ X)
    (e : X'' ⟶ X') [Smooth e] {A : Finset X.IdealSheafData} {B : Finset X'.IdealSheafData}
    {B' : Finset X''.IdealSheafData} (hAB : IsPullbackComponents g A B)
    (hBB' : IsPullbackComponents e B B') : IsPullbackComponents (e ≫ g) A B' := by
  intro c''
  rw [hBB' c'']
  constructor
  · rintro ⟨b, hb, η'', hη'', rfl⟩
    obtain ⟨c, hc, η', hη', rfl⟩ := (hAB b).mp hb
    refine ⟨c, hc, η'', ?_, rfl⟩
    rw [support_vanishingIdeal_eq] at hη''
    have := (mem_genericPoints_preimage_iff e.continuous e.isOpenMap
      (c.support.preimage g.continuous) η'').mpr ⟨η', hη', hη''⟩
    rwa [closeds_preimage_comp] at this
  · rintro ⟨c, hc, η'', hη'', rfl⟩
    rw [← closeds_preimage_comp, mem_genericPoints_preimage_iff e.continuous e.isOpenMap] at hη''
    obtain ⟨η', hη', hη''⟩ := hη''
    refine ⟨IdealSheafData.vanishingIdeal (Closeds.closure {η'}), (hAB _).mpr ⟨c, hc, η', hη',
        rfl⟩, η'', ?_, rfl⟩
    rwa [support_vanishingIdeal_eq]

open Classical in
/-- Along an isomorphism `e`, the components of the preimages of the members of `B` (reduced
ideals of closures of points) are their inverse images `b.comap e`. -/
theorem isPullbackComponents_image_comap_of_isIso {X' X'' : Scheme.{u}} [NoetherianSpace X']
    [NoetherianSpace X''] (e : X'' ⟶ X') [IsIso e] {B : Finset X'.IdealSheafData}
    (hB : ∀ b ∈ B, ∃ η' : X', b = IdealSheafData.vanishingIdeal (Closeds.closure {η'})) :
    IsPullbackComponents e B (B.image fun b => b.comap e) := by
  classical
  have hoi : IsOpenImmersion e := IsOpenImmersion.of_isIso e
  have hsme : Smooth e := inferInstance
  have hoe : IsOpenEmbedding e := e.isOpenEmbedding
  have hinj : Function.Injective e := hoe.injective
  have hsurj : Function.Surjective e := surjective_of_isIso e
  -- the inverse image of the closure of `e η''` is the closure of `η''`
  have hcl : ∀ η'' : X'',
      (Closeds.closure {e η''}).preimage e.continuous = Closeds.closure {η''} := by
    intro η''
    apply SetLike.coe_injective
    change e ⁻¹' closure {e η''} = closure {η''}
    rw [hoe.isOpenMap.preimage_closure_eq_closure_preimage hoe.continuous, ← Set.image_singleton,
      hinj.preimage_image]
  have key : ∀ η'' : X'',
      (IdealSheafData.vanishingIdeal (Closeds.closure {e η''})).comap e =
        IdealSheafData.vanishingIdeal (Closeds.closure {η''}) := by
    intro η''
    rw [Hironaka.Smooth.comap_vanishingIdeal_of_smooth e, hcl]
  intro c''
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨η', rfl⟩ := hB b hb
    obtain ⟨η'', rfl⟩ := hsurj η'
    refine ⟨_, hb, η'', ?_, key η''⟩
    rw [support_vanishingIdeal_eq, hcl]
    exact ⟨subset_closure rfl,
      fun η₁ h1 h2 => (h2.antisymm (specializes_iff_mem_closure.mpr h1)).eq⟩
  · rintro ⟨b, hb, η'', hη'', rfl⟩
    obtain ⟨η', rfl⟩ := hB b hb
    rw [support_vanishingIdeal_eq] at hη''
    have h1 : e η'' ∈ (Closeds.closure {η'}).genericPoints :=
      mem_genericPoints_of_mem_genericPoints_preimage hoe.continuous
        hoe.isOpenMap _ hη''
    have h2 : e η'' = η' :=
      (h1.2 (subset_closure rfl) (specializes_iff_mem_closure.mpr h1.1)).symm
    refine ⟨_, hb, ?_⟩
    rw [← key η'', h2]

open Classical in
/-- The remaining members at the end of the erased run are the inverse images, along the
last-stage isomorphism, of the remaining members at the end of the run
(`strictTransformSeq_eraseEmpty_last`). -/
theorem remainingAt_eraseEmpty {X : Scheme.{u}} (Q : BlowUpSequence X)
    (G : Finset X.IdealSheafData) :
    remainingAt Q.eraseEmpty G = (remainingAt Q G).image fun c => c.comap Q.eraseEmptyLastHom := by
  unfold remainingAt
  exact (Finset.image_congr
    (f := fun c => Q.eraseEmpty.strictTransformSeq c (Fin.last _))
    (g := fun c => (Q.strictTransformSeq c (Fin.last _)).comap Q.eraseEmptyLastHom)
    (fun c _ => strictTransformSeq_eraseEmpty_last Q c)).trans
    (Finset.image_image (s := G) (f := fun c => Q.strictTransformSeq c (Fin.last _))
      (g := fun b => b.comap Q.eraseEmptyLastHom)).symm

/-! ### The isolated triple along the erased run -/

/-- `isolatedAt_isPullbackOf` up to unit members: the isolated marked triple of a run `Q'`
upstairs is the pull-back up to unit members of the isolated marked triple of `Q` downstairs along
a smooth lift `g` of the last stages, when the induced triples are and the union of the absorbed
strict transforms upstairs is the preimage of the one downstairs (the colon commutes with the flat
lift, `Hironaka.Scheme.BlowUp.FlatColon`; the reduced ideal of a closed set pulls back to the
reduced ideal of the preimage, `Hironaka.Resolution.Algebraic.Smooth.GeometricallyReduced`). -/
theorem isolatedAt_isPullbackOfUpToUnits {T T' : MarkedTriple k} (Q : BlowUpSequence T.X.left)
    (hQ : Q.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E) (Q' : BlowUpSequence T'.X.left)
    (hQ' : Q'.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E)
    (g : Q'.stage (Fin.last _) ⟶ Q.stage (Fin.last _)) [Smooth g]
    (hind : (T'.induced Q' hQ' (Fin.last _)).IsPullbackOfUpToUnits (T.induced Q hQ (Fin.last _)) g)
    (F : Finset T.X.left.IdealSheafData) (F' : Finset T'.X.left.IdealSheafData)
    (hΓ : (⨆ c' ∈ F', (Q'.strictTransformSeq c' (Fin.last _)).support) =
      (⨆ c ∈ F, (Q.strictTransformSeq c (Fin.last _)).support).preimage g.continuous) :
    (isolatedAt T' Q' hQ' F').IsPullbackOfUpToUnits (isolatedAt T Q hQ F) g := by
  obtain ⟨hover, hI, hm, e, he⟩ := hind
  refine ⟨hover, ?_, hm, e, he⟩
  have hLN : IsLocallyNoetherian (Q.stage (Fin.last _)) :=
    ((T.induced Q hQ (Fin.last _)).X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hLN' : IsLocallyNoetherian (Q'.stage (Fin.last _)) :=
    ((T'.induced Q' hQ' (Fin.last _)).X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hN : NoetherianSpace (Q.stage (Fin.last _)) :=
    Hironaka.BD.noetherianSpace_triple (T.induced Q hQ (Fin.last _)).toTriple
  set Γ : Closeds (Q.stage (Fin.last _)) :=
    ⨆ c ∈ F, (Q.strictTransformSeq c (Fin.last _)).support with hΓdef
  have hI' : (T'.induced Q' hQ' (Fin.last _)).I = (T.induced Q hQ (Fin.last _)).I.comap g := hI
  have key : ((T.induced Q hQ (Fin.last _)).I.colon (IdealSheafData.vanishingIdeal Γ)).comap g =
      ((T.induced Q hQ (Fin.last _)).I.comap g).colon ((IdealSheafData.vanishingIdeal Γ).comap g) :=
    IdealSheafData.colon_comap_of_flat_of_isLocallyNoetherian g _ _
  have key2 : (IdealSheafData.vanishingIdeal Γ).comap g = IdealSheafData.vanishingIdeal
      (Γ.preimage g.continuous) :=
    Hironaka.Smooth.comap_vanishingIdeal_of_smooth g Γ
  change (T'.induced Q' hQ' (Fin.last _)).I.colon (IdealSheafData.vanishingIdeal _) =
    ((T.induced Q hQ (Fin.last _)).I.colon (IdealSheafData.vanishingIdeal Γ)).comap g
  rw [hI', key, key2]
  exact congrArg (fun Z => ((T.induced Q hQ (Fin.last _)).I.comap g).colon
      (IdealSheafData.vanishingIdeal Z)) hΓ

/-- The union of the strict transforms at the end of the ERASED pulled-back run of the components
of the preimages of the members of `F` is the preimage, along `eraseEmptyLastHom ≫ g`, of the
union of the strict transforms of the members of `F`
(`iSup_support_strictTransformSeq_pullback_last` carried along the last-stage isomorphism,
`strictTransformSeq_eraseEmpty_last`). -/
theorem iSup_support_strictTransformSeq_eraseEmpty_pullback_last {X X' : Scheme.{u}}
    [IsLocallyNoetherian X'] [NoetherianSpace X'] (Q : BlowUpSequence X) (h : X' ⟶ X)
    (g : (Q.pullback h).stage (Fin.last _) ⟶ Q.stage (Fin.last _))
    (hg : ∀ J : X.IdealSheafData, (Q.pullback h).strictTransformSeq (J.comap h) (Fin.last _) =
      (Q.strictTransformSeq J (Fin.last _)).comap g)
    (F : Finset X.IdealSheafData) (F' : Finset X'.IdealSheafData)
    (hFF' : IsPullbackComponents h F F') :
    (⨆ c' ∈ F', ((Q.pullback h).eraseEmpty.strictTransformSeq c' (Fin.last _)).support) =
      (⨆ c ∈ F, (Q.strictTransformSeq c (Fin.last _)).support).preimage
        ((Q.pullback h).eraseEmptyLastHom ≫ g).continuous := by
  let e₁ : (Q.pullback h).eraseEmpty.stage (Fin.last _) ⟶ (Q.pullback h).stage (Fin.last _) :=
    (Q.pullback h).eraseEmptyLastHom
  have h1 : (⨆ c' ∈ F', ((Q.pullback h).eraseEmpty.strictTransformSeq c' (Fin.last _)).support) =
      (⨆ c' ∈ F', ((Q.pullback h).strictTransformSeq c' (Fin.last _)).support).preimage
        e₁.continuous := by
    apply SetLike.coe_injective
    ext x
    rw [coe_iSup_finset]
    change _ ↔ x ∈ e₁ ⁻¹' ((⨆ c' ∈ F', ((Q.pullback h).strictTransformSeq c' (Fin.last _)).support :
      Closeds ((Q.pullback h).stage (Fin.last _))) : Set _)
    rw [Set.mem_preimage, coe_iSup_finset, Set.mem_iUnion₂, Set.mem_iUnion₂]
    refine exists_congr fun c' => exists_congr fun _ => ?_
    rw [strictTransformSeq_eraseEmpty_last]
    exact mem_support_comap_iff_apply _ _ _
  rw [h1, iSup_support_strictTransformSeq_pullback_last Q h g hg F F' hFF']
  exact closeds_preimage_comp g e₁ _

/-! ### The loop along a smooth morphism meeting every component -/

open Classical in
/-- **The loop along a smooth morphism meeting every component** ([Wlo05, Theorem 1.0.2] clause
(d), [Wlo05, 4.1]; the second bullet of [Kol07, 34.1]): for marked triples of mark `1`, a smooth
`h` carrying the pull-back data up to unit boundary members, a family `C` of reduced ideals of
irreducible closed sets each meeting the image of `h`, and `C'` the components of their
preimages, the modified run upstairs is the pull-back of the modified run downstairs with its
empty blow-ups deleted. Strong induction on the number of members: one round is transported by
the stop-rule equivalence (`stopRule_aux`) read across the erasure
(`centerContains_eraseEmpty_iff`, `exists_eraseIdx_eq_of_lt`), the pull-back data up to unit
members of the isolated triple, the components relation for the remaining members and the image
hypothesis for them; the round is assembled by `pullback_concat` and `eraseEmpty_concat`. -/
theorem bedAux_eraseEmpty_pullback :
    ∀ (N : ℕ) (T T' : MarkedTriple k) (hm : T.m = 1) (hm' : T'.m = 1)
      (h : T'.X.left ⟶ T.X.left) [Smooth h], T'.IsPullbackOfUpToUnits T h →
      ∀ (C : Finset T.X.left.IdealSheafData) (C' : Finset T'.X.left.IdealSheafData), C.card = N →
        (∀ c ∈ C, ∃ η : T.X.left, c = IdealSheafData.vanishingIdeal (Closeds.closure {η})) →
        (∀ c ∈ C, ∃ x : T'.X.left, h x ∈ c.support) →
        IsPullbackComponents h C C' →
        bedAux T' hm' C' = ((bedAux T hm C).pullback h).eraseEmpty := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro T T' hm hm' h _ hp C C' hcard hC hmeets hCC'
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have : IsLocallyNoetherian T'.X.left := (T'.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have : NoetherianSpace T'.X.left := Hironaka.BD.noetherianSpace_triple T'.toTriple
  -- the runs (Theorem 69's second bullet on the pull-back up to unit members)
  have hR : bmoOneRun T' hm' = ((bmoOneRun T hm).pullback h).eraseEmpty :=
    bmoOneRun_eraseEmpty_pullback T T' hm hm' h hp
  set S := bmoOneRun T hm with hSdef
  have hstop := stopRule_aux S h C C' hC hCC'
  -- an empty centre absorbs nothing alive: a component not absorbed before `n` whose strict
  -- transform the centre at `n` contains makes that centre nonempty
  have hne_top : ∀ c' ∈ C', ∀ (n : ℕ) (hn : n < (S.pullback h).length),
      (∀ m < n, ¬ CenterContains (S.pullback h) c' m) → CenterContains (S.pullback h) c' n →
      (S.pullback h).center ⟨n, hn⟩ ≠ ⊤ := by
    intro c' hc' n hn hhist hcc htop
    obtain ⟨c, hc, η', hη', rfl⟩ := (hCC' c').mp hc'
    have := isReduced_subscheme_vanishingIdeal (X := T'.X.left) (Closeds.closure {η'})
    obtain ⟨ζ, hζ, -, -⟩ := exists_isGenericPoint_strictTransformSeq (S.pullback h) _
      (Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η') ⟨n, Nat.lt_succ_of_lt hn⟩
      (fun m hm₁ hle => hhist m hm₁ ⟨m.2, hle⟩)
    obtain ⟨hn', hle⟩ := hcc
    rw [htop, top_le_iff] at hle
    have hmem := hζ.mem
    rw [hle, IdealSheafData.support_top] at hmem
    exact hmem
  by_cases hex : ∃ n, HasAbsorptionAt T hm C n
  · set n := Nat.find hex with hn
    have hmin : ∀ m < n, ¬ HasAbsorptionAt T hm C m := fun m hm₁ => Nat.find_min hex hm₁
    have hnone : ∀ m < n, ∀ c ∈ C, ¬ CenterContains S c m :=
      fun m hm₁ c hc hcc => hmin m hm₁ ⟨c, hc, hcc⟩
    obtain ⟨hhist', hiff⟩ := hstop n hnone
    have habs : HasAbsorptionAt T hm C n := Nat.find_spec hex
    obtain ⟨c₀, hc₀, hcc₀⟩ := habs
    have hn_le : n ≤ S.length := hcc₀.1.le
    have hn_lt : n < (S.pullback h).length := by rw [length_pullback]; exact hcc₀.1
    -- a component of `h⁻¹(V(c₀))` exists: the image of `h` meets `V(c₀)`
    obtain ⟨η₀', hη₀'⟩ : ∃ η₀', η₀' ∈ (c₀.support.preimage h.continuous).genericPoints := by
      obtain ⟨x, hx⟩ := hmeets c₀ hc₀
      obtain ⟨η₀', hη₀', -⟩ := Closeds.exists_mem_genericPoints_specializes
        (c₀.support.preimage h.continuous) (show x ∈ c₀.support.preimage h.continuous from hx)
      exact ⟨η₀', hη₀'⟩
    have hc₀' : IdealSheafData.vanishingIdeal (Closeds.closure {η₀'}) ∈ C' :=
      (hCC' _).mpr ⟨c₀, hc₀, η₀', hη₀', rfl⟩
    have hcc₀' : CenterContains (S.pullback h) (IdealSheafData.vanishingIdeal (Closeds.closure
        {η₀'})) n :=
      (hiff c₀ hc₀ η₀' hη₀').mpr hcc₀
    have hPn : (S.pullback h).center ⟨n, hn_lt⟩ ≠ ⊤ :=
      hne_top _ hc₀' n hn_lt (fun m hm₁ => hhist' _ hc₀' m hm₁) hcc₀'
    -- the first absorbing stage upstairs is the index of `n` in the erased run
    have hE2 : ∀ c', CenterContains (bmoOneRun T' hm') c' (eraseIdx (S.pullback h) n) ↔
        CenterContains (S.pullback h) c' n := fun c' => by
      rw [hR]
      exact centerContains_eraseEmpty_iff (S.pullback h) c' n hn_lt hPn
    have hex' : ∃ n', HasAbsorptionAt T' hm' C' n' :=
      ⟨_, _, hc₀', (hE2 _).mpr hcc₀'⟩
    have hfind : Nat.find hex' = eraseIdx (S.pullback h) n := by
      rw [Nat.find_eq_iff]
      refine ⟨⟨_, hc₀', (hE2 _).mpr hcc₀'⟩, fun m' hlt' => ?_⟩
      rintro ⟨c', hc', hcc'⟩
      rw [hR] at hcc'
      obtain ⟨m, hm₁, hne, he, hmn⟩ := exists_eraseIdx_eq_of_lt (S.pullback h) hcc'.1 hlt'
      rw [← he, centerContains_eraseEmpty_iff (S.pullback h) c' m hm₁ hne] at hcc'
      exact hhist' c' hc' m hmn hcc'
    -- the round's data on the truncations; the lifts of the last stages
    have hQ : (S.take n).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E :=
      isOrderGeSeq_take _ _ _ _ (isOrderGeSeq_bmoOneRun T hm) n
    have hPu : ((S.take n).pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E :=
      isOrderGeSeq_pullback_of_upToUnits hp hQ
    have hQ' : ((S.take n).pullback h).eraseEmpty.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m
        T'.E :=
      isOrderGeSeq_pullback_eraseEmpty_of_upToUnits hp hQ
    have hQ'take : (bmoOneRun T' hm').take (eraseIdx (S.pullback h) n) =
        ((S.take n).pullback h).eraseEmpty := by
      rw [hR, take_pullback]
      exact eraseEmpty_take (S.pullback h) n
    let g : ((S.take n).pullback h).stage (Fin.last _) ⟶ (S.take n).stage (Fin.last _) :=
      (S.take n).pullbackLastHom h
    have hsm : Smooth g := smooth_pullbackLastHom _ h
    let e₀ : ((S.take n).pullback h).eraseEmpty.stage (Fin.last _) ⟶
        ((S.take n).pullback h).stage (Fin.last _) :=
      ((S.take n).pullback h).eraseEmptyLastHom
    have hiso : IsIso e₀ := isIso_eraseEmptyLastHom _
    have hsme : Smooth e₀ := Hironaka.BMO.smooth_eraseEmptyLastHom' _
    have hsm₁ : Smooth (e₀ ≫ g) := inferInstance
    have hg : ∀ J : T.X.left.IdealSheafData,
        ((S.take n).pullback h).strictTransformSeq (J.comap h) (Fin.last _) =
          ((S.take n).strictTransformSeq J (Fin.last _)).comap g :=
      fun J => strictTransformSeq_pullback_last (S.take n) h J
    have hind :
        (T'.induced ((S.take n).pullback h).eraseEmpty hQ' (Fin.last _)).IsPullbackOfUpToUnits
          (T.induced (S.take n) hQ (Fin.last _)) (e₀ ≫ g) :=
      hp.induced_eraseEmpty hQ hQ'
    have hN' : NoetherianSpace (((S.take n).pullback h).stage (Fin.last _)) :=
      Hironaka.BD.noetherianSpace_triple (T'.induced _ hPu (Fin.last _)).toTriple
    have hN'' : NoetherianSpace (((S.take n).pullback h).eraseEmpty.stage (Fin.last _)) :=
      Hironaka.BD.noetherianSpace_triple (T'.induced _ hQ' (Fin.last _)).toTriple
    have hhistQ : ∀ c ∈ C, ∀ m : Fin (S.take n).length,
        ¬ (S.take n).center m ≤ (S.take n).strictTransformSeq c m.castSucc :=
      fun c hc => forall_not_center_le_take S c hn_le (fun m hm₁ => hnone m hm₁ c hc)
    have hhistQ' : ∀ c' ∈ C', ∀ m : Fin ((S.take n).pullback h).length,
        ¬ ((S.take n).pullback h).center m ≤
          ((S.take n).pullback h).strictTransformSeq c' m.castSucc := by
      intro c' hc'
      rw [take_pullback]
      exact forall_not_center_le_take (S.pullback h) c' (by rwa [length_pullback])
        (fun m hm₁ => hhist' c' hc' m hm₁)
    -- the absorbed families are related as components
    have hFF' : IsPullbackComponents h (C.filter fun c => CenterContains S c n)
        (C'.filter fun c' => CenterContains (S.pullback h) c' n) := by
      intro c'
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hc', hcc'⟩
        obtain ⟨c, hc, η', hη', rfl⟩ := (hCC' c').mp hc'
        exact ⟨c, ⟨hc, (hiff c hc η' hη').mp hcc'⟩, η', hη', rfl⟩
      · rintro ⟨c, ⟨hc, hcc⟩, η', hη', rfl⟩
        exact ⟨(hCC' _).mpr ⟨c, hc, η', hη', rfl⟩, (hiff c hc η' hη').mpr hcc⟩
    have eF : (C'.filter fun c' => CenterContains (bmoOneRun T' hm') c' (eraseIdx (S.pullback h) n))
        = C'.filter fun c' => CenterContains (S.pullback h) c' n :=
      Finset.filter_congr fun c' _ => hE2 c'
    have eG : (C'.filter fun c' =>
        ¬ CenterContains (bmoOneRun T' hm') c' (eraseIdx (S.pullback h) n)) =
        C'.filter fun c' => ¬ CenterContains (S.pullback h) c' n :=
      Finset.filter_congr fun c' _ => not_congr (hE2 c')
    -- the isolated triple upstairs is the pull-back up to unit members of the one downstairs
    have hΓ := iSup_support_strictTransformSeq_eraseEmpty_pullback_last (S.take n) h g hg _ _ hFF'
    have hpg : (isolatedAt T' ((S.take n).pullback h).eraseEmpty hQ'
        (C'.filter fun c' => CenterContains (S.pullback h) c' n)).IsPullbackOfUpToUnits
          (isolatedAt T (S.take n) hQ (C.filter fun c => CenterContains S c n)) (e₀ ≫ g) :=
      isolatedAt_isPullbackOfUpToUnits (S.take n) hQ _ hQ' (e₀ ≫ g) hind _ _ hΓ
    -- the remaining members upstairs are the components of the preimages of those downstairs
    have hprime' : ∀ c₁ ∈ remainingAt (S.take n) (C.filter fun c => ¬ CenterContains S c n),
        ∃ ζ : (S.take n).stage (Fin.last _), c₁ = IdealSheafData.vanishingIdeal (Closeds.closure
            {ζ}) :=
      remainingAt_prime (S.take n) _ (fun c hc => hC c (Finset.mem_filter.mp hc).1)
        (fun c hc => hhistQ c (Finset.mem_filter.mp hc).1)
    have hR₀ : IsPullbackComponents g
        (remainingAt (S.take n) (C.filter fun c => ¬ CenterContains S c n))
        (remainingAt ((S.take n).pullback h)
          (C'.filter fun c' => ¬ CenterContains (S.pullback h) c' n)) :=
      isPullbackComponents_remainingAt (S.take n) h g hg
        (fun hη' hh hh' => exists_genericPoints_strictTransformSeq_pullback_last (S.take n) h hη'
          hh hh')
        C C' hC hCC' _ _ (fun c hc η' hη' => not_congr (hiff c hc η' hη')) hhistQ hhistQ'
    have hprimeR : ∀ b ∈ remainingAt ((S.take n).pullback h)
        (C'.filter fun c' => ¬ CenterContains (S.pullback h) c' n),
        ∃ η' : ((S.take n).pullback h).stage (Fin.last _),
          b = IdealSheafData.vanishingIdeal (Closeds.closure {η'}) := by
      intro b hb
      obtain ⟨c, -, η', -, rfl⟩ := (hR₀ b).mp hb
      exact ⟨η', rfl⟩
    have hR' : IsPullbackComponents (e₀ ≫ g)
        (remainingAt (S.take n) (C.filter fun c => ¬ CenterContains S c n))
        (remainingAt ((S.take n).pullback h).eraseEmpty
          (C'.filter fun c' => ¬ CenterContains (S.pullback h) c' n)) := by
      rw [remainingAt_eraseEmpty]
      exact isPullbackComponents_comp g e₀ hR₀
        (isPullbackComponents_image_comap_of_isIso e₀ hprimeR)
    -- the image hypothesis propagates: a component upstairs of a remaining member is alive at the
    -- end of the round and lies over the strict transform downstairs
    have hmeets₁ : ∀ c₁ ∈ remainingAt (S.take n) (C.filter fun c => ¬ CenterContains S c n),
        ∃ y : ((S.take n).pullback h).eraseEmpty.stage (Fin.last _), (e₀ ≫ g) y ∈ c₁.support := by
      intro c₁ hc₁
      obtain ⟨c, hcG, rfl⟩ := Finset.mem_image.mp hc₁
      obtain ⟨hc, -⟩ := Finset.mem_filter.mp hcG
      obtain ⟨x, hx⟩ := hmeets c hc
      obtain ⟨η', hη', -⟩ := Closeds.exists_mem_genericPoints_specializes
        (c.support.preimage h.continuous) (show x ∈ c.support.preimage h.continuous from hx)
      have hc' : IdealSheafData.vanishingIdeal (Closeds.closure {η'}) ∈ C' := (hCC' _).mpr ⟨c, hc,
          η', hη', rfl⟩
      have := isReduced_subscheme_vanishingIdeal (X := T'.X.left) (Closeds.closure {η'})
      obtain ⟨ζ', hζ', -, -⟩ := exists_isGenericPoint_strictTransformSeq ((S.take n).pullback h) _
        (Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η') (Fin.last _)
        (fun m _ => hhistQ' _ hc' m)
      obtain ⟨η, rfl⟩ := hC c hc
      rw [support_vanishingIdeal_eq] at hη'
      have hle : ((S.take n).pullback h).strictTransformSeq
            ((IdealSheafData.vanishingIdeal (Closeds.closure {η})).comap h) (Fin.last _) ≤
          ((S.take n).pullback h).strictTransformSeq (IdealSheafData.vanishingIdeal
              (Closeds.closure {η'}))
            (Fin.last _) :=
        strictTransformSeq_mono _ (comap_le_of_mem_genericPoints_preimage h hη') _
      have hmem : ζ' ∈ (((S.take n).strictTransformSeq (IdealSheafData.vanishingIdeal
          (Closeds.closure {η}))
          (Fin.last _)).comap g).support := by
        rw [← hg]
        exact IdealSheafData.support_antitone hle hζ'.mem
      refine ⟨(inv e₀) ζ', ?_⟩
      have he : e₀ ((inv e₀) ζ') = ζ' := by
        rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
        rfl
      rw [Scheme.Hom.comp_apply, he]
      exact (mem_support_comap_iff_apply _ _ _).mp hmem
    have hlt : (remainingComponents T hm C n).card < N := by
      have := card_remainingComponents_lt T hm C hex
      rw [← hn, hcard] at this
      exact this
    have hIH := @ih _ hlt (isolatedTriple T hm C n)
      (isolatedAt T' ((S.take n).pullback h).eraseEmpty hQ'
        (C'.filter fun c' => CenterContains (S.pullback h) c' n)) hm hm' (e₀ ≫ g) hsm₁ hpg
      (remainingComponents T hm C n)
      (remainingAt ((S.take n).pullback h).eraseEmpty
        (C'.filter fun c' => ¬ CenterContains (S.pullback h) c' n)) rfl hprime' hmeets₁ hR'
    -- assemble
    have hpc := pullback_concat ((bmoOneRun T hm).take n)
      (bedAux (isolatedTriple T hm C n) hm (remainingComponents T hm C n)) h
    rw [bedAux_eq_concat_of_find T' hm' C' hex' _ hfind,
      bedAux_eq_concat_of_find T hm C hex n hn.symm,
      concat_bedAux_congr T' hm' C' _ hQ'take hQ' eF eG, hpc, eraseEmpty_concat]
    refine congrArg (fun R => (((bmoOneRun T hm).take n).pullback h).eraseEmpty.concat R) ?_
    rw [hIH]
    exact (congrArg BlowUpSequence.eraseEmpty (pullback_comp _ e₀ g)).trans
      (eraseEmpty_pullback_of_flat_surjective _ e₀ (surjective_of_isIso e₀))
  · have hex' : ¬ ∃ n', HasAbsorptionAt T' hm' C' n' := by
      rintro ⟨n', c', hc', hcc'⟩
      rw [hR] at hcc'
      obtain ⟨m, hm₁, hne, he⟩ := exists_eraseIdx_eq (S.pullback h) n' hcc'.1
      rw [← he, centerContains_eraseEmpty_iff (S.pullback h) c' m hm₁ hne] at hcc'
      obtain ⟨c, hc, η', hη', rfl⟩ := (hCC' c').mp hc'
      have hnone : ∀ m' < m, ∀ c ∈ C, ¬ CenterContains S c m' :=
        fun m' _ c hc hcc => hex ⟨m', c, hc, hcc⟩
      exact hex ⟨m, c, hc, ((hstop m hnone).2 c hc η' hη').mp hcc'⟩
    rw [bedAux_of_not_exists T' hm' C' hex', bedAux_of_not_exists T hm C hex]
    exact hR

/-- **`BED` commutes with smooth morphisms up to empty blow-ups** ([Wlo05, Theorem 1.0.2] clause
(d); the second bullet of [Kol07, 34.1]): for a smooth `h : X' → X` carrying the pull-back data
whose image meets every irreducible component of `Y` (every specialization-maximal point `η` of
`V(I_Y)` has `Set.range h ∩ closure {η}` nonempty),
`BED(X', h^* I_Y, ∅) = (h^* BED(X, I_Y, ∅)).eraseEmpty` — the loop `bedAux_eraseEmpty_pullback` on
the components of `V(I_Y)` and of `V(h^* I_Y)` (`isPullbackComponents_componentIdeals`), the
generic points of the components being exactly the maximal points of the hypothesis. The
hypothesis `hE` is present because clause (d) of [Wlo05, Theorem 1.0.2] is stated for the
embedded desingularization of `Y` with empty boundary, the setting in which
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFunctorClauses` applies this theorem; the proof does
not need it, because the transport of the loop works for any marked triple of mark `1` whose members
are the reduced ideals of the components (`componentIdeals_prime`). -/
theorem bed_pullback_eraseEmpty (TX TX' : Triple k) (hE : IsEmpty TX.E.ι)
    (h : TX'.X.left ⟶ TX.X.left) [Smooth h] (hp : TX'.IsPullbackOf TX h)
    (hmeets : ∀ η ∈ (TX.I.support : Set TX.X.left),
      (∀ η' ∈ (TX.I.support : Set TX.X.left), η' ⤳ η → η' = η) →
      (Set.range h ∩ closure {η}).Nonempty) :
    BED TX' = ((BED TX).pullback h).eraseEmpty := by
  have _ := hE
  have hmeets' : ∀ c ∈ componentIdeals TX, ∃ x : TX'.X.left, h x ∈ c.support := by
    intro c hc
    have := Hironaka.BD.noetherianSpace_triple TX
    simp only [componentIdeals, Finset.mem_image, Set.Finite.mem_toFinset] at hc
    obtain ⟨η, hη, rfl⟩ := hc
    obtain ⟨x, ⟨x', rfl⟩, hxcl⟩ := hmeets η hη.1 (fun η' hη' hsp => hη.2 hη' hsp)
    refine ⟨x', ?_⟩
    rw [support_vanishingIdeal_eq]
    exact hxcl
  exact bedAux_eraseEmpty_pullback _ ⟨TX, 1⟩ ⟨TX', 1⟩ rfl rfl h
    (MarkedTriple.IsPullbackOf.upToUnits ⟨hp, rfl⟩) (componentIdeals TX) (componentIdeals TX') rfl
    (componentIdeals_prime TX) hmeets' (isPullbackComponents_componentIdeals TX TX' h hp)

end Hironaka.Resolution
