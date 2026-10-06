/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs
public import Hironaka.Manifold.LocalDiffeomorph
import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Hom
import Hironaka.Manifold.FiniteSuccession.Functor.LiftedFibre
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Submanifold.CodimUnique
import Hironaka.Resolution.Analytic.Functor.ExtensionOf
import Hironaka.Resolution.Analytic.Wlo09.FamilyCoherence

/-!
# The lifts of a pull-back up to empty blow-ups are bijective on the fibres

For `R.IsPullbackUpToEmptyAlong S g` ([Wlo09, Theorem 3.5.1 (2)] read on successions), the lifts
`f_k : R_{j_k} → S_k` of the local analytic isomorphism `g` are local analytic isomorphisms over
`g`; this module shows that each `f_k` maps the fibre of the composite blow-down of `R` over a
point `y` bijectively onto the fibre of the composite blow-down of `S` over `g y`
(`FiniteSuccession.bijOn_fiber_of_isPullbackUpToEmptyAlong_clauses`). This is the sense in which
the stages of `R` are the fibre products `N ×_M S_k` [Wlo09, Proposition 3.4.1], stated without
forming them; it is what the global lift of `g` to the principalizations
(`Hironaka/Resolution/Analytic/Wlo09/FamilyLift.lean`) needs to identify `Ñ` with `N ×_M M̃`.

The argument is an induction on the stage. At stage `0` the lift is the restriction of `g`, and
both fibres are single points. At a step where `S` blows up a centre `Z` and `R` blows up its
pull-back `f_k⁻¹(Z)`, a continuous map over `f_k` between the two blowings-up is bijective over
a local inverse of `f_k` (`injOn_of_comm_local`, `exists_eq_of_comm_local`, from the uniqueness
of the blowing-up), so `f_{k+1}` maps the fibre of the blow-down over `c` bijectively onto the
fibre over `f_k c` (`bijOn_fiber_of_comm`; a point off the pulled-back centre has a single
preimage on both sides, a centre of codimension `0` has none, and the chart data of the two
blowings-up are aligned by `IsBlowUp.congr_chart` and `IsClosedSubmanifold.codim_eq_of_nonempty`).
At a step where the pulled-back centre is empty, the blow-up of `S` is a bijection over the
complement of its centre, which contains the range of `f_k`.

* `stageMapLE_bijective_of_eq`, `stageMapLE_apply_of_eq`: at two equal indices the composite
  `stageMapLE` is a bijection commuting with the composite blow-downs (the transported identity).
* `PartialDiffeomorph.restrOpen`, `IsLocalDiffeomorphAt.congr_of_eventuallyEq`: a map agreeing
  near a point with a local analytic isomorphism at that point is one.
* `bijOn_fiber_of_comm`: the one-step fibre bijection.
* `bijOn_fiber_of_isPullbackUpToEmptyAlong_clauses`: the fibre bijection at every stage, and
  `IsPullbackUpToEmptyAlong.exists_lift_bijOn_fiber` for the last stage, with the lift carried to
  the last stage of `R`.
-/

@[expose] public section

noncomputable section

open Set Topology Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

/-! ### Partial diffeomorphisms restricted to an open subset -/

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H₁ : Type*} [TopologicalSpace H₁] {H₂ : Type*} [TopologicalSpace H₂]
  {I : ModelWithCorners 𝕜 E H₁} {J : ModelWithCorners 𝕜 F H₂}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H₁ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N] {n : WithTop ℕ∞}

/-- The restriction of a partial diffeomorphism to an open subset `s` of its domain: the source
becomes `Φ.source ∩ s`, the target its image. -/
def restrOpen (Φ : PartialDiffeomorph I J M N n) (s : Set M) (hs : IsOpen s) :
    PartialDiffeomorph I J M N n where
  toPartialEquiv := Φ.toPartialEquiv.restr s
  open_source := by
    rw [PartialEquiv.restr_source]
    exact Φ.open_source.inter hs
  open_target := by
    rw [PartialEquiv.restr_target]
    exact Φ.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage Φ.open_target hs
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono fun _ hx => hx.1
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono fun _ hx => hx.1

theorem restrOpen_source (Φ : PartialDiffeomorph I J M N n) (s : Set M) (hs : IsOpen s) :
    (Φ.restrOpen s hs).source = Φ.source ∩ s :=
  PartialEquiv.restr_source _ _

theorem restrOpen_apply (Φ : PartialDiffeomorph I J M N n) (s : Set M) (hs : IsOpen s) (x : M) :
    Φ.restrOpen s hs x = Φ x := rfl

end PartialDiffeomorph

/-- A map which agrees near `x` with a local diffeomorphism at `x` is a local diffeomorphism at
`x`: the partial diffeomorphism of the latter, restricted to the open set where the two agree. -/
theorem IsLocalDiffeomorphAt.congr_of_eventuallyEq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H₁ : Type*} [TopologicalSpace H₁] {H₂ : Type*} [TopologicalSpace H₂]
    {I : ModelWithCorners 𝕜 E H₁} {J : ModelWithCorners 𝕜 F H₂}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H₁ M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N] {n : WithTop ℕ∞}
    {f f' : M → N} {x : M} (hf' : IsLocalDiffeomorphAt I J n f' x) (h : f =ᶠ[𝓝 x] f') :
    IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨Φ, hx, hΦ⟩ := hf'.exists_partialDiffeomorph
  obtain ⟨s, hs, hso, hxs⟩ := mem_nhds_iff.mp h
  refine IsLocalDiffeomorphAt.of_eqOn (Φ.restrOpen s hso) ?_ ?_
  · rw [PartialDiffeomorph.restrOpen_source]
    exact ⟨hx, hxs⟩
  · intro p hp
    rw [PartialDiffeomorph.restrOpen_source] at hp
    exact (hs hp.2).trans (hΦ hp.1)

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### The composite between two equal stages -/

section StageMapLEEq

variable {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- At two equal indices the composite `stageMapLE` is a bijection (the transported identity,
`stageMapLE_self`). -/
theorem stageMapLE_bijective_of_eq {a b : Fin (S.length + 1)} (hab : a = b) (hle : a ≤ b) :
    Function.Bijective (S.stageMapLE hle) := by
  subst hab
  rw [stageMapLE_self]
  exact Function.bijective_id

/-- At two equal indices the composite `stageMapLE` is a local analytic isomorphism. -/
theorem stageMapLE_isLocalDiffeomorph_of_eq {a b : Fin (S.length + 1)} (hab : a = b)
    (hle : a ≤ b) : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (S.stageMapLE hle) := by
  subst hab
  rw [stageMapLE_self]
  exact (Diffeomorph.refl 𝓘(𝕜, E) _ ω).isLocalDiffeomorph

end StageMapLEEq

/-! ### The one-step fibre bijection -/

section Step

variable {N₀ M₀ N' M' : AnalyticManifold.{u} 𝕜 E} {n n' : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
  {ψ' : E ≃L[𝕜] (Fin n' → 𝕜)} {Y : Set M₀} {c c' : ℕ} {h : AnalyticMap N₀ M₀}

/-- A blowing-up along a centre of codimension `0` has no point over the centre (there is no
blow-up chart of index `i : Fin 0`, while the charts cover the preimage of every adapted chart). -/
theorem _root_.Manifold.IsBlowUp.notMem_preimage_of_codim_zero (hY : IsClosedSubmanifold ψ Y 0)
    {π : M' → M₀} (hπ : IsBlowUp ψ Y 0 π) (p : M') : π p ∉ Y := by
  intro hp
  obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart (π p) hp
  obtain ⟨i, -, -, -⟩ := hπ.cover φ σ hφ p haφ
  exact i.elim0

/-- **The one-step fibre bijection.** For `h : N₀ → M₀` a local analytic isomorphism, `π` the
blowing-up of `M₀` along the closed submanifold `Y` and `π'` the blowing-up of `N₀` along
`h⁻¹(Y)` (with any chart data), a continuous map `G` over `h` maps the fibre of `π'` over every
`b` bijectively onto the fibre of `π` over `h b`. Over a point off `h⁻¹(Y)` both fibres are
single points (`IsBlowUp.bijOn_compl`); over a point of `h⁻¹(Y)` the codimensions agree
(`IsClosedSubmanifold.codim_eq_of_nonempty`), a codimension `0` leaves both fibres empty, and
otherwise `G` is a bijection over a local inverse of `h` (`injOn_of_comm_local`,
`exists_eq_of_comm_local`). -/
theorem bijOn_fiber_of_comm (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hY : IsClosedSubmanifold ψ Y c) {π : M' → M₀} (hπ : IsBlowUp ψ Y c π) {π' : N' → N₀}
    (hY' : IsClosedSubmanifold ψ' (⇑h ⁻¹' Y) c') (hπ' : IsBlowUp ψ' (⇑h ⁻¹' Y) c' π')
    {G : N' → M'} (hG : Continuous G) (hGπ : ∀ q, π (G q) = h (π' q)) (b : N₀) :
    BijOn G (π' ⁻¹' {b}) (π ⁻¹' {h b}) := by
  have hmaps : MapsTo G (π' ⁻¹' {b}) (π ⁻¹' {h b}) := fun q hq => by
    rw [mem_preimage, mem_singleton_iff, hGπ, (mem_singleton_iff.mp hq)]
  by_cases hb : b ∈ ⇑h ⁻¹' Y
  · -- over a point of the pulled-back centre: align the chart data
    have hne : (⇑h ⁻¹' Y).Nonempty := ⟨b, hb⟩
    have hcc : c' = c :=
      IsClosedSubmanifold.codim_eq_of_nonempty hY' (hY.preimage_of_isLocalDiffeomorph hh) hne
    subst hcc
    have hπ'' : IsBlowUp ψ (⇑h ⁻¹' Y) c' π' := hπ'.congr_chart ψ
    have hY'' : IsClosedSubmanifold ψ (⇑h ⁻¹' Y) c' := hY'.congr_chart ψ
    rcases Nat.eq_zero_or_pos c' with hc | hc
    · -- codimension `0`: both fibres are empty
      subst hc
      have h1 : π' ⁻¹' {b} = ∅ := eq_empty_of_forall_notMem fun q hq =>
        hπ''.notMem_preimage_of_codim_zero hY'' q (by rw [mem_singleton_iff.mp hq]; exact hb)
      have h2 : π ⁻¹' {h b} = ∅ := eq_empty_of_forall_notMem fun p hp =>
        hπ.notMem_preimage_of_codim_zero hY p (by rw [mem_singleton_iff.mp hp]; exact hb)
      rw [h1, h2]
      exact bijOn_empty G
    · -- positive codimension: the local inverse of `h` at `b`
      obtain ⟨Φ, hbΦ, hΦ⟩ := (hh b).exists_partialDiffeomorph
      obtain ⟨q₀, hq₀⟩ := hπ''.surjective hY'' ⟨0, hc⟩ b
      have : Nonempty N' := ⟨q₀⟩
      have : Nonempty M' := ⟨G q₀⟩
      refine ⟨hmaps, ?_, ?_⟩
      · exact (injOn_of_comm_local hh hY hπ hπ'' hG hGπ hΦ).mono fun q hq =>
          mem_preimage.mpr (by rw [mem_singleton_iff.mp hq]; exact hbΦ)
      · intro p hp
        have hpt : π p ∈ Φ.target := by
          rw [mem_singleton_iff.mp hp, hΦ hbΦ]
          exact Φ.map_source hbΦ
        obtain ⟨u, hu, hGu⟩ := exists_eq_of_comm_local hh hY hπ hπ'' hG hGπ hΦ hpt
        refine ⟨u, ?_, hGu⟩
        rw [mem_preimage, mem_singleton_iff]
        apply Φ.injOn hu hbΦ
        rw [← hΦ hu, ← hΦ hbΦ, ← hGπ, hGu]
        exact mem_singleton_iff.mp hp
  · -- off the pulled-back centre: both fibres are single points
    have hb' : h b ∉ Y := hb
    refine ⟨hmaps, fun q₁ hq₁ q₂ hq₂ hG12 => ?_, fun p hp => ?_⟩
    · exact hπ'.bijOn_compl.injOn (by rw [mem_preimage, mem_singleton_iff.mp hq₁]; exact hb)
        (by rw [mem_preimage, mem_singleton_iff.mp hq₂]; exact hb)
        ((mem_singleton_iff.mp hq₁).trans (mem_singleton_iff.mp hq₂).symm)
    · obtain ⟨q, -, hq⟩ := hπ'.bijOn_compl.surjOn (show b ∈ (⇑h ⁻¹' Y)ᶜ from hb)
      refine ⟨q, mem_preimage.mpr (mem_singleton_iff.mpr hq), ?_⟩
      apply hπ.bijOn_compl.injOn
      · rw [mem_preimage, hGπ, hq]
        exact hb'
      · rw [mem_preimage, mem_singleton_iff.mp hp]
        exact hb'
      · rw [hGπ, hq, mem_singleton_iff.mp hp]

end Step

/-! ### The fibre bijection along a pull-back up to empty blow-ups -/

section Fibre

variable {M N : AnalyticManifold.{u} 𝕜 E} {U : Opens M} {U' : Opens N}
  (R : FiniteSuccession (N.restrict U')) (S : FiniteSuccession (M.restrict U)) (g : AnalyticMap N M)

/-- The fibre of the composite blow-down of `R` at stage `a` over `y`. -/
def fiberR (a : Fin (R.length + 1)) (y : N.restrict U') : Set (R.stage a) :=
  {p | R.stageMap a p = y}

/-- The fibre of the composite blow-down of `S` at stage `k` over `g y`, read in `M`. -/
def fiberS (k : Fin (S.length + 1)) (y : N.restrict U') : Set (S.stage k) :=
  {s | M.inclusion U (S.stageMap k s) = g (N.inclusion U' y)}

variable {R S g}

/-- The fibre at an index equal to `0` is a single point. -/
theorem fiberR_eq_of_eq_zero {a : Fin (R.length + 1)} (ha : a = 0) (y : N.restrict U') :
    ∃ p₀ : R.stage a, fiberR R a y = {p₀} := by
  subst ha
  exact ⟨y, by ext p; exact Iff.rfl⟩

/-- Two points of the fibre of `S` at stage `0` over `g y` coincide. -/
theorem fiberS_zero_eq (y : N.restrict U') {s₁ s₂ : S.stage 0} (h₁ : s₁ ∈ fiberS S g 0 y)
    (h₂ : s₂ ∈ fiberS S g 0 y) : s₁ = s₂ := by
  have h : M.inclusion U (S.stageMap 0 s₁) = M.inclusion U (S.stageMap 0 s₂) :=
    (h₁ : M.inclusion U (S.stageMap 0 s₁) = _).trans (h₂ : M.inclusion U (S.stageMap 0 s₂) = _).symm
  exact Subtype.ext h

/-- The fibre of `R` at the stage after `j`, pulled down by the blow-up, lies in the fibre at the
stage of `j`. -/
theorem map_mem_fiberR {j : Fin R.length} {y : N.restrict U'} {p : R.stage j.succ}
    (hp : p ∈ fiberR R j.succ y) : R.map j p ∈ fiberR R j.castSucc y :=
  hp

/-- The fibre of `S` at the stage after `k`, pulled down by the blow-up, lies in the fibre at the
stage of `k`. -/
theorem map_mem_fiberS {k : Fin S.length} {y : N.restrict U'} {s : S.stage k.succ}
    (hs : s ∈ fiberS S g k.succ y) : S.map k s ∈ fiberS S g k.castSucc y :=
  hs

/-- **A non-jump step.** The stages `a = b` of `R` carry two lifts `fa`, `fb` to consecutive
stages of `S` with `σ^S_{k+1} ∘ fb = fa` (through the transported identity `stageMapLE`), and the
pull-back of the centre of `S` along `fa` is empty. Then the fibre bijection passes from `fa` to
`fb`: the blow-up of `S` is a bijection over the complement of its centre, which contains the
range of `fa`. -/
theorem bijOn_fiber_nonjump {k : Fin S.length} {a b : Fin (R.length + 1)} (hb : b = a)
    (hle : a ≤ b) (fa : AnalyticMap (R.stage a) (S.stage k.castSucc))
    (fb : AnalyticMap (R.stage b) (S.stage k.succ))
    (hmap : ∀ p, S.map k (fb p) = fa (R.stageMapLE hle p))
    (hcen : ((S.center k).pullback fa fa.contMDiff).support = ∅) (y : N.restrict U')
    (hmaps : MapsTo fb (fiberR R b y) (fiberS S g k.succ y))
    (ih : BijOn fa (fiberR R a y) (fiberS S g k.castSucc y)) :
    BijOn fb (fiberR R b y) (fiberS S g k.succ y) := by
  subst hb
  have hid : ∀ p, R.stageMapLE hle p = p := fun p => by
    rw [R.stageMapLE_self b hle]
    rfl
  have hnot : ∀ p, fa p ∉ (S.center k).support := fun p hp => by
    rw [_root_.Manifold.IdealSheaf.support_pullback] at hcen
    exact (eq_empty_iff_forall_notMem.mp hcen) p hp
  have hcompl := (S.isBlowUp_map k).bijOn_compl
  refine ⟨hmaps, fun p₁ hp₁ p₂ hp₂ hf => ?_, fun s hs => ?_⟩
  · have h1 := hmap p₁
    rw [hf, hmap p₂, hid, hid] at h1
    exact (ih.injOn hp₂ hp₁ h1).symm
  · obtain ⟨p, hp, hfp⟩ := ih.surjOn (map_mem_fiberS hs)
    refine ⟨p, hp, ?_⟩
    apply hcompl.injOn
    · rw [mem_preimage, hmap p, hid]
      exact hnot p
    · rw [mem_preimage, ← hfp]
      exact hnot p
    · rw [hmap p, hid, hfp]

/-- **A jump step.** The stage `b` of `R` is the stage after `j`, the blow-up of `R` along the
pull-back of the centre of `S` at stage `k`, and `σ^S_{k+1} ∘ fb = fa ∘ σ^R_{j+1}` (through
`stageMapLE`, which is `σ^R_{j+1}` here). The fibre bijection passes from `fa` to `fb` by the
one-step fibre bijection over every point of the fibre of `R` at stage `j`
(`bijOn_fiber_of_comm`). -/
theorem bijOn_fiber_jump {k : Fin S.length} {j : Fin R.length} {b : Fin (R.length + 1)}
    (hb : b = j.succ) (hle : j.castSucc ≤ b)
    (fa : AnalyticMap (R.stage j.castSucc) (S.stage k.castSucc))
    (fb : AnalyticMap (R.stage b) (S.stage k.succ))
    (hfa : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω fa)
    (hmap : ∀ p, S.map k (fb p) = fa (R.stageMapLE hle p))
    (hcen : R.center j = (S.center k).pullback fa fa.contMDiff) (y : N.restrict U')
    (hmaps : MapsTo fb (fiberR R b y) (fiberS S g k.succ y))
    (ih : BijOn fa (fiberR R j.castSucc y) (fiberS S g k.castSucc y)) :
    BijOn fb (fiberR R b y) (fiberS S g k.succ y) := by
  subst hb
  -- `stageMapLE hle` is the blow-up `σ^R_{j+1}`
  have hdec : ∀ p, R.stageMapLE hle p = R.map j p := fun p => by
    rw [R.stageMapLE_succ (b := j) hle le_rfl]
    change R.stageMapLE (le_refl j.castSucc) (R.map j p) = R.map j p
    rw [R.stageMapLE_self j.castSucc le_rfl]
    rfl
  -- the support of the pulled-back centre
  have hsupp : (R.center j).support = ⇑fa ⁻¹' (S.center k).support := by
    rw [hcen, _root_.Manifold.IdealSheaf.support_pullback]
  have hY' : IsClosedSubmanifold (R.chartAt j) (⇑fa ⁻¹' (S.center k).support) (R.codim j) := by
    rw [← hsupp]
    exact R.isClosedSubmanifold_center j
  have hπ' : IsBlowUp (R.chartAt j) (⇑fa ⁻¹' (S.center k).support) (R.codim j) (R.map j) := by
    rw [← hsupp]
    exact R.isBlowUp_map j
  -- the one-step bijection over every point of the stage `j`
  have hstep : ∀ c₀ : R.stage j.castSucc,
      BijOn fb (R.map j ⁻¹' {c₀}) (S.map k ⁻¹' {fa c₀}) := fun c₀ =>
    bijOn_fiber_of_comm hfa (S.isClosedSubmanifold_center k) (S.isBlowUp_map k) hY' hπ'
      fb.contMDiff.continuous (fun q => by rw [hmap q, hdec q]) c₀
  refine ⟨hmaps, fun p₁ hp₁ p₂ hp₂ hf => ?_, fun s hs => ?_⟩
  · have hc : R.map j p₁ = R.map j p₂ := by
      refine ih.injOn (map_mem_fiberR hp₁) (map_mem_fiberR hp₂) ?_
      rw [← hdec, ← hdec, ← hmap, ← hmap, hf]
    exact (hstep (R.map j p₁)).injOn rfl hc.symm hf
  · obtain ⟨c₀, hc₀, hfc₀⟩ := ih.surjOn (map_mem_fiberS hs)
    obtain ⟨p, hp, hfp⟩ := (hstep c₀).surjOn
      (show s ∈ S.map k ⁻¹' {fa c₀} by rw [mem_preimage, mem_singleton_iff, hfc₀])
    refine ⟨p, ?_, hfp⟩
    change R.stageMap j.castSucc (R.map j p) = y
    rw [mem_singleton_iff.mp hp]
    exact hc₀

/-- **The fibre bijection at every stage**, for the clauses of `IsPullbackUpToEmptyAlong`: the lift
`f k` maps the fibre of the composite blow-down of `R` at stage `blk k` over `y` bijectively onto
the fibre of the composite blow-down of `S` at stage `k` over `g y`. Induction on `k`: at stage `0`
the fibres are single points; at a non-jump `bijOn_fiber_nonjump`, at a jump `bijOn_fiber_jump`. -/
theorem bijOn_fiber_of_isPullbackUpToEmptyAlong_clauses
    (blk : Fin (S.length + 1) → Fin (R.length + 1))
    (f : ∀ k, AnalyticMap (R.stage (blk k)) (S.stage k)) (h0 : blk 0 = 0)
    (hstep : ∀ k : Fin S.length,
      (blk k.succ : ℕ) = blk k.castSucc ∨ (blk k.succ : ℕ) = blk k.castSucc + 1)
    (hld : ∀ k, IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (f k))
    (hov : ∀ k p, M.inclusion U (S.stageMap k (f k p)) = g (N.inclusion U' (R.stageMap (blk k) p)))
    (hm : ∀ (k : Fin S.length) (hle : blk k.castSucc ≤ blk k.succ) (p : R.stage (blk k.succ)),
      S.map k (f k.succ p) = f k.castSucc (R.stageMapLE hle p))
    (hcj : ∀ (k : Fin S.length) (ha : (blk k.castSucc : ℕ) < R.length),
      (blk k.succ : ℕ) = blk k.castSucc + 1 →
        R.centerAt (blk k.castSucc) ha =
          (S.center k).pullback (f k.castSucc) (f k.castSucc).contMDiff)
    (hcn : ∀ k : Fin S.length, (blk k.succ : ℕ) = blk k.castSucc →
      ((S.center k).pullback (f k.castSucc) (f k.castSucc).contMDiff).support = ∅)
    (k : Fin (S.length + 1)) (y : N.restrict U') :
    BijOn (f k) (fiberR R (blk k) y) (fiberS S g k y) := by
  -- the lifts map fibres to fibres, at every stage
  have hmaps : ∀ k, MapsTo (f k) (fiberR R (blk k) y) (fiberS S g k y) := fun k p hp => by
    change M.inclusion U (S.stageMap k (f k p)) = g (N.inclusion U' y)
    rw [hov k p, show R.stageMap (blk k) p = y from hp]
  induction k using Fin.induction with
  | zero =>
    obtain ⟨p₀, hp₀⟩ := fiberR_eq_of_eq_zero h0 y
    refine ⟨hmaps 0, ?_, fun s hs => ?_⟩
    · rw [hp₀]
      exact injOn_singleton _ _
    · refine ⟨p₀, by rw [hp₀]; exact mem_singleton p₀, ?_⟩
      exact fiberS_zero_eq y (hmaps 0 (by rw [hp₀]; exact mem_singleton p₀)) hs
  | succ k ih =>
    rcases hstep k with hj | hj
    · exact bijOn_fiber_nonjump (Fin.ext hj) (Fin.le_iff_val_le_val.mpr hj.ge) (f k.castSucc)
        (f k.succ) (hm k _) (hcn k hj) y (hmaps k.succ) ih
    · have ha : (blk k.castSucc : ℕ) < R.length := by
        have := (blk k.succ).2
        omega
      exact bijOn_fiber_jump (j := ⟨blk k.castSucc, ha⟩) (Fin.ext hj)
        (Fin.le_iff_val_le_val.mpr (by simp only [Fin.val_castSucc]; omega))
        (f k.castSucc) (f k.succ) (hld _) (hm k _) (hcj k ha hj) y (hmaps k.succ) ih

/-- **The last lift of a pull-back up to empty blow-ups is bijective on the fibres**, carried to
the last stage of `R`: for `R.IsPullbackUpToEmptyAlong S g` there is a local analytic isomorphism
`φ : R_{r'} → S_r` over `g` which maps the fibre of the composite of `R` over every `y` bijectively
onto the fibre of the composite of `S` over `g y`. The last lift of any witness, after the
transported identity `stageMapLE` from the last stage of `R` to the stage `blk r`. -/
theorem IsPullbackUpToEmptyAlong.exists_lift_bijOn_fiber (h : R.IsPullbackUpToEmptyAlong S g) :
    ∃ φ : AnalyticMap R.last S.last,
      IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ ∧
      (∀ p, M.inclusion U (S.composite (φ p)) = g (N.inclusion U' (R.composite p))) ∧
      ∀ y : N.restrict U', BijOn φ (fiberR R (Fin.last _) y) (fiberS S g (Fin.last _) y) := by
  obtain ⟨blk, f, h0, hl, hstep, hld, hov, hm, hcj, hcn⟩ := isPullbackUpToEmptyAlong_iff.mp h
  have hle : blk (Fin.last _) ≤ Fin.last _ := hl.le
  set t := R.stageMapLE hle with ht
  have htb := R.stageMapLE_bijective_of_eq hl hle
  have htl := R.stageMapLE_isLocalDiffeomorph_of_eq hl hle
  have htm : ∀ p, R.stageMap (blk (Fin.last _)) (t p) = R.stageMap (Fin.last _) p := fun p =>
    R.stageMap_stageMapLE_of_eq hl p
  refine ⟨(f (Fin.last _)).comp t,
    fun p => IsLocalDiffeomorphAt.comp (hf := htl p) (hg := hld (Fin.last _) (t p)),
    fun p => ?_, fun y => ?_⟩
  · change M.inclusion U (S.stageMap (Fin.last _) (f (Fin.last _) (t p))) = _
    rw [hov, htm]
    rfl
  · have hb := bijOn_fiber_of_isPullbackUpToEmptyAlong_clauses blk f h0 hstep hld hov hm hcj hcn
      (Fin.last _) y
    have htfib : ∀ p, p ∈ fiberR R (Fin.last _) y ↔ t p ∈ fiberR R (blk (Fin.last _)) y :=
      fun p => by
        change R.stageMap (Fin.last _) p = y ↔ R.stageMap (blk (Fin.last _)) (t p) = y
        rw [htm]
    refine ⟨fun p hp => hb.mapsTo ((htfib p).mp hp), fun p₁ hp₁ p₂ hp₂ hf => ?_, fun s hs => ?_⟩
    · exact htb.1 (hb.injOn ((htfib p₁).mp hp₁) ((htfib p₂).mp hp₂) hf)
    · obtain ⟨p', hp', hfp'⟩ := hb.surjOn hs
      obtain ⟨p, rfl⟩ := htb.2 p'
      exact ⟨p, (htfib p).mpr hp', hfp'⟩

end Fibre

end AnalyticManifold.FiniteSuccession

end

end
