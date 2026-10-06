/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Defs
public import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.AnalyticSpace.CoherentColon
import Hironaka.AnalyticSpace.HomExt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The saturation of an ideal sheaf of finite type is of finite type

For ideal sheaves of finite type `J`, `I` on a `K`-analytic space `X`, the saturation
`⨆_k (J_x : I_x^k)` of `J` by `I` is again an ideal sheaf of finite type
(`saturation_hasLocalGenerators`). This is the finite type of the ideal of the strict transform
asserted in [BM97, Proposition 3.13 and the sentence after it] ("`I_{X'}` is an ideal of finite type
(since `X` is locally Noetherian)"), proved here over `K = ℝ` or `ℂ` at once and without the Noether
lemma. The argument uses only the recurrence of the colon chain `C_k := (J : I^k)`, which is
stationary near every point with a uniform index (`colonChain_locallyStationary`):

* (a) `C_{k+1} = (C_k : I)`, the associativity of colons (`colon_pow_succ`);
* (b) the stalk `𝒪_{X,x}` is Noetherian (`AnalyticSpace.isNoetherianRing_stalk`; Rückert's basis
  theorem [Dem, Ch. II, (2.7)], carried to the stalks of an analytic space through its local
  models), so the chain is stationary at `x` (`exists_colon_pow_stationary_at`);
* (c) one equality `C_{N,x} = C_{N+1,x}` of ideal sheaves of finite type propagates to a
  neighbourhood (`exists_opens_stalkIdeal_eq_of_le_of_eq`: an identity between finitely many germs
  holds nearby, [Fre17, Ch. I, 10.5]);
* (d) the recurrence carries the equality up the chain on that neighbourhood
  (`colonChain_locallyStationary`).

Hence the saturation has local generators (`saturation_hasLocalGenerators`, through the bridge
`hasLocalGenerators_iSup_colon_pow_of_colonChain_locallyStationary`). What the argument uses of the
chain is the recurrence, which an arbitrary increasing chain of ideal sheaves lacks; for those one
needs the Noether lemma. The theorem is the finite-type input of the strict transform
(`Hironaka.Manifold.BlowUp.Transform.SaturationFiniteType`).
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u

namespace AnalyticSpace

/-- In a commutative ring, `(J : I^{k+1}) = ((J : I^k) : I)`: the associativity of colons. -/
theorem colon_pow_succ {R : Type*} [CommRing R] (J I : Ideal R) (k : ℕ) :
    Submodule.colon J (SetLike.coe (I ^ (k + 1))) =
      Submodule.colon (Submodule.colon J (SetLike.coe (I ^ k))) (SetLike.coe I) := by
  ext a
  simp only [Submodule.mem_colon, SetLike.mem_coe, smul_eq_mul]
  constructor
  · intro h i hi p hp
    rw [mul_assoc, mul_comm i p]
    exact h _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hp hi)
  · intro h s hs
    rw [pow_succ] at hs
    refine Submodule.mul_induction_on hs (fun m hm n hn => ?_) (fun x y hx hy => ?_)
    · rw [mul_comm m n, ← mul_assoc]
      exact h n hn m hm
    · rw [mul_add]
      exact J.add_mem hx hy

/-- For ideal sheaves of finite type `A ≤ B` of a sheaf of rings with `A_x = B_x`, `A = B` on a
neighbourhood of `x` [Fre17, Ch. I, 10.5]: the finitely many local generators of `B` have germs in
`A_x`, hence are germs of sections of `A` (`mem_stalkIdeal_iff`), which agree with them near `x`; so
they generate stalks of `A` on the common neighbourhood. This uses that `IdealSheaf` carries finite
type. -/
theorem exists_opens_stalkIdeal_eq_of_le_of_eq {Y : TopCat.{u}} {𝒪 : TopCat.Sheaf CommRingCat.{u} Y}
    {A B : IdealSheaf 𝒪} (hAB : A ≤ B) {x : Y} (hx : A.stalkIdeal x = B.stalkIdeal x) :
    ∃ (W : Opens Y) (_ : x ∈ W), ∀ y ∈ W, A.stalkIdeal y = B.stalkIdeal y := by
  obtain ⟨U, hxU, k, b, hbB, hb⟩ := B.exists_generators x
  have hmem : ∀ i, 𝒪.presheaf.germ U x hxU (b i) ∈ A.stalkIdeal x := fun i =>
    hx ▸ B.germ_mem_stalkIdeal hxU (hbB i)
  choose V hxV g hgA hg using fun i => A.mem_stalkIdeal_iff.mp (hmem i)
  choose W hxW iV iU hW using fun i =>
    TopCat.Presheaf.germ_eq 𝒪.presheaf x (hxV i) hxU (g i) (b i) (hg i)
  have hmemInf : ∀ z : Y, z ∈ (U ⊓ ⨅ i, W i : Opens Y) ↔ z ∈ U ∧ ∀ i, z ∈ W i := by
    intro z
    rw [← SetLike.mem_coe, Opens.coe_inf, Opens.coe_iInf, Set.mem_inter_iff, Set.mem_iInter]
    simp only [SetLike.mem_coe]
  refine ⟨U ⊓ ⨅ i, W i, ?_, fun y hy => ?_⟩
  · exact (hmemInf x).mpr ⟨hxU, hxW⟩
  · obtain ⟨hyU, hyW⟩ := (hmemInf y).mp hy
    refine le_antisymm (hAB y) ?_
    rw [hb y hyU]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    dsimp only
    have h1 : 𝒪.presheaf.germ U y hyU (b i) =
        𝒪.presheaf.germ (W i) y (hyW i) (𝒪.presheaf.map (iU i).op (b i)) :=
      (TopCat.Presheaf.germ_res_apply 𝒪.presheaf (iU i) y (hyW i) (b i)).symm
    rw [h1, ← hW i, TopCat.Presheaf.germ_res_apply]
    exact A.germ_mem_stalkIdeal _ (hgA i)

variable {K : Type} [RCLike K]

/-- At a point `x` the increasing chain `k ↦ (J_x : I_x^k)` of ideals of the Noetherian stalk is
stationary (`monotone_stabilizes_iff_noetherian`). -/
theorem exists_colon_pow_stationary_at (X : AnalyticSpace.{u} K)
    (J I : IdealSheaf X.toLocallyRingedSpace.𝒪) (x : X) :
    ∃ N : ℕ, ∀ m ≥ N,
      Submodule.colon (J.stalkIdeal x) (SetLike.coe (I.stalkIdeal x ^ m)) =
        Submodule.colon (J.stalkIdeal x) (SetLike.coe (I.stalkIdeal x ^ N)) := by
  have hN : IsNoetherianRing (X.toLocallyRingedSpace.𝒪.presheaf.stalk x) :=
    AnalyticSpace.isNoetherianRing_stalk X x
  have hnoeth : _root_.IsNoetherian (X.toLocallyRingedSpace.𝒪.presheaf.stalk x)
      (X.toLocallyRingedSpace.𝒪.presheaf.stalk x) := isNoetherianRing_iff.mp hN
  let f : ℕ →o Ideal (X.toLocallyRingedSpace.𝒪.presheaf.stalk x) :=
    ⟨fun k => Submodule.colon (J.stalkIdeal x) (SetLike.coe (I.stalkIdeal x ^ k)),
      fun a b hab => Submodule.colon_mono le_rfl
        (SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right hab))⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr hnoeth f
  exact ⟨N, fun m hm => (hN m hm).symm⟩

/-- The finite type of the saturation from the local stationarity of the one colon chain
`k ↦ (J_x : I_x^k)`, proved by the argument of
`hasLocalGenerators_iSup_colon_pow_of_locallyStationary` (`Hironaka.AnalyticSpace.NoetherDerived`),
which cannot be invoked here because its hypothesis quantifies over every chain. -/
theorem hasLocalGenerators_iSup_colon_pow_of_colonChain_locallyStationary (X : AnalyticSpace.{u} K)
    (J I : IdealSheaf X.toLocallyRingedSpace.𝒪)
    (hloc : ∀ x : X, ∃ (V : Opens X) (_ : x ∈ V) (N : ℕ), ∀ m ≥ N, ∀ y ∈ V,
      Submodule.colon (J.stalkIdeal y) (SetLike.coe (I.stalkIdeal y ^ m)) =
        Submodule.colon (J.stalkIdeal y) (SetLike.coe (I.stalkIdeal y ^ N))) :
    IdealSheaf.HasLocalGenerators (𝒪 := X.toLocallyRingedSpace.𝒪)
      fun x : X => ⨆ k : ℕ,
        Submodule.colon (J.stalkIdeal x) (SetLike.coe (I.stalkIdeal x ^ k)) := by
  intro a
  obtain ⟨C, hC⟩ : ∃ C : ℕ → IdealSheaf X.toLocallyRingedSpace.𝒪, C = fun k =>
      IdealSheaf.ofStalks _ (fun x => Submodule.colon (J.stalkIdeal x)
        (SetLike.coe ((I ^ k).stalkIdeal x)))
        (hasLocalGenerators_colon_idealSheaf X J (I ^ k)) := ⟨_, rfl⟩
  have hCs : ∀ k (x : X), (C k).stalkIdeal x =
      Submodule.colon (J.stalkIdeal x) (SetLike.coe (I.stalkIdeal x ^ k)) := by
    intro k x
    rw [hC]
    dsimp only
    rw [IdealSheaf.stalkIdeal_ofStalks, IdealSheaf.stalkIdeal_pow]
  have hmono : ∀ k, C k ≤ C (k + 1) := by
    intro k x
    rw [hCs, hCs]
    exact Submodule.colon_mono le_rfl
      (SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right (Nat.le_succ k)))
  have hmono' : Monotone C := monotone_nat_of_le_succ hmono
  obtain ⟨V, haV, N, hN⟩ := hloc a
  obtain ⟨U', haU', l, g, -, hg⟩ := (C N).exists_generators a
  obtain ⟨U, hU⟩ : ∃ U, U = V ⊓ U' := ⟨_, rfl⟩
  have hUV : U ≤ V := hU ▸ inf_le_left
  have hUU' : U ≤ U' := hU ▸ inf_le_right
  have haU : a ∈ U := by
    rw [hU, ← SetLike.mem_coe, Opens.coe_inf]
    exact ⟨haV, haU'⟩
  refine ⟨U, haU, Fin l, inferInstance,
    fun i => X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE hUU').op (g i), fun b hb => ?_⟩
  have hsup : (⨆ k : ℕ, Submodule.colon (J.stalkIdeal b) (SetLike.coe (I.stalkIdeal b ^ k))) =
      (C N).stalkIdeal b := by
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le N (hCs N b).le)
    rw [← hCs]
    rcases le_total k N with hk | hk
    · exact IdealSheaf.le_def.mp (hmono' hk) b
    · rw [hCs, hCs, hN k hk b (hUV hb)]
  have hgi : ∀ i, X.toLocallyRingedSpace.𝒪.presheaf.germ U b hb
      (X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE hUU').op (g i)) =
        X.toLocallyRingedSpace.𝒪.presheaf.germ U' b (hUU' hb) (g i) := fun i =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  dsimp only
  rw [hsup, hg b (hUU' hb)]
  congr 1
  ext s
  simp only [Set.mem_range, hgi]

/-- **The colon chain `k ↦ (J_y : I_y^k)` of two ideal sheaves of finite type on a `K`-analytic
space is stationary with a uniform index near every point** (the conclusion asserted in [BM97,
Proposition 3.13 and the sentence after it]): (b) gives the index `N` at `x`, (c) propagates
`C_N = C_{N+1}` to a neighbourhood, and (a) carries it up the chain by induction. -/
theorem colonChain_locallyStationary (X : AnalyticSpace.{u} K)
    (J I : IdealSheaf X.toLocallyRingedSpace.𝒪) (x : X) :
    ∃ (V : Opens X) (_ : x ∈ V) (N : ℕ), ∀ m ≥ N, ∀ y ∈ V,
      Submodule.colon (J.stalkIdeal y) (SetLike.coe (I.stalkIdeal y ^ m)) =
        Submodule.colon (J.stalkIdeal y) (SetLike.coe (I.stalkIdeal y ^ N)) := by
  obtain ⟨C, hC⟩ : ∃ C : ℕ → IdealSheaf X.toLocallyRingedSpace.𝒪, C = fun k =>
      IdealSheaf.ofStalks _ (fun x => Submodule.colon (J.stalkIdeal x)
        (SetLike.coe ((I ^ k).stalkIdeal x)))
        (hasLocalGenerators_colon_idealSheaf X J (I ^ k)) := ⟨_, rfl⟩
  have hCs : ∀ k (x : X), (C k).stalkIdeal x =
      Submodule.colon (J.stalkIdeal x) (SetLike.coe (I.stalkIdeal x ^ k)) := by
    intro k x
    rw [hC]
    dsimp only
    rw [IdealSheaf.stalkIdeal_ofStalks, IdealSheaf.stalkIdeal_pow]
  have hmono : ∀ k, C k ≤ C (k + 1) := by
    intro k x
    rw [hCs, hCs]
    exact Submodule.colon_mono le_rfl
      (SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right (Nat.le_succ k)))
  obtain ⟨N, hN⟩ := exists_colon_pow_stationary_at X J I x
  have hxeq : (C N).stalkIdeal x = (C (N + 1)).stalkIdeal x := by
    rw [hCs, hCs]
    exact (hN (N + 1) (Nat.le_succ N)).symm
  obtain ⟨V, hxV, hV⟩ := exists_opens_stalkIdeal_eq_of_le_of_eq (hmono N) hxeq
  refine ⟨V, hxV, N, fun m hm y hy => ?_⟩
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [colon_pow_succ, ih, ← colon_pow_succ, ← hCs (N + 1) y, ← hCs N y]
    exact (hV y hy).symm

/-- **The saturation `⨆_k (J_x : I_x^k)` of an ideal sheaf of finite type by another is of finite
type**, over `K = ℝ` or `ℂ` [BM97, Proposition 3.13 and the sentence after it]: the bridge applied
to `colonChain_locallyStationary`. This is the finite-type input of the strict transform of a closed
subspace. -/
theorem saturation_hasLocalGenerators (X : AnalyticSpace.{u} K)
    (J I : IdealSheaf X.toLocallyRingedSpace.𝒪) :
    IdealSheaf.HasLocalGenerators (𝒪 := X.toLocallyRingedSpace.𝒪)
      fun x : X => ⨆ k : ℕ,
        Submodule.colon (J.stalkIdeal x) (SetLike.coe (I.stalkIdeal x ^ k)) :=
  hasLocalGenerators_iSup_colon_pow_of_colonChain_locallyStationary X J I
    (colonChain_locallyStationary X J I)

end AnalyticSpace

end
