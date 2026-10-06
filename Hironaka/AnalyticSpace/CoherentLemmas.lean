/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Coherent
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Locally finitely generated systems: bookkeeping

Lemmas on the definitions of `Hironaka/AnalyticSpace/Coherent.lean`, the "obvious" parts of
[Fre17, Ch. I, §10] and [Fre17, Ch. V, §7]:

* `mem_relationSubmodule_iff`: `a ∈ ker F_y ↔ ∀ i, Σ_j (F i j)_y * a j = 0`, Freitag's `F_a`;
* restriction of a matrix of sections to a smaller open does not change the relation modules
  (`relationSubmodule_res`), and locally finitely generated systems restrict
  (`HasLocalGeneratorsOn.mono`) and are local (`hasLocalGeneratorsOn_of_forall_exists`)
  [Fre17, Ch. I, 10.2];
* the facts about `⊤`: `(⊤ : IdealSheaf 𝒪).IsCoherent ↔ ∀ J, J.IsCoherent`
  (`IdealSheaf.isCoherent_top_iff`; every family of sections is a family of sections of `⊤`), and
  `IsCoherent 𝒪 → (⊤).IsCoherent` (the `q = 1` slice, `IsCoherent.isCoherent_top`);
* the first step of Oka's theorem [Fre17, Ch. I, 10.3]: coherence of the sheaf of rings follows
  from the one-row case by induction on the number of rows (`isCoherent_of_isCoherent_top`), so
  that `𝒪_X` is coherent iff every ideal sheaf of finite type is
  (`isCoherent_iff_forall_isCoherent_idealSheaf`, the equivalence recalled in [BM97, (3.8)]).

The bridge between `IdealSheaf.HasLocalGenerators` (one generator per section, on the whole space)
and `HasLocalGeneratorsOn` with `p = 1` is `hasLocalGenerators_iff_hasLocalGeneratorsOn_top` in
`Hironaka/AnalyticSpace/CoherentAnalytic.lean`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Manifold

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf CommRingCat.{u} X}

section Relation

variable {U : Opens X} {p q : ℕ}

/-- Freitag's `F_a`: `a` is a relation at `y` iff every row of `F` vanishes on `a` at `y`. -/
theorem mem_relationSubmodule_iff (F : Fin q → Fin p → 𝒪.presheaf.obj (op U)) {y : X} (hy : y ∈ U)
    (a : Fin p → 𝒪.presheaf.stalk y) :
    a ∈ relationSubmodule 𝒪 F y hy ↔ ∀ i, ∑ j, 𝒪.presheaf.germ U y hy (F i j) * a j = 0 :=
  mem_relKer_iff _ a

/-- Restricting the matrix of sections to a smaller open does not change the relation module at a
point of
the smaller open. -/
theorem relationSubmodule_res {V : Opens X} (hVU : V ≤ U)
    (F : Fin q → Fin p → 𝒪.presheaf.obj (op U)) {y : X} (hy : y ∈ V) :
    relationSubmodule 𝒪 (fun i j => 𝒪.presheaf.map (homOfLE hVU).op (F i j)) y hy =
      relationSubmodule 𝒪 F y (hVU hy) := by
  ext a
  simp only [mem_relationSubmodule_iff, TopCat.Presheaf.germ_res_apply]

end Relation

section LocalGenerators

variable {U : Opens X} {p : ℕ}

/-- Local finite generation restricts to smaller opens [Fre17, Ch. I, 10.2]. -/
theorem HasLocalGeneratorsOn.mono
    {M : ∀ y : X, y ∈ U → Submodule (𝒪.presheaf.stalk y) (Fin p → 𝒪.presheaf.stalk y)}
    (h : HasLocalGeneratorsOn 𝒪 U p M) {V : Opens X} (hVU : V ≤ U) :
    HasLocalGeneratorsOn 𝒪 V p fun y hy => M y (hVU hy) := by
  intro x hx
  obtain ⟨W, hWU, hxW, k, r, hr⟩ := h x (hVU hx)
  refine ⟨W ⊓ V, inf_le_right, ⟨hxW, hx⟩, k,
    fun l j => 𝒪.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op (r l j), fun y hy => ?_⟩
  have : (fun l => fun j => 𝒪.presheaf.germ (W ⊓ V) y hy
      (𝒪.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op (r l j))) =
      fun l => fun j => 𝒪.presheaf.germ W y hy.1 (r l j) := by
    funext l j
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [this]
  exact hr y hy.1

/-- A system is locally finitely generated on `U` if every point of `U` has a neighbourhood in `U`
on which it is [Fre17, Ch. I, 10.2]. -/
theorem hasLocalGeneratorsOn_of_forall_exists
    {M : ∀ y : X, y ∈ U → Submodule (𝒪.presheaf.stalk y) (Fin p → 𝒪.presheaf.stalk y)}
    (h : ∀ x ∈ U, ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      HasLocalGeneratorsOn 𝒪 V p fun y hy => M y (hVU hy)) :
    HasLocalGeneratorsOn 𝒪 U p M := by
  intro x hx
  obtain ⟨V, hVU, hxV, hV⟩ := h x hx
  obtain ⟨W, hWV, hxW, k, r, hr⟩ := hV x hxV
  exact ⟨W, hWV.trans hVU, hxW, k, r, hr⟩

/-- Local finite generation is invariant under a stalkwise equality of systems. -/
theorem HasLocalGeneratorsOn.congr
    {M N : ∀ y : X, y ∈ U → Submodule (𝒪.presheaf.stalk y) (Fin p → 𝒪.presheaf.stalk y)}
    (h : HasLocalGeneratorsOn 𝒪 U p M) (hMN : ∀ y hy, M y hy = N y hy) :
    HasLocalGeneratorsOn 𝒪 U p N := by
  intro x hx
  obtain ⟨V, hVU, hxV, k, r, hr⟩ := h x hx
  exact ⟨V, hVU, hxV, k, r, fun y hy => (hMN y (hVU hy)).symm.trans (hr y hy)⟩

end LocalGenerators

section Top

/-- `(⊤ : IdealSheaf 𝒪).IsCoherent ↔ ∀ J, J.IsCoherent`: every finite family of sections is a
family of sections of `⊤` ([BM97, (3.8)], "every ideal of finite type in `𝒪_X` is coherent"). -/
theorem IdealSheaf.isCoherent_top_iff :
    (⊤ : IdealSheaf 𝒪).IsCoherent ↔ ∀ J : IdealSheaf 𝒪, J.IsCoherent := by
  refine ⟨fun h J U p g _ => h U p g fun j => ?_, fun h => h ⊤⟩
  rw [IdealSheaf.carrier_top]
  exact Submodule.mem_top

/-- The `q = 1` slice of coherence of the sheaf of rings: `⊤` is a coherent ideal sheaf. -/
theorem IsCoherent.isCoherent_top (h : IsCoherent 𝒪) : (⊤ : IdealSheaf 𝒪).IsCoherent :=
  fun U p g _ => h U p 1 fun _ => g

end Top

section Algebra

variable {R : Type*} [CommRing R]

theorem relKer_of_isEmpty {p q : ℕ} [IsEmpty (Fin q)] (F : Fin q → Fin p → R) : relKer F = ⊤ := by
  ext a
  simp only [mem_relKer_iff, Submodule.mem_top, iff_true]
  exact fun i => isEmptyElim i

/-- The unit vectors span `Fin p → R`. -/
theorem span_range_single_one_eq_top (p : ℕ) :
    Submodule.span R (Set.range fun l : Fin p => (Pi.single l (1 : R) : Fin p → R)) = ⊤ := by
  have := (Pi.basisFun R (Fin p)).span_eq
  have hr : Set.range (Pi.basisFun R (Fin p)) =
      Set.range fun l : Fin p => (Pi.single l (1 : R) : Fin p → R) := by
    ext v; simp [Pi.basisFun_apply]
  rwa [hr] at this

/-- Swapping a double sum with the coefficients pulled through. -/
theorem sum_mul_sum_swap {p k : ℕ} (f : Fin p → R) (g : Fin k → Fin p → R) (c : Fin k → R) :
    ∑ j, f j * ∑ l, c l * g l j = ∑ l, (∑ j, f j * g l j) * c l := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

theorem sum_mul_sum_swap' {p k : ℕ} (f : Fin p → R) (g : Fin k → Fin p → R) (c : Fin k → R) :
    ∑ j, f j * ∑ l, c l * g l j = ∑ l, c l * ∑ j, f j * g l j := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

/-- The first step of Oka's theorem [Fre17, Ch. I, 10.3], the algebra at one ring: if the relations
of the last `q` rows of `F` are generated by `A`, and the relations of the row
`l ↦ Σ_j F 0 j · A l j` are generated by `B`, then the relations of `F` are generated by
`C i j = Σ_l B i l · A l j`. -/
theorem relKer_succ_eq_span {p q k m : ℕ} (F : Fin (q + 1) → Fin p → R) (A : Fin k → Fin p → R)
    (B : Fin m → Fin k → R)
    (hA : relKer (fun i => F i.succ) = Submodule.span R (Set.range A))
    (hB : relKer (fun _ : Fin 1 => fun l => ∑ j, F 0 j * A l j) = Submodule.span R (Set.range B)) :
    relKer F = Submodule.span R (Set.range fun i => fun j => ∑ l, B i l * A l j) := by
  have hArel : ∀ (l : Fin k) (i : Fin q), ∑ j, F i.succ j * A l j = 0 := by
    intro l i
    have : A l ∈ relKer (fun i => F i.succ) := by
      rw [hA]; exact Submodule.subset_span ⟨l, rfl⟩
    exact (mem_relKer_iff _ _).1 this i
  have hBrel : ∀ i, ∑ l, (∑ j, F 0 j * A l j) * B i l = 0 := by
    intro i
    have : B i ∈ relKer (fun _ : Fin 1 => fun l => ∑ j, F 0 j * A l j) := by
      rw [hB]; exact Submodule.subset_span ⟨i, rfl⟩
    exact (mem_relKer_iff _ _).1 this 0
  apply le_antisymm
  · intro a ha
    rw [mem_relKer_iff] at ha
    have ha' : a ∈ relKer (fun i => F i.succ) := by
      rw [mem_relKer_iff]; exact fun i => ha i.succ
    rw [hA, Submodule.mem_span_range_iff_exists_fun] at ha'
    obtain ⟨c, hc⟩ := ha'
    have hc0 : c ∈ relKer (fun _ : Fin 1 => fun l => ∑ j, F 0 j * A l j) := by
      rw [mem_relKer_iff]
      intro _
      have h0 := ha 0
      rw [← hc] at h0
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
      calc ∑ l, (∑ j, F 0 j * A l j) * c l = ∑ j, F 0 j * ∑ l, c l * A l j :=
            (sum_mul_sum_swap _ _ _).symm
        _ = 0 := h0
    rw [hB, Submodule.mem_span_range_iff_exists_fun] at hc0
    obtain ⟨d, hd⟩ := hc0
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨d, ?_⟩
    rw [← hc]
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have : ∀ l, c l = ∑ i, d i * B i l := by
      intro l
      have := congrFun hd l
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this.symm
    simp only [this, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun x _ => by ring
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_relKer_iff]
    intro r
    refine Fin.cases ?_ (fun r' => ?_) r
    · calc ∑ j, F 0 j * ∑ l, B i l * A l j = ∑ l, (∑ j, F 0 j * A l j) * B i l :=
            sum_mul_sum_swap _ _ _
        _ = 0 := hBrel i
    · calc ∑ j, F r'.succ j * ∑ l, B i l * A l j = ∑ l, B i l * ∑ j, F r'.succ j * A l j :=
            sum_mul_sum_swap' _ _ _
        _ = 0 := by simp only [hArel, mul_zero, Finset.sum_const_zero]

end Algebra

section Reduction

variable {U : Opens X} {p q : ℕ}

/-- The first step of Oka's theorem [Fre17, Ch. I, 10.3]: coherence of the sheaf of rings follows
from the case of one row (`(⊤ : IdealSheaf 𝒪).IsCoherent`), by induction on the number of rows. -/
theorem isCoherent_of_isCoherent_top (h : (⊤ : IdealSheaf 𝒪).IsCoherent) : IsCoherent 𝒪 := by
  intro U p q F
  induction q generalizing U p with
  | zero =>
    intro x hx
    refine ⟨U, le_rfl, hx, p, fun l j => if l = j then 1 else 0, fun y hy => ?_⟩
    dsimp only
    rw [relationSubmodule, relKer_of_isEmpty]
    have : (fun l => fun j => 𝒪.presheaf.germ U y hy
        (if l = j then (1 : 𝒪.presheaf.obj (op U)) else 0)) =
        fun l : Fin p => (Pi.single l (1 : 𝒪.presheaf.stalk y) : Fin p → 𝒪.presheaf.stalk y) := by
      funext l j
      by_cases hlj : l = j
      · subst hlj; simp
      · simp [hlj, Ne.symm hlj]
    rw [this, span_range_single_one_eq_top]
  | succ q ih =>
    intro x hx
    obtain ⟨V, hVU, hxV, k, A, hA⟩ := ih U p (fun i => F i.succ) x hx
    obtain ⟨W, hWV, hxW, m, B, hB⟩ :=
      h V k (fun l => ∑ j, 𝒪.presheaf.map (homOfLE hVU).op (F 0 j) * A l j)
        (fun _ => by rw [IdealSheaf.carrier_top]; exact Submodule.mem_top) x hxV
    refine ⟨W, hWV.trans hVU, hxW, m,
      fun i j => ∑ l, B i l * 𝒪.presheaf.map (homOfLE hWV).op (A l j), fun y hy => ?_⟩
    dsimp only
    rw [relationSubmodule]
    have hC : (fun i => fun j => 𝒪.presheaf.germ W y hy
        (∑ l, B i l * 𝒪.presheaf.map (homOfLE hWV).op (A l j))) =
        fun i => fun j => ∑ l,
          𝒪.presheaf.germ W y hy (B i l) * 𝒪.presheaf.germ V y (hWV hy) (A l j) := by
      funext i j
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, TopCat.Presheaf.germ_res_apply]
    rw [hC]
    apply relKer_succ_eq_span
    · have := hA y (hWV hy)
      dsimp only at this
      rw [relationSubmodule] at this
      exact this
    · have := hB y hy
      dsimp only at this
      rw [relationSubmodule] at this
      convert this using 3
      funext l
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, TopCat.Presheaf.germ_res_apply]

/-- A sheaf of rings `𝒪_X` is coherent iff every ideal of finite type in `𝒪_X` is coherent
([BM97, (3.8)], recalled there for the structure sheaf of a space), for any sheaf of commutative
rings on any space: `→` is the `q = 1` slice through `⊤`, `←` is Freitag's first step. -/
theorem isCoherent_iff_forall_isCoherent_idealSheaf :
    IsCoherent 𝒪 ↔ ∀ J : IdealSheaf 𝒪, J.IsCoherent :=
  ⟨fun h => IdealSheaf.isCoherent_top_iff.1 h.isCoherent_top,
    fun h => isCoherent_of_isCoherent_top (h ⊤)⟩

end Reduction

end Manifold
