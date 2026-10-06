/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Pieces
public import Hironaka.Resolution.Algebraic.Monomial.Restrict.Rename
public import Hironaka.Resolution.Algebraic.Monomial.Restrict
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Refinement of a piece family along an analytic map

To compare the monomial procedure run on a restricted or pulled-back triple with the run on the
original, the piece families of the two are related by a **refinement**: `Ψ` on `X` refines `Φ` on
`Y` along `ρ : X → Y` with parent map `p` on the pieces and label map `σ` when every piece of `Ψ`
lies in the preimage of its parent, the preimage of a parent is the union of its children, children
of one parent are disjoint, labels pass through the strictly monotone `σ`, and exponents through `p`
(`PieceFamily.RefinesAlong`). No order on the pieces is assumed; only the order of the labels is
preserved, which is all the lexicographic comparison of member tuples in [Kol07, 111, Step 3] uses.
The label map is an embedding rather than the identity because two open sets carry different sets of
labels.

The file proves the elementary consequences: the face through `x` maps bijectively onto the face
through `ρ x`, so the exponent sums agree (`total_faceAt`); faces map to faces and a face with a
point over `X` lifts; the preimage of the centre of a set of faces is the centre of the faces of `Ψ`
mapping into it (`preimage_centerOf`), empty when there are none. It also provides the **pull-back
family** `Φ.pullbackFamily ρ` (the same pieces, labels and exponents, the pieces replaced by their
whole preimages), which refines `Φ` with the identity maps and whose state is a sub-state of the
state of `Φ` in the sense of the combinatorial model (`Hironaka.Monomial.MonomialState.Sub`), and
the **relabelling** `Ψ.relabel σ L`, whose state is related to the state of `Ψ` by the renaming of
labels `Hironaka.Monomial.MonomialState.Rel` and refines the state of the pull-back family
(`Hironaka.Monomial.MonomialState.Refines`). These are the three relations through which the
combinatorial model compares the two runs (`BMO/Step3Monomial/RealizePullback.lean`).
-/

@[expose] public section

open Set Topology TopologicalSpace Hironaka.Monomial
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {X Y : AnalyticManifold.{u} 𝕜 E}

namespace PieceFamily

/-- `Ψ` on `X` **refines** `Φ` on `Y` along `ρ : X → Y`, with parent map `p` on pieces and label map
`σ`, strictly monotone on the labels in use: every piece of `Ψ` lies in the preimage of its parent,
the preimage of a parent is the union of its children, children of one parent are disjoint, labels
pass through `σ` and exponents through `p`. A parent may have no child (its preimage is then empty)
or several; a label of `Φ` off the range of `σ` has no child, so its members are empty over `X`. -/
structure RefinesAlong (Ψ : PieceFamily X) (ρ : AnalyticMap X Y) (p σ : ℕ → ℕ)
    (Φ : PieceFamily Y) : Prop where
  /-- Parents of live children are live. -/
  p_lt : ∀ c, c < Ψ.nextComp → p c < Φ.nextComp
  /-- The label map lands in `Φ`'s label range. -/
  σ_lt : ∀ ℓ, ℓ < Ψ.nextLabel → σ ℓ < Φ.nextLabel
  /-- The label map is an order embedding of the label range. -/
  σ_strictMonoOn : StrictMonoOn σ (Set.Iio Ψ.nextLabel)
  /-- Labels pass through `σ`. -/
  label_eq : ∀ c, c < Ψ.nextComp → Φ.label (p c) = σ (Ψ.label c)
  /-- Exponents pass through `p`. -/
  a_eq : ∀ c, c < Ψ.nextComp → Φ.a (p c) = Ψ.a c
  /-- A child lies in the preimage of its parent. -/
  piece_subset : ∀ c, c < Ψ.nextComp → Ψ.piece c ⊆ ⇑ρ ⁻¹' Φ.piece (p c)
  /-- The preimage of a parent is the union of its children. -/
  preimage_eq : ∀ c, c < Φ.nextComp → ⇑ρ ⁻¹' Φ.piece c =
    ⋃ c' ∈ (Finset.range Ψ.nextComp).filter (fun c' => p c' = c), Ψ.piece c'
  /-- Children of one parent are disjoint. -/
  disjoint : ∀ c c', c < Ψ.nextComp → c' < Ψ.nextComp → c ≠ c' → p c = p c' →
    Disjoint (Ψ.piece c) (Ψ.piece c')

variable {Ψ : PieceFamily X} {Φ : PieceFamily Y} {ρ : AnalyticMap X Y} {p σ : ℕ → ℕ}

namespace RefinesAlong

variable (h : Ψ.RefinesAlong ρ p σ Φ)
include h

/-- A point of `X` in the preimage of a parent lies in one of its children. -/
theorem exists_child {c : ℕ} (hc : c < Φ.nextComp) {x : X} (hx : ρ x ∈ Φ.piece c) :
    ∃ c', c' < Ψ.nextComp ∧ p c' = c ∧ x ∈ Ψ.piece c' := by
  have hx' : x ∈ ⋃ c' ∈ (Finset.range Ψ.nextComp).filter (fun c' => p c' = c), Ψ.piece c' := by
    rw [← h.preimage_eq c hc]; exact hx
  obtain ⟨c', hc', hxc'⟩ := Set.mem_iUnion₂.mp hx'
  obtain ⟨hlt, hpc⟩ := Finset.mem_filter.mp hc'
  exact ⟨c', Finset.mem_range.mp hlt, hpc, hxc'⟩

/-- The parent map sends the face through `x` onto the face through `ρ x`. -/
theorem image_faceAt (x : X) : (Ψ.faceAt x).image p = Φ.faceAt (ρ x) := by
  ext c
  constructor
  · intro hc
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hlt, hx⟩ := Ψ.mem_faceAt.mp hc'
    exact Φ.mem_faceAt.mpr ⟨h.p_lt c' hlt, h.piece_subset c' hlt hx⟩
  · intro hc
    obtain ⟨hlt, hx⟩ := Φ.mem_faceAt.mp hc
    obtain ⟨c', hlt', hpc, hxc'⟩ := h.exists_child hlt hx
    exact Finset.mem_image.mpr ⟨c', Ψ.mem_faceAt.mpr ⟨hlt', hxc'⟩, hpc⟩

/-- The parent map is injective on the face through `x`, children of one parent being disjoint. -/
theorem injOn_faceAt (x : X) : Set.InjOn p ↑(Ψ.faceAt x) := by
  intro c hc c' hc' hpc
  by_contra hne
  obtain ⟨hlt, hx⟩ := Ψ.mem_faceAt.mp (Finset.mem_coe.mp hc)
  obtain ⟨hlt', hx'⟩ := Ψ.mem_faceAt.mp (Finset.mem_coe.mp hc')
  exact Set.disjoint_left.mp (h.disjoint c c' hlt hlt' hne hpc) hx hx'

/-- The exponent sums of the faces through `x` and through `ρ x` agree. -/
theorem total_faceAt (x : X) : Ψ.total (Ψ.faceAt x) = Φ.total (Φ.faceAt (ρ x)) := by
  unfold PieceFamily.total
  rw [← h.image_faceAt x, Finset.sum_image (h.injOn_faceAt x)]
  refine Finset.sum_congr rfl fun c hc => ?_
  exact (h.a_eq c (Ψ.mem_faceAt.mp hc).1).symm

/-- A face of `Ψ` maps to a face of `Φ`, and the parent map is injective on it. -/
theorem image_mem_nerve {T : Finset ℕ} (hT : T ∈ Ψ.nerve) :
    T.image p ∈ Φ.nerve ∧ Set.InjOn p ↑T := by
  obtain ⟨hsub, hne, x, hx⟩ := Ψ.mem_nerve_iff T |>.mp hT
  have hlt : ∀ c ∈ T, c < Ψ.nextComp := fun c hc => Finset.mem_range.mp (hsub hc)
  refine ⟨(Φ.mem_nerve_iff _).mpr ⟨?_, hne.image p, ρ x, ?_⟩, ?_⟩
  · intro c' hc'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    exact Finset.mem_range.mpr (h.p_lt c (hlt c hc))
  · intro c' hc'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    exact h.piece_subset c (hlt c hc) (hx c hc)
  · intro c hc c' hc' hpc
    by_contra hne'
    exact Set.disjoint_left.mp
      (h.disjoint c c' (hlt c (Finset.mem_coe.mp hc)) (hlt c' (Finset.mem_coe.mp hc')) hne' hpc)
      (hx c (Finset.mem_coe.mp hc)) (hx c' (Finset.mem_coe.mp hc'))

/-- A face of `Φ` with a point over `X` lifts to a face of `Ψ` through that point. -/
theorem exists_lift {T' : Finset ℕ} (hT' : T' ∈ Φ.nerve) {x : X} (hx : ρ x ∈ Φ.faceSet T') :
    ∃ T ∈ Ψ.nerve, T.image p = T' ∧ x ∈ Ψ.faceSet T := by
  classical
  obtain ⟨hsub', hne', -⟩ := (Φ.mem_nerve_iff T').mp hT'
  have hxT' : ∀ c' ∈ T', ρ x ∈ Φ.piece c' := Φ.mem_faceSet.mp hx
  refine ⟨(Ψ.faceAt x).filter fun c => p c ∈ T', ?_, ?_, ?_⟩
  · refine (Ψ.mem_nerve_iff _).mpr ⟨fun c hc => Ψ.faceAt_subset_range x (Finset.mem_filter.mp hc).1,
      ?_, x, fun c hc => (Ψ.mem_faceAt.mp (Finset.mem_filter.mp hc).1).2⟩
    obtain ⟨c', hc'⟩ := hne'
    obtain ⟨c, hlt, hpc, hxc⟩ :=
      h.exists_child (Finset.mem_range.mp (hsub' hc')) (hxT' c' hc')
    exact ⟨c, Finset.mem_filter.mpr ⟨Ψ.mem_faceAt.mpr ⟨hlt, hxc⟩, hpc ▸ hc'⟩⟩
  · ext c'
    constructor
    · intro hc'
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
      exact (Finset.mem_filter.mp hc).2
    · intro hc'
      obtain ⟨c, hlt, hpc, hxc⟩ :=
        h.exists_child (Finset.mem_range.mp (hsub' hc')) (hxT' c' hc')
      exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨Ψ.mem_faceAt.mpr ⟨hlt, hxc⟩, hpc ▸ hc'⟩,
        hpc⟩
  · exact Ψ.mem_faceSet.mpr fun c hc => (Ψ.mem_faceAt.mp (Finset.mem_filter.mp hc).1).2

/-- The preimage of the centre of a set `S` of faces of `Φ` is the centre of the faces of `Ψ`
mapping into `S`. -/
theorem preimage_centerOf (S : Finset (Finset ℕ)) (hS : ∀ P ∈ S, P ∈ Φ.nerve) :
    ⇑ρ ⁻¹' Φ.centerOf S = Ψ.centerOf (Ψ.nerve.filter fun Q => Q.image p ∈ S) := by
  classical
  ext x
  rw [Set.mem_preimage, Φ.mem_centerOf, Ψ.mem_centerOf]
  constructor
  · rintro ⟨P, hP, hx⟩
    obtain ⟨Q, hQ, hQP, hxQ⟩ := h.exists_lift (hS P hP) hx
    exact ⟨Q, Finset.mem_filter.mpr ⟨hQ, hQP ▸ hP⟩, hxQ⟩
  · rintro ⟨Q, hQ, hx⟩
    obtain ⟨hQn, hQS⟩ := Finset.mem_filter.mp hQ
    refine ⟨Q.image p, hQS, Φ.mem_faceSet.mpr fun c' hc' => ?_⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    exact h.piece_subset c (Ψ.lt_nextComp_of_mem_nerve hQn hc) (Ψ.mem_faceSet.mp hx c hc)

/-- A centre none of whose faces is the image of a face of `Ψ` has empty preimage; the corresponding
blow-up is then deleted from the run over `X` ([Kol07, 32]). -/
theorem preimage_centerOf_eq_empty (S : Finset (Finset ℕ)) (hS : ∀ P ∈ S, P ∈ Φ.nerve)
    (hno : ∀ Q ∈ Ψ.nerve, Q.image p ∉ S) : ⇑ρ ⁻¹' Φ.centerOf S = ∅ := by
  classical
  rw [h.preimage_centerOf S hS]
  have hfilter : (Ψ.nerve.filter fun Q => Q.image p ∈ S) = ∅ :=
    Finset.filter_eq_empty_iff.mpr hno
  rw [hfilter]
  simp [PieceFamily.centerOf]

end RefinesAlong

/-! ### The pull-back family -/

/-- The **pull-back of `Φ` along `ρ`**: the same pieces, labels and exponents, the pieces replaced
by their whole preimages (possibly empty, possibly disconnected). -/
def pullbackFamily (Φ : PieceFamily Y) (ρ : AnalyticMap X Y) : PieceFamily X where
  nextComp := Φ.nextComp
  nextLabel := Φ.nextLabel
  piece c := ⇑ρ ⁻¹' Φ.piece c
  label := Φ.label
  a := Φ.a
  label_lt := Φ.label_lt
  isClosed_piece c := (Φ.isClosed_piece c).preimage ρ.contMDiff.continuous

variable (Φ ρ) in
/-- The pull-back family refines `Φ` along `ρ` with the identity maps: one child per parent. -/
theorem pullbackFamily_refinesAlong : (Φ.pullbackFamily ρ).RefinesAlong ρ id id Φ where
  p_lt _ hc := hc
  σ_lt _ hℓ := hℓ
  σ_strictMonoOn := strictMono_id.strictMonoOn _
  label_eq _ _ := rfl
  a_eq _ _ := rfl
  piece_subset _ _ := Set.Subset.rfl
  preimage_eq c hc := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion₂.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, rfl⟩, hx⟩
    · intro hx
      obtain ⟨c', hc', hx'⟩ := Set.mem_iUnion₂.mp hx
      have hcc : c' = c := (Finset.mem_filter.mp hc').2
      exact hcc ▸ hx'
  disjoint _ _ _ _ hne heq := absurd heq hne

variable (Φ ρ) in
/-- The nerve of the pull-back family is the set of faces of `Φ` with a point over `X`. -/
theorem mem_nerve_pullbackFamily (T : Finset ℕ) :
    T ∈ (Φ.pullbackFamily ρ).nerve ↔ T ∈ Φ.nerve ∧ (Φ.faceSet T ∩ Set.range ρ).Nonempty := by
  rw [(Φ.pullbackFamily ρ).mem_nerve_iff, Φ.mem_nerve_iff]
  constructor
  · rintro ⟨hsub, hne, x, hx⟩
    exact ⟨⟨hsub, hne, ρ x, fun c hc => hx c hc⟩, ρ x, Φ.mem_faceSet.mpr fun c hc => hx c hc,
      Set.mem_range_self x⟩
  · rintro ⟨⟨hsub, hne, -⟩, y, hy, x, rfl⟩
    exact ⟨hsub, hne, x, fun c hc => Φ.mem_faceSet.mp hy c hc⟩

variable (Φ ρ) in
/-- The invariants of the state pass to the pull-back family: a sub-nerve closed under nonempty
subsets. -/
theorem isValid_pullbackFamily {n m : ℕ} (hV : Φ.IsValid n m) :
    (Φ.pullbackFamily ρ).IsValid n m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hV
  have hmem : ∀ T ∈ (Φ.pullbackFamily ρ).nerve, T ∈ Φ.nerve := fun T hT =>
    ((Φ.mem_nerve_pullbackFamily ρ T).mp hT).1
  refine ⟨h1, fun T hT => h2 T (hmem T hT), fun T hT => h3 T (hmem T hT), h4, ?_,
    fun T hT => h6 T (hmem T hT), fun T hT => h7 T (hmem T hT)⟩
  intro T hT T' hT' hne
  obtain ⟨hTn, y, hy, hyr⟩ := (Φ.mem_nerve_pullbackFamily ρ T).mp hT
  refine (Φ.mem_nerve_pullbackFamily ρ T').mpr ⟨h5 T hTn T' hT' hne, y, ?_, hyr⟩
  exact Φ.faceSet_anti (Finset.mem_powerset.mp hT') hy

variable (Φ ρ) in
/-- The state of the pull-back family is a sub-state of the state of `Φ`: the same data and a
sub-nerve (`Hironaka.Monomial.MonomialState.Sub`). -/
theorem sub_toState_pullbackFamily {n m : ℕ} (hV : Φ.IsValid n m) :
    MonomialState.Sub ((Φ.pullbackFamily ρ).toState n m (Φ.isValid_pullbackFamily ρ hV))
      (Φ.toState n m hV) where
  n_eq := rfl
  m_eq := rfl
  nextComp_eq := rfl
  nextLabel_eq := rfl
  label_eq := rfl
  a_eq := rfl
  nerve_sub T hT := ((Φ.mem_nerve_pullbackFamily ρ T).mp hT).1

/-! ### The relabelling and the chain of states -/

/-- The relabelling of a piece family along a label map into a larger label range; the pieces are
unchanged. -/
def relabel (Ψ : PieceFamily X) (σ : ℕ → ℕ) (L : ℕ) (hσ : ∀ ℓ, ℓ < Ψ.nextLabel → σ ℓ < L) :
    PieceFamily X where
  nextComp := Ψ.nextComp
  nextLabel := L
  piece := Ψ.piece
  label c := σ (Ψ.label c)
  a := Ψ.a
  label_lt c hc := hσ _ (Ψ.label_lt c hc)
  isClosed_piece := Ψ.isClosed_piece

/-- The relabelled family has the nerve of `Ψ`, its pieces being unchanged. -/
theorem nerve_relabel (Ψ : PieceFamily X) (σ : ℕ → ℕ) (L : ℕ)
    (hσ : ∀ ℓ, ℓ < Ψ.nextLabel → σ ℓ < L) : (Ψ.relabel σ L hσ).nerve = Ψ.nerve := by
  ext T
  rw [(Ψ.relabel σ L hσ).mem_nerve_iff, Ψ.mem_nerve_iff]
  exact Iff.rfl

/-- The nerve of the state of the relabelled family is the nerve of `Ψ`. -/
theorem mem_nerve_toState_relabel (Ψ : PieceFamily X) (σ : ℕ → ℕ) (L : ℕ)
    (hσ : ∀ ℓ, ℓ < Ψ.nextLabel → σ ℓ < L) {n m : ℕ} (hV' : (Ψ.relabel σ L hσ).IsValid n m)
    (T : Finset ℕ) : T ∈ ((Ψ.relabel σ L hσ).toState n m hV').nerve ↔ T ∈ Ψ.nerve := by
  change T ∈ (Ψ.relabel σ L hσ).nerve ↔ T ∈ Ψ.nerve
  rw [Ψ.nerve_relabel]

/-- The state of the relabelled family is the state of `Ψ` with the labels renamed by the order
embedding `σ`, the pieces untouched (`Hironaka.Monomial.MonomialState.Rel`). -/
theorem rel_toState_relabel (h : Ψ.RefinesAlong ρ p σ Φ) {n m : ℕ} (hV : Ψ.IsValid n m)
    (hV' : (Ψ.relabel σ Φ.nextLabel h.σ_lt).IsValid n m) :
    MonomialState.Rel id σ (Ψ.toState n m hV)
      ((Ψ.relabel σ Φ.nextLabel h.σ_lt).toState n m hV') where
  n_eq := rfl
  m_eq := rfl
  mono := strictMono_id.strictMonoOn _
  lt _ hc := hc
  a_eq _ _ := rfl
  label_eq _ _ := rfl
  σmono := h.σ_strictMonoOn
  σlt := h.σ_lt
  nerve_eq := by
    change (Ψ.relabel σ Φ.nextLabel h.σ_lt).nerve = Ψ.nerve.image (Finset.image id)
    rw [Ψ.nerve_relabel]
    ext T
    constructor
    · intro hT
      exact Finset.mem_image.mpr ⟨T, hT, Finset.image_id⟩
    · intro hT
      obtain ⟨T', hT', hTT⟩ := Finset.mem_image.mp hT
      rw [Finset.image_id] at hTT
      exact hTT ▸ hT'

/-- The relabelled state refines the state of the pull-back family along the parent map
(`Hironaka.Monomial.MonomialState.Refines`): faces map injectively to faces, and every face with a
point over `X` lifts. -/
theorem refines_toState_relabel (h : Ψ.RefinesAlong ρ p σ Φ) {n m : ℕ}
    (hV' : (Ψ.relabel σ Φ.nextLabel h.σ_lt).IsValid n m) (hVΦ : Φ.IsValid n m) :
    MonomialState.Refines p ((Ψ.relabel σ Φ.nextLabel h.σ_lt).toState n m hV')
      ((Φ.pullbackFamily ρ).toState n m (Φ.isValid_pullbackFamily ρ hVΦ)) where
  n_eq := rfl
  m_eq := rfl
  nextLabel_eq := rfl
  lt := h.p_lt
  label_eq := h.label_eq
  a_eq := h.a_eq
  injOn T hT :=
    (h.image_mem_nerve ((Ψ.mem_nerve_toState_relabel σ Φ.nextLabel h.σ_lt hV' T).mp hT)).2
  image_mem T hT := by
    have hT' : T ∈ Ψ.nerve := (Ψ.mem_nerve_toState_relabel σ Φ.nextLabel h.σ_lt hV' T).mp hT
    obtain ⟨-, -, x, hx⟩ := (Ψ.mem_nerve_iff T).mp hT'
    have hlt : ∀ c ∈ T, c < Ψ.nextComp := fun c hc => Ψ.lt_nextComp_of_mem_nerve hT' hc
    refine (Φ.mem_nerve_pullbackFamily ρ _).mpr ⟨(h.image_mem_nerve hT').1, ρ x, ?_,
      Set.mem_range_self x⟩
    refine Φ.mem_faceSet.mpr fun c' hc' => ?_
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    exact h.piece_subset c (hlt c hc) (hx c hc)
  exists_lift T' hT' := by
    obtain ⟨hT'n, y, hy, x, rfl⟩ := (Φ.mem_nerve_pullbackFamily ρ T').mp hT'
    obtain ⟨T, hT, hTT', -⟩ := h.exists_lift hT'n hy
    exact ⟨T, (Ψ.mem_nerve_toState_relabel σ Φ.nextLabel h.σ_lt hV' T).mpr hT, hTT'⟩

end PieceFamily

end Hironaka.Manifold.BMO
