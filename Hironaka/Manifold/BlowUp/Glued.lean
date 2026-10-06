/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Glue
public import Mathlib.Topology.Gluing
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The gluing of the blowing-up: the glued space

The pieces and transition data of `Hironaka.Manifold.BlowUp.Glue` are fed to Mathlib's
`TopCat.GlueData.mk'` (gluing data given by elements and intersections): the pieces, lifted to
the universe of `M`, are the objects, the transition domains the open subsets, the transition
maps the transition homeomorphisms; the identity, inverse and cocycle laws are those proved
there. The glued space `Glued ψ Y c` carries the inclusions `toGlued j` of the pieces, open
embeddings that are jointly surjective, and two points of pieces are identified exactly when the
transition map carries one to the other (`toGlued_eq_iff`). The blow-down
`gluedProj : Glued ψ Y c → M` is defined piecewise and is continuous.

This is the topological space underlying the blowing-up of `M` with centre `Y`
[BM88, Definition 4.1]; its structure of analytic manifold is the subject of
`Hironaka.Manifold.BlowUp.GluedCharts`.
-/

@[expose] public section

open TopologicalSpace CategoryTheory
open scoped Manifold ContDiff Topology

universe u

namespace Manifold

namespace BlowUpGlue

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M] (Y : Set M)
  (c : ℕ)

/-! ### The gluing data -/

variable {ψ Y c}

/-- A piece as a topological space in the universe of `M`. -/
abbrev pieceSpace (j : PieceIdx ψ Y c) : TopCat.{u} := TopCat.of (ULift.{u} (pieceSet j))

/-- The transition domain as an open subset of the piece. -/
def transOpens (j j' : PieceIdx ψ Y c) : Opens (pieceSpace j) :=
  ⟨{x | x.down.1 ∈ transDom j j'},
    (isOpen_transDom j j').preimage (continuous_subtype_val.comp continuous_uliftDown)⟩

/-- Membership in the transition open of a piece space, unfolded. -/
theorem mem_transOpens_iff {j j' : PieceIdx ψ Y c} {x : pieceSpace j} :
    x ∈ transOpens j j' ↔ x.down.1 ∈ transDom j j' := Iff.rfl

/-- The transition homeomorphism between the transition domains. -/
def transHom (j j' : PieceIdx ψ Y c) :
    (Opens.toTopCat _).obj (transOpens j j') ⟶ (Opens.toTopCat _).obj (transOpens j' j) :=
  TopCat.ofHom
    ⟨fun x => ⟨⟨⟨transMap j j' x.1.down.1, transMap_mem_pieceSet x.2⟩⟩, transMap_mem x.2⟩, by
      refine Continuous.subtype_mk (continuous_uliftUp.comp (Continuous.subtype_mk ?_ _)) _
      exact (analyticOnNhd_transMap j j').continuousOn.comp_continuous
        (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_subtype_val))
        fun x => x.2⟩

/-- The transition homeomorphism of the gluing data acts by the transition map. -/
theorem transHom_apply_coe (j j' : PieceIdx ψ Y c)
    (x : (Opens.toTopCat _).obj (transOpens j j')) :
    (transHom j j' x).1.down.1 = transMap j j' x.1.down.1 := rfl

variable (ψ Y c)

/-- The gluing data of the blowing-up, in the element-wise form `TopCat.GlueData.MkCore`. -/
def glueCore : TopCat.GlueData.MkCore.{u} where
  J := PieceIdx ψ Y c
  U := pieceSpace
  V := transOpens
  t := transHom
  V_id j := by
    apply Opens.ext
    apply Set.eq_univ_of_forall
    intro x
    rw [SetLike.mem_coe, mem_transOpens_iff, transDom_self]
    exact x.down.2
  t_id j := by
    funext x
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    exact transMap_self x.1.down.2
  t_inter := fun _ _ _ x hx => transMap_mem_of_mem x.2 hx
  cocycle _ _ _ x hx := by
    apply ULift.ext
    apply Subtype.ext
    exact transMap_transMap x.2 hx

/-- The glue data of the blowing-up. -/
def glueData : TopCat.GlueData.{u} := TopCat.GlueData.mk' (glueCore ψ Y c)

/-- The glued space: the blowing-up of `M` with centre `Y` as a topological space. -/
abbrev Glued : Type u := (glueData ψ Y c).toGlueData.glued

variable {ψ Y c}

/-- The inclusion of a piece into the glued space. -/
def toGlued (j : PieceIdx ψ Y c) (u : pieceSet j) : Glued ψ Y c :=
  (glueData ψ Y c).toGlueData.ι j (ULift.up u)

/-- The inclusion of a piece into the glued space is continuous. -/
theorem continuous_toGlued (j : PieceIdx ψ Y c) : Continuous (toGlued j) :=
  (TopCat.Hom.hom ((glueData ψ Y c).toGlueData.ι j)).continuous.comp continuous_uliftUp

/-- The inclusion of a piece into the glued space is an open embedding. -/
theorem isOpenEmbedding_toGlued (j : PieceIdx ψ Y c) : Topology.IsOpenEmbedding (toGlued j) :=
  ((glueData ψ Y c).ι_isOpenEmbedding j).comp Homeomorph.ulift.symm.isOpenEmbedding

/-- The pieces cover the glued space. -/
theorem toGlued_jointly_surjective (p : Glued ψ Y c) :
    ∃ (j : PieceIdx ψ Y c) (u : pieceSet j), toGlued j u = p := by
  obtain ⟨j, y, hy⟩ := (glueData ψ Y c).ι_jointly_surjective p
  exact ⟨j, y.down, hy⟩

/-- A set in the glued space is open iff its preimage in every piece is open. -/
theorem isOpen_glued_iff (s : Set (Glued ψ Y c)) :
    IsOpen s ↔ ∀ j : PieceIdx ψ Y c, IsOpen (toGlued j ⁻¹' s) := by
  rw [(glueData ψ Y c).isOpen_iff]
  refine forall_congr' fun j => ?_
  constructor
  · intro h
    exact h.preimage continuous_uliftUp
  · intro h
    have h2 : (⇑((glueData ψ Y c).toGlueData.ι j)) ⁻¹' s = ULift.down ⁻¹' (toGlued j ⁻¹' s) :=
      Set.ext fun _ => Iff.rfl
    rw [h2]
    exact h.preimage continuous_uliftDown

/-- Two points of two pieces are identified in the glued space iff they are related by the gluing
relation (Mathlib's `ι_eq_iff_rel` with the piece indices made explicit). -/
theorem ι_eq_iff_rel' (j j' : PieceIdx ψ Y c) (x : pieceSpace j) (y : pieceSpace j') :
    (glueData ψ Y c).toGlueData.ι j x = (glueData ψ Y c).toGlueData.ι j' y ↔
      (glueData ψ Y c).Rel ⟨j, x⟩ ⟨j', y⟩ :=
  (glueData ψ Y c).ι_eq_iff_rel j j' x y

/-- Two points of pieces are identified in the glued space exactly when the transition map
carries one to the other. -/
theorem toGlued_eq_iff {j j' : PieceIdx ψ Y c} {u : pieceSet j} {u' : pieceSet j'} :
    toGlued j u = toGlued j' u' ↔
      ∃ _ : (u : Fin n → 𝕜) ∈ transDom j j', transMap j j' u = u' := by
  refine (ι_eq_iff_rel' j j' (ULift.up u) (ULift.up u')).trans ⟨?_, ?_⟩
  · rintro ⟨x, hx1, hx2⟩
    have h1 : x.1.down.1 = u := congrArg (fun y : ULift (pieceSet j) => (y.down : Fin n → 𝕜)) hx1
    have h2 : transMap j j' x.1.down.1 = u' :=
      congrArg (fun y : ULift (pieceSet j') => (y.down : Fin n → 𝕜)) hx2
    rw [h1] at h2
    have hx : x.1.down.1 ∈ transDom j j' := x.2
    rw [h1] at hx
    exact ⟨hx, h2⟩
  · rintro ⟨h, hu'⟩
    refine ⟨⟨ULift.up u, h⟩, rfl, ?_⟩
    apply ULift.ext
    apply Subtype.ext
    exact hu'

/-- The inclusion of a piece into the glued space is injective. -/
theorem toGlued_injective (j : PieceIdx ψ Y c) : Function.Injective (toGlued j) :=
  (isOpenEmbedding_toGlued j).injective

/-- The transition map is compatible with the inclusions: a point and its transition are identified
in the glued space. -/
theorem toGlued_transMap {j j' : PieceIdx ψ Y c} {u : pieceSet j}
    (hu : (u : Fin n → 𝕜) ∈ transDom j j') :
    toGlued j' ⟨transMap j j' u, transMap_mem_pieceSet hu⟩ = toGlued j u :=
  (toGlued_eq_iff.mpr ⟨hu, rfl⟩).symm

/-- A point of a piece lies in the image of another piece exactly when it lies in the transition
domain. -/
theorem toGlued_mem_range_iff {j j' : PieceIdx ψ Y c} {u : pieceSet j} :
    toGlued j u ∈ Set.range (toGlued j') ↔ (u : Fin n → 𝕜) ∈ transDom j j' := by
  constructor
  · rintro ⟨u', hu'⟩
    obtain ⟨h, -⟩ := toGlued_eq_iff.mp hu'.symm
    exact h
  · intro h
    exact ⟨_, toGlued_transMap h⟩

/-! ### The blow-down of the glued space -/

/-- A piece containing the point `p`. -/
def pieceOf (p : Glued ψ Y c) : PieceIdx ψ Y c := (toGlued_jointly_surjective p).choose

/-- The coordinates of `p` in the piece `pieceOf p`. -/
def pieceElt (p : Glued ψ Y c) : pieceSet (pieceOf p) :=
  (toGlued_jointly_surjective p).choose_spec.choose

/-- Every point of the glued space is the inclusion of its chosen piece element. -/
theorem toGlued_pieceElt (p : Glued ψ Y c) : toGlued (pieceOf p) (pieceElt p) = p :=
  (toGlued_jointly_surjective p).choose_spec.choose_spec

/-- The blow-down `π : M' → M` of the glued space, defined piecewise. -/
def gluedProj (p : Glued ψ Y c) : M := blowDown (pieceOf p) (pieceElt p)

/-- The blow-down of the glued space restricts to the blow-down of each piece. -/
theorem gluedProj_toGlued (j : PieceIdx ψ Y c) (u : pieceSet j) :
    gluedProj (toGlued j u) = blowDown j u := by
  have h := toGlued_pieceElt (toGlued j u)
  obtain ⟨hmem, htrans⟩ := toGlued_eq_iff.mp h
  rw [gluedProj, ← blowDown_transMap hmem, htrans]

/-- The blow-down of the glued space is continuous. -/
theorem continuous_gluedProj : Continuous (gluedProj : Glued ψ Y c → M) := by
  rw [continuous_def]
  intro O hO
  rw [isOpen_glued_iff]
  intro j
  have : toGlued j ⁻¹' (gluedProj ⁻¹' O) = (fun u : pieceSet j => blowDown j u) ⁻¹' O := by
    ext u
    simp only [Set.mem_preimage, gluedProj_toGlued]
  rw [this]
  exact hO.preimage ((continuousOn_blowDown j).comp_continuous continuous_subtype_val fun u => u.2)

/-- The blow-down of a point of piece `j` lies in the source of the piece's chart. -/
theorem gluedProj_mem_source (j : PieceIdx ψ Y c) (u : pieceSet j) :
    gluedProj (toGlued j u) ∈ (pieceChart j).source := by
  rw [gluedProj_toGlued]
  exact blowDown_mem_source u.2

end

end BlowUpGlue

end Manifold
