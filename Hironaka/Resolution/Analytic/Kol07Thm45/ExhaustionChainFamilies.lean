/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.Resolution
public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductGluedFamily
public import Hironaka.Resolution.Analytic.Kol07Thm45.Glue.OverFamilyChain
public import Hironaka.Resolution.Analytic.Kol07Thm45.Glue.OverRigidity
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductGluedFamilyCompat
import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductLevelPair
import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductPadIdentityPiece
import Hironaka.Resolution.Analytic.Kol07Thm45.PadReadingOpens
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionOnMembers
import Hironaka.Resolution.Analytic.Kol07Thm45.RigidOverLocalResolution
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The chain families of an exhaustion

Kollár's globalisation glues the resolutions of the members of a cover along their overlaps
[Kol07, Proposition 37, proof], and the exceptional divisor of the result has simple normal
crossings with support `Π⁻¹(X.singularLocus)` [Kol07, Theorem 45(3)]; Włodarczyk glues over an
exhaustion by relatively compact opens [Wlo09, §4.3]. Here the resolutions `Ũ_n → U_n` of the
members of an exhaustion are glued along their overlaps (`ExhaustionGluing`, `Resolution.lean`), and
the exceptional families of the levels glue with them when their members are matched level to level
by a LABEL — the stage of the common blow-up sequence each member is the exceptional divisor of.
`Hironaka/Resolution/Analytic/Kol07Thm45/Glue/OverFamilyChain.lean` does the gluing from four inputs
per level: a simple normal crossings family `H n` on `Ũ_n`, label maps `e n` on the members with
non-empty trace on the overlap with the next level, the adjacent identity `hpair` and the covering
`hsurj`. This module supplies them (`BEDanFamStar.exists_chainFamilies`).

Per level, `exists_gluedMembers_resolutionOn_compat` (`ResolutionOnMembers.lean`) gives `H n` —
the glued family of the level's coproduct traces on `resolutionOn`, with its three clauses and the
PIECE-TRACE clause named here `PieceTraceCompat`: over every base open inside a piece's domain the
members are the piece traces, along every isomorphism over `X`. Its hypothesis is the labelled
compatibility of the level's coproduct traces, `labelledCompat_pieceTrace`
(`CoproductGluedFamilyCompat.lean`).

Per adjacent pair, the two levels are compared through the DOUBLED datum: the levels' data padded
to a common dimension and summed (`sumPadData`), whose single run carries a common label set into
which both levels' label sets embed (`exists_orderEmbedding_comap_sumInl/InrResIn_sigmaMembers`,
`CoproductSumData.lean`) — read at the levels' reading opens through the padded reading opens
(`padReadingOpens`, `PadReadingOpens.lean`) and the padding identity
(`exists_padIdentity_of_padPreimageOpens_eq` on `padIdentityOn`). Extending each level's members by
the unit ideal along its label map (`Function.extend`), the local pair identity
`exists_isoOver_resolutionOn_pair_of_forall_label` (`CoproductLevelPair.lean`) gives, at every
point of the overlap, an isomorphism over `X` of the parts of the two glued resolutions carrying
the extended members label by label; the pointwise criterion for one pair of subspaces
(`compatClosedSubspaces_pair_of_forall_exists_isoOver_two`) with the rigidity
`rigidOver_resolutionOnToSpace` turns it into the adjacent identity for every common label
(`exists_pairLabels`). The `bed`-free bookkeeping `exists_chainLabelMaps_of_extend` then reads off
the label maps: a member with non-empty trace has a partner at the other level, since the
extension by `⊤` would otherwise pull the unit ideal back to its trace (`cosupport_top`; the
transition, an isomorphism, reflects the unit ideal: `comap_ne_top_of_isIso`).

* `GlueOver.compatClosedSubspaces_pair_of_forall_exists_isoOver_two` — the pointwise criterion for
  one pair;
* `GlueOver.exists_chainLabelMaps_of_extend` — the label maps from common label sets;
* `LocalEmbeddingData.PieceTraceCompat` — the piece-trace clause, named;
* `BEDanFamStar.exists_pairLabels` — the common label set of two adjacent levels;
* `BEDanFamStar.exists_chainFamilies_of_compat`, `BEDanFamStar.exists_chainFamilies` — the chain
  families. Used by `ResolutionSncGlobal.lean`.

Not in the sources beyond the statements cited; bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set AnalyticSpace
open KLocallyRingedSpace Hironaka.Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

namespace GlueOver

variable {K : Type} [RCLike K]

section Pairwise

variable {X : AnalyticSpace.{u} K} {ι : Type u} [Countable ι]
    {R : ι → AnalyticSpace.{u} K}
  {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace} {dom : ι → Opens X}
  (G : GlueOver X R π dom)

omit [Countable ι] in
/-- **The pointwise criterion for ONE pair of closed subspaces** `Zi`, `Zj` of two distinct pieces
((37.2) in [Kol07, Proposition 37, proof]) — the family form
`compatClosedSubspaces_pair_of_forall_exists_isoOver` at the family that is `Zi` at `i`, `Zj` at
`j` and the unit ideal elsewhere (`Function.update` twice on the constant `⊤`). -/
theorem compatClosedSubspaces_pair_of_forall_exists_isoOver_two (i j : ι) (hij : i ≠ j)
    (Zi : ClosedSubspace (R i)) (Zj : ClosedSubspace (R j))
    (h : ∀ y : R i, y ∈ glueOpens X R π dom i j →
      ∃ (P : Opens X) (_ : P ≤ dom i ⊓ dom j), KLocallyRingedSpace.Hom.toFun
          (π i) y ∈ P ∧ RigidOver (π i) P ∧
        ∃ θ : (R i).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ P) ⟶
          (R j).toKLocallyRingedSpace.restrictOpen
            (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π j), Hom.continuous_toFun (π j)⟩ P),
          IsIso θ ∧
          ofRestrict (R i).toKLocallyRingedSpace _ ≫ π i =
            (θ ≫ ofRestrict (R j).toKLocallyRingedSpace _) ≫ π j ∧
          QuotientSpace.comap (θ ≫ ofRestrict (R j).toKLocallyRingedSpace _).1 Zj =
            QuotientSpace.comap (ofRestrict (R i).toKLocallyRingedSpace _).1 Zi) :
    QuotientSpace.comap (G.t i j).1 (restrictGlue π dom j i Zj) = restrictGlue π dom i j Zi := by
  classical
  obtain ⟨C, hC⟩ : ∃ C : ∀ k, ClosedSubspace (R k),
      C = Function.update (Function.update (fun k => (⊤ : ClosedSubspace (R k))) i Zi) j Zj :=
    ⟨_, rfl⟩
  have hCj : C j = Zj := by rw [hC, Function.update_self]
  have hCi : C i = Zi := by rw [hC, Function.update_of_ne hij, Function.update_self]
  have key := G.compatClosedSubspaces_pair_of_forall_exists_isoOver C i j fun y hy => by
    obtain ⟨P, hP, hyP, hrig, θ, hθ, hover, hZ⟩ := h y hy
    exact ⟨P, hP, hyP, hrig, θ, hθ, hover, by rw [hCj, hCi]; exact hZ⟩
  rw [hCj, hCi] at key
  exact key

end Pairwise

section Chain

variable {X : AnalyticSpace.{u} K} {R : ULift.{u} ℕ → AnalyticSpace.{u} K}
  {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace} {dom : ULift.{u} ℕ → Opens X}
  (G : GlueOver X R π dom) {Λ : ℕ → Type u}

/-- **The label maps from common label sets of the adjacent pairs** ([Kol07, Proposition 37,
proof]) — injections `l₁ n : Λ n → Λ' n`, `l₂ n : Λ (n+1) → Λ' n` into a common label set with the
adjacent
identity `hpr` on the members EXTENDED BY `⊤` (`Function.extend`) give the label maps `e n` on the
members with non-empty trace, the labelled identity `hpair` and the covering `hsurj`. A member `σ`
of level `n` with non-empty trace has a partner `τ` with `l₂ τ = l₁ σ` — else its extension at
`l₁ σ` is `⊤`, the identity pulls the unit ideal back to the trace of `σ`, whose cosupport is then
empty (`cosupport_top`); `e n σ` is that partner and `hpair` is the identity at `l₁ σ`. A member
`τ` of level `n+1` with non-empty trace has a partner `σ` with `l₁ σ = l₂ τ` — else the transition
pulls `τ`'s trace back to `⊤`, and the transition, an isomorphism, reflects the unit ideal
(`comap_ne_top_of_isIso`); the partner's trace is non-empty by the same reflection, and it is sent
to `τ` by injectivity of `l₂`. -/
theorem exists_chainLabelMaps_of_extend (H : ∀ n, Λ n → ClosedSubspace (R (ULift.up n)))
    (Λ' : ℕ → Type u) (l₁ : ∀ n, Λ n → Λ' n) (l₂ : ∀ n, Λ (n + 1) → Λ' n)
    (hl₁ : ∀ n, Function.Injective (l₁ n)) (hl₂ : ∀ n, Function.Injective (l₂ n))
    (hpr : ∀ n (l : Λ' n), QuotientSpace.comap (G.t (ULift.up n) (ULift.up (n + 1))).1
        (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n)
          (Function.extend (l₂ n) (H (n + 1)) (fun _ => ⊤) l)) =
      restrictGlue π dom (ULift.up n) (ULift.up (n + 1))
        (Function.extend (l₁ n) (H n) (fun _ => ⊤) l)) :
    ∃ e : ∀ n, {σ : Λ n // chainTraceNonempty π dom H n σ} → Λ (n + 1),
      (∀ n σ, QuotientSpace.comap (G.t (ULift.up n) (ULift.up (n + 1))).1
          (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) (H (n + 1) (e n σ))) =
        restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) (H n σ.1)) ∧
      ∀ n (τ : Λ (n + 1)),
        (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) (H (n + 1) τ)).support.Nonempty →
          ∃ σ, e n σ = τ := by
  have rtop₁ : ∀ n, restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) (⊤ : ClosedSubspace _) = ⊤ :=
    fun n => QuotientSpace.comap_top _
  have rtop₂ : ∀ n, restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) (⊤ : ClosedSubspace _) = ⊤ :=
    fun n => QuotientSpace.comap_top _
  -- every member with non-empty trace has a partner at the next level
  have hpartner : ∀ n (σ : {σ : Λ n // chainTraceNonempty π dom H n σ}),
      ∃ τ, l₂ n τ = l₁ n σ.1 := by
    intro n σ
    by_contra hne
    have h2 : Function.extend (l₂ n) (H (n + 1)) (fun _ => ⊤) (l₁ n σ.1) = ⊤ :=
      Function.extend_apply' _ _ _ hne
    have h1 : Function.extend (l₁ n) (H n) (fun _ => ⊤) (l₁ n σ.1) = H n σ.1 :=
      (hl₁ n).extend_apply _ _ _
    have key := hpr n (l₁ n σ.1)
    rw [h1, h2, rtop₂ n, QuotientSpace.comap_top] at key
    have hσ : (restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) (H n σ.1)).support.Nonempty :=
      σ.2
    rw [← key, Manifold.IdealSheaf.support_top] at hσ
    exact Set.not_nonempty_empty hσ
  refine ⟨fun n σ => Classical.choose (hpartner n σ), fun n σ => ?_, fun n τ hτ => ?_⟩
  · have hτ : l₂ n (Classical.choose (hpartner n σ)) = l₁ n σ.1 :=
      Classical.choose_spec (hpartner n σ)
    have h2 : Function.extend (l₂ n) (H (n + 1)) (fun _ => ⊤) (l₁ n σ.1) =
        H (n + 1) (Classical.choose (hpartner n σ)) :=
      (congrArg (Function.extend (l₂ n) (H (n + 1)) (fun _ => ⊤)) hτ.symm).trans
        ((hl₂ n).extend_apply _ _ _)
    have h1 : Function.extend (l₁ n) (H n) (fun _ => ⊤) (l₁ n σ.1) = H n σ.1 :=
      (hl₁ n).extend_apply _ _ _
    have key := hpr n (l₁ n σ.1)
    rw [h1, h2] at key
    exact key
  · -- the partner of a member of the next level with non-empty trace
    have hpart : ∃ σ, l₁ n σ = l₂ n τ := by
      by_contra hne
      have h1 : Function.extend (l₁ n) (H n) (fun _ => ⊤) (l₂ n τ) = ⊤ :=
        Function.extend_apply' _ _ _ hne
      have h2 : Function.extend (l₂ n) (H (n + 1)) (fun _ => ⊤) (l₂ n τ) = H (n + 1) τ :=
        (hl₂ n).extend_apply _ _ _
      have key := hpr n (l₂ n τ)
      rw [h1, h2, rtop₁ n] at key
      have hiso : IsIso (G.t (ULift.up n) (ULift.up (n + 1))).1 :=
        G.toKGlueData.toLRSGlueData.toGlueData.t_isIso _ _
      have htop : restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) (H (n + 1) τ) = ⊤ := by
        by_contra hne
        exact QuotientSpace.comap_ne_top_of_isIso (G.t (ULift.up n) (ULift.up (n + 1))).1 hne key
      rw [htop, Manifold.IdealSheaf.support_top] at hτ
      exact Set.not_nonempty_empty hτ
    obtain ⟨σ, hσ⟩ := hpart
    have hσne : chainTraceNonempty π dom H n σ := by
      by_contra hne
      have htop : restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) (H n σ) = ⊤ :=
        Manifold.IdealSheaf.eq_top_of_not_nonempty_support hne
      have h1 : Function.extend (l₁ n) (H n) (fun _ => ⊤) (l₂ n τ) = H n σ :=
        (congrArg (Function.extend (l₁ n) (H n) (fun _ => ⊤)) hσ.symm).trans
          ((hl₁ n).extend_apply _ _ _)
      have h2 : Function.extend (l₂ n) (H (n + 1)) (fun _ => ⊤) (l₂ n τ) = H (n + 1) τ :=
        (hl₂ n).extend_apply _ _ _
      have key := hpr n (l₂ n τ)
      rw [h1, h2, htop] at key
      have hiso : IsIso (G.t (ULift.up n) (ULift.up (n + 1))).1 :=
        G.toKGlueData.toLRSGlueData.toGlueData.t_isIso _ _
      have htop' : restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) (H (n + 1) τ) = ⊤ := by
        by_contra hne
        exact QuotientSpace.comap_ne_top_of_isIso (G.t (ULift.up n) (ULift.up (n + 1))).1 hne key
      rw [htop', Manifold.IdealSheaf.support_top] at hτ
      exact Set.not_nonempty_empty hτ
    exact ⟨⟨σ, hσne⟩, hl₂ n ((Classical.choose_spec (hpartner n ⟨σ, hσne⟩)).trans hσ)⟩

end Chain

end GlueOver

end AnalyticSpace

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜}

namespace LocalEmbeddingData

variable {U : Set X} (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
  (hbed : bed.IsEmbeddedDesing) (h : D.ResolutionGluesOn bed)

/-- **The piece-trace clause, named** — for every piece `i`, every base open `P ⊆ U` inside the
piece's domain and every isomorphism `s` over `X` from the part of `resolutionOn` over `P` to the
part of the piece's local resolution over `P`, the pull-back of the piece trace of label `σ` is the
pull-back of the member `H σ` (the last clause of `exists_gluedMembers_resolutionOn_compat`). -/
abbrev PieceTraceCompat
    (H : D.sigmaIndex bed h.some.W h.some.isCompact_closure_W →
      ClosedSubspace (D.resolutionOn bed)) : Prop :=
  ∀ (i : D.ι) (P : Opens X), (P : Set X) ⊆ U → P ≤ D.pieceDom i (h.some.W i) →
    ∀ s : (D.resolutionOn bed).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed),
            Hom.continuous_toFun (D.resolutionOnToSpace bed)⟩ P) ⟶
        ((D.embedding i).localResolution bed (h.some.W i)
            (h.some.isCompact_closure_W i)).toKLocallyRingedSpace.restrictOpen
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
              (h.some.isCompact_closure_W i)),
            Hom.continuous_toFun ((D.embedding i).toSpaceMap bed (h.some.W i)
              (h.some.isCompact_closure_W i))⟩ P),
      IsIso s →
      ofRestrict _ _ ≫ D.resolutionOnToSpace bed =
        (s ≫ ofRestrict _ _) ≫
          (D.embedding i).toSpaceMap bed (h.some.W i) (h.some.isCompact_closure_W i) →
      ∀ σ, QuotientSpace.comap s.1 (QuotientSpace.comap (ofRestrict _ _).1
          (pieceTrace D bed h.some hbed i σ)) =
        QuotientSpace.comap (ofRestrict _ _).1 (H σ)

end LocalEmbeddingData

namespace BEDanFamStar

variable (bed : BEDanFamStar.{u} 𝕜) (Ex : bed.ExhaustionGluing X)

/-- **The common label set of two adjacent levels** of the exhaustion and the adjacent identity,
label by label, on the levels' members extended by `⊤` ([Kol07, Proposition 37, proof];
[Kol07, 34.4] for the padding). The common label set is that of the doubled datum
`sumPadData (Ex.D n) (Ex.D (n+1))` over the padded reading opens (`padReadingOpens`, reading the
levels' reading opens back: `preimageOpens_padExt_padReadingOpens`); the levels embed by the label
maps of `CoproductSumData.lean` composed with the padding identity's label isomorphisms read at
the levels' reading opens (`exists_padIdentity_of_padPreimageOpens_eq` on `padIdentityOn`); the
identity is the pointwise criterion for the pair
(`compatClosedSubspaces_pair_of_forall_exists_isoOver_two`), supplied point by point by
`exists_isoOver_resolutionOn_pair_of_forall_label` with the rigidity
`rigidOver_resolutionOnToSpace`. -/
theorem exists_pairLabels (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) (n : ℕ)
    (H₁ : (Ex.D n).sigmaIndex bed (Ex.glues n).some.W (Ex.glues n).some.isCompact_closure_W →
      ClosedSubspace ((Ex.D n).resolutionOn bed))
    (hH₁ : (Ex.D n).PieceTraceCompat bed hbed (Ex.glues n) H₁)
    (H₂ : (Ex.D (n + 1)).sigmaIndex bed (Ex.glues (n + 1)).some.W
        (Ex.glues (n + 1)).some.isCompact_closure_W →
      ClosedSubspace ((Ex.D (n + 1)).resolutionOn bed))
    (hH₂ : (Ex.D (n + 1)).PieceTraceCompat bed hbed (Ex.glues (n + 1)) H₂) :
    ∃ (Λ : Type u)
      (l₁ : (Ex.D n).sigmaIndex bed (Ex.glues n).some.W (Ex.glues n).some.isCompact_closure_W → Λ)
      (l₂ : (Ex.D (n + 1)).sigmaIndex bed (Ex.glues (n + 1)).some.W
        (Ex.glues (n + 1)).some.isCompact_closure_W → Λ),
      Function.Injective l₁ ∧ Function.Injective l₂ ∧
      ∀ l : Λ, QuotientSpace.comap (Ex.glue.t (ULift.up n) (ULift.up (n + 1))).1
          (GlueOver.restrictGlue (fun n : ULift.{u} ℕ => (Ex.D n.down).resolutionOnToSpace bed)
            (fun n => Ex.U n.down) (ULift.up (n + 1)) (ULift.up n)
            (Function.extend l₂ H₂ (fun _ => ⊤) l)) =
        GlueOver.restrictGlue (fun n : ULift.{u} ℕ => (Ex.D n.down).resolutionOnToSpace bed)
          (fun n => Ex.U n.down) (ULift.up n) (ULift.up (n + 1))
          (Function.extend l₁ H₁ (fun _ => ⊤) l) := by
  -- the padded reading opens of the two levels read the levels' reading opens
  obtain ⟨W₁, hW₁, hpre₁⟩ : ∃ (W₁ : ∀ i : (Ex.D n).ι, Opens (pieceAmbient.{u} 𝕜
        (((Ex.D n).padLeftData (Ex.D (n + 1)).n).embedding i).G))
      (_ : ∀ i, IsCompact (closure (W₁ i : Set (pieceAmbient.{u} 𝕜
        (((Ex.D n).padLeftData (Ex.D (n + 1)).n).embedding i).G)))),
      (Ex.D n).padPreimageOpens (Fin.castAddEmb (Ex.D (n + 1)).n) W₁ = (Ex.glues n).some.W :=
    ⟨fun i => padReadingOpens (Fin.castAddEmb (Ex.D (n + 1)).n) ((Ex.D n).embedding i).G
        ((Ex.glues n).some.W i),
      fun i => isCompact_closure_padReadingOpens _ _ _ ((Ex.glues n).some.isCompact_closure_W i),
      funext fun i => preimageOpens_padExt_padReadingOpens _ _ _⟩
  obtain ⟨W₂, hW₂, hpre₂⟩ : ∃ (W₂ : ∀ j : (Ex.D (n + 1)).ι, Opens (pieceAmbient.{u} 𝕜
        (((Ex.D (n + 1)).padRightData (Ex.D n).n).embedding j).G))
      (_ : ∀ j, IsCompact (closure (W₂ j : Set (pieceAmbient.{u} 𝕜
        (((Ex.D (n + 1)).padRightData (Ex.D n).n).embedding j).G)))),
      (Ex.D (n + 1)).padPreimageOpens (Fin.natAddEmb (Ex.D n).n) W₂ = (Ex.glues (n + 1)).some.W :=
    ⟨fun j => padReadingOpens (Fin.natAddEmb (Ex.D n).n) ((Ex.D (n + 1)).embedding j).G
        ((Ex.glues (n + 1)).some.W j),
      fun j => isCompact_closure_padReadingOpens _ _ _
        ((Ex.glues (n + 1)).some.isCompact_closure_W j),
      funext fun j => preimageOpens_padExt_padReadingOpens _ _ _⟩
  -- the padding identities at the levels' reading opens
  obtain ⟨o₁, ψ₁, -, hmem₁, hpiece₁⟩ :=
    (Ex.D n).exists_padIdentity_of_padPreimageOpens_eq (Fin.castAddEmb (Ex.D (n + 1)).n) W₁ hW₁
      bed hbed (Ex.glues n).some.W (Ex.glues n).some.isCompact_closure_W
      ((Ex.D n).padIdentityOn (Fin.castAddEmb (Ex.D (n + 1)).n) W₁ hW₁ bed hbed) hpre₁
  obtain ⟨o₂, ψ₂, -, hmem₂, hpiece₂⟩ :=
    (Ex.D (n + 1)).exists_padIdentity_of_padPreimageOpens_eq (Fin.natAddEmb (Ex.D n).n) W₂ hW₂
      bed hbed (Ex.glues (n + 1)).some.W (Ex.glues (n + 1)).some.isCompact_closure_W
      ((Ex.D (n + 1)).padIdentityOn (Fin.natAddEmb (Ex.D n).n) W₂ hW₂ bed hbed) hpre₂
  -- the label maps of the two padded levels into the common label set
  obtain ⟨lab₁, hlab₁, hlab₁'⟩ :=
    LocalEmbeddingData.exists_orderEmbedding_comap_sumInlResIn_sigmaMembers (Ex.D n) (Ex.D (n + 1))
      W₁ W₂ bed hW₁ hW₂ hbed
  obtain ⟨lab₂, hlab₂, hlab₂'⟩ :=
    LocalEmbeddingData.exists_orderEmbedding_comap_sumInrResIn_sigmaMembers (Ex.D n) (Ex.D (n + 1))
      W₁ W₂ bed hW₁ hW₂ hbed
  have hinj₁ : Function.Injective fun k => lab₁ (o₁.symm k) :=
    lab₁.injective.comp o₁.symm.injective
  have hinj₂ : Function.Injective fun k => lab₂ (o₂.symm k) :=
    lab₂.injective.comp o₂.symm.injective
  -- the levels' members extended by `⊤` to the common label set
  have hA₁ : ∀ k, Function.extend (fun k => lab₁ (o₁.symm k)) H₁ (fun _ => ⊤) (lab₁ k) =
      H₁ (o₁ k) := fun k =>
    (congrArg (Function.extend (fun k => lab₁ (o₁.symm k)) H₁ (fun _ => ⊤))
      (congrArg (fun m => lab₁ m) (o₁.symm_apply_apply k)).symm).trans
      (hinj₁.extend_apply H₁ (fun _ => ⊤) (o₁ k))
  have hA₁' : ∀ σ, σ ∉ Set.range lab₁ →
      Function.extend (fun k => lab₁ (o₁.symm k)) H₁ (fun _ => ⊤) σ = ⊤ :=
    fun σ hσ => Function.extend_apply' _ _ _ fun ⟨a, ha⟩ => hσ ⟨o₁.symm a, ha⟩
  have hA₂ : ∀ k, Function.extend (fun k => lab₂ (o₂.symm k)) H₂ (fun _ => ⊤) (lab₂ k) =
      H₂ (o₂ k) := fun k =>
    (congrArg (Function.extend (fun k => lab₂ (o₂.symm k)) H₂ (fun _ => ⊤))
      (congrArg (fun m => lab₂ m) (o₂.symm_apply_apply k)).symm).trans
      (hinj₂.extend_apply H₂ (fun _ => ⊤) (o₂ k))
  have hA₂' : ∀ σ, σ ∉ Set.range lab₂ →
      Function.extend (fun k => lab₂ (o₂.symm k)) H₂ (fun _ => ⊤) σ = ⊤ :=
    fun σ hσ => Function.extend_apply' _ _ _ fun ⟨a, ha⟩ => hσ ⟨o₂.symm a, ha⟩
  refine ⟨_, fun k => lab₁ (o₁.symm k), fun k => lab₂ (o₂.symm k), hinj₁, hinj₂, fun l => ?_⟩
  -- the pointwise criterion at the pair, supplied point by point by the local pair identity
  refine Ex.glue.compatClosedSubspaces_pair_of_forall_exists_isoOver_two (ULift.up n)
    (ULift.up (n + 1)) (fun h => Nat.succ_ne_self n (congrArg ULift.down h).symm)
    (Function.extend (fun k => lab₁ (o₁.symm k)) H₁ (fun _ => ⊤) l)
    (Function.extend (fun k => lab₂ (o₂.symm k)) H₂ (fun _ => ⊤) l) fun y hy => ?_
  obtain ⟨P, hP, hxP, θ, hθ, hover, hmemb⟩ :=
    LocalEmbeddingData.exists_isoOver_resolutionOn_pair_of_forall_label (Ex.D n) (Ex.D (n + 1))
      bed hbed (Ex.glues n) (Ex.glues (n + 1)) W₁ hW₁ W₂ hW₂ o₁ ψ₁ hmem₁ hpiece₁ o₂ ψ₂ hmem₂
      hpiece₂ lab₁ hlab₁ hlab₁' lab₂ hlab₂ hlab₂' hpre₁ hpre₂ H₁ hH₁ H₂ hH₂
      (Function.extend (fun k => lab₁ (o₁.symm k)) H₁ (fun _ => ⊤)) hA₁ hA₁'
      (Function.extend (fun k => lab₂ (o₂.symm k)) H₂ (fun _ => ⊤)) hA₂ hA₂'
      (Ex.U n ⊓ Ex.U (n + 1)) (fun x hx => Opens.mem_inf.mp hx)
      (KLocallyRingedSpace.Hom.toFun ((Ex.D n).resolutionOnToSpace bed) y)
      (show KLocallyRingedSpace.Hom.toFun ((Ex.D n).resolutionOnToSpace bed) y ∈ Ex.U n ⊓ Ex.U
          (n + 1) from hy)
  exact ⟨P, hP, hxP, (Ex.D n).rigidOver_resolutionOnToSpace bed hbed hind P
    (fun x hx => (Opens.mem_inf.mp (hP hx)).1), θ, hθ, hover, hmemb l⟩

/-- **The chain families of an exhaustion from the labelled compatibility of every level**
([Kol07, Proposition 37, proof]; [Kol07, Theorem 45(3)]; [Wlo09, §4.3]) — the input of
`Hironaka/Resolution/Analytic/Kol07Thm45/Glue/OverFamilyChain.lean`: on every level the simple
normal crossings family of `exists_gluedMembers_resolutionOn_compat` (locally finite, supported on
the preimage of the singular locus), and the label maps `e n` on the members with non-empty trace
with the adjacent identity `hpair` and the covering `hsurj`, from the common label sets of the
adjacent pairs (`exists_pairLabels`) through `exists_chainLabelMaps_of_extend`. -/
theorem exists_chainFamilies_of_compat (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed)
    (hc : ∀ n, (Ex.glues n).some.glue.LabelledCompat
      (LocalEmbeddingData.pieceTrace (Ex.D n) bed (Ex.glues n).some hbed) (fun _ σ => σ)) :
    ∃ H : ∀ n, (Ex.D n).sigmaIndex bed (Ex.glues n).some.W (Ex.glues n).some.isCompact_closure_W →
        ClosedSubspace ((Ex.D n).resolutionOn bed),
      (∀ n, ClosedSubspace.IsSncFamily (H n)) ∧
      (∀ n, LocallyFinite (fun σ => Manifold.IdealSheaf.support (H n σ))) ∧
      (∀ n, (⋃ σ, Manifold.IdealSheaf.support (H n σ)) =
        KLocallyRingedSpace.Hom.toFun ((Ex.D n).resolutionOnToSpace bed) ⁻¹'
            singularLocus X)
            ∧
      ∃ e : ∀ n, {σ // GlueOver.chainTraceNonempty
            (fun n : ULift.{u} ℕ => (Ex.D n.down).resolutionOnToSpace bed) (fun n => Ex.U n.down)
            H n σ} →
          (Ex.D (n + 1)).sigmaIndex bed (Ex.glues (n + 1)).some.W
            (Ex.glues (n + 1)).some.isCompact_closure_W,
        (∀ n σ, QuotientSpace.comap (Ex.glue.t (ULift.up n) (ULift.up (n + 1))).1
            (GlueOver.restrictGlue (fun n : ULift.{u} ℕ => (Ex.D n.down).resolutionOnToSpace bed)
              (fun n => Ex.U n.down) (ULift.up (n + 1)) (ULift.up n) (H (n + 1) (e n σ))) =
          GlueOver.restrictGlue (fun n : ULift.{u} ℕ => (Ex.D n.down).resolutionOnToSpace bed)
            (fun n => Ex.U n.down) (ULift.up n) (ULift.up (n + 1)) (H n σ.1)) ∧
        ∀ n τ, (GlueOver.restrictGlue (fun n : ULift.{u} ℕ => (Ex.D n.down).resolutionOnToSpace bed)
            (fun n => Ex.U n.down) (ULift.up (n + 1)) (ULift.up n)
            (H (n + 1) τ)).support.Nonempty →
          ∃ σ, e n σ = τ := by
  -- the glued family with its piece-trace clause at every level
  have hlev : ∀ n, ∃ H : (Ex.D n).sigmaIndex bed (Ex.glues n).some.W
        (Ex.glues n).some.isCompact_closure_W →
        ClosedSubspace ((Ex.D n).resolutionOn bed),
      ClosedSubspace.IsSncFamily H ∧
      LocallyFinite (fun σ => Manifold.IdealSheaf.support (H σ)) ∧
      (⋃ σ, Manifold.IdealSheaf.support (H σ)) =
        KLocallyRingedSpace.Hom.toFun ((Ex.D n).resolutionOnToSpace bed) ⁻¹'
            singularLocus X ∧
      (Ex.D n).PieceTraceCompat bed hbed (Ex.glues n) H :=
    fun n => (Ex.D n).exists_gluedMembers_resolutionOn_compat bed hbed hind (Ex.glues n) (hc n)
  choose H hH using hlev
  -- the common label sets of the adjacent pairs
  choose Λ' l₁ l₂ hl₁ hl₂ hpr using fun n =>
    exists_pairLabels bed Ex hbed hind n (H n) (hH n).2.2.2 (H (n + 1)) (hH (n + 1)).2.2.2
  obtain ⟨e, hpair, hsurj⟩ := Ex.glue.exists_chainLabelMaps_of_extend H Λ' l₁ l₂ hl₁ hl₂ hpr
  exact ⟨H, fun n => (hH n).1, fun n => (hH n).2.1, fun n => (hH n).2.2.1, e, hpair, hsurj⟩

/-- **The chain families of an exhaustion** ([Kol07, Proposition 37, proof];
[Kol07, Theorem 45(3)]; [Wlo09, §4.3]) — `exists_chainFamilies_of_compat` with the labelled
compatibility of every level's coproduct traces, `labelledCompat_pieceTrace`
(`CoproductGluedFamilyCompat.lean`). No reducedness of `X` is assumed. -/
theorem exists_chainFamilies (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) :
    ∃ H : ∀ n, (Ex.D n).sigmaIndex bed (Ex.glues n).some.W (Ex.glues n).some.isCompact_closure_W →
        ClosedSubspace ((Ex.D n).resolutionOn bed),
      (∀ n, ClosedSubspace.IsSncFamily (H n)) ∧
      (∀ n, LocallyFinite (fun σ => Manifold.IdealSheaf.support (H n σ))) ∧
      (∀ n, (⋃ σ, Manifold.IdealSheaf.support (H n σ)) =
        KLocallyRingedSpace.Hom.toFun ((Ex.D n).resolutionOnToSpace bed) ⁻¹'
            singularLocus X)
            ∧
      ∃ e : ∀ n, {σ // GlueOver.chainTraceNonempty
            (fun n : ULift.{u} ℕ => (Ex.D n.down).resolutionOnToSpace bed) (fun n => Ex.U n.down)
            H n σ} →
          (Ex.D (n + 1)).sigmaIndex bed (Ex.glues (n + 1)).some.W
            (Ex.glues (n + 1)).some.isCompact_closure_W,
        (∀ n σ, QuotientSpace.comap (Ex.glue.t (ULift.up n) (ULift.up (n + 1))).1
            (GlueOver.restrictGlue (fun n : ULift.{u} ℕ => (Ex.D n.down).resolutionOnToSpace bed)
              (fun n => Ex.U n.down) (ULift.up (n + 1)) (ULift.up n) (H (n + 1) (e n σ))) =
          GlueOver.restrictGlue (fun n : ULift.{u} ℕ => (Ex.D n.down).resolutionOnToSpace bed)
            (fun n => Ex.U n.down) (ULift.up n) (ULift.up (n + 1)) (H n σ.1)) ∧
        ∀ n τ, (GlueOver.restrictGlue (fun n : ULift.{u} ℕ => (Ex.D n.down).resolutionOnToSpace bed)
            (fun n => Ex.U n.down) (ULift.up (n + 1)) (ULift.up n)
            (H (n + 1) τ)).support.Nonempty →
          ∃ σ, e n σ = τ :=
  exists_chainFamilies_of_compat bed Ex hbed hind fun n =>
    (Ex.D n).labelledCompat_pieceTrace bed (Ex.glues n).some hbed hind

end BEDanFamStar

end Hironaka.Manifold

end
