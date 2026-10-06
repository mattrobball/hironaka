/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.FamilyData
public import Hironaka.Resolution.Analytic.OrderReduction.Step22Defs
public import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The data consumed by Step 2.2 of the proof of Theorem 103

Step 2.2 of the proof of [Kol07, Theorem 103] ([Kol07, 104, Step 2.2]) applies, at the last stage
of the sequence of Step 2.1, Lemma 102 to the triple `(X_r, I_r, H_r + E_r)` at the member `H_r`,
the transform of the hypersurface of maximal contact. Kollár declares `H` the first member of
`H + E`; the library appends it as the greatest member of the boundary, and the class `stepHClass`
(`Step22Defs.lean`) is that of triples with a greatest member. What the machinery of Step 2.2 in
the compatible-family form (`Step22Fam.lean` to `LocalFunctorFam.lean`) uses of the family applied
at that member is four of the clauses of `BDanFamData` (`FamilyData.lean`): the value, the order
clause in the form "of order `≥ s`" ([Kol07, Definition 66 (1′)–(4′)]; it enters the uniqueness of
the hypersurface of maximal contact, [Kol07, Theorem 97]), the commutation with local analytic
isomorphisms and the indifference to empty boundary members. Neither the exactness of the order nor
Lemma 102 (1) is used there. This matters because the modified algorithm of Włodarczyk (the proof
of [Wlo09, Theorem 7.4.1]: the components on which the ideal has become the ideal of a smooth
hypersurface are left alone) supplies data for the same step which satisfy the four clauses but
not the other two.

* `HFamData ψ₀ s` — the four clauses; `BDanFamData.toHFamData` (Lemma 102's family is an
  instance).
* `HFData ψ₀ s` — the data of Step 2 at the mark `s`: Step 2.1's data `bd₁ : BDanFamData ψ₀ s` and
  the data `hf : HFamData ψ₀ (tuningParam s)` for the hypersurface step at the re-tuned mark
  (Step 2.2 begins by replacing `I` by `W(I)` once more); `HFData.ofBDanFamData` takes both from
  Lemma 102's data at every mark, as Kollár does, with the unfolding lemmas `ofBDanFamData_bd₁`,
  `ofBDanFamData_hf`.
* `HFamData.hstepFunctor` — the family at the greatest member, as a family functor on the class
  `stepHClass s`; its commutation with local analytic isomorphisms is
  `HFamData.hstepFunctor_commutesWithLocalIsos` (`Step22FamFunctoriality.lean`).

The assembly of Step 2 over `HFData` is in `Step22Fam.lean` and its successors; the data of
Włodarczyk's modified step at the mark `1` are `BMOmod.hFamDataMod` (`Modified/StepBData.lean`).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-- The data consumed by Step 2.2 of the proof of [Kol07, Theorem 103] at the mark `s`: a
compatible family on every triple of the class of `BO_{n,s}` and every member of its boundary,
which on every relatively compact open is a smooth blow-up sequence of order `≥ s` for the
restricted triple ([Kol07, Definition 66 (1′)–(4′)]), commutes with local analytic isomorphisms
(both bullets of [Kol07, 34.1] in one clause per open) and is indifferent to empty boundary
members. These are the clauses of `BDanFamData` without the exactness of the order and without
Lemma 102 (1). -/
structure HFamData (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) (s : ℕ) where
  /-- The value at the member `j` as a compatible family. -/
  fam : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M), AnalyticTriple.BOClass s T →
    T.F.ι → CompatibleFamily T
  /-- [Kol07, Definition 66 (1′)–(4′)] per open: the value on `U` is of order `≥ s` for the
  restricted triple `(U, 𝓘|_U, E|_U)`. -/
  isOfOrderGe : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass s T) (j : T.F.ι) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))),
    ((fam T hT j).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I s
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf
  /-- Both bullets of [Kol07, 34.1] in one clause per open, the member index kept: along a local
  analytic isomorphism `g`, the value of the pulled-back triple on a relatively compact open is the
  pull-back of the value on the image open, with empty blow-ups deleted. -/
  commutesWithLocalIsos : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (hT : AnalyticTriple.BOClass s T) (hT' : AnalyticTriple.BOClass s (T.pullback g hg))
    (j : T.F.ι) (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
    (fam (T.pullback g hg) hT' j).seqOn U' hU' =
      (((fam T hT j).seqOn (AnalyticMap.imageOpens g hg U')
            (AnalyticMap.isCompact_closure_image g hU')).pullback
          (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
          (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
            Set.Subset.rfl)).eraseEmpty
  /-- Indifference to empty boundary members, per open: deleting empty members along an order
  embedding of the index types does not change the value at a kept member. -/
  indifferentToEmptyMembers : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι),
    (∀ i, T.F.hyp (e i) = F'.hyp i) → (∀ b, b ∉ Set.range e → T.F.hyp b = ∅) →
    ∀ (hT : AnalyticTriple.BOClass s T)
      (hT' : AnalyticTriple.BOClass s
        (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M))
      (i : F'.ι) (U : Opens M) (hU : IsCompact (closure (U : Set M))),
      (fam T hT (e i)).seqOn U hU =
        (fam ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ hT' i).seqOn U hU

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {s : ℕ}

/-- Lemma 102's family data satisfy the four clauses of `HFamData` (its exact order gives the order
clause). -/
def BDanFamData.toHFamData (bd : BDanFamData ψ₀ s) : HFamData ψ₀ s where
  fam := bd.fam
  isOfOrderGe T hT j U hU := (bd.isOfOrder T hT j U hU).isOfOrderGe
  commutesWithLocalIsos := bd.commutesWithLocalIsos
  indifferentToEmptyMembers := bd.indifferentToEmptyMembers

/-- The data of Step 2 of the proof of [Kol07, Theorem 103] in the compatible-family form, at the
mark `s`: the data of Step 2.1 (Lemma 102's family at the mark `s`, [Kol07, Theorem 103,
Step 2.1]) and the data for the hypersurface step of Step 2.2 at the re-tuned mark `tuningParam s`
([Kol07, 104, Step 2.2]: "we can again replace `I` by `W(I)`"). Kollár takes both from Lemma 102's
data at every mark (`HFData.ofBDanFamData`); Włodarczyk's modified algorithm (the proof of
[Wlo09, Theorem 7.4.1]) takes the second from the modified marked resolution
(`BMOmod.hFamDataMod`). -/
structure HFData (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) (s : ℕ) where
  /-- The data of Step 2.1 at the mark `s`. -/
  bd₁ : BDanFamData.{u} ψ₀ s
  /-- The data for the hypersurface step at the re-tuned mark `tuningParam s`. -/
  hf : HFamData.{u} ψ₀ (tuningParam s)

/-- The data of Step 2 as Kollár takes them: Lemma 102's family data at the mark `s` and at the
re-tuned mark. -/
def HFData.ofBDanFamData (bd : ∀ s : ℕ, BDanFamData.{u} ψ₀ s) (s : ℕ) : HFData.{u} ψ₀ s :=
  ⟨bd s, (bd (tuningParam s)).toHFamData⟩

@[simp] theorem HFData.ofBDanFamData_bd₁ (bd : ∀ s : ℕ, BDanFamData.{u} ψ₀ s) (s : ℕ) :
    (HFData.ofBDanFamData bd s).bd₁ = bd s := rfl

@[simp] theorem HFData.ofBDanFamData_hf (bd : ∀ s : ℕ, BDanFamData.{u} ψ₀ s) (s : ℕ) :
    (HFData.ofBDanFamData bd s).hf = (bd (tuningParam s)).toHFamData := rfl

namespace HFamData

open _root_.Manifold

variable (hf : HFamData ψ₀ s)

/-- The value of the family depends only on the triple and the member: transport along an equality
of triples and a matching equality of members. -/
theorem fam_congr_seqOn {M : AnalyticManifold.{u} 𝕜 E} {T₁ T₂ : AnalyticTriple ψ₀ M} (e : T₁ = T₂)
    (h₁ : AnalyticTriple.BOClass s T₁) (h₂ : AnalyticTriple.BOClass s T₂) (j₁ : T₁.F.ι)
    (j₂ : T₂.F.ι) (hj : HEq j₁ j₂) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (hf.fam T₁ h₁ j₁).seqOn U hU = (hf.fam T₂ h₂ j₂).seqOn U hU := by
  subst e
  cases hj
  rfl

/-- The family applied at the greatest member of the boundary, as a family functor on the class
`stepHClass s` of triples of `BOClass s` with a greatest member; `stepHFamFunctor`
(`Step22Fam.lean`) is this functor at Lemma 102's data. -/
def hstepFunctor : AnalyticFamilyFunctor ψ₀ (BO.stepHClass s) where
  fam T hT := hf.fam T hT.1 (BO.greatestIdx hT)

theorem hstepFunctor_fam {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : BO.stepHClass s T) : hf.hstepFunctor.fam T hT = hf.fam T hT.1 (BO.greatestIdx hT) := rfl

end HFamData

end Hironaka.Manifold

end
