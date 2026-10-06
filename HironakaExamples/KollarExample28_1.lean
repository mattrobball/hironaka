/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import HironakaExamples.Sequence.Prop37Constraints

/-!
# Kollár's Example 28.1: local blow-up sequences that do not glue

[Kol07, Example 28.1]: `X` a smooth threefold, `C₁, C₂` irreducible curves meeting at two points
`p₁, p₂`, `Cᵢ` smooth away from `pᵢ` where it has a cusp transversal to the other curve; on
`U₁ = X ∖ {p₁}` one blows up `C₁` first, on `U₂ = X ∖ {p₂}` `C₂` first; over `U₁ ∩ U₂`, where the
two curves are disjoint, both local sequences blow up the same two curves, in opposite orders, and
no rule says which to blow up first. This file places local models on `X = 𝔸³_k`:
`p₁ = (0, 0, 0)`, `p₂ = (1, 0, 0)`,
`C₁ = V(z, y² − x³)` (a cuspidal curve near `p₁`), `C₂ = V(y, z² − (x − 1)³)` (near `p₂`). On `𝔸³`
these two curves are disjoint (`z = y = 0` forces `x = 0` and `x = 1`): the file does not model
Kollár's global configuration (curves meeting at `p₁, p₂` with transversal cusps, the end results
gluing to a locally but not globally projective `Y`); the disjoint model suffices for the failure
of the gluing condition (37.1) of [Kol07, Proposition 37] (the first centres of the local
sequences agree on the overlaps), which is Kollár's own diagnosis. The `example`s instantiate the
mechanism of `HironakaExamples/Sequence/Prop37Constraints.lean`: the first centres `C₁|_{U₁}`,
`C₂|_{U₂}` of the two local sequences differ on the overlap `U₁ ×_X U₂` (the point `q = (4, 8, 0)`
of `U₁ ∩ U₂` lies on `C₁` and not on `C₂`), so, whatever the continuations, no blow-up sequence on
`X` restricts to both (`not_exists_pullback_eq_of_center_ne`), and (37.1) is the condition violated.
The `example`s show that these two first centres do not glue; that the rule "blow up the smooth
curve first" selects them (smoothness of `C₁` on `U₁`, the cusp of `C₂` at `p₂`) is not proved here.
-/

@[expose] public section

namespace Hironaka.Sequence.Examples.Example28

open AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme BlowUpSequence
open Scheme.IdealSheafData

variable (k : Type) [Field k]

/-- The coordinate ring `k[x, y, z]`, with `x = X 0`, `y = X 1`, `z = X 2`. -/
abbrev Poly := MvPolynomial (Fin 3) k

/-- The affine space `𝔸³_k`. -/
noncomputable abbrev A3 : Scheme := Spec (CommRingCat.of (Poly k))

/-- The ideal sheaf of the closed subscheme `V(I) ⊆ 𝔸³_k`. -/
noncomputable def vanishing (I : Ideal (Poly k)) : (A3 k).IdealSheafData :=
  ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of (Poly k))).inv.hom)

/-- `C₁ = V(z, y² − x³)`: the cuspidal model near `p₁ = (0, 0, 0)` (its singularity at `p₁` and
smoothness elsewhere are not proved here). -/
noncomputable def idealC₁ : Ideal (Poly k) :=
  Ideal.span {MvPolynomial.X 2, MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3}

/-- `C₂ = V(y, z² − (x − 1)³)`: the cuspidal model near `p₂ = (1, 0, 0)` (its singularity at `p₂`
and smoothness elsewhere are not proved here). -/
noncomputable def idealC₂ : Ideal (Poly k) :=
  Ideal.span {MvPolynomial.X 1, MvPolynomial.X 2 ^ 2 - (MvPolynomial.X 0 - 1) ^ 3}

theorem eval_surjective (v : Fin 3 → k) : Function.Surjective (MvPolynomial.eval v) :=
  fun a => ⟨MvPolynomial.C a, MvPolynomial.eval_C a⟩

/-- The `k`-point of `𝔸³_k` with coordinates `v`: the maximal ideal `ker (eval v)`. -/
noncomputable def pt (v : Fin 3 → k) : A3 k :=
  (⟨RingHom.ker (MvPolynomial.eval v),
    (RingHom.ker_isMaximal_of_surjective _ (eval_surjective k v)).isPrime⟩ : PrimeSpectrum (Poly k))

theorem isMaximal_pt (v : Fin 3 → k) : (pt k v).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (eval_surjective k v)

theorem mem_pt_iff (v : Fin 3 → k) (f : Poly k) :
    f ∈ (pt k v).asIdeal ↔ MvPolynomial.eval v f = 0 :=
  RingHom.mem_ker

/-- A point of `𝔸³_k` lies on `V(I)` iff `I` is contained in its prime ideal. -/
theorem mem_support_vanishing_iff (I : Ideal (Poly k)) (x : A3 k) :
    x ∈ (vanishing k I).support ↔ I ≤ x.asIdeal := by
  have hbij := (ConcreteCategory.bijective_of_isIso (C := CommRingCat)
    (Scheme.ΓSpecIso (CommRingCat.of (Poly k))).inv)
  rw [← SetLike.mem_coe, vanishing, coe_support_ofIdealTop, Spec_zeroLocus]
  refine (PrimeSpectrum.mem_zeroLocus (x : PrimeSpectrum (Poly k)) _).trans ?_
  constructor
  · intro h f hf
    exact h (Ideal.mem_map_of_mem _ hf)
  · intro h f hf
    have : f ∈ (I.map (Scheme.ΓSpecIso (CommRingCat.of (Poly k))).inv.hom).comap
        (Scheme.ΓSpecIso (CommRingCat.of (Poly k))).inv.hom := hf
    rw [Ideal.comap_map_of_bijective _ hbij] at this
    exact h this

/-- The open subscheme `X ∖ {p}` for a closed point `p`. -/
def openCompl (p : A3 k) (hp : p.asIdeal.IsMaximal) : (A3 k).Opens :=
  ⟨{p}ᶜ, ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 hp).isOpen_compl⟩

theorem mem_openCompl_iff (p : A3 k) (hp : p.asIdeal.IsMaximal) (x : A3 k) :
    x ∈ openCompl k p hp ↔ x ≠ p := Iff.rfl

/-- `p₁ = (0, 0, 0)`. -/
noncomputable abbrev p₁ : A3 k := pt k ![0, 0, 0]

/-- `p₂ = (1, 0, 0)`. -/
noncomputable abbrev p₂ : A3 k := pt k ![1, 0, 0]

/-- The witness point `q = (4, 8, 0)`: on `C₁` (`8² = 4³`), not on `C₂` (`y = 8 ≠ 0`). -/
noncomputable abbrev q : A3 k := pt k ![4, 8, 0]

/-- `U₁ = X ∖ {p₁}`. -/
noncomputable abbrev U₁ : (A3 k).Opens := openCompl k (p₁ k) (isMaximal_pt k _)

/-- `U₂ = X ∖ {p₂}`. -/
noncomputable abbrev U₂ : (A3 k).Opens := openCompl k (p₂ k) (isMaximal_pt k _)

/-- Two `k`-points with different coordinates are different points (a polynomial separates them). -/
theorem pt_ne_of_eval_ne {v w : Fin 3 → k} (f : Poly k) (hv : MvPolynomial.eval v f = 0)
    (hw : MvPolynomial.eval w f ≠ 0) : pt k v ≠ pt k w := by
  intro h
  have : f ∈ (pt k w).asIdeal := h ▸ (mem_pt_iff k v f).2 hv
  exact hw ((mem_pt_iff k w f).1 this)

theorem q_ne_p₁ [CharZero k] : q k ≠ p₁ k :=
  pt_ne_of_eval_ne k (MvPolynomial.X 0 - MvPolynomial.C 4) (by simp) (by simp)

theorem q_ne_p₂ [CharZero k] : q k ≠ p₂ k :=
  pt_ne_of_eval_ne k (MvPolynomial.X 0 - MvPolynomial.C 4) (by simp) (by norm_num)

/-- `q ∈ C₁`. -/
theorem q_mem_C₁ : q k ∈ (vanishing k (idealC₁ k)).support := by
  rw [mem_support_vanishing_iff, idealC₁, Ideal.span_le]
  rintro f (rfl | rfl)
  · exact (mem_pt_iff k _ _).2 (by simp)
  · exact (mem_pt_iff k _ _).2 (by norm_num)

/-- `q ∉ C₂`. -/
theorem q_not_mem_C₂ [CharZero k] : q k ∉ (vanishing k (idealC₂ k)).support := by
  rw [mem_support_vanishing_iff, idealC₂, Ideal.span_le]
  intro h
  have := (mem_pt_iff k _ _).1 (h (Set.mem_insert _ _))
  norm_num at this

/-- The first centres of the two local sequences differ on the overlap `U₁ ×_X U₂`: the point `q`
lies on `C₁` and not on `C₂`. -/
theorem center_ne [CharZero k] :
    ((vanishing k (idealC₁ k)).comap (U₁ k).ι).comap (pullback.fst (U₁ k).ι (U₂ k).ι) ≠
      ((vanishing k (idealC₂ k)).comap (U₂ k).ι).comap (pullback.snd (U₁ k).ι (U₂ k).ι) := by
  intro heq
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := (U₁ k).ι) (g := (U₂ k).ι)
    (⟨q k, q_ne_p₁ k⟩ : U₁ k) (⟨q k, q_ne_p₂ k⟩ : U₂ k) rfl
  have h₁ : w ∈ (((vanishing k (idealC₁ k)).comap (U₁ k).ι).comap
      (pullback.fst (U₁ k).ι (U₂ k).ι)).support := by
    rw [mem_support_comap_iff_apply, mem_support_comap_iff_apply, hw₁]
    exact q_mem_C₁ k
  rw [heq, mem_support_comap_iff_apply, mem_support_comap_iff_apply, hw₂] at h₁
  exact q_not_mem_C₂ k h₁

/-- The two-piece cover `{U₁, U₂}` of `𝔸³_k`, indexed by `Bool`. -/
noncomputable def piece : Bool → Scheme
  | true => U₁ k
  | false => U₂ k

/-- The inclusions of the pieces. -/
noncomputable def incl : ∀ b, piece k b ⟶ A3 k
  | true => (U₁ k).ι
  | false => (U₂ k).ι

instance (b : Bool) : IsOpenImmersion (incl k b) := by
  cases b <;> exact inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))

/-- The two local sequences with the first centres the rule "blow up the smooth curve first" is
meant to select: `C₁|_{U₁}` on `U₁`, `C₂|_{U₂}` on `U₂`, with arbitrary continuations `r₁`, `r₂`
(the selection itself is not proved here). -/
noncomputable def localSeq
    (r₁ : BlowUpSequence ((vanishing k (idealC₁ k)).comap (U₁ k).ι).blowUp)
    (r₂ : BlowUpSequence ((vanishing k (idealC₂ k)).comap (U₂ k).ι).blowUp) :
    ∀ b, BlowUpSequence (piece k b)
  | true => cons (U₁ k) ((vanishing k (idealC₁ k)).comap (U₁ k).ι) r₁
  | false => cons (U₂ k) ((vanishing k (idealC₂ k)).comap (U₂ k).ι) r₂

/-- Example 28.1: the two local sequences do not agree on the overlap; the gluing condition (37.1)
fails for these first centres. -/
example [CharZero k]
    (r₁ : BlowUpSequence ((vanishing k (idealC₁ k)).comap (U₁ k).ι).blowUp)
    (r₂ : BlowUpSequence ((vanishing k (idealC₂ k)).comap (U₂ k).ι).blowUp) :
    ¬ AgreeOnOverlaps (incl k) (localSeq k r₁ r₂) :=
  not_agreeOnOverlaps_of_center_ne (incl k) (localSeq k r₁ r₂) (i := true) (j := false) rfl rfl
    (center_ne k)

/-- Example 28.1: no blow-up sequence on `𝔸³_k` restricts to the two local sequences, whatever
their continuations; a rule selecting these first centres is not a blow-up sequence functor. -/
example [CharZero k]
    (r₁ : BlowUpSequence ((vanishing k (idealC₁ k)).comap (U₁ k).ι).blowUp)
    (r₂ : BlowUpSequence ((vanishing k (idealC₂ k)).comap (U₂ k).ι).blowUp) :
    ¬ ∃ S₀ : BlowUpSequence (A3 k), ∀ b, S₀.pullback (incl k b) = localSeq k r₁ r₂ b :=
  not_exists_pullback_eq_of_center_ne (incl k) (localSeq k r₁ r₂) (i := true) (j := false) rfl rfl
    (center_ne k)

end Hironaka.Sequence.Examples.Example28
