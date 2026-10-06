/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.RingHom.Flat
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Saturations under a ring map that becomes flat after a descent

The transport lemma behind the local description of the strict transform of a closed analytic
subspace, `I_{X',a'} = {f ∈ 𝒪_{M',a'} : y_exc^k f ∈ I_{σ^{-1}(X),a'} for some k}`
[BM97, Proposition 3.13]: for a ring map `χ : R → S` and a further map `ι : S → T` such that
`ι ∘ χ` is flat and ideals of `S` descend along `ι` (`ι⁻¹(J T) = J`), the saturation
`⋃_k (I : e^k)` of an ideal `I ⊆ R` by the powers of an element `e` is carried by `χ` onto the
saturation of `I S` by the powers of `χ(e)`:
`⋃_k (I S : χ(e)^k) = (⋃_k (I : e^k)) S`.

The inclusion `⊇` needs nothing. For `⊆`, an element `g` with `χ(e)^k g ∈ I S` is sent by `ι`
into `(I T : (ιχ)(e)^k) = (I : e^k) T` — colon ideals by a principal ideal commute with flat base
change, `AlgebraicGeometry.map_colon_singleton_of_flat` — and `(I : e^k) T ∩ S = (I : e^k) S` by
the descent hypothesis. Bierstone and Milman prove Proposition 3.13 through the diagram of initial
exponents; the argument here uses flatness instead, with `S` the local ring of the blown-up
manifold at `a'`, `T` its completion, and `R` a polynomial chart ring of the blow-up: the
flatness of `R → T` comes from identifying the completions of the chart ring and of the local
ring, and the descent from the faithful flatness of completion (`I 𝒪̂ ∩ 𝒪 = I`). Hironaka's
definition of the strict transform of a sheaf of ideals is [Hir64, Ch. 0, §2, pp. 129–130].
-/

@[expose] public section

universe u

namespace Algebra

variable {R : Type*} {S : Type u} {T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- **A flat descent datum for `χ : R → S`**: a ring `T` with a map `ι : S → T` along which every
ideal of `S` descends (`ι⁻¹(J T) = J`) and such that `ι ∘ χ : R → T` is flat. For `χ` the map
from a polynomial chart ring of a blow-up to the local ring `𝒪_{M',a'}` of the blown-up manifold,
the datum is the completion `T = 𝒪̂_{M',a'}`. -/
def HasFlatDescentDatum (χ : R →+* S) : Prop :=
  ∃ (T : Type u) (_ : CommRing T) (ι : S →+* T),
    (ι.comp χ).Flat ∧ ∀ J : Ideal S, (J.map ι).comap ι = J

/-- The saturation `⋃_k (I : e^k)` is carried by `χ` onto the saturation of `I S` by `χ(e)`, given
a map `ι : S → T` with `ι ∘ χ` flat along which ideals of `S` descend. The transport step of
[BM97, Proposition 3.13]; not stated there in this form. -/
theorem iSup_colon_pow_map_eq_map_iSup_colon_pow (χ : R →+* S) (ι : S →+* T)
    (hflat : (ι.comp χ).Flat) (hdesc : ∀ J : Ideal S, (J.map ι).comap ι = J) (I : Ideal R)
    (e : R) :
    (⨆ k : ℕ, (I.map χ).colon {χ e ^ k}) = (⨆ k : ℕ, I.colon {e ^ k}).map χ := by
  rw [Ideal.map_iSup]
  refine le_antisymm (iSup_le fun k g hg => ?_) (iSup_mono fun k => ?_)
  · have hg' : g * χ e ^ k ∈ I.map χ := by
      simpa only [smul_eq_mul] using Submodule.mem_colon_singleton.mp hg
    have key : (I.colon {e ^ k}).map (ι.comp χ) =
        (I.map (ι.comp χ)).colon {(ι.comp χ) (e ^ k)} :=
      @AlgebraicGeometry.map_colon_singleton_of_flat R T _ _ (ι.comp χ).toAlgebra hflat I (e ^ k)
    refine Submodule.mem_iSup_of_mem k ?_
    rw [← hdesc ((I.colon {e ^ k}).map χ), Ideal.mem_comap, Ideal.map_map, key,
      Submodule.mem_colon_singleton, smul_eq_mul, RingHom.comp_apply, map_pow, ← map_mul,
      ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hg'
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have ha' : a * e ^ k ∈ I := by
      simpa only [smul_eq_mul] using Submodule.mem_colon_singleton.mp ha
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_pow, ← map_mul]
    exact Ideal.mem_map_of_mem _ ha'

/-- The transport lemma with the datum as a hypothesis. -/
theorem HasFlatDescentDatum.iSup_colon_pow_map_eq {χ : R →+* S} (hχ : HasFlatDescentDatum χ)
    (I : Ideal R) (e : R) :
    (⨆ k : ℕ, (I.map χ).colon {χ e ^ k}) = (⨆ k : ℕ, I.colon {e ^ k}).map χ := by
  obtain ⟨T, _, ι, hflat, hdesc⟩ := hχ
  exact iSup_colon_pow_map_eq_map_iSup_colon_pow χ ι hflat hdesc I e

end Algebra
