/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.StructureSheaf
import Hironaka.Algebra.Local.Taylor
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.Germ.TaylorIdeal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Stalk homomorphisms agreeing modulo an ideal on the coordinates agree on all germs

Kollár's proof of the uniqueness of blow-up sequences checks the agreement of the two lifts
`f', g'` on `V(M_{i+1})` on the pulled-back coordinates `y_j` of a chart of the blow-up
[Kol07, Theorem 97, proof]. This module is the passage from the coordinates to every germ, for two
local ring homomorphisms `F, G : 𝒪_{M,a} → 𝒪_{N,b}` preserving the constants (the two pull-backs
`f'^*`, `g'^*`) and an ideal `K ⊆ 𝒪_{N,b}`: if `F x_i − G x_i ∈ K` for the coordinate germs `x_i`
of a chart at `a`, then `F s − G s ∈ K` for every germ `s` (`sub_mem_of_forall_coord_sub_mem`).

The proof is Hadamard's lemma iterated against Krull's intersection theorem: writing
`s = s(a) + ∑ (x_i − x_i(a)) g_i` (`exists_eq_sum_coord_mul'`),
`F s − G s = ∑ (F x_i − G x_i) F g_i + ∑ G(x_i − x_i(a)) (F g_i − G g_i)`; the first sum lies in
`K`, the second in `𝔪_b · (K + 𝔪_b^N)` once `F g_i − G g_i ∈ K + 𝔪_b^N` (induction on `N`), so
`F s − G s ∈ K + 𝔪_b^{N+1}` for every `N`, and `⋂_N (K + 𝔪_b^N) = K` in the Noetherian local ring
`𝒪_{N,b}` (`isNoetherianRing_stalk`; Krull's intersection theorem [Kol07, Definition 55] in the
form `IsLocalRing.mem_of_forall_mem_sup_pow`).
-/

public section

noncomputable section

open TopologicalSpace IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))
  (φ : OpenPartialHomeomorph M E) {a : M} (ha : a ∈ φ.source) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)
  {N : Type u} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(𝕜, E) ω N]
  [FiniteDimensional 𝕜 E] {b : N}

/-- Two ring homomorphisms of stalks `F, G : 𝒪_{M,a} → 𝒪_{N,b}` preserving the constants, `G`
local, which agree modulo an ideal `K` on the coordinate germs of a chart at `a`, agree modulo `K`
on every germ (the passage from the coordinates to all germs in [Kol07, Theorem 97, proof]):
Hadamard's lemma iterated against Krull's intersection theorem in the Noetherian local ring
`𝒪_{N,b}`. -/
theorem sub_mem_of_forall_coord_sub_mem
    (F G : (structureSheaf 𝕜 E M).presheaf.stalk a →+* (structureSheaf 𝕜 E N).presheaf.stalk b)
    [IsLocalHom G] (hF : ∀ c : 𝕜, F (const 𝕜 E M a c) = const 𝕜 E N b c)
    (hG : ∀ c : 𝕜, G (const 𝕜 E M a c) = const 𝕜 E N b c)
    (K : Ideal ((structureSheaf 𝕜 E N).presheaf.stalk b))
    (hK : ∀ i, F (coord E ψ φ hφ ha i) - G (coord E ψ φ hφ ha i) ∈ K)
    (s : (structureSheaf 𝕜 E M).presheaf.stalk a) : F s - G s ∈ K := by
  refine mem_of_forall_mem_sup_pow fun m => ?_
  induction m generalizing s with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
    exact Submodule.mem_top
  | succ m ih =>
    obtain ⟨g, hg⟩ := exists_eq_sum_coord_mul' E ψ φ ha hφ (s - const 𝕜 E M a (eval 𝕜 E M a s))
      (by rw [map_sub, eval_const, sub_self])
    have hs : s = const 𝕜 E M a (eval 𝕜 E M a s) + ∑ i,
        (coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i))) * g i := by
      rw [← hg]
      ring
    rw [hs, map_add, map_add, hF, hG, add_sub_add_left_eq_sub, map_sum, map_sum,
      ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun i _ => ?_
    have e : F ((coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i))) * g i) -
        G ((coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i))) * g i) =
          (F (coord E ψ φ hφ ha i) - G (coord E ψ φ hφ ha i)) * F (g i) +
            G (coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i))) *
              (F (g i) - G (g i)) := by
      rw [map_mul, map_mul, map_sub, map_sub, hF, hG]
      ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (hK i))) ?_
    have hm : G (coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i))) ∈
        maximalIdeal ((structureSheaf 𝕜 E N).presheaf.stalk b) :=
      map_nonunit G _ ((mem_maximalIdeal_iff_eval E _).mpr (by rw [map_sub, eval_const, sub_self]))
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (ih (g i))
    rw [← hyz, mul_add]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hy)) (Ideal.mem_sup_right ?_)
    rw [pow_succ']
    exact Ideal.mul_mem_mul hm hz

end Hironaka.Manifold

end
