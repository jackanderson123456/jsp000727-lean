import Blocks
import Research.PiecewiseAssembly

namespace JSP727.OddBlocks

open Finset
open Erdos254.PiecewiseAssembly
variable {a : ℕ → ℕ} {d : ℕ} (B : OddBlocks a d)

/-- An even-indexed singleton or the odd indices chosen from a nonreserved bin. -/
def Source (x : ℕ) (s : Finset ℕ) : Prop :=
  (∃ j : ℕ, s = {2*j} ∧ d*x = a (2*j)) ∨
  ∃ k : ℕ, 0 < k ∧ s = B.support k ∧ x = B.value k

theorem source_sum {x s} (h : B.Source x s) : ∑ i ∈ s, a i = d*x := by
  rcases h with ⟨j,rfl,he⟩ | ⟨k,_,rfl,rfl⟩
  · simpa using he.symm
  · exact (B.value_eq k).symm

private theorem even_not_mem_bin (k j : ℕ) : 2*j ∉ B.support k := by
  intro hj
  obtain ⟨i,_,_,he⟩ := B.window k _ hj
  omega

theorem disjoint_reserve {x s} (h : B.Source x s) : Disjoint (B.support 0) s := by
  rcases h with ⟨j,rfl,_⟩ | ⟨k,hk,rfl,_⟩
  · simpa using B.even_not_mem_bin 0 j
  · exact B.support_disjoint (by omega)

theorem disjoint_sources {x y s t} (hd : 0 < d) (hx : B.Source x s)
    (hy : B.Source y t) (hne : x ≠ y) : Disjoint s t := by
  rcases hx with ⟨i,rfl,hi⟩ | ⟨i,_,rfl,rfl⟩ <;>
    rcases hy with ⟨j,rfl,hj⟩ | ⟨j,_,rfl,rfl⟩
  · rw [Finset.disjoint_singleton_left, mem_singleton]
    intro he
    exact hne ((Nat.mul_right_inj hd.ne').mp (hi.trans ((congrArg a he).trans hj.symm)))
  · simpa using B.even_not_mem_bin j i
  · simpa using B.even_not_mem_bin i j
  · exact B.support_disjoint (fun h => hne (congrArg B.value h))

theorem flatten_with_reserve {U : Set ℕ} (hd : 0 < d)
    (hU : ∀ x ∈ U, ∃ t, B.Source x t) {n : ℕ} (hr : Representable U n) :
    ∃ s : Finset ℕ, B.support 0 ⊆ s ∧ ∑ i ∈ s, a i = d*(B.value 0+n) := by
  classical
  obtain ⟨v,hv,rfl⟩ := hr
  have hchoose (x : ℕ) : ∃ t, x ∈ v → B.Source x t := by
    by_cases hx : x ∈ v
    · obtain ⟨t,ht⟩ := hU x (hv x hx)
      exact ⟨t,fun _ => ht⟩
    · exact ⟨∅,fun h => (hx h).elim⟩
  choose f hf using hchoose
  have hdis : Disjoint (B.support 0) (v.biUnion f) := by
    rw [Finset.disjoint_left]
    intro i hi hmem
    obtain ⟨x,hx,hix⟩ := mem_biUnion.mp hmem
    exact Finset.disjoint_left.mp (B.disjoint_reserve (hf x hx)) hi hix
  refine ⟨B.support 0 ∪ v.biUnion f, subset_union_left, ?_⟩
  rw [sum_union hdis, ← B.value_eq, Nat.mul_add, sum_biUnion, mul_sum]
  · congr 1
    exact sum_congr rfl (fun i hi => B.source_sum (hf i hi))
  · intro x hx y hy hxy
    exact B.disjoint_sources hd (hf x hx) (hf y hy) hxy

theorem no_even_collision (ha : StrictMono a) (hpos : ∀ i, 0 < a i)
    (hf : SubsetSumFree a) (k j : ℕ) : d*B.value k ≠ a (2*j) := by
  intro he
  have hsingle := unique_representation ha hpos hf ((B.value_eq k).symm.trans he)
  exact B.even_not_mem_bin k j (hsingle ▸ mem_singleton_self _)

theorem reserve_prevents_even_sum (ha : StrictMono a) (hpos : ∀ i, 0 < a i)
    (hf : SubsetSumFree a) (hd : 0 < d) {s : Finset ℕ} (hs : B.support 0 ⊆ s)
    (j : ℕ) : ∑ i ∈ s, a i ≠ a (2*j) := by
  intro he
  have heq := unique_representation ha hpos hf he
  obtain ⟨t,ht⟩ := Finset.card_pos.mp (show 0 < (B.support 0).card by rwa [B.card])
  exact B.even_not_mem_bin 0 j ((Finset.mem_singleton.mp (heq ▸ hs ht)) ▸ ht)

end JSP727.OddBlocks
