import LinearGaps

namespace JSP727

open Finset Filter

/-- The positive set A contains no sum of distinct smaller members that is
itself in A. A finite set represents each summand at most once. -/
def IsSubsetSumFree (A : Set ℕ) : Prop :=
  ∀ x ∈ A, 0 < x ∧ ∀ s : Finset ℕ, (∀ y ∈ s, y ∈ A ∧ y < x) →
    ∑ y ∈ s, y ≠ x

/-- For n ≥ 1 this is the gap between the nth and (n+1)st terms, using
one-based indices in the mathematical problem and zero-based Nat.nth in Lean. -/
noncomputable def gap (A : Set ℕ) (n : ℕ) : ℕ :=
  Nat.nth (· ∈ A) n - Nat.nth (· ∈ A) (n-1)

theorem arbitrarily_large_linear_ratio {a : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (hf : SubsetSumFree a) (K N : ℕ) :
    ∃ i ≥ N, K*(i+1) < a (i+1)-a i := by
  by_contra! h
  let M := (range N).sup (fun i => a (i+1)-a i)
  let L := max (K+1) M
  have hK : K+1 ≤ L := le_max_left _ _
  apply no_linear_gaps ha hpos hf L (by omega)
  intro i
  by_cases hi : N ≤ i
  · exact (h i hi).trans (Nat.mul_le_mul_right _ (by omega))
  · have hM : a (i+1)-a i ≤ M := le_sup (f := fun j => a (j+1)-a j) (mem_range.mpr (by omega))
    exact hM.trans ((le_max_right _ _).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))

/-- Every linear multiple of n is exceeded by gaps at arbitrarily large
indices. This answers the explicit inequality in Erdős problem 876. -/
theorem erdos876_linear {A : Set ℕ} (hinf : A.Infinite) (hfree : IsSubsetSumFree A)
    (K N : ℕ) : ∃ n ≥ N, 0 < n ∧ K*n < gap A n := by
  let a := Nat.nth (· ∈ A)
  have hm : StrictMono a := Nat.nth_strictMono hinf
  have hmem (i : ℕ) : a i ∈ A := Nat.nth_mem_of_infinite hinf i
  have hf : SubsetSumFree a := by
    intro i s hlt hs
    apply (hfree (a i) (hmem i)).2 (s.image a) ?_ ?_
    · intro j hj
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
      exact ⟨hmem _,hm (hlt _ hk)⟩
    · simpa [sum_image hm.injective.injOn] using hs
  obtain ⟨i,hi,hg⟩ := arbitrarily_large_linear_ratio hm (fun i => (hfree _ (hmem i)).1)
    hf K N
  exact ⟨i+1, by omega, by omega, by simpa [gap,a] using hg⟩

theorem erdos876_eventual_question :
    ¬ ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧ ∀ᶠ n : ℕ in atTop, gap A n < n := by
  rintro ⟨A,hinf,hfree,hev⟩
  obtain ⟨N,hN⟩ := eventually_atTop.1 hev
  obtain ⟨n,hn,_,hg⟩ := erdos876_linear hinf hfree 1 N
  have := hN n hn
  omega

end JSP727
