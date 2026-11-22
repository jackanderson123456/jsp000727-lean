import SubsetSumFree

namespace JSP727

open Finset

/-- Extend a finite prefix by multiples of the prescribed modulus.
Each new term exceeds the sum of all its predecessors. -/
private theorem extend_by_multiples {a : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (hf : SubsetSumFree a) (N d : ℕ) (hd : 0 < d) :
    ∃ b : ℕ → ℕ, StrictMono b ∧ (∀ i, 0 < b i) ∧ SubsetSumFree b ∧
      (∀ i < N, b i = a i) ∧ ∀ i ≥ N, d ∣ b i := by
  let B := d * ((∑ i ∈ range N, a i) + 1)
  let b := fun i => if i < N then a i else B * 2^(i-N)
  have heq (i) (hi : i < N) : b i = a i := if_pos hi
  have htail (k) : b (N+k) = B * 2^k := by simp [b]
  have hdouble (k) : b (N+k+1) = b (N+k) * 2 := by
    rw [show N+k+1 = N+(k+1) by omega, htail, htail, pow_succ]
    exact (Nat.mul_assoc _ _ _).symm
  have hmajor (k) : ∑ i ∈ range (N+k), b i < b (N+k) := by
    induction k with
    | zero =>
      simp only [Nat.add_zero]
      have hb : b N = B := by simpa using htail 0
      rw [hb, sum_congr rfl (fun i hi => heq i (mem_range.mp hi))]
      exact (Nat.lt_succ_self _).trans_le (Nat.le_mul_of_pos_left _ hd)
    | succ k ih =>
      rw [← Nat.add_assoc, sum_range_succ, hdouble]
      omega
  have hlarge (i) (hi : N ≤ i) : ∑ j ∈ range i, b j < b i := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hi
    exact hmajor k
  refine ⟨b,strictMono_nat_of_lt_succ ?_,?_,?_,heq,?_⟩
  · intro i
    by_cases h : i+1 < N
    · rw [heq _ (by omega), heq _ h]
      exact ha (Nat.lt_succ_self _)
    · exact (single_le_sum (f := b) (fun j _ => Nat.zero_le (b j))
        (mem_range.mpr (Nat.lt_succ_self i))).trans_lt (hlarge _ (by omega))
  · intro i
    by_cases h : i < N
    · simpa [heq i h] using hpos i
    · exact (Nat.zero_le _).trans_lt (hlarge i (by omega))
  · intro i s hs hsum
    by_cases h : i < N
    · apply hf i s hs
      simpa only [heq i h, sum_congr rfl (fun j hj => heq j ((hs j hj).trans h))] using hsum
    · have hsub : s ⊆ range i := fun j hj => mem_range.mpr (hs j hj)
      have := (sum_le_sum_of_subset (f := b) hsub).trans_lt (hlarge i (by omega))
      omega
  · intro i hi
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [htail]
    exact dvd_mul_of_dvd_left (dvd_mul_right d _) _

/-- A modulus with at most d exceptions in a single sufficiently long
prefix already obeys the quantitative bound. -/
theorem finite_exceptional_divisor_bound {a : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (hf : SubsetSumFree a) {N C d : ℕ}
    (hd : 0 < d) (hwidth : (4*C+3)*d ≤ N)
    (hg : ∀ i < N, a i ≤ C*(i+1)^2)
    (hcount : Nat.count (fun i => ¬ d ∣ a i) N ≤ d) :
    d ≤ C*(4*C+3)^2 := by
  obtain ⟨b,hm,hp,hbf,heq,hdvd⟩ := extend_by_multiples ha hpos hf N d hd
  refine exceptional_divisor_bound_of_local_growth hm hp hbf ?_ hd ?_
  · intro i hi
    have h := hi.trans_le hwidth
    rw [heq i h]
    exact hg i h
  · have hpre (n : ℕ) (hn : n ≤ N) :
        Nat.count (fun i => ¬ d ∣ b i) n = Nat.count (fun i => ¬ d ∣ a i) n := by
      induction n with
      | zero => rfl
      | succ n ih => simp [Nat.count_succ, heq n (by omega), ih (by omega)]
    have htail (k : ℕ) : Nat.count (fun i => ¬ d ∣ b i) (N+k) ≤ d := by
      induction k with
      | zero => simpa [hpre N le_rfl] using hcount
      | succ k ih => simpa [← Nat.add_assoc, Nat.count_succ, hdvd (N+k) (by omega)] using ih
    intro n
    rcases le_total n N with h | h
    · rw [hpre n h]
      exact (Nat.count_monotone _ h).trans hcount
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
      exact htail k

/-- When the sixteenth power of the quadratic envelope grows at most
linearly, the finite translates test applies with N = d² for every large d. -/
theorem large_modulus_window {g : ℕ → ℕ} {S : ℕ} (hp : ∀ n, 1 ≤ g n)
    (hs : ∀ n, (g n)^16 ≤ S*(n+1)) :
    ∃ D, ∀ d ≥ D, 0 < d ∧ (4*g (d^2)+3)*d ≤ d^2 ∧
      g (d^2)*(4*g (d^2)+3)^2 < d := by
  let W := 100*(S+1)
  refine ⟨49*W^3+1,?_⟩
  intro d hd
  let H := g (d^2)
  have hH : 1 ≤ H := hp _
  have hpos : 0 < d := by omega
  have hcube : 49*H^3 < d := by
    by_cases hsmall : H ≤ W
    · have := Nat.mul_le_mul_left 49 (Nat.pow_le_pow_left hsmall 3)
      omega
    · have hsq : H^8 ≤ (2*(S+1))*d := by
        apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
        calc
          (H^8)^2 = H^16 := by ring
          _ ≤ S*(d^2+1) := hs _
          _ ≤ S*(2*d^2) := by gcongr; nlinarith [Nat.one_le_pow 2 d hpos]
          _ ≤ ((2*(S+1))*d)^2 := by
            nlinarith [Nat.zero_le (S^2*d^2), Nat.zero_le (S*d^2)]
      have hpow : H ≤ H^5 := by
        calc
          H = H*1 := by ring
          _ ≤ H*H^4 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hH)
          _ = _ := by ring
      have hW : 98*(S+1) < H^5 := by dsimp [W] at hsmall; omega
      have hlt := Nat.mul_lt_mul_of_pos_right hW (by positivity : 0 < H^3)
      have hcancel : (2*(S+1))*(49*H^3) < (2*(S+1))*d := by
        calc
          _ = (98*(S+1))*H^3 := by ring
          _ < H^5*H^3 := hlt
          _ = H^8 := by ring
          _ ≤ _ := hsq
      exact Nat.lt_of_mul_lt_mul_left hcancel
  have hlin : 4*H+3 ≤ 7*H := by omega
  have hb : H*(4*H+3)^2 ≤ 49*H^3 := by
    calc
      _ ≤ H*(7*H)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlin 2)
      _ = _ := by ring
  have hwidth : 4*H+3 ≤ H*(4*H+3)^2 := by
    have h₁ := Nat.le_mul_of_pos_right (4*H+3) (by omega : 0 < 4*H+3)
    have h₂ := Nat.le_mul_of_pos_left ((4*H+3)^2) hH
    rw [sq] at h₂
    simpa only [sq] using h₁.trans h₂
  refine ⟨hpos,?_,hb.trans_lt hcube⟩
  simpa only [H, sq] using Nat.mul_le_mul_right d ((hwidth.trans hb).trans hcube.le)

/-- Sequences with the stated growth envelope have at least d+1
exceptions to divisibility by d before index d², for all sufficiently large d. -/
theorem many_nonmultiples {a g : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (hf : SubsetSumFree a) (hm : Monotone g)
    (hp : ∀ i, 1 ≤ g i) {S : ℕ} (hs : ∀ i, (g i)^16 ≤ S*(i+1))
    (hg : ∀ i, a i ≤ g (i+1)*(i+1)^2) :
    ∃ D, ∀ d ≥ D, d < Nat.count (fun i => ¬ d ∣ a i) (d^2) := by
  obtain ⟨D,hD⟩ := large_modulus_window hp hs
  refine ⟨D,?_⟩
  intro d hd
  obtain ⟨hposd,hwidth,hstrict⟩ := hD d hd
  by_contra! h
  apply (not_le_of_gt hstrict)
  apply finite_exceptional_divisor_bound ha hpos hf hposd hwidth _ h
  intro i hi
  exact (hg i).trans (Nat.mul_le_mul_right _ (hm hi))

end JSP727
