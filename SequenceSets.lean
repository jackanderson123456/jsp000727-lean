import Normalization
import Research.Negative
import Research.InfiniteCoinCover

namespace JSP727

open Filter Finset
open Erdos254 Erdos254.InfiniteCoinCover

theorem sequence_phase_divergence_of_not_summable {a : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) {θ : ℝ} (hs : ¬ Summable (fun i => phase (a i*θ))) :
    Tendsto (phasePartialSum (Set.range a) θ) atTop atTop := by
  classical
  let w := fun j : ℕ => nearestIntegerDistance (θ*j)
  have heq (i : ℕ) : w (a i) = phase (a i*θ) := by
    simp only [w, phase, nearestIntegerDistance, abs_sub_round_eq_min, mul_comm]
  have hsum := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun i => show 0 ≤ phase (a i*θ) from abs_nonneg _)).mp
    hs
  apply (phasePartialSum_tendsto_iff_unbounded _ _).2
  intro M
  obtain ⟨n,hn⟩ := (tendsto_atTop.1 hsum M).exists
  refine ⟨a n, hn.trans ?_⟩
  change (∑ i ∈ range n, phase (a i*θ)) ≤
    ∑ j ∈ (Icc 1 (a n)).filter (fun j => j ∈ Set.range a), w j
  simp_rw [← heq]
  rw [← sum_image ha.injective.injOn]
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpos _,(ha (mem_range.mp hi)).le⟩, ⟨i,rfl⟩⟩
  · intro j _ _
    exact nearestIntegerDistance_nonneg _

theorem sequence_phase_divergence {a : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) {K : ℕ} (hK : 0 < K) (hg : ∀ i, a (i+1)-a i ≤ K*(i+1))
    {θ : ℝ} (hθ : Irrational θ) : Tendsto (phasePartialSum (Set.range a) θ) atTop atTop :=
  sequence_phase_divergence_of_not_summable ha hpos (not_summable_phase_of_linear_gaps ha hK hg hθ)

theorem covers_range {a : ℕ → ℕ} (ha : StrictMono a) {q : ℕ} (hc : Covers a q) (z : ℤ) :
    ∃ s : Finset ℕ, (∀ n ∈ s, n ∈ Set.range a) ∧ (q : ℤ) ∣ z-(∑ n ∈ s, n : ℕ) := by
  obtain ⟨t,ht⟩ := hc z
  refine ⟨t.image a,?_,?_⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact ⟨i,rfl⟩
  · simpa [sum_image ha.injective.injOn] using ht

def SyndeticSums (A : Set ℕ) : Prop :=
  ∃ K : ℕ, ∀ n : ℕ, ∃ t : Finset ℕ, (∀ b ∈ t, b ∈ A) ∧
    (∑ b ∈ t, b) ≤ n ∧ n ≤ (∑ b ∈ t, b)+K

theorem syndetic_of_prefix_growth {a : ℕ → ℕ} (ha : StrictMono a) (hpos : ∀ i, 0 < a i)
    {H : ℕ} (hg : ∀ n, a n ≤ (∑ i ∈ range n, a i)+H) : SyndeticSums (Set.range a) := by
  classical
  refine ⟨H,infinite_prefix_growth_gives_syndetic_subsetSums _ H
    (Set.infinite_range_of_injective ha.injective) ?_⟩
  rintro _ ⟨n,rfl⟩ _
  have hsub : (range n).image a ⊆ smallerCoins (Set.range a) (a n) := by
    intro b hb
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hpos _,ha (mem_range.mp hj)⟩,⟨j,rfl⟩⟩
  have hlo := Finset.sum_le_sum_of_subset (f := id) hsub
  rw [sum_image ha.injective.injOn] at hlo
  change ∑ i ∈ range n, a i ≤ ∑ x ∈ smallerCoins (Set.range a) (a n), x at hlo
  have := hg n
  omega

theorem syndetic_of_linear_gaps {a : ℕ → ℕ} (ha : StrictMono a) (hpos : ∀ i, 0 < a i)
    {K : ℕ} (hg : ∀ i, a (i+1)-a i ≤ K*(i+1)) : SyndeticSums (Set.range a) := by
  let H := a 0 + K*(K+1)
  apply syndetic_of_prefix_growth ha hpos (H := H)
  intro n
  cases n with
  | zero => simp [H]
  | succ n =>
    have hb : (n-K)*K ≤ ∑ i ∈ range n, a i := by
      calc
        _ = ∑ _i ∈ Ico K n, K := by simp [Nat.card_Ico]
        _ ≤ ∑ i ∈ Ico K n, a i := sum_le_sum (fun i hi => (mem_Ico.mp hi).1.trans (ha.id_le i))
        _ ≤ _ := sum_le_sum_of_subset (by intro i hi; exact mem_range.mpr (mem_Ico.mp hi).2)
    have hn : K*(n+1) ≤ (n-K)*K + K*(K+1) := by
      rcases le_total K n with h | h
      · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le h
        simp
        nlinarith
      · exact (Nat.mul_le_mul_left K (Nat.succ_le_succ h)).trans (Nat.le_add_left _ _)
    have := hg n
    rw [sum_range_succ]
    dsimp [H]
    omega

end JSP727
