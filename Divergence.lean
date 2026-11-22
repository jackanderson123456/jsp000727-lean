import Scales
import Mathlib.Analysis.PSeries

namespace JSP727

open Filter Finset

private theorem summable_disjoint_intervals {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) {lo hi : ℕ → ℕ} (hl : ∀ k, lo k ≤ hi k)
    (hu : ∀ k, hi k ≤ lo (k+1)) : Summable (fun k => ∑ i ∈ Ico (lo k) (hi k), w i) := by
  apply summable_of_sum_range_le (fun k => sum_nonneg (fun i _ => hw i)) (c := ∑' i, w i)
  intro n
  have hpart (m) : (∑ k ∈ range m, ∑ i ∈ Ico (lo k) (hi k), w i) ≤ ∑ i ∈ range (lo m), w i := by
    induction m with
    | zero => simpa using sum_nonneg (s := range (lo 0)) (fun i _ => hw i)
    | succ m ih =>
      rw [sum_range_succ, ← sum_range_add_sum_Ico w ((hl m).trans (hu m))]
      apply add_le_add ih
      exact sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico le_rfl (hu m)) (fun i _ _ => hw i)
  exact (hpart n).trans (hs.sum_le_tsum _ (fun i _ => hw i))

/-- Condense the dyadic index itself along the progression 72·16^k. -/
private theorem summable_from_geometric_samples {g : ℕ → ℕ} (hm : Monotone g)
    (hp : ∀ i, 1 ≤ g i)
    (hs : Summable (fun k : ℕ => ((16^k : ℕ) : ℝ)/(g (2^(72*16^k)) : ℝ))) :
    Summable (fun j : ℕ => 1/(g (2^j) : ℝ)) := by
  let u := fun k : ℕ => 72*16^k
  let f := fun j : ℕ => 1/(g (2^j) : ℝ)
  have hmono : Antitone f := by
    intro i j h
    exact one_div_le_one_div_of_le (by exact_mod_cast (hp _)) (by
      exact_mod_cast hm (Nat.pow_le_pow_right (by decide : 0 < 2) h))
  have hinc : StrictMono u := strictMono_nat_of_lt_succ (fun k => by
    dsimp [u]
    rw [pow_succ]
    have : 0 < (16 : ℕ)^k := by positivity
    omega)
  have hdiff : SuccDiffBounded 16 u := by
    intro k
    simp only [u, pow_succ, nsmul_eq_mul]
    omega
  apply (summable_schlomilch_iff_of_nonneg (f := f) (fun i => by dsimp [f]; positivity)
    (fun _ _ _ h => hmono h) (fun k => show 0 < u k by dsimp [u]; positivity) hinc
    (by decide : 16 ≠ 0) hdiff).mp
  apply (hs.mul_left (1080 : ℝ)).congr
  intro k
  dsimp [u,f]
  rw [pow_succ]
  push_cast
  ring

/-- Under the subpower envelope, summability at an irrational phase would
force convergence of the dyadic reciprocal series. -/
theorem phase_divergence_of_envelope {a g : ℕ → ℕ} (ha : StrictMono a)
    (hap : ∀ i, 0 < a i) (hf : SubsetSumFree a) (hm : Monotone g)
    (hp : ∀ i, 1 ≤ g i) {S : ℕ} (hslow : ∀ i, (g i)^16 ≤ S*(i+1))
    (hgap : ∀ i, a (i+1)-a i ≤ (i+1)*g (i+1)) (hg : ∀ i, a i ≤ g (i+1)*(i+1)^2)
    (hdiv : ¬ Summable (fun j : ℕ => 1/(g (2^j) : ℝ))) {θ : ℝ} (hθ : Irrational θ) :
    ¬ Summable (fun i => phase (a i*θ)) := by
  intro hs
  obtain ⟨M,hM⟩ := denominator_window_of_growth ha hap hf hm hp hslow hg hθ hs
  let lo := fun k : ℕ => 2^(10*16^k)
  let hi := fun k : ℕ => 2^(72*16^k)
  let w := fun i => phase (a i*θ)
  let P := fun k => ∑ i ∈ Ico (lo k) (hi k), w i
  have hP : Summable P := summable_disjoint_intervals (lo := lo) (hi := hi) (w := w)
    (fun i => abs_nonneg _) hs
    (fun k => Nat.pow_le_pow_right (by decide) (by omega))
    (fun k => Nat.pow_le_pow_right (by decide) (by rw [pow_succ]; omega))
  apply hdiv
  apply summable_from_geometric_samples hm hp
  apply (hP.mul_left (2048 : ℝ)).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  refine Filter.eventually_atTop.2 ⟨16+S+M,?_⟩
  intro k hk
  have hkx : k ≤ 16^k := (Nat.le_of_lt Nat.lt_two_pow_self).trans
    (Nat.pow_le_pow_left (by decide) k)
  have hmass := geometric_band_mass ha hm hp hslow hgap hM
    (x := 16^k) (by omega) (by omega) (by omega)
  have hgR : 0 < (g (2^(72*16^k)) : ℝ) := by exact_mod_cast hp _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((16^k : ℕ):ℝ)/(g (2^(72*16^k)) : ℝ))]
  apply (div_le_iff₀ hgR).mpr
  change ((16^k : ℕ) : ℝ) ≤ 2048*P k*(g (2^(72*16^k)) : ℝ)
  simpa [P,hi,lo,w,mul_assoc,mul_comm,mul_left_comm] using hmass

end JSP727
