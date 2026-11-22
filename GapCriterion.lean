import GeneralGaps
import LogGaps

namespace JSP727

open Filter Finset

/-- Existence with the indicated eventual bound on consecutive gaps. -/
def HasGapBound (F : ℕ → ℕ) : Prop :=
  ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧ SubsetSumFree a ∧
    ∃ C : ℕ, ∀ᶠ i : ℕ in atTop, a (i+1)-a i ≤ C*(i+1)*F (i+1)

private theorem controlled_of_eventual {F a : ℕ → ℕ} (hm : Monotone F) (hp : ∀ i, 1 ≤ F i)
    {C : ℕ} (hc : ∀ᶠ i : ℕ in atTop, a (i+1)-a i ≤ C*(i+1)*F (i+1)) : ControlledGaps F a := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 hc
  let M := (range N).sup (fun i => a (i+1)-a i)
  let K := C+M+1
  have hK : 0 < K := by dsimp [K]; omega
  refine ⟨K,hK,?_⟩
  intro i
  by_cases hi : N ≤ i
  · apply (hN i hi).trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (show C ≤ K by dsimp [K]; omega))
      (hm (Nat.le_mul_of_pos_left _ hK))
  · have hM : a (i+1)-a i ≤ M := le_sup (f := fun i => a (i+1)-a i) (mem_range.mpr (by omega))
    exact hM.trans ((show M ≤ K by dsimp [K]; omega).trans
      ((Nat.le_mul_of_pos_right K (Nat.succ_pos i)).trans (Nat.le_mul_of_pos_right _ (hp _))))

/-- Cauchy condensation exchanges the original reciprocal series for the
dyadic sum of the reciprocal of the factor alone. -/
theorem summable_gap_budget_iff {F : ℕ → ℕ} (hm : Monotone F) (hp : ∀ i, 1 ≤ F i) :
    Summable (fun n : ℕ => 1/(((max 1 n : ℕ) : ℝ)*F n)) ↔
      Summable (fun j : ℕ => 1/(F (2^j) : ℝ)) := by
  let g := fun n : ℕ => (max 1 n)*F n
  have hgp (n) : 1 ≤ g n := Nat.mul_pos (le_max_left 1 n) (hp n)
  have hgm : Monotone g := fun _ _ h => Nat.mul_le_mul (max_le_max_left _ h) (hm h)
  have hc := summable_condensed_iff_of_nonneg (f := fun n : ℕ => 1/(g n : ℝ))
    (fun n => by positivity) (fun _ _ _ h => one_div_le_one_div_of_le
      (by exact_mod_cast hgp _) (by exact_mod_cast hgm h))
  have heq (j : ℕ) : (2 : ℝ)^j*(1/(g (2^j) : ℝ)) = 1/(F (2^j) : ℝ) := by
    dsimp [g]
    rw [max_eq_right Nat.one_le_two_pow]
    push_cast
    field_simp
  rw [show (fun j : ℕ => (2 : ℝ)^j*(1/(g (2^j) : ℝ))) =
    (fun j : ℕ => 1/(F (2^j) : ℝ)) from funext heq] at hc
  simpa only [g,Nat.cast_mul] using hc.symm

/-- Exact discrete criterion. The power hypothesis includes every positive
nondecreasing slowly varying factor. -/
theorem discrete_gap_criterion {F : ℕ → ℕ} (hm : Monotone F) (hp : ∀ i, 1 ≤ F i)
    {S : ℕ} (hslow : ∀ i, (F i)^16 ≤ S*(i+1)) :
    HasGapBound F ↔ Summable (fun n : ℕ => 1/(((max 1 n : ℕ) : ℝ)*F n)) := by
  constructor
  · rintro ⟨a,ha,hap,hf,C,hC⟩
    apply (summable_gap_budget_iff hm hp).mpr
    by_contra hdiv
    exact no_controlled_gaps ha hap hf hm hp hslow hdiv (controlled_of_eventual hm hp hC)
  · intro hs
    let g := fun n : ℕ => max 1 n * F n
    have hgp (n) : 0 < g n := Nat.mul_pos (le_max_left 1 n) (hp n)
    have hgm : Monotone g := fun _ _ h => Nat.mul_le_mul (max_le_max_left _ h) (hm h)
    obtain ⟨a,ha,hap,hf,⟨C,hC⟩,_⟩ := exists_of_summable_reciprocal hgp hgm
      (by simpa only [g,Nat.cast_mul] using hs)
    refine ⟨a,ha,hap,hf,C,Eventually.of_forall (fun i => ?_)⟩
    simpa [g,Nat.mul_assoc] using hC i

end JSP727
