import Construction
import Mathlib.Analysis.PSeries

namespace JSP727

theorem exists_of_real_budget {g : ℕ → ℝ} (hg : ∀ i, 1 ≤ g i) (hm : Monotone g)
    (hs : Summable (fun i => 1/g i)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧ SubsetSumFree a ∧
      (∃ C : ℝ, ∀ i, (a (i+1)-a i : ℕ) ≤ C*g (i+1)) ∧
      ∀ i, g i ≤ 8*((a (i+1)-a i : ℕ) : ℝ) := by
  let G := fun i => ⌈g i⌉₊
  have hp (i) : 0 < G i := Nat.one_le_ceil_iff.mpr (lt_of_lt_of_le zero_lt_one (hg i))
  have hs' : Summable (fun i => 1/(G i : ℝ)) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
    intro i
    exact one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one (hg i)) (Nat.le_ceil _)
  obtain ⟨a,ha,hpos,hfree,⟨C,hC⟩,hl⟩ := exists_of_summable_reciprocal hp (Nat.ceil_mono.comp hm) hs'
  refine ⟨a,ha,hpos,hfree,⟨2*C,?_⟩,?_⟩
  · intro i
    have hceil : (G (i+1) : ℝ) ≤ 2*g (i+1) := by
      have := Nat.ceil_lt_add_one (by linarith [hg (i+1)] : 0 ≤ g (i+1))
      dsimp [G]
      linarith [hg (i+1)]
    calc
      _ ≤ (C:ℝ)*G (i+1) := by exact_mod_cast hC i
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg C : (0:ℝ) ≤ C)]
  · intro i
    exact (Nat.le_ceil (g i)).trans (by exact_mod_cast hl i)

/-- In particular any positive extra power of the logarithm suffices:
the gap to term n is at most a constant times n(1+log₂ n)^(1+ε). -/
theorem logarithmic_gap_construction (ε : ℝ) (hε : 0 < ε) :
    let g := fun n : ℕ => (max 1 n : ℕ) * ((Nat.log 2 n : ℝ)+1)^(1+ε)
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧ SubsetSumFree a ∧
      (∃ C : ℝ, ∀ i, (a (i+1)-a i : ℕ) ≤ C*g (i+1)) ∧
      ∀ i, g i ≤ 8*((a (i+1)-a i : ℕ) : ℝ) := by
  let g := fun n : ℕ => ((max 1 n : ℕ) : ℝ)*((Nat.log 2 n : ℝ)+1)^(1+ε)
  have hp : 0 ≤ 1+ε := by linarith
  have hg (n : ℕ) : 1 ≤ g n := by
    dsimp [g]
    apply one_le_mul_of_one_le_of_one_le
    · exact_mod_cast le_max_left 1 n
    · exact Real.one_le_rpow (by linarith [Nat.cast_nonneg (Nat.log 2 n) (α := ℝ)]) hp
  have hm : Monotone g := by
    intro n m h
    dsimp [g]
    gcongr
  apply exists_of_real_budget hg hm
  apply (summable_condensed_iff_of_nonneg (fun _ => by positivity) (fun _ _ _ h =>
    one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one (hg _)) (hm h))).mp
  have hs := (Real.summable_one_div_nat_add_rpow 1 (1+ε)).mpr (by linarith)
  apply hs.congr
  intro k
  dsimp [g]
  rw [Nat.log_pow (by decide : 1 < 2), max_eq_right k.one_le_two_pow,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ k+1)]
  push_cast
  field_simp

end JSP727
