import Mathlib

namespace JSP727

/-- The rational members of the integer span of finitely many reals have a
common denominator. Project the ambient rational vector space onto the line
spanned by 1, then clear the denominators of the projected generators. -/
theorem common_denominator {ι : Type*} [Fintype ι] (α : ι → ℝ) :
    ∃ D : ℕ, 0 < D ∧ ∀ k : ι → ℤ, ∀ r : ℚ,
      ∑ i, (k i : ℝ)*α i = r → ∃ z : ℤ, (D : ℝ)*r = z := by
  classical
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1:ℝ) ≠ 0)
  have hfix (r : ℚ) : f (r : ℝ) = r := by
    simpa [Algebra.smul_def, hf] using f.map_smul r (1 : ℝ)
  let b := fun i => f (α i)
  let D := ∏ i, (b i).den
  have hpos : 0 < D := Finset.prod_pos (fun i _ => (b i).pos)
  have hclear (i : ι) : ∃ z : ℤ, (D : ℚ)*b i = z := by
    obtain ⟨m,hm⟩ := (Finset.dvd_prod_of_mem (fun j => (b j).den) (Finset.mem_univ i) :
      (b i).den ∣ D)
    refine ⟨(m:ℤ)*(b i).num, ?_⟩
    change D = (b i).den * m at hm
    rw [hm, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← Rat.mul_den_eq_num (b i)]
    ring
  choose z hz using hclear
  refine ⟨D,hpos,?_⟩
  intro k r hr
  have hp : ∑ i, (k i : ℚ)*b i = r := by
    have he := congrArg f hr
    rw [hfix, map_sum] at he
    convert he using 1
    apply Finset.sum_congr rfl
    intro i _
    simpa [b, zsmul_eq_mul] using (map_zsmul f (k i) (α i)).symm
  refine ⟨∑ i, k i*z i, ?_⟩
  suffices (D : ℚ)*r = (∑ i, k i*z i : ℤ) by exact_mod_cast this
  rw [← hp, Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.cast_mul, ← hz i]
  ring

end JSP727
