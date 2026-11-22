import GapCriterion
import IntegralTest
import SlowFactor

namespace JSP727

open Filter MeasureTheory Set
open scoped Topology

/-- The admissible upper bound on all sufficiently late consecutive gaps. -/
def HasRealGapBound (F : ℝ → ℝ) : Prop :=
  ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧ SubsetSumFree a ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i : ℕ in atTop,
      ((a (i+1)-a i : ℕ) : ℝ) ≤ C*((i : ℝ)+1)*F ((i : ℝ)+1)

private theorem integral_gap_samples {F : ℝ → ℝ} (hm : MonotoneOn F (Ici 1))
    (hp : ∀ x ≥ 1, 1 ≤ F x) :
    IntegrableOn (fun x => 1/(x*F x)) (Ioi 1) ↔
      Summable (fun i : ℕ => 1/(((i : ℝ)+1)*F ((i : ℝ)+1))) := by
  have hanti : AntitoneOn (fun x => 1/(x*F x)) (Ici 1) := by
    intro x hx y hy hxy
    exact one_div_le_one_div_of_le (mul_pos (zero_lt_one.trans_le hx)
      (zero_lt_one.trans_le (hp x hx))) (mul_le_mul hxy (hm hx hy hxy)
      (zero_le_one.trans (hp x hx)) (zero_le_one.trans hy))
  simpa only [add_comm (1 : ℝ)] using integral_test hanti (fun x hx =>
    one_div_nonneg.mpr (mul_nonneg (zero_le_one.trans hx) (zero_le_one.trans (hp _ hx))))

private theorem integral_of_ceiling_series {F : ℝ → ℝ} (hm : MonotoneOn F (Ici 1))
    (hp : ∀ x ≥ 1, 1 ≤ F x)
    (hs : Summable (fun n : ℕ => 1/(((max 1 n : ℕ) : ℝ)*ceilingFactor F n))) :
    IntegrableOn (fun x => 1/(x*F x)) (Ioi 1) := by
  apply (integral_gap_samples hm hp).mpr
  have hs' := (summable_nat_add_iff 1).mpr (hs.mul_left (2 : ℝ))
  apply Summable.of_nonneg_of_le _ _ hs'
  · intro i
    have hf := hp ((i : ℝ)+1) (by linarith [Nat.cast_nonneg (α := ℝ) i])
    positivity
  · intro i
    have hn : (1 : ℝ) ≤ (i : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
    have hF := hp _ hn
    have hG : 0 < (⌈F ((i : ℝ)+1)⌉₊ : ℝ) := by exact_mod_cast Nat.one_le_ceil_iff.mpr (zero_lt_one.trans_le hF)
    have hceil : (⌈F ((i : ℝ)+1)⌉₊ : ℝ) ≤ 2*F ((i : ℝ)+1) := by
      linarith [Nat.ceil_lt_add_one (zero_le_one.trans hF)]
    simp only [ceilingFactor, max_eq_right (Nat.le_add_left 1 i), Nat.cast_add, Nat.cast_one, max_eq_right hn]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hceil (zero_le_one.trans hn)
    linarith only [h,show ((i : ℝ)+1)*(2*F ((i : ℝ)+1)) = 2*(((i : ℝ)+1)*F ((i : ℝ)+1)) by ring]

private noncomputable def realBudget (F : ℝ → ℝ) (i : ℕ) : ℝ :=
  (max 1 (i : ℝ))*F (max 1 (i : ℝ))

private theorem budget_succ (F : ℝ → ℝ) (i : ℕ) :
    realBudget F (i+1) = ((i : ℝ)+1)*F ((i : ℝ)+1) := by
  simp only [realBudget,Nat.cast_add,Nat.cast_one,
    max_eq_right (show (1 : ℝ) ≤ (i : ℝ)+1 by linarith [Nat.cast_nonneg (α := ℝ) i])]

/-- The convergent side gives one sequence whose gaps are bounded above
and below by positive multiples of the prescribed scale. -/
theorem integral_gap_construction {F : ℝ → ℝ} (hm : MonotoneOn F (Ici 1))
    (hp : ∀ x ≥ 1, 1 ≤ F x) (hv : SlowlyVarying F)
    (hs : IntegrableOn (fun x => 1/(x*F x)) (Ioi 1)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧ SubsetSumFree a ∧
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ i : ℕ in atTop,
        (1/32 : ℝ)*((i : ℝ)+1)*F ((i : ℝ)+1) ≤ ((a (i+1)-a i : ℕ) : ℝ) ∧
        ((a (i+1)-a i : ℕ) : ℝ) ≤ C*((i : ℝ)+1)*F ((i : ℝ)+1) := by
  let g := realBudget F
  have gpos (i) : 1 ≤ g i := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (hp _ (le_max_left _ _))
  have gmono : Monotone g := by
    intro i j h
    have hn : max 1 (i : ℝ) ≤ max 1 (j : ℝ) := max_le_max_left _ (by exact_mod_cast h)
    exact mul_le_mul hn (hm (Set.mem_Ici.mpr (le_max_left _ _)) (Set.mem_Ici.mpr (le_max_left _ _)) hn)
      (zero_le_one.trans (hp _ (le_max_left _ _))) (zero_le_one.trans (le_max_left _ _))
  have gsum : Summable (fun i => 1/g i) := (summable_nat_add_iff 1).mp (by
    simpa only [g,budget_succ] using (integral_gap_samples hm hp).mp hs)
  obtain ⟨a,ha,hap,hf,⟨C,hC⟩,hl⟩ := exists_of_real_budget gpos gmono gsum
  refine ⟨a,ha,hap,hf,max 1 C,zero_lt_one.trans_le (le_max_left _ _),?_⟩
  have ht := (hv 2 (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)), eventually_ge_atTop 1]
    with i hi hi1
  change F (2*(i : ℝ))/F i < 2 at hi
  have hir : 1 ≤ (i : ℝ) := by exact_mod_cast hi1
  have hfi := hp _ hir
  have htw := (div_lt_iff₀ (zero_lt_one.trans_le hfi)).mp hi
  have hle : F ((i : ℝ)+1) ≤ 2*F i := (hm (show 1 ≤ (i : ℝ)+1 by linarith)
    (show 1 ≤ 2*(i : ℝ) by linarith) (by linarith)).trans htw.le
  have hmul := mul_le_mul (show (i : ℝ)+1 ≤ 2*i by linarith) hle
    (zero_le_one.trans (hp _ (by linarith))) (by positivity)
  have hlow := hl i
  simp only [g,realBudget,max_eq_right hir] at hlow
  constructor
  · nlinarith only [hmul,hlow]
  · have hub := (hC i).trans (mul_le_mul_of_nonneg_right (le_max_right 1 C) (zero_le_one.trans (gpos _)))
    simpa only [g,budget_succ,mul_assoc] using hub

/-- Korsky's integral criterion for the uniform gap question in Erdős 876.
The ceiling is internal: the statement is for real positive, nondecreasing,
slowly varying factors and the actual improper-integral integrability condition. -/
theorem erdos876_integral_criterion {F : ℝ → ℝ} (hm : MonotoneOn F (Ici 1))
    (hp : ∀ x ≥ 1, 1 ≤ F x) (hv : SlowlyVarying F) :
    HasRealGapBound F ↔ IntegrableOn (fun x => 1/(x*F x)) (Ioi 1) := by
  constructor
  · rintro ⟨a,ha,hap,hf,C,hC,he⟩
    obtain ⟨S,hS⟩ := ceilingFactor_growth hm hp hv
    apply integral_of_ceiling_series hm hp
    apply (discrete_gap_criterion (ceilingFactor_mono hm) (ceilingFactor_pos hp) hS).mp
    refine ⟨a,ha,hap,hf,⌈C⌉₊,?_⟩
    filter_upwards [he] with i hi
    have hn : 1 ≤ (i : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
    have hF := hp _ hn
    have hG : F ((i : ℝ)+1) ≤ (ceilingFactor F (i+1) : ℝ) := by
      simpa only [ceilingFactor,Nat.cast_add,Nat.cast_one,max_eq_right hn] using Nat.le_ceil (F ((i : ℝ)+1))
    have hu := hi.trans (mul_le_mul (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (zero_le_one.trans hn))
      hG (zero_le_one.trans hF) (by positivity))
    exact_mod_cast hu
  · intro hs
    obtain ⟨a,ha,hap,hf,C,hC,he⟩ := integral_gap_construction hm hp hv hs
    exact ⟨a,ha,hap,hf,C,hC,he.mono (fun _ h => h.2)⟩

end JSP727
