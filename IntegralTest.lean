import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

namespace JSP727

open MeasureTheory Filter Finset Set
open scoped Topology

/-- The integral test from 1 to infinity, with no continuity assumption. -/
theorem integral_test {f : ℝ → ℝ} (hf : AntitoneOn f (Ici 1))
    (hp : ∀ x ≥ 1, 0 ≤ f x) :
    IntegrableOn f (Ioi 1) ↔ Summable (fun i : ℕ => f (1+i)) := by
  have hmono (n : ℕ) : AntitoneOn f (Icc 1 (1+n)) := hf.mono (fun _ hx => hx.1)
  have hle (n : ℕ) : (1 : ℝ) ≤ 1+n := le_add_of_nonneg_right (Nat.cast_nonneg n)
  constructor
  · intro hfint
    apply (summable_nat_add_iff 1).mp
    apply summable_of_sum_range_le (fun i => hp _ (hle _)) (c := ∫ x in Ioi (1 : ℝ), f x)
    intro n
    have hpart := (hmono n).sum_le_integral
    rw [intervalIntegral.integral_of_le (hle n)] at hpart
    exact hpart.trans (setIntegral_mono_set hfint
      ((ae_restrict_mem measurableSet_Ioi).mono (fun x hx => hp x hx.le))
      (Ioc_subset_Ioi_self.eventuallyLE))
  · intro hs
    let b := fun n : ℕ => (1 : ℝ)+n
    have hb : Tendsto b atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (b := b)
      (∑' i : ℕ, f (1+i)) 1 _ hb
    · apply Eventually.of_forall
      intro n
      have hnorm : (∫ x in (1:ℝ)..b n, ‖f x‖) = ∫ x in (1:ℝ)..b n, f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (hle n)] at hx
        exact Real.norm_of_nonneg (hp x hx.1)
      rw [hnorm]
      exact (hmono n).integral_le_sum |>.trans (hs.sum_le_tsum _ (fun i _ => hp _ (hle i)))
    · intro n
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (hle n)).mp
      apply AntitoneOn.intervalIntegrable
      simpa only [b,Set.uIcc_of_le (hle n)] using hmono n

end JSP727
