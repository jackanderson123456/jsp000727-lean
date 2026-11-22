import Mathlib

namespace JSP727

open Filter
open scoped Topology

/-- Dyadic iteration turns an eventual doubling estimate at dilation 2^16
into a uniform sixteenth-power growth envelope. -/
theorem growth_of_large_dilation {G : ℕ → ℕ} (hm : Monotone G)
    (hd : ∀ᶠ n : ℕ in atTop, G (65536*n) ≤ 2*G n) :
    ∃ S : ℕ, ∀ n, (G n)^16 ≤ S*(n+1) := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 hd
  let B := G (65536*(N+1))
  have hpow (j : ℕ) : G (65536^j) ≤ B*2^j := by
    induction j with
    | zero =>
      simp only [pow_zero, mul_one]
      apply hm
      omega
    | succ j ih =>
      rw [pow_succ, mul_comm (65536^j),pow_succ]
      by_cases hj : N ≤ 65536^j
      · have h := (hN _ hj).trans (Nat.mul_le_mul_left 2 ih)
        simpa [mul_left_comm,mul_comm,mul_assoc] using h
      · have hle : G (65536*65536^j) ≤ B := hm (Nat.mul_le_mul_left 65536 (by omega))
        exact hle.trans (by
          have hh : 0 < 2^j*2 := by positivity
          exact Nat.le_mul_of_pos_right _ hh)
  refine ⟨B^16*65536,?_⟩
  intro n
  let j := Nat.log 65536 (n+1)
  have hlo : 65536^j ≤ n+1 := Nat.pow_log_le_self _ (by omega)
  have hhi : n ≤ 65536^(j+1) := (Nat.le_succ _).trans
    (Nat.lt_pow_succ_log_self (by decide : 1 < 65536) (n+1)).le
  calc
    _ ≤ (B*2^(j+1))^16 := Nat.pow_le_pow_left ((hm hhi).trans (hpow _)) _
    _ = B^16*(65536^j*65536) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm (j+1), pow_mul,
        show (2 : ℕ)^16 = 65536 by decide, pow_succ (65536 : ℕ) j]
    _ ≤ _ := by
      rw [mul_comm (65536^j), ← mul_assoc]
      exact Nat.mul_le_mul_left _ hlo

/-- Standard slow variation on the positive tail. -/
def SlowlyVarying (F : ℝ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → Tendsto (fun x => F (c*x)/F x) atTop (𝓝 1)

noncomputable def ceilingFactor (F : ℝ → ℝ) (n : ℕ) : ℕ :=
  ⌈F (max 1 (n : ℝ))⌉₊

theorem ceilingFactor_mono {F : ℝ → ℝ} (hm : MonotoneOn F (Set.Ici 1)) : Monotone (ceilingFactor F) := by
  intro i j h
  apply Nat.ceil_mono
  exact hm (Set.mem_Ici.mpr (le_max_left _ _)) (Set.mem_Ici.mpr (le_max_left _ _))
    (max_le_max_left _ (by exact_mod_cast h))

theorem ceilingFactor_pos {F : ℝ → ℝ} (hp : ∀ x ≥ 1, 1 ≤ F x) (n : ℕ) : 1 ≤ ceilingFactor F n :=
  Nat.one_le_ceil_iff.mpr (zero_lt_one.trans_le (hp _ (le_max_left _ _)))

theorem ceilingFactor_growth {F : ℝ → ℝ} (hm : MonotoneOn F (Set.Ici 1))
    (hp : ∀ x ≥ 1, 1 ≤ F x) (hv : SlowlyVarying F) :
    ∃ S : ℕ, ∀ i, (ceilingFactor F i)^16 ≤ S*(i+1) := by
  apply growth_of_large_dilation (ceilingFactor_mono hm)
  have h := (hv 65536 (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := h.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [he, eventually_ge_atTop 1] with n hn hnpos
  change F (65536*(n : ℝ))/F n < 2 at hn
  have hnr : 1 ≤ (n : ℝ) := by exact_mod_cast hnpos
  have hF : 0 < F n := zero_lt_one.trans_le (hp _ hnr)
  have hlt := (div_lt_iff₀ hF).mp hn
  dsimp [ceilingFactor]
  push_cast
  rw [max_eq_right hnr, max_eq_right (by linarith : 1 ≤ 65536*(n : ℝ))]
  apply Nat.ceil_le.mpr
  push_cast
  exact hlt.le.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num))

end JSP727
