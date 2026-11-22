import SubsetSumFree
import Rotation

namespace JSP727

set_option maxHeartbeats 800000

open Finset

/-- A changing target interval for an irrational rotation can be handled
term by term. Earlier fractional parts each exceed the current lower bound. -/
private theorem free_of_fractional_parts {a D : ℕ → ℕ} (ha : StrictMono a)
    (hp : ∀ i, 0 < a i) (hD : ∀ i, 0 < D i) (hm : Monotone D) {θ : ℝ}
    (hb : ∀ i, 1/(D i : ℝ) < Int.fract (a i*θ) ∧ Int.fract (a i*θ) < 2/(D i : ℝ))
    (hmass : ∀ s : Finset ℕ, ∑ i ∈ s, 2/(D i : ℝ) < 1) : SubsetSumFree a := by
  intro n s hlt heq
  have hc : 2 ≤ s.card := by
    by_contra! h
    rcases Nat.lt_or_eq_of_le (show s.card ≤ 1 by omega) with h₀ | h₁
    · have he : s = ∅ := card_eq_zero.mp (by omega)
      subst s
      simp at heq
      have := hp n
      omega
    · obtain ⟨j,rfl⟩ := card_eq_one.mp h₁
      have hj := hlt j (mem_singleton_self _)
      exact (ha hj).ne (by simpa using heq)
  let w := fun i => Int.fract (a i*θ)
  have hsumlt : ∑ i ∈ s, w i < 1 := (sum_le_sum (fun i _ => (hb i).2.le)).trans_lt (hmass s)
  have hfr : Int.fract (a n*θ) = ∑ i ∈ s, w i := by
    apply Int.fract_eq_iff.mpr
    refine ⟨sum_nonneg (fun _ _ => Int.fract_nonneg _), hsumlt,
      ∑ i ∈ s, ⌊(a i : ℝ)*θ⌋, ?_⟩
    rw [← heq, Nat.cast_sum, sum_mul, Int.cast_sum, ← sum_sub_distrib]
    exact sum_congr rfl (fun i _ => by dsimp only [w,Int.fract]; ring)
  have hl (i) (hi : i ∈ s) : 1/(D n : ℝ) < w i := by
    apply lt_of_le_of_lt _ (hb i).1
    exact one_div_le_one_div_of_le (by exact_mod_cast hD i) (by exact_mod_cast hm (hlt i hi).le)
  have hbnd : 2/(D n : ℝ) < ∑ i ∈ s, w i := by
    calc
      _ ≤ (s.card : ℝ)*(1/(D n : ℝ)) := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      _ = ∑ _i ∈ s, 1/(D n : ℝ) := by simp
      _ < _ := sum_lt_sum_of_nonempty (card_pos.mp (by omega)) hl
  exact (hb n).2.not_ge (by rw [hfr]; exact hbnd.le)

private theorem lower_gap_of_separation {a D : ℕ → ℕ} (ham : StrictMono a)
    (hD : ∀ i, 0 < D i) (hm : Monotone D)
    (hb : ∀ i, 1/(D i : ℝ) < Int.fract (a i*Real.sqrt 2) ∧
      Int.fract (a i*Real.sqrt 2) < 2/(D i : ℝ)) (i : ℕ) :
    D i ≤ 8*(a (i+1)-a i) := by
  have hinc (j : ℕ) : a j < a (j+1) := ham (Nat.lt_succ_self _)
  let q := a (i+1)-a i
  let z := ⌊(a (i+1) : ℝ)*Real.sqrt 2⌋ - ⌊(a i : ℝ)*Real.sqrt 2⌋
  have hsep := sqrt_two_separation q (Nat.sub_pos_of_lt (hinc i)) z
  have hDr : 0 < (D i : ℝ) := by exact_mod_cast (hD i)
  have hf₀ := hb i
  have hf₁ := hb (i+1)
  have hupper : Int.fract (a (i+1)*Real.sqrt 2) < 2/(D i : ℝ) :=
    hf₁.2.trans_le (div_le_div_of_nonneg_left (by norm_num) hDr (by exact_mod_cast hm (Nat.le_succ i)))
  have hid : (q : ℝ)*Real.sqrt 2-z =
      Int.fract (a (i+1)*Real.sqrt 2) - Int.fract (a i*Real.sqrt 2) := by
    dsimp only [q,z,Int.fract]
    rw [Nat.cast_sub (hinc i).le, Int.cast_sub]
    ring
  have herr : |(q : ℝ)*Real.sqrt 2-z| ≤ 2/(D i : ℝ) := by
    rw [hid,abs_le]
    constructor <;> linarith [Int.fract_nonneg (a i*Real.sqrt 2),
      Int.fract_nonneg (a (i+1)*Real.sqrt 2), hf₀.2]
  have hfinal := hsep.trans (mul_le_mul_of_nonneg_left herr (by positivity))
  rw [← mul_div_assoc, le_div_iff₀ hDr] at hfinal
  exact_mod_cast (show (D i : ℝ) ≤ 8*q by linarith)

private theorem construct_scaled (D : ℕ → ℕ) (hD : ∀ i, 3 ≤ D i) (hm : Monotone D)
    (hmass : ∀ s : Finset ℕ, ∑ i ∈ s, 2/(D i : ℝ) < 1) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧ SubsetSumFree a ∧
      (∀ i, a (i+1)-a i ≤ 33*D (i+1)) ∧ ∀ i, D i ≤ 8*(a (i+1)-a i) := by
  let pick := fun i start => (sqrt_two_visit (D i) start (hD i)).choose
  have hpk (i start) := (sqrt_two_visit (D i) start (hD i)).choose_spec
  let a : ℕ → ℕ := Nat.rec (motive := fun _ => ℕ) (pick 0 1) (fun i x => pick (i+1) (x+1))
  have hinc (i : ℕ) : a i < a (i+1) := (hpk (i+1) (a i+1)).1
  have ham := strictMono_nat_of_lt_succ hinc
  have hap (i) : 0 < a i := (hpk 0 1).1.trans (ham.monotone (Nat.zero_le i))
  let w := fun i : ℕ => Int.fract (Nat.cast (R := ℝ) (a i)*Real.sqrt 2)
  have hb (i : ℕ) : 1/(D i : ℝ) < w i ∧ w i < 2/(D i : ℝ) := by
    cases i with
    | zero => exact (hpk 0 1).2.2
    | succ i => exact (hpk (i+1) (a i+1)).2.2
  refine ⟨a,ham,hap,free_of_fractional_parts ham hap (fun i => by have := hD i; omega)
    hm hb hmass,?_,?_⟩
  · intro i
    have hp : a (i+1) ≤ a i+1+32*D (i+1) := (hpk (i+1) (a i+1)).2.1
    have := hD (i+1)
    omega
  · exact lower_gap_of_separation ham (fun i => by have := hD i; omega) hm hb

/-- Every nondecreasing positive integer gap budget with summable reciprocal
admits an infinite subset-sum-free sequence with gaps at most a constant
times that budget. The preceding budget bounds each gap from below as well. -/
theorem exists_of_summable_reciprocal {g : ℕ → ℕ} (hg : ∀ i, 0 < g i) (hm : Monotone g)
    (hs : Summable (fun i => 1/(g i : ℝ))) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧ SubsetSumFree a ∧
      (∃ C : ℕ, ∀ i, a (i+1)-a i ≤ C*g (i+1)) ∧ ∀ i, g i ≤ 8*(a (i+1)-a i) := by
  obtain ⟨m,hmBig⟩ := exists_nat_gt (2*∑' i, (1/(g i : ℝ)))
  let M := m+3
  let D := fun i => M*g i
  have hM : 0 < M := by dsimp [M]; omega
  have hd (i) : 3 ≤ D i := by
    have h := Nat.le_mul_of_pos_right M (hg i)
    dsimp [D,M] at *
    omega
  have hmono : Monotone D := fun _ _ hij => Nat.mul_le_mul_left _ (hm hij)
  have hmass (s : Finset ℕ) : ∑ i ∈ s, 2/(D i : ℝ) < 1 := by
    have htot := hs.sum_le_tsum s (fun i _ => by positivity)
    have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
    calc
      _ = (2*∑ i ∈ s, 1/(g i : ℝ))/M := by
        rw [mul_sum, sum_div]
        apply sum_congr rfl
        intro i _
        simp [D, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ < _ := by
        rw [div_lt_one hMr]
        dsimp [M]
        push_cast
        linarith
  obtain ⟨a,ha,hp,hf,hu,hl⟩ := construct_scaled D hd hmono hmass
  refine ⟨a,ha,hp,hf,⟨33*M,?_⟩,?_⟩
  · intro i
    simpa [D,mul_assoc] using hu i
  · intro i
    exact (Nat.le_mul_of_pos_left (g i) hM).trans (hl i)

end JSP727
