import SubsetSumFree
import Residues
import Phase

namespace JSP727

private theorem exception_count_mul (a : ℕ → ℕ) {d : ℕ} (hd : 0 < d) (q n : ℕ) :
    Nat.count (fun i => ¬ d*q ∣ a i) n =
      Nat.count (fun i => ¬ d ∣ a i) n +
      Nat.count (fun j => ¬ q ∣ quotientSeq a d j) (Nat.count (fun i => d ∣ a i) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : d ∣ a n
    · have hterm : quotientSeq a d (Nat.count (fun i => d ∣ a i) n) = a n / d := by
        simp only [quotientSeq, Nat.nth_count (p := fun j => d ∣ a j) h]
      have heq : d*q ∣ a n ↔ q ∣ a n/d := by
        nth_rw 1 [← Nat.mul_div_cancel' h]
        exact Nat.mul_dvd_mul_iff_left hd
      by_cases hq : q ∣ a n/d <;> simp [Nat.count_succ, h, heq, hterm, hq, ih, add_assoc]
    · have hbad : ¬ d*q ∣ a n := fun hh => h ((dvd_mul_right d q).trans hh)
      simp [Nat.count_succ, h, hbad, ih, add_assoc, add_comm]

/-- A bounded set of exceptional moduli suffices for the normalization. -/
theorem modular_normalization_of_bounded_moduli {a : ℕ → ℕ} {U : ℕ}
    (hbound : ∀ d, 0 < d → FewExceptions a d → d ≤ U) :
    ∃ d, 0 < d ∧ FewExceptions a d ∧ ∀ q, 0 < q → Covers (quotientSeq a d) q := by
  classical
  have hone : FewExceptions a 1 := by
    intro n
    simp
  have hU : 1 ≤ U := hbound 1 (by decide) hone
  let d := Nat.findGreatest (FewExceptions a) U
  have hd : 0 < d := Nat.le_findGreatest hU hone
  have hgood : FewExceptions a d := Nat.findGreatest_spec hU hone
  refine ⟨d, hd, hgood, ?_⟩
  intro q hq
  by_contra hfail
  obtain ⟨e, he, hex⟩ := few_exceptions_of_missing ⟨q,hq,hfail⟩
  have hdprod : 0 < d*e := Nat.mul_pos hd (by omega)
  have hwe : FewExceptions a (d*e) := by
    intro n
    rw [exception_count_mul a hd]
    have h₁ := hgood n
    have h₂ := hex (Nat.count (fun i => d ∣ a i) n)
    nlinarith [Nat.zero_le ((d-1)*(e-1)),
      Nat.sub_add_cancel (show 1 ≤ d by omega), Nat.sub_add_cancel (show 1 ≤ e by omega),
      Nat.mul_le_mul (show 1 ≤ d by omega) (show 1 ≤ e-1 by omega)]
  have hub : d*e ≤ U := hbound _ hdprod hwe
  have hle : d*e ≤ d := Nat.le_findGreatest hub hwe
  nlinarith

/-- For a sum-free sequence of at most quadratic growth, divide the terms
that are multiples of a single bounded divisor by that divisor. The resulting
sequence has finite subset sums in every residue class, for every modulus. -/
theorem exists_modular_normalization {a : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (hf : SubsetSumFree a) {C : ℕ}
    (hg : ∀ i, a i ≤ C * (i+1)^2) :
    ∃ d, 0 < d ∧ FewExceptions a d ∧ ∀ q, 0 < q → Covers (quotientSeq a d) q :=
  modular_normalization_of_bounded_moduli (fun _ hd h => exceptional_divisor_bound ha hpos hf hg hd h)

theorem linear_gap_window {a : ℕ → ℕ} {K : ℕ}
    (hg : ∀ i, a (i+1)-a i ≤ K*(i+1)) {u v : ℕ} (huv : u ≤ v) :
    a v-a u ≤ (v-u)*(K*v) := by
  have hspan (l : ℕ) (hl : u+l ≤ v) : a (u+l) ≤ a u + l*(K*v) := by
    induction l with
    | zero => simp
    | succ l ih =>
      have hstep := hg (u+l)
      have hmono := Nat.mul_le_mul_left K hl
      have hpre := ih (by omega)
      rw [Nat.succ_mul]
      simp only [← Nat.add_assoc] at hmono ⊢
      omega
  have hraw := hspan (v-u) (by omega)
  rw [Nat.add_sub_of_le huv] at hraw
  omega

theorem affine_linear_gaps {a : ℕ → ℕ} {K : ℕ}
    (hg : ∀ i, a (i+1)-a i ≤ K*(i+1)) (t c i : ℕ) :
    a (t*(i+1)+c)-a (t*i+c) ≤ (t*K*(t+c))*(i+1) := by
  have hx : t*(i+1)+c = t*i+c+t := by ring
  have hl : t*i+c ≤ t*(i+1)+c := by omega
  have hm : t*(i+1)+c ≤ (t+c)*(i+1) := by nlinarith
  calc
    _ ≤ ((t*(i+1)+c)-(t*i+c))*(K*(t*(i+1)+c)) := linear_gap_window hg hl
    _ ≤ t*(K*((t+c)*(i+1))) := by
      rw [show (t*(i+1)+c)-(t*i+c) = t by omega]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hm)
    _ = _ := by ring

theorem quadratic_bound_of_linear_gaps {a : ℕ → ℕ} {K : ℕ}
    (hg : ∀ i, a (i+1)-a i ≤ K*(i+1)) (i : ℕ) :
    a i ≤ (a 0+K)*(i+1)^2 := by
  have h := linear_gap_window hg (Nat.zero_le i)
  simp only [Nat.sub_zero] at h
  have hle : a i ≤ a 0 + i*(K*i) := by omega
  calc
    _ ≤ _ := hle
    _ = a 0*1 + K*i^2 := by ring
    _ ≤ a 0*(i+1)^2 + K*(i+1)^2 := by
      have hpos : 0 < (i+1)^2 := by positivity
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hpos)
        (Nat.mul_le_mul_left _ (by gcongr; omega))
    _ = _ := by ring

/-- A uniform linear gap bound survives the normalization. -/
theorem quotient_linear_gaps {a : ℕ → ℕ} {d K : ℕ} (hd : 0 < d)
    (h : FewExceptions a d) (hg : ∀ i, a (i+1)-a i ≤ K*(i+1)) :
    ∀ i, quotientSeq a d (i+1)-quotientSeq a d i ≤ (K*(d+1)^2)*(i+1) := by
  let f := Nat.nth (fun j => d ∣ a j)
  obtain ⟨hm, hle, heq⟩ := divisible_indices h
  intro i
  have hi : i ≤ f i := hm.id_le i
  let u := f i
  let v := f (i+1)
  have huv : u ≤ v := hm.monotone (Nat.le_succ _)
  have hstep : v-u ≤ d+1 := by have := hle (i+1); dsimp [v,u,f] at *; omega
  have hv : v ≤ (i+1)*(d+1) := by
    have hle' := hle (i+1)
    change v ≤ i+1+d at hle'
    nlinarith
  have hdiv : quotientSeq a d (i+1)-quotientSeq a d i ≤ a v-a u := by
    calc
      _ ≤ d*(quotientSeq a d (i+1)-quotientSeq a d i) := Nat.le_mul_of_pos_left _ hd
      _ = _ := by rw [Nat.mul_sub, heq, heq]
  calc
    _ ≤ (v-u)*(K*v) := hdiv.trans (linear_gap_window hg huv)
    _ ≤ (d+1)*(K*((i+1)*(d+1))) := Nat.mul_le_mul hstep (Nat.mul_le_mul_left K hv)
    _ = _ := by ring

end JSP727
