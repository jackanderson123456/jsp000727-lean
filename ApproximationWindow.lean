import Phase
import PrefixScarcity

namespace JSP727

open Finset

/-- For a fixed irrational rotation, arbitrarily small error excludes every
denominator in a fixed finite set. -/
private theorem finite_denominators {θ : ℝ} (hθ : Irrational θ) (B : ℕ) :
    ∃ M : ℕ, ∀ n, 0 < n → n ≤ B → 1 < (M : ℝ)*phase (n*θ) := by
  induction B with
  | zero => exact ⟨1,by omega⟩
  | succ B ih =>
    obtain ⟨M,hM⟩ := ih
    have hp : 0 < phase (((B+1 : ℕ) : ℝ)*θ) := by
      apply abs_pos.mpr
      exact sub_ne_zero.mpr ((hθ.natCast_mul (by omega : B+1 ≠ 0)).ne_int _)
    obtain ⟨m,hm⟩ := exists_nat_gt (1/phase (((B+1 : ℕ) : ℝ)*θ))
    refine ⟨max M m,?_⟩
    intro n hn hB
    rcases Nat.lt_or_eq_of_le hB with h | rfl
    · exact (hM n hn (by omega)).trans_le (mul_le_mul_of_nonneg_right
        (by exact_mod_cast le_max_left M m) (abs_nonneg _))
    · exact ((div_lt_iff₀ hp).mp hm).trans_le (mul_le_mul_of_nonneg_right
        (by exact_mod_cast le_max_right M m) hp.le)

private theorem dirichlet_large_denominator {θ : ℝ} (hθ : Irrational θ) (B : ℕ) :
    ∃ M : ℕ, ∀ T : ℕ, T ≥ M → ∀ r : ℚ, |θ-r| ≤ 1/(((T : ℝ)+1)*r.den) → B < r.den := by
  obtain ⟨M,hM⟩ := finite_denominators hθ B
  refine ⟨M,?_⟩
  intro T hT r he
  by_contra! hbad
  have hstrict := hM r.den r.pos hbad
  have hq : 0 < (r.den : ℝ) := by positivity
  have hT' : 0 < (T : ℝ)+1 := by positivity
  have hrat : (r : ℝ)*r.den = r.num := by rw [Rat.cast_def]; field_simp
  have herr := (le_div_iff₀ (mul_pos hT' hq)).mp he
  have hnear : phase (r.den*θ) ≤ |θ-r| * r.den := by
    calc
      _ ≤ |(r.den : ℝ)*θ-r.num| := round_le _ _
      _ = |θ-r| * r.den := by
        rw [← hrat, mul_comm (r.den : ℝ), ← sub_mul, abs_mul, abs_of_pos hq]
  have hMT : (M : ℝ) ≤ (T : ℝ)+1 := by exact_mod_cast (show M ≤ T+1 by omega)
  have hle := mul_le_mul hMT hnear (abs_nonneg _) hT'.le
  nlinarith only [hstrict, hle, herr]

/-- Separation from all integers at a nonmultiple of the reduced denominator. -/
theorem dirichlet_spacing {θ : ℝ} {T h : ℕ} {r : ℚ}
    (he : |θ-r| ≤ 1/(((T : ℝ)+1)*r.den)) (hnd : ¬ r.den ∣ h)
    (hsize : 2*h ≤ T+1) (z : ℤ) :
    1/(2*(r.den : ℝ)) ≤ |(h : ℝ)*θ-z| := by
  have hd : 0 < (r.den : ℝ) := by positivity
  have ht : 0 < (T : ℝ)+1 := by positivity
  have hsz : 2*(h : ℝ) ≤ (T : ℝ)+1 := by exact_mod_cast hsize
  have hsmall : (h : ℝ)*|θ-r| ≤ 1/(2*(r.den : ℝ)) := by
    calc
      _ ≤ (h : ℝ)*(1/(((T : ℝ)+1)*r.den)) := by gcongr
      _ ≤ _ := by field_simp; linarith
  have hsep := (div_le_iff₀ hd).mpr (nonmultiple_rational_spacing r hnd z)
  have htri : |(h : ℝ)*r-z| ≤ (h : ℝ)*|θ-r| + |(h : ℝ)*θ-z| := by
    calc
      _ = |(h : ℝ)* (r-θ) + ((h : ℝ)*θ-z)| := by congr 1; ring
      _ ≤ _ := by simpa [abs_mul, abs_sub_comm (r : ℝ) θ] using
          abs_add_le ((h : ℝ)*(r-θ)) ((h : ℝ)*θ-z)
  linarith [show 1/(r.den : ℝ) = 2*(1/(2*(r.den : ℝ))) by field_simp]

/-- Summability and finite-prefix scarcity force a good rational denominator
between the sixth root of T and T at every sufficiently large scale. -/
theorem denominator_window {θ : ℝ} (hθ : Irrational θ) {a : ℕ → ℕ}
    (hs : Summable (fun i => phase (a i*θ))) {D : ℕ}
    (hnon : ∀ d ≥ D, d < Nat.count (fun i => ¬ d ∣ a i) (d^2))
    (hsize : ∀ d ≥ D, ∀ i < d^2, 2*a i ≤ d^6) :
    ∃ M : ℕ, ∀ T : ℕ, T ≥ M → ∃ r : ℚ, r.den ≤ T ∧ T < r.den^6 ∧
      |θ-r| ≤ 1/(((T : ℝ)+1)*r.den) := by
  obtain ⟨s,htail⟩ := summable_iff_vanishing_norm.mp hs (1/8) (by norm_num)
  obtain ⟨M,hM⟩ := dirichlet_large_denominator hθ (D+2*s.card)
  refine ⟨M+1,?_⟩
  intro T hT
  obtain ⟨r,he,hr⟩ := Real.exists_rat_abs_sub_le_and_den_le θ (by omega : 0 < T)
  refine ⟨r,hr,?_,he⟩
  by_contra! h
  have hbig := hM T (by omega) r he
  have hD : D ≤ r.den := by omega
  let u := (range (r.den^2)).filter (fun i => ¬ r.den ∣ a i)
  have hu : r.den < u.card := by simpa only [Nat.count_eq_card_filter_range, u] using hnon _ hD
  let v := u \ s
  have hcard : r.den ≤ 2*v.card := by
    have hsub := card_le_card_sdiff_add_card (s := u) (t := s)
    dsimp only [v]
    omega
  have hdis : Disjoint v s := Finset.sdiff_disjoint
  have hupper : ∑ i ∈ v, phase (a i*θ) < 1/8 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sum_nonneg (fun i _ =>
      show 0 ≤ phase (a i*θ) from abs_nonneg _))] using htail v hdis
  have hterm (i) (hi : i ∈ v) : 1/(2*(r.den : ℝ)) ≤ phase (a i*θ) := by
    obtain ⟨hi',hnd⟩ := mem_filter.mp (mem_sdiff.mp hi).1
    exact dirichlet_spacing he hnd ((hsize _ hD _ (mem_range.mp hi')).trans (by omega)) _
  have hlower := sum_le_sum hterm
  simp only [sum_const, nsmul_eq_mul] at hlower
  have hsmall : (v.card : ℝ) / (2*(r.den : ℝ)) < 1/8 := by
    simpa only [div_eq_mul_inv, one_mul] using hlower.trans_lt hupper
  have hscaled := (div_lt_iff₀ (by positivity : 0 < 2*(r.den : ℝ))).mp hsmall
  have hcard' : (r.den : ℝ) ≤ 2*(v.card : ℝ) := by exact_mod_cast hcard
  linarith [show 0 < (r.den : ℝ) by positivity]

/-- Applied to an increasing subset-sum-free sequence, the two finite-prefix
hypotheses of the denominator window follow from the same growth envelope. -/
theorem denominator_window_of_growth {a g : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (hf : SubsetSumFree a) (hm : Monotone g)
    (hp : ∀ i, 1 ≤ g i) {S : ℕ} (hslow : ∀ i, (g i)^16 ≤ S*(i+1))
    (hg : ∀ i, a i ≤ g (i+1)*(i+1)^2) {θ : ℝ} (hθ : Irrational θ)
    (hs : Summable (fun i => phase (a i*θ))) :
    ∃ M : ℕ, ∀ T : ℕ, T ≥ M → ∃ r : ℚ, r.den ≤ T ∧ T < r.den^6 ∧
      |θ-r| ≤ 1/(((T : ℝ)+1)*r.den) := by
  obtain ⟨D₁,h₁⟩ := many_nonmultiples ha hpos hf hm hp hslow hg
  obtain ⟨D₂,h₂⟩ := large_modulus_window hp hslow
  apply denominator_window hθ hs (D := D₁+D₂+2) (fun d hd => h₁ d (by omega))
  intro d hd i hi
  have ⟨hposd,hwidth,_⟩ := h₂ d (by omega)
  rw [sq d] at hwidth
  have hgd : 4*g (d^2)+3 ≤ d := by
    exact Nat.le_of_mul_le_mul_right (by simpa only [sq] using hwidth) hposd
  have hbound : a i ≤ d*(d^2)^2 := by
    apply (hg i).trans
    exact Nat.mul_le_mul ((hm hi).trans (by omega)) (Nat.pow_le_pow_left hi 2)
  calc
    2*a i ≤ 2*(d*(d^2)^2) := Nat.mul_le_mul_left _ hbound
    _ ≤ d*(d*(d^2)^2) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end JSP727
