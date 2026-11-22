import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

namespace JSP727

open Finset

/-- Distance to the nearest integer. -/
noncomputable def phase (t : ℝ) : ℝ := |t - round t|

private theorem large_approximant {θ : ℝ} (hirr : Irrational θ) (D : ℕ) :
    ∃ q : ℚ, D < q.den ∧ |θ - q| < 1 / (q.den : ℝ)^2 := by
  by_contra! h
  let M : ℤ := ⌈(|θ|+1)*D⌉
  let s := (Icc (-M) M) ×ˢ (range (D+1))
  apply Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hirr
  apply Set.Finite.subset (s.finite_toSet.image (fun p : ℤ × ℕ => (p.1 : ℚ) / p.2))
  intro q hq
  change |θ - q| < 1 / (q.den : ℝ)^2 at hq
  have hd : q.den ≤ D := by by_contra! hn; exact (h q hn).not_gt hq
  have hd1 : 1 ≤ (q.den : ℝ) := by exact_mod_cast q.pos
  have hnear : |θ - q| < 1 :=
    hq.trans_le ((div_le_iff₀ (by positivity)).2 (by nlinarith))
  have habs : |(q : ℝ)| ≤ |θ|+1 := by
    calc
      |(q : ℝ)| = |θ - (θ-q)| := by ring_nf
      _ ≤ |θ| + |θ-q| := abs_sub _ _
      _ ≤ _ := by linarith
  have hnum : |(q.num : ℝ)| ≤ (|θ|+1)*D := by
    have heq : (q : ℝ) * q.den = q.num := by rw [Rat.cast_def]; field_simp
    rw [← heq, abs_mul, abs_of_pos (by positivity : 0 < (q.den : ℝ))]
    exact mul_le_mul habs (by exact_mod_cast hd) (by positivity) (by positivity)
  have hi : |q.num| ≤ M := by
    exact_mod_cast hnum.trans (Int.le_ceil _)
  refine ⟨(q.num, q.den), ?_, q.num_div_den⟩
  simpa [s, abs_le] using And.intro (abs_le.mp hi) (show q.den < D+1 by omega)

theorem nonmultiple_rational_spacing (q : ℚ) {h : ℕ}
    (hnd : ¬ q.den ∣ h) (z : ℤ) :
    1 ≤ |(h : ℝ) * q - z| * q.den := by
  have hne : (h : ℤ)*q.num - z*q.den ≠ 0 := by
    intro hz
    have hdiv : (q.den : ℤ) ∣ (h : ℤ)*q.num :=
      ⟨z, by linear_combination hz⟩
    have hnat : q.den ∣ h := by
      have h' := Int.natAbs_dvd_natAbs.mpr hdiv
      exact q.reduced.symm.dvd_of_dvd_mul_right (by simpa [Int.natAbs_mul] using h')
    exact hnd hnat
  have hi := Int.one_le_abs hne
  have heq : (q : ℝ) * q.den = q.num := by rw [Rat.cast_def]; field_simp
  calc
    1 ≤ (|((h : ℤ)*q.num - z*q.den : ℤ)| : ℝ) := by exact_mod_cast hi
    _ = |((h : ℝ)*q-z) * q.den| := by
      push_cast
      congr 1
      rw [← heq]
      ring
    _ = _ := by rw [abs_mul, abs_of_pos (by positivity : 0 < (q.den : ℝ))]

private theorem adjacent_phases {θ : ℝ} {q : ℚ}
    (hq : |θ-q| < 1 / (q.den : ℝ)^2)
    {x y : ℕ} (hxy : x < y) (hgap : 2*(y-x) ≤ q.den) :
    1/(2*(q.den : ℝ)) ≤ phase (y*θ) + phase (x*θ) := by
  let h := y-x
  let z := round ((y : ℝ)*θ) - round ((x : ℝ)*θ)
  have hd : 0 < (q.den : ℝ) := by positivity
  have hh : 0 < h := Nat.sub_pos_of_lt hxy
  have hhd : h < q.den := by dsimp [h] at *; omega
  have hhr : 2*(h : ℝ) ≤ q.den := by exact_mod_cast hgap
  have herr : (h : ℝ)*|θ-q| ≤ 1/(2*(q.den : ℝ)) := by
    calc
      _ ≤ (h : ℝ)*(1/(q.den : ℝ)^2) := by gcongr
      _ ≤ _ := by field_simp; nlinarith
  have htri : |(h : ℝ)*q-z| ≤ (h : ℝ)*|θ-q| + |(h : ℝ)*θ-z| := by
    calc
      _ = |(h : ℝ)*(q-θ) + ((h : ℝ)*θ-z)| := by congr 1; ring
      _ ≤ _ := by
        simpa [abs_mul, abs_sub_comm (q : ℝ) θ, abs_of_nonneg (Nat.cast_nonneg h : 0 ≤ (h : ℝ))] using
          abs_add_le ((h : ℝ)*(q-θ)) ((h : ℝ)*θ-z)
  have hph : |(h : ℝ)*θ-z| ≤ phase (y*θ) + phase (x*θ) := by
    dsimp [h,z,phase]
    rw [Nat.cast_sub hxy.le, Int.cast_sub]
    calc
      _ = |((y:ℝ)*θ-(round (y*θ) : ℝ))-((x:ℝ)*θ-(round (x*θ) : ℝ))| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  have hsep : 1/(q.den : ℝ) ≤ |(h : ℝ)*q-z| :=
    (div_le_iff₀ hd).mpr (nonmultiple_rational_spacing q
      (fun hdiv => hhd.not_ge (Nat.le_of_dvd hh hdiv)) z)
  linarith [show 1/(q.den : ℝ) = 2*(1/(2*(q.den : ℝ))) by field_simp]

/-- A sequence with linear gaps has divergent nearest-integer distances at
every irrational phase. This is the linear case of Korsky's Proposition 3.5.
The proof only needs Dirichlet approximation with unbounded denominators. -/
theorem not_summable_phase_of_linear_gaps {a : ℕ → ℕ} (ha : StrictMono a)
    {K : ℕ} (hK : 0 < K) (hg : ∀ i, a (i+1)-a i ≤ K*(i+1))
    {θ : ℝ} (hθ : Irrational θ) : ¬ Summable (fun i => phase (a i * θ)) := by
  intro hs
  let w := fun i => phase (a i * θ)
  have hw (i : ℕ) : 0 ≤ w i := abs_nonneg _
  let ε := 1/(128*(K : ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨s, ht⟩ := summable_iff_vanishing_norm.mp hs ε hε
  let B := s.sup id
  obtain ⟨q, hlarge, hq⟩ := large_approximant hθ ((B+2)*(8*K))
  let n := q.den / (8*K)
  have hk8 : 0 < 8*K := by omega
  have hbn : B+2 ≤ n := (Nat.le_div_iff_mul_le hk8).mpr hlarge.le
  have hlo : n*(8*K) ≤ q.den := Nat.div_mul_le_self _ _
  have hup : q.den < (n+1)*(8*K) := by
    simpa only [n, Nat.mul_comm (8*K)] using Nat.lt_mul_div_succ q.den hk8
  let t := Ico n (2*n)
  have hlate {u : Finset ℕ} (hu : ∀ i ∈ u, B < i) : ∑ i ∈ u, w i < ε := by
    have hdis : Disjoint u s := by
      rw [Finset.disjoint_left]
      intro i hi his
      exact (hu i hi).not_ge (le_sup (f := id) his)
    simpa [w, Real.norm_eq_abs, abs_of_nonneg (sum_nonneg (fun i _ => hw i) : 0 ≤ ∑ i ∈ u, w i)]
      using ht u hdis
  have hw₀ : ∑ i ∈ t, w i < ε := hlate (by
    intro i hi; have := (mem_Ico.mp hi).1; omega)
  have hw₁ : ∑ i ∈ t, w (i+1) < ε := by
    have ht' : ∀ i ∈ t.image Nat.succ, B < i := by
      intro i hi
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hi
      have := (mem_Ico.mp hk).1
      omega
    simpa [sum_image Nat.succ_injective.injOn] using hlate ht'
  have hpair (i : ℕ) (hi : i ∈ t) :
      1/(2*(q.den : ℝ)) ≤ w (i+1)+w i := by
    apply adjacent_phases hq (ha (Nat.lt_succ_self i))
    have hi' := (mem_Ico.mp hi).2
    calc
      2*(a (i+1)-a i) ≤ 2*(K*(i+1)) := Nat.mul_le_mul_left _ (hg _)
      _ ≤ 2*(K*(2*n)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hi')
      _ ≤ n*(8*K) := by nlinarith
      _ ≤ _ := hlo
  have htotal := sum_le_sum hpair
  have htc : t.card = n := by simp [t, Nat.card_Ico, two_mul]
  simp only [sum_const, htc, nsmul_eq_mul, sum_add_distrib] at htotal
  have hwt : (n : ℝ) * (1/(2*(q.den : ℝ))) < 2*ε := by
    linarith
  dsimp [ε] at hwt
  have hden : (0 : ℝ) < q.den := by positivity
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  field_simp at hwt
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hupr : (q.den : ℝ) < (n+1)*(8*(K : ℝ)) := by exact_mod_cast hup
  nlinarith [mul_le_mul_of_nonneg_right hn hKr.le]

end JSP727
