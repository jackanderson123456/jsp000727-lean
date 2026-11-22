import ApproximationWindow

namespace JSP727

open Finset

/-- Among 16k real points at mutual distances at least one, at least 8k
have absolute value at least k. -/
private theorem separated_sum {s : Finset ℕ} {f : ℕ → ℝ} {k : ℕ}
    (hk : 0 < k) (hcard : s.card = 16*k)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ |f i-f j|) :
    (8*(k : ℝ))*k ≤ ∑ i ∈ s, |f i| := by
  classical
  let t := s.filter (fun i => |f i| < k)
  have maps : Set.MapsTo (fun i => ⌊f i⌋) (t : Set ℕ) (Icc (-(k : ℤ)) (k : ℤ) : Finset ℤ) := by
    intro i hi
    obtain ⟨_,hb⟩ := mem_filter.mp (show i ∈ t from hi)
    obtain ⟨hl,hu⟩ := abs_lt.mp hb
    exact mem_Icc.mpr ⟨Int.le_floor.mpr (by simpa using hl.le), Int.floor_le_iff.mpr (by
      push_cast; linarith)⟩
  have inj : Set.InjOn (fun i => ⌊f i⌋) (t : Set ℕ) := by
    intro i hi j hj he
    by_contra hne
    have h := hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hne
    have hi₁ := Int.floor_le (f i)
    have hi₂ := Int.lt_floor_add_one (f i)
    have hj₁ := Int.floor_le (f j)
    have hj₂ := Int.lt_floor_add_one (f j)
    change ⌊f i⌋ = ⌊f j⌋ at he
    rw [he] at hi₁ hi₂
    exact h.not_gt (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have ht := card_le_card_of_injOn _ maps inj
  rw [Int.card_Icc] at ht
  have hcount := card_le_card_sdiff_add_card (s := s) (t := t)
  have hbig : 8*k ≤ (s \ t).card := by omega
  calc
    _ ≤ ((s \ t).card : ℝ)*k := by gcongr; exact_mod_cast hbig
    _ = ∑ _ ∈ s \ t, (k : ℝ) := by simp
    _ ≤ ∑ i ∈ s \ t, |f i| := by
      apply sum_le_sum
      intro i hi
      obtain ⟨his,hit⟩ := mem_sdiff.mp hi
      exact le_of_not_gt (fun h => hit (mem_filter.mpr ⟨his,h⟩))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => abs_nonneg _)

/-- One short run of values with length 16k and span at most half the
denominator costs at least 4k²/q in distance to the nearest integer. -/
theorem phase_run_mass {a : ℕ → ℕ} (ha : StrictMono a) {s : Finset ℕ} {k T : ℕ}
    (hk : 0 < k) (hcard : s.card = 16*k) {θ : ℝ} {r : ℚ} (hr : r.den ≤ T)
    (he : |θ-r| ≤ 1/(((T : ℝ)+1)*r.den))
    (hspan : ∀ i ∈ s, ∀ j ∈ s, i < j → 2*(a j-a i) ≤ r.den) :
    4*(k : ℝ)^2 ≤ (r.den : ℝ)*∑ i ∈ s, phase (a i*θ) := by
  let f := fun i => 2*(r.den : ℝ)*((a i : ℝ)*θ-round (a i*θ))
  have hd : 0 < (r.den : ℝ) := by positivity
  have sep (i j : ℕ) (hi : i ∈ s) (hj : j ∈ s) (hij : i < j) : 1 ≤ |f j-f i| := by
    let z := round (a j*θ) - round (a i*θ)
    have hlt := ha hij
    have hwidth := hspan i hi j hj hij
    have hnd : ¬ r.den ∣ a j-a i := fun h => by
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) h
      omega
    have h := dirichlet_spacing he hnd (by omega) z
    have hraw := (div_le_iff₀ (by positivity : 0 < 2*(r.den : ℝ))).mp h
    have heq : f j-f i = (2*(r.den : ℝ))*(((a j-a i : ℕ) : ℝ)*θ-z) := by
      dsimp [f,z]
      rw [Nat.cast_sub hlt.le, Int.cast_sub]
      ring
    rwa [heq, abs_mul, abs_of_pos (by positivity : 0 < 2*(r.den : ℝ)), mul_comm]
  have hp := separated_sum hk hcard (f := f) (by
    intro i hi j hj hne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_sub_comm]
      exact sep i j hi hj h
    · exact sep j i hj hi h)
  have sum_eq : ∑ i ∈ s, |f i| = (2*(r.den : ℝ))*∑ i ∈ s, phase (a i*θ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    simp [f,phase,abs_mul,abs_of_nonneg (show 0 ≤ (r.den : ℝ) by positivity)]
  rw [sum_eq] at hp
  nlinarith

end JSP727
