import BlockMass

namespace JSP727

open Finset

private theorem two_pow_mono {i j : ℕ} (h : i ≤ j) : (2 : ℕ)^i ≤ 2^j :=
  Nat.pow_le_pow_right (by decide) h

/-- A power-of-two interval for q contains a band of dyadic indices j.
Every block in this band satisfies the two inequalities in the packing lemma. -/
private theorem choose_scale_band {g : ℕ → ℕ} {S x q : ℕ}
    (hs : ∀ i, (g i)^16 ≤ S*(i+1)) (hx : 16 ≤ x) (hS : S ≤ x)
    (hlo : 2^(96*x) < q^6) (hhi : q ≤ 2^(96*x)) :
    ∃ l, x ≤ l ∧ l ≤ 6*x ∧ ∀ j, 10*l ≤ j → j < 12*l →
      128*(2^j)*g (2*(2^j)) ≤ q ∧ q ≤ (2^j)^2 := by
  have hq : 2^(16*x) ≤ q := by
    by_contra! hh
    have hpow := Nat.pow_le_pow_left hh.le 6
    rw [← pow_mul, show 16*x*6 = 96*x by ring] at hpow
    omega
  have hpos : 0 < q := (pow_pos (by decide : 0 < (2 : ℕ)) _).trans_le hq
  let l := Nat.log 2 q / 16
  have hlog : 16*x ≤ Nat.log 2 q := Nat.le_log_of_pow_le (by decide) hq
  have hlog' : Nat.log 2 q ≤ 96*x := by
    have := Nat.log_mono_right (b := 2) hhi
    simpa [Nat.log_pow (by decide : 1 < 2)] using this
  have hx' : x ≤ l := by dsimp [l]; omega
  have hupper : l ≤ 6*x := by dsimp [l]; omega
  have h₁ : 2^(16*l) ≤ q := (two_pow_mono (by dsimp [l]; omega)).trans
    (Nat.pow_log_le_self 2 hpos.ne')
  have h₂ : q < 2^(16*l+16) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) q).trans_le
    (two_pow_mono (by dsimp [l]; omega))
  refine ⟨l,hx',hupper,?_⟩
  intro j hj hj'
  have hl : S ≤ 2^l := (hS.trans hx').trans (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hg : g (2*2^j) ≤ 2^(2*l) := by
    apply (Nat.pow_le_pow_iff_left (by decide : 16 ≠ 0)).mp
    calc
      _ ≤ S*(2*2^j+1) := hs _
      _ ≤ (2^l)*(2^(j+2)) := Nat.mul_le_mul hl (by
        rw [pow_add]; have : 1 ≤ (2 : ℕ)^j := Nat.one_le_two_pow; omega)
      _ = 2^(l+(j+2)) := (pow_add _ _ _).symm
      _ ≤ 2^(2*l*16) := two_pow_mono (by omega)
      _ = _ := pow_mul _ _ _
  constructor
  · calc
      _ ≤ 128*(2^j)*(2^(2*l)) := Nat.mul_le_mul_left _ hg
      _ = 2^(7+j+2*l) := by rw [pow_add, pow_add (2 : ℕ) 7 j]; norm_num
      _ ≤ 2^(16*l) := two_pow_mono (by omega)
      _ ≤ _ := h₁
  · calc
      _ ≤ 2^(16*l+16) := h₂.le
      _ ≤ 2^(j*2) := two_pow_mono (by omega)
      _ = _ := pow_mul _ _ _

/-- Every sufficiently large geometric scale x contains many disjoint
dyadic blocks, all paid for by the phase mass of one longer interval. -/
theorem geometric_band_mass {a g : ℕ → ℕ} (ha : StrictMono a) (hm : Monotone g)
    (hp : ∀ i, 1 ≤ g i) {S : ℕ} (hslow : ∀ i, (g i)^16 ≤ S*(i+1))
    (hg : ∀ i, a (i+1)-a i ≤ (i+1)*g (i+1)) {θ : ℝ} {M : ℕ}
    (hwin : ∀ T : ℕ, T ≥ M → ∃ r : ℚ, r.den ≤ T ∧ T < r.den^6 ∧
      |θ-r| ≤ 1/(((T : ℝ)+1)*r.den)) {x : ℕ}
    (hx : 16 ≤ x) (hS : S ≤ x) (hM : M ≤ x) :
    (x : ℝ) ≤ 2048*(g (2^(72*x)) : ℝ)*
      ∑ i ∈ Ico (2^(10*x)) (2^(72*x)), phase (a i*θ) := by
  let T := 2^(96*x)
  have hTx : x ≤ T := (Nat.le_of_lt Nat.lt_two_pow_self).trans (two_pow_mono (by omega))
  obtain ⟨r,hr,hq,he⟩ := hwin T (hM.trans hTx)
  obtain ⟨l,hxl,hlx,hband⟩ := choose_scale_band hslow hx hS hq hr
  let w := fun i => phase (a i*θ)
  let C : ℝ := 2048*(g (2^(72*x)) : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpartial (m) (hm' : m ≤ 2*l) :
      (m : ℝ) ≤ C*∑ i ∈ Ico (2^(10*l)) (2^(10*l+m)), w i := by
    induction m with
    | zero => simp
    | succ m ih =>
      have prev := ih (by omega)
      let j := 10*l+m
      obtain ⟨h₁,h₂⟩ := hband j (by dsimp [j]; omega) (by dsimp [j]; omega)
      have hblock := dyadic_block_mass ha hm hp hg hr he (pow_pos (by decide : 0 < (2 : ℕ)) j) h₁ h₂
      have hpow : 2*(2^j) = 2^(j+1) := by rw [pow_succ, mul_comm]
      rw [hpow] at hblock
      have hj : j+1 ≤ 72*x := by dsimp [j]; omega
      have hcg : 2048*(g (2^(j+1)) : ℝ) ≤ C :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hm (two_pow_mono hj)) (by norm_num)
      have hmass := hblock.trans (mul_le_mul_of_nonneg_right hcg (sum_nonneg (fun i _ =>
        show 0 ≤ w i from abs_nonneg _)))
      change 1 ≤ C*∑ i ∈ Ico (2^j) (2^(j+1)), w i at hmass
      change (m : ℝ) ≤ C*∑ i ∈ Ico (2^(10*l)) (2^j),w i at prev
      change ((m+1 : ℕ) : ℝ) ≤ C*∑ i ∈ Ico (2^(10*l)) (2^(j+1)),w i
      rw [← sum_Ico_consecutive w (two_pow_mono (show 10*l ≤ j by dsimp [j]; omega))
        (two_pow_mono (Nat.le_succ j)), mul_add]
      push_cast
      linarith only [prev,hmass]
  have hsubset : Ico (2^(10*l)) (2^(10*l+2*l)) ⊆ Ico (2^(10*x)) (2^(72*x)) :=
    Ico_subset_Ico (two_pow_mono (by omega)) (two_pow_mono (by omega))
  exact (show (x : ℝ) ≤ ((2*l : ℕ) : ℝ) by exact_mod_cast (show x ≤ 2*l by omega)).trans
    ((hpartial (2*l) le_rfl).trans (mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ => show 0 ≤ w i from abs_nonneg _)) hC))

end JSP727
