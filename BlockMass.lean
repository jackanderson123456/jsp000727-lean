import PhasePacking

namespace JSP727

open Finset

private theorem gap_span {a : ℕ → ℕ} {H n : ℕ}
    (hb : ∀ i < n, a (i+1)-a i ≤ H) {u v : ℕ} (hu : u ≤ v) (hv : v ≤ n) :
    a v-a u ≤ (v-u)*H := by
  have aux (k) (hk : u+k ≤ n) : a (u+k) ≤ a u+k*H := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h₁ := ih (by omega)
      have h₂ := hb (u+k) (by omega)
      rw [← Nat.add_assoc, Nat.succ_mul]
      omega
  have h := aux (v-u) (by omega)
  rw [Nat.add_sub_of_le hu] at h
  omega

/-- A dyadic block on which the denominator dominates the largest gap,
and is at most the square of the block length, carries phase mass. -/
theorem dyadic_block_mass {a g : ℕ → ℕ} (ha : StrictMono a) (hm : Monotone g)
    (hp : ∀ i, 1 ≤ g i) (hg : ∀ i, a (i+1)-a i ≤ (i+1)*g (i+1))
    {θ : ℝ} {T n : ℕ} {r : ℚ} (hr : r.den ≤ T)
    (he : |θ-r| ≤ 1/(((T : ℝ)+1)*r.den))
    (hn : 0 < n) (hlo : 128*n*g (2*n) ≤ r.den) (hhi : r.den ≤ n^2) :
    1 ≤ 2048*(g (2*n) : ℝ)*∑ i ∈ Ico n (2*n), phase (a i*θ) := by
  let H := 2*n*g (2*n)
  let k := r.den / (64*H)
  let L := 16*k
  let t := n / L
  let w := fun i => phase (a i*θ)
  have hHn : n ≤ H := by
    exact (show n ≤ 2*n by omega).trans (Nat.le_mul_of_pos_right _ (hp _))
  have hH : 0 < H := hn.trans_le hHn
  have h64 : 0 < 64*H := by omega
  have hmult : 64*H = 128*n*g (2*n) := by dsimp [H]; ring
  have hk : 0 < k := Nat.div_pos (hmult ▸ hlo) h64
  have hL : 0 < L := by dsimp [L]; omega
  have hklow : k*(64*H) ≤ r.den := Nat.div_mul_le_self _ _
  have hkhi : r.den < (k+1)*(64*H) := by
    simpa only [k, mul_comm (64*H)] using Nat.lt_mul_div_succ r.den h64
  have hkhi' : r.den ≤ 128*H*k := by
    calc
      _ ≤ (k+1)*(64*H) := hkhi.le
      _ ≤ (2*k)*(64*H) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hLn : L ≤ n := by
    apply Nat.le_of_mul_le_mul_right (b := n) _ hn
    calc
      L*n ≤ L*H := Nat.mul_le_mul_left _ hHn
      _ ≤ k*(64*H) := by dsimp [L]; nlinarith [Nat.zero_le (k*H)]
      _ ≤ r.den := hklow
      _ ≤ n*n := by simpa [sq] using hhi
  have ht : 0 < t := Nat.div_pos hLn hL
  have htl : t*L ≤ n := Nat.div_mul_le_self _ _
  have hnlt : n < (t+1)*L := by simpa only [t, mul_comm L] using Nat.lt_mul_div_succ n hL
  have hntk : n ≤ 32*(t*k) := by
    calc
      _ ≤ (t+1)*L := hnlt.le
      _ ≤ (2*t)*L := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by dsimp [L]; ring
  have hb (i) (hi : i < 2*n) : a (i+1)-a i ≤ H :=
    (hg i).trans (Nat.mul_le_mul hi (hm hi))
  have hmass (j) (hj : j ≤ t) :
      (j : ℝ)*(4*(k : ℝ)^2) ≤ (r.den : ℝ)*∑ i ∈ Ico n (n+j*L), w i := by
    induction j with
    | zero => simp
    | succ j ih =>
      have prev := ih (by omega)
      let lo := n+j*L
      let hi := n+(j+1)*L
      have hstep : hi = lo+L := by dsimp [lo,hi]; ring
      have hhiEnd : hi ≤ 2*n := by
        have hjL := (Nat.mul_le_mul_right L hj).trans htl
        dsimp [hi]; omega
      have hc : (Ico lo hi).card = 16*k := by simp [hstep,Nat.card_Ico,L]
      have hspan (u) (hu : u ∈ Ico lo hi) (v) (hv : v ∈ Ico lo hi) (huv : u < v) :
          2*(a v-a u) ≤ r.den := by
        have huo := (mem_Ico.mp hu).1
        have hve := (mem_Ico.mp hv).2
        have hbound := gap_span hb huv.le (v := v) (by omega)
        have hlen : v-u ≤ L := by omega
        calc
          _ ≤ 2*(L*H) := Nat.mul_le_mul_left _ (hbound.trans (Nat.mul_le_mul_right _ hlen))
          _ ≤ k*(64*H) := by dsimp [L]; nlinarith [Nat.zero_le (k*H)]
          _ ≤ _ := hklow
      have hrun := phase_run_mass ha hk hc hr he hspan
      change 4*(k : ℝ)^2 ≤ (r.den : ℝ)*∑ i ∈ Ico lo hi, w i at hrun
      change (j : ℝ)*(4*(k : ℝ)^2) ≤ (r.den : ℝ)*∑ i ∈ Ico n lo, w i at prev
      change ((j+1 : ℕ) : ℝ)*(4*(k : ℝ)^2) ≤ (r.den : ℝ)*∑ i ∈ Ico n hi, w i
      rw [← sum_Ico_consecutive w (show n ≤ lo by dsimp [lo]; omega) (show lo ≤ hi by omega)]
      push_cast
      linarith only [hrun,prev,mul_add (r.den : ℝ) (∑ i ∈ Ico n lo,w i) (∑ i ∈ Ico lo hi,w i)]
  let P := ∑ i ∈ Ico n (2*n), w i
  have hP : 0 ≤ P := sum_nonneg (fun i _ => abs_nonneg _)
  have hsub : Ico n (n+t*L) ⊆ Ico n (2*n) := Ico_subset_Ico le_rfl (by omega)
  have htot := (hmass t le_rfl).trans (mul_le_mul_of_nonneg_left
    (sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => show 0 ≤ w i from abs_nonneg _))
    (Nat.cast_nonneg r.den : 0 ≤ (r.den : ℝ)))
  have hr' : (r.den : ℝ) ≤ 128*(H : ℝ)*k := by exact_mod_cast hkhi'
  have hupper := htot.trans (mul_le_mul_of_nonneg_right hr' hP)
  change (t : ℝ)*(4*(k : ℝ)^2) ≤ 128*(H : ℝ)*k*P at hupper
  have hc : (t : ℝ)*k ≤ 32*(H : ℝ)*P := by
    apply (mul_le_mul_iff_of_pos_right (show 0 < (k : ℝ) by exact_mod_cast hk)).mp
    nlinarith only [hupper]
  have hn' : (n : ℝ) ≤ 32*((t : ℝ)*k) := by exact_mod_cast hntk
  have hresult : (n : ℝ) ≤ 1024*(H : ℝ)*P := by linarith only [hn',hc]
  apply le_of_mul_le_mul_left (a := (n : ℝ)) _ (by exact_mod_cast hn)
  change (n : ℝ)*1 ≤ (n : ℝ)*(2048*(g (2*n) : ℝ)*P)
  change (n : ℝ) ≤ 1024*((2*n*g (2*n) : ℕ) : ℝ)*P at hresult
  push_cast at hresult
  nlinarith only [hresult]

end JSP727
