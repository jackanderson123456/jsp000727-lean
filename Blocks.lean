import Normalization

namespace JSP727

open Finset

/-- Bin k consists of odd indices 2j+1 with k*d² ≤ j < (k+1)*d².
Select d indices on which the sequence takes the same residue modulo d. -/
structure OddBlocks (a : ℕ → ℕ) (d : ℕ) where
  support : ℕ → Finset ℕ
  card (k) : (support k).card = d
  window (k i) : i ∈ support k →
    ∃ j, k*d^2 ≤ j ∧ j < (k+1)*d^2 ∧ i = 2*j+1
  divisible (k) : d ∣ ∑ i ∈ support k, a i

private theorem choose_bin (a : ℕ → ℕ) {d : ℕ} (hd : 0 < d) (k : ℕ) :
    ∃ s : Finset ℕ, s.card = d ∧
      (∀ i ∈ s, ∃ j, k*d^2 ≤ j ∧ j < (k+1)*d^2 ∧ i = 2*j+1) ∧
      d ∣ ∑ i ∈ s, a i := by
  classical
  haveI : NeZero d := ⟨hd.ne'⟩
  let f := fun j : ℕ => 2*j+1
  have hfinj : Function.Injective f := fun i j h => by dsimp [f] at h; omega
  let bin := (Ico (k*d^2) ((k+1)*d^2)).image f
  have hcard : bin.card = d*d := by
    simp [bin, card_image_of_injective _ hfinj, Nat.card_Ico, add_mul, pow_two]
  let residue := fun j => (a j : ZMod d)
  obtain ⟨r,_,hr⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := bin) (t := univ) (f := residue) (n := d) (fun _ _ => mem_univ _) univ_nonempty
    (by simp [ZMod.card, hcard])
  obtain ⟨s,hs,hsize⟩ := exists_subset_card_eq hr
  refine ⟨s,hsize,?_,?_⟩
  · intro i hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp (mem_filter.mp (hs hi)).1
    exact ⟨j,(mem_Ico.mp hj).1,(mem_Ico.mp hj).2,rfl⟩
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    calc
      ∑ i ∈ s, (a i : ZMod d) = ∑ i ∈ s, r := sum_congr rfl (fun _ hi => (mem_filter.mp (hs hi)).2)
      _ = 0 := by simp [hsize, nsmul_eq_mul]

noncomputable def oddBlocks (a : ℕ → ℕ) {d : ℕ} (hd : 0 < d) : OddBlocks a d where
  support k := (choose_bin a hd k).choose
  card k := (choose_bin a hd k).choose_spec.1
  window k := (choose_bin a hd k).choose_spec.2.1
  divisible k := (choose_bin a hd k).choose_spec.2.2

namespace OddBlocks

variable {a : ℕ → ℕ} {d : ℕ} (B : OddBlocks a d)

def value (k : ℕ) : ℕ := (∑ i ∈ B.support k, a i) / d

theorem value_eq (k : ℕ) : d*B.value k = ∑ i ∈ B.support k, a i :=
  Nat.mul_div_cancel' (B.divisible k)

theorem value_bounds (ha : StrictMono a) (hd : 0 < d) (k : ℕ) :
    a (2*(k*d^2)) ≤ B.value k ∧ B.value k < a (2*((k+1)*d^2)) := by
  have hne : (B.support k).Nonempty := card_pos.mp ((B.card k).symm ▸ hd)
  constructor
  · apply (Nat.le_of_mul_le_mul_left · hd)
    rw [B.value_eq]
    calc
      d*a (2*(k*d^2)) = ∑ _i ∈ B.support k, a (2*(k*d^2)) := by simp [B.card]
      _ ≤ _ := sum_le_sum (by
        intro i hi
        obtain ⟨j,hj,_,rfl⟩ := B.window k i hi
        exact ha.monotone (by omega))
  · apply (Nat.mul_lt_mul_left hd).mp
    rw [B.value_eq]
    calc
      _ < ∑ _i ∈ B.support k, a (2*((k+1)*d^2)) := sum_lt_sum_of_nonempty hne (by
        intro i hi
        obtain ⟨j,_,hj,rfl⟩ := B.window k i hi
        exact ha (by omega))
      _ = _ := by simp [B.card]

theorem value_strictMono (ha : StrictMono a) (hd : 0 < d) : StrictMono B.value :=
  strictMono_nat_of_lt_succ (fun i => (B.value_bounds ha hd i).2.trans_le
    (B.value_bounds ha hd (i+1)).1)

theorem support_disjoint {i j : ℕ} (hij : i ≠ j) : Disjoint (B.support i) (B.support j) := by
  rw [Finset.disjoint_left]
  intro n hni hnj
  obtain ⟨r,hr,hr',he⟩ := B.window i n hni
  obtain ⟨s,hs,hs',he'⟩ := B.window j n hnj
  rcases lt_or_gt_of_ne hij with h | h
  · have : (i+1)*d^2 ≤ j*d^2 := Nat.mul_le_mul_right (d^2) h
    omega
  · have : (j+1)*d^2 ≤ i*d^2 := Nat.mul_le_mul_right (d^2) h
    omega

theorem value_linear_gaps (ha : StrictMono a) (hd : 0 < d) {K : ℕ}
    (hg : ∀ i, a (i+1)-a i ≤ K*(i+1)) (k : ℕ) :
    B.value (k+1)-B.value k ≤ (16*K*(d^2)^2)*(k+1) := by
  let L := d^2
  let u := 2*(k*L)
  let v := 2*((k+1+1)*L)
  have hu : a u ≤ B.value k := (B.value_bounds ha hd k).1
  have hv : B.value (k+1) ≤ a v := (B.value_bounds ha hd (k+1)).2.le
  have hspan : v = u+4*L := by dsimp [u,v]; ring
  have hlim : v ≤ 4*L*(k+1) := by dsimp [v]; nlinarith
  calc
    _ ≤ a v-a u := by omega
    _ ≤ (v-u)*(K*v) := linear_gap_window hg (by omega)
    _ ≤ (4*L)*(K*(4*L*(k+1))) := by
      rw [show v-u=4*L by omega]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlim)
    _ = _ := by dsimp [L]; ring

end OddBlocks
end JSP727
