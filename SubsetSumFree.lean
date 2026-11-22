import Mathlib

/-! Counting translates in a subset-sum-free sequence, following Erdős's
argument as presented in Samuel Korsky, *An Integral Criterion for Gaps in
Sum-Free Sequences*, Lemma 3.1 and Proposition 3.3. All indices start at zero. -/

namespace JSP727

open Finset

/-- No term is a sum of distinct terms with smaller indices. -/
def SubsetSumFree (a : ℕ → ℕ) : Prop :=
  ∀ n (s : Finset ℕ), (∀ i ∈ s, i < n) → ∑ i ∈ s, a i ≠ a n

theorem unique_representation {a : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (hf : SubsetSumFree a) {n : ℕ} {s : Finset ℕ}
    (hs : ∑ j ∈ s, a j = a n) : s = {n} := by
  have hmem : n ∈ s := by
    by_contra hn
    apply hf n s _ hs
    intro i hi
    have hb := single_le_sum (f := a) (fun j _ => Nat.zero_le (a j)) hi
    exact lt_of_le_of_ne (ha.le_iff_le.mp (hs ▸ hb)) (fun h => hn (h ▸ hi))
  have hrest : ∑ j ∈ s.erase n, a j = 0 := by
    have he := sum_erase_add s a hmem
    omega
  ext i
  rw [mem_singleton]
  constructor
  · intro hi
    by_contra hne
    have hb := single_le_sum (f := a) (fun j _ => Nat.zero_le (a j))
      (mem_erase.mpr ⟨hne,hi⟩)
    have := hpos i
    omega
  · rintro rfl
    exact hmem

theorem SubsetSumFree.comp {a f : ℕ → ℕ} (hf : SubsetSumFree a) (hm : StrictMono f) :
    SubsetSumFree (a ∘ f) := by
  intro n s hs he
  apply hf (f n) (s.image f) ?_ ?_
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact hm (hs i hi)
  · simpa [sum_image hm.injective.injOn, Function.comp_def] using he

private theorem translates_ne {a : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (hf : SubsetSumFree a)
    {i j x y : ℕ} (hij : i < j) (hjx : j ≤ x) :
    a x + ∑ k ∈ range j, a k ≠ a y + ∑ k ∈ range i, a k := by
  intro heq
  have hsplit := sum_range_add_sum_Ico a hij.le
  have hsum : a x + ∑ k ∈ Ico i j, a k = a y := by omega
  have hbound := single_le_sum (f := a) (fun k _ => Nat.zero_le (a k))
    (mem_Ico.mpr ⟨le_rfl, hij⟩ : i ∈ Ico i j)
  have hxy : x < y := ha.lt_iff_lt.mp (by have := hpos i; omega)
  apply hf y (insert x (Ico i j))
  · intro k hk
    rcases mem_insert.mp hk with rfl | hk
    · exact hxy
    · exact (mem_Ico.mp hk).2.trans_le (hjx.trans hxy.le)
  · rwa [sum_insert (by simp [Nat.not_lt.mpr hjx] : x ∉ Ico i j)]

/-- The r+1 partial sums of the first r terms translate the following
interval of indices into disjoint sets of positive integers. -/
theorem disjoint_translates_bound {a : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (hf : SubsetSumFree a) (r n : ℕ) :
    (r + 1) * (n - r) ≤ a (n - 1) + ∑ k ∈ range r, a k := by
  let dom := range (r+1) ×ˢ Ico r n
  let target := Icc 1 (a (n-1) + ∑ k ∈ range r, a k)
  let f := fun p : ℕ × ℕ => a p.2 + ∑ k ∈ range p.1, a k
  have maps : Set.MapsTo f (dom : Set (ℕ × ℕ)) (target : Set ℕ) := by
    rintro ⟨j,x⟩ hp
    obtain ⟨hj,hx,hxn⟩ : j < r+1 ∧ r ≤ x ∧ x < n := by simpa [dom] using hp
    refine mem_Icc.mpr ⟨(hpos x).trans_le (Nat.le_add_right _ _), ?_⟩
    apply Nat.add_le_add (ha.monotone (by omega : x ≤ n-1))
    apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega : j ≤ r))
    intros
    exact Nat.zero_le _
  have inj : Set.InjOn f (dom : Set (ℕ × ℕ)) := by
    rintro ⟨i,x⟩ hp ⟨j,y⟩ hq heq
    obtain ⟨hi,hrx,_⟩ : i < r+1 ∧ r ≤ x ∧ x < n := by simpa [dom] using hp
    obtain ⟨hj,hry,_⟩ : j < r+1 ∧ r ≤ y ∧ y < n := by simpa [dom] using hq
    change a x + ∑ k ∈ range i, a k = a y + ∑ k ∈ range j, a k at heq
    rcases lt_trichotomy i j with h | rfl | h
    · exact (translates_ne ha hpos hf h (by omega : j ≤ y) heq.symm).elim
    · have := ha.injective (Nat.add_right_cancel heq)
      simp [this]
    · exact (translates_ne ha hpos hf h (by omega : i ≤ x) heq).elim
  simpa [dom, target, Nat.card_Icc] using card_le_card_of_injOn f maps inj

/-- The exceptional indices for a modulus, counted on every finite prefix. -/
def FewExceptions (a : ℕ → ℕ) (d : ℕ) : Prop :=
  ∀ n, Nat.count (fun i => ¬ d ∣ a i) n ≤ d

private theorem split_count (a : ℕ → ℕ) (d n : ℕ) :
    Nat.count (fun i => d ∣ a i) n + Nat.count (fun i => ¬ d ∣ a i) n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : d ∣ a n <;> simp [Nat.count_succ, h] <;> omega

noncomputable def quotientSeq (a : ℕ → ℕ) (d i : ℕ) : ℕ :=
  a (Nat.nth (fun j => d ∣ a j) i) / d

theorem divisible_indices {a : ℕ → ℕ} {d : ℕ} (h : FewExceptions a d) :
    let f := Nat.nth (fun j => d ∣ a j)
    StrictMono f ∧ (∀ i, f i ≤ i+d) ∧ ∀ i, d * quotientSeq a d i = a (f i) := by
  let p := fun i => d ∣ a i
  have hinf : (setOf p).Infinite := by
    intro hfin
    let n := hfin.toFinset.card + d + 1
    have hle := Nat.count_le_card (p := p) hfin n
    have := split_count a d n
    have := h n
    dsimp [p, n] at *
    omega
  refine ⟨Nat.nth_strictMono hinf, ?_, ?_⟩
  · intro i
    have := h (i + d + 1)
    have := split_count a d (i + d + 1)
    exact Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count
      (p := p) (show i < Nat.count p (i+d+1) by dsimp [p]; omega))
  · intro i
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.nth_mem_of_infinite hinf i)

/-- Deleting the exceptional terms and dividing by d preserves sum-freeness.
The kth remaining term comes from an original index at most k+d. -/
theorem normalized_subsequence {a : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (hf : SubsetSumFree a)
    {d : ℕ} (hd : 0 < d) (h : FewExceptions a d) :
    StrictMono (quotientSeq a d) ∧ (∀ i, 0 < quotientSeq a d i) ∧
        SubsetSumFree (quotientSeq a d) ∧ ∀ i, d * quotientSeq a d i ≤ a (i+d) := by
  let p := fun i => d ∣ a i
  let f := Nat.nth p
  let b := fun i => a (f i) / d
  obtain ⟨hidx, hle, heq⟩ := divisible_indices h
  change StrictMono b ∧ (∀ i, 0 < b i) ∧ SubsetSumFree b ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hlt := ha (hidx hij)
    rw [← heq, ← heq] at hlt
    exact (Nat.mul_lt_mul_left hd).mp hlt
  · intro i
    have hgt := hpos (f i)
    rw [← heq] at hgt
    exact Nat.pos_of_mul_pos_left hgt
  · intro n s hs hsum
    change ∑ i ∈ s, quotientSeq a d i = quotientSeq a d n at hsum
    apply hf (f n) (s.image f)
    · intro k hk
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
      exact hidx (hs i hi)
    · rw [sum_image (fun _ _ _ _ hxy => hidx.injective hxy), ← heq,
          ← hsum, mul_sum]
      exact sum_congr rfl (fun i _ => (heq i).symm)
  · intro i
    rw [heq]
    apply ha.monotone
    exact hle i

/-- A quantitative quadratic-growth case of Korsky's Proposition 3.3.
In particular only finitely many moduli have at most d exceptional terms. -/
theorem exceptional_divisor_bound {a : ℕ → ℕ} (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (hf : SubsetSumFree a) {C d : ℕ}
    (hg : ∀ i, a i ≤ C * (i+1)^2) (hd : 0 < d) (h : FewExceptions a d) :
    d ≤ C * (4*C+3)^2 := by
  let b := quotientSeq a d
  obtain ⟨hb, hbpos, hbf, hbound⟩ := normalized_subsequence ha hpos hf hd h
  let T := 4*C+2
  have hbnd (i : ℕ) : d * b i ≤ C * (i+d+1)^2 :=
    (hbound i).trans (hg _)
  have hsmall (i : ℕ) (hi : i ∈ range d) : b i ≤ 4*C*d := by
    apply (Nat.le_of_mul_le_mul_left · hd)
    have hir := mem_range.mp hi
    calc
      d * b i ≤ C * (i+d+1)^2 := hbnd i
      _ ≤ C * (2*d)^2 := by gcongr; omega
      _ = d * (4*C*d) := by ring
  have hsum : ∑ i ∈ range d, b i ≤ d * (4*C*d) := by
    simpa using sum_le_sum hsmall
  have hT : 2 ≤ T := by dsimp [T]; omega
  have hn : 0 < T*d := Nat.mul_pos (by omega) hd
  have hlarge : b (T*d-1) ≤ C*(T+1)^2*d := by
    apply (Nat.le_of_mul_le_mul_left · hd)
    calc
      d * b (T*d-1) ≤ C * (T*d-1+d+1)^2 := hbnd _
      _ = C * ((T+1)*d)^2 := by
        rw [show (T+1)*d = T*d+d by ring, show T*d-1+d+1 = T*d+d by omega]
      _ = d * (C*(T+1)^2*d) := by ring
  have hcount := disjoint_translates_bound hb hbpos hbf d (T*d)
  have hdif : T*d-d = (4*C+1)*d := by
    dsimp [T]
    rw [show 4*C+2 = (4*C+1)+1 by omega, Nat.add_mul]
    omega
  rw [hdif] at hcount
  have hprod : d * d ≤ (C*(T+1)^2) * d := by nlinarith
  simpa [T, Nat.add_assoc] using (le_of_mul_le_mul_right hprod hd)

end JSP727
