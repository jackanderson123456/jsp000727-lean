import Completeness
import Supports

namespace JSP727

open Filter

set_option maxHeartbeats 1600000

/-- No infinite increasing sequence of positive integers that is subset-sum-free
can have a uniform linear upper bound on its consecutive gaps. -/
theorem no_linear_gaps {a : ℕ → ℕ} (ha : StrictMono a) (hpos : ∀ i, 0 < a i)
    (hf : SubsetSumFree a) (K : ℕ) (hK : 0 < K)
    (hg : ∀ i, a (i+1)-a i ≤ K*(i+1)) : False := by
  classical
  let ev := fun i : ℕ => 2*i
  let c := a ∘ ev
  have he : StrictMono ev := by intro i j h; dsimp [ev]; omega
  have hcm : StrictMono c := ha.comp he
  have hcp (i) : 0 < c i := hpos _
  have hcf : SubsetSumFree c := hf.comp he
  let L := 2*K*(2+0)
  have hcg (i) : c (i+1)-c i ≤ L*(i+1) := by
    simpa [c,ev,L] using affine_linear_gaps hg 2 0 i
  obtain ⟨d,hd,hfew,hmod⟩ := exists_modular_normalization hcm hcp hcf
    (quadratic_bound_of_linear_gaps hcg)
  let b := quotientSeq c d
  obtain ⟨hbm,hbp,_,_⟩ := normalized_subsequence hcm hcp hcf hd hfew
  let f := Nat.nth (fun j => d ∣ c j)
  have hbe (i) : d*b i = a (2*f i) := (divisible_indices hfew).2.2 i
  let C := Set.range b
  let B := oddBlocks a hd
  let v := B.value
  have hvm : StrictMono v := B.value_strictMono ha hd
  have hvp (i) : 0 < v i := (hpos _).trans_le (B.value_bounds ha hd i).1
  let g := fun r i : ℕ => v (3*i+r+1)
  let A := fun r => Set.range (g r)
  have hsyn (r : ℕ) : SyndeticSums (A r) := by
    have hm : StrictMono (g r) := hvm.comp (by intro i j h; change 3*i+r+1 < 3*j+r+1; omega)
    apply syndetic_of_linear_gaps hm (fun i => hvp _) (K := 3*(16*K*(d^2)^2)*(3+(r+1)))
    intro i
    simpa only [g, v, Nat.add_assoc] using
      affine_linear_gaps (B.value_linear_gaps ha hd hg) 3 (r+1) i
  have dis {r s : ℕ} (hr : r < 3) (hs : s < 3) (hne : r ≠ s) : Disjoint (A r) (A s) := by
    rw [Set.disjoint_left]
    rintro x ⟨i,rfl⟩ ⟨j,hj⟩
    have he := hvm.injective hj
    change 3*j+s+1 = 3*i+r+1 at he
    omega
  have disC (r : ℕ) : Disjoint (A r) C := by
    rw [Set.disjoint_left]
    rintro x ⟨i,rfl⟩ ⟨j,hj⟩
    apply B.no_even_collision ha hpos hf (3*i+r+1) (f j)
    exact (congrArg (d*·) hj.symm).trans (hbe j)
  have hph (θ : ℝ) (hθ : Irrational θ) :
      Tendsto (Erdos254.phasePartialSum C θ) atTop atTop := by
    apply sequence_phase_divergence hbm hbp (K := L*(d+1)^2) _ (quotient_linear_gaps hd hfew hcg) hθ
    dsimp [L]
    positivity
  let U := (((A 0 ∪ A 1) ∪ C) ∪ A 2)
  obtain ⟨N,hN⟩ := four_sets_complete (A 0) (A 1) (A 2) C
    (dis (r := 0) (s := 1) (by decide) (by decide) (by decide))
    (dis (r := 0) (s := 2) (by decide) (by decide) (by decide))
    (dis (r := 1) (s := 2) (by decide) (by decide) (by decide)) (disC 0) (disC 1) (disC 2)
    (hsyn 0) (hsyn 1) (hsyn 2) hph (fun q hq z => covers_range hbm (hmod q hq) z)
  have hsrcB (r x : ℕ) (hx : x ∈ A r) : ∃ s, B.Source x s := by
    obtain ⟨i,rfl⟩ := hx
    exact ⟨_, Or.inr ⟨3*i+r+1, by omega, rfl, rfl⟩⟩
  have hsrc (x : ℕ) (hx : x ∈ U) : ∃ s, B.Source x s := by
    rcases hx with ((hx|hx)|hx)|hx
    · exact hsrcB 0 _ hx
    · exact hsrcB 1 _ hx
    · obtain ⟨j,rfl⟩ := hx
      exact ⟨_,Or.inl ⟨f j,rfl,hbe j⟩⟩
    · exact hsrcB 2 _ hx
  let j := N+v 0
  have hbig : N+v 0 ≤ b j := hbm.id_le j
  obtain ⟨s,hs,heq⟩ := B.flatten_with_reserve hd hsrc (hN (b j-v 0) (by omega))
  apply B.reserve_prevents_even_sum ha hpos hf hd hs (f j)
  rw [heq, show B.value 0 + (b j-v 0) = b j by change v 0+(b j-v 0) = _; omega, hbe j]

end JSP727
