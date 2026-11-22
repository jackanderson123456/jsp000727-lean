import SequenceSets

namespace JSP727

open Finset

/-- The prefix growth test still holds with any subpower factor in the
gap envelope. Only a square-root upper bound on that factor is needed here. -/
theorem syndetic_of_growth_envelope {a g : ℕ → ℕ} (ha : StrictMono a) (hpos : ∀ i, 0 < a i)
    (hp : ∀ i, 1 ≤ g i) {S : ℕ} (hs : ∀ i, (g i)^16 ≤ S*(i+1))
    (hg : ∀ i, a (i+1)-a i ≤ (i+1)*g (i+1)) : SyndeticSums (Set.range a) := by
  let D := 128*(S+1)
  apply syndetic_of_prefix_growth ha hpos (H := a D)
  intro n
  cases n with
  | zero => simpa using ha.monotone (Nat.zero_le D)
  | succ n =>
    by_cases hn : n < D
    · exact (ha.monotone hn).trans (Nat.le_add_left _ _)
    have hD : 128*(S+1) ≤ n := by simpa [D] using Nat.le_of_not_gt hn
    let G := g (n+1)
    have hsq : G^2 ≤ S*(n+2) := (Nat.pow_le_pow_right (hp _) (by decide : 2 ≤ 16)).trans (hs _)
    have hsmall : 8*G ≤ n := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
      calc
        (8*G)^2 = 64*G^2 := by ring
        _ ≤ 64*(S*(n+2)) := Nat.mul_le_mul_left _ hsq
        _ ≤ (128*S)*n := by
          have h := Nat.mul_le_mul_left S (show n+2 ≤ 2*n by omega)
          nlinarith only [h]
        _ ≤ n^2 := by simpa [sq] using Nat.mul_le_mul_right n (show 128*S ≤ n by omega)
    let k := n/2
    have hlen : n+1 ≤ 3*(n-k) := by dsimp [k]; omega
    have hlow : 3*G ≤ k := by dsimp [k]; omega
    have hgap : (n+1)*G ≤ (n-k)*k := by
      calc
        _ ≤ (3*(n-k))*G := Nat.mul_le_mul_right _ hlen
        _ = (n-k)*(3*G) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hlow
    have hsum : (n-k)*k ≤ ∑ i ∈ range n, a i := by
      calc
        _ = ∑ _ ∈ Ico k n, k := by simp [Nat.card_Ico]
        _ ≤ ∑ i ∈ Ico k n, a i := sum_le_sum (fun i hi => (mem_Ico.mp hi).1.trans (ha.id_le i))
        _ ≤ _ := sum_le_sum_of_subset (fun i hi => mem_range.mpr (mem_Ico.mp hi).2)
    have hstep := (hg n).trans (hgap.trans hsum)
    rw [sum_range_succ]
    omega

end JSP727
