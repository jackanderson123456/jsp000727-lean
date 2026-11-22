import Blocks
import PrefixScarcity
import PhasePacking

namespace JSP727

/-- Allow a constant multiple both outside the gap bound and in the
argument of its nondecreasing factor. -/
def ControlledGaps (F a : ℕ → ℕ) : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∀ i, a (i+1)-a i ≤ K*(i+1)*F (K*(i+1))

private theorem gap_window {F a : ℕ → ℕ} (hm : Monotone F) {K : ℕ}
    (h : ∀ i, a (i+1)-a i ≤ K*(i+1)*F (K*(i+1))) {u v : ℕ} (huv : u ≤ v) :
    a v-a u ≤ (v-u)*(K*v*F (K*v)) := by
  have aux (j : ℕ) (hj : u+j ≤ v) : a (u+j) ≤ a u + j*(K*v*F (K*v)) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h₁ := ih (by omega)
      have h₂ := h (u+j)
      have hK := Nat.mul_le_mul_left K hj
      have hmono := Nat.mul_le_mul hK (hm hK)
      simp only [← Nat.add_assoc] at hmono ⊢
      rw [Nat.succ_mul]
      omega
  have h' := aux (v-u) (by omega)
  rw [Nat.add_sub_of_le huv] at h'
  omega

private theorem controlled_of_windows {F a b : ℕ → ℕ} (hm : Monotone F)
    (hg : ControlledGaps F a) {L : ℕ}
    (hwin : ∀ i, ∃ u v, u ≤ v ∧ v-u ≤ L ∧ v ≤ L*(i+1) ∧ b (i+1)-b i ≤ a v-a u) :
    ControlledGaps F b := by
  obtain ⟨K,hK,h⟩ := hg
  let C := (L+1)^2*K
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro i
  obtain ⟨u,v,huv,hlen,hend,hb⟩ := hwin i
  have hKend : K*v ≤ C*(i+1) := by
    calc
      _ ≤ K*(L*(i+1)) := Nat.mul_le_mul_left _ hend
      _ ≤ _ := by dsimp [C]; nlinarith [Nat.zero_le (K*L^2*(i+1)),Nat.zero_le (K*L*(i+1))]
  have hm₁ : (v-u)*(K*v) ≤ C*(i+1) := by
    calc
      _ ≤ L*(K*(L*(i+1))) := Nat.mul_le_mul hlen (Nat.mul_le_mul_left _ hend)
      _ ≤ _ := by dsimp [C]; nlinarith [Nat.zero_le (K*L*(i+1))]
  exact hb.trans ((gap_window hm h huv).trans (by
    rw [← mul_assoc]
    exact Nat.mul_le_mul hm₁ (hm hKend)))

theorem ControlledGaps.affine {a F : ℕ → ℕ} (hg : ControlledGaps F a)
    (hm : Monotone F) (t c : ℕ) : ControlledGaps F (fun i => a (t*i+c)) := by
  apply controlled_of_windows hm hg (L := t+c)
  intro i
  refine ⟨t*i+c,t*(i+1)+c,?_,?_,?_,le_rfl⟩
  all_goals rw [Nat.mul_add, Nat.mul_one]
  · omega
  · omega
  · nlinarith

theorem ControlledGaps.quotient {F a : ℕ → ℕ} (hg : ControlledGaps F a)
    (hm : Monotone F) {d : ℕ} (hd : 0 < d) (h : FewExceptions a d) :
    ControlledGaps F (quotientSeq a d) := by
  let f := Nat.nth (fun j => d ∣ a j)
  obtain ⟨hfm,hle,heq⟩ := divisible_indices h
  apply controlled_of_windows hm hg (L := d+1)
  intro i
  have h₁ : i ≤ f i := hfm.id_le i
  have h₂ : f (i+1) ≤ i+1+d := hle _
  refine ⟨f i,f (i+1),hfm.monotone (Nat.le_succ _),by omega,by nlinarith,?_⟩
  calc
    _ ≤ d*(quotientSeq a d (i+1)-quotientSeq a d i) := Nat.le_mul_of_pos_left _ hd
    _ = _ := by rw [Nat.mul_sub, heq, heq]

theorem ControlledGaps.odd_blocks {F a : ℕ → ℕ} (hg : ControlledGaps F a)
    (hm : Monotone F) (ha : StrictMono a) {d : ℕ} (hd : 0 < d) (B : OddBlocks a d) :
    ControlledGaps F B.value := by
  apply controlled_of_windows hm hg (L := 4*d^2)
  intro i
  let u := 2*(i*d^2)
  let v := 2*((i+1+1)*d^2)
  have hu : a u ≤ B.value i := (B.value_bounds ha hd i).1
  have hv : B.value (i+1) ≤ a v := (B.value_bounds ha hd (i+1)).2.le
  have he : v = u+4*d^2 := by dsimp [u,v]; ring
  refine ⟨u,v,by omega,by omega,?_,by omega⟩
  dsimp [v]; nlinarith

/-- A single dilated envelope simultaneously bounds the gaps and the values
and inherits the subpower bound and divergence of the reciprocal series. -/
theorem envelope_of_controlled {F a : ℕ → ℕ} (hm : Monotone F) (hp : ∀ i, 1 ≤ F i)
    {S : ℕ} (hslow : ∀ i, (F i)^16 ≤ S*(i+1))
    (hdiv : ¬ Summable (fun j : ℕ => 1/(F (2^j) : ℝ))) (hc : ControlledGaps F a) :
    ∃ g : ℕ → ℕ, Monotone g ∧ (∀ i, 1 ≤ g i) ∧ (∃ A, ∀ i, (g i)^16 ≤ A*(i+1)) ∧
      (¬ Summable (fun j : ℕ => 1/(g (2^j) : ℝ))) ∧
      (∀ i, a (i+1)-a i ≤ (i+1)*g (i+1)) ∧ ∀ i, a i ≤ g (i+1)*(i+1)^2 := by
  obtain ⟨K,hK,h⟩ := hc
  let B := a 0+K+1
  let g := fun i => B*F (K*i)
  have hB : 0 < B := by dsimp [B]; omega
  have hgm : Monotone g := fun _ _ hi => Nat.mul_le_mul_left _ (hm (Nat.mul_le_mul_left _ hi))
  have hgp (i) : 1 ≤ g i := Nat.mul_pos hB (hp _)
  refine ⟨g,hgm,hgp,⟨B^16*S*(K+1),?_⟩,?_,?_,?_⟩
  · intro i
    calc
      _ = B^16*(F (K*i))^16 := mul_pow _ _ _
      _ ≤ B^16*(S*(K*i+1)) := Nat.mul_le_mul_left _ (hslow _)
      _ ≤ _ := by nlinarith [Nat.zero_le (B^16*S*i),Nat.zero_le (B^16*S*K)]
  · intro hs
    apply hdiv
    apply (summable_nat_add_iff K).mp
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hs.mul_left (B : ℝ))
    intro j
    have harg : K*2^j ≤ 2^(j+K) := by
      rw [pow_add, mul_comm (2^j)]
      exact Nat.mul_le_mul_right _ (Nat.le_of_lt Nat.lt_two_pow_self)
    have hsmp : 1/(F (2^(j+K)) : ℝ) ≤ 1/(F (K*2^j) : ℝ) :=
      one_div_le_one_div_of_le (by exact_mod_cast hp _) (by exact_mod_cast hm harg)
    apply hsmp.trans
    dsimp [g]
    push_cast
    have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    field_simp
    exact le_rfl
  · intro i
    apply (h i).trans
    change K*(i+1)*F (K*(i+1)) ≤ (i+1)*(B*F (K*(i+1)))
    have hKB : K ≤ B := by dsimp [B]; omega
    simpa only [mul_assoc,mul_left_comm,mul_comm] using
      Nat.mul_le_mul_right ((i+1)*F (K*(i+1))) hKB
  · intro i
    have hwin := gap_window hm h (Nat.zero_le i)
    simp only [Nat.sub_zero] at hwin
    have hval : a i ≤ a 0+i*(K*i*F (K*i)) := by omega
    have hF := hm (Nat.mul_le_mul_left K (Nat.le_succ i))
    have h₁ : a 0 ≤ a 0*(F (K*(i+1))*(i+1)^2) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos (hp _) (by positivity))
    have h₂ : i*(K*i*F (K*i)) ≤ K*(F (K*(i+1))*(i+1)^2) := by
      calc
        _ = K*(F (K*i)*i^2) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul hF (Nat.pow_le_pow_left (Nat.le_succ i) 2))
    apply hval.trans
    dsimp [g,B]
    nlinarith [Nat.zero_le (F (K*(i+1))*(i+1)^2)]

end JSP727
