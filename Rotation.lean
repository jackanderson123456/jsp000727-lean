import Mathlib

namespace JSP727

/-- A quantitative irrationality bound for the rotation by √2. -/
theorem sqrt_two_separation (q : ℕ) (hq : 0 < q) (z : ℤ) :
    1 ≤ (4*(q : ℝ))*|(q : ℝ)*Real.sqrt 2-z| := by
  let X := (q : ℝ)*Real.sqrt 2
  have hx : Irrational X := irrational_sqrt_two.natCast_mul hq.ne'
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hroot := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hX : X^2 = 2*(q : ℝ)^2 := by dsimp [X]; rw [mul_pow, hroot]; ring
  have hXpos : 0 ≤ X := by dsimp [X]; positivity
  have hsqrt : Real.sqrt 2 ≤ 3/2 := by nlinarith [Real.sqrt_nonneg 2]
  have hXbound : X ≤ (q : ℝ)*(3/2) :=
    mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg _)
  change 1 ≤ 4*(q : ℝ)*|X-z|
  by_cases hfar : 1 ≤ |X-z|
  · nlinarith [mul_le_mul hq1 hfar (by norm_num : (0:ℝ) ≤ 1) (Nat.cast_nonneg q)]
  have hNZ : (2*(q : ℤ)^2-z^2) ≠ 0 := by
    intro he
    have hr : 2*(q : ℝ)^2-(z : ℝ)^2 = 0 := by exact_mod_cast he
    have hm : (X-z)*(X+z) = 0 := by nlinarith
    rcases mul_eq_zero.mp hm with h | h
    · exact hx.ne_int z (by linarith)
    · exact hx.ne_int (-z) (by push_cast; linarith)
  have hnorm : (1 : ℝ) ≤ |2*(q : ℝ)^2-(z : ℝ)^2| := by exact_mod_cast Int.one_le_abs hNZ
  have hplus : |X+z| ≤ 4*(q : ℝ) := by
    obtain ⟨hl,hu⟩ := abs_lt.mp (lt_of_not_ge hfar)
    rw [abs_le]
    constructor <;> linarith
  calc
    1 ≤ |2*(q : ℝ)^2-(z : ℝ)^2| := hnorm
    _ = |X+z| * |X-z| := by rw [← abs_mul]; congr 1; nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hplus (abs_nonneg _)

private theorem residue_grid (r : ℚ) (J : ℤ) :
    ∃ k : ℕ, k < r.den ∧ ∃ l : ℤ, (k : ℤ)*r.num = J+r.den*l := by
  haveI : NeZero r.den := ⟨r.den_nz⟩
  obtain ⟨u,v,huv⟩ := r.isCoprime_num_den
  let w := (u*J : ℤ)
  let k := (w : ZMod r.den).val
  have he : (k : ZMod r.den) = (w : ZMod r.den) := ZMod.natCast_zmod_val _
  have hr : (k : ZMod r.den)*(r.num : ZMod r.den) = (J : ZMod r.den) := by
    have h := congrArg (fun z : ℤ => (z : ZMod r.den)) huv
    push_cast at h
    simp at h
    rw [he]
    dsimp [w]
    push_cast
    linear_combination (J : ZMod r.den)*h
  have hdiv : (r.den : ℤ) ∣ (k : ℤ)*r.num-J :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa using hr.symm)
  obtain ⟨l,hl⟩ := hdiv
  exact ⟨k,ZMod.val_lt _,l,by linarith⟩

/-- Starting anywhere, at most 32D additional steps reach a fractional
part strictly between 1/D and 2/D. -/
theorem sqrt_two_visit (D start : ℕ) (hD : 3 ≤ D) :
    ∃ n : ℕ, start ≤ n ∧ n ≤ start+32*D ∧
      1/(D : ℝ) < Int.fract (n*Real.sqrt 2) ∧ Int.fract (n*Real.sqrt 2) < 2/(D : ℝ) := by
  let M := 32*D
  have hM : 0 < M := by dsimp [M]; omega
  obtain ⟨r,herr,hrden⟩ := Real.exists_rat_abs_sub_le_and_den_le (Real.sqrt 2) hM
  let q := r.den
  have hq : (0 : ℝ) < q := by exact_mod_cast r.pos
  have hMr : (0 : ℝ) < M+1 := by positivity
  have hc : (r : ℝ)*q = r.num := by dsimp [q]; rw [Rat.cast_def]; field_simp
  have hscaled : |(q : ℝ)*Real.sqrt 2-r.num| ≤ 1/((M:ℝ)+1) := by
    rw [← hc, mul_comm (q:ℝ), ← sub_mul, abs_mul, abs_of_pos hq]
    apply (le_div_iff₀ hMr).mpr
    have hsmall := (le_div_iff₀ (mul_pos hMr hq)).mp herr
    dsimp [q] at *
    linarith only [show |Real.sqrt 2-r| * r.den*((M:ℝ)+1) =
      |Real.sqrt 2-r| * (((M:ℝ)+1)*r.den) by ring, hsmall]
  have hlower : 8*(D : ℝ) < q := by
    have hsep := sqrt_two_separation q r.pos r.num
    have htop := hsep.trans (mul_le_mul_of_nonneg_left hscaled (by positivity))
    rw [mul_one_div, le_div_iff₀ hMr] at htop
    dsimp [M] at htop
    push_cast at htop
    linarith
  let target := 3/(2*(D : ℝ))
  let J := ⌊(q : ℝ)*(target-(start:ℝ)*Real.sqrt 2)⌋
  obtain ⟨k,hk,l,hl⟩ := residue_grid r J
  have hdelta : |(k : ℝ)*((q : ℝ)*Real.sqrt 2-r.num)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ (k:ℝ)*(1/((M:ℝ)+1)) := by gcongr
      _ ≤ _ := by rw [mul_one_div, div_le_one hMr]; exact_mod_cast (show k ≤ M+1 by omega)
  have hfloor := Int.floor_le ((q:ℝ)*(target-(start:ℝ)*Real.sqrt 2))
  have hceil := Int.lt_floor_add_one ((q:ℝ)*(target-(start:ℝ)*Real.sqrt 2))
  change (J:ℝ) ≤ _ at hfloor
  change _ < (J:ℝ)+1 at hceil
  have hlr : (k : ℝ)*r.num = (J:ℝ)+(q:ℝ)*l := by exact_mod_cast hl
  let y := ((start+k : ℕ):ℝ)*Real.sqrt 2-l
  have hbox : -2 < (q:ℝ)*(y-target) ∧ (q:ℝ)*(y-target) ≤ 1 := by
    obtain ⟨hδ₁,hδ₂⟩ := abs_le.mp hdelta
    dsimp [y]
    push_cast
    constructor <;> nlinarith only [hfloor,hceil,hlr,hδ₁,hδ₂]
  have hDr : (0:ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hshift : target - 1/D = 1/(2*(D:ℝ)) ∧ 2/D - target = 1/(2*(D:ℝ)) := by
    dsimp [target]; constructor <;> field_simp <;> ring
  have hmargin : 2 < (q:ℝ)*(1/(2*(D:ℝ))) := by
    rw [mul_one_div, lt_div_iff₀ (by positivity)]; linarith
  have hb : 1/(D:ℝ) < y ∧ y < 2/(D:ℝ) := by
    constructor
    · by_contra! hh
      have he := congrArg (fun t : ℝ => (q:ℝ)*t) hshift.1
      nlinarith only [mul_le_mul_of_nonneg_left hh hq.le, hbox.1, hmargin, he]
    · by_contra! hh
      have he := congrArg (fun t : ℝ => (q:ℝ)*t) hshift.2
      nlinarith only [mul_le_mul_of_nonneg_left hh hq.le, hbox.2, hmargin, he]
  have hfr : Int.fract (((start+k:ℕ):ℝ)*Real.sqrt 2) = y := by
    apply Int.fract_eq_iff.mpr
    exact ⟨(by positivity : (0:ℝ) < 1/D).le.trans hb.1.le,
      hb.2.trans ((div_lt_one hDr).mpr (by exact_mod_cast (show 2 < D by omega))),
      l,by dsimp [y]; ring⟩
  refine ⟨start+k,by omega,by dsimp [M] at hrden; omega,?_⟩
  rwa [hfr]

end JSP727
