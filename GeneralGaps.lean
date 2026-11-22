import LinearGaps
import GapBounds
import Divergence
import SubpowerSums

namespace JSP727

open Filter Finset

/-- The divergent side of the gap criterion, in discrete form. A subpower
envelope is enough, without a slow-variation assumption. -/
theorem no_controlled_gaps {a F : ℕ → ℕ} (ha : StrictMono a) (hap : ∀ i, 0 < a i)
    (hf : SubsetSumFree a) (hm : Monotone F) (hp : ∀ i, 1 ≤ F i)
    {S : ℕ} (hslow : ∀ i, (F i)^16 ≤ S*(i+1))
    (hdiv : ¬ Summable (fun j : ℕ => 1/(F (2^j) : ℝ))) :
    ¬ ControlledGaps F a := by
  intro hc
  let c := fun i : ℕ => a (2*i)
  have heven : StrictMono (fun i : ℕ => 2*i) := by intro i j h; exact Nat.mul_lt_mul_of_pos_left h (by decide)
  have hcm : StrictMono c := ha.comp heven
  have hcp (i) : 0 < c i := hap _
  have hcf : SubsetSumFree c := hf.comp heven
  have hcc : ControlledGaps F c := by simpa [c] using hc.affine hm 2 0
  obtain ⟨g,hgm,hgp,⟨A,hgs⟩,_,_,hgv⟩ := envelope_of_controlled hm hp hslow hdiv hcc
  obtain ⟨D,hD⟩ := many_nonmultiples hcm hcp hcf hgm hgp hgs hgv
  obtain ⟨d,hd,hfew,hmod⟩ := modular_normalization_of_bounded_moduli
    (a := c) (U := D) (by
      intro d _ h
      by_contra! hlt
      exact (hD d hlt.le).not_ge (h (d^2)))
  apply reserved_completeness_contradiction ha hap hf hd hfew hmod
  · intro r
    let B := oddBlocks a hd
    let b := fun i => B.value (3*i+r+1)
    have hbm := B.value_strictMono ha hd
    have hb : StrictMono b := hbm.comp (by intro i j h; change 3*i+r+1 < 3*j+r+1; omega)
    have hbp (i) : 0 < b i := (hap _).trans_le (B.value_bounds ha hd _).1
    have hbc : ControlledGaps F b := by
      simpa only [b,Nat.add_assoc] using (hc.odd_blocks hm ha hd B).affine hm 3 (r+1)
    obtain ⟨G,_,hGp,⟨_,hGs⟩,_,hgap,_⟩ := envelope_of_controlled hm hp hslow hdiv hbc
    exact syndetic_of_growth_envelope hb hbp hGp hGs hgap
  · intro θ hθ
    obtain ⟨hbm,hbp,hbf,_⟩ := normalized_subsequence hcm hcp hcf hd hfew
    obtain ⟨G,hGm,hGp,⟨_,hGs⟩,hGd,hgap,hval⟩ :=
      envelope_of_controlled hm hp hslow hdiv (hcc.quotient hm hd hfew)
    exact sequence_phase_divergence_of_not_summable hbm hbp
      (phase_divergence_of_envelope hbm hbp hbf hGm hGp hGs hgap hval hGd hθ)

end JSP727
