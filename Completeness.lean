import SequenceSets
import Torus
import Research.BFWFromSpectral

namespace JSP727

open Filter Set
open scoped Topology
open Erdos254 Erdos254.ConditionalBohrCriterion Erdos254.PiecewiseAssembly
open Erdos254.GeneralBFWReduction Erdos254.BFWFromSpectral

/-- The disjoint four-set completeness criterion in the form used in Korsky's
proof. The three syndeticity assumptions concern distinct subset sums. -/
theorem four_sets_complete (B₀ B₁ B₂ C : Set ℕ)
    (h01 : Disjoint B₀ B₁) (h02 : Disjoint B₀ B₂) (h12 : Disjoint B₁ B₂)
    (h0C : Disjoint B₀ C) (h1C : Disjoint B₁ C) (h2C : Disjoint B₂ C)
    (h₀ : SyndeticSums B₀) (h₁ : SyndeticSums B₁) (h₂ : SyndeticSums B₂)
    (hphase : ∀ θ : ℝ, Irrational θ → Tendsto (phasePartialSum C θ) atTop atTop)
    (hmod : ∀ q : ℕ, 0 < q → ∀ z : ℤ, ∃ s : Finset ℕ,
      (∀ n ∈ s, n ∈ C) ∧ (q : ℤ) ∣ z-(∑ n ∈ s, n : ℕ)) :
    ∃ N : ℕ, ∀ n ≥ N, Representable (((B₀ ∪ B₁) ∪ C) ∪ B₂) n := by
  have hbfw := general_bfw_implies_finite_sum_property general_bfw_from_spectral
  obtain ⟨d,α,U,hU,n₀,hn₀,J,hJ,hpiece⟩ := hbfw B₀ B₁ h01 (by
    intro i
    by_cases hi : i=0
    · simpa [hi,SyndeticSums] using h₀
    · simpa [hi,SyndeticSums] using h₁)
  obtain ⟨H,hClosed,ha,hcorr⟩ := torus_corrections C hphase hmod α
  obtain ⟨K,hK⟩ := h₂
  apply conditional_piecewise_bohr_completeness (B₀ ∪ B₁) C B₂
    (Set.disjoint_union_left.mpr ⟨h0C,h1C⟩)
    (Set.disjoint_union_left.mpr ⟨h02,h12⟩) h2C.symm
    (fun i => (α i : UnitAddCircle)) H hClosed ha hcorr U hU n₀ hn₀ J hJ hpiece K
  intro n
  obtain ⟨s,hs,hl,hu⟩ := hK n
  exact ⟨_, ⟨s,hs,rfl⟩, hl, hu⟩

end JSP727
