import Denominators
import Research.TorusCorrectionGroup
import Research.CircleEscape

/-! Finite-dimensional torus corrections with divergence required only at
irrational phases. The tail-limit, character separation, and scalar escape
theorems used here are from Will Blair's formalization of Erdős 254. -/

namespace JSP727

open Filter Set
open scoped Topology
open Erdos254 Erdos254.TailSemigroup Erdos254.TorusOrbit
open Erdos254.TorusCharacterSeparation Erdos254.CompactSemigroup
open Erdos254.TorusCorrectionGroup Erdos254.PiecewiseAssembly

private theorem lift_tail_limit {G T : Type*} [AddCommGroup G] [TopologicalSpace G]
    [CompactSpace G] [AddCommGroup T] [TopologicalSpace T] [T2Space T]
    (A : Set ℕ) (v : ℕ → G) (f : G →ₜ+ T) {z : T}
    (hz : z ∈ tailLimit A (fun n => f (v n))) :
    ∃ y ∈ tailLimit A v, f y = z := by
  let S := tailSubsetSums A v
  have hmap (n : ℕ) : f '' S n = tailSubsetSums A (fun i => f (v i)) n := by
    ext t
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s, hs, (map_sum f v s).symm⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨_, ⟨s,hs,rfl⟩, map_sum f v s⟩
  let K := fun n => closure (S n) ∩ (f ⁻¹' {z})
  have hclosed (n : ℕ) : IsClosed (K n) :=
    isClosed_closure.inter (isClosed_singleton.preimage f.continuous)
  have hnonempty (n : ℕ) : (K n).Nonempty := by
    have hn : z ∈ closure (tailSubsetSums A (fun i => f (v i)) n) :=
      Set.mem_iInter.mp hz n
    rw [← hmap, ← image_closure_of_isCompact (f := (⇑f : G → T))
      isClosed_closure.isCompact f.continuous_toFun.continuousOn] at hn
    obtain ⟨y,hy,he⟩ := hn
    exact ⟨y,hy,he⟩
  have hdir : Directed (fun X Y : Set G => X ⊇ Y) K := by
    intro n m
    refine ⟨max n m, ?_, ?_⟩
    · exact inter_subset_inter_left _ (closure_mono (tailSubsetSums_mono_cutoff A v (le_max_left _ _)))
    · exact inter_subset_inter_left _ (closure_mono (tailSubsetSums_mono_cutoff A v (le_max_right _ _)))
  obtain ⟨y,hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed K hdir
    hnonempty (fun n => (hclosed n).isCompact) hclosed
  exact ⟨y, Set.mem_iInter.mpr (fun n => (Set.mem_iInter.mp hy n).1), (Set.mem_iInter.mp hy 0).2⟩

/-- Some multiple of the given rotation lies in the group of tail limits.
Rational characters are killed by a common denominator and irrational
characters have a nonzero scalar tail limit. -/
theorem multiple_mem_tail_limit {ι : Type*} [Fintype ι] (A : Set ℕ)
    (hphase : ∀ θ : ℝ, Irrational θ → Tendsto (phasePartialSum A θ) atTop atTop)
    (α : ι → ℝ) :
    ∃ D : ℕ, 0 < D ∧ ∃ H : AddSubgroup (UnitAddTorus ι),
      (H : Set (UnitAddTorus ι)) = tailLimit A (fun n => n • (fun i => (α i : UnitAddCircle))) ∧
      D • (fun i => (α i : UnitAddCircle)) ∈ H := by
  classical
  let a : UnitAddTorus ι := fun i => (α i : UnitAddCircle)
  let v := fun n : ℕ => n • a
  let S := tailLimit A v
  have hS : IsClosed S := tailLimit_isClosed A v
  obtain ⟨H,hH⟩ := compact_add_subsemigroup_is_addSubgroup S
    ⟨0,zero_mem_tailLimit A v⟩ hS (fun _ hx _ hy => tailLimit_add_mem A v hx hy)
  obtain ⟨D,hD,hden⟩ := common_denominator α
  refine ⟨D,hD,H,hH,?_⟩
  change D • a ∈ H
  by_contra hnot
  obtain ⟨k,hAnn,hsep⟩ := exists_character_separating_point H (hH ▸ hS) hnot
  let C := torusChar k
  let φ := ∑ i, (k i : ℝ)*α i
  have hCa : C a = (φ : UnitAddCircle) := torusChar_phase k α
  have hz (y) (hy : y ∈ H) : C y = 0 := by
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    have hfour := hAnn y hy
    rw [mFourier_eq_torusChar_toCircle] at hfour
    simpa [C] using hfour
  by_cases hφ : Irrational φ
  · obtain ⟨z, hzlim, hnz⟩ := CircleEscape.tailLimit_has_nonzero_qsmul A φ 1
      (by simpa using hphase φ hφ)
    have he (n : ℕ) : C (v n) = ((φ*n : ℝ) : UnitAddCircle) := by
      dsimp only [v]
      rw [map_nsmul, hCa, ← AddCircle.coe_nsmul, nsmul_eq_mul, mul_comm]
    have hzl : z ∈ tailLimit A (fun n => C (v n)) := by simpa only [he] using hzlim
    obtain ⟨y,hy,hyz⟩ := lift_tail_limit A v C hzl
    have hyH : y ∈ H := by change y ∈ (H : Set _); rwa [hH]
    exact hnz (by simp [← hyz, hz y hyH])
  · obtain ⟨r,hr⟩ := Classical.not_not.mp hφ
    obtain ⟨j,hj⟩ := hden k r hr.symm
    have hzero : C (D • a) = 0 := by
      rw [map_nsmul, hCa, ← hr, ← AddCircle.coe_nsmul, nsmul_eq_mul, hj]
      simp
    apply hsep
    rw [mFourier_eq_torusChar_toCircle]
    change ((C (D • a)).toCircle : ℂ) = 1
    simp [hzero]

private theorem finite_add_tail {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (A : Set ℕ) (v : ℕ → G) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ∈ A) {y : G} (hy : y ∈ tailLimit A v) :
    (∑ n ∈ s, v n) + y ∈ closure (tailSubsetSums A v 0) := by
  classical
  let N := s.sup id + 1
  apply mem_closure_iff.mpr
  intro O hO hyO
  let U := (fun t => (∑ n ∈ s, v n) + t) ⁻¹' O
  have hU : IsOpen U := hO.preimage (continuous_const.add continuous_id)
  have hyN : y ∈ closure (tailSubsetSums A v N) := Set.mem_iInter.mp hy N
  obtain ⟨w,hw,hwr⟩ := mem_closure_iff.mp hyN U hU hyO
  obtain ⟨t,ht,rfl⟩ := hwr
  have hdis : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro n hn hnt
    have hle : n ≤ s.sup id := Finset.le_sup (f := id) hn
    have htN := (ht n hnt).2
    dsimp [N] at htN
    omega
  refine ⟨_,hw,s ∪ t,?_,Finset.sum_union hdis⟩
  intro n hn
  exact ⟨(Finset.mem_union.mp hn).elim (hs n) (fun h => (ht n h).1), Nat.zero_le _⟩

/-- Modular coverage on the full set, together with irrational divergence,
gives all the torus corrections needed by the completeness argument. -/
theorem torus_corrections {ι : Type*} [Fintype ι] (A : Set ℕ)
    (hphase : ∀ θ : ℝ, Irrational θ → Tendsto (phasePartialSum A θ) atTop atTop)
    (hmod : ∀ q : ℕ, 0 < q → ∀ z : ℤ, ∃ s : Finset ℕ,
      (∀ n ∈ s, n ∈ A) ∧ (q : ℤ) ∣ z-(∑ n ∈ s, n : ℕ)) (α : ι → ℝ) :
    ∃ H : AddSubgroup (UnitAddTorus ι), IsClosed (H : Set (UnitAddTorus ι)) ∧
      (fun i => (α i : UnitAddCircle)) ∈ H ∧
      ∀ x ∈ H, ∀ O : Set (UnitAddTorus ι), IsOpen O → x ∈ O →
        ∃ n : ℕ, Representable A n ∧ n • (fun i => (α i : UnitAddCircle)) ∈ O := by
  classical
  let a : UnitAddTorus ι := fun i => (α i : UnitAddCircle)
  let v := fun n : ℕ => n • a
  obtain ⟨D,hD,H,hH,hDa⟩ := multiple_mem_tail_limit A hphase α
  let G := (AddSubgroup.zmultiples a).topologicalClosure
  have hc : (G : Set _) ⊆ closure (tailSubsetSums A v 0) := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    obtain ⟨z,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    obtain ⟨s,hs,k,hk⟩ := hmod D hD z
    have htail : k • (D • a) ∈ tailLimit A v := by
      rw [← hH]
      exact H.zsmul_mem hDa k
    have hhit := finite_add_tail A v s hs htail
    change (∑ n ∈ s, n • a) + k • (D • a) ∈ _ at hhit
    have hn (t : ℕ) : (t : ℤ) • a = t • a := by simp
    rw [sum_nsmul_coeff, ← hn (∑ n ∈ s, n), ← hn D,
      ← mul_zsmul, ← add_zsmul] at hhit
    convert hhit using 2
    linear_combination hk
  refine ⟨G, AddSubgroup.isClosed_topologicalClosure _,
    (AddSubgroup.zmultiples a).le_topologicalClosure (AddSubgroup.mem_zmultiples a), ?_⟩
  intro x hx O hO hxO
  obtain ⟨_,hy,⟨s,hs,rfl⟩⟩ := mem_closure_iff.mp (hc hx) O hO hxO
  refine ⟨∑ n ∈ s, n, ⟨s,fun n hn => (hs n hn).1,rfl⟩, ?_⟩
  simpa only [v, sum_nsmul_coeff] using hy

end JSP727
