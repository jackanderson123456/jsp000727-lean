import Mathlib

/-! A missing subset-sum residue forces a divisor with few exceptions.
This is a least-modulus proof of the assertion used in Korsky's Lemma 3.2,
in the form needed for divisor normalization. -/

namespace JSP727

open Finset

def Covers (a : ℕ → ℕ) (q : ℕ) : Prop :=
  ∀ x : ℤ, ∃ s : Finset ℕ, (q : ℤ) ∣ x - (∑ i ∈ s, a i : ℕ)

private def weight (a : ℕ → ℕ) (q : ℕ) (s : Finset ℕ) : ZMod q :=
  ∑ i ∈ s, (a i : ZMod q)

private def Rep (a : ℕ → ℕ) (q : ℕ) (x : ZMod q) : Prop :=
  ∃ s : Finset ℕ, weight a q s = x

private theorem covers_iff_rep (a : ℕ → ℕ) (q : ℕ) [NeZero q] :
    Covers a q ↔ ∀ x, Rep a q x := by
  constructor
  · intro hc x
    obtain ⟨s,hs⟩ := hc x.val
    refine ⟨s, ?_⟩
    have he := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).2 hs
    simpa [weight] using he
  · intro hc x
    obtain ⟨s,hs⟩ := hc (x : ZMod q)
    exact ⟨s, (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).1 (by simpa [weight] using hs)⟩

private def prefixSums (a : ℕ → ℕ) (q : ℕ) [NeZero q] (n : ℕ) : Finset (ZMod q) :=
  (range n).powerset.image (weight a q)

private theorem mem_prefix {a : ℕ → ℕ} {q : ℕ} [NeZero q] {n : ℕ} {x : ZMod q} :
    x ∈ prefixSums a q n ↔ ∃ s ⊆ range n, weight a q s = x := by
  simp [prefixSums]

private theorem prefix_mono (a : ℕ → ℕ) (q : ℕ) [NeZero q] : Monotone (prefixSums a q) := by
  intro n m h x hx
  obtain ⟨s,hs,rfl⟩ := mem_prefix.mp hx
  exact mem_prefix.mpr ⟨s, hs.trans (range_mono h), rfl⟩

private theorem stable_of_equal_prefix {a : ℕ → ℕ} {q : ℕ} [NeZero q] (i : ℕ)
    (he : prefixSums a q i = prefixSums a q (i+1)) :
    ∀ x, Rep a q x → Rep a q (x+a i) := by
  rintro x ⟨s,rfl⟩
  let small := s ∩ range i
  let rest := s \ small
  have hsmall : small ⊆ range i := inter_subset_right
  have hsmalls : small ⊆ s := inter_subset_left
  have hi : i ∉ small := fun h => (Nat.lt_irrefl i) (mem_range.mp (hsmall h))
  have hnext : weight a q small + a i ∈ prefixSums a q (i+1) := by
    refine mem_prefix.mpr ⟨insert i small, ?_, ?_⟩
    · exact insert_subset (mem_range.mpr (Nat.lt_succ_self i)) (hsmall.trans (range_mono (by omega)))
    · simp [weight, hi, add_comm]
  obtain ⟨t,ht,htw⟩ := mem_prefix.mp (he ▸ hnext)
  have hdis : Disjoint rest t := by
    rw [Finset.disjoint_left]
    intro j hj hjt
    obtain ⟨hjs, hjn⟩ := mem_sdiff.mp hj
    exact hjn (mem_inter.mpr ⟨hjs,ht hjt⟩)
  have hsplit : weight a q rest + weight a q small = weight a q s :=
    sum_sdiff hsmalls
  refine ⟨rest ∪ t, ?_⟩
  change ∑ k ∈ rest ∪ t, (a k : ZMod q) = _
  rw [sum_union hdis]
  change weight a q rest + weight a q t = _
  rw [htw, ← add_assoc, hsplit]

private theorem stable_multiples {a : ℕ → ℕ} {q : ℕ} [NeZero q] (c : ZMod q)
    (hs : ∀ x, Rep a q x → Rep a q (x+c)) {y : ZMod q} (hy : Rep a q y) (z : ZMod q) :
    Rep a q (y+z*c) := by
  have hn (n : ℕ) : Rep a q (y+(n : ZMod q)*c) := by
    induction n with
    | zero => simpa using hy
    | succ n ih => simpa [Nat.cast_succ, add_mul, add_assoc] using hs _ ih
  simpa using hn z.val

/-- If a prefix stops growing when c is adjoined, coverage modulo gcd(c,q)
already implies coverage modulo q. -/
private theorem covers_of_stable {a : ℕ → ℕ} {q c : ℕ} [NeZero q]
    (hg : Covers a (c.gcd q))
    (hs : ∀ x, Rep a q x → Rep a q (x+(c : ZMod q))) : Covers a q := by
  intro x
  obtain ⟨s,k,hk⟩ := hg x
  have hbez : (c : ZMod q) * (Nat.gcdA c q : ZMod q) = (c.gcd q : ℕ) := by
    simpa using (ZMod.intCast_eq_intCast_iff _ _ q).2 (Int.gcd_a_modEq c q)
  have hcast := congrArg (fun v : ℤ => (v : ZMod q)) hk
  push_cast at hcast
  have htarget : weight a q s + ((k : ZMod q)*(Nat.gcdA c q : ZMod q))*c = (x : ZMod q) := by
    dsimp [weight]
    rw [show (k : ZMod q)*Nat.gcdA c q*c = (c*Nat.gcdA c q)*k by ring, hbez]
    linear_combination -hcast
  obtain ⟨t,ht⟩ := stable_multiples (c : ZMod q) hs (y := weight a q s) ⟨s,rfl⟩
    ((k : ZMod q)*Nat.gcdA c q)
  exact ⟨t,(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).1
    (by simpa [weight] using ht.trans htarget)⟩

/-- A least missing modulus d has at most d-2 exceptional terms in the whole
sequence. Cardinality increases every time a nonmultiple of d is adjoined. -/
theorem few_exceptions_of_missing {a : ℕ → ℕ} (h : ∃ q, 0 < q ∧ ¬ Covers a q) :
    ∃ d, 2 ≤ d ∧ ∀ n, Nat.count (fun i => ¬ d ∣ a i) n + 2 ≤ d := by
  classical
  let d := Nat.find h
  have hd := (Nat.find_spec h).1
  have hbad : ¬ Covers a d := (Nat.find_spec h).2
  change 0 < d at hd
  haveI : NeZero d := ⟨hd.ne'⟩
  have hgrow (i : ℕ) (hi : ¬ d ∣ a i) :
      (prefixSums a d i).card < (prefixSums a d (i+1)).card := by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨prefix_mono _ _ (Nat.le_succ _), ?_⟩
    intro he
    let g := (a i).gcd d
    have hlt : g < d := lt_of_le_of_ne (Nat.gcd_le_right _ hd)
      (fun heq => hi (Nat.gcd_eq_right_iff_dvd.mp heq))
    have hcov : Covers a g := by
      by_contra hmissing
      exact Nat.find_min h hlt ⟨Nat.gcd_pos_of_pos_right _ hd, hmissing⟩
    exact hbad (covers_of_stable hcov (stable_of_equal_prefix i he))
  have hlower (n : ℕ) : Nat.count (fun i => ¬ d ∣ a i) n + 1 ≤ (prefixSums a d n).card := by
    induction n with
    | zero => simp [prefixSums, weight]
    | succ n ih =>
      have hmono := card_le_card (prefix_mono a d (Nat.le_succ n))
      by_cases hn : d ∣ a n
      · simpa [Nat.count_succ, hn] using ih.trans hmono
      · have := hgrow n hn
        simp [Nat.count_succ, hn]
        omega
  have hupper (n : ℕ) : (prefixSums a d n).card < d := by
    suffices (prefixSums a d n).card < (univ : Finset (ZMod d)).card by
      simpa [ZMod.card] using this
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, ?_⟩
    intro he
    apply hbad ((covers_iff_rep _ _).mpr ?_)
    intro x
    have hx : x ∈ prefixSums a d n := he ▸ mem_univ _
    obtain ⟨s,_,hs⟩ := mem_prefix.mp hx
    exact ⟨s,hs⟩
  have bound (n : ℕ) : Nat.count (fun i => ¬ d ∣ a i) n + 2 ≤ d := by
    have := hlower n
    have := hupper n
    omega
  exact ⟨d, by simpa using bound 0, bound⟩

end JSP727
