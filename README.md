# Erdős 876 · Consecutive gaps in subset-sum-free sequences

How small can the consecutive gaps of an infinite subset-sum-free sequence of positive integers stay? For every nondecreasing slowly varying $F\ge1$, a uniform eventual gap bound $O(nF(n))$ is possible exactly when $\int_1^\infty dx/(xF(x))$ converges. In the convergent case a single sequence has gaps of order $nF(n)$. The threshold rules out $O(n\log n)$ and permits $O(n(\log n)^{1+\varepsilon})$ for all $\varepsilon>0$. In particular the answer to Erdős's explicit question whether the gaps can eventually stay below $n$ is **no**. [English mathematical proof](PROOF.md) · [Original problem](https://www.erdosproblems.com/876)

| Lean declaration | Conclusion |
| --- | --- |
| `JSP727.erdos876_integral_criterion` | Exact equivalence between existence with an eventual gap bound and integrability on $(1,\infty)$ for real nondecreasing slowly varying $F\ge1$. |
| `JSP727.integral_gap_construction` | In the convergent case the gaps eventually lie between $nF(n)/32$ and $C nF(n)$, with $C>0$. |
| `JSP727.discrete_gap_criterion` | A necessary and sufficient reciprocal-series test for nondecreasing positive integer factors with $F(n)^{16}\le S(n+1)$. |
| `JSP727.erdos876_eventual_question` | A negative answer to the question whether the $n$th gap can eventually stay below $n$. |
| `JSP727.erdos876_linear` | For every integer $K$ and every starting index $N$, some positive $n\ge N$ has gap greater than $Kn$. |
| `JSP727.exists_of_summable_reciprocal` | For any nondecreasing positive integer budget $g$ with $\sum 1/g(n)<\infty$, constructs a sequence with gap between $g(n-1)/8$ and $C g(n)$. |
| `JSP727.logarithmic_gap_construction` | Specializes the real-budget construction to $n(1+\lfloor\log_2 n\rfloor)^{1+\varepsilon}$, for every positive real $\varepsilon$. |

The sequence statements use $a_0<a_1<\cdots$. In each gap from index $i$ to index $i+1$, put $n=i+1$ for the original one-based enumeration. The explicit yes-or-no result also uses an infinite set, finite sets of distinct smaller members, and its enumeration by `Nat.nth`. This is the negative answer to the proposition recorded as `erdos_876.parts.i` in Formal Conjectures. The integral criterion addresses the general question about an eventual upper bound. Korsky's additional results under a requirement of recurring bounded or locally small gaps are separate statements in his manuscript. [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/983809371205c75d9d314e5f135172edfa064ffa/FormalConjectures/ErdosProblems/876.lean) · [Main theorem](IntegralCriterion.lean) · [Set formulation](Prize.lean)

## Reproduce

Use Lean 4.31.0 with the revisions in `lake-manifest.json`. In a clean checkout, from the repository root, run the following commands.

```sh
lake exe cache get
lake build
lake env lean --trust=0 Audit.lean
```

The audit reports exactly `[propext, Classical.choice, Quot.sound]` for each of the seven declarations in the table.

On a memory-constrained machine, the optional command `python build_dependency.py` builds the pinned upstream Lean modules in dependency order before `lake build`. The full build and the axiom audit use the same source in either case.

## Contributions and sources

The mathematical claim on unbounded gap ratios was communicated by Liam Price in July 2026 and attributed to GPT 5.6 Sol Pro. Samuel Korsky's September 2026 manuscript states the integral criterion in Theorem 2.1 and credits Price's earlier result. Its proof-claim entry credits GPT Astra. This repository records the Lean formalization and mathematical exposition prepared using OpenAI Codex for the submitting GitHub account `jackanderson123456`. The nonexistence proof here uses finite-prefix scarcity of multiples, Dirichlet approximation and packing on disjoint dyadic blocks. [Price and Korsky proof-claim records](https://www.erdosproblems.com/forum/thread/876/proof-claims) · [Korsky manuscript](https://drive.google.com/file/d/1kf9KetNCVaWtnFQvcp-odO3Zkf9eiDF1/view)

The disjoint-translates count goes back to Erdős. The modular normalization and odd-bin construction follow Korsky. The completeness argument uses the theorem of Bergelson and Simmons and imports Will Blair's MIT-licensed Lean work on Erdős 254, including the formal Bergelson–Furstenberg–Weiss theorem. The torus argument here handles irrational divergence together with modular coverage of full subset sums. The positive construction uses termwise shrinking intervals of the $\sqrt2$ rotation. [Bergelson and Simmons](https://arxiv.org/abs/1507.02208) · [Blair's Lean source](https://github.com/williamjblair/lean-proofs/tree/4f915a323443bfb1709a6805a013812016dca88a/starfleet/erdos-254)
