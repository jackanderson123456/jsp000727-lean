# Erdős 876 · Consecutive gaps in subset-sum-free sequences

For every infinite increasing sequence of positive integers in which no term is a sum of distinct earlier terms, the ratio of the $n$th gap to $n$ is unbounded on every tail. Conversely, for every $\varepsilon>0$ there is such a sequence with gaps $O(n(1+\log n)^{1+\varepsilon})$. A more general construction works for any nondecreasing positive gap budget with summable reciprocal. [English mathematical proof](PROOF.md) · [Original problem](https://www.erdosproblems.com/876)

| Lean declaration | Conclusion |
| --- | --- |
| `JSP727.erdos876_eventual_question` | A negative answer to the question whether the $n$th gap can eventually stay below $n$. |
| `JSP727.erdos876_linear` | For every integer $K$ and every starting index $N$, some positive $n\ge N$ has gap greater than $Kn$. |
| `JSP727.exists_of_summable_reciprocal` | For any nondecreasing positive integer budget $g$ with $\sum 1/g(n)<\infty$, constructs a sequence with gap between $g(n-1)/8$ and $C g(n)$. |
| `JSP727.logarithmic_gap_construction` | Specializes the real-budget construction to $n(1+\lfloor\log_2 n\rfloor)^{1+\varepsilon}$, for every positive real $\varepsilon$. |

The first two statements use an infinite set of positive integers, quantification over finite sets of distinct smaller terms, and its increasing enumeration by `Nat.nth`. The construction gives a strictly increasing sequence indexed from zero. Its gap from index $i$ to index $i+1$ corresponds to the original gap with $n=i+1$. The divergence direction for a general slowly varying factor in Korsky's integral criterion extends beyond the theorems listed here.

## Reproduce

Use Lean 4.31.0 with the revisions in `lake-manifest.json`. In a clean checkout, from the repository root, run the following commands.

```sh
lake exe cache get
lake build
lake env lean --trust=0 Audit.lean
```

The audit reports exactly `[propext, Classical.choice, Quot.sound]` for each of the four declarations in the table.

On a memory-constrained machine, the optional command `python build_dependency.py` builds the pinned upstream Lean modules in dependency order before `lake build`. The full build and the axiom audit use the same source in either case.

## Contributions and sources

The mathematical claim on unbounded gap ratios was communicated by L. Price in July 2026 and attributed to GPT 5.6 Sol Pro. Samuel Korsky's September 2026 manuscript states the full integral criterion and credits Price's earlier result. Its proof-claim entry credits GPT Astra. This repository records a Lean formalization and mathematical exposition prepared with OpenAI Codex for the submitting account. [Price and Korsky proof-claim records](https://www.erdosproblems.com/forum/thread/876/proof-claims) · [Korsky manuscript](https://drive.google.com/file/d/1kf9KetNCVaWtnFQvcp-odO3Zkf9eiDF1/view)

The disjoint-translates count goes back to Erdős. The modular normalization and odd-bin construction follow Korsky. The completeness argument uses the theorem of Bergelson and Simmons and imports Will Blair's MIT-licensed Lean work on Erdős 254, including the formal Bergelson–Furstenberg–Weiss theorem. The torus argument here handles irrational divergence together with modular coverage of full subset sums. The positive construction uses termwise shrinking intervals of the $\sqrt2$ rotation. [Bergelson and Simmons](https://arxiv.org/abs/1507.02208) · [Blair's Lean source](https://github.com/williamjblair/lean-proofs/tree/4f915a323443bfb1709a6805a013812016dca88a/starfleet/erdos-254)
