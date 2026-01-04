# Semiprime Interleaving and Twin Prime Detection

A Lean 4 formalization of a novel combinatorial characterization of twin primes via the interleaving of anchored semiprime sets.

## Overview

This project introduces the **interleaving statistic** $L(n)$, which measures how two consecutive "anchored semiprime sets" merge when sorted. The main result establishes a precise equivalence between perfect interleaving and prime ratio record minima, providing a new combinatorial lens for studying twin primes.

## Key Definitions

**Anchored Semiprime Set:** For $n \geq 1$,
$$S_n = \{p_i \cdot p_n : 1 \leq i \leq n\}$$

**Interleaving Statistic:** $L(n)$ counts the length of the maximal alternating prefix $(A, B, A, B, \ldots)$ when merging $S_n$ and $S_{n+1}$ in sorted order.

**Prime Ratio:** $r_n = p_{n+1}/p_n$

## Main Results

| Result | Statement | Status |
|--------|-----------|--------|
| **Keystone Lemma** | $L(n) = n \Leftrightarrow r_n$ is a strict record minimum | ✅ Proven |
| **Twin → Perfect** | Twin prime index $\Rightarrow L(n) = n$ | ✅ Proven (unconditional) |
| **Density Constraint** | $L(n) = n \land g(n) \geq 4 \Rightarrow$ bound on twin locations | ✅ Proven |
| **Main Equivalence** | Under TDH: $L(n) = n \Leftrightarrow$ twin prime index | ✅ Proven (conditional) |
| **Bridge Theorem** | Equivalence holds $\Leftrightarrow$ TDH holds | ✅ Proven |

**Twin Density Hypothesis (TDH):** For $n \geq 10$ with $g(n) \geq 4$, there exists a twin prime index $i < n$ such that $p_i \cdot g(n) > 2 \cdot p_n$.

## Example

For $n = 3$ (twin primes $p_3 = 5$, $p_4 = 7$):

```
S₃ = {2·5, 3·5, 5·5} = {10, 15, 25}
S₄ = {2·7, 3·7, 5·7, 7·7} = {14, 21, 35, 49}

Merged: 10(A), 14(B), 15(A), 21(B), 25(A), 35(B), 49(B)
Pattern: A, B, A, B, A, B, B

L(3) = 3 = n  ✓ Perfect interleaving!
```

For $n = 4$ (non-twin: $p_4 = 7$, $p_5 = 11$, gap = 4):

```
S₄ = {14, 21, 35, 49}
S₅ = {22, 33, 55, 77, 121}

Merged: 14(A), 21(A), 22(B), ...
Pattern: A, A, B, ...

L(4) = 0 < 4 = n  ✗ Not perfect interleaving
```

## Repository Structure

```
SemiprimeInterleaving/
├── README.md                      # This file
├── SemiprimeInterleaving.lean     # Main Lean 4 proof (~2300 lines)
├── lakefile.lean                  # Lake build configuration
├── lean-toolchain                 # Lean version specification
└── paper/
    └── SemiprimeInterleaving_Paper.pdf  # Full paper with proofs
```

## Building

Requires Lean 4 and Mathlib. To build:

```bash
lake update
lake build
```

## Formalization Details

The Lean formalization includes:

- **Complete definitions** of `nthPrime`, `primeGap`, `primeRatio`, `semiprimeList`, `L`, `isStrictRecordMin`
- **Full proofs** of all theorems with no `sorry`
- **Explicit computations** for base cases ($n < 10$)
- **Helper lemmas** including ratio transitivity and merge ordering

Key techniques used:
- Cross-multiplication to avoid division (ratios compared via `p_{n+1} · p_j < p_{j+1} · p_n`)
- Induction on prime indices
- Case analysis on twin vs. non-twin indices

## The Insight

The framework reveals that twin primes create a special "resonance" in the semiprime structure:

1. Twin primes have the smallest possible gap (2)
2. This gives them the smallest possible ratio $r_n = 1 + 2/p_n$
3. For large $n$, this ratio beats all previous ratios
4. This causes perfect interleaving in the semiprime merge

The converse is more subtle: non-twins *could* achieve perfect interleaving if all preceding twins are "small enough" — but the Twin Density Hypothesis asserts this never happens for $n \geq 10$.

## Citation

If you use this work, please cite:

```bibtex
@misc{zer0dyn2026semiprime,
  author = {ZER0DYN},
  title = {Semiprime Interleaving and Twin Prime Detection: A Combinatorial Characterization via Prime Ratio Records},
  year = {2026},
  howpublished = {\url{https://github.com/ZER0DYN/SemiprimeInterleaving}}
}
```

## License

MIT License

## Author

**ZER0DYN** — January 2026

---

*"The primes are not random, but they play a good imitation of it."* — Terence Tao
