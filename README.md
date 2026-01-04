# Semiprime Interleaving

**A Combinatorial Encoding of Prime Ratio Record Minima**

A Lean 4 formalization of a combinatorial statistic that encodes prime ratio record minima through the merge behavior of anchored semiprime sets.

## What This Is

This project introduces the **interleaving statistic** $L(n)$, which measures how two consecutive "anchored semiprime sets" merge when sorted. The main result is a clean equivalence:

$$L(n) = n \quad \Longleftrightarrow \quad r_n = \frac{p_{n+1}}{p_n} \text{ is a strict record minimum}$$

This provides a **combinatorial encoding** of an arithmetic condition — translating ratio comparisons into a structural property of sorted lists.

## What This Is NOT

To avoid misunderstanding:

- ❌ This is **not** progress toward the twin prime conjecture
- ❌ This does **not** introduce new arithmetic content about primes
- ❌ The "detection" claim is conditional on a hypothesis that is **logically equivalent** to the desired conclusion (proven via the Bridge Theorem)

The interleaving statistic is a **re-encoding**, not a **discovery**. It provides a **lens**, not a **lever**.

## Key Definitions

**Anchored Semiprime Set:**
$$S_n = \{p_i \cdot p_n : 1 \leq i \leq n\}$$

**Interleaving Statistic:** $L(n)$ counts the length of the maximal alternating prefix $(A, B, A, B, \ldots)$ when merging $S_n$ and $S_{n+1}$ in sorted order.

**Prime Ratio:** $r_n = p_{n+1}/p_n$

## Results

| Result | Statement | Status |
|--------|-----------|--------|
| **Keystone Lemma** | $L(n) = n \Leftrightarrow r_n$ is a strict record minimum | ✅ Proven |
| **Twin → Perfect** | Twin prime index $\Rightarrow L(n) = n$ | ✅ Proven (repackages gap minimization) |
| **Density Constraint** | $L(n) = n \land g(n) \geq 4 \Rightarrow$ bound on twin locations | ✅ Proven |
| **Bridge Theorem** | The converse hypothesis $\Leftrightarrow$ the converse conclusion | ✅ Proven (shows circularity) |

## Example

For $n = 3$ (twin primes $p_3 = 5$, $p_4 = 7$):

```
S₃ = {2·5, 3·5, 5·5} = {10, 15, 25}
S₄ = {2·7, 3·7, 5·7, 7·7} = {14, 21, 35, 49}

Merged: 10(A), 14(B), 15(A), 21(B), 25(A), 35(B), 49(B)
Pattern: A, B, A, B, A, B, B

L(3) = 3 = n  ✓ Perfect interleaving
```

This occurs because twin gaps minimize the normalized ratio $r_n = 1 + 2/p_n$. The interleaving statistic encodes this known fact in combinatorial language.

## What Might Be Valuable

Despite the limitations, this project may offer:

1. **A combinatorial lens** — a visual/structural way to think about ratio records
2. **A formal artifact** — the Lean 4 formalization (~2300 lines, no `sorry`) may interest the formal methods community
3. **A template for variants** — the encoding might generalize to other anchors or record phenomena

## Repository Structure

```
SemiprimeInterleaving/
├── README.md                      # This file
├── SemiprimeInterleaving.lean     # Main Lean 4 proof (~2300 lines)
├── lakefile.toml                  # Lake build configuration
├── lean-toolchain                 # Lean version specification
├── lake-manifest.json             # Dependency locks
└── paper/
    └── SemiprimeInterleaving_Paper.pdf
```

## Building

Requires Lean 4 and Mathlib. To build:

```bash
lake update
lake build
```

## The Core Insight (Honestly Stated)

The Keystone Lemma equivalence is **definitional rather than surprising**:

1. The interleaving statistic was *designed* to encode ratio comparisons
2. $B_j < A_{j+1}$ (needed for alternation) is equivalent to $r_n < r_j$ by cross-multiplication
3. The equivalence follows by construction

Twin primes achieve $L(n) = n$ because they have gap 2, which minimizes $r_n = 1 + g(n)/p_n$. This is the well-known fact that twin primes have minimal gaps, repackaged.

## Honest Assessment

This framework is:
- ✅ Correct and carefully engineered
- ✅ Formally verified end-to-end
- ✅ A clean encoding that organizes known facts

But as mathematics:
- It is a **re-encoding**, not a discovery
- It is a **lens**, not a lever
- It is a **representation**, not a result

## Citation

```bibtex
@misc{zer0dyn2026semiprime,
  author = {Zer0dyn},
  title = {Semiprime Interleaving: A Combinatorial Encoding of Prime Ratio Record Minima},
  year = {2026},
  howpublished = {\url{https://github.com/Zer0dyn/SemiprimeInterleaving}}
}
```

## License

MIT License

## Author

**Zer0dyn** — January 2026
