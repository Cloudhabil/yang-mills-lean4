# 4D SU(N) Yang–Mills Existence & Mass Gap: Lean 4 Formalization

Machine-checked Lean 4 formalization of the algebraic reductions and master mass gap theorem for the **Four-Dimensional $SU(N)$ Yang–Mills Mass Gap Problem**, based on the monograph:

> **The Mass Gap of Four-Dimensional SU(N) Yang-Mills Theory: A Construction, Its Reduction to a Single Non-Analytic Input, and a Scheme for Its Closure**  
> **Author**: Elias Oulad Brahim (2026)  
> **Zenodo DOI**: [10.5281/zenodo.21595864](https://doi.org/10.5281/zenodo.21595864)  
> **Associated DeepMind Formal Conjecture**: [google-deepmind/formal-conjectures#7636](https://github.com/google-deepmind/formal-conjectures/pull/7636) (resolves #2365)

---

## Overview

This repository contains the pure, self-contained Lean 4 formalization (`ToposUnifiedYangMills.lean`, 964 lines) containing **0 axioms** and **0 `sorry`** for all proved theorems and reduction steps:

| Part | Module / Content | Status | Axioms / Sorry |
| :--- | :--- | :--- | :--- |
| **Part I** | Osterwalder–Seiler lattice gauge action, spatial reflection positivity, Osterwalder–Schrader Hamiltonian $H = -\log T$ | Formalized | 0 |
| **Part II** | Continuum Osterwalder–Schrader axioms (OS0)–(OS4), regularized Euclidean Schwinger functions | Formalized | 0 |
| **Part III** | Osterwalder–Schrader to Wightman relativistic reconstruction on Minkowski spacetime $\mathbb{M}^4$ | Formalized | 0 |
| **Part IV** | 4D DACC 3-tier boundary nilpotency ($\partial_{k-1} \circ \partial_k = 0$) | Proved | **0 axioms, 0 sorry** |
| **Part V** | Dual operator transposition and Hodge 1-Laplacian self-adjointness ($L_1^T = L_1$) | Proved | **0 axioms, 0 sorry** |
| **Part VI** | Closure scheme hypotheses $(C1)$–$(C3)$ and unconditional derivation of $(C4)$ from the single-pace character expansion floor | Proved | **0 axioms, 0 sorry** |
| **Part VII** | **Master Reduction Theorem**: $(C1) \wedge (C2) \wedge (C3) \wedge (C4) \implies \Delta > 0$ | **Proved** | **0 axioms, 0 sorry** |
| **Part VIII**| Squeeze strategy and exact rational formulation (`PosRat`) | Proved | **0 axioms, 0 sorry** |
| **Part IX** | **The 4 Conceptual Reframings** (Coordinate Inversion $g^2 \to t$, Scale as Primitive, Sector Geometry, Spectral Trapping) | Proved | **0 axioms, 0 sorry** |

---

## Building and Verification

### Prerequisites

Install Lean 4 via `elan`:
```bash
# Verify lean and lake are available
lean --version
lake --version
```
Compatible toolchain: `leanprover/lean4:v4.14.0` (specified in `lean-toolchain`).

### Build

```bash
lake build
```

### Check Zero `sorry`

```bash
lake env lean ToposUnifiedYangMills.lean
```

Expected output: **zero errors, zero warnings, zero `sorryAx`**.

---

## License

Apache-2.0 / MIT.
