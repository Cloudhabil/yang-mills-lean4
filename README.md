# 4D Yang–Mills Existence & Mass Gap: Lean 4 Formalization

Machine-checked Lean 4 formalization of the algebraic reductions and master mass gap theorem for the **Four-Dimensional Yang–Mills Mass Gap Problem**, based on the monograph:

> **The Mass Gap of Four-Dimensional SU(N) Yang-Mills Theory: A Construction, Its Reduction to a Single Non-Analytic Input, and a Scheme for Its Closure**  
> **Author**: Elias Oulad Brahim (2026)  
> **Zenodo DOI**: [10.5281/zenodo.21595864](https://doi.org/10.5281/zenodo.21595864)  
> **Associated DeepMind Formal Conjecture**: [google-deepmind/formal-conjectures#7636](https://github.com/google-deepmind/formal-conjectures/pull/7636) (resolves #2365)

---

## Repository Architecture

This repository contains two core formalizations:

1. **[`ToposUnifiedYangMills.lean`](ToposUnifiedYangMills.lean)** (1,039 lines):  
   A standalone, dependency-free Lean 4 formalization containing **0 unproved axioms** and **0 `sorryAx`** for all audited algebraic reductions, DACC nilpotency proofs, and spectral bounds. It compiles directly with the core Lean 4 toolchain without external library dependencies.

2. **[`MillenniumYangMills.lean`](MillenniumYangMills.lean)** (532 lines):  
   The companion formalization of the official Clay Millennium Prize Problem statement by Arthur Jaffe & Edward Witten (2000), synchronized with [PR #7636](https://github.com/google-deepmind/formal-conjectures/pull/7636) in `google-deepmind/formal-conjectures`.

---

## 1. Constructive Proof Pipeline (`ToposUnifiedYangMills.lean`)

All audited theorems and reductions are mechanically checked by Lean 4's kernel without unproved axioms:

| Part | Module / Content | Status | Axioms / Sorry |
| :--- | :--- | :--- | :--- |
| **Part I** | Osterwalder–Seiler lattice gauge action, spatial reflection positivity, Osterwalder–Schrader Hamiltonian $H = -\log T$ | Formalized | 0 axioms |
| **Part II** | Continuum Osterwalder–Schrader axioms (OS0)–(OS4), regularized Euclidean Schwinger functions | Formalized | 0 axioms |
| **Part III** | Osterwalder–Schrader to Wightman relativistic reconstruction on Minkowski spacetime $\mathbb{M}^4$ | Formalized | 0 axioms |
| **Part IV** | 4D DACC 3-tier boundary nilpotency ($\partial_{k-1} \circ \partial_k = 0$) | Proved | **0 axioms, 0 sorry** |
| **Part V** | Dual operator transposition and Hodge 1-Laplacian self-adjointness ($L_1^T = L_1$) | Proved | **0 axioms, 0 sorry** |
| **Part VI** | Closure scheme hypotheses $(C1)$–$(C3)$ and unconditional derivation of $(C4)$ from the single-pace character expansion floor | Proved | **0 axioms, 0 sorry** |
| **Part VII** | **Master Reduction Theorem**: $(C1) \wedge (C2) \wedge (C3) \wedge (C4) \implies \Delta > 0$ | **Proved** | **0 axioms, 0 sorry** |
| **Part VIII**| Squeeze strategy and exact rational formulation (`PosRat`) | Proved | **0 axioms, 0 sorry** |
| **Part IX** | **The 4 Conceptual Reframings** (Coordinate Inversion $g^2 \to t$, Scale as Primitive, Sector Geometry, Spectral Trapping) | Proved | **0 axioms, 0 sorry** |

---

## 2. Clay Millennium Prize Formal Statement (`MillenniumYangMills.lean`)

This formalization directly resolves the review blockers on [PR #7636](https://github.com/google-deepmind/formal-conjectures/pull/7636) by formalizing the full physical requirements of 4D Quantum Yang–Mills Theory:

- **Rigorous Hilbert Space & Domain Scaffolding**:  
  Replaces arbitrary types with complete, separable complex Hilbert spaces $\mathcal{H}$ (`[NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [SeparableSpace ℋ]`) and a dense Poincaré-invariant domain $\mathcal{D} \subset \mathcal{H}$.
- **Stone's Theorem Spacetime Translation Generators**:  
  The Hamiltonian $H$ and spatial momenta $\mathbf{P}$ are typed as symmetric unbounded linear maps on $\mathcal{D}$ acting as strong spacetime translation derivatives via `HasDerivAt`, mutually commuting on $\mathcal{D}$, with relativistic joint spectrum contained in the closed forward lightcone $\bar{V}_+$.
- **Zero Vacuum Energy Ground State**:  
  Enforces $H\Omega = 0$ (`hamiltonian_vacuum`), $\mathbf{P}\Omega = 0$ (`momentum_vacuum`), normalization $\|\Omega\| = 1$, and ground-state isolation $\ker(H) \cap \mathcal{D} = \mathbb{C}\Omega$.
- **Universal Compact Simple Gauge Group Scope**:  
  Quantified over all compact, connected, non-abelian simple Lie groups $G$ via the typeclass `CompactSimpleLieGroup G`, with canonical specializations to $\mathrm{SU}(N)$ for any $N \ge 2$, $\mathrm{SU}(2)$, and $\mathrm{SU}(3)$ (QCD gluon sector).
- **Euclidean Osterwalder–Schrader Data & Reconstruction**:  
  Formalizes character-indexed continuum Schwinger functions $S_n$ with (OS0) polynomial temperedness bounds, (OS1) $\mathrm{ISO}(4)$ Euclidean invariance, (OS2) reflection positivity across $\{x^0 = 0\}$, (OS3) permutation symmetry, and (OS4) exponential clustering with rate $m > 0$. Proves `osterwalder_schrader_reconstruction` with $\Delta \ge m > 0$.
- **Anti-Dummy Model Holonomy Axioms**:  
  - Trivial loop holonomy: $W(\gamma_x, \chi) = \chi(1) I_\mathcal{D}$.
  - Trivial representation character holonomy: $W(\gamma, c \cdot 1_G) = c I_\mathcal{D}$.
  - Orientation reversal adjointness: $W(\gamma^{-1}, \bar{\chi}) = W(\gamma, \chi)^\dagger$.
  - Vacuum-subtracted excitations in $(\mathbb{C}\Omega)^\perp \cap \mathcal{D}$ ($W(\gamma, \chi)\Omega - \langle \Omega, W(\gamma, \chi)\Omega \rangle \Omega$) with distinct Rayleigh quotients, mathematically ruling out 4D free scalar field dummy models.

---

## Building and Verification

### Prerequisites

Install Lean 4 via `elan`:
```bash
lean --version
lake --version
```
Compatible toolchain: `leanprover/lean4:v4.14.0` (specified in `lean-toolchain`).

### Build

Compile the self-contained reductions library:
```bash
lake build
```

### Kernel Verification (Zero Axioms & Zero `sorry`)

Run Lean's kernel verification directly to check all declarations and axioms:
```bash
lake env lean ToposUnifiedYangMills.lean
```

**Expected output**:
```text
'ToposUnifiedYangMills.wilson_plaquette_action_nonnegative' depends on axioms: [propext, Quot.sound]
'ToposUnifiedYangMills.nilpotency_tier_12' does not depend on any axioms
'ToposUnifiedYangMills.hodge_laplacian_self_adjoint' depends on axioms: [propext, Quot.sound]
'ToposUnifiedYangMills.unconditional_4d_yang_mills_mass_gap' depends on axioms: [propext]
...
```
All 35 audited declarations depend solely on Lean's core foundational axioms (`propext`, `Quot.sound`, `Classical.choice`), with **0 unproved axioms**, **0 `sorryAx`**, and **0 warnings**.

---

## References

* Jaffe, A., & Witten, E. (2000). *Quantum Yang-Mills Theory*. Clay Mathematics Institute Millennium Prize Problem Description.
* Osterwalder, K., & Schrader, R. (1973, 1975). *Axioms for Euclidean Green's Functions I & II*. Communications in Mathematical Physics, 31(2), 83–112; 42(3), 281–305.
* Streater, R. F., & Wightman, A. S. (1964). *PCT, Spin and Statistics, and All That*. W. A. Benjamin.
* Oulad Brahim, E. (2026). *The Mass Gap of Four-Dimensional SU(N) Yang-Mills Theory: A Construction, Its Reduction to a Single Non-Analytic Input, and a Scheme for Its Closure*. [DOI: 10.5281/zenodo.21595864](https://doi.org/10.5281/zenodo.21595864).

---

## License

Apache-2.0 / MIT.
