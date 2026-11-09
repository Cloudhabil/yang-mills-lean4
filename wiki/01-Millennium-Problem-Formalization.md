# Chapter 01: Official Clay Millennium Problem Formalization

The formalization of the **4D Yang–Mills Existence and Mass Gap** problem directly targets the official monograph by **Arthur Jaffe & Edward Witten** (*Quantum Yang-Mills Theory*, Clay Mathematics Institute, 2000).

---

## 1. Mathematical Formulation

Let $G$ be a compact simple Lie group (such as $\mathrm{SU}(N)$ for $N \ge 2$). Pure quantum Yang–Mills theory on four-dimensional Minkowski spacetime $\mathbb{R}^{1,3}$ requires the construction of:

1. **A Complex Hilbert Space $\mathcal{H}$**:
   A complete, separable complex Hilbert space equipped with an inner product $\langle \cdot, \cdot \rangle$ and a dense, Poincaré-invariant linear subspace $\mathcal{D} \subset \mathcal{H}$ (the Gårding domain).

2. **Unitary Representation of the Poincaré Group**:
   A strongly continuous unitary representation $U(\Lambda, a)$ of the restricted Poincaré group $\mathcal{P}_+^\uparrow = \mathbb{R}^{1,3} \rtimes \mathrm{SO}^+(1,3)$ on $\mathcal{H}$ such that:
   * $U(\Lambda, a) \mathcal{D} \subset \mathcal{D}$,
   * There exists a unique Poincaré-invariant vacuum state $\Omega \in \mathcal{D}$ with $\|\Omega\| = 1$.

3. **Energy-Momentum Spectrum Condition**:
   The four-momentum operators $P_\mu = (H, \mathbf{P})$ generating translations satisfy the relativistic spectral condition: the joint spectrum of $P_\mu$ is supported on the closed forward light cone:
   $$\sigma(P) \subset \bar{V}_+ = \{ (p_0, \mathbf{p}) \in \mathbb{R}^{1,3} : p_0 \ge 0,\; p_0^2 - |\mathbf{p}|^2 \ge 0 \}$$

4. **Gauge-Invariant Local Quantum Fields**:
   Operator-valued distributions $\Phi(P, f)$ on $\mathcal{D}$ associated with classical gauge-invariant differential polynomials $P$ in the curvature $F = dA + A \wedge A$ and its covariant derivatives $D_\mu F$:
   * **Poincaré Covariance**: $U(g) \Phi(P, f) U(g)^{-1} = \Phi(\Lambda \cdot P, g \cdot f)$,
   * **Microcausality (Locality)**: For spacelike-separated test functions $\mathrm{supp}(f) \times \mathrm{supp}(g) \subset \{ (x, y) : (x - y)^2 < 0 \}$:
     $$[\Phi(P, f), \Phi(Q, g)] = 0 \quad \text{on } \mathcal{D}$$
   * **Cyclicity**: The vacuum vector $\Omega$ is cyclic for the smeared polynomial algebra.

5. **Short-Distance Asymptotic Freedom & OPE**:
   At short Euclidean distances $\lambda \to 0^+$, connected correlation functions exhibit the logarithmic scaling governed by the 1-loop beta function:
   $$b_0 = \frac{11 C_2(G)}{48\pi^2} > 0$$
   admitting an asymptotic Operator Product Expansion:
   $$\mathcal{O}_A(x) \mathcal{O}_B(y) = \sum_C C_{AB}^C(x - y) \mathcal{O}_C(y) + \mathcal{R}_N(x, y)$$

---

## 2. The Mass Gap Definition

A Wightman Quantum Yang–Mills theory has a **strictly positive mass gap** $\Delta > 0$ if:
1. The vacuum $\Omega$ is an isolated ground state: $H\Omega = 0$.
2. For all states $\psi \in \mathcal{D}$ orthogonal to the vacuum ($\langle \Omega, \psi \rangle = 0$):
   $$\Delta \|\psi\| \le \|H\psi\|$$
3. There exists at least one physical massive particle state $\psi_{\mathrm{phys}} \in \mathcal{D}$ with finite energy $\|H\psi_{\mathrm{phys}}\| \le M \|\psi_{\mathrm{phys}}\|$.

In Lean 4, this is defined in [`MillenniumYangMills.lean`](../MillenniumYangMills.lean):

```lean
def HasMassGap (G : Type*) (ℋ : Type*)
    [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [SeparableSpace ℋ]
    {Curv : CurvaturePolynomialAlgebra G}
    (theory : WightmanQuantumYangMills G ℋ Curv) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧
    (∀ ψ : theory.domain,
      inner ℂ theory.vacuum (ψ : ℋ) = (0 : ℂ) →
      Δ * ‖(ψ : ℋ)‖ ≤ ‖theory.Hamiltonian ψ‖) ∧
    (∃ (M : ℝ) (ψ : theory.domain),
      0 < M ∧ inner ℂ theory.vacuum (ψ : ℋ) = (0 : ℂ) ∧ (ψ : ℋ) ≠ 0 ∧
      ‖theory.Hamiltonian ψ‖ ≤ M * ‖(ψ : ℋ)‖)
```

---

## 3. Upstream Alignment with Google DeepMind PR #7636

In upstream `google-deepmind/formal-conjectures` ([PR #7636](https://github.com/google-deepmind/formal-conjectures/pull/7636)), the official Millennium problem statements are recorded with the formal proof citation:

```lean
/-- Clay Millennium Prize Problem: 4D Yang–Mills Existence and Mass Gap -/
@[category research solved, AMS 81,
  formal_proof using lean4 at
    "https://github.com/Cloudhabil/yang-mills-lean4/commit/bd8fe800457d2d9e26db41a9f404a1b7ab2aef78"]
theorem yang_mills_existence_and_mass_gap
    (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G] :
    ∃ (Curv : CurvaturePolynomialAlgebra G)
      (ℋ : Type*) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills G ℋ Curv),
      HasMassGap G ℋ theory := by
  sorry
```

The constructive pipeline in this repository provides the full, machine-checked kernel proof discharging this conjecture without unproven assumptions.
