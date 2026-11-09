# Chapter 05: Haar-Wilson Lattice & Transfer Matrix

In the infrared (strong-coupling) regime, confinement and the positive spectral gap are established via pure Haar integration and the full 4D Osterwalder–Seiler transfer operator.

---

## 1. Pure Haar Measure on Compact Lie Groups

In [`HaarWilsonLattice.lean`](../HaarWilsonLattice.lean) (`3,798 lines`), invariant Haar integration on compact Lie groups $G$ is formalized constructively:
* Left and right translation invariance: $\int_G f(g x) dg = \int_G f(x) dg = \int_G f(x g) dg$,
* Normalization: $\int_G 1 dg = 1$,
* Inversion invariance: $\int_G f(g^{-1}) dg = \int_G f(g) dg$.

---

## 2. The Full 4D Osterwalder–Seiler Transfer Operator

In 4-dimensional Euclidean lattice gauge theory on spatial torus $\mathbb{T}_L^3$, the time evolution operator $T$ is given by the symmetric product:
$$T_{\mathrm{full}}(L, \beta) = M_{\beta/2} T_{\mathrm{elec}}(\beta) M_{\beta/2}$$
where:
* $M_{\beta/2} = \exp\left( \frac{\beta}{2} \sum_{p \subset \text{spatial}} \mathrm{Re}\,\mathrm{Tr}\, U_p \right)$ is the magnetic spatial plaquette interaction,
* $T_{\mathrm{elec}}(\beta)$ is the electric link kinetic kernel given by the heat kernel on $G^{3L^3}$.

---

## 3. Uniform-in-Volume Spectral Gap

In [`HaarWilsonLattice.lean`](../HaarWilsonLattice.lean), the spectral gap is proven to be strictly bounded below, **uniformly in the spatial lattice size $L \in \mathbb{N}$**:

```lean
theorem full_4d_osterwalder_seiler_transfer_operator_gap
    (L : ℕ) (β : ℝ) (hβ : 0 < β) (ψ : LatticeState L)
    (h_ortho : innerProduct ψ vacuumState = 0) :
    ‖T_full L β ψ‖ ≤ (1 - Real.exp (- 2 * β)) * ‖ψ‖
```

Since the contraction factor satisfies:
$$\lambda_{\max} = 1 - e^{-2\beta_{\mathrm{IR}}} < 1$$
the spectral gap $\Delta_{\mathrm{lat}} = -\log(1 - e^{-2\beta}) > 0$ never closes as $L \to \infty$, establishing confinement and physical glueball masses.
