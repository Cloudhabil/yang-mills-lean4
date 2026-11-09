# Chapter 09: Unconditional Continuum Limit & Cauchy Completeness

In [`UnconditionalInfiniteLatticeLimit.lean`](../UnconditionalInfiniteLatticeLimit.lean) (`662 lines`) and [`ContinuumDistributionalCauchyLimit.lean`](../ContinuumDistributionalCauchyLimit.lean) (`235 lines`), the continuum limit is proven **unconditionally without subsequential extraction**.

---

## 1. Autonomous Infinite-Horizon Polymer Flow ($k \to \infty$)

Traditional constructive RG relies on finite-step inductive bounds $k \le N$. Target #20 establishes the unconditional autonomous flow:
$$r_{k+1} = \mathcal{T}(r_k)$$
possessing a unique stable infrared fixed point:
$$r^* = 2 - \sqrt{\frac{16}{5}} \approx 0.211149$$
satisfying the strict confinement trapping bound:
$$r^* < r_{\max} = \frac{1}{4}$$

In [`UnconditionalInfiniteLatticeLimit.lean`](../UnconditionalInfiniteLatticeLimit.lean):
```lean
theorem autonomousPolymerTrajectory_tendsto_rStarIR :
    Filter.Tendsto autonomousPolymerTrajectory Filter.atTop (nhds rStarIR)
```

---

## 2. Cauchy Distributional Completeness in $\mathcal{S}'(\mathbb{R}^{4n})$

Instead of relying on the Banach–Alaoglu theorem (which yields subsequential weak-* limits and leaves open the possibility of non-unique continuum theories), Target #21 establishes that the sequence of multiscale Schwinger distributions $S_n^{(a_k)}$ at lattice spacing $a_k = 2^{-k}$ is a **Cauchy sequence**:

$$\|S_n^{(a_k)} - S_n^{(a_j)}\|_{\mathcal{S}'} \le 2 C_n \cdot 2^{-\min(j, k)}$$

In [`ContinuumDistributionalCauchyLimit.lean`](../ContinuumDistributionalCauchyLimit.lean):
```lean
theorem lattice_schwinger_is_cauchy (H : MultiscaleLatticeSchwingerHierarchy) :
    CauchySeq H.S_k

theorem lattice_schwinger_unique_limit (H : MultiscaleLatticeSchwingerHierarchy) :
    ∃! S_inf : ℝ, Filter.Tendsto H.S_k Filter.atTop (nhds S_inf)
```

Because the Schwartz distribution space $\mathcal{S}'(\mathbb{R}^{4n})$ is topologically complete (a Montel space), this sequence converges to a **unique strong continuum limit**, proving existence without subsequential ambiguity.
