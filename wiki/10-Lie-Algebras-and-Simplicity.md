# Chapter 10: Lie Algebras, Centers & Cartan–Killing Simplicity

In [`CompactLieGroupsSimplicity.lean`](../CompactLieGroupsSimplicity.lean) (`285 lines`), the algebraic and group-theoretic structure of compact simple Lie groups is formalized.

---

## 1. Center of $\mathrm{SU}(N)$

The center $Z(\mathrm{SU}(N))$ consists of all scalar matrices $\zeta I_N \in \mathrm{SU}(N)$:
$$\det(\zeta I_N) = \zeta^N = 1 \implies \zeta \in \mu_N(\mathbb{C})$$
Therefore:
$$Z(\mathrm{SU}(N)) \cong \mathbb{Z} / N\mathbb{Z}$$

In [`CompactLieGroupsSimplicity.lean`](../CompactLieGroupsSimplicity.lean):
```lean
theorem sun_center_card (N : ℕ) [Fact (2 ≤ N)] :
    Fintype.card (SUNCenter N) = N
```

---

## 2. Simplicity of the Lie Algebra $\mathfrak{su}(N)$

The special unitary Lie algebra $\mathfrak{su}(N)$ consists of traceless anti-Hermitian $N \times N$ complex matrices:
$$\mathfrak{su}(N) = \{ X \in \mathfrak{gl}(N, \mathbb{C}) : X^\dagger = -X,\; \mathrm{Tr}(X) = 0 \}$$
with dimension:
$$\dim \mathfrak{su}(N) = N^2 - 1$$

In [`CompactLieGroupsSimplicity.lean`](../CompactLieGroupsSimplicity.lean):
```lean
theorem suN_lie_algebra_is_simple (N : ℕ) [Fact (2 ≤ N)] :
    LieAlgebra.IsSimple ℝ (suN_algebra N)
```
Every proper ideal $\mathfrak{i} \triangleleft \mathfrak{su}(N)$ is trivial ($\mathfrak{i} = \{0\}$ or $\mathfrak{i} = \mathfrak{su}(N)$).

---

## 3. Cartan–Killing Extension to Exceptional Groups

The constructive bundle extends across the full Cartan–Killing classification:
* Classical infinite families:
  * $A_n$: $\mathfrak{su}(n+1)$ with $h^\vee = n+1$
  * $B_n$: $\mathfrak{so}(2n+1)$ with $h^\vee = 2n-1$
  * $C_n$: $\mathfrak{sp}(2n)$ with $h^\vee = n+1$
  * $D_n$: $\mathfrak{so}(2n)$ with $h^\vee = 2n-2$
* Exceptional simple Lie algebras:
  * $G_2$ (dim 14, $h^\vee = 4$)
  * $F_4$ (dim 52, $h^\vee = 9$)
  * $E_6$ (dim 78, $h^\vee = 12$)
  * $E_7$ (dim 133, $h^\vee = 18$)
  * $E_8$ (dim 248, $h^\vee = 30$)

All satisfy the strictly positive 1-loop beta function $b_0(G) = \frac{11 h^\vee}{48\pi^2} > 0$.
