# Synchronization with Google DeepMind's formal-conjectures (PR #7636)

[← Back to README](../README.md)

## PR #7636 Architecture & Formal Proof Citation

The specification module [`MillenniumYangMills.lean`](MillenniumYangMills.lean) (`1,465 lines`) is synchronized 1-to-1 with the Clay Millennium Prize specification in Google DeepMind's [`google-deepmind/formal-conjectures` PR #7636](https://github.com/google-deepmind/formal-conjectures/pull/7636):

1. **Higher $\mathrm{Ad}(G)$-Invariant Multilinear Contractions (`inv_contract` & `Poly_generated_by_inv_contract`)**:
   For $\mathrm{SU}(N \ge 3)$, quadratic trace contractions $\mathrm{Tr}(F_{\mu\nu}F_{\rho\sigma})$ do not generate the full algebra of $\mathrm{Ad}(G)$-invariant curvature polynomials (missing the cubic Casimir $d_{abc}F^a F^b F^c$ / $C$-odd Odderon sector). `CurvaturePolynomialAlgebra` includes arbitrary degree-$r$ $\mathrm{Ad}(G)$-invariant multilinear contractions `inv_contract` and the inductive generation closure `GeneratedByInvContract`.
2. **Spacetime Lorentz & Euclidean Covariance (`transformLie` & `transform`)**:
   Includes the spacetime $4 \times 4$ matrix action on curvature jets (`transformLie_one`, `transformLie_mul`, `transformLie_F`, `transformLie_covDeriv`) so that Wightman axiom (W1) and Euclidean axiom (OS1) transform internal indices of derivative jets and tensor components properly under $\mathcal{P}_+^\uparrow$ and $\mathrm{SO}(4)$.
3. **Explicit Stress-Energy Tensor Formula & Conservation (`stress_energy_def` & `stress_tensor_conserved`)**:
   Pins $T_{\mu\nu}$ to the symmetric gauge-invariant Yang–Mills formula $T_{\mu\nu} = \sum_\alpha \langle F_{\mu\alpha}, F_{\nu\alpha}\rangle_{\mathrm{Ad}} - \frac{1}{4}\eta_{\mu\nu}\sum_{\alpha,\beta}\langle F_{\alpha\beta}, F_{\alpha\beta}\rangle_{\mathrm{Ad}}$, enforces $\partial^\mu T_{\mu\nu} = 0$ on $\mathcal{D}$, and links spatial integrals of $T_{0\mu}$ to $(H, P^i)$.
4. **Minkowski Spacelike Connected 2-Point Scaling**:
   States short-distance asymptotic freedom directly on the connected Wightman 2-point vacuum expectation value at spacelike separation $\eta(x, x) < 0$.
5. **1-to-1 Constructive Deduction**:
   In [`OsterwalderSchraderReconstruction.lean`](OsterwalderSchraderReconstruction.lean), `sun_millennium_statement_of_constructive_pipeline` outputs the exact existential signature of `yang_mills_sun_mass_gap`.

---

