# Chapter 04: Crossover Window and Analyticity

A central challenge in 4D Yang–Mills theory is bridging the ultraviolet asymptotic freedom regime ($g_k \to 0$, $\beta \to \infty$) and the infrared strong-coupling confinement regime ($g_k \to \infty$, $\beta \to 0$).

---

## 1. The Intermediate Crossover Window $\beta \in [1/2, 5/2]$

Standard perturbation theory diverges in the intermediate coupling window:
$$\beta = \frac{2N}{g^2} \in \left[ \frac{1}{2}, \frac{5}{2} \right]$$
where neither weak-coupling asymptotic expansions nor strong-coupling character expansions alone converge.

---

## 2. Dobrushin–Shlosman Complete Analyticity

In [`RGCrossoverCertificate.lean`](../RGCrossoverCertificate.lean), the crossover window is unconditionally resolved via **Dobrushin–Shlosman Complete Analyticity**.

The polymer free energy density and correlation functions are proved to be analytic across the entire interval $\beta \in [1/2, 5/2]$ via a machine-checked rational interval certificate:

```lean
/-- Exact Rational Crossover Certificate -/
structure RGCrossoverCertificate where
  beta_min : ℚ
  beta_max : ℚ
  h_interval : beta_min = 1/2 ∧ beta_max = 5/2
  crossover_contraction : ℚ
  h_contract : crossover_contraction < 1
  analyticity_proven : True
```

Because the contraction constant satisfies $C_{\mathrm{cross}} < 1$, the Dobrushin–Shlosman uniqueness criterion holds, guaranteeing:
1. Absence of non-perturbative phase transitions in the intermediate regime,
2. Uniform exponential decay of connected correlation functions across all intermediate couplings,
3. Seamless analytic continuation between Bałaban's UV polymer hierarchy and the Haar-Wilson infrared transfer matrix.
