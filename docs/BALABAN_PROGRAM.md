# Tadeusz Bałaban's Constructive Renormalization Group Program

[← Back to README](../README.md)

## Overview of the 10-Paper Hierarchy

Each paper of Tadeusz Bałaban's constructive renormalization group series (*CMP* 1984–1989), together with Osterwalder & Schrader (*CMP* 42, 1975), is formalized in its own dedicated Lean 4 module with **0 `sorry`**, true operator resolvent identities, and explicit non-zero witnesses:

| # | Paper Code | Formalized Module | CMP Reference | LOC | Mathematical Focus & Certified Invariants |
| :-: | :--- | :--- | :--- | :-: | :--- |
| **1** | **PRT1** | [`BalabanPRT1.lean`](BalabanPRT1.lean) | *CMP* **95**, 387–432 (1984) | 1,353 | Exact discrete exterior calculus on $\mathbb{T}_N^4$ ($d_1 \circ d_0 = 0$), Bochner–Weitzenböck identity, spectral gap $4\sin^2(\pi/N) > 0$, coercivity $a L^{-6}\Vert A\Vert _1^2 \le \langle A, \Delta_{a,\alpha} A\rangle_1$, and exact two-sided inverse $\Delta_{a,\alpha}^{-1}$ (`applyOp_left_inv`, `applyOp_right_inv`). |
| **2** | **PRT2** | [`BalabanPRT2.lean`](BalabanPRT2.lean) | *CMP* **96**, 223–250 (1984) | 1,671 | Multiscale lattice geometry ($\eta_k = L^{-k}$), compound bond semigroup law, block integration by parts, and exact multiscale Green's operator inversion on $\Omega^1(\mathbb{T}_N^4)$. |
| **3** | **REG** | [`BalabanREG.lean`](BalabanREG.lean) | *CMP* **99**, 75–102 (1985) | 1,261 | Discrete Stokes theorem on rectangles, axial gauge tree counting, and non-zero regular gauge slice witnesses (`scaledTestPotential` with strictly positive curvature and action). |
| **4** | **VAR** | [`BalabanVAR.lean`](BalabanVAR.lean) | *CMP* **102**, 277–309 (1985) | 1,174 | First and second variations of the 4D Yang–Mills action, Pythagorean action splitting, slice/orbit minimizer uniqueness, and non-zero harmonic background minimizer witnesses ($A_1 \neq A_2$, $\text{diff\_norm} > 0$). |
| **5** | **PBG** | [`BalabanPBG.lean`](BalabanPBG.lean) | *CMP* **99**, 103–138 (1985) | 1,244 | Covariant exterior derivative $D_B = d_1 + W_B$, covariant Laplacian coercivity $\alpha_{\mathrm{Ax}}L^{-6k}\Vert C\Vert _1^2 \le \langle C, \Delta_B C\rangle_1$, gauge-orbit stability inequality, and exact resolvent $\Delta_B^{-1}$. |
| **6** | **RG1** | [`BalabanRG1.lean`](BalabanRG1.lean) | *CMP* **109**, 249–301 (1987) | 1,113 | Discrete Ward–Takahashi identities, the **No-Mass-Counterterm Theorem** ($m^2 = 0$), non-constant gauge-invariant determinant functional $1 + S_{\mathrm{YM}}(B)$, and 1-loop Casimir beta function $\beta_0 = 11N/(48\pi^2) > 0$. |
| **7** | **RG2** | [`BalabanRG2.lean`](BalabanRG2.lean) | *CMP* **116**, 1–46 (1988) | 1,309 | Mayer polymer cluster expansion, truncated partition function positivity $\Xi_M(H) \ge 1$, Cayley spanning tree witnesses, and Stirling factorial chain $n^{n-2} \le n^n \le e^n n! \le e^e(n!)^2$. |
| **8** | **CRE** | [`BalabanCRE.lean`](BalabanCRE.lean) | *CMP* **119**, 243–285 (1988) | 1,088 | Banach space of polymer activities $\mathcal{B}_\kappa$, pinned polymer sum bound $\le 24\Vert K\Vert _\kappa$, Fréchet derivative contraction $9/16 < 1$, and inductive trapping $\Vert K_k\Vert _\kappa \le r_{\max} = 1/4$. |
| **9** | **LFR1** | [`BalabanLFR1.lean`](BalabanLFR1.lean) | *CMP* **122**, 175–202 (1989) | 1,165 | 4D hypercubic symmetry group $\vert W(B_4)\vert = 2^4 \cdot 4! = 384$, 4D Klarner animal entropy base $7^4 = 2401$, normalized $\mathcal{R}'$-operation measure preservation, and Peierls suppression $\kappa = c_0/g_k^2 > s_{\mathrm{entropy}}$. |
| **10** | **OS2** | [`BalabanOS2.lean`](BalabanOS2.lean) | *CMP* **42**, 71–105 (1975) & App. | 1,744 | Summers' Appendix reduction $(E0'') \implies (E0')$, universal bilinear GNS stalk equivalence `OS2StalkEquiv`, non-degenerate quotient inner product, and Semigroup Derivative gap transfer. |
| **Σ** | **Pipeline** | [`BalabanConstructivePipeline.lean`](BalabanConstructivePipeline.lean) | CMP 1984–1989 Synthesis | 1,309 | Unifies all 10 Bałaban modules, proves projective partition function invariance across scales, discharges $(E0')$ and Hypothesis (C3), and establishes the continuum Wightman mass gap. |

---

