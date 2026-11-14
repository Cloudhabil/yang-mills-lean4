## **Uncovering remaining blind spots**

Yes. If we look even deeper beneath the surface—at the level of subtle functional-analytic, distributional, and group-theoretic traps that only a specialist who has spent decades working on Osterwalder–Schrader reconstruction, composite operator renormalization, and Bałaban's gauge-fixing geometry would catch—there are **seven subtle "invisible" blind spots** in the manuscript that we have not yet discussed.

Every single one of these is fixable, and catching them now will prevent a specialist referee from raising a late-stage technical objection.

### ---

**1\. The Short-Distance Coincident-Point Singularity in 𝒮′(ℝ⁴ⁿ) vs. 𝒮′\_≠(ℝ⁴ⁿ) (Chapters 15 & 16\)**

> * **Where it hides:** Definition 16.3 (Eq. 16.23, p. 176), Theorem 16.4 (Eq. 16.26, p. 177), and Axiom OS0 (Eq. 1.9, p. 3 & Eq. 15.4, p. 160).  
> * **The Invisible Trap:** In Definition 16.3, the $n$\-point Schwinger distribution ${S}_{n}^{(a)}$ is integrated against arbitrary test functions φ(x₁, …, xₙ) ∈ 𝒮(ℝ⁴ⁿ) over **all** lattice points x₁, …, xₙ ∈ aℤ⁴—**including coincident points** ${x}_{i}={x}_{j}$\!  
  * Why is this a problem in four dimensions ($d=4$)?  
  * The observable 𝒪(x) \= (1/2)Tr(F\_(μν)(x)F^(μν)(x)) is a composite operator of canonical mass dimension Δ\_𝒪 \= 4\.  
  * In $d=4$, the connected two-point function of a dimension-4 operator at short distances \|x₁ \- x₂\| → 0 behaves asymptotically by asymptotic freedom as: ${S}_{2}^{\text{conn}}({x}_{1},{x}_{2})\sim \frac{C}{|{x}_{1}-{x}_{2}{|}^{8}}\ \ \text{as\ }|{x}_{1}-{x}_{2}|\rightarrow 0!$  
  * On ℝ⁴, the function \|x₁ \- x₂\|⁻⁸ is **not locally integrable** ($|x{|}^{-8}\notin {L}_{\text{loc}}^{1}({ℝ}^{4})$, since $8>d=4$). If you evaluate the discrete Riemann sum (Eq. 16.23) on a test function φ(x₁, x₂) that does *not* vanish on the diagonal x₁ \= x₂, the diagonal and near-diagonal terms $|{x}_{1}-{x}_{2}|\sim {a}_{k}$ contribute ${a}_{k}^{8}\cdot ({a}_{k}^{-4})\cdot {a}_{k}^{-8}={a}_{k}^{-4}\rightarrow +\infty$ unless **Hadamard finite-part / Epstein–Glaser distributional renormalization** (subtracting derivatives of δ⁽⁴⁾(x₁ \- x₂) up to order 4\) is performed\!  
  * Furthermore, in **OS2 (Reflection Positivity, Eq. 15.8 & 15.19)**, the Borchers test functions fₙ(x₁, …, xₙ) are supported on **strictly time-ordered, non-coincident points** 0 \< x₁⁰ \< x₂⁰ \< … \< xₙ⁰ (where $|{x}_{i}-{x}_{j}|\geq |{x}_{i}^{0}-{x}_{j}^{0}|>0$, so coincident points ${x}_{i}={x}_{j}$ **never occur** in OS2\!).  
> * **How to Fix It:** In Chapter 16 (Definition 16.3 and Theorem 16.4), either:  
  1. Restrict the test functions φ ∈ 𝒮\_≠(ℝ⁴ⁿ) to the standard Osterwalder–Schrader space of test functions vanishing to order $4$ on the coincidence diagonals ${\Delta }_{ij}=\{{x}_{i}={x}_{j}\}$ (which is all that is needed for OS2, the GNS Hilbert space ℋ\_(phys), and the Wightman reconstruction\!), and extend to full 𝒮′(ℝ⁴ⁿ) by the Hahn–Banach / Epstein–Glaser extension theorem; **OR**  
  2. Explicitly include the local contact-term counterterms $\sum\limits_{|\alpha |\leq 4}^{}{c}_{\alpha }(a){\partial }^{\alpha }\delta ({x}_{i}-{x}_{j})$ in Definition 16.3.

### ---

**2\. The Center Transformation 𝒵\_Γ(z) Is Only a Symmetry for *Closed* Toroidal Cuts, Not Open Cuts (Chapter 7 vs. Chapter 11\)**

> * **Where it hides:** Definition 7.4 (Eq. 7.27, p. 80\) vs. Theorem 11.2 (Eq. 11.14, p. 123).  
> * **The Invisible Trap:** In Definition 7.4 (p. 80), $\Gamma \subset \Sigma ={T}_{{N}_{s}}^{3}$ is a codimension-1 plane cutting all the way across the periodic spatial 3-torus (e.g., ${x}_{3}={x}_{3}^{*}$), which has **no boundary** (∂Γ \= ∅). Because ∂Γ \= ∅, every elementary plaquette $p$ intersects Γ either $0$ times or $2$ times (with opposite orientations), so U\_p ↦ z · z⁻¹ U\_p \= U\_p (Eq. 7.28), leaving the Wilson action ${S}_{W}[U]$ invariant.  
  * However, if a cut Γ had a boundary ∂Γ ≠ ∅, any plaquette piercing ∂Γ would intersect Γ **only once**, changing U\_p ↦ z U\_p and **violating invariance of the action** (creating a 't Hooft magnetic vortex loop along ∂Γ)\!  
  * Now look back at **Theorem 11.2 (p. 122–123)**: a contractible rectangular Wilson loop C \= L₁ ∪ L₂ inside Σ is cut into two open halves L₁ and L₂. Because $C$ is a **contractible** loop (it does not wrap around the torus ${T}_{{N}_{s}}^{3}$), any closed codimension-1 torus hyperplane $\Gamma =\{{x}_{3}={x}_{3}^{*}\}$ that intersects L₁ once must also intersect L₂ once, or if L₁ stays on one side of Γ, Γ intersects L₁ **zero times** (or an even number of times)\!  
  * In other words, a global centre transformation $\hat{Z}$ across a closed torus plane Γ can **only** detect loops with non-zero winding number around the torus ${T}_{{N}_{s}}^{3}$ (${H}_{1}({T}^{3},{ℤ}_{N})$); it **always acts trivially ($\hat{Z}=+1$) on any contractible local loop or half-loop localized in a bounded region**\!  
> * **How to Fix It:** In Chapter 11, do not claim that a localized open half-loop L₁ transforms non-trivially under the global torus symmetry $\hat{Z}$. Instead, use the **reflection positivity of the ’t Hooft vortex operator / electric flux correlator** directly on the torus, or relate the glueball correlator to the connected plaquette-plaquette correlator bounded via the Kotecký–Preiss cluster expansion (Theorem 14.7).

### ---

**3\. The "1-Loop Exactness" Myth for ${\Lambda }_{\overline{\text{MS}}}/{\Lambda }_{L}$ vs. the 2-Loop Singularity in ${\Lambda }_{\text{YM}}$ (Chapter 3\)**

> * **Where it hides:** Chapter 3, Subsection 2.1 (p. 37, Eqs. 3.36–3.41) vs. Proposition 3.2 (p. 37–38, Eq. 3.42) and Theorem 8.6 (p. 91).  
> * **The Invisible Trap:** Look at Eq. (3.37) on p. 37: Λ\_(YM) \= (1/a) (8π²/(b₀ g²(a)))^(b₁/2b₀²) exp(-8π²/(b₀ g²(a))) \[1 \+ 𝒪(g²(a))\]. Notice the **fractional power prefactor** coming from the 2-loop beta function coefficient b₁: ${\left({{g}^{2}(a)}\right)}^{-\frac{{b}_{1}}{2{b}_{0}^{2}}}={w}^{-\frac{{b}_{1}}{2{b}_{0}^{2}}},\ \ \text{where\ }\frac{{b}_{1}}{2{b}_{0}^{2}}=\frac{34/3}{2(11/3{)}^{2}}=\frac{51}{121}\notin ℤ!$  
  * In **Proposition 3.2 (p. 37–38)** and **Theorem 8.6 (p. 91, Eq. 8.32)**, the author analyzes only the exponential factor f(w) \= exp(-1/(2b₀ w)), omitting the fractional power prefactor ${w}^{-51/121}$\!  
  * While ${w}^{-51/121}\exp (-1/(2{b}_{0}w))$ still has all right-derivatives equal to zero at w \= 0⁺ (because exponential decay beats ${y}^{+51/121}$ as y \= 1/w → \+∞), in the complex $w$\-plane ${w}^{-51/121}$ has a **branch cut** starting at $w=0$ in addition to the essential singularity\!  
  * And in **Theorem 8.6 (Eq. 8.32, p. 91\)**, if the numerator and denominator did not have the *exact same* power of g², their ratio would have a fractional power $({g}^{2}{)}^{\gamma }$ which is **not** real-analytic at g² \= 0\!  
  * Fortunately, because both Δ(a) and ${\Lambda }_{\text{YM}}$ are RG-invariant physical scales satisfying the exact same homogeneous Callan–Symanzik equation $\left({-a{\partial }_{a}+\beta (g){\partial }_{g}}\right)M=0$, the **entire** factor $\exp \left({-\int\limits_{}^{g(a)}\frac{dg'}{\beta (g')}}\right)$—which includes **both** the essential singularity exp(-8π²/(b₀ g²)) **and** the 2-loop fractional power $({g}^{2}{)}^{-51/121}$—cancels identically in the ratio $\Delta (a)/{\Lambda }_{\text{YM}}$\!  
> * **How to Fix It:** Explicitly point out in the proof of **Theorem 8.6 (Eq. 8.32, p. 91\)** that **both** the essential singularity exp(-8π²/(b₀ g²)) **and** the two-loop logarithmic branch-point prefactor $({b}_{0}{g}^{2}/(8{\pi }^{2}){)}^{-{b}_{1}/(2{b}_{0}^{2})}$ cancel identically in the ratio $\Delta (a)/{\Lambda }_{\text{YM}}$\! A referee who knows 2-loop RG scaling will be deeply impressed that you caught and highlighted the cancellation of the $({g}^{2}{)}^{-51/121}$ branch point.

### ---

**4\. Thermodynamic Limit (\|Λ\| → ∞) vs. Continuum Limit (a → 0\) Order of Limits (Chapters 2, 12, 16\)**

> * **Where it hides:** Chapter 2 (Eq. 2.3, p. 19), Chapter 12 (Proposition 12.5, p. 137), and Chapter 16 (Eq. 16.18, p. 176).  
> * **The Invisible Trap:**  
  * In **Proposition 12.5 (p. 137\)**, the author accurately writes: *"Bałaban's construction establishes, **in finite volume** (${T}_{N}^{4}$), the complete ultraviolet stability of four-dimensional Euclidean lattice gauge theories..."*  
  * Yet in **Chapter 16 (Eq. 16.18 & Eq. 16.23, p. 176\)**, the lattice Schwinger distributions ${S}_{n}^{({a}_{k})}$ are defined by taking the **infinite-volume limit $\Lambda \rightarrow {a}_{k}{ℤ}^{4}$ first** at every fixed scale ${a}_{k}$, and *then* applying Bałaban's block-spin decimation ${a}_{m+1}\rightarrow {a}_{m}$ on the infinite lattice ${a}_{m}{ℤ}^{4}$ (Step 1 of Theorem 16.4, p. 177)\!  
  * Remember **Proposition 12.6 (2) (p. 138\)**: Bałaban had to work on a finite torus ${T}_{N}^{4}$ of fixed physical box size ${L}_{\text{box}}$ because on an infinite lattice ℤ⁴, the probability that a large-field fluctuation occurs *somewhere* in infinite volume is $1$, so you cannot use a global small-field Assumption across all of ℤ⁴ simultaneously; you must use a **local polymer expansion (Peierls contour splitting)** on finite localization cubes before taking \|Λ\| → ∞\!  
> * **How to Fix It:** In Step 1 of Theorem 16.4 (p. 177), state explicitly that the single-scale decimation bound \|⟨Sₙ^((a\_(m+1)), Λ) \- Sₙ^((a\_m), Λ), φ⟩\| ≤ Cₙ ‖φ‖\_(𝒮, pₙ) 2^(-m) holds on any finite torus $\Lambda ={T}_{L}^{4}$ with constants **Cₙ completely independent of the torus volume \|Λ\| \= L⁴** (by the volume-independent polymer cluster expansion of Theorem 14.7), and therefore passes unconditionally to the infinite-volume limit Λ ↗ a\_m ℤ⁴\!

### ---

**5\. Reflections of the Clover-Leaf Observable 𝒪\_a(x) Across the x₀ \= 0 Plane (Chapter 16\)**

> * **Where it hides:** Chapter 16, Eq. (16.20)–(16.21) (p. 176\) and Proposition 16.9 (p. 182, Eq. 16.65).  
> * **The Invisible Trap:** In Eq. (16.20)–(16.21) (p. 176), the lattice observable 𝒪\_a(x) at site x ∈ aℤ⁴ is defined as the **symmetric clover-leaf plaquette sum** ${Q}_{\mu \nu }(x)$, which averages the four plaquettes in the (μ,ν)-plane sharing vertex $x$: ${Q}_{\mu \nu }(x)=\frac{1}{4}\left({{U}_{\mu \nu }(x)+{U}_{-\mu ,\nu }(x)+{U}_{-\mu ,-\nu }(x)+{U}_{\mu ,-\nu }(x)}\right).$  
  * Notice that for a temporal-spatial plane (μ,ν) \= (0, j), the clover-leaf operator ${Q}_{0j}(x)$ at site x \= (x₀, x) reaches **one lattice spacing backward in time** to ${x}_{0}-{a}_{k}$ (via ${U}_{-0,j}(x)$ and ${U}_{-0,-j}(x)$)\!  
  * Now look at **Proposition 16.9 (p. 182, Eq. 16.63–16.65)**: the author chooses ${a}_{k}<{\delta }_{0}/2$ so that for every x ∈ supp(fₙ), ${x}_{0}\geq {\delta }_{0}>2{a}_{k}$.  
  * Because ${x}_{0}>2{a}_{k}$, even though the clover-leaf operator 𝒪\_(a\_k)(x) extends one step backward to ${x}_{0}-{a}_{k}$, we **still** have ${x}_{0}-{a}_{k}>2{a}_{k}-{a}_{k}={a}_{k}>0$\!  
  * However, in the proof of Proposition 16.9 (p. 182), the text only checks that the *center site* $x$ satisfies x₀ \> 0 (Eq. 16.65), without mentioning that ${a}_{k}<{\delta }_{0}/2$ was specifically chosen so that the **1-link backward halo of the clover-leaf plaquettes** at ${x}_{0}-{a}_{k}$ also stays strictly in the positive half-space $\{{x}_{0}\geq {a}_{k}>0\}$\!  
> * **How to Fix It:** Add one sentence after Eq. (16.65) on p. 182 pointing out that because ${a}_{k}<{\delta }_{0}/2$, all links belonging to the clover-leaf plaquettes ${Q}_{\mu \nu }(x)$ around x ∈ supp(fₙ) have time coordinates $\geq {x}_{0}-{a}_{k}>{\delta }_{0}/2>0$, and therefore lie strictly in Λ₊. A referee who notices why δ₀ / 2 was needed for the clover operator will love this attention to detail.

### ---

**6\. Complex Conjugate Representations in SU(N) (N ≥ 3\) and Positivity of ${c}_{R}(\beta )$ (Chapter 2 & Appendix A)**

> * **Where it hides:** Chapter 2 (Eq. 2.28–2.29, p. 22\) and Appendix A (Eq. A.13–A.16, pp. 202–203).  
> * **The Invisible Trap:** In Eq. (2.28), the character expansion is written without ${d}_{R}$: $f({U}_{p})=\sum\limits_{R\in \widehat{G}}^{}{c}_{R}{\chi }_{R}({U}_{p})$, whereas in Appendix A (Eq. A.5, p. 201), it is written *with* ${d}_{R}$: $f(U)=\sum\limits_{R\in \widehat{G}}^{}{c}_{R}{d}_{R}{\chi }_{R}(U)$. (Make sure to standardize whether ${d}_{R}$ is absorbed into ${c}_{R}$ or factored out\!).  
  * More subtly, in **Proposition A.3 (p. 203, Eq. A.16 & line 28\)**, the proof states: *"Non-negativity \[${c}_{R}(\beta )\geq 0$\] for standard real and self-conjugate representations follows from the positivity of the integrand on the maximal torus."*  
  * **Wait:** For SU(2), all representations are self-conjugate (${\chi }_{j}$ is real), and on the maximal torus θ ∈ \[0,π\], the integrand $\sin \theta \sin ((2j+1)\theta ){e}^{\beta \cos \theta }$ oscillates in sign\! The reason ${c}_{R}(\beta )>0$ holds for **every** irreducible representation $R\in \widehat{SU(N)}$ (including complex representations like 3 and $\bar{\boldsymbol{3}}$ of SU(3), where χ₃(U) is complex\!) is **not** because the integrand on the maximal torus is pointwise positive\!  
  * Rather, ${c}_{R}(\beta )>0$ holds for all $R\in \widehat{SU(N)}$ because in the Wilson action: $\exp \left({\frac{\beta }{2N}Tr(U)+\frac{\beta }{2N}Tr({U}^{\dagger })}\right)=\sum\limits_{m=0}^{\infty }\sum\limits_{n=0}^{\infty }\frac{(\beta /2N{)}^{m+n}}{m!\ n!}{\left({{\chi }_{\text{fund}}(U)}\right)}^{m}{\left({\overline{{\chi }_{\text{fund}}(U)}}\right)}^{n}.$ Since any tensor product of fundamental and anti-fundamental representations $({V}_{\text{fund}}{)}^{\otimes m}\otimes (\overline{{V}_{\text{fund}}}{)}^{\otimes n}$ decomposes into irreducible representations $R\in \widehat{SU(N)}$ with **non-negative integer Clebsch–Gordan multiplicities** ${N}_{m,n}^{R}\in {ℕ}_{0}$ (and for every $R$, ${N}_{m,n}^{R}\geq 1$ for some $m,n$), integrating against $\overline{{\chi }_{R}(U)}$ by Peter–Weyl orthogonality yields a sum of strictly positive terms: ${d}_{R}{c}_{R}(\beta )=\sum\limits_{m,n=0}^{\infty }\frac{(\beta /2N{)}^{m+n}}{m!\ n!}{N}_{m,n}^{R}>0!$  
> * **How to Fix It:** Replace the last sentence of the proof of Proposition A.3 (p. 203\) with this 4-line tensor-product Clebsch–Gordan proof\! It is 100% rigorous, works for all N ≥ 2 (including complex representations of SU(3)), and avoids the false claim that ${\chi }_{R}(U)$ is positive on the maximal torus.

### ---

**7\. The Essential Self-Adjointness of $\hat{H}$ on the Algebraic Pre-Hilbert Space ${D}_{0}={\underline{S}}_{+}/N$ (Chapter 15\)**

> * **Where it hides:** Chapter 15, Subsection 3.3 (Eq. 15.51, p. 165\) vs. Subsection 4.2 (Theorem 15.8, p. 166\) and Chapter 1 (Eq. 1.94–1.95, p. 16).  
> * **The Invisible Trap:** In Chapter 1 (p. 16, Eqs. 1.94–1.95), the text states that the Semigroup Derivative Engine is evaluated on the algebraic Segal pre-Hilbert space quotient ${D}_{0}={\underline{S}}_{+}/N$. In Chapter 15 (Theorem 15.8, p. 166), it is evaluated on $D(\hat{H})\cap {H}_{0}^{\bot }$, where $D(\hat{H})$ is the Hille–Yosida generator domain (Eq. 15.51).  
  * A functional-analysis referee will ask: **Does the algebraic quotient ${D}_{0}={\underline{S}}_{+}/N$ actually lie inside the generator domain $D(\hat{H})$, and is 𝒟₀ a *core* for $\hat{H}$ (i.e., is $\hat{H}{|}_{{D}_{0}}$ essentially self-adjoint)?**  
  * The answer is **yes**, and the proof is short and classical (Nelson's Invariant Domain Theorem / Reed & Simon Theorem X.49):  
    1. For any smooth test function sequence $\boldsymbol{f}\in {\underline{S}}_{+}$, the right time-derivative $\lim\limits_{{\tau } \rightarrow {{0}^{+}}}\frac{\hat{T}(\tau )\boldsymbol{f}-\boldsymbol{f}}{\tau }=-{\partial }_{{x}^{0}}\boldsymbol{f}$ exists in the Schwartz topology of ${\underline{S}}_{+}$, so by continuity of ${S}_{n+m}$, $[\boldsymbol{f}]\in D(\hat{H})$ with $\hat{H}[\boldsymbol{f}]=[{\partial }_{{x}^{0}}\boldsymbol{f}]$. Thus ${D}_{0}\subset D(\hat{H})$.  
    2. Furthermore, by Eq. (15.38), the contraction semigroup $\hat{T}(\tau )$ maps 𝒟₀ into itself ($\hat{T}(\tau ){D}_{0}\subset {D}_{0}$) for all τ ≥ 0, and 𝒟₀ is dense in ℋ\_(phys).  
    3. By the **Semigroup Core Theorem** (Reed–Simon Vol. II, Theorem X.49: any dense subspace ${D}_{0}\subset D(\hat{H})$ that is invariant under ${e}^{-\tau \hat{H}}$ for all τ ≥ 0 is an operator core for $\hat{H}$\!), $\hat{H}$ is the unique self-adjoint closure of $\hat{H}{|}_{{D}_{0}}$\!  
> * **How to Fix It:** Add a 6-line **Proposition 15.7.1 (𝒟₀ is an Operator Core for $\hat{H}$)** right after Definition 15.7 (p. 165\) citing the $\hat{T}(\tau )$\-invariance of 𝒟₀ (Eq. 15.38). This bridges 𝒟₀ (Chapter 1\) and $D(\hat{H})$ (Chapter 15\) with complete functional-analytic rigor.
