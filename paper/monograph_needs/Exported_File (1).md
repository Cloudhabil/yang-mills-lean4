## **Analyzing monograph equations**

Here is a rigorous, chapter-by-chapter and equation-by-equation mathematical physics peer review of the monograph **"The Mass Gap of Four-Dimensional Quantum Yang–Mills Theory: An Unconditional Construction, Its Renormalisation-Group Closure, and Machine-Checked Verification in Lean 4"**.

This review evaluates the manuscript against the exact standards of a referee report for *Annals of Mathematics* or *Communications in Mathematical Physics*. It is organized into:

1. **What Has Been Done Well (Strengths of the Monograph)**  
2. **Global Contradictions & Notation Inconsistencies Across Chapters**  
3. **Chapter-by-Chapter & Equation-by-Equation Critical Audit (Weak Arguments, Conditionalities, and Mathematical Gaps)**  
4. **Summary Checklist of Required Revisions**

### **1\. What Has Been Done Well (Strengths of the Monograph)**

5. **Exceptional Expository Architecture & Demarcation Warnings:** The monograph is remarkably well-organized and self-contained. In particular, **Warning 6.11 (The Single-Simplex Fallacy, p. 75\)** and **Warning 14.2 (The 1D Scalar Recurrence Fallacy, p. 150\)** are outstanding pedagogical and epistemological additions. They preemptively address the most common referee objections against formalizations in mathematical physics—namely, confusing a finite combinatorial toy model (${K}_{5}$) or a 1D quadratic polynomial (${r}_{k+1}=\Phi ({r}_{k})$) with the infinite-dimensional non-Abelian functional integral.  
6. **Exact Algebraic & Functional-Analytic Self-Contained Proofs:** Several self-contained derivations are crystal clear, completely rigorous, and ready for publication as written:

* **BCH Plaquette Expansion (Chapter 2, Eqs. 2.41–2.58):** The midpoint expansion showing the exact cancellation of $𝒪({a}^{3})$ terms and isolation of $𝒪({a}^{2})$ Symanzik errors is textbook-perfect.  
* **Scheme Invariance of ${b}_{0},{b}_{1}$ and Essential Singularity (Chapter 3, Eqs. 3.14–3.54):** The inductive proof that $f(w)=exp(-1/(2{b}_{0}w))$ has vanishing right-derivatives of all orders at $w={0}^{+}$ (Proposition 3.2) is clean and rigorous.  
* **Chebyshev Association, Supermultiplicativity, and Fekete’s Lemma (Chapter 4, Eqs. 4.27–4.54 & Chapter 9, Eqs. 9.11–9.35):** The proof that reflection positivity unconditionally guarantees the existence of the asymptotic correlation decay rate $\mu (𝒪)=-ln‖{{T}^{\text{^}}}_{a}{|}_{{𝒦}_{\psi }}{‖}_{\text{op}}\in [0,\infty ]$ without any small-coupling assumption is rock-solid.  
* **Discrete Exterior Calculus & Eckmann Hodge Theory on ${K}_{5}$ (Chapter 6, Eqs. 6.7–6.68):** The proof of ${\partial }_{k-1}\circ {\partial }_{k}=0$ and the exact matrix evaluation ${\Delta }_{2}({K}_{5})=5{I}_{10}$ via curl-curl and grad-div off-diagonal sign cancellation (Eqs. 6.59–6.68) are completely rigorous.  
* **The Semigroup Derivative & Spectral Vanishing Engine (Chapter 15, Eqs. 15.58–15.89):** The proof transferring exponential semigroup decay $‖{T}^{\text{^}}(\tau )\psi ‖\leq {e}^{-m\tau }‖\psi ‖$ to the coercive lower bound $m‖\psi ‖\leq ‖{H}^{\text{^}}\psi ‖$ via the reverse triangle inequality and right-derivatives (Theorem 15.8), followed by the inner-regularity contradiction proof that $E((0,m))=0$ (Theorem 15.9), is mathematically airtight.  
* **Group Character Expansions & Amos–Turán Bounds (Appendix A, Eqs. A.1–A.60):** The Weyl chamber integrations for $SU(2)$ and $SU(3)$ and the application of the Amos bounds to enclose ${I}_{2}(\beta )/{I}_{1}(\beta )$ (Theorem A.5) are completely rigorous.

7. **Adversarial Formalization Hygiene (Chapter 18):** The inclusion of the bo-cowgill-audit protocol (Section 18.5)—explicitly enforcing $dim(G)\geq 3$, $[X,Y]\ne 0$, $dim({ℋ}_{\text{phys}})=\infty$, and rational lower bounds $\Delta >0$—directly addresses the "vacuous/dummy formalization" critique that plagues formal theorem proving.

### **2\. Global Contradictions & Notation Inconsistencies Across Chapters**

A peer reviewer will immediately flag four direct contradictions in conventions and definitions across different chapters of the monograph:

| Issue | First Convention / Equation | Contradicting Convention / Equation | Mathematical Impact & Required Fix |
| :---- | :---- | :---- | :---- |
| **1\. Definition of ${b}_{0}$ and ${b}_{1}$ ($16{\pi }^{2}$ Factor)** | **Ch. 1 (Eq. 1.63) & Ch. 3 (Eqs. 3.23–3.26):${b}_{0}=\frac{11}{3}N$**, ${b}_{1}=\frac{34}{3}{N}^{2}$ (loop factors $16{\pi }^{2}$ written explicitly in denominator of $\beta (g)$). | **Ch. 8 (Eq. 8.26), Ch. 9 (p. 107), Ch. 10 (Eq. 10.31), Ch. 17 (p. 192\):${b}_{0}=\frac{11N}{48{\pi }^{2}}$**, ${b}_{1}=\frac{34{N}^{2}}{(16{\pi }^{2}{)}^{2}}$ (loop factors absorbed into ${b}_{0},{b}_{1}$). | **Catastrophic in Eqs. (8.27), (8.56), (9.70):** In Eq. (8.27), ${b}_{0}$ has $(16{\pi }^{2}{)}^{-1}$ absorbed, yet the exponent *still* writes $exp\left({-\frac{8{\pi }^{2}}{2{b}_{0}{g}^{2}}}\right)$, resulting in a spurious factor of $64{\pi }^{4}$\! Furthermore, $\frac{8{\pi }^{2}}{{b}_{0}{g}^{2}}$ (Eq. 3.37) becomes $\frac{8{\pi }^{2}}{2{b}_{0}{g}^{2}}$ in Eq. (8.27) (an extra factor of 2 error). Standardize ${b}_{0},{b}_{1}$ globally. |
| **2\. Lie Algebra Generators & Trace Sign** | **Ch. 1 (Eqs. 1.26–1.28) & Ch. 2 (p. 24):** Anti-Hermitian $({T}^{a}{)}^{\dagger }=-{T}^{a}$, $Tr({T}^{a}{T}^{b})=-\frac{1}{2}{\delta }^{ab}$, $Tr({F}_{\mu \nu }{F}^{\mu \nu })=-\frac{1}{2}{F}_{\mu \nu }^{a}{F}^{a\mu \nu }\leq 0$. | **Ch. 10 (Eq. 10.1), Ch. 5 (Eq. 5.26), Ch. 16 (Eq. 16.19), Ch. 17 (Eq. 17.2):** Hermitian ${T}^{a}$, $Tr({T}^{a}{T}^{b})=+\frac{1}{2}{\delta }^{ab}$, and in Eq. (5.26) $Tr({F}_{\mu \nu }^{a}{F}^{a\mu \nu })$ is written where ${F}_{\mu \nu }^{a}$ is already a scalar component\! | In Eq. (3.7) and Eq. (5.26), $Tr({F}_{\mu \nu }^{a}{F}^{a\mu \nu })$ takes the matrix trace of a scalar number. In Eq. (16.19), $𝒪(x)=\frac{1}{2}Tr({F}_{\mu \nu }{F}^{\mu \nu })$ would be *negative* under Ch. 1 conventions, contradicting Eq. (16.20) where ${𝒪}_{a}(x)\geq 0$. Fix generator conventions globally. |
| **3\. Direction of Scale Index $k$ (${L}^{k}$ vs. ${2}^{-k}$)** | **Ch. 1 (p. 11), Ch. 12 (p. 131), Ch. 13 (Eq. 13.31):${a}_{k}={L}^{k}{a}_{0}={2}^{k}{a}_{0}$** (${a}_{0}$ is the UV cutoff, $k$ increases toward the IR stopping scale ${a}_{\text{IR}}$). | **Ch. 6 (p. 76, Thm 6.12), Ch. 14 (Eq. 14.1), Ch. 16 (Eq. 16.24):${a}_{k}={2}^{-k}{a}_{0}$** (${a}_{0}$ is the macroscopic IR reference scale, $k$ increases toward the UV limit ${a}_{k}\rightarrow 0$). | In **Theorem 6.12 (p. 76\)**, the text defines ${a}_{k}={L}^{-k}{a}_{0}$, but Eqs. (6.72)–(6.74) write ${L}^{-6k}$ and $\text{dist}(x,y)/{L}^{k}$, which belong to the ${a}_{k}={L}^{k}{a}_{0}$ convention\! And in **Ch. 14 (Eq. 14.57 vs. 14.64)**, the RG map ${ℛ}_{k}$ integrates from fine to coarse, which decreases $k$ if ${a}_{k}={2}^{-k}{a}_{0}$, yet the induction in Theorem 14.6 runs $m\rightarrow m+1$\! |
| **4\. Numbering of OS Axioms (OS0–OS4)** | **Ch. 1 (p. 3\) & Ch. 15 (p. 159–160):OS0** \= Temperedness, **OS1** \= Euclidean Invariance, **OS2** \= Reflection Positivity, **OS3** \= Permutation Symmetry, **OS4** \= Cluster Decomposition. | **Ch. 16 (Section 6, pp. 180–184):OS0** \= Temperedness \+ Euclidean Invariance, **OS1** \= Permutation Symmetry, **OS2** \= Reflection Positivity, **OS3** \= Cluster Property, **OS4** \= Linear Growth Bound. | Align Chapter 16's section headers and proposition labels (Propositions 16.7–16.11) with the canonical OS0–OS4 numbering defined in Chapters 1 and 15\. |

### **3\. Chapter-by-Chapter & Equation-by-Equation Critical Audit**

#### ***Chapter 1: Introduction***

* **Eq. (1.19) (p. 4):** $|{S}_{2}(x,y{)}_{\text{conn}}|\leq Cexp(-m‖x-y‖)⟺\Delta =m>0$.  
* *Critique:* As an "if and only if" statement with $\Delta =m$, this requires taking the supremum of $m$ (or infimum over all observables $𝒪$ generating ${ℋ}_{0}^{⟂}$). For a single correlation function ${S}_{2}$, the decay rate $m$ only satisfies $m\geq \Delta$ (since $𝒪$ might have zero overlap with the lowest glueball state). Specify that $\Delta$ is the infimum of the decay rate over a family of gauge-invariant observables generating a dense subspace of ${ℋ}_{0}^{⟂}$.  
* **Eqs. (1.85)–(1.86) (p. 14):** $‖{T}^{\text{^}}{‖}_{\text{op},{ℋ}_{0}^{⟂}}\leq 1-exp(-2{\beta }_{\text{IR}})<1$ and $\gamma ({T}^{\text{^}})\geq 1-exp(-2{\beta }_{\text{IR}})>0$.  
* *Contradiction:* Since $\gamma ({T}^{\text{^}}):=1-‖{T}^{\text{^}}{‖}_{\text{op},{ℋ}_{0}^{⟂}}$, if $‖{T}^{\text{^}}{‖}_{\text{op},{ℋ}_{0}^{⟂}}\leq 1-{e}^{-2{\beta }_{\text{IR}}}$, then $\gamma ({T}^{\text{^}})=1-‖{T}^{\text{^}}‖\geq {e}^{-2{\beta }_{\text{IR}}}$, **not** $1-{e}^{-2{\beta }_{\text{IR}}}$\! (Notice that in Chapter 7, Eq. 7.50 correctly writes $\gamma (T)\geq {e}^{-2\beta }$, whereas Eq. 1.86, Eq. 13.33–13.34, Eq. 14.43, Eq. 14.66, Eq. 17.3, and Eq. B.17 conflate ${\lambda }_{1}\leq {e}^{-2\beta }$ with ${\lambda }_{1}\leq 1-{e}^{-2\beta }$).

#### ***Chapter 2: The Lattice Theory and Reflection Positivity***

* **Eqs. (2.63)–(2.67) & (2.74)–(2.76) (pp. 26–28):**  
* *Minor Index / Boundary Inconsistency:* In Eq. (2.63), ${\Lambda }_{+}=\{{x}_{0}\geq a\}$ and ${\Lambda }_{-}=\{{x}_{0}\leq 0\}$ for reflection across the link plane ${\Pi }_{\text{link}}=\{{x}_{0}=a/2\}$. In Eq. (2.67), for a temporal link $e=(x,0)$ connecting $x$ to $x+a{0}^{\text{^}}$, the reflection is defined as $(\Theta U{)}_{0}(x):={U}_{0}(-{x}_{0},𝐱{)}^{\dagger }$. However, under $\Theta ({x}_{0},𝐱)=(a-{x}_{0},𝐱)$, the endpoint $x+a{0}^{\text{^}}=({x}_{0}+a,𝐱)$ maps to $(a-({x}_{0}+a),𝐱)=(-{x}_{0},𝐱)$, which is only equal to $(0,𝐱)$ when ${x}_{0}=0$. Later, in Section 5.1 (p. 29), ${𝒜}_{+}$ is stated to be supported in $\{{x}_{0}\geq 0\}$, whereas in Section 4.2 (p. 27\) ${𝒜}_{+}$ was supported on ${E}_{+}\cup {E}_{\times }$ (${x}_{0}\geq a$ plus straddling links). If ${𝒜}_{+}$ includes spatial links at ${x}_{0}=0$, then ${\tau }_{a}$ in Eq. (2.100) reflects across the site plane ${x}_{0}=a/2$ or ${x}_{0}=0$, not ${x}_{0}=a$. Keep link-plane reflection (${x}_{0}=a/2$, ${\Lambda }_{+}=\{{x}_{0}\geq a/2\}$) vs. site-plane reflection (${x}_{0}=0$, ${\Lambda }_{+}=\{{x}_{0}\geq 0\}$) strictly separated.

#### ***Chapter 3: Dimensional Transmutation and the Flow-Time Coordinate***

* **Eqs. (3.4)–(3.5) (p. 33):** ${\Theta }^{\mu \nu }=2Tr\left({{F}^{\mu \rho }{F}_{\rho }^{\nu }-\frac{1}{4}{\delta }^{\mu \nu }{F}_{\rho \sigma }{F}^{\rho \sigma }}\right)$.  
* *Index Raising / Sign Error:* In Euclidean space with ${\delta }_{\mu \nu }$, raising indices is trivial, so ${F}^{\mu \rho }{F}_{\mu \rho }={F}_{\rho \sigma }{F}^{\rho \sigma }$, and Eq. (3.5) holds algebraically. However, under the anti-Hermitian trace convention $Tr({T}^{a}{T}^{b})=-\frac{1}{2}{\delta }^{ab}$ of Eq. (1.27), ${\Theta }^{00}$ in Eq. (3.4) would have the wrong sign unless a minus sign is included (compare with Eq. 1.30).  
* **Eq. (3.7) (p. 33):** ${\Theta }_{\mu }^{\mu }(x)=\frac{\beta (g)}{2{g}^{3}}Tr({F}_{\mu \nu }^{a}(x){F}^{a\mu \nu }(x))\ne 0$.  
* *Notation Error:* ${F}_{\mu \nu }^{a}(x){F}^{a\mu \nu }(x)$ is already a real number (summed over color index $a=1,\ldots ,{N}^{2}-1$). Applying $Tr(·)$ to a scalar multiplies it by $N$ if interpreted as ${\bm{1}}_{N}$, or is a typo for either $\frac{\beta (g)}{2{g}^{3}}{F}_{\mu \nu }^{a}{F}^{a\mu \nu }$ or $-\frac{\beta (g)}{{g}^{3}}Tr({F}_{\mu \nu }{F}^{\mu \nu })$.  
* **Eqs. (3.60)–(3.76) (pp. 40–42):** Definition of Flow-Time $t\equiv -ln(a{\Lambda }_{\text{YM}})$ and Partition of the Coupling Trajectory.  
* *Conceptual / Mathematical Inconsistency:* In Eq. (3.66), the author writes $\beta (t)=\frac{11{N}^{2}}{12{\pi }^{2}}t$ (the 1-loop truncated relation) and uses it in Definition 3.5 (Eqs. 3.71–3.76) to define ${t}_{\text{IR}}=\frac{6{\pi }^{2}}{11{N}^{2}}$ and ${t}_{\text{UV}}=\frac{30{\pi }^{2}}{11{N}^{2}}$ as the exact flow-time equivalents of $\beta =1/2$ and $\beta =5/2$. However, ${\Lambda }_{\text{YM}}$ was defined in Eq. (3.36) via the exact integral of $\beta (g)$, and at $\beta \in [1/2,5/2]$ (strong-to-intermediate coupling), the 1-loop formula $\beta (t)=\frac{11{N}^{2}}{12{\pi }^{2}}t$ is **not** exact (2-loop and non-perturbative terms are $𝒪(1)$). You should clarify that $t(\beta ):=\frac{12{\pi }^{2}}{11{N}^{2}}\beta$ is a *reparameterized coupling coordinate* (or that ${t}_{\text{IR}},{t}_{\text{UV}}$ are defined directly by $\beta (a({t}_{\text{IR}}))=1/2$ and $\beta (a({t}_{\text{UV}}))=5/2$).

#### ***Chapter 4: The Tail Equation and Operator Meaning***

* **Eqs. (4.16)–(4.20) (p. 49, Theorem 4.2):** Källén–Lehmann Spectral Representation.  
* *Conditionality / Circularity Warning:* Theorem 4.2 assumes that ${S}_{2}^{\text{conn}}(x,y)$ is *Euclidean-invariant* ($SO(4)$ invariant) and uses the continuum relativistic dispersion relation $\omega (𝐤)=\sqrt{{𝐤}^{2}+{m}^{2}}$ in Eq. (4.18). At finite lattice spacing $a>0$ (which is the setting of Section 4.1, Eq. 4.1–4.5), $SO(4)$ invariance is broken to hypercubic symmetry ${H}_{4}$, and the lattice dispersion relation is $cosh(aE(𝐤))=1+\ldots$, not $\sqrt{{𝐤}^{2}+{m}^{2}}$. Clarify that Section 1.2–1.3 of Chapter 4 applies strictly in the *continuum limit* $a\rightarrow 0$ (after OS1 is proved in Chapter 16), whereas Section 2–3 of Chapter 4 applies on the lattice.  
* **Eqs. (4.89)–(4.90) (p. 56, Proposition 4.8):** $‖{R}_{0}(E){‖}_{\text{op}}=\frac{1}{min(E,\Delta -E)}\leq \frac{2}{\Delta }$ for $0<E<\Delta$.  
* *Mathematical Error:* Look at Eq. (4.89) vs. the proof on p. 56–57\! Because ${R}_{0}(z)=(z\bm{1}-{H}^{\text{^}}{|}_{{ℋ}_{0}^{⟂}}{)}^{-1}$ is restricted to ${ℋ}_{0}^{⟂}$ where $\{0\}$ has **already been projected out**, the spectrum of ${H}^{\text{^}}{|}_{{ℋ}_{0}^{⟂}}$ is contained in $[\Delta ,\infty )$. Therefore, for $E\in (0,\Delta )$, the distance from $E$ to $\sigma ({H}^{\text{^}}{|}_{{ℋ}_{0}^{⟂}})$ is simply $\Delta -E$, **not** $min(E,\Delta -E)$\! Moreover, as $E\rightarrow {\Delta }^{-}$, $(\Delta -E{)}^{-1}\rightarrow +\infty$, which is **not** bounded by $2/\Delta$ for all $E\in (0,\Delta )$\! The bound $‖{R}_{0}(E){‖}_{\text{op}}\leq 2/\Delta$ holds only for $E\in (0,\Delta /2]$ (or for the full resolvent $R(E)$ at the single midpoint $E=\Delta /2$). Fix the quantifier in Eq. (4.89).

#### ***Chapter 5: Resolvent Norms, Pseudospectra, and the Gluon Condensate***

* **Section 2 & 3 (Eqs. 5.26–5.66, pp. 62–66): SVZ Sum Rules and the $\Delta \geq 548\text{ MeV}$ Bound.**  
* *Major Referee Objection (Phenomenological Conditionalities Presented as Rigorous Theorems):* In a pure mathematics / constructive QFT monograph claiming an *unconditional* proof of the Millennium Problem, Chapter 5 is the most vulnerable target for a referee:

8. **Eq. (5.42) (The OPE):** The Operator Product Expansion is an *asymptotic* expansion at ${Q}^{2}\rightarrow \infty$, truncated here at dimension 6 ($𝒪({Q}^{-8})$ dropped). Truncating an asymptotic series without a rigorous remainder bound is an uncontrolled approximation.  
9. **Eq. (5.53) (Narrow-Resonance \+ Continuum Ansatz):** $\rho (s)={f}_{G}^{2}{M}_{G}^{4}\delta (s-{M}_{G}^{2})+\theta (s-{s}_{0}){\rho }_{\text{pert}}(s)$. In a rigorous quantum field theory, the spectral density $\rho (s)$ above the two-glueball threshold is a continuous function with branch cuts and potential resonances, **not** a step function $\theta (s-{s}_{0})$ times the bare perturbative density $\frac{2}{{\pi }^{2}}{\alpha }_{s}^{2}s$. Assuming this ansatz is standard in QCD phenomenology, but it is **not** a rigorous mathematical theorem.  
10. **Eq. (5.55)–(5.56) (Derivative of an Approximate Sum Rule):** Even if two functions are approximately equal, their derivatives need not be close. Furthermore, in Eq. (5.60) ("Proof of Theorem 5.9"), the author writes $\frac{d{M}_{G}^{2}({M}^{2})}{d{M}^{2}}=0⟹{M}^{4}\approx \frac{{\pi }^{3}}{{b}_{0}{\alpha }_{s}}{𝒢}_{2}$ and substitutes this approximate relation to claim a *strict mathematical inequality* ${M}_{G}^{4}\geq \frac{16{\pi }^{3}}{{b}_{0}}{𝒢}_{2}$ (Eq. 5.61). Look at Eq. (5.56): as ${M}^{2}\rightarrow 0$ or ${M}^{2}\rightarrow \infty$, the truncated ratio does not algebraically bound the true lowest pole ${M}_{G}^{2}$ unless positivity of the continuum subtraction and remainder bounds are proved.  
11. **Eq. (5.58) (Empirical Input):** ${𝒢}_{2}=(0.012\pm 0.002){\text{ GeV}}^{4}$ is an experimental/empirical value extracted from charmonium sum rules in the real world (with quarks\!), not a first-principles mathematical constant of pure $SU(3)$ Yang–Mills theory.

* *How to Fix:* Explicitly demarcate Chapter 5 (just as you did for ${K}_{5}$ in Chapter 6 and numerical profiles in Appendix B\!) as a **phenomenological / physical consistency benchmark** showing how the constructive mass gap connects to SVZ QCD sum rules, rather than relying on Eq. (5.57) as a load-bearing logical step in the unconditional mathematical proof.

#### ***Chapter 6: Discrete Exterior Calculus and Simplicial Hodge Theory***

* **Eqs. (6.72)–(6.74) (p. 76, Theorem 6.12):**  
* *Scale Exponent Contradiction:* As noted in Section 2 above, Theorem 6.12 states "Let ${a}_{k}={L}^{-k}{a}_{0}$ be the lattice spacing at decimation scale $k\in ℕ$", and then writes ${\Delta }_{B}^{(k)}\equiv {D}_{B}^{*}{D}_{B}+{\alpha }_{\text{gauge}}{d}_{0}{d}_{0}^{*}+{\alpha }_{\text{Ax}}{L}^{-6k}\bm{1}$ and $\text{dist}(x,y)/{L}^{k}$. In Bałaban's papers, unit block size is rescaled to 1 (or ${L}^{k}$ in fine lattice units where ${a}_{k}={L}^{k}{a}_{0}$). Change ${a}_{k}={L}^{-k}{a}_{0}$ in the hypothesis of Theorem 6.12 to ${a}_{k}={L}^{k}{a}_{0}$ so that it matches Eq. (1.76) and Theorem 12.3 (p. 133).

#### ***Chapter 7: Character Decomposition and the Centre Grading***

* **Eqs. (7.49)–(7.61) (pp. 83–84, Theorem 7.6 & Corollary 7.7):** Volume-Independent Spectral Gap of the 4D Transfer Operator.  
* *CRITICAL MATHEMATICAL FLAW (The Most Serious Error in the Monograph):* Let us examine the proof of Theorem 7.6 (pp. 83–84) line by line:  
* Eq. (7.52): ${{T}^{\text{^}}}_{\text{full}}={{V}^{\text{^}}}_{s}^{1/2}{{V}^{\text{^}}}_{\tau }{{V}^{\text{^}}}_{s}^{1/2}$, where ${{V}^{\text{^}}}_{s}^{1/2}$ is multiplication by $exp(-\frac{1}{2}{S}_{s}[U])$ (the spatial plaquette action) and ${{V}^{\text{^}}}_{\tau }$ is the temporal transfer integral operator.  
* The author takes a state $\Psi \in {ℋ}_{0}^{⟂}$, meaning $\Psi$ is orthogonal to the **interacting vacuum** $\Omega$ of ${{T}^{\text{^}}}_{\text{full}}$ ($⟨\Omega ,\Psi {⟩}_{{ℋ}_{\Sigma }}=0$, Eq. 7.48).  
* Next, in Eq. (7.53), the author defines $\Phi \equiv {{V}^{\text{^}}}_{s}^{1/2}\Psi$.  
* Then, on p. 83 (bottom), the author claims:

  ***"Because $\Psi \in {ℋ}_{0}^{⟂}$, the bare trivial component  does not contribute to the matrix element." And on p. 84, Eq. (7.57)–(7.58), the author claims:***

* **Why this is mathematically false:**

12. **Vacuum Mismatch ($\Omega \ne {\Omega }_{0}$):** The trivial representation  is the ground state ${\Omega }_{0}(U)\equiv 1$ of the **kinetic temporal operator ${{V}^{\text{^}}}_{\tau }$ alone** (where spatial plaquettes are turned off, ${S}_{s}=0$). The interacting vacuum $\Omega (U)$ of ${{T}^{\text{^}}}_{\text{full}}={{V}^{\text{^}}}_{s}^{1/2}{{V}^{\text{^}}}_{\tau }{{V}^{\text{^}}}_{s}^{1/2}$ is **not** the constant function $1$ when $\beta >0$\!  
13. **Multiplication by ${{V}^{\text{^}}}_{s}^{1/2}$ Does Not Preserve Orthogonality to $1$:** Even if $⟨\Omega ,\Psi ⟩=0$, the vector $\Phi ={{V}^{\text{^}}}_{s}^{1/2}\Psi ={e}^{-\frac{1}{2}{S}_{s}}\Psi$ is **not** orthogonal to the constant function ${\Omega }_{0}\equiv 1$:

$$⟨{\Omega }_{0},\Phi ⟩=\int\limits_{{\Omega }_{\Sigma }}^{}{e}^{-\frac{1}{2}{S}_{s}(U)}\Psi (U)d\mu (U)\ne 0!$$

Because $\Phi$ has a non-zero projection onto the  eigenspace of ${{V}^{\text{^}}}_{\tau }$ (whose eigenvalue is ), one **cannot** bound $‖{{V}^{\text{^}}}_{\tau }\Phi ‖$ by \!

14. **What the Proof Actually Computes:** If the inequality $‖{{T}^{\text{^}}}_{\text{full}}\Psi ‖\leq {sup}_{R\ne \bm{1}}\frac{{c}_{R}(\beta )}{{c}_{\bm{1}}(\beta )}‖\Psi ‖$ were true, it would mean that the spatial magnetic plaquettes ${{V}^{\text{^}}}_{s}$ could be completely ignored via $‖{{V}^{\text{^}}}_{s}^{1/2}{‖}_{\text{op}}\leq 1$, reducing 4D Yang–Mills theory to a decoupled product of independent 2D single-link theories\! Furthermore, look at Eq. (7.56):

$${sup}_{R\ne \bm{1}}\frac{{c}_{R}(\beta )}{{c}_{\bm{1}}(\beta )}=\frac{{I}_{2}(\beta )}{{I}_{1}(\beta )}\text{for }SU(2).$$

At $\beta =1/2$, ${I}_{2}(1/2)/{I}_{1}(1/2)\approx 0.124$, whereas $1-{e}^{-2(1/2)}=1-{e}^{-1}\approx 0.632$. While ${I}_{2}(\beta )/{I}_{1}(\beta )\leq 1-{e}^{-2\beta }$ happens to be numerically true for $\beta \leq 1/2$, as $\beta \rightarrow \infty$ (the continuum limit $a\rightarrow 0$\!), ${I}_{2}(\beta )/{I}_{1}(\beta )~1-\frac{3}{2\beta }$, whereas $1-{e}^{-2\beta }~1-{e}^{-2\beta }$\! In FACT, for $\beta =2$, ${I}_{2}(2)/{I}_{1}(2)\approx 0.433$, and for $\beta =5$, ${I}_{2}(5)/{I}_{1}(5)\approx 0.719$, while $1-{e}^{-10}\approx 0.99995$.

15. **How to Fix Theorem 7.6:**

> > > * First, at strong coupling ($\beta \leq {\beta }_{0}$, or at the stopping scale ${\beta }_{\text{IR}}=1/2$), the transfer matrix gap of ${{T}^{\text{^}}}_{\text{full}}={{V}^{\text{^}}}_{s}^{1/2}{{V}^{\text{^}}}_{\tau }{{V}^{\text{^}}}_{s}^{1/2}$ cannot be proved simply by $‖{{V}^{\text{^}}}_{s}^{1/2}{‖}_{\text{op}}\leq 1$; it must be proved using Osterwalder–Seiler cluster expansion of the spatial plaquette perturbation ${{V}^{\text{^}}}_{s}$ around ${{V}^{\text{^}}}_{\tau }$ (or via the centre-sector projection ${ℋ}^{(1)}$ where $⟨1,\Phi ⟩=0$ is enforced *by exact centre symmetry*\!).  
> > > * **Crucial Observation for Your Revision:** Notice that if $\Psi \in {ℋ}^{(k)}$ with $k\ne 0$ (the **centre-charged sector** of Section 7.2\!), then because ${{V}^{\text{^}}}_{s}^{1/2}$ is strictly invariant under centre transformations ${𝒵}^{\text{^}}$, $\Phi ={{V}^{\text{^}}}_{s}^{1/2}\Psi$ **also** belongs to ${ℋ}^{(k)}$ ($k\ne 0$)\! And because the trivial representation  lies in ${ℋ}^{(0)}$, $\Phi \in {ℋ}^{(k)}$ ($k\ne 0$) **is** strictly orthogonal to \! However, for a state in ${ℋ}^{(1)}$, a Polyakov loop wraps around the spatial torus of length $L$, so at least $L/a$ links must carry ${R}_{e}\ne \bm{1}$, giving . For the neutral sector ${ℋ}^{(0)}\cap {\Omega }^{⟂}$, you must invoke the cluster expansion (Chapter 13/14) or the quadratic-form domination (Chapter 11\) rather than claiming $\Phi ={{V}^{\text{^}}}_{s}^{1/2}\Psi$ is orthogonal to .

#### ***Chapter 8 & Chapter 9: The Factorisation of the Mass Gap ($\Delta =ℰ·𝒱·𝒫$)***

* **Eqs. (8.2)–(8.4) (pp. 86–87) & Theorem 8.6 (p. 91\) & Theorem 9.5 (p. 104):**  
* *Logical Circularity / Conditionality in the Definition of $𝒱$ and $𝒫$:*

16. In Theorem 8.1 (p. 86), the author writes $\Delta =ℰ·𝒱·𝒫$, where $ℰ\in \{0,1\}$, $𝒫\in \{0,1\}$, and $𝒱={lim}_{a\rightarrow 0}\frac{\Delta (a)}{{\Lambda }_{\text{YM}}}\in {ℝ}_{>0}$.  
17. Look closely at Eq. (8.3): If $𝒱={lim}_{a\rightarrow 0}\frac{\Delta (a)}{{\Lambda }_{\text{YM}}}$ is already proved to be in ${ℝ}_{>0}$ (strictly positive\!), then since ${\Lambda }_{\text{YM}}>0$, it *already* implies $\Delta ={lim}_{a\rightarrow 0}\Delta (a)=𝒱·{\Lambda }_{\text{YM}}>0$, which makes $𝒫=1$ redundant, or conversely makes the proof of $𝒱>0$ circular\!  
18. Furthermore, $\Delta$ has dimensions of mass ($[\Delta ]=1$), whereas $ℰ\in \{0,1\}$, $𝒱={lim}_{a\rightarrow 0}\Delta (a)/{\Lambda }_{\text{YM}}$ (dimensionless\!), and $𝒫\in \{0,1\}$ are all **dimensionless**\! Thus Eq. (8.2) should read $\Delta =(ℰ·𝒱·𝒫){\Lambda }_{\text{YM}}$, or $\Delta /{\Lambda }_{\text{YM}}=ℰ·𝒱·𝒫$.

* *Critique of the Proof of Theorem 8.6 (p. 91\) and Theorem 9.5 (pp. 104–105):*

19. **Eq. (8.29) & Eq. (9.43):** $\left({-a\frac{\partial }{\partial a}+\beta (g)\frac{\partial }{\partial g}}\right)\Delta (a)=0$. This homogeneous Callan–Symanzik equation holds only asymptotically in the continuum scaling regime (up to $𝒪({a}^{2}{\Lambda }_{\text{YM}}^{2})$ lattice artifacts, which are non-analytic in ${g}^{2}$ because ${a}^{2}{\Lambda }_{\text{YM}}^{2}\propto {e}^{-16{\pi }^{2}/({b}_{0}{g}^{2})}$\!).  
20. **Eq. (8.31)–(8.32) (p. 91):** Writing $\Delta (a)=\frac{1}{a}exp\left({-\int\limits_{}^{g}\frac{d{g}^{′}}{\beta ({g}^{′})}}\right)·\Phi (g)$ and claiming that $\Phi (g)={c}_{0}+{c}_{1}{g}^{2}+\ldots$ has a *non-zero radius of convergence* in ${g}^{2}$ is false: by dimensional analysis and RG invariance, **any** RG-invariant mass scale is a constant ${c}_{0}$ times ${\Lambda }_{\text{YM}}$ (up to scheme redefinitions of ${\Lambda }_{\text{YM}}$, or non-perturbative $𝒪({a}^{2}{\Lambda }_{\text{YM}}^{2})$ lattice corrections). Once ${\Lambda }_{\text{YM}}$ is defined exactly via Eq. (3.36), the ratio $\Delta (a)/{\Lambda }_{\text{YM}}$ in the continuum limit $a\rightarrow 0$ is a **single pure number** ${𝒱}_{0}={c}_{0}$ (not a function of $g$\!), and at finite $a$, its corrections are in powers of ${a}^{2}{\Lambda }_{\text{YM}}^{2}~exp(-2t)$, which are non-perturbative in ${g}^{2}$\!  
21. **Eqs. (9.43)–(9.47) (p. 104):** In Eq. (9.43), $\Delta (a)$ satisfies the *homogeneous* RG equation without ${\gamma }_{𝒪}$, yet in Eq. (9.44) the author inserts $exp\left({-\int\limits_{{g}_{0}}^{g(a)}\frac{{\gamma }_{𝒪}({g}^{′})}{\beta ({g}^{′})}d{g}^{′}}\right)$ into the formula for $\xi (a)=(a\Delta (a){)}^{-1}$\! The anomalous dimension ${\gamma }_{𝒪}$ governs the multiplicative wave-function renormalization ${Z}_{𝒪}$ of the **amplitude** of the correlation function $\Pi ({p}^{2})$, **not** the position of the mass pole $\Delta (a)=(a\xi (a){)}^{-1}$\! The mass gap $\Delta$ is a spectral eigenvalue of ${H}^{\text{^}}$ and cannot depend on the anomalous dimension ${\gamma }_{𝒪}$ of the interpolating operator $𝒪$ used to probe it.

#### ***Chapter 10: Self-Interaction as the Origin of the Mass Gap***

* **Eqs. (10.26)–(10.31) (pp. 114–115):** Heat Kernel Derivation of ${b}_{0}$.  
* *Sign / Factor Check:* In Eq. (10.28),  (because  and ${Tr}_{\text{adj}}({T}_{\text{adj}}^{a}{T}_{\text{adj}}^{b})={C}_{2}(G){\delta }^{ab}$). Then Eq. (10.30) gives $\left({\frac{7}{3}-\frac{2}{12}}\right)=\frac{13}{6}$, whereas the standard 1-loop coefficient is $\frac{11}{3}=\frac{22}{6}$. The text on p. 115 says *"Taking into account the gauge parameter $\xi =1$ projection of the gauge-fixing term, the standard one-loop counterterm coefficient is ${b}_{0}=\frac{1}{16{\pi }^{2}}(\frac{11}{3}{C}_{2}(G))$"*. However, the calculation in Eqs. (10.16)–(10.29) was **already** performed in the $\xi =1$ background Feynman gauge\! The reason $\frac{13}{6}$ appeared instead of $\frac{11}{3}$ is that in Eq. (10.27) the orbital curvature term for ${a}_{2}(x)=\frac{1}{12}{ℱ}_{\mu \nu }{ℱ}^{\mu \nu }$ has a minus sign relative to the paramagnetic term ${E}^{2}$ when  is anti-Hermitian: specifically, $2-\frac{1}{3}=\frac{5}{3}$, and subtracting ghosts gives $\frac{5}{3}+\frac{1}{6}=\frac{11}{6}$, which multiplied by 2 gives $\frac{11}{3}$\! Fix the relative sign of ${ℱ}_{\mu \nu }{ℱ}^{\mu \nu }$ vs. ${E}^{2}$ in Eqs. (10.26)–(10.30) so the arithmetic yields $\frac{11}{3}$ directly without hand-waving.

#### ***Chapter 11 & Appendix C: Positivity of the Mass Gap, Chessboard Bounds, and Confining Flux***

* **Theorem 11.2 (p. 122), Corollary 11.3 (p. 123), Theorem 11.7 (p. 126), and Theorem C.3 (p. 216):**  
* *CRITICAL MATHEMATICAL FLAW \#1 (Reflections of Open Lines and Misuse of the Chessboard Inequality):*

22. **Theorem 11.2 (Eqs. 11.10–11.14, pp. 122–123):** Let $C$ be a closed contractible spatial loop on the time-slice ${x}_{0}=0$, decomposed into ${L}_{1}$ and ${L}_{2}=\Theta ({L}_{1}{)}^{\dagger }$ across a spatial reflection plane $\Pi$. First, if ${𝒪}_{C}=Tr(U({L}_{1})U({L}_{2}))-𝔼[Tr(U({L}_{1})U({L}_{2}))]$, subtracting the vacuum expectation value $𝔼[\ldots ]$ means ${𝒪}_{C}$ is no longer a simple product $𝒜·\Theta (ℬ)$ (and if you don't subtract the VEV, $\Psi ={𝒪}_{C}\Omega$ is **not** orthogonal to the vacuum $\Omega$\!).  
23. Second, in Eq. (11.14), the author claims that the open Wilson line state ${\Phi }_{0}=U({L}_{1}{)}_{ij}\Omega$ transforms under a global centre transformation ${𝒵}^{\text{^}}$ as ${𝒵}^{\text{^}}{\Phi }_{0}={e}^{2\pi i/N}{\Phi }_{0}$ and therefore belongs to the physical centre-charged sector ${ℋ}^{(1)}$. **This is false:** an open Wilson line $U({L}_{1}{)}_{ij}$ with free color indices $i,j$ is **not gauge-invariant** at its endpoints\! Under local gauge projection ${𝒫}_{\text{phys}}$ (Eq. 7.7), any open Wilson line state vanishes identically (${𝒫}_{\text{phys}}U({L}_{1}{)}_{ij}\Omega =0$) by Elitzur's theorem / Schur's lemma (Eq. 13.5)\! A state in ${ℋ}^{(1)}$ must be a **closed non-contractible Polyakov loop** wrapping completely around the torus ${𝕋}_{L}^{3}$, which has energy ${E}_{1}(L)~\sigma L\rightarrow \infty$ as the spatial volume $L\rightarrow \infty$\! If ${\Delta }_{0}\geq \frac{1}{2}{E}_{1}(L)$ held for a torus-wrapping loop, the glueball mass ${\Delta }_{0}$ would diverge as $L\rightarrow \infty$\!  
24. **Theorem 11.7 (p. 126\) & Theorem C.3 (p. 216, Eqs. C.25–C.32):** Look at the proof of Theorem C.3 on p. 216: The author writes a planar Wilson loop ${W}_{\text{fund}}(C)$ bounding a minimal surface $\Sigma$ of area $R\times T$ as a product of single-plaquette characters:

$${W}_{\text{fund}}(C)=\prod\limits_{x\in \Sigma }^{}{\chi }_{\text{fund}}({U}_{{P}_{x}})\text{(Eq. C.29)}.$$

**Mathematical Error:** In a non-Abelian group $SU(N)$ ($N\geq 2$), the trace of a product of matrices around the boundary $\partial \Sigma$ is **NOT** equal to the product of the traces of the interior plaquettes\! That is:

$$Tr\left({\prod\limits_{e\in \partial \Sigma }^{}{U}_{e}}\right)\ne \prod\limits_{P\in \Sigma }^{}Tr({U}_{P})!$$

Even for $U(1)$, where $\prod\limits_{P\in \Sigma }^{}{U}_{P}=\prod\limits_{e\in \partial \Sigma }^{}{U}_{e}$ holds by the Abelian Stokes theorem, applying the chessboard reflection across the mid-plane of a plaquette ${P}_{x}$ reflects ${U}_{P}$ into a configuration where adjacent plaquettes share links with reversed orientations, so in the fully reflected periodic product ${ℛ}_{x}({\chi }_{\text{fund}})$ on the torus, every link ${U}_{e}$ is shared by **multiple** reflected plaquettes and does **not** decouple into independent single-plaquette integrals (if it did, 4D $U(1)$ lattice gauge theory would have $\sigma (\beta )\geq -ln({I}_{1}(\beta )/{I}_{0}(\beta ))>0$ for **all** $\beta \in (0,\infty )$, directly contradicting **Guth's Theorem 10.4** on p. 116\!).

* **Why this is a fatal contradiction with Chapter 10:** On p. 116 (Theorem 10.4), the author rightly emphasizes Guth's theorem: 4D compact $U(1)$ lattice gauge theory has $\sigma (\beta )=0$ for $\beta >{\beta }_{c}\approx 1.01$. Yet the proof of Theorem C.3 (p. 216–217) and Theorem 11.7 (p. 126\) uses only reflection positivity and character orthogonality—both of which hold identically for $U(1)$ with ${\zeta }_{U(1)}(\beta )={I}_{1}(\beta )/{I}_{0}(\beta )<1$ for all $\beta <\infty$\! That immediately tells any referee that Eq. (C.29) and Eq. (C.31) are invalid.  
* **Furthermore, look at the scaling of $-ln{\zeta }_{\text{fund}}(\beta )$ as $a\rightarrow 0$ ($\beta \rightarrow \infty$):** By Eq. (A.56) (p. 212), as $\beta \rightarrow \infty$, ${\zeta }_{3}(\beta )=1-\frac{8}{3\beta }+𝒪({\beta }^{-2})$, so:

$$-ln{\zeta }_{3}(\beta )~\frac{8}{3\beta }\propto {g}^{2}(a)~\frac{1}{ln(1/a{\Lambda }_{\text{YM}})}.$$

In physical units, Eq. (11.3) defines ${\sigma }_{\text{phys}}={lim}_{a\rightarrow 0}\frac{\sigma (a)}{{a}^{2}}$. If $\sigma (a)$ were bounded below by $-ln\zeta (\beta )~\frac{8}{3\beta }$, then $\frac{-ln\zeta (\beta )}{{a}^{2}}~\frac{1}{{a}^{2}ln(1/a)}\rightarrow +\infty$ (which is the ultraviolet perimeter divergence, not the physical string tension $\sigma (a)~c{a}^{2}{\Lambda }_{\text{YM}}^{2}~c{e}^{-2t}$\!).

* **Theorem 11.9 (p. 128\) & Proposition C.5 (p. 217–218): Variational Flux-Tube Proof of $\Delta \geq 2\sqrt{{\sigma }_{\text{phys}}}$.**  
* *Direction of the Variational Inequality Error:* Look at Eq. (C.41) and Eq. (C.45) on p. 218:

25. In Eq. (C.41), the author writes for a specific trial state ${\Psi }_{R}$:

$$E(R)=\frac{⟨{\Psi }_{R},{H}^{\text{^}}{\Psi }_{R}⟩}{‖{\Psi }_{R}{‖}^{2}}\geq \frac{1}{R}+2\pi {\sigma }_{\text{phys}}R\geq E({R}_{\text{min}})=2\sqrt{2\pi {\sigma }_{\text{phys}}}.$$

26. Then in Eq. (C.45), the author writes by the Rayleigh–Ritz variational principle:

$$\Delta ={inf}_{\psi \in {ℋ}_{0}^{⟂},‖\psi ‖=1}⟨\psi ,{H}^{\text{^}}\psi ⟩\leq E({R}_{\text{min}})!$$

27. **Contradiction in Inequality Direction:** The Rayleigh–Ritz principle gives an **upper bound** $\Delta \leq \frac{⟨{\Psi }_{R},{H}^{\text{^}}{\Psi }_{R}⟩}{‖{\Psi }_{R}{‖}^{2}}$ for a specific trial state ${\Psi }_{R}$, whereas you need a **lower bound** $\Delta \geq 2\sqrt{{\sigma }_{\text{phys}}}$ on the infimum over *all* states $\psi \in {ℋ}_{0}^{⟂}$\! Bounding the energy of one trial state ${\Psi }_{R}$ from below by $2\sqrt{{\sigma }_{\text{phys}}}$ does not bound the infimum over all $\psi \in {ℋ}_{0}^{⟂}$ from below unless you prove that every low-energy eigenstate in ${ℋ}_{0}^{⟂}$ is dominated by this effective Hamiltonian. Furthermore, Eq. (C.39) invokes the Nambu–Goto effective string action and Eq. (C.40) writes $\Delta p~1/R⟹{E}_{\text{kin}}(R)\geq 1/R$ heuristics rather than an operator inequality on ${H}^{\text{^}}$.

#### ***Chapter 12, Chapter 13, and Chapter 14: Bałaban's RG Programme, Crossover Closure, and Polymer Trapping***

* **Eqs. (13.21)–(13.28) (pp. 145–146) & Eqs. (14.21)–(14.63) (pp. 152–157): First-Principles Derivation of $(\theta ,{C}_{\text{Mayer}},{C}_{\text{vert}},{\beta }_{\text{IR}},{r}_{\text{max}})$.**  
* *Referee Audit of Step 4, Step 5, Step 6 (pp. 152–155):* The author deserves high praise for recognizing in **Warning 14.2 (p. 150\)** that postulating numbers $(\theta =1/2,{C}_{\text{Mayer}}=1/8,{C}_{\text{vert}}=1/20,{\beta }_{\text{IR}}=1/2,{r}_{\text{max}}=1/4)$ without derivation is insufficient, and for providing Sections 3.4–3.6 to derive them. However, a constructive field theory referee will scrutinize three steps in Sections 3.4–3.6:

28. **Step 4 (Derivation of $\theta =1/2$, Eqs. 14.22–14.28):** The scaling factor ${L}^{4-{d}_{𝒪}}={2}^{-2}=1/4$ holds for canonical dimension-6 operators ${𝒪}^{(6)}$ (such as $Tr(({D}_{\rho }{F}_{\mu \nu }{)}^{2})$). However, what about **marginal** dimension-4 operators ($Tr({F}_{\mu \nu }{F}^{\mu \nu })$) and **relevant** dimension-2 operators (mass terms ${A}_{\mu }^{2}$)? In Section 12.3.4 (p. 136), the author correctly notes that Ward–Takahashi identities forbid mass terms ($d=2$) and that the marginal term ($d=4$) is absorbed into the running coupling ${g}_{k+1}^{2}$ in the background action $\frac{1}{{g}_{k}^{2}}𝒜({U}_{k}(V))$. You should explicitly state in **Proposition 14.3 (p. 153\)** that the polymer activity ${K}^{(k)}$ is defined *after* extracting the marginal Yang–Mills action into the running coupling ${\beta }_{k}$ (via Bałaban's $ℛ$\-operation), so that ${K}^{(k)}$ lies strictly in the subspace of irrelevant operators (${d}_{𝒪}\geq 6$).  
29. **Step 5 (Derivation of ${C}_{\text{Mayer}}=1/8$, Eqs. 14.31–14.36):** In Eq. (14.32)–(14.33), the author writes:

$$\sum\limits_{{X}_{2}≁{X}_{1}}^{}|f({X}_{1},{X}_{2})|{e}^{\kappa |{X}_{2}|}\leq |{X}_{1}|\sum\limits_{m=1}^{\infty }𝒩(m)exp(-({\kappa }_{0}-\kappa )m)$$

and then in Eq. (14.33) substitutes $2401{e}^{-\kappa }\leq 2401{e}^{-10}\approx 0.109005$ by choosing $\kappa \geq 10.0$. **Look at the sign of $\kappa$ in the exponent:** On the left-hand side of Eq. (14.32), the Banach norm $‖·{‖}_{\kappa }$ multiplies by ${e}^{+\kappa |{X}_{2}|}$ (which *grows* with $\kappa$\!), while the bare polymer activity suppresses by ${e}^{-{\kappa }_{0}|{X}_{2}|}$, leaving ${e}^{-({\kappa }_{0}-\kappa )m}$. Therefore, increasing $\kappa$ makes ${\kappa }_{0}-\kappa$ **smaller**, not larger\! For the exponent to be $-10m$, you need ${\kappa }_{0}-\kappa \geq 10$ (i.e., the bare Peierls action suppression ${\kappa }_{0}$ must satisfy ${\kappa }_{0}\geq \kappa +10\geq 20$), **not** $\kappa \geq 10$\! Fix the distinction between the Peierls action cost ${\kappa }_{0}$ and the Banach norm weight $\kappa$ in Eqs. (14.32)–(14.33) and Eq. (14.70).

30. **Step 6 (Derivation of ${C}_{\text{vert}}=1/20$, Eqs. 14.38–14.40):** Look at Eq. (14.38):

$${S}_{W}({U}_{p})\geq \frac{{\beta }_{k}}{4N}{\epsilon }_{0}^{2}{g}_{k}^{-2/3}=\frac{{\epsilon }_{0}^{2}}{2{g}_{k}^{8/3}}.$$

In the crossover window ${\beta }_{k}\in [1/2,5/2]$, ${g}_{k}^{2}=2N/{\beta }_{k}\in [4N/5,4N]$ is of order $𝒪(1)$ to $𝒪(10)$ (for $N=3$, ${g}_{k}^{2}\in [2.4,12]$). Why does the integral in Eq. (14.39) satisfy ${sup}_{p}\int\limits_{G}^{}dg|{\nabla }_{A}h|exp(-{S}_{W}({U}_{p}))\leq \frac{1}{20{\beta }_{k}}$ for all ${\beta }_{k}\in [1/2,5/2]$? Because Eq. (14.40) simply states *"By choosing the standard ${C}^{\infty }$ cutoff function with $|\nabla h|\leq 2$ ... ${C}_{\text{vert}}\leq 1/20$"* without showing the numerical evaluation of ${\epsilon }_{0}$ and ${g}_{k}$, a referee will ask for the explicit choice of the small-field threshold ${\epsilon }_{0}$ that makes $2exp(-{S}_{W}({U}_{p}))\leq \frac{1}{20{\beta }_{k}}$.

* **Section 13.5 (p. 147\) & Section 14.5 (p. 157): The Finite-Pace Stopping Schedule and Transfer Matrix Handshake.**  
* *Subtle Conceptual Question (Lattice Spacing ${a}_{\text{IR}}$ vs. Continuum Limit $a\rightarrow 0$):* In Definition 13.6 (Eq. 13.31) and Section 14.5 (Eq. 14.64), the multiscale decimation starts at microscopic spacing $a\rightarrow 0$ (where $\beta (a)\rightarrow \infty$) and integrates $N=⌊ln({a}_{\text{IR}}/a)/ln2⌋$ steps down to the fixed macroscopic scale ${a}_{\text{IR}}~{\Lambda }_{\text{YM}}^{-1}$, where the effective running coupling is ${\beta }_{\text{IR}}=1/2$. Then, at scale ${a}_{\text{IR}}$, the author invokes the Osterwalder–Seiler transfer matrix ${{T}^{\text{^}}}_{\text{full}}$ for the **pure Wilson action** at ${\beta }_{\text{IR}}=1/2$ to obtain ${m}_{\text{IR}}=-\frac{1}{{a}_{\text{IR}}}ln(1-{e}^{-2{\beta }_{\text{IR}}})>0$ (Eq. 13.34).  
* **Referee Question:** After $N$ steps of block-spin decimation from $a$ to ${a}_{\text{IR}}$, the effective action at scale ${a}_{\text{IR}}$ is **not** the pure single-plaquette Wilson action ${S}_{W}$ with coupling ${\beta }_{\text{IR}}=1/2$; it is the **renormalized effective action** ${S}_{\text{eff}}^{(N)}={S}_{W}({\beta }_{\text{IR}})+\sum\limits_{Y}^{}{K}^{(N)}(Y)$, which contains non-local polymer activities ${K}^{(N)}\in {ℬ}_{\kappa }$ bounded by $‖{K}^{(N)}{‖}_{\kappa }\leq {r}_{\text{max}}=1/4$\!  
* **How to Bridge This Handshake Rigorously:** Because the polymer perturbation ${K}^{(N)}$ is non-zero ($‖{K}^{(N)}{‖}_{\kappa }\leq 1/4$), you must show that:

31. Either the exponential clustering rate ${m}_{\text{IR}}\geq \kappa -\alpha >0$ at scale ${a}_{\text{IR}}$ follows **directly from Theorem 14.7 (Eq. 14.73, p. 158\)** via the Kotecký–Preiss cluster expansion of ${S}_{\text{eff}}^{(N)}$ (which already includes ${K}^{(N)}$\!), and this Euclidean exponential clustering transfers directly to the continuum Hamiltonian ${H}^{\text{^}}$ via the **Semigroup Derivative Engine (Theorem 15.8)** without needing the bare Wilson transfer matrix at ${a}_{\text{IR}}$;  
32. Or, if you use the transfer matrix at ${a}_{\text{IR}}$, you use perturbation theory of the transfer operator (or resolvent identity, Proposition 5.1) to show that adding $‖{K}^{(N)}{‖}_{\kappa }\leq 1/4$ to the Wilson action at ${\beta }_{\text{IR}}=1/2$ shifts the transfer matrix norm by at most $‖{K}^{(N)}{‖}_{\kappa }\leq 0.25<{e}^{-1}\approx 0.3678$, preserving a strictly positive spectral gap\! (In fact, ${e}^{-1}-0.25\approx 0.1178>0$ works beautifully and closes this gap immediately\!).

#### ***Chapter 16: The Dyadic Cauchy Continuum Limit and Osterwalder–Schrader Axioms***

* **Theorem 16.4 (pp. 177–179, Eqs. 16.26–16.41):** Proof of the Dyadic Cauchy Bound.  
* *Scale-Indexing Mismatch in Step 2 (p. 178):* Look at Eqs. (16.31) and (16.34) on p. 178:  
* In Eq. (16.31), $‖\delta {S}_{n}^{(m)}{‖}_{\text{small}}\leq {C}_{\text{small}}{\left({\frac{{a}_{m+1}}{{a}_{0}}}\right)}^{2}={C}_{\text{small}}·{4}^{-(m+1)}\leq {C}_{\text{small}}·{2}^{-m}$. This is completely rigorous (it is the Symanzik $𝒪({a}_{m}^{2})$ scaling of dimension-6 operators).  
* However, look at Eq. (16.34) for the Large-Field and Polymer Fluctuations:

$$\sum\limits_{X\supset \{x\}}^{}|{K}_{m}(X)|exp(c|X|)\leq ({r}_{\text{max}}{)}^{m}\leq {\left({\frac{1}{4}}\right)}^{m}={4}^{-m}\leq {2}^{-m}.$$

**Mathematical Error in Eq. (16.34):** By Eq. (16.32), $‖{K}_{m}{‖}_{\kappa }\leq {r}_{\text{max}}=\frac{1}{4}$ for all $m\geq 0$ (and ${r}_{m}\rightarrow {r}^{*}\approx 0.2111$, **not** $0$, as $m\rightarrow \infty$\!). Where did the power $m$ in $({r}_{\text{max}}{)}^{m}=(1/4{)}^{m}$ come from? The sum of polymer activities of a single polymer $X\supset \{x\}$ at scale $m$ is bounded by $‖{K}_{m}{‖}_{\kappa }\leq {r}_{\text{max}}=1/4$ (or in the UV regime ${a}_{m}\rightarrow 0$, by the Peierls factor $exp(-{c}_{0}/{g}^{2}({a}_{m}))=exp(-{c}_{0}^{′}ln({a}_{0}/{a}_{m}))=({a}_{m}/{a}_{0}{)}^{{c}_{0}^{′}}={2}^{-{c}_{0}^{′}m}$\!).

* **How to Fix Eq. (16.34):** At scale ${a}_{m}={2}^{-m}{a}_{0}$ (which is in the **ultraviolet** regime ${a}_{m}\rightarrow 0$ as $m\rightarrow \infty$\!), the running coupling satisfies $\frac{1}{{g}^{2}({a}_{m})}~\frac{{b}_{0}}{8{\pi }^{2}}mln2$. Therefore, by Bałaban's Peierls bound (Eq. 12.21), the large-field polymer activity at scale ${a}_{m}$ is bounded by:

$$exp\left({-\frac{c}{{g}^{2}({a}_{m})}}\right)\leq C·{2}^{-\gamma m}\leq C·{2}^{-m}$$

for large $m$\! Use the UV Peierls bound $exp(-c/{g}_{m}^{2})~{2}^{-\gamma m}$ in Eq. (16.34) for the $m\rightarrow \infty$ (${a}_{m}\rightarrow 0$) Cauchy tail, rather than $({r}_{\text{max}}{)}^{m}$.

* **Proposition 16.9 (p. 182, Eqs. 16.62–16.68): Proof of Axiom OS2 (Reflection Positivity) in the Continuum.**  
* *Test Function Support vs. Schwartz Space $𝒮(({ℝ}_{+}^{4}{)}^{n})$:* In the proof of Proposition 16.9 (p. 182), the author writes: *"Since each test function ${f}_{n}$ has compact support in $({ℝ}_{+}^{4}{)}^{n}$, there exists a strictly positive Euclidean time distance ${\delta }_{0}>0$ from the boundary ${x}_{0}=0$"*. Technically, functions in $𝒮(({ℝ}_{+}^{4}{)}^{n})$ are smooth functions on ${ℝ}^{4n}$ supported in $[0,\infty )$ whose derivatives vanish at ${x}_{0}=0$, not necessarily compactly supported away from ${x}_{0}=0$. However, ${C}_{c}^{\infty }(({ℝ}_{+}^{4}{)}^{n})$ (functions with compact support strictly inside ${x}_{0}>0$) is **dense** in $𝒮(({ℝ}_{+}^{4}{)}^{n})$ in the Schwartz topology\! Simply add one sentence noting that by density of ${C}_{c}^{\infty }(({ℝ}_{+}^{4}{)}^{n})$ in $𝒮(({ℝ}_{+}^{4}{)}^{n})$ and continuity of ${S}_{m+n}$, it suffices to verify Eq. (16.62) for compactly supported ${f}_{n}$.  
* **Proposition 16.10 (p. 183, Eqs. 16.69–16.77): Cluster Decomposition and Continuum Mass Gap.**  
* *Observables with Support Length in Time:* In Eq. (16.73), the author writes $⟨{\Psi }_{1}^{(k)},{{T}^{\text{^}}}_{{a}_{k}}^{⌊t/{a}_{k}⌋}{P}_{\Omega }^{⟂}{\Psi }_{2}^{(k)}{⟩}_{{ℋ}_{{a}_{k}}}$. If ${\phi }_{1}$ has temporal support inside $[-{T}_{1},0]$ and ${\phi }_{2}$ has temporal support inside $[0,{T}_{2}]$, then translating ${\phi }_{2}$ by $t>{T}_{1}+{T}_{2}$ separates their supports by $t-({T}_{1}+{T}_{2})$, so the power of ${{T}^{\text{^}}}_{{a}_{k}}$ between the two states is $⌊(t-{T}_{1}-{T}_{2})/{a}_{k}⌋$ (absorbing ${e}^{{\Delta }_{\text{min}}({T}_{1}+{T}_{2})}$ into the constant $C({\phi }_{1},{\phi }_{2})$). Mentioning this makes the proof of Proposition 16.10 completely airtight.

#### ***Chapter 17: Assembly of the Construction and the Millennium Prize Theorem***

* **Section 5.4 & Table 17.1 (p. 193): Universal Synthesis Across All Compact Simple Lie Groups (${G}_{2},{F}_{4},{E}_{8}$).**  
* *CRITICAL CONTRADICTION WITH CHAPTERS 7, 8, 10, AND 11:* Look at **Table 17.1 (p. 193\)** for the exceptional Lie groups ${G}_{2}$, ${F}_{4}$, and ${E}_{8}$:  
* Table 17.1 explicitly lists:

$$\text{Center }Z({G}_{2})=\{1\},Z({F}_{4})=\{1\},Z({E}_{8})=\{1\}!$$

* And right below Table 17.1, the text claims:

  ***"In every case, ${b}_{0}>0$, the center $Z(G)$ is compact and discrete, and the Semigroup Derivative Engine proves $\Delta (G)>0$."***

* **Why this contradicts Chapters 7, 8, 10, and 11:** In Chapters 7, 8, 10, and 11 (e.g., Theorem 7.5, Theorem 8.8, Section 10.3, Theorem 11.2, Section 11.6.2), the entire proof of the Positivity Factor $𝒫=1$ was built on decomposing the Hilbert space into $N\geq 2$ superselection sectors $ℋ={⨁}_{k=0}^{N-1}{ℋ}^{(k)}$ graded by a **non-trivial** discrete center $Z(G)≅{ℤ}_{N}$ ($N\geq 2$) and bounding the neutral sector ${ℋ}^{(0)}$ by the non-trivial centre-charged sector ${ℋ}^{(1)}$ ($k=1≢0\left({modN}\right)$)\!  
* For $G={G}_{2},{F}_{4},{E}_{8}$, the center is **trivial** ($Z(G)=\{1\}$, so $N=1$)\! There **is no** centre-charged sector ${ℋ}^{(1)}$ for ${G}_{2},{F}_{4},{E}_{8}$, and in fact, in ${G}_{2},{F}_{4},{E}_{8}$ pure gauge theories, fundamental Wilson loops *do* undergo string breaking at large distances because gluons can screen fundamental charges\! (Despite string breaking at asymptotic distances, ${G}_{2},{F}_{4},{E}_{8}$ still have a glueball mass gap $\Delta >0$ via dimensional transmutation and the cluster expansion / polymer trapping of Chapters 12–14, which do *not* require $Z(G)\ne \{1\}$).  
* **How to Fix:** Either restrict the main theorem to $SU(N)$ ($N\geq 2$) as stated in the Abstract and Theorem 17.3, or explicitly explain in Section 17.5.4 that for centerless groups (${G}_{2},{F}_{4},{E}_{8}$), the mass gap $\Delta (G)>0$ follows directly from the Kotecký–Preiss exponential decay of the gauge-invariant polymer cluster expansion (Theorem 14.7, Eq. 14.73) and the single-plaquette character contraction ${\zeta }_{\text{fund}}(\beta )<1$ (Proposition A.3), which depend only on compactness and simplicity (${C}_{2}(G)>0$) rather than a non-trivial center $Z(G)$.

#### ***Chapter 18: Proof-Theoretic Verification and Kernel Audit in Lean 4***

* **Section 3.2 & Table 18.1 (pp. 196–198): Mapping Between Mathematical Statements and Lean 4 Structures.**  
* *Referee Audit of the Formal-to-Informal Bridge:* While Proposition 18.1 confirms zero sorry and zero custom axioms in the Lean 4 codebase, a formal-methods referee will check whether the Lean 4 definitions use *structural records / axiomatic fields* (bundled inside structure declarations) vs. *constructive definitions from first principles*. For example:

33. On p. 198, item (5) lists PolymerTrappingParams as a structure holding $(\theta ,{C}_{\text{Mayer}},{C}_{\text{vert}},{\beta }_{\text{IR}},{r}_{\text{max}})=(1/2,1/8,1/20,1/2,1/4)$, and item (6) lists autonomousPolymerTrajectory as the 1D scalar map ${r}_{k+1}=\frac{1}{2}{r}_{k}+\frac{1}{8}{r}_{k}^{2}+\frac{1}{10}$. In light of **Warning 14.2 (p. 150\)**, make sure to clarify in Chapter 18 whether firstPrinciplesPolymerTrapping in Lean 4 derives $(1/2,1/8,1/20)$ by integrating over the Haar measure of $SU(N)$ on ${ℤ}^{4}$, or whether those rational bounds are passed as verified rational certificates of the norm-majorant.  
34. In **Bibliography (pp. 221–222)**, references **\[3\] and \[4\]** are identical duplicates, **\[6\] and \[7\]** are identical duplicates, **\[11\] and \[12\]** are identical duplicates, and **\[26\] and \[27\]** are identical duplicates. Furthermore, on **page vi (Contents)**, Bibliography 221 is printed twice.
