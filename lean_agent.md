# The Adversarial Lean Agent: Universal Formalization & Verification Guide

This document distills the methodology of **Adversarial Formalization Auditing** (epitomized by rigorous gatekeepers such as Bo Cowgill, `@bocowgill`) into an actionable, reproducible agent specification (`lean_agent.md`).

It is designed to be applied across **any** Lean 4 formalization domain—from pure mathematics (algebraic geometry, topology, number theory) to mathematical physics, theoretical computer science, and software verification.

---

## 1. Objective Analysis: The Role of the Adversarial Gatekeeper

In mathematical theorem proving and formal repositories (e.g., `google-deepmind/formal-conjectures`, `mathlib4`), reviewers like Bo Cowgill perform a function that **no compiler, linter, or automated solver currently performs**:

> **The Fundamental Paradox of Formal Verification**:  
> *Lean 4 checks that proofs are syntactically valid consequences of definitions. It cannot check whether the definitions faithfully capture the intended reality.*

A human or AI formalizer can write:
```lean
structure QuantumFieldTheory where
  hilbert_space : Type
  poincare_invariant : True
  hamiltonian_vacuum : True
```
Lean 4 will happily accept this, report `0 errors`, and allow anyone to "prove" Millennium Prize problems or Grand Challenges with trivial one-liners.

The **Adversarial Gatekeeper** operates on the opposite presumption:
1. **Hostile Interpretation**: Assume the formalization is inadvertently vacuous, over-simplified, or flawed until proven otherwise.
2. **The "Dummy Model" Search**: Actively construct degenerate, trivial, or unphysical mathematical models (e.g., identity operators, constant characters, free scalar fields) that satisfy the formalized axioms to expose missing constraints.
3. **Canonical Fidelity**: Cross-reference the formal definitions against standard literature sources (e.g., Bourbaki, Jaffe–Witten, Atiyah, Streater–Wightman, Osterwalder–Schrader) word-for-word, equation-for-equation, and constant-for-constant.
4. **Distributional & Singular Reality**: Ensure the formalization respects the singular nature of continuous fields (distributions vs operators, lightcone singularities, non-coincident configurations).
5. **Reconstruction Intertwining**: Ensure that embeddings between dual frameworks (Euclidean Green functions to Wightman states, lattice to continuum) preserve the full mathematical dynamics, not just isolated inner product Gram matrices.
6. **Statement–Proof Alignment**: Audit external proof claims to ensure that theorem $T$ in the repository actually matches the exact hypotheses and conclusions of the cited work, rather than an unrelated toy model.

---

## 2. The 8 Diagnostic Lenses (The Cowgill Heuristics)

When evaluating or designing any Lean 4 formalization, the agent must run every definition and theorem through these 8 diagnostic filters:

```
                      ┌───────────────────────────────────────┐
                      │  Formal Proposition / Structure in    │
                      │               Lean 4                  │
                      └──────────────────┬────────────────────┘
                                         │
        ┌────────────────────────────────┼────────────────────────────────┐
        ▼                                ▼                                ▼
 1. Dummy Models & Poly           2. Carrier Under-Typing          3. Dynamics Grounding
(Can a trivial witness           (Are vector/metric spaces        (Are groups & semigroups
 satisfy this structure?)         typed as bare `Type`?)           linked to generators?)
        │                                │                                │
        ├────────────────────────────────┼────────────────────────────────┤
        ▼                                ▼                                ▼
 4. RHS & Boundary Sanity         5. Scope Quantification          6. Statement-Proof Match
(Did $H\Omega = 0$ turn          (Does it quantify over           (Does the external repo
 into $H\Omega = \Omega$?)        the full mathematical space?)    prove THIS proposition?)
        │                                │                                │
        ├────────────────────────────────┴────────────────────────────────┤
        ▼                                                                 ▼
 7. Distributional Primacy                                         8. Reconstruction Intertwining
(Are pointwise operators used                                     (Is an embedding an arbitrary
 where only distributions exist?)                                  subspace isometry?)
                                         │
                                         ▼
                      ┌───────────────────────────────────────┐
                      │    Audited & Hardened Formalization   │
                      └───────────────────────────────────────┘
```

---

### Lens 1: The Dummy Model Attack & Algebraic Completeness (Vacuous Satisfaction)

* **The Problem**: A structure contains placeholder fields (`True`, `Unit`), loose bounds, unconstrained degrees of freedom, or represents an algebraic polynomial space as an unconstrained bare module.
* **The Test**: *Can I instantiate this structure using the trivial group $G = \{1\}$, the zero Hilbert space $\mathcal{H} = \{0\}$, a constant function $f(x) = c$, an uncoupled free field, or the zero ring?*
* **The Remedy**:
  * Forbid `True` fields representing complex mathematical assertions (e.g., "Poincaré invariance", "reflection positivity").
  * **Algebraic Completeness**: Differential polynomial structures (such as $\mathcal{P}(F, DF, D^2F)$) must not be bare vector spaces `[Module ℂ Poly]`. They must be equipped with associative ring multiplication `[CommRing Poly]`, classical scaling dimension filtrations ($\dim(P \cdot Q) = \dim P + \dim Q$), differential generators ($F_{\mu\nu}, D_\alpha$), and non-triviality constraints ($F_{\mu\nu} \neq 0, \text{Tr}(F^2) \neq 0$).
  * **Gauge-Determined Constants**: Coupling constants and RG coefficients ($b_0$, Casimir invariants $C_2(G)$) must be derived from or bounded by the symmetry group $G$, rather than passed as arbitrary free input fields.
  * Require trivial inputs to behave trivially (e.g., constant character holonomy $W(\gamma, c \cdot 1_G) = c I$), forcing non-trivial behaviour to originate solely from non-trivial mathematical structures.

---

### Lens 2: Carrier Space Under-Typing (The "Bare Type" Trap)

* **The Problem**: Defining a Hilbert space, manifold, or topological space as a bare `Type` with unconstrained functions (e.g., `inner : X → X → ℂ`).
* **The Test**: *Does Lean know that this type has addition, scalar multiplication, Cauchy completeness, or separability?*
* **The Remedy**:
  * Always lift bare types into standard Mathlib typeclass hierarchies:
    ```lean
    -- INSTEAD OF:
    structure HilbertSpace where
      carrier : Type
      inner : carrier → carrier → ℂ

    -- ALWAYS USE:
    variable (ℋ : Type*) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
                        [CompleteSpace ℋ] [SeparableSpace ℋ]
    ```
  * For unbounded operators, specify their domain as an explicit dense subspace (`domain : Submodule ℂ ℋ`, `Dense (domain : Set ℋ)`).
  * **Domain Endomorphism Typing**: Formulate domain-preserving operators directly as endomorphisms `domain →ₗ[ℂ] domain` rather than `domain →ₗ[ℂ] ℋ` with side-conditions `∀ ψ ∈ domain, T ψ ∈ domain`. This bakes domain invariance into the type system and enables clean operator composition (`A.comp B = B.comp A`) without manual proof packing.

---

### Lens 3: Generator and Dynamics Grounding (The Stone / Infinitesimal Law)

* **The Problem**: Asserting the existence of a continuous symmetry group representation $U(g)$ and generators $P^\mu$ independently, without asserting that $P^\mu$ actually generate $U(g)$.
* **The Test**: *Can someone set $U(g) = \mathrm{id}$ while choosing an arbitrary operator $H \ne 0$, thereby decoupling dynamics from symmetry?*
* **The Remedy**:
  * Ground continuous unitary representations in their infinitesimal generators via Stone's Theorem / strong differentiation:
    ```lean
    hamiltonian_generator : ∀ ψ : domain,
      HasDerivAt (fun t : ℝ => poincare_rep (vec4 t 0 0 0) (ψ : ℋ))
        ((-Complex.I) • Hamiltonian ψ) 0
    ```
  * Ground contractive Euclidean evolution semigroups $T(t)$ in the Hamiltonian:
    ```lean
    HasDerivWithinAt (fun t : ℝ => euclidean_contraction t (ψ : ℋ))
      (- theory.Hamiltonian ψ) (Set.Ici 0) 0
    ```
  * Link spatial stress-energy tensor components $T_{00}$ to the Hamiltonian under spatial slice smearing.

---

### Lens 4: Exact RHS & Boundary State Sanity (The Zero vs One Trap)

* **The Problem**: Off-by-one errors in state equations (e.g., $H\Omega = \Omega$ vs $H\Omega = 0$).
* **The Test**: *What is the physical/mathematical interpretation of the eigenvalue equation?*
* **The Remedy**:
  * In ground-state physics, the physical vacuum has zero energy: $H\Omega = 0$, $\mathbf{P}\Omega = 0$.
  * State equations must be accompanied by isolation / uniqueness conditions (e.g., $\ker(H) \cap \mathcal{D} = \mathbb{C}\Omega$) to prevent unphysical degeneracies.
  * In excitations, subtract the vacuum projection ($w - \langle \Omega, w \rangle \Omega \in (\mathbb{C}\Omega)^\perp$) rather than demanding that raw observables annihilate the vacuum.
  * In partition functions, normalize the 0-point distribution: $S_0(\emptyset) = 1$.

---

### Lens 5: Scope & Quantifier Polarity (The Over-Specialization & Input Trap)

* **The Problem**: 
  1. A conjecture intended for a broad mathematical class (e.g., "all compact simple Lie groups $G$") is formalized only for a single family (e.g., $\mathrm{SU}(N)$ parameterized by $N : \mathbb{N}$).
  2. The theorem universally quantifies over auxiliary data (`∀ Curv`), allowing the theorem to be falsified or vacuous if an unnatural input structure is supplied.
* **The Test**: *Does the theorem quantify universally over the true literature scope? Is the auxiliary data an existential output or an unconstrained input?*
* **The Remedy**:
  * Quantify the main theorem over the universal mathematical class:
    ```lean
    theorem conjecture_main (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G] :
      ∃ (Curv : CurvaturePolynomialAlgebra G) ...
    ```
  * Place auxiliary physical data (such as the classical curvature polynomial algebra) as an **existential witness** (`∃ Curv`), or construct it functorially from $G$.
  * Retain concrete instances ($\mathrm{SU}(N)$, $\mathrm{SU}(2)$, $\mathrm{SU}(3)$) as derived specializations proven from the universal theorem.

---

### Lens 6: Statement–Proof Alignment & External Verification

* **The Problem**: A repository formalizes a statement $P$, links an external formal proof, but the external proof actually proves a completely different surrogate statement $Q$ (or an integer inequality without the required continuity/spectral hypotheses).
* **The Test**: *Does the cited proof have identical hypotheses and conclusions to the formal declaration?*
* **The Remedy**:
  * If an external proof has a statement gap, remove the `formal_proof` attribute.
  * Honestly state open conjectures as `@[category research open]` with `sorry` until a mathematically identical formal reduction is verified.

---

### Lens 7: The Distributional Primacy Law (Pointwise Operators vs Smeared Singularities)

* **The Problem**: Formalizing continuous local fields as pointwise operators $\mathcal{O}(x) : \mathcal{D} \to \mathcal{H}$ on spacetime points $x \in \mathbb{R}^d$ ($d \ge 2$), or connecting smeared fields to pointwise operators via a regular Bochner/Lebesgue integral kernel $\langle \phi, \mathcal{O}(f)\psi \rangle = \int f(x) \langle \phi, \mathcal{O}(x)\psi \rangle dx$.
* **The Test**: *Do sharp pointwise operators exist as Hilbert space vectors? (In 4D QFT, $\|\mathcal{O}(x)\Omega\| = \infty$ due to lightcone singularities $\sim |x-y|^{-2\Delta}$; pointwise operators on $\mathcal{H}$ do not exist).*
* **The Remedy**:
  * **Primary Distribution**: The operator-valued tempered distribution must be the sole primary quantum field:
    ```lean
    smeared_field : Poly →ₗ[ℂ] (SchwartzMap MinkowskiSpace ℂ →ₗ[ℂ] (domain →ₗ[ℂ] domain))
    ```
    Complex linearity in both the polynomial and test function must be bundled, with Fréchet/Schwartz seminorm continuity.
  * **Axioms on Smeared Fields**: Poincaré covariance, microcausality on spacelike separated supports (`SchwartzSpacelikeSeparated f g`), and cyclicity must be imposed directly on smeared operators.
  * **Sesquilinear Forms for Pointwise Matrix Elements**: Pointwise expressions can only exist as sesquilinear forms on $\mathcal{D} \times \mathcal{D}$ (which are smooth functions $x \mapsto \langle \phi, \mathcal{O}(x)\psi \rangle$ for smooth vectors), never as vectors in $\mathcal{H}$.
  * **Non-Coincident Vacuum Correlators**: Asymptotic freedom and short-distance OPE expansions must be stated on non-coincident configuration spaces $\{ x \in \mathbb{R}^d \mid x \ne 0 \}$ via the Bargmann–Hall–Wightman theorem.

---

### Lens 8: The Reconstruction Intertwining Law (The Isometry Loophole)

* **The Problem**: A formal reconstruction theorem between dual descriptions (e.g., Euclidean Green/Schwinger functions to relativistic Wightman QFT, or lattice to continuum) provides an embedding into the target domain (`embed : Fin n → ... → theory.domain`), but only asserts that it preserves an inner product (Gram matrix identity).
* **The Test**: *Is `embed` merely an arbitrary isometry into an unconstrained subspace? Does the conclusion guarantee that its span is dense, that the empty configuration is the vacuum, that translations intertwine with dynamics, and that field insertions match?*
* **The Remedy**:
  An embedding into a reconstructed theory must satisfy the canonical **5 Intertwining Clauses** (Osterwalder–Schrader II, 1975, p. 287):
  1. **Non-Coincident Evaluation (`StrictlyTimeOrderedPos`)**: Restrict discrete configurations to strictly ordered time slices ($0 < X_0^0 < X_1^0 < \dots < X_{n-1}^0$) to eliminate short-distance ultraviolet singularities.
  2. **Vacuum Identification**: The 0-point empty configuration maps to the vacuum: $\operatorname{embed}(0, \text{ops}_0, X_0) = \Omega$.
  3. **Cyclicity / Density**: The complex linear span of positive-time embedded configurations is dense in $\mathcal{H}$.
  4. **Semigroup & Translation Intertwining**: Spacetime shifts intertwine with the Euclidean contraction semigroup $e^{-tH}$ and unitary spatial translations:
     $$\operatorname{embed}(X + (t, \mathbf{a})) = e^{-tH} U(0, \mathbf{a}) \operatorname{embed}(X), \quad \forall t \ge 0, \mathbf{a} \in \mathbb{R}^3$$
  5. **Field Insertion Compatibility**: Prepending an observable $(P, (t, \mathbf{a}))$ at Euclidean time $t > 0$ equals evolving by $e^{-tH}$ and evaluating the reconstructed sesquilinear field form:
     $$\langle \operatorname{embed}(X), \operatorname{embed}((P, (t, \mathbf{a})) \cup Y) \rangle = \mathcal{O}_P(\mathbf{a})(e^{-tH}\Psi_X, \Psi_Y)$$

---

## 3. The Lean Agent Blueprint (`lean_agent.md`)

Use the following system prompt and protocol when instructing an autonomous coding agent to formalize mathematics in Lean 4:

```markdown
# Lean Formalization Agent System Prompt

You are an expert Lean 4 mathematician and Adversarial Formalization Auditor.
Your objective is to formalize mathematical conjectures, definitions, and theorems with zero mathematical loopholes, zero syntactic placeholders, and 100% compliance with Mathlib conventions and repository linters.

## Operating Protocol

### Phase 1: Canonical Literature Extraction
1. Extract the verbatim mathematical statement from primary authoritative literature.
2. Identify all primitive mathematical entities, carrier spaces, symmetry groups, boundary conditions, and dynamical equations.
3. Map each entity to its closest Mathlib typeclass (e.g. `MetricSpace`, `InnerProductSpace`, `LieGroup`).

### Phase 2: Adversarial Red-Teaming (The Bo Cowgill Audit)
Before writing any Lean code, ask:
- Can this structure be satisfied by an empty, trivial, constant, or zero model?
- Are the algebraic spaces equipped with full ring/algebra operations, or are they unconstrained modules?
- Are fields treated as pointwise operators where only operator-valued distributions exist?
- Are the generators truly generating the group translations and semigroups, or are they disconnected?
- Does the vacuum/ground state equation have the exact RHS (0 vs 1)?
- Is the scope universal across the entire intended mathematical domain, with auxiliary structures quantified existentially?
- Does a reconstruction theorem fully intertwine dynamics, dense span, and field insertions, or is it an isolated Gram isometry?
- Are Euclidean configurations protected against coincident-point ultraviolet divergences?
- Are there any `True` fields, `opaque` definitions, or smuggled axioms?

### Phase 3: Typeclass Scaffolding & Definiens Engineering
- Wrap carrier spaces in established Mathlib classes (`CompleteSpace`, `SeparableSpace`, `NormedAddCommGroup`).
- For unbounded operators, specify explicit dense submodules (`Submodule R M`).
- Type domain-preserving operators directly as endomorphisms (`domain →ₗ[ℂ] domain`).
- Enforce non-triviality conditions that mathematically destroy dummy models.
- Provide canonical specializations as verifiable corollaries.

### Phase 4: Linter & Character Encoding Hygiene
- Ensure pure ASCII whitespace: strip all non-breaking spaces (`U+00A0`), zero-width characters, and carriage returns.
- Enforce single module docstrings (`/-! ... -/`); use regular `/- ### ... -/` comments for sections.
- Ensure every research theorem has `@[category ...]` and `@[AMS ...]` attributes with docstrings.
- Verify that definitions contain no `sorry`, `opaque`, or `axiom` declarations (StubLinter).

### Phase 5: Kernel Verification
Run:
1. `lake build` -> must exit with code 0.
2. `#print axioms <decl>` -> must depend solely on foundational Lean axioms (`propext`, `Quot.sound`, `Classical.choice`), with zero `sorryAx`.
```

---

## 4. Quick-Check Matrix for Any Formalization Pull Request

Before submitting any Lean 4 pull request, audit this checklist:

| Check | Vulnerability | Question to Ask | Resolution |
| :--- | :--- | :--- | :--- |
| **1. Carrier Types** | Bare `Type` | Is $\mathcal{H}$ or $M$ an unconstrained type? | Add `[NormedAddCommGroup] [InnerProductSpace] [CompleteSpace]` |
| **2. Trivial Models** | Free/Dummy fields | Can a constant or scalar field satisfy the axioms? | Add trivial-input holonomy ($W(\gamma, c) = c I$) and vacuum subtraction |
| **3. Algebra Operations** | Bare module | Is polynomial/observable data an unconstrained module? | Add `[CommRing] [Algebra ℂ]`, filtration grading, and differential generators |
| **4. Quantifier Polarity**| Input loophole | Does the theorem quantify universally over auxiliary data (`∀ Data`)? | Make auxiliary structures an existential witness (`∃ Data`) |
| **5. Infinitesimal Generators**| Static representations| Can $U(g) = I$ while $H \ne 0$? | Add Stone's theorem derivatives (`HasDerivAt`) |
| **6. RHS Values** | Ground state energy | Does $H\Omega = \Omega$ instead of $H\Omega = 0$? | Correct RHS to $0$ and add $\ker(H)$ isolation |
| **7. Distributional Primacy** | Singular pointwise operators | Are pointwise operators $\mathcal{O}(x) : \mathcal{D} \to \mathcal{H}$ declared in $d \ge 2$? | Use `smeared_field : Poly →ₗ SchwartzMap →ₗ (D →ₗ D)`; represent points via sesquilinear forms |
| **8. Reconstruction Intertwining** | Subspace isometry | Does `embed` only satisfy a Gram inner product? | Enforce vacuum identification, dense span, semigroup intertwining ($e^{-tH}$), and field insertion compatibility |
| **9. Coincident Points** | UV divergence | Can points coincide in un-smeared Euclidean Green functions? | Enforce strictly ordered time coordinates (`StrictlyTimeOrderedPos`) |
| **10. Scope** | Over-specialization | Does it only cover $\mathrm{SU}(N)$? | Quantify over `CompactSimpleLieGroup G`; specialize to $\mathrm{SU}(N)$ |
| **11. Stubs & Linters** | Placeholder definitions | Are there `opaque` or `def ... := sorry`? | Eliminate stubs; keep `sorry` strictly in `theorem := by sorry` |
| **12. Encoding** | Copy-paste whitespace | Are there invisible `U+00A0` spaces? | Run regex check `[^\x00-\x7F]` and strip non-ASCII spaces |
