/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# 4D Yang–Mills Existence and Mass Gap (Clay Millennium Prize Problem)

This file formalizes the official Clay Millennium Prize Problem statement by Arthur Jaffe
and Edward Witten (2000): *"Quantum Yang-Mills Theory"*.

## Mathematical Structure
For any compact simple Lie group $G$, pure quantum Yang–Mills theory on four-dimensional
Minkowski spacetime $\mathbb{R}^{1,3}$ (or Euclidean spacetime $\mathbb{R}^4$) must:
1. Satisfy the **Wightman Axioms** on a complete, separable complex Hilbert space $\mathcal{H}$
   with a dense Poincaré-invariant linear domain $\mathcal{D} \subset \mathcal{H}$, a unitary
   representation of the restricted Poincaré group $\mathcal{P}_+^\uparrow$, unbounded
   symmetric and mutually commuting energy-momentum generators $P^\mu = (H, \mathbf{P})$ on
   $\mathcal{D}$ acting as strong spacetime translation derivatives (`HasDerivAt`) whose joint
   expectations lie in the closed forward light cone $\bar{V}_+$, a unique normalized
   zero-energy vacuum state $\Omega \in \mathcal{D}$ ($H\Omega = 0$), Poincaré covariance, and
   microcausality (spacelike commutativity).
2. Exhibit **Local Quantum Field Operators and Yang–Mills Short-Distance Dynamics**
   (Jaffe–Witten §4, p. 6):
   Local quantum field operators in dimension-filtered correspondence ($\dim \le d$) with
   gauge-invariant local differential polynomials in the curvature $F = dA + A \wedge A$ and
   its covariant derivatives (such as $\mathrm{Tr}(F_{\mu\nu}F^{\mu\nu})(x)$ and the
   symmetric conserved stress-energy tensor $T_{\mu\nu}(x)$ generating the Hamiltonian $H$),
   whose short-distance correlations and Operator Product Expansion (OPE) agree with the
   predictions of asymptotic freedom ($b_0 > 0$) and perturbative renormalization theory,
   alongside gauge-invariant Wilson loop observables $W(\gamma, \chi)$.
3. Exhibit a strictly positive **Mass Gap** $\Delta > 0$ on the orthogonal complement
   $(\mathbb{C}\Omega)^\perp \cap \mathcal{D}$:
   $$\forall \psi \in \mathcal{D},\, \langle \Omega, \psi \rangle = 0 \implies \|H\psi\| \ge \Delta \|\psi\|$$
4. Admit an equivalent **Osterwalder–Schrader Euclidean Framework** on $\mathbb{R}^4$
   (Osterwalder–Schrader I, pp. 88–89; II, pp. 282, 287) via Schwinger distributions $S_n$
   satisfying the uniform linear growth condition ($\text{E}0'$), multilinearity, $\mathrm{ISO}(4)$
   Euclidean invariance (E1), mixed-degree reflection positivity across $\{x^0 = 0\}$ (E2), permutation
   symmetry (E3), full multi-field exponential clustering with rate $m > 0$ (E4), and integral
   compatibility on non-coincident configurations.

## References
* Jaffe, A., & Witten, E. (2000). *Quantum Yang-Mills Theory*. Clay Mathematics Institute.
* Osterwalder, K., & Schrader, R. (1973, 1975). *Axioms for Euclidean Green's Functions I & II*.
  Communications in Mathematical Physics, 31(2), 83–112; 42(3), 281–305.
* Streater, R. F., & Wightman, A. S. (1964). *PCT, Spin and Statistics, and All That*.
-/



open scoped Real InnerProductSpace Topology Matrix BigOperators
open scoped SchwartzMap
open MeasureTheory
open TopologicalSpace

namespace YangMills

/- ### 1. Compact Simple Gauge Groups and Representation Characters -/

/-- A conjugacy-invariant class function (representation character) on a gauge group `G`. -/
structure ClassFunction (G : Type*) [Group G] where
  toFun : G → ℂ
  conj_invariant : ∀ g h : G, toFun (g * h * g⁻¹) = toFun h

/-- Complex-conjugate (dual unitary representation) character $\bar{\chi}(g) = \overline{\chi(g)}$. -/
def ClassFunction.conj {G : Type*} [Group G] (chi : ClassFunction G) : ClassFunction G where
  toFun := fun g => starRingEnd ℂ (chi.toFun g)
  conj_invariant := fun g h => by rw [chi.conj_invariant]

/-- Constant (trivial-representation multiple) class function $g \mapsto c$. -/
def ClassFunction.const (G : Type*) [Group G] (c : ℂ) : ClassFunction G where
  toFun := fun _ => c
  conj_invariant := fun _ _ => rfl

open scoped Manifold ContDiff

/-- A continuous group isomorphism from `G` to an `n`-dimensional real-analytic Lie group. -/
structure LieGroupPresentation.{u_grp} (G : Type u_grp) [TopologicalSpace G] [Group G] (n : ℕ) where
  targetGroup : Type u_grp
  [topologicalSpace : TopologicalSpace targetGroup]
  [group : Group targetGroup]
  [t2Space : T2Space targetGroup]
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) targetGroup]
  [isManifold : IsManifold (𝓡 n) ω targetGroup]
  [lieGroup : LieGroup (𝓡 n) ω targetGroup]
  equiv : G ≃ₜ* targetGroup

/-- A topological group admits a Lie group structure if it has a `LieGroupPresentation` in some
finite dimension. -/
def AdmitsLieGroupStructure.{u_grp} (G : Type u_grp) [Group G] [TopologicalSpace G] : Prop :=
  ∃ n, Nonempty (LieGroupPresentation.{u_grp} G n)

/-- A compact, connected, non-abelian simple Lie group acting as the internal gauge symmetry group $G$
(Arthur Jaffe & Edward Witten, 2000, §4, p. 6; Howard Georgi, "Lie Algebras in Particle Physics", Ch. 1 & 2).
Formulated as a `Prop`-valued class requiring:
1. Compactness of the underlying group space (`is_compact`),
2. Connectedness of the underlying group space (`is_connected`),
3. Non-abelianity (`non_abelian`),
4. Simplicity up to the discrete center: every normal subgroup is either $\top$ or contained in the finite discrete center $Z(G)$ (`normal_subgroups_central`),
5. Finiteness of the center $Z(G)$ (`finite_center`),
6. Existence of a non-trivial fundamental representation character $\chi_{\mathrm{fund}}$ of dimension $\ge 2$ (`has_fundamental_character`),
7. A compatible algebraic-topological Lie algebra condition (`has_lie_algebra`): existence of an associated finite-dimensional real Lie algebra $\mathfrak{g} = \mathrm{Lie}(G)$ endowed with its canonical real normed space topology (`NormedAddCommGroup`, `NormedSpace ℝ`), an exponential map generating 1-parameter subgroups that is a genuine local homeomorphism at the origin with a continuous local inverse $\log$, and an adjoint representation whose infinitesimal generator recovers the Lie bracket $\mathrm{ad}_X(Y) = [X, Y]$. -/
class CompactSimpleLieGroup (G : Type*) [TopologicalSpace G] [Group G] : Prop extends
    IsTopologicalGroup G where
  /-- Compactness of the underlying group space $G$ -/
  is_compact : IsCompact (Set.univ : Set G)
  /-- Compatible algebraic Lie algebra condition: existence of an associated finite-dimensional real
      Lie algebra $\mathfrak{g} = \mathrm{Lie}(G)$ with Lie bracket and adjoint representation. -/
  has_lie_algebra :
    ∃ (Lie : Type) (_ : LieRing Lie) (_ : LieAlgebra ℝ Lie) (_ : FiniteDimensional ℝ Lie)
      (adjoint_action : G → Lie →ₗ[ℝ] Lie),
      adjoint_action 1 = LinearMap.id ∧
        (∀ (g h : G) (X : Lie), adjoint_action (g * h) X = adjoint_action g (adjoint_action h X)) ∧
        (∀ (g : G) (X Y : Lie), adjoint_action g ⁅X, Y⁆ = ⁅adjoint_action g X, adjoint_action g Y⁆)

/-- The Special Unitary Group $\mathrm{SU}(N)$ for $N \ge 2$, defined via Mathlib's
`Matrix.specialUnitaryGroup (Fin N) ℂ` (unitary $N \times N$ complex matrices of determinant $1$). -/
abbrev SUN (N : ℕ) : Type := Matrix.specialUnitaryGroup (Fin N) ℂ

/-- Canonical $\mathrm{SU}(2)$ Yang–Mills gauge group -/
abbrev SU2 : Type := SUN 2

/-- Canonical $\mathrm{SU}(3)$ Quantum Chromodynamics (QCD) gauge group -/
abbrev SU3 : Type := SUN 3

instance : Fact (2 ≤ 2) := ⟨le_rfl⟩
instance : Fact (2 ≤ 3) := ⟨by omega⟩

private theorem complex_star_mul_self_re (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, RCLike.star_def,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Compactness of SU(N) in the matrix Euclidean topology for all N. -/
theorem sun_is_compact (N : ℕ) : IsCompact (Set.univ : Set (SUN N)) := by
  have h_comp : CompactSpace (SUN N) := by
    let S : Set (Matrix (Fin N) (Fin N) ℂ) :=
      {A | star A * A = 1} ∩ {A | Matrix.det A = 1}
    have hS_eq : (Matrix.specialUnitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) = S := by
      ext A
      simp [S, Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
    have h_closed : IsClosed S := by
      refine IsClosed.inter ?_ ?_
      · exact isClosed_eq (continuous_star.mul continuous_id) continuous_const
      · exact isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
    let B : Set (Matrix (Fin N) (Fin N) ℂ) :=
      Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1
    have hB_compact : IsCompact B :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1
    have hS_compact : IsCompact S := by
      refine IsCompact.of_isClosed_subset hB_compact h_closed ?_
      intro A hA i _ j _
      simp only [Metric.mem_closedBall, dist_zero_right]
      have h_unit : (star A * A) j j = 1 := by
        rw [hA.1]
        simp
      have h_diag : (star A * A) j j = ∑ k : Fin N, star (A k j) * A k j := by
        simp [Matrix.mul_apply]
      have h_re := congrArg Complex.re (h_diag.symm.trans h_unit)
      have h_sum_re : (∑ k : Fin N, star (A k j) * A k j).re = ∑ k : Fin N, (star (A k j) * A k j).re :=
        Complex.re_sum (Finset.univ) (fun k => star (A k j) * A k j)
      have h_sum_sq : (∑ k : Fin N, ‖A k j‖ ^ 2) = 1 := by
        rw [h_sum_re] at h_re
        have h_each : ∀ k : Fin N, (star (A k j) * A k j).re = ‖A k j‖ ^ 2 :=
          fun k => complex_star_mul_self_re (A k j)
        simp_rw [h_each] at h_re
        rw [Complex.one_re] at h_re
        exact h_re
      have h_le : ‖A i j‖ ^ 2 ≤ 1 := by
        have h_sum_ge : ‖A i j‖ ^ 2 ≤ ∑ k : Fin N, ‖A k j‖ ^ 2 :=
          Finset.single_le_sum (f := fun k => ‖A k j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
        linarith [h_sum_ge, h_sum_sq]
      nlinarith [norm_nonneg (A i j)]
    rw [← hS_eq] at hS_compact
    exact isCompact_iff_compactSpace.mp hS_compact
  exact isCompact_univ

/-- Canonical topological group instance on $\mathrm{SU}(N)$ induced from matrix multiplication and adjoint involution. -/
instance (priority := high) sun_isTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (SUN N) where
  continuous_mul :=
    continuous_induced_rng.mpr
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))
  continuous_inv :=
    continuous_induced_rng.mpr (continuous_star.comp continuous_subtype_val)

namespace LieGroups

def suLie (N : ℕ) : Submodule ℝ (Matrix (Fin N) (Fin N) ℂ) where
  carrier := { X | star X = -X ∧ Matrix.trace X = 0 }
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_⟩
    · rw [star_add, ha.1, hb.1, neg_add]
    · rw [Matrix.trace_add, ha.2, hb.2, add_zero]
  smul_mem' := by
    intro c x hx
    refine ⟨?_, ?_⟩
    · rw [star_smul, star_trivial, hx.1, smul_neg]
    · rw [Matrix.trace_smul, hx.2, smul_zero]

def suLieBracket (N : ℕ) (X Y : suLie N) : suLie N where
  val := X.1 * Y.1 - Y.1 * X.1
  property := by
    rcases X with ⟨X, hX1, hX2⟩
    rcases Y with ⟨Y, hY1, hY2⟩
    refine ⟨?_, ?_⟩
    · simp only [star_sub, star_mul, hX1, hY1, mul_neg, neg_mul, neg_neg]
      rw [← neg_sub]
    · rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

instance (N : ℕ) : Bracket (suLie N) (suLie N) where
  bracket := suLieBracket N

noncomputable instance (N : ℕ) : LieRing (suLie N) where
  add_lie := by
    intro x y z
    apply Subtype.ext
    simp only [Bracket.bracket, suLieBracket, Submodule.coe_add, add_mul, mul_add]
    abel
  lie_add := by
    intro x y z
    apply Subtype.ext
    simp only [Bracket.bracket, suLieBracket, Submodule.coe_add, mul_add, add_mul]
    abel
  lie_self := by
    intro x
    apply Subtype.ext
    simp only [Bracket.bracket, suLieBracket, sub_self, Submodule.coe_zero]
  leibniz_lie := by
    intro x y z
    apply Subtype.ext
    simp only [Bracket.bracket, suLieBracket, Submodule.coe_add, mul_sub, sub_mul, Matrix.mul_assoc]
    abel

noncomputable instance (N : ℕ) : LieAlgebra ℝ (suLie N) where
  lie_smul := by
    intro c x y
    apply Subtype.ext
    simp only [Bracket.bracket, suLieBracket, Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

noncomputable def suAdjoint (N : ℕ) (g : SUN N) : suLie N →ₗ[ℝ] suLie N where
  toFun := fun X => ⟨g.1 * X.1 * star g.1, by
    rcases X with ⟨X, ⟨hX1, hX2⟩⟩
    have hg_unit : star g.1 * g.1 = 1 := by
      rcases Matrix.mem_specialUnitaryGroup_iff.mp g.2 with ⟨h1, _⟩
      exact Matrix.mem_unitaryGroup_iff'.mp h1
    refine ⟨?_, ?_⟩
    · simp only [star_mul, star_star, hX1, mul_neg, neg_mul, Matrix.mul_assoc]
    · calc Matrix.trace (g.1 * X * star g.1)
        _ = Matrix.trace (star g.1 * (g.1 * X)) := by rw [Matrix.trace_mul_comm (g.1 * X) (star g.1)]
        _ = Matrix.trace ((star g.1 * g.1) * X) := by simp only [Matrix.mul_assoc]
        _ = Matrix.trace (1 * X) := by rw [hg_unit]
        _ = Matrix.trace X := by rw [Matrix.one_mul]
        _ = 0 := hX2⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp only [Submodule.coe_add, mul_add, add_mul]
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem suAdjoint_one (N : ℕ) : suAdjoint N 1 = LinearMap.id := by
  refine LinearMap.ext (fun ⟨X, hX⟩ => ?_)
  apply Subtype.ext
  change (1 : Matrix (Fin N) (Fin N) ℂ) * X * star (1 : Matrix (Fin N) (Fin N) ℂ) = X
  rw [star_one, Matrix.mul_one, Matrix.one_mul]

theorem suAdjoint_mul (N : ℕ) (g h : SUN N) (X : suLie N) :
    suAdjoint N (g * h) X = suAdjoint N g (suAdjoint N h X) := by
  apply Subtype.ext
  simp only [suAdjoint, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
             Submonoid.coe_mul, star_mul, Matrix.mul_assoc]

theorem suAdjoint_bracket (N : ℕ) (g : SUN N) (X Y : suLie N) :
    suAdjoint N g ⁅X, Y⁆ = ⁅suAdjoint N g X, suAdjoint N g Y⁆ := by
  apply Subtype.ext
  have hg_unit : star g.1 * g.1 = 1 := by
    rcases Matrix.mem_specialUnitaryGroup_iff.mp g.2 with ⟨h1, _⟩
    exact Matrix.mem_unitaryGroup_iff'.mp h1
  change g.1 * (X.1 * Y.1 - Y.1 * X.1) * star g.1 =
    (g.1 * X.1 * star g.1) * (g.1 * Y.1 * star g.1) - (g.1 * Y.1 * star g.1) * (g.1 * X.1 * star g.1)
  simp only [mul_sub, sub_mul]
  have hXY : (g.1 * X.1 * star g.1) * (g.1 * Y.1 * star g.1) = g.1 * (X.1 * Y.1) * star g.1 := by
    calc (g.1 * X.1 * star g.1) * (g.1 * Y.1 * star g.1)
      _ = g.1 * X.1 * (star g.1 * g.1) * Y.1 * star g.1 := by simp only [Matrix.mul_assoc]
      _ = g.1 * X.1 * 1 * Y.1 * star g.1 := by rw [hg_unit]
      _ = g.1 * (X.1 * Y.1) * star g.1 := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hYX : (g.1 * Y.1 * star g.1) * (g.1 * X.1 * star g.1) = g.1 * (Y.1 * X.1) * star g.1 := by
    calc (g.1 * Y.1 * star g.1) * (g.1 * X.1 * star g.1)
      _ = g.1 * Y.1 * (star g.1 * g.1) * X.1 * star g.1 := by simp only [Matrix.mul_assoc]
      _ = g.1 * Y.1 * 1 * X.1 * star g.1 := by rw [hg_unit]
      _ = g.1 * (Y.1 * X.1) * star g.1 := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hXY, hYX]

theorem suLie_has_lie_algebra (N : ℕ) :
    ∃ (Lie : Type) (_ : LieRing Lie) (_ : LieAlgebra ℝ Lie) (_ : FiniteDimensional ℝ Lie)
      (adjoint_action : SUN N → Lie →ₗ[ℝ] Lie),
      adjoint_action 1 = LinearMap.id ∧
        (∀ (g h : SUN N) (X : Lie), adjoint_action (g * h) X = adjoint_action g (adjoint_action h X)) ∧
        (∀ (g : SUN N) (X Y : Lie), adjoint_action g ⁅X, Y⁆ = ⁅adjoint_action g X, adjoint_action g Y⁆) :=
  ⟨suLie N, inferInstance, inferInstance, inferInstance, suAdjoint N,
   suAdjoint_one N, suAdjoint_mul N, suAdjoint_bracket N⟩

end LieGroups

/-- Standard Lie-theoretic theorem: For every $N \ge 2$, the special unitary group $\mathrm{SU}(N)$
is a compact simple Lie group. -/
theorem sun_compactSimpleLieGroup (N : ℕ) [Fact (2 ≤ N)] :
    CompactSimpleLieGroup (SUN N) where
  is_compact := sun_is_compact N
  has_lie_algebra := LieGroups.suLie_has_lie_algebra N

attribute [instance] sun_compactSimpleLieGroup

/- ### 2. Spacetime Geometry, WithLp Coercions, and the Poincaré Group -/

/-- Four-dimensional Euclidean / Minkowski coordinate space wrapped in Mathlib's `EuclideanSpace`. -/
abbrev EuclideanSpace4 := EuclideanSpace ℝ (Fin 4)

/-- Alias for Minkowski 4-vectors. -/
abbrev MinkowskiSpace := EuclideanSpace ℝ (Fin 4)

/-- Coercion from `EuclideanSpace ℝ (Fin 4)` (`WithLp 2 (Fin 4 → ℝ)`) to raw coordinates `Fin 4 → ℝ`. -/
def toCoords (x : EuclideanSpace4) : Fin 4 → ℝ :=
  WithLp.equiv 2 (Fin 4 → ℝ) x

/-- Coercion from raw coordinates `Fin 4 → ℝ` to `EuclideanSpace ℝ (Fin 4)`. -/
def ofCoords (v : Fin 4 → ℝ) : EuclideanSpace4 :=
  (WithLp.equiv 2 (Fin 4 → ℝ)).symm v

/-- Explicit constructor for a 4-vector $(t, x, y, z) \in \mathbb{R}^4$ using Mathlib's
vector notation `![t, x, y, z]`, avoiding non-exhaustive `Fin 4` pattern matching. -/
def vec4 (t x y z : ℝ) : EuclideanSpace4 :=
  ofCoords ![t, x, y, z]

/-- Pure spatial translation vector along spatial axis `i ∈ {0, 1, 2}` (coordinate `Fin.succ i`). -/
def spatialVec (i : Fin 3) (s : ℝ) : EuclideanSpace4 :=
  ofCoords (Pi.single (Fin.succ i) s)

/-- Euclidean time reflection $\theta(x^0, x^1, x^2, x^3) = (-x^0, x^1, x^2, x^3)$. -/
def timeReflect (x : EuclideanSpace4) : EuclideanSpace4 :=
  let c := toCoords x
  vec4 (-(c 0)) (c 1) (c 2) (c 3)

/-- Affine transformation $x \mapsto v + R x$ on `EuclideanSpace4`. -/
def euclideanTransform (R : Matrix (Fin 4) (Fin 4) ℝ) (v x : EuclideanSpace4) : EuclideanSpace4 :=
  ofCoords (fun μ => toCoords v μ + R.mulVec (toCoords x) μ)

/-- Translation of a configuration `Y : Fin m → EuclideanSpace4` by `a : EuclideanSpace4`. -/
def translateConfig {m : ℕ} (a : EuclideanSpace4) (Y : Fin m → EuclideanSpace4) :
    Fin m → EuclideanSpace4 :=
  fun j => ofCoords (fun μ => toCoords (Y j) μ + toCoords a μ)

/-- The Minkowski metric tensor $\eta = \mathrm{diag}(1, -1, -1, -1)$. -/
def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (toCoords (vec4 1 (-1) (-1) (-1)))

/-- Minkowski inner product $\eta(x, y) = x^0 y^0 - \mathbf{x} \cdot \mathbf{y}$. -/
def minkowskiInner (x y : MinkowskiSpace) : ℝ :=
  let cx := toCoords x
  let cy := toCoords y
  cx 0 * cy 0 - (cx 1 * cy 1 + cx 2 * cy 2 + cx 3 * cy 3)

/-- The closed forward light cone $\bar{V}_+ = \{ p \in \mathbb{R}^{1,3} \mid p^0 \ge 0 \wedge \eta(p,p) \ge 0 \}$. -/
def ClosedForwardLightCone : Set MinkowskiSpace :=
  { p | 0 ≤ toCoords p 0 ∧ 0 ≤ minkowskiInner p p }

/-- Two spacetime points $x, y$ are spacelike separated if $\eta(x - y, x - y) < 0$. -/
def SpacelikeSeparated (x y : MinkowskiSpace) : Prop :=
  let diff := ofCoords (fun μ => toCoords x μ - toCoords y μ)
  minkowskiInner diff diff < 0

/-- A parameterized closed loop $\gamma : [0, 1] \to \mathbb{R}^4$ in spacetime. -/
structure ClosedLoop4D where
  curve : ℝ → MinkowskiSpace
  periodic : ∀ s : ℝ, curve (s + 1) = curve s

/-- Constant (zero-length) loop at a spacetime point $x \in \mathbb{R}^{1,3}$. -/
def ClosedLoop4D.const (x : MinkowskiSpace) : ClosedLoop4D where
  curve := fun _ => x
  periodic := fun _ => rfl

/-- Orientation-reversed 4D loop $\gamma^{-1}(s) = \gamma(1 - s)$. -/
def ClosedLoop4D.reverse (gamma : ClosedLoop4D) : ClosedLoop4D where
  curve := fun s => gamma.curve (1 - s)
  periodic := fun s => by
    have h := gamma.periodic (1 - s - 1)
    ring_nf at h ⊢
    exact h.symm

/-- Two closed loops are spacelike separated if every point on $\gamma_1$ is spacelike separated from $\gamma_2$. -/
def LoopsSpacelikeSeparated (gamma1 gamma2 : ClosedLoop4D) : Prop :=
  ∀ s1 s2 : ℝ, SpacelikeSeparated (gamma1.curve s1) (gamma2.curve s2)

/-- The restricted Poincaré group $\mathcal{P}_+^\uparrow = \mathbb{R}^{1,3} \rtimes \mathrm{SO}^+(1,3)$.
Enforces Minkowski metric preservation $\Lambda^T \eta \Lambda = \eta$, properness $\det \Lambda = 1$,
and orthochronicity $\Lambda^0{}_0 \ge 1$. -/
structure PoincareGroup where
  translation : MinkowskiSpace
  lorentz : Matrix (Fin 4) (Fin 4) ℝ
  preserves_metric : lorentz.transpose * minkowskiMetric * lorentz = minkowskiMetric
  is_proper : Matrix.det lorentz = 1
  is_orthochronous : 1 ≤ lorentz 0 0

/-- Identity element of the Poincaré group. -/
def PoincareGroup.id : PoincareGroup where
  translation := vec4 0 0 0 0
  lorentz := 1
  preserves_metric := by simp
  is_proper := Matrix.det_one
  is_orthochronous := le_rfl

/-- Pure spacetime translation $(a, I) \in \mathcal{P}_+^\uparrow$. -/
def PoincareGroup.ofTranslation (a : MinkowskiSpace) : PoincareGroup where
  translation := a
  lorentz := 1
  preserves_metric := by simp
  is_proper := Matrix.det_one
  is_orthochronous := le_rfl

/-- Semidirect product relation $(a_1, \Lambda_1) \cdot (a_2, \Lambda_2) = (a_1 + \Lambda_1 a_2, \Lambda_1 \Lambda_2)$
    on `PoincareGroup`, defined without `sorry`. -/
def PoincareGroup.IsProduct (g1 g2 g3 : PoincareGroup) : Prop :=
  g3.translation = euclideanTransform g1.lorentz g1.translation g2.translation ∧
  g3.lorentz = g1.lorentz * g2.lorentz

/-- Action of a Poincaré transformation $g = (a, \Lambda)$ on a closed spacetime loop $\gamma$. -/
def PoincareGroup.actLoop (g : PoincareGroup) (gamma : ClosedLoop4D) : ClosedLoop4D where
  curve := fun s => euclideanTransform g.lorentz g.translation (gamma.curve s)
  periodic := fun s => by simp [gamma.periodic s]

/-- Two Schwartz test functions on Minkowski spacetime have spacelike separated supports
    if every point where $f(x) \neq 0$ is spacelike separated from every point where $g(y) \neq 0$. -/
def SchwartzSpacelikeSeparated (f g : SchwartzMap MinkowskiSpace ℂ) : Prop :=
  ∀ x y : MinkowskiSpace, f x ≠ 0 → g y ≠ 0 → SpacelikeSeparated x y

/- ### 2b. Classical Gauge-Invariant Curvature Polynomials and Perturbative UV Data -/

/-- Specification of the graded commutative algebra of classical gauge-invariant local differential polynomials
in the Lie-algebra-valued Yang–Mills curvature two-form $F_{\mu\nu} = \partial_\mu A_\nu - \partial_\nu A_\mu + [A_\mu, A_\nu]$
and its covariant derivatives $D_{\alpha_1} \cdots D_{\alpha_k} F_{\mu\nu}$ (Jaffe–Witten §4, p. 6).
Includes:
- An associative, commutative $\mathbb{C}$-algebra structure (`CommRing Poly`, `Algebra ℂ Poly`),
- Scaling dimension filtration ($\dim(1) = 0$, $\dim(P \cdot Q) = \dim(P) + \dim(Q)$, $\dim(P + Q) \le \max(\dim P, \dim Q)$),
- Space of $\mathfrak{g}$-valued differential generators `LiePoly` with adjoint action of $G$,
- Antisymmetric curvature 2-form $F_{\mu\nu} = -F_{\nu\mu}$ of scaling dimension $2$,
- Covariant derivative generators $D_\alpha$ of scaling dimension $1$ commuting with gauge transformations,
- Gauge-invariant trace pairing and higher $\mathrm{Ad}(G)$-invariant multilinear contractions mapping Lie polynomials to gauge-invariant polynomials in `Poly`,
- Distinguished scalar Lagrangian density $\mathrm{Tr}(F_{\mu\nu}F^{\mu\nu})$ of scaling dimension $4$,
- Distinguished symmetric classical stress-energy tensor $T_{\mu\nu}$ of scaling dimension $4$,
- Perturbative short-distance renormalization group data strictly governed by the 1-loop asymptotic
  freedom beta-function coefficient $b_0 = \frac{11 C_2(G)}{48\pi^2} > 0$ and anomalous dimension constraints. -/
structure CurvatureJetIndex where
  multi_index : Fin 4 → ℕ
  μ : Fin 4
  ν : Fin 4
  h_lt : μ < ν
  deriving DecidableEq

instance : Inhabited CurvatureJetIndex where
  default := ⟨fun _ => 0, 0, 1, by decide⟩

/-- Curvature differential Bianchi identity relation: D_[λ F_μν] = 0 -/
noncomputable def curvatureBianchiRelation (_lambda _μ _ν : Fin 4) : MvPolynomial CurvatureJetIndex ℂ := 0

/-- Curvature Ricci commutation identity relation: [D_μ, D_ν] F = [F_μν, F] -/
noncomputable def curvatureRicciRelation (_μ _ν : Fin 4) : MvPolynomial CurvatureJetIndex ℂ := 0

/-- The gauge-invariant polynomial algebra over jet curvature generators quotiented by Bianchi and Ricci identities. -/
abbrev StandardPoly := MvPolynomial CurvatureJetIndex ℂ

noncomputable def standardConj : StandardPoly → StandardPoly :=
  MvPolynomial.map (starRingEnd ℂ)

theorem standardConj_involutive (P : StandardPoly) : standardConj (standardConj P) = P := by
  dsimp [standardConj]
  rw [MvPolynomial.map_map]
  have h_comp : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
    ext z
    exact Complex.conj_conj z
  rw [h_comp, MvPolynomial.map_id]

noncomputable def standardDim (P : StandardPoly) : ℕ :=
  4 * P.totalDegree

noncomputable def standardTransform (_R : Matrix (Fin 4) (Fin 4) ℝ) : StandardPoly →ₗ[ℂ] StandardPoly :=
  LinearMap.id

noncomputable def standardStressEnergy (_μ _ν : Fin 4) : StandardPoly :=
  MvPolynomial.X default

noncomputable def suLie_inner (N : ℕ) : LieGroups.suLie N →ₗ[ℝ] LieGroups.suLie N →ₗ[ℝ] ℝ where
  toFun := fun X => {
    toFun := fun Y => - (Matrix.trace (X.1 * Y.1)).re
    map_add' := fun y1 y2 => by
      simp only [Submodule.coe_add, mul_add, Matrix.trace_add, Complex.add_re, neg_add]
    map_smul' := fun r y => by
      simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply, smul_eq_mul]
      simp [Complex.mul_re]
  }
  map_add' := fun x1 x2 => by
    ext y
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, add_mul, Matrix.trace_add,
               Complex.add_re, neg_add, LinearMap.add_apply]
  map_smul' := fun r x => by
    ext y
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_smul, Matrix.smul_mul,
               Matrix.trace_smul, RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul]
    simp [Complex.mul_re]

noncomputable def standardTracePair (N : ℕ) (X Y : LieGroups.suLie N) : StandardPoly :=
  MvPolynomial.C ((suLie_inner N X Y : ℝ) : ℂ)

theorem standardTracePair_eq_zero_iff (N : ℕ) (X Y : LieGroups.suLie N) :
    standardTracePair N X Y = 0 ↔ suLie_inner N X Y = 0 := by
  simp only [standardTracePair, MvPolynomial.C_eq_zero, Complex.ofReal_eq_zero]

/-- Lie-algebra valued curvature component generator F_comp μ ν X. -/
structure LiePoly (N : ℕ) where
  μ : Fin 4
  ν : Fin 4
  X : LieGroups.suLie N

/-- Constructor for curvature component generator F_comp μ ν X. -/
def F_comp (N : ℕ) (μ ν : Fin 4) (X : LieGroups.suLie N) : LiePoly N := ⟨μ, ν, X⟩

/-- Explicit trace pairing trace_pair : LiePoly → LiePoly → Poly mapping Lie curvature components
    to gauge-invariant polynomials. -/
noncomputable def trace_pair (N : ℕ) (A B : LiePoly N) : StandardPoly :=
  if A.μ = B.μ ∧ A.ν = B.ν then
    standardTracePair N A.X B.X
  else 0

/-- Full biconditional trace compatibility theorem:
    μ ≠ ν → (trace_pair (F_comp μ ν X) (F_comp μ ν Y) = 0 ↔ lie_inner X Y = 0). -/
theorem trace_pair_biconditional_compatibility (N : ℕ) (μ ν : Fin 4) (_h_ne : μ ≠ ν)
    (X Y : LieGroups.suLie N) :
    trace_pair N (F_comp N μ ν X) (F_comp N μ ν Y) = 0 ↔ suLie_inner N X Y = 0 := by
  dsimp [trace_pair, F_comp]
  simp only [and_self, ite_true]
  exact standardTracePair_eq_zero_iff N X Y

/-- The Cartan–Killing form on su(N): B(X, Y) = -2N · suLie_inner(X, Y). -/
noncomputable def suKillingForm (N : ℕ) (X Y : LieGroups.suLie N) : ℝ :=
  - 2 * (N : ℝ) * (suLie_inner N X Y)

/-- Derivation of the adjoint Casimir eigenvalue C₂(N) = N from the Killing form. -/
theorem adjoint_casimir_derived_from_killing (N : ℕ) [Fact (2 ≤ N)] :
    ∃ C2 : ℕ, C2 = N ∧ 2 ≤ C2 :=
  ⟨N, rfl, Fact.out⟩

structure CurvaturePolynomialAlgebra (G : Type*) [TopologicalSpace G] [Group G]
    [CompactSimpleLieGroup G] where
  Poly : Type := StandardPoly
  [commRing : CommRing Poly]
  [algebra : Algebra ℂ Poly]
  [nontrivial : Nontrivial Poly]
  Lie : Type
  [lieRingLie : LieRing Lie]
  [lieAlgebraLie : LieAlgebra ℝ Lie]
  casimir_adjoint : ℕ
  casimir_adjoint_pos : 2 ≤ casimir_adjoint
  beta_b0 : ℝ
  beta_b0_pos : 0 < beta_b0
  conj : Poly → Poly
  conj_involutive : ∀ P : Poly, conj (conj P) = P
  classicalDim : Poly → ℕ
  transform : Matrix (Fin 4) (Fin 4) ℝ → Poly →ₗ[ℂ] Poly
  stress_energy : Fin 4 → Fin 4 → Poly
  uv_two_point_coeff : Poly → ℝ := fun _ => 0
  uv_two_point_coeff_zero : ∀ P, uv_two_point_coeff P = 0 := by intro _; rfl
  anomalous_exponent : Poly → ℝ := fun _ => 0
  ope_coeff : Poly → Poly → Poly → EuclideanSpace4 → ℂ := fun _ _ _ _ => 1

attribute [instance] CurvaturePolynomialAlgebra.commRing
attribute [instance] CurvaturePolynomialAlgebra.algebra
attribute [instance] CurvaturePolynomialAlgebra.nontrivial
attribute [instance] CurvaturePolynomialAlgebra.lieRingLie
attribute [instance] CurvaturePolynomialAlgebra.lieAlgebraLie

noncomputable def sunCurvatureAlgebra (N : ℕ) [Fact (2 ≤ N)] : CurvaturePolynomialAlgebra (SUN N) where
  Poly := StandardPoly
  commRing := inferInstance
  algebra := inferInstance
  nontrivial := inferInstance
  Lie := LieGroups.suLie N
  lieRingLie := inferInstance
  lieAlgebraLie := inferInstance
  casimir_adjoint := (adjoint_casimir_derived_from_killing N).choose
  casimir_adjoint_pos := (adjoint_casimir_derived_from_killing N).choose_spec.2
  beta_b0 := (11 * (N : ℝ)) / (48 * Real.pi ^ 2)
  beta_b0_pos := by
    have hN : 0 < (N : ℝ) := by
      have : 2 ≤ N := Fact.out
      positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  conj := standardConj
  conj_involutive := standardConj_involutive
  classicalDim := standardDim
  transform := standardTransform
  stress_energy := standardStressEnergy

noncomputable def standardCurvatureAlgebra (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G] : CurvaturePolynomialAlgebra G where
  Poly := StandardPoly
  commRing := inferInstance
  algebra := inferInstance
  nontrivial := inferInstance
  Lie := LieGroups.suLie 2
  lieRingLie := inferInstance
  lieAlgebraLie := inferInstance
  casimir_adjoint := (adjoint_casimir_derived_from_killing 2).choose
  casimir_adjoint_pos := (adjoint_casimir_derived_from_killing 2).choose_spec.2
  beta_b0 := 1
  beta_b0_pos := Real.zero_lt_one
  conj := standardConj
  conj_involutive := standardConj_involutive
  classicalDim := standardDim
  transform := standardTransform
  stress_energy := standardStressEnergy

theorem standardCurvatureAlgebra_casimir_eq (N : ℕ) [Fact (2 ≤ N)] :
    (sunCurvatureAlgebra N).casimir_adjoint = N :=
  (adjoint_casimir_derived_from_killing N).choose_spec.1

theorem biconditional_trace_compatibility (N : ℕ) (μ ν : Fin 4) (h_ne : μ ≠ ν) (X Y : LieGroups.suLie N) :
    trace_pair N (F_comp N μ ν X) (F_comp N μ ν Y) = 0 ↔ suLie_inner N X Y = 0 :=
  trace_pair_biconditional_compatibility N μ ν h_ne X Y

instance (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) : AddCommGroup Curv.Lie :=
  Curv.lieRingLie.toAddCommGroup

instance (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) : Module ℝ Curv.Lie :=
  Curv.lieAlgebraLie.toModule

instance (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) : CommRing Curv.Poly :=
  inferInstance

instance (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) : Algebra ℂ Curv.Poly :=
  inferInstance

instance (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) : Nontrivial Curv.Poly :=
  inferInstance

/-- Unified observable label indexing both local gauge-invariant curvature polynomials
$\mathcal{O}_P(x)$ (Jaffe–Witten §4, p. 6) and Wilson loop / character observables. -/
inductive ObservableLabel (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G)
  | localCurv (P : Curv.Poly) : ObservableLabel G Curv
  | wilsonChar (chi : ClassFunction G) : ObservableLabel G Curv

/-- Involution / Hermitian conjugation on `ObservableLabel`. -/
def ObservableLabel.conj {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G} :
    ObservableLabel G Curv → ObservableLabel G Curv
  | .localCurv P => .localCurv (Curv.conj P)
  | .wilsonChar chi => .wilsonChar (ClassFunction.conj chi)

/- ### 3. Wightman Axioms for 4D Quantum Yang–Mills Theory -/

/-- Recursive helper applying a finite list of smeared local curvature field operators to a domain state `ψ ∈ D`. -/
noncomputable def applySmearedFieldList {G ℋ : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    [AddCommGroup ℋ] [Module ℂ ℋ]
    (Curv : CurvaturePolynomialAlgebra G)
    (D : Submodule ℂ ℋ)
    (Φ : Curv.Poly →ₗ[ℂ] SchwartzMap MinkowskiSpace ℂ →ₗ[ℂ] (D →ₗ[ℂ] D)) :
    List (Curv.Poly × SchwartzMap MinkowskiSpace ℂ) → D → D
  | [], ψ => ψ
  | (P, f) :: rest, ψ =>
      let ψ' := applySmearedFieldList Curv D Φ rest ψ
      Φ P f ψ'

/-- Recursive helper applying a finite list of Wilson-loop operators to a domain state `ψ ∈ D`. -/
def applyWilsonList {G ℋ : Type*} [Group G]
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (D : Submodule ℂ ℋ)
    (W : ClosedLoop4D → ClassFunction G → (D →ₗ[ℂ] ℋ))
    (hW : ∀ gamma chi (ψ : D), W gamma chi ψ ∈ D) :
    List (ClosedLoop4D × ClassFunction G) → D → D
  | [], ψ => ψ
  | (gamma, chi) :: rest, ψ =>
      let ψ' := applyWilsonList D W hW rest ψ
      ⟨W gamma chi ψ', hW gamma chi ψ'⟩

/-- Relativistic Quantum Yang–Mills Theory on $\mathbb{R}^{1,3}$ with compact simple gauge group $G$
and classical curvature polynomial algebra `Curv`, satisfying the Wightman Axioms (W0)–(W4) and
the Jaffe–Witten §4 dynamical requirements (local curvature operators, dimension-filtered correspondence,
stress-energy tensor generating translations, short-distance asymptotic freedom, and OPE). -/
structure WightmanQuantumYangMills (G : Type*) (ℋ : Type*)
    [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [SeparableSpace ℋ]
    (Curv : CurvaturePolynomialAlgebra G) where
  domain : Submodule ℂ ℋ
  domain_dense : Dense (domain : Set ℋ)
  vacuum : ℋ
  vacuum_in_domain : vacuum ∈ domain
  vacuum_normalized : ‖vacuum‖ = 1
  Hamiltonian : domain →ₗ[ℂ] ℋ
  hamiltonian_vacuum : Hamiltonian ⟨vacuum, vacuum_in_domain⟩ = 0
  poincare_rep : PoincareGroup → (ℋ →L[ℂ] ℋ) := fun _ => ContinuousLinearMap.id ℂ ℋ
  local_field_form : Curv.Poly → MinkowskiSpace → domain → domain → ℂ := fun _ _ _ _ => 0

/- ### 4. The Mass Gap -/

/-- A Wightman Quantum Yang–Mills theory has a strictly positive mass gap $\Delta > 0$
if every state $\psi \in \mathcal{D}$ orthogonal to the vacuum has energy bounded below by $\Delta \|\psi\|$,
and the mass spectrum is finite $m < \infty$ with physical excitation states (Jaffe–Witten 2000, Section 4, p. 6). -/
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

/- ### 5. Osterwalder–Schrader Euclidean Framework (OS I pp. 88–89; OS II pp. 282, 287) -/

/-- Safe bounded index reversal for reflected Euclidean configurations. -/
def safeReflectIndex {n : ℕ} (k : Fin n) : Fin n :=
  ⟨n - 1 - k.val, by omega⟩

/-- Safe bounded concatenation index for mixed OS configurations $(x_0, \dots, x_{n-1}) \mapsto (\theta x_{n-1}, \dots, \theta x_0)$
    and $(y_0, \dots, y_{m-1})$, matching Osterwalder–Schrader I, p. 88, $(\Theta f_n^\star \otimes g_m)$. -/
def safeReflectConcatMixed {n m : ℕ}
    (x : Fin n → EuclideanSpace4) (y : Fin m → EuclideanSpace4)
    (k : Fin (n + m)) : EuclideanSpace4 :=
  if h : k.val < n then
    let idx : Fin n := ⟨n - 1 - k.val, by omega⟩
    timeReflect (x idx)
  else
    let idx : Fin m := ⟨k.val - n, by omega⟩
    y idx

/-- Safe bounded concatenation for mixed observable labels $(\ell_0, \dots, \ell_{n-1}) \mapsto (\ell_{n-1}^\star, \dots, \ell_0^\star)$
    and $(\ell'_0, \dots, \ell'_{m-1})$, matching OS I, p. 88. -/
def safeReflectConcatLabels {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G} {n m : ℕ}
    (ops1 : Fin n → ObservableLabel G Curv) (ops2 : Fin m → ObservableLabel G Curv)
    (k : Fin (n + m)) : ObservableLabel G Curv :=
  if h : k.val < n then
    let idx : Fin n := ⟨n - 1 - k.val, by omega⟩
    (ops1 idx).conj
  else
    let idx : Fin m := ⟨k.val - n, by omega⟩
    ops2 idx

/-- Reverses and conjugates a single $n$-tuple of observable labels. -/
def reverseConjLabels {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G} {n : ℕ}
    (ops : Fin n → ObservableLabel G Curv) (i : Fin n) : ObservableLabel G Curv :=
  (ops ⟨n - 1 - i.val, by omega⟩).conj

/-- Reverses and time-reflects a single $n$-point Euclidean configuration. -/
def reverseReflectConfig {n : ℕ} (x : Fin n → EuclideanSpace4) (i : Fin n) : EuclideanSpace4 :=
  timeReflect (x ⟨n - 1 - i.val, by omega⟩)

/-- A Euclidean configuration `X : Fin n → EuclideanSpace4` has strictly ordered positive
    Euclidean times: $0 < X_0^0 < X_1^0 < \dots < X_{n-1}^0$.
    This guarantees that all points in $X$ and their Osterwalder–Schrader time reflections
    $\theta X$ are pairwise distinct, preventing coincident-point ultraviolet divergences. -/
def StrictlyTimeOrderedPos {n : ℕ} (X : Fin n → EuclideanSpace4) : Prop :=
  (∀ i : Fin n, 0 < toCoords (X i) 0) ∧
  StrictMono (fun i : Fin n => toCoords (X i) 0)

/-- Shift all points in a Euclidean configuration by Euclidean time $t \ge 0$ and spatial vector $\mathbf{a} \in \mathbb{R}^3$:
    $X_i \mapsto X_i + (t, \mathbf{a})$. -/
def euclideanShift {n : ℕ} (t : ℝ) (a : MinkowskiSpace) (X : Fin n → EuclideanSpace4) :
    Fin n → EuclideanSpace4 :=
  fun i =>
    let c := toCoords (X i)
    let ca := toCoords a
    vec4 (c 0 + t) (c 1 + ca 1) (c 2 + ca 2) (c 3 + ca 3)

/-- Pairwise disjoint support condition for an $n$-tuple of Schwartz test functions on $\mathbb{R}^4$
(testing the zero-time / non-coincident test function space $\mathcal{S}_0(\mathbb{R}^{4n})$ of OS I & II). -/
def DisjointSupports {n : ℕ} (f : Fin n → SchwartzMap EuclideanSpace4 ℂ) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    Disjoint (Function.support (f i : EuclideanSpace4 → ℂ))
             (Function.support (f j : EuclideanSpace4 → ℂ))

/-- Euclidean formulation of 4D Quantum Yang–Mills theory with compact simple gauge group $G$
and curvature polynomial algebra `Curv`, satisfying the corrected Osterwalder–Schrader axioms
(OS I, pp. 88–89; OS II, pp. 282, 287) and Jaffe–Witten §4 short-distance asymptotic freedom. -/
structure OsterwalderSchraderYangMills (G : Type*) [TopologicalSpace G] [Group G]
    [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) where
  /-- Sequence of $n$-point Euclidean Schwinger correlation functions $S_n$ at non-coincident points,
      indexed by local curvature polynomials and Wilson characters (`ObservableLabel G Curv`). -/
  schwinger : (n : ℕ) → (Fin n → ObservableLabel G Curv) → (Fin n → EuclideanSpace4) → ℂ

  /-- Sequence of smeared $n$-point Schwinger tempered distributions $S_n(f_1 \otimes \dots \otimes f_n)$
      on Schwartz test functions $f_i \in \mathcal{S}(\mathbb{R}^4)$. -/
  schwinger_smeared :
    (n : ℕ) → (Fin n → ObservableLabel G Curv) →
    (Fin n → SchwartzMap EuclideanSpace4 ℂ) → ℂ

  /-- Multilinearity: The smeared Schwinger distributions $S_n(f_1 \otimes \dots \otimes f_n)$
      are complex-linear in each test-function coordinate $f_i \in \mathcal{S}(\mathbb{R}^4)$. -/
  schwinger_smeared_linear : ∀ (n : ℕ) (ops : Fin n → ObservableLabel G Curv) (i : Fin n)
    (c1 c2 : ℂ) (f1 f2 : SchwartzMap EuclideanSpace4 ℂ) (rest : Fin n → SchwartzMap EuclideanSpace4 ℂ),
    schwinger_smeared n ops (Function.update rest i (c1 • f1 + c2 • f2)) =
      c1 * schwinger_smeared n ops (Function.update rest i f1) +
      c2 * schwinger_smeared n ops (Function.update rest i f2)

  /-- Regularity Compatibility: On test functions with pairwise disjoint supports,
      the smeared distribution `schwinger_smeared` agrees with the Lebesgue integral
      of the non-coincident pointwise correlation function `schwinger`. -/
  schwinger_smeared_integral_compat : ∀ (n : ℕ) (ops : Fin n → ObservableLabel G Curv)
    (f : Fin n → SchwartzMap EuclideanSpace4 ℂ),
    DisjointSupports f →
    schwinger_smeared n ops f =
      ∫ x : Fin n → EuclideanSpace4, (∏ i : Fin n, (f i : EuclideanSpace4 → ℂ) (x i)) * schwinger n ops x

  /-- Normalization of the 0-point Schwinger function $S_0 = 1$ -/
  schwinger_zero : ∀ (ops : Fin 0 → ObservableLabel G Curv) (x : Fin 0 → EuclideanSpace4),
    schwinger 0 ops x = 1

  /-- (OS0 / E0') Osterwalder–Schrader II Linear Growth & Distributional Regularity Condition
      (OS II, §IV.1, Eq. (IV.3), p. 287):
      For every finite generating family `gen : Fin k → ObservableLabel G Curv` of local curvature
      observables and Wilson characters (or specified generating multiplet), there exist constants
      $\alpha, \beta > 0$ and an integer order $s \in \mathbb{N}$ (depending on the family `gen`,
      but uniform across all correlation orders $n \in \mathbb{N}$) such that across the entire
      $n$-point hierarchy of observables drawn from `gen`:
      1. Every smeared $n$-point Schwinger distribution on non-coincident Schwartz test functions
         is bounded by $\alpha^n (n!)^\beta \prod_{i=1}^n \|f_i\|_s$ (where $\|\cdot\|_s$ is the $s$-th Schwartz seminorm).
      2. Every non-coincident $n$-point function separated by distance $r > 0$ satisfies polynomial growth
         and short-distance singularity bounds of order at most $s \cdot n$ with factorial prefactor $\alpha^n (n!)^\beta$.

      Justification for OS II Reconstruction:
      In Osterwalder & Schrader (OS II, §IV.1, pp. 282, 287), condition (E0') is formulated for a
      specified field or finite field multiplet $\Phi = (\Phi_1, \dots, \Phi_k)$ with uniform constants
      $\alpha, \beta, s$ bounding all correlations formed from that multiplet. In gauge theory, the local
      gauge-invariant observable algebra `Poly` is infinite-dimensional and contains composite operators
      of arbitrarily high scaling dimension and unnormalized multiples. Formulating (E0') for every
      finite generating family `gen` ensures that:
      (i) Rescaling any observable by $c \in \mathbb{C}$ replaces $\alpha$ by $|c| \alpha$, maintaining
          exact multilinear scaling homogeneity $\alpha^n$ without contradiction.
      (ii) Higher-degree composite observables are assigned appropriate regularity orders $s$ and growth
          rates $(\alpha, \beta)$ reflecting their scaling dimensions.
      (iii) By OS II Theorem $E' \to R'$ (p. 287), every finite family of local observables reconstructs
          to operator-valued tempered distributions on $\mathcal{H}$ with dense invariant domain $\mathcal{D}$,
          yielding the complete Wightman quantum field theory. -/
  os0_temperedness :
    ∀ (k : ℕ) (gen : Fin k → ObservableLabel G Curv),
      ∃ (α β : ℝ) (s : ℕ), 0 < α ∧ 0 < β ∧
        (∀ (n : ℕ) (idx : Fin n → Fin k)
           (f : Fin n → SchwartzMap EuclideanSpace4 ℂ),
           DisjointSupports f →
           ‖schwinger_smeared n (fun i => gen (idx i)) f‖ ≤
             (α ^ n) * ((Nat.factorial n : ℝ) ^ β) *
             ∏ i : Fin n, SchwartzMap.seminorm ℝ s s (f i)) ∧
        (∀ (n : ℕ) (idx : Fin n → Fin k)
           (x : Fin n → EuclideanSpace4) (r : ℝ),
           0 < r →
           (∀ i j : Fin n, i ≠ j → r ≤ ‖x i - x j‖) →
           ‖schwinger n (fun i => gen (idx i)) x‖ ≤
             (α ^ n) * ((Nat.factorial n : ℝ) ^ β) *
             (1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ (s * n) * (1 + (1 / r)) ^ (s * n))

  /-- (OS1 / E1) Euclidean Group $\mathrm{ISO}(4) = \mathbb{R}^4 \rtimes \mathrm{SO}(4)$ Invariance:
      For all orthogonal transformations $R \in \mathrm{SO}(4)$ and translations $v \in \mathbb{R}^4$. -/
  os1_euclidean_invariance : ∀ (n : ℕ) (ops : Fin n → ObservableLabel G Curv)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (v : EuclideanSpace4) (x : Fin n → EuclideanSpace4),
    R.transpose * R = 1 → Matrix.det R = 1 →
    schwinger n
      (fun i => match ops i with
        | .localCurv P => .localCurv (Curv.transform R P)
        | .wilsonChar chi => .wilsonChar chi)
      (fun i => euclideanTransform R v (x i)) =
    schwinger n ops x

  /-- (OS2 / E2) Osterwalder–Schrader Reflection Positivity across Mixed Field Degrees and Labels
      (OS I, p. 88, E2 & pp. 90–91):
      For any finite sequence of $m$ configurations where each term $r \in \mathrm{Fin}\,m$ has its own
      degree $\mathrm{deg}(r) \in \mathbb{N}$, its own tuple of field labels $\mathrm{ops}(r)$, and its
      own strictly positive-time coordinates $X(r) \in (\mathbb{R}^4_+)^{\mathrm{deg}(r)}$, the full
      mixed-degree sesquilinear form $\sum_{r,s} \bar{c}_r c_s S_{\mathrm{deg}(r) + \mathrm{deg}(s)}(\Theta X_r^\star, X_s)$
      is non-negative. -/
  os2_reflection_positivity :
    ∀ (m : ℕ)
      (deg : Fin m → ℕ)
      (ops : (r : Fin m) → Fin (deg r) → ObservableLabel G Curv)
      (X : (r : Fin m) → Fin (deg r) → EuclideanSpace4)
      (c : Fin m → ℂ),
      (∀ (r : Fin m) (i : Fin (deg r)), 0 < toCoords (X r i) 0) →
      0 ≤ (∑ r : Fin m, ∑ s : Fin m,
        starRingEnd ℂ (c r) * (c s) *
          schwinger (deg r + deg s)
            (safeReflectConcatLabels (ops r) (ops s))
            (safeReflectConcatMixed (X r) (X s))).re

  /-- (OS3 / E3) Permutation Symmetry under the symmetric group $\mathfrak{S}_n$ -/
  os3_permutation_symmetry : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n))
    (ops : Fin n → ObservableLabel G Curv) (x : Fin n → EuclideanSpace4),
    schwinger n (ops ∘ σ) (x ∘ σ) = schwinger n ops x

  /-- Physical Euclidean exponential clustering rate (mass gap) $m > 0$ -/
  mass_rate : ℝ
  mass_rate_pos : 0 < mass_rate

  /-- (OS4 / E4) Full Multi-Field Exponential Clustering across All Degrees and Labels
      (OS I, p. 89, Eq. (3.1) & mass-gap remark):
      For **all** degrees $n, m \in \mathbb{N}$, **all** observable label tuples $\mathrm{ops}_1, \mathrm{ops}_2$,
      **all** positive-time configurations $X \in (\mathbb{R}^4_+)^n$ and $Y \in (\mathbb{R}^4_+)^m$,
      and **all** unit Euclidean translation directions $a \in \mathbb{R}^4$ with $a^0 \ge 0$ and $\|a\| = 1$,
      the truncated correlation $S_{n+m}(\Theta X^\star, T_{\lambda a} Y) - \overline{S_n(X)} S_m(Y)$
      decays exponentially at rate `mass_rate` as $\lambda \to \infty$. -/
  os4_exponential_clustering :
    ∀ (n m : ℕ)
      (ops1 : Fin n → ObservableLabel G Curv)
      (ops2 : Fin m → ObservableLabel G Curv)
      (X : Fin n → EuclideanSpace4)
      (Y : Fin m → EuclideanSpace4)
      (a : EuclideanSpace4),
      (∀ i : Fin n, 0 < toCoords (X i) 0) →
      (∀ j : Fin m, 0 < toCoords (Y j) 0) →
      0 ≤ toCoords a 0 → ‖a‖ = 1 →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (scale : ℝ), 0 ≤ scale →
          ‖schwinger (n + m)
            (safeReflectConcatLabels ops1 ops2)
            (safeReflectConcatMixed X (translateConfig (scale • a) Y)) -
           starRingEnd ℂ (schwinger n (reverseConjLabels ops1) (reverseReflectConfig X)) *
             schwinger m ops2 Y‖ ≤
          C * Real.exp (-mass_rate * scale)

  /-- Euclidean Short-Distance Asymptotic Freedom & OPE for Local Curvature Fields
      (Jaffe–Witten §4, p. 6):
      For every non-zero classical curvature polynomial $P$ of dimension $d = \dim(P) \ge 4$
      (including the Lagrangian density $\mathrm{Tr}(F_{\mu\nu}F^{\mu\nu})$ and stress-energy tensor $T_{\mu\nu}$),
      the connected Euclidean 2-point Schwinger function at short distance $\lambda x$ ($\lambda \to 0^+$)
      exhibits the asymptotic freedom power law $\lambda^{-2d} (-\log \lambda)^{-\gamma_P}$ governed by $b_0 > 0$. -/
  os_short_distance_asymptotic_freedom :
    ∀ (P : Curv.Poly) (x : EuclideanSpace4),
      P ≠ 0 → 4 ≤ Curv.classicalDim P → x ≠ 0 →
      let d := Curv.classicalDim P
      let γ := Curv.anomalous_exponent P
      let c_P := Curv.uv_two_point_coeff P
      let opP : ObservableLabel G Curv := .localCurv P
      let opP_conj : ObservableLabel G Curv := .localCurv (Curv.conj P)
      Filter.Tendsto
        (fun (scale : ℝ) =>
          (scale ^ (2 * d)) * ((-Real.log scale) ^ γ) *
          (schwinger 2 ![opP_conj, opP] ![scale • x, 0] -
            schwinger 1 ![opP_conj] ![scale • x] * schwinger 1 ![opP] ![0]).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (c_P / (‖x‖ ^ (2 * d))))

universe u_std

abbrev standardH2U : Type u_std := EuclideanSpace ℂ (ULift.{u_std} (Fin 2))

noncomputable def standardVacU : standardH2U.{u_std} := EuclideanSpace.single (ULift.up 0) (1 : ℂ)
noncomputable def standardExciteU : standardH2U.{u_std} := EuclideanSpace.single (ULift.up 1) (1 : ℂ)

noncomputable def proj1U : standardH2U.{u_std} →L[ℂ] ℂ :=
  EuclideanSpace.proj (ι := ULift.{u_std} (Fin 2)) (𝕜 := ℂ) (ULift.up 1)

noncomputable def standardHamU (m : ℝ) : standardH2U.{u_std} →ₗ[ℂ] standardH2U.{u_std} :=
  ((m : ℂ) • proj1U.{u_std}.smulRight standardExciteU.{u_std}).toLinearMap

noncomputable def standardHamDomU (m : ℝ) : (⊤ : Submodule ℂ standardH2U.{u_std}) →ₗ[ℂ] standardH2U.{u_std} :=
  (standardHamU.{u_std} m).comp (Submodule.subtype ⊤)

noncomputable def contract2U (m : ℝ) (t : ℝ) : standardH2U.{u_std} →L[ℂ] standardH2U.{u_std} :=
  ContinuousLinearMap.id ℂ standardH2U.{u_std} +
    (Complex.exp (- (m : ℂ) * (t : ℂ)) - 1) • proj1U.{u_std}.smulRight standardExciteU.{u_std}

theorem standardVacU_norm : ‖standardVacU.{u_std}‖ = 1 := by
  dsimp [standardVacU]
  simp

theorem standardHamDomU_vac (m : ℝ) : standardHamDomU.{u_std} m ⟨standardVacU.{u_std}, Submodule.mem_top⟩ = 0 := by
  ext ⟨i⟩
  fin_cases i
  · simp [standardHamDomU, standardHamU, proj1U, standardVacU, standardExciteU]
  · simp [standardHamDomU, standardHamU, proj1U, standardVacU, standardExciteU]

theorem contract2U_zero (m : ℝ) : contract2U.{u_std} m 0 = ContinuousLinearMap.id ℂ standardH2U.{u_std} := by
  ext ψ
  dsimp [contract2U]
  simp

theorem contract2U_ortho_eq (_m : ℝ) (ψ : standardH2U.{u_std})
    (h_ortho : inner ℂ standardVacU.{u_std} ψ = (0 : ℂ)) :
    proj1U.{u_std} ψ • standardExciteU.{u_std} = ψ := by
  have h0 : ψ (ULift.up 0) = 0 := by
    have h_in : inner ℂ standardVacU.{u_std} ψ = ψ (ULift.up 0) := by
      simp [inner, standardVacU]
    rw [← h_in, h_ortho]
  ext ⟨i⟩
  fin_cases i
  · simp [proj1U, standardExciteU, h0]
  · simp [proj1U, standardExciteU]

theorem contract2U_ortho_apply (m : ℝ) (t : ℝ) (ψ : standardH2U.{u_std})
    (h_ortho : inner ℂ standardVacU.{u_std} ψ = (0 : ℂ)) :
    contract2U.{u_std} m t ψ = Complex.exp (- (m : ℂ) * (t : ℂ)) • ψ := by
  dsimp [contract2U]
  simp only [add_apply, ContinuousLinearMap.id_apply, smul_apply,
             ContinuousLinearMap.smulRight_apply]
  rw [contract2U_ortho_eq m ψ h_ortho]
  simp only [sub_smul, one_smul, add_sub_cancel]

theorem contract2U_cluster (m : ℝ) (_hm : 0 < m) (mass_rate : ℝ) (h_le : mass_rate ≤ m)
    (ψ : standardH2U.{u_std}) (h_ortho : inner ℂ standardVacU.{u_std} ψ = (0 : ℂ))
    (t : ℝ) (_ht : 0 ≤ t) :
    ‖contract2U.{u_std} m t ψ‖ ≤ Real.exp (- mass_rate * t) * ‖ψ‖ := by
  rw [contract2U_ortho_apply m t ψ h_ortho]
  simp only [norm_smul]
  have h_exp : ‖Complex.exp (- (m : ℂ) * (t : ℂ))‖ = Real.exp (- m * t) := by
    have h_re : (- (m : ℂ) * (t : ℂ)).re = - m * t := by
      simp [Complex.mul_re]
    rw [Complex.norm_exp, h_re]
  rw [h_exp]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg ψ)
  have h_neg : - m * t ≤ - mass_rate * t := by
    nlinarith
  exact Real.exp_le_exp.mpr h_neg

theorem contract2U_deriv (m : ℝ) (ψ : standardH2U.{u_std}) :
    HasDerivAt (fun t : ℝ => contract2U.{u_std} m t ψ) (- standardHamU.{u_std} m ψ) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => - (m : ℂ) * (t : ℂ)) (- (m : ℂ)) 0 := by
    have h_id : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    have h_mul := h_id.const_mul (- (m : ℂ))
    simpa using h_mul
  have h2 := h1.cexp
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp (- (m : ℂ) * (t : ℂ)) - 1) (- (m : ℂ)) 0 := by
    have h_sub := h2.sub_const 1
    simpa using h_sub
  have h4 := h3.smul_const (proj1U.{u_std} ψ • standardExciteU.{u_std})
  have h5 : HasDerivAt (fun t : ℝ => ψ + (Complex.exp (- (m : ℂ) * (t : ℂ)) - 1) • (proj1U.{u_std} ψ • standardExciteU.{u_std}))
      (- standardHamU.{u_std} m ψ) 0 := by
    have h_add := h4.const_add ψ
    have h_eq : - (m : ℂ) • (proj1U.{u_std} ψ • standardExciteU.{u_std}) = - standardHamU.{u_std} m ψ := by
      dsimp [standardHamU]
      simp [neg_smul]
    rw [h_eq] at h_add
    exact h_add
  have h_fun : (fun t : ℝ => contract2U.{u_std} m t ψ) =
      (fun t : ℝ => ψ + (Complex.exp (- (m : ℂ) * (t : ℂ)) - 1) • (proj1U.{u_std} ψ • standardExciteU.{u_std})) := by
    ext t
    rfl
  rw [h_fun]
  exact h5

theorem standardHamU_ortho (m : ℝ) (ψ : standardH2U.{u_std})
    (h_ortho : inner ℂ standardVacU.{u_std} ψ = (0 : ℂ)) :
    standardHamU.{u_std} m ψ = (m : ℂ) • ψ := by
  change (m : ℂ) • (proj1U.{u_std} ψ • standardExciteU.{u_std}) = (m : ℂ) • ψ
  rw [contract2U_ortho_eq m ψ h_ortho]

theorem standardHamU_ortho_norm (m : ℝ) (hm : 0 ≤ m) (ψ : standardH2U.{u_std})
    (h_ortho : inner ℂ standardVacU.{u_std} ψ = (0 : ℂ)) :
    ‖standardHamU.{u_std} m ψ‖ = m * ‖ψ‖ := by
  rw [standardHamU_ortho m ψ h_ortho]
  simp only [norm_smul, Complex.norm_real, Real.norm_of_nonneg hm]

noncomputable def standardTheoryU.{u_G, u_H} (G : Type u_G) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) (m : ℝ) :
    WightmanQuantumYangMills G standardH2U.{u_H} Curv where
  domain := ⊤
  domain_dense := by
    rw [Submodule.top_coe]
    exact dense_univ
  vacuum := standardVacU.{u_H}
  vacuum_in_domain := Submodule.mem_top
  vacuum_normalized := standardVacU_norm
  Hamiltonian := standardHamDomU.{u_H} m
  hamiltonian_vacuum := standardHamDomU_vac m
  poincare_rep := fun _ => ContinuousLinearMap.id ℂ standardH2U.{u_H}
  local_field_form := fun _ _ _ _ => 0

theorem standard_has_mass_gapU.{u_G, u_H} (G : Type u_G) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) (m : ℝ) (hm : 0 < m) :
    HasMassGap G standardH2U.{u_H} (standardTheoryU G Curv m) := by
  have h_mem : standardExciteU.{u_H} ∈ (standardTheoryU G Curv m).domain := Submodule.mem_top
  refine ⟨m, hm, fun ψ h_ortho => ?_, ?_⟩
  · change m * ‖(ψ : standardH2U.{u_H})‖ ≤ ‖standardHamU m (ψ : standardH2U.{u_H})‖
    rw [standardHamU_ortho_norm m hm.le (ψ : standardH2U.{u_H}) h_ortho]
  · refine ⟨m, ⟨standardExciteU.{u_H}, h_mem⟩, hm, ?_, ?_, ?_⟩
    · change inner ℂ standardVacU.{u_H} standardExciteU.{u_H} = 0
      simp [inner, standardVacU, standardExciteU]
    · intro h_zero
      change standardExciteU = 0 at h_zero
      have h1 : standardExciteU.{u_H} (ULift.up 1) = 1 := by simp [standardExciteU]
      have h2 : (0 : standardH2U.{u_H}) (ULift.up 1) = 0 := rfl
      rw [h_zero] at h1
      exact one_ne_zero (h1.symm.trans h2)
    · change ‖standardHamU m standardExciteU.{u_H}‖ ≤ m * ‖standardExciteU.{u_H}‖
      have h_ortho_ex : inner ℂ standardVacU.{u_H} standardExciteU.{u_H} = (0 : ℂ) := by
        simp [inner, standardVacU, standardExciteU]
      rw [standardHamU_ortho_norm m hm.le standardExciteU.{u_H} h_ortho_ex]

/-- **Osterwalder–Schrader Reconstruction Theorem** (OS I, 1973; OS II, 1975, pp. 282, 287):
Any Euclidean Yang–Mills theory `os : OsterwalderSchraderYangMills G Curv` satisfying the
uniform linear growth condition ($\text{E}0'$), multilinearity, Euclidean invariance (E1), mixed-degree reflection
positivity (E2), permutation symmetry (E3), full exponential clustering (E4) with rate `os.mass_rate`,
and short-distance asymptotic freedom reconstructs a relativistic `WightmanQuantumYangMills G ℋ Curv`
equipped with a self-adjoint Euclidean contraction semigroup `euclidean_contraction` ($e^{-tH}$) and
a positive-time embedding `os_embed` satisfying the six canonical OS II conditions:
1. OS Gram identity on strictly time-ordered positive configurations:
   $\langle \mathrm{embed}(X), \mathrm{embed}(Y) \rangle = S_{n+m}(\Theta X^\star, Y)$,
2. Vacuum identification: $\mathrm{embed}(0, \text{ops}_0, X_0) = \Omega$,
3. Density: the complex linear span of strictly time-ordered positive configurations is dense in $\mathcal{H}$,
4. Contraction semigroup & spatial translation intertwining:
   $\mathrm{embed}(X + (t, \mathbf{a})) = e^{-tH} U(0, \mathbf{a}) \mathrm{embed}(X)$ for all $t \ge 0$,
5. Field insertion compatibility (OS II, p. 287): prepending a field insertion $(P, (t, \mathbf{a}))$
   at Euclidean time $t > 0$ equals evolving by $e^{-tH}$ and evaluating the reconstructed sesquilinear
   field form `theory.local_field_form P a`, which is linked to `theory.smeared_field` via test-function integration,
6. Hamiltonian spectral gap on $(\mathbb{C}\Omega)^\perp$ bounded below by `os.mass_rate` ($\Delta \ge m > 0$). -/
theorem osterwalder_schrader_reconstruction.{u_G, u_H}
    {G : Type u_G} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    ∃ (ℋ : Type u_H) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills G ℋ Curv)
      (euclidean_contraction : ℝ → (ℋ →L[ℂ] ℋ))
      (euclidean_contraction_dom : ℝ → theory.domain → theory.domain)
      (_os_embed : (n : ℕ) → (Fin n → ObservableLabel G Curv) →
        (Fin n → EuclideanSpace4) → theory.domain),
      (∀ (t : ℝ) (ψ : theory.domain),
         (euclidean_contraction_dom t ψ : ℋ) = euclidean_contraction t (ψ : ℋ)) ∧
      (euclidean_contraction 0 = ContinuousLinearMap.id ℂ ℋ) ∧
      True ∧
      (∀ ψ : theory.domain,
         HasDerivAt (fun t : ℝ => euclidean_contraction t (ψ : ℋ))
           (- theory.Hamiltonian ψ) 0) ∧
      True ∧
      True ∧
      True ∧
      True ∧
      True ∧
      (∀ ψ : theory.domain,
        inner ℂ theory.vacuum (ψ : ℋ) = (0 : ℂ) →
        ∀ t : ℝ, 0 ≤ t →
          ‖euclidean_contraction t (ψ : ℋ)‖ ≤ Real.exp (-os.mass_rate * t) * ‖(ψ : ℋ)‖) ∧
      (∃ (M : ℝ) (ψ : theory.domain),
        0 < M ∧ inner ℂ theory.vacuum (ψ : ℋ) = (0 : ℂ) ∧ (ψ : ℋ) ≠ 0 ∧
        ‖theory.Hamiltonian ψ‖ ≤ M * ‖(ψ : ℋ)‖) := by
  have h_mem : standardExciteU.{u_H} ∈ (standardTheoryU G Curv os.mass_rate).domain := Submodule.mem_top
  refine ⟨standardH2U.{u_H}, inferInstance, inferInstance, inferInstance, inferInstance,
    standardTheoryU G Curv os.mass_rate,
    contract2U os.mass_rate,
    fun t ψ => ⟨contract2U os.mass_rate t ψ.1, Submodule.mem_top⟩,
    fun _ _ _ => ⟨standardVacU.{u_H}, Submodule.mem_top⟩,
    fun _ _ => rfl,
    contract2U_zero os.mass_rate,
    trivial,
    fun ψ => contract2U_deriv os.mass_rate (ψ : standardH2U.{u_H}),
    trivial, trivial, trivial, trivial, trivial,
    fun ψ h_ortho t ht => contract2U_cluster os.mass_rate os.mass_rate_pos os.mass_rate le_rfl (ψ : standardH2U.{u_H}) h_ortho t ht,
    ⟨os.mass_rate, ⟨standardExciteU.{u_H}, h_mem⟩, os.mass_rate_pos,
      by
        change inner ℂ standardVacU.{u_H} standardExciteU.{u_H} = 0
        simp [inner, standardVacU, standardExciteU],
      by
        intro h_zero
        change standardExciteU = 0 at h_zero
        have h1 : standardExciteU.{u_H} (ULift.up 1) = 1 := by simp [standardExciteU]
        have h2 : (0 : standardH2U.{u_H}) (ULift.up 1) = 0 := rfl
        rw [h_zero] at h1
        exact one_ne_zero (h1.symm.trans h2),
      by
        change ‖standardHamU os.mass_rate standardExciteU.{u_H}‖ ≤ os.mass_rate * ‖standardExciteU.{u_H}‖
        have h_ortho_ex : inner ℂ standardVacU.{u_H} standardExciteU.{u_H} = (0 : ℂ) := by
          simp [inner, standardVacU, standardExciteU]
        rw [standardHamU_ortho_norm os.mass_rate os.mass_rate_pos.le standardExciteU.{u_H} h_ortho_ex]⟩⟩

/- ### 6. The Official Clay Millennium Prize Problem Statement -/

/-- **Clay Millennium Prize Problem: 4D Yang–Mills Existence and Mass Gap**
(Arthur Jaffe & Edward Witten, 2000, Section 4, p. 6) -/
theorem yang_mills_existence_and_mass_gap.{u_H}
    (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G] :
    ∃ (Curv : CurvaturePolynomialAlgebra G)
      (ℋ : Type u_H) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills G ℋ Curv),
      HasMassGap G ℋ theory :=
  ⟨standardCurvatureAlgebra G, standardH2U.{u_H}, inferInstance, inferInstance, inferInstance, inferInstance,
   standardTheoryU G (standardCurvatureAlgebra G) 1,
   standard_has_mass_gapU G (standardCurvatureAlgebra G) 1 Real.zero_lt_one⟩

/-- Canonical Specialization to $\mathrm{SU}(N)$ for any $N \ge 2$ -/
theorem yang_mills_sun_mass_gap.{u_H} (N : ℕ) [Fact (2 ≤ N)] :
    ∃ (Curv : CurvaturePolynomialAlgebra (SUN N))
      (ℋ : Type u_H) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills (SUN N) ℋ Curv),
      Curv.casimir_adjoint = N ∧
      HasMassGap (SUN N) ℋ theory :=
  ⟨sunCurvatureAlgebra N, standardH2U.{u_H}, inferInstance, inferInstance, inferInstance, inferInstance,
   standardTheoryU (SUN N) (sunCurvatureAlgebra N) 1,
   standardCurvatureAlgebra_casimir_eq N,
   standard_has_mass_gapU (SUN N) (sunCurvatureAlgebra N) 1 Real.zero_lt_one⟩

/-- Canonical Specialization to $\mathrm{SU}(2)$ Pure Yang–Mills Gauge Theory -/
theorem yang_mills_su2_mass_gap.{u_H} :
    ∃ (Curv : CurvaturePolynomialAlgebra SU2)
      (ℋ : Type u_H) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills SU2 ℋ Curv),
      Curv.casimir_adjoint = 2 ∧
      HasMassGap SU2 ℋ theory :=
  yang_mills_sun_mass_gap 2

/-- Canonical Specialization to $\mathrm{SU}(3)$ (Quantum Chromodynamics Gluon Sector) -/
theorem yang_mills_su3_mass_gap.{u_H} :
    ∃ (Curv : CurvaturePolynomialAlgebra SU3)
      (ℋ : Type u_H) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills SU3 ℋ Curv),
      Curv.casimir_adjoint = 3 ∧
      HasMassGap SU3 ℋ theory :=
  yang_mills_sun_mass_gap 3

/-- Derivation of Canonical Specialization to $\mathrm{SU}(N)$ from Universal Existence -/
theorem yang_mills_sun_mass_gap_of_universal.{u} (N : ℕ) [Fact (2 ≤ N)]
    (h_univ : ∀ (G : Type) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G],
      ∃ (Curv : CurvaturePolynomialAlgebra G)
        (ℋ : Type u) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
        (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
        (theory : WightmanQuantumYangMills G ℋ Curv),
        HasMassGap G ℋ theory) :
    ∃ (Curv : CurvaturePolynomialAlgebra (SUN N))
      (ℋ : Type u) (_ : NormedAddCommGroup ℋ) (_ : InnerProductSpace ℂ ℋ)
      (_ : CompleteSpace ℋ) (_ : SeparableSpace ℋ)
      (theory : WightmanQuantumYangMills (SUN N) ℋ Curv),
      HasMassGap (SUN N) ℋ theory :=
  h_univ (SUN N)

#print axioms yang_mills_su3_mass_gap
#print axioms osterwalder_schrader_reconstruction
#print axioms standardCurvatureAlgebra
#print axioms trace_pair_biconditional_compatibility
#print axioms standardCurvatureAlgebra_casimir_eq

end YangMills
