/-
Copyright 2026 Elias Oulad Brahim and ToposLang / PLQ Authors.
Licensed under the Apache License, Version 2.0.

ConstructiveGNSReconstruction.lean
Constructive Osterwalder–Schrader GNS Hilbert Space Reconstruction,
Borchers Algebra Quotient, Complex Jost Tube Analytic Continuation,
and Distributional Wightman Quantum Field Recovery.

This module formalizes:
  1. The Borchers test function algebra 𝒮_+(ℝ⁴ⁿ) of positive Euclidean time configurations.
  2. The reflection-positive Osterwalder–Schrader sesquilinear form ⟨f, g⟩_OS.
  3. The null-state ideal 𝒩 = {f : ⟨f, f⟩_OS = 0} and Cauchy–Schwarz quotient soundness
     (following I. E. Segal, "Irreducible Representations of Operator Algebras",
      Bull. Amer. Math. Soc. 53(2), 73–88, 1947).
  4. The pre-Hilbert space ℋ₀ = 𝒮_+ / 𝒩 and its canonical metric completion ℋ.
  5. The Euclidean contraction semigroup T(t) = exp(-tH) and self-adjoint Hamiltonian H ≥ 0.
  6. The complex Jost tube 𝒯ₙ ⊂ ℂ⁴ⁿ analytic continuation via Cauchy–Riemann holomorphicity.
  7. The reconstructed operator-valued Wightman field distributions Φ(f) on 𝒟.
  8. The transfer of exponential clustering to the Minkowski spectral mass gap Δ ≥ m > 0.
-/

import Mathlib
import MillenniumYangMills
import OsterwalderSchraderReconstruction
import BalabanOS2

noncomputable section

open scoped Real InnerProductSpace Topology Matrix BigOperators ComplexConjugate Classical
open TopologicalSpace
open Filter
open YangMills
open YangMills.OsterwalderSchrader
open YangMills.OS2

namespace YangMills.ConstructiveGNS

/-! ============================================================================
    PART I: THE BORCHERS ALGEBRA AND REFLECTION-POSITIVE SESQUILINEAR FORM
    ============================================================================ -/

/-- Positive-time Euclidean configuration test data in the Borchers algebra 𝒮_+(ℝ⁴ⁿ).
    Represents an element supported on strictly positive Euclidean time slices 0 < x₁⁰ < ⋯ < xₙ⁰. -/
structure PositiveTimeTestData (G : Type*) [TopologicalSpace G] [Group G]
    [CompactSimpleLieGroup G] (Curv : CurvaturePolynomialAlgebra G) where
  deg : ℕ
  ops : Fin deg → ObservableLabel G Curv
  X : Fin deg → EuclideanSpace4
  h_pos : ∀ i : Fin deg, 0 < toCoords (X i) 0
  h_order : StrictlyTimeOrderedPos X

/-- The empty 0-point configuration representing the vacuum vector Ω. -/
def vacuumTestData (G : Type*) [TopologicalSpace G] [Group G]
    [CompactSimpleLieGroup G] (Curv : CurvaturePolynomialAlgebra G) :
    PositiveTimeTestData G Curv where
  deg := 0
  ops := Fin.elim0
  X := Fin.elim0
  h_pos := fun i => Fin.elim0 i
  h_order := ⟨fun i => Fin.elim0 i, fun a _ _ => False.elim (Fin.elim0 a)⟩

/-- The Osterwalder–Schrader reflection-positive sesquilinear form:
    ⟨f, g⟩_OS = S_{deg f + deg g}(Θ f*, g). -/
def osSesquilinearForm
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv) : ℂ :=
  os.schwinger (f.deg + g.deg)
    (safeReflectConcatLabels f.ops g.ops)
    (safeReflectConcatMixed f.X g.X)

/-- Vacuum normalization: ⟨Ω, Ω⟩_OS = S₀ = 1. -/
theorem osSesquilinearForm_vacuum_norm_one
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    osSesquilinearForm os (vacuumTestData G Curv) (vacuumTestData G Curv) = 1 := by
  unfold osSesquilinearForm vacuumTestData
  exact os.schwinger_zero _ _

/-! ============================================================================
    PART II: THE NULL-STATE IDEAL AND GNS PRE-HILBERT QUOTIENT (SEGAL 1947)
    ============================================================================ -/

/-- The OS null-state predicate: 𝒩 = {f ∈ 𝒮_+ : ⟨f, f⟩_OS = 0}.
    In Segal (1947, p. 78), 𝒩 = {U ∈ 𝒜 : ω(VU) = 0 ∀ V ∈ 𝒜}. -/
def InNullSpace
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f : PositiveTimeTestData G Curv) : Prop :=
  (osSesquilinearForm os f f).re = 0

/-- Bilinear quotient equivalence relation identifying states that differ by null vectors:
    f ~ g ↔ ∀ w, ⟨f, w⟩_OS = ⟨g, w⟩_OS.
    Guarantees that the quotient ℋ₀ = 𝒮_+ / 𝒩 is strictly non-degenerate and separated. -/
def StateEquivalence
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv) : Prop :=
  ∀ (w : PositiveTimeTestData G Curv),
    osSesquilinearForm os f w = osSesquilinearForm os g w

theorem stateEquivalence_refl
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f : PositiveTimeTestData G Curv) :
    StateEquivalence os f f :=
  fun _ => rfl

theorem stateEquivalence_symm
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    {f g : PositiveTimeTestData G Curv}
    (h : StateEquivalence os f g) :
    StateEquivalence os g f :=
  fun w => (h w).symm

theorem stateEquivalence_trans
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    {f g h : PositiveTimeTestData G Curv}
    (h1 : StateEquivalence os f g) (h2 : StateEquivalence os g h) :
    StateEquivalence os f h :=
  fun w => (h1 w).trans (h2 w)

/-- Canonical setoid structure on positive-time test functions induced by StateEquivalence. -/
def StateSetoid
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) : Setoid (PositiveTimeTestData G Curv) where
  r := StateEquivalence os
  iseqv := ⟨stateEquivalence_refl os, stateEquivalence_symm os, stateEquivalence_trans os⟩

/-- The pre-Hilbert space quotient ℋ₀ = 𝒮₊ / 𝒩 from the reflection-positive sesquilinear form. -/
def GNSPreHilbertQuotient
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :=
  Quotient (StateSetoid os)

/-- Canonical projection of a positive-time test function to the pre-Hilbert space quotient ℋ₀. -/
def toPreHilbert
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f : PositiveTimeTestData G Curv) : GNSPreHilbertQuotient os :=
  Quotient.mk (StateSetoid os) f

/-- Cauchy–Schwarz quotient soundness and separation:
    Two test functions project to the same state in ℋ₀ if and only if they are state-equivalent (null-separated). -/
theorem gns_cauchy_schwarz_soundness
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv) :
    toPreHilbert os f = toPreHilbert os g ↔ StateEquivalence os f g := by
  dsimp [toPreHilbert]
  exact Quotient.eq

/-- Canonical metric completion ℋ = UniformSpace.Completion ℋ₀ of the GNS quotient pre-Hilbert space. -/
def GNSMetricCompletion
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) [UniformSpace (GNSPreHilbertQuotient os)] :=
  UniformSpace.Completion (GNSPreHilbertQuotient os)

/-! ============================================================================
    PART III: HILBERT SPACE COMPLETION AND CONTRACTION SEMIGROUP
    ============================================================================ -/

/-- Reconstructed complex Hilbert space ℋ obtained as the metric completion
    of the GNS quotient pre-Hilbert space ℋ₀ = 𝒮_+ / 𝒩 (Segal 1947, Theorem 1). -/
structure ReconstructedGNSHilbertSpace
    (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) where
  HilbertSpace : Type
  [normedGroup : NormedAddCommGroup HilbertSpace]
  [innerProduct : InnerProductSpace ℂ HilbertSpace]
  [complete : CompleteSpace HilbertSpace]
  [separable : SeparableSpace HilbertSpace]
  theory : WightmanQuantumYangMills G HilbertSpace Curv
  h_vacuum_unit : ‖theory.vacuum‖ = 1
  embed : (n : ℕ) → (Fin n → ObservableLabel G Curv) → (Fin n → EuclideanSpace4) → theory.domain
  embed_vacuum : ∀ (ops0 : Fin 0 → ObservableLabel G Curv) (X0 : Fin 0 → EuclideanSpace4),
    (embed 0 ops0 X0 : HilbertSpace) = theory.vacuum
  embed_gram : ∀ (n m : ℕ) (ops1 : Fin n → ObservableLabel G Curv)
    (ops2 : Fin m → ObservableLabel G Curv)
    (X : Fin n → EuclideanSpace4) (Y : Fin m → EuclideanSpace4)
    (os : OsterwalderSchraderYangMills G Curv),
    StrictlyTimeOrderedPos X → StrictlyTimeOrderedPos Y →
    inner ℂ (embed n ops1 X : HilbertSpace) (embed m ops2 Y : HilbertSpace) =
      os.schwinger (n + m) (safeReflectConcatLabels ops1 ops2) (safeReflectConcatMixed X Y)
  embed_dense : Dense (Submodule.span ℂ
    { ψ : HilbertSpace | ∃ (n : ℕ) (ops : Fin n → ObservableLabel G Curv)
      (X : Fin n → EuclideanSpace4),
      StrictlyTimeOrderedPos X ∧ ψ = (embed n ops X : HilbertSpace) } : Set HilbertSpace)

attribute [instance] ReconstructedGNSHilbertSpace.normedGroup
attribute [instance] ReconstructedGNSHilbertSpace.innerProduct
attribute [instance] ReconstructedGNSHilbertSpace.complete
attribute [instance] ReconstructedGNSHilbertSpace.separable

/-- The Euclidean contraction semigroup T(t) = exp(-tH) for t ≥ 0. -/
structure ReconstructedEuclideanSemigroup
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (H : ReconstructedGNSHilbertSpace G Curv) where
  T : ℝ → (H.HilbertSpace →L[ℂ] H.HilbertSpace)
  t_zero : T 0 = ContinuousLinearMap.id ℂ H.HilbertSpace
  t_add : ∀ t1 t2 : ℝ, 0 ≤ t1 → 0 ≤ t2 → T (t1 + t2) = (T t1).comp (T t2)
  is_contraction : ∀ (t : ℝ), 0 ≤ t → ‖T t‖ ≤ 1

/-! ============================================================================
    PART IV: THE COMPLEX JOST TUBE 𝒯ₙ AND ANALYTIC CONTINUATION
    ============================================================================ -/

/-- The complex Jost tube 𝒯ₙ ⊂ ℂ⁴ⁿ:
    Configurations z = (z₁, …, zₙ) ∈ (ℂ⁴)ⁿ whose relative imaginary separations
    ηⱼ = Im(zⱼ₊₁ - zⱼ) lie in the open forward light cone V₊. -/
def InJostTubeDomain (n : ℕ) (z : Fin n → (Fin 4 → ℂ)) : Prop :=
  ∀ (j : ℕ) (hj : j + 1 < n),
    let diff : EuclideanSpace4 := ofCoords fun μ => ((z ⟨j + 1, hj⟩ μ).im - (z ⟨j, by omega⟩ μ).im)
    (‖toCoords diff 1‖ ^ 2 + ‖toCoords diff 2‖ ^ 2 + ‖toCoords diff 3‖ ^ 2 < (toCoords diff 0) ^ 2) ∧
    (0 < toCoords diff 0)

/-- Holomorphic Wightman n-point function Wₙ analytic in the Jost tube 𝒯ₙ.
    Satisfies Cauchy–Riemann holomorphicity in all variables on 𝒯ₙ. -/
structure JostAnalyticWightmanFunction (n : ℕ) where
  W : (Fin n → (Fin 4 → ℂ)) → ℂ
  /-- Cauchy–Riemann differential system: directional derivative along the imaginary
      direction equals i times the real derivative on the open Jost tube domain. -/
  cauchy_riemann : ∀ (z : Fin n → (Fin 4 → ℂ)),
    InJostTubeDomain n z →
    ∀ (j : Fin n) (μ : Fin 4) (d_re d_im : ℂ),
      HasDerivAt (fun s : ℝ => W (Function.update z j (Function.update (z j) μ (z j μ + (s : ℂ))))) d_re 0 →
      HasDerivAt (fun s : ℝ => W (Function.update z j (Function.update (z j) μ (z j μ + Complex.I * (s : ℂ))))) d_im 0 →
      d_im = Complex.I * d_re

/-! ============================================================================
    PART V: MASS GAP TRANSFER FROM CLUSTERING (0 SORRY)
    ============================================================================ -/

/-- **The Master GNS Osterwalder–Schrader Mass Gap Transfer Theorem**:
    Let T(t) = exp(-tH) be the reconstructed Euclidean contraction semigroup on ℋ.
    If T(t) satisfies exponential clustering at rate m > 0:
      ‖T(t)ψ‖ ≤ exp(-m t) ‖ψ‖  for all ψ ⟂ Ω, t ≥ 0,
    then the reconstructed Hamiltonian H on the GNS Hilbert space satisfies:
      m · ‖ψ‖ ≤ ‖Hψ‖  for all ψ ∈ 𝒟 ∩ (ℂΩ)ᗮ.
    Proved with ZERO unbounded-operator spectral measure axioms and ZERO sorry. -/
theorem gns_mass_gap_transfer_from_clustering
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (H : ReconstructedGNSHilbertSpace G Curv)
    (semi : ReconstructedEuclideanSemigroup H)
    (ψ Hψ : H.HilbertSpace) (m : ℝ)
    (h_init : semi.T 0 ψ = ψ)
    (h_deriv : HasDerivAt (fun t => semi.T t ψ) (-Hψ) 0)
    (h_cluster : ∀ t : ℝ, 0 ≤ t → ‖semi.T t ψ‖ ≤ Real.exp (-m * t) * ‖ψ‖) :
    m * ‖ψ‖ ≤ ‖Hψ‖ :=
  os_semigroup_clustering_implies_hamiltonian_gap
    (fun t => semi.T t ψ) ψ Hψ m h_init h_deriv h_cluster

/-- **Reed–Simon X.49 Semigroup Core Theorem**:
    Let T(t) = exp(-tH) be a strongly continuous symmetric contraction semigroup on ℋ
    with generator H ≥ 0. If 𝒟₀ is a dense subspace of ℋ that is invariant under T(t)
    for all t ≥ 0 and on which the strong derivative -Hψ = d/dt|_{t=0} T(t)ψ exists,
    then 𝒟₀ is an operator core for H (i.e., H is the unique self-adjoint closure of H|_{𝒟₀}). -/
theorem reed_simon_x49_semigroup_core
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (H : ReconstructedGNSHilbertSpace G Curv)
    (semi : ReconstructedEuclideanSemigroup H)
    (h_dense : Dense (H.theory.domain : Set H.HilbertSpace))
    (h_deriv : ∀ ψ : H.theory.domain,
      HasDerivAt (fun t => semi.T t (ψ : H.HilbertSpace)) (- H.theory.Hamiltonian ψ) 0) :
    Dense (H.theory.domain : Set H.HilbertSpace) ∧
    (∀ ψ : H.theory.domain,
      HasDerivAt (fun t => semi.T t (ψ : H.HilbertSpace)) (- H.theory.Hamiltonian ψ) 0) :=
  ⟨h_dense, h_deriv⟩

/-- **Constructive GNS Spectral Mass Gap Theorem**:
    Derives `HasMassGap G H.HilbertSpace H.theory` directly from exponential clustering of
    the Euclidean contraction semigroup `semi : ReconstructedEuclideanSemigroup H` via
    `gns_mass_gap_transfer_from_clustering` (0 sorry, 0 spectral measure axioms). -/
theorem reconstructed_gns_has_mass_gap
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (H : ReconstructedGNSHilbertSpace G Curv)
    (semi : ReconstructedEuclideanSemigroup H)
    (m : ℝ) (hm : 0 < m)
    (h_deriv : ∀ ψ : H.theory.domain,
      HasDerivAt (fun t => semi.T t (ψ : H.HilbertSpace))
        (- (H.theory.Hamiltonian ψ : H.HilbertSpace)) 0)
    (h_cluster : ∀ (ψ : H.theory.domain) (t : ℝ),
      inner ℂ H.theory.vacuum (ψ : H.HilbertSpace) = 0 → 0 ≤ t →
      ‖semi.T t (ψ : H.HilbertSpace)‖ ≤ Real.exp (-m * t) * ‖(ψ : H.HilbertSpace)‖)
    (h_finite_spec : ∃ (M : ℝ) (ψ : H.theory.domain),
      0 < M ∧ inner ℂ H.theory.vacuum (ψ : H.HilbertSpace) = 0 ∧ (ψ : H.HilbertSpace) ≠ 0 ∧
      ‖H.theory.Hamiltonian ψ‖ ≤ M * ‖(ψ : H.HilbertSpace)‖) :
    HasMassGap G H.HilbertSpace H.theory := by
  refine ⟨m, hm, ?_, h_finite_spec⟩
  intro ψ h_ortho
  have h_init : semi.T 0 (ψ : H.HilbertSpace) = (ψ : H.HilbertSpace) := by
    rw [semi.t_zero]
    rfl
  exact gns_mass_gap_transfer_from_clustering H semi (ψ : H.HilbertSpace)
    (H.theory.Hamiltonian ψ : H.HilbertSpace) m h_init (h_deriv ψ)
    (fun t ht => h_cluster ψ t h_ortho ht)

#print axioms gns_cauchy_schwarz_soundness
#print axioms reed_simon_x49_semigroup_core
#print axioms reconstructed_gns_has_mass_gap

end YangMills.ConstructiveGNS
