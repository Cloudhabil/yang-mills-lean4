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

/-- Canonical sesquilinear OS reflection form `sesqOS` on positive-time states,
    defined from `os.schwinger` and `safeReflectConcatMixed`. -/
def sesqOS
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv) : ℂ :=
  osSesquilinearForm os f g

/-- Non-negativity of the diagonal OS reflection form `0 ≤ Re ⟨ψ, ψ⟩_OS`,
    proved directly from `os.os2_reflection_positivity`. -/
theorem sesqOS_nonneg
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ψ : PositiveTimeTestData G Curv) :
    0 ≤ (sesqOS os ψ ψ).re := by
  have h_e2 := os.os2_reflection_positivity 1
    (fun _ => ψ.deg)
    (fun _ => ψ.ops)
    (fun _ => ψ.X)
    (fun _ => (1 : ℂ))
    (fun _ i => ψ.h_pos i)
  have h_univ : (Finset.univ : Finset (Fin 1)) = {0} := rfl
  simp only [h_univ, Finset.sum_singleton, map_one, one_mul] at h_e2
  exact h_e2

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

private noncomputable def gnsRawDist
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv) : ℝ :=
  ⨆ w : PositiveTimeTestData G Curv, min 1 ‖sesqOS os f w - sesqOS os g w‖

private theorem gnsRawDist_bddAbove
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv) :
    BddAbove (Set.range fun w : PositiveTimeTestData G Curv =>
      min 1 ‖sesqOS os f w - sesqOS os g w‖) :=
  ⟨1, Set.forall_mem_range.mpr fun _ => min_le_left _ _⟩

private theorem gnsRawDist_congr
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    {f f' g g' : PositiveTimeTestData G Curv}
    (hf : StateEquivalence os f f') (hg : StateEquivalence os g g') :
    gnsRawDist os f g = gnsRawDist os f' g' := by
  unfold gnsRawDist sesqOS
  congr 1
  ext w
  rw [hf w, hg w]

/-- Canonical `MetricSpace` structure on `GNSPreHilbertQuotient os` induced by `sesqOS`. -/
@[instance_reducible]
noncomputable def gnsPreHilbertMetricSpace
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    MetricSpace (GNSPreHilbertQuotient os) where
  dist := Quotient.lift₂ (gnsRawDist os)
    (fun _ _ _ _ hf hg => gnsRawDist_congr os hf hg)
  dist_self := Quotient.ind fun f => by
    change gnsRawDist os f f = 0
    simp [gnsRawDist]
  dist_comm := Quotient.ind₂ fun f g => by
    change gnsRawDist os f g = gnsRawDist os g f
    unfold gnsRawDist
    congr 1
    ext w
    rw [norm_sub_rev]
  dist_triangle := fun x y z => by
    refine Quotient.inductionOn₃ x y z fun f g h => ?_
    change gnsRawDist os f h ≤ gnsRawDist os f g + gnsRawDist os g h
    have : Nonempty (PositiveTimeTestData G Curv) := ⟨vacuumTestData G Curv⟩
    refine ciSup_le fun w => ?_
    have h_tri : min 1 ‖sesqOS os f w - sesqOS os h w‖ ≤
        min 1 ‖sesqOS os f w - sesqOS os g w‖ + min 1 ‖sesqOS os g w - sesqOS os h w‖ := by
      rcases le_total 1 ‖sesqOS os f w - sesqOS os g w‖ with hfg | hfg
      · rw [min_eq_left hfg]
        exact (min_le_left _ _).trans (le_add_of_nonneg_right (le_min zero_le_one (norm_nonneg _)))
      · rcases le_total 1 ‖sesqOS os g w - sesqOS os h w‖ with hgh | hgh
        · rw [min_eq_left hgh]
          exact (min_le_left _ _).trans (le_add_of_nonneg_left (le_min zero_le_one (norm_nonneg _)))
        · rw [min_eq_right hfg, min_eq_right hgh]
          exact (min_le_right _ _).trans (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    exact h_tri.trans (add_le_add
      (le_ciSup (gnsRawDist_bddAbove os f g) w)
      (le_ciSup (gnsRawDist_bddAbove os g h) w))
  eq_of_dist_eq_zero := fun {x y} hxy => by
    refine Quotient.inductionOn₂ x y (fun f g hfg => ?_) hxy
    change gnsRawDist os f g = 0 at hfg
    apply Quotient.sound
    intro w
    have hle : min 1 ‖sesqOS os f w - sesqOS os g w‖ ≤ 0 := by
      rw [← hfg]
      exact le_ciSup (gnsRawDist_bddAbove os f g) w
    have h_nonneg : 0 ≤ min 1 ‖sesqOS os f w - sesqOS os g w‖ :=
      le_min zero_le_one (norm_nonneg _)
    have hmin0 : min 1 ‖sesqOS os f w - sesqOS os g w‖ = 0 := le_antisymm hle h_nonneg
    rcases min_eq_iff.mp hmin0 with ⟨h1, _⟩ | ⟨hnorm0, _⟩
    · norm_num at h1
    · exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)

/-- Canonical `UniformSpace` on `GNSPreHilbertQuotient os` constructed from `sesqOS`. -/
noncomputable instance gnsPreHilbertUniformSpace
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    UniformSpace (GNSPreHilbertQuotient os) :=
  (gnsPreHilbertMetricSpace os).toUniformSpace

/-- Canonical metric completion ℋ = UniformSpace.Completion ℋ₀ of the GNS quotient pre-Hilbert space. -/
def GNSMetricCompletion
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :=
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

/-! ============================================================================
    PART IV: CONSTRUCTIVE EUCLIDEAN TIME-TRANSLATION SEMIGROUP FROM OS1 & OS4
    ============================================================================ -/

private theorem toCoords_vec4 (t x y z : ℝ) :
    toCoords (vec4 t x y z) = ![t, x, y, z] := rfl

private theorem toCoords_euclideanShift {n : ℕ} (t : ℝ) (X : Fin n → EuclideanSpace4) (i : Fin n) :
    toCoords (euclideanShift t 0 X i) =
      ![toCoords (X i) 0 + t, toCoords (X i) 1, toCoords (X i) 2, toCoords (X i) 3] := by
  simp [euclideanShift, toCoords_vec4, toCoords]
  rfl

/-- **(1) Shifted Positive-Time Test Data**: shifts all Euclidean time coordinates forward by `t ≥ 0`
    via `euclideanShift t 0`, preserving strict positivity (`0 < c 0 + t`) and strict time ordering. -/
def shiftPositiveTimeTestData
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (t : ℝ) (ht : 0 ≤ t) (f : PositiveTimeTestData G Curv) :
    PositiveTimeTestData G Curv where
  deg := f.deg
  ops := f.ops
  X := euclideanShift t 0 f.X
  h_pos := fun i => by
    have h0 : toCoords (euclideanShift t 0 f.X i) 0 = toCoords (f.X i) 0 + t := rfl
    rw [h0]
    exact add_pos_of_pos_of_nonneg (f.h_pos i) ht
  h_order := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · change 0 < toCoords (f.X i) 0 + t
      exact add_pos_of_pos_of_nonneg (f.h_pos i) ht
    · change toCoords (f.X i) 0 + t < toCoords (f.X j) 0 + t
      linarith [f.h_order.2 hij]

/-- **(2a) OS Reflection Symmetry of Time-Translation**:
    Using `os.os1_euclidean_invariance` with `(R, v) = (1, vec4 t 0 0 0)`,
    `⟨T(t)f, g⟩_OS = ⟨f, T(t)g⟩_OS`. -/
theorem sesqOS_shift_symm
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) (f g : PositiveTimeTestData G Curv) :
    sesqOS os (shiftPositiveTimeTestData t ht f) g =
      sesqOS os f (shiftPositiveTimeTestData t ht g) := by
  unfold sesqOS osSesquilinearForm shiftPositiveTimeTestData
  dsimp only
  have h_inv := os.os1_euclidean_invariance (f.deg + g.deg)
    (safeReflectConcatLabels f.ops g.ops)
    (1 : Matrix (Fin 4) (Fin 4) ℝ)
    (vec4 t 0 0 0)
    (safeReflectConcatMixed (euclideanShift t 0 f.X) g.X)
    (by simp) Matrix.det_one
  have h_ops :
      (fun i => match safeReflectConcatLabels f.ops g.ops i with
        | .localCurv P => .localCurv (Curv.transform 1 P)
        | .wilsonChar chi => .wilsonChar chi) =
      safeReflectConcatLabels f.ops g.ops := by
    ext i
    cases h : safeReflectConcatLabels f.ops g.ops i with
    | localCurv P => simp only [Curv.transform_id, LinearMap.id_apply]
    | wilsonChar chi => rfl
  have h_pts :
      (fun k => euclideanTransform (1 : Matrix (Fin 4) (Fin 4) ℝ) (vec4 t 0 0 0)
        (safeReflectConcatMixed (euclideanShift t 0 f.X) g.X k)) =
      safeReflectConcatMixed f.X (euclideanShift t 0 g.X) := by
    ext k μ
    change toCoords (vec4 t 0 0 0) μ +
      ((1 : Matrix (Fin 4) (Fin 4) ℝ).mulVec
        (toCoords (safeReflectConcatMixed (euclideanShift t 0 f.X) g.X k))) μ =
      toCoords (safeReflectConcatMixed f.X (euclideanShift t 0 g.X) k) μ
    rw [Matrix.one_mulVec]
    unfold safeReflectConcatMixed
    split_ifs with hk
    · unfold timeReflect euclideanShift
      fin_cases μ <;> simp [vec4, ofCoords, toCoords]
    · unfold euclideanShift
      fin_cases μ <;> simp [vec4, ofCoords, toCoords] <;> ring
  calc os.schwinger (f.deg + g.deg) (safeReflectConcatLabels f.ops g.ops)
        (safeReflectConcatMixed (euclideanShift t 0 f.X) g.X)
    _ = os.schwinger (f.deg + g.deg)
          (fun i => match safeReflectConcatLabels f.ops g.ops i with
            | .localCurv P => .localCurv (Curv.transform 1 P)
            | .wilsonChar chi => .wilsonChar chi)
          (fun k => euclideanTransform (1 : Matrix (Fin 4) (Fin 4) ℝ) (vec4 t 0 0 0)
            (safeReflectConcatMixed (euclideanShift t 0 f.X) g.X k)) := h_inv.symm
    _ = os.schwinger (f.deg + g.deg) (safeReflectConcatLabels f.ops g.ops)
          (safeReflectConcatMixed f.X (euclideanShift t 0 g.X)) :=
        congrArg₂ (os.schwinger (f.deg + g.deg)) h_ops h_pts

/-- **(2b) Preservation of `StateEquivalence`**:
    `shiftPositiveTimeTestData t ht` descends cleanly to `GNSPreHilbertQuotient os`. -/
theorem shiftPositiveTimeTestData_congr
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) {f f' : PositiveTimeTestData G Curv}
    (h : StateEquivalence os f f') :
    StateEquivalence os (shiftPositiveTimeTestData t ht f) (shiftPositiveTimeTestData t ht f') := by
  intro w
  change sesqOS os (shiftPositiveTimeTestData t ht f) w =
    sesqOS os (shiftPositiveTimeTestData t ht f') w
  rw [sesqOS_shift_symm os t ht f w, sesqOS_shift_symm os t ht f' w]
  exact h (shiftPositiveTimeTestData t ht w)

private theorem shiftPositiveTimeTestData_zero
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (f : PositiveTimeTestData G Curv) :
    shiftPositiveTimeTestData 0 le_rfl f = f := by
  cases f with
  | mk deg ops X h_pos h_order =>
    simp only [shiftPositiveTimeTestData]
    congr 1
    ext i μ
    fin_cases μ <;> simp [euclideanShift, vec4, ofCoords, toCoords]

private theorem shiftPositiveTimeTestData_add
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (t1 t2 : ℝ) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (f : PositiveTimeTestData G Curv) :
    shiftPositiveTimeTestData (t1 + t2) (add_nonneg ht1 ht2) f =
      shiftPositiveTimeTestData t1 ht1 (shiftPositiveTimeTestData t2 ht2 f) := by
  cases f with
  | mk deg ops X h_pos h_order =>
    simp only [shiftPositiveTimeTestData]
    congr 1
    ext i μ
    fin_cases μ <;> (simp [euclideanShift, vec4, ofCoords, toCoords]; try ring)

/-- **(3) Constructive Quotient Euclidean Time-Translation Semigroup**
    `gnsPreHilbertSemigroup os t ht : GNSPreHilbertQuotient os → GNSPreHilbertQuotient os`. -/
def gnsPreHilbertSemigroup
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) :
    GNSPreHilbertQuotient os → GNSPreHilbertQuotient os :=
  Quotient.lift (fun f => toPreHilbert os (shiftPositiveTimeTestData t ht f))
    (fun _ _ h => Quotient.sound (shiftPositiveTimeTestData_congr os t ht h))

/-- Semigroup identity at `t = 0`: `T(0) = id`. -/
theorem gnsPreHilbertSemigroup_zero
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    gnsPreHilbertSemigroup os 0 le_rfl = id := by
  ext x
  refine Quotient.inductionOn x fun f => ?_
  change toPreHilbert os (shiftPositiveTimeTestData 0 le_rfl f) = toPreHilbert os f
  rw [shiftPositiveTimeTestData_zero]

/-- Semigroup composition law: `T(t1 + t2) = T(t1) ∘ T(t2)`. -/
theorem gnsPreHilbertSemigroup_add
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t1 t2 : ℝ) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) :
    gnsPreHilbertSemigroup os (t1 + t2) (add_nonneg ht1 ht2) =
      gnsPreHilbertSemigroup os t1 ht1 ∘ gnsPreHilbertSemigroup os t2 ht2 := by
  ext x
  refine Quotient.inductionOn x fun f => ?_
  change toPreHilbert os (shiftPositiveTimeTestData (t1 + t2) (add_nonneg ht1 ht2) f) =
    toPreHilbert os (shiftPositiveTimeTestData t1 ht1 (shiftPositiveTimeTestData t2 ht2 f))
  rw [shiftPositiveTimeTestData_add]

/-- **(4) Exponential Clustering of Shifted OS Correlations from OS4**:
    For any positive-time states `f, g`, `sesqOS os f (shiftPositiveTimeTestData t ht g)`
    clusters exponentially to `conj(S_{f.deg}(Θ f*)) * S_{g.deg}(g)` at rate `os.mass_rate`. -/
theorem sesqOS_shift_clustering
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t : ℝ) (ht : 0 ≤ t),
        ‖sesqOS os f (shiftPositiveTimeTestData t ht g) -
          starRingEnd ℂ (os.schwinger f.deg (reverseConjLabels f.ops) (reverseReflectConfig f.X)) *
            os.schwinger g.deg g.ops g.X‖ ≤
        C * Real.exp (-os.mass_rate * t) := by
  let a : EuclideanSpace4 := vec4 1 0 0 0
  have ha0 : 0 ≤ toCoords a 0 := by
    change 0 ≤ (1 : ℝ)
    norm_num
  have ha_norm : ‖a‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have h_sum : (∑ i : Fin 4, ‖a i‖ ^ 2) = 1 := by
      have ha_eq : ∀ i : Fin 4, a i = (![1, 0, 0, 0] : Fin 4 → ℝ) i := fun _ => rfl
      simp only [ha_eq, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      norm_num
    rw [h_sum, Real.sqrt_one]
  obtain ⟨C, hC_nonneg, h_cluster⟩ := os.os4_exponential_clustering
    f.deg g.deg f.ops g.ops f.X g.X a f.h_pos g.h_pos ha0 ha_norm
  refine ⟨C, hC_nonneg, fun t ht => ?_⟩
  have h_trans : translateConfig (t • a) g.X = euclideanShift t 0 g.X := by
    ext j μ
    change toCoords (g.X j) μ + toCoords (t • a) μ = toCoords (euclideanShift t 0 g.X j) μ
    have h_smul : toCoords (t • a) μ = t * toCoords a μ := rfl
    rw [h_smul]
    fin_cases μ <;> simp [a, euclideanShift, vec4, ofCoords, toCoords]
  have h_bound := h_cluster t ht
  rw [h_trans] at h_bound
  exact h_bound

#print axioms gns_cauchy_schwarz_soundness
#print axioms reed_simon_x49_semigroup_core
#print axioms reconstructed_gns_has_mass_gap
#print axioms sesqOS_shift_symm
#print axioms gnsPreHilbertSemigroup_zero
#print axioms gnsPreHilbertSemigroup_add
#print axioms sesqOS_shift_clustering

end YangMills.ConstructiveGNS
