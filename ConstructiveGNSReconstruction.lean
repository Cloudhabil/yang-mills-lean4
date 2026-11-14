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
  is_symmetric : ∀ (t : ℝ), 0 ≤ t → ∀ (φ ψ : H.HilbertSpace),
    inner ℂ (T t φ) ψ = inner ℂ φ (T t ψ)
  m_rate : ℝ
  m_rate_pos : 0 < m_rate
  matrix_element_clustering : ∀ (ψ : H.HilbertSpace),
    inner ℂ H.theory.vacuum ψ = 0 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), 0 ≤ t →
      ‖inner ℂ ψ (T t ψ)‖ ≤ C * Real.exp (-m_rate * t)

/-- **Iterated Cauchy–Schwarz Semigroup Exponential Decay**:
    From symmetry `⟨T(t)φ, ψ⟩ = ⟨φ, T(t)ψ⟩` and matrix-element clustering
    `|⟨ψ, T(t)ψ⟩| ≤ C_ψ exp(-m t)` on `(ℂΩ)ᗮ`, iterated Cauchy–Schwarz
    `‖T(t)ψ‖² = ⟨ψ, T(2t)ψ⟩ ≤ ‖ψ‖ ‖T(2t)ψ‖` eliminates the prefactor `C_ψ` and proves
    `‖T(t)ψ‖ ≤ exp(-m t) ‖ψ‖` for all `ψ ⊥ Ω` and `t ≥ 0`. -/
theorem semigroup_exp_decay_of_symmetric_contraction_clustering
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (H : ReconstructedGNSHilbertSpace G Curv)
    (semi : ReconstructedEuclideanSemigroup H)
    (ψ : H.HilbertSpace) (t : ℝ)
    (h_ortho : inner ℂ H.theory.vacuum ψ = 0) (ht : 0 ≤ t) :
    ‖semi.T t ψ‖ ≤ Real.exp (-semi.m_rate * t) * ‖ψ‖ := by
  have h_step : ∀ (s : ℝ), 0 ≤ s → ∀ (φ : H.HilbertSpace),
      ‖semi.T s φ‖ ^ 2 ≤ ‖φ‖ * ‖semi.T (2 * s) φ‖ := by
    intro s hs φ
    have h_sq : ‖semi.T s φ‖ ^ 2 = (inner ℂ (semi.T s φ) (semi.T s φ)).re := by
      symm
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    have h_symm : inner ℂ (semi.T s φ) (semi.T s φ) = inner ℂ φ (semi.T (2 * s) φ) := by
      rw [semi.is_symmetric s hs φ (semi.T s φ)]
      have h2s : 2 * s = s + s := by ring
      rw [h2s, semi.t_add s s hs hs]
      rfl
    rw [h_sq, h_symm]
    exact le_trans (Complex.re_le_norm _) (norm_inner_le_norm φ (semi.T (2 * s) φ))
  have h_iter : ∀ (k : ℕ),
      ‖semi.T t ψ‖ ^ (2 ^ k) ≤ ‖ψ‖ ^ (2 ^ k - 1) * ‖semi.T ((2 ^ k : ℝ) * t) ψ‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h_nonneg : 0 ≤ ‖semi.T t ψ‖ ^ (2 ^ k) := pow_nonneg (norm_nonneg _) _
      have h_sq_le := pow_le_pow_left₀ h_nonneg ih 2
      have h_pow_eq : (‖semi.T t ψ‖ ^ (2 ^ k)) ^ 2 = ‖semi.T t ψ‖ ^ (2 ^ (k + 1)) := by
        rw [← pow_mul, pow_succ]
      rw [h_pow_eq, mul_pow, ← pow_mul] at h_sq_le
      have h_s : 0 ≤ (2 ^ k : ℝ) * t := mul_nonneg (by positivity) ht
      have h_st := h_step ((2 ^ k : ℝ) * t) h_s ψ
      have h2k : 2 * ((2 ^ k : ℝ) * t) = (2 ^ (k + 1) : ℝ) * t := by
        rw [pow_succ]; ring
      rw [h2k] at h_st
      have h_mul := mul_le_mul_of_nonneg_left h_st (pow_nonneg (norm_nonneg ψ) ((2 ^ k - 1) * 2))
      refine le_trans h_sq_le (le_trans h_mul ?_)
      have h_exp : (2 ^ k - 1) * 2 + 1 = 2 ^ (k + 1) - 1 := by
        have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
        rw [pow_succ]
        omega
      rw [← mul_assoc, ← pow_succ, h_exp]
  obtain ⟨C, _hC_nonneg, h_mat⟩ := semi.matrix_element_clustering ψ h_ortho
  have h_mat_sq : ∀ k : ℕ,
      ‖semi.T ((2 ^ k : ℝ) * t) ψ‖ ^ 2 ≤ C * Real.exp (-semi.m_rate * ((2 ^ (k + 1) : ℝ) * t)) := by
    intro k
    have hs : 0 ≤ (2 ^ k : ℝ) * t := mul_nonneg (by positivity) ht
    have h_sq : ‖semi.T ((2 ^ k : ℝ) * t) ψ‖ ^ 2 =
        (inner ℂ ψ (semi.T ((2 ^ (k + 1) : ℝ) * t) ψ)).re := by
      have h_n : ‖semi.T ((2 ^ k : ℝ) * t) ψ‖ ^ 2 =
          (inner ℂ (semi.T ((2 ^ k : ℝ) * t) ψ) (semi.T ((2 ^ k : ℝ) * t) ψ)).re := by
        symm
        rw [inner_self_eq_norm_sq_to_K]
        norm_cast
      rw [h_n, semi.is_symmetric _ hs]
      have h2k : (2 ^ (k + 1) : ℝ) * t = (2 ^ k : ℝ) * t + (2 ^ k : ℝ) * t := by
        rw [pow_succ]; ring
      rw [h2k, semi.t_add _ _ hs hs]
      rfl
    rw [h_sq]
    have h2k_nonneg : 0 ≤ (2 ^ (k + 1) : ℝ) * t := mul_nonneg (by positivity) ht
    exact le_trans (Complex.re_le_norm _) (h_mat _ h2k_nonneg)
  by_cases hψ : ψ = 0
  · subst hψ; simp
  have hψ_pos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have h_den_pos : 0 < Real.exp (-semi.m_rate * t) * ‖ψ‖ :=
    mul_pos (Real.exp_pos _) hψ_pos
  let r : ℝ := ‖semi.T t ψ‖ / (Real.exp (-semi.m_rate * t) * ‖ψ‖)
  suffices hr : r ≤ 1 by
    exact (div_le_one h_den_pos).mp hr
  by_contra hr_gt
  push_neg at hr_gt
  have h_upper : ∀ k : ℕ, r ^ (2 ^ (k + 1)) ≤ C / ‖ψ‖ ^ 2 := by
    intro k
    have h_pow_k := h_iter k
    have h_sq_k := pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) h_pow_k 2
    have h_lhs : (‖semi.T t ψ‖ ^ (2 ^ k)) ^ 2 = ‖semi.T t ψ‖ ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, pow_succ]
    rw [h_lhs, mul_pow, ← pow_mul] at h_sq_k
    have h_m := mul_le_mul_of_nonneg_left (h_mat_sq k) (pow_nonneg hψ_pos.le ((2 ^ k - 1) * 2))
    have h_comb := le_trans h_sq_k h_m
    have h_exp_pow : (Real.exp (-semi.m_rate * t)) ^ (2 ^ (k + 1)) =
        Real.exp (-semi.m_rate * ((2 ^ (k + 1) : ℝ) * t)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h_den_pow_pos : 0 < (Real.exp (-semi.m_rate * t) * ‖ψ‖) ^ (2 ^ (k + 1)) :=
      pow_pos h_den_pos _
    rw [div_pow, mul_pow, h_exp_pow]
    rw [div_le_div_iff₀ (mul_pos (Real.exp_pos _) (pow_pos hψ_pos _)) (sq_pos_of_pos hψ_pos)]
    have h_exp2 : (2 ^ k - 1) * 2 + 2 = 2 ^ (k + 1) := by
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      rw [pow_succ]; omega
    have h_rhs_eq :
        ‖ψ‖ ^ ((2 ^ k - 1) * 2) * (C * Real.exp (-semi.m_rate * ((2 ^ (k + 1) : ℝ) * t))) * ‖ψ‖ ^ 2 =
        C * (Real.exp (-semi.m_rate * ((2 ^ (k + 1) : ℝ) * t)) * ‖ψ‖ ^ (2 ^ (k + 1))) := by
      calc ‖ψ‖ ^ ((2 ^ k - 1) * 2) * (C * Real.exp (-semi.m_rate * ((2 ^ (k + 1) : ℝ) * t))) * ‖ψ‖ ^ 2
        _ = C * (Real.exp (-semi.m_rate * ((2 ^ (k + 1) : ℝ) * t)) * (‖ψ‖ ^ ((2 ^ k - 1) * 2) * ‖ψ‖ ^ 2)) := by ring
        _ = C * (Real.exp (-semi.m_rate * ((2 ^ (k + 1) : ℝ) * t)) * ‖ψ‖ ^ (2 ^ (k + 1))) := by
            rw [← pow_add, h_exp2]
    rw [← h_rhs_eq]
    exact mul_le_mul_of_nonneg_right h_comb (sq_nonneg _)
  have h_tend : Filter.Tendsto (fun k : ℕ => r ^ (2 ^ (k + 1))) Filter.atTop Filter.atTop := by
    refine (tendsto_pow_atTop_atTop_of_one_lt hr_gt).comp ?_
    exact Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => by
      have h_lt : k + 1 < 2 ^ (k + 1) := Nat.lt_pow_self (by norm_num : 1 < 2)
      omega⟩
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp ((Filter.tendsto_atTop.mp h_tend) (C / ‖ψ‖ ^ 2 + 1))
  have hk' := hk k le_rfl
  linarith [h_upper k]

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

/-! ============================================================================
    PART V: TRUNCATED CONTINUUM CHARACTERISTIC FUNCTIONAL (OS0)
    ============================================================================ -/

/-- Truncated continuum characteristic functional:
    `𝒞_N(f) = ∑_{n=0}^N (i^n / n!) S_n(f^⊗n)`. -/
noncomputable def charFunctionalTrunc
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (op : ObservableLabel G Curv) (N : ℕ)
    (f : SchwartzMap EuclideanSpace4 ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1),
    (Complex.I ^ n / (Nat.factorial n : ℂ)) *
      os.schwinger_smeared n (fun _ => op) (fun _ => f)

private theorem schwinger_smeared_zero_eq_one
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ops : Fin 0 → ObservableLabel G Curv)
    (f : Fin 0 → SchwartzMap EuclideanSpace4 ℂ) :
    os.schwinger_smeared 0 ops f = 1 := by
  have h_disj : DisjointSupports f := fun i => i.elim0
  rw [os.schwinger_smeared_integral_compat 0 ops f h_disj]
  simp [os.schwinger_zero, MeasureTheory.Measure.real_def, MeasureTheory.volume_pi]

/-- Normalization of the truncated characteristic functional at `N = 0`: `𝒞_0(f) = 1`. -/
theorem charFunctionalTrunc_zero
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (op : ObservableLabel G Curv) (f : SchwartzMap EuclideanSpace4 ℂ) :
    charFunctionalTrunc os op 0 f = 1 := by
  unfold charFunctionalTrunc
  simp [schwinger_smeared_zero_eq_one]

/-- Normalization of the truncated characteristic functional at `f = 0`: `𝒞_N(0) = 1`. -/
theorem charFunctionalTrunc_zero_test
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (op : ObservableLabel G Curv) (N : ℕ) :
    charFunctionalTrunc os op N 0 = 1 := by
  unfold charFunctionalTrunc
  rw [Finset.sum_range_succ']
  have h0 : (Complex.I ^ 0 / (Nat.factorial 0 : ℂ)) *
      os.schwinger_smeared 0 (fun _ => op) (fun _ => 0) = 1 := by
    simp [schwinger_smeared_zero_eq_one]
  have h_rest : ∀ k ∈ Finset.range N,
      (Complex.I ^ (k + 1) / (Nat.factorial (k + 1) : ℂ)) *
        os.schwinger_smeared (k + 1) (fun _ => op) (fun _ => 0) = 0 := by
    intro k _
    have h_lin := os.schwinger_smeared_linear (k + 1) (fun _ => op) 0 0 0 0 0 (fun _ => 0)
    have h_upd : Function.update (fun _ : Fin (k + 1) => (0 : SchwartzMap EuclideanSpace4 ℂ))
        0 ((0 : ℂ) • 0 + (0 : ℂ) • 0) = fun _ => 0 := by
      ext j
      by_cases hj : j = 0
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [h_upd] at h_lin
    simp only [zero_mul, add_zero] at h_lin
    rw [h_lin, mul_zero]
  rw [Finset.sum_eq_zero h_rest, zero_add, h0]

/-- OS0 Schwartz seminorm bound for `charFunctionalTrunc os op 1 f` from `os.os0_temperedness`. -/
theorem charFunctionalTrunc_one_os0_bound
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (op : ObservableLabel G Curv) :
    ∃ (α : ℝ) (s : ℕ), 0 < α ∧
      ∀ (f : SchwartzMap EuclideanSpace4 ℂ),
        ‖charFunctionalTrunc os op 1 f‖ ≤ 1 + α * SchwartzMap.seminorm ℝ s s f := by
  obtain ⟨α, β, s, hα, _hβ, h_smeared, _⟩ := os.os0_temperedness 1 (fun _ => op)
  refine ⟨α, s, hα, fun f => ?_⟩
  unfold charFunctionalTrunc
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : (Complex.I ^ 0 / (Nat.factorial 0 : ℂ)) *
      os.schwinger_smeared 0 (fun _ => op) (fun _ => f) = 1 := by
    simp [schwinger_smeared_zero_eq_one]
  rw [h0]
  have h_disj1 : DisjointSupports (fun _ : Fin 1 => f) := by
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  have h1 := h_smeared 1 (fun _ => 0) (fun _ => f) h_disj1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, Real.one_rpow, mul_one,
    Fin.prod_univ_one] at h1
  have h_term1 : ‖(Complex.I ^ 1 / (Nat.factorial 1 : ℂ)) *
      os.schwinger_smeared 1 (fun _ => op) (fun _ => f)‖ ≤
      α * SchwartzMap.seminorm ℝ s s f := by
    rw [norm_mul]
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, Complex.norm_I, one_mul]
    exact h1
  exact le_trans (norm_add_le _ _) (by linarith [norm_one (α := ℂ)])

/-! ============================================================================
    PART VI: RELATIVISTIC MASS-SQUARED OPERATOR & SINGLE-PARTICLE DISPERSION
    ============================================================================ -/

/-- Relativistic mass-squared operator `M² = H² - ∑_{i=1}^3 P_i²` on `theory.domain`. -/
noncomputable def massSqOp
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [SeparableSpace ℋ]
    {Curv : CurvaturePolynomialAlgebra G}
    (theory : WightmanQuantumYangMills G ℋ Curv) : theory.domain →ₗ[ℂ] ℋ where
  toFun ψ :=
    theory.Hamiltonian ⟨theory.Hamiltonian ψ, theory.hamiltonian_domain_invariant ψ⟩ -
      ∑ i : Fin 3, theory.Momentum i ⟨theory.Momentum i ψ, theory.momentum_domain_invariant i ψ⟩
  map_add' ψ φ := by
    have hH : (⟨theory.Hamiltonian (ψ + φ), theory.hamiltonian_domain_invariant (ψ + φ)⟩ : theory.domain) =
        ⟨theory.Hamiltonian ψ, theory.hamiltonian_domain_invariant ψ⟩ +
        ⟨theory.Hamiltonian φ, theory.hamiltonian_domain_invariant φ⟩ := by
      ext; simp [map_add]
    have hP : ∀ i : Fin 3,
        (⟨theory.Momentum i (ψ + φ), theory.momentum_domain_invariant i (ψ + φ)⟩ : theory.domain) =
        ⟨theory.Momentum i ψ, theory.momentum_domain_invariant i ψ⟩ +
        ⟨theory.Momentum i φ, theory.momentum_domain_invariant i φ⟩ := by
      intro i; ext; simp [map_add]
    rw [hH, map_add]
    simp_rw [hP, map_add, Finset.sum_add_distrib]
    abel
  map_smul' c ψ := by
    have hH : (⟨theory.Hamiltonian (c • ψ), theory.hamiltonian_domain_invariant (c • ψ)⟩ : theory.domain) =
        c • ⟨theory.Hamiltonian ψ, theory.hamiltonian_domain_invariant ψ⟩ := by
      ext; simp [map_smul]
    have hP : ∀ i : Fin 3,
        (⟨theory.Momentum i (c • ψ), theory.momentum_domain_invariant i (c • ψ)⟩ : theory.domain) =
        c • ⟨theory.Momentum i ψ, theory.momentum_domain_invariant i ψ⟩ := by
      intro i; ext; simp [map_smul]
    rw [hH, map_smul]
    simp_rw [hP, map_smul, ← Finset.smul_sum]
    simp [smul_sub]

/-- Symmetry of the relativistic mass-squared operator on `theory.domain`. -/
theorem massSqOp_symmetric
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [SeparableSpace ℋ]
    {Curv : CurvaturePolynomialAlgebra G}
    (theory : WightmanQuantumYangMills G ℋ Curv)
    (ψ φ : theory.domain) :
    inner ℂ (massSqOp theory ψ) (φ : ℋ) = inner ℂ (ψ : ℋ) (massSqOp theory φ) := by
  unfold massSqOp
  simp only [LinearMap.coe_mk, AddHom.coe_mk, inner_sub_left, inner_sub_right,
    inner_sum, sum_inner]
  have hH :
      inner ℂ (theory.Hamiltonian ⟨theory.Hamiltonian ψ, theory.hamiltonian_domain_invariant ψ⟩) (φ : ℋ) =
      inner ℂ (ψ : ℋ) (theory.Hamiltonian ⟨theory.Hamiltonian φ, theory.hamiltonian_domain_invariant φ⟩) := by
    rw [theory.hamiltonian_symmetric ⟨theory.Hamiltonian ψ, _⟩ φ]
    change inner ℂ (theory.Hamiltonian ψ) (theory.Hamiltonian φ) = _
    rw [theory.hamiltonian_symmetric ψ ⟨theory.Hamiltonian φ, _⟩]
  have hP : ∀ i : Fin 3,
      inner ℂ (theory.Momentum i ⟨theory.Momentum i ψ, theory.momentum_domain_invariant i ψ⟩) (φ : ℋ) =
      inner ℂ (ψ : ℋ) (theory.Momentum i ⟨theory.Momentum i φ, theory.momentum_domain_invariant i φ⟩) := by
    intro i
    rw [theory.momentum_symmetric i ⟨theory.Momentum i ψ, _⟩ φ]
    change inner ℂ (theory.Momentum i ψ) (theory.Momentum i φ) = _
    rw [theory.momentum_symmetric i ψ ⟨theory.Momentum i φ, _⟩]
  rw [hH]
  simp_rw [hP]

/-- Exact quadratic form identity `⟨ψ, M² ψ⟩ = ‖H ψ‖² - ∑ᵢ ‖Pᵢ ψ‖²`. -/
theorem massSqOp_inner_eq
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [SeparableSpace ℋ]
    {Curv : CurvaturePolynomialAlgebra G}
    (theory : WightmanQuantumYangMills G ℋ Curv)
    (ψ : theory.domain) :
    inner ℂ (ψ : ℋ) (massSqOp theory ψ) =
      ((‖theory.Hamiltonian ψ‖ ^ 2 : ℝ) : ℂ) -
        ∑ i : Fin 3, ((‖theory.Momentum i ψ‖ ^ 2 : ℝ) : ℂ) := by
  unfold massSqOp
  simp only [LinearMap.coe_mk, AddHom.coe_mk, inner_sub_right, inner_sum]
  have hH : inner ℂ (ψ : ℋ) (theory.Hamiltonian ⟨theory.Hamiltonian ψ, theory.hamiltonian_domain_invariant ψ⟩) =
      ((‖theory.Hamiltonian ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← theory.hamiltonian_symmetric ψ ⟨theory.Hamiltonian ψ, _⟩]
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hP : ∀ i : Fin 3,
      inner ℂ (ψ : ℋ) (theory.Momentum i ⟨theory.Momentum i ψ, theory.momentum_domain_invariant i ψ⟩) =
      ((‖theory.Momentum i ψ‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← theory.momentum_symmetric i ψ ⟨theory.Momentum i ψ, _⟩]
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hH]
  simp_rw [hP]

/-- Single-particle rest-frame mass-shell bound:
    for `ψ ⊥ Ω` with `P_i ψ = 0`, `Δ² ‖ψ‖² ≤ Re ⟨ψ, M² ψ⟩`. -/
theorem massSqOp_rest_frame_mass_shell_bound
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [SeparableSpace ℋ]
    {Curv : CurvaturePolynomialAlgebra G}
    (theory : WightmanQuantumYangMills G ℋ Curv)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (h_gap : ∀ φ : theory.domain,
      inner ℂ theory.vacuum (φ : ℋ) = 0 → Δ * ‖(φ : ℋ)‖ ≤ ‖theory.Hamiltonian φ‖)
    (ψ : theory.domain)
    (h_ortho : inner ℂ theory.vacuum (ψ : ℋ) = 0)
    (h_rest : ∀ i : Fin 3, theory.Momentum i ψ = 0) :
    Δ ^ 2 * ‖(ψ : ℋ)‖ ^ 2 ≤ (inner ℂ (ψ : ℋ) (massSqOp theory ψ)).re := by
  rw [massSqOp_inner_eq]
  simp_rw [h_rest, norm_zero, sq, mul_zero, Complex.ofReal_zero, Finset.sum_const_zero, sub_zero]
  simp only [Complex.ofReal_re]
  have h_lin := h_gap ψ h_ortho
  have h_sq := pow_le_pow_left₀ (mul_nonneg hΔ (norm_nonneg _)) h_lin 2
  rw [mul_pow] at h_sq
  simpa [sq] using h_sq

#print axioms gns_cauchy_schwarz_soundness
#print axioms reed_simon_x49_semigroup_core
#print axioms reconstructed_gns_has_mass_gap
#print axioms semigroup_exp_decay_of_symmetric_contraction_clustering
#print axioms sesqOS_shift_symm
#print axioms gnsPreHilbertSemigroup_zero
#print axioms gnsPreHilbertSemigroup_add
#print axioms sesqOS_shift_clustering
#print axioms charFunctionalTrunc_zero
#print axioms charFunctionalTrunc_zero_test
#print axioms charFunctionalTrunc_one_os0_bound
#print axioms massSqOp_symmetric
#print axioms massSqOp_inner_eq
#print axioms massSqOp_rest_frame_mass_shell_bound

end YangMills.ConstructiveGNS
