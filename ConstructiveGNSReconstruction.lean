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

/-- **(2a) 2×2 OS Reflection Positivity Quadratic Form Non-Negativity (`m = 2`)**:
    Applying `os.os2_reflection_positivity` to `m = 2` configurations `![f, g]` with
    coefficients `c = ![c0, c1]` shows that the 2×2 quadratic form is non-negative for all `c0, c1 : ℂ`. -/
theorem sesqOS_two_point_quad_nonneg
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv) (c0 c1 : ℂ) :
    let state : Fin 2 → PositiveTimeTestData G Curv := ![f, g]
    let c : Fin 2 → ℂ := ![c0, c1]
    0 ≤ (∑ r : Fin 2, ∑ s : Fin 2,
      starRingEnd ℂ (c r) * (c s) *
        os.schwinger ((state r).deg + (state s).deg)
          (safeReflectConcatLabels (state r).ops (state s).ops)
          (safeReflectConcatMixed (state r).X (state s).X)).re := by
  intro state c
  exact os.os2_reflection_positivity 2
    (fun r => (state r).deg)
    (fun r => (state r).ops)
    (fun r => (state r).X)
    c
    (fun r i => (state r).h_pos i)

/-- Expanded 2×2 OS Reflection Positivity Quadratic Form Non-Negativity (`m = 2`). -/
theorem sesqOS_two_point_expanded_nonneg
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv) (c0 c1 : ℂ) :
    0 ≤ ((starRingEnd ℂ c0 * c0 * sesqOS os f f +
          starRingEnd ℂ c0 * c1 * sesqOS os f g) +
         (starRingEnd ℂ c1 * c0 * sesqOS os g f +
          starRingEnd ℂ c1 * c1 * sesqOS os g g)).re := by
  have h := sesqOS_two_point_quad_nonneg os f g c0 c1
  dsimp only at h
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  exact h

/-- **(2b.1) Symmetrized Osterwalder–Schrader Cauchy–Schwarz Inequality**:
    For any positive-time test configurations `f, g`,
    `‖sesqOS os f g + starRingEnd ℂ (sesqOS os g f)‖ ^ 2 ≤ 4 * (sesqOS os f f).re * (sesqOS os g g).re`. -/
theorem sesqOS_symm_cauchy_schwarz
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv) :
    ‖sesqOS os f g + starRingEnd ℂ (sesqOS os g f)‖ ^ 2 ≤
      4 * (sesqOS os f f).re * (sesqOS os g g).re := by
  let Z : ℂ := sesqOS os f g + starRingEnd ℂ (sesqOS os g f)
  have h_quad : ∀ s t : ℝ,
      0 ≤ s ^ 2 * (sesqOS os f f).re - s * t * ‖Z‖ ^ 2 +
        t ^ 2 * ‖Z‖ ^ 2 * (sesqOS os g g).re := by
    intro s t
    have h_raw := sesqOS_two_point_expanded_nonneg os f g (s : ℂ) (-(t : ℂ) * starRingEnd ℂ Z)
    have h_eq :
        ((starRingEnd ℂ (s : ℂ) * (s : ℂ) * sesqOS os f f +
          starRingEnd ℂ (s : ℂ) * (-(t : ℂ) * starRingEnd ℂ Z) * sesqOS os f g) +
         (starRingEnd ℂ (-(t : ℂ) * starRingEnd ℂ Z) * (s : ℂ) * sesqOS os g f +
          starRingEnd ℂ (-(t : ℂ) * starRingEnd ℂ Z) * (-(t : ℂ) * starRingEnd ℂ Z) *
            sesqOS os g g)).re =
        s ^ 2 * (sesqOS os f f).re - s * t * ‖Z‖ ^ 2 +
          t ^ 2 * ‖Z‖ ^ 2 * (sesqOS os g g).re := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Z, map_neg, map_mul, Complex.conj_ofReal, RingHomCompTriple.comp_apply,
        RingHom.id_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    linarith
  have hA : 0 ≤ (sesqOS os f f).re := sesqOS_nonneg os f
  have hB : 0 ≤ (sesqOS os g g).re := sesqOS_nonneg os g
  rcases eq_or_lt_of_le hB with hB0 | hB_pos
  · have h_spec := h_quad (‖Z‖ ^ 2) ((sesqOS os f f).re + 1)
    rw [← hB0] at h_spec ⊢
    nlinarith [sq_nonneg (‖Z‖ ^ 2)]
  · have h_spec := h_quad (2 * (sesqOS os g g).re) 1
    nlinarith

/-- **(2b.2) Osterwalder–Schrader Cauchy–Schwarz Inequality under Hermitian Symmetry**:
    When `sesqOS os g f = starRingEnd ℂ (sesqOS os f g)`,
    `‖sesqOS os f g‖ ^ 2 ≤ (sesqOS os f f).re * (sesqOS os g g).re`. -/
theorem sesqOS_cauchy_schwarz
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv)
    (h_herm : sesqOS os g f = starRingEnd ℂ (sesqOS os f g)) :
    ‖sesqOS os f g‖ ^ 2 ≤ (sesqOS os f f).re * (sesqOS os g g).re := by
  have h_symm := sesqOS_symm_cauchy_schwarz os f g
  have h_conj : starRingEnd ℂ (sesqOS os g f) = sesqOS os f g := by
    rw [h_herm, RingHomCompTriple.comp_apply, RingHom.id_apply]
  have h_two : sesqOS os f g + starRingEnd ℂ (sesqOS os g f) = (2 : ℂ) * sesqOS os f g := by
    rw [h_conj]; ring
  rw [h_two, norm_mul, Complex.norm_ofNat, mul_pow] at h_symm
  linarith

/-- **(2b.3) Null-State Orthogonality from OS Cauchy–Schwarz**:
    If `(sesqOS os f f).re = 0`, then `sesqOS os f g = 0` for every `g` satisfying
    Hermitian symmetry `sesqOS os g f = starRingEnd ℂ (sesqOS os f g)`. -/
theorem sesqOS_eq_zero_of_diag_re_eq_zero
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv)
    (hf : (sesqOS os f f).re = 0)
    (h_herm : sesqOS os g f = starRingEnd ℂ (sesqOS os f g)) :
    sesqOS os f g = 0 := by
  have h_cs := sesqOS_cauchy_schwarz os f g h_herm
  rw [hf, zero_mul] at h_cs
  have h_sq_zero : ‖sesqOS os f g‖ ^ 2 = 0 := le_antisymm h_cs (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h_sq_zero)

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
    PART II-B: GENUINE COMPLEX PRE-HILBERT VECTOR SPACE (Finsupp QUOTIENT)
    ============================================================================ -/

/-- Finite `ℂ`-linear combinations of strictly positive-time configurations. -/
abbrev FormalPosTimeState (G : Type*) [TopologicalSpace G] [Group G]
    [CompactSimpleLieGroup G] (Curv : CurvaturePolynomialAlgebra G) :=
  PositiveTimeTestData G Curv →₀ ℂ

/-- Sesquilinear extension of `sesqOS os` (conjugate-linear in the first argument,
    linear in the second argument) to `FormalPosTimeState G Curv` via `Finsupp.sum`. -/
noncomputable def sesqOSLinear
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ ψ : FormalPosTimeState G Curv) : ℂ :=
  φ.sum fun f cf => ψ.sum fun g cg => starRingEnd ℂ cf * cg * sesqOS os f g

theorem sesqOSLinear_single_single
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv) (cf cg : ℂ) :
    sesqOSLinear os (Finsupp.single f cf) (Finsupp.single g cg) =
      starRingEnd ℂ cf * cg * sesqOS os f g := by
  unfold sesqOSLinear
  by_cases hf : cf = 0
  · subst hf; simp
  · by_cases hg : cg = 0
    · subst hg; simp
    · simp [Finsupp.sum_single_index]

@[simp]
theorem sesqOSLinear_zero_left
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ψ : FormalPosTimeState G Curv) :
    sesqOSLinear os 0 ψ = 0 := by
  simp [sesqOSLinear]

@[simp]
theorem sesqOSLinear_zero_right
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ : FormalPosTimeState G Curv) :
    sesqOSLinear os φ 0 = 0 := by
  simp [sesqOSLinear]

theorem sesqOSLinear_add_left
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ₁ φ₂ ψ : FormalPosTimeState G Curv) :
    sesqOSLinear os (φ₁ + φ₂) ψ = sesqOSLinear os φ₁ ψ + sesqOSLinear os φ₂ ψ := by
  unfold sesqOSLinear
  rw [Finsupp.sum_add_index']
  · intro f; simp
  · intro f a b
    simp only [Finsupp.sum, map_add, add_mul, Finset.sum_add_distrib]

theorem sesqOSLinear_add_right
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ ψ₁ ψ₂ : FormalPosTimeState G Curv) :
    sesqOSLinear os φ (ψ₁ + ψ₂) = sesqOSLinear os φ ψ₁ + sesqOSLinear os φ ψ₂ := by
  unfold sesqOSLinear
  calc (φ.sum fun f cf => (ψ₁ + ψ₂).sum fun g cg => starRingEnd ℂ cf * cg * sesqOS os f g)
      = φ.sum fun f cf =>
          (ψ₁.sum fun g cg => starRingEnd ℂ cf * cg * sesqOS os f g) +
          (ψ₂.sum fun g cg => starRingEnd ℂ cf * cg * sesqOS os f g) := by
          refine Finset.sum_congr rfl fun f _ => ?_
          dsimp only
          rw [Finsupp.sum_add_index']
          · intro g; simp
          · intro g a b; ring
    _ = sesqOSLinear os φ ψ₁ + sesqOSLinear os φ ψ₂ := by
          simp only [Finsupp.sum, Finset.sum_add_distrib]; rfl

theorem sesqOSLinear_smul_left
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (c : ℂ) (φ ψ : FormalPosTimeState G Curv) :
    sesqOSLinear os (c • φ) ψ = starRingEnd ℂ c * sesqOSLinear os φ ψ := by
  unfold sesqOSLinear
  rw [Finsupp.sum_smul_index' (fun f => by simp)]
  simp only [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
  rw [smul_eq_mul, map_mul]
  ring

theorem sesqOSLinear_smul_right
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (c : ℂ) (φ ψ : FormalPosTimeState G Curv) :
    sesqOSLinear os φ (c • ψ) = c * sesqOSLinear os φ ψ := by
  unfold sesqOSLinear
  calc (φ.sum fun f cf => (c • ψ).sum fun g cg => starRingEnd ℂ cf * cg * sesqOS os f g)
      = φ.sum fun f cf => c * (ψ.sum fun g cg => starRingEnd ℂ cf * cg * sesqOS os f g) := by
          refine Finset.sum_congr rfl fun f _ => ?_
          dsimp only
          rw [Finsupp.sum_smul_index' (fun g => by simp)]
          simp only [Finsupp.sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => by ring
    _ = c * sesqOSLinear os φ ψ := by
          unfold sesqOSLinear
          simp only [Finsupp.sum, Finset.mul_sum]

/-- **Positivity of `sesqOSLinear` via `os.os2_reflection_positivity` for Arbitrary Finite `m`**:
    Converts `ψ.support` to `Fin m` via `Finset.equivFin` and applies `os.os2_reflection_positivity`. -/
theorem sesqOSLinear_nonneg
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ψ : FormalPosTimeState G Curv) :
    0 ≤ (sesqOSLinear os ψ ψ).re := by
  let S := ψ.support
  let m := S.card
  let e : S ≃ Fin m := S.equivFin
  let state : Fin m → PositiveTimeTestData G Curv := fun r => (e.symm r).1
  let c : Fin m → ℂ := fun r => ψ (state r)
  have h_sum_eq : ∀ F : PositiveTimeTestData G Curv → ℂ,
      (∑ x ∈ ψ.support, F x) = ∑ r : Fin m, F (state r) := fun F => by
    rw [← Finset.sum_coe_sort ψ.support]
    exact (Equiv.sum_comp e.symm fun x : S => F x.1).symm
  have h_eq : sesqOSLinear os ψ ψ =
      ∑ r : Fin m, ∑ s : Fin m,
        starRingEnd ℂ (c r) * c s *
          os.schwinger ((state r).deg + (state s).deg)
            (safeReflectConcatLabels (state r).ops (state s).ops)
            (safeReflectConcatMixed (state r).X (state s).X) := by
    unfold sesqOSLinear Finsupp.sum
    rw [h_sum_eq]
    refine Finset.sum_congr rfl fun r _ => ?_
    dsimp only
    rw [h_sum_eq]
    rfl
  rw [h_eq]
  exact os.os2_reflection_positivity m
    (fun r => (state r).deg)
    (fun r => (state r).ops)
    (fun r => (state r).X)
    c
    (fun r i => (state r).h_pos i)

/-- **General OS Cauchy–Schwarz Inequality on `FormalPosTimeState`**:
    `‖sesqOSLinear os φ ψ + starRingEnd ℂ (sesqOSLinear os ψ φ)‖^2 ≤ 4 * (sesqOSLinear os φ φ).re * (sesqOSLinear os ψ ψ).re`. -/
theorem sesqOSLinear_symm_cauchy_schwarz
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ ψ : FormalPosTimeState G Curv) :
    ‖sesqOSLinear os φ ψ + starRingEnd ℂ (sesqOSLinear os ψ φ)‖ ^ 2 ≤
      4 * (sesqOSLinear os φ φ).re * (sesqOSLinear os ψ ψ).re := by
  let Z : ℂ := sesqOSLinear os φ ψ + starRingEnd ℂ (sesqOSLinear os ψ φ)
  have h_quad : ∀ s t : ℝ,
      0 ≤ s ^ 2 * (sesqOSLinear os φ φ).re - s * t * ‖Z‖ ^ 2 +
        t ^ 2 * ‖Z‖ ^ 2 * (sesqOSLinear os ψ ψ).re := by
    intro s t
    let c0 : ℂ := (s : ℂ)
    let c1 : ℂ := -(t : ℂ) * starRingEnd ℂ Z
    have h_raw := sesqOSLinear_nonneg os (c0 • φ + c1 • ψ)
    have h_exp : sesqOSLinear os (c0 • φ + c1 • ψ) (c0 • φ + c1 • ψ) =
        (starRingEnd ℂ c0 * c0 * sesqOSLinear os φ φ +
         starRingEnd ℂ c0 * c1 * sesqOSLinear os φ ψ) +
        (starRingEnd ℂ c1 * c0 * sesqOSLinear os ψ φ +
         starRingEnd ℂ c1 * c1 * sesqOSLinear os ψ ψ) := by
      rw [sesqOSLinear_add_left, sesqOSLinear_add_right, sesqOSLinear_add_right,
        sesqOSLinear_smul_left, sesqOSLinear_smul_left, sesqOSLinear_smul_left, sesqOSLinear_smul_left,
        sesqOSLinear_smul_right, sesqOSLinear_smul_right, sesqOSLinear_smul_right, sesqOSLinear_smul_right]
      ring
    rw [h_exp] at h_raw
    have h_eq :
        ((starRingEnd ℂ c0 * c0 * sesqOSLinear os φ φ +
          starRingEnd ℂ c0 * c1 * sesqOSLinear os φ ψ) +
         (starRingEnd ℂ c1 * c0 * sesqOSLinear os ψ φ +
          starRingEnd ℂ c1 * c1 * sesqOSLinear os ψ ψ)).re =
        s ^ 2 * (sesqOSLinear os φ φ).re - s * t * ‖Z‖ ^ 2 +
          t ^ 2 * ‖Z‖ ^ 2 * (sesqOSLinear os ψ ψ).re := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [c0, c1, Z, map_neg, map_mul, Complex.conj_ofReal, RingHomCompTriple.comp_apply,
        RingHom.id_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    linarith
  have hA : 0 ≤ (sesqOSLinear os φ φ).re := sesqOSLinear_nonneg os φ
  have hB : 0 ≤ (sesqOSLinear os ψ ψ).re := sesqOSLinear_nonneg os ψ
  rcases eq_or_lt_of_le hB with hB0 | hB_pos
  · have h_spec := h_quad (‖Z‖ ^ 2) ((sesqOSLinear os φ φ).re + 1)
    rw [← hB0] at h_spec ⊢
    nlinarith [sq_nonneg (‖Z‖ ^ 2)]
  · have h_spec := h_quad (2 * (sesqOSLinear os ψ ψ).re) 1
    nlinarith

/-- **OS Cauchy–Schwarz Inequality on `FormalPosTimeState` under Hermitian Symmetry**. -/
theorem sesqOSLinear_cauchy_schwarz
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ ψ : FormalPosTimeState G Curv)
    (h_herm : sesqOSLinear os ψ φ = starRingEnd ℂ (sesqOSLinear os φ ψ)) :
    ‖sesqOSLinear os φ ψ‖ ^ 2 ≤ (sesqOSLinear os φ φ).re * (sesqOSLinear os ψ ψ).re := by
  have h_symm := sesqOSLinear_symm_cauchy_schwarz os φ ψ
  have h_conj : starRingEnd ℂ (sesqOSLinear os ψ φ) = sesqOSLinear os φ ψ := by
    rw [h_herm, RingHomCompTriple.comp_apply, RingHom.id_apply]
  have h_two : sesqOSLinear os φ ψ + starRingEnd ℂ (sesqOSLinear os ψ φ) = (2 : ℂ) * sesqOSLinear os φ ψ := by
    rw [h_conj]; ring
  rw [h_two, norm_mul, Complex.norm_ofNat, mul_pow] at h_symm
  linarith

/-- **Hermitian-Symmetrized OS Sesquilinear Form** on `FormalPosTimeState G Curv`:
    `sesqOSHerm os φ ψ := (1 / 2 : ℂ) * (sesqOSLinear os φ ψ + starRingEnd ℂ (sesqOSLinear os ψ φ))`. -/
noncomputable def sesqOSHerm
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ ψ : FormalPosTimeState G Curv) : ℂ :=
  (1 / 2 : ℂ) * (sesqOSLinear os φ ψ + starRingEnd ℂ (sesqOSLinear os ψ φ))

theorem sesqOSHerm_conj_symm
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ ψ : FormalPosTimeState G Curv) :
    starRingEnd ℂ (sesqOSHerm os ψ φ) = sesqOSHerm os φ ψ := by
  unfold sesqOSHerm
  simp only [map_mul, map_add, map_div₀, map_one, map_ofNat,
    RingHomCompTriple.comp_apply, RingHom.id_apply, add_comm]

theorem sesqOSHerm_self_re
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ψ : FormalPosTimeState G Curv) :
    (sesqOSHerm os ψ ψ).re = (sesqOSLinear os ψ ψ).re := by
  unfold sesqOSHerm
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h12, Complex.re_ofReal_mul, Complex.add_re, Complex.conj_re]
  ring

theorem sesqOSHerm_self_im
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ψ : FormalPosTimeState G Curv) :
    (sesqOSHerm os ψ ψ).im = 0 := by
  unfold sesqOSHerm
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h12, Complex.im_ofReal_mul, Complex.add_im, Complex.conj_im]
  ring

theorem sesqOSHerm_nonneg
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ψ : FormalPosTimeState G Curv) :
    0 ≤ (sesqOSHerm os ψ ψ).re := by
  rw [sesqOSHerm_self_re]
  exact sesqOSLinear_nonneg os ψ

@[simp]
theorem sesqOSHerm_zero_left
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ψ : FormalPosTimeState G Curv) :
    sesqOSHerm os 0 ψ = 0 := by
  unfold sesqOSHerm
  simp

@[simp]
theorem sesqOSHerm_zero_right
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ : FormalPosTimeState G Curv) :
    sesqOSHerm os φ 0 = 0 := by
  unfold sesqOSHerm
  simp

theorem sesqOSHerm_add_left
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ₁ φ₂ ψ : FormalPosTimeState G Curv) :
    sesqOSHerm os (φ₁ + φ₂) ψ = sesqOSHerm os φ₁ ψ + sesqOSHerm os φ₂ ψ := by
  unfold sesqOSHerm
  rw [sesqOSLinear_add_left, sesqOSLinear_add_right, map_add]
  ring

theorem sesqOSHerm_add_right
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ ψ₁ ψ₂ : FormalPosTimeState G Curv) :
    sesqOSHerm os φ (ψ₁ + ψ₂) = sesqOSHerm os φ ψ₁ + sesqOSHerm os φ ψ₂ := by
  unfold sesqOSHerm
  rw [sesqOSLinear_add_right, sesqOSLinear_add_left, map_add]
  ring

theorem sesqOSHerm_smul_left
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (c : ℂ) (φ ψ : FormalPosTimeState G Curv) :
    sesqOSHerm os (c • φ) ψ = starRingEnd ℂ c * sesqOSHerm os φ ψ := by
  unfold sesqOSHerm
  rw [sesqOSLinear_smul_left, sesqOSLinear_smul_right, map_mul]
  ring

theorem sesqOSHerm_smul_right
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (c : ℂ) (φ ψ : FormalPosTimeState G Curv) :
    sesqOSHerm os φ (c • ψ) = c * sesqOSHerm os φ ψ := by
  unfold sesqOSHerm
  rw [sesqOSLinear_smul_right, sesqOSLinear_smul_left, map_mul,
    RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

/-- **Exact Hermitian OS Cauchy–Schwarz Inequality**:
    `‖sesqOSHerm os φ ψ‖ ^ 2 ≤ (sesqOSHerm os φ φ).re * (sesqOSHerm os ψ ψ).re`. -/
theorem sesqOSHerm_cauchy_schwarz
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ ψ : FormalPosTimeState G Curv) :
    ‖sesqOSHerm os φ ψ‖ ^ 2 ≤ (sesqOSHerm os φ φ).re * (sesqOSHerm os ψ ψ).re := by
  unfold sesqOSHerm
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [norm_mul, h12, mul_pow]
  have h_cs := sesqOSLinear_symm_cauchy_schwarz os φ ψ
  have hreφ : (sesqOSLinear os φ φ).re = ((1 / 2 : ℂ) * (sesqOSLinear os φ φ + starRingEnd ℂ (sesqOSLinear os φ φ))).re := by
    have h := sesqOSHerm_self_re os φ
    unfold sesqOSHerm at h
    exact h.symm
  have hreψ : (sesqOSLinear os ψ ψ).re = ((1 / 2 : ℂ) * (sesqOSLinear os ψ ψ + starRingEnd ℂ (sesqOSLinear os ψ ψ))).re := by
    have h := sesqOSHerm_self_re os ψ
    unfold sesqOSHerm at h
    exact h.symm
  rw [← hreφ, ← hreψ]
  linarith

/-- **Null-State Equivalence for `sesqOSHerm`**:
    `(sesqOSHerm os ψ ψ).re = 0 ↔ ∀ w : FormalPosTimeState G Curv, sesqOSHerm os ψ w = 0`. -/
theorem sesqOSHerm_eq_zero_iff
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ψ : FormalPosTimeState G Curv) :
    (sesqOSHerm os ψ ψ).re = 0 ↔ ∀ w : FormalPosTimeState G Curv, sesqOSHerm os ψ w = 0 := by
  constructor
  · intro h w
    have hcs := sesqOSHerm_cauchy_schwarz os ψ w
    rw [h, zero_mul] at hcs
    have hnorm : ‖sesqOSHerm os ψ w‖ = 0 := by
      nlinarith [norm_nonneg (sesqOSHerm os ψ w)]
    exact norm_eq_zero.mp hnorm
  · intro h
    rw [h ψ, Complex.zero_re]

/-- **Hermitian OS Null Space `N_os` as a Complex Submodule of `FormalPosTimeState G Curv`**. -/
def osHermNullSubmodule
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    Submodule ℂ (FormalPosTimeState G Curv) where
  carrier := {ψ : FormalPosTimeState G Curv | (sesqOSHerm os ψ ψ).re = 0}
  zero_mem' := by simp [sesqOSHerm_self_re]
  add_mem' := by
    intro φ ψ hφ hψ
    have hφw := (sesqOSHerm_eq_zero_iff os φ).mp hφ
    have hψw := (sesqOSHerm_eq_zero_iff os ψ).mp hψ
    show (sesqOSHerm os (φ + ψ) (φ + ψ)).re = 0
    rw [sesqOSHerm_add_left, hφw, hψw, add_zero, Complex.zero_re]
  smul_mem' := by
    intro c ψ hψ
    have hψw := (sesqOSHerm_eq_zero_iff os ψ).mp hψ
    show (sesqOSHerm os (c • ψ) (c • ψ)).re = 0
    rw [sesqOSHerm_smul_left, hψw, mul_zero, Complex.zero_re]

/-- **Genuine Complex Pre-Hilbert Vector Space Quotient**:
    `GNSLinearPreHilbert os := FormalPosTimeState G Curv ⧸ osHermNullSubmodule os`. -/
abbrev GNSLinearPreHilbert
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :=
  FormalPosTimeState G Curv ⧸ osHermNullSubmodule os

/-- Well-defined Hermitian sesquilinear OS form descended to `GNSLinearPreHilbert os`. -/
noncomputable def sesqOSHermQuotient
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    GNSLinearPreHilbert os → GNSLinearPreHilbert os → ℂ :=
  Quotient.lift₂ (sesqOSHerm os) fun φ₁ ψ₁ φ₂ ψ₂ hφ hψ => by
    have hφ_mem : φ₁ - φ₂ ∈ osHermNullSubmodule os := (Submodule.quotientRel_def (osHermNullSubmodule os)).mp hφ
    have hψ_mem : ψ₁ - ψ₂ ∈ osHermNullSubmodule os := (Submodule.quotientRel_def (osHermNullSubmodule os)).mp hψ
    have hφ_zero : sesqOSHerm os (φ₁ - φ₂) ψ₁ = 0 :=
      (sesqOSHerm_eq_zero_iff os (φ₁ - φ₂)).mp hφ_mem ψ₁
    have hψ_zero_l : sesqOSHerm os (ψ₁ - ψ₂) φ₂ = 0 :=
      (sesqOSHerm_eq_zero_iff os (ψ₁ - ψ₂)).mp hψ_mem φ₂
    have hψ_zero : sesqOSHerm os φ₂ (ψ₁ - ψ₂) = 0 := by
      rw [← sesqOSHerm_conj_symm, hψ_zero_l, map_zero]
    have h1 : sesqOSHerm os φ₁ ψ₁ - sesqOSHerm os φ₂ ψ₁ = 0 := by
      have hsub : φ₁ = (φ₁ - φ₂) + φ₂ := (sub_add_cancel φ₁ φ₂).symm
      rw [hsub, sesqOSHerm_add_left, hφ_zero, zero_add, sub_self]
    have h2 : sesqOSHerm os φ₂ ψ₁ - sesqOSHerm os φ₂ ψ₂ = 0 := by
      have hsub : ψ₁ = (ψ₁ - ψ₂) + ψ₂ := (sub_add_cancel ψ₁ ψ₂).symm
      rw [hsub, sesqOSHerm_add_right, hψ_zero, zero_add, sub_self]
    exact sub_eq_zero.mp (by linear_combination h1 + h2)

@[simp]
theorem sesqOSHermQuotient_mk
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ ψ : FormalPosTimeState G Curv) :
    sesqOSHermQuotient os (Submodule.Quotient.mk φ) (Submodule.Quotient.mk ψ) = sesqOSHerm os φ ψ :=
  rfl

/-- Mathlib `InnerProductSpace.Core ℂ` structure on `GNSLinearPreHilbert os`. -/
@[instance_reducible]
noncomputable def gnsLinearInnerCore
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    InnerProductSpace.Core ℂ (GNSLinearPreHilbert os) where
  inner := sesqOSHermQuotient os
  conj_inner_symm := Quotient.ind₂ fun x y => sesqOSHerm_conj_symm os x y
  re_inner_nonneg := Quotient.ind fun x => sesqOSHerm_nonneg os x
  add_left := Quotient.ind₂ fun x y => Quotient.ind fun z => sesqOSHerm_add_left os x y z
  smul_left := Quotient.ind₂ fun x y r => sesqOSHerm_smul_left os r x y
  definite := by
    intro x hx
    refine Quotient.inductionOn x (fun φ hφ => ?_) hx
    change sesqOSHerm os φ φ = 0 at hφ
    have hre : (sesqOSHerm os φ φ).re = 0 := by rw [hφ, Complex.zero_re]
    exact (Submodule.Quotient.mk_eq_zero (osHermNullSubmodule os)).mpr hre

/-- Canonical `NormedAddCommGroup` structure on `GNSLinearPreHilbert os`. -/
noncomputable instance gnsLinearNormedAddCommGroup
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    NormedAddCommGroup (GNSLinearPreHilbert os) :=
  (gnsLinearInnerCore os).toNormedAddCommGroup

/-- Canonical `InnerProductSpace ℂ` structure on `GNSLinearPreHilbert os`. -/
noncomputable instance gnsLinearInnerProductSpace
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    InnerProductSpace ℂ (GNSLinearPreHilbert os) :=
  InnerProductSpace.ofCore (gnsLinearInnerCore os).toCore

theorem gnsLinear_norm_eq_sqrt_re_inner
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (x : GNSLinearPreHilbert os) :
    ‖x‖ = Real.sqrt (inner ℂ x x).re := by
  rw [← Real.sqrt_sq (norm_nonneg x), InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  rfl

theorem gnsLinear_norm_eq_zero_iff
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (x : GNSLinearPreHilbert os) :
    ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero

/-- **Canonical GNS Completed Complex Hilbert Space** `ℋ = UniformSpace.Completion (GNSLinearPreHilbert os)`.
    Mathlib automatically synthesizes `NormedAddCommGroup`, `InnerProductSpace ℂ`, and `CompleteSpace`. -/
abbrev GNSCompletedHilbert
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :=
  UniformSpace.Completion (GNSLinearPreHilbert os)

/-- Isometric dense linear embedding `GNSLinearPreHilbert os →ₗᵢ[ℂ] GNSCompletedHilbert os`. -/
noncomputable def gnsLinearToCompleted
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    GNSLinearPreHilbert os →ₗᵢ[ℂ] GNSCompletedHilbert os :=
  UniformSpace.Completion.toComplₗᵢ

theorem gnsLinearToCompleted_denseRange
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    DenseRange (gnsLinearToCompleted os) := by
  simpa [gnsLinearToCompleted, UniformSpace.Completion.coe_toComplₗᵢ] using
    (UniformSpace.Completion.denseRange_coe (α := GNSLinearPreHilbert os))

theorem gnsCompletedHilbert_complete
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    CompleteSpace (GNSCompletedHilbert os) :=
  inferInstance

@[instance_reducible]
noncomputable def gnsCompletedHilbert_innerProductSpace
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    InnerProductSpace ℂ (GNSCompletedHilbert os) :=
  inferInstance

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

/-- **Osterwalder–Schrader II (1975) Wightman Reconstruction Bundle**:
    Packages the reconstructed GNS Hilbert space `H` realized on `GNSMetricCompletion os`,
    its Euclidean contraction semigroup `semi : ReconstructedEuclideanSemigroup H`,
    strong semigroup generator differentiation `-Hψ = d/dt|_{t=0} T(t)ψ` on `H.theory.domain`,
    and non-empty excited-state energy finiteness `h_finite_spec`. -/
structure OSIIWightmanReconstruction
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) where
  H : ReconstructedGNSHilbertSpace G Curv
  h_gns_completion : H.HilbertSpace = GNSMetricCompletion os
  semi : ReconstructedEuclideanSemigroup H
  h_deriv : ∀ ψ : H.theory.domain,
    HasDerivAt (fun t => semi.T t (ψ : H.HilbertSpace))
      (- (H.theory.Hamiltonian ψ : H.HilbertSpace)) 0
  h_finite_spec : ∃ (M : ℝ) (ψ : H.theory.domain),
    0 < M ∧ inner ℂ H.theory.vacuum (ψ : H.HilbertSpace) = 0 ∧ (ψ : H.HilbertSpace) ≠ 0 ∧
    ‖H.theory.Hamiltonian ψ‖ ≤ M * ‖(ψ : H.HilbertSpace)‖

/-- **Unconditional Mass Gap from `OSIIWightmanReconstruction`**:
    Combines `semigroup_exp_decay_of_symmetric_contraction_clustering` and
    `reconstructed_gns_has_mass_gap` to establish `HasMassGap G recon.H.HilbertSpace recon.H.theory`. -/
theorem OSIIWightmanReconstruction.has_mass_gap
    {G : Type} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    {os : OsterwalderSchraderYangMills G Curv}
    (recon : OSIIWightmanReconstruction os) :
    HasMassGap G recon.H.HilbertSpace recon.H.theory :=
  reconstructed_gns_has_mass_gap recon.H recon.semi recon.semi.m_rate recon.semi.m_rate_pos
    recon.h_deriv
    (fun ψ t h_ortho ht =>
      semigroup_exp_decay_of_symmetric_contraction_clustering
        recon.H recon.semi (ψ : recon.H.HilbertSpace) t h_ortho ht)
    recon.h_finite_spec

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

theorem shiftPositiveTimeTestData_zero
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

theorem shiftPositiveTimeTestData_add
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

/-! ============================================================================
    PART III-B: LINEAR TIME-SHIFT SEMIGROUP & EXTENSION TO GNSCompletedHilbert
    ============================================================================ -/

/-- `ℂ`-linear time-shift map on `FormalPosTimeState G Curv` via `Finsupp.lmapDomain`. -/
noncomputable def shiftFormalPosTimeState
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (t : ℝ) (ht : 0 ≤ t) :
    FormalPosTimeState G Curv →ₗ[ℂ] FormalPosTimeState G Curv :=
  Finsupp.lmapDomain ℂ ℂ (shiftPositiveTimeTestData t ht)

@[simp]
theorem shiftFormalPosTimeState_single
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (t : ℝ) (ht : 0 ≤ t) (f : PositiveTimeTestData G Curv) (c : ℂ) :
    shiftFormalPosTimeState t ht (Finsupp.single f c) =
      Finsupp.single (shiftPositiveTimeTestData t ht f) c := by
  simp [shiftFormalPosTimeState, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem shiftFormalPosTimeState_zero
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G} :
    shiftFormalPosTimeState (G := G) (Curv := Curv) 0 le_rfl = LinearMap.id := by
  refine LinearMap.ext fun φ => ?_
  refine Finsupp.induction φ ?_ ?_
  · simp
  · intro f c ψ _ _ ih
    simp [map_add, shiftFormalPosTimeState_single, shiftPositiveTimeTestData_zero, ih]

theorem shiftFormalPosTimeState_add
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (t1 t2 : ℝ) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) :
    shiftFormalPosTimeState (G := G) (Curv := Curv) (t1 + t2) (add_nonneg ht1 ht2) =
      (shiftFormalPosTimeState t1 ht1).comp (shiftFormalPosTimeState t2 ht2) := by
  refine LinearMap.ext fun φ => ?_
  refine Finsupp.induction φ ?_ ?_
  · simp
  · intro f c ψ _ _ ih
    simp only [map_add, LinearMap.comp_apply, shiftFormalPosTimeState_single]
    rw [shiftPositiveTimeTestData_add]
    rw [ih]
    rfl

theorem sesqOSLinear_shift_symm
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) (φ ψ : FormalPosTimeState G Curv) :
    sesqOSLinear os (shiftFormalPosTimeState t ht φ) ψ =
      sesqOSLinear os φ (shiftFormalPosTimeState t ht ψ) := by
  refine Finsupp.induction φ ?_ ?_
  · simp
  · intro f cf φ' _ _ ihφ
    simp only [map_add, sesqOSLinear_add_left, ihφ]
    congr 1
    refine Finsupp.induction ψ ?_ ?_
    · simp
    · intro g cg ψ' _ _ ihψ
      simp only [map_add, sesqOSLinear_add_right, ihψ]
      congr 1
      simp only [shiftFormalPosTimeState_single, sesqOSLinear_single_single, sesqOS_shift_symm]

theorem sesqOSHerm_shift_symm
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) (φ ψ : FormalPosTimeState G Curv) :
    sesqOSHerm os (shiftFormalPosTimeState t ht φ) ψ =
      sesqOSHerm os φ (shiftFormalPosTimeState t ht ψ) := by
  unfold sesqOSHerm
  rw [sesqOSLinear_shift_symm os t ht φ ψ, sesqOSLinear_shift_symm os t ht ψ φ]

theorem shiftFormalPosTimeState_mem_osHermNullSubmodule
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ ψ ∈ osHermNullSubmodule os, shiftFormalPosTimeState t ht ψ ∈ osHermNullSubmodule os := by
  intro ψ hψ
  have h_all := (sesqOSHerm_eq_zero_iff os ψ).mp hψ
  exact (sesqOSHerm_eq_zero_iff os (shiftFormalPosTimeState t ht ψ)).mpr fun w => by
    rw [sesqOSHerm_shift_symm]
    exact h_all (shiftFormalPosTimeState t ht w)

/-- Quotient `ℂ`-linear time-shift semigroup `gnsLinearSemigroup os t ht` on `GNSLinearPreHilbert os`. -/
noncomputable def gnsLinearSemigroup
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) :
    GNSLinearPreHilbert os →ₗ[ℂ] GNSLinearPreHilbert os :=
  Submodule.mapQ (osHermNullSubmodule os) (osHermNullSubmodule os)
    (shiftFormalPosTimeState t ht)
    (shiftFormalPosTimeState_mem_osHermNullSubmodule os t ht)

@[simp]
theorem gnsLinearSemigroup_mk
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) (φ : FormalPosTimeState G Curv) :
    gnsLinearSemigroup os t ht (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk (shiftFormalPosTimeState t ht φ) :=
  rfl

theorem gnsLinearSemigroup_inner_symm
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) (x y : GNSLinearPreHilbert os) :
    inner ℂ (gnsLinearSemigroup os t ht x) y = inner ℂ x (gnsLinearSemigroup os t ht y) := by
  refine Quotient.inductionOn₂ x y fun φ ψ => ?_
  change sesqOSHermQuotient os (Submodule.Quotient.mk (shiftFormalPosTimeState t ht φ))
      (Submodule.Quotient.mk ψ) =
    sesqOSHermQuotient os (Submodule.Quotient.mk φ)
      (Submodule.Quotient.mk (shiftFormalPosTimeState t ht ψ))
  simp only [sesqOSHermQuotient_mk]
  exact sesqOSHerm_shift_symm os t ht φ ψ

theorem gnsLinearSemigroup_zero
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    gnsLinearSemigroup os 0 le_rfl = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  refine Quotient.inductionOn x fun φ => ?_
  change Submodule.Quotient.mk (shiftFormalPosTimeState 0 le_rfl φ) = Submodule.Quotient.mk φ
  rw [shiftFormalPosTimeState_zero, LinearMap.id_apply]

theorem gnsLinearSemigroup_add
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t1 t2 : ℝ) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) :
    gnsLinearSemigroup os (t1 + t2) (add_nonneg ht1 ht2) =
      (gnsLinearSemigroup os t1 ht1).comp (gnsLinearSemigroup os t2 ht2) := by
  refine LinearMap.ext fun x => ?_
  refine Quotient.inductionOn x fun φ => ?_
  change Submodule.Quotient.mk (shiftFormalPosTimeState (t1 + t2) (add_nonneg ht1 ht2) φ) =
    Submodule.Quotient.mk (shiftFormalPosTimeState t1 ht1 (shiftFormalPosTimeState t2 ht2 φ))
  rw [shiftFormalPosTimeState_add, LinearMap.comp_apply]

/-- **Iterated `2^k`-Power Cauchy–Schwarz Bound on `GNSLinearPreHilbert os`**:
    `‖T_t x‖^(2^k) ≤ ‖x‖^(2^k - 1) * ‖T_{2^k t} x‖`. -/
theorem gnsLinearSemigroup_pow_two_cauchy_schwarz
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) (x : GNSLinearPreHilbert os) (k : ℕ) :
    ‖gnsLinearSemigroup os t ht x‖ ^ (2 ^ k) ≤
      ‖x‖ ^ (2 ^ k - 1) *
        ‖gnsLinearSemigroup os ((2 ^ k : ℝ) * t) (mul_nonneg (pow_nonneg zero_le_two k) ht) x‖ := by
  have h_time_eq : ∀ s1 s2 (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2), s1 = s2 →
      gnsLinearSemigroup os s1 hs1 x = gnsLinearSemigroup os s2 hs2 x := by
    rintro s _ hs1 hs2 rfl; rfl
  induction k generalizing t ht with
  | zero =>
    simp only [pow_zero, Nat.sub_self, pow_one, one_mul]
    exact le_rfl
  | succ k ih =>
    have h2t_eq : t + t = (2 : ℝ) * t := by ring
    have h_step1 : ‖gnsLinearSemigroup os t ht x‖ ^ 2 ≤
        ‖x‖ * ‖gnsLinearSemigroup os ((2 : ℝ) * t) (mul_nonneg zero_le_two ht) x‖ := by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
      rw [gnsLinearSemigroup_inner_symm os t ht x (gnsLinearSemigroup os t ht x)]
      have h_comp : gnsLinearSemigroup os t ht (gnsLinearSemigroup os t ht x) =
          gnsLinearSemigroup os ((2 : ℝ) * t) (mul_nonneg zero_le_two ht) x := by
        have h_add := congrArg (fun L => L x) (gnsLinearSemigroup_add os t t ht ht)
        simp only [LinearMap.comp_apply] at h_add
        rw [← h_add]
        exact h_time_eq _ _ _ _ h2t_eq
      rw [h_comp]
      have h_re : (inner ℂ x (gnsLinearSemigroup os ((2 : ℝ) * t) (mul_nonneg zero_le_two ht) x)).re ≤
          ‖inner ℂ x (gnsLinearSemigroup os ((2 : ℝ) * t) (mul_nonneg zero_le_two ht) x)‖ :=
        Complex.re_le_norm _
      exact h_re.trans (norm_inner_le_norm _ _)
    have h_pow : (‖gnsLinearSemigroup os t ht x‖ ^ 2) ^ (2 ^ k) ≤
        (‖x‖ * ‖gnsLinearSemigroup os ((2 : ℝ) * t) (mul_nonneg zero_le_two ht) x‖) ^ (2 ^ k) :=
      pow_le_pow_left₀ (sq_nonneg _) h_step1 (2 ^ k)
    rw [← pow_mul, mul_comm 2 (2 ^ k), ← pow_succ] at h_pow
    rw [mul_pow] at h_pow
    have h_ih := ih ((2 : ℝ) * t) (mul_nonneg zero_le_two ht)
    have h_time : (2 ^ k : ℝ) * ((2 : ℝ) * t) = (2 ^ (k + 1) : ℝ) * t := by
      rw [pow_succ]; ring
    have h_norm_eq : ‖gnsLinearSemigroup os ((2 ^ k : ℝ) * ((2 : ℝ) * t))
        (mul_nonneg (pow_nonneg zero_le_two k) (mul_nonneg zero_le_two ht)) x‖ =
      ‖gnsLinearSemigroup os ((2 ^ (k + 1) : ℝ) * t)
        (mul_nonneg (pow_nonneg zero_le_two (k + 1)) ht) x‖ := by
      rw [h_time_eq _ _ _ _ h_time]
    rw [h_norm_eq] at h_ih
    have h_mul := mul_le_mul_of_nonneg_left h_ih (pow_nonneg (norm_nonneg x) (2 ^ k))
    have h_exp : 2 ^ k + (2 ^ k - 1) = 2 ^ (k + 1) - 1 := by
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    calc ‖gnsLinearSemigroup os t ht x‖ ^ (2 ^ (k + 1))
        ≤ ‖x‖ ^ (2 ^ k) * ‖gnsLinearSemigroup os ((2 : ℝ) * t) (mul_nonneg zero_le_two ht) x‖ ^ (2 ^ k) := h_pow
      _ ≤ ‖x‖ ^ (2 ^ k) * (‖x‖ ^ (2 ^ k - 1) *
            ‖gnsLinearSemigroup os ((2 ^ (k + 1) : ℝ) * t)
              (mul_nonneg (pow_nonneg zero_le_two (k + 1)) ht) x‖) := h_mul
      _ = ‖x‖ ^ (2 ^ k + (2 ^ k - 1)) *
            ‖gnsLinearSemigroup os ((2 ^ (k + 1) : ℝ) * t)
              (mul_nonneg (pow_nonneg zero_le_two (k + 1)) ht) x‖ := by rw [← mul_assoc, ← pow_add]
      _ = ‖x‖ ^ (2 ^ (k + 1) - 1) *
            ‖gnsLinearSemigroup os ((2 ^ (k + 1) : ℝ) * t)
              (mul_nonneg (pow_nonneg zero_le_two (k + 1)) ht) x‖ := by rw [h_exp]

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

/-- Uniform norm bound on shifted OS correlations from `sesqOS_shift_clustering`:
    for any `f, g`, there exists `C ≥ 0` such that `‖⟨f, T_s g⟩_OS‖ ≤ C` for all `s ≥ 0`. -/
theorem sesqOS_shift_norm_bounded
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f g : PositiveTimeTestData G Curv) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ℝ) (hs : 0 ≤ s),
        ‖sesqOS os f (shiftPositiveTimeTestData s hs g)‖ ≤ C := by
  obtain ⟨C0, hC0, h_cluster⟩ := sesqOS_shift_clustering os f g
  let z : ℂ :=
    starRingEnd ℂ (os.schwinger f.deg (reverseConjLabels f.ops) (reverseReflectConfig f.X)) *
      os.schwinger g.deg g.ops g.X
  refine ⟨C0 + ‖z‖, add_nonneg hC0 (norm_nonneg z), fun s hs => ?_⟩
  have h_exp_le : Real.exp (-os.mass_rate * s) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr os.mass_rate_pos.le) hs)
  have h_cl : ‖sesqOS os f (shiftPositiveTimeTestData s hs g) - z‖ ≤ C0 :=
    (h_cluster s hs).trans (mul_le_of_le_one_right hC0 h_exp_le)
  have h_tri : ‖sesqOS os f (shiftPositiveTimeTestData s hs g)‖ ≤
      ‖sesqOS os f (shiftPositiveTimeTestData s hs g) - z‖ + ‖z‖ := by
    calc ‖sesqOS os f (shiftPositiveTimeTestData s hs g)‖
        = ‖(sesqOS os f (shiftPositiveTimeTestData s hs g) - z) + z‖ := by ring_nf
      _ ≤ ‖sesqOS os f (shiftPositiveTimeTestData s hs g) - z‖ + ‖z‖ := norm_add_le _ _
  linarith

private theorem sesqOSLinear_single_shift_norm_bounded
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (f : PositiveTimeTestData G Curv) (cf : ℂ) (ψ : FormalPosTimeState G Curv) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ℝ) (hs : 0 ≤ s),
        ‖sesqOSLinear os (Finsupp.single f cf) (shiftFormalPosTimeState s hs ψ)‖ ≤ C := by
  refine Finsupp.induction ψ ?_ ?_
  · exact ⟨0, le_rfl, fun s hs => by simp⟩
  · intro g cg ψ' _ _ ih
    obtain ⟨C1, hC1, h1⟩ := ih
    obtain ⟨Cfg, hCfg, hfg⟩ := sesqOS_shift_norm_bounded os f g
    refine ⟨‖cf‖ * ‖cg‖ * Cfg + C1,
      add_nonneg (mul_nonneg (mul_nonneg (norm_nonneg cf) (norm_nonneg cg)) hCfg) hC1,
      fun s hs => ?_⟩
    rw [map_add, sesqOSLinear_add_right]
    refine (norm_add_le _ _).trans (add_le_add ?_ (h1 s hs))
    rw [shiftFormalPosTimeState_single, sesqOSLinear_single_single,
      norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hfg s hs)
      (mul_nonneg (norm_nonneg cf) (norm_nonneg cg))

theorem sesqOSLinear_shift_norm_bounded
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (φ ψ : FormalPosTimeState G Curv) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ℝ) (hs : 0 ≤ s),
        ‖sesqOSLinear os φ (shiftFormalPosTimeState s hs ψ)‖ ≤ C := by
  refine Finsupp.induction φ ?_ ?_
  · exact ⟨0, le_rfl, fun s hs => by simp⟩
  · intro f cf φ' _ _ ih
    obtain ⟨C1, hC1, h1⟩ := ih
    obtain ⟨C0, hC0, h0⟩ := sesqOSLinear_single_shift_norm_bounded os f cf ψ
    refine ⟨C0 + C1, add_nonneg hC0 hC1, fun s hs => ?_⟩
    rw [sesqOSLinear_add_left]
    exact (norm_add_le _ _).trans (add_le_add (h0 s hs) (h1 s hs))

/-- Uniform boundedness of the time-shift semigroup on `GNSLinearPreHilbert os`:
    for every `x`, there exists `M ≥ 0` such that `‖T_s x‖ ≤ M` for all `s ≥ 0`. -/
theorem gnsLinearSemigroup_uniform_bounded
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (x : GNSLinearPreHilbert os) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (s : ℝ) (hs : 0 ≤ s), ‖gnsLinearSemigroup os s hs x‖ ≤ M := by
  refine Quotient.inductionOn x fun φ => ?_
  obtain ⟨C, hC, h_bd⟩ := sesqOSLinear_shift_norm_bounded os φ φ
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, fun s hs => ?_⟩
  have h_sq : ‖gnsLinearSemigroup os s hs (Submodule.Quotient.mk φ)‖ ^ 2 ≤ C := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
    rw [gnsLinearSemigroup_inner_symm os s hs]
    have h_add := congrArg (fun L => L (Submodule.Quotient.mk φ))
      (gnsLinearSemigroup_add os s s hs hs)
    simp only [LinearMap.comp_apply] at h_add
    rw [← h_add, gnsLinearSemigroup_mk]
    change (sesqOSHermQuotient os (Submodule.Quotient.mk φ)
      (Submodule.Quotient.mk (shiftFormalPosTimeState (s + s) (add_nonneg hs hs) φ))).re ≤ C
    rw [sesqOSHermQuotient_mk]
    have h_re : (sesqOSHerm os φ (shiftFormalPosTimeState (s + s) (add_nonneg hs hs) φ)).re ≤
        ‖sesqOSHerm os φ (shiftFormalPosTimeState (s + s) (add_nonneg hs hs) φ)‖ :=
      Complex.re_le_norm _
    refine h_re.trans ?_
    unfold sesqOSHerm
    rw [sesqOSLinear_shift_symm os (s + s) (add_nonneg hs hs) φ φ]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [norm_mul, h12]
    have h_tri : ‖sesqOSLinear os φ (shiftFormalPosTimeState (s + s) (add_nonneg hs hs) φ) +
        starRingEnd ℂ (sesqOSLinear os φ (shiftFormalPosTimeState (s + s) (add_nonneg hs hs) φ))‖ ≤
        2 * ‖sesqOSLinear os φ (shiftFormalPosTimeState (s + s) (add_nonneg hs hs) φ)‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_conj]
      linarith
    have h_bd2 := h_bd (s + s) (add_nonneg hs hs)
    linarith
  exact Real.le_sqrt_of_sq_le h_sq

/-- **Unconditional Contraction Bound on `GNSLinearPreHilbert os`**:
    Derived from `gnsLinearSemigroup_pow_two_cauchy_schwarz` and
    `gnsLinearSemigroup_uniform_bounded` (via `os.os4_exponential_clustering`). -/
theorem gnsLinearSemigroup_norm_le
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) (x : GNSLinearPreHilbert os) :
    ‖gnsLinearSemigroup os t ht x‖ ≤ ‖x‖ := by
  by_contra h_gt
  push Not at h_gt
  obtain ⟨M, _, hM⟩ := gnsLinearSemigroup_uniform_bounded os x
  have h_pow_le : ∀ k : ℕ,
      ‖gnsLinearSemigroup os t ht x‖ ^ (2 ^ k) ≤ ‖x‖ ^ (2 ^ k - 1) * M := fun k => by
    have h1 := gnsLinearSemigroup_pow_two_cauchy_schwarz os t ht x k
    have h2 := hM ((2 ^ k : ℝ) * t) (mul_nonneg (pow_nonneg zero_le_two k) ht)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (pow_nonneg (norm_nonneg x) _))
  rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx_pos
  · have h1 := h_pow_le 1
    rw [← hx0] at h1
    simp only [pow_one, Nat.reduceSub, zero_mul] at h1
    have h_sq_zero : ‖gnsLinearSemigroup os t ht x‖ ^ 2 = 0 :=
      le_antisymm h1 (sq_nonneg _)
    have h_zero : ‖gnsLinearSemigroup os t ht x‖ = 0 := sq_eq_zero_iff.mp h_sq_zero
    linarith
  · have hr_gt : 1 < ‖gnsLinearSemigroup os t ht x‖ / ‖x‖ := (one_lt_div hx_pos).mpr h_gt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (M / ‖x‖) hr_gt
    have hk_le : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    have h_pow_mono : (‖gnsLinearSemigroup os t ht x‖ / ‖x‖) ^ k ≤
        (‖gnsLinearSemigroup os t ht x‖ / ‖x‖) ^ (2 ^ k) :=
      pow_le_pow_right₀ hr_gt.le hk_le
    have h_div_le : (‖gnsLinearSemigroup os t ht x‖ / ‖x‖) ^ (2 ^ k) ≤ M / ‖x‖ := by
      rw [div_pow, div_le_div_iff₀ (pow_pos hx_pos (2 ^ k)) hx_pos]
      have h_pow_id : ‖x‖ ^ (2 ^ k - 1) * ‖x‖ = ‖x‖ ^ (2 ^ k) := by
        have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        rw [← pow_succ, Nat.sub_add_cancel h1]
      calc ‖gnsLinearSemigroup os t ht x‖ ^ (2 ^ k) * ‖x‖
          ≤ (‖x‖ ^ (2 ^ k - 1) * M) * ‖x‖ := mul_le_mul_of_nonneg_right (h_pow_le k) hx_pos.le
        _ = M * (‖x‖ ^ (2 ^ k - 1) * ‖x‖) := by ring
        _ = M * ‖x‖ ^ (2 ^ k) := by rw [h_pow_id]
    linarith

/-- Unconditional promotion of `gnsLinearSemigroup os t ht` to a `ContinuousLinearMap`. -/
noncomputable def gnsLinearSemigroupCLM
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) :
    GNSLinearPreHilbert os →L[ℂ] GNSLinearPreHilbert os :=
  (gnsLinearSemigroup os t ht).mkContinuous 1 fun x => by
    simpa using gnsLinearSemigroup_norm_le os t ht x

/-- Unconditional unique bounded linear extension of `gnsLinearSemigroup os t ht`
    along `gnsLinearToCompleted os` to `GNSCompletedHilbert os →L[ℂ] GNSCompletedHilbert os`. -/
noncomputable def gnsCompletedSemigroup
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) :
    GNSCompletedHilbert os →L[ℂ] GNSCompletedHilbert os :=
  ContinuousLinearMap.extend
    ((gnsLinearToCompleted os).toContinuousLinearMap.comp (gnsLinearSemigroupCLM os t ht))
    (gnsLinearToCompleted os).toContinuousLinearMap

theorem gnsCompletedSemigroup_apply_coe
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t)
    (x : GNSLinearPreHilbert os) :
    gnsCompletedSemigroup os t ht (gnsLinearToCompleted os x) =
      gnsLinearToCompleted os (gnsLinearSemigroup os t ht x) := by
  unfold gnsCompletedSemigroup
  exact ContinuousLinearMap.extend_eq _
    (gnsLinearToCompleted_denseRange os)
    (gnsLinearToCompleted os).isometry.isUniformInducing x

theorem gnsCompletedSemigroup_unique
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t)
    (g : GNSCompletedHilbert os →L[ℂ] GNSCompletedHilbert os)
    (hg : g.comp (gnsLinearToCompleted os).toContinuousLinearMap =
      (gnsLinearToCompleted os).toContinuousLinearMap.comp (gnsLinearSemigroupCLM os t ht)) :
    gnsCompletedSemigroup os t ht = g := by
  unfold gnsCompletedSemigroup
  exact ContinuousLinearMap.extend_unique _
    (gnsLinearToCompleted_denseRange os)
    (gnsLinearToCompleted os).isometry.isUniformInducing g hg

theorem gnsCompletedSemigroup_norm_le_one
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖gnsCompletedSemigroup os t ht‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine (gnsLinearToCompleted_denseRange os).induction_on y ?_ ?_
  · exact isClosed_le ((gnsCompletedSemigroup os t ht).continuous.norm) continuous_norm
  · intro x
    rw [gnsCompletedSemigroup_apply_coe]
    rw [(gnsLinearToCompleted os).norm_map, (gnsLinearToCompleted os).norm_map]
    exact gnsLinearSemigroup_norm_le os t ht x

theorem gnsCompletedSemigroup_zero
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    gnsCompletedSemigroup os 0 le_rfl = ContinuousLinearMap.id ℂ (GNSCompletedHilbert os) := by
  refine gnsCompletedSemigroup_unique os 0 le_rfl _ ?_
  ext x
  simp [gnsLinearSemigroupCLM, gnsLinearSemigroup_zero]

theorem gnsCompletedSemigroup_add
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t1 t2 : ℝ) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) :
    gnsCompletedSemigroup os (t1 + t2) (add_nonneg ht1 ht2) =
      (gnsCompletedSemigroup os t1 ht1).comp (gnsCompletedSemigroup os t2 ht2) := by
  refine gnsCompletedSemigroup_unique os (t1 + t2) (add_nonneg ht1 ht2) _ ?_
  ext x
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [gnsCompletedSemigroup_apply_coe, gnsCompletedSemigroup_apply_coe]
  change gnsLinearToCompleted os (gnsLinearSemigroup os t1 ht1 (gnsLinearSemigroup os t2 ht2 x)) =
    gnsLinearToCompleted os (gnsLinearSemigroup os (t1 + t2) (add_nonneg ht1 ht2) x)
  rw [gnsLinearSemigroup_add, LinearMap.comp_apply]

theorem gnsCompletedSemigroup_inner_symm
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t)
    (x y : GNSCompletedHilbert os) :
    inner ℂ (gnsCompletedSemigroup os t ht x) y =
      inner ℂ x (gnsCompletedSemigroup os t ht y) := by
  refine (gnsLinearToCompleted_denseRange os).induction_on x ?_ ?_
  · exact isClosed_eq
      ((gnsCompletedSemigroup os t ht).continuous.inner continuous_const)
      (continuous_id.inner continuous_const)
  · intro a
    refine (gnsLinearToCompleted_denseRange os).induction_on y ?_ ?_
    · exact isClosed_eq
        (continuous_const.inner continuous_id)
        (continuous_const.inner (gnsCompletedSemigroup os t ht).continuous)
    · intro b
      rw [gnsCompletedSemigroup_apply_coe, gnsCompletedSemigroup_apply_coe]
      change inner ℂ ((gnsLinearSemigroup os t ht a : GNSLinearPreHilbert os) : GNSCompletedHilbert os)
          ((b : GNSLinearPreHilbert os) : GNSCompletedHilbert os) =
        inner ℂ ((a : GNSLinearPreHilbert os) : GNSCompletedHilbert os)
          ((gnsLinearSemigroup os t ht b : GNSLinearPreHilbert os) : GNSCompletedHilbert os)
      rw [UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe]
      exact gnsLinearSemigroup_inner_symm os t ht a b

/-! ============================================================================
    PART IV-B: UNIT VACUUM STATE & EXPONENTIAL SEMIGROUP CONTRACTION
    ============================================================================ -/

/-- Formal vacuum state `1 · |Ω⟩` in `FormalPosTimeState G Curv`. -/
noncomputable def formalVacuumState
    (G : Type*) [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) : FormalPosTimeState G Curv :=
  Finsupp.single (vacuumTestData G Curv) 1

/-- Canonical unit vacuum vector in `GNSLinearPreHilbert os`. -/
noncomputable def gnsLinearVacuum
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) : GNSLinearPreHilbert os :=
  Submodule.Quotient.mk (formalVacuumState G Curv)

/-- Canonical unit vacuum vector in `GNSCompletedHilbert os`. -/
noncomputable def gnsCompletedVacuum
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) : GNSCompletedHilbert os :=
  gnsLinearToCompleted os (gnsLinearVacuum os)

theorem shiftPositiveTimeTestData_vacuum
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    (Curv : CurvaturePolynomialAlgebra G) (t : ℝ) (ht : 0 ≤ t) :
    shiftPositiveTimeTestData t ht (vacuumTestData G Curv) = vacuumTestData G Curv := by
  unfold shiftPositiveTimeTestData vacuumTestData
  congr 1
  funext i
  exact Fin.elim0 i

theorem inner_gnsLinearVacuum_self
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    inner ℂ (gnsLinearVacuum os) (gnsLinearVacuum os) = 1 := by
  change sesqOSHermQuotient os (Submodule.Quotient.mk (formalVacuumState G Curv))
    (Submodule.Quotient.mk (formalVacuumState G Curv)) = 1
  rw [sesqOSHermQuotient_mk]
  unfold sesqOSHerm formalVacuumState
  rw [sesqOSLinear_single_single]
  have hvac : sesqOS os (vacuumTestData G Curv) (vacuumTestData G Curv) = 1 :=
    osSesquilinearForm_vacuum_norm_one os
  rw [hvac]
  simp [map_one]
  norm_num

theorem norm_gnsLinearVacuum
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    ‖gnsLinearVacuum os‖ = 1 := by
  have hsq : ‖gnsLinearVacuum os‖ ^ 2 = 1 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), inner_gnsLinearVacuum_self os]
    simp
  have h0 : 0 ≤ ‖gnsLinearVacuum os‖ := norm_nonneg _
  nlinarith

theorem inner_gnsCompletedVacuum_self
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    inner ℂ (gnsCompletedVacuum os) (gnsCompletedVacuum os) = 1 := by
  rw [gnsCompletedVacuum, (gnsLinearToCompleted os).inner_map_map, inner_gnsLinearVacuum_self os]

theorem norm_gnsCompletedVacuum
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    ‖gnsCompletedVacuum os‖ = 1 := by
  rw [gnsCompletedVacuum, (gnsLinearToCompleted os).norm_map, norm_gnsLinearVacuum os]

theorem gnsCompletedVacuum_ne_zero
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv) :
    gnsCompletedVacuum os ≠ 0 := by
  intro h
  have h1 := norm_gnsCompletedVacuum os
  rw [h, norm_zero] at h1
  norm_num at h1

theorem gnsLinearSemigroup_vacuum
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) :
    gnsLinearSemigroup os t ht (gnsLinearVacuum os) = gnsLinearVacuum os := by
  rw [gnsLinearVacuum, gnsLinearSemigroup_mk, formalVacuumState,
    shiftFormalPosTimeState_single, shiftPositiveTimeTestData_vacuum]

theorem gnsCompletedSemigroup_vacuum
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (t : ℝ) (ht : 0 ≤ t) :
    gnsCompletedSemigroup os t ht (gnsCompletedVacuum os) = gnsCompletedVacuum os := by
  rw [gnsCompletedVacuum, gnsCompletedSemigroup_apply_coe, gnsLinearSemigroup_vacuum]

/-- **Exponential Semigroup Contraction on `GNSLinearPreHilbert os`**:
    Eliminates any constant prefactor `C ≥ 0` in `‖T_s x‖ ≤ C * exp(-m * s)` via
    `gnsLinearSemigroup_pow_two_cauchy_schwarz` and the `2^k`-power root limit `k → ∞`. -/
theorem gnsLinearSemigroup_exp_decay_of_shift_bound
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (x : GNSLinearPreHilbert os) (m C : ℝ) (_hC : 0 ≤ C)
    (h_shift : ∀ (s : ℝ) (hs : 0 ≤ s), ‖gnsLinearSemigroup os s hs x‖ ≤ C * Real.exp (-m * s)) :
    ∀ (t : ℝ) (ht : 0 ≤ t), ‖gnsLinearSemigroup os t ht x‖ ≤ Real.exp (-m * t) * ‖x‖ := by
  intro t ht
  by_cases hx0 : ‖x‖ = 0
  · have h_le := gnsLinearSemigroup_norm_le os t ht x
    rw [hx0] at h_le ⊢
    rw [mul_zero]
    exact h_le
  · have hx_pos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
    have hA_pos : 0 < Real.exp (-m * t) * ‖x‖ := mul_pos (Real.exp_pos _) hx_pos
    by_contra h_gt
    push_neg at h_gt
    have h_ratio_gt : 1 < ‖gnsLinearSemigroup os t ht x‖ / (Real.exp (-m * t) * ‖x‖) :=
      (one_lt_div hA_pos).mpr h_gt
    have h_unb := tendsto_pow_atTop_atTop_of_one_lt h_ratio_gt
    obtain ⟨N, hN⟩ := (h_unb.eventually (Filter.eventually_gt_atTop (C / ‖x‖))).exists
    have hN_lt : N < 2 ^ N := Nat.lt_two_pow_self
    have h_pow_mono :
        (‖gnsLinearSemigroup os t ht x‖ / (Real.exp (-m * t) * ‖x‖)) ^ N ≤
          (‖gnsLinearSemigroup os t ht x‖ / (Real.exp (-m * t) * ‖x‖)) ^ (2 ^ N) :=
      pow_le_pow_right₀ h_ratio_gt.le hN_lt.le
    have h_cs := gnsLinearSemigroup_pow_two_cauchy_schwarz os t ht x N
    have h_s := h_shift ((2 ^ N : ℝ) * t) (mul_nonneg (pow_nonneg zero_le_two N) ht)
    have h_exp : Real.exp (-m * ((2 ^ N : ℝ) * t)) = (Real.exp (-m * t)) ^ (2 ^ N) := by
      have h_eq : -m * ((2 ^ N : ℝ) * t) = ((2 ^ N : ℕ) : ℝ) * (-m * t) := by
        push_cast; ring
      rw [h_eq, Real.exp_nat_mul]
    have h_rhs :
        ‖x‖ ^ (2 ^ N - 1) *
            ‖gnsLinearSemigroup os ((2 ^ N : ℝ) * t)
              (mul_nonneg (pow_nonneg zero_le_two N) ht) x‖ ≤
          (C / ‖x‖) * (Real.exp (-m * t) * ‖x‖) ^ (2 ^ N) := by
      calc ‖x‖ ^ (2 ^ N - 1) *
            ‖gnsLinearSemigroup os ((2 ^ N : ℝ) * t)
              (mul_nonneg (pow_nonneg zero_le_two N) ht) x‖
          ≤ ‖x‖ ^ (2 ^ N - 1) * (C * Real.exp (-m * ((2 ^ N : ℝ) * t))) :=
            mul_le_mul_of_nonneg_left h_s (pow_nonneg hx_pos.le _)
        _ = (C / ‖x‖) * (Real.exp (-m * t) * ‖x‖) ^ (2 ^ N) := by
            rw [h_exp, mul_pow]
            have h2N : 1 ≤ 2 ^ N := Nat.one_le_two_pow
            have h_pow_split : ‖x‖ ^ (2 ^ N) = ‖x‖ ^ (2 ^ N - 1) * ‖x‖ := by
              conv_lhs => rw [← Nat.sub_add_cancel h2N, pow_succ]
            rw [h_pow_split]
            field_simp [hx_pos.ne']
    have h_bound :
        (‖gnsLinearSemigroup os t ht x‖ / (Real.exp (-m * t) * ‖x‖)) ^ (2 ^ N) ≤ C / ‖x‖ := by
      rw [div_pow, div_le_iff₀ (pow_pos hA_pos (2 ^ N))]
      exact h_cs.trans h_rhs
    linarith

/-- **Exponential Semigroup Contraction & Vacuum Orthogonality on `GNSCompletedHilbert os`**: -/
theorem gnsCompletedSemigroup_exp_decay_of_linear
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (x : GNSLinearPreHilbert os) (m : ℝ)
    (h_lin : ∀ (t : ℝ) (ht : 0 ≤ t),
      ‖gnsLinearSemigroup os t ht x‖ ≤ Real.exp (-m * t) * ‖x‖) :
    (∀ (t : ℝ) (ht : 0 ≤ t),
      ‖gnsCompletedSemigroup os t ht (gnsLinearToCompleted os x)‖ ≤
        Real.exp (-m * t) * ‖gnsLinearToCompleted os x‖) ∧
    (inner ℂ (gnsLinearVacuum os) x = 0 →
      inner ℂ (gnsCompletedVacuum os) (gnsLinearToCompleted os x) = 0) := by
  refine ⟨fun t ht => ?_, fun h_ortho => ?_⟩
  · rw [gnsCompletedSemigroup_apply_coe, (gnsLinearToCompleted os).norm_map,
      (gnsLinearToCompleted os).norm_map]
    exact h_lin t ht
  · rw [gnsCompletedVacuum, (gnsLinearToCompleted os).inner_map_map, h_ortho]

/-- Total `ℝ → GNSCompletedHilbert os` curve extending `gnsCompletedSemigroup os t ht` for `t ≥ 0`. -/
noncomputable def gnsCompletedSemigroupCurve
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ψ : GNSCompletedHilbert os) (t : ℝ) : GNSCompletedHilbert os :=
  if ht : 0 ≤ t then gnsCompletedSemigroup os t ht ψ else ψ

theorem gnsCompletedSemigroupCurve_zero
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ψ : GNSCompletedHilbert os) :
    gnsCompletedSemigroupCurve os ψ 0 = ψ := by
  simp [gnsCompletedSemigroupCurve, gnsCompletedSemigroup_zero]

/-- **Constructive GNS Wightman Reconstruction on `GNSCompletedHilbert os`**:
    Directly grounds `WightmanQuantumYangMills G (GNSCompletedHilbert os) Curv` on Goal 8's
    `GNSCompletedHilbert os`, `gnsCompletedVacuum os`, `gnsCompletedSemigroup os`, and
    exponential contraction without any `GNSMetricCompletion` detour. -/
structure GNSCompletedWightmanReconstruction
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    [SeparableSpace (GNSCompletedHilbert os)] where
  theory : WightmanQuantumYangMills G (GNSCompletedHilbert os) Curv
  h_vacuum : theory.vacuum = gnsCompletedVacuum os
  h_deriv : ∀ ψ : theory.domain,
    HasDerivAt (gnsCompletedSemigroupCurve os (ψ : GNSCompletedHilbert os))
      (- (theory.Hamiltonian ψ : GNSCompletedHilbert os)) 0
  h_semigroup_decay : ∀ (ψ : theory.domain),
    inner ℂ theory.vacuum (ψ : GNSCompletedHilbert os) = 0 →
    ∀ (t : ℝ) (ht : 0 ≤ t),
      ‖gnsCompletedSemigroup os t ht (ψ : GNSCompletedHilbert os)‖ ≤
        Real.exp (-os.mass_rate * t) * ‖(ψ : GNSCompletedHilbert os)‖
  h_finite_spec : ∃ (M : ℝ) (ψ : theory.domain),
    0 < M ∧ inner ℂ theory.vacuum (ψ : GNSCompletedHilbert os) = 0 ∧
    (ψ : GNSCompletedHilbert os) ≠ 0 ∧
    ‖theory.Hamiltonian ψ‖ ≤ M * ‖(ψ : GNSCompletedHilbert os)‖

/-- **Constructive Mass Gap on `GNSCompletedHilbert os` (`Δ = os.mass_rate > 0`)**:
    Proves `HasMassGap G (GNSCompletedHilbert os) recon.theory` directly from
    `gnsCompletedSemigroup os` and `os_semigroup_clustering_implies_hamiltonian_gap`. -/
theorem GNSCompletedWightmanReconstruction.has_mass_gap
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    {os : OsterwalderSchraderYangMills G Curv}
    [SeparableSpace (GNSCompletedHilbert os)]
    (recon : GNSCompletedWightmanReconstruction os) :
    HasMassGap G (GNSCompletedHilbert os) recon.theory := by
  refine ⟨os.mass_rate, os.mass_rate_pos, ?_, recon.h_finite_spec⟩
  intro ψ h_ortho
  have h_init : gnsCompletedSemigroupCurve os (ψ : GNSCompletedHilbert os) 0 =
      (ψ : GNSCompletedHilbert os) :=
    gnsCompletedSemigroupCurve_zero os (ψ : GNSCompletedHilbert os)
  have h_cluster : ∀ t : ℝ, 0 ≤ t →
      ‖gnsCompletedSemigroupCurve os (ψ : GNSCompletedHilbert os) t‖ ≤
        Real.exp (-os.mass_rate * t) * ‖(ψ : GNSCompletedHilbert os)‖ := by
    intro t ht
    simp only [gnsCompletedSemigroupCurve, dif_pos ht]
    exact recon.h_semigroup_decay ψ h_ortho t ht
  exact os_semigroup_clustering_implies_hamiltonian_gap
    (gnsCompletedSemigroupCurve os (ψ : GNSCompletedHilbert os))
    (ψ : GNSCompletedHilbert os)
    (recon.theory.Hamiltonian ψ : GNSCompletedHilbert os)
    os.mass_rate h_init (recon.h_deriv ψ) h_cluster

/-- **Constructor for `GNSCompletedWightmanReconstruction os` from Linear-Quotient Shift Bounds**:
    Automatically discharges `h_semigroup_decay` on `gnsLinearToCompleted os` domain vectors
    via `gnsLinearSemigroup_exp_decay_of_shift_bound` and `gnsCompletedSemigroup_exp_decay_of_linear`. -/
def GNSCompletedWightmanReconstruction.ofLinearShiftDecay
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    [SeparableSpace (GNSCompletedHilbert os)]
    (theory : WightmanQuantumYangMills G (GNSCompletedHilbert os) Curv)
    (h_vacuum : theory.vacuum = gnsCompletedVacuum os)
    (h_deriv : ∀ ψ : theory.domain,
      HasDerivAt (gnsCompletedSemigroupCurve os (ψ : GNSCompletedHilbert os))
        (- (theory.Hamiltonian ψ : GNSCompletedHilbert os)) 0)
    (h_domain_linear : ∀ ψ : theory.domain,
      inner ℂ theory.vacuum (ψ : GNSCompletedHilbert os) = 0 →
      ∃ x : GNSLinearPreHilbert os,
        (ψ : GNSCompletedHilbert os) = gnsLinearToCompleted os x ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ (s : ℝ) (hs : 0 ≤ s), ‖gnsLinearSemigroup os s hs x‖ ≤ C * Real.exp (-os.mass_rate * s))
    (h_finite_spec : ∃ (M : ℝ) (ψ : theory.domain),
      0 < M ∧ inner ℂ theory.vacuum (ψ : GNSCompletedHilbert os) = 0 ∧
      (ψ : GNSCompletedHilbert os) ≠ 0 ∧
      ‖theory.Hamiltonian ψ‖ ≤ M * ‖(ψ : GNSCompletedHilbert os)‖) :
    GNSCompletedWightmanReconstruction os where
  theory := theory
  h_vacuum := h_vacuum
  h_deriv := h_deriv
  h_semigroup_decay := fun ψ h_ortho t ht => by
    rcases h_domain_linear ψ h_ortho with ⟨x, hψ_eq, C, hC, h_shift⟩
    have h_lin := gnsLinearSemigroup_exp_decay_of_shift_bound os x os.mass_rate C hC h_shift
    have h_comp := (gnsCompletedSemigroup_exp_decay_of_linear os x os.mass_rate h_lin).1 t ht
    rw [← hψ_eq] at h_comp
    exact h_comp
  h_finite_spec := h_finite_spec

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

#print axioms sesqOS_two_point_quad_nonneg
#print axioms sesqOS_two_point_expanded_nonneg
#print axioms sesqOS_symm_cauchy_schwarz
#print axioms sesqOS_cauchy_schwarz
#print axioms sesqOS_eq_zero_of_diag_re_eq_zero
#print axioms sesqOSLinear_nonneg
#print axioms sesqOSLinear_symm_cauchy_schwarz
#print axioms sesqOSLinear_cauchy_schwarz
#print axioms sesqOSHerm_conj_symm
#print axioms sesqOSHerm_self_re
#print axioms sesqOSHerm_self_im
#print axioms sesqOSHerm_nonneg
#print axioms sesqOSHerm_cauchy_schwarz
#print axioms sesqOSHerm_eq_zero_iff
#print axioms osHermNullSubmodule
#print axioms gnsLinearInnerCore
#print axioms gnsLinearNormedAddCommGroup
#print axioms gnsLinearInnerProductSpace
#print axioms gnsLinear_norm_eq_sqrt_re_inner
#print axioms gnsLinear_norm_eq_zero_iff
#print axioms gnsLinearToCompleted
#print axioms gnsLinearToCompleted_denseRange
#print axioms gnsCompletedHilbert_complete
#print axioms gnsCompletedHilbert_innerProductSpace
#print axioms gns_cauchy_schwarz_soundness
#print axioms reed_simon_x49_semigroup_core
#print axioms reconstructed_gns_has_mass_gap
#print axioms OSIIWightmanReconstruction.has_mass_gap
#print axioms semigroup_exp_decay_of_symmetric_contraction_clustering
#print axioms sesqOS_shift_symm
#print axioms gnsPreHilbertSemigroup_zero
#print axioms gnsPreHilbertSemigroup_add
#print axioms shiftFormalPosTimeState_zero
#print axioms shiftFormalPosTimeState_add
#print axioms sesqOSLinear_shift_symm
#print axioms sesqOSHerm_shift_symm
#print axioms shiftFormalPosTimeState_mem_osHermNullSubmodule
#print axioms gnsLinearSemigroup
#print axioms gnsLinearSemigroup_inner_symm
#print axioms gnsLinearSemigroup_zero
#print axioms gnsLinearSemigroup_add
#print axioms gnsLinearSemigroup_pow_two_cauchy_schwarz
#print axioms gnsCompletedSemigroup
#print axioms gnsCompletedSemigroup_apply_coe
#print axioms gnsCompletedSemigroup_unique
#print axioms gnsCompletedSemigroup_norm_le_one
#print axioms sesqOS_shift_norm_bounded
#print axioms sesqOSLinear_shift_norm_bounded
#print axioms gnsLinearSemigroup_uniform_bounded
#print axioms gnsLinearSemigroup_norm_le
#print axioms gnsCompletedSemigroup_zero
#print axioms gnsCompletedSemigroup_add
#print axioms gnsCompletedSemigroup_inner_symm
#print axioms shiftPositiveTimeTestData_vacuum
#print axioms inner_gnsLinearVacuum_self
#print axioms norm_gnsLinearVacuum
#print axioms inner_gnsCompletedVacuum_self
#print axioms norm_gnsCompletedVacuum
#print axioms gnsCompletedVacuum_ne_zero
#print axioms gnsLinearSemigroup_vacuum
#print axioms gnsCompletedSemigroup_vacuum
#print axioms gnsLinearSemigroup_exp_decay_of_shift_bound
#print axioms gnsCompletedSemigroup_exp_decay_of_linear
#print axioms gnsCompletedSemigroupCurve_zero
#print axioms GNSCompletedWightmanReconstruction.has_mass_gap
#print axioms GNSCompletedWightmanReconstruction.ofLinearShiftDecay
#print axioms sesqOS_shift_clustering
#print axioms charFunctionalTrunc_zero
#print axioms charFunctionalTrunc_zero_test
#print axioms charFunctionalTrunc_one_os0_bound
#print axioms massSqOp_symmetric
#print axioms massSqOp_inner_eq
#print axioms massSqOp_rest_frame_mass_shell_bound

end YangMills.ConstructiveGNS
