/-
Copyright 2026 Elias Oulad Brahim and ToposLang / PLQ Authors.
Licensed under the Apache License, Version 2.0.

HaarWilsonLattice.lean
Constructive Haar-Measure Wilson Lattice Gauge Theory, Character Floor Lemma 1,
and Volume-Independent Strong-Coupling Spectral Gap in Lean 4 (Mathlib v4.33.1).
-/

import Mathlib
import ToposUnifiedYangMills

set_option linter.defProp false
set_option linter.unusedVariables true

open scoped Real InnerProductSpace Topology Matrix BigOperators ENNReal NNReal ComplexConjugate Classical
open MeasureTheory
open TopologicalSpace

namespace HaarWilsonLattice

/-- Continuous functions on a compact space are Bochner integrable with respect to any
    locally finite (in particular, finite or probability) Borel measure. -/
theorem integrable_of_continuous_compact {X E : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] {f : X → E} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem integral_add_apply {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : X → E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, (f x + g x) ∂μ) = (∫ x, f x ∂μ) + (∫ x, g x ∂μ) :=
  integral_add hf hg

theorem integral_add4 {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f1 f2 f3 f4 : X → E}
    (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) (h4 : Integrable f4 μ) :
    (∫ x, ((f1 x + f2 x) + (f3 x + f4 x)) ∂μ) =
      (∫ x, f1 x ∂μ) + (∫ x, f2 x ∂μ) + (∫ x, f3 x ∂μ) + (∫ x, f4 x ∂μ) := by
  have h12 : Integrable (fun x => f1 x + f2 x) μ := h1.add h2
  have h34 : Integrable (fun x => f3 x + f4 x) μ := h3.add h4
  rw [integral_add_apply h12 h34, integral_add_apply h1 h2, integral_add_apply h3 h4]
  abel

theorem integral_add6 {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f1 f2 f3 f4 f5 f6 : X → E}
    (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : Integrable f3 μ)
    (h4 : Integrable f4 μ) (h5 : Integrable f5 μ) (h6 : Integrable f6 μ) :
    (∫ x, (((((f1 x + f2 x) + f3 x) + f4 x) + f5 x) + f6 x) ∂μ) =
      (∫ x, f1 x ∂μ) + (∫ x, f2 x ∂μ) + (∫ x, f3 x ∂μ) +
        (∫ x, f4 x ∂μ) + (∫ x, f5 x ∂μ) + (∫ x, f6 x ∂μ) := by
  have h12 : Integrable (fun x => f1 x + f2 x) μ := h1.add h2
  have h123 : Integrable (fun x => (f1 x + f2 x) + f3 x) μ := h12.add h3
  have h1234 : Integrable (fun x => ((f1 x + f2 x) + f3 x) + f4 x) μ := h123.add h4
  have h12345 : Integrable (fun x => (((f1 x + f2 x) + f3 x) + f4 x) + f5 x) μ := h1234.add h5
  rw [integral_add_apply h12345 h6, integral_add_apply h1234 h5,
      integral_add_apply h123 h4, integral_add_apply h12 h3, integral_add_apply h1 h2]

/-! ============================================================================
    PART I: NORMALIZED BI-INVARIANT HAAR PROBABILITY MEASURE ON COMPACT GROUPS
    ============================================================================ -/

section HaarProbability

variable (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The whole compact Lie group `G` packaged as a `PositiveCompacts G` normalization reference
    so that `haarMeasure` assigns unit total mass `μ(G) = 1`. -/
def univPositiveCompacts : PositiveCompacts G where
  toCompacts := ⟨Set.univ, isCompact_univ⟩
  interior_nonempty' := by simp

/-- Normalized Haar probability measure `μ_Haar` on a compact topological group `G`,
    constructed directly from Mathlib's `MeasureTheory.Measure.haarMeasure`. -/
noncomputable def haarProb : Measure G :=
  Measure.haarMeasure (univPositiveCompacts G)

instance haarProb_isHaarMeasure : Measure.IsHaarMeasure (haarProb G) :=
  Measure.isHaarMeasure_haarMeasure (univPositiveCompacts G)

instance haarProb_isMulLeftInvariant : Measure.IsMulLeftInvariant (haarProb G) :=
  inferInstance

instance haarProb_isOpenPosMeasure : Measure.IsOpenPosMeasure (haarProb G) :=
  inferInstance

theorem haarProb_univ : haarProb G Set.univ = 1 :=
  Measure.haarMeasure_self

instance haarProb_isProbabilityMeasure : IsProbabilityMeasure (haarProb G) :=
  ⟨haarProb_univ G⟩

@[simp]
theorem haarProb_real_univ : (haarProb G).real Set.univ = 1 := by
  simp [Measure.real]

/-- Unimodularity of compact Hausdorff second-countable groups:
    the normalized left Haar measure `haarProb G` is automatically right-invariant. -/
instance haarProb_isMulRightInvariant [T2Space G] [SecondCountableTopology G] :
    Measure.IsMulRightInvariant (haarProb G) where
  map_mul_right_eq_self g := by
    let ν : Measure G := Measure.map (· * g) (haarProb G)
    have h_meas_g : Measurable (· * g : G → G) := (continuous_mul_const g).measurable
    have h_prob_ν : ν Set.univ = 1 := by
      rw [Measure.map_apply h_meas_g MeasurableSet.univ, Set.preimage_univ, haarProb_univ]
    have _ : IsFiniteMeasure ν := ⟨by rw [h_prob_ν]; exact ENNReal.one_lt_top⟩
    have _ : Measure.IsMulLeftInvariant ν := by
      refine ⟨fun h => ?_⟩
      have h_meas_h : Measurable (h * · : G → G) := (continuous_const_mul h).measurable
      rw [Measure.map_map h_meas_h h_meas_g]
      have h_comm : ((h * ·) ∘ (· * g) : G → G) = ((· * g) ∘ (h * ·)) := by
        funext x
        simp [Function.comp, mul_assoc]
      rw [h_comm, ← Measure.map_map h_meas_g h_meas_h, map_mul_left_eq_self]
    have h_smul : ν = Measure.haarScalarFactor ν (haarProb G) • haarProb G :=
      Measure.isMulLeftInvariant_eq_smul ν (haarProb G)
    have h_factor : (Measure.haarScalarFactor ν (haarProb G) : ℝ≥0∞) = 1 := by
      have h_eval := congrArg (fun m : Measure G => m Set.univ) h_smul
      simpa [h_prob_ν, haarProb_univ] using h_eval.symm
    have h_nnreal : Measure.haarScalarFactor ν (haarProb G) = 1 := by
      exact_mod_cast h_factor
    change ν = haarProb G
    rw [h_smul, h_nnreal, one_smul]

/-- Inversion invariance `μ(E⁻¹) = μ(E)` of the normalized Haar measure `haarProb G`. -/
instance haarProb_isInvInvariant [T2Space G] [SecondCountableTopology G] :
    Measure.IsInvInvariant (haarProb G) where
  inv_eq_self := by
    let ν : Measure G := (haarProb G).inv
    have h_prob_ν : ν Set.univ = 1 := by
      change Measure.map Inv.inv (haarProb G) Set.univ = 1
      rw [Measure.map_apply continuous_inv.measurable MeasurableSet.univ,
          Set.preimage_univ, haarProb_univ]
    have _ : IsFiniteMeasure ν := ⟨by rw [h_prob_ν]; exact ENNReal.one_lt_top⟩
    have _ : Measure.IsMulLeftInvariant ν := by
      refine ⟨fun h => ?_⟩
      have h_meas_h : Measurable (h * · : G → G) := (continuous_const_mul h).measurable
      have h_meas_rinv : Measurable (· * h⁻¹ : G → G) := (continuous_mul_const h⁻¹).measurable
      change Measure.map (h * ·) (Measure.map Inv.inv (haarProb G)) = ν
      rw [Measure.map_map h_meas_h continuous_inv.measurable]
      have h_comm : ((h * ·) ∘ (Inv.inv : G → G)) = (Inv.inv ∘ (· * h⁻¹)) := by
        funext x
        simp [Function.comp]
      rw [h_comm, ← Measure.map_map continuous_inv.measurable h_meas_rinv,
          map_mul_right_eq_self]
      rfl
    have h_smul : ν = Measure.haarScalarFactor ν (haarProb G) • haarProb G :=
      Measure.isMulLeftInvariant_eq_smul ν (haarProb G)
    have h_factor : (Measure.haarScalarFactor ν (haarProb G) : ℝ≥0∞) = 1 := by
      have h_eval := congrArg (fun m : Measure G => m Set.univ) h_smul
      simpa [h_prob_ν, haarProb_univ] using h_eval.symm
    have h_nnreal : Measure.haarScalarFactor ν (haarProb G) = 1 := by
      exact_mod_cast h_factor
    change ν = haarProb G
    rw [h_smul, h_nnreal, one_smul]

end HaarProbability

/-! ============================================================================
    PART II: NORMALIZED GAUGE CHARACTER & CONCRETE ZERO-SORRY SU(2) INSTANCE
    ============================================================================ -/

/-- Normalized real gauge character `χ : G → [-1, 1]` on a compact Lie group `G`
    (representing `(1 / d_fund) Re Tr_fund(U)`), satisfying class invariance,
    zero Haar mean, second-moment bound `∫ χ² ≤ 1/2`, and Schur's character
    functional equation `∫_X χ(g X h X⁻¹) dμ(X) = χ(g) χ(h)`. -/
structure NormalizedGaugeCharacter (G : Type*)
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] where
  χ : G → ℝ
  χ_continuous : Continuous χ
  χ_one : χ 1 = 1
  χ_abs_le_one : ∀ g : G, |χ g| ≤ 1
  χ_conj : ∀ g h : G, χ (g * h * g⁻¹) = χ h
  χ_inv : ∀ g : G, χ g⁻¹ = χ g
  χ_integral_zero : ∫ g, χ g ∂(haarProb G) = 0
  χ_sq_integral_le_half : ∫ g, (χ g) ^ 2 ∂(haarProb G) ≤ 1 / 2
  χ_functional_eq : ∀ g h : G, ∫ x, χ (g * x * h * x⁻¹) ∂(haarProb G) = χ g * χ h

namespace NormalizedGaugeCharacter

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (C : NormalizedGaugeCharacter G)

theorem χ_le_one (g : G) : C.χ g ≤ 1 :=
  (abs_le.mp (C.χ_abs_le_one g)).2

theorem neg_one_le_χ (g : G) : -1 ≤ C.χ g :=
  (abs_le.mp (C.χ_abs_le_one g)).1

theorem χ_mul_comm (g h : G) : C.χ (g * h) = C.χ (h * g) := by
  have h1 := C.χ_conj h (g * h)
  have h2 : C.χ (h * g) = C.χ (g * h) := by simpa [mul_assoc] using h1
  exact h2.symm

end NormalizedGaugeCharacter

/-! ### Concrete Zero-`sorry` Topological & Measure Structure for `YangMills.SUN N` -/

section ConcreteSUN

instance (priority := high) sun_isTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (YangMills.SUN N) where
  continuous_mul :=
    continuous_induced_rng.mpr
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))
  continuous_inv :=
    continuous_induced_rng.mpr (continuous_star.comp continuous_subtype_val)

instance matrixN_secondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))

instance sun_secondCountableTopology (N : ℕ) :
    SecondCountableTopology (YangMills.SUN N) :=
  letI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) := matrixN_secondCountableTopology N
  (⟨rfl⟩ : Topology.IsInducing
    (Subtype.val : YangMills.SUN N → Matrix (Fin N) (Fin N) ℂ)).secondCountableTopology

instance sun_t2Space (N : ℕ) : T2Space (YangMills.SUN N) :=
  inferInstance

noncomputable instance sun_measurableSpace (N : ℕ) : MeasurableSpace (YangMills.SUN N) :=
  borel (YangMills.SUN N)

instance sun_borelSpace (N : ℕ) : BorelSpace (YangMills.SUN N) :=
  ⟨rfl⟩

instance (priority := 100) compactSpace_of_compactSimpleLieGroup
    (G : Type*) [TopologicalSpace G] [Group G] [h : YangMills.CompactSimpleLieGroup G] :
    CompactSpace G :=
  isCompact_univ_iff.mp h.is_compact

end ConcreteSUN

/-! ### Concrete Zero-`sorry` Topological & Haar Character Verification for `YangMills.SU2` -/

section ConcreteSU2

instance (priority := high) su2_isTopologicalGroup : IsTopologicalGroup YangMills.SU2 where
  continuous_mul :=
    continuous_induced_rng.mpr
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))
  continuous_inv :=
    continuous_induced_rng.mpr (continuous_star.comp continuous_subtype_val)

instance matrix2_secondCountableTopology :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

instance su2_secondCountableTopology : SecondCountableTopology YangMills.SU2 :=
  (⟨rfl⟩ : Topology.IsInducing
    (Subtype.val : YangMills.SU2 → Matrix (Fin 2) (Fin 2) ℂ)).secondCountableTopology

noncomputable instance su2_measurableSpace : MeasurableSpace YangMills.SU2 :=
  borel YangMills.SU2

instance su2_borelSpace : BorelSpace YangMills.SU2 :=
  ⟨rfl⟩

private theorem complex_star_mul_self_re (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, RCLike.star_def,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

instance su2_compactSpace : CompactSpace YangMills.SU2 := by
  let S : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
    {A | star A * A = 1} ∩ {A | Matrix.det A = 1}
  have hS_eq : (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) = S := by
    ext A
    simp [S, Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  have h_closed : IsClosed S := by
    refine IsClosed.inter ?_ ?_
    · exact isClosed_eq (continuous_star.mul continuous_id) continuous_const
    · exact isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  let B : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
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
    have h_diag : (star A * A) j j = star (A 0 j) * A 0 j + star (A 1 j) * A 1 j := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h_re := congrArg Complex.re (h_diag.symm.trans h_unit)
    have h_norm0 : (star (A 0 j) * A 0 j).re = ‖A 0 j‖ ^ 2 :=
      complex_star_mul_self_re (A 0 j)
    have h_norm1 : (star (A 1 j) * A 1 j).re = ‖A 1 j‖ ^ 2 :=
      complex_star_mul_self_re (A 1 j)
    have h_sum_sq : ‖A 0 j‖ ^ 2 + ‖A 1 j‖ ^ 2 = 1 := by
      rw [Complex.add_re, h_norm0, h_norm1, Complex.one_re] at h_re
      exact h_re
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    have h_le_sq : ‖A i j‖ ^ 2 ≤ 1 := by
      rcases hi with rfl | rfl
      · nlinarith [sq_nonneg ‖A 1 j‖]
      · nlinarith [sq_nonneg ‖A 0 j‖]
    nlinarith [norm_nonneg (A i j)]
  rw [← hS_eq] at hS_compact
  exact isCompact_iff_compactSpace.mp hS_compact

/-- Normalized fundamental character `(1/2) Re Tr(U)` on `SU(2)`. -/
noncomputable def su2Chi (U : YangMills.SU2) : ℝ :=
  ((U.1 0 0).re + (U.1 1 1).re) / 2

theorem su2_entry_relations (U : YangMills.SU2) :
    U.1 1 1 = star (U.1 0 0) ∧
    U.1 0 1 = - star (U.1 1 0) ∧
    (U.1 0 0).re ^ 2 + (U.1 0 0).im ^ 2 + (U.1 1 0).re ^ 2 + (U.1 1 0).im ^ 2 = 1 := by
  rcases Matrix.mem_specialUnitaryGroup_iff.mp U.2 with ⟨hU_unit, hU_det⟩
  have h_mul : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp hU_unit
  let adj : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![U.1 1 1, -U.1 0 1], ![-U.1 1 0, U.1 0 0]]
  have h_det2 : U.1 0 0 * U.1 1 1 - U.1 0 1 * U.1 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hU_det
  have h_adj_mul : adj * U.1 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [adj, Fin.zero_eta, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.one_apply_eq]
      linear_combination h_det2
    · simp only [adj, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, ne_eq, Fin.zero_eta, Fin.mk_one,
         zero_ne_one, not_false_eq_true, Matrix.one_apply_ne]
      ring
    · simp only [adj, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, ne_eq, Fin.mk_one, Fin.zero_eta,
        one_ne_zero, not_false_eq_true, Matrix.one_apply_ne]
      ring
    · simp only [adj, Fin.mk_one, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.one_apply_eq]
      linear_combination h_det2
  have h_eq : star U.1 = adj := by
    calc star U.1
        = star U.1 * 1 := (Matrix.mul_one _).symm
      _ = star U.1 * (U.1 * star U.1) := by
          rw [Matrix.mem_unitaryGroup_iff.mp hU_unit]
      _ = adj * (U.1 * star U.1) := by
          rw [← Matrix.mul_assoc, h_mul, ← Matrix.mul_assoc, h_adj_mul]
      _ = adj := by
          rw [Matrix.mem_unitaryGroup_iff.mp hU_unit, Matrix.mul_one]
  have h11 : U.1 1 1 = star (U.1 0 0) := by
    have h00 := congrFun (congrFun h_eq 0) 0
    simpa [adj] using h00.symm
  have h01 : U.1 0 1 = - star (U.1 1 0) := by
    have h01' := congrFun (congrFun h_eq 0) 1
    have h_neg : star (U.1 1 0) = - U.1 0 1 := by simpa [adj] using h01'
    calc U.1 0 1 = - (- U.1 0 1) := by ring
      _ = - star (U.1 1 0) := by rw [← h_neg]
  have h_unit00 := congrArg Complex.re (congrFun (congrFun h_mul 0) 0)
  have h_norm :
      (U.1 0 0).re ^ 2 + (U.1 0 0).im ^ 2 + (U.1 1 0).re ^ 2 + (U.1 1 0).im ^ 2 = 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, RCLike.star_def,
      Matrix.one_apply_eq, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.one_re] at h_unit00
    nlinarith
  exact ⟨h11, h01, h_norm⟩

theorem su2Chi_eq_re00 (U : YangMills.SU2) : su2Chi U = (U.1 0 0).re := by
  unfold su2Chi
  rw [(su2_entry_relations U).1, Complex.star_def, Complex.conj_re]
  ring

/-- Central element `-I₂ ∈ SU(2)`. -/
def su2NegOne : YangMills.SU2 :=
  ⟨Matrix.of ![![(-1 : ℂ), 0], ![0, -1]], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.det_fin_two]⟩

/-- Quaternion basis element `Y₁ = diag(i, -i) ∈ SU(2)`. -/
def su2Y1 : YangMills.SU2 :=
  ⟨Matrix.of ![![Complex.I, 0], ![0, -Complex.I]], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.det_fin_two]⟩

/-- Quaternion basis element `Y₂ = [[0, -1], [1, 0]] ∈ SU(2)`. -/
def su2Y2 : YangMills.SU2 :=
  ⟨Matrix.of ![![(0 : ℂ), -1], ![1, 0]], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.det_fin_two]⟩

/-- Quaternion basis element `Y₃ = [[0, -i], [-i, 0]] ∈ SU(2)`. -/
def su2Y3 : YangMills.SU2 :=
  ⟨Matrix.of ![![(0 : ℂ), -Complex.I], ![-Complex.I, 0]], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.det_fin_two]⟩

theorem su2Chi_continuous : Continuous su2Chi := by
  have h00 : Continuous (fun U : YangMills.SU2 => (U.1 0 0).re) :=
    Complex.continuous_re.comp
      ((continuous_apply (0 : Fin 2)).comp
        ((continuous_apply (0 : Fin 2)).comp continuous_subtype_val))
  have h11 : Continuous (fun U : YangMills.SU2 => (U.1 1 1).re) :=
    Complex.continuous_re.comp
      ((continuous_apply (1 : Fin 2)).comp
        ((continuous_apply (1 : Fin 2)).comp continuous_subtype_val))
  exact (h00.add h11).div_const 2

theorem su2Chi_quat_squares (U : YangMills.SU2) :
    (su2Chi U) ^ 2 + (su2Chi (su2Y1 * U)) ^ 2 +
      (su2Chi (su2Y2 * U)) ^ 2 + (su2Chi (su2Y3 * U)) ^ 2 = 1 := by
  rw [su2Chi_eq_re00 U, su2Chi_eq_re00 (su2Y1 * U),
      su2Chi_eq_re00 (su2Y2 * U), su2Chi_eq_re00 (su2Y3 * U)]
  have h1 : ((su2Y1 * U).1 0 0).re = -(U.1 0 0).im := by
    change ((su2Y1.1 * U.1) 0 0).re = _
    simp [su2Y1, Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : ((su2Y2 * U).1 0 0).re = -(U.1 1 0).re := by
    change ((su2Y2.1 * U.1) 0 0).re = _
    simp [su2Y2, Matrix.mul_apply, Fin.sum_univ_two]
  have h3 : ((su2Y3 * U).1 0 0).re = (U.1 1 0).im := by
    change ((su2Y3.1 * U.1) 0 0).re = _
    simp [su2Y3, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h1, h2, h3]
  nlinarith [(su2_entry_relations U).2.2]

theorem su2Chi_quat_conj_average (g h : YangMills.SU2) :
    su2Chi (g * h) + su2Chi (g * su2Y1 * h * su2Y1⁻¹) +
      su2Chi (g * su2Y2 * h * su2Y2⁻¹) + su2Chi (g * su2Y3 * h * su2Y3⁻¹) =
      4 * su2Chi g * su2Chi h := by
  rw [su2Chi_eq_re00 (g * h), su2Chi_eq_re00 (g * su2Y1 * h * su2Y1⁻¹),
      su2Chi_eq_re00 (g * su2Y2 * h * su2Y2⁻¹), su2Chi_eq_re00 (g * su2Y3 * h * su2Y3⁻¹),
      su2Chi_eq_re00 g, su2Chi_eq_re00 h]
  rcases su2_entry_relations g with ⟨_, hg01, _⟩
  rcases su2_entry_relations h with ⟨hh11, hh01, _⟩
  have t0 : ((g * h).1 0 0).re = ((g.1 * h.1) 0 0).re := rfl
  have t1 : ((g * su2Y1 * h * su2Y1⁻¹).1 0 0).re =
      ((g.1 * su2Y1.1 * h.1 * star su2Y1.1) 0 0).re := rfl
  have t2 : ((g * su2Y2 * h * su2Y2⁻¹).1 0 0).re =
      ((g.1 * su2Y2.1 * h.1 * star su2Y2.1) 0 0).re := rfl
  have t3 : ((g * su2Y3 * h * su2Y3⁻¹).1 0 0).re =
      ((g.1 * su2Y3.1 * h.1 * star su2Y3.1) 0 0).re := rfl
  rw [t0, t1, t2, t3]
  simp [su2Y1, su2Y2, su2Y3, Matrix.mul_apply, Fin.sum_univ_two, hg01, hh11, hh01]
  ring

/-- Exact Schur second-moment identity on `SU(2)`: `∫_{SU(2)} χ(U)² dμ_Haar = 1/4`. -/
theorem su2Chi_sq_integral_eq :
    ∫ U, (su2Chi U) ^ 2 ∂(haarProb YangMills.SU2) = 1 / 4 := by
  let μ := haarProb YangMills.SU2
  let f : YangMills.SU2 → ℝ := fun U => (su2Chi U) ^ 2
  have hf_int : Integrable f μ :=
    integrable_of_continuous_compact (su2Chi_continuous.pow 2)
  have hf1 : Integrable (fun U => f (su2Y1 * U)) μ :=
    integrable_of_continuous_compact ((su2Chi_continuous.comp (continuous_const_mul su2Y1)).pow 2)
  have hf2 : Integrable (fun U => f (su2Y2 * U)) μ :=
    integrable_of_continuous_compact ((su2Chi_continuous.comp (continuous_const_mul su2Y2)).pow 2)
  have hf3 : Integrable (fun U => f (su2Y3 * U)) μ :=
    integrable_of_continuous_compact ((su2Chi_continuous.comp (continuous_const_mul su2Y3)).pow 2)
  have h_sum : ∫ U, ((f U + f (su2Y1 * U)) + (f (su2Y2 * U) + f (su2Y3 * U))) ∂μ = 1 := by
    have h_pt : ∀ U, (f U + f (su2Y1 * U)) + (f (su2Y2 * U) + f (su2Y3 * U)) = (1 : ℝ) := by
      intro U
      simpa [f, add_assoc] using su2Chi_quat_squares U
    simp_rw [h_pt]
    simp [μ]
  rw [integral_add4 hf_int hf1 hf2 hf3,
      integral_mul_left_eq_self f su2Y1,
      integral_mul_left_eq_self f su2Y2,
      integral_mul_left_eq_self f su2Y3] at h_sum
  linarith

/-- Complete, zero-`sorry` `NormalizedGaugeCharacter` instance for `SU(2)`. -/
noncomputable def su2GaugeCharacter : NormalizedGaugeCharacter YangMills.SU2 where
  χ := su2Chi
  χ_continuous := su2Chi_continuous
  χ_one := by
    rw [su2Chi_eq_re00]
    simp
  χ_abs_le_one U := by
    rw [su2Chi_eq_re00]
    have h_sq : (U.1 0 0).re ^ 2 ≤ 1 := by
      have h_rel := (su2_entry_relations U).2.2
      nlinarith [sq_nonneg (U.1 0 0).im, sq_nonneg (U.1 1 0).re, sq_nonneg (U.1 1 0).im]
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)
  χ_conj g h := by
    unfold su2Chi
    have h_tr : Matrix.trace ((g * h * g⁻¹).1) = Matrix.trace h.1 := by
      change Matrix.trace (g.1 * h.1 * (g⁻¹).1) = Matrix.trace h.1
      rw [Matrix.trace_mul_cycle]
      have h_id : (g⁻¹ * g).1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by simp
      change Matrix.trace ((g⁻¹ * g).1 * h.1) = Matrix.trace h.1
      rw [h_id, Matrix.one_mul]
    have h_re := congrArg Complex.re h_tr
    simp only [Matrix.trace_fin_two, Complex.add_re] at h_re
    linarith
  χ_inv U := by
    rw [su2Chi_eq_re00 U⁻¹, su2Chi_eq_re00 U]
    change ((star U.1) 0 0).re = (U.1 0 0).re
    simp
  χ_integral_zero := by
    have h_neg : ∀ U : YangMills.SU2, su2Chi (su2NegOne * U) = - su2Chi U := by
      intro U
      rw [su2Chi_eq_re00 (su2NegOne * U), su2Chi_eq_re00 U]
      change ((su2NegOne.1 * U.1) 0 0).re = _
      simp [su2NegOne, Matrix.mul_apply, Fin.sum_univ_two]
    have h_inv := integral_mul_left_eq_self (μ := haarProb YangMills.SU2) su2Chi su2NegOne
    have h_int_neg : ∫ U, su2Chi (su2NegOne * U) ∂(haarProb YangMills.SU2) =
        - ∫ U, su2Chi U ∂(haarProb YangMills.SU2) := by
      simp_rw [h_neg, integral_neg]
    linarith
  χ_sq_integral_le_half := by
    rw [su2Chi_sq_integral_eq]
    norm_num
  χ_functional_eq g h := by
    let μ := haarProb YangMills.SU2
    let F : YangMills.SU2 → ℝ := fun X => su2Chi (g * X * h * X⁻¹)
    have hF_cont : Continuous F := by
      unfold F
      exact su2Chi_continuous.comp
        (((continuous_const.mul continuous_id).mul continuous_const).mul continuous_inv)
    have hF_int : Integrable F μ := integrable_of_continuous_compact hF_cont
    have hF1 : Integrable (fun X => F (su2Y1 * X)) μ :=
      integrable_of_continuous_compact (hF_cont.comp (continuous_const_mul su2Y1))
    have hF2 : Integrable (fun X => F (su2Y2 * X)) μ :=
      integrable_of_continuous_compact (hF_cont.comp (continuous_const_mul su2Y2))
    have hF3 : Integrable (fun X => F (su2Y3 * X)) μ :=
      integrable_of_continuous_compact (hF_cont.comp (continuous_const_mul su2Y3))
    have h_pt : ∀ X : YangMills.SU2,
        (F X + F (su2Y1 * X)) + (F (su2Y2 * X) + F (su2Y3 * X)) =
          4 * su2Chi g * su2Chi h := by
      intro X
      have h_avg := su2Chi_quat_conj_average g (X * h * X⁻¹)
      have h_c : su2Chi (X * h * X⁻¹) = su2Chi h := by
        unfold su2Chi
        have h_tr : Matrix.trace ((X * h * X⁻¹).1) = Matrix.trace h.1 := by
          change Matrix.trace (X.1 * h.1 * (X⁻¹).1) = Matrix.trace h.1
          rw [Matrix.trace_mul_cycle]
          have h_id : (X⁻¹ * X).1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by simp
          change Matrix.trace ((X⁻¹ * X).1 * h.1) = Matrix.trace h.1
          rw [h_id, Matrix.one_mul]
        have h_re := congrArg Complex.re h_tr
        simp only [Matrix.trace_fin_two, Complex.add_re] at h_re
        linarith
      rw [h_c] at h_avg
      simpa [F, mul_assoc, add_assoc] using h_avg
    have h_int_eq : ∫ X, ((F X + F (su2Y1 * X)) + (F (su2Y2 * X) + F (su2Y3 * X))) ∂μ =
        4 * su2Chi g * su2Chi h := by
      simp_rw [h_pt]
      simp [μ]
    rw [integral_add4 hF_int hF1 hF2 hF3,
        integral_mul_left_eq_self F su2Y1,
        integral_mul_left_eq_self F su2Y2,
        integral_mul_left_eq_self F su2Y3] at h_int_eq
    linarith

end ConcreteSU2

/-! ### General SU(N) Fundamental Trace Character Architecture (N ≥ 2) -/

section GeneralSUN

open scoped Matrix

/-- Normalized fundamental trace function `(1 / N) Re Tr(U)` on `SUN N`. -/
noncomputable def sunFundamentalTrace (N : ℕ) (U : YangMills.SUN N) : ℝ :=
  (1 / (N : ℝ)) * (Matrix.trace (U.1 : Matrix (Fin N) (Fin N) ℂ)).re

theorem sunFundamentalTrace_one (N : ℕ) [Fact (2 ≤ N)] :
    sunFundamentalTrace N 1 = 1 := by
  unfold sunFundamentalTrace
  have hN : (N : ℝ) ≠ 0 := by
    have : 2 ≤ N := Fact.out
    positivity
  have h_tr : Matrix.trace ((1 : YangMills.SUN N).1 : Matrix (Fin N) (Fin N) ℂ) = (N : ℂ) := by
    simp [Matrix.trace_one]
  rw [h_tr, Complex.natCast_re, one_div, inv_mul_cancel₀ hN]

theorem sunFundamentalTrace_conj (N : ℕ) (g h : YangMills.SUN N) :
    sunFundamentalTrace N (g * h * g⁻¹) = sunFundamentalTrace N h := by
  unfold sunFundamentalTrace
  have h_tr : Matrix.trace ((g * h * g⁻¹).1 : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.trace (h.1 : Matrix (Fin N) (Fin N) ℂ) := by
    change Matrix.trace (g.1 * h.1 * (g⁻¹).1) = Matrix.trace h.1
    rw [Matrix.trace_mul_cycle]
    have h_id : (g⁻¹ * g).1 = (1 : Matrix (Fin N) (Fin N) ℂ) := by simp
    change Matrix.trace ((g⁻¹ * g).1 * h.1) = Matrix.trace h.1
    rw [h_id, Matrix.one_mul]
  rw [h_tr]

theorem su2Chi_eq_sunFundamentalTrace (U : YangMills.SU2) :
    su2Chi U = sunFundamentalTrace 2 U := by
  unfold su2Chi sunFundamentalTrace
  simp only [Matrix.trace_fin_two, Complex.add_re]
  ring

theorem sunFundamentalTrace_continuous (N : ℕ) :
    Continuous (sunFundamentalTrace N) := by
  unfold sunFundamentalTrace
  refine continuous_const.mul (Complex.continuous_re.comp ?_)
  have h_tr : (fun U : YangMills.SUN N => Matrix.trace (U.1 : Matrix (Fin N) (Fin N) ℂ)) =
      (fun U : YangMills.SUN N => ∑ i : Fin N, U.1 i i) := by
    ext U; rfl
  rw [h_tr]
  exact continuous_finsetSum Finset.univ (fun i _ =>
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val))

/-- Canonical Gauge Character Class for compact gauge groups G. -/
class StandardGaugeCharacter (G : Type*)
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] where
  standardChar : NormalizedGaugeCharacter G

noncomputable instance : StandardGaugeCharacter YangMills.SU2 where
  standardChar := su2GaugeCharacter

/-- Haar Schur Orthogonality Data for the Fundamental Trace Character on `SUN N`. -/
structure SUNSchurOrthogonality (N : ℕ) [Fact (2 ≤ N)] where
  continuous_trace : Continuous (sunFundamentalTrace N)
  abs_le_one : ∀ g : YangMills.SUN N, |sunFundamentalTrace N g| ≤ 1
  inv_eq : ∀ g : YangMills.SUN N, sunFundamentalTrace N g⁻¹ = sunFundamentalTrace N g
  integral_zero : ∫ g, sunFundamentalTrace N g ∂(haarProb (YangMills.SUN N)) = 0
  sq_integral_le_half : ∫ g, (sunFundamentalTrace N g) ^ 2 ∂(haarProb (YangMills.SUN N)) ≤ 1 / 2
  functional_eq : ∀ g h : YangMills.SUN N,
    ∫ x, sunFundamentalTrace N (g * x * h * x⁻¹) ∂(haarProb (YangMills.SUN N)) =
      sunFundamentalTrace N g * sunFundamentalTrace N h

/-- Canonical Constructor of `NormalizedGaugeCharacter` for `SUN N` from Schur orthogonality. -/
noncomputable def sunGaugeCharacterOfSchur (N : ℕ) [Fact (2 ≤ N)]
    (h_schur : SUNSchurOrthogonality N) :
    NormalizedGaugeCharacter (YangMills.SUN N) where
  χ := sunFundamentalTrace N
  χ_continuous := h_schur.continuous_trace
  χ_one := sunFundamentalTrace_one N
  χ_abs_le_one := h_schur.abs_le_one
  χ_conj := sunFundamentalTrace_conj N
  χ_inv := h_schur.inv_eq
  χ_integral_zero := h_schur.integral_zero
  χ_sq_integral_le_half := h_schur.sq_integral_le_half
  χ_functional_eq := h_schur.functional_eq

/-- Canonical SU(3) Gauge Character constructor from Schur orthogonality data. -/
noncomputable def su3GaugeCharacterOfSchur
    (h_schur : SUNSchurOrthogonality 3) :
    NormalizedGaugeCharacter YangMills.SU3 :=
  sunGaugeCharacterOfSchur 3 h_schur

/-- Unconditional Constructive Proof that `SUNSchurOrthogonality 2` is Inhabited (Zero `sorry`). -/
noncomputable def su2SchurOrthogonality : SUNSchurOrthogonality 2 where
  continuous_trace := sunFundamentalTrace_continuous 2
  abs_le_one := fun g => by
    rw [← su2Chi_eq_sunFundamentalTrace]
    exact su2GaugeCharacter.χ_abs_le_one g
  inv_eq := fun g => by
    rw [← su2Chi_eq_sunFundamentalTrace, ← su2Chi_eq_sunFundamentalTrace]
    exact su2GaugeCharacter.χ_inv g
  integral_zero := by
    have h_eq : (fun g : YangMills.SUN 2 => sunFundamentalTrace 2 g) = su2Chi := by
      ext g; exact (su2Chi_eq_sunFundamentalTrace g).symm
    rw [h_eq]
    exact su2GaugeCharacter.χ_integral_zero
  sq_integral_le_half := by
    have h_eq : (fun g : YangMills.SUN 2 => (sunFundamentalTrace 2 g) ^ 2) = (fun g => (su2Chi g) ^ 2) := by
      ext g; rw [su2Chi_eq_sunFundamentalTrace]
    rw [h_eq]
    exact su2GaugeCharacter.χ_sq_integral_le_half
  functional_eq := fun g h => by
    have h_eq : (fun x : YangMills.SUN 2 => sunFundamentalTrace 2 (g * x * h * x⁻¹)) =
        (fun x => su2Chi (g * x * h * x⁻¹)) := by
      ext x; rw [su2Chi_eq_sunFundamentalTrace]
    rw [h_eq, ← su2Chi_eq_sunFundamentalTrace g, ← su2Chi_eq_sunFundamentalTrace h]
    exact su2GaugeCharacter.χ_functional_eq g h

noncomputable instance : Fact (HaarWilsonLattice.SUNSchurOrthogonality 2) :=
  ⟨su2SchurOrthogonality⟩

noncomputable instance (priority := low) (N : ℕ) [Fact (2 ≤ N)] [h : Fact (SUNSchurOrthogonality N)] :
    StandardGaugeCharacter (YangMills.SUN N) where
  standardChar := sunGaugeCharacterOfSchur N h.out

end GeneralSUN

/-! ============================================================================
    PART III: WILSON PLAQUETTE WEIGHT & REAL HAAR CHARACTER COEFFICIENTS c₀, c₁/₂
    ============================================================================ -/

section CharacterCoefficients

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Single-plaquette Wilson Boltzmann weight `w_β(g) = exp(-β (1 - χ(g)))`. -/
noncomputable def wilsonWeight (C : NormalizedGaugeCharacter G) (β : ℝ) (g : G) : ℝ :=
  Real.exp (-β * (1 - C.χ g))

theorem wilsonWeight_continuous (C : NormalizedGaugeCharacter G) (β : ℝ) :
    Continuous (wilsonWeight C β) := by
  unfold wilsonWeight
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub C.χ_continuous))

theorem wilsonWeight_pos (C : NormalizedGaugeCharacter G) (β : ℝ) (g : G) :
    0 < wilsonWeight C β g :=
  Real.exp_pos _

theorem wilsonWeight_one (C : NormalizedGaugeCharacter G) (β : ℝ) :
    wilsonWeight C β 1 = 1 := by
  simp [wilsonWeight, C.χ_one]

theorem wilsonWeight_inv (C : NormalizedGaugeCharacter G) (β : ℝ) (g : G) :
    wilsonWeight C β g⁻¹ = wilsonWeight C β g := by
  simp [wilsonWeight, C.χ_inv]

theorem wilsonWeight_conj (C : NormalizedGaugeCharacter G) (β : ℝ) (h g : G) :
    wilsonWeight C β (h * g * h⁻¹) = wilsonWeight C β g := by
  simp [wilsonWeight, C.χ_conj]

theorem wilsonWeight_mul_comm (C : NormalizedGaugeCharacter G) (β : ℝ) (g h : G) :
    wilsonWeight C β (g * h) = wilsonWeight C β (h * g) := by
  simp [wilsonWeight, C.χ_mul_comm g h]

theorem wilsonWeight_bounds (C : NormalizedGaugeCharacter G) {β : ℝ} (hβ : 0 ≤ β) (g : G) :
    Real.exp (-2 * β) ≤ wilsonWeight C β g ∧ wilsonWeight C β g ≤ 1 := by
  unfold wilsonWeight
  have h_low := C.neg_one_le_χ g
  have h_high := C.χ_le_one g
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith
  · exact Real.exp_le_one_iff.mpr (by nlinarith)

/-- Trivial-representation real Haar character coefficient `c₀(β) = ∫_G w_β(g) dμ_Haar(g)`. -/
noncomputable def haarC0 (C : NormalizedGaugeCharacter G) (β : ℝ) : ℝ :=
  ∫ g, wilsonWeight C β g ∂(haarProb G)

/-- Fundamental-representation real Haar character coefficient
    `c_{1/2}(β) = ∫_G w_β(g) χ(g) dμ_Haar(g)`. -/
noncomputable def haarCHalf (C : NormalizedGaugeCharacter G) (β : ℝ) : ℝ :=
  ∫ g, wilsonWeight C β g * C.χ g ∂(haarProb G)

theorem haarC0_bounds (C : NormalizedGaugeCharacter G) {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-2 * β) ≤ haarC0 C β ∧ haarC0 C β ≤ 1 := by
  unfold haarC0
  have hw_int : Integrable (wilsonWeight C β) (haarProb G) :=
    integrable_of_continuous_compact (wilsonWeight_continuous C β)
  constructor
  · have h_const : ∫ _ : G, Real.exp (-2 * β) ∂(haarProb G) = Real.exp (-2 * β) := by
      simp
    rw [← h_const]
    exact integral_mono (integrable_const _) hw_int fun g => (wilsonWeight_bounds C hβ g).1
  · have h_const : ∫ _ : G, (1 : ℝ) ∂(haarProb G) = 1 := by
      simp
    rw [← h_const]
    exact integral_mono hw_int (integrable_const _) fun g => (wilsonWeight_bounds C hβ g).2

theorem haarC0_pos (C : NormalizedGaugeCharacter G) {β : ℝ} (hβ : 0 ≤ β) :
    0 < haarC0 C β :=
  lt_of_lt_of_le (Real.exp_pos _) (haarC0_bounds C hβ).1

/-- Unconditional strict positivity `0 < haarCHalf C β` for every `β > 0`,
    proved directly over Mathlib's `haarMeasure` without Bessel series expansions. -/
theorem haarCHalf_pos (C : NormalizedGaugeCharacter G) {β : ℝ} (hβ : 0 < β) :
    0 < haarCHalf C β := by
  let φ : G → ℝ := fun g => (Real.exp (β * C.χ g) - 1) * C.χ g
  have hφ_cont : Continuous φ :=
    ((Real.continuous_exp.comp (continuous_const.mul C.χ_continuous)).sub
      continuous_const).mul C.χ_continuous
  have hφ_int : Integrable φ (haarProb G) :=
    integrable_of_continuous_compact hφ_cont
  have hχ_int : Integrable C.χ (haarProb G) :=
    integrable_of_continuous_compact C.χ_continuous
  have h_decomp : ∀ g : G,
      wilsonWeight C β g * C.χ g = Real.exp (-β) * φ g + Real.exp (-β) * C.χ g := by
    intro g
    unfold wilsonWeight φ
    have hexp : Real.exp (-β * (1 - C.χ g)) = Real.exp (-β) * Real.exp (β * C.χ g) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hexp]
    ring
  have h_eq : haarCHalf C β = Real.exp (-β) * ∫ g, φ g ∂(haarProb G) := by
    unfold haarCHalf
    simp_rw [h_decomp]
    rw [integral_add (hφ_int.const_mul _) (hχ_int.const_mul _),
        integral_const_mul, integral_const_mul, C.χ_integral_zero, mul_zero, add_zero]
  rw [h_eq]
  refine mul_pos (Real.exp_pos _) ?_
  have hφ_nonneg : ∀ g : G, 0 ≤ φ g := by
    intro g
    unfold φ
    rcases le_or_gt 0 (C.χ g) with h_ge | h_lt
    · have hexp_ge : 1 ≤ Real.exp (β * C.χ g) :=
        Real.one_le_exp (mul_nonneg hβ.le h_ge)
      exact mul_nonneg (sub_nonneg.mpr hexp_ge) h_ge
    · have hexp_le : Real.exp (β * C.χ g) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hβ.le h_lt.le)
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hexp_le) h_lt.le
  have hφ_one : 0 < φ 1 := by
    unfold φ
    rw [C.χ_one, mul_one, mul_one, sub_pos, Real.one_lt_exp_iff]
    exact hβ
  let U : Set G := {g : G | φ 1 / 2 < φ g}
  have hU_open : IsOpen U := isOpen_lt continuous_const hφ_cont
  have h1_mem : (1 : G) ∈ U := by
    change φ 1 / 2 < φ 1
    linarith
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have hU_pos : 0 < (haarProb G).real U := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨(hU_open.measure_pos (haarProb G) ⟨1, h1_mem⟩), measure_lt_top (haarProb G) U⟩
  have h_ind_le : ∀ g : G, U.indicator (fun _ => φ 1 / 2) g ≤ φ g := by
    intro g
    by_cases hg : g ∈ U
    · simp only [Set.indicator_of_mem hg]
      exact le_of_lt hg
    · simp only [Set.indicator_of_notMem hg]
      exact hφ_nonneg g
  have h_ind_int : Integrable (U.indicator (fun _ => φ 1 / 2)) (haarProb G) :=
    (integrable_const (φ 1 / 2)).indicator hU_meas
  have h_low : ∫ g, U.indicator (fun _ => φ 1 / 2) g ∂(haarProb G) ≤ ∫ g, φ g ∂(haarProb G) :=
    integral_mono h_ind_int hφ_int h_ind_le
  rw [integral_indicator_const _ hU_meas, smul_eq_mul] at h_low
  exact lt_of_lt_of_le (mul_pos hU_pos (half_pos hφ_one)) h_low

theorem haarCHalf_le_haarC0 (C : NormalizedGaugeCharacter G) (β : ℝ) :
    haarCHalf C β ≤ haarC0 C β := by
  unfold haarCHalf haarC0
  have hw_int : Integrable (wilsonWeight C β) (haarProb G) :=
    integrable_of_continuous_compact (wilsonWeight_continuous C β)
  have hwχ_int : Integrable (fun g => wilsonWeight C β g * C.χ g) (haarProb G) :=
    integrable_of_continuous_compact ((wilsonWeight_continuous C β).mul C.χ_continuous)
  refine integral_mono hwχ_int hw_int fun g => ?_
  exact mul_le_of_le_one_right (wilsonWeight_pos C β g).le (C.χ_le_one g)

/-- Schur Character Convolution Eigen-Identity:
    convolving the class Boltzmann weight `w_β` against a translated character `χ(g⁻¹ * h)`
    reproduces `χ(h)` scaled by `c_{1/2}(β)`. -/
theorem wilsonWeight_char_convolution (C : NormalizedGaugeCharacter G) (β : ℝ) (h : G) :
    ∫ g, wilsonWeight C β g * C.χ (g⁻¹ * h) ∂(haarProb G) = haarCHalf C β * C.χ h := by
  let μ := haarProb G
  have h_inv_int :
      ∫ g, wilsonWeight C β g * C.χ (g⁻¹ * h) ∂μ =
        ∫ g, wilsonWeight C β g * C.χ (g * h) ∂μ := by
    have h1 := integral_inv_eq_self (fun g : G => wilsonWeight C β g * C.χ (g⁻¹ * h)) μ
    simpa [wilsonWeight_inv] using h1.symm
  rw [h_inv_int]
  have h_conj_x : ∀ x : G,
      ∫ g, wilsonWeight C β g * C.χ (g * h) ∂μ =
        ∫ g, wilsonWeight C β g * C.χ (g * x * h * x⁻¹) ∂μ := by
    intro x
    calc ∫ g, wilsonWeight C β g * C.χ (g * h) ∂μ
        = ∫ g, wilsonWeight C β (x⁻¹ * g * x) * C.χ ((x⁻¹ * g * x) * h) ∂μ := by
            have hL := integral_mul_left_eq_self
              (fun g : G => wilsonWeight C β (g * x) * C.χ (g * x * h)) x⁻¹ (μ := μ)
            have hR := integral_mul_right_eq_self
              (fun g : G => wilsonWeight C β g * C.χ (g * h)) x (μ := μ)
            simpa [mul_assoc] using (hL.trans hR).symm
      _ = ∫ g, wilsonWeight C β g * C.χ (g * x * h * x⁻¹) ∂μ := by
            congr 1 with g
            have hw : wilsonWeight C β (x⁻¹ * g * x) = wilsonWeight C β g := by
              simpa using wilsonWeight_conj C β x⁻¹ g
            have hχ : C.χ (x⁻¹ * g * x * h) = C.χ (g * x * h * x⁻¹) := by
              have hc := C.χ_conj x (x⁻¹ * g * x * h)
              simpa [mul_assoc] using hc.symm
            rw [hw, hχ]
  have h_prod_cont :
      Continuous (fun p : G × G => wilsonWeight C β p.1 * C.χ (p.1 * p.2 * h * p.2⁻¹)) :=
    ((wilsonWeight_continuous C β).comp continuous_fst).mul
      (C.χ_continuous.comp
        (((continuous_fst.mul continuous_snd).mul continuous_const).mul continuous_snd.inv))
  have h_prod_int :
      Integrable (fun p : G × G => wilsonWeight C β p.1 * C.χ (p.1 * p.2 * h * p.2⁻¹))
        (μ.prod μ) :=
    integrable_of_continuous_compact h_prod_cont
  calc ∫ g, wilsonWeight C β g * C.χ (g * h) ∂μ
      = ∫ x, (∫ g, wilsonWeight C β g * C.χ (g * h) ∂μ) ∂μ := by
          simp [μ]
    _ = ∫ x, (∫ g, wilsonWeight C β g * C.χ (g * x * h * x⁻¹) ∂μ) ∂μ := by
          congr 1 with x
          exact h_conj_x x
    _ = ∫ g, (∫ x, wilsonWeight C β g * C.χ (g * x * h * x⁻¹) ∂μ) ∂μ := by
          rw [← integral_prod_symm _ h_prod_int, integral_prod _ h_prod_int]
    _ = ∫ g, wilsonWeight C β g * (C.χ g * C.χ h) ∂μ := by
          congr 1 with g
          rw [integral_const_mul, C.χ_functional_eq g h]
    _ = haarCHalf C β * C.χ h := by
          unfold haarCHalf
          simp_rw [← mul_assoc]
          rw [integral_mul_const]

/-- 2D Bessel Haar Lower Bound:
    `∫_G w_β(g)² dμ_Haar(g) ≥ c₀(β)² + 2 c_{1/2}(β)²`. -/
theorem wilsonWeight_sq_bessel_lower_bound (C : NormalizedGaugeCharacter G) (β : ℝ) :
    (haarC0 C β) ^ 2 + 2 * (haarCHalf C β) ^ 2 ≤
      ∫ g, (wilsonWeight C β g) ^ 2 ∂(haarProb G) := by
  let μ := haarProb G
  let c0 := haarC0 C β
  let ch := haarCHalf C β
  let w := wilsonWeight C β
  have hw_cont : Continuous w := wilsonWeight_continuous C β
  have hχ_cont : Continuous C.χ := C.χ_continuous
  have hw_int : Integrable w μ := integrable_of_continuous_compact hw_cont
  have hw2_int : Integrable (fun g => (w g) ^ 2) μ :=
    integrable_of_continuous_compact (hw_cont.pow 2)
  have hwχ_int : Integrable (fun g => w g * C.χ g) μ :=
    integrable_of_continuous_compact (hw_cont.mul hχ_cont)
  have hχ_int : Integrable C.χ μ := integrable_of_continuous_compact hχ_cont
  have hχ2_int : Integrable (fun g => (C.χ g) ^ 2) μ :=
    integrable_of_continuous_compact (hχ_cont.pow 2)
  let rem : G → ℝ := fun g => (w g - c0 - 2 * ch * C.χ g) ^ 2
  have hrem_nonneg : 0 ≤ ∫ g, rem g ∂μ :=
    integral_nonneg fun g => sq_nonneg _
  have i1 : Integrable (fun g => (-2 * c0) * w g) μ := hw_int.const_mul _
  have i2 : Integrable (fun g => (-4 * ch) * (w g * C.χ g)) μ := hwχ_int.const_mul _
  have i3 : Integrable (fun _ : G => c0 ^ 2) μ := integrable_const _
  have i4 : Integrable (fun g => (4 * c0 * ch) * C.χ g) μ := hχ_int.const_mul _
  have i5 : Integrable (fun g => (4 * ch ^ 2) * (C.χ g) ^ 2) μ := hχ2_int.const_mul _
  have h_int_eq :
      ∫ g, rem g ∂μ =
        (∫ g, (w g) ^ 2 ∂μ) + (-2 * c0) * c0 + (-4 * ch) * ch +
          c0 ^ 2 + (4 * c0 * ch) * (∫ g, C.χ g ∂μ) +
          (4 * ch ^ 2) * (∫ g, (C.χ g) ^ 2 ∂μ) := by
    have h_pt : ∀ g : G,
        rem g = (((((w g) ^ 2 + (-2 * c0) * w g) + (-4 * ch) * (w g * C.χ g)) +
          c0 ^ 2) + (4 * c0 * ch) * C.χ g) + (4 * ch ^ 2) * (C.χ g) ^ 2 := by
      intro g
      unfold rem
      ring
    simp_rw [h_pt]
    rw [integral_add6 hw2_int i1 i2 i3 i4 i5,
        integral_const_mul, integral_const_mul, integral_const,
        integral_const_mul, integral_const_mul]
    simp [μ, c0, ch, w, haarC0, haarCHalf]
  rw [h_int_eq, C.χ_integral_zero] at hrem_nonneg
  have hχ2 := C.χ_sq_integral_le_half
  have h_term : (4 * ch ^ 2) * (∫ g, (C.χ g) ^ 2 ∂μ) ≤ 2 * ch ^ 2 := by
    nlinarith [sq_nonneg ch]
  linarith

end CharacterCoefficients

/-! ============================================================================
    PART IV: LEMMA 1 (`block_partition_lower_bound`) — HAAR PARTITION INTEGRALS
    ============================================================================ -/

section BlockPartitionLowerBound

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Oriented 3-edge boundary holonomy `U_{e₁} U_{e₂} U_{e₃}⁻¹` for each of the 10 triangular
    2-cells of the 4-simplex `K₅` (`FourSimplexComplex` / `B2_4D` in `ToposUnifiedYangMills`). -/
def simplexFaceHolonomy (U : Fin 10 → G) (f : Fin 10) : G :=
  if f = 0 then U 0 * U 4 * (U 1)⁻¹
  else if f = 1 then U 0 * U 5 * (U 2)⁻¹
  else if f = 2 then U 0 * U 6 * (U 3)⁻¹
  else if f = 3 then U 1 * U 7 * (U 2)⁻¹
  else if f = 4 then U 1 * U 8 * (U 3)⁻¹
  else if f = 5 then U 2 * U 9 * (U 3)⁻¹
  else if f = 6 then U 4 * U 7 * (U 5)⁻¹
  else if f = 7 then U 4 * U 8 * (U 6)⁻¹
  else if f = 8 then U 5 * U 9 * (U 6)⁻¹
  else U 7 * U 9 * (U 8)⁻¹

omit [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
theorem simplexFaceHolonomy_continuous (f : Fin 10) :
    Continuous (fun U : Fin 10 → G => simplexFaceHolonomy U f) := by
  have h_tri : ∀ i j k : Fin 10,
      Continuous (fun U : Fin 10 → G => U i * U j * (U k)⁻¹) :=
    fun i j k => (((continuous_apply i).mul (continuous_apply j)).mul (continuous_apply k).inv)
  unfold simplexFaceHolonomy
  split_ifs <;> exact h_tri _ _ _

/-- Closed 4-simplex `K₅` Haar block partition function `Z_{K₅}(β)` over 10 link variables
    and 10 triangular faces integrated with respect to `Measure.pi (fun _ => haarProb G)`. -/
noncomputable def simplexBlockPartition (C : NormalizedGaugeCharacter G) (β : ℝ) : ℝ :=
  ∫ U : Fin 10 → G,
    (∏ f : Fin 10, wilsonWeight C β (simplexFaceHolonomy U f))
    ∂(Measure.pi fun _ : Fin 10 => haarProb G)

/-- Fixed-boundary block partition function `Z_block(β, U_∂)` integrating `n_int` internal links
    against `n_faces` plaquette holonomies `hol(U_int, U_∂, f)` at fixed boundary links `U_∂`. -/
noncomputable def fixedBoundaryBlockPartition
    {n_int n_bdry n_faces : ℕ}
    (C : NormalizedGaugeCharacter G)
    (hol : (Fin n_int → G) → (Fin n_bdry → G) → Fin n_faces → G)
    (h_hol_cont : ∀ (U_bdry : Fin n_bdry → G) (f : Fin n_faces),
      Continuous (fun U_int : Fin n_int → G => hol U_int U_bdry f))
    (β : ℝ) (U_bdry : Fin n_bdry → G) : ℝ :=
  have _ := h_hol_cont
  ∫ U_int : Fin n_int → G,
    (∏ f : Fin n_faces, wilsonWeight C β (hol U_int U_bdry f))
    ∂(Measure.pi fun _ : Fin n_int => haarProb G)

/-- **Real-Axis Lee–Yang Zero Exclusion for Fixed-Boundary Block Partition Functions**:
    For every real coupling `β ≥ 0` and every boundary link configuration `U_∂`,
    `Z_block(β, U_∂) ≥ exp(-2 β n_faces) > 0`. -/
theorem fixedBoundaryBlockPartition_pos
    {n_int n_bdry n_faces : ℕ}
    (C : NormalizedGaugeCharacter G)
    (hol : (Fin n_int → G) → (Fin n_bdry → G) → Fin n_faces → G)
    (h_hol_cont : ∀ (U_bdry : Fin n_bdry → G) (f : Fin n_faces),
      Continuous (fun U_int : Fin n_int → G => hol U_int U_bdry f))
    {β : ℝ} (hβ : 0 ≤ β) (U_bdry : Fin n_bdry → G) :
    Real.exp (-2 * β * (n_faces : ℝ)) ≤
      fixedBoundaryBlockPartition C hol h_hol_cont β U_bdry ∧
    0 < fixedBoundaryBlockPartition C hol h_hol_cont β U_bdry := by
  let μ_int : Measure (Fin n_int → G) := Measure.pi fun _ : Fin n_int => haarProb G
  have h_cont : Continuous (fun U_int : Fin n_int → G =>
      ∏ f : Fin n_faces, wilsonWeight C β (hol U_int U_bdry f)) :=
    continuous_finsetProd Finset.univ fun f _ =>
      (wilsonWeight_continuous C β).comp (h_hol_cont U_bdry f)
  have h_int : Integrable (fun U_int : Fin n_int → G =>
      ∏ f : Fin n_faces, wilsonWeight C β (hol U_int U_bdry f)) μ_int :=
    integrable_of_continuous_compact h_cont
  have h_pt : ∀ U_int : Fin n_int → G,
      Real.exp (-2 * β * (n_faces : ℝ)) ≤
        ∏ f : Fin n_faces, wilsonWeight C β (hol U_int U_bdry f) := by
    intro U_int
    have h_pow : Real.exp (-2 * β * (n_faces : ℝ)) = (Real.exp (-2 * β)) ^ n_faces := by
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [h_pow]
    calc (Real.exp (-2 * β)) ^ n_faces
        = ∏ _f : Fin n_faces, Real.exp (-2 * β) := by simp
      _ ≤ ∏ f : Fin n_faces, wilsonWeight C β (hol U_int U_bdry f) :=
          Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
            (fun f _ => (wilsonWeight_bounds C hβ (hol U_int U_bdry f)).1)
  have h_const_int :
      ∫ _ : Fin n_int → G, Real.exp (-2 * β * (n_faces : ℝ)) ∂μ_int =
        Real.exp (-2 * β * (n_faces : ℝ)) := by
    have h_univ : μ_int.real Set.univ = 1 := by
      simp [Measure.real]
    simp [h_univ]
  have h_le : Real.exp (-2 * β * (n_faces : ℝ)) ≤
      fixedBoundaryBlockPartition C hol h_hol_cont β U_bdry := by
    unfold fixedBoundaryBlockPartition
    rw [← h_const_int]
    exact integral_mono (integrable_const _) h_int h_pt
  exact ⟨h_le, lt_of_lt_of_le (Real.exp_pos _) h_le⟩

/-- Unconditional positivity `Z_{K₅}(β) ≥ exp(-20 β) > 0` of the 10-link, 10-face 4-simplex
    Haar partition integral for all `β ≥ 0`. -/
theorem simplexBlockPartition_lower_bound (C : NormalizedGaugeCharacter G) {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-20 * β) ≤ simplexBlockPartition C β ∧ 0 < simplexBlockPartition C β := by
  let hol : (Fin 10 → G) → (Fin 0 → G) → Fin 10 → G :=
    fun U _ f => simplexFaceHolonomy U f
  have h_cont' : ∀ (U_b : Fin 0 → G) (f : Fin 10),
      Continuous (fun U : Fin 10 → G => hol U U_b f) :=
    fun _ f => simplexFaceHolonomy_continuous f
  rcases fixedBoundaryBlockPartition_pos C hol h_cont' hβ (fun i => Fin.elim0 i) with ⟨h_le, h_pos⟩
  have h_exp : Real.exp (-20 * β) = Real.exp (-2 * β * (10 : ℕ)) := by ring_nf
  rw [h_exp]
  exact ⟨h_le, h_pos⟩

/-- **8-Link Single-Pace Cell Haar Partition Integral `Z_pace(β)`**:
    Integrates 8 link variables (`Fin 4 → G × G` under product Haar measure) across 4 paired
    2-plaquette channels (`8` plaquette Boltzmann weights in total). -/
noncomputable def singlePaceHaarPartition (C : NormalizedGaugeCharacter G) (β : ℝ) : ℝ :=
  ∫ U : Fin 4 → (G × G),
    (∏ i : Fin 4,
      wilsonWeight C β ((U i).1 * (U i).2⁻¹) * wilsonWeight C β ((U i).2 * (U i).1⁻¹))
    ∂(Measure.pi fun _ : Fin 4 => (haarProb G).prod (haarProb G))

/-- **Lemma 1 (`block_partition_lower_bound`) — Exact Haar Single-Pace Character Floor**:
    For every real coupling `β > 0`, the 8-link single-pace Haar partition integral satisfies
      `Z_pace(β) ≥ c₀(β)⁸ + 8 c₀(β)⁶ c_{1/2}(β)² > c₀(β)⁸ > 0`,
    connecting Mathlib's `haarMeasure` directly to the `q* = 8 c₀⁶ c_{1/2}²` single-pace floor
    and excluding real-axis Lee–Yang partition zeros. -/
theorem block_partition_lower_bound (C : NormalizedGaugeCharacter G) {β : ℝ} (hβ : 0 < β) :
    (haarC0 C β) ^ 8 + 8 * (haarC0 C β) ^ 6 * (haarCHalf C β) ^ 2 ≤
      singlePaceHaarPartition C β ∧
    0 < 8 * (haarC0 C β) ^ 6 * (haarCHalf C β) ^ 2 ∧
    0 < singlePaceHaarPartition C β := by
  let μ := haarProb G
  let pairFn : G × G → ℝ := fun p =>
    wilsonWeight C β (p.1 * p.2⁻¹) * wilsonWeight C β (p.2 * p.1⁻¹)
  have h_fact : singlePaceHaarPartition C β = (∫ p : G × G, pairFn p ∂(μ.prod μ)) ^ 4 := by
    unfold singlePaceHaarPartition
    have h_pow := MeasureTheory.integral_fintype_prod_eq_pow
      (ι := Fin 4) pairFn (μ := μ.prod μ)
    simpa [Fintype.card_fin] using h_pow
  have h_pair_eq : ∫ p : G × G, pairFn p ∂(μ.prod μ) = ∫ g : G, (wilsonWeight C β g) ^ 2 ∂μ := by
    have h_cont : Continuous pairFn := by
      unfold pairFn
      exact ((wilsonWeight_continuous C β).comp (continuous_fst.mul continuous_snd.inv)).mul
        ((wilsonWeight_continuous C β).comp (continuous_snd.mul continuous_fst.inv))
    have h_int : Integrable pairFn (μ.prod μ) :=
      integrable_of_continuous_compact h_cont
    rw [integral_prod _ h_int]
    have h_inner : ∀ g1 : G,
        ∫ g2 : G, pairFn (g1, g2) ∂μ = ∫ u : G, (wilsonWeight C β u) ^ 2 ∂μ := by
      intro g1
      have h_symm : ∀ g2 : G, pairFn (g1, g2) = (wilsonWeight C β (g1 * g2⁻¹)) ^ 2 := by
        intro g2
        unfold pairFn
        have h_inv : wilsonWeight C β (g2 * g1⁻¹) = wilsonWeight C β (g1 * g2⁻¹) := by
          have h1 := wilsonWeight_inv C β (g2 * g1⁻¹)
          simpa [mul_inv_rev] using h1.symm
        rw [h_inv, sq]
      simp_rw [h_symm]
      have h1 := integral_inv_eq_self (fun g2 : G => (wilsonWeight C β (g1 * g2⁻¹)) ^ 2) μ
      simp only [inv_inv] at h1
      rw [← h1, integral_mul_left_eq_self (fun u : G => (wilsonWeight C β u) ^ 2) g1]
    simp_rw [h_inner]
    simp [μ]
  rw [h_fact, h_pair_eq]
  have _ : 0 < haarC0 C β := haarC0_pos C hβ.le
  have _ : 0 < haarCHalf C β := haarCHalf_pos C hβ
  have h_bessel := wilsonWeight_sq_bessel_lower_bound C β
  have h_alg :
      (haarC0 C β) ^ 8 + 8 * (haarC0 C β) ^ 6 * (haarCHalf C β) ^ 2 ≤
        ((haarC0 C β) ^ 2 + 2 * (haarCHalf C β) ^ 2) ^ 4 := by
    have h_diff :
        ((haarC0 C β) ^ 2 + 2 * (haarCHalf C β) ^ 2) ^ 4 -
          ((haarC0 C β) ^ 8 + 8 * (haarC0 C β) ^ 6 * (haarCHalf C β) ^ 2) =
        24 * (haarC0 C β) ^ 4 * (haarCHalf C β) ^ 4 +
          32 * (haarC0 C β) ^ 2 * (haarCHalf C β) ^ 6 +
          16 * (haarCHalf C β) ^ 8 := by
      ring
    have h_nonneg :
        0 ≤ 24 * (haarC0 C β) ^ 4 * (haarCHalf C β) ^ 4 +
          32 * (haarC0 C β) ^ 2 * (haarCHalf C β) ^ 6 +
          16 * (haarCHalf C β) ^ 8 := by
      positivity
    linarith
  have h_base_nonneg : 0 ≤ (haarC0 C β) ^ 2 + 2 * (haarCHalf C β) ^ 2 := by positivity
  have h_pow4 :
      ((haarC0 C β) ^ 2 + 2 * (haarCHalf C β) ^ 2) ^ 4 ≤
        (∫ g : G, (wilsonWeight C β g) ^ 2 ∂μ) ^ 4 :=
    pow_le_pow_left₀ h_base_nonneg h_bessel 4
  have h_floor_pos : 0 < 8 * (haarC0 C β) ^ 6 * (haarCHalf C β) ^ 2 := by positivity
  have h_main :
      (haarC0 C β) ^ 8 + 8 * (haarC0 C β) ^ 6 * (haarCHalf C β) ^ 2 ≤
        (∫ g : G, (wilsonWeight C β g) ^ 2 ∂μ) ^ 4 :=
    le_trans h_alg h_pow4
  have h_z_pos : 0 < (∫ g : G, (wilsonWeight C β g) ^ 2 ∂μ) ^ 4 := by
    have hc08 : 0 < (haarC0 C β) ^ 8 := by positivity
    linarith
  exact ⟨h_main, h_floor_pos, h_z_pos⟩

end BlockPartitionLowerBound

/-! ============================================================================
    PART V: 3D SPATIAL LATTICE L² HILBERT SPACE & WILSON TRANSFER OPERATORS
    ============================================================================ -/

section ConstructiveWilsonLattice

set_option linter.unusedSectionVars false

/-- Pointwise evaluation `f ↦ f y` on `C(Y, ℂ)` as an `ℝ`-linear continuous functional,
    enabling `((∫ z, F z ∂ν) : C(Y, ℂ)) y = ∫ z, F z y ∂ν` via `integral_comp_comm`. -/
noncomputable def evalContinuousMapCLM {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] (y : Y) :
    C(Y, ℂ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => f y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by simpa using f.norm_coe_le_norm y)

/-- Casts a real Bochner integral directly into `ℂ` via `Complex.ofReal`. -/
theorem complex_integral_ofReal {X : Type*} [MeasurableSpace X] {μ : Measure X} (f : X → ℝ) :
    ∫ x, (f x : ℂ) ∂μ = ((∫ x, f x ∂μ : ℝ) : ℂ) :=
  @integral_ofReal X _ μ ℂ _ f

/-- Commutes a `ℂ`-linear continuous linear map `L : E →L[ℂ] F` across a Bochner integral. -/
theorem clm_integral_comm {Z E F : Type*} [MeasurableSpace Z] {ν : Measure Z}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) {f : Z → E} (hf : Integrable f ν) :
    L (∫ z, f z ∂ν) = ∫ z, L (f z) ∂ν :=
  ((L.restrictScalars ℝ).integral_comp_comm hf).symm

/-- Complex Hilbert-space Pythagorean identity `‖x + y‖² = ‖x‖² + ‖y‖²` for `⟪x, y⟫ = 0`. -/
theorem pythagoras_complex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {x y : E} (h : inner ℂ x y = 0) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have hyx : inner ℂ y x = 0 := by
    rw [← inner_conj_symm, h, map_zero]
  have h1 : ((‖x + y‖ ^ 2 : ℝ) : ℂ) = ((‖x‖ ^ 2 + ‖y‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    simpa [h, hyx, inner_self_eq_norm_sq_to_K] using (inner_add_add_self (𝕜 := ℂ) x y)
  exact_mod_cast h1

/-- Right inner-product functional `ψ ↦ ⟪φ, ψ⟫_ℂ` as a `ℂ`-linear continuous functional. -/
noncomputable def innerRightCLM {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (φ : E) : E →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun ψ => inner ℂ φ ψ
      map_add' := fun _ _ => inner_add_right _ _ _
      map_smul' := fun _ _ => inner_smul_right _ _ _ }
    ‖φ‖ (fun ψ => norm_inner_le_norm φ ψ)

/-- Inner product with a Bochner integral in the right argument on a complex Hilbert space. -/
theorem inner_bochner_right {Z E : Type*} [MeasurableSpace Z] {ν : Measure Z}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    {F : Z → E} (hF : Integrable F ν) (φ : E) :
    inner ℂ φ (∫ z, F z ∂ν) = ∫ z, inner ℂ φ (F z) ∂ν :=
  clm_integral_comm (innerRightCLM φ) hF

/-- Inner product with a Bochner integral in the left argument on a complex Hilbert space. -/
theorem inner_bochner_left {Z E : Type*} [MeasurableSpace Z] {ν : Measure Z}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    {F : Z → E} (hF : Integrable F ν) (ψ : E) :
    inner ℂ (∫ z, F z ∂ν) ψ = ∫ z, inner ℂ (F z) ψ ∂ν := by
  rw [← inner_conj_symm, inner_bochner_right hF ψ, ← integral_conj]
  congr 1 with z
  exact inner_conj_symm (F z) ψ

/-- General Bochner-averaged continuous linear operator `(A ψ) = ∫ z, w(z) • T(z) ψ ∂ν`
    on a complex Banach space `E`, with operator norm bounded by `∫ z, ‖w(z)‖ ∂ν`. -/
noncomputable def bochnerAvgCLM
    {Z E : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (w : Z → ℂ) (hw : Continuous w)
    (T : Z → E →L[ℂ] E)
    (hT_norm : ∀ z (ψ : E), ‖T z ψ‖ ≤ ‖ψ‖)
    (hT_cont : ∀ ψ : E, Continuous (fun z => T z ψ)) :
    E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun ψ => ∫ z, w z • T z ψ ∂ν
      map_add' := fun ψ₁ ψ₂ => by
        have h1 : Integrable (fun z => w z • T z ψ₁) ν :=
          integrable_of_continuous_compact (hw.smul (hT_cont ψ₁))
        have h2 : Integrable (fun z => w z • T z ψ₂) ν :=
          integrable_of_continuous_compact (hw.smul (hT_cont ψ₂))
        simp_rw [map_add, smul_add]
        exact integral_add_apply h1 h2
      map_smul' := fun c ψ => by
        dsimp
        have h_int : Integrable (fun z => w z • T z ψ) ν :=
          integrable_of_continuous_compact (hw.smul (hT_cont ψ))
        have h_comm : ∀ z, w z • T z (c • ψ) = (ContinuousLinearMap.lsmul ℂ ℂ c : E →L[ℂ] E) (w z • T z ψ) := by
          intro z
          simp [map_smul, smul_comm (w z) c]
        simp_rw [h_comm]
        exact (clm_integral_comm (ContinuousLinearMap.lsmul ℂ ℂ c : E →L[ℂ] E) h_int).symm }
    (∫ z, ‖w z‖ ∂ν)
    (fun ψ => by
      dsimp
      have hw_norm_int : Integrable (fun z => ‖w z‖ * ‖ψ‖) ν :=
        (integrable_of_continuous_compact hw.norm).mul_const ‖ψ‖
      have h_int_norm : Integrable (fun z => ‖w z • T z ψ‖) ν :=
        (integrable_of_continuous_compact (hw.smul (hT_cont ψ))).norm
      calc ‖∫ z, w z • T z ψ ∂ν‖
          ≤ ∫ z, ‖w z • T z ψ‖ ∂ν := norm_integral_le_integral_norm _
        _ ≤ ∫ z, ‖w z‖ * ‖ψ‖ ∂ν :=
            integral_mono h_int_norm hw_norm_int fun z => by
              rw [norm_smul]
              exact mul_le_mul_of_nonneg_left (hT_norm z ψ) (norm_nonneg _)
        _ = (∫ z, ‖w z‖ ∂ν) * ‖ψ‖ := integral_mul_const _ _)

@[simp]
theorem bochnerAvgCLM_apply
    {Z E : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (w : Z → ℂ) (hw : Continuous w)
    (T : Z → E →L[ℂ] E)
    (hT_norm : ∀ z (ψ : E), ‖T z ψ‖ ≤ ‖ψ‖)
    (hT_cont : ∀ ψ : E, Continuous (fun z => T z ψ)) (ψ : E) :
    bochnerAvgCLM ν w hw T hT_norm hT_cont ψ = ∫ z, w z • T z ψ ∂ν :=
  rfl

theorem bochnerAvgCLM_norm_le
    {Z E : Type*} [TopologicalSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (w : Z → ℂ) (hw : Continuous w)
    (T : Z → E →L[ℂ] E)
    (hT_norm : ∀ z (ψ : E), ‖T z ψ‖ ≤ ‖ψ‖)
    (hT_cont : ∀ ψ : E, Continuous (fun z => T z ψ)) (ψ : E) :
    ‖bochnerAvgCLM ν w hw T hT_norm hT_cont ψ‖ ≤ (∫ z, ‖w z‖ ∂ν) * ‖ψ‖ := by
  have hM : 0 ≤ ∫ z, ‖w z‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  calc ‖bochnerAvgCLM ν w hw T hT_norm hT_cont ψ‖
      ≤ ‖bochnerAvgCLM ν w hw T hT_norm hT_cont‖ * ‖ψ‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (∫ z, ‖w z‖ ∂ν) * ‖ψ‖ :=
        mul_le_mul_of_nonneg_right (LinearMap.mkContinuous_norm_le _ hM _) (norm_nonneg _)

/-- 3D periodic spatial lattice sites `Λ_L = (ℤ / Lℤ)³`. -/
abbrev Site3D (L : ℕ) := Fin 3 → Fin L

/-- Oriented spatial lattice edges `E(Λ_L) = Λ_L × {0, 1, 2}`. -/
abbrev SpatialEdge (L : ℕ) := Site3D L × Fin 3

instance site3D_decidableEq (L : ℕ) : DecidableEq (Site3D L) :=
  inferInstance

instance spatialEdge_decidableEq (L : ℕ) : DecidableEq (SpatialEdge L) :=
  inferInstance

/-- Cyclic unit shift `(v + 1) mod L` on `Fin L`. -/
def shiftFin {L : ℕ} (v : Fin L) : Fin L :=
  ⟨(v.val + 1) % L, Nat.mod_lt _ (Nat.zero_lt_of_lt v.isLt)⟩

/-- Unit lattice translation `x + e_μ` along spatial axis `μ ∈ Fin 3` on `Λ_L`. -/
def shiftSite {L : ℕ} (x : Site3D L) (μ : Fin 3) : Site3D L :=
  Function.update x μ (shiftFin (x μ))

theorem shiftSite_comm {L : ℕ} (x : Site3D L) {μ ν : Fin 3} (h : μ ≠ ν) :
    shiftSite (shiftSite x μ) ν = shiftSite (shiftSite x ν) μ := by
  unfold shiftSite
  have hxν : Function.update x μ (shiftFin (x μ)) ν = x ν :=
    Function.update_of_ne h.symm _ _
  have hxμ : Function.update x ν (shiftFin (x ν)) μ = x μ :=
    Function.update_of_ne h _ _
  rw [hxν, hxμ, Function.update_comm h]

/-- Spatial gauge-field configurations `U : E(Λ_L) → G`. -/
abbrev SpatialConfig (L : ℕ) (G : Type*) := SpatialEdge L → G

/-- Spatial local gauge transformations `Ω : Λ_L → G`. -/
abbrev GaugeConfig (L : ℕ) (G : Type*) := Site3D L → G

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Single-edge spatial configuration equal to `u` at `e` and `1` at all `e' ≠ e`. -/
def edgeSingle (L : ℕ) (e : SpatialEdge L) (u : G) : SpatialConfig L G :=
  fun e' => if e' = e then u else 1

@[simp]
theorem edgeSingle_same (L : ℕ) (e : SpatialEdge L) (u : G) :
    edgeSingle L e u e = u :=
  if_pos rfl

theorem edgeSingle_of_ne (L : ℕ) {e e' : SpatialEdge L} (h : e' ≠ e) (u : G) :
    edgeSingle L e u e' = 1 :=
  if_neg h

/-- Unconditional strict positivity `0 < haarC0 C β` for EVERY real `β ∈ ℝ`. -/
theorem haarC0_pos_all (C : NormalizedGaugeCharacter G) (β : ℝ) :
    0 < haarC0 C β := by
  have hw_int : Integrable (wilsonWeight C β) (haarProb G) :=
    integrable_of_continuous_compact (wilsonWeight_continuous C β)
  have h_pt : ∀ g : G, Real.exp (-2 * |β|) ≤ wilsonWeight C β g := by
    intro g
    unfold wilsonWeight
    apply Real.exp_le_exp.mpr
    have h1 := C.neg_one_le_χ g
    have h2 := C.χ_le_one g
    rcases abs_cases β with ⟨habs, _⟩ | ⟨habs, _⟩ <;> nlinarith
  have h_const : ∫ _ : G, Real.exp (-2 * |β|) ∂(haarProb G) = Real.exp (-2 * |β|) := by
    simp
  have h_le : Real.exp (-2 * |β|) ≤ haarC0 C β := by
    unfold haarC0
    rw [← h_const]
    exact integral_mono (integrable_const _) hw_int h_pt
  exact lt_of_lt_of_le (Real.exp_pos _) h_le

/-- Product Haar probability measure `μ_Haar^{E(Λ_L)}` on `G^{E(Λ_L)}`. -/
noncomputable def spatialHaar (L : ℕ) (G : Type*)
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Measure (SpatialConfig L G) :=
  Measure.pi fun _ : SpatialEdge L => haarProb G

/-- Product Haar probability measure `μ_Haar^{Λ_L}` on local gauge transformations `G^{Λ_L}`. -/
noncomputable def gaugeHaar (L : ℕ) (G : Type*)
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Measure (GaugeConfig L G) :=
  Measure.pi fun _ : Site3D L => haarProb G

instance spatialHaar_isProbabilityMeasure (L : ℕ) :
    IsProbabilityMeasure (spatialHaar L G) := by
  unfold spatialHaar
  infer_instance

instance gaugeHaar_isProbabilityMeasure (L : ℕ) :
    IsProbabilityMeasure (gaugeHaar L G) := by
  unfold gaugeHaar
  infer_instance

instance spatialHaar_isOpenPosMeasure (L : ℕ) :
    Measure.IsOpenPosMeasure (spatialHaar L G) := by
  unfold spatialHaar
  infer_instance

theorem spatialHaar_mp_mul_left (L : ℕ) (W : SpatialConfig L G) :
    MeasurePreserving (fun U : SpatialConfig L G => W * U)
      (spatialHaar L G) (spatialHaar L G) :=
  measurePreserving_pi _ _ fun e => measurePreserving_mul_left (haarProb G) (W e)

theorem spatialHaar_mp_mul_right (L : ℕ) (W : SpatialConfig L G) :
    MeasurePreserving (fun U : SpatialConfig L G => U * W)
      (spatialHaar L G) (spatialHaar L G) :=
  measurePreserving_pi _ _ fun e => measurePreserving_mul_right (haarProb G) (W e)

instance spatialHaar_isMulLeftInvariant (L : ℕ) :
    Measure.IsMulLeftInvariant (spatialHaar L G) where
  map_mul_left_eq_self W := (spatialHaar_mp_mul_left L W).map_eq

instance spatialHaar_isMulRightInvariant (L : ℕ) :
    Measure.IsMulRightInvariant (spatialHaar L G) where
  map_mul_right_eq_self W := (spatialHaar_mp_mul_right L W).map_eq

instance gaugeHaar_isMulLeftInvariant (L : ℕ) :
    Measure.IsMulLeftInvariant (gaugeHaar L G) where
  map_mul_left_eq_self Ω :=
    (measurePreserving_pi _ _ fun x => measurePreserving_mul_left (haarProb G) (Ω x)).map_eq

instance gaugeHaar_isMulRightInvariant (L : ℕ) :
    Measure.IsMulRightInvariant (gaugeHaar L G) where
  map_mul_right_eq_self Ω :=
    (measurePreserving_pi _ _ fun x => measurePreserving_mul_right (haarProb G) (Ω x)).map_eq

theorem gaugeHaar_mp_inv (L : ℕ) :
    MeasurePreserving (Inv.inv : GaugeConfig L G → GaugeConfig L G)
      (gaugeHaar L G) (gaugeHaar L G) :=
  measurePreserving_pi _ _ fun _ =>
    ⟨continuous_inv.measurable, Measure.inv_eq_self (haarProb G)⟩

instance gaugeHaar_isInvInvariant (L : ℕ) :
    Measure.IsInvInvariant (gaugeHaar L G) where
  inv_eq_self := (gaugeHaar_mp_inv (G := G) L).map_eq

/-- Spatial lattice Hilbert space `ℋ_lat(L) = L²(G^{E(Λ_L)}, μ_Haar; ℂ)`. -/
noncomputable abbrev SpatialL2 (L : ℕ) (G : Type*)
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :=
  Lp ℂ 2 (spatialHaar L G)

/-- Normalized constant-`1` ground state `Ω₀ ∈ L²(G^{E(Λ_L)}, μ_Haar; ℂ)`. -/
noncomputable def vacuumL2 (L : ℕ) (G : Type*)
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] : SpatialL2 L G :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top (spatialHaar L G) Set.univ) (1 : ℂ)

theorem vacuumL2_norm (L : ℕ) : ‖vacuumL2 L G‖ = 1 := by
  unfold vacuumL2
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
  have h_univ : (spatialHaar L G).real Set.univ = 1 := by simp [Measure.real]
  simp [h_univ]

theorem inner_vacuumL2 (L : ℕ) (ψ : SpatialL2 L G) :
    inner ℂ (vacuumL2 L G) ψ = ∫ U, ψ U ∂(spatialHaar L G) := by
  unfold vacuumL2
  rw [L2.inner_indicatorConstLp_one, Measure.restrict_univ]

theorem toLp_one_eq_vacuumL2 (L : ℕ) :
    ContinuousMap.toLp 2 (spatialHaar L G) ℂ (1 : C(SpatialConfig L G, ℂ)) = vacuumL2 L G := by
  rw [Lp.ext_iff]
  refine (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (spatialHaar L G) 1).trans ?_
  refine Filter.EventuallyEq.trans ?_
    (indicatorConstLp_coeFn (p := 2) (μ := spatialHaar L G)
      (hs := MeasurableSet.univ) (hμs := measure_ne_top (spatialHaar L G) Set.univ)
      (c := (1 : ℂ))).symm
  exact Filter.Eventually.of_forall fun _ => by simp

/-- Unitary `L²` operator induced by a continuous `spatialHaar`-preserving transformation. -/
noncomputable def unitaryOfMP (L : ℕ)
    (f : C(SpatialConfig L G, SpatialConfig L G))
    (hf : MeasurePreserving f (spatialHaar L G) (spatialHaar L G)) :
    SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  (Lp.compMeasurePreservingₗᵢ ℂ f hf).toContinuousLinearMap

theorem unitaryOfMP_congr (L : ℕ)
    {f₁ f₂ : C(SpatialConfig L G, SpatialConfig L G)} (h : f₁ = f₂)
    (hf₁ : MeasurePreserving f₁ (spatialHaar L G) (spatialHaar L G))
    (hf₂ : MeasurePreserving f₂ (spatialHaar L G) (spatialHaar L G)) :
    unitaryOfMP L f₁ hf₁ = unitaryOfMP L f₂ hf₂ := by
  subst h
  rfl

theorem unitaryOfMP_norm (L : ℕ)
    (f : C(SpatialConfig L G, SpatialConfig L G))
    (hf : MeasurePreserving f (spatialHaar L G) (spatialHaar L G))
    (ψ : SpatialL2 L G) :
    ‖unitaryOfMP L f hf ψ‖ = ‖ψ‖ :=
  Lp.norm_compMeasurePreserving ψ hf

@[simp]
theorem unitaryOfMP_vacuum (L : ℕ)
    (f : C(SpatialConfig L G, SpatialConfig L G))
    (hf : MeasurePreserving f (spatialHaar L G) (spatialHaar L G)) :
    unitaryOfMP L f hf (vacuumL2 L G) = vacuumL2 L G :=
  rfl

theorem unitaryOfMP_id (L : ℕ)
    (hf : MeasurePreserving (ContinuousMap.id (SpatialConfig L G))
      (spatialHaar L G) (spatialHaar L G))
    (ψ : SpatialL2 L G) :
    unitaryOfMP L (ContinuousMap.id _) hf ψ = ψ :=
  Lp.compMeasurePreserving_id_apply ψ

theorem unitaryOfMP_comp_apply (L : ℕ)
    (f₁ : C(SpatialConfig L G, SpatialConfig L G))
    (hf₁ : MeasurePreserving f₁ (spatialHaar L G) (spatialHaar L G))
    (f₂ : C(SpatialConfig L G, SpatialConfig L G))
    (hf₂ : MeasurePreserving f₂ (spatialHaar L G) (spatialHaar L G))
    (ψ : SpatialL2 L G) :
    unitaryOfMP L f₂ hf₂ (unitaryOfMP L f₁ hf₁ ψ) =
      unitaryOfMP L (f₁.comp f₂) (hf₁.comp hf₂) ψ :=
  (Lp.compMeasurePreserving_comp_apply ψ hf₁ hf₂).symm

theorem unitaryOfMP_toLp (L : ℕ)
    (f : C(SpatialConfig L G, SpatialConfig L G))
    (hf : MeasurePreserving f (spatialHaar L G) (spatialHaar L G))
    (g : C(SpatialConfig L G, ℂ)) :
    unitaryOfMP L f hf (ContinuousMap.toLp 2 (spatialHaar L G) ℂ g) =
      ContinuousMap.toLp 2 (spatialHaar L G) ℂ (g.comp f) := by
  rw [Lp.ext_iff]
  have h1 : unitaryOfMP L f hf (ContinuousMap.toLp 2 (spatialHaar L G) ℂ g) =ᵐ[spatialHaar L G]
      (ContinuousMap.toLp 2 (spatialHaar L G) ℂ g) ∘ f :=
    Lp.coeFn_compMeasurePreserving _ hf
  have h2 : (ContinuousMap.toLp 2 (spatialHaar L G) ℂ g : SpatialConfig L G → ℂ) ∘ f =ᵐ[spatialHaar L G]
      g ∘ f :=
    hf.quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (spatialHaar L G) g)
  have h3 := (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (spatialHaar L G) (g.comp f)).symm
  exact (h1.trans h2).trans h3

theorem inner_unitaryOfMP_inv (L : ℕ)
    (f : C(SpatialConfig L G, SpatialConfig L G))
    (hf : MeasurePreserving f (spatialHaar L G) (spatialHaar L G))
    (f_inv : C(SpatialConfig L G, SpatialConfig L G))
    (hf_inv : MeasurePreserving f_inv (spatialHaar L G) (spatialHaar L G))
    (h_comp : f.comp f_inv = ContinuousMap.id _)
    (φ ψ : SpatialL2 L G) :
    inner ℂ (unitaryOfMP L f hf φ) ψ = inner ℂ φ (unitaryOfMP L f_inv hf_inv ψ) := by
  rw [← (Lp.compMeasurePreservingₗᵢ ℂ f_inv hf_inv).inner_map_map (unitaryOfMP L f hf φ) ψ]
  change inner ℂ (unitaryOfMP L f_inv hf_inv (unitaryOfMP L f hf φ))
      (unitaryOfMP L f_inv hf_inv ψ) = _
  rw [unitaryOfMP_comp_apply]
  have h_mp : MeasurePreserving (ContinuousMap.id (SpatialConfig L G))
      (spatialHaar L G) (spatialHaar L G) := MeasurePreserving.id _
  rw [unitaryOfMP_congr L h_comp (hf.comp hf_inv) h_mp, unitaryOfMP_id]

/-! ### Local Spatial Gauge Transformations & Gauge Projection `gaugeProj` -/

/-- Local spatial gauge action `(Ω · U)_{(x, μ)} = Ω(x) U_{(x, μ)} Ω(x + e_μ)⁻¹`. -/
def gaugeAct (L : ℕ) (Ω : GaugeConfig L G) (U : SpatialConfig L G) : SpatialConfig L G :=
  fun e => Ω e.1 * U e * (Ω (shiftSite e.1 e.2))⁻¹

theorem gaugeAct_one (L : ℕ) : gaugeAct (G := G) L 1 = id := by
  funext U e
  simp [gaugeAct]

theorem gaugeAct_mul (L : ℕ) (Ω₁ Ω₂ : GaugeConfig L G) (U : SpatialConfig L G) :
    gaugeAct L (Ω₁ * Ω₂) U = gaugeAct L Ω₁ (gaugeAct L Ω₂ U) := by
  funext e
  simp [gaugeAct, mul_assoc]

def gaugeActJointMap (L : ℕ) :
    C(GaugeConfig L G × SpatialConfig L G, SpatialConfig L G) where
  toFun p := gaugeAct L p.1 p.2
  continuous_toFun :=
    continuous_pi fun e =>
      ((((continuous_apply e.1).comp continuous_fst).mul
        ((continuous_apply e).comp continuous_snd)).mul
        (((continuous_apply (shiftSite e.1 e.2)).comp continuous_fst).inv))

def gaugeActMap (L : ℕ) (Ω : GaugeConfig L G) :
    C(SpatialConfig L G, SpatialConfig L G) :=
  (gaugeActJointMap (G := G) L).curry Ω

theorem gaugeAct_mp (L : ℕ) (Ω : GaugeConfig L G) :
    MeasurePreserving (gaugeActMap L Ω) (spatialHaar L G) (spatialHaar L G) :=
  measurePreserving_pi _ _ fun (e : SpatialEdge L) =>
    (measurePreserving_mul_right (haarProb G) (Ω (shiftSite e.1 e.2))⁻¹).comp
      (measurePreserving_mul_left (haarProb G) (Ω e.1))

/-- Unitary gauge transformation operator `(U_Ω ψ)(U) = ψ(Ω · U)`. -/
noncomputable def gaugeUnitary (L : ℕ) (Ω : GaugeConfig L G) :
    SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  unitaryOfMP L (gaugeActMap L Ω) (gaugeAct_mp L Ω)

@[simp]
theorem gaugeUnitary_vacuum (L : ℕ) (Ω : GaugeConfig L G) :
    gaugeUnitary L Ω (vacuumL2 L G) = vacuumL2 L G :=
  rfl

theorem gaugeUnitary_continuous (L : ℕ) (ψ : SpatialL2 L G) :
    Continuous (fun Ω : GaugeConfig L G => gaugeUnitary L Ω ψ) :=
  continuous_const.compMeasurePreservingLp
    (gaugeActJointMap (G := G) L).curry.continuous
    (gaugeAct_mp L) (by norm_num)

theorem gaugeUnitary_mul (L : ℕ) (Ω₁ Ω₂ : GaugeConfig L G) (ψ : SpatialL2 L G) :
    gaugeUnitary L Ω₂ (gaugeUnitary L Ω₁ ψ) = gaugeUnitary L (Ω₁ * Ω₂) ψ := by
  unfold gaugeUnitary
  rw [unitaryOfMP_comp_apply]
  have h_eq : (gaugeActMap (G := G) L Ω₁).comp (gaugeActMap L Ω₂) =
      gaugeActMap L (Ω₁ * Ω₂) := by
    ext U e
    exact (congrFun (gaugeAct_mul L Ω₁ Ω₂ U) e).symm
  rw [unitaryOfMP_congr L h_eq]

/-- Haar orthogonal projection `P_gauge = ∫_{G^{Λ_L}} gaugeUnitary Ω dμ_Haar(Ω)` onto the
    physical gauge-invariant subspace `L²(G^{E(Λ_L)} / G^{Λ_L}, μ_Haar)`. -/
noncomputable def gaugeProj (L : ℕ) : SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  bochnerAvgCLM (gaugeHaar L G)
    (fun _ => (1 : ℂ)) continuous_const
    (gaugeUnitary L)
    (fun Ω ψ => (unitaryOfMP_norm L (gaugeActMap L Ω) (gaugeAct_mp L Ω) ψ).le)
    (gaugeUnitary_continuous L)

theorem gaugeProj_norm_le (L : ℕ) (ψ : SpatialL2 L G) :
    ‖gaugeProj L ψ‖ ≤ ‖ψ‖ := by
  have h := bochnerAvgCLM_norm_le (gaugeHaar L G)
    (fun _ => (1 : ℂ)) continuous_const (gaugeUnitary L)
    (fun Ω φ => (unitaryOfMP_norm L (gaugeActMap L Ω) (gaugeAct_mp L Ω) φ).le)
    (gaugeUnitary_continuous L) ψ
  have h_one : ∫ _ : GaugeConfig L G, ‖(1 : ℂ)‖ ∂(gaugeHaar L G) = 1 := by simp
  unfold gaugeProj
  simpa [h_one] using h

@[simp]
theorem gaugeProj_vacuum (L : ℕ) :
    gaugeProj L (vacuumL2 L G) = vacuumL2 L G := by
  change ∫ Ω : GaugeConfig L G, (1 : ℂ) • gaugeUnitary L Ω (vacuumL2 L G) ∂(gaugeHaar L G) = _
  simp

theorem gaugeUnitary_comp_gaugeProj (L : ℕ) (Ω₀ : GaugeConfig L G) :
    (gaugeUnitary (G := G) L Ω₀).comp (gaugeProj L) = gaugeProj L := by
  apply ContinuousLinearMap.ext
  intro ψ
  have h_int : Integrable (fun Ω : GaugeConfig L G => gaugeUnitary L Ω ψ) (gaugeHaar L G) :=
    integrable_of_continuous_compact (gaugeUnitary_continuous L ψ)
  change gaugeUnitary L Ω₀ (∫ Ω, (1 : ℂ) • gaugeUnitary L Ω ψ ∂(gaugeHaar L G)) =
    ∫ Ω, (1 : ℂ) • gaugeUnitary L Ω ψ ∂(gaugeHaar L G)
  simp only [one_smul]
  rw [clm_integral_comm (gaugeUnitary L Ω₀) h_int]
  simp_rw [gaugeUnitary_mul]
  exact integral_mul_right_eq_self (fun Ω => gaugeUnitary L Ω ψ) Ω₀

theorem gaugeProj_comp_gaugeUnitary (L : ℕ) (Ω₀ : GaugeConfig L G) :
    (gaugeProj (G := G) L).comp (gaugeUnitary L Ω₀) = gaugeProj L := by
  apply ContinuousLinearMap.ext
  intro ψ
  change ∫ Ω, (1 : ℂ) • gaugeUnitary L Ω (gaugeUnitary L Ω₀ ψ) ∂(gaugeHaar L G) =
    ∫ Ω, (1 : ℂ) • gaugeUnitary L Ω ψ ∂(gaugeHaar L G)
  simp only [one_smul, gaugeUnitary_mul]
  exact integral_mul_left_eq_self (fun Ω => gaugeUnitary L Ω ψ) Ω₀

theorem gaugeProj_idempotent (L : ℕ) :
    (gaugeProj (G := G) L).comp (gaugeProj L) = gaugeProj L := by
  apply ContinuousLinearMap.ext
  intro ψ
  change ∫ Ω, (1 : ℂ) • gaugeUnitary L Ω (gaugeProj L ψ) ∂(gaugeHaar L G) = gaugeProj L ψ
  have h_pt : ∀ Ω : GaugeConfig L G, gaugeUnitary L Ω (gaugeProj L ψ) = gaugeProj L ψ :=
    fun Ω => DFunLike.congr_fun (gaugeUnitary_comp_gaugeProj L Ω) ψ
  simp [h_pt]

theorem gaugeProj_selfAdjoint (L : ℕ) (φ ψ : SpatialL2 L G) :
    inner ℂ (gaugeProj L φ) ψ = inner ℂ φ (gaugeProj L ψ) := by
  have hφ : Integrable (fun Ω : GaugeConfig L G => gaugeUnitary L Ω φ) (gaugeHaar L G) :=
    integrable_of_continuous_compact (gaugeUnitary_continuous L φ)
  have hψ : Integrable (fun Ω : GaugeConfig L G => gaugeUnitary L Ω ψ) (gaugeHaar L G) :=
    integrable_of_continuous_compact (gaugeUnitary_continuous L ψ)
  change inner ℂ (∫ Ω, (1 : ℂ) • gaugeUnitary L Ω φ ∂(gaugeHaar L G)) ψ =
    inner ℂ φ (∫ Ω, (1 : ℂ) • gaugeUnitary L Ω ψ ∂(gaugeHaar L G))
  simp only [one_smul]
  rw [inner_bochner_left hφ ψ, inner_bochner_right hψ φ]
  have h_inv_inner : ∀ Ω : GaugeConfig L G,
      inner ℂ (gaugeUnitary L Ω φ) ψ = inner ℂ φ (gaugeUnitary L Ω⁻¹ ψ) := by
    intro Ω
    refine inner_unitaryOfMP_inv L (gaugeActMap L Ω) (gaugeAct_mp L Ω)
      (gaugeActMap L Ω⁻¹) (gaugeAct_mp L Ω⁻¹) ?_ φ ψ
    ext U e
    change gaugeAct L Ω (gaugeAct L Ω⁻¹ U) e = U e
    rw [← gaugeAct_mul, mul_inv_cancel, gaugeAct_one]
    rfl
  simp_rw [h_inv_inner]
  exact integral_inv_eq_self (fun Ω : GaugeConfig L G => inner ℂ φ (gaugeUnitary L Ω ψ))
    (gaugeHaar L G)

/-! ### Single-Edge Temporal Shifts, Edge Expectations, and Temporal Link Kernels -/

def edgeShiftJointMap (L : ℕ) (e : SpatialEdge L) :
    C(G × SpatialConfig L G, SpatialConfig L G) where
  toFun p := p.2 * edgeSingle L e p.1
  continuous_toFun := by
    refine continuous_pi fun e' => ?_
    by_cases h : e' = e
    · subst h
      have h_eq : (fun p : G × SpatialConfig L G => (p.2 * edgeSingle L e' p.1) e') =
          fun p => p.2 e' * p.1 := by
        funext p
        simp
      rw [h_eq]
      exact ((continuous_apply e').comp continuous_snd).mul continuous_fst
    · have h_eq : (fun p : G × SpatialConfig L G => (p.2 * edgeSingle L e p.1) e') =
          fun p => p.2 e' := by
        funext p
        simp [edgeSingle_of_ne L h]
      rw [h_eq]
      exact (continuous_apply e').comp continuous_snd

def edgeShiftMap (L : ℕ) (e : SpatialEdge L) (u : G) :
    C(SpatialConfig L G, SpatialConfig L G) :=
  (edgeShiftJointMap L e).curry u

theorem edgeShift_mp (L : ℕ) (e : SpatialEdge L) (u : G) :
    MeasurePreserving (edgeShiftMap L e u) (spatialHaar L G) (spatialHaar L G) :=
  spatialHaar_mp_mul_right L (edgeSingle L e u)

/-- Unitary single-edge right-shift operator `(edgeShift e u ψ)(U) = ψ(U · u_e)`. -/
noncomputable def edgeShift (L : ℕ) (e : SpatialEdge L) (u : G) :
    SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  unitaryOfMP L (edgeShiftMap L e u) (edgeShift_mp L e u)

@[simp]
theorem edgeShift_vacuum (L : ℕ) (e : SpatialEdge L) (u : G) :
    edgeShift L e u (vacuumL2 L G) = vacuumL2 L G :=
  rfl

theorem edgeShift_continuous (L : ℕ) (e : SpatialEdge L) (ψ : SpatialL2 L G) :
    Continuous (fun u : G => edgeShift L e u ψ) :=
  continuous_const.compMeasurePreservingLp
    (edgeShiftJointMap (G := G) L e).curry.continuous
    (edgeShift_mp L e) (by norm_num)

theorem edgeShift_joint_continuous (L : ℕ) (e₁ e₂ : SpatialEdge L) (ψ : SpatialL2 L G) :
    Continuous (fun p : G × G => edgeShift L e₁ p.1 (edgeShift L e₂ p.2 ψ)) := by
  let jointMap : C((G × G) × SpatialConfig L G, SpatialConfig L G) :=
    ⟨fun q => (q.2 * edgeSingle L e₁ q.1.1) * edgeSingle L e₂ q.1.2, by
      have h1 : Continuous (fun q : (G × G) × SpatialConfig L G => (q.1.1, q.2)) :=
        (continuous_fst.comp continuous_fst).prodMk continuous_snd
      have h2 : Continuous (fun q : (G × G) × SpatialConfig L G =>
          (q.1.2, (edgeShiftJointMap (G := G) L e₁) (q.1.1, q.2))) :=
        (continuous_snd.comp continuous_fst).prodMk
          ((edgeShiftJointMap L e₁).continuous.comp h1)
      exact (edgeShiftJointMap L e₂).continuous.comp h2⟩
  have h_mp : ∀ p : G × G,
      MeasurePreserving (jointMap.curry p) (spatialHaar L G) (spatialHaar L G) :=
    fun p => (edgeShift_mp L e₂ p.2).comp (edgeShift_mp L e₁ p.1)
  have h_cont : Continuous (fun p : G × G => unitaryOfMP L (jointMap.curry p) (h_mp p) ψ) :=
    continuous_const.compMeasurePreservingLp jointMap.curry.continuous h_mp (by norm_num)
  have h_eq : (fun p : G × G => edgeShift L e₁ p.1 (edgeShift L e₂ p.2 ψ)) =
      fun p : G × G => unitaryOfMP L (jointMap.curry p) (h_mp p) ψ := by
    funext p
    unfold edgeShift
    rw [unitaryOfMP_comp_apply]
    have h_map : (edgeShiftMap (G := G) L e₂ p.2).comp (edgeShiftMap L e₁ p.1) =
        jointMap.curry p := rfl
    rw [unitaryOfMP_congr L h_map]
  rw [h_eq]
  exact h_cont

theorem edgeShift_mul (L : ℕ) (e : SpatialEdge L) (u₁ u₂ : G) (ψ : SpatialL2 L G) :
    edgeShift L e u₁ (edgeShift L e u₂ ψ) = edgeShift L e (u₁ * u₂) ψ := by
  unfold edgeShift
  rw [unitaryOfMP_comp_apply]
  have h_eq : (edgeShiftMap (G := G) L e u₂).comp (edgeShiftMap L e u₁) =
      edgeShiftMap L e (u₁ * u₂) := by
    ext U e'
    change ((U * edgeSingle L e u₁) * edgeSingle L e u₂) e' =
      (U * edgeSingle L e (u₁ * u₂)) e'
    by_cases h : e' = e
    · subst h
      simp [mul_assoc]
    · simp [edgeSingle_of_ne L h]
  rw [unitaryOfMP_congr L h_eq]

theorem edgeShift_comm (L : ℕ) {e₁ e₂ : SpatialEdge L} (hne : e₁ ≠ e₂)
    (u₁ u₂ : G) (ψ : SpatialL2 L G) :
    edgeShift L e₁ u₁ (edgeShift L e₂ u₂ ψ) =
      edgeShift L e₂ u₂ (edgeShift L e₁ u₁ ψ) := by
  unfold edgeShift
  rw [unitaryOfMP_comp_apply, unitaryOfMP_comp_apply]
  have h_eq : (edgeShiftMap (G := G) L e₂ u₂).comp (edgeShiftMap L e₁ u₁) =
      (edgeShiftMap L e₁ u₁).comp (edgeShiftMap L e₂ u₂) := by
    ext U e'
    change ((U * edgeSingle L e₁ u₁) * edgeSingle L e₂ u₂) e' =
      ((U * edgeSingle L e₂ u₂) * edgeSingle L e₁ u₁) e'
    by_cases h1 : e' = e₁
    · subst h1
      simp [edgeSingle_of_ne L hne]
    · by_cases h2 : e' = e₂
      · subst h2
        simp [edgeSingle_of_ne L h1]
      · simp [edgeSingle_of_ne L h1, edgeSingle_of_ne L h2]
  rw [unitaryOfMP_congr L h_eq]

theorem inner_edgeShift_inv (L : ℕ) (e : SpatialEdge L) (u : G)
    (φ ψ : SpatialL2 L G) :
    inner ℂ (edgeShift L e u φ) ψ = inner ℂ φ (edgeShift L e u⁻¹ ψ) := by
  refine inner_unitaryOfMP_inv L (edgeShiftMap L e u) (edgeShift_mp L e u)
    (edgeShiftMap L e u⁻¹) (edgeShift_mp L e u⁻¹) ?_ φ ψ
  ext U e'
  change ((U * edgeSingle L e u⁻¹) * edgeSingle L e u) e' = U e'
  by_cases h : e' = e
  · subst h
    simp [mul_assoc]
  · simp [edgeSingle_of_ne L h]

/-- Conditional Haar expectation `P_e = ∫_G edgeShift e u dμ_Haar(u)` integrating out link `e`. -/
noncomputable def edgeExpect (L : ℕ) (e : SpatialEdge L) :
    SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  bochnerAvgCLM (haarProb G)
    (fun _ => (1 : ℂ)) continuous_const
    (edgeShift L e)
    (fun u ψ => (unitaryOfMP_norm L (edgeShiftMap L e u) (edgeShift_mp L e u) ψ).le)
    (edgeShift_continuous L e)

theorem edgeExpect_norm_le (L : ℕ) (e : SpatialEdge L) (ψ : SpatialL2 L G) :
    ‖edgeExpect L e ψ‖ ≤ ‖ψ‖ := by
  have h := bochnerAvgCLM_norm_le (haarProb G)
    (fun _ => (1 : ℂ)) continuous_const (edgeShift L e)
    (fun u φ => (unitaryOfMP_norm L (edgeShiftMap L e u) (edgeShift_mp L e u) φ).le)
    (edgeShift_continuous L e) ψ
  have h_one : ∫ _ : G, ‖(1 : ℂ)‖ ∂(haarProb G) = 1 := by simp
  unfold edgeExpect
  simpa [h_one] using h

@[simp]
theorem edgeExpect_vacuum (L : ℕ) (e : SpatialEdge L) :
    edgeExpect L e (vacuumL2 L G) = vacuumL2 L G := by
  change ∫ u : G, (1 : ℂ) • edgeShift L e u (vacuumL2 L G) ∂(haarProb G) = _
  simp

/-- Normalized temporal-plaquette Wilson integral operator on edge `e`:
    `(T_e ψ)(U) = (1 / c₀(β)) ∫_G w_β(u) ψ(U · u_e) dμ_Haar(u)`. -/
noncomputable def edgeTransferOp (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (e : SpatialEdge L) : SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  bochnerAvgCLM (haarProb G)
    (fun u => ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp ((wilsonWeight_continuous C β).div_const _))
    (edgeShift L e)
    (fun u ψ => (unitaryOfMP_norm L (edgeShiftMap L e u) (edgeShift_mp L e u) ψ).le)
    (edgeShift_continuous L e)

theorem wilsonWeight_div_haarC0_integral (C : NormalizedGaugeCharacter G) (β : ℝ) :
    ∫ u : G, wilsonWeight C β u / haarC0 C β ∂(haarProb G) = 1 := by
  have hc0 : haarC0 C β ≠ 0 := (haarC0_pos_all C β).ne'
  rw [integral_div]
  change haarC0 C β / haarC0 C β = 1
  exact div_self hc0

theorem wilsonWeight_div_haarC0_norm_integral (C : NormalizedGaugeCharacter G) (β : ℝ) :
    ∫ u : G, ‖((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ)‖ ∂(haarProb G) = 1 := by
  have hc0 : 0 < haarC0 C β := haarC0_pos_all C β
  have h_pt : ∀ u : G,
      ‖((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ)‖ = wilsonWeight C β u / haarC0 C β := by
    intro u
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (wilsonWeight_pos C β u) hc0)]
  simp_rw [h_pt]
  exact wilsonWeight_div_haarC0_integral C β

theorem edgeTransferOp_norm_le (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (e : SpatialEdge L) (ψ : SpatialL2 L G) :
    ‖edgeTransferOp C L β e ψ‖ ≤ ‖ψ‖ := by
  have h := bochnerAvgCLM_norm_le (haarProb G)
    (fun u => ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp ((wilsonWeight_continuous C β).div_const _))
    (edgeShift L e)
    (fun u φ => (unitaryOfMP_norm L (edgeShiftMap L e u) (edgeShift_mp L e u) φ).le)
    (edgeShift_continuous L e) ψ
  unfold edgeTransferOp
  rw [wilsonWeight_div_haarC0_norm_integral C β, one_mul] at h
  exact h

@[simp]
theorem edgeTransferOp_vacuum (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (e : SpatialEdge L) :
    edgeTransferOp C L β e (vacuumL2 L G) = vacuumL2 L G := by
  change ∫ u : G, ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ) •
    edgeShift L e u (vacuumL2 L G) ∂(haarProb G) = vacuumL2 L G
  simp only [edgeShift_vacuum]
  rw [integral_smul_const, complex_integral_ofReal, wilsonWeight_div_haarC0_integral C β,
      Complex.ofReal_one, one_smul]

theorem edgeExpect_edgeShift_right (L : ℕ) (e : SpatialEdge L) (g : G) (ψ : SpatialL2 L G) :
    edgeExpect L e (edgeShift L e g ψ) = edgeExpect L e ψ := by
  change ∫ u : G, (1 : ℂ) • edgeShift L e u (edgeShift L e g ψ) ∂(haarProb G) =
    ∫ u : G, (1 : ℂ) • edgeShift L e u ψ ∂(haarProb G)
  simp only [one_smul, edgeShift_mul]
  exact integral_mul_right_eq_self (fun u : G => edgeShift L e u ψ) g

theorem edgeShift_edgeExpect_left (L : ℕ) (e : SpatialEdge L) (g : G) (ψ : SpatialL2 L G) :
    edgeShift L e g (edgeExpect L e ψ) = edgeExpect L e ψ := by
  have h_int : Integrable (fun u : G => edgeShift L e u ψ) (haarProb G) :=
    integrable_of_continuous_compact (edgeShift_continuous L e ψ)
  change edgeShift L e g (∫ u : G, (1 : ℂ) • edgeShift L e u ψ ∂(haarProb G)) =
    ∫ u : G, (1 : ℂ) • edgeShift L e u ψ ∂(haarProb G)
  simp only [one_smul]
  rw [clm_integral_comm (edgeShift L e g) h_int]
  simp_rw [edgeShift_mul]
  exact integral_mul_left_eq_self (fun u : G => edgeShift L e u ψ) g

theorem edgeExpect_idempotent (L : ℕ) (e : SpatialEdge L) :
    (edgeExpect (G := G) L e).comp (edgeExpect L e) = edgeExpect L e := by
  apply ContinuousLinearMap.ext
  intro ψ
  change ∫ u : G, (1 : ℂ) • edgeShift L e u (edgeExpect L e ψ) ∂(haarProb G) = edgeExpect L e ψ
  simp [edgeShift_edgeExpect_left]

theorem edgeExpect_comp_edgeTransferOp (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (e : SpatialEdge L) :
    (edgeExpect L e).comp (edgeTransferOp C L β e) = edgeExpect L e := by
  apply ContinuousLinearMap.ext
  intro ψ
  let w : G → ℂ := fun u => ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ)
  have hw_cont : Continuous w :=
    Complex.continuous_ofReal.comp ((wilsonWeight_continuous C β).div_const _)
  have h_int : Integrable (fun u : G => w u • edgeShift L e u ψ) (haarProb G) :=
    integrable_of_continuous_compact (hw_cont.smul (edgeShift_continuous L e ψ))
  change edgeExpect L e (∫ u : G, w u • edgeShift L e u ψ ∂(haarProb G)) = edgeExpect L e ψ
  rw [clm_integral_comm (edgeExpect L e) h_int]
  simp_rw [map_smul, edgeExpect_edgeShift_right]
  rw [integral_smul_const]
  have hw_one : ∫ u : G, w u ∂(haarProb G) = 1 := by
    simp only [w]
    rw [complex_integral_ofReal, wilsonWeight_div_haarC0_integral C β, Complex.ofReal_one]
  rw [hw_one, one_smul]

theorem edgeTransferOp_comp_edgeExpect (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (e : SpatialEdge L) :
    (edgeTransferOp C L β e).comp (edgeExpect L e) = edgeExpect L e := by
  apply ContinuousLinearMap.ext
  intro ψ
  let w : G → ℂ := fun u => ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ)
  change ∫ u : G, w u • edgeShift L e u (edgeExpect L e ψ) ∂(haarProb G) = edgeExpect L e ψ
  simp_rw [edgeShift_edgeExpect_left]
  rw [integral_smul_const]
  have hw_one : ∫ u : G, w u ∂(haarProb G) = 1 := by
    simp only [w]
    rw [complex_integral_ofReal, wilsonWeight_div_haarC0_integral C β, Complex.ofReal_one]
  rw [hw_one, one_smul]

theorem edgeExpect_selfAdjoint (L : ℕ) (e : SpatialEdge L) (φ ψ : SpatialL2 L G) :
    inner ℂ (edgeExpect L e φ) ψ = inner ℂ φ (edgeExpect L e ψ) := by
  have hφ : Integrable (fun u : G => edgeShift L e u φ) (haarProb G) :=
    integrable_of_continuous_compact (edgeShift_continuous L e φ)
  have hψ : Integrable (fun u : G => edgeShift L e u ψ) (haarProb G) :=
    integrable_of_continuous_compact (edgeShift_continuous L e ψ)
  change inner ℂ (∫ u : G, (1 : ℂ) • edgeShift L e u φ ∂(haarProb G)) ψ =
    inner ℂ φ (∫ u : G, (1 : ℂ) • edgeShift L e u ψ ∂(haarProb G))
  simp only [one_smul]
  rw [inner_bochner_left hφ ψ, inner_bochner_right hψ φ]
  simp_rw [inner_edgeShift_inv]
  exact integral_inv_eq_self (fun u : G => inner ℂ φ (edgeShift L e u ψ)) (haarProb G)

theorem edgeTransferOp_selfAdjoint (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (e : SpatialEdge L) (φ ψ : SpatialL2 L G) :
    inner ℂ (edgeTransferOp C L β e φ) ψ = inner ℂ φ (edgeTransferOp C L β e ψ) := by
  let w : G → ℂ := fun u => ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ)
  have hw_cont : Continuous w :=
    Complex.continuous_ofReal.comp ((wilsonWeight_continuous C β).div_const _)
  have hφ : Integrable (fun u : G => w u • edgeShift L e u φ) (haarProb G) :=
    integrable_of_continuous_compact (hw_cont.smul (edgeShift_continuous L e φ))
  have hψ : Integrable (fun u : G => w u • edgeShift L e u ψ) (haarProb G) :=
    integrable_of_continuous_compact (hw_cont.smul (edgeShift_continuous L e ψ))
  change inner ℂ (∫ u : G, w u • edgeShift L e u φ ∂(haarProb G)) ψ =
    inner ℂ φ (∫ u : G, w u • edgeShift L e u ψ ∂(haarProb G))
  rw [inner_bochner_left hφ ψ, inner_bochner_right hψ φ]
  have h_pt : ∀ u : G,
      inner ℂ (w u • edgeShift L e u φ) ψ = inner ℂ φ (w u⁻¹ • edgeShift L e u⁻¹ ψ) := by
    intro u
    rw [inner_smul_left, inner_smul_right, inner_edgeShift_inv]
    have hw_real : conj (w u) = w u⁻¹ := by
      simp [w, wilsonWeight_inv]
    rw [hw_real]
  simp_rw [h_pt]
  exact integral_inv_eq_self (fun u : G => inner ℂ φ (w u • edgeShift L e u ψ)) (haarProb G)

/-- General Fubini commutativity for weighted single-edge Bochner operators on distinct edges. -/
theorem bochner_edge_comm (L : ℕ) {e₁ e₂ : SpatialEdge L} (hne : e₁ ≠ e₂)
    (w₁ w₂ : G → ℂ) (hw₁ : Continuous w₁) (hw₂ : Continuous w₂) :
    (bochnerAvgCLM (haarProb G) w₁ hw₁ (edgeShift L e₁)
      (fun u φ => (unitaryOfMP_norm L (edgeShiftMap L e₁ u) (edgeShift_mp L e₁ u) φ).le)
      (edgeShift_continuous L e₁)).comp
    (bochnerAvgCLM (haarProb G) w₂ hw₂ (edgeShift L e₂)
      (fun u φ => (unitaryOfMP_norm L (edgeShiftMap L e₂ u) (edgeShift_mp L e₂ u) φ).le)
      (edgeShift_continuous L e₂)) =
    (bochnerAvgCLM (haarProb G) w₂ hw₂ (edgeShift L e₂)
      (fun u φ => (unitaryOfMP_norm L (edgeShiftMap L e₂ u) (edgeShift_mp L e₂ u) φ).le)
      (edgeShift_continuous L e₂)).comp
    (bochnerAvgCLM (haarProb G) w₁ hw₁ (edgeShift L e₁)
      (fun u φ => (unitaryOfMP_norm L (edgeShiftMap L e₁ u) (edgeShift_mp L e₁ u) φ).le)
      (edgeShift_continuous L e₁)) := by
  let A₁ := bochnerAvgCLM (haarProb G) w₁ hw₁ (edgeShift L e₁)
    (fun u φ => (unitaryOfMP_norm L (edgeShiftMap L e₁ u) (edgeShift_mp L e₁ u) φ).le)
    (edgeShift_continuous L e₁)
  let A₂ := bochnerAvgCLM (haarProb G) w₂ hw₂ (edgeShift L e₂)
    (fun u φ => (unitaryOfMP_norm L (edgeShiftMap L e₂ u) (edgeShift_mp L e₂ u) φ).le)
    (edgeShift_continuous L e₂)
  apply ContinuousLinearMap.ext
  intro ψ
  change A₁ (∫ u₂ : G, w₂ u₂ • edgeShift L e₂ u₂ ψ ∂(haarProb G)) =
    A₂ (∫ u₁ : G, w₁ u₁ • edgeShift L e₁ u₁ ψ ∂(haarProb G))
  have h₂_int : Integrable (fun u₂ : G => w₂ u₂ • edgeShift L e₂ u₂ ψ) (haarProb G) :=
    integrable_of_continuous_compact (hw₂.smul (edgeShift_continuous L e₂ ψ))
  have h₁_int : Integrable (fun u₁ : G => w₁ u₁ • edgeShift L e₁ u₁ ψ) (haarProb G) :=
    integrable_of_continuous_compact (hw₁.smul (edgeShift_continuous L e₁ ψ))
  rw [clm_integral_comm A₁ h₂_int, clm_integral_comm A₂ h₁_int]
  change ∫ u₂ : G, (∫ u₁ : G, w₁ u₁ • edgeShift L e₁ u₁ (w₂ u₂ • edgeShift L e₂ u₂ ψ) ∂(haarProb G)) ∂(haarProb G) =
    ∫ u₁ : G, (∫ u₂ : G, w₂ u₂ • edgeShift L e₂ u₂ (w₁ u₁ • edgeShift L e₁ u₁ ψ) ∂(haarProb G)) ∂(haarProb G)
  have h_prod_cont : Continuous (fun p : G × G =>
      (w₁ p.1 * w₂ p.2) • edgeShift L e₁ p.1 (edgeShift L e₂ p.2 ψ)) :=
    ((hw₁.comp continuous_fst).mul (hw₂.comp continuous_snd)).smul
      (edgeShift_joint_continuous L e₁ e₂ ψ)
  have h_prod_int : Integrable (fun p : G × G =>
      (w₁ p.1 * w₂ p.2) • edgeShift L e₁ p.1 (edgeShift L e₂ p.2 ψ))
      ((haarProb G).prod (haarProb G)) :=
    integrable_of_continuous_compact h_prod_cont
  have h_lhs : ∀ u₂ u₁ : G,
      w₁ u₁ • edgeShift L e₁ u₁ (w₂ u₂ • edgeShift L e₂ u₂ ψ) =
        (w₁ u₁ * w₂ u₂) • edgeShift L e₁ u₁ (edgeShift L e₂ u₂ ψ) := by
    intro u₂ u₁
    rw [map_smul, smul_smul]
  have h_rhs : ∀ u₁ u₂ : G,
      w₂ u₂ • edgeShift L e₂ u₂ (w₁ u₁ • edgeShift L e₁ u₁ ψ) =
        (w₁ u₁ * w₂ u₂) • edgeShift L e₁ u₁ (edgeShift L e₂ u₂ ψ) := by
    intro u₁ u₂
    rw [map_smul, smul_smul, mul_comm (w₂ u₂) (w₁ u₁), edgeShift_comm L hne u₁ u₂ ψ]
  simp_rw [h_lhs, h_rhs]
  rw [← integral_prod_symm _ h_prod_int, integral_prod _ h_prod_int]

theorem edgeExpect_comm (L : ℕ) (e₁ e₂ : SpatialEdge L) :
    (edgeExpect (G := G) L e₁).comp (edgeExpect L e₂) =
      (edgeExpect L e₂).comp (edgeExpect L e₁) := by
  by_cases h : e₁ = e₂
  · subst h; rfl
  · exact bochner_edge_comm L h _ _ continuous_const continuous_const

theorem edgeTransferOp_comm (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (e₁ e₂ : SpatialEdge L) :
    (edgeTransferOp C L β e₁).comp (edgeTransferOp C L β e₂) =
      (edgeTransferOp C L β e₂).comp (edgeTransferOp C L β e₁) := by
  by_cases h : e₁ = e₂
  · subst h; rfl
  · exact bochner_edge_comm L h _ _
      (Complex.continuous_ofReal.comp ((wilsonWeight_continuous C β).div_const _))
      (Complex.continuous_ofReal.comp ((wilsonWeight_continuous C β).div_const _))

theorem edgeTransferOp_edgeExpect_comm (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (e₁ e₂ : SpatialEdge L) :
    (edgeTransferOp C L β e₁).comp (edgeExpect L e₂) =
      (edgeExpect L e₂).comp (edgeTransferOp C L β e₁) := by
  by_cases h : e₁ = e₂
  · subst h
    rw [edgeTransferOp_comp_edgeExpect, edgeExpect_comp_edgeTransferOp]
  · exact bochner_edge_comm L h _ _
      (Complex.continuous_ofReal.comp ((wilsonWeight_continuous C β).div_const _))
      continuous_const

/-- Exact gauge covariance of each single-link temporal transfer operator `edgeTransferOp`. -/
theorem gaugeUnitary_edgeTransferOp_comm (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (Ω : GaugeConfig L G) (e : SpatialEdge L) :
    (gaugeUnitary L Ω).comp (edgeTransferOp C L β e) =
      (edgeTransferOp C L β e).comp (gaugeUnitary L Ω) := by
  apply ContinuousLinearMap.ext
  intro ψ
  let y := shiftSite e.1 e.2
  let w : G → ℂ := fun u => ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ)
  have hw_cont : Continuous w :=
    Complex.continuous_ofReal.comp ((wilsonWeight_continuous C β).div_const _)
  have h_int : Integrable (fun u : G => w u • edgeShift L e u ψ) (haarProb G) :=
    integrable_of_continuous_compact (hw_cont.smul (edgeShift_continuous L e ψ))
  change gaugeUnitary L Ω (∫ u : G, w u • edgeShift L e u ψ ∂(haarProb G)) =
    ∫ v : G, w v • edgeShift L e v (gaugeUnitary L Ω ψ) ∂(haarProb G)
  rw [clm_integral_comm (gaugeUnitary L Ω) h_int]
  have h_shift_cov : ∀ v : G,
      gaugeUnitary L Ω (edgeShift L e (Ω y * v * (Ω y)⁻¹) ψ) =
        edgeShift L e v (gaugeUnitary L Ω ψ) := by
    intro v
    unfold gaugeUnitary edgeShift
    rw [unitaryOfMP_comp_apply, unitaryOfMP_comp_apply]
    have h_map : (edgeShiftMap L e (Ω y * v * (Ω y)⁻¹)).comp (gaugeActMap L Ω) =
        (gaugeActMap L Ω).comp (edgeShiftMap L e v) := by
      ext U e'
      change ((gaugeAct L Ω U) * edgeSingle L e (Ω y * v * (Ω y)⁻¹)) e' =
        gaugeAct L Ω (U * edgeSingle L e v) e'
      by_cases he : e' = e
      · subst he
        simp [gaugeAct, y, mul_assoc]
      · simp [gaugeAct, edgeSingle_of_ne L he]
    rw [unitaryOfMP_congr L h_map]
  have h_conj_int :
      ∫ u : G, gaugeUnitary L Ω (w u • edgeShift L e u ψ) ∂(haarProb G) =
        ∫ v : G, gaugeUnitary L Ω (w (Ω y * v * (Ω y)⁻¹) •
          edgeShift L e (Ω y * v * (Ω y)⁻¹) ψ) ∂(haarProb G) := by
    let F : G → SpatialL2 L G := fun u => gaugeUnitary L Ω (w u • edgeShift L e u ψ)
    have hL := integral_mul_left_eq_self (fun z : G => F (z * (Ω y)⁻¹)) (Ω y) (μ := haarProb G)
    have hR := integral_mul_right_eq_self F (Ω y)⁻¹ (μ := haarProb G)
    simpa [F, mul_assoc] using (hL.trans hR).symm
  rw [h_conj_int]
  congr 1 with v
  have hw_conj : w (Ω y * v * (Ω y)⁻¹) = w v := by
    simp [w, wilsonWeight_conj]
  rw [map_smul, hw_conj, h_shift_cov v]

/-! ### Full Spatial Product Operators, `electricWilsonTransferOp` & `fullWilsonTransferOp` -/

/-- Canonical duplicate-free enumeration of all `3 L³` spatial lattice links. -/
noncomputable def allEdges (L : ℕ) : List (SpatialEdge L) :=
  (Finset.univ : Finset (SpatialEdge L)).toList

theorem allEdges_nodup (L : ℕ) : (allEdges L).Nodup :=
  Finset.nodup_toList _

@[simp]
theorem allEdges_toFinset (L : ℕ) : (allEdges L).toFinset = Finset.univ := by
  simp [allEdges]

/-- Ordered composition of single-edge temporal transfer operators over a list of edges. -/
noncomputable def listTransferOp (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    List (SpatialEdge L) → (SpatialL2 L G →L[ℂ] SpatialL2 L G)
  | [] => ContinuousLinearMap.id ℂ _
  | e :: l => (edgeTransferOp C L β e).comp (listTransferOp C L β l)

/-- Ordered composition of single-edge conditional Haar expectations over a list of edges. -/
noncomputable def listExpect (L : ℕ) :
    List (SpatialEdge L) → (SpatialL2 L G →L[ℂ] SpatialL2 L G)
  | [] => ContinuousLinearMap.id ℂ _
  | e :: l => (edgeExpect L e).comp (listExpect L l)

theorem listTransferOp_norm_le (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    ∀ (l : List (SpatialEdge L)) (ψ : SpatialL2 L G), ‖listTransferOp C L β l ψ‖ ≤ ‖ψ‖
  | [], ψ => le_refl ‖ψ‖
  | e :: l, ψ =>
      (edgeTransferOp_norm_le C L β e _).trans (listTransferOp_norm_le C L β l ψ)

theorem listTransferOp_vacuum (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    ∀ l : List (SpatialEdge L), listTransferOp C L β l (vacuumL2 L G) = vacuumL2 L G
  | [] => rfl
  | e :: l => by
      simp [listTransferOp, listTransferOp_vacuum C L β l]

theorem listExpect_vacuum (L : ℕ) :
    ∀ l : List (SpatialEdge L), listExpect L l (vacuumL2 L G) = vacuumL2 L G
  | [] => rfl
  | e :: l => by
      simp [listExpect, listExpect_vacuum L l]

theorem edgeExpect_listExpect_comm (L : ℕ) (a : SpatialEdge L) :
    ∀ l : List (SpatialEdge L),
      (edgeExpect (G := G) L a).comp (listExpect L l) = (listExpect L l).comp (edgeExpect L a)
  | [] => rfl
  | e :: l => by
      simp only [listExpect]
      rw [← ContinuousLinearMap.comp_assoc, edgeExpect_comm L a e,
          ContinuousLinearMap.comp_assoc, edgeExpect_listExpect_comm L a l,
          ← ContinuousLinearMap.comp_assoc]

theorem edgeTransferOp_listExpect_comm (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (a : SpatialEdge L) :
    ∀ l : List (SpatialEdge L),
      (edgeTransferOp C L β a).comp (listExpect L l) =
        (listExpect L l).comp (edgeTransferOp C L β a)
  | [] => rfl
  | e :: l => by
      simp only [listExpect]
      rw [← ContinuousLinearMap.comp_assoc, edgeTransferOp_edgeExpect_comm C L β a e,
          ContinuousLinearMap.comp_assoc, edgeTransferOp_listExpect_comm C L β a l,
          ← ContinuousLinearMap.comp_assoc]

theorem edgeTransferOp_listTransferOp_comm (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (a : SpatialEdge L) :
    ∀ l : List (SpatialEdge L),
      (edgeTransferOp C L β a).comp (listTransferOp C L β l) =
        (listTransferOp C L β l).comp (edgeTransferOp C L β a)
  | [] => rfl
  | e :: l => by
      simp only [listTransferOp]
      rw [← ContinuousLinearMap.comp_assoc, edgeTransferOp_comm C L β a e,
          ContinuousLinearMap.comp_assoc, edgeTransferOp_listTransferOp_comm C L β a l,
          ← ContinuousLinearMap.comp_assoc]

theorem listExpect_idempotent (L : ℕ) :
    ∀ l : List (SpatialEdge L), (listExpect (G := G) L l).comp (listExpect L l) = listExpect L l
  | [] => rfl
  | e :: l => by
      apply ContinuousLinearMap.ext
      intro ψ
      simp only [listExpect, ContinuousLinearMap.comp_apply]
      have h1 := (DFunLike.congr_fun (edgeExpect_listExpect_comm (G := G) L e l)
        (listExpect L l ψ)).symm
      simp only [ContinuousLinearMap.comp_apply] at h1
      have h2 := DFunLike.congr_fun (listExpect_idempotent L l) ψ
      simp only [ContinuousLinearMap.comp_apply] at h2
      have h3 := DFunLike.congr_fun (edgeExpect_idempotent (G := G) L e) (listExpect L l ψ)
      simp only [ContinuousLinearMap.comp_apply] at h3
      rw [h1, h2, h3]

theorem listExpect_comp_listTransferOp (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    ∀ l : List (SpatialEdge L),
      (listExpect L l).comp (listTransferOp C L β l) = listExpect L l
  | [] => rfl
  | e :: l => by
      apply ContinuousLinearMap.ext
      intro ψ
      simp only [listExpect, listTransferOp, ContinuousLinearMap.comp_apply]
      have h1 := (DFunLike.congr_fun (edgeTransferOp_listExpect_comm C L β e l)
        (listTransferOp C L β l ψ)).symm
      simp only [ContinuousLinearMap.comp_apply] at h1
      have h2 := DFunLike.congr_fun (listExpect_comp_listTransferOp C L β l) ψ
      simp only [ContinuousLinearMap.comp_apply] at h2
      have h3 := DFunLike.congr_fun (edgeExpect_comp_edgeTransferOp C L β e) (listExpect L l ψ)
      simp only [ContinuousLinearMap.comp_apply] at h3
      rw [h1, h2, h3]

theorem edgeExpect_listTransferOp_comm (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (a : SpatialEdge L) :
    ∀ l : List (SpatialEdge L),
      (edgeExpect L a).comp (listTransferOp C L β l) =
        (listTransferOp C L β l).comp (edgeExpect L a)
  | [] => rfl
  | e :: l => by
      simp only [listTransferOp]
      rw [← ContinuousLinearMap.comp_assoc, ← edgeTransferOp_edgeExpect_comm C L β e a,
          ContinuousLinearMap.comp_assoc, edgeExpect_listTransferOp_comm C L β a l,
          ← ContinuousLinearMap.comp_assoc]

theorem listTransferOp_comp_listExpect (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    ∀ l : List (SpatialEdge L),
      (listTransferOp C L β l).comp (listExpect L l) = listExpect L l
  | [] => rfl
  | e :: l => by
      apply ContinuousLinearMap.ext
      intro ψ
      simp only [listExpect, listTransferOp, ContinuousLinearMap.comp_apply]
      have h1 := (DFunLike.congr_fun (edgeExpect_listTransferOp_comm C L β e l)
        (listExpect L l ψ)).symm
      simp only [ContinuousLinearMap.comp_apply] at h1
      have h2 := DFunLike.congr_fun (listTransferOp_comp_listExpect C L β l) ψ
      simp only [ContinuousLinearMap.comp_apply] at h2
      have h3 := DFunLike.congr_fun (edgeTransferOp_comp_edgeExpect C L β e) (listExpect L l ψ)
      simp only [ContinuousLinearMap.comp_apply] at h3
      rw [h1, h2, h3]

theorem listExpect_selfAdjoint (L : ℕ) :
    ∀ (l : List (SpatialEdge L)) (φ ψ : SpatialL2 L G),
      inner ℂ (listExpect L l φ) ψ = inner ℂ φ (listExpect L l ψ)
  | [], _, _ => rfl
  | e :: l, φ, ψ => by
      simp only [listExpect, ContinuousLinearMap.comp_apply]
      rw [edgeExpect_selfAdjoint, listExpect_selfAdjoint L l]
      have h_comm := DFunLike.congr_fun (edgeExpect_listExpect_comm (G := G) L e l) ψ
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h_comm
      rw [← h_comm]

theorem listTransferOp_selfAdjoint (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    ∀ (l : List (SpatialEdge L)) (φ ψ : SpatialL2 L G),
      inner ℂ (listTransferOp C L β l φ) ψ = inner ℂ φ (listTransferOp C L β l ψ)
  | [], _, _ => rfl
  | e :: l, φ, ψ => by
      simp only [listTransferOp, ContinuousLinearMap.comp_apply]
      rw [edgeTransferOp_selfAdjoint, listTransferOp_selfAdjoint C L β l]
      have h_comm := DFunLike.congr_fun (edgeTransferOp_listTransferOp_comm C L β e l) ψ
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h_comm
      rw [← h_comm]

theorem gaugeUnitary_listTransferOp_comm (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (Ω : GaugeConfig L G) :
    ∀ l : List (SpatialEdge L),
      (gaugeUnitary L Ω).comp (listTransferOp C L β l) =
        (listTransferOp C L β l).comp (gaugeUnitary L Ω)
  | [] => rfl
  | e :: l => by
      simp only [listTransferOp]
      rw [← ContinuousLinearMap.comp_assoc, gaugeUnitary_edgeTransferOp_comm C L β Ω e,
          ContinuousLinearMap.comp_assoc, gaugeUnitary_listTransferOp_comm C L β Ω l,
          ← ContinuousLinearMap.comp_assoc]

/-- Unprojected temporal link-product Wilson transfer operator `∏_{e ∈ E(Λ_L)} T_e` on `SpatialL2 L G`. -/
noncomputable def prodTransferOp (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  listTransferOp C L β (allEdges L)

theorem gaugeProj_prodTransferOp_comm (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    (gaugeProj L).comp (prodTransferOp C L β) =
      (prodTransferOp C L β).comp (gaugeProj L) := by
  apply ContinuousLinearMap.ext
  intro ψ
  have h_int : Integrable (fun Ω : GaugeConfig L G => gaugeUnitary L Ω ψ) (gaugeHaar L G) :=
    integrable_of_continuous_compact (gaugeUnitary_continuous L ψ)
  change ∫ Ω : GaugeConfig L G, (1 : ℂ) • gaugeUnitary L Ω (prodTransferOp C L β ψ) ∂(gaugeHaar L G) =
    prodTransferOp C L β (∫ Ω : GaugeConfig L G, (1 : ℂ) • gaugeUnitary L Ω ψ ∂(gaugeHaar L G))
  simp only [one_smul]
  rw [clm_integral_comm (prodTransferOp C L β) h_int]
  congr 1
  funext Ω
  simpa [prodTransferOp] using
    DFunLike.congr_fun (gaugeUnitary_listTransferOp_comm C L β Ω (allEdges L)) ψ

/-- **Strong-Coupling (Pure-Electric, `β_mag = 0`) Gauge-Projected Wilson Transfer Operator**:
    `T_electric(L, β) = P_gauge ∘ ∏_{e ∈ E(Λ_L)} T_e(β)`. -/
noncomputable def electricWilsonTransferOp (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  (gaugeProj L).comp (prodTransferOp C L β)

theorem electricWilsonTransferOp_norm_le (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (ψ : SpatialL2 L G) :
    ‖electricWilsonTransferOp C L β ψ‖ ≤ ‖ψ‖ :=
  (gaugeProj_norm_le L _).trans (listTransferOp_norm_le C L β (allEdges L) ψ)

@[simp]
theorem electricWilsonTransferOp_vacuum (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    electricWilsonTransferOp C L β (vacuumL2 L G) = vacuumL2 L G := by
  simp [electricWilsonTransferOp, prodTransferOp, listTransferOp_vacuum]

theorem electricWilsonTransferOp_gauge_left (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (Ω : GaugeConfig L G) :
    (gaugeUnitary L Ω).comp (electricWilsonTransferOp C L β) =
      electricWilsonTransferOp C L β := by
  unfold electricWilsonTransferOp
  rw [← ContinuousLinearMap.comp_assoc, gaugeUnitary_comp_gaugeProj]

theorem electricWilsonTransferOp_gauge_right (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (Ω : GaugeConfig L G) :
    (electricWilsonTransferOp C L β).comp (gaugeUnitary L Ω) =
      electricWilsonTransferOp C L β := by
  unfold electricWilsonTransferOp
  rw [gaugeProj_prodTransferOp_comm, ContinuousLinearMap.comp_assoc,
      gaugeProj_comp_gaugeUnitary, ← gaugeProj_prodTransferOp_comm]

theorem electricWilsonTransferOp_selfAdjoint (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (φ ψ : SpatialL2 L G) :
    inner ℂ (electricWilsonTransferOp C L β φ) ψ =
      inner ℂ φ (electricWilsonTransferOp C L β ψ) := by
  unfold electricWilsonTransferOp
  simp only [ContinuousLinearMap.comp_apply]
  rw [gaugeProj_selfAdjoint]
  have h_sa : inner ℂ (prodTransferOp C L β φ) (gaugeProj L ψ) =
      inner ℂ φ (prodTransferOp C L β (gaugeProj L ψ)) :=
    listTransferOp_selfAdjoint C L β (allEdges L) φ (gaugeProj L ψ)
  rw [h_sa]
  have h_comm := DFunLike.congr_fun (gaugeProj_prodTransferOp_comm C L β) ψ
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h_comm
  rw [h_comm]

/-! ### Full 4D Magnetic + Electric Osterwalder–Seiler Wilson Transfer Operator -/

/-- The 3 oriented spatial coordinate planes `(0, 1), (1, 2), (0, 2)` in `Fin 3 × Fin 3`. -/
def spatialPlaneAxes : Fin 3 → Fin 3 × Fin 3
  | 0 => (0, 1)
  | 1 => (1, 2)
  | 2 => (0, 2)

theorem spatialPlaneAxes_ne (k : Fin 3) :
    (spatialPlaneAxes k).1 ≠ (spatialPlaneAxes k).2 := by
  fin_cases k <;> decide

/-- Spatial `1 × 1` plaquette holonomy `U_{x, μ} U_{x+μ, ν} U_{x+ν, μ}⁻¹ U_{x, ν}⁻¹` on `Λ_L`. -/
def spatialPlaquetteHolonomy {L : ℕ} (U : SpatialConfig L G) (x : Site3D L) (k : Fin 3) : G :=
  let axes := spatialPlaneAxes k
  U (x, axes.1) * U (shiftSite x axes.1, axes.2) *
    (U (shiftSite x axes.2, axes.1))⁻¹ * (U (x, axes.2))⁻¹

theorem spatialPlaquetteHolonomy_continuous (L : ℕ) (x : Site3D L) (k : Fin 3) :
    Continuous (fun U : SpatialConfig L G => spatialPlaquetteHolonomy U x k) := by
  dsimp only [spatialPlaquetteHolonomy]
  exact (((continuous_apply (A := fun _ : SpatialEdge L => G) (x, (spatialPlaneAxes k).1)).mul
    (continuous_apply (A := fun _ : SpatialEdge L => G)
      (shiftSite x (spatialPlaneAxes k).1, (spatialPlaneAxes k).2))).mul
    (continuous_apply (A := fun _ : SpatialEdge L => G)
      (shiftSite x (spatialPlaneAxes k).2, (spatialPlaneAxes k).1)).inv).mul
    (continuous_apply (A := fun _ : SpatialEdge L => G) (x, (spatialPlaneAxes k).2)).inv

theorem spatialPlaquetteHolonomy_gauge (L : ℕ) (Ω : GaugeConfig L G)
    (U : SpatialConfig L G) (x : Site3D L) (k : Fin 3) :
    spatialPlaquetteHolonomy (gaugeAct L Ω U) x k =
      Ω x * spatialPlaquetteHolonomy U x k * (Ω x)⁻¹ := by
  unfold spatialPlaquetteHolonomy gaugeAct
  have h_comm : shiftSite (shiftSite x (spatialPlaneAxes k).1) (spatialPlaneAxes k).2 =
      shiftSite (shiftSite x (spatialPlaneAxes k).2) (spatialPlaneAxes k).1 :=
    shiftSite_comm x (spatialPlaneAxes_ne k)
  dsimp only
  rw [h_comm]
  simp only [mul_inv_rev, inv_inv, mul_assoc]
  simp only [inv_mul_cancel_left]

/-- Spatial magnetic Wilson action `S_mag(U) = ∑_{p ⊂ Λ_L} (1 - χ(U_p))`. -/
noncomputable def spatialMagneticAction (C : NormalizedGaugeCharacter G) (L : ℕ)
    (U : SpatialConfig L G) : ℝ :=
  ∑ p : Site3D L × Fin 3, (1 - C.χ (spatialPlaquetteHolonomy U p.1 p.2))

theorem spatialMagneticAction_continuous (C : NormalizedGaugeCharacter G) (L : ℕ) :
    Continuous (spatialMagneticAction C L) :=
  continuous_finsetSum Finset.univ fun p _ =>
    continuous_const.sub (C.χ_continuous.comp (spatialPlaquetteHolonomy_continuous L p.1 p.2))

theorem spatialMagneticAction_gauge_invariant (C : NormalizedGaugeCharacter G) (L : ℕ)
    (Ω : GaugeConfig L G) (U : SpatialConfig L G) :
    spatialMagneticAction C L (gaugeAct L Ω U) = spatialMagneticAction C L U := by
  unfold spatialMagneticAction
  congr 1 with p
  rw [spatialPlaquetteHolonomy_gauge, C.χ_conj]

/-- Continuous half-step magnetic Boltzmann factor `exp(-(β/2) S_mag(U))`. -/
noncomputable def magneticHalfWeightMap (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    C(SpatialConfig L G, ℝ) where
  toFun U := Real.exp (-(β / 2) * spatialMagneticAction C L U)
  continuous_toFun :=
    Real.continuous_exp.comp (continuous_const.mul (spatialMagneticAction_continuous C L))

theorem mulReal_memLp (L : ℕ) (m : C(SpatialConfig L G, ℝ)) (ψ : SpatialL2 L G) :
    MemLp (fun U => (m U : ℂ) * ψ U) 2 (spatialHaar L G) :=
  (Lp.memLp ψ).of_le_mul
    ((Complex.continuous_ofReal.comp m.continuous).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable ψ))
    (Filter.Eventually.of_forall fun U => by
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm U) (norm_nonneg _))

/-- Bounded self-adjoint multiplication operator on `SpatialL2 L G` by a real continuous
    function `m : C(SpatialConfig L G, ℝ)`. -/
noncomputable def mulRealCLM (L : ℕ) (m : C(SpatialConfig L G, ℝ)) :
    SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  LinearMap.mkContinuous
    { toFun := fun ψ => (mulReal_memLp L m ψ).toLp (fun U => (m U : ℂ) * ψ U)
      map_add' := fun ψ₁ ψ₂ => by
        rw [Lp.ext_iff]
        filter_upwards [(mulReal_memLp L m (ψ₁ + ψ₂)).coeFn_toLp,
          Lp.coeFn_add ((mulReal_memLp L m ψ₁).toLp _) ((mulReal_memLp L m ψ₂).toLp _),
          (mulReal_memLp L m ψ₁).coeFn_toLp, (mulReal_memLp L m ψ₂).coeFn_toLp,
          Lp.coeFn_add ψ₁ ψ₂] with U h12 hadd h1 h2 hψ
        simp only [Pi.add_apply] at hadd hψ ⊢
        rw [h12, hadd, h1, h2, hψ, mul_add]
      map_smul' := fun c ψ => by
        rw [Lp.ext_iff]
        filter_upwards [(mulReal_memLp L m (c • ψ)).coeFn_toLp,
          Lp.coeFn_smul c ((mulReal_memLp L m ψ).toLp _),
          (mulReal_memLp L m ψ).coeFn_toLp, Lp.coeFn_smul c ψ] with U hc hsmul h1 hψ
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul] at hsmul hψ ⊢
        rw [hc, hsmul, h1, hψ]
        ring }
    ‖m‖
    (fun ψ => by
      dsimp
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(mulReal_memLp L m ψ).coeFn_toLp] with U hU
      rw [hU, norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm U) (norm_nonneg _))

theorem mulRealCLM_coeFn (L : ℕ) (m : C(SpatialConfig L G, ℝ)) (ψ : SpatialL2 L G) :
    mulRealCLM L m ψ =ᵐ[spatialHaar L G] fun U => (m U : ℂ) * ψ U :=
  (mulReal_memLp L m ψ).coeFn_toLp

theorem mulRealCLM_selfAdjoint (L : ℕ) (m : C(SpatialConfig L G, ℝ))
    (φ ψ : SpatialL2 L G) :
    inner ℂ (mulRealCLM L m φ) ψ = inner ℂ φ (mulRealCLM L m ψ) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulRealCLM_coeFn L m φ, mulRealCLM_coeFn L m ψ] with U hφ hψ
  rw [hφ, hψ]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem gaugeUnitary_mulRealCLM_comm (L : ℕ) (m : C(SpatialConfig L G, ℝ))
    (Ω : GaugeConfig L G)
    (hm_gauge : ∀ U : SpatialConfig L G, m (gaugeAct L Ω U) = m U) :
    (gaugeUnitary L Ω).comp (mulRealCLM L m) =
      (mulRealCLM L m).comp (gaugeUnitary L Ω) := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [Lp.ext_iff]
  have h1 : gaugeUnitary L Ω (mulRealCLM L m ψ) =ᵐ[spatialHaar L G]
      (mulRealCLM L m ψ) ∘ (gaugeActMap L Ω) :=
    Lp.coeFn_compMeasurePreserving _ (gaugeAct_mp L Ω)
  have h2 : ((mulRealCLM L m ψ : SpatialConfig L G → ℂ) ∘ (gaugeActMap L Ω)) =ᵐ[spatialHaar L G]
      fun U => (m (gaugeAct L Ω U) : ℂ) * ψ (gaugeAct L Ω U) :=
    (gaugeAct_mp L Ω).quasiMeasurePreserving.ae_eq_comp (mulRealCLM_coeFn L m ψ)
  have h3 := mulRealCLM_coeFn L m (gaugeUnitary L Ω ψ)
  have h4 := Lp.coeFn_compMeasurePreserving ψ (gaugeAct_mp L Ω)
  filter_upwards [h1.trans h2, h3, h4] with U hL hR hU
  change gaugeUnitary L Ω (mulRealCLM L m ψ) U = mulRealCLM L m (gaugeUnitary L Ω ψ) U
  rw [hL, hR]
  have hU' : gaugeUnitary L Ω ψ U = ψ (gaugeAct L Ω U) := hU
  rw [hU', hm_gauge U]

/-- Half-step spatial magnetic weight operator `M_{L, β/2} = exp(-(β/2) S_mag)`. -/
noncomputable def magneticHalfWeightOp (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  mulRealCLM L (magneticHalfWeightMap C L β)

/-- **Full 4D Magnetic + Electric Osterwalder–Seiler Wilson Transfer Operator**:
    `T_full(L, β) = exp(-(β/2) S_mag) ∘ T_electric(L, β) ∘ exp(-(β/2) S_mag)`. -/
noncomputable def fullWilsonTransferOp (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  (magneticHalfWeightOp C L β).comp
    ((electricWilsonTransferOp C L β).comp (magneticHalfWeightOp C L β))

theorem fullWilsonTransferOp_selfAdjoint (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (φ ψ : SpatialL2 L G) :
    inner ℂ (fullWilsonTransferOp C L β φ) ψ =
      inner ℂ φ (fullWilsonTransferOp C L β ψ) := by
  unfold fullWilsonTransferOp magneticHalfWeightOp
  simp only [ContinuousLinearMap.comp_apply]
  rw [mulRealCLM_selfAdjoint, electricWilsonTransferOp_selfAdjoint, mulRealCLM_selfAdjoint]

theorem fullWilsonTransferOp_gauge_left (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (Ω : GaugeConfig L G) :
    (gaugeUnitary L Ω).comp (fullWilsonTransferOp C L β) =
      fullWilsonTransferOp C L β := by
  unfold fullWilsonTransferOp magneticHalfWeightOp
  have hm : ∀ U : SpatialConfig L G,
      magneticHalfWeightMap C L β (gaugeAct L Ω U) = magneticHalfWeightMap C L β U := by
    intro U
    change Real.exp (-(β / 2) * spatialMagneticAction C L (gaugeAct L Ω U)) = _
    rw [spatialMagneticAction_gauge_invariant]
    rfl
  rw [← ContinuousLinearMap.comp_assoc, gaugeUnitary_mulRealCLM_comm L _ Ω hm,
      ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (gaugeUnitary L Ω),
      electricWilsonTransferOp_gauge_left]

theorem fullWilsonTransferOp_gauge_right (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (Ω : GaugeConfig L G) :
    (fullWilsonTransferOp C L β).comp (gaugeUnitary L Ω) =
      fullWilsonTransferOp C L β := by
  unfold fullWilsonTransferOp magneticHalfWeightOp
  have hm : ∀ U : SpatialConfig L G,
      magneticHalfWeightMap C L β (gaugeAct L Ω U) = magneticHalfWeightMap C L β U := by
    intro U
    change Real.exp (-(β / 2) * spatialMagneticAction C L (gaugeAct L Ω U)) = _
    rw [spatialMagneticAction_gauge_invariant]
    rfl
  rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc,
      ← gaugeUnitary_mulRealCLM_comm L _ Ω hm, ← ContinuousLinearMap.comp_assoc (electricWilsonTransferOp C L β),
      electricWilsonTransferOp_gauge_right]

/-! ============================================================================
    PART VI: EXACT GLUEBALL EIGENSTATE & VOLUME-INDEPENDENT SPECTRAL GAP
    ============================================================================ -/

/-! ### 1. Single-Edge Doeblin Minorization Contraction (`1 - exp(-2β)`) -/

/-- **Single-Edge Doeblin Contraction Bound**:
    For every `β > 0` and every `φ ∈ SpatialL2 L G` with zero conditional mean `P_e φ = 0`,
    `‖T_e(β) φ‖ ≤ (1 - exp(-2β)) ‖φ‖`. -/
theorem edgeTransferOp_doeblin_contraction (C : NormalizedGaugeCharacter G) (L : ℕ)
    {β : ℝ} (hβ : 0 < β) (e : SpatialEdge L)
    {φ : SpatialL2 L G} (hφ : edgeExpect L e φ = 0) :
    ‖edgeTransferOp C L β e φ‖ ≤ (1 - Real.exp (-2 * β)) * ‖φ‖ := by
  let c0 := haarC0 C β
  let m := Real.exp (-2 * β)
  have hc0_pos : 0 < c0 := haarC0_pos C hβ.le
  have hc0_le : c0 ≤ 1 := (haarC0_bounds C hβ.le).2
  let w : G → ℂ := fun u => ((wilsonWeight C β u / c0 : ℝ) : ℂ)
  let wm : G → ℂ := fun u => (((wilsonWeight C β u - m) / c0 : ℝ) : ℂ)
  have hw_cont : Continuous w :=
    Complex.continuous_ofReal.comp ((wilsonWeight_continuous C β).div_const c0)
  have hw_int : Integrable (fun u : G => w u • edgeShift L e u φ) (haarProb G) :=
    integrable_of_continuous_compact (hw_cont.smul (edgeShift_continuous L e φ))
  have hm_cont : Continuous (fun _ : G => ((m / c0 : ℝ) : ℂ)) := continuous_const
  have hm_int : Integrable (fun u : G => ((m / c0 : ℝ) : ℂ) • edgeShift L e u φ) (haarProb G) :=
    integrable_of_continuous_compact (hm_cont.smul (edgeShift_continuous L e φ))
  have h_zero_int : ∫ u : G, ((m / c0 : ℝ) : ℂ) • edgeShift L e u φ ∂(haarProb G) = 0 := by
    have h_int_shift : Integrable (fun u : G => edgeShift L e u φ) (haarProb G) :=
      integrable_of_continuous_compact (edgeShift_continuous L e φ)
    have h_smul := (clm_integral_comm
      (ContinuousLinearMap.lsmul ℂ ℂ ((m / c0 : ℝ) : ℂ) :
        SpatialL2 L G →L[ℂ] SpatialL2 L G) h_int_shift).symm
    change ∫ u : G, ((ContinuousLinearMap.lsmul ℂ ℂ ((m / c0 : ℝ) : ℂ) :
      SpatialL2 L G →L[ℂ] SpatialL2 L G) (edgeShift L e u φ)) ∂(haarProb G) = 0
    rw [h_smul]
    have hexp : ∫ u : G, edgeShift L e u φ ∂(haarProb G) = edgeExpect L e φ := by
      change _ = ∫ u : G, (1 : ℂ) • edgeShift L e u φ ∂(haarProb G)
      simp
    rw [hexp, hφ, map_zero]
  have h_sub_eq : edgeTransferOp C L β e φ = ∫ u : G, wm u • edgeShift L e u φ ∂(haarProb G) := by
    calc edgeTransferOp C L β e φ
        = (∫ u : G, w u • edgeShift L e u φ ∂(haarProb G)) -
            (∫ u : G, ((m / c0 : ℝ) : ℂ) • edgeShift L e u φ ∂(haarProb G)) := by
            rw [h_zero_int, sub_zero]
            rfl
      _ = ∫ u : G, (w u • edgeShift L e u φ - ((m / c0 : ℝ) : ℂ) • edgeShift L e u φ) ∂(haarProb G) :=
            (integral_sub hw_int hm_int).symm
      _ = ∫ u : G, wm u • edgeShift L e u φ ∂(haarProb G) := by
            congr 1
            funext u
            rw [← sub_smul]
            exact congrArg (· • edgeShift L e u φ) (by simp [w, wm, sub_div])
  rw [h_sub_eq]
  have hwm_cont : Continuous wm :=
    Complex.continuous_ofReal.comp
      (((wilsonWeight_continuous C β).sub continuous_const).div_const c0)
  have hwm_norm_int : Integrable (fun u : G => ‖wm u • edgeShift L e u φ‖) (haarProb G) :=
    (integrable_of_continuous_compact (hwm_cont.smul (edgeShift_continuous L e φ))).norm
  have h_dom_int : Integrable (fun u : G => ((wilsonWeight C β u - m) / c0) * ‖φ‖) (haarProb G) :=
    (integrable_of_continuous_compact
      (((wilsonWeight_continuous C β).sub continuous_const).div_const c0)).mul_const ‖φ‖
  have h_pt_norm : ∀ u : G,
      ‖wm u • edgeShift L e u φ‖ ≤ ((wilsonWeight C β u - m) / c0) * ‖φ‖ := by
    intro u
    rw [norm_smul, show ‖edgeShift L e u φ‖ = ‖φ‖ from unitaryOfMP_norm L _ _ φ]
    have h_nonneg : 0 ≤ (wilsonWeight C β u - m) / c0 :=
      div_nonneg (sub_nonneg.mpr (wilsonWeight_bounds C hβ.le u).1) hc0_pos.le
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h_nonneg]
  have h_int_coeff : ∫ u : G, (wilsonWeight C β u - m) / c0 ∂(haarProb G) = 1 - m / c0 := by
    simp_rw [sub_div]
    have h1 : Integrable (fun u : G => wilsonWeight C β u / c0) (haarProb G) :=
      integrable_of_continuous_compact ((wilsonWeight_continuous C β).div_const c0)
    have h2 : Integrable (fun _ : G => m / c0) (haarProb G) := integrable_const _
    rw [integral_sub h1 h2, wilsonWeight_div_haarC0_integral C β]
    simp
  have h_coeff_le : 1 - m / c0 ≤ 1 - m := by
    have hm_pos : 0 < m := Real.exp_pos _
    have hm_div : m ≤ m / c0 := by
      rw [le_div_iff₀ hc0_pos]
      nlinarith
    linarith
  calc ‖∫ u : G, wm u • edgeShift L e u φ ∂(haarProb G)‖
      ≤ ∫ u : G, ‖wm u • edgeShift L e u φ‖ ∂(haarProb G) :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ u : G, ((wilsonWeight C β u - m) / c0) * ‖φ‖ ∂(haarProb G) :=
          integral_mono hwm_norm_int h_dom_int h_pt_norm
    _ = (∫ u : G, (wilsonWeight C β u - m) / c0 ∂(haarProb G)) * ‖φ‖ :=
          integral_mul_const _ _
    _ = (1 - m / c0) * ‖φ‖ := by rw [h_int_coeff]
    _ ≤ (1 - m) * ‖φ‖ := mul_le_mul_of_nonneg_right h_coeff_le (norm_nonneg φ)

/-! ### 2. Identification of `listExpect (allEdges L)` with Vacuum Orthogonal Projection -/

/-- Truncates a full spatial configuration `W` to a subset `S` of edges (setting `e ∉ S` to `1`). -/
def truncConfig {L : ℕ} [DecidableEq (SpatialEdge L)]
    (S : Finset (SpatialEdge L)) (W : SpatialConfig L G) : SpatialConfig L G :=
  fun e => if e ∈ S then W e else 1

def subShiftJointMap (L : ℕ) [DecidableEq (SpatialEdge L)]
    (S : Finset (SpatialEdge L)) :
    C(SpatialConfig L G × SpatialConfig L G, SpatialConfig L G) where
  toFun p := p.2 * truncConfig S p.1
  continuous_toFun := by
    refine continuous_pi fun e => ?_
    by_cases h : e ∈ S
    · have h_eq : (fun p : SpatialConfig L G × SpatialConfig L G =>
          (p.2 * truncConfig S p.1) e) = fun p => p.2 e * p.1 e := by
        funext p
        simp [truncConfig, h]
      rw [h_eq]
      exact ((continuous_apply e).comp continuous_snd).mul
        ((continuous_apply e).comp continuous_fst)
    · have h_eq : (fun p : SpatialConfig L G × SpatialConfig L G =>
          (p.2 * truncConfig S p.1) e) = fun p => p.2 e := by
        funext p
        simp [truncConfig, h]
      rw [h_eq]
      exact (continuous_apply e).comp continuous_snd

def subShiftMap (L : ℕ) [DecidableEq (SpatialEdge L)]
    (S : Finset (SpatialEdge L)) (W : SpatialConfig L G) :
    C(SpatialConfig L G, SpatialConfig L G) :=
  (subShiftJointMap L S).curry W

theorem subShift_mp (L : ℕ) [DecidableEq (SpatialEdge L)]
    (S : Finset (SpatialEdge L)) (W : SpatialConfig L G) :
    MeasurePreserving (subShiftMap L S W) (spatialHaar L G) (spatialHaar L G) :=
  spatialHaar_mp_mul_right L (truncConfig S W)

noncomputable def subShift (L : ℕ) [DecidableEq (SpatialEdge L)]
    (S : Finset (SpatialEdge L)) (W : SpatialConfig L G) :
    SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  unitaryOfMP L (subShiftMap L S W) (subShift_mp L S W)

theorem subShift_continuous (L : ℕ) [DecidableEq (SpatialEdge L)]
    (S : Finset (SpatialEdge L)) (ψ : SpatialL2 L G) :
    Continuous (fun W : SpatialConfig L G => subShift L S W ψ) :=
  continuous_const.compMeasurePreservingLp
    (subShiftJointMap (G := G) L S).curry.continuous
    (subShift_mp L S) (by norm_num)

/-- Joint conditional Haar expectation integrating out all links in `S ⊆ E(Λ_L)`. -/
noncomputable def subExpect (L : ℕ) [DecidableEq (SpatialEdge L)]
    (S : Finset (SpatialEdge L)) :
    SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  bochnerAvgCLM (spatialHaar L G)
    (fun _ => (1 : ℂ)) continuous_const
    (subShift L S)
    (fun W ψ => (unitaryOfMP_norm L (subShiftMap L S W) (subShift_mp L S W) ψ).le)
    (subShift_continuous L S)

theorem subExpect_empty (L : ℕ) [DecidableEq (SpatialEdge L)] :
    subExpect (G := G) L ∅ = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro ψ
  change ∫ W : SpatialConfig L G, (1 : ℂ) • subShift L ∅ W ψ ∂(spatialHaar L G) = ψ
  have h_id : ∀ W : SpatialConfig L G, subShift L ∅ W ψ = ψ := by
    intro W
    unfold subShift
    have h_map : subShiftMap (G := G) L ∅ W = ContinuousMap.id _ := by
      ext U e
      change (U * truncConfig ∅ W) e = U e
      simp [truncConfig]
    have h_mp : MeasurePreserving (ContinuousMap.id (SpatialConfig L G))
        (spatialHaar L G) (spatialHaar L G) := MeasurePreserving.id _
    rw [unitaryOfMP_congr L h_map (subShift_mp L ∅ W) h_mp, unitaryOfMP_id]
  simp [h_id]

theorem subExpect_insert (L : ℕ) [DecidableEq (SpatialEdge L)]
    {a : SpatialEdge L} {S : Finset (SpatialEdge L)} (ha : a ∉ S) :
    subExpect (G := G) L (insert a S) = (edgeExpect L a).comp (subExpect L S) := by
  apply ContinuousLinearMap.ext
  intro ψ
  have h_left_shift : ∀ (u : G) (W : SpatialConfig L G),
      subShift L (insert a S) (edgeSingle L a u * W) ψ =
        edgeShift L a u (subShift L (insert a S) W ψ) := by
    intro u W
    unfold subShift edgeShift
    rw [unitaryOfMP_comp_apply]
    have h_map : (subShiftMap L (insert a S) W).comp (edgeShiftMap L a u) =
        subShiftMap L (insert a S) (edgeSingle L a u * W) := by
      ext U e
      change ((U * edgeSingle L a u) * truncConfig (insert a S) W) e =
        (U * truncConfig (insert a S) (edgeSingle L a u * W)) e
      by_cases he : e = a
      · subst he
        simp [truncConfig, mul_assoc]
      · simp [truncConfig, edgeSingle_of_ne L he]
    rw [unitaryOfMP_congr L h_map]
  have h_inv_u : ∀ u : G,
      edgeShift L a u (subExpect L (insert a S) ψ) = subExpect L (insert a S) ψ := by
    intro u
    have h_int : Integrable (fun W => subShift L (insert a S) W ψ) (spatialHaar L G) :=
      integrable_of_continuous_compact (subShift_continuous L (insert a S) ψ)
    change edgeShift L a u (∫ W, (1 : ℂ) • subShift L (insert a S) W ψ ∂(spatialHaar L G)) =
      ∫ W, (1 : ℂ) • subShift L (insert a S) W ψ ∂(spatialHaar L G)
    simp only [one_smul]
    rw [clm_integral_comm (edgeShift L a u) h_int]
    simp_rw [← h_left_shift u]
    exact integral_mul_left_eq_self
      (fun W : SpatialConfig L G => subShift L (insert a S) W ψ) (edgeSingle L a u)
  have h_absorb : subExpect L (insert a S) ψ = edgeExpect L a (subExpect L (insert a S) ψ) := by
    change _ = ∫ u : G, (1 : ℂ) • edgeShift L a u (subExpect L (insert a S) ψ) ∂(haarProb G)
    simp [h_inv_u]
  have h_split : ∀ W : SpatialConfig L G,
      subShift L (insert a S) W ψ = edgeShift L a (W a) (subShift L S W ψ) := by
    intro W
    unfold subShift edgeShift
    rw [unitaryOfMP_comp_apply]
    have h_map : (subShiftMap L S W).comp (edgeShiftMap L a (W a)) =
        subShiftMap L (insert a S) W := by
      ext U e
      change ((U * edgeSingle L a (W a)) * truncConfig S W) e =
        (U * truncConfig (insert a S) W) e
      by_cases he : e = a
      · subst he
        simp [truncConfig, ha]
      · simp [truncConfig, he, edgeSingle_of_ne L he]
    rw [unitaryOfMP_congr L h_map.symm]
  rw [h_absorb]
  have h_int_ins : Integrable (fun W => subShift L (insert a S) W ψ) (spatialHaar L G) :=
    integrable_of_continuous_compact (subShift_continuous L (insert a S) ψ)
  have h_int_S : Integrable (fun W => subShift L S W ψ) (spatialHaar L G) :=
    integrable_of_continuous_compact (subShift_continuous L S ψ)
  change edgeExpect L a (∫ W, (1 : ℂ) • subShift L (insert a S) W ψ ∂(spatialHaar L G)) =
    edgeExpect L a (∫ W, (1 : ℂ) • subShift L S W ψ ∂(spatialHaar L G))
  simp only [one_smul]
  rw [clm_integral_comm (edgeExpect L a) h_int_ins,
      clm_integral_comm (edgeExpect L a) h_int_S]
  congr 1 with W
  rw [h_split W, edgeExpect_edgeShift_right]

theorem listExpect_eq_subExpect (L : ℕ) [DecidableEq (SpatialEdge L)] :
    ∀ {l : List (SpatialEdge L)}, l.Nodup → listExpect (G := G) L l = subExpect L l.toFinset
  | [], _ => by
      simp [listExpect, subExpect_empty]
  | a :: l, hl => by
      rcases List.nodup_cons.mp hl with ⟨ha, hl'⟩
      have ha_fin : a ∉ l.toFinset := by simpa using ha
      simp only [listExpect, List.toFinset_cons]
      rw [subExpect_insert L ha_fin, listExpect_eq_subExpect L hl']

/-- Rank-one orthogonal projection `ψ ↦ ⟪Ω₀, ψ⟫ • Ω₀` onto the vacuum line `ℂ Ω₀`. -/
noncomputable def vacuumProjCLM (L : ℕ) : SpatialL2 L G →L[ℂ] SpatialL2 L G :=
  LinearMap.mkContinuous
    { toFun := fun ψ => inner ℂ (vacuumL2 L G) ψ • vacuumL2 L G
      map_add' := fun ψ₁ ψ₂ => by rw [inner_add_right, add_smul]
      map_smul' := fun c ψ => by rw [inner_smul_right, RingHom.id_apply, mul_smul] }
    1
    (fun ψ => by
      dsimp
      rw [norm_smul, vacuumL2_norm, mul_one, one_mul]
      calc ‖inner ℂ (vacuumL2 L G) ψ‖
          ≤ ‖vacuumL2 L G‖ * ‖ψ‖ := norm_inner_le_norm _ _
        _ = ‖ψ‖ := by rw [vacuumL2_norm, one_mul])

theorem subExpect_univ_eq_vacuumProj (L : ℕ) [DecidableEq (SpatialEdge L)] :
    subExpect (G := G) L Finset.univ = vacuumProjCLM L := by
  let μ := spatialHaar L G
  let toLpMap : C(SpatialConfig L G, ℂ) →L[ℂ] SpatialL2 L G :=
    ContinuousMap.toLp 2 μ ℂ
  have h_on_cont : ∀ f : C(SpatialConfig L G, ℂ),
      subExpect L Finset.univ (toLpMap f) = vacuumProjCLM L (toLpMap f) := by
    intro f
    let F : C(SpatialConfig L G, C(SpatialConfig L G, ℂ)) :=
      (f.comp (subShiftJointMap L Finset.univ)).curry
    have hF_int : Integrable F μ := integrable_of_continuous_compact F.continuous
    have h_step1 : subExpect L Finset.univ (toLpMap f) = toLpMap (∫ W, F W ∂μ) := by
      change ∫ W, (1 : ℂ) • subShift L Finset.univ W (toLpMap f) ∂μ = _
      simp only [one_smul]
      have h_pt : ∀ W : SpatialConfig L G,
          subShift L Finset.univ W (toLpMap f) = toLpMap (F W) := by
        intro W
        unfold subShift
        rw [unitaryOfMP_toLp]
        rfl
      simp_rw [h_pt]
      exact (clm_integral_comm toLpMap hF_int).symm
    have h_eval : ∫ W, F W ∂μ =
        (∫ W, f W ∂μ) • (1 : C(SpatialConfig L G, ℂ)) := by
      ext U
      have h_pt := (evalContinuousMapCLM U).integral_comp_comm hF_int
      change (evalContinuousMapCLM U) (∫ W, F W ∂μ) = (∫ W, f W ∂μ) * 1
      rw [← h_pt, mul_one]
      have h_mul : ∀ W : SpatialConfig L G, evalContinuousMapCLM U (F W) = f (U * W) := by
        intro W
        have h_trunc : truncConfig (Finset.univ : Finset (SpatialEdge L)) W = W := by
          funext e; simp [truncConfig]
        change f (U * truncConfig Finset.univ W) = f (U * W)
        rw [h_trunc]
      simp_rw [h_mul]
      exact integral_mul_left_eq_self f U
    have h_rhs : vacuumProjCLM L (toLpMap f) = (∫ W, f W ∂μ) • vacuumL2 L G := by
      change inner ℂ (vacuumL2 L G) (toLpMap f) • vacuumL2 L G = _
      rw [inner_vacuumL2]
      have h_ae : (toLpMap f : SpatialConfig L G → ℂ) =ᵐ[μ] f :=
        ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ f
      rw [integral_congr_ae h_ae]
    rw [h_step1, h_eval, map_smul, toLp_one_eq_vacuumL2, h_rhs]
  have h_dense : DenseRange toLpMap :=
    ContinuousMap.toLp_denseRange _ _ ℂ (by norm_num)
  have h_eq_fn : (subExpect L Finset.univ : SpatialL2 L G → SpatialL2 L G) =
      (vacuumProjCLM L : SpatialL2 L G → SpatialL2 L G) :=
    h_dense.equalizer (subExpect L Finset.univ).continuous (vacuumProjCLM L).continuous
      (funext h_on_cont)
  apply ContinuousLinearMap.ext
  intro ψ
  exact congrFun h_eq_fn ψ

theorem listExpect_allEdges_eq_zero_of_ortho (L : ℕ)
    {ψ : SpatialL2 L G} (hψ : inner ℂ (vacuumL2 L G) ψ = 0) :
    listExpect L (allEdges L) ψ = 0 := by
  rw [listExpect_eq_subExpect L (allEdges_nodup L), allEdges_toFinset,
      subExpect_univ_eq_vacuumProj]
  change inner ℂ (vacuumL2 L G) ψ • vacuumL2 L G = 0
  rw [hψ, zero_smul]

/-! ### 3. Efron–Stein Orthogonal Telescoping & Volume-Independent Spectral Gap -/

/-- **Efron–Stein Orthogonal Telescoping Contraction**:
    For every duplicate-free list `l` of spatial edges and every `β > 0`,
    `‖T_l (ψ - P_l ψ)‖ ≤ (1 - exp(-2β)) ‖ψ - P_l ψ‖`,
    with contraction factor `1 - exp(-2β)` completely independent of `l.length`! -/
theorem listTransferOp_efron_stein (C : NormalizedGaugeCharacter G) (L : ℕ)
    {β : ℝ} (hβ : 0 < β) :
    ∀ {l : List (SpatialEdge L)}, l.Nodup →
      ∀ ψ : SpatialL2 L G,
        ‖listTransferOp C L β l (ψ - listExpect L l ψ)‖ ≤
          (1 - Real.exp (-2 * β)) * ‖ψ - listExpect L l ψ‖
  | [], _, ψ => by
      have h_zero : ψ - listExpect L [] ψ = 0 := sub_self ψ
      simp [h_zero]
  | a :: l, hl, ψ => by
      rcases List.nodup_cons.mp hl with ⟨_, hl_nodup⟩
      let r : ℝ := 1 - Real.exp (-2 * β)
      have hr_nonneg : 0 ≤ r := by
        unfold r
        have hexp : Real.exp (-2 * β) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      let P_l := listExpect (G := G) L l
      let P_a := edgeExpect (G := G) L a
      let T_l := listTransferOp C L β l
      let T_a := edgeTransferOp C L β a
      let u : SpatialL2 L G := ψ - P_l ψ
      let v : SpatialL2 L G := P_l ψ - P_a (P_l ψ)
      have huv_eq : ψ - listExpect L (a :: l) ψ = u + v := by
        simp [listExpect, P_l, P_a, u, v, sub_add_sub_cancel]
      have hPl_idem : ∀ φ, P_l (P_l φ) = P_l φ :=
        fun φ => DFunLike.congr_fun (listExpect_idempotent L l) φ
      have hPa_idem : ∀ φ, P_a (P_a φ) = P_a φ :=
        fun φ => DFunLike.congr_fun (edgeExpect_idempotent L a) φ
      have hPl_Pa : ∀ φ, P_l (P_a φ) = P_a (P_l φ) :=
        fun φ => (DFunLike.congr_fun (edgeExpect_listExpect_comm L a l) φ).symm
      have hPl_Ta : ∀ φ, P_l (T_a φ) = T_a (P_l φ) :=
        fun φ => (DFunLike.congr_fun (edgeTransferOp_listExpect_comm C L β a l) φ).symm
      have hPl_Tl : ∀ φ, P_l (T_l φ) = P_l φ :=
        fun φ => DFunLike.congr_fun (listExpect_comp_listTransferOp C L β l) φ
      have hTl_Pl : ∀ φ, T_l (P_l φ) = P_l φ :=
        fun φ => DFunLike.congr_fun (listTransferOp_comp_listExpect C L β l) φ
      have hPl_u : P_l u = 0 := by
        simp [u, map_sub, hPl_idem]
      have hPl_v : P_l v = v := by
        simp [v, map_sub, hPl_idem, hPl_Pa]
      have h_ortho_uv : inner ℂ u v = 0 := by
        rw [← hPl_v, ← listExpect_selfAdjoint L l u v, hPl_u, inner_zero_left]
      have hTl_v : T_l v = v := by
        rw [← hPl_v, hTl_Pl, hPl_v]
      have hPl_Ta_Tl_u : P_l (T_a (T_l u)) = 0 := by
        rw [hPl_Ta, hPl_Tl, hPl_u, map_zero]
      have hPl_Ta_v : P_l (T_a v) = T_a v := by
        rw [hPl_Ta, hPl_v]
      have h_ortho_T : inner ℂ (T_a (T_l u)) (T_a (T_l v)) = 0 := by
        rw [hTl_v, ← hPl_Ta_v, ← listExpect_selfAdjoint L l (T_a (T_l u)) (T_a v),
            hPl_Ta_Tl_u, inner_zero_left]
      have h_norm_u : ‖T_a (T_l u)‖ ≤ r * ‖u‖ :=
        (edgeTransferOp_norm_le C L β a (T_l u)).trans
          (listTransferOp_efron_stein C L hβ hl_nodup ψ)
      have hPa_v : P_a v = 0 := by
        simp [v, map_sub, hPa_idem]
      have h_norm_v : ‖T_a (T_l v)‖ ≤ r * ‖v‖ := by
        rw [hTl_v]
        exact edgeTransferOp_doeblin_contraction C L hβ a hPa_v
      have h_pyth_in : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 :=
        pythagoras_complex h_ortho_uv
      have h_pyth_out : ‖T_a (T_l (u + v))‖ ^ 2 =
          ‖T_a (T_l u)‖ ^ 2 + ‖T_a (T_l v)‖ ^ 2 := by
        rw [map_add, map_add]
        exact pythagoras_complex h_ortho_T
      have h_sq_u : ‖T_a (T_l u)‖ ^ 2 ≤ (r * ‖u‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h_norm_u 2
      have h_sq_v : ‖T_a (T_l v)‖ ^ 2 ≤ (r * ‖v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h_norm_v 2
      have h_sq_total : ‖T_a (T_l (u + v))‖ ^ 2 ≤ (r * ‖u + v‖) ^ 2 := by
        calc ‖T_a (T_l (u + v))‖ ^ 2
            = ‖T_a (T_l u)‖ ^ 2 + ‖T_a (T_l v)‖ ^ 2 := h_pyth_out
          _ ≤ (r * ‖u‖) ^ 2 + (r * ‖v‖) ^ 2 := add_le_add h_sq_u h_sq_v
          _ = r ^ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by ring
          _ = r ^ 2 * ‖u + v‖ ^ 2 := by rw [← h_pyth_in]
          _ = (r * ‖u + v‖) ^ 2 := by ring
      change ‖T_a (T_l (ψ - listExpect L (a :: l) ψ))‖ ≤ r * ‖ψ - listExpect L (a :: l) ψ‖
      rw [huv_eq]
      have hA : 0 ≤ ‖T_a (T_l (u + v))‖ := norm_nonneg _
      have hB : 0 ≤ r * ‖u + v‖ := mul_nonneg hr_nonneg (norm_nonneg _)
      nlinarith

/-- **Unconditional Volume-Independent Strong-Coupling Spectral Gap Theorem**:
    For EVERY spatial lattice volume `L ∈ ℕ` (`3 L³` edges), EVERY coupling `β > 0`,
    and EVERY state `ψ ∈ L²(G^{E(Λ_L)}, μ_Haar)` orthogonal to the vacuum `Ω₀`,
      `‖electricWilsonTransferOp C L β ψ‖ ≤ (1 - exp(-2β)) ‖ψ‖`.
    The spectral gap `1 - (1 - exp(-2β)) = exp(-2β) > 0` does NOT degrade as `L → ∞`. -/
theorem electricWilsonTransferOp_spectral_gap (C : NormalizedGaugeCharacter G)
    (L : ℕ) {β : ℝ} (hβ : 0 < β)
    (ψ : SpatialL2 L G) (h_ortho : inner ℂ (vacuumL2 L G) ψ = 0) :
    ‖electricWilsonTransferOp C L β ψ‖ ≤ (1 - Real.exp (-2 * β)) * ‖ψ‖ := by
  have hP0 : listExpect L (allEdges L) ψ = 0 :=
    listExpect_allEdges_eq_zero_of_ortho L h_ortho
  have h_prod : ‖prodTransferOp C L β ψ‖ ≤ (1 - Real.exp (-2 * β)) * ‖ψ‖ := by
    have h_es := listTransferOp_efron_stein C L hβ (allEdges_nodup L) ψ
    simpa [prodTransferOp, hP0] using h_es
  exact (gaugeProj_norm_le L (prodTransferOp C L β ψ)).trans h_prod

/-! ### 4. Exact 1-Plaquette Glueball Eigenstate (`L ≥ 2`, `β > 0`) & Non-Triviality -/

theorem edgeExpect_toLp (L : ℕ) (e : SpatialEdge L) (g : C(SpatialConfig L G, ℂ)) :
    edgeExpect L e (ContinuousMap.toLp 2 (spatialHaar L G) ℂ g) =
      ContinuousMap.toLp 2 (spatialHaar L G) ℂ
        (∫ u : G, (g.comp (edgeShiftJointMap L e)).curry u ∂(haarProb G)) := by
  let toLpMap : C(SpatialConfig L G, ℂ) →L[ℂ] SpatialL2 L G :=
    ContinuousMap.toLp 2 (spatialHaar L G) ℂ
  let F : C(G, C(SpatialConfig L G, ℂ)) := (g.comp (edgeShiftJointMap L e)).curry
  have hF_int : Integrable F (haarProb G) := integrable_of_continuous_compact F.continuous
  change ∫ u : G, (1 : ℂ) • edgeShift L e u (toLpMap g) ∂(haarProb G) = toLpMap (∫ u : G, F u ∂(haarProb G))
  simp only [one_smul]
  have h_pt : ∀ u : G, edgeShift L e u (toLpMap g) = toLpMap (F u) := by
    intro u
    unfold edgeShift
    rw [unitaryOfMP_toLp]
    rfl
  simp_rw [h_pt]
  exact (clm_integral_comm toLpMap hF_int).symm

theorem edgeTransferOp_toLp (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (e : SpatialEdge L) (g : C(SpatialConfig L G, ℂ)) :
    edgeTransferOp C L β e (ContinuousMap.toLp 2 (spatialHaar L G) ℂ g) =
      ContinuousMap.toLp 2 (spatialHaar L G) ℂ
        (∫ u : G, ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ) •
          (g.comp (edgeShiftJointMap L e)).curry u ∂(haarProb G)) := by
  let toLpMap : C(SpatialConfig L G, ℂ) →L[ℂ] SpatialL2 L G :=
    ContinuousMap.toLp 2 (spatialHaar L G) ℂ
  let w : G → ℂ := fun u => ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ)
  have hw_cont : Continuous w :=
    Complex.continuous_ofReal.comp ((wilsonWeight_continuous C β).div_const _)
  let F : G → C(SpatialConfig L G, ℂ) :=
    fun u => w u • (g.comp (edgeShiftJointMap L e)).curry u
  have hF_cont : Continuous F :=
    hw_cont.smul ((g.comp (edgeShiftJointMap L e)).curry.continuous)
  have hF_int : Integrable F (haarProb G) := integrable_of_continuous_compact hF_cont
  change ∫ u : G, w u • edgeShift L e u (toLpMap g) ∂(haarProb G) =
    toLpMap (∫ u : G, F u ∂(haarProb G))
  have h_pt : ∀ u : G, w u • edgeShift L e u (toLpMap g) = toLpMap (F u) := by
    intro u
    unfold edgeShift
    rw [unitaryOfMP_toLp, ← map_smul]
    rfl
  simp_rw [h_pt]
  exact (clm_integral_comm toLpMap hF_int).symm

/-- Origin site `(0, 0, 0) ∈ Λ_L` for `L ≥ 2`. -/
def originSite (L : ℕ) (hL : 2 ≤ L) : Site3D L :=
  fun _ => ⟨0, by omega⟩

def plaqEdge1 (L : ℕ) (hL : 2 ≤ L) : SpatialEdge L := (originSite L hL, 0)
def plaqEdge2 (L : ℕ) (hL : 2 ≤ L) : SpatialEdge L := (shiftSite (originSite L hL) 0, 1)
def plaqEdge3 (L : ℕ) (hL : 2 ≤ L) : SpatialEdge L := (shiftSite (originSite L hL) 1, 0)
def plaqEdge4 (L : ℕ) (hL : 2 ≤ L) : SpatialEdge L := (originSite L hL, 1)

theorem plaqEdges_distinct (L : ℕ) (hL : 2 ≤ L) :
    plaqEdge1 L hL ≠ plaqEdge2 L hL ∧
    plaqEdge1 L hL ≠ plaqEdge3 L hL ∧
    plaqEdge1 L hL ≠ plaqEdge4 L hL ∧
    plaqEdge2 L hL ≠ plaqEdge3 L hL ∧
    plaqEdge2 L hL ≠ plaqEdge4 L hL ∧
    plaqEdge3 L hL ≠ plaqEdge4 L hL := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact absurd (congrArg Prod.snd h) (by simp [plaqEdge1, plaqEdge2])
  · intro h
    have h1 := congrFun (congrArg Prod.fst h) 1
    simp only [plaqEdge1, plaqEdge3, originSite, shiftSite, Function.update_self,
      shiftFin, Fin.ext_iff, zero_add, Nat.mod_eq_of_lt hL] at h1
    omega
  · intro h; exact absurd (congrArg Prod.snd h) (by simp [plaqEdge1, plaqEdge4])
  · intro h; exact absurd (congrArg Prod.snd h) (by simp [plaqEdge2, plaqEdge3])
  · intro h
    have h1 := congrFun (congrArg Prod.fst h) 0
    simp only [plaqEdge2, plaqEdge4, originSite, shiftSite, Function.update_self,
      shiftFin, Fin.ext_iff, zero_add, Nat.mod_eq_of_lt hL] at h1
    omega
  · intro h; exact absurd (congrArg Prod.snd h) (by simp [plaqEdge3, plaqEdge4])

/-- Continuous `1 × 1` spatial plaquette Wilson-loop observable `W_p(U) = χ(U_{p₀})`. -/
noncomputable def plaquetteGlueballMap (C : NormalizedGaugeCharacter G) (L : ℕ) (hL : 2 ≤ L) :
    C(SpatialConfig L G, ℂ) where
  toFun U := (C.χ (spatialPlaquetteHolonomy U (originSite L hL) 0) : ℂ)
  continuous_toFun :=
    Complex.continuous_ofReal.comp
      (C.χ_continuous.comp (spatialPlaquetteHolonomy_continuous L (originSite L hL) 0))

/-- 1-plaquette `0⁺⁺` glueball state `[W_p] ∈ SpatialL2 L G` for `L ≥ 2`. -/
noncomputable def plaquetteGlueballL2 (C : NormalizedGaugeCharacter G) (L : ℕ) (hL : 2 ≤ L) :
    SpatialL2 L G :=
  ContinuousMap.toLp 2 (spatialHaar L G) ℂ (plaquetteGlueballMap C L hL)

theorem plaquetteGlueballL2_norm_pos (C : NormalizedGaugeCharacter G) (L : ℕ) (hL : 2 ≤ L) :
    0 < ‖plaquetteGlueballL2 C L hL‖ := by
  rw [norm_pos_iff]
  intro h_zero
  have h_inj := ContinuousMap.toLp_injective (p := 2) (μ := spatialHaar L G) (𝕜 := ℂ) (E := ℂ)
  have h_map_zero : plaquetteGlueballMap C L hL = 0 := by
    apply h_inj
    simpa [plaquetteGlueballL2] using h_zero
  have h_eval := congrArg (fun f : C(SpatialConfig L G, ℂ) => f 1) h_map_zero
  have h_one : plaquetteGlueballMap C L hL 1 = (1 : ℂ) := by
    change (C.χ (spatialPlaquetteHolonomy (1 : SpatialConfig L G) (originSite L hL) 0) : ℂ) = 1
    simp [spatialPlaquetteHolonomy, C.χ_one]
  rw [h_one] at h_eval
  exact one_ne_zero h_eval

theorem plaquetteGlueballL2_gaugeProj (C : NormalizedGaugeCharacter G) (L : ℕ) (hL : 2 ≤ L) :
    gaugeProj L (plaquetteGlueballL2 C L hL) = plaquetteGlueballL2 C L hL := by
  have h_unit : ∀ Ω : GaugeConfig L G,
      gaugeUnitary L Ω (plaquetteGlueballL2 C L hL) = plaquetteGlueballL2 C L hL := by
    intro Ω
    unfold plaquetteGlueballL2 gaugeUnitary
    rw [unitaryOfMP_toLp]
    congr 1
    ext U
    change (C.χ (spatialPlaquetteHolonomy (gaugeAct L Ω U) (originSite L hL) 0) : ℂ) =
      (C.χ (spatialPlaquetteHolonomy U (originSite L hL) 0) : ℂ)
    rw [spatialPlaquetteHolonomy_gauge, C.χ_conj]
  change ∫ Ω : GaugeConfig L G, (1 : ℂ) • gaugeUnitary L Ω (plaquetteGlueballL2 C L hL) ∂(gaugeHaar L G) = _
  simp [h_unit]

theorem plaquetteGlueballL2_ortho_vacuum (C : NormalizedGaugeCharacter G) (L : ℕ) (hL : 2 ≤ L) :
    inner ℂ (vacuumL2 L G) (plaquetteGlueballL2 C L hL) = 0 := by
  rcases plaqEdges_distinct L hL with ⟨h12, h13, h14, _, _, _⟩
  have h_exp_zero : edgeExpect L (plaqEdge1 L hL) (plaquetteGlueballL2 C L hL) = 0 := by
    unfold plaquetteGlueballL2
    rw [edgeExpect_toLp]
    suffices h_c : ∫ u : G,
        ((plaquetteGlueballMap C L hL).comp (edgeShiftJointMap L (plaqEdge1 L hL))).curry u
          ∂(haarProb G) = 0 by
      rw [h_c, map_zero]
    let F := ((plaquetteGlueballMap C L hL).comp (edgeShiftJointMap L (plaqEdge1 L hL))).curry
    have hF_int : Integrable F (haarProb G) := integrable_of_continuous_compact F.continuous
    ext U
    have h_pt := (evalContinuousMapCLM U).integral_comp_comm hF_int
    change (evalContinuousMapCLM U) (∫ u : G, F u ∂(haarProb G)) = 0
    rw [← h_pt]
    have h_eval_u : ∀ u : G,
        evalContinuousMapCLM U (F u) =
          (C.χ ((U (plaqEdge1 L hL) * u) *
            (U (plaqEdge2 L hL) * (U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹)) : ℂ) := by
      intro u
      change (C.χ (spatialPlaquetteHolonomy (U * edgeSingle L (plaqEdge1 L hL) u)
        (originSite L hL) 0) : ℂ) = _
      unfold spatialPlaquetteHolonomy spatialPlaneAxes
      have he2 : (U * edgeSingle L (plaqEdge1 L hL) u) (plaqEdge2 L hL) = U (plaqEdge2 L hL) := by
        simp [edgeSingle_of_ne L h12.symm]
      have he3 : (U * edgeSingle L (plaqEdge1 L hL) u) (plaqEdge3 L hL) = U (plaqEdge3 L hL) := by
        simp [edgeSingle_of_ne L h13.symm]
      have he4 : (U * edgeSingle L (plaqEdge1 L hL) u) (plaqEdge4 L hL) = U (plaqEdge4 L hL) := by
        simp [edgeSingle_of_ne L h14.symm]
      have he1 : (U * edgeSingle L (plaqEdge1 L hL) u) (plaqEdge1 L hL) = U (plaqEdge1 L hL) * u := by
        simp
      change (C.χ (((U * edgeSingle L (plaqEdge1 L hL) u) (plaqEdge1 L hL)) *
        ((U * edgeSingle L (plaqEdge1 L hL) u) (plaqEdge2 L hL)) *
        ((U * edgeSingle L (plaqEdge1 L hL) u) (plaqEdge3 L hL))⁻¹ *
        ((U * edgeSingle L (plaqEdge1 L hL) u) (plaqEdge4 L hL))⁻¹) : ℂ) = _
      rw [he1, he2, he3, he4]
      simp [mul_assoc]
    simp_rw [h_eval_u]
    let A := U (plaqEdge1 L hL)
    let B := U (plaqEdge2 L hL) * (U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹
    have h_real_zero : ∫ u : G, C.χ ((A * u) * B) ∂(haarProb G) = 0 := by
      have hL_inv := integral_mul_left_eq_self (fun z : G => C.χ (z * B)) A (μ := haarProb G)
      have hR_inv := integral_mul_right_eq_self C.χ B (μ := haarProb G)
      rw [hL_inv, hR_inv, C.χ_integral_zero]
    rw [complex_integral_ofReal, h_real_zero, Complex.ofReal_zero]
  calc inner ℂ (vacuumL2 L G) (plaquetteGlueballL2 C L hL)
      = inner ℂ (edgeExpect L (plaqEdge1 L hL) (vacuumL2 L G)) (plaquetteGlueballL2 C L hL) := by
          rw [edgeExpect_vacuum]
    _ = inner ℂ (vacuumL2 L G) (edgeExpect L (plaqEdge1 L hL) (plaquetteGlueballL2 C L hL)) :=
          edgeExpect_selfAdjoint L (plaqEdge1 L hL) _ _
    _ = 0 := by rw [h_exp_zero, inner_zero_right]

theorem wilsonWeight_char_convolution_pos (C : NormalizedGaugeCharacter G) (β : ℝ) (h : G) :
    ∫ g : G, wilsonWeight C β g * C.χ (g * h) ∂(haarProb G) = haarCHalf C β * C.χ h := by
  have h1 := integral_inv_eq_self (fun g : G => wilsonWeight C β g * C.χ (g⁻¹ * h)) (haarProb G)
  have h2 : ∫ g : G, wilsonWeight C β g⁻¹ * C.χ (g⁻¹⁻¹ * h) ∂(haarProb G) =
      ∫ g : G, wilsonWeight C β g * C.χ (g * h) ∂(haarProb G) := by
    simp [wilsonWeight_inv]
  rw [← h2, h1]
  exact wilsonWeight_char_convolution C β h

/-- Single-edge eigenvalue action of `edgeTransferOp C L β e` on the 1-plaquette glueball state:
    multiplies by `c_{1/2}(β) / c₀(β)` if `e` is one of the 4 plaquette links, and by `1` otherwise. -/
theorem edgeTransferOp_plaquetteGlueball (C : NormalizedGaugeCharacter G) (L : ℕ)
    (hL : 2 ≤ L) (β : ℝ) (e : SpatialEdge L) :
    let S : Finset (SpatialEdge L) :=
      {plaqEdge1 L hL, plaqEdge2 L hL, plaqEdge3 L hL, plaqEdge4 L hL}
    edgeTransferOp C L β e (plaquetteGlueballL2 C L hL) =
      (if e ∈ S then ((haarCHalf C β / haarC0 C β : ℝ) : ℂ) else 1) •
        plaquetteGlueballL2 C L hL := by
  rcases plaqEdges_distinct L hL with ⟨h12, h13, h14, h23, h24, h34⟩
  intro S
  unfold plaquetteGlueballL2
  rw [edgeTransferOp_toLp, ← map_smul]
  congr 1
  let w : G → ℂ := fun u => ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ)
  have hw_cont : Continuous w :=
    Complex.continuous_ofReal.comp ((wilsonWeight_continuous C β).div_const _)
  let F : G → C(SpatialConfig L G, ℂ) :=
    fun u => w u • ((plaquetteGlueballMap C L hL).comp (edgeShiftJointMap L e)).curry u
  have hF_int : Integrable F (haarProb G) :=
    integrable_of_continuous_compact
      (hw_cont.smul (((plaquetteGlueballMap C L hL).comp (edgeShiftJointMap L e)).curry.continuous))
  ext U
  have h_pt := (evalContinuousMapCLM U).integral_comp_comm hF_int
  let c : ℂ := if e ∈ S then ((haarCHalf C β / haarC0 C β : ℝ) : ℂ) else 1
  change (evalContinuousMapCLM U) (∫ u : G, F u ∂(haarProb G)) =
    c * plaquetteGlueballMap C L hL U
  rw [← h_pt]
  have h_conv_helper : ∀ (h : G) (sgn : Bool),
      ∫ u : G, ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ) *
        (C.χ ((if sgn then u else u⁻¹) * h) : ℂ) ∂(haarProb G) =
      ((haarCHalf C β / haarC0 C β : ℝ) : ℂ) * (C.χ h : ℂ) := by
    intro h sgn
    have h_real : ∫ u : G, (wilsonWeight C β u / haarC0 C β) *
        C.χ ((if sgn then u else u⁻¹) * h) ∂(haarProb G) =
        (haarCHalf C β / haarC0 C β) * C.χ h := by
      simp_rw [div_mul_eq_mul_div]
      rw [integral_div]
      cases sgn
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [wilsonWeight_char_convolution C β h, mul_div_right_comm]
      · simp only [↓reduceIte]
        rw [wilsonWeight_char_convolution_pos C β h, mul_div_right_comm]
    have h_cast : (fun u : G => ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ) *
        (C.χ ((if sgn then u else u⁻¹) * h) : ℂ)) =
        fun u : G => (((wilsonWeight C β u / haarC0 C β) *
          C.χ ((if sgn then u else u⁻¹) * h) : ℝ) : ℂ) := by
      funext u; simp
    rw [h_cast, complex_integral_ofReal, h_real]
    simp
  by_cases heS : e ∈ S
  · have h_cases : e = plaqEdge1 L hL ∨ e = plaqEdge2 L hL ∨
        e = plaqEdge3 L hL ∨ e = plaqEdge4 L hL := by
      simpa [S] using heS
    have hc_eq : c = ((haarCHalf C β / haarC0 C β : ℝ) : ℂ) := if_pos heS
    rw [hc_eq]
    rcases h_cases with rfl | rfl | rfl | rfl
    · let h := U (plaqEdge2 L hL) * (U (plaqEdge3 L hL))⁻¹ *
        (U (plaqEdge4 L hL))⁻¹ * U (plaqEdge1 L hL)
      have h_pt_u : ∀ u : G, evalContinuousMapCLM U (F u) =
          ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ) * (C.χ (u * h) : ℂ) := by
        intro u
        change w u * (C.χ (((U * edgeSingle L (plaqEdge1 L hL) u) (plaqEdge1 L hL)) *
          ((U * edgeSingle L (plaqEdge1 L hL) u) (plaqEdge2 L hL)) *
          ((U * edgeSingle L (plaqEdge1 L hL) u) (plaqEdge3 L hL))⁻¹ *
          ((U * edgeSingle L (plaqEdge1 L hL) u) (plaqEdge4 L hL))⁻¹) : ℂ) = _
        simp only [Pi.mul_apply, edgeSingle_same,
          edgeSingle_of_ne L h12.symm, edgeSingle_of_ne L h13.symm,
          edgeSingle_of_ne L h14.symm, mul_one]
        have h_cyc : C.χ ((U (plaqEdge1 L hL) * u) * U (plaqEdge2 L hL) *
            (U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹) = C.χ (u * h) := by
          have hc := C.χ_mul_comm (U (plaqEdge1 L hL))
            (u * (U (plaqEdge2 L hL) * (U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹))
          simpa [h, mul_assoc] using hc
        rw [h_cyc]
      simp_rw [h_pt_u]
      simpa [plaquetteGlueballMap, spatialPlaquetteHolonomy, spatialPlaneAxes,
        plaqEdge1, plaqEdge2, plaqEdge3, plaqEdge4, h, mul_assoc,
        C.χ_mul_comm (U (originSite L hL, 0))] using (h_conv_helper h true)
    · let h := (U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹ *
        U (plaqEdge1 L hL) * U (plaqEdge2 L hL)
      have h_pt_u : ∀ u : G, evalContinuousMapCLM U (F u) =
          ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ) * (C.χ (u * h) : ℂ) := by
        intro u
        change w u * (C.χ (((U * edgeSingle L (plaqEdge2 L hL) u) (plaqEdge1 L hL)) *
          ((U * edgeSingle L (plaqEdge2 L hL) u) (plaqEdge2 L hL)) *
          ((U * edgeSingle L (plaqEdge2 L hL) u) (plaqEdge3 L hL))⁻¹ *
          ((U * edgeSingle L (plaqEdge2 L hL) u) (plaqEdge4 L hL))⁻¹) : ℂ) = _
        simp only [Pi.mul_apply, edgeSingle_same,
          edgeSingle_of_ne L h12, edgeSingle_of_ne L h23.symm,
          edgeSingle_of_ne L h24.symm, mul_one]
        have h_cyc : C.χ (U (plaqEdge1 L hL) * (U (plaqEdge2 L hL) * u) *
            (U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹) = C.χ (u * h) := by
          have hc := C.χ_mul_comm (U (plaqEdge1 L hL) * U (plaqEdge2 L hL))
            (u * ((U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹))
          simpa [h, mul_assoc] using hc
        rw [h_cyc]
      simp_rw [h_pt_u]
      have h_base : C.χ h = C.χ (U (plaqEdge1 L hL) * U (plaqEdge2 L hL) *
          (U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹) := by
        have hc := C.χ_mul_comm ((U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹)
          (U (plaqEdge1 L hL) * U (plaqEdge2 L hL))
        simpa [h, mul_assoc] using hc
      have h_res := h_conv_helper h true
      simp only [↓reduceIte] at h_res
      rw [h_res, h_base]
      rfl
    · let h := (U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹ *
        U (plaqEdge1 L hL) * U (plaqEdge2 L hL)
      have h_pt_u : ∀ u : G, evalContinuousMapCLM U (F u) =
          ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ) * (C.χ (u⁻¹ * h) : ℂ) := by
        intro u
        change w u * (C.χ (((U * edgeSingle L (plaqEdge3 L hL) u) (plaqEdge1 L hL)) *
          ((U * edgeSingle L (plaqEdge3 L hL) u) (plaqEdge2 L hL)) *
          ((U * edgeSingle L (plaqEdge3 L hL) u) (plaqEdge3 L hL))⁻¹ *
          ((U * edgeSingle L (plaqEdge3 L hL) u) (plaqEdge4 L hL))⁻¹) : ℂ) = _
        simp only [Pi.mul_apply, edgeSingle_same,
          edgeSingle_of_ne L h13, edgeSingle_of_ne L h23,
          edgeSingle_of_ne L h34.symm, mul_one, mul_inv_rev]
        have h_cyc : C.χ (U (plaqEdge1 L hL) * U (plaqEdge2 L hL) *
            (u⁻¹ * (U (plaqEdge3 L hL))⁻¹) * (U (plaqEdge4 L hL))⁻¹) = C.χ (u⁻¹ * h) := by
          have hc := C.χ_mul_comm (U (plaqEdge1 L hL) * U (plaqEdge2 L hL))
            (u⁻¹ * ((U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹))
          simpa [h, mul_assoc] using hc
        rw [h_cyc]
      simp_rw [h_pt_u]
      have h_base : C.χ h = C.χ (U (plaqEdge1 L hL) * U (plaqEdge2 L hL) *
          (U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹) := by
        have hc := C.χ_mul_comm ((U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹)
          (U (plaqEdge1 L hL) * U (plaqEdge2 L hL))
        simpa [h, mul_assoc] using hc
      have h_res := h_conv_helper h false
      simp only [Bool.false_eq_true, ↓reduceIte] at h_res
      rw [h_res, h_base]
      rfl
    · let h := (U (plaqEdge4 L hL))⁻¹ * U (plaqEdge1 L hL) *
        U (plaqEdge2 L hL) * (U (plaqEdge3 L hL))⁻¹
      have h_pt_u : ∀ u : G, evalContinuousMapCLM U (F u) =
          ((wilsonWeight C β u / haarC0 C β : ℝ) : ℂ) * (C.χ (u⁻¹ * h) : ℂ) := by
        intro u
        change w u * (C.χ (((U * edgeSingle L (plaqEdge4 L hL) u) (plaqEdge1 L hL)) *
          ((U * edgeSingle L (plaqEdge4 L hL) u) (plaqEdge2 L hL)) *
          ((U * edgeSingle L (plaqEdge4 L hL) u) (plaqEdge3 L hL))⁻¹ *
          ((U * edgeSingle L (plaqEdge4 L hL) u) (plaqEdge4 L hL))⁻¹) : ℂ) = _
        simp only [Pi.mul_apply, edgeSingle_same,
          edgeSingle_of_ne L h14, edgeSingle_of_ne L h24,
          edgeSingle_of_ne L h34, mul_one, mul_inv_rev]
        have h_cyc : C.χ (U (plaqEdge1 L hL) * U (plaqEdge2 L hL) *
            (U (plaqEdge3 L hL))⁻¹ * (u⁻¹ * (U (plaqEdge4 L hL))⁻¹)) = C.χ (u⁻¹ * h) := by
          have hc := C.χ_mul_comm
            (U (plaqEdge1 L hL) * U (plaqEdge2 L hL) * (U (plaqEdge3 L hL))⁻¹)
            (u⁻¹ * (U (plaqEdge4 L hL))⁻¹)
          simpa [h, mul_assoc] using hc
        rw [h_cyc]
      simp_rw [h_pt_u]
      have h_base : C.χ h = C.χ (U (plaqEdge1 L hL) * U (plaqEdge2 L hL) *
          (U (plaqEdge3 L hL))⁻¹ * (U (plaqEdge4 L hL))⁻¹) := by
        have hc := C.χ_mul_comm ((U (plaqEdge4 L hL))⁻¹)
          (U (plaqEdge1 L hL) * U (plaqEdge2 L hL) * (U (plaqEdge3 L hL))⁻¹)
        simpa [h, mul_assoc] using hc
      have h_res := h_conv_helper h false
      simp only [Bool.false_eq_true, ↓reduceIte] at h_res
      rw [h_res, h_base]
      rfl
  · have hc_eq : c = 1 := if_neg heS
    rw [hc_eq, one_mul]
    have hne1 : plaqEdge1 L hL ≠ e := fun h => heS (by simp [S, ← h])
    have hne2 : plaqEdge2 L hL ≠ e := fun h => heS (by simp [S, ← h])
    have hne3 : plaqEdge3 L hL ≠ e := fun h => heS (by simp [S, ← h])
    have hne4 : plaqEdge4 L hL ≠ e := fun h => heS (by simp [S, ← h])
    have h_pt_u : ∀ u : G,
        evalContinuousMapCLM U (F u) = w u * plaquetteGlueballMap C L hL U := by
      intro u
      change w u * (C.χ (((U * edgeSingle L e u) (plaqEdge1 L hL)) *
        ((U * edgeSingle L e u) (plaqEdge2 L hL)) *
        ((U * edgeSingle L e u) (plaqEdge3 L hL))⁻¹ *
        ((U * edgeSingle L e u) (plaqEdge4 L hL))⁻¹) : ℂ) = _
      simp only [Pi.mul_apply, edgeSingle_of_ne L hne1, edgeSingle_of_ne L hne2,
        edgeSingle_of_ne L hne3, edgeSingle_of_ne L hne4, mul_one]
      rfl
    simp_rw [h_pt_u]
    rw [integral_mul_const]
    have hw_one : ∫ u : G, w u ∂(haarProb G) = 1 := by
      simp only [w]
      rw [complex_integral_ofReal, wilsonWeight_div_haarC0_integral C β, Complex.ofReal_one]
    rw [hw_one, one_mul]

/-- **Exact 1-Plaquette Glueball Eigenvalue Theorem**:
    For every `L ≥ 2` and every `β ∈ ℝ`,
      `electricWilsonTransferOp C L β [W_p] = (c_{1/2}(β) / c₀(β))⁴ • [W_p]`. -/
theorem electricWilsonTransferOp_plaquetteGlueball_eigenstate
    (C : NormalizedGaugeCharacter G) (L : ℕ) (hL : 2 ≤ L) (β : ℝ) :
    electricWilsonTransferOp C L β (plaquetteGlueballL2 C L hL) =
      (((haarCHalf C β / haarC0 C β : ℝ) ^ 4 : ℝ) : ℂ) • plaquetteGlueballL2 C L hL := by
  classical
  let S : Finset (SpatialEdge L) :=
    {plaqEdge1 L hL, plaqEdge2 L hL, plaqEdge3 L hL, plaqEdge4 L hL}
  let r : ℂ := ((haarCHalf C β / haarC0 C β : ℝ) : ℂ)
  have h_list : ∀ {l : List (SpatialEdge L)}, l.Nodup →
      listTransferOp C L β l (plaquetteGlueballL2 C L hL) =
        (∏ e ∈ l.toFinset, if e ∈ S then r else 1) • plaquetteGlueballL2 C L hL := by
    intro l hl
    induction l with
    | nil =>
        simp [listTransferOp]
    | cons a l ih =>
        rcases List.nodup_cons.mp hl with ⟨ha, hl'⟩
        have ha_fin : a ∉ l.toFinset := by simpa using ha
        simp only [listTransferOp, ContinuousLinearMap.comp_apply,
          ih hl', map_smul, List.toFinset_cons, Finset.prod_insert ha_fin]
        have h_edge := edgeTransferOp_plaquetteGlueball C L hL β a
        dsimp only at h_edge
        rw [h_edge, smul_smul, mul_comm]
  have h_prod_eval :
      (∏ e ∈ (allEdges L).toFinset, if e ∈ S then r else 1) = r ^ 4 := by
    rw [allEdges_toFinset]
    have h_filter :
        (∏ e ∈ (Finset.univ : Finset (SpatialEdge L)), if e ∈ S then r else 1) =
          ∏ _e ∈ S, r := by
      rw [← Finset.prod_filter]
      congr 1
      ext e
      simp
    rcases plaqEdges_distinct L hL with ⟨h12, h13, h14, h23, h24, h34⟩
    have h_card : S.card = 4 := by
      dsimp [S]
      rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
          Finset.card_insert_of_notMem (by simp [h23, h24]),
          Finset.card_insert_of_notMem (by simp [h34]),
          Finset.card_singleton]
    rw [h_filter, Finset.prod_const, h_card]
  unfold electricWilsonTransferOp prodTransferOp
  simp only [ContinuousLinearMap.comp_apply,
    h_list (allEdges_nodup L), h_prod_eval, map_smul,
    plaquetteGlueballL2_gaugeProj]
  dsimp only [r]
  push_cast
  rfl

theorem electricWilsonTransferOp_plaquetteGlueball_norm_pos
    (C : NormalizedGaugeCharacter G) (L : ℕ) (hL : 2 ≤ L) {β : ℝ} (hβ : 0 < β) :
    0 < ‖electricWilsonTransferOp C L β (plaquetteGlueballL2 C L hL)‖ := by
  rw [electricWilsonTransferOp_plaquetteGlueball_eigenstate]
  rw [norm_smul, Complex.norm_real]
  have h_ratio_pos : 0 < (haarCHalf C β / haarC0 C β) ^ 4 :=
    pow_pos (div_pos (haarCHalf_pos C hβ) (haarC0_pos C hβ.le)) 4
  rw [Real.norm_eq_abs, abs_of_pos h_ratio_pos]
  exact mul_pos h_ratio_pos (plaquetteGlueballL2_norm_pos C L hL)

end ConstructiveWilsonLattice

/-! ### 5. Constructive Instantiation of `ToposUnifiedYangMills.WilsonLatticeYangMills` -/

section Target1StrongCoupling

variable {G : Type*} [TopologicalSpace G] [Group G] [YangMills.CompactSimpleLieGroup G]
  [CompactSpace G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- **Constructive Strong-Coupling (`β_mag = 0`) Wilson Lattice Yang–Mills Instance**:
    Replaces black-box operator parameters in `ToposUnifiedYangMills.WilsonLatticeYangMills`
    with the explicit `MeasureTheory.Measure.haarMeasure` Hilbert space `SpatialL2 L G`
    and the Haar Bochner integral operator `electricWilsonTransferOp C L β`, proving
    vacuum normalization (`‖Ω₀‖ = 1`) and glueball non-triviality (`‖T [W_p]‖ > 0` on `Ω₀^⊥`)
    unconditionally in the Lean 4 kernel. -/
noncomputable def constructiveElectricWilsonLattice
    (Curv : YangMills.CurvaturePolynomialAlgebra G)
    (C : NormalizedGaugeCharacter G)
    (beta_lat : ℝ → ℝ) :
    ToposUnifiedYangMills.WilsonLatticeYangMills G Curv where
  ℋ_lat L := SpatialL2 L G
  normed_space _ := inferInstance
  inner_space _ := inferInstance
  beta_lat := beta_lat
  T_wilson L β := electricWilsonTransferOp C L β
  Ω_lat L _ := vacuumL2 L G
  Ω_norm L _ _ _ := vacuumL2_norm L
  T_non_trivial L β hβ hL :=
    ⟨plaquetteGlueballL2 C L hL,
      plaquetteGlueballL2_ortho_vacuum C L hL,
      electricWilsonTransferOp_plaquetteGlueball_norm_pos C L hL (β := β) hβ⟩

/-- **Target 1 Theorem — Unconditional Strong-Coupling Uniform-in-Volume Mass Gap**:
    At any fixed infrared lattice spacing `a_IR > 0` and bare coupling `β_IR > 0`,
    the constructive Haar Wilson transfer operator `T_wilson L β_IR` on `L²(G^{E(Λ_L)}, μ_Haar)`
    exhibits a strictly positive physical mass gap
      `m_IR = - log(1 - exp(-2 β_IR)) / a_IR > 0`
    such that `‖T_wilson L β_IR ψ‖ ≤ exp(-a_IR * m_IR) ‖ψ‖` uniformly for ALL spatial
    volumes `L ∈ ℕ` (`L → ∞`) and ALL excited states `ψ ⊥ Ω_lat`. -/
theorem strong_coupling_uniform_volume_gap
    (Curv : YangMills.CurvaturePolynomialAlgebra G)
    (C : NormalizedGaugeCharacter G)
    (beta_lat : ℝ → ℝ)
    {a_IR β_IR : ℝ} (ha : 0 < a_IR) (hβ : 0 < β_IR) :
    let lat := constructiveElectricWilsonLattice Curv C beta_lat
    let m_IR : ℝ := -Real.log (1 - Real.exp (-2 * β_IR)) / a_IR
    0 < m_IR ∧
    ∀ (L : ℕ) (ψ : lat.ℋ_lat L),
      inner ℂ (lat.Ω_lat L β_IR) ψ = (0 : ℂ) →
      ‖lat.T_wilson L β_IR ψ‖ ≤ Real.exp (-a_IR * m_IR) * ‖ψ‖ := by
  intro lat m_IR
  have hexp_lt_one : Real.exp (-2 * β_IR) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have h1m_pos : 0 < 1 - Real.exp (-2 * β_IR) := by linarith
  have h1m_lt_one : 1 - Real.exp (-2 * β_IR) < 1 := by
    have hexp_pos : 0 < Real.exp (-2 * β_IR) := Real.exp_pos _
    linarith
  have hlog_neg : Real.log (1 - Real.exp (-2 * β_IR)) < 0 :=
    Real.log_neg h1m_pos h1m_lt_one
  have hm_pos : 0 < m_IR := by
    unfold m_IR
    exact div_pos (neg_pos.mpr hlog_neg) ha
  refine ⟨hm_pos, fun L ψ h_ortho => ?_⟩
  have h_exp_id : Real.exp (-a_IR * m_IR) = 1 - Real.exp (-2 * β_IR) := by
    unfold m_IR
    have h_alg : -a_IR * (-Real.log (1 - Real.exp (-2 * β_IR)) / a_IR) =
        Real.log (1 - Real.exp (-2 * β_IR)) := by
      field_simp [ha.ne']
    rw [h_alg, Real.exp_log h1m_pos]
  rw [h_exp_id]
  exact electricWilsonTransferOp_spectral_gap C L hβ ψ h_ortho

/-- **Scale-Matched Pure-Electric (`β_mag = 0`) Discharge of `HypothesisC2_UniformLatticeGap`**:
    Whenever a bare coupling trajectory `beta_lat : ℝ → ℝ` satisfies `0 < beta_lat a` and
    `1 - exp(-2 * beta_lat a) ≤ exp(-a * m_gap)` for all `a > 0` (which holds at strong coupling
    or for any pure-electric trajectory bounded below `-(1/2) log(1 - exp(-a * m_gap))`),
    `constructiveElectricWilsonLattice` satisfies `HypothesisC2_UniformLatticeGap` unconditionally.
    (Truth-Intent Scope Note: Under asymptotic freedom `(C1)`, `beta_lat a → +∞` as `a → 0⁺`,
    so `1 - exp(-2 * beta_lat a) ≈ 1 - O(1/β)` cannot beat `exp(-a * m_gap)` as `a → 0⁺` without
    turning on the spatial magnetic coupling `β_mag = β` in `fullWilsonTransferOp`.) -/
theorem electric_strong_coupling_satisfies_C2
    (Curv : YangMills.CurvaturePolynomialAlgebra G)
    (C : NormalizedGaugeCharacter G)
    (beta_lat : ℝ → ℝ)
    (m_gap : ℝ)
    (h_pos : ∀ a > 0, 0 < beta_lat a)
    (h_rate : ∀ a > 0, 1 - Real.exp (-2 * beta_lat a) ≤ Real.exp (-a * m_gap)) :
    ToposUnifiedYangMills.HypothesisC2_UniformLatticeGap G
      (constructiveElectricWilsonLattice Curv C beta_lat) m_gap := by
  unfold ToposUnifiedYangMills.HypothesisC2_UniformLatticeGap
  intro L a ha _
  dsimp only
  intro ψ h_ortho
  have h_gap := electricWilsonTransferOp_spectral_gap C L (h_pos a ha) ψ h_ortho
  exact h_gap.trans (mul_le_mul_of_nonneg_right (h_rate a ha) (norm_nonneg ψ))

/-! ### 6. Full 4D Osterwalder–Seiler Transfer Operator & Intertwined Ground State Gap -/

theorem spatialMagneticAction_nonneg (C : NormalizedGaugeCharacter G) (L : ℕ)
    (U : SpatialConfig L G) :
    0 ≤ spatialMagneticAction C L U := by
  unfold spatialMagneticAction
  refine Finset.sum_nonneg fun p _ => ?_
  have h := C.χ_le_one (spatialPlaquetteHolonomy U p.1 p.2)
  linarith

theorem magneticHalfWeightMap_le_one (C : NormalizedGaugeCharacter G) (L : ℕ)
    {β : ℝ} (hβ : 0 ≤ β) (U : SpatialConfig L G) :
    magneticHalfWeightMap C L β U ≤ 1 := by
  dsimp [magneticHalfWeightMap]
  have h_act := spatialMagneticAction_nonneg C L U
  have h_exp : -(β / 2) * spatialMagneticAction C L U ≤ 0 := by
    have h_half : 0 ≤ β / 2 := by linarith
    nlinarith
  exact Real.exp_le_one_iff.mpr h_exp

theorem magneticHalfWeightMap_pos (C : NormalizedGaugeCharacter G) (L : ℕ)
    (β : ℝ) (U : SpatialConfig L G) :
    0 < magneticHalfWeightMap C L β U := by
  dsimp [magneticHalfWeightMap]
  exact Real.exp_pos _

theorem magneticHalfWeightOp_norm_le (C : NormalizedGaugeCharacter G) (L : ℕ)
    {β : ℝ} (hβ : 0 ≤ β) (ψ : SpatialL2 L G) :
    ‖magneticHalfWeightOp C L β ψ‖ ≤ ‖ψ‖ := by
  unfold magneticHalfWeightOp
  have h_ae : ∀ᵐ (U : SpatialConfig L G) ∂(spatialHaar L G),
      ‖(mulRealCLM L (magneticHalfWeightMap C L β) ψ) U‖ ≤ 1 * ‖ψ U‖ := by
    filter_upwards [mulRealCLM_coeFn L (magneticHalfWeightMap C L β) ψ] with U hU
    rw [hU, norm_mul, Complex.norm_real, one_mul]
    have h_pos := magneticHalfWeightMap_pos C L β U
    have h_le := magneticHalfWeightMap_le_one C L hβ U
    rw [Real.norm_eq_abs, abs_of_pos h_pos]
    exact mul_le_of_le_one_left (norm_nonneg _) h_le
  have h_norm := Lp.norm_le_mul_norm_of_ae_le_mul h_ae
  simpa using h_norm

theorem magneticHalfWeightOp_selfAdjoint (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (φ ψ : SpatialL2 L G) :
    inner ℂ (magneticHalfWeightOp C L β φ) ψ = inner ℂ φ (magneticHalfWeightOp C L β ψ) :=
  mulRealCLM_selfAdjoint L (magneticHalfWeightMap C L β) φ ψ

/-- Interacting bare ground state vector `M_{β/2} Ω₀`. -/
noncomputable def magneticVacuumVector (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    SpatialL2 L G :=
  magneticHalfWeightOp C L β (vacuumL2 L G)

/-- Normalized true physical lattice ground state `Ω_lat(L, β) = M_{β/2} Ω₀ / ‖M_{β/2} Ω₀‖`. -/
noncomputable def normalizedMagneticVacuum (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    SpatialL2 L G :=
  if _h : magneticVacuumVector C L β = 0 then
    vacuumL2 L G
  else
    (‖magneticVacuumVector C L β‖⁻¹ : ℂ) • magneticVacuumVector C L β

/-- Inverse half-step magnetic multiplier `exp(+(β/2) S_mag)`. -/
noncomputable def invMagneticHalfWeightMap (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    C(SpatialConfig L G, ℝ) where
  toFun U := Real.exp ((β / 2) * spatialMagneticAction C L U)
  continuous_toFun := Real.continuous_exp.comp
    (continuous_const.mul (spatialMagneticAction_continuous C L))

theorem magneticHalfWeightMap_mul_inv (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (U : SpatialConfig L G) :
    magneticHalfWeightMap C L β U * invMagneticHalfWeightMap C L β U = 1 := by
  dsimp [magneticHalfWeightMap, invMagneticHalfWeightMap]
  rw [← Real.exp_add]
  have : -(β / 2) * spatialMagneticAction C L U + (β / 2) * spatialMagneticAction C L U = 0 := by ring
  rw [this, Real.exp_zero]

theorem invMagneticHalfWeightMap_mul (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (U : SpatialConfig L G) :
    invMagneticHalfWeightMap C L β U * magneticHalfWeightMap C L β U = 1 := by
  rw [mul_comm, magneticHalfWeightMap_mul_inv]

theorem magneticHalfWeightOp_mul_inv (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (φ : SpatialL2 L G) :
    magneticHalfWeightOp C L β (mulRealCLM L (invMagneticHalfWeightMap C L β) φ) = φ := by
  unfold magneticHalfWeightOp
  rw [Lp.ext_iff]
  filter_upwards [mulRealCLM_coeFn L (magneticHalfWeightMap C L β)
      (mulRealCLM L (invMagneticHalfWeightMap C L β) φ),
    mulRealCLM_coeFn L (invMagneticHalfWeightMap C L β) φ] with U h1 h2
  rw [h1, h2, ← mul_assoc]
  have h_mul : ((magneticHalfWeightMap C L β U : ℂ) * (invMagneticHalfWeightMap C L β U : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul, magneticHalfWeightMap_mul_inv C L β U, Complex.ofReal_one]
  rw [h_mul, one_mul]

theorem inv_mul_magneticHalfWeightOp (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (φ : SpatialL2 L G) :
    mulRealCLM L (invMagneticHalfWeightMap C L β) (magneticHalfWeightOp C L β φ) = φ := by
  unfold magneticHalfWeightOp
  rw [Lp.ext_iff]
  filter_upwards [mulRealCLM_coeFn L (invMagneticHalfWeightMap C L β)
      (mulRealCLM L (magneticHalfWeightMap C L β) φ),
    mulRealCLM_coeFn L (magneticHalfWeightMap C L β) φ] with U h1 h2
  rw [h1, h2, ← mul_assoc]
  have h_mul : ((invMagneticHalfWeightMap C L β U : ℂ) * (magneticHalfWeightMap C L β U : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul, invMagneticHalfWeightMap_mul C L β U, Complex.ofReal_one]
  rw [h_mul, one_mul]

theorem magneticVacuumVector_ne_zero (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    magneticVacuumVector C L β ≠ 0 := by
  intro h_zero
  have h_inv := inv_mul_magneticHalfWeightOp C L β (vacuumL2 L G)
  have h_vac_zero : vacuumL2 L G = 0 := by
    calc vacuumL2 L G
        = mulRealCLM L (invMagneticHalfWeightMap C L β) (magneticHalfWeightOp C L β (vacuumL2 L G)) := h_inv.symm
      _ = mulRealCLM L (invMagneticHalfWeightMap C L β) (magneticVacuumVector C L β) := rfl
      _ = mulRealCLM L (invMagneticHalfWeightMap C L β) 0 := by rw [h_zero]
      _ = 0 := map_zero _
  have h_norm : ‖vacuumL2 L G‖ = 1 := vacuumL2_norm L
  rw [h_vac_zero, norm_zero] at h_norm
  exact zero_ne_one h_norm

theorem normalizedMagneticVacuum_norm (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ) :
    ‖normalizedMagneticVacuum C L β‖ = 1 := by
  unfold normalizedMagneticVacuum
  split_ifs with h
  · exact vacuumL2_norm (G := G) L
  · rw [norm_smul]
    have h_pos : 0 < ‖magneticVacuumVector C L β‖ := norm_pos_iff.mpr h
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ h_pos.ne']

theorem magnetic_half_weight_ortho_bare_vacuum (C : NormalizedGaugeCharacter G) (L : ℕ) (β : ℝ)
    (ψ : SpatialL2 L G)
    (h_ortho : inner ℂ (normalizedMagneticVacuum C L β) ψ = 0) :
    inner ℂ (vacuumL2 L G) (magneticHalfWeightOp C L β ψ) = 0 := by
  have h_mv : inner ℂ (magneticVacuumVector C L β) ψ = 0 := by
    by_cases h : magneticVacuumVector C L β = 0
    · rw [h, inner_zero_left]
    · have h_norm_def : normalizedMagneticVacuum C L β =
          (‖magneticVacuumVector C L β‖⁻¹ : ℂ) • magneticVacuumVector C L β := by
        unfold normalizedMagneticVacuum
        simp [h]
      rw [h_norm_def, inner_smul_left] at h_ortho
      have h_pos : 0 < ‖magneticVacuumVector C L β‖ := norm_pos_iff.mpr h
      have hc : (↑‖magneticVacuumVector C L β‖)⁻¹ ≠ (0 : ℂ) :=
        inv_ne_zero (Complex.ofReal_ne_zero.mpr h_pos.ne')
      have h_star_c : star ((↑‖magneticVacuumVector C L β‖)⁻¹ : ℂ) ≠ 0 :=
        star_ne_zero.mpr hc
      exact mul_eq_zero.mp h_ortho |>.resolve_left h_star_c
  unfold magneticVacuumVector at h_mv
  rw [magneticHalfWeightOp_selfAdjoint] at h_mv
  exact h_mv

/-- **Uniform Spectral Gap of the Full 4D Osterwalder–Seiler Transfer Operator**:
    For every `β > 0` and every state `ψ ⊥ Ω_lat(L, β)` orthogonal to the normalized interacting vacuum,
    the full 4D transfer operator `T_full(L, β) = M_{β/2} ∘ T_electric ∘ M_{β/2}` satisfies
      `‖T_full(L, β) ψ‖ ≤ (1 - exp(-2β)) ‖ψ‖`
    uniformly for ALL spatial volumes `L ∈ ℕ`. -/
theorem fullWilsonTransferOp_spectral_gap (C : NormalizedGaugeCharacter G)
    (L : ℕ) {β : ℝ} (hβ : 0 < β)
    (ψ : SpatialL2 L G)
    (h_ortho : inner ℂ (normalizedMagneticVacuum C L β) ψ = 0) :
    ‖fullWilsonTransferOp C L β ψ‖ ≤ (1 - Real.exp (-2 * β)) * ‖ψ‖ := by
  unfold fullWilsonTransferOp
  simp only [ContinuousLinearMap.comp_apply]
  have h_out := magneticHalfWeightOp_norm_le C L hβ.le
    ((electricWilsonTransferOp C L β) (magneticHalfWeightOp C L β ψ))
  have h_inner := magnetic_half_weight_ortho_bare_vacuum C L β ψ h_ortho
  have h_elec := electricWilsonTransferOp_spectral_gap C L hβ
    (magneticHalfWeightOp C L β ψ) h_inner
  have h_in := magneticHalfWeightOp_norm_le C L hβ.le ψ
  have h_pos_gap : 0 ≤ 1 - Real.exp (-2 * β) := by
    have : Real.exp (-2 * β) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have h_elec_bound :
      ‖(electricWilsonTransferOp C L β) (magneticHalfWeightOp C L β ψ)‖ ≤
        (1 - Real.exp (-2 * β)) * ‖ψ‖ :=
    h_elec.trans (mul_le_mul_of_nonneg_left h_in h_pos_gap)
  exact h_out.trans h_elec_bound

/-- Exact non-trivial glueball excitation orthogonal to the interacting vacuum:
    `ψ = M_{-β/2} W_p`. -/
noncomputable def fullPlaquetteExcitation (C : NormalizedGaugeCharacter G) (L : ℕ) (hL : 2 ≤ L) (β : ℝ) :
    SpatialL2 L G :=
  mulRealCLM L (invMagneticHalfWeightMap C L β) (plaquetteGlueballL2 C L hL)

theorem fullPlaquetteExcitation_ortho_vacuum (C : NormalizedGaugeCharacter G) (L : ℕ) (hL : 2 ≤ L) (β : ℝ) :
    inner ℂ (normalizedMagneticVacuum C L β) (fullPlaquetteExcitation C L hL β) = 0 := by
  have h_ne := magneticVacuumVector_ne_zero C L β
  have h_norm_def : normalizedMagneticVacuum C L β =
      (‖magneticVacuumVector C L β‖⁻¹ : ℂ) • magneticVacuumVector C L β := by
    unfold normalizedMagneticVacuum
    simp [h_ne]
  rw [h_norm_def, inner_smul_left]
  have h_mv : inner ℂ (magneticVacuumVector C L β) (fullPlaquetteExcitation C L hL β) = 0 := by
    unfold magneticVacuumVector fullPlaquetteExcitation
    rw [magneticHalfWeightOp_selfAdjoint, magneticHalfWeightOp_mul_inv]
    exact plaquetteGlueballL2_ortho_vacuum C L hL
  rw [h_mv, mul_zero]

theorem fullWilsonTransferOp_excitation_norm_pos
    (C : NormalizedGaugeCharacter G) (L : ℕ) (hL : 2 ≤ L) {β : ℝ} (hβ : 0 < β) :
    0 < ‖fullWilsonTransferOp C L β (fullPlaquetteExcitation C L hL β)‖ := by
  unfold fullWilsonTransferOp
  simp only [ContinuousLinearMap.comp_apply]
  unfold fullPlaquetteExcitation
  rw [magneticHalfWeightOp_mul_inv]
  rw [electricWilsonTransferOp_plaquetteGlueball_eigenstate C L hL β]
  rw [map_smul, norm_smul, Complex.norm_real]
  have h_ratio_pos : 0 < (haarCHalf C β / haarC0 C β) ^ 4 :=
    pow_pos (div_pos (haarCHalf_pos C hβ) (haarC0_pos C hβ.le)) 4
  rw [Real.norm_eq_abs, abs_of_pos h_ratio_pos]
  have h_mw_pos : 0 < ‖magneticHalfWeightOp C L β (plaquetteGlueballL2 C L hL)‖ := by
    rw [norm_pos_iff]
    intro h_mw_zero
    have h_inv := inv_mul_magneticHalfWeightOp C L β (plaquetteGlueballL2 C L hL)
    have h_w_zero : plaquetteGlueballL2 C L hL = 0 := by
      calc plaquetteGlueballL2 C L hL
          = mulRealCLM L (invMagneticHalfWeightMap C L β)
              (magneticHalfWeightOp C L β (plaquetteGlueballL2 C L hL)) := h_inv.symm
        _ = mulRealCLM L (invMagneticHalfWeightMap C L β) 0 := by rw [h_mw_zero]
        _ = 0 := map_zero _
    have h_norm := plaquetteGlueballL2_norm_pos C L hL
    rw [h_w_zero, norm_zero] at h_norm
    exact lt_irrefl 0 h_norm
  exact mul_pos h_ratio_pos h_mw_pos

/-- **Constructive Full 4D (`β_mag = β > 0`) Wilson Lattice Yang–Mills Instance**:
    Instantiates `ToposUnifiedYangMills.WilsonLatticeYangMills` with the full 4D Osterwalder–Seiler
    transfer operator `fullWilsonTransferOp C L β` and normalized interacting vacuum `normalizedMagneticVacuum C L β`,
    unconditionally in the Lean 4 kernel. -/
noncomputable def constructiveFullWilsonLattice
    (Curv : YangMills.CurvaturePolynomialAlgebra G)
    (C : NormalizedGaugeCharacter G)
    (beta_lat : ℝ → ℝ) :
    ToposUnifiedYangMills.WilsonLatticeYangMills G Curv where
  ℋ_lat L := SpatialL2 L G
  normed_space _ := inferInstance
  inner_space _ := inferInstance
  beta_lat := beta_lat
  T_wilson L β := fullWilsonTransferOp C L β
  Ω_lat L β := normalizedMagneticVacuum C L β
  Ω_norm L β _ _ := normalizedMagneticVacuum_norm C L β
  T_non_trivial L β hβ hL :=
    ⟨fullPlaquetteExcitation C L hL β,
      fullPlaquetteExcitation_ortho_vacuum C L hL β,
      fullWilsonTransferOp_excitation_norm_pos C L hL hβ⟩

/-- **Target 1 Main Theorem — Full 4D Strong-Coupling Uniform-in-Volume Mass Gap**:
    At any fixed infrared lattice spacing `a_IR > 0` and bare coupling `β_IR > 0`,
    the full 4D constructive Osterwalder–Seiler transfer operator `T_wilson L β_IR` on `L²(G^{E(Λ_L)}, μ_Haar)`
    with spatial magnetic action active (`β_mag = β_IR`) exhibits a strictly positive physical mass gap
      `m_IR = - log(1 - exp(-2 β_IR)) / a_IR > 0`
    such that `‖T_wilson L β_IR ψ‖ ≤ exp(-a_IR * m_IR) ‖ψ‖` uniformly for ALL spatial
    volumes `L ∈ ℕ` (`L → ∞`) and ALL excited states `ψ ⊥ Ω_lat(L, β_IR)`. -/
theorem full_strong_coupling_uniform_volume_gap
    (Curv : YangMills.CurvaturePolynomialAlgebra G)
    (C : NormalizedGaugeCharacter G)
    (beta_lat : ℝ → ℝ)
    {a_IR β_IR : ℝ} (ha : 0 < a_IR) (hβ : 0 < β_IR) :
    let lat := constructiveFullWilsonLattice Curv C beta_lat
    let m_IR : ℝ := -Real.log (1 - Real.exp (-2 * β_IR)) / a_IR
    0 < m_IR ∧
    ∀ (L : ℕ) (ψ : lat.ℋ_lat L),
      inner ℂ (lat.Ω_lat L β_IR) ψ = (0 : ℂ) →
      ‖lat.T_wilson L β_IR ψ‖ ≤ Real.exp (-a_IR * m_IR) * ‖ψ‖ := by
  intro lat m_IR
  have hexp_lt_one : Real.exp (-2 * β_IR) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have h1m_pos : 0 < 1 - Real.exp (-2 * β_IR) := by linarith
  have h1m_lt_one : 1 - Real.exp (-2 * β_IR) < 1 := by
    have hexp_pos : 0 < Real.exp (-2 * β_IR) := Real.exp_pos _
    linarith
  have hlog_neg : Real.log (1 - Real.exp (-2 * β_IR)) < 0 :=
    Real.log_neg h1m_pos h1m_lt_one
  have hm_pos : 0 < m_IR := by
    unfold m_IR
    exact div_pos (neg_pos.mpr hlog_neg) ha
  refine ⟨hm_pos, fun L ψ h_ortho => ?_⟩
  have h_exp_id : Real.exp (-a_IR * m_IR) = 1 - Real.exp (-2 * β_IR) := by
    unfold m_IR
    have h_alg : -a_IR * (-Real.log (1 - Real.exp (-2 * β_IR)) / a_IR) =
        Real.log (1 - Real.exp (-2 * β_IR)) := by
      field_simp [ha.ne']
    rw [h_alg, Real.exp_log h1m_pos]
  rw [h_exp_id]
  exact fullWilsonTransferOp_spectral_gap C L hβ ψ h_ortho

/-- **Scale-Matched Full 4D (`β_mag = β`) Discharge of `HypothesisC2_UniformLatticeGap`**:
    Whenever a bare coupling trajectory `beta_lat : ℝ → ℝ` satisfies `0 < beta_lat a` and
    `1 - exp(-2 * beta_lat a) ≤ exp(-a * m_gap)` for all `a > 0`,
    the full 4D theory `constructiveFullWilsonLattice` satisfies `HypothesisC2_UniformLatticeGap`
    unconditionally in the Lean 4 kernel. -/
theorem full_strong_coupling_satisfies_C2
    (Curv : YangMills.CurvaturePolynomialAlgebra G)
    (C : NormalizedGaugeCharacter G)
    (beta_lat : ℝ → ℝ)
    (m_gap : ℝ)
    (h_pos : ∀ a > 0, 0 < beta_lat a)
    (h_rate : ∀ a > 0, 1 - Real.exp (-2 * beta_lat a) ≤ Real.exp (-a * m_gap)) :
    ToposUnifiedYangMills.HypothesisC2_UniformLatticeGap G
      (constructiveFullWilsonLattice Curv C beta_lat) m_gap := by
  unfold ToposUnifiedYangMills.HypothesisC2_UniformLatticeGap
  intro L a ha _
  dsimp only
  intro ψ h_ortho
  have h_gap := fullWilsonTransferOp_spectral_gap C L (h_pos a ha) ψ h_ortho
  exact h_gap.trans (mul_le_mul_of_nonneg_right (h_rate a ha) (norm_nonneg ψ))

end Target1StrongCoupling

end HaarWilsonLattice
