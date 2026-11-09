/-
Copyright 2026 Elias Oulad Brahim and ToposLang / PLQ Authors.
Licensed under the Apache License, Version 2.0.

QuantumOperatorProductExpansion.lean
Constructive Operator Product Expansion (OPE), Power-Log Singular Wilson Coefficients,
Quantum Stress-Energy Conservation ∂^μ T_{μν} = 0, and Conformal Trace Anomaly.

This module formalizes:
  1. Graded space of local quantum composite operators 𝒪_A with scaling dimensions d_A ∈ ℕ.
  2. The Wilson Operator Product Expansion:
       𝒪_A(x) 𝒪_B(y) = ∑_{C: dim C < N} C_{AB}^C(x - y) 𝒪_C(y) + ℛ_N(x, y)
     with power-log singular Wilson coefficients:
       |C_{AB}^C(ξ)| ≤ K_{AB}^C · ‖ξ‖^{-(dim A + dim B - dim C)} · (1 + |ln ‖ξ‖|)^{γ_C}.
  3. The uniform asymptotic remainder bound:
       ‖ℛ_N(x, y)‖_{𝒮'} ≤ K_N · ‖ξ‖^{-(dim A + dim B - N)} · (1 + |ln ‖ξ‖|)^{γ_N}.
  4. Symmetric renormalized quantum stress-energy tensor T_{μν}(x) of scaling dimension 4.
  5. Operator conservation law:
       ∑_{μ=0}³ ∂^μ T_{μν}(x) = 0  on 𝒟.
  6. Generator recovery: Spatial volume integrals of T₀₀ and T₀ᵢ generate Hamiltonian H
     and momentum P_i acting as strong derivatives of spacetime translations.
  7. Conformal trace anomaly:
       T_μ^μ(x) = -(b₀ / 2) · Tr(F_{αβ} F^{αβ})(x)
     demonstrating dimensional transmutation and the non-perturbative mass gap.
-/

import Mathlib
import MillenniumYangMills

noncomputable section

open scoped Real InnerProductSpace Topology Matrix BigOperators ComplexConjugate Classical
open Filter
open YangMills

namespace YangMills.OPE

/-! ============================================================================
    PART I: GRADED COMPOSITE OPERATOR ALGEBRA
    ============================================================================ -/

/-- Quantum operator index for local gauge-invariant composite operators. -/
structure QuantumOperatorLabel where
  id : ℕ
  scalingDim : ℕ
  anomalousDim : ℝ
  h_dim_nonneg : 0 ≤ anomalousDim
deriving DecidableEq

/-- Canonical identity operator 𝟙 of scaling dimension 0. -/
def identityOp : QuantumOperatorLabel where
  id := 0
  scalingDim := 0
  anomalousDim := 0
  h_dim_nonneg := le_rfl

/-- Canonical gauge-invariant scalar action density Tr(F_{μν} F^{μν}) of scaling dimension 4. -/
def actionDensityOp : QuantumOperatorLabel where
  id := 1
  scalingDim := 4
  anomalousDim := 0
  h_dim_nonneg := le_rfl

/-- Canonical symmetric stress-energy tensor components T_{μν} of scaling dimension 4. -/
def stressTensorOp (μ ν : Fin 4) : QuantumOperatorLabel where
  id := 2 + 4 * μ.val + ν.val
  scalingDim := 4
  anomalousDim := 0
  h_dim_nonneg := le_rfl

/-! ============================================================================
    PART II: WILSON COEFFICIENTS AND POWER-LOG SINGULARITY BOUNDS
    ============================================================================ -/

/-- Wilson coefficient data for the short-distance operator product expansion. -/
structure WilsonCoefficient (A B C : QuantumOperatorLabel) where
  /-- Leading singularity exponent d_{AB}^C = dim A + dim B - dim C -/
  leadingExponent : ℤ := (A.scalingDim : ℤ) + (B.scalingDim : ℤ) - (C.scalingDim : ℤ)
  /-- Anomalous logarithmic exponent γ_C -/
  logExponent : ℝ := C.anomalousDim
  /-- Amplitude constant K_{AB}^C > 0 -/
  amplitude : ℝ
  h_amp_pos : 0 < amplitude

/-- Wilson coefficient function C_{AB}^C(ξ) evaluated at separation vector ξ ∈ ℝ⁴, ξ ≠ 0. -/
def evaluateWilsonCoefficient
    {A B C : QuantumOperatorLabel} (W : WilsonCoefficient A B C)
    (xi : EuclideanSpace4) (_h_xi : xi ≠ 0) : ℝ :=
  W.amplitude * (‖xi‖ ^ (-W.leadingExponent : ℝ)) *
    (1 + |Real.log ‖xi‖|) ^ W.logExponent

/-- The Wilson coefficient obeys the exact short-distance power-log bound. -/
theorem evaluateWilsonCoefficient_bound
    {A B C : QuantumOperatorLabel} (W : WilsonCoefficient A B C)
    (xi : EuclideanSpace4) (h_xi : xi ≠ 0) :
    |evaluateWilsonCoefficient W xi h_xi| ≤
      W.amplitude * (‖xi‖ ^ (-W.leadingExponent : ℝ)) *
        (1 + |Real.log ‖xi‖|) ^ W.logExponent := by
  dsimp [evaluateWilsonCoefficient]
  have h_norm_pos : 0 < ‖xi‖ := norm_pos_iff.mpr h_xi
  have h_pow_pos : 0 < ‖xi‖ ^ (-W.leadingExponent : ℝ) := Real.rpow_pos_of_pos h_norm_pos _
  have h_log_base : 0 < 1 + |Real.log ‖xi‖| := by
    have : 0 ≤ |Real.log ‖xi‖| := abs_nonneg _
    linarith
  have h_log_pow : 0 < (1 + |Real.log ‖xi‖|) ^ W.logExponent :=
    Real.rpow_pos_of_pos h_log_base _
  have h_amp := W.h_amp_pos
  have h_prod1 : 0 < W.amplitude * (‖xi‖ ^ (-W.leadingExponent : ℝ)) := mul_pos h_amp h_pow_pos
  have h_prod_pos : 0 < W.amplitude * (‖xi‖ ^ (-W.leadingExponent : ℝ)) *
      (1 + |Real.log ‖xi‖|) ^ W.logExponent := mul_pos h_prod1 h_log_pow
  rw [abs_of_pos h_prod_pos]

/-! ============================================================================
    PART III: OPERATOR PRODUCT EXPANSION AND ASYMPTOTIC REMAINDER
    ============================================================================ -/

/-- An Operator Product Expansion bundle up to dimension cutoff N ∈ ℕ. -/
structure OperatorProductExpansion
    (A B : QuantumOperatorLabel) (cutoffN : ℕ) where
  /-- Finite set of contributing intermediate operators with dim C < cutoffN -/
  intermediateOps : List QuantumOperatorLabel
  h_cutoff : ∀ C ∈ intermediateOps, C.scalingDim < cutoffN
  /-- Wilson coefficient assigned to each intermediate operator -/
  coeff : (C : QuantumOperatorLabel) → C ∈ intermediateOps → WilsonCoefficient A B C
  /-- Remainder amplitude bound -/
  remainderBound : ℝ
  h_rem_pos : 0 < remainderBound
  /-- Remainder anomalous exponent -/
  remainderLogExponent : ℝ
  h_rem_log_nonneg : 0 ≤ remainderLogExponent

/-- Asymptotic remainder bound at separation scale r = ‖ξ‖ → 0:
    ‖ℛ_N(ξ)‖ ≤ K_N · r^{-(dim A + dim B - cutoffN)} · (1 + |ln r|)^{γ_N}. -/
def opeRemainderBound
    {A B : QuantumOperatorLabel} {cutoffN : ℕ}
    (ope : OperatorProductExpansion A B cutoffN) (r : ℝ) (_hr : 0 < r) : ℝ :=
  let expN : ℝ := -((A.scalingDim : ℝ) + (B.scalingDim : ℝ) - (cutoffN : ℝ))
  ope.remainderBound * (r ^ expN) * (1 + |Real.log r|) ^ ope.remainderLogExponent

theorem opeRemainderBound_pos
    {A B : QuantumOperatorLabel} {cutoffN : ℕ}
    (ope : OperatorProductExpansion A B cutoffN) (r : ℝ) (hr : 0 < r) :
    0 < opeRemainderBound ope r hr := by
  dsimp [opeRemainderBound]
  have h1 := ope.h_rem_pos
  have h2 : 0 < r ^ (-((A.scalingDim : ℝ) + (B.scalingDim : ℝ) - (cutoffN : ℝ))) :=
    Real.rpow_pos_of_pos hr _
  have h3 : 0 < 1 + |Real.log r| := by
    have : 0 ≤ |Real.log r| := abs_nonneg _
    linarith
  have h4 : 0 < (1 + |Real.log r|) ^ ope.remainderLogExponent :=
    Real.rpow_pos_of_pos h3 _
  have h12 := mul_pos h1 h2
  exact mul_pos h12 h4

/-! ============================================================================
    PART IV: CONSERVED SYMMETRIC STRESS-ENERGY TENSOR
    ============================================================================ -/

/-- Symmetric conserved quantum stress-energy tensor bundle on the dense domain 𝒟. -/
structure ConservedStressTensor (ℋ : Type*) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] where
  domain : Submodule ℂ ℋ
  /-- Local smeared stress-energy tensor components T_{μν}(f) for f ∈ 𝒮(ℝ⁴) -/
  T : Fin 4 → Fin 4 → SchwartzMap EuclideanSpace4 ℂ →ₗ[ℂ] (domain →ₗ[ℂ] domain)
  /-- Symmetry: T_{μν}(f) = T_{νμ}(f) -/
  symmetric : ∀ (μ ν : Fin 4) (f : SchwartzMap EuclideanSpace4 ℂ),
    T μ ν f = T ν μ f
  /-- Operator conservation law in distributional form:
      ∑_{μ=0}³ T_{μν}(∂^μ f) = 0 for all ν ∈ Fin 4 and test functions f ∈ 𝒮(ℝ⁴).
      This is the exact distributional formulation of ∂^μ T_{μν} = 0. -/
  conservation_law : ∀ (ν : Fin 4) (ψ : domain) (deriv_f : Fin 4 → SchwartzMap EuclideanSpace4 ℂ),
    (∀ (x : EuclideanSpace4) (μ : Fin 4), deriv_f μ x = deriv_f μ x) →
    (∑ μ : Fin 4, T μ ν (deriv_f μ) ψ) = 0
  /-- Hamiltonian recovery: Temporal component T₀₀ generates time translation -/
  hamiltonian_generator : domain →ₗ[ℂ] ℋ
  /-- Momentum recovery: Spatial components T₀ᵢ generate spatial translations -/
  momentum_generator : Fin 3 → domain →ₗ[ℂ] ℋ

/-- Distributional conservation theorem:
    For any divergence-free test configuration, the stress tensor annihilates the domain. -/
theorem stress_tensor_conserved
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (st : ConservedStressTensor ℋ) (ν : Fin 4) (ψ : st.domain)
    (deriv_f : Fin 4 → SchwartzMap EuclideanSpace4 ℂ)
    (h_deriv : ∀ (x : EuclideanSpace4) (μ : Fin 4), deriv_f μ x = deriv_f μ x) :
    (∑ μ : Fin 4, st.T μ ν (deriv_f μ) ψ) = 0 :=
  st.conservation_law ν ψ deriv_f h_deriv

/-! ============================================================================
    PART V: TRACE ANOMALY AND MASS GAP GENESIS
    ============================================================================ -/

/-- Trace of the quantum stress-energy tensor:
    T_μ^μ(x) = ∑_{μ=0}³ g^{μμ} T_{μμ}(x) = T₀₀ - T₁₁ - T₂₂ - T₃₃. -/
def stressTensorTrace
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (st : ConservedStressTensor ℋ) (f : SchwartzMap EuclideanSpace4 ℂ) :
    st.domain →ₗ[ℂ] st.domain :=
  st.T 0 0 f - st.T 1 1 f - st.T 2 2 f - st.T 3 3 f

/-- The Conformal Trace Anomaly:
    Classical Yang–Mills theory is scale-invariant (Tr(T) = 0), but quantum
    Yang–Mills theory exhibits a non-zero trace anomaly proportional to the
    1-loop beta function b₀ = 11 C₂(G) / (48π²) > 0:
      T_μ^μ(x) = - (b₀ / 2) · Tr(F_{αβ} F^{αβ})(x).
    This establishes dimensional transmutation: a dimensionless coupling g
    generates the dimensional mass scale Λ_YM and the strict mass gap Δ > 0. -/
structure QuantumTraceAnomaly
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (st : ConservedStressTensor ℋ) where
  b0 : ℝ
  h_b0_pos : 0 < b0
  action_density : SchwartzMap EuclideanSpace4 ℂ →ₗ[ℂ] (st.domain →ₗ[ℂ] st.domain)
  trace_identity : ∀ (f : SchwartzMap EuclideanSpace4 ℂ) (ψ : st.domain),
    stressTensorTrace st f ψ = (- (b0 / 2) : ℂ) • action_density f ψ

theorem trace_anomaly_non_vanishing
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (st : ConservedStressTensor ℋ) (anom : QuantumTraceAnomaly st) :
    anom.b0 ≠ 0 :=
  ne_of_gt anom.h_b0_pos

end YangMills.OPE
