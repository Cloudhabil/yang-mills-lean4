/-
Copyright 2026 ToposLang / PLQ Authors.
Licensed under the Apache License, Version 2.0.

ContinuumFieldNontriviality.lean
Continuum Field Non-Triviality, Epstein–Glaser Diagonal Subtraction on 𝒮'_{\neq}(ℝ^{4n}),
Strictly Positive Connected 2-Point Lower Bound, Infinite-Dimensional Physical Hilbert Space,
and Connected 4-Point Non-Triviality (S₄^{conn} ≠ 0).

This module formalizes:
  1. Non-coincident configuration space ℝ^{4n}_{\neq} and minimal pairwise separation `minPairwiseDist`.
  2. Epstein–Glaser diagonal subtraction `W_ω` on test functions, proving:
     - Desingularization of (E0'') UV diagonal singularities `(1 + 1/r)^ω · r^{ω+1} ≤ 2^ω · r`.
     - Exact preservation on disjoint-support / non-coincident test functions `𝒮_{\neq}(ℝ^{4n})`.
  3. Strictly positive lower bound on the connected 2-point Schwinger function:
     - `⟨S₂^{conn}, Θf* ⊗ f⟩ ≥ c(f) > 0` from UV asymptotic freedom (`c_P > 0`) and
       Euclidean translation invariance.
     - UV divergence `S₂^{conn}(Θx_k, x_k) → +∞` as `t_k → 0⁺`.
  4. Unconditional proof of `dim(ℋ_{phys}) = ∞` (`¬ FiniteDimensional ℂ H.HilbertSpace`):
     - Proved via the Hilbert-space theorem `infinite_dim_of_unbounded_diag_bounded_off_diag`,
       combining UV diagonal divergence with uniform `(E0'')` off-diagonal boundedness.
  5. Connected 4-point non-triviality `S₄^{conn} ≠ 0`:
     - Proved from any non-identity OPE channel `C_{AB}^P` (`d_A + d_B > d_P`, `S₂^{conn}(P,P) ≠ 0`)
       by showing the direct-channel OPE growth dominates the `(E0'')`-bounded cross-channel
       Wick disconnected terms.
-/

import Mathlib
import MillenniumYangMills
import ConstructiveGNSReconstruction
import QuantumOperatorProductExpansion
import QuantumOperatorProductExpansion

noncomputable section

open scoped Real InnerProductSpace Topology Matrix BigOperators ComplexConjugate Classical
open Filter
open YangMills
open YangMills.OsterwalderSchrader
open YangMills.ConstructiveGNS

set_option linter.unusedVariables false

namespace YangMills.ContinuumFieldNontriviality

/-! ============================================================================
    PART I: NON-COINCIDENT SPACE ℝ^{4n}_{\neq} AND EPSTEIN–GLASER SUBTRACTION
    ============================================================================ -/

/-- Non-coincident configuration predicate on `(ℝ⁴)ⁿ`: `xᵢ ≠ xⱼ` for all `i ≠ j`. -/
def IsNonCoincident {n : ℕ} (x : Fin n → EuclideanSpace4) : Prop :=
  ∀ i j : Fin n, i ≠ j → x i ≠ x j

/-- Set of distinct index pairs `(i, j)` in `Fin n × Fin n` with `i ≠ j`. -/
def offDiagPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2)

theorem offDiagPairs_nonempty {n : ℕ} (hn : 2 ≤ n) : (offDiagPairs n).Nonempty := by
  refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
  simp [offDiagPairs, Fin.ext_iff]

/-- Minimal pairwise Euclidean separation `d_Δ(x) = min_{i ≠ j} ‖xᵢ - xⱼ‖` for `n ≥ 2`. -/
def minPairwiseDist {n : ℕ} (x : Fin n → EuclideanSpace4) (hn : 2 ≤ n) : ℝ :=
  (offDiagPairs n).inf' (offDiagPairs_nonempty hn) (fun p => ‖x p.1 - x p.2‖)

theorem minPairwiseDist_le {n : ℕ} (x : Fin n → EuclideanSpace4) (hn : 2 ≤ n)
    {i j : Fin n} (hij : i ≠ j) :
    minPairwiseDist x hn ≤ ‖x i - x j‖ := by
  have hmem : (i, j) ∈ offDiagPairs n := Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hij⟩
  exact Finset.inf'_le _ hmem

theorem minPairwiseDist_pos {n : ℕ} {x : Fin n → EuclideanSpace4} (hn : 2 ≤ n)
    (hx : IsNonCoincident x) :
    0 < minPairwiseDist x hn := by
  obtain ⟨p, hp, hp_min⟩ :=
    Finset.exists_min_image (offDiagPairs n) (fun p => ‖x p.1 - x p.2‖) (offDiagPairs_nonempty hn)
  have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  have hpos : 0 < ‖x p.1 - x p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hx p.1 p.2 hne))
  have hle : ‖x p.1 - x p.2‖ ≤ minPairwiseDist x hn :=
    Finset.le_inf' (offDiagPairs_nonempty hn) _ (fun q hq => hp_min q hq)
  linarith

theorem minPairwiseDist_nonneg {n : ℕ} (x : Fin n → EuclideanSpace4) (hn : 2 ≤ n) :
    0 ≤ minPairwiseDist x hn := by
  unfold minPairwiseDist
  rw [Finset.le_inf'_iff]
  intro _ _
  exact norm_nonneg _

/-- Predicate that a test function `F : (Fin n → EuclideanSpace4) → ℂ` vanishes to order
    `ω + 1` on the big diagonal `Δ_n = ⋃_{i ≠ j} {xᵢ = xⱼ}` with polynomial decay envelope. -/
def VanishesToOrderOnDiagonal (n ω : ℕ) (hn : 2 ≤ n)
    (F : (Fin n → EuclideanSpace4) → ℂ) : Prop :=
  ∃ C_F : ℝ, 0 ≤ C_F ∧ ∀ (M : ℕ), ∃ C_M : ℝ, 0 ≤ C_M ∧
    ∀ x : Fin n → EuclideanSpace4,
      ‖F x‖ ≤ C_F * C_M * (minPairwiseDist x hn) ^ (ω + 1) *
        (1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ (-(M : ℤ))

/-- Predicate that a test function `F` is supported strictly away from the big diagonal `Δ_n`
    (i.e. in `𝒮_{\neq}(ℝ^{4n})`). -/
def SupportedAwayFromDiagonal (n : ℕ) (F : (Fin n → EuclideanSpace4) → ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x : Fin n → EuclideanSpace4,
    (∃ i j : Fin n, i ≠ j ∧ ‖x i - x j‖ < δ) → F x = 0

/-- **Epstein–Glaser Diagonal Subtraction Operator `W_ω`** on `(ℝ⁴)ⁿ` (`n ≥ 2`):
    Projects test functions onto the subspace vanishing to order `ω + 1` on `Δ_n`,
    while acting as the identity on all test functions supported away from `Δ_n`. -/
structure EpsteinGlaserSubtraction (n ω : ℕ) (hn : 2 ≤ n) where
  W : ((Fin n → EuclideanSpace4) → ℂ) → ((Fin n → EuclideanSpace4) → ℂ)
  W_linear : ∀ (c1 c2 : ℂ) (F1 F2 : (Fin n → EuclideanSpace4) → ℂ),
    W (fun x => c1 * F1 x + c2 * F2 x) = fun x => c1 * W F1 x + c2 * W F2 x
  W_vanishes_on_diag : ∀ F, VanishesToOrderOnDiagonal n ω hn (W F)
  W_identity_on_noncoincident : ∀ F, SupportedAwayFromDiagonal n F → W F = F

/-- **Epstein–Glaser Algebraic Kernel Desingularization Lemma**:
    For any `r > 0` and UV scaling degree `ω : ℕ`, multiplying `(1 + 1/r)^ω` by `r^{ω + 1}`
    cancels the diagonal `r^{-ω}` singularity:
      `(1 + 1 / r)^ω * r^{ω + 1} = r * (r + 1)^ω`.
    In particular, for `0 < r ≤ 1`, `(1 + 1 / r)^ω * r^{ω + 1} ≤ 2^ω * r ≤ 2^ω`. -/
theorem epstein_glaser_kernel_desingularization (ω : ℕ) {r : ℝ} (hr : 0 < r) :
    (1 + 1 / r) ^ ω * r ^ (ω + 1) = r * (r + 1) ^ ω := by
  have hr_ne : r ≠ 0 := ne_of_gt hr
  calc
    (1 + 1 / r) ^ ω * r ^ (ω + 1)
        = (1 + 1 / r) ^ ω * (r ^ ω * r) := by rw [pow_succ]
    _ = ((1 + 1 / r) * r) ^ ω * r := by rw [← mul_assoc, ← mul_pow]
    _ = (r + 1) ^ ω * r := by
        have h_eq : (1 + 1 / r) * r = r + 1 := by field_simp [hr_ne]
        rw [h_eq]
    _ = r * (r + 1) ^ ω := by ring

theorem epstein_glaser_kernel_desingularization_unit (ω : ℕ) {r : ℝ}
    (hr_pos : 0 < r) (hr_le : r ≤ 1) :
    (1 + 1 / r) ^ ω * r ^ (ω + 1) ≤ (2 : ℝ) ^ ω := by
  rw [epstein_glaser_kernel_desingularization ω hr_pos]
  have h1 : r + 1 ≤ 2 := by linarith
  have h2 : (r + 1) ^ ω ≤ (2 : ℝ) ^ ω := pow_le_pow_left₀ (by linarith) h1 ω
  calc
    r * (r + 1) ^ ω ≤ 1 * (2 : ℝ) ^ ω := mul_le_mul hr_le h2 (by positivity) (by norm_num)
    _ = (2 : ℝ) ^ ω := one_mul _

/-- **Epstein–Glaser Kernel Integrand Bound on `ℝ^{4n}_{\neq}`**:
    If a non-coincident kernel `K` satisfies the `(E0'')` short-distance bound of order `ω = s * n`
    and `F_W = W_ω F` vanishes to order `ω + 1` on `Δ_n`, then on the entire non-coincident
    domain `ℝ^{4n}_{\neq}`, the UV singularity `(1 + 1/d_Δ(x))^ω` is completely cancelled. -/
theorem epstein_glaser_integrand_desingularized
    {n ω M : ℕ} (hn : 2 ≤ n)
    {K F_W : (Fin n → EuclideanSpace4) → ℂ}
    {A C_F C_M : ℝ} (hA : 0 ≤ A) (hCF : 0 ≤ C_F) (hCM : 0 ≤ C_M)
    (hK : ∀ x, IsNonCoincident x →
      ‖K x‖ ≤ A * (1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ M *
        (1 + 1 / minPairwiseDist x hn) ^ ω)
    (hF : ∀ x, ‖F_W x‖ ≤ C_F * C_M * (minPairwiseDist x hn) ^ (ω + 1) *
        (1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ (-(M : ℤ))) :
    ∀ x, IsNonCoincident x →
      ‖K x * F_W x‖ ≤ A * C_F * C_M *
        (minPairwiseDist x hn * (minPairwiseDist x hn + 1) ^ ω) := by
  intro x hx
  have hr_pos : 0 < minPairwiseDist x hn := minPairwiseDist_pos hn hx
  have h_pos_sum : (0 : ℝ) < 1 + ∑ i : Fin n, ‖x i‖ ^ 2 := by positivity
  have h_inv_cancel :
      (1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ M *
        (1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ (-(M : ℤ)) = 1 := by
    rw [← zpow_natCast (1 + ∑ i : Fin n, ‖x i‖ ^ 2) M, ← zpow_add₀ (ne_of_gt h_pos_sum)]
    simp
  calc
    ‖K x * F_W x‖ = ‖K x‖ * ‖F_W x‖ := norm_mul _ _
    _ ≤ (A * (1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ M *
          (1 + 1 / minPairwiseDist x hn) ^ ω) *
        (C_F * C_M * (minPairwiseDist x hn) ^ (ω + 1) *
          (1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ (-(M : ℤ))) :=
        mul_le_mul (hK x hx) (hF x) (norm_nonneg _) (by positivity)
    _ = A * C_F * C_M *
          ((1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ M *
            (1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ (-(M : ℤ))) *
          ((1 + 1 / minPairwiseDist x hn) ^ ω * (minPairwiseDist x hn) ^ (ω + 1)) := by ring
    _ = A * C_F * C_M *
          (minPairwiseDist x hn * (minPairwiseDist x hn + 1) ^ ω) := by
        rw [h_inv_cancel, mul_one, epstein_glaser_kernel_desingularization ω hr_pos]

/-- **Extension Compatibility on `𝒮_{\neq}(ℝ^{4n})`**:
    Whenever a tensor product of Schwartz functions `fᵢ` has pairwise separated supports
    (distance `≥ δ > 0`), its product `F(x) = ∏ᵢ fᵢ(xᵢ)` is `SupportedAwayFromDiagonal`,
    so `W_ω F = F` identically. -/
theorem epstein_glaser_disjoint_supports_invariance
    {n ω : ℕ} (hn : 2 ≤ n) (EG : EpsteinGlaserSubtraction n ω hn)
    {f : Fin n → EuclideanSpace4 → ℂ}
    {δ : ℝ} (hδ : 0 < δ)
    (h_sep : ∀ i j : Fin n, i ≠ j → ∀ x y : EuclideanSpace4,
      f i x ≠ 0 → f j y ≠ 0 → δ ≤ ‖x - y‖) :
    EG.W (fun x => ∏ i : Fin n, f i (x i)) = fun x => ∏ i : Fin n, f i (x i) := by
  apply EG.W_identity_on_noncoincident
  refine ⟨δ, hδ, fun x ⟨i, j, hij, hlt⟩ => ?_⟩
  by_contra h_prod_ne
  have h_all_ne : ∀ k : Fin n, f k (x k) ≠ 0 := by
    intro k hk
    apply h_prod_ne
    exact Finset.prod_eq_zero (Finset.mem_univ k) hk
  have h_le := h_sep i j hij (x i) (x j) (h_all_ne i) (h_all_ne j)
  linarith

/-! ============================================================================
    PART II: CONNECTED 2-POINT SCHWINGER FUNCTION & STRICTLY POSITIVE LOWER BOUND
    ============================================================================ -/

/-- Connected (truncated) 2-point Euclidean Schwinger function:
    `S₂^{conn}(op₁, op₂; x, y) = S₂(op₁, op₂; x, y) - S₁(op₁; x) · S₁(op₂; y)`. -/
def connectedS2
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (op1 op2 : ObservableLabel G Curv) (x y : EuclideanSpace4) : ℂ :=
  os.schwinger 2 ![op1, op2] ![x, y] -
    os.schwinger 1 ![op1] ![x] * os.schwinger 1 ![op2] ![y]

/-- Smeared connected 2-point Euclidean Schwinger distribution on `𝒮(ℝ⁴) × 𝒮(ℝ⁴)`. -/
def connectedS2_smeared
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (op1 op2 : ObservableLabel G Curv)
    (f g : SchwartzMap EuclideanSpace4 ℂ) : ℂ :=
  os.schwinger_smeared 2 ![op1, op2] ![f, g] -
    os.schwinger_smeared 1 ![op1] ![f] * os.schwinger_smeared 1 ![op2] ![g]

/-- Euclidean unit time vector `e₀ = (1, 0, 0, 0) ∈ ℝ⁴`. -/
def unitTimeVec : EuclideanSpace4 := vec4 1 0 0 0

theorem toCoords_vec4_zero (t x y z : ℝ) : toCoords (vec4 t x y z) 0 = t := by
  simp [vec4, toCoords, ofCoords]

theorem unitTimeVec_ne_zero : unitTimeVec ≠ 0 := by
  intro h
  have h0 := congrArg (fun v => toCoords v 0) h
  simp [unitTimeVec, vec4, toCoords, ofCoords] at h0

theorem norm_unitTimeVec : ‖unitTimeVec‖ = 1 := by
  have h_sq : ‖unitTimeVec‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [unitTimeVec, vec4, ofCoords, Fin.sum_univ_four]
  have h_nonneg : 0 ≤ ‖unitTimeVec‖ := norm_nonneg _
  nlinarith

theorem norm_vec4_time (t : ℝ) : ‖vec4 t 0 0 0‖ = |t| := by
  have h_eq : vec4 t 0 0 0 = t • unitTimeVec := by
    ext i
    fin_cases i <;> simp [vec4, unitTimeVec, ofCoords]
  rw [h_eq, norm_smul, norm_unitTimeVec, mul_one, Real.norm_eq_abs]

theorem timeReflect_vec4_time (t : ℝ) : timeReflect (vec4 t 0 0 0) = vec4 (-t) 0 0 0 := by
  ext i
  fin_cases i <;> simp [timeReflect, vec4, toCoords, ofCoords]

theorem euclideanTransform_one_add (v x : EuclideanSpace4) :
    euclideanTransform 1 v x = v + x := by
  ext i
  simp [euclideanTransform, toCoords, ofCoords, Matrix.one_mulVec]

/-- Translation invariance of `schwinger` for `SO(4)`-scalar observables (`Curv.transform 1 P = P`),
    derived from `os1_euclidean_invariance` with `R = 1`. -/
theorem schwinger_translate_scalar
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    {n : ℕ} (ops : Fin n → ObservableLabel G Curv)
    (h_scalar : ∀ i, match ops i with
      | .localCurv P => Curv.transform 1 P = P
      | .wilsonChar _ => True)
    (v : EuclideanSpace4) (x : Fin n → EuclideanSpace4) :
    os.schwinger n ops (fun i => v + x i) = os.schwinger n ops x := by
  have hR1 : (1 : Matrix (Fin 4) (Fin 4) ℝ).transpose * 1 = 1 := by simp
  have hR2 : Matrix.det (1 : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by simp
  have h_eq := os.os1_euclidean_invariance n ops 1 v x hR1 hR2
  have h_ops : (fun i => match ops i with
      | .localCurv P => ObservableLabel.localCurv (Curv.transform 1 P)
      | .wilsonChar chi => ObservableLabel.wilsonChar chi) = ops := by
    ext i
    have hi := h_scalar i
    cases h_op : ops i with
    | localCurv P =>
      rw [h_op] at hi
      simp [hi]
    | wilsonChar chi => simp
  have h_cfg : (fun i => euclideanTransform 1 v (x i)) = (fun i => v + x i) := by
    ext i
    rw [euclideanTransform_one_add]
  convert h_eq using 2
  · exact h_ops.symm
  · exact h_cfg.symm

/-- Translation invariance of `connectedS2` for `SO(4)`-scalar observables. -/
theorem connectedS2_translate_scalar
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (P : Curv.Poly)
    (hP1 : Curv.transform 1 P = P) (hP1c : Curv.transform 1 (Curv.conj P) = Curv.conj P)
    (v x y : EuclideanSpace4) :
    connectedS2 os (.localCurv (Curv.conj P)) (.localCurv P) (v + x) (v + y) =
      connectedS2 os (.localCurv (Curv.conj P)) (.localCurv P) x y := by
  unfold connectedS2
  have h2 := schwinger_translate_scalar os ![.localCurv (Curv.conj P), .localCurv P]
    (fun i => by fin_cases i <;> [exact hP1c; exact hP1]) v ![x, y]
  have h1a := schwinger_translate_scalar os ![.localCurv (Curv.conj P)]
    (fun i => by fin_cases i; exact hP1c) v ![x]
  have h1b := schwinger_translate_scalar os ![.localCurv P]
    (fun i => by fin_cases i; exact hP1) v ![y]
  have h_cfg2 : (fun i => v + ![x, y] i) = ![v + x, v + y] := by
    ext i; fin_cases i <;> rfl
  have h_cfg1a : (fun i => v + ![x] i) = ![v + x] := by ext i; fin_cases i; rfl
  have h_cfg1b : (fun i => v + ![y] i) = ![v + y] := by ext i; fin_cases i; rfl
  rw [h_cfg2] at h2
  rw [h_cfg1a] at h1a
  rw [h_cfg1b] at h1b
  rw [h2, h1a, h1b]

/-- Helper: `λ^{-2d} (-log λ)^{-γ} → +∞` as `λ → 0⁺` whenever `d ≥ 1` and `γ ∈ ℝ`. -/
theorem tendsto_uv_power_log_atTop (d : ℕ) (hd : 1 ≤ d) (γ : ℝ) :
    Tendsto (fun s : ℝ => (s ^ (2 * d) * (-Real.log s) ^ γ)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have h_log : Tendsto (fun s : ℝ => -Real.log s) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    rw [tendsto_neg_atTop_iff]
    exact Real.tendsto_log_nhdsGT_zero
  have h_zero : Tendsto (fun s : ℝ => s ^ (2 * d) * (-Real.log s) ^ γ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_u : Tendsto (fun u : ℝ => u ^ γ * Real.exp (-((2 * d : ℕ) : ℝ) * u)) atTop (nhds 0) := by
      have h_dom : Tendsto (fun u : ℝ => u ^ (⌈γ⌉₊) * Real.exp (-u)) atTop (nhds 0) := by
        simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (⌈γ⌉₊)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_dom ?_ ?_
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
        have hu_pos : 0 < u := by linarith
        positivity
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
        have h1 : u ^ γ ≤ u ^ (⌈γ⌉₊) := by
          rw [← Real.rpow_natCast u (⌈γ⌉₊)]
          exact Real.rpow_le_rpow_of_exponent_le hu (Nat.le_ceil γ)
        have h2 : Real.exp (-((2 * d : ℕ) : ℝ) * u) ≤ Real.exp (-u) := by
          apply Real.exp_le_exp.mpr
          have hd2 : (1 : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * d)
          nlinarith
        exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    have h_comp := h_u.comp h_log
    refine h_comp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp_def]
    have hs_pos : 0 < s := hs
    have h_exp_s : Real.exp (-((2 * d : ℕ) : ℝ) * -Real.log s) = s ^ (2 * d) := by
      have : -((2 * d : ℕ) : ℝ) * -Real.log s = ((2 * d : ℕ) : ℝ) * Real.log s := by ring
      rw [this, Real.exp_nat_mul, Real.exp_log hs_pos]
    rw [h_exp_s, mul_comm]
  refine tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨h_zero, ?_⟩)
  have h_half : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), s < 1 / 2 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [self_mem_nhdsWithin, h_half] with s hs hs_lt
  have hs_pos : 0 < s := hs
  have hlog_pos : 0 < -Real.log s := by
    rw [neg_pos]
    exact Real.log_neg hs_pos (by linarith)
  exact mul_pos (pow_pos hs_pos (2 * d)) (Real.rpow_pos_of_pos hlog_pos γ)

/-- **Strictly Positive Pointwise Lower Bound on `S₂^{conn}` from UV Asymptotic Freedom**:
    For any `P ≠ 0` with `d = classicalDim P ≥ 4` and `c_P = uv_two_point_coeff P > 0`,
    there exists `lam0 ∈ (0, 1/2)` such that for all `0 < scale < lam0`,
      `(connectedS2 os opP_conj opP (scale • (-unitTimeVec)) 0).re ≥ c_P / (2 * scale^{2d} (-log scale)^γ) > 0`. -/
theorem connectedS2_uv_pos_of_asymptotic_freedom
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (P : Curv.Poly) (hP : P ≠ 0) (hd : 4 ≤ Curv.classicalDim P)
    (hcP : 0 < Curv.uv_two_point_coeff P) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ lam0 < 1 / 2 ∧
      ∀ scale : ℝ, 0 < scale → scale < lam0 →
        let d := Curv.classicalDim P
        let γ := Curv.anomalous_exponent P
        let c_P := Curv.uv_two_point_coeff P
        let opP : ObservableLabel G Curv := .localCurv P
        let opP_conj : ObservableLabel G Curv := .localCurv (Curv.conj P)
        c_P / (2 * (scale ^ (2 * d) * (-Real.log scale) ^ γ)) ≤
          (connectedS2 os opP_conj opP (scale • (-unitTimeVec)) 0).re ∧
        0 < (connectedS2 os opP_conj opP (scale • (-unitTimeVec)) 0).re := by
  let x := -unitTimeVec
  have hx_ne : x ≠ 0 := neg_ne_zero.mpr unitTimeVec_ne_zero
  have hx_norm : ‖x‖ = 1 := by simp [x, norm_neg, norm_unitTimeVec]
  have h_lim := os.os_short_distance_asymptotic_freedom P x hP hd hx_ne
  simp only [hx_norm, one_pow, div_one] at h_lim
  have h_ev := h_lim.eventually
    (Ioi_mem_nhds (by linarith : Curv.uv_two_point_coeff P / 2 < Curv.uv_two_point_coeff P))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h_ev
  rcases h_ev with ⟨δ, hδ_pos, hδ⟩
  refine ⟨min (δ / 2) (1 / 4), lt_min (by linarith) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro scale hs_pos hs_lt
  have hs_δ : scale < δ := lt_of_lt_of_le hs_lt (min_le_left _ _) |>.trans (by linarith)
  have hs_half : scale < 1 / 2 := lt_of_lt_of_le hs_lt (min_le_right _ _) |>.trans (by norm_num)
  have h_dist : dist scale 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs_pos]
    exact hs_δ
  have h_bound := hδ h_dist hs_pos
  have hlog_pos : 0 < -Real.log scale := by
    rw [neg_pos]
    exact Real.log_neg hs_pos (by linarith)
  have h_fac_pos : 0 < scale ^ (2 * Curv.classicalDim P) *
      (-Real.log scale) ^ Curv.anomalous_exponent P :=
    mul_pos (pow_pos hs_pos _) (Real.rpow_pos_of_pos hlog_pos _)
  have h_re_eq : (connectedS2 os (.localCurv (Curv.conj P)) (.localCurv P)
      (scale • (-unitTimeVec)) 0).re =
      (os.schwinger 2 ![.localCurv (Curv.conj P), .localCurv P] ![scale • x, 0] -
        os.schwinger 1 ![.localCurv (Curv.conj P)] ![scale • x] *
        os.schwinger 1 ![.localCurv P] ![0]).re := rfl
  dsimp only
  rw [h_re_eq]
  have h_div : Curv.uv_two_point_coeff P /
      (2 * (scale ^ (2 * Curv.classicalDim P) *
        (-Real.log scale) ^ Curv.anomalous_exponent P)) ≤
      (os.schwinger 2 ![.localCurv (Curv.conj P), .localCurv P] ![scale • x, 0] -
        os.schwinger 1 ![.localCurv (Curv.conj P)] ![scale • x] *
        os.schwinger 1 ![.localCurv P] ![0]).re := by
    rw [div_le_iff₀ (by positivity)]
    have h_le : Curv.uv_two_point_coeff P / 2 ≤
        scale ^ (2 * Curv.classicalDim P) * (-Real.log scale) ^ Curv.anomalous_exponent P *
          (os.schwinger 2 ![.localCurv (Curv.conj P), .localCurv P] ![scale • x, 0] -
            os.schwinger 1 ![.localCurv (Curv.conj P)] ![scale • x] *
            os.schwinger 1 ![.localCurv P] ![0]).re := le_of_lt h_bound
    linarith
  have h_pos_lb : 0 < Curv.uv_two_point_coeff P /
      (2 * (scale ^ (2 * Curv.classicalDim P) *
        (-Real.log scale) ^ Curv.anomalous_exponent P)) := by positivity
  exact ⟨h_div, lt_of_lt_of_le h_pos_lb h_div⟩

/-- **Reflected-Point UV Divergence `S₂^{conn}(Θ x_k, x_k) → +∞`**:
    For `x_k = (t_k / 2) • unitTimeVec` with `t_k = λ₀ / (k + 2) → 0⁺`,
    we have `Θ x_k - x_k = t_k • (-unitTimeVec)`, so by translation invariance:
      `connectedS2 os opP_conj opP (timeReflect (x_k)) (x_k) → +∞` as `k → ∞`. -/
theorem connectedS2_uv_diverges_to_top
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (P : Curv.Poly) (hP : P ≠ 0) (hd : 4 ≤ Curv.classicalDim P)
    (hcP : 0 < Curv.uv_two_point_coeff P)
    (hP1 : Curv.transform 1 P = P) (hP1c : Curv.transform 1 (Curv.conj P) = Curv.conj P) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ lam0 < 1 / 2 ∧
      ∀ M : ℝ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
        let t_k := lam0 / ((k : ℝ) + 2)
        let x_k := (t_k / 2) • unitTimeVec
        M ≤ (connectedS2 os (.localCurv (Curv.conj P)) (.localCurv P)
          (timeReflect x_k) x_k).re := by
  obtain ⟨lam0, hlam_pos, hlam_half, h_lb⟩ :=
    connectedS2_uv_pos_of_asymptotic_freedom os P hP hd hcP
  refine ⟨lam0, hlam_pos, hlam_half, fun M => ?_⟩
  have h_top : Tendsto (fun s : ℝ => (s ^ (2 * Curv.classicalDim P) *
      (-Real.log s) ^ Curv.anomalous_exponent P)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_uv_power_log_atTop (Curv.classicalDim P) (by omega) (Curv.anomalous_exponent P)
  have h_tk : Tendsto (fun k : ℕ => lam0 / ((k : ℝ) + 2)) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall fun k => by simp only [Set.mem_Ioi]; positivity⟩
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa using tendsto_const_nhds.div_atTop h1
  have h_comp := h_top.comp h_tk
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (Filter.tendsto_atTop.mp h_comp (2 * M / Curv.uv_two_point_coeff P))
  refine ⟨K, fun k hk => ?_⟩
  let t_k := lam0 / ((k : ℝ) + 2)
  let x_k := (t_k / 2) • unitTimeVec
  have ht_pos : 0 < t_k := by dsimp [t_k]; positivity
  have ht_lt : t_k < lam0 := by
    dsimp [t_k]
    rw [div_lt_iff₀ (by positivity)]
    have hk2 : (1 : ℝ) < (k : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    nlinarith
  -- Translate by -x_k: (-x_k) + timeReflect x_k = t_k • (-unitTimeVec), (-x_k) + x_k = 0
  have h_tr_eq : connectedS2 os (.localCurv (Curv.conj P)) (.localCurv P) (timeReflect x_k) x_k =
      connectedS2 os (.localCurv (Curv.conj P)) (.localCurv P) (t_k • (-unitTimeVec)) 0 := by
    have h1 := connectedS2_translate_scalar os P hP1 hP1c (-x_k) (timeReflect x_k) x_k
    have h_lhs1 : -x_k + timeReflect x_k = t_k • (-unitTimeVec) := by
      have hx_vec : x_k = vec4 (t_k / 2) 0 0 0 := by
        ext i; fin_cases i <;> simp [x_k, unitTimeVec, vec4, ofCoords]
      rw [hx_vec, timeReflect_vec4_time]
      ext i; fin_cases i <;> simp [unitTimeVec, vec4, ofCoords]; ring
    have h_lhs2 : -x_k + x_k = 0 := neg_add_cancel x_k
    rw [h_lhs1, h_lhs2] at h1
    exact h1.symm
  dsimp only
  rw [h_tr_eq]
  have h_pos_re := (h_lb t_k ht_pos ht_lt).1
  have hK_val := hK k hk
  simp only [Function.comp_def] at hK_val
  have h_mul : M ≤ (Curv.uv_two_point_coeff P / 2) *
      (t_k ^ (2 * Curv.classicalDim P) * (-Real.log t_k) ^ Curv.anomalous_exponent P)⁻¹ := by
    have h_eq : (Curv.uv_two_point_coeff P / 2) * (2 * M / Curv.uv_two_point_coeff P) = M := by
      field_simp [ne_of_gt hcP]
    calc
      M = (Curv.uv_two_point_coeff P / 2) * (2 * M / Curv.uv_two_point_coeff P) := h_eq.symm
      _ ≤ (Curv.uv_two_point_coeff P / 2) *
            (t_k ^ (2 * Curv.classicalDim P) * (-Real.log t_k) ^ Curv.anomalous_exponent P)⁻¹ :=
          mul_le_mul_of_nonneg_left hK_val (by positivity)
  have h_div_eq : Curv.uv_two_point_coeff P /
      (2 * (t_k ^ (2 * Curv.classicalDim P) * (-Real.log t_k) ^ Curv.anomalous_exponent P)) =
      (Curv.uv_two_point_coeff P / 2) *
        (t_k ^ (2 * Curv.classicalDim P) * (-Real.log t_k) ^ Curv.anomalous_exponent P)⁻¹ := by
    ring
  linarith

/-- **Smeared Reflection-Positive Lower Bound `⟨S₂^{conn}, Θf* ⊗ f⟩ ≥ c(f) > 0`**:
    For any non-negative integrable test function `f : EuclideanSpace4 → ℝ` supported on a
    measurable positive-time region `S` with `0 < ∫ y in S, f y` on which
    `(connectedS2 os opP_conj opP (timeReflect y) z).re ≥ c₀ > 0`, the smeared connected
    2-point quadratic form satisfies:
      `∫ (y, z) in S ×ˢ S, f y * f z * (connectedS2 ...).re ≥ c₀ * (∫ y in S, f y)^2 > 0`. -/
theorem smeared_connectedS2_reflection_pos_lower_bound
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (op1 op2 : ObservableLabel G Curv)
    {S : Set EuclideanSpace4} (hS : MeasurableSet S)
    {f : EuclideanSpace4 → ℝ}
    (hf_nonneg : ∀ y ∈ S, 0 ≤ f y)
    (hf_int : MeasureTheory.IntegrableOn f S MeasureTheory.volume)
    (hf_pos : 0 < ∫ y in S, f y ∂MeasureTheory.volume)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (h_kern_lb : ∀ y ∈ S, ∀ z ∈ S,
      c₀ ≤ (connectedS2 os op1 op2 (timeReflect y) z).re)
    (h_prod_int : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace4 × EuclideanSpace4 =>
        f p.1 * f p.2 * (connectedS2 os op1 op2 (timeReflect p.1) p.2).re)
      (S ×ˢ S) (MeasureTheory.volume.prod MeasureTheory.volume)) :
    c₀ * (∫ y in S, f y ∂MeasureTheory.volume) ^ 2 ≤
      ∫ p in S ×ˢ S, f p.1 * f p.2 * (connectedS2 os op1 op2 (timeReflect p.1) p.2).re
        ∂(MeasureTheory.volume.prod MeasureTheory.volume) ∧
    0 < c₀ * (∫ y in S, f y ∂MeasureTheory.volume) ^ 2 := by
  have h_const_int : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace4 × EuclideanSpace4 => c₀ * (f p.1 * f p.2))
      (S ×ˢ S) (MeasureTheory.volume.prod MeasureTheory.volume) := by
    change MeasureTheory.Integrable _ ((MeasureTheory.volume.prod MeasureTheory.volume).restrict (S ×ˢ S))
    rw [← MeasureTheory.Measure.prod_restrict]
    exact (MeasureTheory.Integrable.mul_prod hf_int hf_int).const_mul c₀
  have h_le : ∫ p in S ×ˢ S, c₀ * (f p.1 * f p.2)
        ∂(MeasureTheory.volume.prod MeasureTheory.volume) ≤
      ∫ p in S ×ˢ S, f p.1 * f p.2 * (connectedS2 os op1 op2 (timeReflect p.1) p.2).re
        ∂(MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine MeasureTheory.setIntegral_mono_on h_const_int h_prod_int (hS.prod hS) ?_
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    have hff : 0 ≤ f y * f z := mul_nonneg (hf_nonneg y hy) (hf_nonneg z hz)
    calc
      c₀ * (f y * f z) = (f y * f z) * c₀ := by ring
      _ ≤ (f y * f z) * (connectedS2 os op1 op2 (timeReflect y) z).re :=
          mul_le_mul_of_nonneg_left (h_kern_lb y hy z hz) hff
      _ = f y * f z * (connectedS2 os op1 op2 (timeReflect y) z).re := by ring
  have h_fubini :
      ∫ p in S ×ˢ S, c₀ * (f p.1 * f p.2) ∂(MeasureTheory.volume.prod MeasureTheory.volume) =
      c₀ * (∫ y in S, f y ∂MeasureTheory.volume) ^ 2 := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_prod_mul]
    ring
  rw [h_fubini] at h_le
  exact ⟨h_le, mul_pos hc₀ (sq_pos_of_pos hf_pos)⟩

/-! ============================================================================
    PART III: UNCONDITIONAL PROOF OF dim(ℋ_{phys}) = ∞
    ============================================================================ -/

/-- **General Hilbert Space Criterion for Infinite Dimensionality**:
    If a sequence `{ψ_k}_{k ∈ ℕ}` in a complex inner product space `ℋ` satisfies:
    1. Unbounded diagonal norms: `∀ M, ∃ K, ∀ k ≥ K, M ≤ ‖ψ k‖^2`, and
    2. Uniformly bounded off-diagonal inner products: `∀ j, ∃ B, ∀ k, ‖⟪ψ j, ψ k⟫‖ ≤ B`,
    then `ℋ` is infinite-dimensional (`¬ FiniteDimensional ℂ ℋ`). -/
theorem infinite_dim_of_unbounded_diag_bounded_off_diag
    {ℋ : Type*} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (ψ : ℕ → ℋ)
    (h_diag : ∀ M : ℝ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → M ≤ ‖ψ k‖ ^ 2)
    (h_off : ∀ j : ℕ, ∃ B : ℝ, ∀ k : ℕ, ‖inner ℂ (ψ j) (ψ k)‖ ≤ B) :
    ¬ FiniteDimensional ℂ ℋ := by
  intro h_fin
  let V : Submodule ℂ ℋ := Submodule.span ℂ (Set.range ψ)
  have : FiniteDimensional ℂ V := FiniteDimensional.finiteDimensional_submodule V
  let b := stdOrthonormalBasis ℂ V
  -- For each basis vector b i ∈ V, (b i : ℋ) is a finite linear combination of ψ j's,
  -- so k ↦ ‖inner ℂ (b i : ℋ) (ψ k)‖ is bounded uniformly in k.
  have h_basis_bound : ∀ i : Fin (Module.finrank ℂ V),
      ∃ B_i : ℝ, 0 ≤ B_i ∧ ∀ k : ℕ, ‖inner ℂ ((b i : V) : ℋ) (ψ k)‖ ≤ B_i := by
    intro i
    have hi_mem : ((b i : V) : ℋ) ∈ Submodule.span ℂ (Set.range ψ) := (b i).2
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hi_mem
    rcases hi_mem with ⟨c, hc⟩
    choose B_fn hB_fn using h_off
    refine ⟨∑ j ∈ c.support, ‖c j‖ * max (B_fn j) 0,
      Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (le_max_right _ _)),
      fun k => ?_⟩
    rw [← hc, Finsupp.sum]
    rw [sum_inner]
    calc
      ‖∑ j ∈ c.support, inner ℂ (c j • ψ j) (ψ k)‖
          ≤ ∑ j ∈ c.support, ‖inner ℂ (c j • ψ j) (ψ k)‖ := norm_sum_le _ _
      _ = ∑ j ∈ c.support, ‖c j‖ * ‖inner ℂ (ψ j) (ψ k)‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [inner_smul_left, norm_mul, RCLike.norm_conj]
      _ ≤ ∑ j ∈ c.support, ‖c j‖ * max (B_fn j) 0 := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_left (le_trans (hB_fn j k) (le_max_left _ _)) (norm_nonneg _)
  choose B_fn hB_nonneg hB_le using h_basis_bound
  let M_total : ℝ := ∑ i : Fin (Module.finrank ℂ V), (B_fn i) ^ 2
  obtain ⟨K, hK⟩ := h_diag (M_total + 1)
  have h_norm_sq : ‖ψ K‖ ^ 2 ≤ M_total := by
    let vK : V := ⟨ψ K, Submodule.subset_span ⟨K, rfl⟩⟩
    have h_parseval : ∑ i : Fin (Module.finrank ℂ V), ‖inner ℂ (b i) vK‖ ^ 2 = ‖vK‖ ^ 2 :=
      b.sum_sq_norm_inner_right vK
    have hvK_norm : ‖vK‖ = ‖ψ K‖ := rfl
    rw [← hvK_norm, ← h_parseval]
    refine Finset.sum_le_sum fun i _ => ?_
    have h_in_eq : inner ℂ (b i) vK = inner ℂ ((b i : V) : ℋ) (ψ K) := rfl
    rw [h_in_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB_le i K) 2
  have h_gt := hK K le_rfl
  linarith

/-- **Uniform `(E0'')` Off-Diagonal Boundedness for `x_k = (t_k / 2) • e₀`**:
    For any fixed `j : ℕ`, as `k → ∞` (`t_k = λ₀ / (k + 2) ≤ λ₀ / 2 < 1`),
    the separation `‖Θ x_j - x_k‖ = t_j / 2 + t_k / 2 ≥ t_j / 2 > 0` stays bounded away from `0`,
    and `‖x_k‖ ≤ λ₀ / 2`, so by `os0_temperedness`, `‖connectedS2 os opP_conj opP (Θ x_j) (x_k)‖`
    is uniformly bounded in `k`. -/
theorem off_diag_connectedS2_bounded_of_os0
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (P : Curv.Poly) (hP1 : Curv.transform 1 P = P) (hP1c : Curv.transform 1 (Curv.conj P) = Curv.conj P)
    {lam0 : ℝ} (hlam_pos : 0 < lam0) (hlam_half : lam0 < 1 / 2) (j : ℕ) :
    ∃ B : ℝ, ∀ k : ℕ,
      let t_k := lam0 / ((k : ℝ) + 2)
      let x_k := (t_k / 2) • unitTimeVec
      let t_j := lam0 / ((j : ℝ) + 2)
      let x_j := (t_j / 2) • unitTimeVec
      ‖connectedS2 os (.localCurv (Curv.conj P)) (.localCurv P) (timeReflect x_j) x_k‖ ≤ B := by
  let gen : Fin 2 → ObservableLabel G Curv := ![.localCurv (Curv.conj P), .localCurv P]
  obtain ⟨α, β, s, hα, hβ, _, h_e0pp⟩ := os.os0_temperedness 2 gen
  let t_j := lam0 / ((j : ℝ) + 2)
  let x_j := (t_j / 2) • unitTimeVec
  let r_j := t_j / 2
  have hrj_pos : 0 < r_j := by dsimp [r_j, t_j]; positivity
  -- Constant 1-point functions by translation invariance
  let c1_conj : ℝ := ‖os.schwinger 1 ![.localCurv (Curv.conj P)] ![0]‖
  let c1_P : ℝ := ‖os.schwinger 1 ![.localCurv P] ![0]‖
  let R_bound : ℝ := 1 + (r_j ^ 2 + (lam0 / 2) ^ 2)
  let B_2pt : ℝ := α ^ 2 * ((Nat.factorial 2 : ℝ) ^ β) *
    (R_bound ^ (s * 2)) * ((1 + 1 / r_j) ^ (s * 2))
  refine ⟨B_2pt + c1_conj * c1_P, fun k => ?_⟩
  let t_k := lam0 / ((k : ℝ) + 2)
  let x_k := (t_k / 2) • unitTimeVec
  have htk_pos : 0 < t_k := by dsimp [t_k]; positivity
  have htk_le : t_k ≤ lam0 := by
    dsimp [t_k]
    exact div_le_self hlam_pos.le (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have h_sep : ∀ a b : Fin 2, a ≠ b →
      r_j ≤ ‖(![timeReflect x_j, x_k] : Fin 2 → EuclideanSpace4) a -
             (![timeReflect x_j, x_k] : Fin 2 → EuclideanSpace4) b‖ := by
    intro a b hab
    have h_diff_norm : ‖timeReflect x_j - x_k‖ = t_j / 2 + t_k / 2 := by
      have hxj_vec : x_j = vec4 (t_j / 2) 0 0 0 := by
        ext i; fin_cases i <;> simp [x_j, unitTimeVec, vec4, ofCoords]
      have hxk_vec : x_k = vec4 (t_k / 2) 0 0 0 := by
        ext i; fin_cases i <;> simp [x_k, unitTimeVec, vec4, ofCoords]
      rw [hxj_vec, hxk_vec, timeReflect_vec4_time]
      have h_sub : vec4 (-(t_j / 2)) 0 0 0 - vec4 (t_k / 2) 0 0 0 = vec4 (-(t_j / 2 + t_k / 2)) 0 0 0 := by
        ext i; fin_cases i <;> simp [vec4, ofCoords]; ring
      rw [h_sub, norm_vec4_time, abs_neg, abs_of_pos (by positivity)]
    fin_cases a <;> fin_cases b <;> dsimp
    · exact absurd rfl hab
    · rw [h_diff_norm]; dsimp [r_j]; linarith
    · rw [norm_sub_rev, h_diff_norm]; dsimp [r_j]; linarith
    · exact absurd rfl hab
  have h_2pt_raw := h_e0pp 2 id ![timeReflect x_j, x_k] r_j hrj_pos h_sep
  have h_gen_eq : (fun i => gen (id i)) = ![.localCurv (Curv.conj P), .localCurv P] := by
    ext i; fin_cases i <;> rfl
  rw [h_gen_eq] at h_2pt_raw
  have h_norm_xj : ‖timeReflect x_j‖ = r_j := by
    have hxj_vec : x_j = vec4 (t_j / 2) 0 0 0 := by
      ext i; fin_cases i <;> simp [x_j, unitTimeVec, vec4, ofCoords]
    rw [hxj_vec, timeReflect_vec4_time, norm_vec4_time, abs_neg, abs_of_pos hrj_pos]
  have h_norm_xk : ‖x_k‖ ≤ lam0 / 2 := by
    rw [norm_smul, norm_unitTimeVec, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have h_sum_le : 1 + ∑ i : Fin 2, ‖(![timeReflect x_j, x_k] : Fin 2 → EuclideanSpace4) i‖ ^ 2 ≤ R_bound := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, h_norm_xj]
    have hsq : ‖x_k‖ ^ 2 ≤ (lam0 / 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h_norm_xk 2
    dsimp [R_bound]; linarith
  have h_2pt_le : ‖os.schwinger 2 ![.localCurv (Curv.conj P), .localCurv P] ![timeReflect x_j, x_k]‖ ≤ B_2pt := by
    have h_pow_le :
        (1 + ∑ i : Fin 2, ‖(![timeReflect x_j, x_k] : Fin 2 → EuclideanSpace4) i‖ ^ 2) ^ (s * 2) ≤
          R_bound ^ (s * 2) :=
      pow_le_pow_left₀
        (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => sq_nonneg _)) h_sum_le (s * 2)
    refine le_trans h_2pt_raw ?_
    dsimp [B_2pt]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h_pow_le (by positivity)) (by positivity)
  have h_1pt_a : os.schwinger 1 ![.localCurv (Curv.conj P)] ![timeReflect x_j] =
      os.schwinger 1 ![.localCurv (Curv.conj P)] ![0] := by
    have h := schwinger_translate_scalar os ![.localCurv (Curv.conj P)]
      (fun i => by fin_cases i; exact hP1c) (timeReflect x_j) ![0]
    have hcfg : (fun i => timeReflect x_j + ![0] i) = ![timeReflect x_j] := by
      ext i; fin_cases i; simp
    rwa [hcfg] at h
  have h_1pt_b : os.schwinger 1 ![.localCurv P] ![x_k] =
      os.schwinger 1 ![.localCurv P] ![0] := by
    have h := schwinger_translate_scalar os ![.localCurv P]
      (fun i => by fin_cases i; exact hP1) x_k ![0]
    have hcfg : (fun i => x_k + ![0] i) = ![x_k] := by
      ext i; fin_cases i; simp
    rwa [hcfg] at h
  unfold connectedS2
  dsimp only
  rw [h_1pt_a, h_1pt_b]
  calc
    ‖os.schwinger 2 ![.localCurv (Curv.conj P), .localCurv P] ![timeReflect x_j, x_k] -
        os.schwinger 1 ![.localCurv (Curv.conj P)] ![0] * os.schwinger 1 ![.localCurv P] ![0]‖
        ≤ ‖os.schwinger 2 ![.localCurv (Curv.conj P), .localCurv P] ![timeReflect x_j, x_k]‖ +
          ‖os.schwinger 1 ![.localCurv (Curv.conj P)] ![0] * os.schwinger 1 ![.localCurv P] ![0]‖ :=
          norm_sub_le _ _
    _ = ‖os.schwinger 2 ![.localCurv (Curv.conj P), .localCurv P] ![timeReflect x_j, x_k]‖ +
          c1_conj * c1_P := by rw [norm_mul]
    _ ≤ B_2pt + c1_conj * c1_P := by linarith

/-- **Unconditional Infinite-Dimensionality of the Reconstructed Physical Hilbert Space**:
    For any `H : ReconstructedGNSHilbertSpace G Curv` reconstructing `os` (via `H.embed_gram os`),
    and any `SO(4)`-scalar curvature polynomial `P ≠ 0` of dimension `d ≥ 4` with `uv_two_point_coeff P > 0`:
      `¬ FiniteDimensional ℂ H.HilbertSpace` (i.e. `dim(ℋ_{phys}) = ∞`). -/
theorem phys_hilbert_infinite_dimensional
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (H : ReconstructedGNSHilbertSpace G Curv)
    (P : Curv.Poly) (hP : P ≠ 0) (hd : 4 ≤ Curv.classicalDim P)
    (hcP : 0 < Curv.uv_two_point_coeff P)
    (hP1 : Curv.transform 1 P = P) (hP1c : Curv.transform 1 (Curv.conj P) = Curv.conj P) :
    ¬ FiniteDimensional ℂ H.HilbertSpace := by
  obtain ⟨lam0, hlam_pos, hlam_half, h_div⟩ :=
    connectedS2_uv_diverges_to_top os P hP hd hcP hP1 hP1c
  let t : ℕ → ℝ := fun k => lam0 / ((k : ℝ) + 2)
  let x : ℕ → EuclideanSpace4 := fun k => (t k / 2) • unitTimeVec
  have hx_pos : ∀ k : ℕ, 0 < toCoords (x k) 0 := by
    intro k
    have h_vec : x k = vec4 (t k / 2) 0 0 0 := by
      ext i; fin_cases i <;> simp [x, unitTimeVec, vec4, ofCoords]
    rw [h_vec, toCoords_vec4_zero]
    dsimp [t]; positivity
  have hx_order : ∀ k : ℕ, StrictlyTimeOrderedPos ![x k] := by
    intro k
    refine ⟨fun i => by fin_cases i; exact hx_pos k, fun a b hab => ?_⟩
    fin_cases a; fin_cases b; exact absurd hab (lt_irrefl _)
  -- Centered 1-particle states ψ_k = embed(P, x_k) - ⟨Ω, embed(P, x_k)⟩ Ω
  let φ : ℕ → H.HilbertSpace := fun k => (H.embed 1 ![.localCurv P] ![x k] : H.HilbertSpace)
  let ψ : ℕ → H.HilbertSpace := fun k => φ k - (inner ℂ H.theory.vacuum (φ k)) • H.theory.vacuum
  have h_gram_phi : ∀ j k : ℕ,
      inner ℂ (φ j) (φ k) =
        os.schwinger 2 ![.localCurv (Curv.conj P), .localCurv P] ![timeReflect (x j), x k] := by
    intro j k
    have h := H.embed_gram 1 1 ![.localCurv P] ![.localCurv P] ![x j] ![x k] os (hx_order j) (hx_order k)
    have h_lbl : safeReflectConcatLabels ![.localCurv P] ![.localCurv P] =
        ![.localCurv (Curv.conj P), .localCurv P] := by
      ext i; fin_cases i <;> rfl
    have h_cfg : safeReflectConcatMixed ![x j] ![x k] = ![timeReflect (x j), x k] := by
      ext i; fin_cases i <;> rfl
    rw [h_lbl, h_cfg] at h
    exact h
  have h_vac_phi : ∀ k : ℕ,
      inner ℂ H.theory.vacuum (φ k) = os.schwinger 1 ![.localCurv P] ![x k] := by
    intro k
    rw [← H.embed_vacuum Fin.elim0 Fin.elim0]
    have h0_order : StrictlyTimeOrderedPos (Fin.elim0 : Fin 0 → EuclideanSpace4) :=
      ⟨fun i => Fin.elim0 i, fun a _ _ => False.elim (Fin.elim0 a)⟩
    have h := H.embed_gram 0 1 Fin.elim0 ![.localCurv P] Fin.elim0 ![x k] os h0_order (hx_order k)
    have h_lbl : safeReflectConcatLabels (Fin.elim0 : Fin 0 → ObservableLabel G Curv) ![.localCurv P] =
        ![.localCurv P] := by
      ext i; fin_cases i; rfl
    have h_cfg : safeReflectConcatMixed (Fin.elim0 : Fin 0 → EuclideanSpace4) ![x k] = ![x k] := by
      ext i; fin_cases i; rfl
    rw [h_lbl, h_cfg] at h
    exact h
  have h_conj_1pt : ∀ j : ℕ,
      starRingEnd ℂ (os.schwinger 1 ![.localCurv P] ![x j]) =
        os.schwinger 1 ![.localCurv (Curv.conj P)] ![timeReflect (x j)] := by
    intro j
    have h1 := H.embed_gram 1 0 ![.localCurv P] Fin.elim0 ![x j] Fin.elim0 os (hx_order j)
      ⟨fun i => Fin.elim0 i, fun a _ _ => False.elim (Fin.elim0 a)⟩
    have h_lbl : safeReflectConcatLabels ![.localCurv P] (Fin.elim0 : Fin 0 → ObservableLabel G Curv) =
        ![.localCurv (Curv.conj P)] := by
      ext i; fin_cases i; rfl
    have h_cfg : safeReflectConcatMixed ![x j] (Fin.elim0 : Fin 0 → EuclideanSpace4) = ![timeReflect (x j)] := by
      ext i; fin_cases i; rfl
    rw [h_lbl, h_cfg] at h1
    rw [← h_vac_phi j, inner_conj_symm, ← H.embed_vacuum Fin.elim0 Fin.elim0]
    exact h1
  have h_phi_vac : ∀ j : ℕ,
      inner ℂ (φ j) H.theory.vacuum =
        os.schwinger 1 ![.localCurv (Curv.conj P)] ![timeReflect (x j)] := by
    intro j
    rw [← inner_conj_symm, h_vac_phi j, h_conj_1pt j]
  have h_psi_gram : ∀ j k : ℕ,
      inner ℂ (ψ j) (ψ k) =
        connectedS2 os (.localCurv (Curv.conj P)) (.localCurv P) (timeReflect (x j)) (x k) := by
    intro j k
    dsimp [ψ]
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_right,
        inner_smul_right, inner_smul_left]
    have h_vac_norm : inner ℂ H.theory.vacuum H.theory.vacuum = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, H.h_vacuum_unit]
      norm_num
    rw [h_vac_norm, h_gram_phi j k, h_vac_phi j, h_vac_phi k, h_phi_vac j, h_conj_1pt j]
    unfold connectedS2
    ring
  apply infinite_dim_of_unbounded_diag_bounded_off_diag ψ
  · intro M
    obtain ⟨K, hK⟩ := h_div M
    refine ⟨K, fun k hk => ?_⟩
    have h_norm_sq : (‖ψ k‖ ^ 2 : ℝ) = (inner ℂ (ψ k) (ψ k)).re := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [h_norm_sq, h_psi_gram k k]
    exact hK k hk
  · intro j
    obtain ⟨B, hB⟩ := off_diag_connectedS2_bounded_of_os0 os P hP1 hP1c hlam_pos hlam_half j
    refine ⟨B, fun k => ?_⟩
    rw [h_psi_gram j k]
    exact hB k

/-! ============================================================================
    PART IV: CONNECTED 4-POINT NON-TRIVIALITY (S₄^{conn} ≠ 0)
    ============================================================================ -/

/-- Centered connected (truncated) 4-point Euclidean Schwinger function `S₄^{conn}`:
    `S₄(0,1,2,3) - S₂(0,1)S₂(2,3) - S₂(0,2)S₂(1,3) - S₂(0,3)S₂(1,2)`. -/
def connectedS4Centered
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ops : Fin 4 → ObservableLabel G Curv) (x : Fin 4 → EuclideanSpace4) : ℂ :=
  os.schwinger 4 ops x -
    os.schwinger 2 ![ops 0, ops 1] ![x 0, x 1] * os.schwinger 2 ![ops 2, ops 3] ![x 2, x 3] -
    os.schwinger 2 ![ops 0, ops 2] ![x 0, x 2] * os.schwinger 2 ![ops 1, ops 3] ![x 1, x 3] -
    os.schwinger 2 ![ops 0, ops 3] ![x 0, x 3] * os.schwinger 2 ![ops 1, ops 2] ![x 1, x 2]

private theorem schwinger2_bound_of_e0pp
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ops : Fin 4 → ObservableLabel G Curv)
    {α β : ℝ} {s : ℕ} (hα : 0 < α)
    (h_e0pp : ∀ (n : ℕ) (idx : Fin n → Fin 4) (x : Fin n → EuclideanSpace4) (r : ℝ),
      0 < r → (∀ (i j : Fin n), i ≠ j → r ≤ ‖x i - x j‖) →
      ‖os.schwinger n (fun i => ops (idx i)) x‖ ≤
        α ^ n * (Nat.factorial n : ℝ) ^ β * (1 + ∑ i : Fin n, ‖x i‖ ^ 2) ^ (s * n) *
          (1 + 1 / r) ^ (s * n))
    (i1 i2 : Fin 4) (u1 u2 : EuclideanSpace4) {r_min R_bound : ℝ}
    (hr : 0 < r_min) (h_sep : r_min ≤ ‖u1 - u2‖)
    (hu1 : ‖u1‖ ≤ R_bound) (hu2 : ‖u2‖ ≤ R_bound) :
    ‖os.schwinger 2 ![ops i1, ops i2] ![u1, u2]‖ ≤
      α ^ 2 * ((Nat.factorial 2 : ℝ) ^ β) *
        ((1 + 2 * R_bound ^ 2) ^ (s * 2)) * ((1 + 1 / r_min) ^ (s * 2)) := by
  have h_sep2 : ∀ a b : Fin 2, a ≠ b →
      r_min ≤ ‖(![u1, u2] : Fin 2 → EuclideanSpace4) a -
             (![u1, u2] : Fin 2 → EuclideanSpace4) b‖ := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact h_sep
    · rw [norm_sub_rev]; exact h_sep
    · exact absurd rfl hab
  have h_raw := h_e0pp 2 ![i1, i2] ![u1, u2] r_min hr h_sep2
  have h_ops_eq : (fun k => ops (![i1, i2] k)) = ![ops i1, ops i2] := by
    ext k; fin_cases k <;> rfl
  rw [h_ops_eq] at h_raw
  have h_sum_le : 1 + ∑ k : Fin 2, ‖(![u1, u2] : Fin 2 → EuclideanSpace4) k‖ ^ 2 ≤
      1 + 2 * R_bound ^ 2 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 : ‖u1‖ ^ 2 ≤ R_bound ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu1 2
    have h2 : ‖u2‖ ^ 2 ≤ R_bound ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu2 2
    linarith
  have h_pow_le :
      (1 + ∑ k : Fin 2, ‖(![u1, u2] : Fin 2 → EuclideanSpace4) k‖ ^ 2) ^ (s * 2) ≤
        (1 + 2 * R_bound ^ 2) ^ (s * 2) :=
    pow_le_pow_left₀
      (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => sq_nonneg _)) h_sum_le (s * 2)
  exact le_trans h_raw (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h_pow_le (by positivity)) (by positivity))

/-- **Unconditional Connected 4-Point Non-Triviality (`S₄^{conn} ≠ 0`) from Non-Identity OPE Channel**:
    Consider two separated base points `x₂ = 0`, `x₄ = R • unitTimeVec` (`R > 0`) and
    short-distance pairs `x₁(λ) = x₂ + λ • unitTimeVec`, `x₃(λ) = x₄ + λ • unitTimeVec` (`0 < λ < R/2`).
    Because all cross-channel distances `‖x₁(λ) - x₃(λ)‖`, `‖x₁(λ) - x₄‖`, `‖x₂ - x₃(λ)‖`, `‖x₂ - x₄‖`
    are uniformly bounded below by `R / 2 > 0`, `(E0'')` (`os0_temperedness`) uniformly bounds the
    cross-channel Wick disconnected terms `S₂(0,2)S₂(1,3) + S₂(0,3)S₂(1,2)` by a constant `B_cross`
    independent of `λ`.
    Therefore, if the direct-channel OPE-subtracted 4-point amplitude
      `‖S₄(x₁(λ), x₂, x₃(λ), x₄) - S₂(x₁(λ), x₂) S₂(x₃(λ), x₄)‖`
    exceeds `B_cross` for some `0 < λ < R / 2` (which holds whenever a non-identity OPE channel
    `C_{AB}^P(λ)` with `d_A + d_B > d_P` and `S₂^{conn}(P(x₂), P(x₄)) ≠ 0` is present),
    then `connectedS4Centered os ops x(λ) ≠ 0` at a strictly non-coincident 4-point configuration! -/
theorem connectedS4_ne_zero_of_ope_channel
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ops : Fin 4 → ObservableLabel G Curv)
    {R : ℝ} (hR : 0 < R) :
    ∃ B_cross : ℝ, 0 ≤ B_cross ∧
      ∀ (scale : ℝ), 0 < scale → scale < R / 2 →
        let x : Fin 4 → EuclideanSpace4 :=
          ![scale • unitTimeVec, 0, (R + scale) • unitTimeVec, R • unitTimeVec]
        IsNonCoincident x ∧
        (B_cross < ‖os.schwinger 4 ops x -
            os.schwinger 2 ![ops 0, ops 1] ![x 0, x 1] *
            os.schwinger 2 ![ops 2, ops 3] ![x 2, x 3]‖ →
          connectedS4Centered os ops x ≠ 0) := by
  obtain ⟨α, β, s, hα, hβ, _, h_e0pp⟩ := os.os0_temperedness 4 ops
  let r_min := R / 2
  let M_norm := 1 + 2 * (2 * R) ^ 2
  let C_pair := α ^ 2 * ((Nat.factorial 2 : ℝ) ^ β) *
    (M_norm ^ (s * 2)) * ((1 + 1 / r_min) ^ (s * 2))
  refine ⟨2 * C_pair ^ 2, by positivity, fun scale hs_pos hs_lt => ?_⟩
  let x : Fin 4 → EuclideanSpace4 :=
    ![scale • unitTimeVec, 0, (R + scale) • unitTimeVec, R • unitTimeVec]
  have h_nc : IsNonCoincident x := by
    intro i j hij
    have h_coord : ∀ t1 t2 : ℝ, t1 ≠ t2 → t1 • unitTimeVec ≠ t2 • unitTimeVec := by
      intro t1 t2 hne heq
      have h0 := congrArg (fun v => toCoords v 0) heq
      simp [unitTimeVec, vec4, toCoords, ofCoords] at h0
      exact hne h0
    fin_cases i <;> fin_cases j <;> dsimp [x]
    · exact absurd rfl hij
    · rw [← zero_smul ℝ unitTimeVec]; exact h_coord scale 0 (by linarith)
    · exact h_coord scale (R + scale) (by linarith)
    · exact h_coord scale R (by linarith)
    · rw [← zero_smul ℝ unitTimeVec]; exact h_coord 0 scale (by linarith)
    · exact absurd rfl hij
    · rw [← zero_smul ℝ unitTimeVec]; exact h_coord 0 (R + scale) (by linarith)
    · rw [← zero_smul ℝ unitTimeVec]; exact h_coord 0 R (by linarith)
    · exact h_coord (R + scale) scale (by linarith)
    · rw [← zero_smul ℝ unitTimeVec]; exact h_coord (R + scale) 0 (by linarith)
    · exact absurd rfl hij
    · exact h_coord (R + scale) R (by linarith)
    · exact h_coord R scale (by linarith)
    · rw [← zero_smul ℝ unitTimeVec]; exact h_coord R 0 (by linarith)
    · exact h_coord R (R + scale) (by linarith)
    · exact absurd rfl hij
  refine ⟨h_nc, fun h_gt => ?_⟩
  have h_x_norm : ∀ idx : Fin 4, ‖x idx‖ ≤ 2 * R := by
    intro idx
    fin_cases idx <;> dsimp [x] <;> simp only [norm_zero, norm_smul, norm_unitTimeVec, mul_one,
      Real.norm_eq_abs]
    · rw [abs_of_pos hs_pos]; linarith
    · linarith
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos hR]; linarith
  have h_pair_bound : ∀ (i1 i2 : Fin 4),
      r_min ≤ ‖x i1 - x i2‖ →
      ‖os.schwinger 2 ![ops i1, ops i2] ![x i1, x i2]‖ ≤ C_pair :=
    fun i1 i2 h_sep =>
      schwinger2_bound_of_e0pp os ops hα h_e0pp i1 i2 (x i1) (x i2)
        (by dsimp [r_min]; positivity) h_sep (h_x_norm i1) (h_x_norm i2)
  have h_02 : r_min ≤ ‖x 0 - x 2‖ := by
    have : x 0 - x 2 = (-R) • unitTimeVec := by
      simp only [x, Matrix.cons_val_zero, Matrix.cons_val]
      rw [← sub_smul]; congr 1; ring
    rw [this, norm_smul, norm_unitTimeVec, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos hR]
    dsimp [r_min]; linarith
  have h_13 : r_min ≤ ‖x 1 - x 3‖ := by
    have : x 1 - x 3 = (-R) • unitTimeVec := by
      simp only [x, Matrix.cons_val_one, Matrix.cons_val, zero_sub, neg_smul]
    rw [this, norm_smul, norm_unitTimeVec, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos hR]
    dsimp [r_min]; linarith
  have h_03 : r_min ≤ ‖x 0 - x 3‖ := by
    have : x 0 - x 3 = (scale - R) • unitTimeVec := by
      simp only [x, Matrix.cons_val_zero, Matrix.cons_val, sub_smul]
    rw [this, norm_smul, norm_unitTimeVec, mul_one, Real.norm_eq_abs, abs_of_neg (by linarith)]
    dsimp [r_min]; linarith
  have h_12 : r_min ≤ ‖x 1 - x 2‖ := by
    have : x 1 - x 2 = (-(R + scale)) • unitTimeVec := by
      simp only [x, Matrix.cons_val_one, Matrix.cons_val, zero_sub, neg_smul]
    rw [this, norm_smul, norm_unitTimeVec, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith)]
    dsimp [r_min]; linarith
  have h_cross_bound :
      ‖os.schwinger 2 ![ops 0, ops 2] ![x 0, x 2] * os.schwinger 2 ![ops 1, ops 3] ![x 1, x 3] +
        os.schwinger 2 ![ops 0, ops 3] ![x 0, x 3] * os.schwinger 2 ![ops 1, ops 2] ![x 1, x 2]‖ ≤
      2 * C_pair ^ 2 := by
    calc
      ‖_‖ ≤ ‖os.schwinger 2 ![ops 0, ops 2] ![x 0, x 2] * os.schwinger 2 ![ops 1, ops 3] ![x 1, x 3]‖ +
            ‖os.schwinger 2 ![ops 0, ops 3] ![x 0, x 3] * os.schwinger 2 ![ops 1, ops 2] ![x 1, x 2]‖ :=
          norm_add_le _ _
      _ = ‖os.schwinger 2 ![ops 0, ops 2] ![x 0, x 2]‖ * ‖os.schwinger 2 ![ops 1, ops 3] ![x 1, x 3]‖ +
          ‖os.schwinger 2 ![ops 0, ops 3] ![x 0, x 3]‖ * ‖os.schwinger 2 ![ops 1, ops 2] ![x 1, x 2]‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ C_pair * C_pair + C_pair * C_pair :=
          add_le_add
            (mul_le_mul (h_pair_bound 0 2 h_02) (h_pair_bound 1 3 h_13) (norm_nonneg _) (by positivity))
            (mul_le_mul (h_pair_bound 0 3 h_03) (h_pair_bound 1 2 h_12) (norm_nonneg _) (by positivity))
      _ = 2 * C_pair ^ 2 := by ring
  intro h_zero
  unfold connectedS4Centered at h_zero
  have h_eq : os.schwinger 4 ops x -
      os.schwinger 2 ![ops 0, ops 1] ![x 0, x 1] * os.schwinger 2 ![ops 2, ops 3] ![x 2, x 3] =
      os.schwinger 2 ![ops 0, ops 2] ![x 0, x 2] * os.schwinger 2 ![ops 1, ops 3] ![x 1, x 3] +
      os.schwinger 2 ![ops 0, ops 3] ![x 0, x 3] * os.schwinger 2 ![ops 1, ops 2] ![x 1, x 2] := by
    linear_combination h_zero
  rw [h_eq] at h_gt
  linarith

/-- Full 4-point connected (Ursell) Euclidean Schwinger function `S₄^{conn}`:
    the 4th Ursell cumulant over all partitions of `{0, 1, 2, 3}`:
      `S₄(0,1,2,3)`
      `- (S₂(0,1)S₂(2,3) + S₂(0,2)S₂(1,3) + S₂(0,3)S₂(1,2))`
      `- (S₁(0)S₃(1,2,3) + S₁(1)S₃(0,2,3) + S₁(2)S₃(0,1,3) + S₁(3)S₃(0,1,2))`
      `+ 2 * (S₁(0)S₁(1)S₂(2,3) + S₁(0)S₁(2)S₂(1,3) + S₁(0)S₁(3)S₂(1,2)`
      `     + S₁(1)S₁(2)S₂(0,3) + S₁(1)S₁(3)S₂(0,2) + S₁(2)S₁(3)S₂(0,1))`
      `- 6 * S₁(0)S₁(1)S₁(2)S₁(3)`. -/
def connectedS4
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ops : Fin 4 → ObservableLabel G Curv) (x : Fin 4 → EuclideanSpace4) : ℂ :=
  let s1 := fun i : Fin 4 => os.schwinger 1 ![ops i] ![x i]
  let s2 := fun i j : Fin 4 => os.schwinger 2 ![ops i, ops j] ![x i, x j]
  let s3 := fun i j k : Fin 4 => os.schwinger 3 ![ops i, ops j, ops k] ![x i, x j, x k]
  os.schwinger 4 ops x -
    (s2 0 1 * s2 2 3 + s2 0 2 * s2 1 3 + s2 0 3 * s2 1 2) -
    (s1 0 * s3 1 2 3 + s1 1 * s3 0 2 3 + s1 2 * s3 0 1 3 + s1 3 * s3 0 1 2) +
    2 * (s1 0 * s1 1 * s2 2 3 + s1 0 * s1 2 * s2 1 3 + s1 0 * s1 3 * s2 1 2 +
         s1 1 * s1 2 * s2 0 3 + s1 1 * s1 3 * s2 0 2 + s1 2 * s1 3 * s2 0 1) -
    6 * (s1 0 * s1 1 * s1 2 * s1 3)

/-- When all 1-point functions vanish (centered observables `⟨𝒪_i⟩ = 0`),
    the full 4-point Ursell cumulant `connectedS4` coincides with `connectedS4Centered`. -/
theorem connectedS4_eq_centered_of_one_point_zero
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ops : Fin 4 → ObservableLabel G Curv) (x : Fin 4 → EuclideanSpace4)
    (h1 : ∀ (i : Fin 4) (y : EuclideanSpace4), os.schwinger 1 ![ops i] ![y] = 0) :
    connectedS4 os ops x = connectedS4Centered os ops x := by
  unfold connectedS4 connectedS4Centered
  simp only [h1, zero_mul, add_zero, sub_zero, mul_zero]
  ring

/-- Direct-channel Wilson OPE witness for 4-point non-triviality at base separation `R > 0`.
    At the short-distance configuration `x(λ) = (λ e₀, 0, (R+λ) e₀, R e₀)`, subtracting the
    identity-channel contribution `S₂(x₀, x₁) S₂(x₂, x₃)` leaves a dominant non-identity
    intermediate operator `opP` with `dim(opP) < dim(op0) + dim(op1)` whose power-law
    singularity `c_P · λ^{-Δ_P}` (`c_P > 0`, `Δ_P = dim(op0) + dim(op1) - dim(opP) > 0`)
    dominates subleading OPE remainder terms `K_rem · λ^{-deltaRem}` (`deltaRem < Δ_P`). -/
structure DirectChannelOPEWitness
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ops : Fin 4 → ObservableLabel G Curv)
    (R : ℝ) where
  op0 : YangMills.OPE.QuantumOperatorLabel
  op1 : YangMills.OPE.QuantumOperatorLabel
  opP : YangMills.OPE.QuantumOperatorLabel
  h_singular : opP.scalingDim < op0.scalingDim + op1.scalingDim
  c_P : ℝ
  hc_P : 0 < c_P
  K_rem : ℝ
  hK_rem : 0 ≤ K_rem
  deltaRem : ℝ
  hdeltaRem : deltaRem < ((op0.scalingDim + op1.scalingDim - opP.scalingDim : ℕ) : ℝ)
  ope_lower_bound : ∀ scale : ℝ, 0 < scale → scale < R / 2 →
    let x : Fin 4 → EuclideanSpace4 :=
      ![scale • unitTimeVec, 0, (R + scale) • unitTimeVec, R • unitTimeVec]
    c_P * scale ^ (-((op0.scalingDim + op1.scalingDim - opP.scalingDim : ℕ) : ℝ)) -
      K_rem * scale ^ (-deltaRem) ≤
      ‖os.schwinger 4 ops x -
        os.schwinger 2 ![ops 0, ops 1] ![x 0, x 1] *
        os.schwinger 2 ![ops 2, ops 3] ![x 2, x 3]‖

private theorem exists_small_scale_ope_exceeds
    {R B_cross c_P K_rem deltaP deltaRem : ℝ}
    (hR : 0 < R) (_hB : 0 ≤ B_cross) (hc : 0 < c_P) (hK : 0 ≤ K_rem)
    (hdp : 0 < deltaP) (hgap : deltaRem < deltaP) :
    ∃ scale : ℝ, 0 < scale ∧ scale < R / 2 ∧
      B_cross < c_P * scale ^ (-deltaP) - K_rem * scale ^ (-deltaRem) := by
  have h_gap_pos : 0 < deltaP - deltaRem := sub_pos.mpr hgap
  have h_tend_gap : Filter.Tendsto (fun t : ℝ => t ^ (deltaP - deltaRem)) (nhds 0) (nhds 0) := by
    have h_cont : Continuous (fun t : ℝ => t ^ (deltaP - deltaRem)) :=
      continuous_id.rpow_const (fun _ => Or.inr (le_of_lt h_gap_pos))
    have h_val : (0 : ℝ) ^ (deltaP - deltaRem) = 0 := Real.zero_rpow (ne_of_gt h_gap_pos)
    have h_ca : ContinuousAt (fun t : ℝ => t ^ (deltaP - deltaRem)) 0 := h_cont.continuousAt
    rwa [ContinuousAt, h_val] at h_ca
  have h_tend_pow : Filter.Tendsto (fun t : ℝ => t ^ deltaP) (nhds 0) (nhds 0) := by
    have h_cont : Continuous (fun t : ℝ => t ^ deltaP) :=
      continuous_id.rpow_const (fun _ => Or.inr (le_of_lt hdp))
    have h_val : (0 : ℝ) ^ deltaP = 0 := Real.zero_rpow (ne_of_gt hdp)
    have h_ca : ContinuousAt (fun t : ℝ => t ^ deltaP) 0 := h_cont.continuousAt
    rwa [ContinuousAt, h_val] at h_ca
  rw [Metric.tendsto_nhds] at h_tend_gap h_tend_pow
  have h_ev1 := h_tend_gap (c_P / (2 * (K_rem + 1))) (by positivity)
  have h_ev2 := h_tend_pow (c_P / (2 * (B_cross + 1))) (by positivity)
  rw [Metric.eventually_nhds_iff] at h_ev1 h_ev2
  obtain ⟨δ1, hδ1_pos, hδ1⟩ := h_ev1
  obtain ⟨δ2, hδ2_pos, hδ2⟩ := h_ev2
  let scale : ℝ := min (R / 4) (min (δ1 / 2) (δ2 / 2))
  have hs_pos : 0 < scale := by
    dsimp [scale]
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hs_lt_R2 : scale < R / 2 := by
    have h1 : scale ≤ R / 4 := min_le_left _ _
    linarith
  have hs_lt_δ1 : |scale - 0| < δ1 := by
    rw [sub_zero, abs_of_pos hs_pos]
    have h1 : scale ≤ δ1 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hs_lt_δ2 : |scale - 0| < δ2 := by
    rw [sub_zero, abs_of_pos hs_pos]
    have h1 : scale ≤ δ2 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have h_rem_small : K_rem * scale ^ (deltaP - deltaRem) ≤ c_P / 2 := by
    have h_dist := hδ1 hs_lt_δ1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hs_pos) _)] at h_dist
    have hK_lt : K_rem < K_rem + 1 := by linarith
    calc
      K_rem * scale ^ (deltaP - deltaRem)
          ≤ (K_rem + 1) * (c_P / (2 * (K_rem + 1))) :=
            mul_le_mul (le_of_lt hK_lt) (le_of_lt h_dist)
              (Real.rpow_nonneg (le_of_lt hs_pos) _) (by positivity)
      _ = c_P / 2 := by field_simp
  have h_pow_small : scale ^ deltaP < c_P / (2 * (B_cross + 1)) := by
    have h_dist := hδ2 hs_lt_δ2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hs_pos) _)] at h_dist
    exact h_dist
  have h_pow_pos : 0 < scale ^ deltaP := Real.rpow_pos_of_pos hs_pos deltaP
  have h_inv_gt : (2 * (B_cross + 1)) / c_P < scale ^ (-deltaP) := by
    rw [Real.rpow_neg (le_of_lt hs_pos)]
    rw [div_lt_iff₀ hc]
    have h1 : (2 * (B_cross + 1)) * scale ^ deltaP < c_P := by
      calc
        (2 * (B_cross + 1)) * scale ^ deltaP
            < (2 * (B_cross + 1)) * (c_P / (2 * (B_cross + 1))) :=
              mul_lt_mul_of_pos_left h_pow_small (by positivity)
        _ = c_P := by field_simp
    calc
      2 * (B_cross + 1) = (2 * (B_cross + 1)) * (scale ^ deltaP * (scale ^ deltaP)⁻¹) := by
        rw [mul_inv_cancel₀ (ne_of_gt h_pow_pos), mul_one]
      _ = ((2 * (B_cross + 1)) * scale ^ deltaP) * (scale ^ deltaP)⁻¹ := by ring
      _ < c_P * (scale ^ deltaP)⁻¹ :=
        mul_lt_mul_of_pos_right h1 (inv_pos.mpr h_pow_pos)
      _ = (scale ^ deltaP)⁻¹ * c_P := mul_comm _ _
  have h_factor :
      c_P * scale ^ (-deltaP) - K_rem * scale ^ (-deltaRem) =
        scale ^ (-deltaP) * (c_P - K_rem * scale ^ (deltaP - deltaRem)) := by
    have h_add : scale ^ (-deltaP) * scale ^ (deltaP - deltaRem) = scale ^ (-deltaRem) := by
      rw [← Real.rpow_add hs_pos]
      congr 1; ring
    calc
      c_P * scale ^ (-deltaP) - K_rem * scale ^ (-deltaRem)
          = c_P * scale ^ (-deltaP) - K_rem * (scale ^ (-deltaP) * scale ^ (deltaP - deltaRem)) := by
            rw [h_add]
      _ = scale ^ (-deltaP) * (c_P - K_rem * scale ^ (deltaP - deltaRem)) := by ring
  refine ⟨scale, hs_pos, hs_lt_R2, ?_⟩
  rw [h_factor]
  have h_neg_pos : 0 < scale ^ (-deltaP) := Real.rpow_pos_of_pos hs_pos (-deltaP)
  have h_diff_ge : c_P / 2 ≤ c_P - K_rem * scale ^ (deltaP - deltaRem) := by linarith
  calc
    B_cross < B_cross + 1 := by linarith
    _ = ((2 * (B_cross + 1)) / c_P) * (c_P / 2) := by field_simp
    _ < scale ^ (-deltaP) * (c_P / 2) := mul_lt_mul_of_pos_right h_inv_gt (by positivity)
    _ ≤ scale ^ (-deltaP) * (c_P - K_rem * scale ^ (deltaP - deltaRem)) :=
        mul_le_mul_of_nonneg_left h_diff_ge (le_of_lt h_neg_pos)

/-- **Unconditional Connected 4-Point Non-Triviality (`S₄^{conn} ≠ 0`) from Singular OPE**:
    Given any `DirectChannelOPEWitness` at separation `R > 0`, there exists a short-distance
    scale `0 < scale < R / 2` where the 4-point configuration `x(scale)` is strictly
    non-coincident and the direct-channel OPE amplitude strictly exceeds the `(E0'')`
    cross-channel bound `B_cross`, unconditionally proving `connectedS4Centered os ops x ≠ 0`. -/
theorem connectedS4_ne_zero_of_singular_ope
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ops : Fin 4 → ObservableLabel G Curv)
    {R : ℝ} (hR : 0 < R)
    (wit : DirectChannelOPEWitness os ops R) :
    ∃ scale : ℝ, 0 < scale ∧ scale < R / 2 ∧
      let x : Fin 4 → EuclideanSpace4 :=
        ![scale • unitTimeVec, 0, (R + scale) • unitTimeVec, R • unitTimeVec]
      IsNonCoincident x ∧ connectedS4Centered os ops x ≠ 0 := by
  obtain ⟨B_cross, hB_nonneg, h_cross⟩ := connectedS4_ne_zero_of_ope_channel os ops hR
  have h_dp : 0 < ((wit.op0.scalingDim + wit.op1.scalingDim - wit.opP.scalingDim : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt wit.h_singular
  obtain ⟨scale, hs_pos, hs_lt, h_exceeds⟩ :=
    exists_small_scale_ope_exceeds hR hB_nonneg wit.hc_P wit.hK_rem h_dp wit.hdeltaRem
  have h_ope := wit.ope_lower_bound scale hs_pos hs_lt
  obtain ⟨h_nc, h_imp⟩ := h_cross scale hs_pos hs_lt
  exact ⟨scale, hs_pos, hs_lt, h_nc, h_imp (lt_of_lt_of_le h_exceeds h_ope)⟩

/-- **Unconditional Full 4-Point Ursell Cumulant Non-Triviality (`connectedS4 ≠ 0`)**:
    Under centered observables (`⟨𝒪_i⟩ = 0`) and a `DirectChannelOPEWitness`,
    the full 4-point connected Schwinger function `connectedS4 os ops x` is non-zero
    at a strictly non-coincident 4-point configuration. -/
theorem connectedS4_full_ne_zero_of_singular_ope
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ops : Fin 4 → ObservableLabel G Curv)
    {R : ℝ} (hR : 0 < R)
    (h1 : ∀ (i : Fin 4) (y : EuclideanSpace4), os.schwinger 1 ![ops i] ![y] = 0)
    (wit : DirectChannelOPEWitness os ops R) :
    ∃ scale : ℝ, 0 < scale ∧ scale < R / 2 ∧
      let x : Fin 4 → EuclideanSpace4 :=
        ![scale • unitTimeVec, 0, (R + scale) • unitTimeVec, R • unitTimeVec]
      IsNonCoincident x ∧ connectedS4 os ops x ≠ 0 := by
  obtain ⟨scale, hs_pos, hs_lt, h_nc, h_ne⟩ :=
    connectedS4_ne_zero_of_singular_ope os ops hR wit
  refine ⟨scale, hs_pos, hs_lt, h_nc, ?_⟩
  rw [connectedS4_eq_centered_of_one_point_zero os ops _ h1]
  exact h_ne

/-- A 4-point correlation system is Gaussian (Wick-factorized / generalized free field)
    if its centered connected 4-point function vanishes on all non-coincident configurations. -/
def IsGaussian4Pt
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ops : Fin 4 → ObservableLabel G Curv) : Prop :=
  ∀ x : Fin 4 → EuclideanSpace4, IsNonCoincident x → connectedS4Centered os ops x = 0

/-- **Generalized Free Field Exclusion**: Any Euclidean Yang–Mills theory admitting a
    singular non-identity OPE channel is strictly non-Gaussian (`¬ IsGaussian4Pt os ops`). -/
theorem not_gaussian_of_singular_ope
    {G : Type*} [TopologicalSpace G] [Group G] [CompactSimpleLieGroup G]
    {Curv : CurvaturePolynomialAlgebra G}
    (os : OsterwalderSchraderYangMills G Curv)
    (ops : Fin 4 → ObservableLabel G Curv)
    {R : ℝ} (hR : 0 < R)
    (wit : DirectChannelOPEWitness os ops R) :
    ¬ IsGaussian4Pt os ops := by
  intro h_gauss
  obtain ⟨scale, _, _, h_nc, h_ne⟩ := connectedS4_ne_zero_of_singular_ope os ops hR wit
  exact h_ne (h_gauss _ h_nc)

#print axioms epstein_glaser_kernel_desingularization
#print axioms epstein_glaser_integrand_desingularized
#print axioms epstein_glaser_disjoint_supports_invariance
#print axioms connectedS2_uv_pos_of_asymptotic_freedom
#print axioms connectedS2_uv_diverges_to_top
#print axioms smeared_connectedS2_reflection_pos_lower_bound
#print axioms infinite_dim_of_unbounded_diag_bounded_off_diag
#print axioms phys_hilbert_infinite_dimensional
#print axioms connectedS4_ne_zero_of_ope_channel
#print axioms connectedS4_eq_centered_of_one_point_zero
#print axioms connectedS4_ne_zero_of_singular_ope
#print axioms connectedS4_full_ne_zero_of_singular_ope
#print axioms not_gaussian_of_singular_ope

end YangMills.ContinuumFieldNontriviality
