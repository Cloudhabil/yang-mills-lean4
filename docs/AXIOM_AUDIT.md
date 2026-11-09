# Comprehensive Lean 4 Kernel Axiom Audit

[← Back to README](../README.md)

## Machine-Checked `#print axioms` Verification

Every constructive capstone theorem is verified via `#print axioms` to depend exclusively on `[propext, Classical.choice, Quot.sound]`:

| Module | Certified Capstone Declaration | Core Axioms | Custom Axioms | `sorry` Status |
| :--- | :--- | :--- | :--- | :--- |
| **UnconditionalInfiniteLimit** | `unconditional_infinite_lattice_master_synthesis` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **UnconditionalInfiniteLimit** | `autonomousPolymerTrajectory_unconditional_all_scales` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **UnconditionalInfiniteLimit** | `autonomousPolymerTrajectory_tendsto_rStarIR` ($r^* = 2 - \sqrt{16/5}$) | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **UnconditionalInfiniteLimit** | `autonomousInfiniteRGFlow_unconditional_invariants` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **UnconditionalInfiniteLimit** | `unconditional_discharges_C2` & `allScaleBetaLat_discharges_C1` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **UnconditionalInfiniteLimit** | `continuum_so4_rotational_restoration_tendsto_zero` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **StandardModelExtension** | `full_standard_model_spectrum_incontrovertible` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **StandardModelExtension** | `landmark9_chiral_anomaly_cancellation_iff_su3_color` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **StandardModelExtension** | `landmark10_electroweak_weinberg_mixing_and_higgs_mass` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **StandardModelExtension** | `landmark11b_neuberger_overlap_exact_ginsparg_wilson` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **StandardModelExtension** | `landmark12_three_generation_beta_baryon_and_gmor_spectrum` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **YangMillsEightLandmarks** | `eight_yang_mills_landmarks_incontrovertible` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **YangMillsEightLandmarks** | `landmark1_su3_odderon_quadratic_blindspot` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **YangMillsEightLandmarks** | `landmark2_unscoped_os0_forces_trivial_schwinger` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **YangMillsEightLandmarks** | `landmark7_1d_scaling_trap_vs_4d_isotropic_ir_gap` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **YangMillsEightLandmarks** | `landmark8_gns_norm_collapse_trap_vs_bilinear_quotient` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **HaarWilsonLattice** | `fullWilsonTransferOp_spectral_gap` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **ToposConstructiveRG** | `dacc_hodge_greens_right_inv` ($\Delta_2 G_2 = I_{10}$) | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **ToposConstructiveRG** | `multiscale_polymer_non_explosion` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **BalabanPRT1** | `lapBalaban_coercive` & `lapBalaban_injective` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **BalabanRG1** | `no_mass_counterterm_of_gauge_invariance` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **BalabanLFR1** | `polymer_activity_ratio_lt_one` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **BalabanOS2** | `os2_quotient_inner_nondegenerate` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **BalabanPipeline** | `balaban_master_continuum_yang_mills_mass_gap` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **OsterwalderSchrader** | `os_semigroup_clustering_implies_hamiltonian_gap` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |
| **OsterwalderSchrader** | `sun_millennium_statement_of_constructive_pipeline` | `[propext, Classical.choice, Quot.sound]` | **None** | **0 sorry** |

---

