import Lake
open Lake DSL

package "yang-mills-lean4" where
  version := v!"0.1.0"
  keywords := #["yang-mills", "mass-gap", "formalization", "lean4"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

@[default_target]
lean_lib «MillenniumYangMills» where
  roots := #[`MillenniumYangMills]

@[default_target]
lean_lib «ToposUnifiedYangMills» where
  roots := #[`ToposUnifiedYangMills]

@[default_target]
lean_lib «ToposConstructiveRG» where
  roots := #[`ToposConstructiveRG]

@[default_target]
lean_lib «RGCrossoverCertificate» where
  roots := #[`RGCrossoverCertificate]

@[default_target]
lean_lib «UVThresholdBridge» where
  roots := #[`UVThresholdBridge]

@[default_target]
lean_lib «HypercubicPolymerCounting» where
  roots := #[`HypercubicPolymerCounting]

@[default_target]
lean_lib «ContinuumFieldNontriviality» where
  roots := #[`ContinuumFieldNontriviality]

@[default_target]
lean_lib «HaarWilsonLattice» where
  roots := #[`HaarWilsonLattice]

@[default_target]
lean_lib «OsterwalderSchraderReconstruction» where
  roots := #[`OsterwalderSchraderReconstruction]

@[default_target]
lean_lib «BalabanConstructivePipeline» where
  roots := #[`BalabanConstructivePipeline]

@[default_target]
lean_lib «BalabanPRT1» where
  roots := #[`BalabanPRT1]

@[default_target]
lean_lib «BalabanPRT2» where
  roots := #[`BalabanPRT2]

@[default_target]
lean_lib «BalabanREG» where
  roots := #[`BalabanREG]

@[default_target]
lean_lib «BalabanVAR» where
  roots := #[`BalabanVAR]

@[default_target]
lean_lib «BalabanPBG» where
  roots := #[`BalabanPBG]

@[default_target]
lean_lib «BalabanRG1» where
  roots := #[`BalabanRG1]

@[default_target]
lean_lib «BalabanRG2» where
  roots := #[`BalabanRG2]

@[default_target]
lean_lib «BalabanCRE» where
  roots := #[`BalabanCRE]

@[default_target]
lean_lib «BalabanLFR1» where
  roots := #[`BalabanLFR1]

@[default_target]
lean_lib «BalabanOS2» where
  roots := #[`BalabanOS2]

@[default_target]
lean_lib «YangMillsEightLandmarks» where
  roots := #[`YangMillsEightLandmarks]

@[default_target]
lean_lib «StandardModelExtension» where
  roots := #[`StandardModelExtension]

@[default_target]
lean_lib «UnconditionalInfiniteLatticeLimit» where
  roots := #[`UnconditionalInfiniteLatticeLimit]

@[default_target]
lean_lib «ContinuumDistributionalCauchyLimit» where
  roots := #[`ContinuumDistributionalCauchyLimit]

@[default_target]
lean_lib «QuantumOperatorProductExpansion» where
  roots := #[`QuantumOperatorProductExpansion]

@[default_target]
lean_lib «ConstructiveGNSReconstruction» where
  roots := #[`ConstructiveGNSReconstruction]

@[default_target]
lean_lib «CompactLieGroupsSimplicity» where
   roots := #[`CompactLieGroupsSimplicity]

@[default_target]
lean_lib «MillenniumSynthesisClosure» where
  roots := #[`MillenniumSynthesisClosure]








