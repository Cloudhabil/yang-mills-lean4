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



