import Lake
open Lake DSL

package "yang-mills-lean4" where
  version := v!"0.1.0"
  keywords := #["yang-mills", "mass-gap", "formalization", "lean4"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

lean_lib «MillenniumYangMills» where
  roots := #[`MillenniumYangMills]

lean_lib «ToposUnifiedYangMills» where
  roots := #[`ToposUnifiedYangMills]

lean_lib «ToposConstructiveRG» where
  roots := #[`ToposConstructiveRG]

lean_lib «RGCrossoverCertificate» where
  roots := #[`RGCrossoverCertificate]

lean_lib «KervaireMilnor7Sphere» where
  roots := #[`KervaireMilnor7Sphere]

lean_lib «SmoothPoincareVariants» where
  roots := #[`SmoothPoincareVariants]

lean_lib «FourManifoldGaugeTopology» where
  roots := #[`FourManifoldGaugeTopology]
