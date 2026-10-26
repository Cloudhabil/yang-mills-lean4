import Lake
open Lake DSL

package "yang-mills-lean4" where
  version := v!"0.1.0"
  keywords := #["yang-mills", "mass-gap", "formalization", "lean4"]

lean_lib «ToposUnifiedYangMills» where
  roots := #[`ToposUnifiedYangMills]
