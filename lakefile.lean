import Lake
open Lake DSL

package "StringGeometry" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

require SGSupermanifolds from git
  "https://github.com/xiyin137/stringgeometry-supermanifolds.git" @ "121ab54"

require SGRiemannSurfaces from git
  "https://github.com/xiyin137/stringgeometry-riemann-surfaces.git" @ "62a9791"

require SGSuperRiemannSurfaces from git
  "https://github.com/xiyin137/stringgeometry-super-riemann-surfaces.git" @ "6179767"

lean_lib StringGeometry where
  roots := #[`StringGeometry]
