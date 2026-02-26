import Lake
open Lake DSL

package "StringGeometry" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

require SGSupermanifolds from git
  "https://github.com/xiyin137/stringgeometry-supermanifolds.git" @ "fc8efce"

require SGRiemannSurfaces from git
  "https://github.com/xiyin137/stringgeometry-riemann-surfaces.git" @ "62a9791"

require SGSuperRiemannSurfaces from git
  "https://github.com/xiyin137/stringgeometry-super-riemann-surfaces.git" @ "e9020d4"

lean_lib StringGeometry where
  roots := #[`StringGeometry]
