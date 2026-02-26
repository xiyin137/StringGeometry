import Lake
open Lake DSL

package "StringGeometry" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

require SGSupermanifolds from git
  "https://github.com/xiyin137/stringgeometry-supermanifolds.git" @ "4d48fb0"

require SGRiemannSurfaces from git
  "https://github.com/xiyin137/stringgeometry-riemann-surfaces.git" @ "ab1b034"

require SGSuperRiemannSurfaces from git
  "https://github.com/xiyin137/stringgeometry-super-riemann-surfaces.git" @ "eea54e7"

lean_lib StringGeometry where
  roots := #[`StringGeometry]
