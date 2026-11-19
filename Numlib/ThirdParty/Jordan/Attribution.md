# Provenance of the Jordan orientation proof

This directory extracts an Apache-2.0 proof prerequisite for the Jordan
curve theorem, the bounded interior and unbounded exterior separation,
and the winding signs of rectifiable Jordan curves. The source files
retain their existing notices and identify the upstream project, commit,
and original path. Each license file is the corresponding upstream
license. ModuleInventory.tsv lists the exact source closure.

| Project | Exact revision | Extracted contribution |
| --- | --- | --- |
| [Rado Kirov's jordan_pick](https://github.com/rkirov/jordan_pick/tree/7905cd4c75038b823a8204e5474996905dd50800) | 7905cd4c75038b823a8204e5474996905dd50800 | The four continuous Jordan and Brouwer modules |
| [Dean Cureton's MovingSofa](https://github.com/deancureton/MovingSofa/tree/4d5569131940815f47a9ccf3e90a4c5043c56127) | 4d5569131940815f47a9ccf3e90a4c5043c56127 | Planar geometry, Jordan separation, continuous angles and winding, and arclength |
| [Kim Morrison's isoperimetric](https://github.com/kim-em/isoperimetric/tree/919aa52aca02625e4525d67d688940261ab5d459) | 919aa52aca02625e4525d67d688940261ab5d459 | Rectifiable parametrizations, a unit winding jump, and the interior sign |

## Local changes

* Prefix the Lean module paths by Numlib.ThirdParty.Jordan and update
  their local imports. The upstream declaration namespaces are retained.
* Replace the four JordanPick modules' Mathlib umbrella imports with
  focused imports. This avoids loading Mathlib's unrelated
  Matrix.IsUpperHessenberg declaration into the existing Numlib matrix
  environment. No Jordan proof statements or proof bodies changed.
* In Isoperimetric.Topology.Orientation, replace the GeometricArea
  import and its dependency on a bundled bounded-variation area path
  with the ordinary continuous restriction to the parameter interval.
  The proof of the range identity comes from the original GeometricArea
  module. The winding theorem still covers every continuous rectifiable
  simple closed traversal.
* Remove the unused final isoperimetric-inequality specification from
  Isoperimetric.Statement. The area and inequality proofs and unrelated
  package targets are outside the extracted module closure.

The extracted modules use the repository's existing Mathlib dependency.
The Humanfia archive, MovingSofa's other dependencies, and the original
projects' Lake configurations are outside this source closure.
