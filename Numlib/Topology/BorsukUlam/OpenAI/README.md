# Vendored odd-sphere dimension theorem

These files are the transitive Lean source dependencies of
`OAI.BorsukNine.SimplicialChains.odd_sphere_dimension_bound_fintype`, from the
[OpenAI math repository](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Geometry/Borsuk)
at commit `4eaee87548250b2682affda7d05d947c05554bae`. The upstream
artifact uses Lean 4.34.1 and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The extracted source uses
Mathlib as its only external import.

The original Apache 2.0 license is in [LICENSE](LICENSE).
[SOURCES.tsv](SOURCES.tsv) gives the sorted upstream file list, corresponding
local paths, and SHA-256 hashes of the original source bytes at the pinned
commit.

The local changes relocate the internal imports from `OAI.Geometry.Borsuk`
to `Numlib.Topology.BorsukUlam.OpenAI`, preserving the declaration namespaces.
[Imports.lean](Imports.lean) lists the selective Mathlib imports used in
place of the upstream root import. This avoids loading the separate Mathlib
Hessenberg declarations into the existing Numlib Hessenberg environment.
`SphereGeometry/IntegralLift.lean` uses the current spelling
`integral_pos_of_integrable_nonneg_ne_zero` for a deprecated Mathlib alias.
The original proof terms and statements are otherwise unchanged.

The backbone entry point is `Numlib.Topology.BorsukUlam`. Run
`lake build Numlib.Topology.BorsukUlam` to build the local prerequisite.

The pinned source and local proof were checked with Lean 4.36.0-rc2.
