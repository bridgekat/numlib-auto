import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Actual derivatives on an open smoothness neighborhood

Continuous differentiability on an open set gives actual Fréchet derivative certificates
throughout a neighborhood of each of its points.
-/

open Filter Topology

/-- Smoothness of nonzero order on an open neighborhood supplies actual derivatives
at every sufficiently near point. -/
theorem ContDiffOn.eventually_hasFDerivAt {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : WithTop ℕ∞} {f : E → F} {U : Set E} {x : E} (hf : ContDiffOn 𝕜 n f U)
    (hn : n ≠ 0) (hU : IsOpen U) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, HasFDerivAt f (fderiv 𝕜 f y) y :=
  Filter.Eventually.mono (show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hx) fun _ hy =>
    ((hf.differentiableOn hn _ hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
