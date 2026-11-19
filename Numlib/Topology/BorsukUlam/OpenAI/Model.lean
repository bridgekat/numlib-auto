/-
Vendored from OpenAI math at commit 4eaee87548250b2682affda7d05d947c05554bae.
Modified for Numlib to use local module paths and selective Mathlib imports.
See the Apache 2.0 license and source manifest in the vendored directory.
-/
import Numlib.Topology.BorsukUlam.OpenAI.Imports

namespace OAI

namespace BorsukNine

abbrev Vector4 := EuclideanSpace ℝ (Fin 4)
abbrev Matrix4 := EuclideanSpace ℝ (Fin 4 × Fin 4)

def projector (u : Vector4) : Matrix4 :=
  WithLp.toLp 2 (fun ij => u ij.1 * u ij.2)

def projectorSet : Set Matrix4 :=
  projector '' {u : Vector4 | ‖u‖ = 1}

def traceOneSymmetric : Set Matrix4 :=
  {A | (∀ i j : Fin 4, A (i, j) = A (j, i)) ∧ ∑ i : Fin 4, A (i, i) = 1}

def HasTenSmallCover : Prop :=
  ∃ C : Fin 10 → Set Matrix4,
    (∀ i, C i ⊆ projectorSet) ∧
    projectorSet ⊆ ⋃ i, C i ∧
    ∀ i, Metric.diam (C i) < Real.sqrt 2

end BorsukNine

end OAI
