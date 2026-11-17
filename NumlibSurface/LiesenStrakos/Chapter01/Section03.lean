/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Energy
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# §1.3. Basic notation

For a positive definite Hermitian operator $B$, [liesen2013krylov] writes $(v,w)_B = w^*Bv$.
The inner product defines a norm on vectors and an induced operator norm.

## Main definitions

* `LiesenStrakos.energyInnerProduct`: the $B$-inner product in the book's argument order.
* `LiesenStrakos.energyVectorNorm`: the norm induced by the $B$-inner product.
* `LiesenStrakos.energyOperatorNorm`: the induced operator norm.
* `LiesenStrakos.EnergyOrthogonal`: orthogonality for the $B$-inner product.
-/

namespace LiesenStrakos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The $B$-inner product in §1.3 of [liesen2013krylov] is $(v,w)_B = w^*Bv$. -/
noncomputable abbrev energyInnerProduct (B : E →ₗ[𝕜] E) (v w : E) : 𝕜 :=
  inner 𝕜 w (B v)

/-- The $B$-norm of a vector is $\|v\|_B = \sqrt{\operatorname{Re}(v^*Bv)}$. -/
noncomputable abbrev energyVectorNorm (B : E →ₗ[𝕜] E) : E → ℝ :=
  energyNorm B

/-- The induced $B$-norm of $M$ is its operator norm for the vector norm $\|\cdot\|_B$. -/
noncomputable def energyOperatorNorm [FiniteDimensional 𝕜 E] (B M : E →ₗ[𝕜] E)
    (hB : B.IsSymmetricCoercive) : ℝ := by
  let e := WithEnergy.equiv B hB
  letI : FiniteDimensional 𝕜 (WithEnergy B hB) := e.finiteDimensional
  exact ‖((e : E →ₗ[𝕜] WithEnergy B hB).comp (M.comp e.symm.toLinearMap)).toContinuousLinearMap‖

/-- Vectors $v$ and $w$ are $B$-orthogonal when $w^*Bv=0$. -/
abbrev EnergyOrthogonal (B : E →ₗ[𝕜] E) (v w : E) : Prop :=
  energyInnerProduct B v w = 0

end LiesenStrakos
