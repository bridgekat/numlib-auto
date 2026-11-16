/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Orthonormal`, and
`Mathlib.Analysis.InnerProductSpace.PiL2` (which imports it) for `norm_sum_smul_eq_norm_toLp`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Parseval's identity for a finite orthonormal family

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$(v_i)_{i \in \iota}$ be an orthonormal family in $E$ indexed by a finite type $\iota$. For every
family of coefficients $c_i \in \mathbb{K}$, the squared norm of the combination is the sum of the
squared moduli of the coefficients:
$$\Big\| \sum_i c_i v_i \Big\|^2 = \sum_i |c_i|^2.$$
This is the squared-norm form of Mathlib's `Orthonormal.inner_sum`. It is the computation in
coordinates behind every column expansion of a factorization with orthonormal columns, such as the
singular value decomposition and principal vectors. Its square root says that the norm of the
combination is the Euclidean norm of the coefficient vector.

## Main results

* `Orthonormal.norm_sum_smul_sq`: $\|\sum_i c_i v_i\|^2 = \sum_i |c_i|^2$.
* `Orthonormal.norm_sum_smul_eq_norm_toLp`: $\|\sum_i c_i v_i\|$ is the norm of $c$ in
  $\mathbb{K}^\iota$ with the Euclidean norm.
-/

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

/-- **Parseval's identity for a finite orthonormal family.** Let $E$ be an inner product space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $\iota$ be a finite type, and let
$(v_i)_{i \in \iota}$ be an orthonormal family in $E$. Then for every
$c \colon \iota \to \mathbb{K}$,
$$\Big\| \sum_i c_i v_i \Big\|^2 = \sum_i |c_i|^2.$$
-/
theorem Orthonormal.norm_sum_smul_sq {v : ι → E} (hv : Orthonormal 𝕜 v) (c : ι → 𝕜) :
    ‖∑ i, c i • v i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  have h := hv.inner_sum c c Finset.univ
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ((‖∑ i, c i • v i‖ ^ 2 : ℝ) : 𝕜) = ((∑ i, ‖c i‖ ^ 2 : ℝ) : 𝕜) := by
    push_cast
    rw [h]
    exact Finset.sum_congr rfl fun i _ => RCLike.conj_mul (c i)
  exact_mod_cast h2

/-- **Parseval's identity for a finite orthonormal family**, without squares. Let $E$ be an inner
product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $\iota$ be a finite type, and
let $(v_i)_{i \in \iota}$ be an orthonormal family in $E$. Then for every
$c \colon \iota \to \mathbb{K}$, the norm $\|\sum_i c_i v_i\|$ equals the Euclidean norm
$(\sum_i |c_i|^2)^{1/2}$ of the coefficient vector.

The coefficient vector is `WithLp.toLp 2 c`, the vector $c$ seen as an element of
`EuclideanSpace 𝕜 ι`. -/
theorem Orthonormal.norm_sum_smul_eq_norm_toLp {v : ι → E} (hv : Orthonormal 𝕜 v) (c : ι → 𝕜) :
    ‖∑ i, c i • v i‖ = ‖(WithLp.toLp 2 c : EuclideanSpace 𝕜 ι)‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [hv.norm_sum_smul_sq, EuclideanSpace.norm_sq_eq]
