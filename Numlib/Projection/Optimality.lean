/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Projection.Basic

/-!
# Optimality properties of projection methods

Let $A$ be a linear operator on an inner product space $E$, let $b \in E$, and let $x^*$ solve
$Ax = b$. Write $\langle u, v \rangle_A = \langle Au, v \rangle$ for the energy inner product,
$\|u\|_A = \sqrt{\operatorname{Re}\langle Au, u \rangle}$ for the energy norm, and $\varphi(x) =
\tfrac12 \operatorname{Re}\langle Ax, x \rangle - \operatorname{Re}\langle b, x \rangle$ for the
energy functional. For symmetric coercive $A$ the first two are an inner product and its norm. This
file shows that the projection conditions of `Numlib.Projection.Basic` are optimality conditions. A
Galerkin iterate over $x_0 + K$ is exactly a minimizer of the energy norm of the error over
$x_0 + K$ ([saad2003iterative] Proposition 5.2, [hestenes1952methods] Theorem 4:3), and exactly a
minimizer of $\varphi$ over $x_0 + K$ ([fong2012cg] §2.1). The Galerkin error is the
energy-orthogonal projection of the initial error $x^* - x_0$ onto the energy-orthogonal complement
of $K$ ([saad2003iterative] Proposition 5.5). Nested trial spaces give nonincreasing errors.

Following [quarteroni2000numerical] Definition 4.4 and the displays after it, $\varphi$ is minimal
along a direction $p$ at $x$ exactly when the residual $b - Ax$ is orthogonal to $p$. The
minimal-error iterate is the orthogonal projection of $x^*$ onto $x_0 + K$, and it is unique. Over
$x_0 + A^H L$ it satisfies the Petrov–Galerkin condition with test space $L$ ([saad2003iterative]
§8.3, [choi2006iterative]).

## Main results

* `IsGalerkin.iff_energyNorm_min`: for symmetric coercive $A$ and finite-dimensional $K$, $x$ is a
  Galerkin iterate if and only if it minimizes $\|x^* - y\|_A$ over $y \in x_0 + K$.
* `IsGalerkin.error_eq_starProjection`: the Galerkin error is the energy-orthogonal projection of
  $x^* - x_0$ onto the energy-orthogonal complement of $K$.
* `IsGalerkin.energyNorm_le_of_le`: on nested trial spaces the energy norms of the Galerkin errors
  are nonincreasing.
* `isGalerkin_iff_forall_quadratic_le`: for symmetric coercive $A$ and $x \in x_0 + K$, $x$ is a
  Galerkin iterate if and only if it minimizes $\varphi$ over $x_0 + K$.
* `inner_residual_eq_zero_iff_forall_quadratic_add_smul_le`: $\varphi$ is minimal at $x$ along the
  line $x + \mathbb{K} p$ if and only if $\langle b - Ax, p \rangle = 0$.
* `IsMinError.eq_starProjection`: the minimal-error iterate is $x_0 + P_K(x^* - x_0)$.
* `IsMinError.unique`: the minimal-error iterate is unique.
* `IsMinError.isPetrovGalerkin_of_map_adjoint`: minimal error over $x_0 + A^H L$ is the
  Petrov–Galerkin condition with test space $L$.

## Implementation notes

* The energy inner product, the energy norm and the energy functional are `energyInner`,
  `energyNorm` and `energyFunctional` of `Numlib.Analysis.InnerProductSpace.Energy`. They are
  defined for every $A$; the hypotheses enter only in the statements.
* $\mathbb{K}$ is the scalar field, $\mathbb{R}$ or $\mathbb{C}$. Over $\mathbb{C}$ a real step
  length detects only the real part of $\langle b - Ax, p \rangle$, so optimality along a direction
  is stated with a real and with a $\mathbb{K}$-valued parameter.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x₀ : E} {K : Submodule 𝕜 E} {x xstar : E}

/-- Let $A : E \to E$ be any linear map. If $\|u\|_A^2 \le \|v\|_A^2$, then $\|u\|_A \le \|v\|_A$.
-/
theorem energyNorm_le_of_sq_le {u v : E} (h : energyNorm A u ^ 2 ≤ energyNorm A v ^ 2) :
    energyNorm A u ≤ energyNorm A v := by
  have h2 := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (energyNorm_nonneg A u), Real.sqrt_sq (energyNorm_nonneg A v)] at h2

/-- **Pythagoras for the energy inner product.** Let $A$ be symmetric coercive. If
$\langle u, v \rangle_A = 0$, then
$$\|u + v\|_A^2 = \|u\|_A^2 + \|v\|_A^2.$$
-/
theorem energyNorm_add_sq (hA : A.IsSymmetricCoercive) {u v : E} (h : energyInner A u v = 0) :
    energyNorm A (u + v) ^ 2 = energyNorm A u ^ 2 + energyNorm A v ^ 2 := by
  have huv : inner 𝕜 (A u) v = (0 : 𝕜) := h
  have hvu : inner 𝕜 (A v) u = (0 : 𝕜) := by
    rw [hA.isSymmetric v u, ← inner_conj_symm, huv, map_zero]
  rw [hA.energyNorm_sq, hA.energyNorm_sq, hA.energyNorm_sq, map_add, inner_add_left,
    inner_add_right, inner_add_right, huv, hvu]
  simp

namespace IsGalerkin

/-- **The Galerkin error is energy-orthogonal to the trial space.** Let $x$ satisfy the Galerkin
condition for $(A, b, x_0, K)$ and let $Ax^* = b$. Then for every $z \in K$,
$$\langle x^* - x, z \rangle_A = 0.$$

No symmetry or coercivity of $A$ is needed, because $\langle A(x^* - x), z \rangle = \langle b -
Ax, z \rangle$. -/
theorem energyInner_error_eq_zero (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) {z : E} (hz : z ∈ K) : energyInner A (xstar - x) z = 0 := by
  have h : energyInner A (xstar - x) z = inner 𝕜 (A (xstar - x)) z := rfl
  rw [h, map_sub, hstar]
  exact inner_eq_zero_symm.1 (hx.inner_residual_eq_zero hz)

/-- **Pythagoras in the energy norm.** Let $A$ be symmetric coercive, let $x$ satisfy the Galerkin
condition for $(A, b, x_0, K)$ and let $Ax^* = b$. Then for every $y \in x_0 + K$,
$$\|x^* - y\|_A^2 = \|x^* - x\|_A^2 + \|x - y\|_A^2.$$
-/
theorem energyNorm_sq_add (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) {y : E} (hy : y - x₀ ∈ K) :
    energyNorm A (xstar - y) ^ 2 = energyNorm A (xstar - x) ^ 2 + energyNorm A (x - y) ^ 2 := by
  have hxy : x - y ∈ K := by
    have h : x - y = (x - x₀) - (y - x₀) := by abel
    rw [h]; exact K.sub_mem hx.mem hy
  have hsum : xstar - y = (xstar - x) + (x - y) := by abel
  rw [hsum]
  exact energyNorm_add_sq hA (energyInner_error_eq_zero hx hstar hxy)

/-- **Galerkin iterates minimize the energy norm of the error** ([saad2003iterative], Proposition
5.2, forward direction). Let $A$ be symmetric coercive, let $x$ satisfy the Galerkin condition
for $(A, b, x_0, K)$, and let $Ax^* = b$. Then for every $y \in x_0 + K$,
$$\|x^* - x\|_A \le \|x^* - y\|_A.$$
-/
theorem energyNorm_le (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) {y : E} (hy : y - x₀ ∈ K) :
    energyNorm A (xstar - x) ≤ energyNorm A (xstar - y) := by
  refine energyNorm_le_of_sq_le ?_
  rw [energyNorm_sq_add hA hx hstar hy]
  nlinarith [energyNorm_nonneg A (x - y)]

/-- **Galerkin iterates are the energy-norm minimizers** ([saad2003iterative], Proposition 5.2). Let
$A$ be symmetric coercive, let $Ax^* = b$, and let $K$ be finite-dimensional. Then $x$ satisfies
the Galerkin condition for $(A, b, x_0, K)$ if and only if $x \in x_0 + K$ and
$$\|x^* - x\|_A \le \|x^* - y\|_A \quad\text{for all } y \in x_0 + K.$$
-/
theorem iff_energyNorm_min (hA : A.IsSymmetricCoercive) (hstar : A xstar = b)
    [FiniteDimensional 𝕜 K] :
    IsGalerkin A b x₀ K x ↔
      x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K → energyNorm A (xstar - x) ≤ energyNorm A (xstar - y) := by
  refine ⟨fun hx => ⟨hx.mem, fun y hy => energyNorm_le hA hx hstar hy⟩, ?_⟩
  rintro ⟨hmem, hmin⟩
  obtain ⟨x', hx', -⟩ :=
    existsUnique_isGalerkin_of_isCoercive (A := A) b x₀ K hA.isCoercive
  have heq : energyNorm A (xstar - x) = energyNorm A (xstar - x') :=
    le_antisymm (hmin x' hx'.mem) (energyNorm_le hA hx' hstar hmem)
  have hpy := energyNorm_sq_add hA hx' hstar hmem
  rw [← heq] at hpy
  have hzero : energyNorm A (x' - x) = 0 := by
    nlinarith [energyNorm_nonneg A (x' - x), energyNorm_nonneg A (xstar - x)]
  have : x' = x := sub_eq_zero.1 (hA.energyNorm_eq_zero_iff.1 hzero)
  rwa [this] at hx'

/-- **Monotonicity on nested subspaces.** Let $A$ be symmetric coercive, let $K \subseteq K'$, let
$x$ and $x'$ satisfy the Galerkin condition for $(A, b, x_0, K)$ and $(A, b, x_0, K')$, and let
$Ax^* = b$. Then $\|x^* - x'\|_A \le \|x^* - x\|_A$. -/
theorem energyNorm_le_of_le (hA : A.IsSymmetricCoercive) {K' : Submodule 𝕜 E} {x' : E}
    (hx : IsGalerkin A b x₀ K x) (hx' : IsGalerkin A b x₀ K' x') (hKK' : K ≤ K')
    (hstar : A xstar = b) : energyNorm A (xstar - x') ≤ energyNorm A (xstar - x) :=
  energyNorm_le hA hx' hstar (hKK' hx.mem)

/-- **Galerkin iterates minimize the quadratic functional** ([fong2012cg], (2.1)). Let $A$ be
symmetric coercive and let $x$ satisfy the Galerkin condition for $(A, b, x_0, K)$. Then for
every $y \in x_0 + K$,
$$\tfrac12 \operatorname{Re}\langle Ax, x \rangle - \operatorname{Re}\langle b, x \rangle \le
  \tfrac12 \operatorname{Re}\langle Ay, y \rangle - \operatorname{Re}\langle b, y \rangle.$$
-/
theorem quadratic_le (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x) {y : E}
    (hy : y - x₀ ∈ K) :
    RCLike.re (inner 𝕜 (A x) x) / 2 - RCLike.re (inner 𝕜 b x) ≤
      RCLike.re (inner 𝕜 (A y) y) / 2 - RCLike.re (inner 𝕜 b y) := by
  have hd : y - x ∈ K := by
    have h : y - x = (y - x₀) - (x - x₀) := by abel
    rw [h]; exact K.sub_mem hy hx.mem
  obtain ⟨d, hdK, rfl⟩ : ∃ d, d ∈ K ∧ y = x + d := ⟨y - x, hd, by abel⟩
  have hbd : inner 𝕜 (b - A x) d = (0 : 𝕜) :=
    inner_eq_zero_symm.1 (hx.inner_residual_eq_zero hdK)
  have hbd' : RCLike.re (inner 𝕜 b d) = RCLike.re (inner 𝕜 (A x) d) := by
    rw [inner_sub_left, sub_eq_zero] at hbd
    rw [hbd]
  have hsymd : RCLike.re (inner 𝕜 (A d) x) = RCLike.re (inner 𝕜 (A x) d) := by
    rw [hA.isSymmetric d x, ← inner_conj_symm]
    exact RCLike.conj_re _
  obtain ⟨c, hc, hAc⟩ := hA.isCoercive
  have hpos : 0 ≤ RCLike.re (inner 𝕜 (A d) d) :=
    le_trans (by positivity) (hAc d)
  simp only [map_add, inner_add_left, inner_add_right]
  rw [hsymd, hbd']
  linarith

/-- Let $A$ be symmetric coercive and let $x$ satisfy the Galerkin condition for $(A, b, x_0, K)$.
Then $\varphi(x) \le \varphi(y)$ for every $y \in x_0 + K$, where $\varphi$ is the energy
functional `energyFunctional A b`. This is `IsGalerkin.quadratic_le` in terms of $\varphi$. -/
theorem energyFunctional_le (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x) {y : E}
    (hy : y - x₀ ∈ K) : energyFunctional A b x ≤ energyFunctional A b y :=
  hx.quadratic_le hA hy

/-- **The Galerkin error as a projection** ([saad2003iterative], Proposition 5.5). Let $A$ be
symmetric coercive, let $K$ be finite-dimensional, let $x$ satisfy the Galerkin condition for
$(A, b, x_0, K)$, and let $Ax^* = b$. Then the error $x^* - x$ is the projection of the initial
error $d_0 = x^* - x_0$, orthogonal in the energy inner product, onto the energy-orthogonal
complement of $K$.

The space $E$ with the energy inner product is `WithEnergy A hA`, reached through
`WithEnergy.equiv A hA`, and $K$ in that space is `WithEnergy.submoduleMap A hA K`. -/
theorem error_eq_starProjection (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) [FiniteDimensional 𝕜 K] :
    WithEnergy.equiv A hA (xstar - x) =
      (WithEnergy.submoduleMap A hA K)ᗮ.starProjection (WithEnergy.equiv A hA (xstar - x₀)) := by
  have hM : WithEnergy.submoduleMap A hA K = K.map (WithEnergy.equiv A hA).toLinearMap := rfl
  have hmem : WithEnergy.equiv A hA (xstar - x) ∈ (WithEnergy.submoduleMap A hA K)ᗮ := by
    refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
    rw [hM] at hu
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hu
    have hzero : inner 𝕜 (A (xstar - x)) z = (0 : 𝕜) :=
      energyInner_error_eq_zero hx hstar hz
    have hgoal : inner 𝕜 (A z) (xstar - x) = (0 : 𝕜) := by
      rw [hA.isSymmetric z (xstar - x), ← inner_conj_symm, hzero, map_zero]
    exact hgoal
  have hdiff : WithEnergy.equiv A hA (xstar - x₀) - WithEnergy.equiv A hA (xstar - x)
      ∈ (WithEnergy.submoduleMap A hA K)ᗮᗮ := by
    have h : WithEnergy.equiv A hA (xstar - x₀) - WithEnergy.equiv A hA (xstar - x)
        = WithEnergy.equiv A hA (x - x₀) := by
      rw [← map_sub]; congr 1; abel
    rw [h]
    exact Submodule.le_orthogonal_orthogonal _
      ((WithEnergy.equiv_mem_submoduleMap_iff A hA).2 hx.mem)
  exact (Submodule.eq_starProjection_of_mem_orthogonal hmem hdiff).symm

end IsGalerkin

/-!
### Optimality along a direction

[quarteroni2000numerical] Definition 4.4 calls $x$ *optimal with respect to a direction $p$* when
$\varphi(x) \le \varphi(x + \lambda p)$ for every real $\lambda$, where $\varphi$ is the energy
functional, and *optimal with respect to a subspace* when it is optimal with respect to every
direction in it. The two displays after the definition show that optimality along $p$ is
$\langle r, p \rangle = 0$ for the residual $r = b - Ax$. The proof of Theorem 4.11 uses that
optimality with respect to $\operatorname{span}\{p_0, \dots, p_{k-1}\}$ is the Galerkin condition.
Over $\mathbb{C}$ a real parameter detects only the real part of $\langle r, p \rangle$, so the
statements come in a form with a real parameter and a form with a $\mathbb{K}$-valued parameter.
-/

/-- **The energy functional along a line.** Let $A$ be symmetric, and let $\varphi$ be the energy
functional. For $x, p \in E$, $t \in \mathbb{K}$ and $r = b - Ax$,
$$\varphi(x + tp) = \varphi(x) - \operatorname{Re}\bigl(t \langle r, p \rangle\bigr) + \tfrac12
  |t|^2 \operatorname{Re}\langle Ap, p \rangle.$$
-/
theorem energyFunctional_add_smul (hA : A.IsSymmetric) (b x p : E) (t : 𝕜) :
    energyFunctional A b (x + t • p)
      = energyFunctional A b x - RCLike.re (t * inner 𝕜 (b - A x) p)
        + ‖t‖ ^ 2 * RCLike.re (inner 𝕜 (A p) p) / 2 := by
  rw [hA.energyFunctional_add]
  simp only [map_smul, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul,
    show A x - b = -(b - A x) by abel, inner_neg_left, mul_neg, map_neg]
  ring

/-- **Optimality along a direction**, form with a $\mathbb{K}$-valued parameter
([quarteroni2000numerical], the displays after Definition 4.4). Let $A$ be symmetric, and let
$p \in E$ satisfy $\operatorname{Re}\langle Ap, p \rangle \ge 0$; this holds for every $p$ when
$A$ is symmetric coercive. Let $\varphi$ be the energy functional and $r = b - Ax$. Then
$\langle r, p \rangle = 0$ if and only if
$$\varphi(x) \le \varphi(x + tp) \quad\text{for every } t \in \mathbb{K}.$$

The function $t \mapsto \varphi(x + tp) - \varphi(x) = -\operatorname{Re}(t \langle r, p
\rangle) + \tfrac12 |t|^2 \operatorname{Re}\langle Ap, p \rangle$ is nonnegative for all $t$ if
and only if its linear coefficient vanishes. Only the implication from
$\langle r, p \rangle = 0$ to minimality needs the sign condition on
$\operatorname{Re}\langle Ap, p \rangle$: if $\langle r, p \rangle \neq 0$, a small multiple of
$\overline{\langle r, p \rangle}$ as $t$ makes the function negative for every value of
$\operatorname{Re}\langle Ap, p \rangle$. The Lean statement assumes the sign condition for both
directions. -/
theorem inner_residual_eq_zero_iff_forall_quadratic_add_smul_le (hA : A.IsSymmetric) {p : E}
    (hp : 0 ≤ RCLike.re (inner 𝕜 (A p) p)) (b x : E) :
    inner 𝕜 (b - A x) p = 0 ↔
      ∀ t : 𝕜, energyFunctional A b x ≤ energyFunctional A b (x + t • p) := by
  refine ⟨fun h t => ?_, fun h => ?_⟩
  · rw [energyFunctional_add_smul hA, h, mul_zero, map_zero, sub_zero]
    have : 0 ≤ ‖t‖ ^ 2 * RCLike.re (inner 𝕜 (A p) p) / 2 := by positivity
    linarith
  · set c := inner 𝕜 (b - A x) p with hc
    set q := RCLike.re (inner 𝕜 (A p) p) with hq
    set s : ℝ := q + 1 with hs
    have hspos : 0 < s := by linarith
    have ht := h (((s⁻¹ : ℝ) : 𝕜) * (starRingEnd 𝕜) c)
    rw [energyFunctional_add_smul hA, ← hc, ← hq, mul_assoc, RCLike.conj_mul, ← RCLike.ofReal_pow,
      ← RCLike.ofReal_mul, RCLike.ofReal_re, norm_mul, RCLike.norm_ofReal, RCLike.norm_conj,
      abs_of_pos (inv_pos.2 hspos)] at ht
    have hkey : ‖c‖ ^ 2 * (q / 2 + 1) ≤ 0 := by
      have h2 : ‖c‖ ^ 2 * (q / 2 + 1)
          = -(s ^ 2) * (- (s⁻¹ * ‖c‖ ^ 2) + (s⁻¹ * ‖c‖) ^ 2 * q / 2) := by
        rw [hs]; field_simp; ring
      rw [h2]
      exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)
    have hc0 : ‖c‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖c‖]
    have : ‖c‖ = 0 := by nlinarith [norm_nonneg c]
    exact norm_eq_zero.1 this

/-- **Optimality along a direction**, form with a real parameter ([quarteroni2000numerical]
Definition 4.4 and the displays after it). Let $A$ be symmetric, and let $p \in E$ satisfy
$\operatorname{Re}\langle Ap, p \rangle \ge 0$. Let $\varphi$ be the energy functional and
$r = b - Ax$. Then $\operatorname{Re}\langle r, p \rangle = 0$ if and only if
$$\varphi(x) \le \varphi(x + \lambda p) \quad\text{for every } \lambda \in \mathbb{R}.$$

Over $\mathbb{R}$ this is `inner_residual_eq_zero_iff_forall_quadratic_add_smul_le`. Over
$\mathbb{C}$ a real parameter constrains only the real part of $\langle r, p \rangle$. -/
theorem re_inner_residual_eq_zero_iff_forall_quadratic_add_real_smul_le (hA : A.IsSymmetric)
    {p : E} (hp : 0 ≤ RCLike.re (inner 𝕜 (A p) p)) (b x : E) :
    RCLike.re (inner 𝕜 (b - A x) p) = 0 ↔
      ∀ t : ℝ, energyFunctional A b x ≤ energyFunctional A b (x + (t : 𝕜) • p) := by
  have hexp : ∀ t : ℝ, energyFunctional A b (x + (t : 𝕜) • p)
      = energyFunctional A b x - t * RCLike.re (inner 𝕜 (b - A x) p)
        + t ^ 2 * RCLike.re (inner 𝕜 (A p) p) / 2 := by
    intro t
    rw [energyFunctional_add_smul hA, RCLike.re_ofReal_mul, RCLike.norm_ofReal, sq_abs]
  refine ⟨fun h t => ?_, fun h => ?_⟩
  · rw [hexp, h, mul_zero, sub_zero]
    have : 0 ≤ t ^ 2 * RCLike.re (inner 𝕜 (A p) p) / 2 := by positivity
    linarith
  · set c := RCLike.re (inner 𝕜 (b - A x) p) with hc
    set q := RCLike.re (inner 𝕜 (A p) p) with hq
    set s : ℝ := q + 1 with hs
    have ht := h (s⁻¹ * c)
    rw [hexp] at ht
    have hkey : c ^ 2 * (q / 2 + 1) ≤ 0 := by
      have h2 : c ^ 2 * (q / 2 + 1) = -(s ^ 2) * (- (s⁻¹ * c * c) + (s⁻¹ * c) ^ 2 * q / 2) := by
        rw [hs]; field_simp; ring
      rw [h2]
      exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)
    have : c ^ 2 ≤ 0 := by nlinarith [sq_nonneg c]
    exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg c))

/-- **Galerkin iterates are the minimizers of the energy functional** ([fong2012cg], (2.1);
[quarteroni2000numerical] Definition 4.4, "optimal with respect to a subspace", as used in the
proof of Theorem 4.11). Let $A$ be symmetric coercive, let $\varphi$ be the energy functional,
and let $x \in x_0 + K$. Then $x$ satisfies the Galerkin condition for $(A, b, x_0, K)$ if and
only if
$$\varphi(x) \le \varphi(y) \quad\text{for every } y \in x_0 + K.$$

This is the converse of `IsGalerkin.quadratic_le`. By
`LinearMap.IsSymmetricCoercive.energyFunctional_sub_eq` ([quarteroni2000numerical] (4.35)),
minimizing $\varphi$ is minimizing the energy norm of the error, which is
`IsGalerkin.iff_energyNorm_min`. No finite dimension is needed: the backward direction tests the
minimality along each direction of $K$ with
`inner_residual_eq_zero_iff_forall_quadratic_add_smul_le`. -/
theorem isGalerkin_iff_forall_quadratic_le (hA : A.IsSymmetricCoercive) (hx : x - x₀ ∈ K) :
    IsGalerkin A b x₀ K x ↔
      ∀ y, y - x₀ ∈ K → energyFunctional A b x ≤ energyFunctional A b y := by
  refine ⟨fun h y hy => h.energyFunctional_le hA hy, fun h => ⟨hx, ?_⟩⟩
  refine (Submodule.mem_orthogonal' _ _).2 fun p hp => ?_
  refine (inner_residual_eq_zero_iff_forall_quadratic_add_smul_le hA.isSymmetric
    (hA.isPositive.re_inner_nonneg_left p) b x).2 fun t => h _ ?_
  rw [add_sub_right_comm]
  exact K.add_mem hx (K.smul_mem t hp)

namespace IsMinError

/-- **Monotonicity on nested subspaces.** Let $K \subseteq K'$, and let $x$ and $x'$ satisfy the
minimal-error condition for $(x^*, x_0, K)$ and $(x^*, x_0, K')$. Then
$\|x^* - x'\| \le \|x^* - x\|$. -/
theorem norm_error_le_of_le {K' : Submodule 𝕜 E} {x' : E} (hx : IsMinError xstar x₀ K x)
    (hx' : IsMinError xstar x₀ K' x') (hKK' : K ≤ K') : ‖xstar - x'‖ ≤ ‖xstar - x‖ :=
  hx'.min x (hKK' hx.mem)

/-- If $x$ satisfies the minimal-error condition for $(x^*, x_0, K)$, then the error $x^* - x$ is
orthogonal to $K$. -/
theorem sub_mem_orthogonal (hx : IsMinError xstar x₀ K x) : xstar - x ∈ Kᗮ := by
  refine (Submodule.mem_orthogonal' _ _).2 fun w hw => ?_
  have h1 : xstar - x = (xstar - x₀) - (x - x₀) := by abel
  rw [h1]
  refine Submodule.inner_eq_zero_of_forall_norm_sub_le hx.mem (fun z hz => ?_) hw
  have h2 := hx.min (x₀ + z) (by simpa using hz)
  rwa [show xstar - (x₀ + z) = (xstar - x₀) - z by abel, h1] at h2

/-- Let $K$ have an orthogonal projection $P_K$. If $x$ satisfies the minimal-error condition for
$(x^*, x_0, K)$, then $x - x_0 = P_K(x^* - x_0)$. So $x$ is the orthogonal projection of $x^*$
onto the affine space $x_0 + K$. -/
theorem eq_starProjection [K.HasOrthogonalProjection] (hx : IsMinError xstar x₀ K x) :
    x - x₀ = K.starProjection (xstar - x₀) := by
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hx.mem fun w hw => ?_).symm
  rw [show (xstar - x₀) - (x - x₀) = xstar - x by abel]
  exact (Submodule.mem_orthogonal' _ _).1 hx.sub_mem_orthogonal w hw

/-- **Uniqueness of the minimal-error iterate.** If $x$ and $x'$ both satisfy the minimal-error
condition for $(x^*, x_0, K)$, then $x = x'$. There is no hypothesis on $K$ or on the dimension.

The midpoint of two minimizers also lies in $x_0 + K$, and the parallelogram law with its
optimality gives $x = x'$. In contrast, minimal-residual iterates are unique only when $A$ is
injective on $K$ (`existsUnique_isMinResidual_of_injOn`), although their residual is always
unique. -/
theorem unique {x' : E} (hx : IsMinError xstar x₀ K x) (hx' : IsMinError xstar x₀ K x') :
    x = x' := by
  have hmem : (x₀ + (2 : 𝕜)⁻¹ • ((x - x₀) + (x' - x₀))) - x₀ ∈ K := by
    rw [add_sub_cancel_left]
    exact K.smul_mem _ (K.add_mem hx.mem hx'.mem)
  have hd : ‖xstar - x‖ = ‖xstar - x'‖ := le_antisymm (hx.min x' hx'.mem) (hx'.min x hx.mem)
  have hsplit : (xstar - x) + (xstar - x')
      = (2 : 𝕜) • (xstar - (x₀ + (2 : 𝕜)⁻¹ • ((x - x₀) + (x' - x₀)))) := by
    match_scalars <;> norm_num
  have hnorm : ‖(xstar - x) + (xstar - x')‖ = 2 * ‖xstar - (x₀ + (2 : 𝕜)⁻¹ •
      ((x - x₀) + (x' - x₀)))‖ := by
    rw [hsplit, norm_smul, RCLike.norm_two]
  have hge : ‖xstar - x‖ ≤ ‖xstar - (x₀ + (2 : 𝕜)⁻¹ • ((x - x₀) + (x' - x₀)))‖ :=
    hx.min _ hmem
  have hpar := parallelogram_law_with_norm 𝕜 (xstar - x) (xstar - x')
  rw [show (xstar - x) - (xstar - x') = x' - x by abel] at hpar
  have hx'x : ‖x' - x‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg (x' - x), norm_nonneg (xstar - x)]
  have : ‖x' - x‖ = 0 := by nlinarith [norm_nonneg (x' - x)]
  exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm

/-- **Minimal error as a Petrov–Galerkin method** ([saad2003iterative], §8.3, and
[choi2006iterative]). Let $E$ and $F$ be finite-dimensional, let $A : E \to F$ be linear, let
$L \subseteq F$ be a subspace, and let $K = A^H L$. If $Ax^* = b$ and $x$ satisfies the
minimal-error condition for $(x^*, x_0, K)$, then $x$ satisfies the Petrov–Galerkin condition
for $(A, b, x_0, K, L)$.

This describes CGNE (Craig's method) as a Petrov–Galerkin method. The adjoint $A^H$ is
`LinearMap.adjoint A`. -/
theorem isPetrovGalerkin_of_map_adjoint {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] {A : E →ₗ[𝕜] F} {b : F} {L : Submodule 𝕜 F}
    (hK : K = L.map (LinearMap.adjoint A)) (hstar : A xstar = b) (hx : IsMinError xstar x₀ K x) :
    IsPetrovGalerkin A b x₀ K L x := by
  refine ⟨hx.mem, (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
  have h1 : b - A x = A (xstar - x) := by rw [map_sub, hstar]
  rw [h1, ← LinearMap.adjoint_inner_left]
  refine (Submodule.mem_orthogonal _ _).1 hx.sub_mem_orthogonal _ ?_
  rw [hK]
  exact Submodule.mem_map_of_mem hw

end IsMinError
