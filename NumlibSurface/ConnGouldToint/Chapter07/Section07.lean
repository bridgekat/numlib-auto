/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin
import NumlibSurface.ConnGouldToint.Chapter07.Section03Algorithms

/-!
# Conn, Gould and Toint, Section 7.7: The diagonal trust-region Newton iteration

Section 7.7 of [conn2000trust] uses a symmetric indefinite factorization of the Hessian, with a
permutation $P$, a triangular factor $L$ and a block diagonal factor, to define the trust-region
norm of the modified absolute-value preconditioner $P L C L^T P^T$ of (7.7.12), where $C$ is the
modified block diagonal. In the coordinates of this factorization the model Hessian becomes
diagonal, as in (7.7.14), and Algorithm 7.7.1 solves the trust-region subproblem for a diagonal
Hessian $D = \operatorname{diag}(d_0, \dots, d_n)$ on $\mathbb{R}^{n+1}$ by coordinate division.
This module defines the preconditioner, the coordinate pseudoinverse $(D + xI)^+$ and the scalar
Newton update of Algorithm 7.7.1, and the algorithm itself. It proves that the coordinate solves and
the Newton update agree with the Moré–Sorensen quantities of Section 7.3 above the pole, that the
Newton iteration converges Q-linearly and with Q-order two from an exterior compatible start, and
that the algorithm returns either an exact minimizer or a step that passes the relative radius test.

## Main definitions

* Equation (7.7.12), `ConnGouldToint.Chapter07.modifiedAbsoluteValuePreconditioner`: the matrix
  $P L C L^T P^T$.
* Algorithm 7.7.1, `ConnGouldToint.Chapter07.diagonalShiftInverse`: the coordinate pseudoinverse
  $(D + xI)^+$.
* Algorithm 7.7.1, Step 2, `ConnGouldToint.Chapter07.diagonalNullGradient`: the part of $g$ on the
  coordinates with $d_i + x = 0$.
* Algorithm 7.7.1, Steps 4–5, `ConnGouldToint.Chapter07.diagonalNewtonStep`: the scalar Newton
  update of the shift.
* Algorithm 7.7.1, `ConnGouldToint.Chapter07.algorithm_7_7_1`: the algorithm with a supplied index
  of a least diagonal entry.
* Equation (7.7.14), `ConnGouldToint.Chapter07.diagonalOperator`: the diagonal Hessian $D$ as an
  operator.
* Algorithm 7.7.1, `ConnGouldToint.Chapter07.algorithm_7_7_1_auto`: the algorithm with an
  automatically chosen least diagonal entry.

## Main results

* Equation (7.7.12), `ConnGouldToint.Chapter07.modifiedAbsoluteValuePreconditioner_posDef`: the
  preconditioner is positive definite when $P$ and $L$ are invertible and $C$ is positive definite.
* Equation (7.7.14), `ConnGouldToint.Chapter07.diagonalOperator_symm`: the diagonal Hessian is
  symmetric.
* Algorithm 7.7.1, Step 2, `ConnGouldToint.Chapter07.diagonal_leftmost`: the least eigenvalue of $D$
  is its least diagonal entry.
* Algorithm 7.7.1, Steps 1, 2 and 5, `ConnGouldToint.Chapter07.diagonalShiftStep_solves`: the
  coordinate solve solves a compatible shifted system.
* Algorithm 7.7.1, `ConnGouldToint.Chapter07.diagonalShiftStep_eq`: above the pole the coordinate
  solve is the shifted step $s(x)$.
* Algorithm 7.7.1, Step 4, `ConnGouldToint.Chapter07.diagonalNewtonStep_eq`: above the pole the
  update is Newton's method on the Moré–Sorensen secular function.
* Algorithm 7.7.1, `ConnGouldToint.Chapter07.algorithm_7_7_1_newton_converges`: from an exterior
  compatible start, the Newton shifts converge Q-linearly and with Q-order two, and
  $\|s(x_k)\| \to \Delta$.
* Algorithm 7.7.1, Steps 3–5, `ConnGouldToint.Chapter07.algorithm_7_7_1_newton_stop`: the relative
  radius test is met after finitely many Newton steps.
* Algorithm 7.7.1, Step 2b, `ConnGouldToint.Chapter07.algorithm_7_7_1_seed_norm`: the starting trial
  of the singular case lies outside or on the boundary.
* Algorithm 7.7.1, `ConnGouldToint.Chapter07.algorithm_7_7_1_returns`: the algorithm returns an
  exact minimizer or a step that passes the relative radius test.
* Algorithm 7.7.1, `ConnGouldToint.Chapter07.algorithm_7_7_1_auto_returns`: the same guarantee with
  the automatic choice of the least diagonal entry.

## Conventions

* Vectors are elements of `EuclideanSpace ℝ (Fin (n + 1))`, with coordinates indexed from $0$, and
  the diagonal Hessian is given by its diagonal $d$.
* The model is $m(s) = \langle g, s \rangle + \frac{1}{2} \langle s, D s \rangle$, which is
  `Subproblem.quadModel g (diagonalOperator d)`.

## Implementation notes

* The coordinate pseudoinverse divides by $d_i + x$ in every coordinate. Division by zero gives
  zero, so a coordinate with $d_i + x = 0$ contributes $0$.
* The algorithm returns `Option V`. The value `none` occurs only if no Newton iterate passes the
  relative radius test, which `ConnGouldToint.Chapter07.algorithm_7_7_1_returns` excludes.
-/

namespace ConnGouldToint.Chapter07

open Matrix Subproblem WithLp Filter
open scoped RealInnerProductSpace Topology

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

/-- **Equation (7.7.12)** of [conn2000trust]. For matrices $P$, $L$ and $C$, the **modified
absolute-value preconditioner** is
$$P L C L^T P^T.$$

Here $P$ is the permutation, $L$ the triangular factor and $C$ the modified block diagonal of
the factorization of the Hessian. -/
def modifiedAbsoluteValuePreconditioner {ι : Type*} [Fintype ι]
    (P L C : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  P * L * C * Lᵀ * Pᵀ

/-- **Equation (7.7.12)** of [conn2000trust], positive definite metric. If $P$ and $L$ are
invertible and $C$ is positive definite, then $P L C L^T P^T$ is positive definite. -/
theorem modifiedAbsoluteValuePreconditioner_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P L C : Matrix ι ι ℝ} (hP : IsUnit P) (hL : IsUnit L) (hC : C.PosDef) :
    (modifiedAbsoluteValuePreconditioner P L C).PosDef := by
  have h := hC.mul_mul_conjTranspose_same (B := P * L)
    (Matrix.vecMul_injective_iff_isUnit.mpr (hP.mul hL))
  simpa only [modifiedAbsoluteValuePreconditioner, conjTranspose_eq_transpose_of_trivial,
    transpose_mul, Matrix.mul_assoc] using h

/-- **Algorithm 7.7.1** of [conn2000trust], coordinate pseudoinverse. For $d \in \mathbb{R}^{n+1}$,
$x \in \mathbb{R}$ and $v \in \mathbb{R}^{n+1}$,
$$\big((D + xI)^+ v\big)_i = \frac{v_i}{d_i + x},$$
where $D = \operatorname{diag}(d)$, with value $0$ in every coordinate where $d_i + x = 0$. -/
noncomputable def diagonalShiftInverse (d : Fin (n + 1) → ℝ) (x : ℝ) (v : V) : V :=
  toLp 2 (fun i => v i / (d i + x))

/-- **Algorithm 7.7.1** of [conn2000trust], Step 2. For $d, g \in \mathbb{R}^{n+1}$ and
$x \in \mathbb{R}$, the **null gradient** $g^0$ keeps the coordinates of $g$ where the shifted
diagonal vanishes:
$$g^0_i = \begin{cases} g_i & \text{if } d_i + x = 0, \\ 0 & \text{otherwise.} \end{cases}$$
-/
noncomputable def diagonalNullGradient (d : Fin (n + 1) → ℝ) (x : ℝ) (g : V) : V :=
  toLp 2 (fun i => if d i + x = 0 then g i else 0)

/-- **Algorithm 7.7.1** of [conn2000trust], Steps 4–5. For $d, g \in \mathbb{R}^{n+1}$ and
$\Delta, x \in \mathbb{R}$, let $s = -(D + xI)^+ g$. The **Newton update** of the shift is
$$x + \frac{\|s\| - \Delta}{\Delta} \cdot \frac{\|s\|^2}{\langle s, (D + xI)^+ s \rangle}.$$
-/
noncomputable def diagonalNewtonStep (d : Fin (n + 1) → ℝ) (g : V) (Δ x : ℝ) : ℝ :=
  let s := -diagonalShiftInverse d x g
  x + ((‖s‖ - Δ) / Δ) * (‖s‖ ^ 2 / ⟪s, diagonalShiftInverse d x s⟫)

/-- **Algorithm 7.7.1** of [conn2000trust]. Let $d, g \in \mathbb{R}^{n+1}$,
$\Delta, \varepsilon \in \mathbb{R}$, and let $i_0$ be an index, intended to satisfy
$d_{i_0} = \min_i d_i$. Put $D = \operatorname{diag}(d)$, $s_0 = -D^+ g$, the pole
$\lambda = -d_{i_0}$, the null gradient $g^0$ at $\lambda$, and $p = -(D + \lambda I)^+ g$. The
algorithm returns:

* $s_0$, if $d_{i_0} > 0$ and $\|s_0\| \le \Delta$;
* otherwise $p + \alpha e_{i_0}$ with $\alpha = \sqrt{\Delta^2 - \|p\|^2 + p_{i_0}^2} -
  p_{i_0}$, if $d_{i_0} \le 0$, $g^0 = 0$ and $\|p\| \le \Delta$;
* otherwise the step $s_k = -(D + x_k I)^+ g$ for the first $k$ with
  $|\|s_k\| - \Delta| \le \varepsilon \Delta$, where $x_k$ is the $k$-th Newton update from
  $x_0 = 0$ if $d_{i_0} > 0$ and from $x_0 = \lambda + \|g^0\| / \Delta$ otherwise, and nothing
  if no such $k$ exists.

If the unshifted matrix is positive definite and its trial lies outside the trust region, Newton
starts at $x_0 = 0$. In the singular compatible boundary case both roots of
$\|p + \alpha e_{i_0}\| = \Delta$ give the same model value, so the positive square root is
used; the coefficient is `ConnGouldToint.Chapter07.moreSorensenBoundaryCoefficient`. -/
noncomputable def algorithm_7_7_1 (d : Fin (n + 1) → ℝ) (g : V) (Δ ε : ℝ)
    (i₀ : Fin (n + 1)) : Option V := by
  classical
  exact
    let s₀ := -diagonalShiftInverse d 0 g
    let pole := -d i₀
    let gn := diagonalNullGradient d pole g
    let p := -diagonalShiftInverse d pole g
    if 0 < d i₀ ∧ ‖s₀‖ ≤ Δ then some s₀
    else if d i₀ ≤ 0 ∧ gn = 0 ∧ ‖p‖ ≤ Δ then
      let u : V := toLp 2 (Pi.single i₀ 1)
      some (p + moreSorensenBoundaryCoefficient Δ p u • u)
    else
      let x₀ := if 0 < d i₀ then 0 else pole + ‖gn‖ / Δ
      let s := fun k : ℕ => -diagonalShiftInverse d ((diagonalNewtonStep d g Δ)^[k] x₀) g
      if h : ∃ k, |‖s k‖ - Δ| ≤ ε * Δ then some (s (Nat.find h)) else none

/-- **Equation (7.7.14)** of [conn2000trust], diagonal Hessian. For $d \in \mathbb{R}^{n+1}$, this
is the operator of the diagonal matrix $D = \operatorname{diag}(d)$ on the Euclidean space
$\mathbb{R}^{n+1}$. -/
noncomputable def diagonalOperator (d : Fin (n + 1) → ℝ) : V →L[ℝ] V :=
  toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ) (diagonal d)

/-- **Equation (7.7.14)** of [conn2000trust], symmetry. The diagonal operator
$D = \operatorname{diag}(d)$ is symmetric. -/
theorem diagonalOperator_symm (d : Fin (n + 1) → ℝ) :
    ((diagonalOperator d : V →L[ℝ] V) : V →ₗ[ℝ] V).IsSymmetric :=
  (isSymm_diagonal d).isSymmetric_toEuclideanLin

private theorem diagonalOperator_apply (d : Fin (n + 1) → ℝ) (v : V) (i : Fin (n + 1)) :
    (diagonalOperator d v) i = d i * v i := by
  change ((diagonal d) *ᵥ ofLp v) i = _
  rw [Matrix.mulVec_diagonal]

private theorem diagonalInner (d : Fin (n + 1) → ℝ) (v : V) :
    ⟪v, diagonalOperator d v⟫ = ∑ i, d i * (v i)^2 := by
  rw [← WithLp.toLp_ofLp 2 v, ← WithLp.toLp_ofLp 2 (diagonalOperator d v)]
  rw [EuclideanSpace.inner_toLp_toLp_real]
  change (∑ i, v i * (diagonalOperator d v) i) = ∑ i, d i * (v i)^2
  exact Finset.sum_congr rfl fun i _ => by rw [diagonalOperator_apply]; ring

private theorem leftmost_le_diagonal (d : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    leftmost (diagonalOperator_symm d) ≤ d i := by
  let u : V := toLp 2 (Pi.single i 1)
  have hu : ‖u‖ = 1 := by simp [u]
  have h := leftmost_mul_norm_sq_le (hH := diagonalOperator_symm d) u
  rw [hu, one_pow, mul_one, diagonalInner] at h
  simpa [u, Pi.single_apply] using h

/-- **Algorithm 7.7.1** of [conn2000trust], Step 2, least eigenvalue. If $d_{i_0} \le d_i$ for every
$i$, then the least eigenvalue of $D = \operatorname{diag}(d)$ is $d_{i_0}$.

The least eigenvalue is `Subproblem.leftmost (diagonalOperator_symm d)`. -/
theorem diagonal_leftmost (d : Fin (n + 1) → ℝ) (i₀ : Fin (n + 1))
    (hi : ∀ i, d i₀ ≤ d i) :
    leftmost (diagonalOperator_symm d) = d i₀ := by
  have hlo : d i₀ ≤ leftmost (diagonalOperator_symm d) := by
    apply (le_leftmost_iff_forall (hH := diagonalOperator_symm d)).2
    intro v
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, diagonalInner]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hi i) (sq_nonneg _)
  exact le_antisymm (leftmost_le_diagonal d i₀) hlo

/-- **Algorithm 7.7.1** of [conn2000trust], Steps 1, 2 and 5, coordinate shifted solve. Let
$d, g \in \mathbb{R}^{n+1}$ and $x \in \mathbb{R}$, and assume $g_i = 0$ whenever $d_i + x = 0$.
Then
$$(D + xI)\big(-(D + xI)^+ g\big) = -g.$$
-/
theorem diagonalShiftStep_solves (d : Fin (n + 1) → ℝ) (g : V) (x : ℝ)
    (hg : ∀ i, d i + x = 0 → g i = 0) :
    (diagonalOperator d + x • 1) (-diagonalShiftInverse d x g) = -g := by
  ext i
  change (diagonalOperator d (-diagonalShiftInverse d x g)) i +
    x * (-diagonalShiftInverse d x g) i = -g i
  rw [diagonalOperator_apply]
  change d i * (-(g i / (d i + x))) + x * (-(g i / (d i + x))) = -g i
  by_cases hz : d i + x = 0
  · simp [hz, hg i hz]
  · calc
      _ = -((g i / (d i + x)) * (d i + x)) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hz]

/-- **Algorithm 7.7.1** of [conn2000trust], shifted step above the pole. Let $\lambda_1$ be the
least eigenvalue of $D = \operatorname{diag}(d)$, and let $x > -\lambda_1$ with $d_i + x \neq 0$
for every $i$. Then
$$-(D + xI)^+ g = s(x) = -(D + xI)^{-1} g.$$

The step $s(x)$ is `ConnGouldToint.Chapter07.shiftedStep`. -/
theorem diagonalShiftStep_eq (d : Fin (n + 1) → ℝ) (g : V) {x : ℝ}
    (hx : -leftmost (diagonalOperator_symm d) < x)
    (hd : ∀ i, d i + x ≠ 0) :
    -diagonalShiftInverse d x g = shiftedStep g (diagonalOperator d) x :=
  (step_spec (hH := diagonalOperator_symm d) hx).2 _
    (diagonalShiftStep_solves d g x (fun i h => (hd i h).elim))

/-- **Algorithm 7.7.1** of [conn2000trust], Step 4, equivalence to secular Newton. Let $g \neq 0$,
$\Delta > 0$, let $\lambda_1$ be the least eigenvalue of $D = \operatorname{diag}(d)$, and let
$x > -\lambda_1$ with $d_i + x \neq 0$ for every $i$. Then the Newton update of the shift equals
one Newton step at $x$ for the Moré–Sorensen secular function
$$\phi(x) = \frac{1}{\|s(x)\|} - \frac{1}{\Delta}.$$

The denominator of the Newton step is evaluated by diagonal division. The Newton step is
`ConnGouldToint.Chapter07.moreSorensenNewtonStep`. -/
theorem diagonalNewtonStep_eq (d : Fin (n + 1) → ℝ) {g : V} (hg : g ≠ 0) {Δ x : ℝ}
    (hΔ : 0 < Δ) (hx : -leftmost (diagonalOperator_symm d) < x)
    (hd : ∀ i, d i + x ≠ 0) :
    diagonalNewtonStep d g Δ x = moreSorensenNewtonStep g (diagonalOperator d) Δ x := by
  let H := diagonalOperator d
  let s := shiftedStep g H x
  let z := Ring.inverse (H + x • 1) s
  have hsolve := diagonalShiftStep_eq d g hx hd
  have hzinv : diagonalShiftInverse d x s = z := by
    apply injective_add_smul (hH := diagonalOperator_symm d) hx
    have hn : -diagonalShiftInverse d x (-s) = diagonalShiftInverse d x s := by
      ext i
      change -(-s i / (d i + x)) = s i / (d i + x)
      rw [neg_div, neg_neg]
    have hsol := diagonalShiftStep_solves d (-s) x (fun i h => (hd i h).elim)
    rw [hn, neg_neg] at hsol
    exact hsol.trans (add_smul_inverse_apply hx s).symm
  have hder := ((lemma_7_3_1 (hH := diagonalOperator_symm d) hg Δ).2.2 x hx).2.1
  change deriv (phi g H Δ) x = -⟪s, -z⟫ / ‖s‖ ^ 3 at hder
  rw [inner_neg_right, neg_neg] at hder
  have hnorm : ‖s‖ ≠ 0 := by
    have hp := secular_pos (hH := diagonalOperator_symm d) hg hx
    change 0 < ‖s‖ ^ 2 at hp
    intro h
    simp [h] at hp
  have hden : ⟪s, z⟫ ≠ 0 := by
    have hp := (trSecular_shape (hH := diagonalOperator_symm d) hg Δ
      (β := -1 / 2) (by norm_num)).2.2 x hx
    change 0 < deriv (phi g H Δ) x at hp
    intro h
    rw [hder, h, zero_div] at hp
    exact (lt_irrefl _ hp)
  unfold diagonalNewtonStep
  rw [hsolve]
  change x + ((‖s‖ - Δ) / Δ) * (‖s‖ ^ 2 / ⟪s, diagonalShiftInverse d x s⟫) =
    moreSorensenNewtonStep g H Δ x
  rw [hzinv, moreSorensenNewtonStep, Newton.scalarStep, phi_eq_inv_norm_sub_inv, hder]
  change x + ((‖s‖ - Δ) / Δ) * (‖s‖ ^ 2 / ⟪s, z⟫) =
    x - (1 / ‖s‖ - 1 / Δ) / (⟪s, z⟫ / ‖s‖ ^ 3)
  field_simp [hnorm, hden, hΔ.ne']
  ring

private theorem diagonal_entries_ne_zero (d : Fin (n + 1) → ℝ) {x : ℝ}
    (hx : -leftmost (diagonalOperator_symm d) < x) (i : Fin (n + 1)) : d i + x ≠ 0 := by
  have hh := leftmost_le_diagonal d i
  exact ne_of_gt (by linarith)

private theorem diagonalNewton_open_converges (d : Fin (n + 1) → ℝ) (g : V)
    {Δ x₀ : ℝ} (hΔ : 0 < Δ) (hx₀ : 0 ≤ x₀)
    (hx : -leftmost (diagonalOperator_symm d) < x₀)
    (hraw : Δ < ‖-diagonalShiftInverse d x₀ g‖) :
    let x := fun k : ℕ => (diagonalNewtonStep d g Δ)^[k] x₀
    ∃ r, 0 ≤ r ∧ ConvergesWithOrder x r 2 ∧
      (∃ γ ∈ Set.Ico (0 : ℝ) 1, ∀ k, ‖x (k + 1) - r‖ ≤ γ * ‖x k - r‖) ∧
      Tendsto (fun k => ‖-diagonalShiftInverse d (x k) g‖) atTop (𝓝 Δ) := by
  let H := diagonalOperator d
  have hg : g ≠ 0 := by
    intro h
    rw [h] at hraw
    have hzero : diagonalShiftInverse d x₀ (0 : V) = 0 := by
      ext i
      simp [diagonalShiftInverse]
    simp [hzero, hΔ.not_gt] at hraw
  have hnorm : Δ < ‖shiftedStep g H x₀‖ := by
    rw [← diagonalShiftStep_eq d g hx (diagonal_entries_ne_zero d hx)]
    exact hraw
  have hφ : phi g H Δ x₀ < 0 := by
    rw [phi_eq_inv_norm_sub_inv]
    exact sub_neg.2 (one_div_lt_one_div_of_lt hΔ hnorm)
  obtain ⟨r, ⟨hr, hroot⟩, -⟩ := existsUnique_secular_root_of_phi_neg (hH := diagonalOperator_symm d)
    hg hΔ hx hφ
  have hr0 : 0 ≤ r := by
    have heq : ‖shiftedStep g H r‖ = Δ := by
      change ‖shiftedStep g H r‖ ^ 2 = Δ ^ 2 at hroot
      nlinarith [norm_nonneg (shiftedStep g H r)]
    have hzero : phi g H Δ r = 0 := by rw [phi_eq_inv_norm_sub_inv, heq, sub_self]
    have hm := (trSecular_shape (hH := diagonalOperator_symm d) hg Δ
      (β := -1 / 2) (by norm_num)).2.1
    have hrx : x₀ ≤ r := by
      by_contra! hlt
      exact hφ.not_gt (hzero ▸ hm hr hx hlt)
    exact hx₀.trans hrx
  have hlemma := lemma_7_3_2 (hH := diagonalOperator_symm d) hg hΔ hr hroot hx hφ
  have hgood := hlemma.1
  let f := moreSorensenNewtonStep g H Δ
  have heq (j : ℕ) : (diagonalNewtonStep d g Δ)^[j] x₀ = f^[j] x₀ := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact diagonalNewtonStep_eq d hg hΔ (hgood j).1
        (diagonal_entries_ne_zero d (hgood j).1)
  have hnormlim := (moreSorensen_easy_newton_convergence (hH := diagonalOperator_symm d)
    hg hΔ hr hr0 hroot hx hφ).2.1.norm
  have hnormr : ‖shiftedStep g H r‖ = Δ := by
    change ‖shiftedStep g H r‖ ^ 2 = Δ ^ 2 at hroot
    nlinarith [norm_nonneg (shiftedStep g H r)]
  refine ⟨r, hr0, ?_, ?_, ?_⟩
  · rw [show (fun j => (diagonalNewtonStep d g Δ)^[j] x₀) = (fun j => f^[j] x₀)
      from funext heq]
    exact hlemma.2.2.2.2
  · obtain ⟨hγ, hb, -⟩ := hlemma.2.2
    have hzero : phi g H Δ r = 0 := by rw [phi_eq_inv_norm_sub_inv, hnormr, sub_self]
    have hm := (trSecular_shape (hH := diagonalOperator_symm d) hg Δ
      (β := -1 / 2) (by norm_num)).2.1
    have hbound (j : ℕ) : f^[j] x₀ ≤ r := by
      by_contra! hlt
      exact (hgood j).2.not_gt (hzero ▸ hm hr (hgood j).1 hlt)
    refine ⟨_, hγ, fun k => ?_⟩
    change ‖(diagonalNewtonStep d g Δ)^[k + 1] x₀ - r‖ ≤
      _ * ‖(diagonalNewtonStep d g Δ)^[k] x₀ - r‖
    rw [heq, heq, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (hbound (k + 1))),
      abs_of_nonpos (sub_nonpos.mpr (hbound k)), neg_sub, neg_sub]
    exact hb k
  have ht : Tendsto (fun k => ‖shiftedStep g H (f^[k] x₀)‖) atTop (𝓝 Δ) := hnormr ▸ hnormlim
  exact ht.congr' (Eventually.of_forall fun k => by
    change ‖shiftedStep g H (f^[k] x₀)‖ =
      ‖-diagonalShiftInverse d ((diagonalNewtonStep d g Δ)^[k] x₀) g‖
    rw [heq, diagonalShiftStep_eq d g (hgood k).1 (diagonal_entries_ne_zero d (hgood k).1)])

private theorem diagonalInverse_eq_on_support {d e : Fin (n + 1) → ℝ} (x : ℝ) (g : V)
    (h : ∀ i, g i ≠ 0 → d i = e i) :
    diagonalShiftInverse d x g = diagonalShiftInverse e x g := by
  ext i
  change g i / (d i + x) = g i / (e i + x)
  by_cases hi : g i = 0
  · simp [hi]
  · rw [h i hi]

/-- **Algorithm 7.7.1** of [conn2000trust], convergence of the Newton shifts. Let
$d, g \in \mathbb{R}^{n+1}$, $\Delta > 0$ and $x_0 \ge 0$. Assume $d_i + x_0 \ge 0$ for every
$i$, $g_i = 0$ whenever $d_i + x_0 = 0$, and $\Delta < \|(D + x_0 I)^+ g\|$. Let $x_k$ be the
iterates of the Newton update from $x_0$. Then there is $r \ge 0$ such that $x_k \to r$ with
order $2$, there is $\gamma \in [0, 1)$ with
$$|x_{k+1} - r| \le \gamma |x_k - r| \qquad \text{for all } k,$$
and $\|(D + x_k I)^+ g\| \to \Delta$.

Convergence with order $2$ is `ConvergesWithOrder x r 2`: $x_k \to r$ and eventually
$|x_{k+1} - r| \le C |x_k - r|^2$ for some $C > 0$. At a singular starting shift, the proof
moves the diagonal entries with $d_i + x_0 = 0$ so that $D + x_0 I$ becomes positive definite;
this changes no computed Newton step. -/
theorem algorithm_7_7_1_newton_converges (d : Fin (n + 1) → ℝ) (g : V)
    {Δ x₀ : ℝ} (hΔ : 0 < Δ) (hx₀ : 0 ≤ x₀)
    (hd : ∀ i, 0 ≤ d i + x₀) (hg : ∀ i, d i + x₀ = 0 → g i = 0)
    (hraw : Δ < ‖-diagonalShiftInverse d x₀ g‖) :
    let x := fun k : ℕ => (diagonalNewtonStep d g Δ)^[k] x₀
    ∃ r, 0 ≤ r ∧ ConvergesWithOrder x r 2 ∧
      (∃ γ ∈ Set.Ico (0 : ℝ) 1, ∀ k, ‖x (k + 1) - r‖ ≤ γ * ‖x k - r‖) ∧
      Tendsto (fun k => ‖-diagonalShiftInverse d (x k) g‖) atTop (𝓝 Δ) := by
  let e := fun i => if d i + x₀ = 0 then d i + 1 else d i
  have he (i : Fin (n + 1)) : 0 < e i + x₀ := by
    by_cases hi : d i + x₀ = 0
    · simp only [e, ite_eq_left hi]; linarith
    · simpa only [e, ite_eq_right hi] using lt_of_le_of_ne (hd i) (Ne.symm hi)
  have heq : ∀ x, diagonalShiftInverse d x g = diagonalShiftInverse e x g := fun x =>
    diagonalInverse_eq_on_support x g fun i hi => by
      simp only [e, ite_eq_right (fun hz => hi (hg i hz))]
  have hN : diagonalNewtonStep d g Δ = diagonalNewtonStep e g Δ := by
    funext x
    unfold diagonalNewtonStep
    dsimp only
    rw [← heq x]
    have h := diagonalInverse_eq_on_support (d := d) (e := e) x (-diagonalShiftInverse d x g)
      fun i hi => by
      have hg' : g i ≠ 0 := by
        intro hz
        apply hi
        change -(g i / (d i + x)) = 0
        simp [hz]
      simp only [e, ite_eq_right (fun hz => hg' (hg i hz))]
    rw [h]
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  have hp : -leftmost (diagonalOperator_symm e) < x₀ := by
    rw [diagonal_leftmost e i (fun j => hi j (Finset.mem_univ _))]
    linarith [he i]
  rw [hN]
  simp_rw [heq]
  exact diagonalNewton_open_converges e g hΔ hx₀ hp (by rwa [← heq x₀])

/-- **Algorithm 7.7.1** of [conn2000trust], Steps 3–5, finite stopping. Under the hypotheses of
`ConnGouldToint.Chapter07.algorithm_7_7_1_newton_converges`, and for $\varepsilon > 0$, some
Newton iterate $x_k$ satisfies
$$\big| \|(D + x_k I)^+ g\| - \Delta \big| \le \varepsilon \Delta.$$

This covers a compatible start at the pole. -/
theorem algorithm_7_7_1_newton_stop (d : Fin (n + 1) → ℝ) (g : V)
    {Δ ε x₀ : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε) (hx₀ : 0 ≤ x₀)
    (hd : ∀ i, 0 ≤ d i + x₀) (hg : ∀ i, d i + x₀ = 0 → g i = 0)
    (hraw : Δ < ‖-diagonalShiftInverse d x₀ g‖) :
    ∃ k, |‖-diagonalShiftInverse d ((diagonalNewtonStep d g Δ)^[k] x₀) g‖ - Δ| ≤ ε * Δ := by
  obtain ⟨-, -, -, -, ht⟩ := algorithm_7_7_1_newton_converges d g hΔ hx₀ hd hg hraw
  obtain ⟨k, hk⟩ := (ht.eventually (Metric.ball_mem_nhds Δ (mul_pos hε hΔ))).exists
  exact ⟨k, (by simpa [Metric.mem_ball, Real.dist_eq] using hk : _ < _).le⟩

/-- **Algorithm 7.7.1** of [conn2000trust], Step 2b. Let $d, g \in \mathbb{R}^{n+1}$,
$\lambda \in \mathbb{R}$ and $\Delta > 0$, and let $g^0 \neq 0$ be the null gradient at
$\lambda$. Then the starting shift $x = \lambda + \|g^0\| / \Delta$ satisfies
$$\Delta \le \|(D + xI)^+ g\|.$$

The coordinates where $d_i + \lambda = 0$ alone contribute a vector of norm exactly $\Delta$. -/
theorem algorithm_7_7_1_seed_norm (d : Fin (n + 1) → ℝ) (g : V) {pole Δ : ℝ}
    (hΔ : 0 < Δ) (hgn : diagonalNullGradient d pole g ≠ 0) :
    let x := pole + ‖diagonalNullGradient d pole g‖ / Δ
    Δ ≤ ‖-diagonalShiftInverse d x g‖ := by
  let gn := diagonalNullGradient d pole g
  let t := ‖gn‖ / Δ
  let y := diagonalShiftInverse d (pole + t) g
  have ht : 0 < t := div_pos (norm_pos_iff.mpr hgn) hΔ
  change Δ ≤ ‖-y‖
  rw [norm_neg]
  have hs : ‖gn‖^2 / t^2 ≤ ‖y‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq gn, EuclideanSpace.real_norm_sq_eq y, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : d i + pole = 0
    · change (if d i + pole = 0 then g i else 0)^2 / t^2 ≤ (g i / (d i + (pole + t)))^2
      rw [ite_eq_left hi, show d i + (pole + t) = t by linarith]
      exact (div_pow (g i) t 2).symm.le
    · change (if d i + pole = 0 then g i else 0)^2 / t^2 ≤ (g i / (d i + (pole + t)))^2
      rw [ite_eq_right hi, zero_pow two_ne_zero, zero_div]
      exact sq_nonneg _
  have hq : ‖gn‖^2 / t^2 = Δ^2 := by
    dsimp only [t]
    field_simp [norm_ne_zero_iff.mpr hgn, hΔ.ne']
    exact div_self (norm_ne_zero_iff.mpr hgn)
  rw [hq] at hs
  exact (pow_le_pow_iff_left₀ hΔ.le (norm_nonneg _) two_ne_zero).mp hs

private theorem diagonalNullGradient_eq_zero_apply (d : Fin (n + 1) → ℝ) (g : V) {x : ℝ}
    (h : diagonalNullGradient d x g = 0) (i : Fin (n + 1)) (hi : d i + x = 0) : g i = 0 := by
  have he := congrFun (congrArg ofLp h) i
  change (if d i + x = 0 then g i else 0) = 0 at he
  rwa [ite_eq_left hi] at he

/-- **Algorithm 7.7.1** of [conn2000trust], finite return. Let $d, g \in \mathbb{R}^{n+1}$,
$\Delta > 0$ and $\varepsilon > 0$, and let $d_{i_0} \le d_i$ for every $i$. Then Algorithm
7.7.1 returns a step $s$, and either $\|s\| \le \Delta$ and $s$ minimizes $m(s) = \langle g, s
\rangle + \frac{1}{2} \langle s, D s \rangle$ on the ball $\|s\| \le \Delta$, or
$$\big| \|s\| - \Delta \big| \le \varepsilon \Delta.$$

The exact branches in Steps 1 and 2 return minimizers, and a Newton return passes the relative
radius test. -/
theorem algorithm_7_7_1_returns (d : Fin (n + 1) → ℝ) (g : V) {Δ ε : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (i₀ : Fin (n + 1)) (hi : ∀ i, d i₀ ≤ d i) :
    ∃ s, algorithm_7_7_1 d g Δ ε i₀ = some s ∧
      ((s ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g (diagonalOperator d))
        (Metric.closedBall 0 Δ) s) ∨ |‖s‖ - Δ| ≤ ε * Δ) := by
  let H := diagonalOperator d
  let pole := -d i₀
  let s₀ := -diagonalShiftInverse d 0 g
  let gn := diagonalNullGradient d pole g
  let p := -diagonalShiftInverse d pole g
  have hleft : -leftmost (diagonalOperator_symm d) = pole := by
    rw [diagonal_leftmost d i₀ hi]
  by_cases hfirst : 0 < d i₀ ∧ ‖s₀‖ ≤ Δ
  · have hsolve : (H + (0 : ℝ) • 1) s₀ = -g :=
      diagonalShiftStep_solves d g 0 (fun i hz =>
        (ne_of_gt (by linarith [hi i, hfirst.1] : 0 < d i + 0) hz).elim)
    have hpos : -leftmost (diagonalOperator_symm d) ≤ 0 := by rw [hleft]; linarith [hfirst.1]
    have hmul : IsTrustRegionMultiplier g H Δ s₀ 0 :=
      ⟨le_rfl, hsolve, isPositive_add_smul_of_le hpos, zero_mul _⟩
    refine ⟨s₀, ?_, Or.inl (hmul.isMinOn_of_norm_le (diagonalOperator_symm d) hfirst.2)⟩
    unfold algorithm_7_7_1
    dsimp only
    rw [ite_eq_left hfirst]
  by_cases hsecond : d i₀ ≤ 0 ∧ gn = 0 ∧ ‖p‖ ≤ Δ
  · let u : V := toLp 2 (Pi.single i₀ 1)
    let α := moreSorensenBoundaryCoefficient Δ p u
    have hu : ‖u‖ = 1 := by simp [u]
    have hb : ‖p + α • u‖ = Δ := norm_add_boundaryCorrection hsecond.2.2 hu
    have hsol : (H + pole • 1) p = -g :=
      diagonalShiftStep_solves d g pole (diagonalNullGradient_eq_zero_apply d g hsecond.2.1)
    have hker : (H + pole • 1) u = 0 := by
      ext i
      change (diagonalOperator d u) i + pole * u i = 0
      rw [diagonalOperator_apply]
      by_cases he : i = i₀
      · subst i
        simp [u, pole]
      · simp [u, he]
    have hmul : IsTrustRegionMultiplier g H Δ (p + α • u) pole := by
      refine ⟨neg_nonneg.mpr hsecond.1, ?_, isPositive_add_smul_of_le hleft.le, ?_⟩
      · rw [map_add, map_smul, hsol, hker, smul_zero, add_zero]
      · rw [hb, sub_self, mul_zero]
    refine ⟨p + α • u, ?_, Or.inl (hmul.isMinOn_of_norm_le (diagonalOperator_symm d) hb.le)⟩
    unfold algorithm_7_7_1
    dsimp only
    rw [ite_eq_right hfirst, ite_eq_left hsecond]
  let x₀ := if 0 < d i₀ then 0 else pole + ‖gn‖ / Δ
  have hstart : 0 ≤ x₀ ∧ (∀ i, 0 ≤ d i + x₀) ∧
      (∀ i, d i + x₀ = 0 → g i = 0) ∧ Δ ≤ ‖-diagonalShiftInverse d x₀ g‖ := by
    by_cases hd : 0 < d i₀
    · have he : Δ < ‖s₀‖ := lt_of_not_ge (fun h => hfirst ⟨hd, h⟩)
      rw [show x₀ = 0 by simp [x₀, hd]]
      refine ⟨le_rfl, fun i => by linarith [hi i], fun i hz => ?_, he.le⟩
      exact (ne_of_gt (by linarith [hi i] : 0 < d i + 0) hz).elim
    · have hp : 0 ≤ pole := neg_nonneg.mpr (le_of_not_gt hd)
      rw [show x₀ = pole + ‖gn‖ / Δ by simp [x₀, hd]]
      by_cases hg : gn = 0
      · have he : Δ < ‖p‖ := lt_of_not_ge (fun h => hsecond ⟨le_of_not_gt hd, hg, h⟩)
        simp only [hg, norm_zero, zero_div, add_zero]
        exact ⟨hp, fun i => by linarith [hi i], diagonalNullGradient_eq_zero_apply d g hg, he.le⟩
      · have ht : 0 < ‖gn‖ / Δ := div_pos (norm_pos_iff.mpr hg) hΔ
        refine ⟨by linarith, fun i => by linarith [hi i], fun i hz => ?_,
          algorithm_7_7_1_seed_norm d g hΔ hg⟩
        exact (ne_of_gt (by linarith [hi i] : 0 < d i + (pole + ‖gn‖ / Δ)) hz).elim
  let s := fun k : ℕ => -diagonalShiftInverse d ((diagonalNewtonStep d g Δ)^[k] x₀) g
  have h : ∃ k, |‖s k‖ - Δ| ≤ ε * Δ := by
    rcases hstart.2.2.2.lt_or_eq with hn | hn
    · exact algorithm_7_7_1_newton_stop d g hΔ hε hstart.1 hstart.2.1 hstart.2.2.1 hn
    · refine ⟨0, ?_⟩
      change |‖-diagonalShiftInverse d x₀ g‖ - Δ| ≤ ε * Δ
      rw [← hn, sub_self, abs_zero]
      exact mul_nonneg hε.le hΔ.le
  refine ⟨s (Nat.find h), ?_, Or.inr (Nat.find_spec h)⟩
  unfold algorithm_7_7_1
  dsimp only
  rw [ite_eq_right hfirst, ite_eq_right hsecond, dite_eq_left h]

/-- **Algorithm 7.7.1** of [conn2000trust], automatic selection. For $d, g \in \mathbb{R}^{n+1}$ and
$\Delta, \varepsilon \in \mathbb{R}$, this runs Algorithm 7.7.1 with an index $i_0$ that attains
$\min_i d_i$, chosen by `Classical.choose`. -/
noncomputable def algorithm_7_7_1_auto (d : Fin (n + 1) → ℝ) (g : V) (Δ ε : ℝ) : Option V :=
  algorithm_7_7_1 d g Δ ε (Classical.choose
    (Finset.exists_min_image Finset.univ d Finset.univ_nonempty))

/-- **Algorithm 7.7.1** of [conn2000trust], run with automatic selection. Let
$d, g \in \mathbb{R}^{n+1}$, $\Delta > 0$ and $\varepsilon > 0$. Then the algorithm with
automatic least-diagonal selection returns a step $s$, and either $\|s\| \le \Delta$ and $s$
minimizes $m(s) = \langle g, s \rangle + \frac{1}{2} \langle s, D s \rangle$ on the ball
$\|s\| \le \Delta$, or $\big| \|s\| - \Delta \big| \le \varepsilon \Delta$. -/
theorem algorithm_7_7_1_auto_returns (d : Fin (n + 1) → ℝ) (g : V) {Δ ε : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) :
    ∃ s, algorithm_7_7_1_auto d g Δ ε = some s ∧
      ((s ∈ Metric.closedBall 0 Δ ∧ IsMinOn (quadModel g (diagonalOperator d))
        (Metric.closedBall 0 Δ) s) ∨ |‖s‖ - Δ| ≤ ε * Δ) := by
  let hm := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
  let i := Classical.choose hm
  have hi (j : Fin (n + 1)) : d i ≤ d j :=
    (Classical.choose_spec hm).2 j (Finset.mem_univ j)
  exact algorithm_7_7_1_returns d g hΔ hε i hi

end ConnGouldToint.Chapter07
