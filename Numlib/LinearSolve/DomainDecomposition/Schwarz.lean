import Numlib.Krylov.Convergence.CG
import Numlib.LinearSolve.Multigrid.Basic
import Numlib.LinearSolve.Projection.Additive

/-!
# The abstract Schwarz theory

A **Schwarz method** solves a linear system by repeatedly solving it on a family of subspaces.
The whole convergence theory is a statement about a finite family `V : ℕ → Submodule 𝕜 H` of
subspaces of an inner product space and their orthogonal projectors `P i = (V i).starProjection`:

* the **additive** operator `A_J = ∑_{i < s} P i` (`Schwarz.additiveOperator`), which is the
  preconditioned operator of the additive method;
* the **multiplicative** error operator `Q_s = (1 - P_{s-1}) ⋯ (1 - P_0)` (`Schwarz.errorOp`),
  which is what one sweep of the multiplicative method does to the error.

No domain, mesh or restriction matrix occurs anywhere.  The classical subdomain projector
`P_i = R_iᵀ A_i⁻¹ R_i A` of a symmetric coercive `A` *is* the orthogonal projector onto
`range R_iᵀ` in the energy inner product, and the local matrix `A_i = R_i A R_iᵀ` is the Galerkin
coarse operator of that subspace; so the theory below is stated in a plain inner product space and
applied with `H = WithEnergy A hA`.  `Schwarz.energyProjection` is that transport, and
`Schwarz.error_multiplicativeStep_eq_errorOp` and `Schwarz.error_additiveStep_eq` identify a
Schwarz sweep with the multiplicative and additive projection processes of
`Numlib/LinearSolve/Projection/Additive.lean`: those act on residuals, these on errors, and the
two are conjugate by `A`.

## The two hypotheses

Convergence rests on two constants that no amount of linear algebra can produce, because they are
statements about a discretization:

* `Schwarz.IsStableDecompositionWith V s K₀` — every vector splits over the family with
  `∑ ‖w i‖² ≤ K₀ ‖u‖²`.  It bounds the smallest eigenvalue of `A_J` from below by `1/K₀`
  (`Schwarz.le_re_inner_additiveOperator`), while the largest is at most the number of subspaces
  (`Schwarz.re_inner_additiveOperator_le`), or at most the number of colours in a colouring of the
  family by mutual orthogonality (`Schwarz.re_inner_additiveOperator_le_of_coloring`).  The two
  bounds together are a `LinearMap.IsSymmetricBoundedBy` statement
  (`Schwarz.isSymmetricBoundedBy_additiveOperator`), from which the convergence rate of the
  preconditioned conjugate gradient method follows with no new estimate
  (`Schwarz.energyNorm_error_le`).
* `Schwarz.IsStrengthenedCauchySchwarzWith V s K₁` — a strengthened Cauchy–Schwarz inequality
  measuring how far the subspaces are from being mutually orthogonal.  With both constants, one
  multiplicative sweep contracts the norm of the error by `√(1 - 1/(K₀ (1 + K₁)²))`
  (`Schwarz.norm_errorOp_le`).

Both difficult proofs rest on the vector-valued Cauchy–Schwarz inequality `Schwarz.inner_sum_le`.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.  The subspace projector is his (14.24), the additive operator his (14.37), the
  multiplicative error operator his (14.26), the two hypotheses his Assumptions 1 and 2 of
  §14.3.4, and the four convergence results his Theorems 14.5–14.7, Lemma 14.8 and Theorem 14.9.
  The vector-valued Cauchy–Schwarz inequality is his Exercise 14.1.
-/

namespace Schwarz

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ### The vector-valued Cauchy–Schwarz inequality -/

/-- **The vector-valued Cauchy–Schwarz inequality**: `∑ re ⟪x i, y i⟫` is bounded by the product
of the root-mean-square norms of the two families.  Cauchy–Schwarz termwise, then the
Cauchy–Schwarz inequality for finite sums of reals. -/
theorem inner_sum_le {ι : Type*} (t : Finset ι) (x y : ι → H) :
    ∑ i ∈ t, RCLike.re (inner 𝕜 (x i) (y i))
      ≤ Real.sqrt (∑ i ∈ t, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ t, ‖y i‖ ^ 2) :=
  (Finset.sum_le_sum fun i _ =>
      (RCLike.re_le_norm _).trans (norm_inner_le_norm (x i) (y i))).trans
    (Real.sum_mul_le_sqrt_mul_sqrt t _ _)

/-! ### Orthogonal projectors onto a family of subspaces -/

section Projectors

variable (K : Submodule 𝕜 H) [K.HasOrthogonalProjection]

/-- The quadratic form of an orthogonal projector is the squared norm of the projection. -/
theorem re_inner_starProjection_self (u : H) :
    RCLike.re (inner 𝕜 (K.starProjection u) u) = ‖K.starProjection u‖ ^ 2 := by
  have h : inner 𝕜 (u - K.starProjection u) (K.starProjection u) = (0 : 𝕜) :=
    K.starProjection_inner_eq_zero u _ (K.starProjection_apply_mem u)
  have h2 : inner 𝕜 u (K.starProjection u)
      = inner 𝕜 (K.starProjection u) (K.starProjection u) := by
    rw [← sub_eq_zero, ← inner_sub_left]
    exact h
  rw [← inner_conj_symm, h2, RCLike.conj_re, inner_self_eq_norm_sq]

/-- An orthogonal projector may be dropped from the second argument of an inner product whose
first argument already lies in the subspace. -/
theorem inner_starProjection_starProjection (a b : H) :
    inner 𝕜 (K.starProjection a) (K.starProjection b) = inner 𝕜 (K.starProjection a) b := by
  have hidem : K.starProjection (K.starProjection b) = K.starProjection b :=
    Submodule.starProjection_eq_self_iff.2 (K.starProjection_apply_mem b)
  rw [Submodule.inner_starProjection_left_eq_right K a (K.starProjection b), hidem,
    ← Submodule.inner_starProjection_left_eq_right K a b]

end Projectors

/-- **Bessel's inequality for a pairwise orthogonal family of subspaces**: the squared norms of
the projections of one vector add up to at most its squared norm. -/
theorem sum_norm_starProjection_sq_le_of_pairwise_orthogonal {ι : Type*} (t : Finset ι)
    (W : ι → Submodule 𝕜 H) [∀ i, (W i).HasOrthogonalProjection]
    (horth : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → W i ⟂ W j) (u : H) :
    ∑ i ∈ t, ‖(W i).starProjection u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  have hcross : ∀ i ∈ t, ∀ j ∈ t, i ≠ j →
      inner 𝕜 ((W i).starProjection u) ((W j).starProjection u) = (0 : 𝕜) := fun i hi j hj hij =>
    (Submodule.isOrtho_iff_inner_eq (𝕜 := 𝕜)).1 (horth i hi j hj hij) _
      ((W i).starProjection_apply_mem u) _ ((W j).starProjection_apply_mem u)
  have hdiag : ∀ i ∈ t, RCLike.re (inner 𝕜 ((W i).starProjection u)
      (∑ j ∈ t, (W j).starProjection u)) = ‖(W i).starProjection u‖ ^ 2 := by
    intro i hi
    rw [inner_sum, map_sum, Finset.sum_eq_single i]
    · exact inner_self_eq_norm_sq _
    · exact fun j hj hji => by rw [hcross i hi j hj (Ne.symm hji), map_zero]
    · exact fun hi' => absurd hi hi'
  have hnormz : ‖∑ i ∈ t, (W i).starProjection u‖ ^ 2
      = ∑ i ∈ t, ‖(W i).starProjection u‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), sum_inner, map_sum]
    exact Finset.sum_congr rfl hdiag
  have hzu : RCLike.re (inner 𝕜 (∑ i ∈ t, (W i).starProjection u) u)
      = ∑ i ∈ t, ‖(W i).starProjection u‖ ^ 2 := by
    rw [sum_inner, map_sum]
    exact Finset.sum_congr rfl fun i _ => re_inner_starProjection_self (W i) u
  have hle : (∑ i ∈ t, ‖(W i).starProjection u‖ ^ 2)
      ≤ ‖∑ i ∈ t, (W i).starProjection u‖ * ‖u‖ := by
    rw [← hzu]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ u)
  nlinarith [hnormz, hle, sq_nonneg (‖∑ i ∈ t, (W i).starProjection u‖ - ‖u‖)]

/-! ### The two hypotheses of the convergence theory -/

variable (V : ℕ → Submodule 𝕜 H) [∀ i, (V i).HasOrthogonalProjection]

/-- **A stable decomposition** over the family `V 0, …, V (s-1)` with constant `K₀`: every vector
is a sum of vectors of the subspaces whose squared norms add up to at most `K₀ ‖u‖²`.  This is
the hypothesis that the subspaces cover the space stably; it is not a consequence of the algebra,
and for a finite-element family it is exactly what an overlapping-subdomain partition of unity
provides. -/
def IsStableDecompositionWith (s : ℕ) (K₀ : ℝ) : Prop :=
  ∀ u : H, ∃ w : ℕ → H, (∀ i ∈ Finset.range s, w i ∈ V i) ∧ ∑ i ∈ Finset.range s, w i = u ∧
    ∑ i ∈ Finset.range s, ‖w i‖ ^ 2 ≤ K₀ * ‖u‖ ^ 2

/-- **A strengthened Cauchy–Schwarz inequality** with constant `K₁`: for every set `S` of pairs of
indices below `s`, the corresponding sum of inner products of projections is bounded by `K₁` times
the product of the root-mean-square norms of the two families of projections.  It measures how far
the subspaces are from being mutually orthogonal: pairwise orthogonal subspaces admit `K₁ = 0`,
and the plain Cauchy–Schwarz inequality always gives `K₁ = s`. -/
def IsStrengthenedCauchySchwarzWith (s : ℕ) (K₁ : ℝ) : Prop :=
  ∀ S : Finset (ℕ × ℕ), S ⊆ Finset.range s ×ˢ Finset.range s → ∀ x y : ℕ → H,
    ∑ ij ∈ S, RCLike.re (inner 𝕜 ((V ij.1).starProjection (x ij.1))
        ((V ij.2).starProjection (y ij.2)))
      ≤ K₁ * Real.sqrt (∑ i ∈ Finset.range s, ‖(V i).starProjection (x i)‖ ^ 2)
        * Real.sqrt (∑ j ∈ Finset.range s, ‖(V j).starProjection (y j)‖ ^ 2)

/-! ### The additive Schwarz operator -/

/-- **The additive Schwarz operator** `A_J = ∑_{i < s} P i`, the sum of the orthogonal projectors
onto the subspaces.  Read in the energy inner product of `A`, it is the preconditioned operator
`M⁻¹ A` of the additive Schwarz method. -/
noncomputable def additiveOperator (s : ℕ) : H →L[𝕜] H :=
  ∑ i ∈ Finset.range s, (V i).starProjection

@[simp]
theorem additiveOperator_apply (s : ℕ) (u : H) :
    additiveOperator V s u = ∑ i ∈ Finset.range s, (V i).starProjection u := by
  rw [additiveOperator, sum_apply]

/-- The additive Schwarz operator is self-adjoint, being a sum of orthogonal projectors. -/
theorem additiveOperator_isSymmetric (s : ℕ) :
    (additiveOperator V s : H →ₗ[𝕜] H).IsSymmetric := by
  intro u v
  change inner 𝕜 (additiveOperator V s u) v = inner 𝕜 u (additiveOperator V s v)
  rw [additiveOperator_apply, additiveOperator_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl fun i _ => Submodule.inner_starProjection_left_eq_right _ u v

/-- The quadratic form of the additive Schwarz operator is the sum of the squared norms of the
projections. -/
theorem re_inner_additiveOperator (s : ℕ) (u : H) :
    RCLike.re (inner 𝕜 (additiveOperator V s u) u)
      = ∑ i ∈ Finset.range s, ‖(V i).starProjection u‖ ^ 2 := by
  rw [additiveOperator_apply, sum_inner, map_sum]
  exact Finset.sum_congr rfl fun i _ => re_inner_starProjection_self (V i) u

/-- The additive Schwarz operator is positive semidefinite. -/
theorem re_inner_additiveOperator_nonneg (s : ℕ) (u : H) :
    0 ≤ RCLike.re (inner 𝕜 (additiveOperator V s u) u) := by
  rw [re_inner_additiveOperator]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **The largest eigenvalue of the additive Schwarz operator is at most the number of
subspaces**: `re ⟪A_J u, u⟫ ≤ s ‖u‖²`.  Each projector is norm non-increasing, and the quadratic
form is the sum of the squared norms of the projections. -/
theorem re_inner_additiveOperator_le (s : ℕ) (u : H) :
    RCLike.re (inner 𝕜 (additiveOperator V s u) u) ≤ s * ‖u‖ ^ 2 := by
  rw [re_inner_additiveOperator]
  calc ∑ i ∈ Finset.range s, ‖(V i).starProjection u‖ ^ 2
      ≤ ∑ _i ∈ Finset.range s, ‖u‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := Submodule.norm_starProjection_apply_le (V i) u
        nlinarith [norm_nonneg ((V i).starProjection u)]
    _ = s * ‖u‖ ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The largest eigenvalue of the additive Schwarz operator is at most the number of colours**:
if the subspaces are coloured so that two subspaces of the same colour are orthogonal, then
`re ⟪A_J u, u⟫ ≤ (card κ) ‖u‖²`.  Each colour class contributes at most `‖u‖²` by Bessel's
inequality, so a colouring of the interaction graph of the subdomains replaces the crude bound by
the number of subspaces. -/
theorem re_inner_additiveOperator_le_of_coloring {κ : Type*} [Fintype κ] (s : ℕ)
    (col : ℕ → κ)
    (horth : ∀ i ∈ Finset.range s, ∀ j ∈ Finset.range s, i ≠ j → col i = col j → V i ⟂ V j)
    (u : H) :
    RCLike.re (inner 𝕜 (additiveOperator V s u) u) ≤ Fintype.card κ * ‖u‖ ^ 2 := by
  classical
  rw [re_inner_additiveOperator, ← Finset.sum_fiberwise (Finset.range s) col]
  calc ∑ k : κ, ∑ i ∈ (Finset.range s).filter fun i => col i = k,
        ‖(V i).starProjection u‖ ^ 2
      ≤ ∑ _k : κ, ‖u‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine sum_norm_starProjection_sq_le_of_pairwise_orthogonal _ V ?_ u
        intro i hi j hj hij
        rw [Finset.mem_filter] at hi hj
        exact horth i hi.1 j hj.1 hij (hi.2.trans hj.2.symm)
    _ = Fintype.card κ * ‖u‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The smallest eigenvalue of the additive Schwarz operator is at least `1/K₀`**: under a
stable decomposition with constant `K₀`, `‖u‖²/K₀ ≤ re ⟪A_J u, u⟫`.  Writing `u = ∑ w i` with
`w i ∈ V i`, each `⟪w i, u⟫` equals `⟪w i, P i u⟫` because `P i` fixes `w i`, and the
vector-valued Cauchy–Schwarz inequality turns `‖u‖²` into the product of the two root-mean-square
norms; the stable decomposition bounds one of them. -/
theorem le_re_inner_additiveOperator {s : ℕ} {K₀ : ℝ}
    (hst : IsStableDecompositionWith V s K₀) (u : H) :
    ‖u‖ ^ 2 / K₀ ≤ RCLike.re (inner 𝕜 (additiveOperator V s u) u) := by
  obtain ⟨w, hmem, hsum, hbound⟩ := hst u
  have hQnn : 0 ≤ RCLike.re (inner 𝕜 (additiveOperator V s u) u) :=
    re_inner_additiveOperator_nonneg V s u
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
  -- the inner products against `u` may be taken against the projections
  have hwi : ∀ i ∈ Finset.range s,
      inner 𝕜 (w i) u = inner 𝕜 (w i) ((V i).starProjection u) := by
    intro i hi
    conv_lhs => rw [← Submodule.starProjection_eq_self_iff.2 (hmem i hi)]
    exact Submodule.inner_starProjection_left_eq_right (V i) (w i) u
  have key : (inner 𝕜 u u : 𝕜) = ∑ i ∈ Finset.range s, inner 𝕜 (w i) u := by
    rw [← sum_inner, hsum]
  have hnorm : ‖u‖ ^ 2
      = ∑ i ∈ Finset.range s, RCLike.re (inner 𝕜 (w i) ((V i).starProjection u)) := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), key, map_sum]
    exact Finset.sum_congr rfl fun i hi => by rw [hwi i hi]
  -- Cauchy–Schwarz, then the stable decomposition
  have hw2 : Real.sqrt (∑ i ∈ Finset.range s, ‖w i‖ ^ 2) ≤ Real.sqrt K₀ * ‖u‖ := by
    calc Real.sqrt (∑ i ∈ Finset.range s, ‖w i‖ ^ 2)
        ≤ Real.sqrt (K₀ * ‖u‖ ^ 2) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt K₀ * ‖u‖ := by
          rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg u)]
  have hmain : ‖u‖ ^ 2 ≤ Real.sqrt K₀ * ‖u‖
      * Real.sqrt (RCLike.re (inner 𝕜 (additiveOperator V s u) u)) := by
    rw [hnorm]
    refine (inner_sum_le (Finset.range s) w fun i => (V i).starProjection u).trans ?_
    rw [← re_inner_additiveOperator V s u]
    exact mul_le_mul_of_nonneg_right hw2 (Real.sqrt_nonneg _)
  -- divide by `‖u‖`, square, and divide by `K₀`
  have hK₀nn : 0 ≤ K₀ := by
    by_contra h
    push Not at h
    have h1 : K₀ * ‖u‖ ^ 2 < 0 := mul_neg_of_neg_of_pos h (pow_pos hupos 2)
    have h0 : (0 : ℝ) ≤ ∑ i ∈ Finset.range s, ‖w i‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have h1 : ‖u‖ * ‖u‖
      ≤ Real.sqrt K₀ * Real.sqrt (RCLike.re (inner 𝕜 (additiveOperator V s u) u)) * ‖u‖ := by
    have h := hmain
    rw [sq] at h
    linarith
  have h2 : ‖u‖ ^ 2 ≤ K₀ * RCLike.re (inner 𝕜 (additiveOperator V s u) u) := by
    have h3 := mul_self_le_mul_self (norm_nonneg u) (le_of_mul_le_mul_right h1 hupos)
    calc ‖u‖ ^ 2 = ‖u‖ * ‖u‖ := sq _
      _ ≤ Real.sqrt K₀ * Real.sqrt (RCLike.re (inner 𝕜 (additiveOperator V s u) u))
          * (Real.sqrt K₀ * Real.sqrt (RCLike.re (inner 𝕜 (additiveOperator V s u) u))) := h3
      _ = Real.sqrt K₀ ^ 2
          * Real.sqrt (RCLike.re (inner 𝕜 (additiveOperator V s u) u)) ^ 2 := by ring
      _ = K₀ * RCLike.re (inner 𝕜 (additiveOperator V s u) u) := by
          rw [Real.sq_sqrt hK₀nn, Real.sq_sqrt hQnn]
  have hK₀pos : 0 < K₀ := by
    rcases hK₀nn.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at h2
      exact absurd h2 (not_le.2 (pow_pos hupos 2))
  rw [div_le_iff₀ hK₀pos]
  linarith

/-- **The spectral equivalence of the additive Schwarz preconditioner** (Saad, *Iterative Methods
for Sparse Linear Systems*, Theorems 14.5 and 14.7 together): under a stable decomposition with
constant `K₀`, the quadratic form of `A_J` is enclosed between `1/K₀` and the number of subspaces.
This is the hypothesis every Chebyshev-type convergence bound of the library takes, so the
condition number of the additive Schwarz preconditioned system is at most `s K₀` with no further
estimate. -/
theorem isSymmetricBoundedBy_additiveOperator {s : ℕ} {K₀ : ℝ}
    (hst : IsStableDecompositionWith V s K₀) :
    (additiveOperator V s : H →ₗ[𝕜] H).IsSymmetricBoundedBy (1 / K₀) s :=
  ⟨additiveOperator_isSymmetric V s,
    fun u => by
      rw [one_div, inv_mul_eq_div]
      exact le_re_inner_additiveOperator V hst u,
    fun u => re_inner_additiveOperator_le V s u⟩

/-- **Additive Schwarz preconditioned conjugate gradients** converge at the rate given by the
condition number `s K₀`: the Chebyshev bound of the conjugate gradient method applied to `A_J`,
whose spectral bounds are `Schwarz.isSymmetricBoundedBy_additiveOperator`.  This is the corollary
that makes the two eigenvalue bounds worth packaging together. -/
theorem energyNorm_error_le [Nontrivial H] {s : ℕ} {K₀ : ℝ} (hK₀ : 0 < K₀)
    (hst : IsStableDecompositionWith V s K₀) {b x₀ : H} {m : ℕ} {x xstar : H}
    (hx : Krylov.IsGalerkinIterate (additiveOperator V s : H →ₗ[𝕜] H) b x₀ m x)
    (hstar : (additiveOperator V s : H →ₗ[𝕜] H) xstar = b) :
    energyNorm (additiveOperator V s : H →ₗ[𝕜] H) (xstar - x)
      ≤ 2 * ((Real.sqrt (s * K₀) - 1) / (Real.sqrt (s * K₀) + 1)) ^ m
        * energyNorm (additiveOperator V s : H →ₗ[𝕜] H) (xstar - x₀) := by
  obtain ⟨u, hu⟩ := exists_ne (0 : H)
  have hupos : (0 : ℝ) < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.2 hu) 2
  have hle : 1 / K₀ ≤ (s : ℝ) := by
    have h1 := le_re_inner_additiveOperator V hst u
    have h2 := re_inner_additiveOperator_le V s u
    refine le_of_mul_le_mul_right ?_ hupos
    rw [one_div, inv_mul_eq_div]
    linarith
  have h := Krylov.IsGalerkinIterate.energyNorm_error_le (by positivity) hle
    (isSymmetricBoundedBy_additiveOperator V hst) hx hstar
  have hrat : (s : ℝ) / K₀⁻¹ = (s : ℝ) * K₀ := by rw [div_eq_mul_inv, inv_inv]
  rwa [one_div, hrat] at h

/-! ### The multiplicative Schwarz sweep -/

/-- **The error propagation operator of a multiplicative Schwarz sweep**: `Q 0 = 1` and
`Q (i+1) = (1 - P i) ∘ Q i`, so that `Q s = (1 - P_{s-1}) ⋯ (1 - P_0)` corrects on the subspaces
in the order `0, 1, …, s-1`.  Indexed by `ℕ` rather than by `Fin s` so that the recursion is
definitional and the prefixes `Q 0, Q 1, …` are all available at once, which is what the
telescoping identity `Schwarz.norm_errorOp_sq_eq` needs. -/
noncomputable def errorOp : ℕ → H →L[𝕜] H
  | 0 => 1
  | i + 1 => (1 - (V i).starProjection) ∘L errorOp i

@[simp]
theorem errorOp_zero : errorOp V 0 = 1 := rfl

theorem errorOp_succ (i : ℕ) :
    errorOp V (i + 1) = (1 - (V i).starProjection) ∘L errorOp V i := rfl

@[simp]
theorem errorOp_succ_apply (i : ℕ) (v : H) :
    errorOp V (i + 1) v = errorOp V i v - (V i).starProjection (errorOp V i v) := rfl

/-- **Saad's Lemma 14.4** (Saad, *Iterative Methods for Sparse Linear Systems*), in the form
(14.35): what a multiplicative sweep adds to the iterate is `∑_{i < s} P i Q i`.  Equivalently,
the sweep is the fixed-point iteration whose preconditioned operator is `1 - Q s`. -/
theorem one_sub_errorOp_eq_sum (s : ℕ) :
    1 - errorOp V s = ∑ i ∈ Finset.range s, (V i).starProjection ∘L errorOp V i := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.sum_range_succ, ← ih, errorOp_succ]
      ext v
      simp only [sub_apply, add_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply]
      abel

/-- The pointwise form of `Schwarz.one_sub_errorOp_eq_sum`. -/
theorem sub_errorOp_apply (s : ℕ) (v : H) :
    v - errorOp V s v = ∑ i ∈ Finset.range s, (V i).starProjection (errorOp V i v) := by
  have h := congrArg (fun T : H →L[𝕜] H => T v) (one_sub_errorOp_eq_sum V s)
  simpa using h

/-- **The telescoping identity of a multiplicative sweep** (Saad, *Iterative Methods for Sparse
Linear Systems*, (14.39)): `‖Q s v‖² = ‖v‖² - ∑_{i < s} ‖P i (Q i v)‖²`.  In particular a sweep
never increases the norm of the error, and the sum on the right is exactly what the convergence
rate has to be bounded below by. -/
theorem norm_errorOp_sq_eq (s : ℕ) (v : H) :
    ‖errorOp V s v‖ ^ 2
      = ‖v‖ ^ 2 - ∑ i ∈ Finset.range s, ‖(V i).starProjection (errorOp V i v)‖ ^ 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hstep : ‖errorOp V (s + 1) v‖ ^ 2
          = ‖errorOp V s v‖ ^ 2 - ‖(V s).starProjection (errorOp V s v)‖ ^ 2 := by
        have h := (V s).norm_sq_eq_add_norm_sq_starProjection (errorOp V s v)
        rw [Submodule.starProjection_orthogonal_val] at h
        rw [errorOp_succ_apply]
        linarith
      rw [hstep, ih, Finset.sum_range_succ]
      ring

/-- A real inequality of the shape `X ≤ c √X √Y` gives `X ≤ c² Y`. -/
private theorem le_sq_mul_of_le_mul_sqrt {X Y c : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : X ≤ c * (Real.sqrt X * Real.sqrt Y)) : X ≤ c ^ 2 * Y := by
  rcases hX.lt_or_eq with hXpos | hXzero
  · have hsx : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
    have hXX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX
    have hYY : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY
    have h1 : Real.sqrt X ≤ c * Real.sqrt Y := by
      refine le_of_mul_le_mul_right ?_ hsx
      linarith
    nlinarith [mul_self_le_mul_self (Real.sqrt_nonneg X) h1]
  · rw [← hXzero]
    exact mul_nonneg (sq_nonneg c) hY

/-- The strictly lower triangular part of a square index range, as a set of pairs. -/
private theorem sum_range_sum_range_eq (s : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.range s, ∑ j ∈ Finset.range i, f i j
      = ∑ ij ∈ (Finset.range s ×ˢ Finset.range s).filter fun p => p.2 < p.1, f ij.1 ij.2 := by
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i hi => ?_
  dsimp only
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_range, Finset.mem_filter]
  simp only [Finset.mem_range] at hi
  omega

/-- **Saad's Lemma 14.8** (Saad, *Iterative Methods for Sparse Linear Systems*): under a
strengthened Cauchy–Schwarz inequality with constant `K₁`, the projections of a vector are
controlled by the projections of the partially swept vectors,
`∑_{i < s} ‖P i v‖² ≤ (1 + K₁)² ∑_{i < s} ‖P i (Q i v)‖²`.  Splitting `P i v` along
`v = Q i v + (1 - Q i) v` and expanding the second half by (14.35) gives a diagonal sum, bounded
by the vector-valued Cauchy–Schwarz inequality, and a strictly lower triangular sum, bounded by
the assumption. -/
theorem sum_norm_starProjection_sq_le {s : ℕ} {K₁ : ℝ}
    (hcs : IsStrengthenedCauchySchwarzWith V s K₁) (v : H) :
    ∑ i ∈ Finset.range s, ‖(V i).starProjection v‖ ^ 2
      ≤ (1 + K₁) ^ 2 * ∑ i ∈ Finset.range s, ‖(V i).starProjection (errorOp V i v)‖ ^ 2 := by
  classical
  have hX : (0 : ℝ) ≤ ∑ i ∈ Finset.range s, ‖(V i).starProjection v‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hY : (0 : ℝ) ≤ ∑ i ∈ Finset.range s, ‖(V i).starProjection (errorOp V i v)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- the term-by-term decomposition
  have hterm : ∀ i ∈ Finset.range s, ‖(V i).starProjection v‖ ^ 2
      = RCLike.re (inner 𝕜 ((V i).starProjection v) ((V i).starProjection (errorOp V i v)))
        + ∑ j ∈ Finset.range i, RCLike.re (inner 𝕜 ((V i).starProjection v)
            ((V j).starProjection (errorOp V j v))) := by
    intro i _
    have hsplit : v = errorOp V i v + (v - errorOp V i v) := by abel
    calc ‖(V i).starProjection v‖ ^ 2
        = RCLike.re (inner 𝕜 ((V i).starProjection v) v) := by
          rw [← inner_starProjection_starProjection, inner_self_eq_norm_sq]
      _ = RCLike.re (inner 𝕜 ((V i).starProjection v)
            (errorOp V i v + (v - errorOp V i v))) := by rw [← hsplit]
      _ = RCLike.re (inner 𝕜 ((V i).starProjection v) (errorOp V i v))
            + RCLike.re (inner 𝕜 ((V i).starProjection v) (v - errorOp V i v)) := by
          rw [inner_add_right, map_add]
      _ = RCLike.re (inner 𝕜 ((V i).starProjection v) ((V i).starProjection (errorOp V i v)))
            + ∑ j ∈ Finset.range i, RCLike.re (inner 𝕜 ((V i).starProjection v)
                ((V j).starProjection (errorOp V j v))) := by
          rw [inner_starProjection_starProjection, sub_errorOp_apply, inner_sum, map_sum]
  have hsum : ∑ i ∈ Finset.range s, ‖(V i).starProjection v‖ ^ 2
      = (∑ i ∈ Finset.range s, RCLike.re (inner 𝕜 ((V i).starProjection v)
            ((V i).starProjection (errorOp V i v))))
        + ∑ i ∈ Finset.range s, ∑ j ∈ Finset.range i,
            RCLike.re (inner 𝕜 ((V i).starProjection v)
              ((V j).starProjection (errorOp V j v))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  -- the diagonal sum, by the vector-valued Cauchy–Schwarz inequality
  have hT1 : (∑ i ∈ Finset.range s, RCLike.re (inner 𝕜 ((V i).starProjection v)
        ((V i).starProjection (errorOp V i v))))
      ≤ Real.sqrt (∑ i ∈ Finset.range s, ‖(V i).starProjection v‖ ^ 2)
        * Real.sqrt (∑ i ∈ Finset.range s, ‖(V i).starProjection (errorOp V i v)‖ ^ 2) :=
    inner_sum_le _ _ _
  -- the strictly lower triangular sum, by the strengthened Cauchy–Schwarz inequality
  have hT2 : (∑ i ∈ Finset.range s, ∑ j ∈ Finset.range i,
        RCLike.re (inner 𝕜 ((V i).starProjection v)
          ((V j).starProjection (errorOp V j v))))
      ≤ K₁ * Real.sqrt (∑ i ∈ Finset.range s, ‖(V i).starProjection v‖ ^ 2)
        * Real.sqrt (∑ i ∈ Finset.range s, ‖(V i).starProjection (errorOp V i v)‖ ^ 2) := by
    rw [sum_range_sum_range_eq]
    exact hcs _ (Finset.filter_subset _ _) (fun _ => v) fun j => errorOp V j v
  refine le_sq_mul_of_le_mul_sqrt hX hY (hsum.trans_le ?_)
  linarith

/-- **Saad's Theorem 14.9** (Saad, *Iterative Methods for Sparse Linear Systems*): under a stable
decomposition with constant `K₀` and a strengthened Cauchy–Schwarz inequality with constant `K₁`,
one multiplicative Schwarz sweep contracts the norm of the error by the factor
`√(1 - 1/(K₀ (1 + K₁)²))`, which depends on nothing but the two constants — in particular not on
the number of subdomains.  Read in the energy inner product, this is contraction of the energy
norm of the error. -/
theorem norm_errorOp_le {s : ℕ} {K₀ K₁ : ℝ} (hK₀ : 0 < K₀) (hK₁ : 0 ≤ K₁)
    (hst : IsStableDecompositionWith V s K₀)
    (hcs : IsStrengthenedCauchySchwarzWith V s K₁) (v : H) :
    ‖errorOp V s v‖ ≤ Real.sqrt (1 - 1 / (K₀ * (1 + K₁) ^ 2)) * ‖v‖ := by
  have hcpos : 0 < K₀ * (1 + K₁) ^ 2 := mul_pos hK₀ (pow_pos (by linarith) 2)
  have h39 := norm_errorOp_sq_eq V s v
  have h148 := sum_norm_starProjection_sq_le V hcs v
  have h147 := le_re_inner_additiveOperator V hst v
  rw [re_inner_additiveOperator] at h147
  have hYbound : ‖v‖ ^ 2
      ≤ (∑ i ∈ Finset.range s, ‖(V i).starProjection (errorOp V i v)‖ ^ 2)
        * (K₀ * (1 + K₁) ^ 2) := by
    have h := h147.trans h148
    rw [div_le_iff₀ hK₀] at h
    linarith
  have hsq : ‖errorOp V s v‖ ^ 2 ≤ (1 - 1 / (K₀ * (1 + K₁) ^ 2)) * ‖v‖ ^ 2 := by
    have hdiv : ‖v‖ ^ 2 / (K₀ * (1 + K₁) ^ 2)
        ≤ ∑ i ∈ Finset.range s, ‖(V i).starProjection (errorOp V i v)‖ ^ 2 :=
      (div_le_iff₀ hcpos).2 hYbound
    have hid : (1 - 1 / (K₀ * (1 + K₁) ^ 2)) * ‖v‖ ^ 2
        = ‖v‖ ^ 2 - ‖v‖ ^ 2 / (K₀ * (1 + K₁) ^ 2) := by
      rw [sub_mul, one_mul, div_mul_eq_mul_div, one_mul]
    rw [h39, hid]
    linarith
  calc ‖errorOp V s v‖ = Real.sqrt (‖errorOp V s v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1 - 1 / (K₀ * (1 + K₁) ^ 2)) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (1 - 1 / (K₀ * (1 + K₁) ^ 2)) * ‖v‖ := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg v)]

/-! ### The energy geometry: Schwarz projectors of a symmetric coercive operator -/

section Energy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The Schwarz subdomain projector** of a symmetric coercive `A`: the `A`-orthogonal projector
onto a finite-dimensional subspace `K`, obtained by transporting `Submodule.starProjection` of the
energy space `WithEnergy A hA` back along `WithEnergy.equiv`.  Classically it is written
`R_iᵀ A_i⁻¹ R_i A` for a boolean restriction `R_i` with `range R_iᵀ = K`, and
`Schwarz.energyProjection_eq_of_galerkinCoarse` is that formula; the definition here needs neither
a basis of `K` nor an inverse.  It is `Multigrid.coarseProjection` with the subspace given
directly instead of as the range of a prolongation. -/
noncomputable def energyProjection (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive)
    (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] : E →ₗ[𝕜] E :=
  (WithEnergy.equiv A hA).symm.toLinearMap ∘ₗ
    (WithEnergy.submoduleMap A hA K).starProjection.toLinearMap ∘ₗ
      (WithEnergy.equiv A hA).toLinearMap

variable (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive) (K : Submodule 𝕜 E)
  [FiniteDimensional 𝕜 K]

@[simp]
theorem equiv_energyProjection (x : E) :
    WithEnergy.equiv A hA (energyProjection A hA K x)
      = (WithEnergy.submoduleMap A hA K).starProjection (WithEnergy.equiv A hA x) :=
  rfl

/-- The Schwarz subdomain projector takes its values in the subspace. -/
theorem energyProjection_apply_mem (x : E) : energyProjection A hA K x ∈ K := by
  rw [← WithEnergy.equiv_mem_submoduleMap_iff A hA, equiv_energyProjection]
  exact Submodule.starProjection_apply_mem _ _

/-- The Schwarz subdomain projector fixes the subspace. -/
theorem energyProjection_apply_of_mem {x : E} (hx : x ∈ K) : energyProjection A hA K x = x :=
  (WithEnergy.equiv A hA).injective
    (Submodule.starProjection_eq_self_iff.2 ((WithEnergy.equiv_mem_submoduleMap_iff A hA).2 hx))

/-- **The defining property of a Schwarz subdomain solve**: correcting the iterate `x` by the
subdomain projection of its error produces the Galerkin iterate of `A y = b` on `x + K`.  This is
what identifies "solve the system restricted to the subdomain and add the correction" with a
projection step, and hence makes `Numlib/LinearSolve/Projection` apply to Schwarz methods. -/
theorem energyProjection_isGalerkin {b x xstar : E} (hstar : A xstar = b) :
    IsGalerkin A b x K (x + energyProjection A hA K (xstar - x)) := by
  refine ⟨by simpa using energyProjection_apply_mem A hA K (xstar - x), ?_⟩
  have hres : b - A (x + energyProjection A hA K (xstar - x))
      = A (xstar - x - energyProjection A hA K (xstar - x)) := by
    rw [← hstar]
    simp only [map_add, map_sub]
    abel
  refine (Submodule.mem_orthogonal _ _).2 fun w hw => ?_
  have hmem : WithEnergy.equiv A hA w ∈ WithEnergy.submoduleMap A hA K :=
    (WithEnergy.equiv_mem_submoduleMap_iff A hA).2 hw
  have hsub : WithEnergy.equiv A hA (xstar - x - energyProjection A hA K (xstar - x))
      ∈ (WithEnergy.submoduleMap A hA K)ᗮ := by
    rw [map_sub, equiv_energyProjection]
    exact Submodule.sub_starProjection_mem_orthogonal _
  have h0 := (Submodule.mem_orthogonal' _ _).1 hsub _ hmem
  rw [WithEnergy.inner_equiv] at h0
  rw [hres, ← inner_conj_symm]
  exact (congrArg (starRingEnd 𝕜) h0).trans (map_zero _)

/-- The Schwarz subdomain projector agrees with the coarse-grid projector of
`Numlib/LinearSolve/Multigrid/Basic.lean` on the range of a prolongation: they are one object,
seen once with the subspace named and once with a map onto it. -/
theorem energyProjection_range {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] (Pr : F →ₗ[𝕜] E) :
    energyProjection A hA (LinearMap.range Pr) = Multigrid.coarseProjection A hA Pr :=
  rfl

/-- **Saad's formula `P_i = R_iᵀ A_i⁻¹ R_i A`** (Saad, *Iterative Methods for Sparse Linear
Systems*, (14.24)) written without an inverse: if `y` solves the subdomain problem
`A_i y = R_i A x` for the Galerkin subdomain operator `A_i = R_i A R_iᵀ`, then the subdomain
projection of `x` is `R_iᵀ y`. -/
theorem energyProjection_eq_of_galerkinCoarse {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 E] (Pr : F →ₗ[𝕜] E)
    {x : E} {y : F} (hy : Multigrid.galerkinCoarse A Pr y = LinearMap.adjoint Pr (A x)) :
    energyProjection A hA (LinearMap.range Pr) x = Pr y :=
  Multigrid.coarseProjection_apply_eq A hA Pr hy

end Energy

/-! ### Schwarz sweeps are projection processes -/

section Sweep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For symmetric coercive `A` a subspace is a nondegenerate Galerkin pair with itself, so the
projection processes of `Numlib/LinearSolve/Projection/Additive.lean` are available for any family
of subspaces. -/
theorem isNondegeneratePair_self {A : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive)
    (K : Submodule 𝕜 E) : Projection.IsNondegeneratePair A K K := by
  refine ⟨rfl, fun z hz horth => ?_⟩
  by_contra hz0
  have h : inner 𝕜 z (A z) = (0 : 𝕜) := (Submodule.mem_orthogonal K (A z)).1 horth z hz
  have h2 : inner 𝕜 (A z) z = (0 : 𝕜) := by
    rw [← inner_conj_symm, h, map_zero]
  have hpos := hA.isCoercive.inner_self_pos hz0
  rw [h2] at hpos
  simp at hpos

/-- **One subdomain solve is one Schwarz projection**: the error left by a Petrov–Galerkin step on
the pair `(K, K)` is `(1 - P) e` for the `A`-orthogonal projector `P` onto `K`.  Saad's residual
projectors of §5.4 and his error projectors of §14.3 are conjugate by `A`, and this is that
conjugation. -/
theorem equiv_error_pairStep {A : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive) {b : E}
    (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K]
    (h : Projection.IsNondegeneratePair A K K) {xstar : E} (hstar : A xstar = b) (y : E) :
    WithEnergy.equiv A hA (xstar - Projection.pairStep A b K K h y)
      = (1 - (WithEnergy.submoduleMap A hA K).starProjection)
          (WithEnergy.equiv A hA (xstar - y)) := by
  have hg : IsGalerkin A b y K (Projection.pairStep A b K K h y) :=
    Projection.pairStep_isPetrovGalerkin h y
  rw [IsGalerkin.error_eq_starProjection hA hg hstar, Submodule.starProjection_orthogonal']

/-- **A multiplicative Schwarz sweep is a multiplicative projection sweep** (Saad, *Iterative
Methods for Sparse Linear Systems*, Algorithm 5.6 and §14.3.1): the error left by sweeping over
the subspaces `W 0, …, W (s-1)` in order is `Q s` applied to the initial error, read in the energy
inner product.  Everything proved about `Schwarz.errorOp` therefore applies to the sweep. -/
theorem error_multiplicativeStep_eq_errorOp {A : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive) {b : E}
    (W : ℕ → Submodule 𝕜 E) [∀ i, FiniteDimensional 𝕜 (W i)]
    (h : ∀ i, Projection.IsNondegeneratePair A (W i) (W i)) {xstar : E} (hstar : A xstar = b)
    (s : ℕ) (x : E) :
    WithEnergy.equiv A hA (xstar - Projection.multiplicativeStep A b W W h (List.range s) x)
      = errorOp (fun i => WithEnergy.submoduleMap A hA (W i)) s
          (WithEnergy.equiv A hA (xstar - x)) := by
  have hfold : ∀ (l : List ℕ) (y : E), Projection.multiplicativeStep A b W W h l y
      = l.foldl (fun z i => Projection.pairStep A b (W i) (W i) (h i) z) y := fun _ _ => rfl
  induction s with
  | zero => simp [hfold]
  | succ s ih =>
      have hstep : Projection.multiplicativeStep A b W W h (List.range (s + 1)) x
          = Projection.pairStep A b (W s) (W s) (h s)
              (Projection.multiplicativeStep A b W W h (List.range s) x) := by
        rw [hfold, hfold, List.range_succ]
        simp
      rw [hstep, equiv_error_pairStep hA (W s) (h s) hstar, ih, errorOp_succ_apply]
      rfl

/-- **An additive Schwarz sweep is an additive projection sweep** (Saad, *Iterative Methods for
Sparse Linear Systems*, Algorithm 5.5 and §14.3.2): with unit weights, the error left by adding
all the subdomain corrections at once is `1 - A_J` applied to the initial error, for the additive
Schwarz operator `A_J = ∑ P i` of the family.  With `ι = Fin s` the operator is
`Schwarz.additiveOperator`, by `Finset.sum_range`. -/
theorem error_additiveStep_eq {ι : Type*} [Fintype ι] {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetricCoercive) {b : E} (W : ι → Submodule 𝕜 E)
    [∀ i, FiniteDimensional 𝕜 (W i)]
    (h : ∀ i, Projection.IsNondegeneratePair A (W i) (W i)) {xstar : E} (hstar : A xstar = b)
    (x : E) :
    WithEnergy.equiv A hA (xstar - Projection.additiveStep A b W W h 1 x)
      = (1 - ∑ i, (WithEnergy.submoduleMap A hA (W i)).starProjection)
          (WithEnergy.equiv A hA (xstar - x)) := by
  have hpair : ∀ i, WithEnergy.equiv A hA (Projection.pairStep A b (W i) (W i) (h i) x - x)
      = (WithEnergy.submoduleMap A hA (W i)).starProjection
          (WithEnergy.equiv A hA (xstar - x)) := by
    intro i
    have h1 := equiv_error_pairStep hA (W i) (h i) hstar x
    have h2 : Projection.pairStep A b (W i) (W i) (h i) x - x
        = xstar - x - (xstar - Projection.pairStep A b (W i) (W i) (h i) x) := by abel
    rw [h2, map_sub, h1, sub_apply, one_apply_eq_self]
    abel
  have hadd : Projection.additiveStep A b W W h 1 x
      = x + ∑ i, (Projection.pairStep A b (W i) (W i) (h i) x - x) := by
    have hdef : Projection.additiveStep A b W W h 1 x
        = x + ∑ i, (1 : ι → 𝕜) i • (Projection.pairStep A b (W i) (W i) (h i) x - x) := rfl
    rw [hdef]
    simp
  have hsub : xstar - Projection.additiveStep A b W W h 1 x
      = xstar - x - ∑ i, (Projection.pairStep A b (W i) (W i) (h i) x - x) := by
    rw [hadd]; abel
  rw [hsub, map_sub, map_sum, sub_apply, one_apply_eq_self, sum_apply]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => hpair i)

end Sweep

end Schwarz
