/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.CG
import Numlib.Multigrid.Basic
import Numlib.Projection.Additive

/-!
# The abstract Schwarz theory

A **Schwarz method** solves a linear system by repeatedly solving it on a family of subspaces, as in
§14.3 of [saad2003iterative]. Its convergence theory is a statement about a finite family of
subspaces $V_0, \dots, V_{s-1}$ of an inner product space $H$ over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, and their orthogonal projectors $P_i$. Two operators carry the theory: the **additive
Schwarz operator** $A_J = \sum_{i < s} P_i$, which is the preconditioned operator of the additive
method, and the **multiplicative error operator** $Q_s = (I - P_{s-1}) \cdots (I - P_0)$, which is
what one sweep of the multiplicative method does to the error. Convergence rests on two constants
that linear algebra alone cannot produce, because they are properties of a discretization. A
**stable decomposition** with constant $K_0$ splits every $u \in H$ as $u = \sum_i w_i$ with
$w_i \in V_i$ and $\sum_i \|w_i\|^2 \le K_0 \|u\|^2$. A **strengthened Cauchy–Schwarz inequality**
with constant $K_1$ measures how far the subspaces are from being mutually orthogonal. Under the
first, the spectrum of $A_J$ lies in $[1/K_0, s]$, and the conjugate gradient method for $A_J$
converges at the rate of the condition number $s K_0$. Under both, one multiplicative sweep
contracts the norm of the error by $\sqrt{1 - 1/(K_0 (1 + K_1)^2)}$.

No domain, mesh or restriction matrix occurs in the theory. For a symmetric coercive operator $A$,
the classical subdomain projector $P_i = R_i^T A_i^{-1} R_i A$ is the orthogonal projector onto the
range of $R_i^T$ in the energy inner product $\langle x, y \rangle_A = \langle A x, y \rangle$, and
$A_i = R_i A R_i^T$ is the Galerkin coarse operator of that subspace. The theory is therefore
applied with $H$ the energy space of $A$. The last two sections identify a Schwarz sweep with the
multiplicative and additive projection processes of `Numlib.Projection.Additive`. Those processes
act on residuals and the Schwarz operators act on errors, and the two are conjugate by $A$.

## Main definitions

* `Schwarz.IsStableDecompositionWith`: every vector splits over the family with
  $\sum_i \|w_i\|^2 \le K_0 \|u\|^2$.
* `Schwarz.IsStrengthenedCauchySchwarzWith`: the strengthened Cauchy–Schwarz inequality with
  constant $K_1$.
* `Schwarz.additiveOperator`: the additive Schwarz operator $A_J = \sum_{i < s} P_i$.
* `Schwarz.errorOp`: the error operator $Q_s = (I - P_{s-1}) \cdots (I - P_0)$ of a multiplicative
  sweep.
* `Schwarz.energyProjection`: the $A$-orthogonal projector onto a finite-dimensional subspace, for a
  symmetric coercive $A$.

## Main results

* `Schwarz.inner_sum_le`: the vector-valued Cauchy–Schwarz inequality.
* `Schwarz.re_inner_additiveOperator_le`: $\operatorname{Re} \langle A_J u, u \rangle \le s \|u\|^2$
  (Theorem 14.5 of [saad2003iterative]).
* `Schwarz.re_inner_additiveOperator_le_of_coloring`: $\operatorname{Re} \langle A_J u, u \rangle$
  is at most the number of colours times $\|u\|^2$, for a colouring of the family by mutual
  orthogonality (Theorem 14.6).
* `Schwarz.le_re_inner_additiveOperator`: under a stable decomposition, $\|u\|^2 / K_0 \le
  \operatorname{Re} \langle A_J u, u \rangle$ (Theorem 14.7).
* `Schwarz.isSymmetricBoundedBy_additiveOperator`: $A_J$ is symmetric with spectral bounds $1/K_0$
  and $s$.
* `Schwarz.energyNorm_error_le`: the convergence rate of the conjugate gradient method for $A_J$.
* `Schwarz.one_sub_errorOp_eq_sum`: $I - Q_s = \sum_{i < s} P_i Q_i$ (Lemma 14.4).
* `Schwarz.norm_errorOp_sq_eq`: $\|Q_s v\|^2 = \|v\|^2 - \sum_{i < s} \|P_i Q_i v\|^2$.
* `Schwarz.sum_norm_starProjection_sq_le`: under a strengthened Cauchy–Schwarz inequality, $\sum_{i
  < s} \|P_i v\|^2 \le (1 + K_1)^2 \sum_{i < s} \|P_i Q_i v\|^2$ (Lemma 14.8).
* `Schwarz.norm_errorOp_le`: $\|Q_s v\| \le \sqrt{1 - 1/(K_0 (1 + K_1)^2)} \, \|v\|$ (Theorem 14.9).
* `Schwarz.energyProjection_isGalerkin`: a subdomain correction is a Galerkin step.
* `Schwarz.energyProjection_eq_of_galerkinCoarse`: the formula $P_i = R_i^T A_i^{-1} R_i A$ of
  (14.24).
* `Schwarz.error_multiplicativeStep_eq_errorOp` and `Schwarz.error_additiveStep_eq`: the errors of
  the multiplicative and additive projection sweeps are $Q_s$ and $I - \sum_i P_i$ applied to the
  initial error.

## Proof outline

The upper bounds on $A_J$ follow from $\operatorname{Re} \langle A_J u, u \rangle = \sum_i \|P_i
u\|^2$ and Bessel's inequality. For the lower bound, write $u = \sum_i w_i$ with $w_i \in V_i$. Then
$\langle w_i, u \rangle = \langle w_i, P_i u \rangle$, and the vector-valued Cauchy–Schwarz
inequality bounds $\|u\|^2$ by the root-mean-square norms of $(w_i)$ and $(P_i u)$. The contraction
of a multiplicative sweep combines the telescoping identity for $\|Q_s v\|^2$ with Lemma 14.8, whose
proof also uses the vector-valued Cauchy–Schwarz inequality.

## Implementation notes

* The subspaces are a function `V : ℕ → Submodule 𝕜 H`, and the first $s$ of them are used. The
  indices start at $0$, so the sweep corrects on $V_0, V_1, \dots, V_{s-1}$ in this order.
* The orthogonal projector $P_i$ is `(V i).starProjection`.
* The theory is stated in an arbitrary inner product space. It is applied to a symmetric coercive
  operator $A$ in the energy space `WithEnergy A hA`, and `WithEnergy.equiv` and
  `WithEnergy.submoduleMap` transport vectors and subspaces to it.
* `Schwarz.energyProjection` is `Multigrid.coarseProjection` of `Numlib.Multigrid.Basic` with the
  subspace given directly instead of as the range of a prolongation
  (`Schwarz.energyProjection_range`).
-/

namespace Schwarz

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ### The vector-valued Cauchy–Schwarz inequality -/

/-- The **vector-valued Cauchy–Schwarz inequality**: for a finite index set $t$ and families
$(x_i)$, $(y_i)$ in $H$,
$$\sum_{i \in t} \operatorname{Re} \langle x_i, y_i \rangle
  \le \Big( \sum_{i \in t} \|x_i\|^2 \Big)^{1/2} \Big( \sum_{i \in t} \|y_i\|^2 \Big)^{1/2}.$$

The proof applies the Cauchy–Schwarz inequality to each term, and then the Cauchy–Schwarz
inequality for finite sums of reals. Compare Exercise 14.1 of [saad2003iterative]. -/
theorem inner_sum_le {ι : Type*} (t : Finset ι) (x y : ι → H) :
    ∑ i ∈ t, RCLike.re (inner 𝕜 (x i) (y i))
      ≤ Real.sqrt (∑ i ∈ t, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ t, ‖y i‖ ^ 2) :=
  (Finset.sum_le_sum fun i _ =>
      (RCLike.re_le_norm _).trans (norm_inner_le_norm (x i) (y i))).trans
    (Real.sum_mul_le_sqrt_mul_sqrt t _ _)

/-! ### Orthogonal projectors onto a family of subspaces -/

section Projectors

variable (K : Submodule 𝕜 H) [K.HasOrthogonalProjection]

/-- For a subspace $K$ with orthogonal projector $P$, $\operatorname{Re} \langle P u, u \rangle =
\|P u\|^2$. -/
theorem re_inner_starProjection_self (u : H) :
    RCLike.re (inner 𝕜 (K.starProjection u) u) = ‖K.starProjection u‖ ^ 2 := by
  have h : inner 𝕜 (u - K.starProjection u) (K.starProjection u) = (0 : 𝕜) :=
    K.starProjection_inner_eq_zero u _ (K.starProjection_apply_mem u)
  have h2 : inner 𝕜 u (K.starProjection u)
      = inner 𝕜 (K.starProjection u) (K.starProjection u) := by
    rw [← sub_eq_zero, ← inner_sub_left]
    exact h
  rw [← inner_conj_symm, h2, RCLike.conj_re, inner_self_eq_norm_sq]

/-- For a subspace $K$ with orthogonal projector $P$, $\langle P a, P b \rangle = \langle P a, b
\rangle$. -/
theorem inner_starProjection_starProjection (a b : H) :
    inner 𝕜 (K.starProjection a) (K.starProjection b) = inner 𝕜 (K.starProjection a) b := by
  have hidem : K.starProjection (K.starProjection b) = K.starProjection b :=
    Submodule.starProjection_eq_self_iff.2 (K.starProjection_apply_mem b)
  rw [Submodule.inner_starProjection_left_eq_right K a (K.starProjection b), hidem,
    ← Submodule.inner_starProjection_left_eq_right K a b]

end Projectors

/-- **Bessel's inequality for pairwise orthogonal subspaces**: let $(W_i)_{i \in t}$ be a finite
family of subspaces of $H$ with orthogonal projectors, such that $W_i \perp W_j$ for $i \neq j$
in $t$. Then for every $u \in H$,
$$\sum_{i \in t} \|P_{W_i} u\|^2 \le \|u\|^2.$$

The inequality is used in the proof of Theorem 14.6 of [saad2003iterative]. -/
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

/-- A **stable decomposition** over the subspaces $V_0, \dots, V_{s-1}$ with constant
$K_0 \in \mathbb{R}$: every $u \in H$ can be written as $u = \sum_{i < s} w_i$ with
$w_i \in V_i$ and
$$\sum_{i < s} \|w_i\|^2 \le K_0 \|u\|^2.$$
This is Assumption 1 of §14.3.4 of [saad2003iterative].

The hypothesis says that the subspaces cover the space stably. It does not follow from the
algebra; for a finite-element family, a partition of unity over overlapping subdomains provides
it. -/
def IsStableDecompositionWith (s : ℕ) (K₀ : ℝ) : Prop :=
  ∀ u : H, ∃ w : ℕ → H, (∀ i ∈ Finset.range s, w i ∈ V i) ∧ ∑ i ∈ Finset.range s, w i = u ∧
    ∑ i ∈ Finset.range s, ‖w i‖ ^ 2 ≤ K₀ * ‖u‖ ^ 2

/-- A **strengthened Cauchy–Schwarz inequality** for $V_0, \dots, V_{s-1}$ with constant
$K_1 \in \mathbb{R}$: for every set $S$ of pairs $(i, j)$ with $i, j < s$ and all families
$(x_i)$, $(y_j)$ in $H$,
$$\sum_{(i, j) \in S} \operatorname{Re} \langle P_i x_i, P_j y_j \rangle \le K_1 \Big( \sum_{i <
  s} \|P_i x_i\|^2 \Big)^{1/2} \Big( \sum_{j < s} \|P_j y_j\|^2 \Big)^{1/2}.$$
This is Assumption 2 of §14.3.4 of [saad2003iterative], inequality (14.40).

The constant measures how far the subspaces are from being mutually orthogonal. Pairwise
orthogonal subspaces admit $K_1 = 1$, because then only the diagonal pairs in $S$ contribute.
The plain Cauchy–Schwarz inequality always gives $K_1 = s$. The set $S$ may contain diagonal
pairs $(i, i)$. -/
def IsStrengthenedCauchySchwarzWith (s : ℕ) (K₁ : ℝ) : Prop :=
  ∀ S : Finset (ℕ × ℕ), S ⊆ Finset.range s ×ˢ Finset.range s → ∀ x y : ℕ → H,
    ∑ ij ∈ S, RCLike.re (inner 𝕜 ((V ij.1).starProjection (x ij.1))
        ((V ij.2).starProjection (y ij.2)))
      ≤ K₁ * Real.sqrt (∑ i ∈ Finset.range s, ‖(V i).starProjection (x i)‖ ^ 2)
        * Real.sqrt (∑ j ∈ Finset.range s, ‖(V j).starProjection (y j)‖ ^ 2)

/-! ### The additive Schwarz operator -/

/-- The **additive Schwarz operator** $A_J = \sum_{i < s} P_i$, the sum of the orthogonal projectors
onto $V_0, \dots, V_{s-1}$, as in (14.37) of [saad2003iterative].

In the energy inner product of an operator $A$, it is the preconditioned operator $M^{-1} A$ of
the additive Schwarz method. -/
noncomputable def additiveOperator (s : ℕ) : H →L[𝕜] H :=
  ∑ i ∈ Finset.range s, (V i).starProjection

/-- $A_J u = \sum_{i < s} P_i u$. -/
@[simp]
theorem additiveOperator_apply (s : ℕ) (u : H) :
    additiveOperator V s u = ∑ i ∈ Finset.range s, (V i).starProjection u := by
  rw [additiveOperator, sum_apply]

/-- The additive Schwarz operator $A_J$ is symmetric, because it is a sum of orthogonal projectors.
-/
theorem additiveOperator_isSymmetric (s : ℕ) :
    (additiveOperator V s : H →ₗ[𝕜] H).IsSymmetric := by
  intro u v
  change inner 𝕜 (additiveOperator V s u) v = inner 𝕜 u (additiveOperator V s v)
  rw [additiveOperator_apply, additiveOperator_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl fun i _ => Submodule.inner_starProjection_left_eq_right _ u v

/-- The quadratic form of the additive Schwarz operator is the sum of the squared norms of the
projections:
$$\operatorname{Re} \langle A_J u, u \rangle = \sum_{i < s} \|P_i u\|^2.$$
-/
theorem re_inner_additiveOperator (s : ℕ) (u : H) :
    RCLike.re (inner 𝕜 (additiveOperator V s u) u)
      = ∑ i ∈ Finset.range s, ‖(V i).starProjection u‖ ^ 2 := by
  rw [additiveOperator_apply, sum_inner, map_sum]
  exact Finset.sum_congr rfl fun i _ => re_inner_starProjection_self (V i) u

/-- The additive Schwarz operator is positive semidefinite: $0 \le \operatorname{Re} \langle A_J u,
u \rangle$. -/
theorem re_inner_additiveOperator_nonneg (s : ℕ) (u : H) :
    0 ≤ RCLike.re (inner 𝕜 (additiveOperator V s u) u) := by
  rw [re_inner_additiveOperator]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The largest eigenvalue of the additive Schwarz operator is at most the number of subspaces: for
every $u \in H$,
$$\operatorname{Re} \langle A_J u, u \rangle \le s \|u\|^2.$$
This is Theorem 14.5 of [saad2003iterative].

Each projector does not increase the norm, and the quadratic form is the sum of the squared
norms of the projections. -/
theorem re_inner_additiveOperator_le (s : ℕ) (u : H) :
    RCLike.re (inner 𝕜 (additiveOperator V s u) u) ≤ s * ‖u‖ ^ 2 := by
  rw [re_inner_additiveOperator]
  calc ∑ i ∈ Finset.range s, ‖(V i).starProjection u‖ ^ 2
      ≤ ∑ _i ∈ Finset.range s, ‖u‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := Submodule.norm_starProjection_apply_le (V i) u
        nlinarith [norm_nonneg ((V i).starProjection u)]
    _ = s * ‖u‖ ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The largest eigenvalue of the additive Schwarz operator is at most the number of colours. Let
$\kappa$ be a finite set of colours and $c : \mathbb{N} \to \kappa$ a colouring such that
$V_i \perp V_j$ whenever $i \neq j$, $i, j < s$ and $c(i) = c(j)$. Then for every $u \in H$,
$$\operatorname{Re} \langle A_J u, u \rangle \le |\kappa| \, \|u\|^2.$$
This is Theorem 14.6 of [saad2003iterative].

Each colour class contributes at most $\|u\|^2$ by Bessel's inequality
(`Schwarz.sum_norm_starProjection_sq_le_of_pairwise_orthogonal`). A colouring of the interaction
graph of the subdomains thus replaces the bound $s$ of `Schwarz.re_inner_additiveOperator_le`,
the number of subspaces, by the number of colours. -/
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

/-- The smallest eigenvalue of the additive Schwarz operator is at least $1/K_0$: if the subspaces
admit a stable decomposition with constant $K_0$, then for every $u \in H$,
$$\frac{\|u\|^2}{K_0} \le \operatorname{Re} \langle A_J u, u \rangle.$$
This is Theorem 14.7 of [saad2003iterative].

No sign condition on $K_0$ is needed, because the division is that of `Real`, with $x / 0 = 0$.
The proof writes $u = \sum_i w_i$ with $w_i \in V_i$, uses $\langle w_i, u \rangle = \langle
w_i, P_i u \rangle$, and applies the vector-valued Cauchy–Schwarz inequality
`Schwarz.inner_sum_le`. -/
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

/-- The **spectral equivalence of the additive Schwarz preconditioner**: if the subspaces admit a
stable decomposition with constant $K_0$, then $A_J$ is symmetric and
$$\frac{1}{K_0} \|u\|^2 \le \operatorname{Re} \langle A_J u, u \rangle \le s \|u\|^2 \quad
  \text{for all } u \in H.$$
This is Theorems 14.5 and 14.7 of [saad2003iterative] together.

The conclusion is `LinearMap.IsSymmetricBoundedBy` with bounds $1/K_0$ and $s$, the hypothesis
of every Chebyshev-type convergence bound of the library. For $K_0 > 0$, the condition number of
the additive Schwarz preconditioned system is therefore at most $s K_0$. -/
theorem isSymmetricBoundedBy_additiveOperator {s : ℕ} {K₀ : ℝ}
    (hst : IsStableDecompositionWith V s K₀) :
    (additiveOperator V s : H →ₗ[𝕜] H).IsSymmetricBoundedBy (1 / K₀) s :=
  ⟨additiveOperator_isSymmetric V s,
    fun u => by
      rw [one_div, inv_mul_eq_div]
      exact le_re_inner_additiveOperator V hst u,
    fun u => re_inner_additiveOperator_le V s u⟩

/-- **Convergence of additive Schwarz preconditioned conjugate gradients.** Let $H$ be nontrivial,
let $K_0 > 0$, and let the subspaces admit a stable decomposition with constant $K_0$. Let $x^*$
solve $A_J x^* = b$, and let $x$ be the Galerkin Krylov iterate at step $m$ of $A_J x = b$ from
$x_0$. Then
$$\|x^* - x\|_{A_J} \le 2 \left( \frac{\sqrt{s K_0} - 1}{\sqrt{s K_0} + 1} \right)^m \|x^* -
  x_0\|_{A_J}.$$

The energy norm $\|v\|_{A_J} = \sqrt{\operatorname{Re} \langle A_J v, v \rangle}$ is
`energyNorm`, and the Galerkin iterate is `Krylov.IsGalerkinIterate`. The proof applies the
Chebyshev bound `Krylov.IsGalerkinIterate.energyNorm_error_le` with the spectral bounds of
`Schwarz.isSymmetricBoundedBy_additiveOperator`. -/
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

/-- The **error operator of a multiplicative Schwarz sweep**: $Q_0 = I$ and
$Q_{i+1} = (I - P_i) Q_i$, so that
$$Q_s = (I - P_{s-1}) \cdots (I - P_0)$$
corrects on the subspaces in the order $V_0, V_1, \dots, V_{s-1}$. This is the operator of
(14.25)–(14.26) of [saad2003iterative].

The operator is indexed by $\mathbb{N}$ and not by `Fin s`. The recursion is then definitional,
and all the prefixes $Q_0, Q_1, \dots$ are available, as the telescoping identity
`Schwarz.norm_errorOp_sq_eq` needs. -/
noncomputable def errorOp : ℕ → H →L[𝕜] H
  | 0 => 1
  | i + 1 => (1 - (V i).starProjection) ∘L errorOp i

/-- An empty sweep is the identity: $Q_0 = I$. -/
@[simp]
theorem errorOp_zero : errorOp V 0 = 1 := rfl

/-- One more subdomain correction composes $I - P_i$ onto the sweep: $Q_{i+1} = (I - P_i) Q_i$. -/
theorem errorOp_succ (i : ℕ) :
    errorOp V (i + 1) = (1 - (V i).starProjection) ∘L errorOp V i := rfl

/-- $Q_{i+1} v = Q_i v - P_i Q_i v$. -/
@[simp]
theorem errorOp_succ_apply (i : ℕ) (v : H) :
    errorOp V (i + 1) v = errorOp V i v - (V i).starProjection (errorOp V i v) := rfl

/-- What a multiplicative sweep adds to the iterate: for every $s \in \mathbb{N}$,
$$I - Q_s = \sum_{i < s} P_i Q_i.$$
This is Lemma 14.4 of [saad2003iterative], in the form (14.35).

Equivalently, the sweep is the fixed-point iteration whose preconditioned operator is $I - Q_s$. -/
theorem one_sub_errorOp_eq_sum (s : ℕ) :
    1 - errorOp V s = ∑ i ∈ Finset.range s, (V i).starProjection ∘L errorOp V i := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.sum_range_succ, ← ih, errorOp_succ]
      ext v
      simp only [sub_apply, add_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply]
      abel

/-- $v - Q_s v = \sum_{i < s} P_i Q_i v$ for every $v \in H$. -/
theorem sub_errorOp_apply (s : ℕ) (v : H) :
    v - errorOp V s v = ∑ i ∈ Finset.range s, (V i).starProjection (errorOp V i v) := by
  have h := congrArg (fun T : H →L[𝕜] H => T v) (one_sub_errorOp_eq_sum V s)
  simpa using h

/-- The **telescoping identity of a multiplicative sweep**: for every $v \in H$,
$$\|Q_s v\|^2 = \|v\|^2 - \sum_{i < s} \|P_i Q_i v\|^2.$$
This is (14.39) of [saad2003iterative].

In particular, a sweep never increases the norm of the error, and the convergence rate follows
from a lower bound for the sum on the right. -/
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

/-- If $0 \le X$, $0 \le Y$ and $X \le c \sqrt{X} \sqrt{Y}$, then $X \le c^2 Y$. -/
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

/-- A double sum over $j < i < s$ equals the sum over the pairs $(i, j)$ with $i, j < s$ and
$j < i$. -/
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

/-- If the subspaces satisfy a strengthened Cauchy–Schwarz inequality with constant $K_1$, then for
every $v \in H$ the projections of $v$ are controlled by the projections of the partially swept
vectors:
$$\sum_{i < s} \|P_i v\|^2 \le (1 + K_1)^2 \sum_{i < s} \|P_i Q_i v\|^2.$$
This is Lemma 14.8 of [saad2003iterative].

The proof splits $P_i v$ along $v = Q_i v + (I - Q_i) v$ and expands the second part by (14.35).
This gives a diagonal sum, bounded by the vector-valued Cauchy–Schwarz inequality, and a
strictly lower triangular sum, bounded by the hypothesis. -/
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

/-- **Convergence of the multiplicative Schwarz method.** Let $K_0 > 0$ and $K_1 \ge 0$, and let the
subspaces admit a stable decomposition with constant $K_0$ and satisfy a strengthened
Cauchy–Schwarz inequality with constant $K_1$. Then for every $v \in H$,
$$\|Q_s v\| \le \sqrt{1 - \frac{1}{K_0 (1 + K_1)^2}} \, \|v\|.$$
This is Theorem 14.9 of [saad2003iterative].

The factor depends only on the two constants, and in particular not on the number of subspaces.
In the energy inner product, this is the contraction of the energy norm of the error. -/
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

/-- Let $A$ be a symmetric coercive operator on $E$, and let $K$ be a finite-dimensional subspace.
The **Schwarz subdomain projector** onto $K$ is the $A$-orthogonal projector $P_K$: the linear
map with $P_K x \in K$ and $\langle A (x - P_K x), z \rangle = 0$ for all $z \in K$. As in
(14.24) of [saad2003iterative], it is classically written $R_i^T A_i^{-1} R_i A$ for a
restriction $R_i$ with range of $R_i^T$ equal to $K$.

The definition transports the orthogonal projector `Submodule.starProjection` of the energy
space `WithEnergy A hA` back along `WithEnergy.equiv`, so it needs neither a basis of $K$ nor an
inverse. The classical formula is `Schwarz.energyProjection_eq_of_galerkinCoarse`. The projector
is `Multigrid.coarseProjection` with the subspace given directly instead of as the range of a
prolongation. -/
noncomputable def energyProjection (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive)
    (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] : E →ₗ[𝕜] E :=
  (WithEnergy.equiv A hA).symm.toLinearMap ∘ₗ
    (WithEnergy.submoduleMap A hA K).starProjection.toLinearMap ∘ₗ
      (WithEnergy.equiv A hA).toLinearMap

variable (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive) (K : Submodule 𝕜 E)
  [FiniteDimensional 𝕜 K]

/-- In the energy space, the subdomain projector is the orthogonal projector onto the image of $K$.
This holds by definition, and the proofs below use it to pass to the energy space. -/
@[simp]
theorem equiv_energyProjection (x : E) :
    WithEnergy.equiv A hA (energyProjection A hA K x)
      = (WithEnergy.submoduleMap A hA K).starProjection (WithEnergy.equiv A hA x) :=
  rfl

/-- The subdomain projector takes values in $K$: $P_K x \in K$. -/
theorem energyProjection_apply_mem (x : E) : energyProjection A hA K x ∈ K := by
  rw [← WithEnergy.equiv_mem_submoduleMap_iff A hA, equiv_energyProjection]
  exact Submodule.starProjection_apply_mem _ _

/-- The subdomain projector fixes $K$: $P_K x = x$ for $x \in K$. -/
theorem energyProjection_apply_of_mem {x : E} (hx : x ∈ K) : energyProjection A hA K x = x :=
  (WithEnergy.equiv A hA).injective
    (Submodule.starProjection_eq_self_iff.2 ((WithEnergy.equiv_mem_submoduleMap_iff A hA).2 hx))

/-- **A subdomain solve is a Galerkin step.** Let $A$ be symmetric coercive, let $K$ be a
finite-dimensional subspace, and let $A x^* = b$. Then for every $x \in E$, the corrected
iterate $x + P_K (x^* - x)$ is the Galerkin iterate of $A y = b$ over $x + K$: the correction
lies in $K$, and
$$b - A \big( x + P_K (x^* - x) \big) \perp K.$$
This is the defining property of the subdomain solve of (14.24) of [saad2003iterative].

The lemma identifies "solve the system restricted to the subdomain and add the correction" with
a projection step, so that the projection methods of `Numlib.Projection.Basic` apply to Schwarz
methods. The specification is `IsGalerkin`. -/
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

/-- Let $F$ be finite-dimensional and $\Pi : F \to E$ linear. The subdomain projector onto the range
of $\Pi$ is the coarse-grid projector `Multigrid.coarseProjection` of $\Pi$ from
`Numlib.Multigrid.Basic`: the two are one object, with the subspace given once by name and once
as the range of a map. -/
theorem energyProjection_range {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] (Pr : F →ₗ[𝕜] E) :
    energyProjection A hA (LinearMap.range Pr) = Multigrid.coarseProjection A hA Pr :=
  rfl

/-- **The formula $P_i = R_i^T A_i^{-1} R_i A$ without an inverse.** Let $E$ and $F$ be
finite-dimensional, let $A$ be symmetric coercive on $E$, and let $\Pi : F \to E$ be linear. If
$y \in F$ solves the subdomain problem
$$\Pi^* A \Pi \, y = \Pi^* A x,$$
then the subdomain projection of $x$ onto the range of $\Pi$ is $\Pi y$. This is (14.24) of
[saad2003iterative], with $\Pi = R_i^T$, $\Pi^* = R_i$ and the Galerkin subdomain operator
$A_i = R_i A R_i^T$.

The operator $\Pi^* A \Pi$ is `Multigrid.galerkinCoarse`, which uses the adjoint
`LinearMap.adjoint`. -/
theorem energyProjection_eq_of_galerkinCoarse {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 E] (Pr : F →ₗ[𝕜] E)
    {x : E} {y : F} (hy : Multigrid.galerkinCoarse A Pr y = LinearMap.adjoint Pr (A x)) :
    energyProjection A hA (LinearMap.range Pr) x = Pr y :=
  Multigrid.coarseProjection_apply_eq A hA Pr hy

end Energy

/-! ### Schwarz sweeps are projection processes -/

section Sweep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For symmetric coercive $A$ and any subspace $K$, the pair $(K, K)$ is nondegenerate: if
$z \in K$ and $A z \perp K$, then $z = 0$. Therefore the projection processes of
`Numlib.Projection.Additive` are available for any family of subspaces, as in §14.3.1 of
[saad2003iterative].

The conclusion is `Projection.IsNondegeneratePair`. -/
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

/-- Let $A$ be symmetric coercive, let $K$ be finite-dimensional with $(K, K)$ nondegenerate, and
let $A x^* = b$. In the energy space, the error after one Petrov–Galerkin step on the pair
$(K, K)$ from $y$ is $(I - P_K)(x^* - y)$, for the $A$-orthogonal projector $P_K$ onto $K$. The
residual projectors of §5.4 of [saad2003iterative] and the error projectors of §14.3 are
conjugate by $A$, and this lemma is that conjugation. -/
theorem equiv_error_pairStep {A : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive) {b : E}
    (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K]
    (h : Projection.IsNondegeneratePair A K K) {xstar : E} (hstar : A xstar = b) (y : E) :
    WithEnergy.equiv A hA (xstar - Projection.pairStep A b K K h y)
      = (1 - (WithEnergy.submoduleMap A hA K).starProjection)
          (WithEnergy.equiv A hA (xstar - y)) := by
  have hg : IsGalerkin A b y K (Projection.pairStep A b K K h y) :=
    Projection.pairStep_isPetrovGalerkin h y
  rw [IsGalerkin.error_eq_starProjection hA hg hstar, Submodule.starProjection_orthogonal']

/-- **A multiplicative Schwarz sweep is a multiplicative projection sweep.** Let $A$ be symmetric
coercive, let $W_0, W_1, \dots$ be finite-dimensional subspaces with each pair $(W_i, W_i)$
nondegenerate, and let $A x^* = b$. Let $x'$ be the result of the multiplicative projection
sweep over $W_0, \dots, W_{s-1}$, in this order, from $x$. Then, in the energy space,
$$x^* - x' = Q_s (x^* - x),$$
where $Q_s$ is the error operator `Schwarz.errorOp` of the subspaces $W_i$ in the energy space.
This connects Algorithm 5.6 and §14.3.1 of [saad2003iterative].

Every result about `Schwarz.errorOp` therefore applies to the sweep. The sweep is
`Projection.multiplicativeStep` over `List.range s`, and the energy space is reached by
`WithEnergy.equiv` and `WithEnergy.submoduleMap`. -/
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

/-- **An additive Schwarz sweep is an additive projection sweep.** Let $A$ be symmetric coercive,
let $(W_i)_{i \in \iota}$ be a finite family of finite-dimensional subspaces with each pair
$(W_i, W_i)$ nondegenerate, and let $A x^* = b$. Let $x'$ be the result of one additive
projection step with unit weights from $x$. Then, in the energy space,
$$x^* - x' = \Big( I - \sum_{i \in \iota} P_i \Big) (x^* - x),$$
where $P_i$ is the orthogonal projector onto $W_i$ in the energy space. This connects Algorithm
5.5 and §14.3.2 of [saad2003iterative].

The step is `Projection.additiveStep` with weights $1$. For $\iota = \{0, \dots, s-1\}$ the
operator $\sum_i P_i$ is `Schwarz.additiveOperator`, by `Finset.sum_range`. -/
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
