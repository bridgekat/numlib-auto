/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Circulant
import Numlib.Analysis.Fourier.Circulant
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.FiniteDifference.Stencil

/-!
# Von Neumann stability analysis on the periodic grid

A constant-coefficient explicit two-level scheme on the periodic grid of $N$ nodes is the circulant
matrix $Q$ of its stencil $c \in \mathbb{C}^N$, with $(Qu)_j = \sum_s c_s u_{j-s}$ and indices
modulo $N$. Let $\omega = e^{2\pi i / N}$. The discrete Fourier modes
$e_k \colon j \mapsto \omega^{jk}$, the columns of the Fourier matrix $F = (\omega^{jk})_{j,k}$, are
common eigenvectors of all such $Q$. The eigenvalues are the **amplification factors**
$\gamma_k = \sum_s c_s \omega^{-sk}$, the discrete Fourier transform of the stencil, and so
$Q^n e_k = \gamma_k^n e_k$ ([quarteroni2000numerical], (13.52)). A matrix $A$ with
$A e_k = \gamma_k e_k$ for every $k$ is $N^{-1} F \operatorname{diag}(\gamma) F^H$, and the discrete
Parseval identity $\|F^H y\|^2 = N \|y\|^2$ then gives $\|Au\|_2 \le \max_k |\gamma_k| \, \|u\|_2$,
with equality on the modes. This gives the two halves of the classical criterion. **Von Neumann's
sufficient condition** ([quarteroni2000numerical], Theorem 13.1): if $|\gamma_k| \le 1$ for every
$k$, then $\|Q^n u\|_2 \le \|u\|_2$ for every $n$, which is stability in $\|\cdot\|_{\Delta, 2}$
with constant $1$. **The necessary condition**: stability over a horizon $T$, $\|Q^n\| \le C$ for
$n \Delta t \le T$, forces $|\gamma_k| \le 1 + 2 (C - 1) \Delta t / T$. This is the argument by
which [quarteroni2000numerical], §13.8.4, conclude that the forward Euler/centred scheme, whose
factors satisfy $|\gamma_k| > 1$ independently of the mesh, is unconditionally unstable.

The implicit two-level scheme $B u^{n+1} = C u^n$ with circulant $B$ and $C$ has the solution
operator $B^{-1} C$, whose amplification factors are the quotients $\gamma^C_k / \gamma^B_k$. A
multi-level scheme is a two-level scheme for a vector of unknowns. Its periodic form is a block
circulant, and the modes diagonalize it into the $m \times m$ **amplification matrices**
$G_k = \sum_s \omega^{-sk} G_s$. Finally, a stencil on the line from
`Numlib.FiniteDifference.Stencil` wraps onto the periodic grid. The wrapped scheme agrees with the
stencil on $N$-periodic grid functions, and its amplification factors are the symbol of the stencil
sampled at $\varphi_k = 2\pi k / N$. For a three-point stencil this gives $\gamma_k = c_0 + c_-
e^{-i\varphi_k} + c_+ e^{i\varphi_k}$, the formula behind every entry of the stability column of
[quarteroni2000numerical], Table 13.1.

## Main definitions

* `FiniteDifference.periodicScheme`: the circulant matrix of a stencil on $N$ points.
* `FiniteDifference.fourierMode`: the Fourier mode $e_k \colon j \mapsto \omega^{jk}$.
* `FiniteDifference.amplificationFactor`: the amplification factor
  $\gamma_k = \sum_s c_s \omega^{-sk}$.
* `FiniteDifference.periodicTwoLevel`: the solution operator $B^{-1} C$ of the implicit scheme
  $B u^{n+1} = C u^n$.
* `FiniteDifference.amplificationFactor₂`: the quotient $\gamma^C_k / \gamma^B_k$.
* `FiniteDifference.Stencil.toPeriodic`: a stencil on $\mathbb{Z}$ wrapped onto $N$ points.
* `FiniteDifference.periodicBlockScheme`: the block circulant of a stencil of $m \times m$ blocks.
* `FiniteDifference.amplificationMatrix`: the amplification matrix $G_k = \sum_s \omega^{-sk} G_s$.
* `FiniteDifference.modeTensor`: the tensored mode $(j, p) \mapsto \omega^{jk} v_p$.

## Main results

* `FiniteDifference.periodicScheme_pow_mulVec_fourierMode`: $Q^n e_k = \gamma_k^n e_k$.
* `FiniteDifference.eq_dft_mul_diagonal_of_forall_mulVec_fourierMode`: a matrix with every mode as
  an eigenvector is $N^{-1} F \operatorname{diag}(\gamma) F^H$.
* `FiniteDifference.sum_normSq_conjTranspose_dft_mulVec`: the discrete Parseval identity
  $\|F^H y\|^2 = N \|y\|^2$.
* `FiniteDifference.norm_toEuclideanLin_le_of_forall_mulVec_fourierMode`:
  $\|Au\|_2 \le \rho \|u\|_2$ when $A e_k = \gamma_k e_k$ and $|\gamma_k| \le \rho$.
* `FiniteDifference.norm_toEuclideanLin_periodicScheme_pow_le`: von Neumann's sufficient condition.
* `FiniteDifference.norm_amplificationFactor_pow_le`: $|\gamma_k|^n \le \|Q^n\|_2$.
* `FiniteDifference.norm_amplificationFactor_le_one_add_of_forall_norm_pow_le`: von Neumann's
  necessary condition.
* `FiniteDifference.periodicTwoLevel_mulVec_fourierMode`:
  $B^{-1} C e_k = (\gamma^C_k / \gamma^B_k) e_k$.
* `FiniteDifference.Stencil.periodicScheme_toPeriodic_mulVec`: the wrapped scheme agrees with the
  stencil on periodic grid functions.
* `FiniteDifference.Stencil.amplificationFactor_toPeriodic_eq_symbol`: the amplification factors of
  a wrapped stencil are its symbol at $2\pi k / N$.
* `FiniteDifference.Stencil.amplificationFactor_toPeriodic_threePoint`: the amplification factors of
  a three-point stencil.
* `FiniteDifference.periodicBlockScheme_pow_mulVec_fourierMode`:
  $B^n (e_k \otimes v) = e_k \otimes (G_k^n v)$.
* `FiniteDifference.norm_toEuclideanLin_periodicBlockScheme_pow_le` and
  `FiniteDifference.norm_toEuclideanCLM_amplificationMatrix_pow_le`: the $\ell^2$ norm of $B^n$ is
  the maximum over $k$ of the norms of $G_k^n$.

## Implementation notes

* The stencil of a periodic scheme is a complex vector `Fin N → ℂ`, and the scheme is
  `Matrix.circulant c`, whose entry $(j, l)$ is $c_{j-l}$ with the subtraction modulo $N$.
* The diagonalization of circulant matrices is the one of `Numlib.Analysis.Fourier.Circulant`, in
  the convention whose eigenvectors are the columns of `Matrix.dft N`
  (`Matrix.circulant_mulVec_dft_col`). This is the complex conjugate of the usual convention of
  numerical linear algebra.
* The $\ell^2$ norm is the norm of `EuclideanSpace ℂ (Fin N)`, and a matrix acts on it through
  `Matrix.toEuclideanLin` and `Matrix.toEuclideanCLM`. The discrete norm $\|\cdot\|_{\Delta, 2}$ is
  a constant multiple of this norm, so the stability constants are the same.
* The norm bounds are stated for any matrix that has the Fourier modes as eigenvectors. They
  therefore apply without change to the implicit two-level schemes.
-/

open Complex Matrix Finset
open scoped Real Fin.IntCast Fin.CommRing

namespace FiniteDifference

variable {N : ℕ}

/-! ### The periodic scheme, the Fourier modes and the amplification factors -/

/-- **The explicit constant-coefficient scheme on the periodic grid.** For a stencil
$c \in \mathbb{C}^N$ on the grid $\{0, \dots, N-1\}$, the scheme is the circulant matrix $Q$
with
$$(Qu)_j = \sum_s c_s u_{j-s},$$
where the subtraction $j - s$ is modulo $N$. -/
noncomputable abbrev periodicScheme (c : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.circulant c

/-- The action of the periodic scheme: $(Qu)_j = \sum_s c_s u_{j-s}$, with the subtraction modulo
$N$. -/
theorem periodicScheme_mulVec_apply (c : Fin N → ℂ) (u : Fin N → ℂ) (j : Fin N) :
    (periodicScheme c *ᵥ u) j = ∑ s, c s * u (j - s) := by
  have := NeZero.of_pos j.pos
  rw [mulVec, dotProduct]
  simp only [circulant_apply]
  exact (Equiv.sum_comp (Equiv.subLeft j) fun l => c (j - l) * u l).symm.trans
    (Finset.sum_congr rfl fun s _ => by simp)

/-- **The $k$-th Fourier mode** on the grid of $N$ points: the vector $e_k$ with
$e_k(j) = \omega^{jk}$, where $\omega = e^{2\pi i / N}$. These are the grid values $e^{ikjh}$,
$h = 2\pi / N$, of the $k$-th harmonic, and $e_k$ is the $k$-th column of the Fourier matrix
`Matrix.dft N`. -/
noncomputable def fourierMode (N : ℕ) (k : Fin N) : Fin N → ℂ := fun j => Matrix.dft N j k

/-- The entries of a Fourier mode: $e_k(j) = \omega^{jk}$ with $\omega = e^{2\pi i / N}$, where $j$
and $k$ are taken as natural numbers in $\{0, \dots, N-1\}$. -/
theorem fourierMode_apply (k j : Fin N) :
    fourierMode N k j = Complex.exp (2 * π * I / N) ^ ((j : ℕ) * (k : ℕ)) := rfl

/-- **The amplification factor** of the $k$-th mode under the scheme with stencil
$c \in \mathbb{C}^N$:
$$\gamma_k = \sum_s c_s \omega^{-sk},$$
the discrete Fourier transform of the stencil at $k$. It is the $k$-th entry of $F^H c$, where
$F$ is the Fourier matrix. -/
noncomputable def amplificationFactor (c : Fin N → ℂ) (k : Fin N) : ℂ :=
  ((Matrix.dft N)ᴴ *ᵥ c) k

/-- The amplification factor as an explicit sum: $\gamma_k = \sum_s (\omega^{-1})^{sk} c_s$, where
$s$ and $k$ are taken as natural numbers in $\{0, \dots, N-1\}$. -/
theorem amplificationFactor_eq_sum (c : Fin N → ℂ) (k : Fin N) :
    amplificationFactor c k
      = ∑ s : Fin N, (Complex.exp (2 * π * I / N))⁻¹ ^ ((s : ℕ) * (k : ℕ)) * c s :=
  Matrix.conjTranspose_dft_mulVec_apply c k

/-- A Fourier mode at a difference of grid points: for $j, s, k \in \{0, \dots, N-1\}$,
$e_k(j - s) = e_k(j) \, (\omega^{-1})^{sk}$, with the subtraction $j - s$ modulo $N$. -/
theorem fourierMode_sub (k j s : Fin N) :
    fourierMode N k (j - s)
      = fourierMode N k j * (Complex.exp (2 * π * I / N))⁻¹ ^ ((s : ℕ) * k) := by
  rw [fourierMode, fourierMode, Matrix.dft_apply_sub, conjTranspose_dft_apply, Nat.mul_comm]

/-- **The Fourier modes are eigenvectors of every circulant scheme** ([quarteroni2000numerical],
(13.52) for one step). For a stencil $c \in \mathbb{C}^N$ and every $k$, the periodic scheme $Q$
satisfies
$$Q e_k = \gamma_k e_k,$$
where $\gamma_k$ is the amplification factor. -/
theorem periodicScheme_mulVec_fourierMode (c : Fin N → ℂ) (k : Fin N) :
    periodicScheme c *ᵥ fourierMode N k = amplificationFactor c k • fourierMode N k :=
  Matrix.circulant_mulVec_dft_col c k

/-- **The recursion on one harmonic** ([quarteroni2000numerical], (13.52)). For a stencil
$c \in \mathbb{C}^N$, every $k$ and every $n \in \mathbb{N}$, the periodic scheme $Q$ satisfies
$$Q^n e_k = \gamma_k^n e_k.$$
-/
theorem periodicScheme_pow_mulVec_fourierMode (c : Fin N → ℂ) (k : Fin N) (n : ℕ) :
    (periodicScheme c ^ n) *ᵥ fourierMode N k
      = amplificationFactor c k ^ n • fourierMode N k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, periodicScheme_mulVec_fourierMode,
      smul_smul, pow_succ]

/-! ### Spectral decomposition and discrete Parseval -/

/-- Let $A \in \mathbb{C}^{N \times N}$ and $\gamma \in \mathbb{C}^N$ satisfy $A e_k = \gamma_k e_k$
for every Fourier mode $e_k$. Then $AF = F \operatorname{diag}(\gamma)$, where $F$ is the
Fourier matrix. -/
theorem mul_dft_eq_of_forall_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ} {γ : Fin N → ℂ}
    (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) :
    A * Matrix.dft N = Matrix.dft N * diagonal γ :=
  Matrix.mul_eq_mul_diagonal_of_forall_mulVec_col hA

/-- **Spectral decomposition through the discrete Fourier transform.** Let
$A \in \mathbb{C}^{N \times N}$ and $\gamma \in \mathbb{C}^N$ satisfy $A e_k = \gamma_k e_k$ for
every Fourier mode $e_k$. Then
$$A = N^{-1} F \operatorname{diag}(\gamma) F^H,$$
where $F$ is the Fourier matrix. -/
theorem eq_dft_mul_diagonal_of_forall_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ}
    {γ : Fin N → ℂ} (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) :
    A = (N : ℂ)⁻¹ • (Matrix.dft N * diagonal γ * (Matrix.dft N)ᴴ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Subsingleton.elim _ _
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [← mul_dft_eq_of_forall_mulVec_fourierMode hA, Matrix.mul_assoc,
    Matrix.dft_mul_conjTranspose_dft, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ hN', one_smul]

/-- **Spectral decomposition of a circulant.** For a stencil $c \in \mathbb{C}^N$, the periodic
scheme is
$$Q = N^{-1} F \operatorname{diag}(\gamma) F^H,$$
where $F$ is the Fourier matrix and $\gamma$ is the vector of amplification factors. -/
theorem periodicScheme_eq_dft_mul_diagonal (c : Fin N → ℂ) :
    periodicScheme c
      = (N : ℂ)⁻¹ • (Matrix.dft N * diagonal (amplificationFactor c) * (Matrix.dft N)ᴴ) :=
  Matrix.circulant_eq_dft_mul_diagonal_mul_conjTranspose_dft c

/-- Parseval's identity for a matrix with orthogonal columns. Let $M \in \mathbb{C}^{N \times N}$
satisfy $M^H M = N \cdot 1$. Then for every $y \in \mathbb{C}^N$,
$$\sum_k |(My)_k|^2 = N \sum_j |y_j|^2.$$
-/
theorem sum_normSq_mulVec_of_conjTranspose_mul {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : Mᴴ * M = (N : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) (y : Fin N → ℂ) :
    ∑ k, ‖(M *ᵥ y) k‖ ^ 2 = N * ∑ j, ‖y j‖ ^ 2 := by
  have h : star (M *ᵥ y) ⬝ᵥ (M *ᵥ y) = (N : ℂ) * (star y ⬝ᵥ y) := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hM, vecMul_smul, vecMul_one, smul_dotProduct,
      smul_eq_mul]
  have h' : ∀ z : Fin N → ℂ, star z ⬝ᵥ z = ∑ k, ((‖z k‖ ^ 2 : ℝ) : ℂ) := fun z => by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  rw [h', h', ← Complex.ofReal_sum, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- **The discrete Parseval identity** ([quarteroni2000numerical], Lemma 10.1, in norm form). For
the Fourier matrix $F$ and every $y \in \mathbb{C}^N$,
$$\sum_k |(F^H y)_k|^2 = N \sum_j |y_j|^2.$$

The proof uses the orthogonality $F^H F = N \cdot 1$. -/
theorem sum_normSq_conjTranspose_dft_mulVec (y : Fin N → ℂ) :
    ∑ k, ‖((Matrix.dft N)ᴴ *ᵥ y) k‖ ^ 2 = N * ∑ j, ‖y j‖ ^ 2 :=
  sum_normSq_mulVec_of_conjTranspose_mul
    (by rw [conjTranspose_conjTranspose, Matrix.dft_mul_conjTranspose_dft]) y

/-- **The discrete Parseval identity** for the inverse transform. For the Fourier matrix $F$ and
every $y \in \mathbb{C}^N$,
$$\sum_k |(F y)_k|^2 = N \sum_j |y_j|^2.$$
-/
theorem sum_normSq_dft_mulVec (y : Fin N → ℂ) :
    ∑ k, ‖(Matrix.dft N *ᵥ y) k‖ ^ 2 = N * ∑ j, ‖y j‖ ^ 2 :=
  sum_normSq_mulVec_of_conjTranspose_mul (Matrix.conjTranspose_dft_mul_dft N) y

/-- For the Fourier matrix $F$ and every $y \in \mathbb{C}^N$, the Euclidean norm satisfies
$\|F^H y\| = \sqrt{N} \|y\|$. -/
theorem norm_toEuclideanLin_conjTranspose_dft (y : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (Matrix.dft N)ᴴ y‖ = √N * ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul (Nat.cast_nonneg N),
    ← sum_normSq_conjTranspose_dft_mulVec]
  rfl

/-- For the Fourier matrix $F$ and every $y \in \mathbb{C}^N$, the Euclidean norm satisfies
$\|F y\| = \sqrt{N} \|y\|$. -/
theorem norm_toEuclideanLin_dft (y : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (Matrix.dft N) y‖ = √N * ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul (Nat.cast_nonneg N),
    ← sum_normSq_dft_mulVec]
  rfl

/-- Let $\gamma \in \mathbb{C}^N$ and $\rho \ge 0$ satisfy $|\gamma_k| \le \rho$ for every $k$. Then
$\|\operatorname{diag}(\gamma) y\| \le \rho \|y\|$ in the Euclidean norm, for every
$y \in \mathbb{C}^N$. -/
theorem norm_toEuclideanLin_diagonal_le {γ : Fin N → ℂ} {ρ : ℝ} (hγ : ∀ k, ‖γ k‖ ≤ ρ) (hρ : 0 ≤ ρ)
    (y : EuclideanSpace ℂ (Fin N)) : ‖toEuclideanLin (diagonal γ) y‖ ≤ ρ * ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hρ,
    ← Real.sqrt_mul (sq_nonneg ρ), Finset.mul_sum]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
  rw [toEuclideanLin_apply, WithLp.ofLp_toLp, mulVec_diagonal, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hγ k) 2) (sq_nonneg _)

/-! ### The $\ell^2$ norm of the powers -/

/-- **The $\ell^2$ bound through the eigenvalues on the Fourier modes.** Let
$A \in \mathbb{C}^{N \times N}$ and $\gamma \in \mathbb{C}^N$ satisfy $A e_k = \gamma_k e_k$ for
every Fourier mode $e_k$, and let $\rho \ge 0$ with $|\gamma_k| \le \rho$ for every $k$. Then
for every $u \in \mathbb{C}^N$,
$$\|Au\|_2 \le \rho \|u\|_2.$$

The proof uses the decomposition $A = N^{-1} F \operatorname{diag}(\gamma) F^H$ and the discrete
Parseval identity twice: $\|Au\| = N^{-1} \sqrt{N} \|\operatorname{diag}(\gamma) F^H u\| \le
N^{-1} \sqrt{N} \rho \sqrt{N} \|u\|$. -/
theorem norm_toEuclideanLin_le_of_forall_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ}
    {γ : Fin N → ℂ} (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) {ρ : ℝ}
    (hγ : ∀ k, ‖γ k‖ ≤ ρ) (hρ : 0 ≤ ρ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin A u‖ ≤ ρ * ‖u‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Subsingleton.elim u 0]
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [eq_dft_mul_diagonal_of_forall_mulVec_fourierMode hA, toEuclideanLin_smul_apply,
    toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, norm_smul, norm_toEuclideanLin_dft,
    norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * (√N * ‖toEuclideanLin (diagonal γ) (toEuclideanLin (Matrix.dft N)ᴴ u)‖)
      ≤ (N : ℝ)⁻¹ * (√N * (ρ * ‖toEuclideanLin (Matrix.dft N)ᴴ u‖)) := by
        gcongr
        exact norm_toEuclideanLin_diagonal_le hγ hρ _
    _ = (N : ℝ)⁻¹ * (√N * (ρ * (√N * ‖u‖))) := by rw [norm_toEuclideanLin_conjTranspose_dft]
    _ = ρ * ‖u‖ := by
        have : √(N : ℝ) * √N = N := Real.mul_self_sqrt hN'.le
        field_simp
        linear_combination ρ * ‖u‖ * this

/-- Powers keep the eigenvector relation: if $A e_k = \gamma_k e_k$ for every Fourier mode $e_k$,
then $A^n e_k = \gamma_k^n e_k$ for every $n \in \mathbb{N}$ and every $k$. -/
theorem pow_mulVec_fourierMode_of_forall_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ}
    {γ : Fin N → ℂ} (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) (n : ℕ) (k : Fin N) :
    (A ^ n) *ᵥ fourierMode N k = γ k ^ n • fourierMode N k := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hA, smul_smul, pow_succ]

/-- **The $\ell^2$ norm of the powers** of a matrix with the Fourier modes as eigenvectors. Let
$A \in \mathbb{C}^{N \times N}$ and $\gamma \in \mathbb{C}^N$ satisfy $A e_k = \gamma_k e_k$ for
every Fourier mode $e_k$, and let $\rho \ge 0$ with $|\gamma_k| \le \rho$ for every $k$. Then
for every $n \in \mathbb{N}$ and every $u \in \mathbb{C}^N$,
$$\|A^n u\|_2 \le \rho^n \|u\|_2.$$
-/
theorem norm_toEuclideanLin_pow_le_of_forall_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ}
    {γ : Fin N → ℂ} (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) {ρ : ℝ}
    (hγ : ∀ k, ‖γ k‖ ≤ ρ) (hρ : 0 ≤ ρ) (n : ℕ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (A ^ n) u‖ ≤ ρ ^ n * ‖u‖ :=
  norm_toEuclideanLin_le_of_forall_mulVec_fourierMode
    (pow_mulVec_fourierMode_of_forall_mulVec_fourierMode hA n)
    (fun k => by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hγ k) n) (by positivity) u

/-- Let $c \in \mathbb{C}^N$ be a stencil and let $\rho \ge 0$ with $|\gamma_k| \le \rho$ for every
amplification factor. Then the periodic scheme $Q$ satisfies $\|Q^n u\|_2 \le \rho^n \|u\|_2$
for every $n \in \mathbb{N}$ and every $u \in \mathbb{C}^N$. -/
theorem norm_toEuclideanLin_periodicScheme_pow (c : Fin N → ℂ) (n : ℕ) {ρ : ℝ}
    (hρ : ∀ k, ‖amplificationFactor c k‖ ≤ ρ) (hρ0 : 0 ≤ ρ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (periodicScheme c ^ n) u‖ ≤ ρ ^ n * ‖u‖ :=
  norm_toEuclideanLin_pow_le_of_forall_mulVec_fourierMode (periodicScheme_mulVec_fourierMode c)
    hρ hρ0 n u

/-- **Von Neumann's sufficient condition** ([quarteroni2000numerical], Theorem 13.1). Let
$c \in \mathbb{C}^N$ be a stencil whose amplification factors satisfy $|\gamma_k| \le 1$ for
every $k$. Then the periodic scheme $Q$ satisfies, for every $n \in \mathbb{N}$ and every
$u \in \mathbb{C}^N$,
$$\|Q^n u\|_2 \le \|u\|_2.$$
So the scheme is stable in $\|\cdot\|_{\Delta, 2}$ with constant $1$, for every number of steps. -/
theorem norm_toEuclideanLin_periodicScheme_pow_le (c : Fin N → ℂ)
    (h : ∀ k, ‖amplificationFactor c k‖ ≤ 1) (n : ℕ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (periodicScheme c ^ n) u‖ ≤ ‖u‖ := by
  simpa using norm_toEuclideanLin_periodicScheme_pow c n h zero_le_one u

/-- Von Neumann's sufficient condition, operator norm form. If the stencil $c \in \mathbb{C}^N$ has
amplification factors with $|\gamma_k| \le 1$ for every $k$, then the periodic scheme $Q$
satisfies $\|Q^n\|_2 \le 1$ for every $n \in \mathbb{N}$. -/
theorem norm_toEuclideanCLM_periodicScheme_pow_le (c : Fin N → ℂ)
    (h : ∀ k, ‖amplificationFactor c k‖ ≤ 1) (n : ℕ) :
    ‖toEuclideanCLM (𝕜 := ℂ) (periodicScheme c ^ n)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    rw [one_mul]; exact norm_toEuclideanLin_periodicScheme_pow_le c h n u

/-- A Fourier mode is not the zero vector: its value at $j = 0$ is $1$. -/
theorem fourierMode_ne_zero (k : Fin N) : fourierMode N k ≠ 0 := fun h => by
  have := congrFun h ⟨0, k.pos⟩
  simp [fourierMode_apply] at this

/-- **The eigenvalues bound the operator norm from below.** Let $A \in \mathbb{C}^{N \times N}$ and
$\gamma \in \mathbb{C}^N$ satisfy $A e_k = \gamma_k e_k$ for every Fourier mode $e_k$. Then for
every $k$ and every $n \in \mathbb{N}$,
$$|\gamma_k|^n \le \|A^n\|_2.$$

The proof tests $A^n$ on the mode $e_k$. -/
theorem norm_pow_le_norm_toEuclideanCLM_pow_of_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ}
    {γ : Fin N → ℂ} (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) (k : Fin N) (n : ℕ) :
    ‖γ k‖ ^ n ≤ ‖toEuclideanCLM (𝕜 := ℂ) (A ^ n)‖ := by
  have hek : (WithLp.toLp 2 (fourierMode N k) : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
    intro h
    exact fourierMode_ne_zero k (by simpa using congrArg WithLp.ofLp h)
  have h := (toEuclideanCLM (𝕜 := ℂ) (A ^ n)).le_opNorm (WithLp.toLp 2 (fourierMode N k))
  rw [toEuclideanCLM_toLp, pow_mulVec_fourierMode_of_forall_mulVec_fourierMode hA, WithLp.toLp_smul,
    norm_smul, norm_pow] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hek)

/-- **The amplification factors bound the norm of the powers from below.** For a stencil
$c \in \mathbb{C}^N$, every $k$ and every $n \in \mathbb{N}$, the periodic scheme $Q$ satisfies
$$|\gamma_k|^n \le \|Q^n\|_2.$$
-/
theorem norm_amplificationFactor_pow_le (c : Fin N → ℂ) (k : Fin N) (n : ℕ) :
    ‖amplificationFactor c k‖ ^ n ≤ ‖toEuclideanCLM (𝕜 := ℂ) (periodicScheme c ^ n)‖ :=
  norm_pow_le_norm_toEuclideanCLM_pow_of_mulVec_fourierMode (periodicScheme_mulVec_fourierMode c)
    k n

/-- **Von Neumann's necessary condition.** Let $A \in \mathbb{C}^{N \times N}$ and
$\gamma \in \mathbb{C}^N$ satisfy $A e_k = \gamma_k e_k$ for every Fourier mode $e_k$. Let
$C \ge 1$ and $0 < \Delta t \le T / 2$, and assume $\|A^n\|_2 \le C$ for every
$n \in \mathbb{N}$ with $n \Delta t \le T$. Then for every $k$,
$$|\gamma_k| \le 1 + \frac{2 (C - 1) \Delta t}{T}.$$

With $n = \lfloor T / \Delta t \rfloor \ge 1$, Bernoulli's inequality gives
$|\gamma_k|^n \le C \le (1 + (C - 1) / n)^n$, and $1 / n \le 2 \Delta t / T$. -/
theorem norm_le_one_add_of_forall_norm_pow_le_of_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ}
    {γ : Fin N → ℂ} (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) {C Δt T : ℝ}
    (hC : 1 ≤ C) (hΔt : 0 < Δt) (hΔT : Δt ≤ T / 2)
    (hstab : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖toEuclideanCLM (𝕜 := ℂ) (A ^ n)‖ ≤ C) (k : Fin N) :
    ‖γ k‖ ≤ 1 + 2 * (C - 1) * Δt / T := by
  have hT : 0 < T := by linarith
  set n : ℕ := ⌊T / Δt⌋₊ with hn
  have hx : (2 : ℝ) ≤ T / Δt := by rw [le_div_iff₀ hΔt]; linarith
  have hn2 : (2 : ℝ) ≤ n := by
    have h2 : (2 : ℕ) ≤ n := Nat.le_floor hx
    exact_mod_cast h2
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hn2; norm_num at hn2
  have hnpos : (0 : ℝ) < n := by linarith
  have hnT : (n : ℝ) * Δt ≤ T := by
    rw [← le_div_iff₀ hΔt]; exact Nat.floor_le (by positivity)
  have hbound : ‖γ k‖ ^ n ≤ C :=
    (norm_pow_le_norm_toEuclideanCLM_pow_of_mulVec_fourierMode hA k n).trans (hstab n hnT)
  -- Bernoulli: `C ≤ (1 + (C - 1)/n)^n`
  have hbern : C ≤ (1 + (C - 1) / n) ^ n := by
    have := one_add_mul_le_pow (a := (C - 1) / n) (by
      have : 0 ≤ (C - 1) / n := by positivity
      linarith) n
    rwa [mul_div_cancel₀ _ hnpos.ne', add_sub_cancel] at this
  have hle : ‖γ k‖ ≤ 1 + (C - 1) / n :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hn0).1 (hbound.trans hbern)
  -- `1/n ≤ 2 Δt / T`, since `n ≥ T/Δt - 1 ≥ T/(2 Δt)`
  have hfloor : T / Δt - 1 ≤ n := by
    have h := Nat.lt_floor_add_one (T / Δt)
    rw [← hn] at h
    linarith
  have hhalf : T / (2 * Δt) ≤ n := by
    have : T / (2 * Δt) ≤ T / Δt - 1 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : T / Δt * Δt = T := div_mul_cancel₀ T hΔt.ne'
      nlinarith
    linarith
  have hinv : (C - 1) / n ≤ 2 * (C - 1) * Δt / T := by
    rw [div_le_div_iff₀ hnpos hT]
    have h1 : T ≤ n * (2 * Δt) := by
      rw [div_le_iff₀ (by positivity)] at hhalf; linarith
    nlinarith
  linarith

/-- **Von Neumann's necessary condition** for the periodic scheme. Let $c \in \mathbb{C}^N$ be a
stencil, let $C \ge 1$ and $0 < \Delta t \le T / 2$, and assume that the periodic scheme $Q$
satisfies $\|Q^n\|_2 \le C$ for every $n \in \mathbb{N}$ with $n \Delta t \le T$. Then every
amplification factor satisfies
$$|\gamma_k| \le 1 + \frac{2 (C - 1) \Delta t}{T}.$$

So a mode with $|\gamma_k| \ge 1 + \varepsilon$ independently of the mesh makes the family
unstable. This is how [quarteroni2000numerical], §13.8.4, conclude that the forward
Euler/centred scheme is unconditionally unstable. -/
theorem norm_amplificationFactor_le_one_add_of_forall_norm_pow_le (c : Fin N → ℂ) {C Δt T : ℝ}
    (hC : 1 ≤ C) (hΔt : 0 < Δt) (hΔT : Δt ≤ T / 2)
    (hstab : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖toEuclideanCLM (𝕜 := ℂ) (periodicScheme c ^ n)‖ ≤ C)
    (k : Fin N) : ‖amplificationFactor c k‖ ≤ 1 + 2 * (C - 1) * Δt / T :=
  norm_le_one_add_of_forall_norm_pow_le_of_mulVec_fourierMode (periodicScheme_mulVec_fourierMode c)
    hC hΔt hΔT hstab k

/-! ### Implicit two-level schemes -/

/-- **The implicit two-level scheme** $B u^{n+1} = C u^n$ with the circulant matrices $B$ and $C$ of
the stencils $b, c \in \mathbb{C}^N$: its solution operator is $B^{-1} C$.

The inverse is `Matrix.inv`, which is $0$ when $B$ is singular. -/
noncomputable def periodicTwoLevel (b c : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (periodicScheme b)⁻¹ * periodicScheme c

/-- The amplification factors of the implicit two-level scheme: the quotients
$\gamma^C_k / \gamma^B_k$ of the amplification factors of the stencils $c$ and $b$. The quotient
is $0$ when $\gamma^B_k = 0$. -/
noncomputable def amplificationFactor₂ (b c : Fin N → ℂ) (k : Fin N) : ℂ :=
  amplificationFactor c k / amplificationFactor b k

/-- A circulant matrix whose amplification factors are all nonzero is invertible: if
$\gamma^B_k \neq 0$ for every $k$, then the periodic scheme of $b$ is invertible. -/
theorem isUnit_periodicScheme_of_forall_ne_zero {b : Fin N → ℂ}
    (hb : ∀ k, amplificationFactor b k ≠ 0) : IsUnit (periodicScheme b) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact isUnit_of_subsingleton _
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [periodicScheme_eq_dft_mul_diagonal]
  have hF : IsUnit (Matrix.dft N) :=
    (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse (by
      rw [Matrix.mul_smul, Matrix.dft_mul_conjTranspose_dft, smul_smul, inv_mul_cancel₀ hN',
        one_smul] : Matrix.dft N * ((N : ℂ)⁻¹ • (Matrix.dft N)ᴴ) = 1))
  have hFH : IsUnit (Matrix.dft N)ᴴ :=
    (isUnit_iff_isUnit_det _).2 (isUnit_det_of_left_inverse (by
      rw [Matrix.smul_mul, Matrix.dft_mul_conjTranspose_dft, smul_smul, inv_mul_cancel₀ hN',
        one_smul] : ((N : ℂ)⁻¹ • Matrix.dft N) * (Matrix.dft N)ᴴ = 1))
  have hD : IsUnit (diagonal (amplificationFactor b)) := by
    rw [isUnit_iff_isUnit_det, det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hb k
  have hprod := (isUnit_iff_isUnit_det _).1 ((hF.mul hD).mul hFH)
  rw [isUnit_iff_isUnit_det, det_smul, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hN')) (isUnit_iff_ne_zero.1 hprod)

/-- The inverse of a circulant matrix with nonzero amplification factors has the Fourier modes as
eigenvectors, with the reciprocal factors: if $\gamma^B_k \neq 0$ for every $k$, then
$B^{-1} e_k = (\gamma^B_k)^{-1} e_k$. -/
theorem inv_periodicScheme_mulVec_fourierMode {b : Fin N → ℂ}
    (hb : ∀ k, amplificationFactor b k ≠ 0) (k : Fin N) :
    (periodicScheme b)⁻¹ *ᵥ fourierMode N k = (amplificationFactor b k)⁻¹ • fourierMode N k := by
  have hu := isUnit_periodicScheme_of_forall_ne_zero hb
  have hdet : IsUnit (periodicScheme b).det := (isUnit_iff_isUnit_det _).1 hu
  have h2 : fourierMode N k
      = amplificationFactor b k • ((periodicScheme b)⁻¹ *ᵥ fourierMode N k) :=
    calc fourierMode N k = ((periodicScheme b)⁻¹ * periodicScheme b) *ᵥ fourierMode N k := by
          rw [nonsing_inv_mul _ hdet, one_mulVec]
      _ = (periodicScheme b)⁻¹ *ᵥ (amplificationFactor b k • fourierMode N k) := by
          rw [← mulVec_mulVec, periodicScheme_mulVec_fourierMode]
      _ = amplificationFactor b k • ((periodicScheme b)⁻¹ *ᵥ fourierMode N k) :=
          mulVec_smul _ _ _
  conv_rhs => rw [h2]
  rw [smul_smul, inv_mul_cancel₀ (hb k), one_smul]

/-- **The Fourier modes are eigenvectors of the implicit two-level scheme.** Let
$b, c \in \mathbb{C}^N$ be stencils with $\gamma^B_k \neq 0$ for every $k$. Then for every $k$,
$$B^{-1} C e_k = \frac{\gamma^C_k}{\gamma^B_k} e_k.$$

The $\ell^2$ bounds `FiniteDifference.norm_toEuclideanLin_pow_le_of_forall_mulVec_fourierMode`,
`FiniteDifference.norm_pow_le_norm_toEuclideanCLM_pow_of_mulVec_fourierMode` and
`FiniteDifference.norm_le_one_add_of_forall_norm_pow_le_of_mulVec_fourierMode` therefore apply
to $B^{-1} C$ without change. -/
theorem periodicTwoLevel_mulVec_fourierMode {b : Fin N → ℂ}
    (hb : ∀ k, amplificationFactor b k ≠ 0) (c : Fin N → ℂ) (k : Fin N) :
    periodicTwoLevel b c *ᵥ fourierMode N k = amplificationFactor₂ b c k • fourierMode N k := by
  rw [periodicTwoLevel, ← mulVec_mulVec, periodicScheme_mulVec_fourierMode, mulVec_smul,
    inv_periodicScheme_mulVec_fourierMode hb, smul_smul, amplificationFactor₂, div_eq_mul_inv]

/-- Von Neumann's sufficient condition for the implicit two-level scheme. Let
$b, c \in \mathbb{C}^N$ be stencils with $\gamma^B_k \neq 0$ and
$|\gamma^C_k / \gamma^B_k| \le 1$ for every $k$. Then for every $n \in \mathbb{N}$ and every
$u \in \mathbb{C}^N$,
$$\|(B^{-1} C)^n u\|_2 \le \|u\|_2.$$
-/
theorem norm_toEuclideanLin_periodicTwoLevel_pow_le {b : Fin N → ℂ}
    (hb : ∀ k, amplificationFactor b k ≠ 0) (c : Fin N → ℂ)
    (h : ∀ k, ‖amplificationFactor₂ b c k‖ ≤ 1) (n : ℕ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (periodicTwoLevel b c ^ n) u‖ ≤ ‖u‖ := by
  simpa using norm_toEuclideanLin_pow_le_of_forall_mulVec_fourierMode
    (periodicTwoLevel_mulVec_fourierMode hb c) h zero_le_one n u

/-! ### Wrapping a stencil onto the periodic grid -/

namespace Stencil

/-- **A stencil wrapped onto the periodic grid** of $N \ge 1$ points. For a stencil $c$ on
$\mathbb{Z}$, the wrapped stencil has at $j \in \{0, \dots, N-1\}$ the weight
$$\sum_{s \equiv j \ (\mathrm{mod}\ N)} c_s.$$
-/
noncomputable def toPeriodic (N : ℕ) [NeZero N] (c : Stencil) : Fin N → ℂ :=
  fun j => ∑ s ∈ c.support, if (s : Fin N) = j then (c s : ℂ) else 0

variable [NeZero N]

/-- **The periodic scheme agrees with the stencil on periodic grid functions.** Let $N \ge 1$, let
$c$ be a stencil on $\mathbb{Z}$, let $v \in \mathbb{C}^N$, and let
$u \colon \mathbb{Z} \to \mathbb{C}$ be its $N$-periodic extension, $u_i = v_{i \bmod N}$. Then
for every $j \in \mathbb{Z}$, the periodic scheme $Q$ of the wrapped stencil satisfies
$$(Qv)_{j \bmod N} = (cu)_j.$$
-/
theorem periodicScheme_toPeriodic_mulVec (c : Stencil) (v : Fin N → ℂ) (j : ℤ) :
    (periodicScheme (toPeriodic N c) *ᵥ v) (j : Fin N)
      = apply c (fun i : ℤ => v (i : Fin N)) j := by
  rw [periodicScheme_mulVec_apply, apply_apply]
  simp only [toPeriodic, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.real_smul, Int.cast_sub, Finset.sum_ite_eq Finset.univ (s : Fin N)]
  simp

/-- For $s \in \mathbb{Z}$ and $k \in \{0, \dots, N-1\}$, let $\bar s \in \{0, \dots, N-1\}$ be the
residue of $s$ modulo $N$. Then $(\omega^{-1})^{\bar s k} = e^{-is \cdot 2\pi k / N}$. -/
private theorem exp_val_intCast (s : ℤ) (k : Fin N) :
    (Complex.exp (2 * π * I / N))⁻¹ ^ (((s : Fin N) : ℕ) * (k : ℕ))
      = Complex.exp (-(I * s * (2 * π * k / N))) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hval : (((s : Fin N) : ℕ) : ℤ) = s % N := by
    rw [Fin.val_intCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne N))]
  rw [inv_pow, ← Complex.exp_nat_mul, ← Complex.exp_neg]
  have hdiv : s = s % N + N * (s / N) := (Int.emod_add_mul_ediv s N).symm
  have hcast : ((((s : Fin N) : ℕ) * (k : ℕ) : ℕ) : ℂ) = ((s % N : ℤ) : ℂ) * (k : ℕ) := by
    push_cast
    rw [← hval]
    push_cast
    ring
  rw [hcast]
  conv_rhs => rw [hdiv]
  rw [show -(I * ((s % N + N * (s / N) : ℤ) : ℂ) * (2 * π * k / N))
      = -(((s % N : ℤ) : ℂ) * (k : ℕ) * (2 * π * I / N)) + (-(s / N) * k : ℤ) * (2 * π * I) by
    push_cast; field_simp; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The amplification factors of a wrapped stencil are its symbol at $\varphi_k = 2\pi k / N$.**
Let $N \ge 1$ and let $c$ be a stencil on $\mathbb{Z}$ with symbol $\sigma$. Then for every
$k \in \{0, \dots, N-1\}$, the amplification factor of the wrapped stencil is
$$\gamma_k = \sigma(2\pi k / N).$$
-/
theorem amplificationFactor_toPeriodic_eq_symbol (c : Stencil) (k : Fin N) :
    amplificationFactor (toPeriodic N c) k = symbol c (2 * π * k / N) := by
  rw [amplificationFactor_eq_sum, symbol]
  simp only [toPeriodic, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (s : Fin N)]
  simp only [Finset.mem_univ, ite_true]
  rw [exp_val_intCast, mul_comm]
  push_cast
  ring_nf

/-- **The three-point amplification factor.** Let $N \ge 1$, and wrap the three-point stencil
$j \mapsto c_- u_{j-1} + c_0 u_j + c_+ u_{j+1}$, with $c_-, c_0, c_+ \in \mathbb{R}$, onto $N$
points. Then for every $k \in \{0, \dots, N-1\}$, with $\varphi_k = 2\pi k / N$,
$$\gamma_k = c_0 + c_- e^{-i\varphi_k} + c_+ e^{i\varphi_k}.$$

Every entry of the stability column of [quarteroni2000numerical], Table 13.1, is this formula
followed by a computation of the modulus. -/
theorem amplificationFactor_toPeriodic_threePoint (cm c0 cp : ℝ) (k : Fin N) :
    amplificationFactor (toPeriodic N (threePoint cm c0 cp)) k
      = c0 + cm * Complex.exp (-(I * (2 * π * k / N)))
        + cp * Complex.exp (I * (2 * π * k / N)) := by
  rw [amplificationFactor_toPeriodic_eq_symbol, symbol_threePoint]
  push_cast
  ring_nf

end Stencil

/-! ### Block circulants for multi-level schemes -/

section Block

variable {m : ℕ}

/-- **A multi-level scheme as a block circulant.** For a stencil of $m \times m$ blocks $G_0, \dots,
G_{N-1} \in \mathbb{C}^{m \times m}$, the block circulant is the matrix on
$\{0, \dots, N-1\} \times \{0, \dots, m-1\}$ whose block $(j, l)$ is $G_{j-l}$, with the
subtraction modulo $N$.

The leap-frog scheme for the wave equation is the case $m = 2$ with the unknowns
$(u^{n+1}, u^n)$. -/
noncomputable def periodicBlockScheme (G : Fin N → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin N × Fin m) (Fin N × Fin m) ℂ :=
  Matrix.of fun jp lq => G (jp.1 - lq.1) jp.2 lq.2

/-- **The amplification matrix** of the mode $k$ of a block scheme with blocks
$G_s \in \mathbb{C}^{m \times m}$:
$$G_k = \sum_s \omega^{-sk} G_s.$$
-/
noncomputable def amplificationMatrix (G : Fin N → Matrix (Fin m) (Fin m) ℂ) (k : Fin N) :
    Matrix (Fin m) (Fin m) ℂ :=
  ∑ s : Fin N, (Complex.exp (2 * π * I / N))⁻¹ ^ ((s : ℕ) * (k : ℕ)) • G s

/-- The mode $e_k$ tensored with a block vector $v \in \mathbb{C}^m$: the vector $e_k \otimes v$
with $(e_k \otimes v)(j, p) = e_k(j) v_p$. -/
noncomputable def modeTensor (N : ℕ) (k : Fin N) (v : Fin m → ℂ) : Fin N × Fin m → ℂ :=
  fun jp => fourierMode N k jp.1 * v jp.2

/-- The action of a block scheme $B$ with blocks $G_s$:
$(Bu)(j, p) = \sum_l (G_{j-l} u(l, \cdot))_p$, with the subtraction modulo $N$. -/
theorem periodicBlockScheme_mulVec_apply (G : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (u : Fin N × Fin m → ℂ) (j : Fin N) (p : Fin m) :
    (periodicBlockScheme G *ᵥ u) (j, p) = ∑ l, (G (j - l) *ᵥ fun q => u (l, q)) p := by
  rw [mulVec, dotProduct, ← Finset.univ_product_univ, Finset.sum_product]
  rfl

/-- **The tensored modes are eigenvectors of a block scheme**, with the amplification matrix acting
on the block. For blocks $G_s \in \mathbb{C}^{m \times m}$, every $k$ and every
$v \in \mathbb{C}^m$, the block scheme $B$ satisfies
$$B (e_k \otimes v) = e_k \otimes (G_k v).$$
-/
theorem periodicBlockScheme_mulVec_modeTensor (G : Fin N → Matrix (Fin m) (Fin m) ℂ) (k : Fin N)
    (v : Fin m → ℂ) :
    periodicBlockScheme G *ᵥ modeTensor N k v = modeTensor N k (amplificationMatrix G k *ᵥ v) := by
  ext ⟨j, p⟩
  have := NeZero.of_pos j.pos
  rw [periodicBlockScheme_mulVec_apply, modeTensor, amplificationMatrix, sum_mulVec,
    Finset.sum_apply, Finset.mul_sum]
  refine (Equiv.sum_comp (Equiv.subLeft j)
    fun l => (G (j - l) *ᵥ fun q => modeTensor N k v (l, q)) p).symm.trans
    (Finset.sum_congr rfl fun s _ => ?_)
  simp only [Equiv.subLeft_apply, sub_sub_cancel, modeTensor, smul_mulVec, Pi.smul_apply,
    smul_eq_mul]
  rw [fourierMode_sub]
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- **The powers of a block scheme on the tensored modes** (the multi-level analogue of
[quarteroni2000numerical], (13.52)). For blocks $G_s \in \mathbb{C}^{m \times m}$, every $k$,
every $v \in \mathbb{C}^m$ and every $n \in \mathbb{N}$, the block scheme $B$ satisfies
$$B^n (e_k \otimes v) = e_k \otimes (G_k^n v).$$
So the $\ell^2$ stability of a multi-level scheme is the uniform boundedness of the powers of
its $m \times m$ amplification matrices. -/
theorem periodicBlockScheme_pow_mulVec_fourierMode (G : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (k : Fin N) (v : Fin m → ℂ) (n : ℕ) :
    (periodicBlockScheme G ^ n) *ᵥ modeTensor N k v
      = modeTensor N k ((amplificationMatrix G k ^ n) *ᵥ v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, periodicBlockScheme_mulVec_modeTensor, pow_succ',
      ← mulVec_mulVec]

/-!
### The $\ell^2$ norm of the powers of a block scheme

The scalar argument carries over. Expanding a block grid function in the tensored modes
$e_k \otimes v$ diagonalizes the block circulant into the $m \times m$ amplification matrices. The
discrete Parseval identity, applied to each block component, then turns the $\ell^2$ norm of the
powers into the maximum of the norms of the powers of the amplification matrices.
-/

/-- Each entry of a Fourier mode has modulus $1$. -/
private theorem norm_fourierMode (k j : Fin N) : ‖fourierMode N k j‖ = 1 := by
  rw [fourierMode_apply, norm_pow]
  have h : Complex.exp (2 * π * I / N) = Complex.exp (((2 * π / N : ℝ) : ℂ) * I) := by
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I, one_pow]

/-- The blockwise discrete Parseval identity: $\sum_{k, p} |\hat u(k, p)|^2 = N \sum_{j, p} |u(j,
p)|^2$ for the componentwise transform $\hat u(k, p) = (F^H u(\cdot, p))_k$. -/
private theorem sum_normSq_blockDft (u : Fin N × Fin m → ℂ) :
    (∑ kp : Fin N × Fin m, ‖((Matrix.dft N)ᴴ *ᵥ fun j => u (j, kp.2)) kp.1‖ ^ 2)
      = N * ∑ jp : Fin N × Fin m, ‖u jp‖ ^ 2 := by
  have h : ∀ p : Fin m, (∑ k : Fin N, ‖((Matrix.dft N)ᴴ *ᵥ fun j => u (j, p)) k‖ ^ 2)
      = N * ∑ j : Fin N, ‖u (j, p)‖ ^ 2 :=
    fun p => sum_normSq_conjTranspose_dft_mulVec fun j => u (j, p)
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => h p

/-- The blockwise discrete Parseval identity for the inverse transform: $\sum_{j, p} |(F v(\cdot,
p))_j|^2 = N \sum_{k, p} |v(k, p)|^2$. -/
private theorem sum_normSq_blockExpand (v : Fin N × Fin m → ℂ) :
    (∑ jp : Fin N × Fin m, ‖(Matrix.dft N *ᵥ fun k => v (k, jp.2)) jp.1‖ ^ 2)
      = N * ∑ kp : Fin N × Fin m, ‖v kp‖ ^ 2 := by
  have h : ∀ p : Fin m, (∑ j : Fin N, ‖(Matrix.dft N *ᵥ fun k => v (k, p)) j‖ ^ 2)
      = N * ∑ k : Fin N, ‖v (k, p)‖ ^ 2 :=
    fun p => sum_normSq_dft_mulVec fun k => v (k, p)
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => h p

/-- A sum of tensored modes is the inverse transform of its coefficients, componentwise: $(\sum_k
e_k \otimes w_k)(j, p) = (F w_{\cdot, p})_j$. -/
private theorem sum_modeTensor_apply (w : Fin N → Fin m → ℂ) (jp : Fin N × Fin m) :
    (∑ k : Fin N, modeTensor N k (w k)) jp = (Matrix.dft N *ᵥ fun k => w k jp.2) jp.1 := by
  rw [Finset.sum_apply, mulVec, dotProduct]
  rfl

/-- The squared $\ell^2$ norm of a tensored mode: $\sum_{j, p} |(e_k \otimes w)(j, p)|^2 = N \sum_p
|w_p|^2$.
-/
private theorem sum_normSq_modeTensor (k : Fin N) (w : Fin m → ℂ) :
    (∑ jp : Fin N × Fin m, ‖modeTensor N k w jp‖ ^ 2) = N * ∑ p, ‖w p‖ ^ 2 := by
  have h : ∀ j : Fin N, (∑ p, ‖modeTensor N k w (j, p)‖ ^ 2) = ∑ p, ‖w p‖ ^ 2 := by
    intro j
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [modeTensor, norm_mul, norm_fourierMode, one_mul]
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun j _ => h j, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A bound $\|M\|_2 \le \rho$ on the operator norm of a matrix gives
$\sum_p |(Mw)_p|^2 \le \rho^2 \sum_p |w_p|^2$. -/
private theorem sum_normSq_mulVec_le {M : Matrix (Fin m) (Fin m) ℂ} {ρ : ℝ}
    (hρ : ‖toEuclideanCLM (𝕜 := ℂ) M‖ ≤ ρ) (w : Fin m → ℂ) :
    (∑ p, ‖(M *ᵥ w) p‖ ^ 2) ≤ ρ ^ 2 * ∑ p, ‖w p‖ ^ 2 := by
  have h := (toEuclideanCLM (𝕜 := ℂ) M).le_opNorm (WithLp.toLp 2 w)
  rw [toEuclideanCLM_toLp] at h
  have h2 : ‖(WithLp.toLp 2 (M *ᵥ w) : EuclideanSpace ℂ (Fin m))‖
      ≤ ρ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin m))‖ :=
    h.trans (mul_le_mul_of_nonneg_right hρ (norm_nonneg _))
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → √a ≤ ρ * √b → a ≤ ρ ^ 2 * b := by
    intro a b ha hb hab
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  exact key _ _ (by positivity) (by positivity) (by simpa [EuclideanSpace.norm_eq] using h2)

/-- For $N \ge 1$, if $\|G_k^n\|_2 \le \rho$ for every $k$, then $\sum_{j, p} |(B^n y)(j, p)|^2 \le
\rho^2 \sum_{j, p} |y(j, p)|^2$ for the block scheme $B$. -/
private theorem sum_normSq_periodicBlockScheme_pow_le (G : Fin N → Matrix (Fin m) (Fin m) ℂ)
    {ρ : ℝ} {n : ℕ} (hN : 0 < N)
    (hρ : ∀ k, ‖toEuclideanCLM (𝕜 := ℂ) (amplificationMatrix G k ^ n)‖ ≤ ρ)
    (y : Fin N × Fin m → ℂ) :
    (∑ jp : Fin N × Fin m, ‖((periodicBlockScheme G ^ n) *ᵥ y) jp‖ ^ 2)
      ≤ ρ ^ 2 * ∑ jp : Fin N × Fin m, ‖y jp‖ ^ 2 := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set û : Fin N × Fin m → ℂ :=
    fun kp => ((Matrix.dft N)ᴴ *ᵥ fun j => y (j, kp.2)) kp.1 with hû
  set z : Fin N × Fin m → ℂ :=
    fun kp => ((amplificationMatrix G kp.1 ^ n) *ᵥ fun q => û (kp.1, q)) kp.2 with hz
  -- `y` is the inverse transform of `û`, hence a superposition of tensored modes
  have hinv : ∀ p : Fin m, (Matrix.dft N *ᵥ fun k => û (k, p)) = (N : ℂ) • fun j => y (j, p) := by
    intro p
    change (Matrix.dft N *ᵥ ((Matrix.dft N)ᴴ *ᵥ fun j => y (j, p))) = _
    rw [mulVec_mulVec, Matrix.dft_mul_conjTranspose_dft, smul_mulVec, one_mulVec]
  have hy : y = ((N : ℂ))⁻¹ • ∑ k : Fin N, modeTensor N k (fun q => û (k, q)) := by
    funext jp
    rw [Pi.smul_apply, smul_eq_mul, sum_modeTensor_apply, hinv jp.2, Pi.smul_apply, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hNC, one_mul]
  -- the powers act modewise
  have hstep : ∀ k : Fin N, (periodicBlockScheme G ^ n) *ᵥ modeTensor N k (fun q => û (k, q))
      = modeTensor N k (fun q => z (k, q)) :=
    fun k => periodicBlockScheme_pow_mulVec_fourierMode G k (fun q => û (k, q)) n
  have hBy : (periodicBlockScheme G ^ n) *ᵥ y
      = fun jp => ((N : ℂ))⁻¹ * (Matrix.dft N *ᵥ fun k => z (k, jp.2)) jp.1 := by
    rw [hy, mulVec_smul, mulVec_sum, Finset.sum_congr rfl fun k _ => hstep k]
    funext jp
    rw [Pi.smul_apply, smul_eq_mul, sum_modeTensor_apply]
  -- Parseval on both sides
  have h1 : (∑ jp : Fin N × Fin m, ‖((periodicBlockScheme G ^ n) *ᵥ y) jp‖ ^ 2)
      = ((N : ℝ))⁻¹ * ∑ kp : Fin N × Fin m, ‖z kp‖ ^ 2 := by
    rw [hBy]
    simp only [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
    rw [← Finset.mul_sum, sum_normSq_blockExpand]
    field_simp
  have hblock : ∀ k : Fin N, (∑ p : Fin m, ‖z (k, p)‖ ^ 2)
      ≤ ρ ^ 2 * ∑ p : Fin m, ‖û (k, p)‖ ^ 2 :=
    fun k => sum_normSq_mulVec_le (hρ k) fun q => û (k, q)
  have h2 : (∑ kp : Fin N × Fin m, ‖z kp‖ ^ 2) ≤ ρ ^ 2 * ∑ kp : Fin N × Fin m, ‖û kp‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hblock k
  have h3 : (∑ kp : Fin N × Fin m, ‖û kp‖ ^ 2) = N * ∑ jp : Fin N × Fin m, ‖y jp‖ ^ 2 :=
    sum_normSq_blockDft y
  rw [h3] at h2
  rw [h1]
  calc ((N : ℝ))⁻¹ * ∑ kp : Fin N × Fin m, ‖z kp‖ ^ 2
      ≤ ((N : ℝ))⁻¹ * (ρ ^ 2 * ((N : ℝ) * ∑ jp : Fin N × Fin m, ‖y jp‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ρ ^ 2 * ∑ jp : Fin N × Fin m, ‖y jp‖ ^ 2 := by field_simp

/-- **The $\ell^2$ bound for the powers of a block scheme.** Let $G_s \in \mathbb{C}^{m \times m}$
be the blocks of a block scheme $B$, let $n \in \mathbb{N}$, and let $\rho \in \mathbb{R}$
satisfy $\|G_k^n\|_2 \le \rho$ for every amplification matrix $G_k$. Then for every
$u \in \mathbb{C}^{N \times m}$,
$$\|B^n u\|_2 \le \rho \|u\|_2.$$

The expansion of $u$ in the tensored modes diagonalizes $B^n$ into the blocks $G_k^n$
(`FiniteDifference.periodicBlockScheme_pow_mulVec_fourierMode`), and the discrete Parseval
identity, applied to each block component of the transform, turns the bounds for each mode into
the global bound. -/
theorem norm_toEuclideanLin_periodicBlockScheme_pow_le (G : Fin N → Matrix (Fin m) (Fin m) ℂ)
    {ρ : ℝ} {n : ℕ} (hρ : ∀ k, ‖toEuclideanCLM (𝕜 := ℂ) (amplificationMatrix G k ^ n)‖ ≤ ρ)
    (u : EuclideanSpace ℂ (Fin N × Fin m)) :
    ‖toEuclideanLin (periodicBlockScheme G ^ n) u‖ ≤ ρ * ‖u‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (hρ ⟨0, hN⟩)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hρ0,
    ← Real.sqrt_mul (sq_nonneg ρ)]
  refine Real.sqrt_le_sqrt ?_
  exact sum_normSq_periodicBlockScheme_pow_le G hN hρ (WithLp.ofLp u)

/-- The operator norm form of the $\ell^2$ bound for a block scheme. Let $n \in \mathbb{N}$ and
$\rho \ge 0$ satisfy $\|G_k^n\|_2 \le \rho$ for every amplification matrix $G_k$. Then the block
scheme $B$ satisfies $\|B^n\|_2 \le \rho$. -/
theorem norm_toEuclideanCLM_periodicBlockScheme_pow_le (G : Fin N → Matrix (Fin m) (Fin m) ℂ)
    {ρ : ℝ} {n : ℕ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ k, ‖toEuclideanCLM (𝕜 := ℂ) (amplificationMatrix G k ^ n)‖ ≤ ρ) :
    ‖toEuclideanCLM (𝕜 := ℂ) (periodicBlockScheme G ^ n)‖ ≤ ρ :=
  ContinuousLinearMap.opNorm_le_bound _ hρ0 fun u =>
    norm_toEuclideanLin_periodicBlockScheme_pow_le G hρ u

/-- **The amplification matrices bound the norm of the powers from below.** For blocks
$G_s \in \mathbb{C}^{m \times m}$, every $k$ and every $n \in \mathbb{N}$, the block scheme $B$
satisfies
$$\|G_k^n\|_2 \le \|B^n\|_2.$$

The proof tests $B^n$ on the tensored modes $e_k \otimes v$, whose norm is $\sqrt{N} \|v\|$.
Together with `FiniteDifference.norm_toEuclideanCLM_periodicBlockScheme_pow_le`, this makes the
$\ell^2$ stability of a multi-level scheme exactly the uniform boundedness of the powers of its
$m \times m$ amplification matrices. -/
theorem norm_toEuclideanCLM_amplificationMatrix_pow_le (G : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (k : Fin N) (n : ℕ) :
    ‖toEuclideanCLM (𝕜 := ℂ) (amplificationMatrix G k ^ n)‖
      ≤ ‖toEuclideanCLM (𝕜 := ℂ) (periodicBlockScheme G ^ n)‖ := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr k.pos
  have hsqrt : (0 : ℝ) < √N := Real.sqrt_pos.mpr hNR
  have hnorm : ∀ u : Fin m → ℂ,
      ‖(WithLp.toLp 2 (modeTensor N k u) : EuclideanSpace ℂ (Fin N × Fin m))‖
        = √N * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin m))‖ := by
    intro u
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul (Nat.cast_nonneg N)]
    congr 1
    simpa using sum_normSq_modeTensor k u
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  have h := (toEuclideanCLM (𝕜 := ℂ) (periodicBlockScheme G ^ n)).le_opNorm
    (WithLp.toLp 2 (modeTensor N k (WithLp.ofLp v)))
  rw [toEuclideanCLM_toLp, periodicBlockScheme_pow_mulVec_fourierMode, hnorm, hnorm] at h
  have hv : (WithLp.toLp 2 (WithLp.ofLp v) : EuclideanSpace ℂ (Fin m)) = v := rfl
  rw [hv] at h
  have hgv : toEuclideanCLM (𝕜 := ℂ) (amplificationMatrix G k ^ n) v
      = WithLp.toLp 2 ((amplificationMatrix G k ^ n) *ᵥ WithLp.ofLp v) := rfl
  rw [hgv]
  nlinarith [h, norm_nonneg (WithLp.toLp 2 ((amplificationMatrix G k ^ n) *ᵥ WithLp.ofLp v) :
    EuclideanSpace ℂ (Fin m)), norm_nonneg v,
    norm_nonneg (toEuclideanCLM (𝕜 := ℂ) (periodicBlockScheme G ^ n))]

end Block

end FiniteDifference
