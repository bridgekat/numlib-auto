import Mathlib.Analysis.SpecialFunctions.Arsinh
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Direct.Updating
import NumlibSurface.GolubVanLoan.Chapter05.Section02

/-!
# Golub–Van Loan §6.5: updating matrix factorizations

Surface file for [golub2013matrix] §6.5: the QR factorization after a rank-one change
((6.5.1)–(6.5.3)), after deleting or appending a column ((6.5.4)) and after appending or deleting a
row; Cholesky updating ((6.5.5)–(6.5.7)) and downdating with hyperbolic rotations
((6.5.8)–(6.5.15), Theorem 6.5.1); the exact content of the rank-revealing ULV decomposition
(6.5.16) and its approximate null space.

## Conventions

Real matrices, 0-based: the book's `n`-by-`n` matrices are `Matrix (Fin n) (Fin n) ℝ`. The book's
QR factorization `A = QR` is `Matrix.IsQR A Q R` (`Q` orthogonal — `unitaryGroup` over `ℝ` — and
`R` upper trapezoidal). The book's Cholesky factorization `A = G Gᵀ` with `G` lower triangular is
the backbone's `Matrix.IsCholesky A Gᵀ` (upper triangular factor with positive diagonal,
`(Gᵀ)ᵀ Gᵀ = A`). The stacked matrix `[Gᵀ; zᵀ]` of (6.5.6) and (6.5.10) is
`Matrix.fromRows Gᵀ (replicateRow Unit z)`, with rows `Fin n ⊕ Unit`; the signature
`S = diag(I_n, −1)` of (6.5.9) is Mathlib's `LieAlgebra.Orthogonal.indefiniteDiagonal (Fin n) Unit`.
A sweep of rotations in the adjacent planes `(k, k + 1)` is a product of the backbone's
`Matrix.adjacentEmbed k (G k)`; the hyperbolic rotation `H_k` of §6.5.4 is
`Matrix.hyperbolicRotation (Sum.inl k) (Sum.inr ()) c s`. The partitions `[R; 0]` of (6.5.16) are
`Matrix.fromRows` over `Fin n ⊕ Fin p`, the rows of `A : Matrix (Fin (n + p)) (Fin n) ℝ` being
reindexed by `finSumFinEquiv`.

The section has no numbered algorithm. Its prose procedures are programs named by content, in the
algorithm conventions of `NumlibSurface/GolubVanLoan`: every product, difference, quotient and
square root is passed through the rounding hook `rnd`, loops are `List.foldlM`, and the exact
semantics (`M := Id`, `rnd := pure`) is a `_spec` theorem against the backbone. The Cholesky
downdate `choleskyDowndate` writes its hyperbolic rotations out (they are not Givens rotations),
through the row helper `hyperbolicApplyLeft`. The Givens-based procedures (`qrUpdateRankOne`,
`qrDeleteColumn`, `qrInsertColumn`, `qrInsertRow`, `qrDeleteFirstRow`, `choleskyUpdate`) call
chapter 5's shared programs (conventions 5 and 13): the pair `[c, s] = givens(a, b)` is
`Chapter05.algorithm_5_1_3`, "rotate rows `i`, `k`" is `Chapter05.givensApplyLeft`, "rotate columns
`i`, `k` of `Q`" is `Chapter05.givensApplyRight`, "rotate entries `i`, `k` of `w`" is
`Chapter05.givensRotateVec`; the products `Qᵀu` are chapter 1's gaxpy (Algorithm 1.1.3) and the
rank-one change of the first row its saxpy (Algorithm 1.1.2). Two sweeps are shared: the top-down
triangularization of an upper Hessenberg matrix (`givensHessenbergSweep`, after Algorithm 5.2.5)
and the bottom-up sweep driven by a vector (`givensVectorSweep`). Every rotation is applied to all
the columns (resp. rows) of its matrix; the book leaves the column ranges implicit, and the extra
columns are zero in both rotated rows.

## Sources

Backbone `Numlib/Direct/Updating` (the structural lemmas of the sweeps, the existence of the
updated factorizations, the stacked Gram identities, Theorem 6.5.1 as
`Matrix.hyperbolicDowndate_step`), `Numlib/LinearAlgebra/Matrix/PlaneRotation` (hyperbolic
rotations, `Matrix.hyperbolicPair`, `Matrix.IsJOrthogonal`), `Numlib/Analysis/Matrix/OperatorNorm`;
the programs and exact specifications of chapter 5 (`Chapter05.algorithm_5_1_3_spec`,
`givensApplyLeft_spec`, `givensApplyRight_spec`) and chapter 1 (Algorithms 1.1.2–1.1.3).

Errata ([golub2013matrix] §6.5): "Following Algorithm 5.2.4" in §6.5.1 means Algorithm 5.2.5
(Hessenberg QR); §6.5.4 prints `Ã = RRᵀ` for `RᵀR`, and `G̃ = Rᵀ` is the Cholesky factor only up
to the signs of its diagonal when the rotations are Givens rotations (a Givens `r` may be
negative), which `equation_6_5_7` normalizes; the statement of Theorem 6.5.1 is mangled in print
("If / and / A = …"), and the "Schur complement of `α`" in its proof is the Schur complement of the
`(1,1)` entry `α − μ²` of `Ã`; in §6.5.5, `‖AV₂‖₂ = ‖U₂L₂₂‖₂` uses `U₂ = U(:, r+1:m)`, which does
not match the `n − r` rows of `L₂₂` — the columns `r+1:n` of `U` are meant, and either way the norm
is `‖L₂₂‖₂` (`ulv_nullspace_norm`).

## Not formalized

The ULV updating procedure of §6.5.5 beyond (6.5.16) (condition estimation, "small" entries,
"`≈ σ_min`", zero chasing), the rank-revealing smallness of `L₂₁`, `L₂₂`, the numerical caveats on
hyperbolic rotations with `|x₁| ≈ |x₂|`, and the flop counts (`26n²`, `O(n²)`, `O(mn)`). (6.5.4),
(6.5.5), (6.5.8), (6.5.9) only name data.
-/

open Matrix

namespace GolubVanLoan.Chapter06

/-! ### §6.5.1 Rank-one changes -/

/-- **(6.5.1).** "Suppose we have the QR factorization `QR = A ∈ ℝⁿˣⁿ` … Observe that
`Ã = A + uvᵀ = Q(R + wvᵀ)` where `w = Qᵀu`." -/
theorem equation_6_5_1 {n : ℕ} {A Q R : Matrix (Fin n) (Fin n) ℝ} (h : IsQR A Q R)
    (u v : Fin n → ℝ) : A + vecMulVec u v = Q * (R + vecMulVec (Qᵀ *ᵥ u) v) := by
  have hQ : Q * Qᵀ = 1 := by
    have := mem_unitaryGroup_iff.1 h.mem_unitaryGroup
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [Matrix.mul_add, h.mul_eq, mul_vecMulVec, mulVec_mulVec, hQ, one_mulVec]

/-- **(6.5.2).** "Suppose rotations `J_{n−1}, …, J₂, J₁` are computed such that
`J₁ᵀ ⋯ J_{n−1}ᵀ w = ±‖w‖₂ e₁` where each `J_k` is a Givens rotation in planes `k` and `k + 1`. If
these same rotations are applied to `R`, then `H = J₁ᵀ ⋯ J_{n−1}ᵀ R` is upper Hessenberg."

The shape holds whatever the rotations are: `J_kᵀ` (0-based plane `(k, k + 1)`) is
`Matrix.adjacentEmbed k (G k)` for an arbitrary `2 × 2` block `G k`, and the sweep
`P = J₁ᵀ ⋯ J_{n−1}ᵀ` applies `J_{n−1}ᵀ` first. -/
theorem equation_6_5_2 {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ} (hR : R.IsUpperTriangular)
    (G : ℕ → Matrix (Fin 2) (Fin 2) ℝ) {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P = (List.map (fun j => adjacentEmbed j (G j)) (List.range (n - 1))).prod)
    (i l : Fin n) (hil : (l : ℕ) + 1 < i) : (P * R) i l = 0 := by
  have hT : R.HasLowerBandwidthRect 0 := fun i j hij => hR (by
    change j < i
    rw [Fin.lt_def]
    omega)
  rw [hP, List.range_eq_range']
  exact prod_planeEmbed_mul_apply_eq_zero hT G 0 (n - 1) (Or.inl hil)

/-- **(6.5.3).** "Consequently, `(J₁ᵀ ⋯ J_{n−1}ᵀ)(R + wvᵀ) = H ± ‖w‖₂ e₁vᵀ = H₁` is also upper
Hessenberg": if the sweep `P` of (6.5.2) maps `w` to `ρ e₁` (the book's `ρ = ±‖w‖₂`), then
`P (R + wvᵀ) = P R + ρ e₁ vᵀ`, and it vanishes below the subdiagonal. -/
theorem equation_6_5_3 {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ} (hR : R.IsUpperTriangular)
    (G : ℕ → Matrix (Fin 2) (Fin 2) ℝ) {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P = (List.map (fun j => adjacentEmbed j (G j)) (List.range (n - 1))).prod)
    {w : Fin n → ℝ} {ρ : ℝ} (hn : 0 < n) (hw : P *ᵥ w = Pi.single ⟨0, hn⟩ ρ) (v : Fin n → ℝ) :
    P * (R + vecMulVec w v) = P * R + vecMulVec (Pi.single ⟨0, hn⟩ ρ) v ∧
      ∀ i l : Fin n, (l : ℕ) + 1 < i → (P * (R + vecMulVec w v)) i l = 0 := by
  have e : P * (R + vecMulVec w v) = P * R + vecMulVec (Pi.single ⟨0, hn⟩ ρ) v := by
    rw [Matrix.mul_add, mul_vecMulVec, hw]
  refine ⟨e, fun i l hil => ?_⟩
  rw [e, Matrix.add_apply, equation_6_5_2 hR G hP i l hil, zero_add, vecMulVec_apply,
    Pi.single_apply, ite_eq_right (fun h => by rw [h] at hil; simp at hil), zero_mul]

/-! ### §6.5.3 Appending or deleting a row -/

/-- **§6.5.3**, "(The procedure is similar when an arbitrary row is deleted.)": if `A = QR` with
`A ∈ ℝ^{(m+1)×n}`, then `A` with its row `k` deleted has a QR factorization. -/
theorem qrDeleteRow_exists {m n : ℕ} {A : Matrix (Fin (m + 1)) (Fin n) ℝ}
    {Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {R : Matrix (Fin (m + 1)) (Fin n) ℝ}
    (h : IsQR A Q R) (k : Fin (m + 1)) :
    ∃ Q₁ R₁, IsQR (A.submatrix k.succAbove id) Q₁ R₁ := by
  obtain ⟨-, -, -, Q₁, -, R₁, -, -, -, -, h₁⟩ := h.exists_deleteRow k
  exact ⟨Q₁, R₁, h₁⟩

/-! ### §6.5.4 Cholesky updating -/

/-- **(6.5.6).** "`Ã = [Gᵀ; zᵀ]ᵀ [Gᵀ; zᵀ]`" for `Ã = A + zzᵀ` (6.5.5) and `A = GGᵀ`. -/
theorem equation_6_5_6 {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hA : G * Gᵀ = A)
    (z : Fin n → ℝ) :
    A + vecMulVec z z =
      (fromRows Gᵀ (replicateRow Unit z))ᵀ * fromRows Gᵀ (replicateRow Unit z) := by
  rw [transpose_mul_self_fromRows, transpose_transpose, hA]

/-- **(6.5.7).** "we can solve this problem by computing a product of Givens rotations
`Q = Q₁ ⋯ Q_n` so that `Qᵀ [Gᵀ; zᵀ] = [R; 0]` is upper triangular. It follows that `Ã = RRᵀ` and
so the updated Cholesky factor is given by `G̃ = Rᵀ`." For any orthogonal `Q`, `Ã = RᵀR` (the book's
`RRᵀ` is a typo); with the signs of the diagonal of `R` normalized, `Rᵀ` is the Cholesky factor. -/
theorem equation_6_5_7 {n : ℕ} {A G R : Matrix (Fin n) (Fin n) ℝ} (hA : G * Gᵀ = A)
    {z : Fin n → ℝ} {Q : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n ⊕ Unit) ℝ)
    (h : Qᵀ * fromRows Gᵀ (replicateRow Unit z) = fromRows R 0) :
    A + vecMulVec z z = Rᵀ * R ∧
      (R.IsUpperTriangular → (∀ i, R i i ≠ 0) →
        IsCholesky (A + vecMulVec z z) (diagonal (fun i => (SignType.sign (R i i) : ℝ)) * R)) := by
  have e : A + vecMulVec z z = Rᵀ * R := by
    rw [equation_6_5_6 hA, transpose_mul_self_eq_of_mem_orthogonalGroup hQ h]
  exact ⟨e, fun hR hd => isCholesky_diagonal_sign_mul hR hd e.symm⟩

/-! ### §6.5.4 Cholesky downdating: `S`-orthogonality and hyperbolic rotations -/

/-- **(6.5.10).** "`Ã = GGᵀ − zzᵀ = [Gᵀ; zᵀ]ᵀ S [Gᵀ; zᵀ]`" with `S = diag(I_n, −1)` (6.5.9). -/
theorem equation_6_5_10 {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hA : G * Gᵀ = A)
    (z : Fin n → ℝ) :
    A - vecMulVec z z =
      (fromRows Gᵀ (replicateRow Unit z))ᵀ *
        LieAlgebra.Orthogonal.indefiniteDiagonal (Fin n) Unit ℝ *
          fromRows Gᵀ (replicateRow Unit z) := by
  rw [transpose_mul_indefiniteDiagonal_mul_fromRows, transpose_transpose, hA]

/-- **§6.5.4, (6.5.11).** "A matrix `H` that satisfies (6.5.11) [`HSHᵀ = S`] is said to be
`S`-orthogonal", for `S = diag(I_n, −1)`. -/
def IsSOrthogonal {n : ℕ} (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ) : Prop :=
  IsJOrthogonal (LieAlgebra.Orthogonal.indefiniteDiagonal (Fin n) Unit ℝ) H

/-- **§6.5.4.** "Note that the product of `S`-orthogonal matrices is also `S`-orthogonal." -/
theorem IsSOrthogonal.mul {n : ℕ} {H₁ H₂ : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ}
    (h₁ : IsSOrthogonal H₁) (h₂ : IsSOrthogonal H₂) : IsSOrthogonal (H₁ * H₂) :=
  IsJOrthogonal.mul h₁ h₂

/-- **(6.5.11)–(6.5.12).** "we seek a matrix `H` … that satisfies two properties: `HSHᵀ = S`,
`Hᵀ [Gᵀ; zᵀ] = [R; 0]` … If this can be accomplished, then it follows … `Ã = RᵀR` … that the
Cholesky factor of `Ã = A − zzᵀ` is given by `G̃ = Rᵀ`" — once the signs of the diagonal of the
triangular `R` are normalized. -/
theorem equation_6_5_12 {n : ℕ} {A G R : Matrix (Fin n) (Fin n) ℝ} (hA : G * Gᵀ = A)
    {z : Fin n → ℝ} {H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ} (hH : IsSOrthogonal H)
    (h : Hᵀ * fromRows Gᵀ (replicateRow Unit z) = fromRows R 0) :
    A - vecMulVec z z = Rᵀ * R ∧
      (R.IsUpperTriangular → (∀ i, R i i ≠ 0) →
        IsCholesky (A - vecMulVec z z) (diagonal (fun i => (SignType.sign (R i i) : ℝ)) * R)) := by
  have e : A - vecMulVec z z = Rᵀ * R := by
    rw [← transpose_mul_self_sub_eq_of_isJOrthogonal hH h, transpose_transpose, hA]
  exact ⟨e, fun hR hd => isCholesky_diagonal_sign_mul hR hd e.symm⟩

/-- **§6.5.4, hyperbolic rotations.** "`H_k ∈ ℝ^{(n+1)×(n+1)}` is a hyperbolic rotation if it
agrees with `I_{n+1}` except in four locations: `[H_k]_{kk} = [H_k]_{n+1,n+1} = cosh(θ)`,
`[H_k]_{k,n+1} = [H_k]_{n+1,k} = −sinh(θ)`. … The `S`-orthogonality of this matrix follows from
`cosh(θ)² − sinh(θ)² = 1`." -/
theorem hyperbolicRotation_isSOrthogonal {n : ℕ} (k : Fin n) (θ : ℝ) :
    IsSOrthogonal (hyperbolicRotation (Sum.inl k) (Sum.inr ()) (Real.cosh θ) (Real.sinh θ)) :=
  isJOrthogonal_hyperbolicRotation Sum.inl_ne_inr (ε := Sum.elim (fun _ => 1) fun _ => -1)
    rfl rfl (by rw [Real.cosh_sq θ]; ring)

/-- **(6.5.13).** "if `|x₁| > |x₂|`, then `{c, s} = {cosh(θ), sinh(θ)}` can be computed as follows:
`τ = x₂/x₁`, `c = 1/√(1 − τ²)`, `s = c · τ`", and then `[c −s; −s c][x₁; x₂] = [r; 0]` (with
`r = sign(x₁) √(x₁² − x₂²)`). The pair is the backbone's `Matrix.hyperbolicPair x₁ x₂`; `c > 0`
and `c² − s² = 1` make it `(cosh θ, sinh θ)` for `θ = arsinh s`. -/
theorem equation_6_5_13 {x₁ x₂ c s : ℝ} (h : |x₂| < |x₁|)
    (hc : c = 1 / √(1 - (x₂ / x₁) ^ 2)) (hs : s = c * (x₂ / x₁)) :
    c ^ 2 - s ^ 2 = 1 ∧ Real.cosh (Real.arsinh s) = c ∧ Real.sinh (Real.arsinh s) = s ∧
      (hyperbolicRotation (0 : Fin 2) 1 c s *ᵥ ![x₁, x₂]) 1 = 0 ∧
      (hyperbolicRotation (0 : Fin 2) 1 c s *ᵥ ![x₁, x₂]) 0 =
        SignType.sign x₁ * √(x₁ ^ 2 - x₂ ^ 2) := by
  have hp : (c, s) = hyperbolicPair x₁ x₂ := by
    rw [hs, hc, hyperbolicPair]
  have hx : |(![x₁, x₂] : Fin 2 → ℝ) 1| < |(![x₁, x₂] : Fin 2 → ℝ) 0| := h
  obtain ⟨hcs, hc0⟩ := hyperbolicPair_sq_sub_sq h
  obtain ⟨h1, h0⟩ := hyperbolicRotation_hyperbolicPair_mulVec (Fin.zero_ne_one) hx
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h0
  rw [← hp] at hcs hc0 h1 h0
  refine ⟨hcs, ?_, Real.sinh_arsinh s, h1, h0⟩
  rw [Real.cosh_arsinh]
  rw [show 1 + s ^ 2 = c ^ 2 by linarith, Real.sqrt_sq hc0.le]

/-- **§6.5.4.** "Since we always have `|cosh(θ)| > |sinh(θ)|`, there is no real solution to
`−sx₁ + cx₂ = 0` if `|x₂| > |x₁|`" — nor if `|x₂| = |x₁| ≠ 0`. -/
theorem hyperbolic_not_exists {x₁ x₂ : ℝ} (h : |x₁| ≤ |x₂|) (hx₂ : x₂ ≠ 0) :
    ¬ ∃ c s : ℝ, c ^ 2 - s ^ 2 = 1 ∧ -s * x₁ + c * x₂ = 0 :=
  not_exists_hyperbolic_of_abs_le h hx₂

/-- **§6.5.4.** "Since `Ã = GGᵀ − zzᵀ` is positive definite, `[Ã]₁₁ = g₁₁² − z₁² > 0`. It follows
that `|g₁₁| > |z₁|` which guarantees that the cosh-sinh computations (6.5.13) go through." Here
`g₁₁` is the `(0, 0)` entry of the upper triangular factor `Gᵀ`. -/
theorem abs_lt_of_posDef_sub {n : ℕ} {A H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : IsCholesky A H) {z : Fin (n + 1) → ℝ} (hA : (A - vecMulVec z z).PosDef) :
    (A - vecMulVec z z) 0 0 = H 0 0 ^ 2 - z 0 ^ 2 ∧ 0 < H 0 0 ^ 2 - z 0 ^ 2 ∧
      |z 0| < |H 0 0| := by
  have h00 : A 0 0 = H 0 0 ^ 2 := by
    rw [hH.apply_eq_sum 0 0]
    simp [Finset.filter_eq', sq]
  have e : (A - vecMulVec z z) 0 0 = H 0 0 ^ 2 - z 0 ^ 2 := by
    rw [Matrix.sub_apply, vecMulVec_apply, h00]
    ring
  have hpos : 0 < H 0 0 ^ 2 - z 0 ^ 2 := e ▸ hA.diag_pos
  exact ⟨e, hpos, sq_lt_sq.1 (by linarith)⟩

/-- **Theorem 6.5.1.** "If `A = [α vᵀ; v B] = [g₁₁ 0; g₁ G₁][g₁₁ g₁ᵀ; 0 G₁ᵀ]` and
`Ã = A − zzᵀ = A − [μ; w][μ; w]ᵀ` are positive definite, then it is possible to determine
`c = cosh(θ)` and `s = sinh(θ)` so
`[c 0 −s; 0 I_{n−1} 0; −s 0 c][g₁₁ g₁ᵀ; 0 G₁ᵀ; μ wᵀ] = [g̃₁₁ g̃₁ᵀ; 0 G₁ᵀ; 0 w₁ᵀ]`. Moreover, the
matrix `Ã₁ = G₁G₁ᵀ − w₁w₁ᵀ` is positive definite."

The factorization is `Matrix.IsCholesky A H` with `H = [g₁₁ g₁ᵀ; 0 G₁ᵀ]` on `Fin (n + 1)`, the
first index carrying `α`, `g₁₁`, `μ`; the rotated stacked matrix is `[R'; z'ᵀ]` with `R'` equal to
`H` off its first row, `z'₀ = 0`, and `w₁ = z'(1:)`. -/
theorem theorem_6_5_1 {n : ℕ} {A H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : IsCholesky A H) {z : Fin (n + 1) → ℝ} (hA : (A - vecMulVec z z).PosDef) :
    ∃ θ : ℝ, ∃ (R' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z' : Fin (n + 1) → ℝ),
      hyperbolicRotation (Sum.inl (0 : Fin (n + 1))) (Sum.inr ()) (Real.cosh θ) (Real.sinh θ) *
          fromRows H (replicateRow Unit z) = fromRows R' (replicateRow Unit z') ∧
        z' 0 = 0 ∧ (∀ i, i ≠ 0 → R' i = H i) ∧
        ((H.submatrix Fin.succ Fin.succ)ᵀ * H.submatrix Fin.succ Fin.succ -
          vecMulVec (fun j : Fin n => z' j.succ) (fun j : Fin n => z' j.succ)).PosDef := by
  obtain ⟨hlt, hcs, R', z', e, hz0, -, hR', -, hpd⟩ :=
    hyperbolicDowndate_step hH hA (c := √(A 0 0) / √(A 0 0 - z 0 ^ 2))
      (s := z 0 / √(A 0 0 - z 0 ^ 2)) rfl rfl
  set c := √(A 0 0) / √(A 0 0 - z 0 ^ 2) with hc
  set s := z 0 / √(A 0 0 - z 0 ^ 2) with hs
  have hc0 : 0 < c := by
    have : 0 < A 0 0 := lt_of_le_of_lt (sq_nonneg _) hlt
    rw [hc]
    exact div_pos (Real.sqrt_pos.2 this) (Real.sqrt_pos.2 (by linarith))
  have hcosh : Real.cosh (Real.arsinh s) = c := by
    rw [Real.cosh_arsinh, show 1 + s ^ 2 = c ^ 2 by linarith, Real.sqrt_sq hc0.le]
  refine ⟨Real.arsinh s, R', z', ?_, hz0, hR', hpd⟩
  rw [hcosh, Real.sinh_arsinh]
  exact e

/-- **(6.5.14).** "The blocks in `A`'s Cholesky factor are given by `g₁₁ = √α`, `g₁ = v/g₁₁`,
`G₁G₁ᵀ = B − (1/α)vvᵀ`", for `A = [α vᵀ; v B]` on `Fin (n + 1)` and its Cholesky factorization
`Matrix.IsCholesky A H`, `H = [g₁₁ g₁ᵀ; 0 G₁ᵀ]`. -/
theorem equation_6_5_14 {n : ℕ} {A H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : IsCholesky A H) :
    H 0 0 = √(A 0 0) ∧ (∀ j : Fin n, H 0 j.succ = A j.succ 0 / H 0 0) ∧
      (H.submatrix Fin.succ Fin.succ)ᵀ * H.submatrix Fin.succ Fin.succ =
        A.submatrix Fin.succ Fin.succ -
          (1 / A 0 0) • vecMulVec (fun j : Fin n => A j.succ 0) (fun j : Fin n => A j.succ 0) := by
  have hA : Hᵀ * H = A := by
    rw [← conjTranspose_eq_transpose_of_trivial, hH.conjTranspose_mul_self]
  have hcol : ∀ i : Fin n, H i.succ 0 = 0 := fun i => hH.isUpperTriangular (Fin.succ_pos i)
  have hent : ∀ i j, A i j = H 0 i * H 0 j + ∑ k : Fin n, H k.succ i * H k.succ j := by
    intro i j
    rw [← hA, mul_apply, Fin.sum_univ_succ]
    rfl
  have h00 : A 0 0 = H 0 0 ^ 2 := by
    rw [hent]
    simp [hcol, sq]
  have hH0 := hH.diag_pos 0
  have hv : ∀ j : Fin n, A j.succ 0 = H 0 0 * H 0 j.succ := fun j => by
    rw [hent]
    simp [hcol, mul_comm]
  refine ⟨by rw [h00, Real.sqrt_sq hH0.le], fun j => ?_, ?_⟩
  · rw [hv, mul_div_cancel_left₀ _ hH0.ne']
  · ext i j
    have e1 : ((H.submatrix Fin.succ Fin.succ)ᵀ * H.submatrix Fin.succ Fin.succ) i j =
        ∑ k : Fin n, H k.succ i.succ * H k.succ j.succ := by
      simp [mul_apply]
    rw [e1, Matrix.sub_apply, Matrix.smul_apply, submatrix_apply, vecMulVec_apply,
      hent i.succ j.succ, hv i, hv j, h00, smul_eq_mul]
    field_simp
    ring

/-- **(6.5.15).** "Since `A − zzᵀ` is positive definite, `a₁₁ − z₁² = g₁₁² − μ² > 0` and so from
(6.5.13) with `τ = μ/g₁₁` we see that `c = √α/√(α − μ²)`, `s = μ/√(α − μ²)`", and the rotation
zeroes `μ` (`−s g₁₁ + c μ = 0`) and produces the new last row `w₁ = −s g₁ + c w`. -/
theorem equation_6_5_15 {n : ℕ} {A H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : IsCholesky A H) {z : Fin (n + 1) → ℝ} (hA : (A - vecMulVec z z).PosDef) :
    hyperbolicPair (H 0 0) (z 0) =
        (√(A 0 0) / √(A 0 0 - z 0 ^ 2), z 0 / √(A 0 0 - z 0 ^ 2)) ∧
      -(z 0 / √(A 0 0 - z 0 ^ 2)) * H 0 0 + √(A 0 0) / √(A 0 0 - z 0 ^ 2) * z 0 = 0 ∧
      ∃ (R' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z' : Fin (n + 1) → ℝ),
        hyperbolicRotation (Sum.inl (0 : Fin (n + 1))) (Sum.inr ())
            (√(A 0 0) / √(A 0 0 - z 0 ^ 2)) (z 0 / √(A 0 0 - z 0 ^ 2)) *
          fromRows H (replicateRow Unit z) = fromRows R' (replicateRow Unit z') ∧
        z' 0 = 0 ∧ ∀ j : Fin n, z' j.succ =
          -(z 0 / √(A 0 0 - z 0 ^ 2)) * H 0 j.succ + √(A 0 0) / √(A 0 0 - z 0 ^ 2) * z j.succ := by
  obtain ⟨hlt, -, R', z', e, hz0, -, -, hw, -⟩ :=
    hyperbolicDowndate_step hH hA (c := √(A 0 0) / √(A 0 0 - z 0 ^ 2))
      (s := z 0 / √(A 0 0 - z 0 ^ 2)) rfl rfl
  obtain ⟨hg, -, -⟩ := equation_6_5_14 hH
  have hH0 := hH.diag_pos 0
  have hd : 0 < A 0 0 - z 0 ^ 2 := by linarith
  have hsq : √(A 0 0) ^ 2 = A 0 0 := Real.sq_sqrt (by nlinarith [sq_nonneg (z 0)])
  have hdd : √(A 0 0 - z 0 ^ 2) ^ 2 = A 0 0 - z 0 ^ 2 := Real.sq_sqrt hd.le
  have hd0 : 0 < √(A 0 0 - z 0 ^ 2) := Real.sqrt_pos.2 hd
  have hA0 : A 0 0 ≠ 0 := by nlinarith [sq_nonneg (z 0)]
  have hroot : √(1 - (z 0 / H 0 0) ^ 2) = √(A 0 0 - z 0 ^ 2) / √(A 0 0) := by
    rw [hg, show 1 - (z 0 / √(A 0 0)) ^ 2 = (√(A 0 0 - z 0 ^ 2) / √(A 0 0)) ^ 2 by
      rw [div_pow, div_pow, hsq, hdd, sub_div, div_self hA0], Real.sqrt_sq (by positivity)]
  refine ⟨?_, ?_, R', z', e, hz0, hw⟩
  · rw [hyperbolicPair, hroot, ← hg]
    have : H 0 0 ≠ 0 := hH0.ne'
    ext
    · simp only
      field_simp
    · simp only
      field_simp
  · rw [hg]
    field_simp
    ring

/-- **§6.5.4.** "The theorem provides the key step in an induction proof that the factorization
(6.5.12) exists": if `A = GGᵀ` and `A − zzᵀ` are positive definite, there are hyperbolic rotations
`H₁, …, H_n` (planes `(k, n+1)`) whose product `H = H₁ ⋯ H_n` is `S`-orthogonal with
`Hᵀ [Gᵀ; zᵀ] = [R; 0]`, `R` upper triangular — indeed `R` is the (upper) Cholesky factor of
`A − zzᵀ`. -/
theorem choleskyDowndate_exists {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hG : IsCholesky A Gᵀ)
    {z : Fin n → ℝ} (hA : (A - vecMulVec z z).PosDef) :
    ∃ c s : Fin n → ℝ, (∀ k, c k ^ 2 - s k ^ 2 = 1) ∧ ∃ R : Matrix (Fin n) (Fin n) ℝ,
      IsSOrthogonal
        (List.ofFn fun k => hyperbolicRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)).prod ∧
      (List.ofFn fun k => hyperbolicRotation (Sum.inl k) (Sum.inr ()) (c k) (s k)).prodᵀ *
        fromRows Gᵀ (replicateRow Unit z) = fromRows R 0 ∧
      R.IsUpperTriangular ∧ IsCholesky (A - vecMulVec z z) R := by
  obtain ⟨c, s, hcs, R, hJ, h, hR⟩ := exists_choleskyDowndate hG hA
  exact ⟨c, s, hcs, R, hJ, h, hR.isUpperTriangular, hR⟩

/-! ### §6.5.4 The downdating procedure -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **§6.5.4, a hyperbolic rotation applied to two rows.** "`[c −s; −s c]`" applied to the rows
`i`, `k` of `S` on the columns `cols`, in place:
`S(i, j) ← c S(i, j) − s S(k, j)`, `S(k, j) ← c S(k, j) − s S(i, j)`, every product and
difference rounded. The hyperbolic counterpart of chapter 5's Givens row update; its exact
semantics is left multiplication by `Matrix.hyperbolicRotation i k c s` on the columns `cols`
(`hyperbolicApplyLeft_spec`). -/
def hyperbolicApplyLeft {ι : Type} [DecidableEq ι] {n : ℕ} (i k : ι) (c s : ℝ)
    (cols : List (Fin n)) (S : Matrix ι (Fin n) ℝ) : M (Matrix ι (Fin n) ℝ) :=
  cols.foldlM (fun (S : Matrix ι (Fin n) ℝ) (j : Fin n) => do
    let x ← rnd ((← rnd (c * S i j)) - (← rnd (s * S k j)))
    let y ← rnd ((← rnd (c * S k j)) - (← rnd (s * S i j)))
    pure ((S.updateRow i (Function.update (S i) j x)).updateRow k
      (Function.update (S k) j y))) S

/-- **§6.5.4, Cholesky downdating with hyperbolic rotations.** "Given a Cholesky factorization
`A = GGᵀ` and a vector `z ∈ ℝⁿ` … compute the Cholesky factorization `Ã = G̃G̃ᵀ` where
`Ã = A − zzᵀ`", by the hyperbolic rotations `H_k` in the planes `(k, n + 1)` of the stacked
matrix `[Gᵀ; zᵀ]`, each computed by (6.5.13): `τ = x₂/x₁`, `c = 1/√(1 − τ²)`, `s = cτ` with
`x₁`, `x₂` the current entries `(k, k)` and `(n + 1, k)`; `G̃ = Rᵀ` for the triangular block `R`
of the result. `√` is `Real.sqrt` followed by one rounding. -/
noncomputable def choleskyDowndate {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) := do
  let S ← (List.finRange n).foldlM (fun (S : Matrix (Fin n ⊕ Unit) (Fin n) ℝ) (k : Fin n) => do
      let τ ← rnd (S (Sum.inr ()) k / S (Sum.inl k) k)
      let c ← rnd (1 / (← rnd (√(← rnd (1 - (← rnd (τ * τ)))))))
      let s ← rnd (c * τ)
      hyperbolicApplyLeft rnd (Sum.inl k) (Sum.inr ()) c s (List.finRange n) S)
    (fromRows Gᵀ (replicateRow Unit z))
  pure (S.toRows₁)ᵀ

end Programs

/-- The entries of a hyperbolic rotation times a matrix. -/
private theorem hyperbolicRotation_mul_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] {i k : ι}
    (hik : i ≠ k) (c s : ℝ) (S : Matrix ι κ ℝ) (p : ι) (q : κ) :
    (hyperbolicRotation i k c s * S) p q =
      if p = i then c * S i q - s * S k q else if p = k then c * S k q - s * S i q
      else S p q := by
  change (planeEmbed i k !![c, -s; -s, c] *ᵥ fun r => S r q) p = _
  rw [planeEmbed_mulVec_apply _ hik]
  split_ifs <;> simp <;> ring

/-- **Exact semantics of `hyperbolicApplyLeft`**: on the columns of a duplicate-free list `cols`
it is left multiplication by the hyperbolic rotation `[c −s; −s c]` in the rows `i`, `k`; the
other columns are unchanged. -/
theorem hyperbolicApplyLeft_spec {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} {i k : ι}
    (hik : i ≠ k) (c s : ℝ) {cols : List (Fin n)} (hcols : cols.Nodup) (S : Matrix ι (Fin n) ℝ) :
    Id.run (hyperbolicApplyLeft pure i k c s cols S) =
      of fun p j => if j ∈ cols then (hyperbolicRotation i k c s * S) p j else S p j := by
  induction cols generalizing S with
  | nil =>
    ext p j
    simp [hyperbolicApplyLeft]
  | cons j l ih =>
    obtain ⟨hjl, hl⟩ := List.nodup_cons.1 hcols
    set S' := (S.updateRow i (Function.update (S i) j (c * S i j - s * S k j))).updateRow k
      (Function.update (S k) j (c * S k j - s * S i j)) with hS'
    have hstep : Id.run (hyperbolicApplyLeft pure i k c s (j :: l) S) =
        Id.run (hyperbolicApplyLeft pure i k c s l S') := rfl
    have hS'e : ∀ p q, S' p q =
        if q = j then (hyperbolicRotation i k c s * S) p q else S p q := fun p q => by
      rw [hyperbolicRotation_mul_apply hik]
      simp only [hS', updateRow_apply, Function.update_apply]
      by_cases hq : q = j
      · subst hq
        by_cases hpk : p = k
        · subst hpk
          simp [Ne.symm hik]
        · by_cases hpi : p = i
          · subst hpi
            simp [hpk]
          · simp [hpk, hpi]
      · simp only [hq, ite_false]
        split_ifs <;> subst_vars <;> rfl
    have hcol : ∀ q, q ≠ j → ∀ p, (hyperbolicRotation i k c s * S') p q =
        (hyperbolicRotation i k c s * S) p q := fun q hq p => by
      rw [hyperbolicRotation_mul_apply hik, hyperbolicRotation_mul_apply hik, hS'e, hS'e, hS'e,
        ite_eq_right hq, ite_eq_right hq, ite_eq_right hq]
    rw [hstep, ih hl]
    ext p q
    simp only [of_apply, List.mem_cons]
    by_cases hq : q = j
    · subst hq
      rw [ite_eq_right hjl, ite_eq_left (Or.inl rfl), hS'e, ite_eq_left rfl]
    · by_cases hql : q ∈ l
      · rw [ite_eq_left hql, ite_eq_left (Or.inr hql), hcol q hq]
      · rw [ite_eq_right hql, ite_eq_right (by tauto), hS'e, ite_eq_right hq]

/-- The quadratic form of a signed Gram matrix: `xᵀ (Rᵀ R − z zᵀ) x = ‖R x‖² − (z ⬝ x)²`. (A copy
of a private lemma of `Numlib/Direct/Updating`.) -/
private theorem dotProduct_transpose_mul_self_sub_mulVec' {n : Type*} [Fintype n]
    (R : Matrix n n ℝ) (z x : n → ℝ) :
    x ⬝ᵥ ((Rᵀ * R - vecMulVec z z) *ᵥ x) = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) - (z ⬝ᵥ x) ^ 2 := by
  have h1 : x ⬝ᵥ ((Rᵀ * R) *ᵥ x) = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have h2 : x ⬝ᵥ (vecMulVec z z *ᵥ x) = (z ⬝ᵥ x) ^ 2 := by
    rw [dotProduct_mulVec, vecMul_vecMulVec, smul_dotProduct, smul_eq_mul, dotProduct_comm x z, sq]
  rw [sub_mulVec, dotProduct_sub, h1, h2]

/-- **The hyperbolic pair exists at every step of the downdate** (a copy of the private
`Matrix.sq_lt_sq_of_posDef_transpose_mul_self_sub` of `Numlib/Direct/Updating`): if `R` is upper
triangular with positive diagonal, `z` vanishes before `k` and `Rᵀ R − z zᵀ` is positive definite,
then `z_k² < r_kk²`; test the form on `R⁻¹ e_k`. -/
private theorem sq_lt_sq_of_posDef_transpose_mul_self_sub' {n : Type*} [Fintype n]
    [LinearOrder n] {R : Matrix n n ℝ} (hR : R.IsUpperTriangular) (hd : ∀ i, 0 < R i i)
    {z : n → ℝ} {k : n} (hz : ∀ j < k, z j = 0) (hP : (Rᵀ * R - vecMulVec z z).PosDef) :
    z k ^ 2 < R k k ^ 2 := by
  have hU : IsUnit R.det := (isUnit_iff_isUnit_det R).1
    ((isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular hR).2 fun i => (hd i).ne')
  have hT := hR.inv
  set x : n → ℝ := fun j => R⁻¹ j k with hx
  have hRx : R *ᵥ x = Pi.single k 1 := by
    ext i
    have := congrFun (congrFun (mul_nonsing_inv R hU) i) k
    rw [mul_apply] at this
    rw [Pi.single_apply, ← one_apply, ← this]
    rfl
  have hkk : R⁻¹ k k * R k k = 1 := by
    have := congrFun (congrFun (nonsing_inv_mul R hU) k) k
    rw [mul_apply, one_apply_eq, Finset.sum_eq_single k] at this
    · exact this
    · intro j _ hjk
      rcases lt_or_gt_of_ne hjk with h | h
      · rw [hT h, zero_mul]
      · rw [hR h, mul_zero]
    · simp
  have hzx : z ⬝ᵥ x = z k * R⁻¹ k k := by
    rw [dotProduct, Finset.sum_eq_single k]
    · intro j _ hjk
      rcases lt_or_gt_of_ne hjk with h | h
      · rw [hz j h, zero_mul]
      · rw [hx]
        dsimp only
        rw [hT h, mul_zero]
    · simp
  have hx0 : x ≠ 0 := fun h => by
    have := congrFun h k
    simp only [hx, Pi.zero_apply] at this
    rw [this, zero_mul] at hkk
    exact zero_ne_one hkk
  have hpos := hP.dotProduct_mulVec_pos hx0
  rw [star_trivial, dotProduct_transpose_mul_self_sub_mulVec', hRx, hzx] at hpos
  simp only [dotProduct_single, Pi.single_eq_same, mul_one] at hpos
  have hr := hd k
  have e : z k ^ 2 = (z k * R⁻¹ k k) ^ 2 * R k k ^ 2 := by
    rw [mul_pow, mul_assoc, ← mul_pow, hkk, one_pow, mul_one]
  rw [e]
  nlinarith [sq_nonneg (z k * R⁻¹ k k), pow_pos hr 2]

/-- One step of `choleskyDowndate` at `Id`: the hyperbolic rotation with the pair (6.5.13) of the
current entries `(k, k)`, `(n + 1, k)`, applied on the left. -/
private theorem choleskyDowndate_step_run {n : ℕ} (k : Fin n)
    (S : Matrix (Fin n ⊕ Unit) (Fin n) ℝ) :
    Id.run (do
      let τ ← pure (S (Sum.inr ()) k / S (Sum.inl k) k)
      let c ← pure (1 / (← pure (√(← pure (1 - (← pure (τ * τ)))))))
      let s ← pure (c * τ)
      hyperbolicApplyLeft (pure : ℝ → Id ℝ) (Sum.inl k) (Sum.inr ()) c s (List.finRange n) S) =
      hyperbolicRotation (Sum.inl k) (Sum.inr ())
        (hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k)).1
        (hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k)).2 * S := by
  have hp : hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k) =
      (1 / √(1 - S (Sum.inr ()) k / S (Sum.inl k) k * (S (Sum.inr ()) k / S (Sum.inl k) k)),
        1 / √(1 - S (Sum.inr ()) k / S (Sum.inl k) k * (S (Sum.inr ()) k / S (Sum.inl k) k)) *
          (S (Sum.inr ()) k / S (Sum.inl k) k)) := by
    rw [hyperbolicPair, sq]
  have hspec := hyperbolicApplyLeft_spec
    (Sum.inl_ne_inr : (Sum.inl k : Fin n ⊕ Unit) ≠ Sum.inr ())
    (1 / √(1 - S (Sum.inr ()) k / S (Sum.inl k) k * (S (Sum.inr ()) k / S (Sum.inl k) k)))
    (1 / √(1 - S (Sum.inr ()) k / S (Sum.inl k) k * (S (Sum.inr ()) k / S (Sum.inl k) k)) *
      (S (Sum.inr ()) k / S (Sum.inl k) k)) (List.nodup_finRange n) S
  simp only [List.mem_finRange, ite_true] at hspec
  rw [hp]
  exact hspec

/-- The downdating sweep at `Id` is a left fold of hyperbolic rotations. -/
private theorem choleskyDowndate_fold_run {n : ℕ} (l : List (Fin n))
    (S : Matrix (Fin n ⊕ Unit) (Fin n) ℝ) :
    Id.run (l.foldlM (fun (S : Matrix (Fin n ⊕ Unit) (Fin n) ℝ) (k : Fin n) => do
      let τ ← pure (S (Sum.inr ()) k / S (Sum.inl k) k)
      let c ← pure (1 / (← pure (√(← pure (1 - (← pure (τ * τ)))))))
      let s ← pure (c * τ)
      hyperbolicApplyLeft (pure : ℝ → Id ℝ) (Sum.inl k) (Sum.inr ()) c s (List.finRange n) S) S) =
      l.foldl (fun S k => hyperbolicRotation (Sum.inl k) (Sum.inr ())
        (hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k)).1
        (hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k)).2 * S) S := by
  induction l generalizing S with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldl_cons, ← choleskyDowndate_step_run, ← ih]
    rfl

/-- **§6.5.4, the downdate is correct in exact arithmetic**: if `A = GGᵀ` is a Cholesky
factorization (`Matrix.IsCholesky A Gᵀ`) and `Ã = A − zzᵀ` is positive definite, the output `G̃`
of `choleskyDowndate` is the Cholesky factor of `Ã`: `Matrix.IsCholesky (A − zzᵀ) G̃ᵀ`. At step
`k` the current `[R; z'ᵀ]` keeps `RᵀR − z'z'ᵀ = Ã` (the rotations are `S`-orthogonal), so
`|z'_k| < r_kk` and the hyperbolic pair (6.5.13) exists (Theorem 6.5.1's argument); the new
diagonal entry `√(r_kk² − z'_k²)` is positive, so no sign normalization is needed. -/
theorem choleskyDowndate_spec {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hG : IsCholesky A Gᵀ)
    {z : Fin n → ℝ} (hA : (A - vecMulVec z z).PosDef) :
    IsCholesky (A - vecMulVec z z) (Id.run (choleskyDowndate pure G z))ᵀ := by
  have hne : ∀ k : Fin n, (Sum.inl k : Fin n ⊕ Unit) ≠ Sum.inr () := fun _ => Sum.inl_ne_inr
  set F : Matrix (Fin n ⊕ Unit) (Fin n) ℝ → Fin n → Matrix (Fin n ⊕ Unit) (Fin n) ℝ :=
    fun S k => hyperbolicRotation (Sum.inl k) (Sum.inr ())
      (hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k)).1
      (hyperbolicPair (S (Sum.inl k) k) (S (Sum.inr ()) k)).2 * S with hF
  set Inv : ℕ → Matrix (Fin n ⊕ Unit) (Fin n) ℝ → Prop := fun t S =>
    ∃ (R : Matrix (Fin n) (Fin n) ℝ) (z' : Fin n → ℝ),
      S = fromRows R (replicateRow Unit z') ∧ R.IsUpperTriangular ∧ (∀ i, 0 < R i i) ∧
        (∀ j : Fin n, (j : ℕ) < t → z' j = 0) ∧ Rᵀ * R - vecMulVec z' z' = A - vecMulVec z z
    with hInv
  have hGG : Gᵀᵀ * Gᵀ = A := by
    rw [← conjTranspose_eq_transpose_of_trivial Gᵀ, hG.conjTranspose_mul_self]
  have hstep : ∀ t (ht : t < n) S, Inv t S → Inv (t + 1) (F S ⟨t, ht⟩) := by
    rintro t ht S ⟨R, z', rfl, hRt, hRd, hz', hGr⟩
    set k : Fin n := ⟨t, ht⟩ with hk
    have hlt : |z' k| < |R k k| := by
      rw [← sq_lt_sq]
      exact sq_lt_sq_of_posDef_transpose_mul_self_sub' hRt hRd (fun j hj => hz' j hj)
        (hGr ▸ hA)
    set x : Fin n ⊕ Unit → ℝ := fun r => fromRows R (replicateRow Unit z') r k with hx
    have hxi : x (Sum.inl k) = R k k := rfl
    have hxr : x (Sum.inr ()) = z' k := rfl
    have hxk : |x (Sum.inr ())| < |x (Sum.inl k)| := by rwa [hxi, hxr]
    obtain ⟨p, hp⟩ : ∃ p, p = hyperbolicPair (x (Sum.inl k)) (x (Sum.inr ())) := ⟨_, rfl⟩
    obtain ⟨hcs, -⟩ := hyperbolicPair_sq_sub_sq hxk
    obtain ⟨hzero, hdiag⟩ := hyperbolicRotation_hyperbolicPair_mulVec (hne k) hxk
    rw [← hp] at hcs hzero hdiag
    have hFS : F (fromRows R (replicateRow Unit z')) k =
        hyperbolicRotation (Sum.inl k) (Sum.inr ()) p.1 p.2 *
          fromRows R (replicateRow Unit z') := by
      rw [hF, hp]
    obtain ⟨R', z'', e, hR't, hz'', hR'i, -, -⟩ :=
      fromRows_rotate_step hRt (k := k) (fun j hj => hz' j hj) !![p.1, -p.2; -p.2, p.1]
    have e' : hyperbolicRotation (Sum.inl k) (Sum.inr ()) p.1 p.2 *
        fromRows R (replicateRow Unit z') = fromRows R' (replicateRow Unit z'') := e
    have hcol : ∀ i, fromRows R' (replicateRow Unit z'') i k =
        (hyperbolicRotation (Sum.inl k) (Sum.inr ()) p.1 p.2 *ᵥ x) i := fun i => by
      rw [← e']
      rfl
    refine ⟨R', z'', hFS.trans e', hR't, fun i => ?_, fun j hj => ?_, ?_⟩
    · by_cases hik : i = k
      · rw [hik]
        have h1 := hcol (Sum.inl k)
        rw [hdiag, fromRows_apply_inl, hxi, hxr, sign_pos (hRd k), SignType.coe_one,
          one_mul] at h1
        rw [h1]
        have h2 := hlt
        rw [abs_of_pos (hRd k)] at h2
        exact Real.sqrt_pos.2 (by nlinarith [abs_lt.1 h2])
      · rw [hR'i i hik]
        exact hRd i
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hz'' j hj
      · obtain rfl : j = k := Fin.ext hj
        have h1 := hcol (Sum.inr ())
        rw [hzero, fromRows_apply_inr] at h1
        simpa using h1
    · rw [← hGr]
      exact (transpose_mul_self_sub_eq_of_isJOrthogonal_of_fromRows
        (isJOrthogonal_hyperbolicRotation (hne k) (ε := Sum.elim (fun _ => 1) fun _ => -1)
          rfl rfl hcs)
        (by rw [hyperbolicRotation_transpose (hne k)]; exact e')).symm
  have hpre : ∀ t (ht : t ≤ n),
      Inv t (((List.finRange n).take t).foldl F (fromRows Gᵀ (replicateRow Unit z))) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨Gᵀ, z, rfl, hG.isUpperTriangular, hG.diag_pos,
        fun _ h => absurd h (Nat.not_lt_zero _), by rw [hGG]⟩
    | succ t ih =>
      intro ht
      have htake : (List.finRange n).take (t + 1) =
          (List.finRange n).take t ++ [⟨t, by omega⟩] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by rw [List.length_finRange]; omega)]
        simp
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact hstep t (by omega) _ (ih (by omega))
  have hrun : Id.run (choleskyDowndate pure G z) =
      ((List.finRange n).foldl F (fromRows Gᵀ (replicateRow Unit z))).toRows₁ᵀ := by
    change (Id.run ((List.finRange n).foldlM _ (fromRows Gᵀ (replicateRow Unit z)))).toRows₁ᵀ = _
    rw [choleskyDowndate_fold_run]
  obtain ⟨R, z', hS, hRt, hRd, hz', hGr⟩ := hpre n le_rfl
  rw [List.take_of_length_le (by simp)] at hS
  have hz0 : z' = 0 := funext fun j => hz' j j.isLt
  subst hz0
  rw [vecMulVec_zero, sub_zero] at hGr
  rw [hrun, hS, toRows₁_fromRows, transpose_transpose]
  exact ⟨hRt, hRd, by rw [conjTranspose_eq_transpose_of_trivial, hGr]⟩

/-! ### §6.5.1–6.5.4 The Givens updating procedures -/

section GivensPrograms

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **A top-down Givens sweep of an upper Hessenberg matrix** (§6.5.1, "Following Algorithm
5.2.4, we compute Givens rotations `G_k`, `k = 1 : n − 1` such that `G_{n−1}ᵀ ⋯ G₁ᵀ H₁ = R₁` is
upper triangular"; §6.5.2 and §6.5.3 use it from a column `a`): for `j = a, …, a + count − 1`,
`[c, s] = givens(H(j, j), H(j + 1, j))` (Algorithm 5.1.3), the rows `j`, `j + 1` of `H` are
rotated and the rotation is accumulated into the columns `j`, `j + 1` of `Q`. Steps past the last
row or column are skipped. -/
noncomputable def givensHessenbergSweep {m n : ℕ} (a count : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ)
    (H : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :=
  (List.range' a count).foldlM
    (fun (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) (j : ℕ) =>
      if h : j + 1 < m ∧ j < n then do
        let cs ← Chapter05.algorithm_5_1_3 rnd (st.2 ⟨j, by omega⟩ ⟨j, h.2⟩)
          (st.2 ⟨j + 1, h.1⟩ ⟨j, h.2⟩)
        let H ← Chapter05.givensApplyLeft rnd ⟨j, by omega⟩ ⟨j + 1, h.1⟩ cs.1 cs.2
          (List.finRange n) st.2
        let Q ← Chapter05.givensApplyRight rnd ⟨j, by omega⟩ ⟨j + 1, h.1⟩ cs.1 cs.2
          (List.finRange m) st.1
        pure (Q, H)
      else pure st) (Q, H)

/-- **A bottom-up Givens sweep driven by a vector** (§6.5.1, "Suppose rotations
`J_{n−1}, …, J₂, J₁` are computed such that `J₁ᵀ ⋯ J_{n−1}ᵀ w = ±‖w‖₂ e₁` … If these same rotations
are applied to `R`"; §6.5.3, "compute Givens rotations `G₁, …, G_{m−1}` such that
`G₁ᵀ ⋯ G_{m−1}ᵀ q = αe₁`"): for `j = b + count − 1, …, b`, `[c, s] = givens(w(j), w(j + 1))`, the
entries `j`, `j + 1` of `w` and the rows `j`, `j + 1` of `R` are rotated, and the rotation is
accumulated into the columns `j`, `j + 1` of `Q`. -/
noncomputable def givensVectorSweep {m n : ℕ} (b count : ℕ) (w : Fin m → ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin m) (Fin n) ℝ) :
    M ((Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :=
  (List.range' b count).reverse.foldlM
    (fun (st : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) (j : ℕ) =>
      if h : j + 1 < m then do
        let cs ← Chapter05.algorithm_5_1_3 rnd (st.1 ⟨j, by omega⟩) (st.1 ⟨j + 1, h⟩)
        let w ← Chapter05.givensRotateVec rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2 st.1
        let R ← Chapter05.givensApplyLeft rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2
          (List.finRange n) st.2.2
        let Q ← Chapter05.givensApplyRight rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2
          (List.finRange m) st.2.1
        pure (w, Q, R)
      else pure st) (w, Q, R)

/-- **§6.5.1, the rank-one QR update.** "Suppose we have the QR factorization `QR = A ∈ ℝⁿˣⁿ` and
that we need to compute the QR factorization `Ã = A + uvᵀ = Q₁R₁`": `w = Qᵀu` (a gaxpy,
Algorithm 1.1.3); the rotations `J_{n−1}, …, J₁` reducing `w` to `±‖w‖₂e₁`, applied to `R` and
accumulated into `Q` (`givensVectorSweep`), which leave `H` upper Hessenberg; `H₁ = H ± ‖w‖₂e₁vᵀ`
(a saxpy on the first row, Algorithm 1.1.2); the rotations `G₁, …, G_{n−1}` triangularizing `H₁`
(`givensHessenbergSweep`). Returns `(Q₁, R₁)`, `Q₁ = QJ_{n−1}⋯J₁G₁⋯G_{n−1}`. -/
noncomputable def qrUpdateRankOne {n : ℕ} (Q R : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let w ← Chapter01.algorithm_1_1_3 rnd Qᵀ u 0
  let st ← givensVectorSweep rnd 0 (n - 1) w Q R
  let H ← if h : 0 < n then do
      let r ← Chapter01.algorithm_1_1_2 rnd (st.1 ⟨0, h⟩) v (st.2.2 ⟨0, h⟩)
      pure (st.2.2.updateRow ⟨0, h⟩ r)
    else pure st.2.2
  givensHessenbergSweep rnd 0 (n - 1) st.2.1 H

/-- **§6.5.2, deleting a column.** "`Qᵀ Ã = H` is upper Hessenberg … the unwanted subdiagonal
elements `h_{k+1,k}, …, h_{n,n−1}` can be zeroed by a sequence of Givens rotations:
`G_{n−1}ᵀ ⋯ G_kᵀ H = R₁` … if `Q₁ = QG_k ⋯ G_{n−1}` then `Ã = Q₁R₁` is the QR factorization of `Ã`."
For `A ∈ ℝ^{m×(n+1)}` with its column `k` (0-based) deleted, `H` is `R` with its column `k`
deleted (no flops). -/
noncomputable def qrDeleteColumn {m n : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin (n + 1)) ℝ) (k : Fin (n + 1)) :
    M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :=
  givensHessenbergSweep rnd k (n - k) Q (R.submatrix id k.succAbove)

/-- **§6.5.2, appending a column.** "if `w = Qᵀz` then `QᵀÃ = [Qᵀa₁| ⋯ |Qᵀa_k|w|Qᵀa_{k+1}| ⋯ ]` is
upper triangular except for the presence of a 'spike' … It is possible to determine a sequence of
Givens rotations that restores the triangular form": `w = Qᵀz` (Algorithm 1.1.3), `H` is `R` with
`w` inserted as its column `k` (0-based), then for `j = m − 2, …, k`,
`[c, s] = givens(H(j, k), H(j + 1, k))` zeroes `H(j + 1, k)` (the book's `J_{m−1}, …, J_{k+1}`), the
rows `j`, `j + 1` of `H` are rotated and the rotation is accumulated into `Q`. -/
noncomputable def qrInsertColumn {m n : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ) (z : Fin m → ℝ) (k : Fin (n + 1)) :
    M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin (n + 1)) ℝ) := do
  let w ← Chapter01.algorithm_1_1_3 rnd Qᵀ z 0
  (List.range' k (m - 1 - k)).reverse.foldlM
    (fun (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin (n + 1)) ℝ) (j : ℕ) =>
      if h : j + 1 < m then do
        let cs ← Chapter05.algorithm_5_1_3 rnd (st.2 ⟨j, by omega⟩ k) (st.2 ⟨j + 1, h⟩ k)
        let H ← Chapter05.givensApplyLeft rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2
          (List.finRange (n + 1)) st.2
        let Q ← Chapter05.givensApplyRight rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2
          (List.finRange m) st.1
        pure (Q, H)
      else pure st) (Q, of fun i => k.insertNth (w i) (R i))

/-- **§6.5.3, inserting a row.** "`diag(1, Qᵀ)Ã = [wᵀ; R] = H` is upper Hessenberg. Thus, rotations
`J₁, …, J_n` can be determined so `J_nᵀ ⋯ J₁ᵀH = R₁` is upper triangular. It follows that
`Ã = Q₁R₁` … where `Q₁ = diag(1, Q)J₁ ⋯ J_n`. See Algorithm 5.2.5. No essential complications
result if the new row is added between rows `k` and `k + 1` of `A`", through the permutation `P`:
the new row `wᵀ` becomes row `k` (0-based), and the starting orthogonal factor is
`Pᵀ diag(1, Q)`, the rows of `diag(1, Q)` permuted by `Fin.cycleRange k` (no flops). -/
noncomputable def qrInsertRow {m n : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ) (w : Fin n → ℝ) (k : Fin (m + 1)) :
    M (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ × Matrix (Fin (m + 1)) (Fin n) ℝ) :=
  givensHessenbergSweep rnd 0 n ((consDiag 1 Q).submatrix k.cycleRange id) (of (Fin.cons w R))

/-- **§6.5.3, deleting the first row.** "Let `qᵀ` be the first row of `Q` and compute Givens
rotations `G₁, …, G_{m−1}` such that `G₁ᵀ ⋯ G_{m−1}ᵀq = αe₁` where `α = ±1`. Note that
`H = G₁ᵀ ⋯ G_{m−1}ᵀR = [vᵀ; R₁]` is upper Hessenberg and that `QG_{m−1} ⋯ G₁ = [α 0; 0 Q₁]`":
the bottom-up sweep driven by `q` (`givensVectorSweep`), then `(Q₁, R₁)` are read off. -/
noncomputable def qrDeleteFirstRow {m n : ℕ} (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (R : Matrix (Fin (m + 1)) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) := do
  let st ← givensVectorSweep rnd 0 m (Q 0) Q R
  pure (st.2.1.submatrix Fin.succ Fin.succ, st.2.2.submatrix Fin.succ id)

/-- **§6.5.4, Cholesky updating.** "`Ã = [Gᵀ; zᵀ]ᵀ [Gᵀ; zᵀ]`, we can solve this problem by computing
a product of Givens rotations `Q = Q₁ ⋯ Q_n` so that `Qᵀ [Gᵀ; zᵀ] = [R; 0]` … The `Q_k` update
involves only rows `k` and `n + 1`": the stacked matrix `[Gᵀ; zᵀ]` on `Fin (n + 1)` rows, for
`k = 0, …, n − 1` the pair `[c, s] = givens(M(k, k), M(n, k))` (Algorithm 5.1.3) and the rotation of
the rows `k` and `n` (`givensApplyLeft`); returns `G̃ = (M(0:n−1, :))ᵀ`. -/
noncomputable def choleskyUpdate {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) := do
  let S ← (List.finRange n).foldlM (fun (S : Matrix (Fin (n + 1)) (Fin n) ℝ) (k : Fin n) => do
      let cs ← Chapter05.algorithm_5_1_3 rnd (S k.castSucc k) (S (Fin.last n) k)
      Chapter05.givensApplyLeft rnd k.castSucc (Fin.last n) cs.1 cs.2 (List.finRange n) S)
    (of fun i => Fin.lastCases (motive := fun _ => Fin n → ℝ) z (fun i => Gᵀ i) i)
  pure (S.submatrix Fin.castSucc id)ᵀ

end GivensPrograms

/-! #### Exact semantics of the Givens sweeps -/

/-- One exact Givens step on a pair `(Q, H)`: `H ← G(p, q, θ)ᵀ H`, `Q ← Q G(p, q, θ)`. -/
private noncomputable def givensPairStep {m n : ℕ} (p q : Fin m) (cs : ℝ × ℝ)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ :=
  (st.1 * Chapter05.givensRotation p q cs.1 cs.2, (Chapter05.givensRotation p q cs.1 cs.2)ᵀ * st.2)

private theorem givensPairStep_mem {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) {cs : ℝ × ℝ}
    (hcs : cs.1 ^ 2 + cs.2 ^ 2 = 1) {st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ}
    (hQ : st.1 ∈ orthogonalGroup (Fin m) ℝ) :
    (givensPairStep p q cs st).1 ∈ orthogonalGroup (Fin m) ℝ :=
  mul_mem hQ (Chapter05.givensRotation_mem_orthogonalGroup hpq hcs)

private theorem givensPairStep_mul {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) {cs : ℝ × ℝ}
    (hcs : cs.1 ^ 2 + cs.2 ^ 2 = 1) (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :
    (givensPairStep p q cs st).1 * (givensPairStep p q cs st).2 = st.1 * st.2 := by
  have hG := (mem_orthogonalGroup_iff _ ℝ).1
    (Chapter05.givensRotation_mem_orthogonalGroup hpq hcs)
  simp only [givensPairStep]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Chapter05.givensRotation p q cs.1 cs.2), hG,
    Matrix.one_mul]

private theorem givensPairStep_apply {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) (cs : ℝ × ℝ)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (l : Fin n) :
    (givensPairStep p q cs st).2 r l =
      if r = p then cs.1 * st.2 p l - cs.2 * st.2 q l
      else if r = q then cs.2 * st.2 p l + cs.1 * st.2 q l else st.2 r l :=
  Chapter05.givensRotation_transpose_mul_apply hpq cs.1 cs.2 st.2 r l

/-- The step kills the entry the Givens pair was computed from. -/
private theorem givensPairStep_zero {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) (l : Fin n)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :
    (givensPairStep p q (Id.run (Chapter05.algorithm_5_1_3 pure (st.2 p l) (st.2 q l))) st).2 q l
      = 0 := by
  rw [givensPairStep_apply hpq, ite_eq_right hpq.symm, ite_eq_left rfl]
  exact (Chapter05.algorithm_5_1_3_spec _ _).2.1

/-- A step leaves an entry zero if, in its column, both rotated rows were zero (when the entry
is in one of them), or the entry itself was zero (otherwise). -/
private theorem givensPairStep_eq_zero {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) (cs : ℝ × ℝ)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) {r : Fin m} {l : Fin n}
    (hin : r = p ∨ r = q → st.2 p l = 0 ∧ st.2 q l = 0)
    (hr : r ≠ p → r ≠ q → st.2 r l = 0) :
    (givensPairStep p q cs st).2 r l = 0 := by
  rw [givensPairStep_apply hpq]
  split_ifs with h1 h2
  · obtain ⟨hp, hq⟩ := hin (Or.inl h1)
    rw [hp, hq]; ring
  · obtain ⟨hp, hq⟩ := hin (Or.inr h2)
    rw [hp, hq]; ring
  · exact hr h1 h2

/-- The row index of an entry in one of the rotated rows. -/
private theorem val_eq_or_of_eq_or {m : ℕ} {p q r : Fin m} (h : r = p ∨ r = q) :
    (r : ℕ) = p ∨ (r : ℕ) = q := h.imp (congrArg _) (congrArg _)

/-- The exact step of `givensHessenbergSweep`. -/
private noncomputable def hessStep {m n : ℕ}
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) (j : ℕ) :
    Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ :=
  if h : j + 1 < m ∧ j < n then
    givensPairStep ⟨j, by omega⟩ ⟨j + 1, h.1⟩
      (Id.run (Chapter05.algorithm_5_1_3 pure (st.2 ⟨j, by omega⟩ ⟨j, h.2⟩)
        (st.2 ⟨j + 1, h.1⟩ ⟨j, h.2⟩))) st
  else st

private theorem idRun_givensHessenbergSweep {m n : ℕ} (a count : ℕ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensHessenbergSweep pure a count Q H) =
      (List.range' a count).foldl hessStep (Q, H) := by
  rw [givensHessenbergSweep, List.idRun_foldlM]
  congr 1
  funext st j
  unfold hessStep
  split_ifs with h
  · have hpq : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h.1⟩ := fun e => by simp [Fin.ext_iff] at e
    simp only [Id.run_bind, Id.run_pure]
    rw [Chapter05.givensApplyLeft_spec_of_forall_mem hpq _ _ (List.nodup_finRange n)
      (List.mem_finRange), Chapter05.givensApplyRight_spec_of_forall_mem hpq _ _
      (List.nodup_finRange m) (List.mem_finRange)]
    rfl
  · rfl

/-- **Exact semantics of `givensHessenbergSweep`**: if `Q` is orthogonal with `QH = A`, `H` is upper
Hessenberg and already triangular in its columns before `a`, and the sweep reaches the last column
or the last row (`n ≤ a + count` or `m ≤ a + count + 1`), the output `(Q', H')` is a QR
factorization of `A` (each rotation zeroes the subdiagonal entry of its column and keeps the
earlier columns). -/
theorem givensHessenbergSweep_spec {m n : ℕ} {a count : ℕ} {A H : Matrix (Fin m) (Fin n) ℝ}
    {Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q ∈ orthogonalGroup (Fin m) ℝ) (hQH : Q * H = A)
    (hH : ∀ (i : Fin m) (j : Fin n), (j : ℕ) + 1 < i → H i j = 0)
    (ha : ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → (j : ℕ) < a → H i j = 0)
    (hc : n ≤ a + count ∨ m ≤ a + count + 1) :
    IsQR A (Id.run (givensHessenbergSweep pure a count Q H)).1
      (Id.run (givensHessenbergSweep pure a count Q H)).2 := by
  set Inv : ℕ → Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ → Prop := fun t st =>
    st.1 ∈ orthogonalGroup (Fin m) ℝ ∧ st.1 * st.2 = A ∧
      (∀ (i : Fin m) (j : Fin n), (j : ℕ) + 1 < i → st.2 i j = 0) ∧
      ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → (j : ℕ) < a + t → st.2 i j = 0 with hInv
  have hstep : ∀ t st, Inv t st → Inv (t + 1) (hessStep st (a + t)) := by
    rintro t st ⟨hQ, hQH, hH, hlow⟩
    unfold hessStep
    split_ifs with h
    · set p : Fin m := ⟨a + t, by omega⟩ with hp
      set q : Fin m := ⟨a + t + 1, h.1⟩ with hq
      set jc : Fin n := ⟨a + t, h.2⟩ with hjc
      have hpv : (p : ℕ) = a + t := rfl
      have hqv : (q : ℕ) = a + t + 1 := rfl
      have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
      have hcs := (Chapter05.algorithm_5_1_3_spec (st.2 p jc) (st.2 q jc)).1
      refine ⟨givensPairStep_mem hpq hcs hQ, by rw [givensPairStep_mul hpq hcs, hQH],
        fun i l hil => ?_, fun i l hil hl => ?_⟩
      · refine givensPairStep_eq_zero hpq _ st (fun hi => ?_) fun _ _ => hH i l hil
        have hiv := val_eq_or_of_eq_or hi
        refine ⟨?_, hH q l (by omega)⟩
        by_cases hl2 : (l : ℕ) + 1 < a + t
        · exact hH p l (by omega)
        · exact hlow p l (by omega) (by omega)
      · by_cases hlj : (l : ℕ) < a + t
        · refine givensPairStep_eq_zero hpq _ st (fun hi => ⟨hlow p l (by omega) hlj,
            hH q l (by omega)⟩) fun _ _ => hlow i l hil hlj
        · have hl' : l = jc := Fin.ext (by simp [hjc]; omega)
          by_cases hi : i = q
          · rw [hi, hl']
            exact givensPairStep_zero hpq jc st
          · have hip : i ≠ p := by
              intro e
              rw [e] at hil
              omega
            rw [givensPairStep_apply hpq, ite_eq_right hip, ite_eq_right hi]
            exact hH i l (by
              have : (i : ℕ) ≠ a + t + 1 := fun e => hi (Fin.ext (by rw [hqv, e]))
              omega)
    · refine ⟨hQ, hQH, hH, fun i l hil hl => ?_⟩
      by_cases hlj : (l : ℕ) < a + t
      · exact hlow i l hil hlj
      · exfalso
        have := i.isLt
        have := l.isLt
        omega
  have hall : ∀ t, Inv t ((List.range' a t).foldl hessStep (Q, H)) := by
    intro t
    induction t with
    | zero => exact ⟨hQ, hQH, hH, fun i j hij hj => ha i j hij (by simpa using hj)⟩
    | succ t ih =>
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, one_mul]
      exact hstep t _ ih
  obtain ⟨hQ', hQH', -, hlow'⟩ := hall count
  rw [idRun_givensHessenbergSweep]
  refine ⟨hQ', fun i j hij => hlow' i j hij ?_, hQH'⟩
  have := i.isLt
  have := j.isLt
  omega

/-- Rotating a vector with the exact Givens update is multiplication by `G(p, q, θ)ᵀ`. -/
private theorem idRun_givensRotateVec {m : ℕ} {p q : Fin m} (hpq : p ≠ q) (c s : ℝ)
    (w : Fin m → ℝ) :
    Id.run (Chapter05.givensRotateVec pure p q c s w) =
      (Chapter05.givensRotation p q c s)ᵀ *ᵥ w := by
  funext r
  rw [Chapter05.givensRotation_transpose_mulVec_apply hpq]
  simp only [Chapter05.givensRotateVec, Id.run_bind, Id.run_pure, Function.update_apply]
  by_cases hrq : r = q
  · subst hrq
    simp [hpq.symm]
  · by_cases hrp : r = p
    · subst hrp
      simp [hrq]
    · simp [hrp, hrq]

/-- The exact step of `givensVectorSweep`. -/
private noncomputable def vecStep {m n : ℕ}
    (st : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) (j : ℕ) :
    (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ :=
  if h : j + 1 < m then
    let cs := Id.run (Chapter05.algorithm_5_1_3 pure (st.1 ⟨j, by omega⟩) (st.1 ⟨j + 1, h⟩))
    ((Chapter05.givensRotation ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2)ᵀ *ᵥ st.1,
      givensPairStep ⟨j, by omega⟩ ⟨j + 1, h⟩ cs (st.2.1, st.2.2))
  else st

private theorem idRun_givensVectorSweep {m n : ℕ} (b count : ℕ) (w : Fin m → ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (givensVectorSweep pure b count w Q R) =
      (List.range' b count).reverse.foldl vecStep (w, Q, R) := by
  rw [givensVectorSweep, List.idRun_foldlM]
  congr 1
  funext st j
  unfold vecStep
  split_ifs with h
  · have hpq : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h⟩ := fun e => by simp [Fin.ext_iff] at e
    simp only [Id.run_bind, Id.run_pure]
    rw [idRun_givensRotateVec hpq, Chapter05.givensApplyLeft_spec_of_forall_mem hpq _ _
      (List.nodup_finRange n) (List.mem_finRange), Chapter05.givensApplyRight_spec_of_forall_mem hpq
      _ _ (List.nodup_finRange m) (List.mem_finRange)]
    rfl
  · rfl

/-- **Exact semantics of `givensVectorSweep`**: for `R` upper trapezoidal and `w` vanishing below
`b + count`, the sweep multiplies `w` and `R` on the left, and `Q` on the right, by one orthogonal
`P` (resp. `Pᵀ`); afterwards `w` vanishes below `b`, and `R` is upper Hessenberg and still
triangular in its columns before `b`. -/
theorem givensVectorSweep_spec {m n : ℕ} (b count : ℕ) (w : Fin m → ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin m) (Fin n) ℝ)
    (hR : ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → R i j = 0)
    (hw : ∀ i : Fin m, b + count < i → w i = 0) :
    (∃ P ∈ orthogonalGroup (Fin m) ℝ,
      (Id.run (givensVectorSweep pure b count w Q R)).1 = P *ᵥ w ∧
      (Id.run (givensVectorSweep pure b count w Q R)).2.1 = Q * Pᵀ ∧
      (Id.run (givensVectorSweep pure b count w Q R)).2.2 = P * R) ∧
    (∀ i : Fin m, b < i → (Id.run (givensVectorSweep pure b count w Q R)).1 i = 0) ∧
    (∀ (i : Fin m) (j : Fin n), (j : ℕ) + 1 < i →
      (Id.run (givensVectorSweep pure b count w Q R)).2.2 i j = 0) ∧
    ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → (j : ℕ) < b →
      (Id.run (givensVectorSweep pure b count w Q R)).2.2 i j = 0 := by
  set V : ℕ → (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ → Prop :=
    fun K st => (∃ P ∈ orthogonalGroup (Fin m) ℝ, st.1 = P *ᵥ w ∧ st.2.1 = Q * Pᵀ ∧
      st.2.2 = P * R) ∧ (∀ i : Fin m, K < i → st.1 i = 0) ∧
      (∀ (i : Fin m) (j : Fin n), (j : ℕ) + 1 < i → st.2.2 i j = 0) ∧
      ∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → (j : ℕ) < K → st.2.2 i j = 0 with hV
  have hstep : ∀ j st, V (j + 1) st → V j (vecStep st j) := by
    rintro j ⟨x, Q', R'⟩ ⟨⟨P, hP, hx, hQ', hR'⟩, hxz, hH, hlow⟩
    dsimp only at hx hQ' hR' hxz hH hlow
    unfold vecStep
    split_ifs with h
    · set p : Fin m := ⟨j, by omega⟩ with hp
      set q : Fin m := ⟨j + 1, h⟩ with hq
      have hpv : (p : ℕ) = j := rfl
      have hqv : (q : ℕ) = j + 1 := rfl
      have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
      obtain ⟨hcs, hz, -⟩ := Chapter05.algorithm_5_1_3_spec (x p) (x q)
      set cs := Id.run (Chapter05.algorithm_5_1_3 pure (x p) (x q)) with hcsdef
      set G := Chapter05.givensRotation p q cs.1 cs.2 with hG
      have hGo : G ∈ orthogonalGroup (Fin m) ℝ :=
        Chapter05.givensRotation_mem_orthogonalGroup hpq hcs
      have hGto : Gᵀ ∈ orthogonalGroup (Fin m) ℝ := by
        rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
        exact Unitary.star_mem hGo
      have happ := givensPairStep_apply hpq cs (Q', R')
      dsimp only at happ
      refine ⟨⟨Gᵀ * P, mul_mem hGto hP, ?_, ?_, ?_⟩, fun i hi => ?_, fun i l hil => ?_,
        fun i l hil hl => ?_⟩
      · dsimp only
        rw [hx, mulVec_mulVec]
      · change Q' * G = Q * (Gᵀ * P)ᵀ
        rw [hQ', transpose_mul, transpose_transpose, Matrix.mul_assoc]
      · change Gᵀ * R' = Gᵀ * P * R
        rw [hR', Matrix.mul_assoc]
      · dsimp only
        rw [Chapter05.givensRotation_transpose_mulVec_apply hpq]
        by_cases hiq : i = q
        · rw [ite_eq_right (by rw [hiq]; exact hpq.symm), ite_eq_left hiq]
          exact hz
        · have hip : i ≠ p := fun e => by rw [e] at hi; omega
          rw [ite_eq_right hip, ite_eq_right hiq]
          exact hxz i (by
            have : (i : ℕ) ≠ j + 1 := fun e => hiq (Fin.ext (by rw [hqv, e]))
            omega)
      · change (givensPairStep p q cs (Q', R')).2 i l = 0
        refine givensPairStep_eq_zero hpq cs _ (fun hi => ?_) fun _ _ => hH i l hil
        have hiv := val_eq_or_of_eq_or hi
        refine ⟨?_, hH q l (by omega)⟩
        by_cases hl2 : (l : ℕ) + 1 < j
        · exact hH p l (by omega)
        · exact hlow p l (by omega) (by omega)
      · change (givensPairStep p q cs (Q', R')).2 i l = 0
        exact givensPairStep_eq_zero hpq cs _ (fun _ => ⟨hlow p l (by omega) (by omega),
          hH q l (by omega)⟩) fun _ _ => hlow i l hil (by omega)
    · refine ⟨⟨P, hP, hx, hQ', hR'⟩, fun i hi => ?_, hH, fun i l hil hl => hlow i l hil (by omega)⟩
      exfalso
      have := i.isLt
      omega
  have hall : ∀ t st, V (b + t) st → V b ((List.range' b t).reverse.foldl vecStep st) := by
    intro t
    induction t with
    | zero => intro st h; simpa using h
    | succ t ih =>
      intro st h
      rw [List.range'_concat, List.reverse_append, one_mul]
      simp only [List.reverse_singleton, List.singleton_append, List.foldl_cons]
      exact ih _ (hstep (b + t) st h)
  have h0 : V (b + count) (w, Q, R) :=
    ⟨⟨1, one_mem _, by simp, by simp, by simp⟩, hw, fun i j hij => hR i j (by omega),
      fun i j hij _ => hR i j hij⟩
  rw [idRun_givensVectorSweep]
  exact hall count _ h0

/-! #### Correctness of the procedures -/

/-- **§6.5.1, the rank-one update is correct in exact arithmetic**: if `A = QR` (`Matrix.IsQR`),
the output `(Q₁, R₁)` of `qrUpdateRankOne` is a QR factorization of `A + uvᵀ`. The first sweep
keeps `Q R = A` and leaves `H` upper Hessenberg with `w` reduced to its first entry (`(6.5.2)`),
so `Q H₁ = A + uvᵀ` with `H₁` still upper Hessenberg (`(6.5.3)`); the second sweep
triangularizes it. -/
theorem qrUpdateRankOne_spec {n : ℕ} {A Q R : Matrix (Fin n) (Fin n) ℝ} (h : IsQR A Q R)
    (u v : Fin n → ℝ) :
    IsQR (A + vecMulVec u v) (Id.run (qrUpdateRankOne pure Q R u v)).1
      (Id.run (qrUpdateRankOne pure Q R u v)).2 := by
  have hQ : Q ∈ orthogonalGroup (Fin n) ℝ := h.mem_unitaryGroup
  have hQQ : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hQ
  have hw1 : Id.run (Chapter01.algorithm_1_1_3 pure Qᵀ u 0) = Qᵀ *ᵥ u := by
    rw [Chapter01.algorithm_1_1_3_spec, zero_add]
  obtain ⟨⟨P, hP, h1, h2, h3⟩, hwz, hHess, -⟩ :=
    givensVectorSweep_spec 0 (n - 1) (Qᵀ *ᵥ u) Q R h.apply_eq_zero (fun i hi => by omega)
  set st := Id.run (givensVectorSweep pure 0 (n - 1) (Qᵀ *ᵥ u) Q R) with hst
  set H : Matrix (Fin n) (Fin n) ℝ := Id.run (if h : 0 < n then do
      let r ← Chapter01.algorithm_1_1_2 pure (st.1 ⟨0, h⟩) v (st.2.2 ⟨0, h⟩)
      pure (st.2.2.updateRow ⟨0, h⟩ r)
    else pure st.2.2) with hHdef
  have hrun : Id.run (qrUpdateRankOne pure Q R u v) =
      Id.run (givensHessenbergSweep pure 0 (n - 1) st.2.1 H) := by
    simp only [qrUpdateRankOne, Id.run_bind, hw1]
    rw [hHdef]
    split_ifs <;> rfl
  have hHe : H = st.2.2 + vecMulVec st.1 v := by
    rw [hHdef]
    split_ifs with hn
    · ext i j
      simp only [Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_2_spec]
      by_cases hi : i = ⟨0, hn⟩
      · subst hi
        simp [vecMulVec_apply, mul_comm]
      · rw [updateRow_ne hi, Matrix.add_apply, vecMulVec_apply,
          hwz i (by have : (i : ℕ) ≠ 0 := fun e => hi (Fin.ext e); omega), zero_mul, add_zero]
    · ext i
      exact absurd i.isLt (by omega)
  have hPP : Pᵀ * P = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hP
  have hPt : Pᵀ ∈ orthogonalGroup (Fin n) ℝ := by
    rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
    exact Unitary.star_mem hP
  have e1 : Q * Pᵀ * (P * R) = A := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᵀ, hPP, Matrix.one_mul, h.mul_eq]
  have e2 : (Q * Pᵀ) *ᵥ (P *ᵥ (Qᵀ *ᵥ u)) = u := by
    rw [mulVec_mulVec, mulVec_mulVec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᵀ P, hPP, Matrix.one_mul, hQQ, one_mulVec]
  have hprod : st.2.1 * H = A + vecMulVec u v := by
    rw [hHe, h1, h2, h3, Matrix.mul_add, mul_vecMulVec, e1, e2]
  have hHH : ∀ (i j : Fin n), (j : ℕ) + 1 < i → H i j = 0 := fun i j hij => by
    rw [hHe, Matrix.add_apply, hHess i j hij, vecMulVec_apply, hwz i (by omega), zero_mul,
      add_zero]
  rw [hrun]
  exact givensHessenbergSweep_spec (by rw [h2]; exact mul_mem hQ hPt) hprod hHH
    (fun i j _ hj => absurd hj (Nat.not_lt_zero _)) (Or.inr (by omega))

/-- **§6.5.2, deleting a column is correct in exact arithmetic**: if `A = QR` then the output of
`qrDeleteColumn` is a QR factorization of `A` with its column `k` deleted. `QᵀÃ = H` is upper
Hessenberg and triangular before column `k` (`Matrix.IsQR.conjTranspose_mul_deleteColumn`), and the
sweep from column `k` triangularizes it. -/
theorem qrDeleteColumn_spec {m n : ℕ} {A : Matrix (Fin m) (Fin (n + 1)) ℝ}
    {Q : Matrix (Fin m) (Fin m) ℝ} {R : Matrix (Fin m) (Fin (n + 1)) ℝ} (h : IsQR A Q R)
    (k : Fin (n + 1)) :
    IsQR (A.submatrix id k.succAbove) (Id.run (qrDeleteColumn pure Q R k)).1
      (Id.run (qrDeleteColumn pure Q R k)).2 := by
  obtain ⟨h1, h2, h3⟩ := h.conjTranspose_mul_deleteColumn k
  have hQ : Q ∈ orthogonalGroup (Fin m) ℝ := h.mem_unitaryGroup
  have hk := k.isLt
  refine givensHessenbergSweep_spec hQ ?_ (fun i j hij => h2 i j hij)
    (fun i j hij hjk => h3 i j hij hjk) (Or.inl (by omega))
  rw [← h1, ← Matrix.mul_assoc, conjTranspose_eq_transpose_of_trivial,
    (mem_orthogonalGroup_iff _ ℝ).1 hQ, Matrix.one_mul]

/-- The exact step of `qrInsertColumn`. -/
private noncomputable def insColStep {m n : ℕ} (k : Fin (n + 1))
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin (n + 1)) ℝ) (j : ℕ) :
    Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin (n + 1)) ℝ :=
  if h : j + 1 < m then
    givensPairStep ⟨j, by omega⟩ ⟨j + 1, h⟩
      (Id.run (Chapter05.algorithm_5_1_3 pure (st.2 ⟨j, by omega⟩ k) (st.2 ⟨j + 1, h⟩ k))) st
  else st

/-- **§6.5.2, appending a column is correct in exact arithmetic**: if `A = QR` then the output of
`qrInsertColumn` is a QR factorization of `A` with `z` inserted as its column `k`. Invariant of the
bottom-up sweep: `QH = Ã`; `H` is triangular off the spike column `k`; the diagonal entries right of
the spike vanish in the rows not yet rotated (so a rotation of the rows `j`, `j + 1` creates no
subdiagonal entry); the spike vanishes below the rows already rotated. -/
theorem qrInsertColumn_spec {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {Q : Matrix (Fin m) (Fin m) ℝ} {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R)
    (z : Fin m → ℝ) (k : Fin (n + 1)) :
    IsQR (of fun i => k.insertNth (z i) (A i)) (Id.run (qrInsertColumn pure Q R z k)).1
      (Id.run (qrInsertColumn pure Q R z k)).2 := by
  set At : Matrix (Fin m) (Fin (n + 1)) ℝ := of fun i => k.insertNth (z i) (A i) with hAt
  obtain ⟨h1, h2⟩ := h.conjTranspose_mul_insertColumn z k
  have hQ : Q ∈ orthogonalGroup (Fin m) ℝ := h.mem_unitaryGroup
  set H₀ : Matrix (Fin m) (Fin (n + 1)) ℝ := of fun i => k.insertNth ((Qᵀ *ᵥ z) i) (R i)
    with hH₀
  rw [conjTranspose_eq_transpose_of_trivial] at h1 h2
  rw [← hAt] at h1 h2
  rw [← hH₀] at h1
  have hrun : Id.run (qrInsertColumn pure Q R z k) =
      (List.range' k (m - 1 - k)).reverse.foldl (insColStep k) (Q, H₀) := by
    simp only [qrInsertColumn, Id.run_bind, Chapter01.algorithm_1_1_3_spec, zero_add,
      List.idRun_foldlM]
    congr 1
    funext st j
    unfold insColStep
    split_ifs with hj
    · have hpq : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, hj⟩ := fun e => by simp [Fin.ext_iff] at e
      simp only [Id.run_bind, Id.run_pure]
      rw [Chapter05.givensApplyLeft_spec_of_forall_mem hpq _ _ (List.nodup_finRange (n + 1))
        (List.mem_finRange), Chapter05.givensApplyRight_spec_of_forall_mem hpq _ _
        (List.nodup_finRange m) (List.mem_finRange)]
      rfl
    · rfl
  set V : ℕ → Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin (n + 1)) ℝ → Prop := fun K st =>
    st.1 ∈ orthogonalGroup (Fin m) ℝ ∧ st.1 * st.2 = At ∧
      (∀ (i : Fin m) (j : Fin (n + 1)), (j : ℕ) < i → j ≠ k → st.2 i j = 0) ∧
      (∀ (i : Fin m) (j : Fin (n + 1)), k < j → (j : ℕ) = i → (i : ℕ) < K → st.2 i j = 0) ∧
      ∀ i : Fin m, K < i → st.2 i k = 0 with hV
  have hstep : ∀ j st, (k : ℕ) ≤ j → V (j + 1) st → V j (insColStep k st j) := by
    rintro j st hkj ⟨hQ, hQH, hab, hdiag, hspike⟩
    unfold insColStep
    split_ifs with hj
    · set p : Fin m := ⟨j, by omega⟩ with hp
      set q : Fin m := ⟨j + 1, hj⟩ with hq
      have hpv : (p : ℕ) = j := rfl
      have hqv : (q : ℕ) = j + 1 := rfl
      have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
      have hcs := (Chapter05.algorithm_5_1_3_spec (st.2 p k) (st.2 q k)).1
      refine ⟨givensPairStep_mem hpq hcs hQ, by rw [givensPairStep_mul hpq hcs, hQH],
        fun i l hil hlk => ?_, fun i l hkl hli hiK => ?_, fun i hi => ?_⟩
      · refine givensPairStep_eq_zero hpq _ st (fun hi => ?_) fun _ _ => hab i l hil hlk
        have hiv := val_eq_or_of_eq_or hi
        refine ⟨?_, hab q l (by omega) hlk⟩
        by_cases hlp : (l : ℕ) < j
        · exact hab p l (by omega) hlk
        · have hkl : k < l := by
            rcases lt_or_gt_of_ne hlk with h' | h'
            · exfalso
              have : (l : ℕ) < k := h'
              omega
            · exact h'
          exact hdiag p l hkl (by omega) (by omega)
      · have hip : i ≠ p := fun e => by rw [e] at hiK; omega
        have hiq : i ≠ q := fun e => by rw [e] at hiK; omega
        rw [givensPairStep_apply hpq, ite_eq_right hip, ite_eq_right hiq]
        exact hdiag i l hkl hli (by omega)
      · by_cases hiq : i = q
        · rw [hiq]
          exact givensPairStep_zero hpq k st
        · have hip : i ≠ p := fun e => by rw [e] at hi; omega
          rw [givensPairStep_apply hpq, ite_eq_right hip, ite_eq_right hiq]
          exact hspike i (by
            have : (i : ℕ) ≠ j + 1 := fun e => hiq (Fin.ext (by rw [hqv, e]))
            omega)
    · refine ⟨hQ, hQH, hab, fun i l hkl hli hiK => hdiag i l hkl hli (by omega), fun i hi => ?_⟩
      exfalso
      have := i.isLt
      omega
  have hall : ∀ t st, V (k + t) st →
      V k ((List.range' k t).reverse.foldl (insColStep k) st) := by
    intro t
    induction t with
    | zero => intro st h; simpa using h
    | succ t ih =>
      intro st h
      rw [List.range'_concat, List.reverse_append, one_mul]
      simp only [List.reverse_singleton, List.singleton_append, List.foldl_cons]
      exact ih _ (hstep (k + t) st (by omega) h)
  have h0 : V (k + (m - 1 - k)) (Q, H₀) := by
    refine ⟨hQ, ?_, fun i j hij hjk => ?_, fun i j hkj hji _ => ?_, fun i hi => ?_⟩
    · rw [← h1, ← Matrix.mul_assoc, (mem_orthogonalGroup_iff _ ℝ).1 hQ, Matrix.one_mul]
    · rw [← h1]
      exact h2 i j hij hjk
    · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq (ne_of_gt hkj)
      have hts : (k.succAbove t : ℕ) = t + 1 := by
        rcases lt_or_ge t.castSucc k with h' | h'
        · rw [Fin.succAbove_of_castSucc_lt _ _ h'] at hkj
          exact absurd hkj (not_lt.2 h'.le)
        · rw [Fin.succAbove_of_le_castSucc _ _ h']
          simp
      simp only [hH₀, of_apply, Fin.insertNth_apply_succAbove]
      exact h.apply_eq_zero i t (by omega)
    · exfalso
      have := i.isLt
      omega
  obtain ⟨hQ', hQH', hab', -, hspike'⟩ := hall (m - 1 - k) (Q, H₀) h0
  rw [hrun]
  refine ⟨hQ', fun i j hij => ?_, hQH'⟩
  by_cases hjk : j = k
  · rw [hjk] at hij ⊢
    exact hspike' i hij
  · exact hab' i j hij hjk

/-- **§6.5.3, inserting a row is correct in exact arithmetic**: if `A = QR` then the output of
`qrInsertRow` is a QR factorization of `A` with `wᵀ` inserted as its row `k`. With
`σ = (Fin.cycleRange k)⁻¹`, `diag(1, Qᵀ) P Ã = [wᵀ; R]` is upper Hessenberg
(`Matrix.IsQR.conjTranspose_mul_insertRow`), and the sweep triangularizes it. -/
theorem qrInsertRow_spec {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R) (w : Fin n → ℝ) (k : Fin (m + 1)) :
    IsQR (of (k.insertNth w A)) (Id.run (qrInsertRow pure Q R w k)).1
      (Id.run (qrInsertRow pure Q R w k)).2 := by
  obtain ⟨h1, h2⟩ := h.conjTranspose_mul_insertRow w k
  have hQ : Q ∈ unitaryGroup (Fin m) ℝ := h.mem_unitaryGroup
  have hQ' : (consDiag 1 Q).submatrix k.cycleRange id ∈ orthogonalGroup (Fin (m + 1)) ℝ :=
    submatrix_mem_unitaryGroup (consDiag_mem_unitaryGroup (by simp) hQ) _
  refine givensHessenbergSweep_spec hQ' ?_ (fun i j hij => h2 i j hij)
    (fun i j _ hj => absurd hj (Nat.not_lt_zero _)) (Or.inl (by omega))
  rw [← h1, submatrix_id_mul, ← Matrix.mul_assoc, consDiag_mul_consDiag, mul_one,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff.1 hQ, consDiag_one, Matrix.one_mul,
    submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id, submatrix_id_id]

/-- **§6.5.3, deleting the first row is correct in exact arithmetic**: if `A = QR` with
`A ∈ ℝ^{(m+1)×n}`, the output of `qrDeleteFirstRow` is a QR factorization of `A(2:m+1, :)`. After
the sweep the first row of `QG_{m−1} ⋯ G₁` is `αe₁ᵀ` (`α² = 1`), so its first column is `αe₁` too,
and `A = [α 0; 0 Q₁][vᵀ; R₁]` with `[vᵀ; R₁]` upper Hessenberg. -/
theorem qrDeleteFirstRow_spec {m n : ℕ} {A : Matrix (Fin (m + 1)) (Fin n) ℝ}
    {Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {R : Matrix (Fin (m + 1)) (Fin n) ℝ}
    (h : IsQR A Q R) :
    IsQR (A.submatrix Fin.succ id) (Id.run (qrDeleteFirstRow pure Q R)).1
      (Id.run (qrDeleteFirstRow pure Q R)).2 := by
  have hQ : Q ∈ orthogonalGroup (Fin (m + 1)) ℝ := h.mem_unitaryGroup
  obtain ⟨⟨P, hP, h1, h2, h3⟩, hwz, hHess, -⟩ :=
    givensVectorSweep_spec 0 m (Q 0) Q R h.apply_eq_zero (fun i hi => by omega)
  set st := Id.run (givensVectorSweep pure 0 m (Q 0) Q R) with hst
  have hrun : Id.run (qrDeleteFirstRow pure Q R) =
      (st.2.1.submatrix Fin.succ Fin.succ, st.2.2.submatrix Fin.succ id) := rfl
  rw [hrun]
  have hPt : Pᵀ ∈ orthogonalGroup (Fin (m + 1)) ℝ := by
    rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
    exact Unitary.star_mem hP
  have hQo : st.2.1 ∈ orthogonalGroup (Fin (m + 1)) ℝ := by rw [h2]; exact mul_mem hQ hPt
  have hQR : st.2.1 * st.2.2 = A := by
    rw [h2, h3, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ,
      (mem_orthogonalGroup_iff' _ ℝ).1 hP, Matrix.one_mul, h.mul_eq]
  have hrow : ∀ j, st.2.1 0 j = st.1 j := by
    intro j
    rw [h2, h1, mul_apply, mulVec, dotProduct]
    simp only [transpose_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hrow0 : ∀ j : Fin m, st.2.1 0 j.succ = 0 := fun j => by
    rw [hrow]
    exact hwz _ (by simp)
  have hcol0 : ∀ i : Fin m, st.2.1 i.succ 0 = 0 := by
    have e1 : (st.2.1 * st.2.1ᵀ) 0 0 = 1 := by rw [(mem_orthogonalGroup_iff _ ℝ).1 hQo]; simp
    have e2 : (st.2.1ᵀ * st.2.1) 0 0 = 1 := by rw [(mem_orthogonalGroup_iff' _ ℝ).1 hQo]; simp
    rw [mul_apply, Fin.sum_univ_succ] at e1 e2
    simp only [transpose_apply, hrow0, mul_zero, Finset.sum_const_zero, add_zero] at e1 e2
    have hs : ∑ i : Fin m, st.2.1 i.succ 0 * st.2.1 i.succ 0 = 0 := by linarith
    intro i
    exact mul_self_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_self_nonneg (st.2.1 (Fin.succ i) 0))).1 hs i (Finset.mem_univ _))
  refine ⟨?_, fun i j hij => ?_, ?_⟩
  · refine (mem_orthogonalGroup_iff _ ℝ).2 ?_
    ext i j
    have := congrFun (congrFun ((mem_orthogonalGroup_iff _ ℝ).1 hQo) i.succ) j.succ
    rw [mul_apply, Fin.sum_univ_succ] at this
    simp only [transpose_apply, hcol0, zero_mul, zero_add, one_apply, Fin.succ_inj] at this
    simpa [mul_apply, one_apply] using this
  · exact hHess i.succ j (by simp; omega)
  · ext i j
    have := congrFun (congrFun hQR i.succ) j
    rw [mul_apply, Fin.sum_univ_succ, hcol0, zero_mul, zero_add] at this
    simpa [mul_apply] using this

/-- The exact step of `choleskyUpdate`. -/
private noncomputable def cholUpdStep {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin n) ℝ) (k : Fin n) :
    Matrix (Fin (n + 1)) (Fin n) ℝ :=
  (Chapter05.givensRotation k.castSucc (Fin.last n)
    (Id.run (Chapter05.algorithm_5_1_3 pure (S k.castSucc k) (S (Fin.last n) k))).1
    (Id.run (Chapter05.algorithm_5_1_3 pure (S k.castSucc k) (S (Fin.last n) k))).2)ᵀ * S

/-- The Gram matrix of a matrix on `Fin (n + 1)` rows splits off its last row. -/
private theorem transpose_mul_self_castSucc {n p : ℕ} (S : Matrix (Fin (n + 1)) (Fin p) ℝ) :
    Sᵀ * S = (S.submatrix Fin.castSucc id)ᵀ * S.submatrix Fin.castSucc id +
      vecMulVec (S (Fin.last n)) (S (Fin.last n)) := by
  ext i j
  simp [mul_apply, Fin.sum_univ_castSucc, vecMulVec_apply]

/-- **§6.5.4, Cholesky updating is correct in exact arithmetic**: if `A = GGᵀ`
(`Matrix.IsCholesky A Gᵀ`), the output `G̃` of `choleskyUpdate` is lower triangular with nonzero
diagonal and `G̃G̃ᵀ = A + zzᵀ`; with the signs of its diagonal normalized it is the Cholesky factor
of `A + zzᵀ` ("the updated Cholesky factor is given by `G̃ = Rᵀ`", up to the signs a Givens `r`
may carry: `equation_6_5_7`). Invariant: the rotations keep the Gram matrix `MᵀM = A + zzᵀ` of the
stacked `M`, keep its top block triangular with nonzero diagonal (`|r| = √(a² + b²)`), and zero the
appended row before the current column. -/
theorem choleskyUpdate_spec {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} (hG : IsCholesky A Gᵀ)
    (z : Fin n → ℝ) :
    (Id.run (choleskyUpdate pure G z))ᵀ.IsUpperTriangular ∧
      (∀ i, Id.run (choleskyUpdate pure G z) i i ≠ 0) ∧
      Id.run (choleskyUpdate pure G z) * (Id.run (choleskyUpdate pure G z))ᵀ =
        A + vecMulVec z z ∧
      IsCholesky (A + vecMulVec z z) (diagonal (fun i =>
        (SignType.sign (Id.run (choleskyUpdate pure G z) i i) : ℝ)) *
          (Id.run (choleskyUpdate pure G z))ᵀ) := by
  set S₀ : Matrix (Fin (n + 1)) (Fin n) ℝ :=
    of fun i => Fin.lastCases (motive := fun _ => Fin n → ℝ) z (fun i => Gᵀ i) i with hS₀
  have hF : ∀ (S : Matrix (Fin (n + 1)) (Fin n) ℝ) (k : Fin n),
      Id.run (Chapter05.givensApplyLeft pure k.castSucc (Fin.last n)
        (Id.run (Chapter05.algorithm_5_1_3 pure (S k.castSucc k) (S (Fin.last n) k))).1
        (Id.run (Chapter05.algorithm_5_1_3 pure (S k.castSucc k) (S (Fin.last n) k))).2
        (List.finRange n) S) = cholUpdStep S k := fun S k =>
    Chapter05.givensApplyLeft_spec_of_forall_mem (Fin.castSucc_lt_last k).ne _ _
      (List.nodup_finRange n) List.mem_finRange S
  have hrun : Id.run (choleskyUpdate pure G z) =
      (((List.finRange n).foldl cholUpdStep S₀).submatrix Fin.castSucc id)ᵀ := by
    simp only [choleskyUpdate, Id.run_bind, Id.run_pure, List.idRun_foldlM, hF]
    rfl
  set Inv : ℕ → Matrix (Fin (n + 1)) (Fin n) ℝ → Prop := fun t S =>
    (∀ i j : Fin n, j < i → S i.castSucc j = 0) ∧ (∀ i : Fin n, S i.castSucc i ≠ 0) ∧
      (∀ j : Fin n, (j : ℕ) < t → S (Fin.last n) j = 0) ∧ Sᵀ * S = A + vecMulVec z z with hInv
  have hstep : ∀ t (ht : t < n) S, Inv t S → Inv (t + 1) (cholUpdStep S ⟨t, ht⟩) := by
    rintro t ht S ⟨hU, hd, hy, hgram⟩
    set k : Fin n := ⟨t, ht⟩ with hk
    have hne : k.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last k).ne
    obtain ⟨hcs, hz, habs⟩ := Chapter05.algorithm_5_1_3_spec (S k.castSucc k) (S (Fin.last n) k)
    set c := (Id.run (Chapter05.algorithm_5_1_3 pure (S k.castSucc k) (S (Fin.last n) k))).1
    set s := (Id.run (Chapter05.algorithm_5_1_3 pure (S k.castSucc k) (S (Fin.last n) k))).2
    have happ := Chapter05.givensRotation_transpose_mul_apply hne c s S
    have hGo := Chapter05.givensRotation_mem_orthogonalGroup hne hcs
    have hne' : ∀ i : Fin n, i ≠ k → i.castSucc ≠ k.castSucc := fun i hi e =>
      hi (Fin.castSucc_injective _ e)
    have hlast : ∀ i : Fin n, i.castSucc ≠ Fin.last n := fun i => (Fin.castSucc_lt_last i).ne
    refine ⟨fun i j hji => ?_, fun i => ?_, fun j hj => ?_, ?_⟩
    · change ((Chapter05.givensRotation k.castSucc (Fin.last n) c s)ᵀ * S) i.castSucc j = 0
      rw [happ]
      by_cases hik : i = k
      · have hjk : j < k := hik ▸ hji
        rw [ite_eq_left (congrArg Fin.castSucc hik), hU k j hjk, hy j hjk]
        ring
      · rw [ite_eq_right (hne' i hik), ite_eq_right (hlast i)]
        exact hU i j hji
    · change ((Chapter05.givensRotation k.castSucc (Fin.last n) c s)ᵀ * S) i.castSucc i ≠ 0
      rw [happ]
      by_cases hik : i = k
      · rw [ite_eq_left (congrArg Fin.castSucc hik), hik]
        intro h0
        rw [h0, abs_zero] at habs
        have := (Real.sqrt_eq_zero (by positivity)).1 habs.symm
        exact hd k (by nlinarith [sq_nonneg (S k.castSucc k), sq_nonneg (S (Fin.last n) k)])
      · rw [ite_eq_right (hne' i hik), ite_eq_right (hlast i)]
        exact hd i
    · change ((Chapter05.givensRotation k.castSucc (Fin.last n) c s)ᵀ * S) (Fin.last n) j = 0
      rw [happ, ite_eq_right hne.symm, ite_eq_left rfl]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · rw [hU k j hj, hy j hj]
        ring
      · obtain rfl : j = k := Fin.ext hj
        exact hz
    · change ((Chapter05.givensRotation k.castSucc (Fin.last n) c s)ᵀ * S)ᵀ *
        ((Chapter05.givensRotation k.castSucc (Fin.last n) c s)ᵀ * S) = _
      rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc
        (Chapter05.givensRotation k.castSucc (Fin.last n) c s),
        (mem_orthogonalGroup_iff _ ℝ).1 hGo, Matrix.one_mul, hgram]
  have hS₀c : ∀ i : Fin n, S₀ i.castSucc = Gᵀ i := fun i => funext fun j => by
    rw [hS₀, of_apply, Fin.lastCases_castSucc]
  have hS₀l : S₀ (Fin.last n) = z := funext fun j => by
    rw [hS₀, of_apply, Fin.lastCases_last]
  have hpre : ∀ t (ht : t ≤ n), Inv t (((List.finRange n).take t).foldl cholUpdStep S₀) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨fun i j hji => ?_, fun i => ?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
      · simp only [List.take_zero, List.foldl_nil, hS₀c]
        exact hG.isUpperTriangular hji
      · simp only [List.take_zero, List.foldl_nil, hS₀c]
        exact (hG.diag_pos i).ne'
      · simp only [List.take_zero, List.foldl_nil]
        rw [transpose_mul_self_castSucc, hS₀l]
        congr 1
        rw [← conjTranspose_eq_transpose_of_trivial (S₀.submatrix Fin.castSucc id),
          ← hG.conjTranspose_mul_self]
        congr 1 <;> ext i j <;> simp [hS₀c]
    | succ t ih =>
      intro ht
      have htake : (List.finRange n).take (t + 1) =
          (List.finRange n).take t ++ [⟨t, by omega⟩] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by rw [List.length_finRange]; omega)]
        simp
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact hstep t (by omega) _ (ih (by omega))
  obtain ⟨hU, hd, hy, hgram⟩ := hpre n le_rfl
  rw [List.take_of_length_le (by simp)] at hU hd hy hgram
  set S := (List.finRange n).foldl cholUpdStep S₀ with hS
  have hy0 : S (Fin.last n) = 0 := funext fun j => hy j j.isLt
  rw [transpose_mul_self_castSucc, hy0, vecMulVec_zero, add_zero] at hgram
  have hR : (S.submatrix Fin.castSucc id).IsUpperTriangular := fun i j hji => hU i j hji
  have hdR : ∀ i, S.submatrix Fin.castSucc id i i ≠ 0 := hd
  rw [hrun, transpose_transpose]
  refine ⟨hR, fun i => ?_, ?_, ?_⟩
  · rw [transpose_apply]
    exact hd i
  · rw [← hgram]
  · have := isCholesky_diagonal_sign_mul hR hdR hgram
    simpa [transpose_apply] using this

/-! ### §6.5.5 The ULV decomposition -/

/-- **(6.5.16)**, its exact content. "A rank-revealing ULV decomposition of a matrix `A ∈ ℝ^{m×n}`
has the form `UᵀAV = [L; 0]`, `UᵀU = I_m`, `VᵀV = I_n` … Such a decomposition can be obtained by
applying QR with column pivoting `UᵀAΠ = [R; 0]` followed by a QR factorization `V₁ᵀRᵀ = Lᵀ`. In
this case the matrix `V` in (6.5.16) is given by `V = ΠV₁`." With `m = n + p`, `U`, `P = Π`
and `V₁` orthogonal (a permutation matrix is) and `Lᵀ` upper triangular, `L` is lower triangular.
The rank-revealing smallness of `L₂₁`, `L₂₂` is a heuristic property of pivoted QR, not
formalized. -/
theorem equation_6_5_16 {n p : ℕ} {A : Matrix (Fin (n + p)) (Fin n) ℝ}
    {U : Matrix (Fin (n + p)) (Fin (n + p)) ℝ} (hU : U ∈ orthogonalGroup (Fin (n + p)) ℝ)
    {P V₁ R L : Matrix (Fin n) (Fin n) ℝ} (hP : P ∈ orthogonalGroup (Fin n) ℝ)
    (hV₁ : V₁ ∈ orthogonalGroup (Fin n) ℝ)
    (hR : (Uᵀ * A * P).submatrix finSumFinEquiv id = fromRows R 0) (hL : V₁ᵀ * Rᵀ = Lᵀ)
    (hLt : Lᵀ.IsUpperTriangular) :
    (Uᵀ * A * (P * V₁)).submatrix finSumFinEquiv id = fromRows L 0 ∧ L.IsLowerTriangular ∧
      Uᵀ * U = 1 ∧ (P * V₁)ᵀ * (P * V₁) = 1 := by
  have hRV : R * V₁ = L := by
    rw [← transpose_transpose (R * V₁), transpose_mul, hL, transpose_transpose]
  refine ⟨?_, fun i j hij => ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, ← hRV]
    ext i j
    have := congrFun (congrFun hR i)
    simp only [submatrix_apply, id] at this ⊢
    rw [mul_apply]
    simp only [this] at *
    rcases i with i | i
    · simp [fromRows_apply_inl, mul_apply]
    · simp [fromRows_apply_inr]
  · exact hLt hij
  · exact (mem_orthogonalGroup_iff' _ ℝ).1 hU
  · exact (mem_orthogonalGroup_iff' _ ℝ).1 ((orthogonalGroup (Fin n) ℝ).mul_mem hP hV₁)

open scoped Matrix.Norms.L2Operator in
/-- **§6.5.5.** "Note that if `V = [V₁ V₂]` (`r | n − r`), `U = [U₁ U₂]`, then the columns of `V₂`
define an approximate nullspace: `‖AV₂‖₂ = ‖U₂L₂₂‖₂ = ‖L₂₂‖₂`." With `n = r + q`, `m = n + p` and
`L = [L₁₁ 0; L₂₁ L₂₂]` lower triangular, `AV₂ = U [0; L₂₂; 0]`, whose 2-norm is `‖L₂₂‖₂` (the book's
`U₂` should be the columns `r + 1 : n` of `U`). -/
theorem ulv_nullspace_norm {r q p : ℕ} {A : Matrix (Fin (r + q + p)) (Fin (r + q)) ℝ}
    {U : Matrix (Fin (r + q + p)) (Fin (r + q + p)) ℝ}
    (hU : U ∈ orthogonalGroup (Fin (r + q + p)) ℝ) {V L : Matrix (Fin (r + q)) (Fin (r + q)) ℝ}
    (h : (Uᵀ * A * V).submatrix finSumFinEquiv id = fromRows L 0) (hL : L.IsLowerTriangular) :
    ‖A * V.submatrix id (Fin.natAdd r)‖ = ‖L.submatrix (Fin.natAdd r) (Fin.natAdd r)‖ := by
  set f : Fin q → Fin (r + q + p) := fun j => Fin.castAdd p (Fin.natAdd r j) with hf
  set W : Matrix (Fin (r + q + p)) (Fin q) ℝ := (1 : Matrix _ _ ℝ).submatrix id f with hW
  have hUU : U * Uᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hU
  have hUU' : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' _ ℝ).1 hU
  have hfinj : Function.Injective f := fun a b hab => by
    simpa [hf, Fin.ext_iff] using hab
  have hWW : Wᵀ * W = 1 := by
    ext a b
    simp only [hW, mul_apply, transpose_apply, submatrix_apply, id, one_apply]
    rw [Finset.sum_eq_single (f a)]
    · simp [hfinj.eq_iff]
    · intro i _ hi
      simp only [hi, ite_false, zero_mul]
    · simp
  have key : Uᵀ * A * V.submatrix id (Fin.natAdd r) =
      W * L.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
    ext i j
    have hsub : (Uᵀ * A * V.submatrix id (Fin.natAdd r)) i j = (Uᵀ * A * V) i (Fin.natAdd r j) := by
      simp only [mul_apply, submatrix_apply, id]
    rw [hsub]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · have e := congrFun (congrFun h (Sum.inl a)) (Fin.natAdd r j)
      simp only [submatrix_apply, finSumFinEquiv_apply_left, id, fromRows_apply_inl] at e
      rw [e, mul_apply]
      refine Fin.addCases (fun a' => ?_) (fun b' => ?_) a
      · have : L (Fin.castAdd q a') (Fin.natAdd r j) = 0 := hL (by
          have := a'.isLt
          simp [Fin.lt_def]
          omega)
        rw [this, Finset.sum_eq_zero]
        intro k _
        simp only [hW, submatrix_apply, id, one_apply, hf]
        rw [ite_eq_right]
        · simp
        · intro hk
          have := congrArg Fin.val hk
          simp at this
          omega
      · rw [Finset.sum_eq_single b']
        · simp [hW, hf, one_apply]
        · intro k _ hk
          simp only [hW, submatrix_apply, id, one_apply, hf]
          rw [ite_eq_right]
          · simp
          · intro hk'
            exact hk (Fin.ext (by have := congrArg Fin.val hk'; simp at this; omega))
        · simp
    · have e := congrFun (congrFun h (Sum.inr b)) (Fin.natAdd r j)
      simp only [submatrix_apply, finSumFinEquiv_apply_right, id, fromRows_apply_inr,
        Matrix.zero_apply] at e
      rw [e, mul_apply, Finset.sum_eq_zero]
      intro k _
      simp only [hW, submatrix_apply, id, one_apply, hf]
      rw [ite_eq_right]
      · simp
      · intro hk
        have := congrArg Fin.val hk
        simp at this
        omega
  have hAV : A * V.submatrix id (Fin.natAdd r) =
      (U * W) * L.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
    rw [Matrix.mul_assoc U W, ← key, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU,
      Matrix.one_mul]
  have hUW : (U * W)ᴴ * (U * W) = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Uᵀ, hUU', Matrix.one_mul, hWW]
  rw [hAV, l2_opNorm_mul_of_conjTranspose_mul_self_eq_one hUW]

end GolubVanLoan.Chapter06
