import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.LeastSquares
import NumlibSurface.GolubVanLoan.Chapter02.Section06
import NumlibSurface.GolubVanLoan.Chapter05.Section01

/-!
# Golub–Van Loan §5.2: the QR factorization

Surface file for [golub2013matrix] §5.2: existence of the QR factorization (Theorem 5.2.1), the
ranges of the factors (Theorem 5.2.2, (5.2.1)–(5.2.3)), uniqueness of the thin factorization and
its Cholesky reading (Theorem 5.2.3); Householder QR (Algorithm 5.2.1), block Householder QR
(Algorithm 5.2.2) and recursive block Householder QR (Algorithm 5.2.3), Givens QR
(Algorithm 5.2.4) with its two reorderings, Hessenberg QR (Algorithm 5.2.5), classical and
modified Gram–Schmidt (Algorithm 5.2.6); the complex Householder QR of §5.2.10.

## Conventions

The full factorization is the backbone's `Matrix.IsQR A Q R` (`Q` unitary — orthogonal over `ℝ` —,
`R` zero below the diagonal, `Q R = A`), the thin one `Matrix.IsThinQR`. An algorithm overwriting
`A` is read back through `upperPart` (the upper triangle of the output) and, for Householder QR, the
factored form `factoredQ β A'` of §5.1.6 with the `β` the program **returned** (convention 13).
A Householder step on `A(j:m, j:n)` is `houseOn` and `householderApplyLeft` on the full array with
the index lists `indexFrom m j`, `indexFrom n j` (convention 10); a Givens step is
`givensApplyLeft` on its column list. Indices are 0-based.

The backward error of Algorithm 5.2.1 is also stated with its reflector data
(`householderQRStep_rounding_data`, `algorithm_5_2_1_rounding_data`), the form §5.3.3 consumes.
Beside Algorithm 5.2.5 live the two Givens sweeps of §6.5 (`givensHessenbergSweep`,
`givensVectorSweep`, with the exact step `givensPairStep`), shared by the updating procedures.

## Not formalized

Stewart's `O(ε κ₂(A))` perturbation of the QR factors (§5.2.1, quoted without statement), the
roundoff claims for Algorithm 5.2.2 ("essentially the same") and for Gram–Schmidt (§5.2.9, quoted
without derivation), the orthogonality `Q̂₁ᵀQ̂₁ = I + E_H`, `‖E_H‖₂ ≈ u` of the Householder `Q`
accumulated in floating point (§5.2.9; no rounding theorem for `forwardAccumulation` /
`backwardAccumulation` is stated), flop counts, level-3 fractions, parallel Givens orderings.
-/

open FloatingPoint Matrix WithLp

namespace GolubVanLoan.Chapter05

variable {m n : ℕ}

/-! ### §5.2.1 Existence and properties -/

section Existence

/-- **Theorem 5.2.1 (QR Factorization)**: "If `A ∈ ℝ^{m×n}`, then there exists an orthogonal
`Q ∈ ℝ^{m×m}` and an upper triangular `R ∈ ℝ^{m×n}` so that `A = QR`." -/
theorem theorem_5_2_1 (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ Q ∈ orthogonalGroup (Fin m) ℝ, ∃ R : Matrix (Fin m) (Fin n) ℝ,
      (∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → R i j = 0) ∧ A = Q * R := by
  obtain ⟨Q, R, h⟩ := exists_isQR A
  exact ⟨Q, h.mem_unitaryGroup, R, h.apply_eq_zero, h.mul_eq.symm⟩

/-- **(5.2.3)**: comparing the `k`-th columns of `A = QR`, `a_k = ∑_{i ≤ k} r_ik q_i`. -/
theorem equation_5_2_3 {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R) (k : Fin n) :
    A.col k = ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) ≤ k), R i k • Q.col i := by
  ext p
  rw [← h.mul_eq, Finset.sum_apply, col_apply, Matrix.mul_apply,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => (i : ℕ) ≤ k)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) ≤ k)) fun i hi => by
    rw [h.apply_eq_zero i k (by simpa using hi), mul_zero], add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

/-- **(5.2.1)**: for a QR factorization of a full-column-rank `A ∈ ℝ^{m×n}`,
`span{a₁, …, a_k} = span{q₁, …, q_k}` for `k = 1:n`, and `r_kk ≠ 0`. -/
theorem equation_5_2_1 {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R) (hA : LinearIndependent ℝ Aᵀ) (hnm : n ≤ m)
    {k : ℕ} (hk : k ≤ n) :
    Submodule.span ℝ (Set.range fun j : Fin k => A.col (Fin.castLE hk j)) =
        Submodule.span ℝ (Set.range fun i : Fin k => Q.col (Fin.castLE (hk.trans hnm) i)) ∧
      ∀ (i : Fin m) (j : Fin n), (i : ℕ) = j → R i j ≠ 0 :=
  h.span_col_prefix_eq hA hnm hk

/-- **(5.2.2), the thin QR factorization**: with `Q₁ = Q(1:m, 1:n)` and `R₁ = R(1:n, 1:n)`
(`n ≤ m`), `A = Q₁ R₁`, and this is a thin QR factorization. -/
theorem equation_5_2_2 {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R) (hnm : n ≤ m) :
    Q.firstColumns hnm * R.firstRows hnm = A ∧ IsThinQR A (Q.firstColumns hnm) (R.firstRows hnm) :=
  ⟨h.firstColumns_mul_firstRows hnm, h.isThinQR hnm⟩

/-- **Theorem 5.2.2**: if `A = QR` is a QR factorization of a full-column-rank `A ∈ ℝ^{m×n}`, then
(5.2.1) holds and `r_kk ≠ 0`; `ran(A) = ran(Q₁)`; `ran(A)⊥ = ran(Q₂)` for
`Q₂ = Q(1:m, n+1:m)`; and `A = Q₁ R₁` (5.2.2). -/
theorem theorem_5_2_2 {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
    {R : Matrix (Fin m) (Fin n) ℝ} (h : IsQR A Q R) (hA : LinearIndependent ℝ Aᵀ)
    (hnm : n ≤ m) :
    (∀ k (hk : k ≤ n),
      Submodule.span ℝ (Set.range fun j : Fin k => A.col (Fin.castLE hk j)) =
        Submodule.span ℝ (Set.range fun i : Fin k => Q.col (Fin.castLE (hk.trans hnm) i))) ∧
      (∀ (i : Fin m) (j : Fin n), (i : ℕ) = j → R i j ≠ 0) ∧
      Submodule.span ℝ (Set.range (Q.firstColumns hnm)ᵀ) = Submodule.span ℝ (Set.range Aᵀ) ∧
      (toEuclideanLin A).rangeᗮ =
        Submodule.span ℝ (Set.range fun i : {i : Fin m // n ≤ i} => toLp 2 (Qᵀ i)) ∧
      Q.firstColumns hnm * R.firstRows hnm = A := by
  have hset : (Set.range fun j : Fin (m - n) =>
      toLp 2 ((Q.lastColumns (Nat.sub_le m n))ᵀ j)) =
        Set.range fun i : {i : Fin m // n ≤ i} => toLp 2 (Qᵀ i) := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨⟨m - (m - n) + j, by omega⟩, show n ≤ m - (m - n) + (j : ℕ) by omega⟩, rfl⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      refine ⟨⟨i - n, by omega⟩, congrArg (toLp 2) (funext fun r => ?_)⟩
      simp only [transpose_apply, lastColumns_apply]
      congr 1
      ext
      simp only
      omega
  exact ⟨fun _ hk => (equation_5_2_1 h hA hnm hk).1, (equation_5_2_1 h hA hnm le_rfl).2,
    h.span_firstColumns_eq hnm hA, (h.range_orthogonal_eq_span_lastColumns hnm hA).trans
      (congrArg _ hset), (equation_5_2_2 h hnm).1⟩

/-- **Theorem 5.2.3 (Thin QR Factorization)**: for full-column-rank `A ∈ ℝ^{m×n}` the thin QR
factorization `A = Q₁ R₁` with orthonormal columns and `R₁` upper triangular with positive
diagonal exists and is unique, and `R₁ = Gᵀ` for the lower triangular Cholesky factor `G` of
`AᵀA` (the backbone's `IsCholesky (AᵀA) R₁` is `R₁ᵀ R₁ = AᵀA` with `R₁` upper triangular and
positive diagonal). -/
theorem theorem_5_2_3 {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ) :
    (∃ Q R, IsThinQR A Q R ∧ ∀ j, 0 < R j j) ∧
      (∀ Q₁ Q₂ R₁ R₂, IsThinQR A Q₁ R₁ → IsThinQR A Q₂ R₂ → (∀ j, 0 < R₁ j j) →
        (∀ j, 0 < R₂ j j) → Q₁ = Q₂ ∧ R₁ = R₂) ∧
      ∀ Q R, IsThinQR A Q R → (∀ j, 0 < R j j) → IsCholesky (Aᵀ * A) R := by
  refine ⟨exists_isThinQR A hA, fun _ _ _ _ h₁ h₂ hd₁ hd₂ => h₁.unique h₂ hd₁ hd₂,
    fun Q R h hd => ?_⟩
  have := h.isCholesky hd
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- **(5.2.4), the 2-norm condition number of a rectangular matrix**: "for rectangular matrices `A`
with full column rank we continue with this definition: `κ₂(A) = σ_max(A)/σ_min(A)`". Defined as
the backbone's `‖A‖₂ ‖A⁺‖₂` (`Matrix.pinvCondNumberLp 2 A`), which is `σ_max/σ_min` for full column
rank (`equation_5_2_4`) and the `κ₂` of §2.6.2 for a nonsingular square `A` (`kappa2_eq_kappa`). -/
noncomputable def kappa2 (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  pinvCondNumberLp 2 A

/-- **(5.2.4)**: for `A` of full column rank (`n ≥ 1`), `κ₂(A) = σ_max(A)/σ_min(A)`, the extreme
singular values read over the columns (`⨆ i, σ_i` and `⨅ i, σ_i`). -/
theorem equation_5_2_4 [NeZero n] {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ) :
    kappa2 A = (⨆ i, A.colSingularValues i) / ⨅ i, A.colSingularValues i :=
  pinvCondNumberLp_two_eq_div_colSingularValues hA

/-- For a nonsingular square `A`, the `κ₂(A)` of (5.2.4) is that of §2.6.2: the backbone's
`condNumberLp 2 A = ‖A‖₂ ‖A⁻¹‖₂`, and chapter 2's `kappa 2 A` is its (finite) value. -/
theorem kappa2_eq_kappa {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) :
    kappa2 A = condNumberLp 2 A ∧ Chapter02.kappa 2 A = ENNReal.ofReal (kappa2 A) := by
  have h : kappa2 A = condNumberLp 2 A := pinvCondNumberLp_eq_condNumberLp 2 hA
  exact ⟨h, by rw [h, Chapter02.kappa_of_isUnit 2 hA]⟩

open scoped Matrix.Norms.L2Operator in
/-- A matrix with independent columns and at least one column is nonzero. -/
theorem l2_opNorm_pos_of_linearIndependent [NeZero n] {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) : 0 < ‖A‖ := by
  refine norm_pos_iff.2 fun h0 => ?_
  have := hA.ne_zero (0 : Fin n)
  rw [h0] at this
  exact this rfl

open scoped Matrix.Norms.L2Operator in
/-- `κ₂(A) = ‖A‖₂ / σ_min(A)` for independent columns, `σ_min` read over the columns. The twin of
`kappa2_eq_div_of_rows`. -/
theorem kappa2_eq_div [NeZero n] {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) : kappa2 A = ‖A‖ / ⨅ i, A.colSingularValues i := by
  rw [kappa2, pinvCondNumberLp, lpOpNorm_two, lpOpNorm_two,
    l2_opNorm_pinv_eq_inv_iInf_colSingularValues hA, div_eq_mul_inv]

open scoped Matrix.Norms.L2Operator in
/-- `κ₂(A) = ‖A‖₂/σ_m(A)` for independent rows, `σ_m` read over the columns of `Aᵀ`. The twin of
`kappa2_eq_div`. -/
theorem kappa2_eq_div_of_rows [NeZero m] {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ A) : kappa2 A = ‖A‖ / ⨅ i, Aᵀ.colSingularValues i := by
  have hAt : LinearIndependent ℝ Aᵀᵀ := by rwa [transpose_transpose]
  have hp : A.pinv = (Aᵀ.pinv)ᵀ := by
    have := pinv_conjTranspose (A := Aᵀ)
    rw [conjTranspose_eq_transpose_of_trivial, conjTranspose_eq_transpose_of_trivial,
      transpose_transpose] at this
    rw [this]
  rw [kappa2, pinvCondNumberLp, lpOpNorm_two, lpOpNorm_two, hp,
    ← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose,
    l2_opNorm_pinv_eq_inv_iInf_colSingularValues hAt, div_eq_mul_inv]

end Existence

/-! ### §5.2.2 Householder QR -/

section Householder

/-- **The upper triangle of an overwritten array** ("the upper triangular part of `A` is
overwritten by the upper triangular part of `R`"): the entries `(i, j)` with `i ≤ j`. -/
def upperPart (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun i j => if (i : ℕ) ≤ j then A i j else 0

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One step `j` of Algorithm 5.2.1: `[v, β] = house(A(j:m, j))`,
`A(j:m, j:n) = (I - β v vᵀ) A(j:m, j:n)`, `A(j+1:m, j) = v(2:m-j+1)`, and `β` recorded. -/
noncomputable def householderQRStep (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) (j : Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) := do
  let vβ ← houseOn rnd (indexFrom m j) (fun i => st.1 i j)
  let A ← householderApplyLeft rnd vβ.1 vβ.2 (indexFrom m j) (indexFrom n j) st.1
  pure (A.updateCol j (fun i => if (j : ℕ) < i then vβ.1 i else A i j),
    Function.update st.2 j vβ.2)

/-- **Algorithm 5.2.1 (Householder QR)**: "Given `A ∈ ℝ^{m×n}` with `m ≥ n`, the following
algorithm finds Householder matrices `H₁, …, H_n` such that if `Q = H₁ ⋯ H_n`, then `QᵀA = R` is
upper triangular. The upper triangular part of `A` is overwritten by the upper triangular part of
`R` and components `j+1:m` of the `j`th Householder vector are stored in `A(j+1:m, j)`":
```
for j = 1:n
    [v, β] = house(A(j:m, j))
    A(j:m, j:n) = (I - β v vᵀ) A(j:m, j:n)
    if j < m:  A(j+1:m, j) = v(2:m-j+1)
end
```
The program also returns the `β_j` (the factored form is "the Householder vectors and the
corresponding `β_j`", §5.1.6; convention 13). -/
noncomputable def algorithm_5_2_1 (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) :=
  (List.finRange n).foldlM (householderQRStep rnd) (A, 0)

end Programs

/-- **The rounding theorems of Algorithm 5.2.1 are not vacuous**: over a total model the program
has a run. -/
theorem algorithm_5_2_1_run_nonempty {fp : RoundingModel ℝ} (hfp : fp.IsTotal)
    (A : Matrix (Fin m) (Fin n) ℝ) : (algorithm_5_2_1 fp.round A).run.Nonempty := by
  have hround := RoundingModel.run_round_nonempty hfp
  unfold algorithm_5_2_1
  apply SetM.run_foldlM_nonempty
  intro st j _
  unfold householderQRStep householderApplyLeft householderScaled householderLeftColumn
  cases h : indexFrom m j with
  | nil =>
    simp only [houseOn]
    all_goals repeat' first
      | exact ⟨_, rfl⟩
      | exact hround _
      | exact dotAccum_run_nonempty hfp _ _ _ _
      | (apply SetM.run_foldlM_nonempty; intros)
      | (apply SetM.run_bind_nonempty <;> intros)
  | cons p t =>
    simp only [houseOn]
    all_goals repeat' first
      | exact ⟨_, rfl⟩
      | exact hround _
      | exact dotAccum_run_nonempty hfp _ _ _ _
      | (apply SetM.run_foldlM_nonempty; intros)
      | (unfold parlettPivot; split_ifs)
      | split_ifs
      | (apply SetM.run_bind_nonempty <;> intros)

/-- An element of the first `j` entries of `List.finRange n` is below `j`. -/
theorem lt_of_mem_take_finRange {j : ℕ} {k : Fin n}
    (hk : k ∈ (List.finRange n).take j) : (k : ℕ) < j := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
  simp only [List.length_take, List.length_finRange] at hi
  rw [List.getElem_take, List.getElem_finRange]
  change i < j
  omega

@[deprecated (since := "2026-09-30")] alias val_lt_of_mem_take_finRange := lt_of_mem_take_finRange

/-- The product of the reflectors of the first `j` steps of Algorithm 5.2.1, read from the state
(the stored vectors and the recorded `β`). -/
private noncomputable def qrPrefix (j : ℕ) (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) :
    Matrix (Fin m) (Fin m) ℝ :=
  householderProduct
    (((List.finRange n).take j).map fun k => (storedHouseholderVec st.1 k, st.2 k))

/-- The invariant of Algorithm 5.2.1 after `j` steps, with `C = Qⱼᵀ A` for the product `Qⱼ` of
the reflectors so far: the upper part and the unprocessed columns of the array hold `C`, the
processed columns of `C` vanish below the diagonal, and every recorded `β` is `0` or `2/vᵀv`. -/
private def qrInvariant (A : Matrix (Fin m) (Fin n) ℝ) (j : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) : Prop :=
  (∀ (i : Fin m) (q : Fin n), ((i : ℕ) ≤ q ∨ j ≤ (q : ℕ)) →
      st.1 i q = ((qrPrefix j st)ᵀ * A) i q) ∧
    (∀ (i : Fin m) (q : Fin n), (q : ℕ) < j → (q : ℕ) < i →
      ((qrPrefix j st)ᵀ * A) i q = 0) ∧
    ∀ k : Fin n, (k : ℕ) < j →
      st.2 k = 0 ∨ st.2 k * (storedHouseholderVec st.1 k ⬝ᵥ storedHouseholderVec st.1 k) = 2

/-- One exact step of Algorithm 5.2.1 preserves the invariant. -/
private theorem qrInvariant_step (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ) (j : Fin n)
    (hI : qrInvariant A j (B, β)) :
    qrInvariant A (j + 1) (Id.run (householderQRStep pure (B, β) j)) := by
  obtain ⟨ha, hb, hc⟩ := hI
  have hjm : (j : ℕ) < m := lt_of_lt_of_le j.isLt hnm
  have hne := indexFrom_ne_nil hjm
  set x : Fin m → ℝ := fun i => B i j with hx
  obtain ⟨hv1, hvout, hdich, -, hmul⟩ := houseOn_spec (nodup_indexFrom m j) hne x
  rw [head_indexFrom hjm hne] at hv1 hmul
  simp only [householderQRStep, Id.run_bind, Id.run_pure]
  rw [householderApplyLeft_spec (nodup_indexFrom m j) (nodup_indexFrom n j) hvout]
  generalize Id.run (houseOn pure (indexFrom m ↑j) x) = vβ at hv1 hvout hdich hmul ⊢
  obtain ⟨v, b⟩ := vβ
  dsimp only at hv1 hvout hdich hmul ⊢
  set P : Matrix (Fin m) (Fin m) ℝ := 1 - b • vecMulVec v v with hP
  set C := (qrPrefix j (B, β))ᵀ * A with hC
  have ha' : ∀ (i : Fin m) (q : Fin n), ((i : ℕ) ≤ q ∨ (j : ℕ) ≤ q) → B i q = C i q := ha
  set B' : Matrix (Fin m) (Fin n) ℝ :=
    of fun i q => if q ∈ indexFrom n j then (P * B) i q else B i q with hB'
  set B'' : Matrix (Fin m) (Fin n) ℝ :=
    B'.updateCol j (fun i => if (j : ℕ) < i then v i else B' i j) with hB''
  -- the entries of the new array
  have hBq : ∀ i (q : Fin n), q ≠ j →
      B'' i q = if q ∈ indexFrom n j then (P * B) i q else B i q := fun i q hq => by
    simp only [hB'', hB', updateCol_ne hq, of_apply]
  have hBj : ∀ i, B'' i j = if (j : ℕ) < i then v i else (P * B) i j := fun i => by
    simp only [hB'', hB', updateCol_self, of_apply, mem_indexFrom, le_refl, ite_true]
  -- facts about the old state
  have hvlt : ∀ r : Fin m, (r : ℕ) < j → v r = 0 := fun r hr =>
    hvout r (by rw [mem_indexFrom]; omega)
  have hxC : ∀ i, B i j = C i j := fun i => ha i j (Or.inr le_rfl)
  have hvC : ∀ q : Fin n, (q : ℕ) < j → (v ⬝ᵥ fun r => C r q) = 0 := fun q hq =>
    Finset.sum_eq_zero fun r _ => by
      change v r * C r q = 0
      by_cases hr : (r : ℕ) < j
      · rw [hvlt r hr, zero_mul]
      · rw [hb r q hq (by omega), mul_zero]
  have hPC : ∀ i (q : Fin n), (q : ℕ) < j → (P * C) i q = C i q := fun i q hq => by
    rw [hP, one_sub_smul_vecMulVec_mul_apply, hvC q hq, mul_zero, sub_zero]
  have hcol : ∀ k : Fin n, (k : ℕ) < j → ∀ i, B'' i k = B i k := fun k hk i => by
    have hkj : k ≠ j := fun e => by rw [e] at hk; omega
    have hk' : k ∉ indexFrom n j := by rw [mem_indexFrom]; omega
    rw [hBq i k hkj, ite_eq_right hk']
  have hsvk : ∀ k : Fin n, (k : ℕ) < j →
      storedHouseholderVec B'' k = storedHouseholderVec B k :=
    fun k hk => funext fun i => by simp only [storedHouseholderVec, hcol k hk]
  have hsvj : storedHouseholderVec B'' j = v := funext fun i => by
    simp only [storedHouseholderVec]
    by_cases hij : (i : ℕ) < j
    · rw [ite_eq_left hij, hvlt i hij]
    · rw [ite_eq_right hij]
      by_cases hij' : (i : ℕ) = j
      · rw [ite_eq_left hij']
        have : i = ⟨j, hjm⟩ := Fin.ext hij'
        rw [this, hv1]
      · rw [ite_eq_right hij', hBj, ite_eq_left (by omega)]
  have hQ : qrPrefix (j + 1) (B'', Function.update β j b) = qrPrefix j (B, β) * P := by
    have htake : (List.finRange n).take ((j : ℕ) + 1) = (List.finRange n).take j ++ [j] := by
      rw [List.take_succ_eq_append_getElem (by simp)]
      simp
    rw [qrPrefix, qrPrefix, htake, List.map_append, List.map_cons, List.map_nil,
      householderProduct_concat]
    congr 1
    · congr 1
      refine List.map_congr_left fun k hk => ?_
      have hk' := lt_of_mem_take_finRange hk
      have hkj : k ≠ j := fun e => by rw [e] at hk'; omega
      simp only [hsvk k hk', Function.update_of_ne hkj]
    · simp only [hsvj, Function.update_self]
      exact hP.symm
  have hQT : (qrPrefix (j + 1) (B'', Function.update β j b))ᵀ * A = P * C := by
    rw [hQ, transpose_mul, hP, transpose_one_sub_smul_vecMulVec, Matrix.mul_assoc]
  refine ⟨fun i q hiq => ?_, fun i q hq hqi => ?_, fun k hk => ?_⟩
  · dsimp only
    rw [hQT]
    rcases lt_trichotomy (q : ℕ) j with hqj | hqj | hqj
    · -- a processed column: unchanged, and the reflector fixes it
      have hiq' : (i : ℕ) ≤ q := hiq.resolve_right (by omega)
      rw [hcol q hqj, ha' i q (Or.inl hiq'), hPC i q hqj]
    · -- the current column
      have hq : q = j := Fin.ext hqj
      subst hq
      have hij : ¬ ((q : ℕ) < i) := by
        rcases hiq with h | h
        · omega
        · omega
      rw [hBj, ite_eq_right hij, hP, one_sub_smul_vecMulVec_mul_apply,
        one_sub_smul_vecMulVec_mul_apply]
      simp only [hxC]
    · -- a later column: the reflector applied to the (unchanged) column of `C`
      have hqj' : q ≠ j := fun e => by rw [e] at hqj; omega
      rw [hBq i q hqj', ite_eq_left (by rw [mem_indexFrom]; omega), hP,
        one_sub_smul_vecMulVec_mul_apply, one_sub_smul_vecMulVec_mul_apply]
      have hcq : ∀ r, B r q = C r q := fun r => ha r q (Or.inr (by omega))
      simp only [hcq]
  · rw [hQT]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hqj | hqj
    · rw [hPC i q hqj]
      exact hb i q hqj hqi
    · have hq : q = j := Fin.ext hqj
      subst hq
      have h1 : (P * C) i q = (P *ᵥ x) i := by
        change ((1 - b • vecMulVec v v) *ᵥ fun r => C r q) i = _
        congr 2
        funext r
        exact (hxC r).symm
      rw [h1, hmul]
      have hi1 : i ≠ ⟨q, hjm⟩ := fun e => by rw [e] at hqi; exact lt_irrefl _ hqi
      have hi2 : i ∈ indexFrom m q := by rw [mem_indexFrom]; omega
      simp [hi1, hi2]
  · dsimp only
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hkj | hkj
    · have hkj' : k ≠ j := fun e => by rw [e] at hkj; omega
      simp only [Function.update_of_ne hkj', hsvk k hkj]
      exact hc k hkj
    · have hk' : k = j := Fin.ext hkj
      subst hk'
      simp only [Function.update_self, hsvj]
      exact hdich

/-- **Algorithm 5.2.1 computes a QR factorization** (exact arithmetic, `m ≥ n`): with
`(A', β) = Id.run (algorithm_5_2_1 pure A)`, the factored form `Q = H₁ ⋯ H_n` of the stored
Householder vectors and the returned `β_j` (convention 13) and the upper triangular part `R` of
the output satisfy `A = QR` with `Q` orthogonal — "`QᵀA = R` is upper triangular" — and every
`β_j` is `0` or `2/v⁽ʲ⁾ᵀv⁽ʲ⁾` (each `H_j` is the identity or the Householder matrix of `v⁽ʲ⁾`). -/
theorem algorithm_5_2_1_spec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    IsQR A (factoredQ (Id.run (algorithm_5_2_1 pure A)).2 (Id.run (algorithm_5_2_1 pure A)).1)
        (upperPart (Id.run (algorithm_5_2_1 pure A)).1) ∧
      ∀ j, (Id.run (algorithm_5_2_1 pure A)).2 j = 0 ∨
        (Id.run (algorithm_5_2_1 pure A)).2 j *
          (storedHouseholderVec (Id.run (algorithm_5_2_1 pure A)).1 j ⬝ᵥ
            storedHouseholderVec (Id.run (algorithm_5_2_1 pure A)).1 j) = 2 := by
  set f := fun st j => Id.run (householderQRStep (m := m) (n := n) pure st j) with hf
  have hprog : Id.run (algorithm_5_2_1 pure A) = (List.finRange n).foldl f (A, 0) := by
    rw [algorithm_5_2_1, List.idRun_foldlM]
  have hall : ∀ j ≤ n, qrInvariant A j (((List.finRange n).take j).foldl f (A, 0)) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun i q _ => ?_, fun i q hq => absurd hq (Nat.not_lt_zero _),
        fun k hk => absurd hk (Nat.not_lt_zero _)⟩
      simp [qrPrefix]
    | succ j ih =>
      intro hj
      rw [List.take_succ_eq_append_getElem (by simpa using hj), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have h := qrInvariant_step hnm A _ _ ⟨j, by omega⟩ (ih (by omega))
      simpa [hf] using h
  have hn := hall n le_rfl
  rw [List.take_of_length_le (by simp), ← hprog] at hn
  generalize Id.run (algorithm_5_2_1 pure A) = st at hn ⊢
  obtain ⟨B, β⟩ := st
  obtain ⟨ha, hb, hc⟩ := hn
  have hQeq : qrPrefix n (B, β) = factoredQ β B := by
    rw [qrPrefix, List.take_of_length_le (by simp), factoredQ, storedReflectors,
      List.ofFn_eq_map]
  rw [hQeq] at ha hb
  simp only at ha hb hc ⊢
  have hdich : ∀ j : Fin n, β j = 0 ∨ β j * (storedHouseholderVec B j ⬝ᵥ
      storedHouseholderVec B j) = 2 := fun j => hc j j.isLt
  have hO : factoredQ β B ∈ orthogonalGroup (Fin m) ℝ := by
    refine householderProduct_mem_orthogonalGroup fun p hp => ?_
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
    exact hdich k
  have hR : (factoredQ β B)ᵀ * A = upperPart B := by
    ext i q
    rw [upperPart, of_apply]
    split_ifs with hiq
    · exact (ha i q (Or.inl hiq)).symm
    · exact hb i q q.isLt (by omega)
  refine ⟨⟨hO, fun i q hqi => ?_, ?_⟩, hdich⟩
  · simp [upperPart, show ¬ ((i : ℕ) ≤ q) by omega]
  · rw [← hR, mul_transpose_mul_of_mem_orthogonalGroup hO]

/-- **The retrieval formula `β_j = 2/(1 + ‖A(j+1:m, j)‖²)`** (after (5.1.4) and after
Algorithm 5.2.1), in its correct form: for the exact output `(A', β)` of Algorithm 5.2.1, every
nonzero `β_j` is the recomputed `2/v⁽ʲ⁾ᵀv⁽ʲ⁾`; `β_j = 0` exactly when `house` met `σ = 0` and
`x₁ ≥ 0`, where the book's formula yields `2`. Hence, when no `β_j` is zero, the factored form
built with the recomputed `β` is the factorization's `Q`. -/
theorem equation_5_1_4_beta (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ j, (Id.run (algorithm_5_2_1 pure A)).2 j ≠ 0 →
      (Id.run (algorithm_5_2_1 pure A)).2 j =
        recomputedBeta (Id.run (algorithm_5_2_1 pure A)).1 j) ∧
      ((∀ j, (Id.run (algorithm_5_2_1 pure A)).2 j ≠ 0) →
        factoredQ (Id.run (algorithm_5_2_1 pure A)).2 (Id.run (algorithm_5_2_1 pure A)).1 =
          factoredQ (recomputedBeta (Id.run (algorithm_5_2_1 pure A)).1)
            (Id.run (algorithm_5_2_1 pure A)).1) := by
  have hdich := (algorithm_5_2_1_spec hnm A).2
  generalize Id.run (algorithm_5_2_1 pure A) = st at hdich ⊢
  obtain ⟨B, β⟩ := st
  simp only at hdich ⊢
  have key : ∀ j, β j ≠ 0 → β j = recomputedBeta B j := fun j hj => by
    have h2 := (hdich j).resolve_left hj
    have hvv : storedHouseholderVec B j ⬝ᵥ storedHouseholderVec B j ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h2; norm_num at h2
    rw [recomputedBeta, eq_div_iff hvv, h2]
  refine ⟨key, fun h => ?_⟩
  rw [factoredQ_eq_prod, factoredQ_eq_prod]
  congr 1
  exact List.map_congr_left fun j _ => by rw [key j (h j)]


/-! ### The backward error of Householder QR -/

section Rounding

/-- The computed `R⁽ᵏ⁾` of Algorithm 5.2.1: the array after `k` steps with the stored Householder
vectors (below the diagonal of the first `k` columns) replaced by zeros. -/
def householderQRPartialR (k : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun i q => if (q : ℕ) < k ∧ (q : ℕ) < i then 0 else B i q

/-- **One computed step of Householder QR, with its reflector data** (what the `b`-loop of
Algorithm 5.3.2 needs besides the backward error): for every run of
step `k` there are exact data `(v, β)` with `P = 1 - β v vᵀ` orthogonal, `|β| vᵀv ≤ 2` and `v`
vanishing above row `k`, such that the stored vector of column `k` is entrywise a relative
perturbation of order `18m + 31` of `v` and the returned `β̂_k` one of `β`; the columns before `k`
and the other `β̂_q` are untouched; and `‖(R⁽ᵏ⁺¹⁾ - P R⁽ᵏ⁾)(:, q)‖₂ ≤ ε ‖R⁽ᵏ⁾(:, q)‖₂`,
`ε = 3 γ_{3(18m + 31) + m + 3}`, for the arrays `R⁽ᵏ⁾` with the stored vectors zeroed. -/
theorem householderQRStep_rounding_data {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hnm : n ≤ m) (hu : ((3 * (18 * m + 31) + m + 3 : ℕ) : ℝ) * fp.u < 1)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) (k : Fin n)
    {st' : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)}
    (h : st' ∈ (householderQRStep fp.round st k).run) :
    ∃ (v : Fin m → ℝ) (β : ℝ), 1 - β • vecMulVec v v ∈ orthogonalGroup (Fin m) ℝ ∧
      |β| * (v ⬝ᵥ v) ≤ 2 ∧ (∀ i, i ∉ indexFrom m k → v i = 0) ∧
      (∀ i, IsRelPert fp.u (18 * m + 31) (v i) (storedHouseholderVec st'.1 k i)) ∧
      IsRelPert fp.u (18 * m + 31) β (st'.2 k) ∧
      (∀ i (q : Fin n), (q : ℕ) < k → st'.1 i q = st.1 i q) ∧
      (∀ q, q ≠ k → st'.2 q = st.2 q) ∧
      ∀ q : Fin n,
        ‖(toLp 2 ((householderQRPartialR ((k : ℕ) + 1) st'.1 -
            (1 - β • vecMulVec v v) * householderQRPartialR k st.1).col q) :
            EuclideanSpace ℝ (Fin m))‖ ≤
          3 * gamma fp.u (3 * (18 * m + 31) + m + 3) *
            ‖(toLp 2 ((householderQRPartialR k st.1).col q) : EuclideanSpace ℝ (Fin m))‖ := by
  obtain ⟨B, β⟩ := st
  have hjm : (k : ℕ) < m := lt_of_lt_of_le k.isLt hnm
  have hne := indexFrom_ne_nil hjm
  have hnd := nodup_indexFrom m k
  have hhead := head_indexFrom hjm hne
  set o := indexFrom m k with ho
  have hlen : o.length ≤ m := (List.length_filter_le _ _).trans (by simp)
  have hu0 := fp.u_nonneg
  have hle : ∀ a : ℕ, a ≤ 3 * (18 * m + 31) + m + 3 → (a : ℝ) * fp.u < 1 := fun a ha =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 ha) hu0).trans_lt hu
  simp only [householderQRStep, SetM.mem_run_bind, SetM.mem_run_pure] at h
  obtain ⟨vβ, hvβ, B', hB', rfl⟩ := h
  set x : Fin m → ℝ := fun i => B i k with hx
  obtain ⟨hvout, v, bb, hO, hmul, hbv, hbb, hv⟩ :=
    houseOn_rounding hfp hnd hne (hle _ (by omega)) x hvβ
  have hpiv : vβ.1 (o.head hne) = 1 := by
    obtain ⟨-, σhat, -, hvi, -⟩ := houseOn_rounds hfp hnd hne x hvβ
    exact hvi
  set K := 18 * o.length + 31 with hK
  -- the exact vector, extended by zero off `o`
  set v' : Fin m → ℝ := fun i => if h : i ∈ o then v ⟨i, h⟩ else 0 with hv'
  have hv'o : (fun i : {i // i ∈ o} => v' i) = v := funext fun i => by simp [hv', i.2]
  have hv'out : ∀ i, i ∉ o → v' i = 0 := fun i hi => by simp [hv', hi]
  have hvv' : ∀ i, IsRelPert fp.u K (v' i) (vβ.1 i) := fun i => by
    by_cases hi : i ∈ o
    · have := hv ⟨i, hi⟩
      simpa [hv', hi] using this
    · rw [hv'out i hi, hvout i hi]
      exact ⟨0, by simpa using gamma_nonneg hu0 (hle K (by omega)), by ring⟩
  have hdot' : v' ⬝ᵥ v' = v ⬝ᵥ v := by rw [dotProduct_eq_dotProduct_subtype o hv'out, hv'o]
  have hP2 : |bb| * (v' ⬝ᵥ v') ≤ 2 := by rwa [hdot']
  obtain ⟨hBout, hcolb, -⟩ := householderApplyLeft_rounding hfp hnd (nodup_indexFrom n k)
    (K := K) (hle _ (by omega)) hbb hvv' hv'out hP2 B hB'
  simp only [hv'o] at hcolb
  have hε : 3 * gamma fp.u (3 * K + o.length + 3) ≤ 3 * gamma fp.u (3 * (18 * m + 31) + m + 3) :=
    mul_le_mul_of_nonneg_left (gamma_mono hu0 (by omega) hu) (by norm_num)
  have hε0 : 0 ≤ 3 * gamma fp.u (3 * (18 * m + 31) + m + 3) := by
    have := gamma_nonneg hu0 hu; positivity
  -- the exact reflector on `ℝ^m`
  set P : Matrix (Fin m) (Fin m) ℝ := 1 - bb • vecMulVec v' v' with hP
  have hPO : P ∈ orthogonalGroup (Fin m) ℝ := by
    by_cases hv0 : v = 0
    · have : v' = 0 := funext fun i => by simp [hv', hv0]
      rw [hP, this, vecMulVec_zero, smul_zero, sub_zero]
      exact one_mem _
    · obtain ⟨p, hp⟩ := Function.ne_iff.1 hv0
      refine one_sub_smul_vecMulVec_mem_orthogonalGroup ?_
      rw [hdot']
      exact beta_mul_eq_zero_of_mem_orthogonalGroup hp hO
  set B'' := B'.updateCol k fun i => if (k : ℕ) < i then vβ.1 i else B' i k with hB''
  have hB''q : ∀ i (q : Fin n), q ≠ k → B'' i q = B' i q := fun i q hq => by
    simp only [hB'', updateCol_ne hq]
  have hB''k : ∀ i, B'' i k = if (k : ℕ) < i then vβ.1 i else B' i k := fun i => by
    simp only [hB'', updateCol_self]
  refine ⟨v', bb, hPO, hP2, hv'out, fun i => ?_, ?_, fun i q hq => ?_, fun q hq => ?_,
    fun q => ?_⟩
  · -- the stored vector
    refine IsRelPert.mono hu0 (by omega) (hle _ (by omega)) (m := K) ?_
    simp only [storedHouseholderVec]
    rcases lt_trichotomy (i : ℕ) k with hik | hik | hik
    · rw [ite_eq_left hik, hv'out i (by rw [ho, mem_indexFrom]; omega)]
      exact IsRelPert.zero (gamma_nonneg hu0 (hle K (by omega)))
    · rw [ite_eq_right (by omega), ite_eq_left hik]
      have hh : ((o.head hne : Fin m) : ℕ) = k := congrArg Fin.val (head_indexFrom hjm hne)
      have h1 : vβ.1 i = 1 := by
        rw [show i = o.head hne from Fin.ext (hik.trans hh.symm)]
        exact hpiv
      have := hvv' i
      rwa [h1] at this
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), hB''k, ite_eq_left hik]
      exact hvv' i
  · simp only [Function.update_self]
    exact hbb.mono hu0 (by omega) (hle _ (by omega))
  · have hqk : q ≠ k := fun e => by rw [e] at hq; exact lt_irrefl _ hq
    change B'' i q = B i q
    rw [hB''q i q hqk]
    exact hBout i q (Or.inr (by rw [mem_indexFrom]; omega))
  · exact Function.update_of_ne hq _ _
  dsimp only
  set R := householderQRPartialR k B with hR
  set R' := householderQRPartialR ((k : ℕ) + 1) B'' with hR'
  have hRe : ∀ i (q : Fin n), R i q = if (q : ℕ) < k ∧ (q : ℕ) < i then 0 else B i q :=
    fun _ _ => rfl
  have hR'e : ∀ i (q : Fin n),
      R' i q = if (q : ℕ) < (k : ℕ) + 1 ∧ (q : ℕ) < i then 0 else B'' i q := fun _ _ => rfl
  have hPR : ∀ i, (P * R) i q = (P *ᵥ fun r => R r q) i := fun i => rfl
  rcases lt_or_ge (q : ℕ) k with hqk | hqk
  · -- a processed column is unchanged, and fixed by the reflector
    have hqk' : q ≠ k := fun e => by rw [e] at hqk; omega
    have hq' : q ∉ indexFrom n k := by rw [mem_indexFrom]; omega
    have hdot0 : (v' ⬝ᵥ fun r => R r q) = 0 := Finset.sum_eq_zero fun r _ => by
      change v' r * R r q = 0
      by_cases hr : r ∈ o
      · have hr' : (k : ℕ) ≤ r := mem_indexFrom.1 hr
        rw [hRe, ite_eq_left ⟨hqk, by omega⟩, mul_zero]
      · rw [hv'out r hr, zero_mul]
    have hzero : (R' - P * R).col q = 0 := funext fun i => by
      change R' i q - (P * R) i q = 0
      rw [hPR, one_sub_smul_vecMulVec_mulVec_apply, hdot0, mul_zero, sub_zero]
      by_cases hqi : (q : ℕ) < i
      · rw [hR'e, ite_eq_left ⟨by omega, hqi⟩, hRe, ite_eq_left ⟨hqk, hqi⟩, sub_self]
      · rw [hR'e, ite_eq_right (by omega), hRe, ite_eq_right (by omega), hB''q i q hqk',
          hBout i q (Or.inr hq'), sub_self]
    rw [hzero, toLp_zero, norm_zero]
    exact mul_nonneg hε0 (norm_nonneg _)
  · -- a column of the current block
    have hq : q ∈ indexFrom n k := mem_indexFrom.2 hqk
    have hRcol : ∀ r, R r q = B r q := fun r => by
      rw [hRe, ite_eq_right (by omega)]
    set e : {i // i ∈ o} → ℝ :=
      (B'.submatrix (Subtype.val : {i // i ∈ o} → Fin m)
          (Subtype.val : {q // q ∈ indexFrom n k} → Fin n) -
        (1 - bb • vecMulVec v v) * B.submatrix Subtype.val Subtype.val).col ⟨q, hq⟩ with he
    have hPx : ∀ i (hi : i ∈ o), (P *ᵥ fun r => R r q) i =
        ((1 - bb • vecMulVec v v) *ᵥ fun r : {r // r ∈ o} => B r q) ⟨i, hi⟩ := fun i hi => by
      rw [hP, one_sub_smul_vecMulVec_mulVec_apply_subtype o hv'out, dite_eq_left hi, hv'o]
      simp only [hRcol]
    set D := (R' - P * R).col q with hD
    have hDout : ∀ i, i ∉ o → D i = 0 := fun i hi => by
      have hik : (i : ℕ) < k := by rw [ho, mem_indexFrom] at hi; omega
      have h1 : (P * R) i q = B i q := by
        rw [hPR, hP, one_sub_smul_vecMulVec_mulVec_apply, hv'out i hi, mul_zero, zero_mul,
          sub_zero, hRcol]
      have h2 : R' i q = B i q := by
        rw [hR'e, ite_eq_right (by omega)]
        by_cases h : q = k
        · subst h
          rw [hB''k, ite_eq_right (by omega)]
          exact hBout i _ (Or.inl hi)
        · rw [hB''q i q h]
          exact hBout i q (Or.inl hi)
      change R' i q - (P * R) i q = 0
      rw [h1, h2, sub_self]
    have hDin : ∀ i (hi : i ∈ o), |D i| ≤ |e ⟨i, hi⟩| := fun i hi => by
      have hki : (k : ℕ) ≤ i := mem_indexFrom.1 hi
      have heq : e ⟨i, hi⟩ = B' i q - ((1 - bb • vecMulVec v v) *ᵥ
          fun r : {r // r ∈ o} => B r q) ⟨i, hi⟩ := rfl
      change |R' i q - (P * R) i q| ≤ _
      rw [hPR, hPx i hi]
      by_cases hqk' : q = k
      · subst hqk'
        by_cases hik : (q : ℕ) < i
        · -- below the diagonal of the current column: both sides vanish
          have hne' : (⟨i, hi⟩ : {r // r ∈ o}) ≠ ⟨o.head hne, List.head_mem hne⟩ :=
            fun h => by
              have := congrArg (fun r : {r // r ∈ o} => (r.1 : ℕ)) h
              have hh : ((o.head hne : Fin m) : ℕ) = q := by
                have := congrArg Fin.val hhead
                simpa only [Fin.val_mk] using this
              simp only at this
              omega
          have hx0 : ((1 - bb • vecMulVec v v) *ᵥ fun r : {r // r ∈ o} => B r q) ⟨i, hi⟩ =
              0 := by
            refine (congrFun hmul ⟨i, hi⟩).trans ?_
            simp [Pi.single_eq_of_ne hne']
          rw [hR'e, ite_eq_left ⟨by omega, hik⟩, hx0, sub_zero, abs_zero]
          exact abs_nonneg _
        · rw [hR'e, ite_eq_right (by omega), hB''k, ite_eq_right hik, heq]
      · rw [hR'e, ite_eq_right (by omega), hB''q i q hqk', heq]
    have hBsub := norm_toLp_restrict_le (p := (· ∈ o)) (fun r => B r q)
    have hRc : R.col q = fun r => B r q := funext hRcol
    calc ‖(toLp 2 D : EuclideanSpace ℝ (Fin m))‖
        = ‖(toLp 2 (fun i : {i // i ∈ o} => D i) : EuclideanSpace ℝ {i // i ∈ o})‖ :=
          norm_toLp_eq_restrict (p := (· ∈ o)) hDout
      _ ≤ ‖(toLp 2 e : EuclideanSpace ℝ {i // i ∈ o})‖ :=
          norm_toLp_le_of_abs_le fun i => hDin i i.2
      _ ≤ 3 * gamma fp.u (3 * K + o.length + 3) *
          ‖(toLp 2 (fun r : {r // r ∈ o} => B r q) : EuclideanSpace ℝ {i // i ∈ o})‖ :=
          hcolb ⟨q, hq⟩
      _ ≤ 3 * gamma fp.u (3 * (18 * m + 31) + m + 3) *
          ‖(toLp 2 (R.col q) : EuclideanSpace ℝ (Fin m))‖ := by
          rw [hRc]
          exact mul_le_mul hε hBsub (norm_nonneg _) hε0

/-- The exact reflectors `1 - β_j v_j v_jᵀ` of reflector data `(v, β)`. -/
noncomputable def dataReflector (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (j : ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  1 - β j • vecMulVec (v j) (v j)

/-- What the `b`-loop of Algorithm 5.3.2 needs of step `q` of Algorithm 5.2.1: the exact data
`(v, β)` of the step's reflector against the array `st` (its stored vector of column `q` and its
returned `β̂_q`). -/
def IsStepData (u : ℝ) (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) (q : Fin n)
    (v : Fin m → ℝ) (β : ℝ) : Prop :=
  |β| * (v ⬝ᵥ v) ≤ 2 ∧ (∀ i, i ∉ indexFrom m q → v i = 0) ∧
    (∀ i, IsRelPert u (18 * m + 31) (v i) (storedHouseholderVec st.1 q i)) ∧
    IsRelPert u (18 * m + 31) β (st.2 q)

/-- **Algorithm 5.2.1's backward error with the reflector data** (the form of
`algorithm_5_2_1_rounding` keeping the reflectors): every run `(A', β̂)` has exact data `(v_j, β_j)`
for every step, with `P_j = 1 - β_j v_j v_jᵀ` orthogonal, such that
`R̂ = upperPart A' = P_{n-1} ⋯ P_0 (A + E)` with columnwise
`‖E(:, q)‖₂ ≤ ((1 + ε)ⁿ - 1) ‖A(:, q)‖₂`, `ε = 3 γ_{3(18m + 31) + m + 3}`. -/
theorem algorithm_5_2_1_rounding_data {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent)
    (hnm : n ≤ m) (hu : ((3 * (18 * m + 31) + m + 3 : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin m) (Fin n) ℝ) {st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)}
    (h : st ∈ (algorithm_5_2_1 fp.round A).run) :
    ∃ (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (E : Matrix (Fin m) (Fin n) ℝ),
      (∀ j, dataReflector v β j ∈ orthogonalGroup (Fin m) ℝ) ∧
      (∀ q : Fin n, IsStepData fp.u st q (v q) (β q)) ∧
      upperPart st.1 = prodRev (dataReflector v β) n * (A + E) ∧
      ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin m))‖ ≤
        ((1 + 3 * gamma fp.u (3 * (18 * m + 31) + m + 3)) ^ n - 1) *
          ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin m))‖ := by
  set ε := 3 * gamma fp.u (3 * (18 * m + 31) + m + 3) with hε
  have hε0 : 0 ≤ ε := by have := gamma_nonneg fp.u_nonneg hu; positivity
  set I : ℕ → Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) → Prop := fun k st =>
    ∃ (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (E : Matrix (Fin m) (Fin n) ℝ),
      (∀ j, dataReflector v β j ∈ orthogonalGroup (Fin m) ℝ) ∧
      (∀ q : Fin n, (q : ℕ) < k → IsStepData fp.u st q (v q) (β q)) ∧
      householderQRPartialR k st.1 = prodRev (dataReflector v β) k * (A + E) ∧
      ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin m))‖ ≤
        ((1 + ε) ^ k - 1) * ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin m))‖ with hI
  have h0 : I 0 (A, 0) := by
    refine ⟨fun _ => 0, fun _ => 0, 0, fun j => ?_, fun q hq => absurd hq (Nat.not_lt_zero _),
      ?_, fun q => ?_⟩
    · simp only [dataReflector, vecMulVec_zero, smul_zero, sub_zero]
      exact one_mem _
    · ext i q
      simp [householderQRPartialR]
    · rw [show (0 : Matrix (Fin m) (Fin n) ℝ).col q = 0 from rfl]
      simp
  have hstep : ∀ (k : Fin n) (c : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)), I k c →
      ∀ c' ∈ (householderQRStep fp.round c k).run, I ((k : ℕ) + 1) c' := by
    rintro k c ⟨v, β, E, hO, hdata, hE, hEb⟩ c' hc'
    obtain ⟨w, γ, hwO, hw2, hwout, hwrel, hγrel, hcols, hβs, hFb⟩ :=
      householderQRStep_rounding_data hfp hnm hu c k hc'
    set v' : ℕ → Fin m → ℝ := fun j => if j = k then w else v j with hv'
    set β' : ℕ → ℝ := fun j => if j = k then γ else β j with hβ'
    have hrefl : ∀ j, dataReflector v' β' j =
        if j = k then 1 - γ • vecMulVec w w else dataReflector v β j := fun j => by
      simp only [dataReflector, hv', hβ']
      split_ifs <;> rfl
    have hO' : ∀ j, dataReflector v' β' j ∈ orthogonalGroup (Fin m) ℝ := fun j => by
      rw [hrefl]
      split_ifs
      · exact hwO
      · exact hO j
    have hW : prodRev (dataReflector v' β') k = prodRev (dataReflector v β) k :=
      prodRev_congr fun j hj => by rw [hrefl, ite_eq_right (show ¬ j = (k : ℕ) by omega)]
    set W := prodRev (dataReflector v' β') ((k : ℕ) + 1) with hWdef
    have hWk : W = (1 - γ • vecMulVec w w) * prodRev (dataReflector v β) k := by
      rw [hWdef, prodRev_succ, hW, hrefl, ite_eq_left rfl]
    -- Lemma 19.3, one step (`FloatingPoint.exists_eq_mul_add_of_step`)
    obtain ⟨E', hE'eq, hE'b⟩ := exists_eq_mul_add_of_step hwO
      (prodRev_mem_orthogonalGroup fun k _ => hO k) hε0 hE hEb hFb
    refine ⟨v', β', E', hO', fun q hq => ?_, ?_, hE'b⟩
    · -- the step data
      by_cases hqk : (q : ℕ) = k
      · have hq' : q = k := Fin.ext hqk
        subst hq'
        simp only [hv', hβ', ite_true]
        exact ⟨hw2, hwout, hwrel, hγrel⟩
      · have hq2 : (q : ℕ) < k := by omega
        have hqk' : q ≠ k := fun e => hqk (by rw [e])
        obtain ⟨h1, h2, h3, h4⟩ := hdata q hq2
        simp only [hv', hβ', hqk, ↓reduceIte]
        refine ⟨h1, h2, fun i => ?_, by rwa [hβs q hqk']⟩
        have hst : storedHouseholderVec c'.1 q = storedHouseholderVec c.1 q := by
          funext i
          simp only [storedHouseholderVec, hcols i q hq2]
        rw [hst]
        exact h3 i
    · rw [hE'eq, ← hWk]
  obtain ⟨v, β, E, hO, hdata, hE, hEb⟩ := SetM.forall_mem_run_foldlM_finRange I h0 hstep st h
  refine ⟨v, β, E, hO, fun q => hdata q q.isLt, ?_, hEb⟩
  have hup : householderQRPartialR n st.1 = upperPart st.1 := by
    ext i q
    have := q.isLt
    simp only [householderQRPartialR, upperPart, of_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  rwa [hup] at hE

/-- **§5.2.2, "the computed upper triangular matrix `R̂` is the exact `R` for a nearby `A`"**,
rigorous: over an idempotent model with `(3(18m + 31) + m + 3) u < 1`, every run `(A', β̂)` of
Algorithm 5.2.1 (`m ≥ n`) has an orthogonal `Z` (the product of the exact reflectors of the
*computed* columns) and an `E` with `Z R̂ = A + E` for `R̂ = upperPart A'`, and columnwise
`‖E(:, q)‖₂ ≤ ((1 + ε)ⁿ - 1) ‖A(:, q)‖₂`, `ε = 3 γ_{3(18m + 31) + m + 3}` — the book's
"`Zᵀ(A + E) = R̂`, `‖E‖₂ ≈ u‖A‖₂`" with the constants of the relational calculus
(`(1 + ε)ⁿ - 1 ≤ γ_n(ε)` by `FloatingPoint.one_add_pow_sub_one_le_gamma`). The discarded
subdiagonal entries of each processed column are part of `E`. -/
theorem algorithm_5_2_1_rounding {fp : RoundingModel ℝ} (hfp : fp.IsIdempotent) (hnm : n ≤ m)
    (hu : ((3 * (18 * m + 31) + m + 3 : ℕ) : ℝ) * fp.u < 1) (A : Matrix (Fin m) (Fin n) ℝ)
    {st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)} (h : st ∈ (algorithm_5_2_1 fp.round A).run) :
    ∃ Z ∈ orthogonalGroup (Fin m) ℝ, ∃ E : Matrix (Fin m) (Fin n) ℝ,
      Z * upperPart st.1 = A + E ∧ ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin m))‖ ≤
        ((1 + 3 * gamma fp.u (3 * (18 * m + 31) + m + 3)) ^ n - 1) *
          ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin m))‖ := by
  obtain ⟨v, β, E, hO, -, hE, hEb⟩ := algorithm_5_2_1_rounding_data hfp hnm hu A h
  have hW := prodRev_mem_orthogonalGroup (r := n) fun k _ => hO k
  refine ⟨(prodRev (dataReflector v β) n)ᵀ, transpose_mem_unitaryGroup_iff.2 hW, E, ?_, hEb⟩
  rw [hE, ← Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ _).1 hW, Matrix.one_mul]

end Rounding

end Householder

/-! ### §5.2.5 Givens QR methods -/

section Givens

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The row above `i`, `i - 1` (for `i = 0` it is `0`; the programs only use it for `i ≥ 1`). -/
def rowAbove (i : Fin m) : Fin m := ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- **Algorithm 5.2.4 (Givens QR)**: "Given `A ∈ ℝ^{m×n}` with `m ≥ n`, the following algorithm
overwrites `A` with `QᵀA = R`, where `R` is upper triangular and `Q` is orthogonal":
```
for j = 1:n
    for i = m:-1:j+1
        [c, s] = givens(A(i-1, j), A(i, j))
        A(i-1:i, j:n) = [c s; -s c]ᵀ A(i-1:i, j:n)
    end
end
```
-/
noncomputable def algorithm_5_2_4 (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
    ((List.finRange m).filter (fun i : Fin m => (j : ℕ) < i)).reverse.foldlM
      (fun (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) => do
        let cs ← algorithm_5_1_3 rnd (A (rowAbove i) j) (A i j)
        givensApplyLeft rnd (rowAbove i) i cs.1 cs.2 (indexFrom n j) A) A) A

/-- **§5.2.5, the first reordering**: Algorithm 5.2.4 with the inner loop body replaced by
`[c, s] = givens(A(j, j), A(i, j))`, `A([j i], j:n) = [c s; -s c]ᵀ A([j i], j:n)` (rotations in
the planes `(j, i)`), "and still emerge with the QR factorization". -/
noncomputable def givensQRDiagonalPivot (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
    ((List.finRange m).filter (fun i : Fin m => (j : ℕ) < i)).reverse.foldlM
      (fun (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) => do
        let jj : Fin m := Fin.castLE hnm j
        let cs ← algorithm_5_1_3 rnd (A jj j) (A i j)
        givensApplyLeft rnd jj i cs.1 cs.2 (indexFrom n j) A) A) A

/-- **§5.2.5, the second reordering**, introducing the zeros by row:
```
for i = 2:m
    for j = 1:i-1
        [c, s] = givens(A(j, j), A(i, j))
        A([j i], j:n) = [c s; -s c]ᵀ A([j i], j:n)
    end
end
```
(the columns `j` range over `j < min(i, n)`). -/
noncomputable def givensQRByRow (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ) :=
  (List.finRange m).foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) =>
    ((List.finRange n).filter (fun j : Fin n => (j : ℕ) < i)).foldlM
      (fun (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) => do
        let jj : Fin m := Fin.castLE hnm j
        let cs ← algorithm_5_1_3 rnd (A jj j) (A i j)
        givensApplyLeft rnd jj i cs.1 cs.2 (indexFrom n j) A) A) A

/-- **Algorithm 5.2.5 (Hessenberg QR)**: "If `A ∈ ℝ^{n×n}` is upper Hessenberg, then the following
algorithm overwrites `A` with `QᵀA = R` where `Q` is orthogonal and `R` is upper triangular.
`Q = G₁ ⋯ G_{n-1}` is a product of Givens rotations where `G_j = G(j, j+1, θ_j)`":
```
for j = 1:n-1
    [c, s] = givens(A(j, j), A(j+1, j))
    A(j:j+1, j:n) = [c s; -s c]ᵀ A(j:j+1, j:n)
end
```
With `n = k + 1`; the program also returns the pairs `(c_j, s_j)`. -/
noncomputable def algorithm_5_2_5 {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    M (Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin k → ℝ × ℝ)) :=
  (List.finRange k).foldlM
    (fun (st : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin k → ℝ × ℝ)) (j : Fin k) => do
      let cs ← algorithm_5_1_3 rnd (st.1 j.castSucc j.castSucc) (st.1 j.succ j.castSucc)
      let A ← givensApplyLeft rnd j.castSucc j.succ cs.1 cs.2 (indexFrom (k + 1) j) st.1
      pure (A, Function.update st.2 j cs)) (A, fun _ => (1, 0))

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
        let cs ← algorithm_5_1_3 rnd (st.2 ⟨j, by omega⟩ ⟨j, h.2⟩)
          (st.2 ⟨j + 1, h.1⟩ ⟨j, h.2⟩)
        let H ← givensApplyLeft rnd ⟨j, by omega⟩ ⟨j + 1, h.1⟩ cs.1 cs.2
          (List.finRange n) st.2
        let Q ← givensApplyRight rnd ⟨j, by omega⟩ ⟨j + 1, h.1⟩ cs.1 cs.2
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
        let cs ← algorithm_5_1_3 rnd (st.1 ⟨j, by omega⟩) (st.1 ⟨j + 1, h⟩)
        let w ← givensRotateVec rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2 st.1
        let R ← givensApplyLeft rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2
          (List.finRange n) st.2.2
        let Q ← givensApplyRight rnd ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2
          (List.finRange m) st.2.1
        pure (w, Q, R)
      else pure st) (w, Q, R)

end Programs

/-! ### §5.2.5–5.2.6 Givens QR: exact semantics -/

section GivensQRSpec

/-- The entries of `G(p, i, θ)ᵀ B`: rows `p` and `i` rotated, the others kept. -/
theorem givensRotation_transpose_mul_apply {p i : Fin m} (hpi : p ≠ i) (c s : ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (q : Fin n) :
    ((givensRotation p i c s)ᵀ * B) r q =
      if r = p then c * B p q - s * B i q else if r = i then s * B p q + c * B i q else B r q := by
  change ((givensRotation p i c s)ᵀ *ᵥ fun t => B t q) r = _
  rw [givensRotation_transpose_mulVec_apply hpi]

/-- The entries of `A G(i, k, θ)`: only the columns `i`, `k` change. -/
theorem mul_givensRotation_apply {p : ℕ} {i k : Fin n} (hik : i ≠ k) (c s : ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (r : Fin p) (q : Fin n) :
    (A * givensRotation i k c s) r q =
      if q = i then c * A r i - s * A r k else if q = k then s * A r i + c * A r k
        else A r q := by
  have h : (A * givensRotation i k c s) r q = ((givensRotation i k c s)ᵀ *ᵥ A r) q := by
    rw [mulVec_transpose]; rfl
  rw [h, givensRotation_transpose_mulVec_apply hik]

/-- One exact step of the Givens QR algorithms: `[c, s] = givens(B(p, j), B(i, j))`, then the
rows `p, i` of `B` rotated on the columns `j:n`. -/
noncomputable def givensStepExact (p i : Fin m) (j : Fin n) (B : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  Id.run (givensApplyLeft pure p i (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).1
    (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).2 (indexFrom n j) B)

/-- **One exact Givens step**: if the rows `p ≠ i` vanish in the columns `< j`, the step is the
full rotation `G(p, i, θ)ᵀ B` by the computed `(c, s)` (with `c² + s² = 1`), it zeroes `B(i, j)`,
and it keeps the rows other than `p, i` and the columns `< j`. -/
theorem givensStepExact_spec {p i : Fin m} (hpi : p ≠ i) (j : Fin n)
    (B : Matrix (Fin m) (Fin n) ℝ) (hz : ∀ q : Fin n, (q : ℕ) < j → B p q = 0 ∧ B i q = 0) :
    (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).1 ^ 2 +
        (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).2 ^ 2 = 1 ∧
      givensStepExact p i j B = (givensRotation p i (Id.run (algorithm_5_1_3 pure (B p j)
        (B i j))).1 (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).2)ᵀ * B ∧
      givensStepExact p i j B i j = 0 ∧
      (∀ r q, r ≠ p → r ≠ i → givensStepExact p i j B r q = B r q) ∧
      (∀ r (q : Fin n), (q : ℕ) < j → givensStepExact p i j B r q = B r q) := by
  obtain ⟨hcs, hz0, -⟩ := algorithm_5_1_3_spec (B p j) (B i j)
  set c := (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).1 with hc
  set s := (Id.run (algorithm_5_1_3 pure (B p j) (B i j))).2 with hs
  have hdef : givensStepExact p i j B = Id.run (givensApplyLeft pure p i c s (indexFrom n j) B) :=
    rfl
  have hleft : ∀ r (q : Fin n), (q : ℕ) < j → ((givensRotation p i c s)ᵀ * B) r q = B r q := by
    intro r q hq
    obtain ⟨h1, h2⟩ := hz q hq
    rw [givensRotation_transpose_mul_apply hpi]
    split_ifs with hr1 hr2
    · rw [hr1, h1, h2]; ring
    · rw [hr2, h1, h2]; ring
    · rfl
  have hG : givensStepExact p i j B = (givensRotation p i c s)ᵀ * B := by
    rw [hdef, givensApplyLeft_spec hpi c s (nodup_indexFrom n j)]
    ext r q
    rw [of_apply]
    split_ifs with hq
    · rfl
    · rw [mem_indexFrom, not_le] at hq
      exact (hleft r q hq).symm
  refine ⟨hcs, hG, ?_, ?_, ?_⟩
  · rw [hG, givensRotation_transpose_mul_apply hpi, ite_eq_right hpi.symm, ite_eq_left rfl]
    exact hz0
  · intro r q hrp hri
    rw [hG, givensRotation_transpose_mul_apply hpi, ite_eq_right hrp, ite_eq_right hri]
  · intro r q hq
    rw [hG]
    exact hleft r q hq

/-- The orthogonal-factor invariant `Q B = A₀` survives the step `B ↦ Gᵀ B`: `(Q G) (Gᵀ B) = Q B`.
-/
theorem exists_mul_eq_of_transpose_mul {A₀ B : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin m) (Fin m) ℝ} (hG : G ∈ orthogonalGroup (Fin m) ℝ)
    (hQ : ∃ Q ∈ orthogonalGroup (Fin m) ℝ, Q * B = A₀) :
    ∃ Q ∈ orthogonalGroup (Fin m) ℝ, Q * (Gᵀ * B) = A₀ := by
  obtain ⟨Q, hQo, hQB⟩ := hQ
  refine ⟨Q * G, mul_mem hQo hG, ?_⟩
  rw [← Matrix.mul_assoc, Matrix.mul_assoc Q G, (mem_orthogonalGroup_iff _ _).1 hG,
    Matrix.mul_one, hQB]

/-- **The inner loop of the column-oriented Givens QR algorithms** (Algorithm 5.2.4 and its first
reordering): rotations in the planes `(piv i, i)` over a list of rows `i > j`, each zeroing
`B(i, j)`, keep `Q B = A₀`, keep the columns `< j` triangular, and zero column `j` in every
processed row, provided no later rotation touches an already zeroed row. -/
theorem givensColumnLoop (A₀ : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) (piv : Fin m → Fin m) :
    ∀ (l : List (Fin m)) (B : Matrix (Fin m) (Fin n) ℝ) (S : Fin m → Prop),
      (∀ i ∈ l, piv i ≠ i ∧ (j : ℕ) ≤ piv i ∧ (j : ℕ) < i) →
      l.Pairwise (fun i i' => i ≠ piv i' ∧ i ≠ i') →
      (∀ r, S r → ∀ i ∈ l, r ≠ piv i ∧ r ≠ i) →
      (∃ Q ∈ orthogonalGroup (Fin m) ℝ, Q * B = A₀) →
      (∀ q : Fin n, (q : ℕ) < j → ∀ r : Fin m, (q : ℕ) < r → B r q = 0) →
      (∀ r, S r → B r j = 0) →
      (∃ Q ∈ orthogonalGroup (Fin m) ℝ,
          Q * l.foldl (fun B i => givensStepExact (piv i) i j B) B = A₀) ∧
        (∀ q : Fin n, (q : ℕ) < j → ∀ r : Fin m, (q : ℕ) < r →
          l.foldl (fun B i => givensStepExact (piv i) i j B) B r q = 0) ∧
        ∀ r, (S r ∨ r ∈ l) → l.foldl (fun B i => givensStepExact (piv i) i j B) B r j = 0 := by
  intro l
  induction l with
  | nil =>
    intro B S _ _ _ hQ hlow hS
    simp only [List.foldl_nil]
    exact ⟨hQ, hlow, fun r hr => hS r (by simpa using hr)⟩
  | cons i l ih =>
    intro B S hpiv hpw hSl hQ hlow hS
    obtain ⟨hpi, hjp, hji⟩ := hpiv i List.mem_cons_self
    have hz : ∀ q : Fin n, (q : ℕ) < j → B (piv i) q = 0 ∧ B i q = 0 := fun q hq =>
      ⟨hlow q hq _ (by omega), hlow q hq _ (by omega)⟩
    obtain ⟨hcs, hB1, hi0, hrest, hleft⟩ := givensStepExact_spec hpi j B hz
    have hG := givensRotation_mem_orthogonalGroup hpi hcs
    rw [List.pairwise_cons] at hpw
    rw [List.foldl_cons]
    have key := ih (givensStepExact (piv i) i j B) (fun r => S r ∨ r = i)
      (fun i' hi' => hpiv i' (List.mem_cons_of_mem _ hi')) hpw.2
      (by
        rintro r (hr | rfl) i' hi'
        · exact hSl r hr i' (List.mem_cons_of_mem _ hi')
        · exact hpw.1 i' hi')
      (by rw [hB1]; exact exists_mul_eq_of_transpose_mul hG hQ)
      (fun q hq r hr => by rw [hleft r q hq]; exact hlow q hq r hr)
      (by
        rintro r (hr | rfl)
        · obtain ⟨h1, h2⟩ := hSl r hr i List.mem_cons_self
          rw [hrest r j h1 h2]
          exact hS r hr
        · exact hi0)
    obtain ⟨h1, h2, h3⟩ := key
    refine ⟨h1, h2, fun r hr => h3 r ?_⟩
    rcases hr with hr | hr
    · exact Or.inl (Or.inl hr)
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr hr

/-- Membership in the list of rows below `j`, traversed upwards. -/
theorem mem_rowsBelow_reverse {j : ℕ} {i : Fin m} :
    i ∈ ((List.finRange m).filter (fun i : Fin m => j < i)).reverse ↔ j < i := by
  simp

/-- **The column-oriented Givens QR algorithms compute a QR factorization** (the common proof of
Algorithm 5.2.4 and its first reordering): for each column `j`, rows `i = m-1, …, j+1` are
rotated in the plane `(pivF j i, i)` with a pivot row `≥ j` below which the loop works upwards. -/
theorem givensQR_columnwise (A : Matrix (Fin m) (Fin n) ℝ) (pivF : Fin n → Fin m → Fin m)
    (hpiv : ∀ (j : Fin n) (i : Fin m), (j : ℕ) < i → pivF j i ≠ i ∧ (j : ℕ) ≤ pivF j i)
    (hpw : ∀ (j : Fin n) (a b : Fin m), (j : ℕ) < a → a < b → b ≠ pivF j a) :
    ∃ Q, IsQR A Q ((List.finRange n).foldl (fun (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
      (((List.finRange m).filter (fun i : Fin m => (j : ℕ) < i)).reverse).foldl
        (fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) => givensStepExact (pivF j i) i j B) B)
          A) := by
  set F : Matrix (Fin m) (Fin n) ℝ → Fin n → Matrix (Fin m) (Fin n) ℝ :=
    fun (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
      (((List.finRange m).filter (fun i : Fin m => (j : ℕ) < i)).reverse).foldl
        (fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) => givensStepExact (pivF j i) i j B) B
    with hF
  have hall : ∀ k ≤ n,
      (∃ Q ∈ orthogonalGroup (Fin m) ℝ, Q * ((List.finRange n).take k).foldl F A = A) ∧
      ∀ q : Fin n, (q : ℕ) < k → ∀ r : Fin m, (q : ℕ) < r →
        ((List.finRange n).take k).foldl F A r q = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [List.take_zero, List.foldl_nil]
      exact ⟨⟨1, one_mem _, Matrix.one_mul A⟩, fun q hq => absurd hq (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨hQ, hlow⟩ := ih (by omega)
      rw [List.take_succ_eq_append_getElem (by simpa using hk), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have hget : (List.finRange n)[k]'(by simpa using hk) = ⟨k, hk⟩ := by simp
      rw [hget]
      obtain ⟨h1, h2, h3⟩ := givensColumnLoop A ⟨k, hk⟩ (pivF ⟨k, hk⟩)
        ((List.finRange m).filter (fun i : Fin m => k < i)).reverse
        (((List.finRange n).take k).foldl F A) (fun _ => False)
        (fun i hi => by
          have hi' := mem_rowsBelow_reverse.1 hi
          exact ⟨(hpiv ⟨k, hk⟩ i hi').1, (hpiv ⟨k, hk⟩ i hi').2, hi'⟩)
        (List.pairwise_reverse.2 (List.pairwise_filter.2
          (((List.sortedLT_finRange m).pairwise).imp fun {a b} hab ha _ =>
            ⟨hpw ⟨k, hk⟩ a b (by simpa using ha) hab, ne_of_gt hab⟩)))
        (fun _ h => h.elim) hQ hlow (fun _ h => h.elim)
      refine ⟨h1, fun q hq r hr => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
      · exact h2 q hq r hr
      · have hqk : q = ⟨k, hk⟩ := Fin.ext hq
        subst hqk
        exact h3 r (Or.inr (mem_rowsBelow_reverse.2 hr))
  obtain ⟨⟨Q, hQo, hQB⟩, hlow⟩ := hall n le_rfl
  rw [List.take_of_length_le (by simp)] at hQB hlow
  exact ⟨Q, hQo, fun i j hji => hlow j j.2 i hji, hQB⟩

/-- **Algorithm 5.2.4 computes a QR factorization**: in exact arithmetic the overwritten array is
`R = QᵀA`, upper triangular, for an orthogonal `Q = G₁ ⋯ G_t` (the product of the rotations
used). -/
theorem algorithm_5_2_4_spec (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ Q, IsQR A Q (Id.run (algorithm_5_2_4 pure A)) := by
  have hprog : Id.run (algorithm_5_2_4 pure A) =
      (List.finRange n).foldl (fun (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
        (((List.finRange m).filter (fun i : Fin m => (j : ℕ) < i)).reverse).foldl
          (fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) =>
            givensStepExact (rowAbove i) i j B) B) A := by
    simp only [algorithm_5_2_4, List.idRun_foldlM]
    rfl
  rw [hprog]
  refine givensQR_columnwise A (fun _ i => rowAbove i) (fun j i hji => ⟨fun h => ?_, ?_⟩)
    (fun j a b hja hab h => ?_)
  · have := congrArg Fin.val h
    simp only [rowAbove] at this
    omega
  · change (j : ℕ) ≤ (i : ℕ) - 1
    omega
  · have := congrArg Fin.val h
    have hab' := Fin.lt_def.1 hab
    simp only [rowAbove] at this
    omega

/-- **§5.2.5, the first reordering computes a QR factorization**: rotating in the planes `(j, i)`
(`[c, s] = givens(A(j, j), A(i, j))`) instead of `(i-1, i)`, "and still emerge with the QR
factorization". -/
theorem givensQRDiagonalPivot_spec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ Q, IsQR A Q (Id.run (givensQRDiagonalPivot pure hnm A)) := by
  have hprog : Id.run (givensQRDiagonalPivot pure hnm A) =
      (List.finRange n).foldl (fun (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
        (((List.finRange m).filter (fun i : Fin m => (j : ℕ) < i)).reverse).foldl
          (fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) =>
            givensStepExact (Fin.castLE hnm j) i j B) B) A := by
    simp only [givensQRDiagonalPivot, List.idRun_foldlM]
    rfl
  rw [hprog]
  refine givensQR_columnwise A (fun j _ => Fin.castLE hnm j) (fun j i hji => ⟨fun h => ?_, ?_⟩)
    (fun j a b hja hab h => ?_)
  · have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    omega
  · simp
  · have := congrArg Fin.val h
    have hab' := Fin.lt_def.1 hab
    simp only [Fin.val_castLE] at this
    omega

/-- **The inner loop of the row-oriented Givens QR** (§5.2.5, zeros introduced by row): in row `i`,
rotations in the planes `(j, i)` for columns `j < i` in increasing order, each zeroing `B(i, j)`,
keep `Q B = A₀` and the triangular rows `< i`, and zero row `i` in every processed column. -/
theorem givensRowLoop (A₀ : Matrix (Fin m) (Fin n) ℝ) (hnm : n ≤ m) (i : Fin m) :
    ∀ (l : List (Fin n)) (B : Matrix (Fin m) (Fin n) ℝ) (T : Fin n → Prop),
      (∀ j ∈ l, (j : ℕ) < i) → l.Pairwise (· < ·) →
      (∀ j ∈ l, ∀ q : Fin n, q < j → T q ∨ q ∈ l) →
      (∀ q, T q → ∀ j ∈ l, q < j) →
      (∃ Q ∈ orthogonalGroup (Fin m) ℝ, Q * B = A₀) →
      (∀ r : Fin m, r < i → ∀ q : Fin n, (q : ℕ) < r → B r q = 0) →
      (∀ q, T q → B i q = 0) →
      (∃ Q ∈ orthogonalGroup (Fin m) ℝ,
          Q * l.foldl (fun B j => givensStepExact (Fin.castLE hnm j) i j B) B = A₀) ∧
        (∀ r : Fin m, r < i → ∀ q : Fin n, (q : ℕ) < r →
          l.foldl (fun B j => givensStepExact (Fin.castLE hnm j) i j B) B r q = 0) ∧
        ∀ q, (T q ∨ q ∈ l) →
          l.foldl (fun B j => givensStepExact (Fin.castLE hnm j) i j B) B i q = 0 := by
  intro l
  induction l with
  | nil =>
    intro B T _ _ _ _ hQ hlow hT
    simp only [List.foldl_nil]
    exact ⟨hQ, hlow, fun q hq => hT q (by simpa using hq)⟩
  | cons j l ih =>
    intro B T hli hpw hcov hTl hQ hlow hT
    rw [List.pairwise_cons] at hpw
    have hji : (j : ℕ) < i := hli j List.mem_cons_self
    have hpi : Fin.castLE hnm j ≠ i := fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_castLE] at this
      omega
    have hpilt : Fin.castLE hnm j < i := Fin.lt_def.2 (by simpa using hji)
    have hz : ∀ q : Fin n, (q : ℕ) < j → B (Fin.castLE hnm j) q = 0 ∧ B i q = 0 := by
      intro q hq
      refine ⟨hlow _ hpilt q (by simpa using hq), ?_⟩
      rcases hcov j List.mem_cons_self q (Fin.lt_def.2 hq) with hTq | hql
      · exact hT q hTq
      · rcases List.mem_cons.1 hql with rfl | hql
        · exact absurd hq (lt_irrefl _)
        · exact absurd (Fin.lt_def.1 (hpw.1 q hql)) (by omega)
    obtain ⟨hcs, hB1, hi0, hrest, hleft⟩ := givensStepExact_spec hpi j B hz
    have hG := givensRotation_mem_orthogonalGroup hpi hcs
    rw [List.foldl_cons]
    have key := ih (givensStepExact (Fin.castLE hnm j) i j B) (fun q => T q ∨ q = j)
      (fun j' hj' => hli j' (List.mem_cons_of_mem _ hj')) hpw.2
      (fun j' hj' q hq => by
        rcases hcov j' (List.mem_cons_of_mem _ hj') q hq with h | h
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr h)
      (by
        rintro q (hq | rfl) j' hj'
        · exact hTl q hq j' (List.mem_cons_of_mem _ hj')
        · exact hpw.1 j' hj')
      (by rw [hB1]; exact exists_mul_eq_of_transpose_mul hG hQ)
      (fun r hr q hqr => by
        by_cases hrp : r = Fin.castLE hnm j
        · subst hrp
          rw [hleft _ q (by simpa using hqr)]
          exact hlow _ hr q hqr
        · rw [hrest r q hrp (ne_of_lt hr)]
          exact hlow r hr q hqr)
      (by
        rintro q (hq | rfl)
        · rw [hleft i q (Fin.lt_def.1 (hTl q hq j List.mem_cons_self))]
          exact hT q hq
        · exact hi0)
    obtain ⟨h1, h2, h3⟩ := key
    refine ⟨h1, h2, fun q hq => h3 q ?_⟩
    rcases hq with hq | hq
    · exact Or.inl (Or.inl hq)
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr hq

/-- **§5.2.5, the second reordering computes a QR factorization**: introducing the zeros by row
(`for i = 2:m, for j = 1:i-1`, rotations in the planes `(j, i)`). -/
theorem givensQRByRow_spec (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ Q, IsQR A Q (Id.run (givensQRByRow pure hnm A)) := by
  set F : Matrix (Fin m) (Fin n) ℝ → Fin m → Matrix (Fin m) (Fin n) ℝ :=
    fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) =>
      ((List.finRange n).filter (fun j : Fin n => (j : ℕ) < i)).foldl
        (fun (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) =>
          givensStepExact (Fin.castLE hnm j) i j B) B
    with hF
  have hprog : Id.run (givensQRByRow pure hnm A) = (List.finRange m).foldl F A := by
    simp only [givensQRByRow, List.idRun_foldlM, hF]
    rfl
  have hall : ∀ k ≤ m,
      (∃ Q ∈ orthogonalGroup (Fin m) ℝ, Q * ((List.finRange m).take k).foldl F A = A) ∧
      ∀ r : Fin m, (r : ℕ) < k → ∀ q : Fin n, (q : ℕ) < r →
        ((List.finRange m).take k).foldl F A r q = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [List.take_zero, List.foldl_nil]
      exact ⟨⟨1, one_mem _, Matrix.one_mul A⟩, fun r hr => absurd hr (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨hQ, hlow⟩ := ih (by omega)
      rw [List.take_succ_eq_append_getElem (by simpa using hk), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have hget : (List.finRange m)[k]'(by simpa using hk) = ⟨k, hk⟩ := by simp
      rw [hget]
      obtain ⟨h1, h2, h3⟩ := givensRowLoop A hnm ⟨k, hk⟩
        ((List.finRange n).filter (fun j : Fin n => (j : ℕ) < k))
        (((List.finRange m).take k).foldl F A) (fun _ => False)
        (fun j hj => by simpa using hj) (((List.sortedLT_finRange n).pairwise).filter _)
        (fun j hj q hq => Or.inr (by
          simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hj ⊢
          exact lt_trans (Fin.lt_def.1 hq) hj))
        (fun _ h => h.elim) hQ
        (fun r hr q hq => hlow r (Fin.lt_def.1 hr) q hq) (fun _ h => h.elim)
      refine ⟨h1, fun r hr q hqr => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | hr
      · exact h2 r (Fin.lt_def.2 hr) q hqr
      · have hrk : r = ⟨k, hk⟩ := Fin.ext hr
        subst hrk
        exact h3 q (Or.inr (by simpa using hqr))
  obtain ⟨⟨Q, hQo, hQB⟩, hlow⟩ := hall m le_rfl
  rw [List.take_of_length_le (by simp)] at hQB hlow
  refine ⟨Q, hQo, fun i j hji => ?_, ?_⟩
  · rw [hprog]; exact hlow i i.2 j hji
  · rw [hprog]; exact hQB

/-! ### Hessenberg QR -/

/-- The product `G₀ G₁ ⋯ G_{t-1}` of the first `t` rotations `G_j = G(j, j+1, θ_j)` of
Algorithm 5.2.5, for pairs `cs j = (c_j, s_j)`. -/
noncomputable def hessenbergRotationsProd {k : ℕ} (cs : Fin k → ℝ × ℝ) (t : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  (((List.finRange k).take t).map fun j =>
    givensRotation j.castSucc j.succ (cs j).1 (cs j).2).prod

/-- One more rotation: `G₀ ⋯ G_t = (G₀ ⋯ G_{t-1}) G_t`. -/
theorem hessenbergRotationsProd_succ {k : ℕ} (cs : Fin k → ℝ × ℝ) {t : ℕ} (ht : t < k) :
    hessenbergRotationsProd cs (t + 1) = hessenbergRotationsProd cs t *
      givensRotation (⟨t, ht⟩ : Fin k).castSucc (⟨t, ht⟩ : Fin k).succ
        (cs ⟨t, ht⟩).1 (cs ⟨t, ht⟩).2 := by
  unfold hessenbergRotationsProd
  have hget : (List.finRange k)[t]'(by simpa using ht) = ⟨t, ht⟩ := by simp
  rw [List.take_succ_eq_append_getElem (by simpa using ht), List.map_append, List.prod_append,
    hget, List.map_singleton, List.prod_singleton]

/-- **`Q = G₁ ⋯ G_{n-1}` is upper Hessenberg** (a product of rotations in the adjacent planes
`(j, j+1)`, in increasing order): the partial product `G₀ ⋯ G_{t-1}` vanishes below the first
subdiagonal and is the identity in the columns `> t`. -/
theorem hessenbergRotationsProd_shape {k : ℕ} (cs : Fin k → ℝ × ℝ) :
    ∀ t ≤ k, (∀ r q : Fin (k + 1), (q : ℕ) + 1 < r → hessenbergRotationsProd cs t r q = 0) ∧
      ∀ r q : Fin (k + 1), t < (q : ℕ) →
        hessenbergRotationsProd cs t r q = if r = q then 1 else 0 := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [hessenbergRotationsProd, List.take_zero, List.map_nil, List.prod_nil]
    refine ⟨fun r q hqr => ?_, fun r q _ => rfl⟩
    rw [one_apply_ne (fun h => by rw [h] at hqr; omega)]
  | succ t ih =>
    intro ht
    obtain ⟨hH, hI⟩ := ih (by omega)
    set a : Fin (k + 1) := (⟨t, ht⟩ : Fin k).castSucc with ha
    set b : Fin (k + 1) := (⟨t, ht⟩ : Fin k).succ with hb
    have hav : (a : ℕ) = t := rfl
    have hbv : (b : ℕ) = t + 1 := rfl
    have hab : a ≠ b := fun h => by have := congrArg Fin.val h; omega
    have hP := hessenbergRotationsProd_succ cs ht
    rw [← ha, ← hb] at hP
    have hent : ∀ r q, hessenbergRotationsProd cs (t + 1) r q =
        if q = a then (cs ⟨t, ht⟩).1 * hessenbergRotationsProd cs t r a +
            -(cs ⟨t, ht⟩).2 * hessenbergRotationsProd cs t r b
        else if q = b then -(-(cs ⟨t, ht⟩).2) * hessenbergRotationsProd cs t r a +
            (cs ⟨t, ht⟩).1 * hessenbergRotationsProd cs t r b
        else hessenbergRotationsProd cs t r q := by
      intro r q
      rw [hP, givensRotation, mul_planeRotation_apply hab]
    have hrb : ∀ r : Fin (k + 1), t + 1 < (r : ℕ) → hessenbergRotationsProd cs t r b = 0 := by
      intro r hr
      rw [hI r b (by omega), ite_eq_right (fun h => by have := congrArg Fin.val h; omega)]
    refine ⟨fun r q hqr => ?_, fun r q hq => ?_⟩
    · rw [hent]
      split_ifs with hqa hqb
      · subst hqa
        rw [hH r a hqr, hrb r (by omega)]
        ring
      · subst hqb
        rw [hH r a (by omega), hrb r (by omega)]
        ring
      · exact hH r q hqr
    · have hqa : q ≠ a := fun h => by rw [h] at hq; omega
      have hqb : q ≠ b := fun h => by rw [h] at hq; omega
      rw [hent, ite_eq_right hqa, ite_eq_right hqb]
      exact hI r q (by omega)

/-- `(q : ℕ) + 1 < r` is the upper Hessenberg condition "some index lies between `q` and `r`". -/
theorem exists_between_iff {k : ℕ} (r q : Fin (k + 1)) :
    (∃ w, q < w ∧ w < r) ↔ (q : ℕ) + 1 < r := by
  constructor
  · rintro ⟨w, hqw, hwr⟩
    have := Fin.lt_def.1 hqw
    have := Fin.lt_def.1 hwr
    omega
  · intro h
    exact ⟨⟨q + 1, by omega⟩, Fin.lt_def.2 (by simp),
      Fin.lt_def.2 (by simpa using h)⟩

/-- **Algorithm 5.2.5 computes the QR factorization of an upper Hessenberg matrix**: in exact
arithmetic the overwritten array is `R = QᵀA`, upper triangular, with
`Q = G₁ ⋯ G_{n-1}`, `G_j = G(j, j+1, θ_j)` built from the returned pairs `(c_j, s_j)`, and `Q` is
upper Hessenberg. -/
theorem algorithm_5_2_5_spec {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hA : A.IsUpperHessenberg) :
    IsQR A (List.ofFn fun j : Fin k => givensRotation j.castSucc j.succ
          ((Id.run (algorithm_5_2_5 pure A)).2 j).1 ((Id.run (algorithm_5_2_5 pure A)).2 j).2).prod
        (Id.run (algorithm_5_2_5 pure A)).1 ∧
      (List.ofFn fun j : Fin k => givensRotation j.castSucc j.succ
          ((Id.run (algorithm_5_2_5 pure A)).2 j).1
          ((Id.run (algorithm_5_2_5 pure A)).2 j).2).prod.IsUpperHessenberg := by
  have hofn : ∀ cs : Fin k → ℝ × ℝ, (List.ofFn fun j : Fin k =>
      givensRotation j.castSucc j.succ (cs j).1 (cs j).2).prod = hessenbergRotationsProd cs k := by
    intro cs
    rw [hessenbergRotationsProd, List.take_of_length_le (by simp), List.ofFn_eq_map]
  rw [hofn]
  set F := fun (st : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin k → ℝ × ℝ)) (j : Fin k) =>
    (givensStepExact j.castSucc j.succ j.castSucc st.1, Function.update st.2 j
      (Id.run (algorithm_5_1_3 pure (st.1 j.castSucc j.castSucc) (st.1 j.succ j.castSucc))))
    with hF
  have hprog :
      Id.run (algorithm_5_2_5 pure A) = (List.finRange k).foldl F (A, fun _ => (1, 0)) := by
    simp only [algorithm_5_2_5, List.idRun_foldlM, hF]
    rfl
  have hAH : ∀ r q : Fin (k + 1), (q : ℕ) + 1 < r → A r q = 0 :=
    fun r q h => hA r q ((exists_between_iff r q).2 h)
  have hall : ∀ t ≤ k,
      hessenbergRotationsProd (((List.finRange k).take t).foldl F (A, fun _ => (1, 0))).2 t *
          (((List.finRange k).take t).foldl F (A, fun _ => (1, 0))).1 = A ∧
        (∀ j : Fin k, (j : ℕ) < t →
          ((((List.finRange k).take t).foldl F (A, fun _ => (1, 0))).2 j).1 ^ 2 +
            ((((List.finRange k).take t).foldl F (A, fun _ => (1, 0))).2 j).2 ^ 2 = 1) ∧
        (∀ q : Fin (k + 1), (q : ℕ) < t → ∀ r : Fin (k + 1), (q : ℕ) < r →
          (((List.finRange k).take t).foldl F (A, fun _ => (1, 0))).1 r q = 0) ∧
        ∀ r q : Fin (k + 1), (q : ℕ) + 1 < r →
          (((List.finRange k).take t).foldl F (A, fun _ => (1, 0))).1 r q = 0 := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨by simp [hessenbergRotationsProd], fun j hj => absurd hj (Nat.not_lt_zero _),
        fun q hq => absurd hq (Nat.not_lt_zero _), ?_⟩
      simpa using hAH
    | succ t ih =>
      intro ht
      obtain ⟨hQ, hunit, htri, hhess⟩ := ih (by omega)
      rw [List.take_succ_eq_append_getElem (by simpa using ht), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have hget : (List.finRange k)[t]'(by simpa using ht) = ⟨t, ht⟩ := by simp
      rw [hget]
      set st := ((List.finRange k).take t).foldl F (A, fun _ => (1, 0)) with hst
      set j : Fin k := ⟨t, ht⟩ with hj
      set a : Fin (k + 1) := j.castSucc with ha
      set b : Fin (k + 1) := j.succ with hb
      have hav : (a : ℕ) = t := rfl
      have hbv : (b : ℕ) = t + 1 := rfl
      have hab : a ≠ b := fun h => by have := congrArg Fin.val h; omega
      have hz : ∀ q : Fin (k + 1), (q : ℕ) < (a : ℕ) → st.1 a q = 0 ∧ st.1 b q = 0 :=
        fun q hq => ⟨htri q (by omega) a (by omega), htri q (by omega) b (by omega)⟩
      obtain ⟨hcs, hB1, hi0, hrest, hleft⟩ := givensStepExact_spec hab a st.1 hz
      have hG := givensRotation_mem_orthogonalGroup hab hcs
      have hFst : F st j = (givensStepExact a b a st.1, Function.update st.2 j
          (Id.run (algorithm_5_1_3 pure (st.1 a a) (st.1 b a)))) := rfl
      rw [hFst]
      dsimp only
      refine ⟨?_, fun j' hj' => ?_, fun q hq r hqr => ?_, fun r q hqr => ?_⟩
      · -- the product gains the rotation of step `t`
        rw [hessenbergRotationsProd_succ _ ht, ← hj]
        have hsame : hessenbergRotationsProd (Function.update st.2 j
            (Id.run (algorithm_5_1_3 pure (st.1 a a) (st.1 b a)))) t =
            hessenbergRotationsProd st.2 t := by
          unfold hessenbergRotationsProd
          congr 1
          refine List.map_congr_left fun j' hj' => ?_
          have hne : j' ≠ j := fun h => by
            have := lt_of_mem_take_finRange hj'
            rw [h] at this
            simp [hj] at this
          rw [Function.update_of_ne hne]
        rw [hsame, Function.update_self, ← ha, ← hb, hB1, Matrix.mul_assoc,
          ← Matrix.mul_assoc _ (_ᵀ), (mem_orthogonalGroup_iff _ _).1 hG, Matrix.one_mul, hQ]
      · by_cases hjj : j' = j
        · subst hjj
          rw [Function.update_self]
          exact hcs
        · rw [Function.update_of_ne hjj]
          refine hunit j' ?_
          have : (j' : ℕ) ≠ t := fun h => hjj (Fin.ext h)
          omega
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
        · rw [hleft r q (by omega)]
          exact htri q hq r hqr
        · have hqa : q = a := Fin.ext (by omega)
          subst hqa
          by_cases hrb : r = b
          · rw [hrb]; exact hi0
          · have hra : r ≠ a := fun h => by rw [h] at hqr; omega
            rw [hrest r _ hra hrb]
            refine hhess r _ ?_
            have : (r : ℕ) ≠ t + 1 := fun h => hrb (Fin.ext h)
            omega
      · by_cases hra : r = a
        · subst hra
          rw [hleft _ q (by omega)]
          exact hhess _ q hqr
        · by_cases hrb : r = b
          · subst hrb
            rw [hleft _ q (by omega)]
            exact hhess _ q hqr
          · rw [hrest r q hra hrb]
            exact hhess r q hqr
  obtain ⟨hQ, hunit, htri, -⟩ := hall k le_rfl
  rw [List.take_of_length_le (by simp)] at hQ hunit htri
  rw [hprog]
  refine ⟨⟨?_, fun i j hji => ?_, hQ⟩, fun r q hrq => ?_⟩
  · unfold hessenbergRotationsProd
    rw [List.take_of_length_le (by simp)]
    refine list_prod_mem fun G hG => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hG
    exact givensRotation_mem_orthogonalGroup
      (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne (hunit j j.2)
  · have hjk : (j : ℕ) < k := by have := i.2; omega
    exact htri j hjk i hji
  · exact ((hessenbergRotationsProd_shape _ k le_rfl).1 r q ((exists_between_iff r q).1 hrq))

end GivensQRSpec

section Sweeps

/-! #### The Givens sweeps of §6.5: exact semantics -/

/-- One exact Givens step on a pair `(Q, H)`: `H ← G(p, q, θ)ᵀ H`, `Q ← Q G(p, q, θ)`. -/
noncomputable def givensPairStep {m n : ℕ} (p q : Fin m) (cs : ℝ × ℝ)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ :=
  (st.1 * givensRotation p q cs.1 cs.2, (givensRotation p q cs.1 cs.2)ᵀ * st.2)

/-- The `Q` of an exact Givens step stays orthogonal. -/
theorem givensPairStep_mem {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) {cs : ℝ × ℝ}
    (hcs : cs.1 ^ 2 + cs.2 ^ 2 = 1) {st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ}
    (hQ : st.1 ∈ orthogonalGroup (Fin m) ℝ) :
    (givensPairStep p q cs st).1 ∈ orthogonalGroup (Fin m) ℝ :=
  mul_mem hQ (givensRotation_mem_orthogonalGroup hpq hcs)

/-- An exact Givens step keeps the product `Q H`. -/
theorem givensPairStep_mul {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) {cs : ℝ × ℝ}
    (hcs : cs.1 ^ 2 + cs.2 ^ 2 = 1) (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :
    (givensPairStep p q cs st).1 * (givensPairStep p q cs st).2 = st.1 * st.2 := by
  have hG := (mem_orthogonalGroup_iff _ ℝ).1
    (givensRotation_mem_orthogonalGroup hpq hcs)
  simp only [givensPairStep]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (givensRotation p q cs.1 cs.2), hG,
    Matrix.one_mul]

/-- The entries of the `H` of an exact Givens step. -/
theorem givensPairStep_apply {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) (cs : ℝ × ℝ)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (l : Fin n) :
    (givensPairStep p q cs st).2 r l =
      if r = p then cs.1 * st.2 p l - cs.2 * st.2 q l
      else if r = q then cs.2 * st.2 p l + cs.1 * st.2 q l else st.2 r l :=
  givensRotation_transpose_mul_apply hpq cs.1 cs.2 st.2 r l

/-- The step kills the entry the Givens pair was computed from. -/
theorem givensPairStep_zero {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) (l : Fin n)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) :
    (givensPairStep p q (Id.run (algorithm_5_1_3 pure (st.2 p l) (st.2 q l))) st).2 q l
      = 0 := by
  rw [givensPairStep_apply hpq, ite_eq_right hpq.symm, ite_eq_left rfl]
  exact (algorithm_5_1_3_spec _ _).2.1

/-- A step leaves an entry zero if, in its column, both rotated rows were zero (when the entry
is in one of them), or the entry itself was zero (otherwise). -/
theorem givensPairStep_eq_zero {m n : ℕ} {p q : Fin m} (hpq : p ≠ q) (cs : ℝ × ℝ)
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
      (Id.run (algorithm_5_1_3 pure (st.2 ⟨j, by omega⟩ ⟨j, h.2⟩)
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
    rw [givensApplyLeft_spec_of_forall_mem hpq _ _ (List.nodup_finRange n)
      (List.mem_finRange), givensApplyRight_spec_of_forall_mem hpq _ _
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
      have hcs := (algorithm_5_1_3_spec (st.2 p jc) (st.2 q jc)).1
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

/-- The exact step of `givensVectorSweep`. -/
private noncomputable def vecStep {m n : ℕ}
    (st : (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) (j : ℕ) :
    (Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ :=
  if h : j + 1 < m then
    let cs := Id.run (algorithm_5_1_3 pure (st.1 ⟨j, by omega⟩) (st.1 ⟨j + 1, h⟩))
    ((givensRotation ⟨j, by omega⟩ ⟨j + 1, h⟩ cs.1 cs.2)ᵀ *ᵥ st.1,
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
    rw [givensRotateVec_pure hpq, givensApplyLeft_spec_of_forall_mem hpq _ _
      (List.nodup_finRange n) (List.mem_finRange), givensApplyRight_spec_of_forall_mem hpq
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
      obtain ⟨hcs, hz, -⟩ := algorithm_5_1_3_spec (x p) (x q)
      set cs := Id.run (algorithm_5_1_3 pure (x p) (x q)) with hcsdef
      set G := givensRotation p q cs.1 cs.2 with hG
      have hGo : G ∈ orthogonalGroup (Fin m) ℝ :=
        givensRotation_mem_orthogonalGroup hpq hcs
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
        rw [givensRotation_transpose_mulVec_apply hpq]
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

end Sweeps


/-! ### Givens QR: rounding errors -/

section GivensQRRounding

/-- **A computed rotation whose second entry is replaced by the exact zero**: if `d` vanishes
off the pivot row `p` and `|d_p| ≤ γ (|c| |x_p| + |s| |x_i|)` with `c² + s² = 1`, then
`‖d‖₂ ≤ γ ‖x‖₂` (Cauchy–Schwarz on `(x_p, x_i)`). -/
theorem norm_le_of_single_of_abs_le {M : ℕ} {p i : Fin M} (hpi : p ≠ i) {c s γ : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hγ : 0 ≤ γ) {x d : Fin M → ℝ} (hd : ∀ l, l ≠ p → d l = 0)
    (hdp : |d p| ≤ γ * (|c| * |x p| + |s| * |x i|)) :
    ‖(toLp 2 d : EuclideanSpace ℝ (Fin M))‖ ≤ γ * ‖(toLp 2 x : EuclideanSpace ℝ (Fin M))‖ := by
  have hnorm : ‖(toLp 2 d : EuclideanSpace ℝ (Fin M))‖ = |d p| := by
    rw [EuclideanSpace.norm_eq, Finset.sum_eq_single p (fun l _ hl => by simp [hd l hl])
      (by simp)]
    simp [Real.sqrt_sq_eq_abs]
  have hcs2 : (|c| * |x p| + |s| * |x i|) ^ 2 ≤ x p ^ 2 + x i ^ 2 := by
    have := sq_abs c; have := sq_abs s; have := sq_abs (x p); have := sq_abs (x i)
    nlinarith [sq_nonneg (|c| * |x i| - |s| * |x p|)]
  have hle : |c| * |x p| + |s| * |x i| ≤ ‖(toLp 2 x : EuclideanSpace ℝ (Fin M))‖ := by
    have h2 := hcs2.trans (sq_add_sq_le_norm_toLp_sq hpi x)
    have h0 : 0 ≤ |c| * |x p| + |s| * |x i| := by positivity
    nlinarith [norm_nonneg (toLp 2 x : EuclideanSpace ℝ (Fin M))]
  rw [hnorm]
  exact hdp.trans (mul_le_mul_of_nonneg_left hle hγ)

/-- The columns of a product: `(M X)(:, q) = M X(:, q)`. -/
theorem col_mul_eq_mulVec {M N : ℕ} (G : Matrix (Fin M) (Fin M) ℝ)
    (X : Matrix (Fin M) (Fin N) ℝ) (q : Fin N) : (G * X).col q = G *ᵥ X.col q := by
  ext r
  rfl

/-- **One step of the columnwise accumulation** ([higham2002accuracy] Lemma 19.3): if
`Q C = A + E` with `Q` orthogonal and `‖E(:, q)‖ ≤ ((1 + ε)^t - 1) ‖A(:, q)‖`, and
`C' = Gᵀ C + F` with `G` orthogonal and `‖F(:, q)‖ ≤ ε ‖C(:, q)‖`, then `(Q G) C' = A + E'` with
`‖E'(:, q)‖ ≤ ((1 + ε)^{t+1} - 1) ‖A(:, q)‖`. The backbone
`FloatingPoint.exists_eq_mul_add_of_step` read for the inverse factor `Qᵀ`. -/
theorem exists_mul_eq_add_of_step {M N : ℕ} {A C C' : Matrix (Fin M) (Fin N) ℝ}
    {Q G : Matrix (Fin M) (Fin M) ℝ} (hQ : Q ∈ orthogonalGroup (Fin M) ℝ)
    (hG : G ∈ orthogonalGroup (Fin M) ℝ) {E : Matrix (Fin M) (Fin N) ℝ} (hQE : Q * C = A + E)
    {ε : ℝ} (hε : 0 ≤ ε) {t : ℕ}
    (hE : ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin M))‖ ≤
      ((1 + ε) ^ t - 1) * ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin M))‖)
    (hF : ∀ q, ‖(toLp 2 ((C' - Gᵀ * C).col q) : EuclideanSpace ℝ (Fin M))‖ ≤
      ε * ‖(toLp 2 (C.col q) : EuclideanSpace ℝ (Fin M))‖) :
    ∃ E' : Matrix (Fin M) (Fin N) ℝ, (Q * G) * C' = A + E' ∧
      ∀ q, ‖(toLp 2 (E'.col q) : EuclideanSpace ℝ (Fin M))‖ ≤
        ((1 + ε) ^ (t + 1) - 1) * ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin M))‖ := by
  have hC : C = Qᵀ * (A + E) := by
    rw [← hQE, ← Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ _).1 hQ, Matrix.one_mul]
  obtain ⟨E', hE', hb⟩ := FloatingPoint.exists_eq_mul_add_of_step
    (transpose_mem_unitaryGroup_iff.2 hG) (transpose_mem_unitaryGroup_iff.2 hQ) hε hC hE hF
  refine ⟨E', ?_, hb⟩
  rw [hE']
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G Gᵀ, (mem_orthogonalGroup_iff _ _).1 hG, Matrix.one_mul,
    ← Matrix.mul_assoc Q Qᵀ, (mem_orthogonalGroup_iff _ _).1 hQ, Matrix.one_mul]

/-- The array of a run of Algorithm 5.2.5 with the computed "zeros" `(j+1, j)` of its first `t`
rotations set to zero. -/
def hessenbergJunkClean {k : ℕ} (t : ℕ) (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  of fun r q => if (q : ℕ) < t ∧ (r : ℕ) = q + 1 then 0 else B r q

/-- **The backward error of the computed Hessenberg QR** (Algorithm 5.2.5, §5.1.12 applied to a
sequence of `n - 1` rotations), rigorous: if `15 u < 1` and `A` is upper Hessenberg, every run
`(R̂', ĉs)` gives an orthogonal `Q` and `E` with `Q R̂ = A + E` for the upper triangle
`R̂ = upperPart R̂'` (the computed sub-diagonal "zeros" discarded), and columnwise
`‖E(:, q)‖₂ ≤ ((1 + √2 γ₁₅)^{n-1} - 1) ‖A(:, q)‖₂`: `Q` is the product of the exact rotations
of which the computed pairs are relative perturbations (`algorithm_5_1_3_rounding`). -/
theorem algorithm_5_2_5_rounding {fp : RoundingModel ℝ} (hu : ((15 : ℕ) : ℝ) * fp.u < 1) {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (hA : A.IsUpperHessenberg)
    {st : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin k → ℝ × ℝ)}
    (h : st ∈ (algorithm_5_2_5 fp.round A).run) :
    ∃ Q ∈ orthogonalGroup (Fin (k + 1)) ℝ, ∃ E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ,
      Q * upperPart st.1 = A + E ∧
        ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin (k + 1)))‖ ≤
          ((1 + √2 * gamma fp.u 15) ^ k - 1) *
            ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin (k + 1)))‖ := by
  set ε := √2 * gamma fp.u 15 with hεdef
  have hu0 := fp.u_nonneg
  have hγ : 0 ≤ gamma fp.u 15 := gamma_nonneg hu0 hu
  have hε : 0 ≤ ε := by positivity
  have hγε : gamma fp.u 15 ≤ ε := by
    have : (1 : ℝ) ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
    nlinarith
  have hu13 : ((13 : ℕ) : ℝ) * fp.u < 1 :=
    (mul_le_mul_of_nonneg_right (by norm_num) hu0).trans_lt hu
  have hAH : ∀ r q : Fin (k + 1), (q : ℕ) + 1 < r → A r q = 0 :=
    fun r q h => hA r q ((exists_between_iff r q).2 h)
  -- the invariant after `t` rotations
  have hinv := SetM.forall_mem_run_foldlM_finRange
    (fun (t : ℕ) (st : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ × (Fin k → ℝ × ℝ)) =>
      (∀ r q : Fin (k + 1), (q : ℕ) + 1 < r → st.1 r q = 0) ∧
        ∃ Q ∈ orthogonalGroup (Fin (k + 1)) ℝ, ∃ E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ,
          Q * hessenbergJunkClean t st.1 = A + E ∧
            ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin (k + 1)))‖ ≤
              ((1 + ε) ^ t - 1) * ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin (k + 1)))‖)
    ⟨hAH, 1, one_mem _, 0, by
      ext r q
      simp [hessenbergJunkClean], fun q => by
        rw [show (0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).col q = 0 from rfl]; simp⟩ ?_ st h
  · obtain ⟨hH, Q, hQ, E, hQE, hE⟩ := hinv
    have hclean : hessenbergJunkClean k st.1 = upperPart st.1 := by
      ext r q
      simp only [hessenbergJunkClean, upperPart, of_apply]
      split_ifs with h1 h2 h2
      · omega
      · rfl
      · rfl
      · have hr := r.2
        by_cases hrq : (r : ℕ) = q + 1
        · exact absurd ⟨by omega, hrq⟩ h1
        · exact hH r q (by omega)
    exact ⟨Q, hQ, E, by rw [← hclean]; exact hQE, hE⟩
  · intro jj st hI st' hst'
    obtain ⟨hH, Q, hQ, E, hQE, hE⟩ := hI
    simp only [SetM.mem_run_bind, SetM.mem_run_pure] at hst'
    obtain ⟨cs, hcs, B', hB', rfl⟩ := hst'
    dsimp only
    set t : ℕ := (jj : ℕ) with ht
    set a : Fin (k + 1) := jj.castSucc with ha
    set b : Fin (k + 1) := jj.succ with hb
    have hav : (a : ℕ) = t := rfl
    have hbv : (b : ℕ) = t + 1 := rfl
    have hab : a ≠ b := fun h => by have := congrArg Fin.val h; omega
    obtain ⟨c, s, hcs1, hzero, hc, hs⟩ := algorithm_5_1_3_rounding hu13 _ _ hcs
    obtain ⟨hout, hrows, hrel⟩ := givensApplyLeft_rounds hab cs.1 cs.2
      (nodup_indexFrom (k + 1) jj) st.1 hB'
    have hG := givensRotation_mem_orthogonalGroup hab hcs1
    have hmem : ∀ q : Fin (k + 1), q ∈ indexFrom (k + 1) jj ↔ t ≤ (q : ℕ) := fun q => by
      rw [mem_indexFrom]
    set C := hessenbergJunkClean t st.1 with hC
    set C' := hessenbergJunkClean (t + 1) B' with hC'
    -- the entries of `Gᵀ C`
    have hGC := fun r q => givensRotation_transpose_mul_apply hab c s C r q
    refine ⟨fun r q hqr => ?_, ?_⟩
    · -- the exact zeros below the subdiagonal are never touched
      by_cases hq : t ≤ (q : ℕ)
      · rw [hrows r q (fun h => by rw [h] at hqr; omega) (fun h => by rw [h] at hqr; omega)]
        exact hH r q hqr
      · rw [hout r q (fun h => hq ((hmem q).1 h))]
        exact hH r q hqr
    have hF : ∀ q, ‖(toLp 2 ((C' - (givensRotation a b c s)ᵀ * C).col q) :
        EuclideanSpace ℝ (Fin (k + 1)))‖ ≤ ε * ‖(toLp 2 (C.col q) :
          EuclideanSpace ℝ (Fin (k + 1)))‖ := by
      intro q
      rcases lt_trichotomy (q : ℕ) t with hq | hq | hq
      · -- a column already reduced: rows `a, b` of `C` vanish there, nothing changes
        have hCa : C a q = 0 := by
          simp only [hC, hessenbergJunkClean, of_apply]
          split_ifs with h1
          · rfl
          · exact hH a q (by omega)
        have hCb : C b q = 0 := by
          simp only [hC, hessenbergJunkClean, of_apply]
          split_ifs with h1
          · rfl
          · exact hH b q (by omega)
        have hzero' : (C' - (givensRotation a b c s)ᵀ * C).col q = 0 := by
          ext r
          simp only [col_apply, Matrix.sub_apply, Pi.zero_apply, hGC, hCa, hCb]
          have hCC : C' r q = C r q := by
            simp only [hC, hC', hessenbergJunkClean, of_apply]
            rw [hout r q (fun h => by have := (hmem q).1 h; omega)]
            split_ifs with h1 h2 h2
            · rfl
            · exact absurd ⟨by omega, h1.2⟩ h2
            · exact absurd ⟨by omega, h2.2⟩ h1
            · rfl
          split_ifs with hra hrb
          · rw [hCC, hra, hCa]; ring
          · rw [hCC, hrb, hCb]; ring
          · rw [hCC, sub_self]
        rw [hzero']
        simp only [toLp_zero, norm_zero]
        positivity
      · -- the column being reduced: only the pivot row carries a rounding error
        have hqa : q = a := Fin.ext (by omega)
        subst hqa
        have hCcol : ∀ r, C r a = st.1 r a := fun r => by
          simp only [hC, hessenbergJunkClean, of_apply]
          rw [ite_eq_right (fun h => by omega)]
        have hdiff := abs_sub_le_of_roundsGivensApply
          (show ((13 + 2 : ℕ) : ℝ) * fp.u < 1 from hu) hc hs (hrel ⟨a, (hmem a).2 le_rfl⟩)
        simp only [submatrix_apply, id] at hdiff
        obtain ⟨hda, -, -⟩ := hdiff
        refine (norm_le_of_single_of_abs_le hab hcs1 hγ (x := C.col a) (p := a) (i := b)
          (fun r hra => ?_) ?_).trans (mul_le_mul_of_nonneg_right hγε (norm_nonneg _))
        · simp only [col_apply, Matrix.sub_apply, hGC, ite_eq_right hra]
          by_cases hrb : r = b
          · rw [ite_eq_left hrb, hrb, hCcol a, hCcol b]
            simp only [hC', hessenbergJunkClean, of_apply]
            rw [ite_eq_left ⟨by omega, by omega⟩]
            linarith [hzero]
          · rw [ite_eq_right hrb]
            simp only [hC', hessenbergJunkClean, of_apply]
            rw [ite_eq_right (fun h => hrb (Fin.ext (by omega))), hrows r a hra hrb, hCcol r,
              sub_self]
        · simp only [col_apply, Matrix.sub_apply, hGC, ↓reduceIte, hCcol]
          simp only [hC', hessenbergJunkClean, of_apply]
          rw [ite_eq_right (fun h => by omega)]
          exact hda
      · -- a column not yet reached: the backbone's bound for a computed rotation
        have hCcol : C.col q = st.1.col q := by
          ext r
          simp only [col_apply, hC, hessenbergJunkClean, of_apply]
          rw [ite_eq_right (fun h => by omega)]
        have hC'col : C'.col q = B'.col q := by
          ext r
          simp only [col_apply, hC', hessenbergJunkClean, of_apply]
          rw [ite_eq_right (fun h => by omega)]
        have hcol : (C' - (givensRotation a b c s)ᵀ * C).col q =
            B'.col q - (planeRotation a b c (-s))ᵀ *ᵥ st.1.col q := by
          rw [show (C' - (givensRotation a b c s)ᵀ * C).col q =
              C'.col q - ((givensRotation a b c s)ᵀ * C).col q from rfl,
            col_mul_eq_mulVec, hCcol, hC'col]
          rfl
        rw [hcol, hCcol]
        exact norm_sub_le_of_roundsGivensApply (show ((13 + 2 : ℕ) : ℝ) * fp.u < 1 from hu) hab
          hcs1 hc hs (hrel ⟨q, (hmem q).2 hq.le⟩)
    obtain ⟨E', hE'eq, hE'⟩ := exists_mul_eq_add_of_step hQ hG hQE hε hE hF
    refine ⟨Q * givensRotation a b c s, mul_mem hQ hG, E', ?_, ?_⟩
    · exact hE'eq
    · exact hE'

end GivensQRRounding


section GivensQRRounding'

/-- The array of a run of Algorithm 5.2.4 with its computed "zeros" set to zero: the entries below
the diagonal of the columns `< j`, and the entries of column `j` in the rows `p` already
processed. -/
def givensQRJunkClean (j : ℕ) (p : List (Fin m)) (B : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  of fun r q => if ((q : ℕ) < j ∧ (q : ℕ) < r) ∨ ((q : ℕ) = j ∧ r ∈ p) then 0 else B r q

/-- **The backward error of Givens QR** (§5.3.3 "similar results hold if Givens QR is used",
§5.1.12 applied to Algorithm 5.2.4), rigorous: if `15 u < 1`, every run `A'` of Algorithm 5.2.4
gives an orthogonal `Q` and `E` with `Q R̂ = A + E` for the upper triangle `R̂ = upperPart A'` (the
computed sub-diagonal "zeros" discarded), and columnwise
`‖E(:, q)‖₂ ≤ ((1 + √2 γ₁₅)^{mn} - 1) ‖A(:, q)‖₂` (`mn` bounds the number of rotations; `Q` is
the product of the exact rotations of which the computed pairs are relative perturbations). -/
theorem algorithm_5_2_4_rounding {fp : RoundingModel ℝ} (hu : ((15 : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin m) (Fin n) ℝ) {A' : Matrix (Fin m) (Fin n) ℝ}
    (h : A' ∈ (algorithm_5_2_4 fp.round A).run) :
    ∃ Q ∈ orthogonalGroup (Fin m) ℝ, ∃ E : Matrix (Fin m) (Fin n) ℝ,
      Q * upperPart A' = A + E ∧
        ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin m))‖ ≤
          ((1 + √2 * gamma fp.u 15) ^ (m * n) - 1) *
            ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin m))‖ := by
  set ε := √2 * gamma fp.u 15 with hεdef
  have hu0 := fp.u_nonneg
  have hγ : 0 ≤ gamma fp.u 15 := gamma_nonneg hu0 hu
  have hε : 0 ≤ ε := by positivity
  have hγε : gamma fp.u 15 ≤ ε := by
    have : (1 : ℝ) ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
    nlinarith
  have hu13 : ((13 : ℕ) : ℝ) * fp.u < 1 :=
    (mul_le_mul_of_nonneg_right (by norm_num) hu0).trans_lt hu
  -- the invariant, with `t` rotations done
  set J : ℕ → List (Fin m) → Matrix (Fin m) (Fin n) ℝ → ℕ → Prop := fun j p B t =>
    ∃ Q ∈ orthogonalGroup (Fin m) ℝ, ∃ E : Matrix (Fin m) (Fin n) ℝ,
      Q * givensQRJunkClean j p B = A + E ∧
        ∀ q, ‖(toLp 2 (E.col q) : EuclideanSpace ℝ (Fin m))‖ ≤
          ((1 + ε) ^ t - 1) * ‖(toLp 2 (A.col q) : EuclideanSpace ℝ (Fin m))‖ with hJ
  -- one rotation
  have hrot : ∀ (jj : Fin n) (p : List (Fin m)) (i : Fin m) (B B' : Matrix (Fin m) (Fin n) ℝ)
      (t : ℕ) (cs : ℝ × ℝ), (jj : ℕ) < i → (∀ r ∈ p, i < r) → J jj p B t →
      cs ∈ (algorithm_5_1_3 fp.round (B (rowAbove i) jj) (B i jj)).run →
      B' ∈ (givensApplyLeft fp.round (rowAbove i) i cs.1 cs.2 (indexFrom n jj) B).run →
      J jj (p ++ [i]) B' (t + 1) := by
    intro jj p i B B' t cs hji hp hI hcs hB'
    obtain ⟨Q, hQ, E, hQE, hE⟩ := hI
    set a := rowAbove i with ha
    have hav : (a : ℕ) = i - 1 := rfl
    have hai : a ≠ i := fun h => by have := congrArg Fin.val h; omega
    obtain ⟨c, s, hcs1, hzero, hc, hs⟩ := algorithm_5_1_3_rounding hu13 _ _ hcs
    obtain ⟨hout, hrows, hrel⟩ := givensApplyLeft_rounds hai cs.1 cs.2
      (nodup_indexFrom n jj) B hB'
    have hG := givensRotation_mem_orthogonalGroup hai hcs1
    have hmem : ∀ q : Fin n, q ∈ indexFrom n jj ↔ (jj : ℕ) ≤ q := fun q => by
      rw [mem_indexFrom]
    have hpa : ∀ r ∈ p, r ≠ a ∧ r ≠ i := fun r hr => by
      have := Fin.lt_def.1 (hp r hr)
      exact ⟨fun h => by rw [h] at this; omega, fun h => by rw [h] at this; omega⟩
    set C := givensQRJunkClean jj p B with hC
    set C' := givensQRJunkClean jj (p ++ [i]) B' with hC'
    have hGC := fun r q => givensRotation_transpose_mul_apply hai c s C r q
    have hF : ∀ q, ‖(toLp 2 ((C' - (givensRotation a i c s)ᵀ * C).col q) :
        EuclideanSpace ℝ (Fin m))‖ ≤ ε * ‖(toLp 2 (C.col q) : EuclideanSpace ℝ (Fin m))‖ := by
      intro q
      rcases lt_trichotomy (q : ℕ) jj with hq | hq | hq
      · -- a column already reduced: rows `a, i` of `C` vanish there
        have hCa : C a q = 0 := by
          simp only [hC, givensQRJunkClean, of_apply]
          rw [ite_eq_left (Or.inl ⟨hq, by omega⟩)]
        have hCi : C i q = 0 := by
          simp only [hC, givensQRJunkClean, of_apply]
          rw [ite_eq_left (Or.inl ⟨hq, by omega⟩)]
        have hzero' : (C' - (givensRotation a i c s)ᵀ * C).col q = 0 := by
          ext r
          simp only [col_apply, Matrix.sub_apply, Pi.zero_apply, hGC, hCa, hCi]
          have hCC : C' r q = C r q := by
            simp only [hC, hC', givensQRJunkClean, of_apply]
            rw [hout r q (fun h => by have := (hmem q).1 h; omega)]
            have hne : (q : ℕ) ≠ jj := by omega
            simp only [hne, false_and, or_false]
          split_ifs with hra hri
          · rw [hCC, hra, hCa]; ring
          · rw [hCC, hri, hCi]; ring
          · rw [hCC, sub_self]
        rw [hzero']
        simp only [toLp_zero, norm_zero]
        positivity
      · -- the column being reduced
        have hqj : q = jj := Fin.ext hq
        subst hqj
        have hCcol : ∀ r, r ∉ p → C r q = B r q := fun r hr => by
          simp only [hC, givensQRJunkClean, of_apply]
          rw [ite_eq_right (fun h => by
            rcases h with h | h
            · omega
            · exact hr h.2)]
        have hai' : a ∉ p := fun h => (hpa a h).1 rfl
        have hii' : i ∉ p := fun h => (hpa i h).2 rfl
        have hdiff := abs_sub_le_of_roundsGivensApply
          (show ((13 + 2 : ℕ) : ℝ) * fp.u < 1 from hu) hc hs (hrel ⟨q, (hmem q).2 le_rfl⟩)
        simp only [submatrix_apply, id] at hdiff
        obtain ⟨hda, -, -⟩ := hdiff
        refine (norm_le_of_single_of_abs_le hai hcs1 hγ (x := C.col q) (p := a) (i := i)
          (fun r hra => ?_) ?_).trans (mul_le_mul_of_nonneg_right hγε (norm_nonneg _))
        · simp only [col_apply, Matrix.sub_apply, hGC, ite_eq_right hra]
          by_cases hri : r = i
          · rw [ite_eq_left hri, hri, hCcol a hai', hCcol i hii']
            simp only [hC', givensQRJunkClean, of_apply]
            rw [ite_eq_left (Or.inr ⟨trivial, List.mem_append_right _ (List.mem_singleton_self i)⟩)]
            linarith [hzero]
          · rw [ite_eq_right hri]
            by_cases hrp : r ∈ p
            · have hC0 : C r q = 0 := by
                simp only [hC, givensQRJunkClean, of_apply]
                rw [ite_eq_left (Or.inr ⟨trivial, hrp⟩)]
              simp only [hC', givensQRJunkClean, of_apply]
              rw [ite_eq_left (Or.inr ⟨trivial, List.mem_append_left _ hrp⟩), hC0, sub_self]
            · simp only [hC', givensQRJunkClean, of_apply]
              rw [ite_eq_right (fun h => by
                rcases h with h | h
                · omega
                · rcases List.mem_append.1 h.2 with h' | h'
                  · exact hrp h'
                  · exact hri (List.mem_singleton.1 h')),
                hrows r q hra hri, hCcol r hrp, sub_self]
        · simp only [col_apply, Matrix.sub_apply, hGC, ↓reduceIte,
            hCcol a hai', hCcol i hii']
          simp only [hC', givensQRJunkClean, of_apply]
          rw [ite_eq_right (fun h => by
            rcases h with h | h
            · omega
            · rcases List.mem_append.1 h.2 with h' | h'
              · exact hai' h'
              · exact hai (List.mem_singleton.1 h'))]
          exact hda
      · -- a column not yet reached
        have hCcol : C.col q = B.col q := by
          ext r
          simp only [col_apply, hC, givensQRJunkClean, of_apply]
          rw [ite_eq_right (fun h => by omega)]
        have hC'col : C'.col q = B'.col q := by
          ext r
          simp only [col_apply, hC', givensQRJunkClean, of_apply]
          rw [ite_eq_right (fun h => by omega)]
        have hcol : (C' - (givensRotation a i c s)ᵀ * C).col q =
            B'.col q - (planeRotation a i c (-s))ᵀ *ᵥ B.col q := by
          rw [show (C' - (givensRotation a i c s)ᵀ * C).col q =
              C'.col q - ((givensRotation a i c s)ᵀ * C).col q from rfl,
            col_mul_eq_mulVec, hCcol, hC'col]
          rfl
        rw [hcol, hCcol]
        exact norm_sub_le_of_roundsGivensApply (show ((13 + 2 : ℕ) : ℝ) * fp.u < 1 from hu) hai
          hcs1 hc hs (hrel ⟨q, (hmem q).2 hq.le⟩)
    obtain ⟨E', hE'eq, hE'⟩ := exists_mul_eq_add_of_step hQ hG hQE hε hE hF
    exact ⟨Q * givensRotation a i c s, mul_mem hQ hG, E', hE'eq, hE'⟩
  -- the loop over the rows of column `j`
  have hcolumn : ∀ (jj : Fin n) (B : Matrix (Fin m) (Fin n) ℝ) (t : ℕ), J jj [] B t →
      ∀ B' ∈ ((((List.finRange m).filter (fun i : Fin m => (jj : ℕ) < i)).reverse).foldlM
        (fun (B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) => do
          let cs ← algorithm_5_1_3 fp.round (B (rowAbove i) jj) (B i jj)
          givensApplyLeft fp.round (rowAbove i) i cs.1 cs.2 (indexFrom n jj) B) B).run,
      J jj ((List.finRange m).filter (fun i : Fin m => (jj : ℕ) < i)).reverse B'
        (t + (((List.finRange m).filter (fun i : Fin m => (jj : ℕ) < i)).reverse).length) := by
    intro jj B t hI
    have hpw : ((List.finRange m).filter (fun i : Fin m => (jj : ℕ) < i)).reverse.Pairwise
        (fun a b => b < a) :=
      List.pairwise_reverse.2 (((List.sortedLT_finRange m).pairwise).filter _)
    refine SetM.forall_mem_run_foldlM (fun p B => J jj p B (t + p.length)) (by simpa using hI) ?_
    intro p x q hl c hc c' hc'
    simp only [SetM.mem_run_bind] at hc'
    obtain ⟨cs, hcs, hc'⟩ := hc'
    have hx : x ∈ ((List.finRange m).filter (fun i : Fin m => (jj : ℕ) < i)).reverse := by
      rw [hl]; simp
    have hpx : ∀ r ∈ p, x < r := by
      intro r hr
      rw [hl, List.pairwise_append] at hpw
      exact hpw.2.2 r hr x List.mem_cons_self
    have := hrot jj p x c c' (t + p.length) cs (mem_rowsBelow_reverse.1 hx) hpx hc hcs hc'
    simpa [Nat.add_assoc] using this
  -- the loop over the columns
  have houter := SetM.forall_mem_run_foldlM_finRange
    (fun (k : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) => ∃ t ≤ m * k, J k [] B t)
    ⟨0, Nat.zero_le _, 1, one_mem _, 0, by
      ext r q
      simp [givensQRJunkClean], fun q => by
        rw [show (0 : Matrix (Fin m) (Fin n) ℝ).col q = 0 from rfl]; simp⟩ ?_ A' h
  · obtain ⟨t, ht, Q, hQ, E, hQE, hE⟩ := houter
    have hclean : givensQRJunkClean n [] A' = upperPart A' := by
      ext r q
      simp only [givensQRJunkClean, upperPart, of_apply, List.not_mem_nil, and_false, or_false]
      have hq := q.2
      split_ifs with h1 h2 h2
      · omega
      · rfl
      · rfl
      · exact absurd ⟨hq, by omega⟩ h1
    refine ⟨Q, hQ, E, by rw [← hclean]; exact hQE, fun q => (hE q).trans ?_⟩
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 : (1 : ℝ) ≤ 1 + ε := by linarith
    linarith [pow_le_pow_right₀ h1 (show t ≤ m * n from ht)]
  · intro jj B hI B' hB'
    obtain ⟨t, ht, hJ0⟩ := hI
    have hJ1 := hcolumn jj B t hJ0 B' hB'
    set L := ((List.finRange m).filter (fun i : Fin m => (jj : ℕ) < i)).reverse with hL
    have hlen : L.length ≤ m := by
      rw [hL, List.length_reverse]
      exact (List.length_filter_le _ _).trans (by simp)
    refine ⟨t + L.length, by nlinarith, ?_⟩
    have hsame : givensQRJunkClean jj L B' = givensQRJunkClean (jj + 1) [] B' := by
      ext r q
      simp only [givensQRJunkClean, of_apply, List.not_mem_nil, and_false, or_false, hL,
        mem_rowsBelow_reverse]
      congr 1
      apply propext
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> omega
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr ⟨h, by omega⟩
    obtain ⟨Q, hQ, E, hQE, hE⟩ := hJ1
    exact ⟨Q, hQ, E, by rw [← hsame]; exact hQE, hE⟩

end GivensQRRounding'

end Givens

/-! ### §5.2.7–5.2.8 Gram–Schmidt -/

section GramSchmidt

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One step `k` of classical Gram–Schmidt: `R(1:k-1, k) = Q(:, 1:k-1)ᵀ A(:, k)`,
`z = A(:, k) - Q(:, 1:k-1) R(1:k-1, k)`, `R(k, k) = ‖z‖₂`, `Q(:, k) = z / R(k, k)`. -/
noncomputable def cgsStep (A : Matrix (Fin m) (Fin n) ℝ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let prev := (List.finRange n).filter (· < k)
  let R ← prev.foldlM (fun (R : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) => do
    let r ← Chapter01.algorithm_1_1_1 rnd (fun p => st.1 p i) (fun p => A p k)
    pure (R.updateRow i (Function.update (R i) k r))) st.2
  let z ← if prev = [] then pure (fun p => A p k) else
    (List.finRange m).foldlM (fun (z : Fin m → ℝ) (p : Fin m) => do
      let s ← dotAccum rnd prev (st.1 p) (fun i => R i k) 0
      let d ← rnd (A p k - s)
      pure (Function.update z p d)) 0
  let rkk ← rnd √(← Chapter01.algorithm_1_1_1 rnd z z)
  let q ← (List.finRange m).foldlM (fun (q : Fin m → ℝ) (p : Fin m) => do
    let d ← rnd (z p / rkk)
    pure (Function.update q p d)) 0
  pure (st.1.updateCol k q, R.updateRow k (Function.update (R k) k rkk))

/-- **§5.2.7, classical Gram–Schmidt (CGS)**:
```
R(1,1) = ‖A(:,1)‖₂;  Q(:,1) = A(:,1)/R(1,1)
for k = 2:n
    R(1:k-1, k) = Q(1:m, 1:k-1)ᵀ A(1:m, k)
    z = A(1:m, k) - Q(1:m, 1:k-1) R(1:k-1, k)
    R(k, k) = ‖z‖₂
    Q(1:m, k) = z/R(k, k)
end
```
The first step is the loop body with no previous columns (`z = A(:, 1)`, no subtraction
performed; `cgsStep`); dot products are Algorithm 1.1.1, the norm is `√` of a dot product. -/
noncomputable def classicalGramSchmidt (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (cgsStep rnd A) (0, 0)

/-- The inner loop body of Algorithm 5.2.6 for a column `j > k`:
`R(k, j) = Q(:, k)ᵀ A(:, j)` (Algorithm 1.1.1) and `A(:, j) = A(:, j) - Q(:, k) R(k, j)`. -/
noncomputable def mgsInner (q : Fin m → ℝ) (k : Fin n)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let rkj ← Chapter01.algorithm_1_1_1 rnd q (fun p => st.1 p j)
  let a ← (List.finRange m).foldlM (fun (a : Fin m → ℝ) (p : Fin m) => do
    let t ← rnd (q p * rkj)
    let d ← rnd (a p - t)
    pure (Function.update a p d)) (fun p => st.1 p j)
  pure (st.1.updateCol j a, st.2.updateRow k (Function.update (st.2 k) j rkj))

/-- One step `k` of Algorithm 5.2.6: `R(k, k) = ‖A(:, k)‖₂`, `Q(:, k) = A(:, k)/R(k, k)`, then
the inner loop over `j = k+1:n` (body `mgsInner`). The state is the working array, `Q` and `R`. -/
noncomputable def mgsStep
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let rkk ← rnd √(← Chapter01.algorithm_1_1_1 rnd (fun p => st.1 p k) (fun p => st.1 p k))
  let q ← (List.finRange m).foldlM (fun (q : Fin m → ℝ) (p : Fin m) => do
    let d ← rnd (st.1 p k / rkk)
    pure (Function.update q p d)) 0
  let st' ← ((List.finRange n).filter (k < ·)).foldlM (mgsInner rnd q k)
    (st.1, st.2.2.updateRow k (Function.update (st.2.2 k) k rkk))
  pure (st'.1, st.2.1.updateCol k q, st'.2)

/-- **Algorithm 5.2.6 (Modified Gram–Schmidt)**: "Given `A ∈ ℝ^{m×n}` with `rank(A) = n`, the
following algorithm computes the thin QR factorization `A = Q₁R₁`":
```
for k = 1:n
    R(k, k) = ‖A(1:m, k)‖₂
    Q(1:m, k) = A(1:m, k)/R(k, k)
    for j = k+1:n
        R(k, j) = Q(1:m, k)ᵀ A(1:m, j)
        A(1:m, j) = A(1:m, j) - Q(1:m, k) R(k, j)
    end
end
```
The working array `A` is part of the state; the result is `(Q, R)`. -/
noncomputable def algorithm_5_2_6 (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let st ← (List.finRange n).foldlM (mgsStep rnd) (A, 0, 0)
  pure (st.2.1, st.2.2)

end Programs

/-- A loop writing entry `(i, k)` of a matrix, for each listed `i`, from a value independent of the
state, writes the listed entries of column `k` and keeps the others. -/
theorem foldl_updateRow_update_eq {α : Type*} (g : Fin n → α) (k : Fin n) (l : List (Fin n))
    (R : Matrix (Fin n) (Fin n) α) :
    l.foldl (fun (R : Matrix (Fin n) (Fin n) α) i => R.updateRow i (Function.update (R i) k (g i)))
      R = of fun i j => if j = k ∧ i ∈ l then g i else R i j := by
  induction l generalizing R with
  | nil => ext i j; simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    ext i j
    simp only [of_apply, updateRow_apply, Function.update_apply, List.mem_cons]
    by_cases hj : j = k <;> by_cases hi : i ∈ l <;> by_cases hia : i = a <;> simp_all

/-- The CGS residual `z = a_k - ∑_{i<k} (q_iᵀ a_k) q_i`. -/
noncomputable def cgsResidual (Q : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (k : Fin n) : Fin m → ℝ :=
  A.col k - ∑ i ∈ Finset.univ.filter (· < k), (Q.col i ⬝ᵥ A.col k) • Q.col i

/-- The exact step of classical Gram–Schmidt. -/
theorem cgsStep_pure (A : Matrix (Fin m) (Fin n) ℝ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Id.run (cgsStep pure A st k) =
      (st.1.updateCol k ((√(cgsResidual st.1 A k ⬝ᵥ cgsResidual st.1 A k))⁻¹ •
          cgsResidual st.1 A k),
        of fun i j => if j = k ∧ i < k then st.1.col i ⬝ᵥ A.col k
          else if j = k ∧ i = k then √(cgsResidual st.1 A k ⬝ᵥ cgsResidual st.1 A k)
          else st.2 i j) := by
  have hmem : ∀ i : Fin n, i ∈ (List.finRange n).filter (· < k) ↔ i < k := fun i => by simp
  have hR : List.foldl (fun (R : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) =>
        R.updateRow i (Function.update (R i) k ((fun p => st.1 p i) ⬝ᵥ fun p => A p k))) st.2
        ((List.finRange n).filter (· < k)) =
      of fun i j => if j = k ∧ i < k then st.1.col i ⬝ᵥ A.col k else st.2 i j := by
    rw [foldl_updateRow_update_eq (fun i => (fun p => st.1 p i) ⬝ᵥ fun p => A p k)]
    ext i j
    simp only [of_apply, hmem]
    rfl
  have hsum : ∀ f : Fin n → ℝ, (((List.finRange n).filter (· < k)).map f).sum =
      ∑ i ∈ Finset.univ.filter (· < k), f i := by
    intro f
    rw [← List.sum_toFinset f ((List.nodup_finRange n).filter _)]
    congr 1
    ext i
    simp
  -- the common tail of both branches, once the residual is identified
  have key : ∀ z : Fin m → ℝ, z = cgsResidual st.1 A k →
      (st.1.updateCol k (List.foldl (fun (q : Fin m → ℝ) (p : Fin m) =>
          Function.update q p (z p / √(z ⬝ᵥ z))) 0 (List.finRange m)),
        (of fun i j => if j = k ∧ i < k then st.1.col i ⬝ᵥ A.col k else st.2 i j :
          Matrix (Fin n) (Fin n) ℝ).updateRow k (Function.update
          ((of fun i j => if j = k ∧ i < k then st.1.col i ⬝ᵥ A.col k else st.2 i j :
            Matrix (Fin n) (Fin n) ℝ) k) k √(z ⬝ᵥ z))) =
      (st.1.updateCol k ((√(cgsResidual st.1 A k ⬝ᵥ cgsResidual st.1 A k))⁻¹ •
          cgsResidual st.1 A k),
        of fun i j => if j = k ∧ i < k then st.1.col i ⬝ᵥ A.col k
          else if j = k ∧ i = k then √(cgsResidual st.1 A k ⬝ᵥ cgsResidual st.1 A k)
          else st.2 i j) := by
    rintro z rfl
    refine Prod.ext ?_ ?_
    · simp only
      congr 1
      rw [List.foldl_update_eq_ite]
      funext p
      simp only [List.mem_finRange, ↓reduceIte, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    · simp only
      ext i j
      simp only [updateRow_apply, Function.update_apply, of_apply]
      by_cases hik : i = k
      · subst hik
        by_cases hjk : j = i <;> simp [hjk]
      · simp [hik]
  have hres : ∀ p, cgsResidual st.1 A k p =
      A p k - ∑ i ∈ Finset.univ.filter (· < k), st.1 p i * (st.1.col i ⬝ᵥ A.col k) := by
    intro p
    simp only [cgsResidual, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      col_apply, mul_comm]
  unfold cgsStep
  by_cases h0 : (List.finRange n).filter (· < k) = []
  · simp only [h0, ↓reduceIte, Id.run_bind, Id.run_pure, List.idRun_foldlM,
      Chapter01.algorithm_1_1_1_spec]
    rw [← h0, hR]
    refine key _ (funext fun p => ?_)
    rw [hres]
    have : Finset.univ.filter (fun i : Fin n => i < k) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hi
      have := (hmem i).2 hi
      rw [h0] at this
      exact List.not_mem_nil this
    rw [this, Finset.sum_empty, sub_zero]
  · simp only [h0, ↓reduceIte, Id.run_bind, Id.run_pure, List.idRun_foldlM,
      Chapter01.algorithm_1_1_1_spec, dotAccum_id, hR]
    refine key _ (funext fun p => ?_)
    rw [List.foldl_update_eq_ite]
    simp only [List.mem_finRange, ↓reduceIte, zero_add, hsum, of_apply, true_and]
    rw [hres]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ite_eq_left (Finset.mem_filter.1 hi).2]

/-- The invariant of classical Gram–Schmidt after `k` steps. -/
private def CGSInvariant (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j : Fin n, (i : ℕ) < k → (j : ℕ) < k →
      st.1.col i ⬝ᵥ st.1.col j = if i = j then 1 else 0) ∧
    (∀ j : Fin n, (j : ℕ) < k → A.col j = ∑ i, st.2 i j • st.1.col i) ∧
    (∀ i j : Fin n, j < i → st.2 i j = 0) ∧
    (∀ j : Fin n, (j : ℕ) < k → 0 < st.2 j j) ∧
    (∀ j : Fin n, k ≤ (j : ℕ) → st.1.col j = 0 ∧ ∀ i, st.2 i j = 0) ∧
    (∀ j : Fin n, (j : ℕ) < k → st.1.col j ∈ Submodule.span ℝ (Aᵀ '' {i | (i : ℕ) < k}))

/-- One step of classical Gram–Schmidt preserves the invariant (full column rank). -/
private theorem cgsInvariant_step {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ} (k : Fin n)
    (h : CGSInvariant A k st) : CGSInvariant A (k + 1) (Id.run (cgsStep pure A st k)) := by
  obtain ⟨Q, R⟩ := st
  obtain ⟨hon, hcol, hlow, hpos, hzero, hspan⟩ := h
  simp only at hon hcol hlow hpos hzero hspan
  rw [cgsStep_pure]
  dsimp only
  set z := cgsResidual Q A k with hz
  set ρ := √(z ⬝ᵥ z) with hρ
  -- the residual is orthogonal to the previous columns
  have hperp : ∀ j : Fin n, (j : ℕ) < k → Q.col j ⬝ᵥ z = 0 := by
    intro j hj
    rw [hz, cgsResidual, dotProduct_sub, dotProduct_sum]
    rw [Finset.sum_congr rfl fun i hi => by
      rw [dotProduct_smul, hon j i hj (by simpa using hi), smul_eq_mul]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, ite_eq_left (by simpa using hj), sub_self]
  -- the residual is nonzero, by independence
  have hz0 : z ≠ 0 := by
    intro h0
    have hmem : A.col k ∈ Submodule.span ℝ (Aᵀ '' {i | (i : ℕ) < k}) := by
      have : A.col k = ∑ i ∈ Finset.univ.filter (· < k), (Q.col i ⬝ᵥ A.col k) • Q.col i := by
        rw [← sub_eq_zero]; exact h0
      rw [this]
      exact Submodule.sum_mem _ fun i hi =>
        Submodule.smul_mem _ _ (hspan i (by simpa using hi))
    exact hA.notMem_span_image (s := {i | (i : ℕ) < k}) (x := k) (by simp) hmem
  have hzz : 0 < z ⬝ᵥ z := lt_of_le_of_ne (by rw [dotProduct_self_eq_norm_sq]; positivity)
    (fun e => hz0 (dotProduct_self_eq_zero.1 e.symm))
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hzz
  have hρρ : ρ * ρ = z ⬝ᵥ z := Real.mul_self_sqrt hzz.le
  have hcolQ : ∀ j : Fin n, (Q.updateCol k (ρ⁻¹ • z)).col j = if j = k then ρ⁻¹ • z else Q.col j :=
    fun j => by
      ext p
      by_cases hj : j = k
      · subst hj; simp
      · simp [hj]
  have hlt : ∀ j : Fin n, (j : ℕ) < k + 1 → j ≠ k → (j : ℕ) < k := fun j hj hjk => by
    have : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
    omega
  have hspan_mono : Submodule.span ℝ (Aᵀ '' {i : Fin n | (i : ℕ) < k}) ≤
      Submodule.span ℝ (Aᵀ '' {i : Fin n | (i : ℕ) < k + 1}) :=
    Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < k) => by
      change (i : ℕ) < k + 1; omega)
  refine ⟨fun i j hi hj => ?_, fun j hj => ?_, fun i j hij => ?_, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_⟩
  · -- orthonormality
    rw [hcolQ, hcolQ]
    by_cases hik : i = k <;> by_cases hjk : j = k
    · subst hik; subst hjk
      simp only [↓reduceIte, dotProduct_smul, smul_dotProduct, smul_eq_mul, ← hρρ]
      field_simp
    · subst hik
      simp only [↓reduceIte, hjk, Ne.symm hjk, smul_dotProduct, smul_eq_mul]
      rw [dotProduct_comm, hperp j (hlt j hj hjk), mul_zero]
    · subst hjk
      simp only [↓reduceIte, hik, dotProduct_smul, smul_eq_mul]
      rw [hperp i (hlt i hi hik), mul_zero]
    · simp only [hik, hjk, ↓reduceIte]
      exact hon i j (hlt i hi hik) (hlt j hj hjk)
  · -- the columns of `A`
    by_cases hjk : j = k
    · subst hjk
      have hterm : ∀ i : Fin n, (of fun i j' => if j' = j ∧ i < j then Q.col i ⬝ᵥ A.col j
            else if j' = j ∧ i = j then ρ else R i j' : Matrix (Fin n) (Fin n) ℝ) i j •
            (if i = j then ρ⁻¹ • z else Q.col i) =
          (if i < j then (Q.col i ⬝ᵥ A.col j) • Q.col i else 0) + (if i = j then z else 0) := by
        intro i
        simp only [of_apply, true_and]
        rcases lt_trichotomy i j with hij | hij | hij
        · simp [hij, ne_of_lt hij]
        · subst hij
          simp only [lt_self_iff_false, ↓reduceIte, smul_smul, mul_inv_cancel₀ hρ0.ne', one_smul,
            zero_add]
        · have hne : i ≠ j := ne_of_gt hij
          simp only [not_lt.2 hij.le, ↓reduceIte, hne, add_zero]
          rw [(hzero j le_rfl).2 i, zero_smul]
      simp only [hcolQ]
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_ite_eq',
        ite_eq_left (Finset.mem_univ _), ← Finset.sum_filter, hz, cgsResidual]
      abel
    · have hj' := hlt j hj hjk
      rw [hcol j hj']
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [of_apply, hjk, false_and, ↓reduceIte, hcolQ]
      by_cases hik : i = k
      · subst hik
        rw [hlow i j (by exact_mod_cast hj'), zero_smul, zero_smul]
      · rw [ite_eq_right hik]
  · -- zeros below the diagonal
    simp only [of_apply]
    split_ifs with h1 h2
    · exact absurd (h1.1 ▸ h1.2) (not_lt.2 hij.le)
    · exact absurd (h2.1.trans h2.2.symm ▸ hij) (lt_irrefl _)
    · exact hlow i j hij
  · -- positive diagonal
    simp only [of_apply]
    by_cases hjk : j = k
    · subst hjk; simp only [lt_self_iff_false, and_false, ↓reduceIte, and_self]; exact hρ0
    · simp only [hjk, false_and, ↓reduceIte]; exact hpos j (hlt j hj hjk)
  · -- the unprocessed columns
    have hjk : j ≠ k := fun e => by rw [e] at hj; omega
    refine ⟨by rw [hcolQ]; simp only [hjk, ↓reduceIte]; exact (hzero j (by omega)).1,
      fun i => ?_⟩
    simp only [of_apply, hjk, false_and, ↓reduceIte]
    exact (hzero j (by omega)).2 i
  · -- the span
    rw [hcolQ]
    by_cases hjk : j = k
    · simp only [hjk, ↓reduceIte]
      rw [hz, cgsResidual]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
      · exact Submodule.subset_span ⟨k, by simp, rfl⟩
      · exact Submodule.sum_mem _ fun i hi =>
          Submodule.smul_mem _ _ (hspan_mono (hspan i (by simpa using hi)))
    · simp only [hjk, ↓reduceIte]
      exact hspan_mono (hspan j (hlt j hj hjk))

/-- **§5.2.7, classical Gram–Schmidt computes the thin QR factorization**: for `A` of full column
rank, the exact output `(Q, R)` satisfies `A = QR`, `QᵀQ = I`, `R` upper triangular with positive
diagonal. -/
theorem classicalGramSchmidt_spec (A : Matrix (Fin m) (Fin n) ℝ) (hA : LinearIndependent ℝ Aᵀ) :
    IsThinQR A (Id.run (classicalGramSchmidt pure A)).1 (Id.run (classicalGramSchmidt pure A)).2 ∧
      ∀ j, 0 < (Id.run (classicalGramSchmidt pure A)).2 j j := by
  have hall : ∀ j ≤ n, CGSInvariant A j (((List.finRange n).take j).foldl
      (fun st k => Id.run (cgsStep pure A st k)) (0, 0)) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun i _ hi => absurd hi (Nat.not_lt_zero _),
        fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl,
        fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ => ⟨?_, fun _ => rfl⟩,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      ext p; rfl
    | succ j ih =>
      intro hj
      rw [List.take_succ_eq_append_getElem (by simpa using hj), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have h := cgsInvariant_step hA ⟨j, by omega⟩ (ih (by omega))
      simpa using h
  obtain ⟨hon, hcol, hlow, hpos, -, -⟩ := hall n le_rfl
  rw [List.take_of_length_le (by simp)] at hon hcol hlow hpos
  have hprog : Id.run (classicalGramSchmidt pure A) =
      (List.finRange n).foldl (fun st k => Id.run (cgsStep pure A st k)) (0, 0) := by
    rw [classicalGramSchmidt, List.idRun_foldlM]
  rw [hprog]
  refine ⟨⟨?_, ?_, fun i j hij => hlow i j hij⟩, fun j => hpos j j.isLt⟩
  · ext p j
    have := congrFun (hcol j j.isLt) p
    rw [Matrix.mul_apply, show A p j = A.col j p from rfl, this, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  · ext i j
    have := hon i j i.isLt j.isLt
    simp only [Matrix.mul_apply, conjTranspose_apply, star_trivial]
    rw [one_apply, ← this]
    rfl

/-- A loop subtracting `q_p c` from each listed entry of a vector, once each. -/
theorem foldl_update_sub_mul (a₀ q : Fin m → ℝ) (c : ℝ) {l : List (Fin m)} (hl : l.Nodup) :
    l.foldl (fun (y : Fin m → ℝ) p => Function.update y p (y p - q p * c)) a₀ =
      fun p => if p ∈ l then a₀ p - q p * c else a₀ p := by
  induction l generalizing a₀ with
  | nil => funext p; simp
  | cons a l ih =>
    rcases List.nodup_cons.1 hl with ⟨ha, hl'⟩
    rw [List.foldl_cons, ih _ hl']
    funext p
    by_cases hp : p ∈ l
    · have hpa : p ≠ a := fun e => ha (e ▸ hp)
      simp [hp, hpa]
    · by_cases hpa : p = a
      · subst hpa; simp [hp]
      · simp [hp, hpa]

/-- The exact inner step of MGS. -/
theorem mgsInner_pure (q : Fin m → ℝ) (k : Fin n)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    Id.run (mgsInner pure q k st j) =
      (st.1.updateCol j (st.1.col j - (q ⬝ᵥ st.1.col j) • q),
        st.2.updateRow k (Function.update (st.2 k) j (q ⬝ᵥ st.1.col j))) := by
  simp only [mgsInner, Id.run_bind, Id.run_pure, List.idRun_foldlM,
    Chapter01.algorithm_1_1_1_spec]
  rw [foldl_update_sub_mul _ _ _ (List.nodup_finRange m)]
  congr 2
  funext p
  simp only [List.mem_finRange, ↓reduceIte, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, col_apply,
    mul_comm]
  rfl

/-- The exact inner loop of MGS over a duplicate-free list of columns other than `k`. -/
theorem foldl_mgsInner_pure (q : Fin m → ℝ) (k : Fin n) (l : List (Fin n)) (hl : l.Nodup)
    (W : Matrix (Fin m) (Fin n) ℝ) (R : Matrix (Fin n) (Fin n) ℝ) :
    l.foldl (fun st j => Id.run (mgsInner pure q k st j)) (W, R) =
      (of fun p j => if j ∈ l then W p j - (q ⬝ᵥ W.col j) * q p else W p j,
        of fun i j => if i = k ∧ j ∈ l then q ⬝ᵥ W.col j else R i j) := by
  induction l generalizing W R with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, ite_false, and_false]; rfl
  | cons a l ih =>
    rcases List.nodup_cons.1 hl with ⟨ha, hl'⟩
    rw [List.foldl_cons, mgsInner_pure, ih hl']
    have hcol : ∀ j, j ∈ l → (W.updateCol a (W.col a - (q ⬝ᵥ W.col a) • q)).col j = W.col j :=
      fun j hj => by
        have hja : j ≠ a := fun e => ha (e ▸ hj)
        ext p; simp [hja]
    refine Prod.ext ?_ ?_
    · ext p j
      simp only [of_apply, List.mem_cons]
      by_cases hj : j ∈ l
      · have hja : j ≠ a := fun e => ha (e ▸ hj)
        simp only [hj, ↓reduceIte, or_true, hcol j hj, updateCol_apply, hja]
      · by_cases hja : j = a
        · subst hja; simp [hj]
        · simp [hj, hja]
    · ext i j
      simp only [of_apply, List.mem_cons]
      by_cases hj : j ∈ l
      · have hja : j ≠ a := fun e => ha (e ▸ hj)
        by_cases hik : i = k
        · simp [hik, hj, hcol j hj]
        · simp [hik, hj, updateRow_apply]
      · by_cases hja : j = a
        · subst hja; by_cases hik : i = k <;> simp [hik, hj, updateRow_apply]
        · by_cases hik : i = k <;> simp [hik, hj, hja, updateRow_apply]

/-- The exact step of MGS. -/
theorem mgsStep_pure
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n) :
    Id.run (mgsStep pure st k) =
      (of fun p j => if k < j then st.1 p j -
          (((√(st.1.col k ⬝ᵥ st.1.col k))⁻¹ • st.1.col k) ⬝ᵥ st.1.col j) *
            ((√(st.1.col k ⬝ᵥ st.1.col k))⁻¹ • st.1.col k) p
          else st.1 p j,
        st.2.1.updateCol k ((√(st.1.col k ⬝ᵥ st.1.col k))⁻¹ • st.1.col k),
        of fun i j => if i = k ∧ k < j then
            ((√(st.1.col k ⬝ᵥ st.1.col k))⁻¹ • st.1.col k) ⬝ᵥ st.1.col j
          else (st.2.2.updateRow k (Function.update (st.2.2 k) k
            √(st.1.col k ⬝ᵥ st.1.col k))) i j) := by
  have hq : List.foldl (fun (q : Fin m → ℝ) (p : Fin m) =>
      Function.update q p (st.1 p k / √((fun p => st.1 p k) ⬝ᵥ fun p => st.1 p k))) 0
        (List.finRange m) = (√(st.1.col k ⬝ᵥ st.1.col k))⁻¹ • st.1.col k := by
    rw [List.foldl_update_eq_ite]
    funext p
    simp only [List.mem_finRange, ↓reduceIte, Pi.smul_apply, smul_eq_mul, col_apply,
      div_eq_inv_mul]
    rfl
  simp only [mgsStep, Id.run_bind, Id.run_pure, List.idRun_foldlM,
    Chapter01.algorithm_1_1_1_spec, hq]
  rw [foldl_mgsInner_pure _ _ _ ((List.nodup_finRange n).filter _)]
  simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq, true_and]
  rfl

/-- The invariant of MGS after `k` steps (working array `W`, `Q`, `R`). -/
private def MGSInvariant (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :
    Prop :=
  (∀ i j : Fin n, (i : ℕ) < k → (j : ℕ) < k →
      st.2.1.col i ⬝ᵥ st.2.1.col j = if i = j then 1 else 0) ∧
    (∀ j : Fin n, (j : ℕ) < k → A.col j = ∑ i, st.2.2 i j • st.2.1.col i) ∧
    (∀ j : Fin n, k ≤ (j : ℕ) → A.col j = st.1.col j + ∑ i, st.2.2 i j • st.2.1.col i) ∧
    (∀ i j : Fin n, (i : ℕ) < k → k ≤ (j : ℕ) → st.2.1.col i ⬝ᵥ st.1.col j = 0) ∧
    (∀ i j : Fin n, j < i → st.2.2 i j = 0) ∧
    (∀ i : Fin n, k ≤ (i : ℕ) → (∀ j, st.2.2 i j = 0) ∧ st.2.1.col i = 0) ∧
    (∀ j : Fin n, (j : ℕ) < k → 0 < st.2.2 j j) ∧
    (∀ j : Fin n, (j : ℕ) < k → st.2.1.col j ∈ Submodule.span ℝ (Aᵀ '' {i | (i : ℕ) < k}))


/-- One step of modified Gram–Schmidt preserves the invariant (full column rank). -/
private theorem mgsInvariant_step {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    {st : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ}
    (k : Fin n) (h : MGSInvariant A k st) :
    MGSInvariant A (k + 1) (Id.run (mgsStep pure st k)) := by
  obtain ⟨W, Q, R⟩ := st
  obtain ⟨hon, hcol, hwork, hperp, hlow, hzero, hpos, hspan⟩ := h
  simp only at hon hcol hwork hperp hlow hzero hpos hspan
  rw [mgsStep_pure]
  unfold MGSInvariant
  dsimp only
  set w := W.col k with hw
  set ρ := √(w ⬝ᵥ w) with hρ
  set q := ρ⁻¹ • w with hq
  have hsumk : ∀ j : Fin n, ∑ i, R i j • Q.col i =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), R i j • Q.col i := by
    intro j
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => (i : ℕ) < k)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < k))
      fun i hi => by rw [(hzero i (not_lt.1 (Finset.mem_filter.1 hi).2)).1 j, zero_smul],
      add_zero]
  -- the working column `k` is nonzero, by independence
  have hw0 : w ≠ 0 := by
    intro h0
    have hmem : A.col k ∈ Submodule.span ℝ (Aᵀ '' {i | (i : ℕ) < k}) := by
      rw [hwork k le_rfl, ← hw, h0, zero_add, hsumk]
      exact Submodule.sum_mem _ fun i hi =>
        Submodule.smul_mem _ _ (hspan i (Finset.mem_filter.1 hi).2)
    exact hA.notMem_span_image (s := {i | (i : ℕ) < k}) (x := k) (by simp) hmem
  have hww : 0 < w ⬝ᵥ w := lt_of_le_of_ne (by rw [dotProduct_self_eq_norm_sq]; positivity)
    (fun e => hw0 (dotProduct_self_eq_zero.1 e.symm))
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hww
  have hρρ : ρ * ρ = w ⬝ᵥ w := Real.mul_self_sqrt hww.le
  have hqq : q ⬝ᵥ q = 1 := by
    rw [hq, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← hρρ]
    field_simp
  have hqperp : ∀ i : Fin n, (i : ℕ) < k → Q.col i ⬝ᵥ q = 0 := fun i hi => by
    rw [hq, dotProduct_smul, hperp i k hi le_rfl, smul_zero]
  have hρq : ρ • q = w := by rw [hq, smul_smul, mul_inv_cancel₀ hρ0.ne', one_smul]
  have hcolQ : ∀ j : Fin n, (Q.updateCol k q).col j = if j = k then q else Q.col j := fun j => by
    ext p
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj]
  have hcolW : ∀ j : Fin n, (of fun p j => if k < j then W p j - (q ⬝ᵥ W.col j) * q p
      else W p j : Matrix (Fin m) (Fin n) ℝ).col j =
        if k < j then W.col j - (q ⬝ᵥ W.col j) • q else W.col j := fun j => by
    ext p
    by_cases hj : k < j <;> simp [hj]
  have hRent : ∀ i j : Fin n, (of fun i j => if i = k ∧ k < j then q ⬝ᵥ W.col j
      else (R.updateRow k (Function.update (R k) k ρ)) i j : Matrix (Fin n) (Fin n) ℝ) i j =
        if i = k then (if k < j then q ⬝ᵥ W.col j else if j = k then ρ else R k j)
        else R i j := fun i j => by
    by_cases hik : i = k
    · subst hik
      by_cases hij : i < j
      · simp [hij]
      · by_cases hj : j = i <;> simp [hij, hj, updateRow_apply, Function.update_apply]
    · simp [hik, updateRow_apply]
  have hlt : ∀ j : Fin n, (j : ℕ) < k + 1 → j ≠ k → (j : ℕ) < k := fun j hj hjk => by
    have : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
    omega
  have hspan_mono : Submodule.span ℝ (Aᵀ '' {i : Fin n | (i : ℕ) < k}) ≤
      Submodule.span ℝ (Aᵀ '' {i : Fin n | (i : ℕ) < k + 1}) :=
    Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < k) => by
      change (i : ℕ) < k + 1; omega)
  refine ⟨fun i j hi hj => ?_, fun j hj => ?_, fun j hj => ?_, fun i j hi hj => ?_,
    fun i j hij => ?_, fun i hi => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · -- orthonormality
    rw [hcolQ, hcolQ]
    by_cases hik : i = k <;> by_cases hjk : j = k
    · subst hik; subst hjk; simp only [↓reduceIte]; exact hqq
    · subst hik
      simp only [↓reduceIte, hjk, Ne.symm hjk]
      rw [dotProduct_comm, hqperp j (hlt j hj hjk)]
    · subst hjk
      simp only [↓reduceIte, hik]
      exact hqperp i (hlt i hi hik)
    · simp only [hik, hjk, ↓reduceIte]
      exact hon i j (hlt i hi hik) (hlt j hj hjk)
  · -- the finished columns
    simp only [hcolQ, hRent]
    by_cases hjk : j = k
    · subst hjk
      rw [hwork j le_rfl]
      have hterm : ∀ i : Fin n, (if i = j then (if j < j then q ⬝ᵥ W.col j else if j = j then ρ
          else R j j) else R i j) • (if i = j then q else Q.col i) =
            (if i = j then w else 0) + R i j • Q.col i := by
        intro i
        by_cases hij : i = j
        · subst hij
          simp only [lt_self_iff_false, ↓reduceIte, hρq, (hzero i le_rfl).2, smul_zero,
            add_zero]
        · simp [hij]
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_ite_eq',
        ite_eq_left (Finset.mem_univ _)]
    · rw [hcol j (hlt j hj hjk)]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hik : i = k
      · subst hik
        have hji : j < i := hlt j hj hjk
        simp only [↓reduceIte, not_lt.2 hji.le, hjk, hlow i j hji, zero_smul]
      · simp [hik]
  · -- the working columns
    have hkj : k < j := by
      change (k : ℕ) < j; omega
    rw [hwork j (by omega), hcolW, ite_eq_left hkj]
    simp only [hcolQ, hRent]
    have hterm : ∀ i : Fin n, (if i = k then (if k < j then q ⬝ᵥ W.col j else if j = k then ρ
        else R k j) else R i j) • (if i = k then q else Q.col i) =
          (if i = k then (q ⬝ᵥ W.col j) • q else 0) + R i j • Q.col i := by
      intro i
      by_cases hik : i = k
      · subst hik
        simp only [↓reduceIte, hkj, (hzero i le_rfl).1, zero_smul, add_zero]
      · simp [hik]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_univ _)]
    abel
  · -- the working columns stay orthogonal to the finished ones
    have hkj : k < j := by
      change (k : ℕ) < j; omega
    rw [hcolQ, hcolW, ite_eq_left hkj]
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte, dotProduct_sub, dotProduct_smul, hqq, smul_eq_mul, mul_one,
        sub_self]
    · simp only [hik, ↓reduceIte, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      rw [hperp i j (hlt i hi hik) (by omega), hqperp i (hlt i hi hik), mul_zero, sub_zero]
  · -- zeros below the diagonal
    rw [hRent]
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte, not_lt.2 hij.le, ne_of_lt hij, hlow i j hij]
    · simp only [hik, ↓reduceIte]
      exact hlow i j hij
  · -- the unprocessed rows and columns
    have hik : i ≠ k := fun e => by rw [e] at hi; omega
    refine ⟨fun j => ?_, ?_⟩
    · rw [hRent]; simp only [hik, ↓reduceIte]; exact (hzero i (by omega)).1 j
    · rw [hcolQ]; simp only [hik, ↓reduceIte]; exact (hzero i (by omega)).2
  · -- positive diagonal
    rw [hRent]
    by_cases hjk : j = k
    · subst hjk; simp only [↓reduceIte, lt_self_iff_false]; exact hρ0
    · simp only [hjk, ↓reduceIte]; exact hpos j (hlt j hj hjk)
  · -- the span
    rw [hcolQ]
    by_cases hjk : j = k
    · subst hjk
      simp only [↓reduceIte]
      rw [hq, hw]
      refine Submodule.smul_mem _ _ ?_
      have hwk : W.col j = A.col j - ∑ i, R i j • Q.col i := by
        rw [hwork j le_rfl]; abel
      rw [hwk, hsumk]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨j, by simp, rfl⟩) ?_
      exact Submodule.sum_mem _ fun i hi =>
        Submodule.smul_mem _ _ (hspan_mono (hspan i (Finset.mem_filter.1 hi).2))
    · simp only [hjk, ↓reduceIte]
      exact hspan_mono (hspan j (hlt j hj hjk))

/-- **Algorithm 5.2.6 (MGS) computes the thin QR factorization**: "Given `A ∈ ℝ^{m×n}` with
`rank(A) = n`, the following algorithm computes the thin QR factorization `A = Q₁R₁` where
`Q₁ ∈ ℝ^{m×n}` has orthonormal columns and `R₁ ∈ ℝ^{n×n}` is upper triangular" (with positive
diagonal). Invariant: after step `k` the working column `j > k` is `a_j - ∑_{i≤k} r_ij q_i`,
orthogonal to `q_0, …, q_k`. -/
theorem algorithm_5_2_6_spec (A : Matrix (Fin m) (Fin n) ℝ) (hA : LinearIndependent ℝ Aᵀ) :
    IsThinQR A (Id.run (algorithm_5_2_6 pure A)).1 (Id.run (algorithm_5_2_6 pure A)).2 ∧
      ∀ j, 0 < (Id.run (algorithm_5_2_6 pure A)).2 j j := by
  have hall : ∀ j ≤ n, MGSInvariant A j (((List.finRange n).take j).foldl
      (fun st k => Id.run (mgsStep pure st k)) (A, 0, 0)) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun i _ hi => absurd hi (Nat.not_lt_zero _),
        fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ => ?_,
        fun i _ hi => absurd hi (Nat.not_lt_zero _), fun _ _ _ => rfl,
        fun i _ => ⟨fun _ => rfl, ?_⟩, fun j hj => absurd hj (Nat.not_lt_zero _),
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      · simp only [List.take_zero, List.foldl_nil]
        rw [Finset.sum_eq_zero fun i _ => by simp, add_zero]
      · ext p; rfl
    | succ j ih =>
      intro hj
      rw [List.take_succ_eq_append_getElem (by simpa using hj), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have h := mgsInvariant_step hA ⟨j, by omega⟩ (ih (by omega))
      simpa using h
  obtain ⟨hon, hcol, -, -, hlow, -, hpos, -⟩ := hall n le_rfl
  rw [List.take_of_length_le (by simp)] at hon hcol hlow hpos
  have hprog : Id.run (algorithm_5_2_6 pure A) =
      (((List.finRange n).foldl (fun st k => Id.run (mgsStep pure st k)) (A, 0, 0)).2.1,
        ((List.finRange n).foldl (fun st k => Id.run (mgsStep pure st k)) (A, 0, 0)).2.2) := by
    simp only [algorithm_5_2_6, Id.run_bind, Id.run_pure, List.idRun_foldlM]
  rw [hprog]
  refine ⟨⟨?_, ?_, fun i j hij => hlow i j hij⟩, fun j => hpos j j.isLt⟩
  · ext p j
    have := congrFun (hcol j j.isLt) p
    rw [Matrix.mul_apply, show A p j = A.col j p from rfl, this, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  · ext i j
    have := hon i j i.isLt j.isLt
    simp only [Matrix.mul_apply, conjTranspose_apply, star_trivial]
    rw [one_apply, ← this]
    rfl

/-- **§5.2.8**: MGS is "a rearrangement of the calculation" of CGS — in exact arithmetic the two
compute the same thin QR factorization of a full-column-rank matrix (`Matrix.IsThinQR.unique`). -/
theorem algorithm_5_2_6_eq_classicalGramSchmidt (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : LinearIndependent ℝ Aᵀ) :
    Id.run (algorithm_5_2_6 pure A) = Id.run (classicalGramSchmidt pure A) := by
  obtain ⟨h₁, hd₁⟩ := algorithm_5_2_6_spec A hA
  obtain ⟨h₂, hd₂⟩ := classicalGramSchmidt_spec A hA
  obtain ⟨hQ, hR⟩ := h₁.unique h₂ hd₁ hd₂
  exact Prod.ext hQ hR

/-- The columns of the orthonormal factor of a thin QR factorization are orthonormal. -/
theorem isThinQR_col_dotProduct_col {A Q : Matrix (Fin m) (Fin n) ℝ} {R : Matrix (Fin n) (Fin n) ℝ}
    (h : IsThinQR A Q R) (i j : Fin n) : Q.col i ⬝ᵥ Q.col j = if i = j then 1 else 0 := by
  have := congrFun (congrFun h.conjTranspose_mul_self i) j
  simp only [Matrix.mul_apply, conjTranspose_apply, star_trivial, one_apply] at this
  rw [← this]
  rfl

/-- **§5.2.8, the derivation of MGS**: for a thin QR factorization `A = Q₁R₁` (columns `q_i`, rows
`r_iᵀ`), `A - ∑_{i<k} q_i r_iᵀ = ∑_{i≥k} q_i r_iᵀ` (the book's `[0 | A^{(k)}]`: its columns `< k`
vanish), and if `r_kk > 0` then, for `A^{(k)} = [z | B]`, `r_kk = ‖z‖₂`, `q_k = z / r_kk` and
`[r_{k,k+1} ⋯ r_{kn}] = q_kᵀ B`. -/
theorem mgs_remainder_eq {A Q : Matrix (Fin m) (Fin n) ℝ} {R : Matrix (Fin n) (Fin n) ℝ}
    (h : IsThinQR A Q R) (k : Fin n) :
    A - ∑ i ∈ Finset.univ.filter (· < k), vecMulVec (Q.col i) (R i) =
        ∑ i ∈ Finset.univ.filter (k ≤ ·), vecMulVec (Q.col i) (R i) ∧
      (∀ j, j < k → (∑ i ∈ Finset.univ.filter (k ≤ ·), vecMulVec (Q.col i) (R i)).col j = 0) ∧
      (0 < R k k →
        R k k = ‖(toLp 2 ((∑ i ∈ Finset.univ.filter (k ≤ ·), vecMulVec (Q.col i) (R i)).col k) :
          EuclideanSpace ℝ (Fin m))‖ ∧
        Q.col k = (R k k)⁻¹ • (∑ i ∈ Finset.univ.filter (k ≤ ·), vecMulVec (Q.col i) (R i)).col k ∧
        ∀ j, k < j → R k j =
          Q.col k ⬝ᵥ (∑ i ∈ Finset.univ.filter (k ≤ ·), vecMulVec (Q.col i) (R i)).col j) := by
  set Ak := ∑ i ∈ Finset.univ.filter (k ≤ ·), vecMulVec (Q.col i) (R i) with hAk
  have hA : A = ∑ i, vecMulVec (Q.col i) (R i) := by
    rw [← h.mul_eq, Chapter01.equation_1_1_4]
    rfl
  have hsplit : A - ∑ i ∈ Finset.univ.filter (· < k), vecMulVec (Q.col i) (R i) = Ak := by
    rw [hA, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· < k), add_sub_cancel_left, hAk]
    congr 1
    ext i
    simp
  -- the columns of `A^{(k)}`
  have hcol : ∀ j, Ak.col j = ∑ i ∈ Finset.univ.filter (k ≤ ·), R i j • Q.col i := by
    intro j
    ext p
    simp only [hAk, col_apply, Matrix.sum_apply, vecMulVec_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm]
  have hup : ∀ i j : Fin n, j < i → R i j = 0 := fun i j hij => h.isUpperTriangular hij
  have hon := isThinQR_col_dotProduct_col h
  have hkk : Q.col k ⬝ᵥ Q.col k = 1 := by simpa using hon k k
  have hcolk : Ak.col k = R k k • Q.col k := by
    rw [hcol, Finset.sum_eq_single k (fun i hi hik => by
      rw [hup i k (lt_of_le_of_ne (Finset.mem_filter.1 hi).2 (Ne.symm hik)), zero_smul])
      (by simp)]
  refine ⟨hsplit, fun j hj => ?_, fun hk => ⟨?_, ?_, fun j hj => ?_⟩⟩
  · rw [hcol]
    exact Finset.sum_eq_zero fun i hi => by
      rw [hup i j (lt_of_lt_of_le hj (Finset.mem_filter.1 hi).2), zero_smul]
  · rw [hcolk, toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    have : ‖(toLp 2 (Q.col k) : EuclideanSpace ℝ (Fin m))‖ = 1 := by
      have h1 := hkk
      rw [dotProduct_self_eq_norm_sq] at h1
      nlinarith [norm_nonneg (toLp 2 (Q.col k) : EuclideanSpace ℝ (Fin m))]
    rw [this, mul_one]
  · rw [hcolk, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  · rw [hcol, dotProduct_sum]
    rw [Finset.sum_eq_single k (fun i hi hik => by
      rw [dotProduct_smul, hon k i, ite_eq_right_iff.2 (fun e => absurd e.symm hik),
        smul_zero]) (by simp)]
    rw [dotProduct_smul, hkk, smul_eq_mul, mul_one]

end GramSchmidt

/-! ### §5.2.4 Recursive block Householder QR -/

section BlockQR

/-- The column split of Algorithm 5.2.3, `Fin (n/2) ⊕ Fin (n - n/2) ≃ Fin n`: the first
`n₁ = ⌊n/2⌋` columns (`Sum.inl`) and the remaining `n - n₁` (`Sum.inr`). -/
def blockSplit (n : ℕ) : Fin (n / 2) ⊕ Fin (n - n / 2) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- The left block of `blockSplit` is the first `⌊n/2⌋` indices. -/
@[simp]
theorem blockSplit_inl_val {n : ℕ} (a : Fin (n / 2)) :
    ((blockSplit n (Sum.inl a) : Fin n) : ℕ) = a := by
  simp [blockSplit]

/-- The right block of `blockSplit` is the indices from `⌊n/2⌋` on. -/
@[simp]
theorem blockSplit_inr_val {n : ℕ} (b : Fin (n - n / 2)) :
    ((blockSplit n (Sum.inr b) : Fin n) : ℕ) = n / 2 + b := by
  simp [blockSplit]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The base case of Algorithm 5.2.3: the thin factorization `A = Q₁ R₁` from Algorithm 5.2.1,
with `Q₁` the first `n` columns of the product of the stored reflectors (accumulated by
`backwardAccumulation` with the returned `β`) and `R₁` the first `n` rows of the upper triangle of
the overwritten array (entries past row `m` read as `0`, so the program is total). -/
noncomputable def thinHouseholderQR {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let st ← algorithm_5_2_1 rnd A
  let Q ← backwardAccumulation rnd (storedReflectors st.1 st.2)
  pure (of fun i j => if hj : (j : ℕ) < m then Q i ⟨j, hj⟩ else 0,
    of fun i j => if hi : (i : ℕ) < m then upperPart st.1 ⟨i, hi⟩ j else 0)

/-- **Algorithm 5.2.3 (Recursive Block Householder QR)**: "Suppose `A ∈ ℝ^{m×n}` has full column
rank and `n_b` is a positive integer. The following algorithm computes `Q₁ ∈ ℝ^{m×n}` with
orthonormal columns and upper triangular `R₁ ∈ ℝ^{n×n}` such that `A = Q₁R₁`":
```
function [Q₁, R₁] = BlockQR(A, n, n_b)
if n ≤ n_b
    Use Algorithm 5.2.1 to compute the thin QR factorization A = Q₁R₁.
else
    n₁ = floor(n/2)
    [Q₁, R₁₁] = BlockQR(A(:, 1:n₁), n₁, n_b)
    R₁₂ = Q₁ᵀ A(:, n₁+1:n)
    A(:, n₁+1:n) = A(:, n₁+1:n) - Q₁R₁₂
    [Q₂, R₂₂] = BlockQR(A(:, n₁+1:n), n - n₁, n_b)
    Q₁ = [Q₁ | Q₂],  R₁ = [R₁₁ R₁₂; 0 R₂₂]
end
```
Well-founded recursion on `n`; the column blocks are recursion arguments, split and reassembled
along `blockSplit n`. The two matrix products are Algorithm 1.1.5 (`R₁₂ = 0 + Q₁ᵀA₂`,
`A₂ + (-Q₁)R₁₂`). The base case is taken also when `n ≤ 1` (for `n_b = 0` the book's recursion
would not terminate at `n = 1`). -/
noncomputable def algorithm_5_2_3 (nb : ℕ) {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  if _h : n ≤ nb ∨ n ≤ 1 then thinHouseholderQR rnd A
  else do
    let QR₁ ← algorithm_5_2_3 nb (A.submatrix id (blockSplit n ∘ Sum.inl))
    let R₁₂ ← Chapter01.algorithm_1_1_5 rnd QR₁.1ᵀ (A.submatrix id (blockSplit n ∘ Sum.inr)) 0
    let A₂ ← Chapter01.algorithm_1_1_5 rnd (-QR₁.1) R₁₂ (A.submatrix id (blockSplit n ∘ Sum.inr))
    let QR₂ ← algorithm_5_2_3 nb A₂
    pure ((fromCols QR₁.1 QR₂.1).submatrix id (blockSplit n).symm,
      (fromBlocks QR₁.2 R₁₂ 0 QR₂.2).submatrix (blockSplit n).symm (blockSplit n).symm)
termination_by n
decreasing_by all_goals omega

end Programs

/-- Full column rank makes `x ↦ Ax` injective. -/
theorem eq_zero_of_mulVec_eq_zero_of_linearIndependent {k : ℕ} {A : Matrix (Fin m) (Fin k) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) {x : Fin k → ℝ} (hx : A *ᵥ x = 0) : x = 0 := by
  have hA' := Fintype.linearIndependent_iff.mp hA
  funext i
  refine hA' x ?_ i
  ext p
  have := congrFun hx p
  simp only [mulVec, dotProduct, Pi.zero_apply] at this
  simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul, Pi.zero_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- A matrix with `Ax = 0 → x = 0` has full column rank. -/
theorem linearIndependent_transpose_of_mulVec {k : ℕ} {A : Matrix (Fin m) (Fin k) ℝ}
    (h : ∀ x, A *ᵥ x = 0 → x = 0) : LinearIndependent ℝ Aᵀ := by
  refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
  refine congrFun (h g ?_) i
  ext p
  have := congrFun hg p
  simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    Pi.zero_apply] at this
  simp only [mulVec, dotProduct, Pi.zero_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- A full-column-rank `m × k` matrix has `k ≤ m`. -/
theorem le_of_linearIndependent_transpose {k : ℕ} {A : Matrix (Fin m) (Fin k) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) : k ≤ m := by
  simpa using hA.fintype_card_le_finrank

/-- The triangular factor of a thin QR factorization of a full-column-rank matrix is
nonsingular. -/
theorem isUnit_of_isThinQR {k : ℕ} {A Q : Matrix (Fin m) (Fin k) ℝ} {R : Matrix (Fin k) (Fin k) ℝ}
    (h : IsThinQR A Q R) (hA : LinearIndependent ℝ Aᵀ) : IsUnit R := by
  rw [← mulVec_injective_iff_isUnit]
  intro x y hxy
  have : A *ᵥ (x - y) = 0 := by
    rw [← h.mul_eq, ← mulVec_mulVec, mulVec_sub]
    change Q *ᵥ (R *ᵥ x - R *ᵥ y) = 0
    rw [show R *ᵥ x = R *ᵥ y from hxy, sub_self, mulVec_zero]
  exact sub_eq_zero.1 (eq_zero_of_mulVec_eq_zero_of_linearIndependent hA this)

/-- Splitting a matrix along `blockSplit` gives its two column blocks. -/
theorem fromCols_blockSplit {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    fromCols (A.submatrix id (blockSplit n ∘ Sum.inl))
      (A.submatrix id (blockSplit n ∘ Sum.inr)) = A.submatrix id (blockSplit n) := by
  ext i (j | j) <;> rfl

/-- `A x` for `x` assembled from two blocks along `blockSplit`. -/
theorem mulVec_blockSplit {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin (n / 2) → ℝ)
    (v : Fin (n - n / 2) → ℝ) :
    A *ᵥ (fun j => Sum.elim u v ((blockSplit n).symm j)) =
      A.submatrix id (blockSplit n ∘ Sum.inl) *ᵥ u +
        A.submatrix id (blockSplit n ∘ Sum.inr) *ᵥ v := by
  ext p
  simp only [mulVec, dotProduct, Pi.add_apply, submatrix_apply, id, Function.comp_apply]
  rw [← Equiv.sum_comp (blockSplit n), Fintype.sum_sum_type]
  simp

/-- The base case of Algorithm 5.2.3 computes a thin QR factorization (`n ≤ m`). -/
theorem thinHouseholderQR_spec {n : ℕ} (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    IsThinQR A (Id.run (thinHouseholderQR pure A)).1 (Id.run (thinHouseholderQR pure A)).2 := by
  obtain ⟨hQR, -⟩ := algorithm_5_2_1_spec hnm A
  set st := Id.run (algorithm_5_2_1 pure A) with hst
  have hrun : Id.run (thinHouseholderQR pure A) =
      (of fun i (j : Fin n) => if hj : (j : ℕ) < m then
          Id.run (backwardAccumulation pure (storedReflectors st.1 st.2)) i ⟨j, hj⟩ else 0,
        of fun (i : Fin n) j => if hi : (i : ℕ) < m then upperPart st.1 ⟨i, hi⟩ j else 0) := rfl
  have e1 : (of fun i (j : Fin n) => if hj : (j : ℕ) < m then
      Id.run (backwardAccumulation pure (storedReflectors st.1 st.2)) i ⟨j, hj⟩ else 0) =
      firstColumns (factoredQ st.2 st.1) hnm := by
    ext i j
    have hj : (j : ℕ) < m := lt_of_lt_of_le j.isLt hnm
    simp only [of_apply, hj, ↓reduceDIte, backwardAccumulation_spec]
    rfl
  have e2 : (of fun (i : Fin n) j => if hi : (i : ℕ) < m then upperPart st.1 ⟨i, hi⟩ j else 0) =
      firstRows (upperPart st.1) hnm := by
    ext i j
    have hi : (i : ℕ) < m := lt_of_lt_of_le i.isLt hnm
    simp only [of_apply, hi, ↓reduceDIte]
    rfl
  rw [hrun, e1, e2]
  exact hQR.isThinQR hnm

private theorem algorithm_5_2_3_spec_aux (nb : ℕ) :
    ∀ n (A : Matrix (Fin m) (Fin n) ℝ), LinearIndependent ℝ Aᵀ →
      IsThinQR A (Id.run (algorithm_5_2_3 pure nb A)).1
        (Id.run (algorithm_5_2_3 pure nb A)).2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA
  rw [algorithm_5_2_3]
  split_ifs with h
  · exact thinHouseholderQR_spec (le_of_linearIndependent_transpose hA) A
  · have hn1 : n / 2 < n := by omega
    have hn2 : n - n / 2 < n := by omega
    set e := blockSplit n with he
    set A₁ := A.submatrix id (e ∘ Sum.inl) with hA₁
    set A₂ := A.submatrix id (e ∘ Sum.inr) with hA₂
    have hA₁i : LinearIndependent ℝ A₁ᵀ := hA.comp _ (e.injective.comp Sum.inl_injective)
    simp only [Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_5_spec, zero_add]
    set QR₁ := Id.run (algorithm_5_2_3 pure nb A₁) with hQR₁
    obtain ⟨h1m, h1o, h1u⟩ := ih _ hn1 A₁ hA₁i
    rw [← hQR₁] at h1m h1o h1u
    set Q₁ := QR₁.1 with hQ₁
    set R₁₁ := QR₁.2 with hR₁₁
    rw [conjTranspose_eq_transpose_of_trivial] at h1o
    set R₁₂ := Q₁ᵀ * A₂ with hR₁₂
    set A₂' := A₂ + -Q₁ * R₁₂ with hA₂'
    have hR₁₁u : IsUnit R₁₁.det :=
      (isUnit_iff_isUnit_det _).1 (isUnit_of_isThinQR ⟨h1m, by
        rw [conjTranspose_eq_transpose_of_trivial]; exact h1o, h1u⟩ hA₁i)
    have hQ₁A : Q₁ = A₁ * R₁₁⁻¹ := by
      rw [← h1m, mul_nonsing_inv_cancel_right _ _ hR₁₁u]
    -- `Q₁ᵀ A₂' = 0`
    have hQA₂' : Q₁ᵀ * A₂' = 0 := by
      rw [hA₂', Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, h1o,
        Matrix.one_mul, hR₁₂, add_neg_cancel]
    -- `A₂'` has full column rank
    have hA₂'i : LinearIndependent ℝ A₂'ᵀ := by
      refine linearIndependent_transpose_of_mulVec fun c hc => ?_
      set d := R₁₁⁻¹ *ᵥ (R₁₂ *ᵥ c) with hd
      have h2 : A₂ *ᵥ c = A₁ *ᵥ d := by
        have := hc
        rw [hA₂', add_mulVec, Matrix.neg_mul, neg_mulVec, add_neg_eq_zero] at this
        rw [this, hd, mulVec_mulVec, ← hQ₁A, mulVec_mulVec]
      have hx := mulVec_blockSplit A (-d) c
      rw [← hA₁, ← hA₂, mulVec_neg, h2, neg_add_cancel] at hx
      have hx0 := eq_zero_of_mulVec_eq_zero_of_linearIndependent hA hx
      funext j
      have := congrFun hx0 (e (Sum.inr j))
      simpa [he] using this
    set QR₂ := Id.run (algorithm_5_2_3 pure nb A₂') with hQR₂
    obtain ⟨h2m, h2o, h2u⟩ := ih _ hn2 A₂' hA₂'i
    rw [← hQR₂] at h2m h2o h2u
    set Q₂ := QR₂.1 with hQ₂
    set R₂₂ := QR₂.2 with hR₂₂
    rw [conjTranspose_eq_transpose_of_trivial] at h2o
    have hR₂₂u : IsUnit R₂₂.det :=
      (isUnit_iff_isUnit_det _).1 (isUnit_of_isThinQR ⟨h2m, by
        rw [conjTranspose_eq_transpose_of_trivial]; exact h2o, h2u⟩ hA₂'i)
    have hQ₁Q₂ : Q₁ᵀ * Q₂ = 0 := by
      have : Q₂ = A₂' * R₂₂⁻¹ := by rw [← h2m, mul_nonsing_inv_cancel_right _ _ hR₂₂u]
      rw [this, ← Matrix.mul_assoc, hQA₂', Matrix.zero_mul]
    have hQ₂Q₁ : Q₂ᵀ * Q₁ = 0 := by
      rw [← transpose_transpose (Q₂ᵀ * Q₁), transpose_mul, transpose_transpose, hQ₁Q₂,
        transpose_zero]
    refine ⟨?_, ?_, ?_⟩
    · rw [← submatrix_mul _ _ _ _ _ e.symm.bijective, fromCols_mul_fromBlocks, h1m, h2m,
        Matrix.mul_zero, add_zero, hA₂', Matrix.neg_mul,
        show Q₁ * R₁₂ + (A₂ + -(Q₁ * R₁₂)) = A₂ by abel]
      ext i j
      obtain ⟨b, rfl⟩ := e.surjective j
      rcases b with b | b <;> simp [hA₁, hA₂]
    · rw [conjTranspose_eq_transpose_of_trivial, transpose_submatrix, transpose_fromCols,
        ← submatrix_mul _ _ _ _ _ Function.bijective_id, fromRows_mul_fromCols, h1o, h2o,
        hQ₁Q₂, hQ₂Q₁, fromBlocks_one, submatrix_one_equiv]
    · intro i j hij
      obtain ⟨a, rfl⟩ := e.surjective i
      obtain ⟨b, rfl⟩ := e.surjective j
      replace hij : ((e b : Fin n) : ℕ) < e a := hij
      rw [he] at hij
      simp only [submatrix_apply, Equiv.symm_apply_apply]
      rcases a with a | a <;> rcases b with b | b
      · rw [blockSplit_inl_val, blockSplit_inl_val] at hij
        exact h1u (Fin.lt_def.2 hij)
      · rw [blockSplit_inl_val, blockSplit_inr_val] at hij
        omega
      · rfl
      · rw [blockSplit_inr_val, blockSplit_inr_val] at hij
        exact h2u (show b < a from Fin.lt_def.2 (by omega))

/-- **Algorithm 5.2.3 is correct**: for `A` of full column rank, the exact run of the recursive
block QR returns a thin QR factorization `A = Q₁R₁` (`Q₁` with orthonormal columns, `R₁` upper
triangular), for every block size `n_b`. Strong induction on `n` with the block identities
`Q₁R₁₁ = A₁`, `R₁₂ = Q₁ᵀA₂`, `Q₂R₂₂ = A₂ - Q₁R₁₂` and `Q₁ᵀQ₂ = 0` (because
`Q₁ᵀ(A₂ - Q₁R₁₂) = 0` and `R₂₂` is nonsingular). -/
theorem algorithm_5_2_3_spec (nb : ℕ) {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : LinearIndependent ℝ Aᵀ) :
    IsThinQR A (Id.run (algorithm_5_2_3 pure nb A)).1 (Id.run (algorithm_5_2_3 pure nb A)).2 :=
  algorithm_5_2_3_spec_aux nb n A hA

end BlockQR


/-! ### §5.2.3 Block Householder QR -/

section BlockHouseholder

/-- The columns `q` with `j ≤ q < τ` (the panel columns from `j` on, 0-based). -/
def colsBetween (n j τ : ℕ) : List (Fin n) :=
  (List.finRange n).filter fun q => j ≤ (q : ℕ) ∧ (q : ℕ) < τ

/-- Membership in `colsBetween`. -/
@[simp]
theorem mem_colsBetween {j τ : ℕ} {q : Fin n} :
    q ∈ colsBetween n j τ ↔ j ≤ (q : ℕ) ∧ (q : ℕ) < τ := by
  simp [colsBetween]

/-- `colsBetween` has no duplicates. -/
theorem nodup_colsBetween (j τ : ℕ) : (colsBetween n j τ).Nodup :=
  (List.nodup_finRange n).filter _

/-- The panel `λ:τ` of Algorithm 5.2.2 as a loop list: the columns `λ, …, τ - 1` in order
(0-based). -/
def panelCols (n lam τ : ℕ) : List (Fin n) := ((List.finRange n).take τ).drop lam

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One step `j` of the panel factorization of Algorithm 5.2.2 (Algorithm 5.2.1's loop body on the
panel `λ:τ`): `[v, β] = house(A(j:m, j))`, `A(j:m, j:τ) = (I - β v vᵀ) A(j:m, j:τ)` in place on
the full array (convention 10), `A(j+1:m, j) = v(2:m-j+1)`, `β` recorded, and `(v, β)` appended
to the panel's reflector data. -/
noncomputable def blockPanelStep (τ : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × List ((Fin m → ℝ) × ℝ)) (j : Fin n) :
    M (Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × List ((Fin m → ℝ) × ℝ)) := do
  let vβ ← houseOn rnd (indexFrom m j) (fun i => st.1 i j)
  let A ← householderApplyLeft rnd vβ.1 vβ.2 (indexFrom m j) (colsBetween n j τ) st.1
  pure (A.updateCol j (fun i => if (j : ℕ) < i then vβ.1 i else A i j),
    Function.update st.2.1 j vβ.2, st.2.2 ++ [vβ])

/-- The block update `A(:, cols) = (I - W Yᵀ)ᵀ A(:, cols) = A(:, cols) - Y (Wᵀ A(:, cols))`, in
place, column by column: `t = Wᵀ a` (Algorithm 1.1.1 per entry), then
`a(i) ← fl(a(i) - Y(i, :) t)` (the inner product accumulated as in Algorithm 1.1.1). -/
noncomputable def wyApplyLeft {r : ℕ} (W Y : Matrix (Fin m) (Fin r) ℝ) (cols : List (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) : M (Matrix (Fin m) (Fin n) ℝ) :=
  cols.foldlM (fun (A : Matrix (Fin m) (Fin n) ℝ) q => do
    let t ← (List.finRange r).foldlM (fun (t : Fin r → ℝ) k => do
      let d ← dotAccum rnd (List.finRange m) (fun i => W i k) (fun i => A i q) 0
      pure (Function.update t k d)) 0
    let c ← (List.finRange m).foldlM (fun (c : Fin m → ℝ) i => do
      let yt ← dotAccum rnd (List.finRange r) (Y i) t 0
      let d ← rnd (c i - yt)
      pure (Function.update c i d)) (fun i => A i q)
    pure (A.updateCol q c)) A

/-- The block update of the accumulated orthogonal factor, `Q = Q (I - W Yᵀ) = Q - (Q W) Yᵀ`, in
place, row by row over `rows`: `s = Q(i, :) W` (Algorithm 1.1.1 per entry), then
`Q(i, p) ← fl(Q(i, p) - Y(p, :) s)`. -/
noncomputable def wyApplyRight {r : ℕ} (W Y : Matrix (Fin m) (Fin r) ℝ) (rows : List (Fin m))
    (Q : Matrix (Fin m) (Fin m) ℝ) : M (Matrix (Fin m) (Fin m) ℝ) :=
  rows.foldlM (fun (Q : Matrix (Fin m) (Fin m) ℝ) i => do
    let s ← (List.finRange r).foldlM (fun (s : Fin r → ℝ) k => do
      let d ← dotAccum rnd (List.finRange m) (Q i) (fun p => W p k) 0
      pure (Function.update s k d)) 0
    let c ← (List.finRange m).foldlM (fun (c : Fin m → ℝ) p => do
      let ys ← dotAccum rnd (List.finRange r) (Y p) s 0
      let d ← rnd (c p - ys)
      pure (Function.update c p d)) (Q i)
    pure (Q.updateRow i c)) Q

/-- One pass of the `while` loop of Algorithm 5.2.2, at panel start `λ` with block size `r`:
`τ = min(λ + r - 1, n)` (0-based: the panel is `λ, …, τ - 1` with `τ = min(λ + r, n)`); the panel
factorization (`blockPanelStep`), collecting the reflector data; Algorithm 5.1.2 for
`I - W Yᵀ = H_λ ⋯ H_τ`; the trailing update `A(λ:m, τ+1:n) = (I - W Yᵀ)ᵀ A(λ:m, τ+1:n)`
(`wyApplyLeft` on the columns from `τ` on); and `Q = Q (I - W Yᵀ)` (`wyApplyRight`). -/
noncomputable def blockQRPanel (r : ℕ)
    (st : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) (lam : ℕ) :
    M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ)) := do
  let P ← (panelCols n lam (min (lam + r) n)).foldlM (blockPanelStep rnd (min (lam + r) n))
    (st.2.1, st.2.2, [])
  let WY ← algorithm_5_1_2 rnd P.2.2
  let A ← wyApplyLeft rnd WY.1 WY.2 (indexFrom n (min (lam + r) n)) P.1
  let Q ← wyApplyRight rnd WY.1 WY.2 (List.finRange m) st.1
  pure (Q, A, P.2.1)

/-- **Algorithm 5.2.2 (Block Householder QR)**: "If `A ∈ ℝ^{m×n}` and `r` is a positive integer,
then the following algorithm computes an orthogonal `Q ∈ ℝ^{m×m}` and an upper triangular
`R ∈ ℝ^{m×n}` so that `A = QR`":
```
Q = I_m;  λ = 1;  k = 0
while λ ≤ n
    τ = min(λ + r - 1, n);  k = k + 1
    Use Algorithm 5.2.1 to upper triangularize A(λ:m, λ:τ), generating Householder
        matrices H_λ, …, H_τ.
    Use Algorithm 5.1.2 to get the block representation I - W_k Y_kᵀ = H_λ ⋯ H_τ.
    A(λ:m, τ+1:n) = (I - W_k Y_kᵀ)ᵀ A(λ:m, τ+1:n)
    Q(:, λ:m) = Q(:, λ:m)(I - W_k Y_kᵀ)
    λ = τ + 1
end
```
The `while` loop is a fold over the `⌈n/r⌉` panel starts `0, r, 2r, …` (`blockQRPanel`). The
array keeps the Householder vectors below the diagonal as in Algorithm 5.2.1; `R` is its upper
triangular part. `W`, `Y` are full-length (`m × r`, zero above row `λ` in exact arithmetic), so
the two block updates run over all rows. Returns `(Q, A)`. -/
noncomputable def algorithm_5_2_2 (r : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    M (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ) := do
  let st ← ((List.range ((n + r - 1) / r)).map (· * r)).foldlM (blockQRPanel rnd r) (1, A, 0)
  pure (st.1, st.2.1)

end Programs

/-! #### Exact semantics of the block updates -/

/-- A loop subtracting `h k` from each listed entry of a vector, once each. -/
theorem foldl_update_sub_eq {ι : Type*} [DecidableEq ι] (h : ι → ℝ) {l : List ι}
    (hl : l.Nodup) (y₀ : ι → ℝ) :
    l.foldl (fun (y : ι → ℝ) k => Function.update y k (y k - h k)) y₀ =
      fun k => if k ∈ l then y₀ k - h k else y₀ k := by
  induction l generalizing y₀ with
  | nil => funext k; simp
  | cons a l ih =>
    rcases List.nodup_cons.1 hl with ⟨ha, hl'⟩
    rw [List.foldl_cons, ih hl']
    funext k
    by_cases hk : k ∈ l
    · have hka : k ≠ a := fun e => ha (e ▸ hk)
      simp [hk, hka]
    · by_cases hka : k = a
      · subst hka; simp [hk]
      · simp [hk, hka]

/-- The exact block update of one column. -/
theorem wyApplyLeft_single {r : ℕ} (W Y : Matrix (Fin m) (Fin r) ℝ) (q : Fin n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (wyApplyLeft pure W Y [q] A) =
      A.updateCol q (fun i => ((1 - Y * Wᵀ : Matrix (Fin m) (Fin m) ℝ) * A) i q) := by
  simp only [wyApplyLeft, List.foldlM_cons, List.foldlM_nil, Id.run_bind, Id.run_pure,
    bind_pure, List.idRun_foldlM, dotAccum_id_finRange, zero_add]
  rw [List.foldl_update_eq_ite, foldl_update_sub_eq _ (List.nodup_finRange m)]
  congr 1
  funext i
  simp only [List.mem_finRange, ↓reduceIte]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_assoc]
  rfl

/-- **Exact semantics of the block update** `A(:, cols) = (I - Y Wᵀ) A(:, cols)`. -/
theorem wyApplyLeft_pure {r : ℕ} (W Y : Matrix (Fin m) (Fin r) ℝ) {cols : List (Fin n)}
    (hcols : cols.Nodup) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (wyApplyLeft pure W Y cols A) =
      of fun i q => if q ∈ cols then ((1 - Y * Wᵀ : Matrix (Fin m) (Fin m) ℝ) * A) i q
        else A i q := by
  induction cols generalizing A with
  | nil => ext i q; simp [wyApplyLeft]
  | cons a l ih =>
    rcases List.nodup_cons.1 hcols with ⟨ha, hl⟩
    rw [show Id.run (wyApplyLeft pure W Y (a :: l) A) =
      Id.run (wyApplyLeft pure W Y l (Id.run (wyApplyLeft pure W Y [a] A))) from rfl, ih hl,
      wyApplyLeft_single]
    ext i q
    by_cases hq : q ∈ l
    · have hqa : q ≠ a := fun e => ha (e ▸ hq)
      simp only [of_apply, hq, List.mem_cons, or_true, ↓reduceIte, Matrix.mul_apply,
        updateCol_apply, hqa]
    · by_cases hqa : q = a
      · subst hqa
        simp [hq]
      · simp [hq, hqa]

/-- The exact block update of one row of `Q`. -/
theorem wyApplyRight_single {r : ℕ} (W Y : Matrix (Fin m) (Fin r) ℝ) (i : Fin m)
    (Q : Matrix (Fin m) (Fin m) ℝ) :
    Id.run (wyApplyRight pure W Y [i] Q) =
      Q.updateRow i (fun p => (Q * (1 - W * Yᵀ : Matrix (Fin m) (Fin m) ℝ)) i p) := by
  simp only [wyApplyRight, List.foldlM_cons, List.foldlM_nil, Id.run_bind, Id.run_pure,
    bind_pure, List.idRun_foldlM, dotAccum_id_finRange, zero_add]
  rw [List.foldl_update_eq_ite, foldl_update_sub_eq _ (List.nodup_finRange m)]
  congr 1
  funext p
  simp only [List.mem_finRange, ↓reduceIte]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, ← Matrix.mul_assoc, dotProduct_comm]
  rfl

/-- **Exact semantics of the update of `Q`**: `Q (I - W Yᵀ)` on the listed rows. -/
theorem wyApplyRight_pure {r : ℕ} (W Y : Matrix (Fin m) (Fin r) ℝ) {rows : List (Fin m)}
    (hrows : rows.Nodup) (Q : Matrix (Fin m) (Fin m) ℝ) :
    Id.run (wyApplyRight pure W Y rows Q) =
      of fun i p => if i ∈ rows then (Q * (1 - W * Yᵀ : Matrix (Fin m) (Fin m) ℝ)) i p
        else Q i p := by
  induction rows generalizing Q with
  | nil => ext i p; simp [wyApplyRight]
  | cons a l ih =>
    rcases List.nodup_cons.1 hrows with ⟨ha, hl⟩
    rw [show Id.run (wyApplyRight pure W Y (a :: l) Q) =
      Id.run (wyApplyRight pure W Y l (Id.run (wyApplyRight pure W Y [a] Q))) from rfl, ih hl,
      wyApplyRight_single]
    ext i p
    by_cases hi : i ∈ l
    · have hia : i ≠ a := fun e => ha (e ▸ hi)
      simp only [of_apply, hi, List.mem_cons, or_true, ↓reduceIte, Matrix.mul_apply,
        updateRow_apply, hia]
    · by_cases hia : i = a
      · subst hia
        simp [hi]
      · simp [hi, hia]

/-! #### Exact steps of Householder QR on a column list -/

/-- The exact reflector data `(v, β)` of step `j` on the array `B`. -/
noncomputable def exactHouse (B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : (Fin m → ℝ) × ℝ :=
  Id.run (houseOn pure (indexFrom m j) (fun i => B i j))

/-- The reflector `I - β v vᵀ` of `p = (v, β)` applied to the listed columns of `B`. -/
noncomputable def reflectCols (p : (Fin m → ℝ) × ℝ) (cols : List (Fin n))
    (B : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun i q => if q ∈ cols then
    ((1 - p.2 • vecMulVec p.1 p.1 : Matrix (Fin m) (Fin m) ℝ) * B) i q else B i q

/-- Column `j` of `B` with its entries below the diagonal replaced by those of `v`. -/
def storeCol (j : Fin n) (v : Fin m → ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  B.updateCol j (fun i => if (j : ℕ) < i then v i else B i j)

/-- One exact step of Householder QR on the column list `cols j`, collecting the reflector data. -/
noncomputable def exactQRStep (cols : Fin n → List (Fin n))
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × List ((Fin m → ℝ) × ℝ)) (j : Fin n) :
    Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × List ((Fin m → ℝ) × ℝ) :=
  (storeCol j (exactHouse st.1 j).1 (reflectCols (exactHouse st.1 j) (cols j) st.1),
    Function.update st.2.1 j (exactHouse st.1 j).2, st.2.2 ++ [exactHouse st.1 j])

/-- The exact step of Algorithm 5.2.1. -/
theorem run_householderQRStep (hnm : n ≤ m) (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ))
    (D : List ((Fin m → ℝ) × ℝ)) (j : Fin n) :
    Id.run (householderQRStep pure st j) =
      ((exactQRStep (fun j => indexFrom n j) (st.1, st.2, D) j).1,
        (exactQRStep (fun j => indexFrom n j) (st.1, st.2, D) j).2.1) := by
  have hjm : (j : ℕ) < m := lt_of_lt_of_le j.isLt hnm
  obtain ⟨-, hvout, -⟩ :=
    houseOn_spec (nodup_indexFrom m j) (indexFrom_ne_nil hjm) (fun i => st.1 i j)
  simp only [householderQRStep, Id.run_bind, Id.run_pure]
  rw [householderApplyLeft_spec (nodup_indexFrom m j) (nodup_indexFrom n j) hvout]
  rfl

/-- The exact step of the panel factorization of Algorithm 5.2.2. -/
theorem run_blockPanelStep (hnm : n ≤ m) (τ : ℕ)
    (st : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) × List ((Fin m → ℝ) × ℝ)) (j : Fin n) :
    Id.run (blockPanelStep pure τ st j) = exactQRStep (fun j => colsBetween n j τ) st j := by
  have hjm : (j : ℕ) < m := lt_of_lt_of_le j.isLt hnm
  obtain ⟨-, hvout, -⟩ :=
    houseOn_spec (nodup_indexFrom m j) (indexFrom_ne_nil hjm) (fun i => st.1 i j)
  simp only [blockPanelStep, Id.run_bind, Id.run_pure]
  rw [householderApplyLeft_spec (nodup_indexFrom m j) (nodup_colsBetween j τ) hvout]
  rfl

/-- The array whose columns `< τ` are those of `X` and the others those of `Y`. -/
def colMix (τ : ℕ) (X Y : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun i q => if (q : ℕ) < τ then X i q else Y i q

/-- Products agree in a column where the right factors agree. -/
theorem mul_apply_eq_of_col_eq {p : ℕ} (N : Matrix (Fin m) (Fin m) ℝ)
    {X Y : Matrix (Fin m) (Fin p) ℝ} {q : Fin p} (h : ∀ r, X r q = Y r q) (i : Fin m) :
    (N * X) i q = (N * Y) i q := by
  simp only [mul_apply, h]

/-- **One full step against one panel step**: on an array whose columns `< τ` are `B_p` and the
others `Pᵀ C`, a step `j < τ` of Algorithm 5.2.1 (on all columns from `j`) equals the panel step
(on the columns `j:τ`) with the trailing columns now `(P H_j)ᵀ C`. -/
theorem exactQRStep_panel (τ : ℕ) (Bp C : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ) (β : Fin n → ℝ) (D₀ E₀ : List ((Fin m → ℝ) × ℝ)) (j : Fin n)
    (hj : (j : ℕ) < τ) :
    exactQRStep (fun j => indexFrom n j) (colMix τ Bp (Pᵀ * C), β, D₀) j =
      (colMix τ (exactQRStep (fun j => colsBetween n j τ) (Bp, β, E₀) j).1
          ((P * (1 - (exactHouse Bp j).2 •
            vecMulVec (exactHouse Bp j).1 (exactHouse Bp j).1))ᵀ * C),
        (exactQRStep (fun j => colsBetween n j τ) (Bp, β, E₀) j).2.1,
        D₀ ++ [exactHouse Bp j]) := by
  have hx : (fun i => colMix τ Bp (Pᵀ * C) i j) = fun i => Bp i j := by
    funext i
    simp [colMix, hj]
  have hH : exactHouse (colMix τ Bp (Pᵀ * C)) j = exactHouse Bp j := by
    unfold exactHouse
    rw [hx]
  simp only [exactQRStep, hH]
  set p := exactHouse Bp j with hp
  set H : Matrix (Fin m) (Fin m) ℝ := 1 - p.2 • vecMulVec p.1 p.1 with hHdef
  refine Prod.ext ?_ rfl
  ext i q
  simp only [storeCol, reflectCols, colMix, of_apply, updateCol_apply, mem_indexFrom,
    mem_colsBetween]
  by_cases hqj : q = j
  · subst hqj
    simp only [↓reduceIte, hj, le_refl, true_and]
    split_ifs
    · rfl
    · exact mul_apply_eq_of_col_eq _ (fun r => by simp [hj]) i
  · simp only [hqj, ↓reduceIte]
    by_cases hqτ : (q : ℕ) < τ
    · simp only [hqτ, and_true, ↓reduceIte]
      split_ifs
      · exact mul_apply_eq_of_col_eq _ (fun r => by simp [hqτ]) i
      · rfl
    · have hjq : (j : ℕ) ≤ q := by omega
      simp only [hqτ, ↓reduceIte, hjq]
      rw [← hHdef, transpose_mul, hHdef, transpose_one_sub_smul_vecMulVec, ← hHdef,
        Matrix.mul_assoc]
      exact mul_apply_eq_of_col_eq _ (fun r => by simp [hqτ]) i

/-- **A panel against the unblocked steps**: over a list of steps `j < τ`, Algorithm 5.2.1's steps
on `[B_p | Pᵀ C]` (columns `< τ` from `B_p`) equal the panel steps on `B_p` followed by the
product of the panel's reflectors on the trailing columns; the panel steps leave the columns
`≥ τ` untouched and collect the same reflector data. -/
theorem foldl_exactQRStep_panel (τ : ℕ) :
    ∀ (l : List (Fin n)), (∀ j ∈ l, (j : ℕ) < τ) →
      ∀ (Bp C : Matrix (Fin m) (Fin n) ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (β : Fin n → ℝ)
        (D₀ E₀ : List ((Fin m → ℝ) × ℝ)),
      ∃ D, (l.foldl (exactQRStep (fun j => colsBetween n j τ)) (Bp, β, E₀)).2.2 = E₀ ++ D ∧
        l.foldl (exactQRStep (fun j => indexFrom n j)) (colMix τ Bp (Pᵀ * C), β, D₀) =
          (colMix τ (l.foldl (exactQRStep (fun j => colsBetween n j τ)) (Bp, β, E₀)).1
              ((P * householderProduct D)ᵀ * C),
            (l.foldl (exactQRStep (fun j => colsBetween n j τ)) (Bp, β, E₀)).2.1, D₀ ++ D) ∧
        ∀ i (q : Fin n), τ ≤ (q : ℕ) →
          (l.foldl (exactQRStep (fun j => colsBetween n j τ)) (Bp, β, E₀)).1 i q = Bp i q := by
  intro l
  induction l with
  | nil =>
    intro _ Bp C P β D₀ E₀
    refine ⟨[], by simp, ?_, fun _ _ _ => rfl⟩
    simp
  | cons j l ih =>
    intro hl Bp C P β D₀ E₀
    have hj : (j : ℕ) < τ := hl j List.mem_cons_self
    set p := exactHouse Bp j with hp
    set s := exactQRStep (fun j => colsBetween n j τ) (Bp, β, E₀) j with hs
    have hs' : s = (s.1, s.2.1, E₀ ++ [p]) := rfl
    obtain ⟨D', hD', hfull, htrail⟩ := ih (fun k hk => hl k (List.mem_cons_of_mem j hk)) s.1 C
      (P * (1 - p.2 • vecMulVec p.1 p.1)) s.2.1 (D₀ ++ [p]) (E₀ ++ [p])
    refine ⟨p :: D', ?_, ?_, fun i q hq => ?_⟩
    · rw [List.foldl_cons, ← hs, hs', hD']
      simp
    · rw [List.foldl_cons, List.foldl_cons, exactQRStep_panel τ Bp C P β D₀ E₀ j hj, ← hp, ← hs,
        hfull, hs', householderProduct_cons, Matrix.mul_assoc]
      simp
    · rw [List.foldl_cons, ← hs, hs', htrail i q hq, hs]
      have hqj : q ≠ j := fun e => by rw [e] at hq; omega
      simp only [exactQRStep, storeCol, reflectCols, updateCol_apply, hqj, ↓reduceIte, of_apply,
        mem_colsBetween]
      rw [ite_eq_right_iff.2 fun h => absurd h.2 (by omega)]

/-- A column in the loop list `panelCols n λ τ` is below `τ`. -/
theorem val_lt_of_mem_panelCols {lam τ : ℕ} {j : Fin n} (h : j ∈ panelCols n lam τ) :
    (j : ℕ) < τ := by
  obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 (List.mem_of_mem_drop h)
  simp only [List.getElem_finRange, Fin.val_cast]
  omega

/-- The first `min(λ + r, n)` columns are the first `min(λ, n)` followed by the panel. -/
theorem take_eq_take_append_panelCols (lam r : ℕ) :
    (List.finRange n).take (min (lam + r) n) =
      (List.finRange n).take (min lam n) ++ panelCols n lam (min (lam + r) n) := by
  unfold panelCols
  by_cases h : lam ≤ n
  · rw [min_eq_left h]
    conv_lhs => rw [← List.take_append_drop lam ((List.finRange n).take (min (lam + r) n))]
    rw [List.take_take, min_eq_left (by omega : lam ≤ min (lam + r) n)]
  · have h1 : min lam n = n := by omega
    have h2 : min (lam + r) n = n := by omega
    rw [h1, h2, List.take_of_length_le (by simp only [List.length_finRange, le_refl]),
      List.drop_eq_nil_of_le (by simp only [List.length_finRange]; omega), List.append_nil]

/-- **The exact reflector data of Algorithm 5.2.1 is its factored form**: after `t` exact steps
(collecting the data), the collected `(v⁽ᵏ⁾, β_k)` are the stored vectors of the current array
with the recorded `β_k`. -/
theorem exactQR_data (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) : ∀ t ≤ n,
    (((List.finRange n).take t).foldl (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).2.2 =
      ((List.finRange n).take t).map fun k =>
        (storedHouseholderVec (((List.finRange n).take t).foldl
            (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).1 k,
          (((List.finRange n).take t).foldl
            (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).2.1 k) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    have hlt : t < (List.finRange n).length := by simp only [List.length_finRange]; omega
    rw [List.take_succ_eq_append_getElem hlt, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.map_append]
    set S := ((List.finRange n).take t).foldl (exactQRStep (fun j => indexFrom n j)) (A, 0, [])
      with hS
    set jj := (List.finRange n)[t] with hjj
    have hjjv : (jj : ℕ) = t := by simp [hjj]
    have hjm : (jj : ℕ) < m := by omega
    obtain ⟨hv1, hvout, -⟩ :=
      houseOn_spec (nodup_indexFrom m jj) (indexFrom_ne_nil hjm) (fun i => S.1 i jj)
    rw [head_indexFrom hjm (indexFrom_ne_nil hjm)] at hv1
    have hcol : ∀ k : Fin n, (k : ℕ) < t → ∀ i,
        (exactQRStep (fun j => indexFrom n j) S jj).1 i k = S.1 i k := by
      intro k hk i
      have hkj : k ≠ jj := fun e => by rw [e] at hk; omega
      simp only [exactQRStep, storeCol, reflectCols, updateCol_apply, hkj, ↓reduceIte, of_apply,
        mem_indexFrom]
      rw [ite_eq_right (by omega)]
    have hsv : storedHouseholderVec (exactQRStep (fun j => indexFrom n j) S jj).1 jj =
        (exactHouse S.1 jj).1 := by
      funext i
      simp only [storedHouseholderVec]
      by_cases hij : (i : ℕ) < jj
      · rw [ite_eq_left hij]
        exact (hvout i (by rw [mem_indexFrom]; omega)).symm
      · rw [ite_eq_right hij]
        by_cases hij' : (i : ℕ) = jj
        · rw [ite_eq_left hij']
          have : i = ⟨jj, hjm⟩ := Fin.ext hij'
          rw [this]
          exact hv1.symm
        · rw [ite_eq_right hij']
          simp only [exactQRStep, storeCol, updateCol_self]
          rw [ite_eq_left (by omega)]
    change S.2.2 ++ [exactHouse S.1 jj] = _
    rw [ih']
    congr 1
    · refine List.map_congr_left fun k hk => ?_
      have hk' : (k : ℕ) < t := by
        obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 hk
        simp only [List.getElem_finRange, Fin.val_cast]
        omega
      have hkj : k ≠ jj := fun e => by rw [e] at hk'; omega
      refine Prod.ext ?_ ?_
      · funext i
        simp only [storedHouseholderVec, hcol k hk']
      · exact (Function.update_of_ne hkj _ _).symm
    · simp only [List.map_cons, List.map_nil, hsv]
      congr 1
      exact Prod.ext rfl (Function.update_self jj (exactHouse S.1 jj).2 S.2.1).symm

/-- **The exact block pass**: one pass of Algorithm 5.2.2 at `λ` runs the panel steps, multiplies
`Q` by the product of the panel's reflectors and applies its transpose to the columns from `τ`
on. -/
theorem run_blockQRPanel (hnm : n ≤ m) (r : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ) (lam : ℕ) :
    Id.run (blockQRPanel pure r (Q, B, β) lam) =
      (Q * householderProduct ((panelCols n lam (min (lam + r) n)).foldl
          (exactQRStep (fun j => colsBetween n j (min (lam + r) n))) (B, β, [])).2.2,
        of fun i q => if q ∈ indexFrom n (min (lam + r) n) then
          ((householderProduct ((panelCols n lam (min (lam + r) n)).foldl
            (exactQRStep (fun j => colsBetween n j (min (lam + r) n))) (B, β, [])).2.2)ᵀ *
            ((panelCols n lam (min (lam + r) n)).foldl
              (exactQRStep (fun j => colsBetween n j (min (lam + r) n))) (B, β, [])).1) i q
          else ((panelCols n lam (min (lam + r) n)).foldl
              (exactQRStep (fun j => colsBetween n j (min (lam + r) n))) (B, β, [])).1 i q,
        ((panelCols n lam (min (lam + r) n)).foldl
          (exactQRStep (fun j => colsBetween n j (min (lam + r) n))) (B, β, [])).2.1) := by
  set P := (panelCols n lam (min (lam + r) n)).foldl
    (exactQRStep (fun j => colsBetween n j (min (lam + r) n))) (B, β, []) with hP
  have hPeq : Id.run ((panelCols n lam (min (lam + r) n)).foldlM
      (blockPanelStep pure (min (lam + r) n)) (B, β, [])) = P := by
    rw [List.idRun_foldlM]
    congr 1
    funext st j
    exact run_blockPanelStep hnm _ st j
  simp only [blockQRPanel, Id.run_bind, Id.run_pure]
  rw [hPeq]
  obtain ⟨hWY, -⟩ := algorithm_5_1_2_spec P.2.2
  rw [wyApplyLeft_pure _ _ (nodup_indexFrom n _), wyApplyRight_pure _ _ (List.nodup_finRange m)]
  have hT : (1 - (Id.run (algorithm_5_1_2 pure P.2.2)).2 *
      (Id.run (algorithm_5_1_2 pure P.2.2)).1ᵀ : Matrix (Fin m) (Fin m) ℝ) =
      (householderProduct P.2.2)ᵀ := by
    rw [hWY, transpose_sub, transpose_one, transpose_mul, transpose_transpose]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · ext i p
    simp only [of_apply, List.mem_finRange, ↓reduceIte, hWY]
  · ext i q
    simp only [of_apply, hT]

/-- The exact run of Algorithm 5.2.1 with the reflector data collected. -/
theorem foldl_householderQRStep_eq (hnm : n ≤ m) : ∀ (l : List (Fin n))
    (B : Matrix (Fin m) (Fin n) ℝ) (β : Fin n → ℝ) (D : List ((Fin m → ℝ) × ℝ)),
    l.foldl (fun st j => Id.run (householderQRStep pure st j)) (B, β) =
      ((l.foldl (exactQRStep (fun j => indexFrom n j)) (B, β, D)).1,
        (l.foldl (exactQRStep (fun j => indexFrom n j)) (B, β, D)).2.1) := by
  intro l
  induction l with
  | nil => intro B β D; rfl
  | cons j l ih =>
    intro B β D
    rw [List.foldl_cons, List.foldl_cons, run_householderQRStep hnm (B, β) D j]
    exact ih _ _ _

/-- The invariant of Algorithm 5.2.2: after the first `K` passes, the state is that of
Algorithm 5.2.1 after `min(K r, n)` steps, with `Q` the product of the reflectors so far. -/
theorem algorithm_5_2_2_inv (hnm : n ≤ m) (r : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (K : ℕ) :
    ((List.range K).map (· * r)).foldl (fun st lam => Id.run (blockQRPanel pure r st lam))
        (1, A, 0) =
      (householderProduct (((List.finRange n).take (min (K * r) n)).foldl
          (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).2.2,
        (((List.finRange n).take (min (K * r) n)).foldl
          (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).1,
        (((List.finRange n).take (min (K * r) n)).foldl
          (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).2.1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih, run_blockQRPanel hnm]
    have hK : (K + 1) * r = K * r + r := by ring
    rw [hK, take_eq_take_append_panelCols (K * r) r, List.foldl_append]
    set U := ((List.finRange n).take (min (K * r) n)).foldl
      (exactQRStep (fun j => indexFrom n j)) (A, 0, []) with hU
    set τ := min (K * r + r) n with hτ
    obtain ⟨D, hD, hfull, htrail⟩ := foldl_exactQRStep_panel τ (panelCols n (K * r) τ)
      (fun j hj => val_lt_of_mem_panelCols hj) U.1 U.1 1 U.2.1 U.2.2 []
    have hmix : colMix τ U.1 ((1 : Matrix (Fin m) (Fin m) ℝ)ᵀ * U.1) = U.1 := by
      ext i q
      simp [colMix]
    rw [hmix] at hfull
    have hfull' : (panelCols n (K * r) τ).foldl (exactQRStep (fun j => indexFrom n j)) U =
        _ := hfull
    rw [hfull']
    rw [List.nil_append] at hD
    rw [hD]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · exact (householderProduct_append _ _).symm
    · ext i q
      simp only [of_apply, colMix, mem_indexFrom, Matrix.one_mul]
      by_cases hq : τ ≤ (q : ℕ)
      · rw [ite_eq_left hq, ite_eq_right (by omega)]
        exact mul_apply_eq_of_col_eq _ (fun r => htrail r q hq) i
      · rw [ite_eq_right hq, ite_eq_left (by omega)]

/-- **Algorithm 5.2.2 computes what Algorithm 5.2.1 computes** (exact arithmetic, `m ≥ n`,
`r ≥ 1`): the array is Algorithm 5.2.1's output `A'` and `Q` is its factored form
`H₁ ⋯ H_n` with the stored vectors and the returned `β` — the blocked update of `A(λ:m, τ+1:n)`
by `(I - W Yᵀ)ᵀ` is the sequence of the panel's reflector applications, and the accumulation of
`Q` by `I - W_k Y_kᵀ` is the product of the panels' reflectors (Algorithm 5.1.2). -/
theorem algorithm_5_2_2_eq (hnm : n ≤ m) {r : ℕ} (hr : 0 < r) (A : Matrix (Fin m) (Fin n) ℝ) :
    Id.run (algorithm_5_2_2 pure r A) =
      (factoredQ (Id.run (algorithm_5_2_1 pure A)).2 (Id.run (algorithm_5_2_1 pure A)).1,
        (Id.run (algorithm_5_2_1 pure A)).1) := by
  have hN : min ((n + r - 1) / r * r) n = n := by
    have := Nat.lt_div_mul_add (a := n + r - 1) hr
    generalize (n + r - 1) / r * r = N at this ⊢
    omega
  have hrun : Id.run (algorithm_5_2_2 pure r A) =
      ((((List.range ((n + r - 1) / r)).map (· * r)).foldl
          (fun st lam => Id.run (blockQRPanel pure r st lam)) (1, A, 0)).1,
        (((List.range ((n + r - 1) / r)).map (· * r)).foldl
          (fun st lam => Id.run (blockQRPanel pure r st lam)) (1, A, 0)).2.1) := by
    simp only [algorithm_5_2_2, Id.run_bind, Id.run_pure, List.idRun_foldlM]
  have htake : (List.finRange n).take n = List.finRange n :=
    List.take_of_length_le (by simp only [List.length_finRange, le_refl])
  have h521 : Id.run (algorithm_5_2_1 pure A) =
      (((List.finRange n).foldl (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).1,
        ((List.finRange n).foldl (exactQRStep (fun j => indexFrom n j)) (A, 0, [])).2.1) := by
    rw [algorithm_5_2_1, List.idRun_foldlM]
    exact foldl_householderQRStep_eq hnm _ A 0 []
  have hdata := exactQR_data hnm A n le_rfl
  rw [htake] at hdata
  rw [hrun, algorithm_5_2_2_inv hnm r A, hN, htake, h521, hdata]
  simp only [factoredQ, storedReflectors, List.ofFn_eq_map]

/-- **Algorithm 5.2.2 computes a QR factorization** (exact arithmetic, `m ≥ n`, block size
`r ≥ 1`): with `(Q, A') = Id.run (algorithm_5_2_2 pure r A)`, `Q` is orthogonal and
`A = Q R` for `R` the upper triangular part of `A'` — the same specification as
Algorithm 5.2.1 (`algorithm_5_2_2_eq`: the blocked algorithm computes the same `Q` and `R`). -/
theorem algorithm_5_2_2_spec (hnm : n ≤ m) {r : ℕ} (hr : 0 < r) (A : Matrix (Fin m) (Fin n) ℝ) :
    IsQR A (Id.run (algorithm_5_2_2 pure r A)).1 (upperPart (Id.run (algorithm_5_2_2 pure r A)).2)
    := by
  rw [algorithm_5_2_2_eq hnm hr A]
  exact (algorithm_5_2_1_spec hnm A).1

end BlockHouseholder

/-! ### §5.2.10 A note on complex Householder QR -/

/-- **§5.2.10**: every `A ∈ ℂ^{m×n}` has a factorization `A = QR` with `Q` unitary (a product of
complex Householder matrices) and `R` upper triangular. -/
theorem complexHouseholderQR (A : Matrix (Fin m) (Fin n) ℂ) : ∃ Q R, IsQR A Q R :=
  exists_isQR A

end GolubVanLoan.Chapter05
