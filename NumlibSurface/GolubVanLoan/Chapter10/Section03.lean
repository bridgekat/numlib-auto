import NumlibSurface.GolubVanLoan.Chapter10.Section05

/-!
# Golub–Van Loan §10.3: practical Lanczos procedures

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §10.3:
the two-vector implementation (10.3.1) of the Lanczos process, the "good Ritz pair" of selective
reorthogonalization (§10.3.4) and the Kahan–Parlett Lemma 10.3.1.

## Conventions

The chapter's (`GolubVanLoan.Chapter10.Section01`). The two-vector program keeps the book's two
`n`-vectors `w`, `v` and swaps them in place, one entry at a time.

## Not formalized

The floating-point analysis of §10.3.2 and §10.3.4 — (10.3.2)–(10.3.3), (10.3.5)–(10.3.6) and the
`≈` estimates between them — is quoted from Paige without derivation. The application of
Theorem 8.1.16 at the end of §10.3.2 is invalid as printed (`T̂_k` is not `Q̂_kᵀ A Q̂_k`). The
ghost-eigenvalue discussion (§10.3.5) and the restarted block Lanczos of §10.3.7 are prose.
Complete reorthogonalization with Householder matrices (10.3.4) and block Lanczos (10.3.8)–(10.3.9)
with Underwood's Theorem 10.3.2 wait for chapter 5's Householder programs (`houseOn`,
`householderApplyLeft`, Algorithm 5.2.1, `backwardAccumulation`).
-/

open scoped Matrix
open Krylov FloatingPoint
open GolubVanLoan.Chapter01

namespace GolubVanLoan.Chapter10

variable {n : ℕ}

/-! ### The two-vector implementation (10.3.1) -/

/-- The state of the two-vector Lanczos program (10.3.1): the step counter `k` (the number of
Lanczos vectors computed), the two vectors `w` and `v`, the coefficients (`alpha j`, `beta j` are
the book's `α_{j+1}`, `β_{j+1}`) and the `done` flag of the `while β_k ≠ 0` loop. -/
structure TwoVectorState (n : ℕ) where
  /-- The book's step counter `k`. -/
  k : ℕ
  /-- The vector `w` (the current Lanczos vector `q_k`). -/
  w : Fin n → ℝ
  /-- The vector `v` (the current residual `r_k`). -/
  v : Fin n → ℝ
  /-- The diagonal coefficients `α`, `0`-based. -/
  alpha : ℕ → ℝ
  /-- The off-diagonal coefficients `β`, `0`-based. -/
  beta : ℕ → ℝ
  /-- Whether the loop has stopped (`β_k = 0`). -/
  done : Bool

section Program

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The in-place swap `t = w_i, w_i = v_i/β, v_i = −β t` for `i = 1 : n` of (10.3.1), one rounded
quotient and one rounded product per entry (the negation is exact). The two vectors are carried as
one vector of pairs. -/
noncomputable def lanczosSwap (w v : Fin n → ℝ) (β : ℝ) : M ((Fin n → ℝ) × (Fin n → ℝ)) := do
  let p ← (List.finRange n).foldlM (fun (p : Fin n → ℝ × ℝ) i => do
      let t := (p i).1
      let a ← rnd ((p i).2 / β)
      let b ← rnd (β * t)
      pure (Function.update p i (a, -b))) (fun i => (w i, v i))
  pure (fun i => (p i).1, fun i => (p i).2)

/-- One pass of the `while` loop of (10.3.1) (a no-op once `done`):
```
for i = 1:n: t = w_i, w_i = v_i/β_k, v_i = −β_k t
v = v + A w,  k = k + 1,  α_k = wᵀv,  v = v − α_k w,  β_k = ‖v‖₂
```
-/
noncomputable def twoVectorLanczosStep (A : Matrix (Fin n) (Fin n) ℝ) (s : TwoVectorState n) :
    M (TwoVectorState n) :=
  if s.done then pure s else do
    let bk := s.beta (s.k - 1)
    let wv ← lanczosSwap rnd s.w s.v bk
    let v ← algorithm_1_1_3 rnd A wv.1 wv.2
    let a ← algorithm_1_1_1 rnd wv.1 v
    let v ← algorithm_1_1_2 rnd (-a) wv.1 v
    let b ← vecNorm rnd v
    pure
      { k := s.k + 1
        w := wv.1
        v := v
        alpha := Function.update s.alpha s.k a
        beta := Function.update s.beta s.k b
        done := decide (b = 0) }

/-- **(10.3.1), Lanczos with two `n`-vectors** ("the Lanczos iteration can be implemented with just
two `n`-vectors of storage"):
```
w = q₁, v = A w, α₁ = wᵀv, v = v − α₁ w, β₁ = ‖v‖₂, k = 1
while β_k ≠ 0
  for i = 1:n: t = w_i, w_i = v_i/β_k, v_i = −β_k t
  v = v + A w,  k = k + 1,  α_k = wᵀv,  v = v − α_k w,  β_k = ‖v‖₂
end
```
The `while` loop is at most `fuel` passes of `twoVectorLanczosStep` (convention 3). -/
noncomputable def twoVectorLanczos (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ) (fuel : ℕ) :
    M (TwoVectorState n) := do
  let v ← algorithm_1_1_3 rnd A q₁ 0
  let a ← algorithm_1_1_1 rnd q₁ v
  let v ← algorithm_1_1_2 rnd (-a) q₁ v
  let b ← vecNorm rnd v
  (List.range fuel).foldlM (fun s _ => twoVectorLanczosStep rnd A s)
    { k := 1, w := q₁, v := v, alpha := Function.update (fun _ => 0) 0 a,
      beta := Function.update (fun _ => 0) 0 b, done := decide (b = 0) }

end Program

/-- Exact semantics of the swap: `w ← v / β`, `v ← −β w`. -/
theorem lanczosSwap_spec (w v : Fin n → ℝ) (β : ℝ) :
    Id.run (lanczosSwap pure w v β) = (β⁻¹ • v, -(β • w)) := by
  have h := idRun_foldlM_update_apply (fun (_ : Fin n) (q : ℝ × ℝ) =>
    (pure (q.2 / β, -(β * q.1)) : Id (ℝ × ℝ))) (List.finRange n) (List.nodup_finRange n)
    (fun i => (w i, v i))
  simp only [lanczosSwap, Id.run_bind, Id.run_pure]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have := congrArg Prod.fst (h i)
    simp only [List.mem_finRange, ↓reduceIte, Id.run_pure] at this
    simpa [div_eq_inv_mul] using this
  · have := congrArg Prod.snd (h i)
    simp only [List.mem_finRange, ↓reduceIte, Id.run_pure] at this
    simpa using this

/-- The exact run after `t + 1` passes of the loop is one more pass. -/
private theorem twoVectorLanczos_succ (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ) (t : ℕ) :
    Id.run (twoVectorLanczos pure A q₁ (t + 1)) =
      Id.run (twoVectorLanczosStep pure A (Id.run (twoVectorLanczos pure A q₁ t))) := by
  simp only [twoVectorLanczos, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- **Exact semantics of (10.3.1)**: for a symmetric `A` and a unit `q₁`, the two-vector run
computes the same `α_j`, `β_j` as Algorithm 10.1.1 (the backbone's `Lanczos.alpha`, `Lanczos.beta`,
for `j < k`), it stops with `k = min (fuel + 1) m` (`m` the grade), and at the end of the loop body
`w = q_k` and `v = r_k = A q_k − α_k q_k − β_{k−1} q_{k−1}` (the book's claim after the display).
The identity `α_k = q_kᵀ(A q_k − β_{k−1} q_{k−1})` used by the program is `q_kᵀ q_{k−1} = 0`. -/
theorem equation_10_3_1 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {q₁ : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q₁ : EuclideanSpace ℝ (Fin n))‖ = 1) (fuel : ℕ) :
    let s := Id.run (twoVectorLanczos pure A q₁ fuel)
    let T := Matrix.toEuclideanLin A
    let q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 q₁
    s.k = min (fuel + 1) (grade T q) ∧
      (∀ j < s.k, s.alpha j = Lanczos.alpha T q j ∧ s.beta j = Lanczos.beta T q j) ∧
      s.w = (Arnoldi.vec T q (s.k - 1)).ofLp ∧ s.v = (Arnoldi.w T q (s.k - 1)).ofLp := by
  intro s T q
  have hT : T.IsSymmetric := hA.isSymmetric_toEuclideanLin
  have hTx : ∀ x, (T x).ofLp = A *ᵥ x.ofLp := fun x => rfl
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : ‖q‖ = 1 := hq
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hg : 0 < grade T q := by
    rw [Nat.pos_iff_ne_zero, Ne, grade_eq_zero_iff]
    push Not
    exact ⟨hq0, inferInstance⟩
  have hv0 : (Arnoldi.vec T q 0).ofLp = q₁ := by
    rw [Arnoldi.vec_zero T q hq0, show ‖q‖ = 1 from hq]
    simp [q]
  -- the invariant after `t` passes
  let P : ℕ → TwoVectorState n → Prop := fun t s =>
    1 ≤ s.k ∧ s.k = min (t + 1) (grade T q) ∧ s.done = decide (grade T q ≤ s.k) ∧
      (∀ j < s.k, s.alpha j = Lanczos.alpha T q j ∧ s.beta j = Lanczos.beta T q j) ∧
      s.w = (Arnoldi.vec T q (s.k - 1)).ofLp ∧ s.v = (Arnoldi.w T q (s.k - 1)).ofLp
  -- the diagonal coefficient and the residual of step `k`, from the backbone
  have hα : ∀ j, (Arnoldi.vec T q j).ofLp ⬝ᵥ (A *ᵥ (Arnoldi.vec T q j).ofLp) =
      Lanczos.alpha T q j := fun j => by
    rw [Lanczos.alpha, Arnoldi.coeff, RCLike.re_to_real,
      EuclideanSpace.inner_eq_star_dotProduct, hTx, star_trivial, dotProduct_comm]
  have hP : ∀ t, P t (Id.run (twoVectorLanczos pure A q₁ t)) := by
    intro t
    induction t with
    | zero =>
      simp only [P, twoVectorLanczos, Id.run_bind, algorithm_1_1_3_spec, algorithm_1_1_1_spec,
        algorithm_1_1_2_spec, vecNorm_spec, zero_add, List.range_zero, List.foldlM_nil,
        Id.run_pure]
      have hw0 : A *ᵥ q₁ + (-(q₁ ⬝ᵥ (A *ᵥ q₁))) • q₁ = (Arnoldi.w T q 0).ofLp := by
        rw [Arnoldi.w, Finset.sum_range_one, ← Lanczos.coe_alpha q hT 0, ← hα 0, hv0]
        simp [sub_eq_add_neg, hTx, hv0]
      have hα0 : q₁ ⬝ᵥ (A *ᵥ q₁) = Lanczos.alpha T q 0 := by rw [← hα 0, hv0]
      rw [hw0, WithLp.toLp_ofLp, ← Lanczos.beta]
      refine ⟨le_rfl, by omega, ?_, fun j hj => ?_, hv0.symm, rfl⟩
      · simp only [Lanczos.beta_eq_zero_iff q hT 0, zero_add]
      · obtain rfl : j = 0 := by omega
        simp [hα0]
    | succ t ih =>
      rw [twoVectorLanczos_succ]
      set s := Id.run (twoVectorLanczos pure A q₁ t)
      obtain ⟨hk1, hk, hdone, hvec, hw, hv⟩ := ih
      cases hsd : s.done with
      | true =>
        have hle : grade T q ≤ s.k := by simpa [hsd] using hdone.symm
        simp only [twoVectorLanczosStep, hsd, ↓reduceIte, Id.run_pure]
        refine ⟨hk1, ?_, hdone, hvec, hw, hv⟩
        rw [hk] at hle ⊢
        omega
      | false =>
        have hlt : s.k < grade T q := by
          have : ¬ grade T q ≤ s.k := by simpa [hsd] using hdone.symm
          omega
        obtain ⟨j, hj⟩ : ∃ j, s.k = j + 1 := ⟨s.k - 1, by omega⟩
        simp only [P, twoVectorLanczosStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
          Id.run_pure, lanczosSwap_spec, algorithm_1_1_3_spec, algorithm_1_1_1_spec,
          algorithm_1_1_2_spec, vecNorm_spec]
        rw [hj, Nat.add_sub_cancel] at hw hv ⊢
        rw [hw, hv, (hvec j (by omega)).2]
        -- the new Lanczos vector
        have hq' : (Lanczos.beta T q j)⁻¹ • (Arnoldi.w T q j).ofLp =
            (Arnoldi.vec T q (j + 1)).ofLp := by
          rw [Arnoldi.vec_succ_eq, Lanczos.beta]
          simp
        rw [hq']
        -- `A q_{k+1} − β_k q_k` and its inner product with `q_{k+1}`
        have horth : (Arnoldi.vec T q (j + 1)).ofLp ⬝ᵥ (Arnoldi.vec T q j).ofLp = 0 := by
          have := Arnoldi.inner_vec_eq_zero T q (i := j) (j := j + 1) (by omega)
          rwa [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at this
        have ha : (Arnoldi.vec T q (j + 1)).ofLp ⬝ᵥ
            (-(Lanczos.beta T q j • (Arnoldi.vec T q j).ofLp) +
              A *ᵥ (Arnoldi.vec T q (j + 1)).ofLp) = Lanczos.alpha T q (j + 1) := by
          rw [dotProduct_add, dotProduct_neg, dotProduct_smul, horth, smul_zero, neg_zero,
            zero_add, hα]
        rw [ha]
        have hr : -(Lanczos.beta T q j • (Arnoldi.vec T q j).ofLp) +
              A *ᵥ (Arnoldi.vec T q (j + 1)).ofLp +
              (-Lanczos.alpha T q (j + 1)) • (Arnoldi.vec T q (j + 1)).ofLp =
            (Arnoldi.w T q (j + 1)).ofLp := by
          rw [Lanczos.w_succ_eq q hT j]
          simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, hTx, RCLike.ofReal_real_eq_id, id]
          module
        rw [hr, WithLp.toLp_ofLp, ← Lanczos.beta]
        refine ⟨by omega, by omega, ?_, fun i hi => ?_, rfl, rfl⟩
        · simp only [Lanczos.beta_eq_zero_iff q hT (j + 1)]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · simp only [Function.update_of_ne (show i ≠ j + 1 by omega)]
            exact hvec i (by omega)
          · simp
  obtain ⟨-, hk, -, hvec, hw, hv⟩ := hP fuel
  exact ⟨hk, hvec, hw, hv⟩

/-! ### Selective orthogonalization (§10.3.4) -/

open scoped Matrix.Norms.L2Operator in
/-- **A good Ritz pair** (§10.3.4, Parlett and Scott): a computed Ritz pair `(θ̂, ŷ)` is *good* if
`‖A ŷ − θ̂ ŷ‖₂ ≤ √u ‖A‖₂`, `u` the unit roundoff of the floating-point model. -/
def IsGoodRitzPair (fp : RoundingModel ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖Matrix.toEuclideanLin A y - θ • y‖ ≤
    Real.sqrt fp.u * ‖A‖

/-! ### The Kahan–Parlett lemma (§10.3.4) -/

/-- The matrix `S₊ = [S | d]` of Lemma 10.3.1: `S` with the column `d` appended. -/
def appendCol {k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (d : Fin n → ℝ) :
    Matrix (Fin n) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j => Fin.lastCases (d i) (fun j' => S i j') j

/-- `I − S₊ᵀ S₊` in block form: `[I − SᵀS, −Sᵀd; −dᵀS, 1 − dᵀd]`. -/
private theorem one_sub_appendCol_submatrix {k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ)
    (d : Fin n → ℝ) :
    ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) - (appendCol S d)ᵀ * appendCol S d).submatrix
        finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (1 - Sᵀ * S) (Matrix.vecMulVec (-(Sᵀ *ᵥ d)) fun _ : Fin 1 => (1 : ℝ))
        (Matrix.vecMulVec (-(Sᵀ *ᵥ d)) fun _ : Fin 1 => (1 : ℝ))ᴴ
        (Matrix.vecMulVec (fun _ : Fin 1 => 1 - d ⬝ᵥ d) fun _ : Fin 1 => (1 : ℝ)) := by
  have e1 : ∀ a : Fin k, (Fin.castAdd 1 a : Fin (k + 1)) = Fin.castSucc a := fun _ => rfl
  have e2 : ∀ a : Fin 1, (Fin.natAdd k a : Fin (k + 1)) = Fin.last k := fun a =>
    Fin.ext (by simp [Fin.fin_one_eq_zero a])
  ext (a | a) (b | b)
  · simp [appendCol, Matrix.mul_apply, Matrix.one_apply, e1, Fin.castSucc_inj]
  · simp [appendCol, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
      e1, e2, Fin.castSucc_ne_last, mul_comm]
  · simp [appendCol, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
      e1, e2, (Fin.castSucc_ne_last _).symm, mul_comm]
  · simp [appendCol, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct, e2]

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm is invariant under a simultaneous reindexing of rows and columns. -/
private theorem l2_opNorm_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix ι ι ℝ) (e : κ ≃ ι) : ‖M.submatrix e e‖ = ‖M‖ := by
  refine le_antisymm (Matrix.l2_opNorm_submatrix_le M e.injective e.injective) ?_
  have h := Matrix.l2_opNorm_submatrix_le (M.submatrix e e) e.symm.injective e.symm.injective
  rwa [Matrix.submatrix_submatrix, e.self_comp_symm, Matrix.submatrix_id_id] at h

open scoped Matrix.Norms.L2Operator in
/-- **Lemma 10.3.1 (Kahan–Parlett).** Suppose `S ∈ ℝ^{n×k}` and `d ∈ ℝⁿ`. If `S₊ = [S | d]`,
`‖I_k − SᵀS‖₂ ≤ μ` and `|1 − dᵀd| ≤ δ`, then `‖I_{k+1} − S₊ᵀS₊‖₂ ≤ μ₊` with
`μ₊ = (μ + δ + √((μ − δ)² + 4 ‖Sᵀd‖₂²))/2`. `I − S₊ᵀS₊` is the symmetric block matrix
`[I − SᵀS, −Sᵀd; −dᵀS, 1 − dᵀd]` (reindexed from `Fin k ⊕ Fin 1`); backbone
`Matrix.l2_opNorm_fromBlocks_le_of_isHermitian`. -/
theorem lemma_10_3_1 {k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (d : Fin n → ℝ) {μ δ : ℝ}
    (hμ : ‖(1 : Matrix (Fin k) (Fin k) ℝ) - Sᵀ * S‖ ≤ μ) (hδ : |1 - d ⬝ᵥ d| ≤ δ) :
    ‖(1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) - (appendCol S d)ᵀ * appendCol S d‖ ≤
      (μ + δ + √((μ - δ) ^ 2 +
        4 * ‖(WithLp.toLp 2 (Sᵀ *ᵥ d) : EuclideanSpace ℝ (Fin k))‖ ^ 2)) / 2 := by
  have hone : ‖(WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)) : EuclideanSpace ℝ (Fin 1))‖ = 1 := by
    simp [EuclideanSpace.norm_eq]
  have hC : ‖Matrix.vecMulVec (-(Sᵀ *ᵥ d)) fun _ : Fin 1 => (1 : ℝ)‖ ≤
      ‖(WithLp.toLp 2 (Sᵀ *ᵥ d) : EuclideanSpace ℝ (Fin k))‖ := by
    rw [l2_opNorm_vecMulVec, hone, mul_one, WithLp.toLp_neg, norm_neg]
  have hD : ‖Matrix.vecMulVec (fun _ : Fin 1 => 1 - d ⬝ᵥ d) fun _ : Fin 1 => (1 : ℝ)‖ ≤ δ := by
    rw [l2_opNorm_vecMulVec, hone, mul_one]
    simpa [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] using hδ
  rw [← l2_opNorm_submatrix_equiv _ finSumFinEquiv, one_sub_appendCol_submatrix]
  exact Matrix.l2_opNorm_fromBlocks_le_of_isHermitian hμ hC hD

end GolubVanLoan.Chapter10
