import Numlib.LinearAlgebra.Matrix.BlockTridiagonal
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter10.Section01

/-!
# Golub–Van Loan §10.3: practical Lanczos procedures

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §10.3:
the two-vector implementation (10.3.1) of the Lanczos process, complete reorthogonalization by
Householder matrices (10.3.4), the "good Ritz pair" of selective reorthogonalization (§10.3.4),
the Kahan–Parlett Lemma 10.3.1, and block Lanczos (10.3.8)–(10.3.9) with Underwood's
Theorem 10.3.2.

## Conventions

The chapter's (`GolubVanLoan.Chapter10.Section01`). The two-vector program keeps the book's two
`n`-vectors `w`, `v` and swaps them in place, one entry at a time. The Householder programs are
chapter 5's (`houseOn`, `householderApplyLeft`, Algorithm 5.2.1, `backwardAccumulation`;
convention 13): (10.3.4) returns the reflector data it applied. Block Lanczos keeps its blocks as
`ℕ`-indexed families (0-based: `X 0` is the book's `X₁`), `[X_1 | ⋯ | X_k]` is `blockCols`
(columns indexed by (block, column)), `T̄_k` is the backbone's `Matrix.blockTridiagonal` of the
blocks, and statements about `k + 1` blocks avoid an empty `T̄_0`.

## Not formalized

The floating-point analysis of §10.3.2 and §10.3.4 — (10.3.2)–(10.3.3), (10.3.5)–(10.3.6) and the
`≈` estimates between them — is quoted from Paige without derivation. The application of
Theorem 8.1.16 at the end of §10.3.2 is invalid as printed (`T̂_k` is not `Q̂_kᵀ A Q̂_k`). The
ghost-eigenvalue discussion (§10.3.5) and the restarted block Lanczos of §10.3.7 are prose.
The book's "orthogonal to working precision" for (10.3.4) and the choice of `X_{k+1}` when some
`R_k` is rank deficient (Golub–Underwood) are prose.
-/

open scoped Matrix
open Krylov FloatingPoint
open GolubVanLoan.Chapter01
open GolubVanLoan.Chapter05 (houseOn householderApplyLeft householderProduct indexFrom)

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
  have h := List.idRun_foldlM_update_apply (fun (_ : Fin n) (q : ℝ × ℝ) =>
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

/-! ### Complete reorthogonalization with Householder matrices (10.3.4) -/

/-- The state of (10.3.4): the Lanczos vectors `q j` (the book's `q_{j+1}`), the coefficients
`alpha j`, `beta j` (the book's `α_{j+1}`, `β_{j+1}`), and the reflector data `H_0, …, H_k` the
program applied, in order, each with the `β` that `house` returned (convention 13). -/
structure HouseholderLanczosState (n : ℕ) where
  /-- The Lanczos vectors, `0`-based. -/
  q : ℕ → Fin n → ℝ
  /-- The diagonal coefficients, `0`-based. -/
  alpha : ℕ → ℝ
  /-- The off-diagonal coefficients, `0`-based. -/
  beta : ℕ → ℝ
  /-- The reflector data `H_0, …, H_k` in order. -/
  data : List ((Fin n → ℝ) × ℝ)

section Program

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- A stored reflector `(v, β)` applied to a vector: chapter 5's `householderApplyLeft` on the
one-column matrix `x` (all rows; `v` vanishes off the rows the reflector acts on). -/
def reflectorApply (h : (Fin n → ℝ) × ℝ) (x : Fin n → ℝ) : M (Fin n → ℝ) := do
  let C ← householderApplyLeft rnd h.1 h.2 (List.finRange n) [(0 : Fin 1)]
    (Matrix.of fun i (_ : Fin 1) => x i)
  pure fun i => C i 0

/-- The pass `k` of (10.3.4) (`1 ≤ k ≤ n − 1`, the book's index; the current vector `q_k` is
`q (k - 1)`): `α_k = q_kᵀ A q_k`, `r_k = (A − α_k I) q_k − β_{k−1} q_{k−1}` (`β_0 q_0 ≡ 0`),
`w = (H_{k−1} ⋯ H_0) r_k` (the stored reflectors applied in turn), `H_k` by `houseOn` on the
entries `k, …, n − 1` (0-based) of `w`, `β_k` the entry `k` of `H_k w`, and
`q_{k+1} = H_0 ⋯ H_k e_{k+1}` (the reflectors applied in reverse order). -/
noncomputable def householderLanczosStep (A : Matrix (Fin n) (Fin n) ℝ)
    (s : HouseholderLanczosState n) (k : Fin n) : M (HouseholderLanczosState n) := do
  let j := (k : ℕ) - 1
  let Aq ← algorithm_1_1_3 rnd A (s.q j) 0
  let a ← algorithm_1_1_1 rnd (s.q j) Aq
  let r ← algorithm_1_1_2 rnd (-a) (s.q j) Aq
  let r ← if j = 0 then pure r else algorithm_1_1_2 rnd (-s.beta (j - 1)) (s.q (j - 1)) r
  let w ← s.data.foldlM (fun w h => reflectorApply rnd h w) r
  let H ← houseOn rnd (indexFrom n k) w
  let Hw ← reflectorApply rnd H w
  let q ← (s.data ++ [H]).reverse.foldlM (fun x h => reflectorApply rnd h x)
    (Pi.single k 1 : Fin n → ℝ)
  pure
    { q := Function.update s.q k q
      alpha := Function.update s.alpha j a
      beta := Function.update s.beta j (Hw k)
      data := s.data ++ [H] }

/-- **(10.3.4), Lanczos with complete reorthogonalization by Householder matrices**:
```
r_0 = q_1 (given unit vector)
Determine Householder H_0 so H_0 r_0 = e_1.
for k = 1:n-1
    α_k = q_kᵀ A q_k
    r_k = (A − α_k I) q_k − β_{k−1} q_{k−1},   (β_0 q_0 ≡ 0)
    w = (H_{k−1} ⋯ H_0) r_k
    Determine Householder H_k so H_k w = [w_1, …, w_k, β_k, 0, …, 0]ᵀ.
    q_{k+1} = H_0 ⋯ H_k e_{k+1}
end
```
No early exit ("it makes no difference if `β_k = 0`"). `H_0` is chapter 5's `houseOn` on all
entries of `q₁`; the program returns the reflector data it applied. -/
noncomputable def householderLanczos (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ) :
    M (HouseholderLanczosState n) := do
  let H₀ ← houseOn rnd (indexFrom n 0) q₁
  (List.finRange (n - 1)).foldlM
    (fun s (k : Fin (n - 1)) =>
      householderLanczosStep rnd A s ⟨k + 1, Nat.add_lt_of_lt_sub k.isLt⟩)
    { q := Function.update 0 0 q₁, alpha := 0, beta := 0, data := [H₀] }

end Program

/-- The reflector `I − β v vᵀ` of reflector data. -/
private noncomputable abbrev reflMat (h : (Fin n → ℝ) × ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - h.2 • Matrix.vecMulVec h.1 h.1

private theorem reflMat_transpose (h : (Fin n → ℝ) × ℝ) : (reflMat h)ᵀ = reflMat h := by
  simp [reflMat, Matrix.transpose_sub, Matrix.transpose_vecMulVec]

private theorem reflectorApply_exact (h : (Fin n → ℝ) × ℝ) (x : Fin n → ℝ) :
    Id.run (reflectorApply pure h x) = reflMat h *ᵥ x := by
  simp only [reflectorApply, Id.run_bind, Id.run_pure]
  rw [GolubVanLoan.Chapter05.householderApplyLeft_spec_of_forall_mem (List.nodup_finRange n)
    (List.nodup_singleton _) (fun q => by simp [Fin.fin_one_eq_zero q])
    (fun i hi => absurd (List.mem_finRange i) hi)]
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

private theorem foldlM_reflectorApply_exact (data : List ((Fin n → ℝ) × ℝ))
    (x : Fin n → ℝ) :
    Id.run (data.foldlM (fun w h => reflectorApply pure h w) x) =
      (householderProduct data)ᵀ *ᵥ x := by
  rw [List.idRun_foldlM]
  induction data generalizing x with
  | nil => simp
  | cons h t ih =>
    rw [List.foldl_cons, ih, reflectorApply_exact, GolubVanLoan.Chapter05.householderProduct_cons,
      Matrix.transpose_mul, reflMat_transpose, Matrix.mulVec_mulVec]

private theorem foldlM_reverse_reflectorApply_exact (data : List ((Fin n → ℝ) × ℝ))
    (x : Fin n → ℝ) :
    Id.run (data.reverse.foldlM (fun x h => reflectorApply pure h x) x) =
      householderProduct data *ᵥ x := by
  rw [List.idRun_foldlM, List.foldl_reverse]
  induction data with
  | nil => simp
  | cons h t ih =>
    rw [List.foldr_cons, ih, reflectorApply_exact, GolubVanLoan.Chapter05.householderProduct_cons,
      Matrix.mulVec_mulVec]

/-- The exact residual `r_k` of the pass with current vector `q_j` (`j = k - 1`). -/
private noncomputable def hlR (A : Matrix (Fin n) (Fin n) ℝ) (s : HouseholderLanczosState n)
    (j : ℕ) : Fin n → ℝ :=
  A *ᵥ s.q j - (s.q j ⬝ᵥ A *ᵥ s.q j) • s.q j - if j = 0 then 0 else s.beta (j - 1) • s.q (j - 1)

/-- The exact vector `w = (H_{k-1} ⋯ H_0) r_k`. -/
private noncomputable def hlW (A : Matrix (Fin n) (Fin n) ℝ) (s : HouseholderLanczosState n)
    (j : ℕ) : Fin n → ℝ :=
  (householderProduct s.data)ᵀ *ᵥ hlR A s j

/-- The exact reflector data `H_k` (`k = j + 1`). -/
private noncomputable def hlH (A : Matrix (Fin n) (Fin n) ℝ) (s : HouseholderLanczosState n)
    (j : ℕ) : (Fin n → ℝ) × ℝ :=
  Id.run (houseOn pure (indexFrom n (j + 1)) (hlW A s j))

private theorem householderLanczosStep_exact (A : Matrix (Fin n) (Fin n) ℝ)
    (s : HouseholderLanczosState n) (j : ℕ) (hj : j + 1 < n) :
    Id.run (householderLanczosStep pure A s ⟨j + 1, hj⟩) =
      { q := Function.update s.q (j + 1) (householderProduct (s.data ++ [hlH A s j]) *ᵥ
          (Pi.single ⟨j + 1, hj⟩ 1 : Fin n → ℝ))
        alpha := Function.update s.alpha j (s.q j ⬝ᵥ A *ᵥ s.q j)
        beta := Function.update s.beta j ((reflMat (hlH A s j) *ᵥ hlW A s j) ⟨j + 1, hj⟩)
        data := s.data ++ [hlH A s j] } := by
  have hr0 : j = 0 → Id.run (algorithm_1_1_2 pure (-(s.q j ⬝ᵥ A *ᵥ s.q j)) (s.q j)
      (A *ᵥ s.q j)) = hlR A s j := by
    intro hj0
    simp [hlR, hj0, algorithm_1_1_2_spec, sub_eq_add_neg]
  have hr1 : j ≠ 0 → Id.run (algorithm_1_1_2 pure (-s.beta (j - 1)) (s.q (j - 1))
      (Id.run (algorithm_1_1_2 pure (-(s.q j ⬝ᵥ A *ᵥ s.q j)) (s.q j) (A *ᵥ s.q j)))) =
      hlR A s j := by
    intro hj0
    simp [hlR, hj0, algorithm_1_1_2_spec, sub_eq_add_neg, add_assoc]
  simp only [householderLanczosStep, Id.run_bind, algorithm_1_1_3_spec, algorithm_1_1_1_spec,
    Nat.add_sub_cancel, zero_add]
  split_ifs with hj0
  · simp only [Id.run_bind, Id.run_pure, hr0 hj0, foldlM_reflectorApply_exact,
      GolubVanLoan.Chapter05.householderProduct_reverse_transpose, reflectorApply_exact]
    rfl
  · simp only [Id.run_bind, Id.run_pure, hr1 hj0, foldlM_reflectorApply_exact,
      GolubVanLoan.Chapter05.householderProduct_reverse_transpose, reflectorApply_exact]
    rfl


/-- An orthogonal matrix preserves dot products. -/
private theorem dotProduct_mulVec_mulVec_of_mem {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) (x y : Fin n → ℝ) :
    (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
    (Matrix.mem_orthogonalGroup_iff' _ _).1 hQ, Matrix.one_mulVec]

/-- The transpose of an orthogonal matrix preserves dot products. -/
private theorem dotProduct_transpose_mulVec_of_mem {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) (x y : Fin n → ℝ) :
    (Qᵀ *ᵥ x) ⬝ᵥ (Qᵀ *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
    (Matrix.mem_orthogonalGroup_iff _ _).1 hQ, Matrix.one_mulVec]

/-- Reflector data with `β = 0` or `β vᵀv = 2` give an orthogonal matrix. -/
private theorem reflMat_mem {h : (Fin n → ℝ) × ℝ} (hh : h.2 = 0 ∨ h.2 * (h.1 ⬝ᵥ h.1) = 2) :
    reflMat h ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  have := GolubVanLoan.Chapter05.householderProduct_mem_orthogonalGroup (data := [h])
    (by simpa using hh)
  simpa using this

/-- Such a reflector is an involution. -/
private theorem reflMat_mul_self {h : (Fin n → ℝ) × ℝ}
    (hh : h.2 = 0 ∨ h.2 * (h.1 ⬝ᵥ h.1) = 2) : reflMat h * reflMat h = 1 :=
  GolubVanLoan.Chapter05.one_sub_smul_vecMulVec_mul_self_of_mem (reflMat_mem hh)

/-- A reflector whose vector vanishes at `i` fixes `e_i`. -/
private theorem reflMat_mulVec_single {h : (Fin n → ℝ) × ℝ} {i : Fin n} (hi : h.1 i = 0) :
    reflMat h *ᵥ (Pi.single i 1 : Fin n → ℝ) = Pi.single i 1 := by
  ext l
  simp [Matrix.vecMulVec_apply, hi, Matrix.one_apply, Pi.single_apply]

/-- An entry of `Qᵀ r` is the dot product of the column `Q e_i` with `r`. -/
private theorem transpose_mulVec_apply (Q : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ)
    (i : Fin n) : (Qᵀ *ᵥ r) i = (Q *ᵥ (Pi.single i 1 : Fin n → ℝ)) ⬝ᵥ r := by
  rw [Matrix.mulVec_single_one]
  rfl

/-- The invariant of (10.3.4) after `t` passes. -/
private structure HLInv (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ) (t : ℕ)
    (s : HouseholderLanczosState n) : Prop where
  data_mem : ∀ p ∈ s.data, p.2 = 0 ∨ p.2 * (p.1 ⬝ᵥ p.1) = 2
  length : s.data.length = t + 1
  q_eq : ∀ i : Fin n, (i : ℕ) ≤ t →
    s.q i = householderProduct s.data *ᵥ (Pi.single i 1 : Fin n → ℝ)
  q_eq_take : ∀ i : Fin n, (i : ℕ) ≤ t →
    s.q i = householderProduct (s.data.take (i + 1)) *ᵥ (Pi.single i 1 : Fin n → ℝ)
  q_vec : ∀ i ≤ t, i < grade (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁) →
    s.q i = (Arnoldi.vec (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁) i).ofLp
  coeff : ∀ j < t, j < grade (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁) →
    s.alpha j = Lanczos.alpha (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁) j ∧
      s.beta j = Lanczos.beta (Matrix.toEuclideanLin A) (WithLp.toLp 2 q₁) j

/-- The next Arnoldi residual is `β_t` times the next Arnoldi vector. -/
private theorem arnoldi_w_eq_smul (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (q : EuclideanSpace ℝ (Fin n)) (t : ℕ) :
    Arnoldi.w T q t = ‖Arnoldi.w T q t‖ • Arnoldi.vec T q (t + 1) := by
  by_cases h : Arnoldi.w T q t = 0
  · simp [h]
  · rw [Arnoldi.vec_succ_eq, smul_smul]
    simp [h]

/-- The Arnoldi residual `w_t` is orthogonal to the vectors `v_i`, `i ≤ t`. -/
private theorem vec_dotProduct_w (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (q : EuclideanSpace ℝ (Fin n)) {i t : ℕ} (hi : i ≤ t) :
    (Arnoldi.vec T q i).ofLp ⬝ᵥ (Arnoldi.w T q t).ofLp = 0 := by
  have h := Arnoldi.inner_vec_eq_zero T q (i := i) (j := t + 1) (by omega)
  rw [arnoldi_w_eq_smul T q t, WithLp.ofLp_smul, dotProduct_smul]
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] at h
  rw [h, smul_zero]

/-- `‖x‖² = x ⬝ x` on `EuclideanSpace ℝ (Fin n)`. -/
private theorem norm_sq_eq_dotProduct (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

/-- One pass preserves the invariant. -/
private theorem hlInv_step {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {q₁ : Fin n → ℝ}
    {t : ℕ} (ht : t + 1 < n) {s : HouseholderLanczosState n} (h : HLInv A q₁ t s) :
    HLInv A q₁ (t + 1) (Id.run (householderLanczosStep pure A s ⟨t + 1, ht⟩)) := by
  set T := Matrix.toEuclideanLin A
  set q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 q₁
  have hT : T.IsSymmetric := hA.isSymmetric_toEuclideanLin
  have hTx : ∀ x, (T x).ofLp = A *ᵥ x.ofLp := fun x => rfl
  have hα : ∀ j, (Arnoldi.vec T q j).ofLp ⬝ᵥ (A *ᵥ (Arnoldi.vec T q j).ofLp) =
      Lanczos.alpha T q j := fun j => by
    rw [Lanczos.alpha, Arnoldi.coeff, RCLike.re_to_real,
      EuclideanSpace.inner_eq_star_dotProduct, hTx, star_trivial, dotProduct_comm]
  have hqv : ∀ i ≤ t, i < grade T q → s.q i = (Arnoldi.vec T q i).ofLp := h.q_vec
  have hco : ∀ j < t, j < grade T q →
      s.alpha j = Lanczos.alpha T q j ∧ s.beta j = Lanczos.beta T q j := h.coeff
  rw [householderLanczosStep_exact A s t ht]
  set P := householderProduct s.data with hPdef
  have hP : P ∈ Matrix.orthogonalGroup (Fin n) ℝ :=
    GolubVanLoan.Chapter05.householderProduct_mem_orthogonalGroup h.data_mem
  set w := hlW A s t with hw
  set H := hlH A s t with hH
  have hne : indexFrom n (t + 1) ≠ [] := GolubVanLoan.Chapter05.indexFrom_ne_nil ht
  obtain ⟨-, hvoff, hβH, -, hmul⟩ :=
    GolubVanLoan.Chapter05.houseOn_spec (GolubVanLoan.Chapter05.nodup_indexFrom n (t + 1)) hne w
  rw [GolubVanLoan.Chapter05.head_indexFrom ht hne] at hmul
  change reflMat H *ᵥ w = _ at hmul
  change H.2 = 0 ∨ H.2 * (H.1 ⬝ᵥ H.1) = 2 at hβH
  change ∀ i, i ∉ indexFrom n (t + 1) → H.1 i = 0 at hvoff
  have hHoff : ∀ i : Fin n, (i : ℕ) ≤ t → H.1 i = 0 := fun i hi =>
    hvoff i (by rw [GolubVanLoan.Chapter05.mem_indexFrom]; omega)
  have hP' : householderProduct (s.data ++ [H]) = P * reflMat H := by
    rw [GolubVanLoan.Chapter05.householderProduct_concat]
  -- the parts of the invariant not involving the Lanczos vectors
  have hq_old : ∀ i : Fin n, (i : ℕ) ≤ t →
      Function.update s.q (t + 1) (householderProduct (s.data ++ [H]) *ᵥ
        (Pi.single ⟨t + 1, ht⟩ 1 : Fin n → ℝ)) i = s.q i := fun i hi =>
    Function.update_of_ne (by omega) _ _
  -- the Lanczos step, below the grade
  have key : t < grade T q →
      (s.q t ⬝ᵥ A *ᵥ s.q t = Lanczos.alpha T q t ∧
        (reflMat H *ᵥ w) ⟨t + 1, ht⟩ = Lanczos.beta T q t) ∧
      (t + 1 < grade T q →
        householderProduct (s.data ++ [H]) *ᵥ (Pi.single ⟨t + 1, ht⟩ 1 : Fin n → ℝ) =
          (Arnoldi.vec T q (t + 1)).ofLp) := by
    intro htg
    have hqt := hqv t le_rfl htg
    -- the residual is the Arnoldi residual
    have hR : hlR A s t = (Arnoldi.w T q t).ofLp := by
      unfold hlR
      rw [hqt, hα]
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · simp only [↓reduceIte, sub_zero, Arnoldi.w, zero_add, Finset.sum_range_one,
          WithLp.ofLp_sub, WithLp.ofLp_smul, hTx]
        rw [← Lanczos.coe_alpha q hT 0]
        simp
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [ite_eq_right (by omega), Nat.add_sub_cancel, hqv t' (by omega) (by omega),
          (hco t' (by omega) (by omega)).2, Lanczos.w_succ_eq q hT t']
        simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, hTx, RCLike.ofReal_real_eq_id, id]
    have hw_eq : w = Pᵀ *ᵥ (Arnoldi.w T q t).ofLp := by rw [hw, hlW, hR]
    have hwz : ∀ i : Fin n, (i : ℕ) ≤ t → w i = 0 := by
      intro i hi
      rw [hw_eq, transpose_mulVec_apply, ← h.q_eq i hi, hqv i hi (by omega)]
      exact vec_dotProduct_w T q hi
    set c := ‖(WithLp.toLp 2 (fun j : {j // j ∈ indexFrom n (t + 1)} => w j) :
      EuclideanSpace ℝ {j // j ∈ indexFrom n (t + 1)})‖ with hc
    have hy : reflMat H *ᵥ w = c • (Pi.single ⟨t + 1, ht⟩ 1 : Fin n → ℝ) := by
      rw [hmul]
      funext i
      by_cases hik : i = ⟨t + 1, ht⟩
      · rw [ite_eq_left hik, hik]
        simp
      · rw [ite_eq_right hik]
        by_cases hio : i ∈ indexFrom n (t + 1)
        · simp [hio, hik]
        · rw [ite_eq_right hio,
            hwz i (by rw [GolubVanLoan.Chapter05.mem_indexFrom] at hio; omega)]
          simp [hik]
    have hcnn : 0 ≤ c := norm_nonneg _
    have hc2 : c ^ 2 = Lanczos.beta T q t ^ 2 := by
      have h1 := dotProduct_mulVec_mulVec_of_mem (reflMat_mem hβH) w w
      rw [hy] at h1
      rw [hw_eq, dotProduct_transpose_mulVec_of_mem hP,
        ← norm_sq_eq_dotProduct (Arnoldi.w T q t)] at h1
      rw [Lanczos.beta, ← h1]
      simp [sq]
    have hcβ : c = Lanczos.beta T q t := (sq_eq_sq₀ hcnn (Lanczos.beta_nonneg T q t)).1 hc2
    refine ⟨⟨by rw [hqt, hα], by rw [hy, hcβ]; simp⟩, fun htg' => ?_⟩
    have hβne : Lanczos.beta T q t ≠ 0 := by
      rw [Ne, Lanczos.beta_eq_zero_iff q hT t]
      omega
    have hHe : reflMat H *ᵥ (Pi.single ⟨t + 1, ht⟩ 1 : Fin n → ℝ) = c⁻¹ • w := by
      have h2 := congrArg (fun x => reflMat H *ᵥ x) hy
      simp only [Matrix.mulVec_mulVec, reflMat_mul_self hβH, Matrix.one_mulVec,
        Matrix.mulVec_smul] at h2
      rw [h2, smul_smul, inv_mul_cancel₀ (hcβ ▸ hβne), one_smul]
    rw [hP', ← Matrix.mulVec_mulVec, hHe, Matrix.mulVec_smul, hw_eq, Matrix.mulVec_mulVec,
      (Matrix.mem_orthogonalGroup_iff _ _).1 hP, Matrix.one_mulVec, hcβ, Arnoldi.vec_succ_eq,
      WithLp.ofLp_smul, Lanczos.beta]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact h.data_mem p hp
    · rw [List.mem_singleton.1 hp]; exact hβH
  · simp [h.length]
  · intro i hi
    rcases Nat.le_succ_iff.1 hi with hi | hi
    · simp only
      rw [hq_old i (by omega), h.q_eq i (by omega), hP', ← Matrix.mulVec_mulVec,
        reflMat_mulVec_single (hHoff i (by omega))]
    · have hik : i = ⟨t + 1, ht⟩ := Fin.ext hi
      subst hik
      simp
  · intro i hi
    rcases Nat.le_succ_iff.1 hi with hi | hi
    · simp only
      rw [hq_old i (by omega), h.q_eq_take i (by omega),
        List.take_append_of_le_length (by rw [h.length]; omega)]
    · have hik : i = ⟨t + 1, ht⟩ := Fin.ext hi
      subst hik
      simp only [Function.update_self]
      rw [List.take_of_length_le (by simp [h.length])]
  · intro i hi hig
    rcases Nat.le_succ_iff.1 hi with hi | rfl
    · simp only
      rw [Function.update_of_ne (by omega)]
      exact hqv i hi hig
    · simp only [Function.update_self]
      exact (key (lt_trans (Nat.lt_succ_self t) hig)).2 hig
  · intro j hj hjg
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · simp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hco j hj hjg
    · simp only [Function.update_self]
      exact (key hjg).1


/-- **Exact semantics of (10.3.4)**: for symmetric `A` and a unit `q₁`, every returned reflector
is the identity or a Householder matrix (`β = 0` or `β vᵀv = 2`, convention 13), the computed
`q_{j+1}` is column `j + 1` of `H_0 ⋯ H_j` (the product of the first `j + 1` returned
reflectors), the `n` computed vectors are orthonormal, below the grade `m` of `q₁` they are the
Lanczos (Arnoldi) vectors, and there the computed `α_j`, `β_j` are the backbone's `Lanczos.alpha`,
`Lanczos.beta` (with `β_j ≥ 0`: `house` maps `w` to `+‖w‖ e`). Past the grade the vectors
continue an orthonormal basis (the book's "may safely run until `k = n − 1`"). -/
theorem equation_10_3_4 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {q₁ : Fin n → ℝ}
    (hq : ‖(WithLp.toLp 2 q₁ : EuclideanSpace ℝ (Fin n))‖ = 1) :
    let s := Id.run (householderLanczos pure A q₁)
    let T := Matrix.toEuclideanLin A
    let q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 q₁
    (∀ p ∈ s.data, p.2 = 0 ∨ p.2 * (p.1 ⬝ᵥ p.1) = 2) ∧
      (∀ i : Fin n, s.q i =
        householderProduct (s.data.take (i + 1)) *ᵥ (Pi.single i 1 : Fin n → ℝ)) ∧
      (∀ i j : Fin n, s.q i ⬝ᵥ s.q j = if i = j then 1 else 0) ∧
      (∀ j : Fin n, (j : ℕ) < grade T q → s.q j = (Arnoldi.vec T q j).ofLp) ∧
      ∀ j, j + 1 < n → j < grade T q →
        s.alpha j = Lanczos.alpha T q j ∧ s.beta j = Lanczos.beta T q j := by
  intro s T q
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : ‖q‖ = 1 := hq
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (Subsingleton.elim q 0) hq0
    · exact hn
  have hv0 : (Arnoldi.vec T q 0).ofLp = q₁ := by
    rw [Arnoldi.vec_zero T q hq0, show ‖q‖ = 1 from hq]
    simp [q]
  have hqq : q₁ ⬝ᵥ q₁ = 1 := by
    have h1 := norm_sq_eq_dotProduct q
    rw [show ‖q‖ = 1 from hq] at h1
    simpa [q] using h1.symm
  -- the initial state
  set H₀ := Id.run (houseOn pure (indexFrom n 0) q₁) with hH₀
  set init : HouseholderLanczosState n :=
    { q := Function.update 0 0 q₁, alpha := 0, beta := 0, data := [H₀] } with hinit
  set f : HouseholderLanczosState n → Fin (n - 1) → HouseholderLanczosState n :=
    fun s k => Id.run (householderLanczosStep pure A s ⟨k + 1, Nat.add_lt_of_lt_sub k.isLt⟩)
    with hf
  have hprog : s = (List.finRange (n - 1)).foldl f init := by
    simp only [s, householderLanczos, Id.run_bind, List.idRun_foldlM]
    rfl
  have hne : indexFrom n 0 ≠ [] := GolubVanLoan.Chapter05.indexFrom_ne_nil hn
  obtain ⟨-, -, hβ₀, -, hmul₀⟩ :=
    GolubVanLoan.Chapter05.houseOn_spec (GolubVanLoan.Chapter05.nodup_indexFrom n 0) hne q₁
  rw [GolubVanLoan.Chapter05.head_indexFrom hn hne] at hmul₀
  change reflMat H₀ *ᵥ q₁ = _ at hmul₀
  change H₀.2 = 0 ∨ H₀.2 * (H₀.1 ⬝ᵥ H₀.1) = 2 at hβ₀
  set c := ‖(WithLp.toLp 2 (fun j : {j // j ∈ indexFrom n 0} => q₁ j) :
      EuclideanSpace ℝ {j // j ∈ indexFrom n 0})‖ with hc
  have hy : reflMat H₀ *ᵥ q₁ = c • (Pi.single ⟨0, hn⟩ 1 : Fin n → ℝ) := by
    rw [hmul₀]
    funext i
    by_cases hi : i = ⟨0, hn⟩
    · subst hi; simp
    · simp [hi, GolubVanLoan.Chapter05.mem_indexFrom]
  have hc1 : c = 1 := by
    have h1 := dotProduct_mulVec_mulVec_of_mem (reflMat_mem hβ₀) q₁ q₁
    rw [hy, hqq] at h1
    have hcnn : 0 ≤ c := norm_nonneg _
    have h2 : c ^ 2 = 1 ^ 2 := by simpa [sq] using h1
    exact (sq_eq_sq₀ hcnn zero_le_one).1 h2
  have hinit_q : reflMat H₀ *ᵥ (Pi.single ⟨0, hn⟩ 1 : Fin n → ℝ) = q₁ := by
    have h2 := congrArg (fun x => reflMat H₀ *ᵥ x) hy
    simp only [Matrix.mulVec_mulVec, reflMat_mul_self hβ₀, Matrix.one_mulVec, hc1,
      one_smul] at h2
    exact h2.symm
  have h0 : HLInv A q₁ 0 init := by
    refine ⟨?_, rfl, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · intro p hp
      rw [List.mem_singleton.1 hp]
      exact hβ₀
    · intro i hi
      obtain rfl : i = ⟨0, hn⟩ := Fin.ext (Nat.le_zero.1 hi)
      simp [init, hinit_q]
    · intro i hi
      obtain rfl : i = ⟨0, hn⟩ := Fin.ext (Nat.le_zero.1 hi)
      simp [init, hinit_q]
    · intro i hi _
      obtain rfl : i = 0 := by omega
      simp only [init, Function.update_self]
      exact hv0.symm
  have hall : ∀ t ≤ n - 1, HLInv A q₁ t (((List.finRange (n - 1)).take t).foldl f init) := by
    intro t
    induction t with
    | zero => intro _; simpa using h0
    | succ t ih =>
      intro ht
      rw [List.take_succ_eq_append_getElem (by simpa using ht), List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have hget : (List.finRange (n - 1))[t]'(by simpa using ht) = ⟨t, by omega⟩ := by simp
      rw [hget]
      exact hlInv_step hA (by omega) (ih (by omega))
  have hs := hall (n - 1) le_rfl
  rw [List.take_of_length_le (by simp), ← hprog] at hs
  have hP : householderProduct s.data ∈ Matrix.orthogonalGroup (Fin n) ℝ :=
    GolubVanLoan.Chapter05.householderProduct_mem_orthogonalGroup hs.data_mem
  refine ⟨hs.data_mem, fun i => hs.q_eq_take i (by omega), fun i j => ?_,
    fun j hj => hs.q_vec j (by omega) hj, fun j hj hjg => hs.coeff j (by omega) hjg⟩
  rw [hs.q_eq i (by omega), hs.q_eq j (by omega), dotProduct_mulVec_mulVec_of_mem hP]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

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
/-- **Lemma 10.3.1 (Kahan–Parlett).** Suppose `S ∈ ℝ^{n×k}` and `d ∈ ℝⁿ`. If `S₊ = [S | d]`,
`‖I_k − SᵀS‖₂ ≤ μ` and `|1 − dᵀd| ≤ δ`, then `‖I_{k+1} − S₊ᵀS₊‖₂ ≤ μ₊` with
`μ₊ = (μ + δ + √((μ − δ)² + 4 ‖Sᵀd‖₂²))/2`. `I − S₊ᵀS₊` is the symmetric block matrix
`[I − SᵀS, −Sᵀd; −dᵀS, 1 − dᵀd]` (reindexed from `Fin k ⊕ Fin 1`); backbone
`Matrix.l2_opNorm_fromBlocks_conjTranspose_le`. -/
theorem lemma_10_3_1 {k : ℕ} (S : Matrix (Fin n) (Fin k) ℝ) (d : Fin n → ℝ) {μ δ : ℝ}
    (hμ : ‖(1 : Matrix (Fin k) (Fin k) ℝ) - Sᵀ * S‖ ≤ μ) (hδ : |1 - d ⬝ᵥ d| ≤ δ) :
    ‖(1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) - (appendCol S d)ᵀ * appendCol S d‖ ≤
      (μ + δ + √((μ - δ) ^ 2 +
        4 * ‖(WithLp.toLp 2 (Sᵀ *ᵥ d) : EuclideanSpace ℝ (Fin k))‖ ^ 2)) / 2 := by
  have hone : ‖(WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)) : EuclideanSpace ℝ (Fin 1))‖ = 1 := by
    simp [EuclideanSpace.norm_eq]
  have hC : ‖Matrix.vecMulVec (-(Sᵀ *ᵥ d)) fun _ : Fin 1 => (1 : ℝ)‖ ≤
      ‖(WithLp.toLp 2 (Sᵀ *ᵥ d) : EuclideanSpace ℝ (Fin k))‖ := by
    rw [Matrix.l2_opNorm_vecMulVec, hone, mul_one, WithLp.toLp_neg, norm_neg]
  have hD : ‖Matrix.vecMulVec (fun _ : Fin 1 => 1 - d ⬝ᵥ d) fun _ : Fin 1 => (1 : ℝ)‖ ≤ δ := by
    rw [Matrix.l2_opNorm_vecMulVec, hone, mul_one]
    simpa [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] using hδ
  rw [← Matrix.l2_opNorm_submatrix_equiv _ finSumFinEquiv finSumFinEquiv,
    one_sub_appendCol_submatrix]
  exact Matrix.l2_opNorm_fromBlocks_conjTranspose_le hμ hC hD

/-! ### Block Lanczos (10.3.6): (10.3.8), (10.3.9) and Theorem 10.3.2 -/

section BlockLanczos

variable {p : ℕ}

/-- The state of block Lanczos (10.3.8): the blocks `X b`, `M b`, `B b` (0-based; `X 0` is the
book's `X₁`, `B b` the book's `B_{b+1}`). -/
structure BlockLanczosState (n p : ℕ) where
  /-- The blocks of Lanczos vectors, `0`-based (`X 0` is the book's `X₁`). -/
  X : ℕ → Matrix (Fin n) (Fin p) ℝ
  /-- The diagonal blocks, `0`-based. -/
  M : ℕ → Matrix (Fin p) (Fin p) ℝ
  /-- The subdiagonal blocks, `0`-based. -/
  B : ℕ → Matrix (Fin p) (Fin p) ℝ

section BlockProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The pass `k` (0-based; the book's pass `k + 1`) of (10.3.8):
`R = A X_k − X_k M_k − X_{k−1} B_{k−1}ᵀ` (Algorithm 1.1.5; the last term is absent for `k = 0`),
the QR factorization `X_{k+1} B_k = R` by chapter 5's Algorithm 5.2.1 and backward accumulation of
its reflector data (`X_{k+1}` the first `p` columns of `Q`, `B_k` the first `p` rows of `R`,
`p ≤ n`), and `M_{k+1} = X_{k+1}ᵀ A X_{k+1}`. -/
noncomputable def blockLanczosStep (hpn : p ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (s : BlockLanczosState n p) (k : ℕ) : M (BlockLanczosState n p) := do
  let AX ← algorithm_1_1_5 rnd A (s.X k) 0
  let R ← algorithm_1_1_5 rnd (-s.X k) (s.M k) AX
  let R ← if k = 0 then pure R else algorithm_1_1_5 rnd (-s.X (k - 1)) (s.B (k - 1))ᵀ R
  let F ← GolubVanLoan.Chapter05.algorithm_5_2_1 rnd R
  let Q ← GolubVanLoan.Chapter05.backwardAccumulation rnd
    (GolubVanLoan.Chapter05.storedReflectors F.1 F.2)
  let X : Matrix (Fin n) (Fin p) ℝ := Q.submatrix id (Fin.castLE hpn)
  let AX ← algorithm_1_1_5 rnd A X 0
  let Mk ← algorithm_1_1_5 rnd Xᵀ AX 0
  pure
    { X := Function.update s.X (k + 1) X
      M := Function.update s.M (k + 1) Mk
      B := Function.update s.B k
        ((GolubVanLoan.Chapter05.upperPart F.1).submatrix (Fin.castLE hpn) id) }

/-- **(10.3.8), block Lanczos**:
```
X_1 ∈ ℝ^{n×p} given with X_1ᵀ X_1 = I_p
M_1 = X_1ᵀ A X_1
for k = 1:r-1
    R_k = A X_k − X_k M_k − X_{k−1} B_{k−1}ᵀ   (X_0 B_0ᵀ ≡ 0)
    X_{k+1} B_k = R_k   (QR factorization of R_k)
    M_{k+1} = X_{k+1}ᵀ A X_{k+1}
end
```
-/
noncomputable def blockLanczos (hpn : p ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (X₁ : Matrix (Fin n) (Fin p) ℝ) (r : ℕ) : M (BlockLanczosState n p) := do
  let AX ← algorithm_1_1_5 rnd A X₁ 0
  let M₁ ← algorithm_1_1_5 rnd X₁ᵀ AX 0
  (List.range (r - 1)).foldlM (blockLanczosStep rnd hpn A)
    { X := Function.update 0 0 X₁, M := Function.update 0 0 M₁, B := 0 }

end BlockProgram

/-- The book's residual block `R_k = A X_k − X_k M_k − X_{k−1} B_{k−1}ᵀ` of a state (0-based,
`X_{-1} B_{-1}ᵀ ≡ 0`). -/
def blockResidual (A : Matrix (Fin n) (Fin n) ℝ) (s : BlockLanczosState n p) (k : ℕ) :
    Matrix (Fin n) (Fin p) ℝ :=
  A * s.X k - s.X k * s.M k - if k = 0 then 0 else s.X (k - 1) * (s.B (k - 1))ᵀ

/-- `[X_1 | ⋯ | X_k]`: the first `k` blocks side by side, columns indexed by (block, column). -/
def blockCols (X : ℕ → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) : Matrix (Fin n) (Fin k × Fin p) ℝ :=
  Matrix.of fun i jl => X jl.1 i jl.2

/-- `[0 | ⋯ | 0 | I_p] ∈ ℝ^{p × kp}`, columns indexed by (block, column). -/
def lastBlockSel (p k : ℕ) : Matrix (Fin p) (Fin k × Fin p) ℝ :=
  Matrix.of fun l bl => if (bl.1 : ℕ) + 1 = k ∧ l = bl.2 then 1 else 0

/-- The exact output of Algorithm 5.2.1 on `R`. -/
private noncomputable def qrOut (R : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin n) (Fin p) ℝ × (Fin p → ℝ) :=
  Id.run (GolubVanLoan.Chapter05.algorithm_5_2_1 pure R)

/-- The exact `X_{k+1}`. -/
private noncomputable def qrX (hpn : p ≤ n) (R : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin n) (Fin p) ℝ :=
  (GolubVanLoan.Chapter05.factoredQ (qrOut R).2 (qrOut R).1).submatrix id (Fin.castLE hpn)

/-- The exact `B_k`. -/
private noncomputable def qrB (hpn : p ≤ n) (R : Matrix (Fin n) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  (GolubVanLoan.Chapter05.upperPart (qrOut R).1).submatrix (Fin.castLE hpn) id

private theorem blockLanczosStep_exact (hpn : p ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (s : BlockLanczosState n p) (k : ℕ) :
    Id.run (blockLanczosStep pure hpn A s k) =
      { X := Function.update s.X (k + 1) (qrX hpn (blockResidual A s k))
        M := Function.update s.M (k + 1)
          ((qrX hpn (blockResidual A s k))ᵀ * (A * qrX hpn (blockResidual A s k)))
        B := Function.update s.B k (qrB hpn (blockResidual A s k)) } := by
  have hr0 : k = 0 → A * s.X k + -s.X k * s.M k = blockResidual A s k := by
    intro hk
    simp [blockResidual, hk, sub_eq_add_neg]
  have hr1 : k ≠ 0 → A * s.X k + -s.X k * s.M k + -s.X (k - 1) * (s.B (k - 1))ᵀ =
      blockResidual A s k := by
    intro hk
    simp [blockResidual, hk, sub_eq_add_neg]
  simp only [blockLanczosStep, Id.run_bind, algorithm_1_1_5_spec, zero_add]
  split_ifs with hk0
  · simp only [Id.run_bind, Id.run_pure, hr0 hk0, algorithm_1_1_5_spec, zero_add,
      GolubVanLoan.Chapter05.backwardAccumulation_spec]
    rfl
  · simp only [Id.run_bind, Id.run_pure, hr1 hk0, algorithm_1_1_5_spec, zero_add,
      GolubVanLoan.Chapter05.backwardAccumulation_spec]
    rfl

/-- The exact QR step: `X_{k+1} B_k = R_k`, `X_{k+1}ᵀ X_{k+1} = I`, `B_k` upper triangular. -/
private theorem qr_facts (hpn : p ≤ n) (R : Matrix (Fin n) (Fin p) ℝ) :
    qrX hpn R * qrB hpn R = R ∧ (qrX hpn R)ᵀ * qrX hpn R = 1 ∧
      ∀ i j : Fin p, j < i → qrB hpn R i j = 0 := by
  obtain ⟨hQR, -⟩ := GolubVanLoan.Chapter05.algorithm_5_2_1_spec hpn R
  change Matrix.IsQR R (GolubVanLoan.Chapter05.factoredQ (qrOut R).2 (qrOut R).1)
    (GolubVanLoan.Chapter05.upperPart (qrOut R).1) at hQR
  set Q := GolubVanLoan.Chapter05.factoredQ (qrOut R).2 (qrOut R).1 with hQ
  set U := GolubVanLoan.Chapter05.upperPart (qrOut R).1 with hU
  refine ⟨?_, ?_, fun i j hij => hQR.apply_eq_zero _ _ (by simpa using hij)⟩
  · conv_rhs => rw [← hQR.mul_eq]
    ext i j
    simp only [qrX, qrB, ← hQ, ← hU, Matrix.mul_apply, Matrix.submatrix_apply, id]
    have hzero : ∀ l ∈ (Finset.univ : Finset (Fin n)),
        l ∉ (Finset.univ : Finset (Fin p)).map (Fin.castLEEmb hpn) → Q i l * U l j = 0 := by
      intro l _ hl
      have hlp : p ≤ (l : ℕ) := by
        by_contra hcon
        exact hl (Finset.mem_map.2 ⟨⟨l, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      rw [hQR.apply_eq_zero l j (by omega), mul_zero]
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero, Finset.sum_map]
    rfl
  · have hQQ : Qᵀ * Q = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff' (A := Q)).1 hQR.mem_unitaryGroup
      simpa [Matrix.star_eq_conjTranspose] using h
    simp only [qrX, ← hQ]
    rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      hQQ]
    exact Matrix.submatrix_one_embedding (Fin.castLEEmb hpn)

/-- The invariant of block Lanczos after `t` passes. -/
private structure BLInv (A : Matrix (Fin n) (Fin n) ℝ) (X₁ : Matrix (Fin n) (Fin p) ℝ) (t : ℕ)
    (s : BlockLanczosState n p) : Prop where
  X_zero : s.X 0 = X₁
  M_eq : ∀ b ≤ t, s.M b = (s.X b)ᵀ * (A * s.X b)
  qr : ∀ b < t, s.X (b + 1) * s.B b = blockResidual A s b
  orth : ∀ b < t, (s.X (b + 1))ᵀ * s.X (b + 1) = 1
  tri : ∀ b < t, ∀ i j : Fin p, j < i → s.B b i j = 0

/-- A pass leaves the earlier residual blocks unchanged. -/
private theorem blockResidual_update (A : Matrix (Fin n) (Fin n) ℝ) (s : BlockLanczosState n p)
    {t b : ℕ} (hb : b ≤ t) (Xn : Matrix (Fin n) (Fin p) ℝ) (Mn Bn : Matrix (Fin p) (Fin p) ℝ) :
    blockResidual A
      { X := Function.update s.X (t + 1) Xn
        M := Function.update s.M (t + 1) Mn
        B := Function.update s.B t Bn } b = blockResidual A s b := by
  unfold blockResidual
  simp only
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  split_ifs with hb0
  · rfl
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

private theorem blInv_step (hpn : p ≤ n) {A : Matrix (Fin n) (Fin n) ℝ}
    {X₁ : Matrix (Fin n) (Fin p) ℝ} {t : ℕ} {s : BlockLanczosState n p} (h : BLInv A X₁ t s) :
    BLInv A X₁ (t + 1) (Id.run (blockLanczosStep pure hpn A s t)) := by
  rw [blockLanczosStep_exact]
  obtain ⟨hXB, hXX, hB⟩ := qr_facts hpn (blockResidual A s t)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only
    rw [Function.update_of_ne (by omega)]
    exact h.X_zero
  · intro b hb
    simp only
    rcases Nat.le_succ_iff.1 hb with hb | rfl
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.M_eq b hb
    · rw [Function.update_self, Function.update_self]
  · intro b hb
    rw [blockResidual_update A s (by omega)]
    simp only
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.qr b hb
    · rw [Function.update_self, Function.update_self]
      exact hXB
  · intro b hb
    simp only
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
    · rw [Function.update_of_ne (by omega)]
      exact h.orth b hb
    · rw [Function.update_self]
      exact hXX
  · intro b hb i j hij
    simp only
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
    · rw [Function.update_of_ne (by omega)]
      exact h.tri b hb i j hij
    · rw [Function.update_self]
      exact hB i j hij

/-- The invariant holds after the whole run. -/
private theorem blInv_run (hpn : p ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (X₁ : Matrix (Fin n) (Fin p) ℝ) (r : ℕ) :
    BLInv A X₁ (r - 1) (Id.run (blockLanczos pure hpn A X₁ r)) := by
  set init : BlockLanczosState n p :=
    { X := Function.update 0 0 X₁, M := Function.update 0 0 (X₁ᵀ * (A * X₁)), B := 0 }
  have hprog : Id.run (blockLanczos pure hpn A X₁ r) =
      (List.range (r - 1)).foldl (fun s k => Id.run (blockLanczosStep pure hpn A s k)) init := by
    simp only [blockLanczos, Id.run_bind, algorithm_1_1_5_spec, zero_add, List.idRun_foldlM]
    rfl
  have h0 : BLInv A X₁ 0 init := by
    refine ⟨by simp [init], fun b hb => ?_, fun b hb => absurd hb (Nat.not_lt_zero _),
      fun b hb => absurd hb (Nat.not_lt_zero _), fun b hb => absurd hb (Nat.not_lt_zero _)⟩
    obtain rfl : b = 0 := by omega
    simp [init]
  have hall : ∀ t, BLInv A X₁ t ((List.range t).foldl
      (fun s k => Id.run (blockLanczosStep pure hpn A s k)) init) := by
    intro t
    induction t with
    | zero => simpa using h0
    | succ t ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact blInv_step hpn ih
  rw [hprog]
  exact hall (r - 1)

/-- `A [X_1 | ⋯ | X_k]`, column block `b`. -/
private theorem mul_blockCols_apply (A : Matrix (Fin n) (Fin n) ℝ)
    (X : ℕ → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (i : Fin n) (b : Fin k) (l : Fin p) :
    (A * blockCols X k) i (b, l) = (A * X b) i l := by
  simp [Matrix.mul_apply, blockCols]

/-- `R [0 | ⋯ | 0 | I_p]`, column block `b`. -/
private theorem mul_lastBlockSel_apply (R : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (i : Fin n)
    (b : Fin k) (l : Fin p) :
    (R * lastBlockSel p k) i (b, l) = if (b : ℕ) + 1 = k then R i l else 0 := by
  by_cases hb : (b : ℕ) + 1 = k
  · simp [Matrix.mul_apply, lastBlockSel, hb]
  · simp [Matrix.mul_apply, lastBlockSel, hb]

/-- The entries of the block tridiagonal `T̄_{k+1}` of `ℕ`-indexed blocks
(`Matrix.blockTridiagonal_apply_eq_ite` with `F = Bᵀ`). -/
private theorem blockTridiagonal_entry (Md Bd : ℕ → Matrix (Fin p) (Fin p) ℝ) (k : ℕ)
    (a c : Fin (k + 1)) (y l : Fin p) :
    Matrix.blockTridiagonal (fun j : Fin k => Bd j) (fun j : Fin (k + 1) => Md j)
        (fun j : Fin k => (Bd j)ᵀ) (a, y) (c, l) =
      if (a : ℕ) = c then Md a y l else if (a : ℕ) = c + 1 then Bd c y l
        else if (c : ℕ) = a + 1 then Bd a l y else 0 :=
  Matrix.blockTridiagonal_apply_eq_ite Bd Md (fun j => (Bd j)ᵀ) a c y l

/-- `[X_1 | ⋯ | X_{k+1}] T̄_{k+1}`, column block `b`. -/
private theorem blockCols_mul_blockTridiagonal_apply (X : ℕ → Matrix (Fin n) (Fin p) ℝ)
    (Md Bd : ℕ → Matrix (Fin p) (Fin p) ℝ) (k : ℕ) (i : Fin n) (b : Fin (k + 1)) (l : Fin p) :
    (blockCols X (k + 1) * Matrix.blockTridiagonal (fun j : Fin k => Bd j)
        (fun j : Fin (k + 1) => Md j) (fun j : Fin k => (Bd j)ᵀ)) i (b, l) =
      (X b * Md b) i l + (if (b : ℕ) + 1 < k + 1 then (X (b + 1) * Bd b) i l else 0) +
        (if (b : ℕ) = 0 then 0 else (X (b - 1) * (Bd (b - 1))ᵀ) i l) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [blockCols, Matrix.of_apply, blockTridiagonal_entry]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ l', X a i l' *
    (if a = (b : ℕ) then Md a l' l else if a = (b : ℕ) + 1 then Bd b l' l
      else if (b : ℕ) = a + 1 then Bd a l l' else 0)) (k + 1)]
  have hsplit : ∀ a ∈ Finset.range (k + 1), (∑ l', X a i l' *
      (if a = (b : ℕ) then Md a l' l else if a = (b : ℕ) + 1 then Bd b l' l
        else if (b : ℕ) = a + 1 then Bd a l l' else 0)) =
      (if a = (b : ℕ) then (X b * Md b) i l else 0) +
        (if a = (b : ℕ) + 1 then (X (b + 1) * Bd b) i l else 0) +
        (if a + 1 = (b : ℕ) then (X a * (Bd a)ᵀ) i l else 0) := by
    intro a _
    by_cases h1 : a = (b : ℕ)
    · subst h1
      simp [Matrix.mul_apply]
    · by_cases h2 : a = (b : ℕ) + 1
      · have h3 : ¬(b : ℕ) + 1 + 1 = b := by omega
        subst h2
        simp [Matrix.mul_apply, h3]
      · by_cases h3 : (b : ℕ) = a + 1
        · have e : ∀ l', (if a = (b : ℕ) then Md a l' l else if a = (b : ℕ) + 1 then Bd b l' l
              else if (b : ℕ) = a + 1 then Bd a l l' else 0) = Bd a l l' := fun l' => by
            rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
          simp_rw [e]
          rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3.symm, zero_add, zero_add]
          simp [Matrix.mul_apply, Matrix.transpose_apply]
        · have e : ∀ l', (if a = (b : ℕ) then Md a l' l else if a = (b : ℕ) + 1 then Bd b l' l
              else if (b : ℕ) = a + 1 then Bd a l l' else 0) = 0 := fun l' => by
            rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
          simp_rw [e]
          rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (fun h => h3 h.symm)]
          simp
  have h3sum : ∑ a ∈ Finset.range (k + 1), (if a + 1 = (b : ℕ) then (X a * (Bd a)ᵀ) i l else 0) =
      if (b : ℕ) = 0 then 0 else (X (b - 1) * (Bd (b - 1))ᵀ) i l := by
    by_cases hb0 : (b : ℕ) = 0
    · rw [ite_eq_left hb0]
      exact Finset.sum_eq_zero fun a _ => ite_eq_right (by omega)
    · rw [ite_eq_right hb0, Finset.sum_eq_single ((b : ℕ) - 1)]
      · exact ite_eq_left (by omega)
      · intro a _ ha
        exact ite_eq_right (by omega)
      · intro ha
        exact absurd (Finset.mem_range.2 (by omega)) ha
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', h3sum]
  simp only [Finset.mem_range, b.isLt, ↓reduceIte]

/-- **(10.3.9)**: "At the beginning of the `k`th pass through the loop we have
`A [X_1 | ⋯ | X_k] = [X_1 | ⋯ | X_k] T̄_k + R_k [0 | ⋯ | 0 | I_p]`", `T̄_k` block tridiagonal with
the `M_i` on the diagonal, `B_i` below and `B_iᵀ` above (the backbone's
`Matrix.blockTridiagonal`). Stated for `k + 1` blocks, after the passes `0, …, k − 1`, in exact
arithmetic; no hypothesis on `A` or on the ranks (each pass computes an exact QR factorization). -/
theorem equation_10_3_9 (hpn : p ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (X₁ : Matrix (Fin n) (Fin p) ℝ) (r : ℕ) {k : ℕ} (hkr : k + 1 ≤ r) :
    let s := Id.run (blockLanczos pure hpn A X₁ r)
    A * blockCols s.X (k + 1) =
      blockCols s.X (k + 1) * Matrix.blockTridiagonal (fun j : Fin k => s.B j)
          (fun j : Fin (k + 1) => s.M j) (fun j : Fin k => (s.B j)ᵀ) +
        blockResidual A s k * lastBlockSel p (k + 1) := by
  intro s
  have h := blInv_run hpn A X₁ r
  ext i ⟨b, l⟩
  rw [mul_blockCols_apply, Matrix.add_apply, blockCols_mul_blockTridiagonal_apply,
    mul_lastBlockSel_apply]
  by_cases hb : (b : ℕ) + 1 < k + 1
  · rw [ite_eq_left hb, ite_eq_right (show ¬(b : ℕ) + 1 = k + 1 by omega), add_zero,
      h.qr b (by omega)]
    simp only [blockResidual, Matrix.sub_apply]
    split_ifs <;> (try simp only [Matrix.zero_apply]) <;> ring
  · have hbk : (b : ℕ) + 1 = k + 1 := by omega
    have hkb : k = (b : ℕ) := by omega
    rw [ite_eq_right hb, ite_eq_left hbk, add_zero, congrArg (blockResidual A s) hkb]
    simp only [blockResidual, Matrix.sub_apply]
    split_ifs <;> (try simp only [Matrix.zero_apply]) <;> ring

/-- The three-term block recurrence `A X_a = X_{a+1} B_a + X_a M_a + X_{a-1} B_{a-1}ᵀ`, for the
passes the run has made. -/
private theorem mul_X_eq {A : Matrix (Fin n) (Fin n) ℝ} {X₁ : Matrix (Fin n) (Fin p) ℝ} {r : ℕ}
    {s : BlockLanczosState n p} (h : BLInv A X₁ (r - 1) s) {a : ℕ} (ha : a < r - 1) :
    A * s.X a = s.X (a + 1) * s.B a + s.X a * s.M a +
      (if a = 0 then 0 else s.X (a - 1) * (s.B (a - 1))ᵀ) := by
  rw [h.qr a ha, blockResidual]
  abel

/-- `X_aᵀ R_d = 0` for `a ≤ d`, once the blocks up to `X_d` are mutually orthogonal (the argument
of Theorem 10.1.1, blockwise). -/
private theorem transpose_mul_blockResidual {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {X₁ : Matrix (Fin n) (Fin p) ℝ} {r : ℕ} {s : BlockLanczosState n p}
    (h : BLInv A X₁ (r - 1) s) {d : ℕ} (hd : d < r)
    (hXX : ∀ c ≤ d, (s.X c)ᵀ * s.X c = 1)
    (hP : ∀ c ≤ d, ∀ a < c, (s.X a)ᵀ * s.X c = 0) {a : ℕ} (ha : a ≤ d) :
    (s.X a)ᵀ * blockResidual A s d = 0 := by
  have hRd : (s.X a)ᵀ * blockResidual A s d = (s.X a)ᵀ * (A * s.X d) -
      (s.X a)ᵀ * s.X d * s.M d -
      (if d = 0 then 0 else (s.X a)ᵀ * s.X (d - 1) * (s.B (d - 1))ᵀ) := by
    unfold blockResidual
    split_ifs <;> simp [Matrix.mul_sub, Matrix.mul_assoc]
  rw [hRd]
  rcases Nat.lt_or_eq_of_le ha with ha | rfl
  · have hsymm : (s.X a)ᵀ * (A * s.X d) = (A * s.X a)ᵀ * s.X d := by
      rw [Matrix.transpose_mul, hA.eq, Matrix.mul_assoc]
    have hAXd : (A * s.X a)ᵀ * s.X d = (s.B a)ᵀ * ((s.X (a + 1))ᵀ * s.X d) := by
      rw [mul_X_eq h (by omega)]
      rcases Nat.eq_zero_or_pos a with rfl | ha0
      · simp [Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul, Matrix.mul_assoc,
          hP d le_rfl 0 ha]
      · have h1 := hP d le_rfl a ha
        have h2 := hP d le_rfl (a - 1) (by omega)
        rw [ite_eq_right (by omega : ¬a = 0)]
        simp [Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul, Matrix.mul_assoc,
          h1, h2]
    rw [hsymm, hAXd, hP d le_rfl a ha, Matrix.zero_mul, sub_zero]
    rcases Nat.lt_or_eq_of_le (show a + 1 ≤ d by omega) with h1 | h1
    · rw [hP d le_rfl (a + 1) h1, Matrix.mul_zero, ite_eq_right (by omega),
        hP (d - 1) (by omega) a (by omega), Matrix.zero_mul, sub_zero]
    · subst h1
      rw [hXX (a + 1) le_rfl, Matrix.mul_one, ite_eq_right (by omega), Nat.add_sub_cancel,
        hXX a (by omega), Matrix.one_mul, sub_self]
  · have hM := h.M_eq a (by omega)
    rw [← hM, hXX a le_rfl, Matrix.one_mul, sub_self, zero_sub]
    split_ifs with ha0
    · simp
    · have h0 : (s.X a)ᵀ * s.X (a - 1) = 0 := by
        rw [← Matrix.transpose_transpose ((s.X a)ᵀ * s.X (a - 1)), Matrix.transpose_mul,
          Matrix.transpose_transpose, hP a le_rfl (a - 1) (by omega), Matrix.transpose_zero]
      rw [h0, Matrix.zero_mul, neg_zero]

/-- The blocks of a run without rank deficiency are mutually orthogonal. -/
private theorem blockLanczos_orth {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {X₁ : Matrix (Fin n) (Fin p) ℝ} {r t : ℕ} (htr : t ≤ r) {s : BlockLanczosState n p}
    (h : BLInv A X₁ (r - 1) s) (hXX : ∀ c < t, (s.X c)ᵀ * s.X c = 1)
    (hunit : ∀ b, b + 1 < t → IsUnit (s.B b)) :
    ∀ c < t, ∀ c' ≤ c, ∀ a < c', (s.X a)ᵀ * s.X c' = 0 := by
  intro c
  induction c with
  | zero => intro _ c' hc' a ha; omega
  | succ c ih =>
    intro hc c' hc' a ha
    rcases Nat.le_succ_iff.1 hc' with hc' | rfl
    · exact ih (by omega) c' hc' a ha
    · have hZ := transpose_mul_blockResidual hA h (d := c) (by omega)
        (fun c' hc' => hXX c' (by omega)) (ih (by omega)) (a := a) (by omega)
      rw [← h.qr c (by omega), ← Matrix.mul_assoc] at hZ
      exact (hunit c (by omega)).mul_left_eq_zero.1 hZ

/-- The column `l` of a block, as a vector of `EuclideanSpace`. -/
private def colE (Y : Matrix (Fin n) (Fin p) ℝ) (l : Fin p) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => Y i l

private theorem colE_mul (Y : Matrix (Fin n) (Fin p) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (l : Fin p) : colE (Y * C) l = ∑ m, C m l • colE Y m := by
  ext i
  simp [colE, Matrix.mul_apply, mul_comm]

private theorem colE_sub (Y Z : Matrix (Fin n) (Fin p) ℝ) (l : Fin p) :
    colE (Y - Z) l = colE Y l - colE Z l := by
  ext i
  simp [colE]

private theorem colE_mul_left (A : Matrix (Fin n) (Fin n) ℝ) (Y : Matrix (Fin n) (Fin p) ℝ)
    (l : Fin p) : colE (A * Y) l = Matrix.toEuclideanLin A (colE Y l) := by
  ext i
  simp [colE, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- The basis part of (10.3.8), for any number of blocks. -/
private theorem blockLanczos_basis (hpn : p ≤ n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) {X₁ : Matrix (Fin n) (Fin p) ℝ} (hX₁ : X₁ᵀ * X₁ = 1) {r t : ℕ} (htr : t ≤ r)
    (hrank : ∀ b, b + 1 < t →
      LinearIndependent ℝ (blockResidual A (Id.run (blockLanczos pure hpn A X₁ r)) b)ᵀ) :
    let s := Id.run (blockLanczos pure hpn A X₁ r)
    (blockCols s.X t)ᵀ * blockCols s.X t = 1 ∧
      (∀ b < t, s.M b = (s.X b)ᵀ * A * s.X b) ∧
      (∀ b, b + 1 < t → ∀ i j : Fin p, j < i → s.B b i j = 0) ∧
      (0 < t → (blockCols s.X t)ᵀ * blockResidual A s (t - 1) = 0) ∧
      LinearMap.range (Matrix.toEuclideanLin (blockCols s.X t)) =
        Krylov.blockSubspace (Matrix.toEuclideanLin A) (fun l => WithLp.toLp 2 fun i => X₁ i l)
          t := by
  intro s
  have h := blInv_run hpn A X₁ r
  change BLInv A X₁ (r - 1) s at h
  have hXX : ∀ c < t, (s.X c)ᵀ * s.X c = 1 := by
    intro c hc
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · rw [h.X_zero]; exact hX₁
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      exact h.orth c' (by omega)
  have hunit : ∀ b, b + 1 < t → IsUnit (s.B b) := by
    intro b hb
    refine Matrix.mulVec_injective_iff_isUnit.1 fun y z hyz => ?_
    have hR : Function.Injective (blockResidual A s b).mulVec :=
      Matrix.mulVec_injective_iff.2 (hrank b hb)
    refine hR ?_
    rw [← h.qr b (by omega), ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact congrArg _ hyz
  have hP := blockLanczos_orth hA htr h hXX hunit
  -- orthonormality of the columns
  have hQQ : (blockCols s.X t)ᵀ * blockCols s.X t = 1 := by
    ext ⟨a, l⟩ ⟨c, l'⟩
    have he : ((blockCols s.X t)ᵀ * blockCols s.X t) (a, l) (c, l') =
        ((s.X a)ᵀ * s.X c) l l' := by
      simp [Matrix.mul_apply, blockCols]
    rw [he, Matrix.one_apply]
    rcases lt_trichotomy (a : ℕ) c with h1 | h1 | h1
    · rw [hP c c.isLt c le_rfl a h1]
      simp [Prod.ext_iff, Fin.ne_of_lt (Fin.lt_def.2 h1)]
    · obtain rfl : a = c := Fin.ext h1
      rw [hXX a a.isLt, Matrix.one_apply]
      simp [Prod.ext_iff]
    · rw [← Matrix.transpose_transpose ((s.X a)ᵀ * s.X c), Matrix.transpose_mul,
        Matrix.transpose_transpose, hP a a.isLt a le_rfl c h1]
      simp [Prod.ext_iff, (Fin.ne_of_lt (Fin.lt_def.2 h1)).symm]
  -- the residual block is orthogonal to the basis
  have hZ : 0 < t → (blockCols s.X t)ᵀ * blockResidual A s (t - 1) = 0 := by
    intro ht0
    ext ⟨a, l⟩ j
    have he : ((blockCols s.X t)ᵀ * blockResidual A s (t - 1)) (a, l) j =
        ((s.X a)ᵀ * blockResidual A s (t - 1)) l j := by
      simp [Matrix.mul_apply, blockCols]
    rw [he, transpose_mul_blockResidual hA h (d := t - 1) (by omega)
      (fun c hc => hXX c (by omega)) (fun c hc => hP (t - 1) (by omega) c hc) (a := a)
      (by omega)]
    rfl
  refine ⟨hQQ, fun b hb => ?_, fun b hb => h.tri b (by omega), ?_, ?_⟩
  · rw [h.M_eq b (by omega), Matrix.mul_assoc]
  · exact hZ
  · set T := Matrix.toEuclideanLin A with hT
    set v : Fin p → EuclideanSpace ℝ (Fin n) := fun l => WithLp.toLp 2 fun i => X₁ i l with hv
    have hmem : ∀ a < t, ∀ l, colE (s.X a) l ∈ Krylov.blockSubspace T v (a + 1) := by
      intro a
      induction a using Nat.strong_induction_on with
      | _ a ih =>
        intro ha l
        rcases Nat.eq_zero_or_pos a with rfl | ha0
        · rw [h.X_zero]
          exact Krylov.subspace_le_blockSubspace T v l 1
            (Krylov.self_mem_subspace (A := T) (v := v l) one_pos)
        · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          have hdet : IsUnit (s.B a').det :=
            (Matrix.isUnit_iff_isUnit_det _).1 (hunit a' (by omega))
          have hX : s.X (a' + 1) = blockResidual A s a' * (s.B a')⁻¹ := by
            rw [← h.qr a' (by omega), Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
          rw [hX, colE_mul]
          refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
          have hK : ∀ c ≤ a', ∀ l, colE (s.X c) l ∈ Krylov.blockSubspace T v (a' + 1 + 1) :=
            fun c hc l => Krylov.blockSubspace_mono T v (by omega) (ih c (by omega) (by omega) l)
          have hAX : colE (A * s.X a') m ∈ Krylov.blockSubspace T v (a' + 1 + 1) := by
            rw [colE_mul_left]
            exact Krylov.map_blockSubspace_le T v (a' + 1)
              (Submodule.mem_map_of_mem (ih a' (by omega) (by omega) m))
          have hXM : ∀ c ≤ a', ∀ C : Matrix (Fin p) (Fin p) ℝ,
              colE (s.X c * C) m ∈ Krylov.blockSubspace T v (a' + 1 + 1) := by
            intro c hc C
            rw [colE_mul]
            exact Submodule.sum_mem _ fun m' _ => Submodule.smul_mem _ _ (hK c hc m')
          unfold blockResidual
          split_ifs with ha'0
          · rw [sub_zero, colE_sub]
            exact Submodule.sub_mem _ hAX (hXM a' le_rfl _)
          · rw [colE_sub, colE_sub]
            exact Submodule.sub_mem _ (Submodule.sub_mem _ hAX (hXM a' le_rfl _))
              (hXM (a' - 1) (by omega) _)
    have hle : LinearMap.range (Matrix.toEuclideanLin (blockCols s.X t)) ≤
        Krylov.blockSubspace T v t := by
      rintro _ ⟨x, rfl⟩
      have hx : Matrix.toEuclideanLin (blockCols s.X t) x =
          ∑ al : Fin t × Fin p, x al • colE (s.X al.1) al.2 := by
        ext i
        simp [colE, blockCols, Matrix.mulVec, dotProduct, mul_comm]
      rw [hx]
      exact Submodule.sum_mem _ fun al _ => Submodule.smul_mem _ _
        (Krylov.blockSubspace_mono T v (show (al.1 : ℕ) + 1 ≤ t by omega)
          (hmem al.1 al.1.isLt al.2))
    have hinj : Function.Injective (Matrix.toEuclideanLin (blockCols s.X t)) := by
      intro x y hxy
      have h1 : blockCols s.X t *ᵥ x.ofLp = blockCols s.X t *ᵥ y.ofLp := congrArg WithLp.ofLp hxy
      have h2 := congrArg (fun z => (blockCols s.X t)ᵀ *ᵥ z) h1
      simp only [Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec] at h2
      ext i
      exact congrFun h2 i
    have hrange : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin (blockCols s.X t))) =
        t * p := by
      rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin]
    have hK : Module.finrank ℝ (Krylov.blockSubspace T v t) ≤ t * p := by
      rw [Krylov.blockSubspace_eq_span]
      have := finrank_range_le_card (R := ℝ) (fun q : Fin t × Fin p => (T ^ (q.1 : ℕ)) (v q.2))
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
      exact this
    exact Submodule.eq_of_le_of_finrank_le hle (hK.trans hrange.ge)

/-- **Exact semantics of (10.3.8)** ("we can show that the `X_k` are mutually orthogonal provided
none of the `R_k` is rank-deficient"): for symmetric `A` and `X₁ᵀ X₁ = I`, if `R_1, …, R_k` have
full column rank, then `[X_1 | ⋯ | X_{k+1}]` has orthonormal columns, `M_b = X_bᵀ A X_b`, every
`B_b` is upper triangular, `[X_1 | ⋯ | X_{k+1}]ᵀ A [X_1 | ⋯ | X_{k+1}] = T̄_{k+1}` (10.3.7), and the
columns span the block Krylov subspace `𝒦_{k+1}(A, X₁)`. -/
theorem equation_10_3_8 (hpn : p ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {X₁ : Matrix (Fin n) (Fin p) ℝ} (hX₁ : X₁ᵀ * X₁ = 1) {r k : ℕ} (hkr : k + 1 ≤ r)
    (hrank : ∀ b < k,
      LinearIndependent ℝ (blockResidual A (Id.run (blockLanczos pure hpn A X₁ r)) b)ᵀ) :
    let s := Id.run (blockLanczos pure hpn A X₁ r)
    (blockCols s.X (k + 1))ᵀ * blockCols s.X (k + 1) = 1 ∧
      (∀ b ≤ k, s.M b = (s.X b)ᵀ * A * s.X b) ∧
      (∀ b < k, ∀ i j : Fin p, j < i → s.B b i j = 0) ∧
      (blockCols s.X (k + 1))ᵀ * A * blockCols s.X (k + 1) =
        Matrix.blockTridiagonal (fun j : Fin k => s.B j) (fun j : Fin (k + 1) => s.M j)
          (fun j : Fin k => (s.B j)ᵀ) ∧
      LinearMap.range (Matrix.toEuclideanLin (blockCols s.X (k + 1))) =
        Krylov.blockSubspace (Matrix.toEuclideanLin A) (fun l => WithLp.toLp 2 fun i => X₁ i l)
          (k + 1) := by
  intro s
  obtain ⟨hQQ, hM, hB, hZ, hR⟩ :=
    blockLanczos_basis hpn hA hX₁ hkr (fun b hb => hrank b (by omega))
  refine ⟨hQQ, fun b hb => hM b (by omega), fun b hb => hB b (by omega), ?_, hR⟩
  have hZ' := hZ k.succ_pos
  rw [Nat.add_sub_cancel] at hZ'
  have h9 := equation_10_3_9 hpn A X₁ r hkr
  simp only at h9
  rw [Matrix.mul_assoc, h9, Matrix.mul_add, ← Matrix.mul_assoc, hQQ, Matrix.one_mul,
    ← Matrix.mul_assoc, hZ', Matrix.zero_mul, add_zero]

/-- For symmetric `A`, the `T̄_{k+1}` of a run is symmetric: its diagonal blocks
`M_b = X_bᵀ A X_b` are. -/
theorem blockLanczos_blockTridiagonal_isHermitian (hpn : p ≤ n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) (X₁ : Matrix (Fin n) (Fin p) ℝ) {r k : ℕ} (hkr : k + 1 ≤ r) :
    (Matrix.blockTridiagonal (fun j : Fin k => (Id.run (blockLanczos pure hpn A X₁ r)).B j)
      (fun j : Fin (k + 1) => (Id.run (blockLanczos pure hpn A X₁ r)).M j)
      (fun j : Fin k => ((Id.run (blockLanczos pure hpn A X₁ r)).B j)ᵀ)).IsHermitian := by
  have h := blInv_run hpn A X₁ r
  set s := Id.run (blockLanczos pure hpn A X₁ r)
  have hM : ∀ b < k + 1, ∀ l l', s.M b l' l = s.M b l l' := by
    intro b hb l l'
    have h1 := h.M_eq b (by omega)
    have h2 : (s.M b)ᵀ = s.M b := by
      rw [h1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq,
        Matrix.mul_assoc]
    exact congrFun (congrFun h2 l) l'
  refine Matrix.IsHermitian.ext fun al cl => ?_
  obtain ⟨a, l⟩ := al
  obtain ⟨c, l'⟩ := cl
  simp only [blockTridiagonal_entry, star_trivial]
  by_cases h1 : (c : ℕ) = a
  · rw [ite_eq_left h1, ite_eq_left h1.symm, h1]
    exact hM a a.isLt l l'
  · by_cases h2 : (c : ℕ) = a + 1
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right (show ¬(a : ℕ) = c by omega),
        ite_eq_right (show ¬(a : ℕ) = c + 1 by omega), ite_eq_left h2]
    · by_cases h3 : (a : ℕ) = c + 1
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3,
          ite_eq_right (show ¬(a : ℕ) = c by omega), ite_eq_left h3]
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
          ite_eq_right (show ¬(a : ℕ) = c by omega), ite_eq_right h3, ite_eq_right h2]

/-- An entry of `Mᵀ A N` as a dot product of columns. -/
private theorem transpose_mul_mul_apply {ι κ : Type*}
    (Mt : Matrix (Fin n) ι ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (N : Matrix (Fin n) κ ℝ)
    (i : ι) (j : κ) :
    (Mtᵀ * A * N) i j = (fun r => Mt r i) ⬝ᵥ (A *ᵥ fun r => N r j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The eigenvalues of `T̄_{k+1}` are those of the compression of `A` to the block Krylov subspace
`𝒦_{k+1}(A, X₁)` (of dimension `(k + 1) p`): by (10.3.8) the columns of `[X_1 | ⋯ | X_{k+1}]` are
an orthonormal basis of `𝒦_{k+1}(A, X₁)` in which the compression has the matrix `T̄_{k+1}`. -/
private theorem eigenvalues₀_blockTridiagonal_eq (hpn : p ≤ n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) {X₁ : Matrix (Fin n) (Fin p) ℝ} (hX₁ : X₁ᵀ * X₁ = 1) {r k : ℕ}
    (hkr : k + 1 ≤ r)
    (hrank : ∀ b < k,
      LinearIndependent ℝ (blockResidual A (Id.run (blockLanczos pure hpn A X₁ r)) b)ᵀ) :
    ∃ hd : Module.finrank ℝ (Krylov.blockSubspace (Matrix.toEuclideanLin A)
        (fun l => WithLp.toLp 2 fun i => X₁ i l) (k + 1)) = (k + 1) * p,
      (blockLanczos_blockTridiagonal_isHermitian hpn hA X₁ hkr).eigenvalues₀ =
        (compression.isSymmetric (Matrix.toEuclideanLin A) _
            hA.isSymmetric_toEuclideanLin).eigenvalues hd ∘
          Fin.cast (by rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]) := by
  set s := Id.run (blockLanczos pure hpn A X₁ r) with hs
  set T := Matrix.toEuclideanLin A with hTdef
  have hT : T.IsSymmetric := hA.isSymmetric_toEuclideanLin
  obtain ⟨hQQ, -, -, hcomp, hrange⟩ := equation_10_3_8 hpn hA hX₁ hkr hrank
  change (blockCols s.X (k + 1))ᵀ * blockCols s.X (k + 1) = 1 at hQQ
  change (blockCols s.X (k + 1))ᵀ * A * blockCols s.X (k + 1) =
    Matrix.blockTridiagonal (fun j : Fin k => s.B j)
      (fun j : Fin (k + 1) => s.M j) (fun j : Fin k => (s.B j)ᵀ) at hcomp
  set v : Fin p → EuclideanSpace ℝ (Fin n) := fun l => WithLp.toLp 2 fun r => X₁ r l with hv
  set K := Krylov.blockSubspace T v (k + 1) with hK
  change LinearMap.range (Matrix.toEuclideanLin (blockCols s.X (k + 1))) = K at hrange
  -- the dimension of the block Krylov subspace
  have hinj : Function.Injective (Matrix.toEuclideanLin (blockCols s.X (k + 1))) := by
    intro x y hxy
    have h1 : blockCols s.X (k + 1) *ᵥ x.ofLp = blockCols s.X (k + 1) *ᵥ y.ofLp :=
      congrArg WithLp.ofLp hxy
    have h2 := congrArg (fun w => (blockCols s.X (k + 1))ᵀ *ᵥ w) h1
    simp only [Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec] at h2
    ext j
    exact congrFun h2 j
  have hd : Module.finrank ℝ K = (k + 1) * p := by
    rw [← hrange, LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
  refine ⟨hd, ?_⟩
  -- an orthonormal basis of `K` from the columns of `[X_1 | ⋯ | X_k]`
  have hcolmem : ∀ al : Fin (k + 1) × Fin p, colE (s.X al.1) al.2 ∈ K := by
    intro al
    rw [← hrange]
    refine ⟨EuclideanSpace.single al 1, ?_⟩
    ext j
    simp [colE, blockCols, Matrix.mulVec, dotProduct, Pi.single_apply]
  set u : Fin (k + 1) × Fin p → K := fun al => ⟨colE (s.X al.1) al.2, hcolmem al⟩ with hu
  have hinner : ∀ al bl : Fin (k + 1) × Fin p,
      inner ℝ (colE (s.X al.1) al.2) (colE (s.X bl.1) bl.2) =
        ((blockCols s.X (k + 1))ᵀ * blockCols s.X (k + 1)) al bl := by
    intro al bl
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    simp [colE, blockCols, Matrix.mul_apply, dotProduct]
  have hon : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro al bl
    rw [Submodule.coe_inner]
    simp only [hu]
    rw [hinner, hQQ, Matrix.one_apply]
  have hsp : Submodule.span ℝ (Set.range u) = ⊤ :=
    hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by
      rw [hd, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin])
  set b := OrthonormalBasis.mk hon hsp.ge with hb
  have htoM : LinearMap.toMatrix b.toBasis b.toBasis (compression T K) =
      Matrix.blockTridiagonal (fun j : Fin k => s.B j)
      (fun j : Fin (k + 1) => s.M j) (fun j : Fin k => (s.B j)ᵀ) := by
    ext al bl
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, hb,
      OrthonormalBasis.coe_mk]
    simp only [compression, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      ContinuousLinearMap.coe_coe]
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, ← hcomp,
      transpose_mul_mul_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct_comm]
    rfl
  have hcard : Fintype.card (Fin (k + 1) × Fin p) = (k + 1) * p := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hchar : (compression T K).charpoly =
      (Matrix.blockTridiagonal (fun j : Fin k => s.B j)
    (fun j : Fin (k + 1) => s.M j) (fun j : Fin k => (s.B j)ᵀ)).charpoly.map
        (algebraMap ℝ ℝ) := by
    rw [← LinearMap.charpoly_toMatrix _ b.toBasis, htoM, Algebra.algebraMap_self,
      Polynomial.map_id]
  have hcast : List.ofFn ((compression.isSymmetric T K hT).eigenvalues hd ∘ Fin.cast hcard) =
      List.ofFn ((compression.isSymmetric T K hT).eigenvalues hd) :=
    (List.ofFn_congr hcard.symm ((compression.isSymmetric T K hT).eigenvalues hd)).symm
  rw [← List.ofFn_inj, ← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀, hcast,
    ← LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues, hchar,
    (blockLanczos_blockTridiagonal_isHermitian hpn hA X₁ hkr).splits_charpoly.roots_map,
    Multiset.map_map]
  congr 2

/-- The angle hypothesis of Theorem 10.3.2: if `cos φ_p = σ_min(Z₁ᵀ X₁) > 0` for the first `p`
columns `Z₁` of an orthogonal `Z` and `X₁ᵀ X₁ = I`, every `x ∈ ran X₁` satisfies
`‖x − P x‖ ≤ tan φ_p ‖P x‖`, `P` the projection onto `span {z_1, …, z_p}`: Bessel's inequality and
`σ_min ‖y‖ ≤ ‖Z₁ᵀ X₁ y‖` give `cos φ_p ‖x‖ ≤ ‖P x‖`, and Pythagoras does the rest. -/
private theorem norm_sub_starProjection_le_tan [Nonempty (Fin p)] (hpn : p ≤ n)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    {X₁ : Matrix (Fin n) (Fin p) ℝ} (hX₁ : X₁ᵀ * X₁ = 1)
    (hc : 0 < ⨅ j, ((Z.submatrix id (Fin.castLE hpn))ᵀ * X₁).colSingularValues j) :
    ∀ x ∈ Submodule.span ℝ
        (Set.range fun l => (WithLp.toLp 2 fun r => X₁ r l : EuclideanSpace ℝ (Fin n))),
      ‖x - (Submodule.span ℝ (schurBasis hZ '' {j | (j : ℕ) < p})).starProjection x‖ ≤
        Real.tan (Real.arccos
            (⨅ j, ((Z.submatrix id (Fin.castLE hpn))ᵀ * X₁).colSingularValues j)) *
          ‖(Submodule.span ℝ (schurBasis hZ '' {j | (j : ℕ) < p})).starProjection x‖ := by
  set z := schurBasis hZ with hzdef
  set Z₁ := Z.submatrix id (Fin.castLE hpn) with hZ₁
  set c := ⨅ j, (Z₁ᵀ * X₁).colSingularValues j with hcdef
  set Pz := Submodule.span ℝ (z '' {j | (j : ℕ) < p}) with hPz
  intro x hx
  obtain ⟨y, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
  set x := ∑ l, y l • (WithLp.toLp 2 fun r => X₁ r l : EuclideanSpace ℝ (Fin n)) with hxdef
  have hxX : x.ofLp = X₁ *ᵥ y := by
    ext j
    simp [hxdef, Matrix.mulVec, dotProduct, mul_comm]
  have hnx : ‖x‖ = ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin p))‖ := by
    have h1 : ‖x‖ ^ 2 = ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin p))‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
        star_trivial, star_trivial, hxX, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        Matrix.mulVec_mulVec, hX₁, Matrix.one_mulVec]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
  -- `‖Z₁ᵀ X₁ y‖ ≤ ‖P x‖` (Bessel)
  have hZx : ‖Matrix.toEuclideanLin (Z₁ᵀ * X₁) (WithLp.toLp 2 y)‖ ≤ ‖Pz.starProjection x‖ := by
    have hzon : Orthonormal ℝ fun j : Fin p => z (Fin.castLE hpn j) :=
      z.orthonormal.comp _ (Fin.castLE_injective hpn)
    have hbes := hzon.sum_inner_products_le (x := Pz.starProjection x) (s := Finset.univ)
    have hcoord : ∀ j : Fin p, (Matrix.toEuclideanLin (Z₁ᵀ * X₁) (WithLp.toLp 2 y)) j =
        inner ℝ (z (Fin.castLE hpn j)) (Pz.starProjection x) := by
      intro j
      have hperp : inner ℝ (z (Fin.castLE hpn j)) (x - Pz.starProjection x) = 0 :=
        Submodule.inner_right_of_mem_orthogonal
          (Submodule.subset_span (Set.mem_image_of_mem _
            (show ((Fin.castLE hpn j : Fin n) : ℕ) < p from j.isLt)))
          (Submodule.sub_starProjection_mem_orthogonal x)
      rw [inner_sub_right, sub_eq_zero] at hperp
      rw [← hperp, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, hxX]
      change ((Z₁ᵀ * X₁) *ᵥ y) j = _
      rw [← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Z₁, Matrix.submatrix_apply,
        id, z, schurBasis_apply, Matrix.euclideanCol_apply]
      exact Finset.sum_congr rfl fun r _ => mul_comm _ _
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq]
    refine le_trans (le_of_eq ?_) hbes
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcoord j]
  have hlow := (Z₁ᵀ * X₁).iInf_colSingularValues_mul_norm_le (WithLp.toLp 2 y)
  rw [← hnx] at hlow
  have hcx : c * ‖x‖ ≤ ‖Pz.starProjection x‖ := hlow.trans hZx
  -- Pythagoras
  have hpy : ‖x‖ ^ 2 = ‖Pz.starProjection x‖ ^ 2 + ‖x - Pz.starProjection x‖ ^ 2 := by
    have h0 : inner ℝ (Pz.starProjection x) (x - Pz.starProjection x) = 0 :=
      Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _)
        (Submodule.sub_starProjection_mem_orthogonal x)
    have h1 := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
    rw [add_sub_cancel] at h1
    simpa [sq] using h1
  set N := ‖x‖
  set a := ‖Pz.starProjection x‖
  set e := ‖x - Pz.starProjection x‖
  have hN0 : 0 ≤ N := norm_nonneg _
  have ha0 : 0 ≤ a := norm_nonneg _
  have he0 : 0 ≤ e := norm_nonneg _
  rcases eq_or_lt_of_le hN0 with hN | hN
  · have : e ^ 2 ≤ 0 := by nlinarith
    have he : e = 0 := by nlinarith
    rw [he]
    exact mul_nonneg (by rw [Real.tan_arccos]; positivity) ha0
  have haN : a ≤ N := (pow_le_pow_iff_left₀ ha0 hN0 two_ne_zero).1 (by nlinarith)
  have hc1 : c ≤ 1 := by
    have h1 : c * N ≤ 1 * N := by linarith
    exact le_of_mul_le_mul_right h1 hN
  have hsq : e ^ 2 ≤ (Real.tan (Real.arccos c) * a) ^ 2 := by
    rw [Real.tan_arccos, mul_pow, div_pow, Real.sq_sqrt (by nlinarith),
      div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h1 : (c * N) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) hcx 2
    nlinarith
  exact (pow_le_pow_iff_left₀ he0 (mul_nonneg (by rw [Real.tan_arccos]; positivity) ha0)
    two_ne_zero).1 hsq

/-- **Theorem 10.3.2 (Underwood).** Let `A` be symmetric with Schur decomposition
`Zᵀ A Z = diag(λ_1, …, λ_n)`, `λ_1 ≥ ⋯ ≥ λ_n`, `Z = [z_1 ⋯ z_n]` orthogonal (any such
decomposition), let `μ_1 ≥ ⋯` be the eigenvalues of the matrix `T̄_{k+1}` obtained after `k + 1`
blocks of (10.3.8), `Z₁ = [z_1 ⋯ z_p]` and `0 < cos φ_p = σ_p(Z₁ᵀ X₁)` (the smallest singular
value). Then for `i = 1 : p`, `λ_i ≥ μ_i ≥ λ_i − (λ_1 − λ_n) (tan φ_p / c_k(1 + 2ρ_i))²`,
`ρ_i = (λ_i − λ_{p+1})/(λ_{p+1} − λ_n)` (the book writes `tan θ_p`; its `k` blocks and `c_{k−1}`
are our `k + 1` and `c_k`). Hypotheses: `p < n`, `X₁ᵀ X₁ = I`, no rank-deficient `R_b` (so that
the run is the block Lanczos process); no gap hypothesis (`ρ_i = 0` in the degenerate cases). The
symmetry of `A` follows from the decomposition (`isSymm_of_schur`). The eigenvalues of `T̄_{k+1}`
are those of the compression of `A` to `𝒦_{k+1}(A, X₁)` (`equation_10_3_8`), and the bound is the
backbone's `BlockLanczos.kaniel_paige_saad` for the eigenbasis `z`, with `tan φ_p` bounding the
angle between `ran X₁` and `span {z_1, …, z_p}`. -/
theorem theorem_10_3_2 (hpn : p < n) {A Z : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hZ : Z ∈ Matrix.orthogonalGroup (Fin n) ℝ) (hZA : Zᵀ * A * Z = Matrix.diagonal lam)
    (hlam : Antitone lam) {X₁ : Matrix (Fin n) (Fin p) ℝ} (hX₁ : X₁ᵀ * X₁ = 1) {r k : ℕ}
    (hkr : k + 1 ≤ r)
    (hrank : ∀ b < k,
      LinearIndependent ℝ (blockResidual A (Id.run (blockLanczos pure hpn.le A X₁ r)) b)ᵀ)
    (i : Fin p) :
    let Z₁ : Matrix (Fin n) (Fin p) ℝ := Z.submatrix id (Fin.castLE hpn.le)
    let φ := Real.arccos (⨅ j, (Z₁ᵀ * X₁).colSingularValues j)
    let μ := (blockLanczos_blockTridiagonal_isHermitian hpn.le (isSymm_of_schur hZ hZA) X₁
      hkr).eigenvalues₀
    let ρ := (lam (Fin.castLE hpn.le i) - lam ⟨p, hpn⟩) / (lam ⟨p, hpn⟩ - lam ⟨n - 1, by omega⟩)
    0 < ⨅ j, (Z₁ᵀ * X₁).colSingularValues j →
      μ ⟨i, by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
        exact lt_of_lt_of_le i.isLt (Nat.le_mul_of_pos_left p k.succ_pos)⟩ ≤
          lam (Fin.castLE hpn.le i) ∧
      lam (Fin.castLE hpn.le i) - (lam ⟨0, by omega⟩ - lam ⟨n - 1, by omega⟩) *
          (Real.tan φ / (Polynomial.Chebyshev.T ℝ k).eval (1 + 2 * ρ)) ^ 2 ≤
        μ ⟨i, by
          rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
          exact lt_of_lt_of_le i.isLt (Nat.le_mul_of_pos_left p k.succ_pos)⟩ := by
  intro Z₁ φ μ ρ hc
  set T := Matrix.toEuclideanLin A with hTdef
  have hT : T.IsSymmetric := (isSymm_of_schur hZ hZA).isSymmetric_toEuclideanLin
  have hb : ∀ j, T (schurBasis hZ j) = lam j • schurBasis hZ j := fun j => by
    rw [schurBasis_apply]; exact toEuclideanLin_euclideanCol_of_schur hZ hZA j
  set v : Fin p → EuclideanSpace ℝ (Fin n) := fun l => WithLp.toLp 2 fun r => X₁ r l with hv
  have hvon : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro l l'
    have h1 := congrFun (congrFun hX₁ l) l'
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    simpa [hv, dotProduct, Matrix.mul_apply, Matrix.one_apply] using h1
  obtain ⟨hd, hμ⟩ :=
    eigenvalues₀_blockTridiagonal_eq hpn.le (isSymm_of_schur hZ hZA) hX₁ hkr hrank
  have : Nonempty (Fin p) := ⟨i⟩
  have hkps := BlockLanczos.kaniel_paige_saad (schurBasis hZ) hb hlam hT v hvon.linearIndependent
    (norm_sub_starProjection_le_tan hpn.le hZ hX₁ hc) (k := k) hd
    ⟨i, lt_of_lt_of_le i.isLt (Nat.le_mul_of_pos_left p (Nat.succ_pos k))⟩ (Fin.castLE hpn.le i)
    ⟨p, hpn⟩ ⟨0, by omega⟩ ⟨n - 1, by omega⟩ rfl i.isLt rfl
    (fun j => Fin.le_def.2 (Nat.zero_le _)) (fun j => Fin.le_def.2 (by simp; omega))
  simp only [μ, hμ, Function.comp_apply, Fin.cast_mk]
  exact ⟨hkps.2, hkps.1⟩

end BlockLanczos

end GolubVanLoan.Chapter10
