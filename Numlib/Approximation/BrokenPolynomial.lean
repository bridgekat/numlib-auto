import Numlib.Analysis.Sobolev.Interval
import Numlib.Approximation.Spline

/-!
# Broken polynomial spaces

The **broken** (discontinuous) piecewise polynomial space of a partition `x 0 < x 1 < ⋯ < x n`: an
element is a polynomial of degree at most `r` on each panel `[x i, x (i+1)]`, with no continuity
across the nodes. It is the trial space of the discontinuous Galerkin method for the transport
equation ([quarteroni2000numerical] §13.10, `Numlib/Variational/Evolution`), and it contains the
continuous piecewise polynomials `X_h^r` of §12.4.5 as the subspace of zero interior jumps.

## Design

* `BrokenPolynomial x r` is the submodule `Submodule.pi Set.univ fun _ => degreeLT ℝ (r + 1)` of
  `Fin n → ℝ[X]`, as a type: a tuple of polynomials of degree `< r + 1`, one per panel, of dimension
  `n (r + 1)` (`finrank_eq`). The partition `x : Fin (n + 1) → ℝ` is a parameter of the type so
  that the `L²(x 0, x n)` inner product `⟪v, w⟫ = ∑ i, ∫_{x i}^{x (i+1)} v_i w_i` can be an
  instance; it is definite exactly when the partition is strictly increasing, which is why the
  inner product space instance asks for `[Fact (StrictMono x)]`. An element `v` is applied as a
  function `v : Fin n → ℝ[X]` (`BrokenPolynomial.poly`), and `BrokenPolynomial.mk` builds one from
  a tuple of polynomials with a degree bound.
* Because each piece is a polynomial, the one-sided traces `v⁺(x i) = v_i(x i)`
  (`traceRight`), `v⁻(x i) = v_{i-1}(x i)` (`traceLeft`, with the inflow convention `v⁻(x 0) = 0`)
  and the jumps `[v]_i = v⁺(x i) - v⁻(x i)` (`jump`) are evaluations, linear in `v`
  (`traceRightₗ`, `traceLeftₗ`, `jumpₗ`).
* `continuous x r` is the subspace of zero interior jumps. For a strictly increasing partition
  its elements glue to continuous functions on `[x 0, x n]` (`toContinuousMap`), and the image is
  the spline space `Spline.splineSpace (x 0) (x n) n x r 0` of `Numlib/Approximation/Spline`
  without smoothness (`toContinuousMap_range_eq_splineSpace`), so that the continuous piecewise
  polynomials have one definition, of which this module holds the per-panel representation — the
  one with traces and jumps.

## Main statements

* `integral_mul_deriv_mul_eq`, `sum_integral_mul_deriv_mul_eq`: panel integration by parts
  `∫ a v v' = ½[a v²] - ½ ∫ a' v²` and its sum over the panels in trace/jump form, the identity
  behind the energy estimate of the upwind discontinuous Galerkin method.
* `inverseInequality_linear`: the inverse inequality `‖v'‖² ≤ 12 h_min⁻² ‖v‖²` for piecewise
  linear functions, the `λ_max ≤ c h⁻²` behind the parabolic stability condition `Δt ≤ C h²` of
  the θ-method with `θ < 1/2` ([quarteroni2000numerical] §13.4.1).
* `toLpₗᵢ`: the isometric embedding of `BrokenPolynomial x r` into `L²(x 0, x n)`, the class of
  the step function `stepFun v` equal to `v_i` on the half-open panel `[x i, x (i+1))`. The
  `r = 1` image is the discontinuous piecewise linear space of
  `Numlib/Approximation/PiecewiseLinearL2`, which lives in `L²` of the subtype `Icc a b`; the
  identification of the two `L²` spaces is not made here.
-/

open Polynomial MeasureTheory intervalIntegral Set
open scoped Interval RealInnerProductSpace

noncomputable section

variable {n : ℕ}

-- the partition is a phantom parameter of the type, there for the inner product instance
set_option linter.unusedVariables false in
/-- **The broken polynomial space** of the partition `x 0 < x 1 < ⋯ < x n`: one polynomial of
degree at most `r` per panel, with no continuity across the nodes. The partition is a parameter of
the type so that the `L²(x 0, x n)` inner product can be an instance
(`BrokenPolynomial.instInnerProductSpace`). -/
def BrokenPolynomial (x : Fin (n + 1) → ℝ) (r : ℕ) : Type :=
  Submodule.pi Set.univ fun _ : Fin n => Polynomial.degreeLT ℝ (r + 1)

namespace BrokenPolynomial

variable {x : Fin (n + 1) → ℝ} {r : ℕ}

/-- The submodule of `Fin n → ℝ[X]` underlying the broken polynomial space. -/
abbrev submodule (n r : ℕ) : Submodule ℝ (Fin n → ℝ[X]) :=
  Submodule.pi Set.univ fun _ : Fin n => Polynomial.degreeLT ℝ (r + 1)

instance : AddCommGroup (BrokenPolynomial x r) := inferInstanceAs (AddCommGroup (submodule n r))

instance : Module ℝ (BrokenPolynomial x r) := inferInstanceAs (Module ℝ (submodule n r))

instance : Inhabited (BrokenPolynomial x r) := ⟨0⟩

/-- The polynomial of `v` on the panel `i`. -/
def poly (v : BrokenPolynomial x r) (i : Fin n) : ℝ[X] := (v : submodule n r).1 i

instance : CoeFun (BrokenPolynomial x r) fun _ => Fin n → ℝ[X] := ⟨poly⟩

/-- The degree bound of the polynomials of a broken polynomial. -/
theorem natDegree_le (v : BrokenPolynomial x r) (i : Fin n) : (v i).natDegree ≤ r := by
  have h : (v i).degree < r + 1 := mem_degreeLT.1 ((v : submodule n r).2 i (Set.mem_univ i))
  by_cases hv : v i = 0
  · rw [hv, natDegree_zero]; exact Nat.zero_le r
  · exact Nat.lt_succ_iff.1 ((natDegree_lt_iff_degree_lt hv).2 (by exact_mod_cast h))

@[ext]
theorem ext {v w : BrokenPolynomial x r} (h : ∀ i, v i = w i) : v = w :=
  Subtype.ext (funext h)

/-- A broken polynomial from a tuple of polynomials of degree at most `r`. -/
def mk (x : Fin (n + 1) → ℝ) (p : Fin n → ℝ[X]) (hp : ∀ i, (p i).natDegree ≤ r) :
    BrokenPolynomial x r :=
  (⟨p, fun i _ => mem_degreeLT.2 ((degree_le_of_natDegree_le (hp i)).trans_lt
    (WithBot.coe_lt_coe.2 (Nat.lt_succ_self r)))⟩ : submodule n r)

@[simp]
theorem mk_apply (p : Fin n → ℝ[X]) (hp : ∀ i, (p i).natDegree ≤ r) (i : Fin n) :
    mk x p hp i = p i := rfl

@[simp]
theorem add_apply (v w : BrokenPolynomial x r) (i : Fin n) : (v + w) i = v i + w i := rfl

@[simp]
theorem sub_apply (v w : BrokenPolynomial x r) (i : Fin n) : (v - w) i = v i - w i := rfl

@[simp]
theorem neg_apply (v : BrokenPolynomial x r) (i : Fin n) : (-v) i = -v i := rfl

@[simp]
theorem smul_apply (c : ℝ) (v : BrokenPolynomial x r) (i : Fin n) : (c • v) i = c • v i := rfl

@[simp]
theorem zero_apply (i : Fin n) : (0 : BrokenPolynomial x r) i = 0 := rfl

/-- Evaluation of the panel polynomial, as a linear map. -/
def evalₗ (x : Fin (n + 1) → ℝ) (r : ℕ) (i : Fin n) (s : ℝ) : BrokenPolynomial x r →ₗ[ℝ] ℝ where
  toFun v := (v i).eval s
  map_add' v w := by simp
  map_smul' c v := by simp

@[simp]
theorem evalₗ_apply (i : Fin n) (s : ℝ) (v : BrokenPolynomial x r) :
    evalₗ x r i s v = (v i).eval s := rfl

/-- The broken polynomial space as the product of the panel spaces `ℝ[X]_{< r + 1}`. -/
def piEquiv (x : Fin (n + 1) → ℝ) (r : ℕ) :
    BrokenPolynomial x r ≃ₗ[ℝ] (Fin n → Polynomial.degreeLT ℝ (r + 1)) where
  toFun v i := ⟨v i, (v : submodule n r).2 i (Set.mem_univ i)⟩
  invFun w := (⟨fun i => (w i : ℝ[X]), fun i _ => (w i).2⟩ : submodule n r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

instance : FiniteDimensional ℝ (Polynomial.degreeLT ℝ (r + 1)) :=
  (Polynomial.degreeLTEquiv ℝ (r + 1)).symm.finiteDimensional

instance : FiniteDimensional ℝ (BrokenPolynomial x r) :=
  (piEquiv x r).symm.finiteDimensional

/-- **The dimension** of the broken polynomial space: `n (r + 1)`. -/
theorem finrank_eq (x : Fin (n + 1) → ℝ) (r : ℕ) :
    Module.finrank ℝ (BrokenPolynomial x r) = n * (r + 1) := by
  rw [(piEquiv x r).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, (Polynomial.degreeLTEquiv ℝ (r + 1)).finrank_eq,
    Module.finrank_fin_fun]

/-! ### Traces and jumps -/

/-- **The right trace** `v⁺(x i) = v_i(x i)`: the value at the node `x i` of the polynomial of the
panel to its right. -/
def traceRight (v : BrokenPolynomial x r) (i : Fin n) : ℝ :=
  (v i).eval (x i.castSucc)

/-- **The left trace** `v⁻(x i) = v_{i-1}(x i)`: the value at the node `x i` of the polynomial of
the panel to its left, with the inflow convention `v⁻(x 0) = 0`. -/
def traceLeft (v : BrokenPolynomial x r) (i : Fin (n + 1)) : ℝ :=
  Fin.cases 0 (fun j => (v j).eval (x j.succ)) i

/-- **The jump** `[v]_i = v⁺(x i) - v⁻(x i)` at the node `x i`; at `x 0` it is `v⁺(x 0)`. -/
def jump (v : BrokenPolynomial x r) (i : Fin n) : ℝ :=
  traceRight v i - traceLeft v i.castSucc

@[simp]
theorem traceLeft_zero (v : BrokenPolynomial x r) : traceLeft v 0 = 0 := rfl

@[simp]
theorem traceLeft_succ (v : BrokenPolynomial x r) (j : Fin n) :
    traceLeft v j.succ = (v j).eval (x j.succ) := rfl

theorem traceRight_apply (v : BrokenPolynomial x r) (i : Fin n) :
    traceRight v i = (v i).eval (x i.castSucc) := rfl

theorem jump_apply (v : BrokenPolynomial x r) (i : Fin n) :
    jump v i = traceRight v i - traceLeft v i.castSucc := rfl

/-- The jump at `x 0` is the right trace. -/
theorem jump_zero (v : BrokenPolynomial x r) (hn : 0 < n) :
    jump v ⟨0, hn⟩ = traceRight v ⟨0, hn⟩ := by
  rw [jump_apply, show (⟨0, hn⟩ : Fin n).castSucc = 0 from rfl, traceLeft_zero, sub_zero]

/-- The right trace, as a linear map. -/
def traceRightₗ (x : Fin (n + 1) → ℝ) (r : ℕ) (i : Fin n) : BrokenPolynomial x r →ₗ[ℝ] ℝ :=
  evalₗ x r i (x i.castSucc)

/-- The left trace, as a linear map. -/
def traceLeftₗ (x : Fin (n + 1) → ℝ) (r : ℕ) (i : Fin (n + 1)) : BrokenPolynomial x r →ₗ[ℝ] ℝ :=
  Fin.cases 0 (fun j => evalₗ x r j (x j.succ)) i

/-- The jump, as a linear map. -/
def jumpₗ (x : Fin (n + 1) → ℝ) (r : ℕ) (i : Fin n) : BrokenPolynomial x r →ₗ[ℝ] ℝ :=
  traceRightₗ x r i - traceLeftₗ x r i.castSucc

@[simp]
theorem traceRightₗ_apply (i : Fin n) (v : BrokenPolynomial x r) :
    traceRightₗ x r i v = traceRight v i := rfl

@[simp]
theorem traceLeftₗ_apply (i : Fin (n + 1)) (v : BrokenPolynomial x r) :
    traceLeftₗ x r i v = traceLeft v i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

@[simp]
theorem jumpₗ_apply (i : Fin n) (v : BrokenPolynomial x r) : jumpₗ x r i v = jump v i := by
  simp [jumpₗ, jump]

theorem traceRight_add (v w : BrokenPolynomial x r) (i : Fin n) :
    traceRight (v + w) i = traceRight v i + traceRight w i :=
  (traceRightₗ x r i).map_add v w

theorem traceRight_smul (c : ℝ) (v : BrokenPolynomial x r) (i : Fin n) :
    traceRight (c • v) i = c * traceRight v i :=
  (traceRightₗ x r i).map_smul c v

theorem traceLeft_add (v w : BrokenPolynomial x r) (i : Fin (n + 1)) :
    traceLeft (v + w) i = traceLeft v i + traceLeft w i := by
  rw [← traceLeftₗ_apply, map_add, traceLeftₗ_apply, traceLeftₗ_apply]

theorem traceLeft_smul (c : ℝ) (v : BrokenPolynomial x r) (i : Fin (n + 1)) :
    traceLeft (c • v) i = c * traceLeft v i := by
  rw [← traceLeftₗ_apply, map_smul, traceLeftₗ_apply, smul_eq_mul]

theorem jump_add (v w : BrokenPolynomial x r) (i : Fin n) :
    jump (v + w) i = jump v i + jump w i := by
  rw [← jumpₗ_apply, map_add, jumpₗ_apply, jumpₗ_apply]

theorem jump_smul (c : ℝ) (v : BrokenPolynomial x r) (i : Fin n) :
    jump (c • v) i = c * jump v i := by
  rw [← jumpₗ_apply, map_smul, jumpₗ_apply, smul_eq_mul]

/-! ### The continuous subspace -/

/-- **The continuous piecewise polynomials** `X_h^r` inside the broken space: the broken
polynomials whose jumps at the interior nodes `x 1, …, x (n-1)` vanish. -/
def continuous (x : Fin (n + 1) → ℝ) (r : ℕ) : Submodule ℝ (BrokenPolynomial x r) where
  carrier := {v | ∀ i : Fin n, 0 < (i : ℕ) → jump v i = 0}
  add_mem' {v w} hv hw i hi := by rw [jump_add, hv i hi, hw i hi, add_zero]
  zero_mem' i _ := by rw [← jumpₗ_apply, map_zero]
  smul_mem' c {v} hv i hi := by rw [jump_smul, hv i hi, mul_zero]

/-- Membership of the continuous subspace: the jumps at the interior nodes vanish. -/
theorem mem_continuous_iff {v : BrokenPolynomial x r} :
    v ∈ continuous x r ↔ ∀ i : Fin n, 0 < (i : ℕ) → jump v i = 0 := Iff.rfl

/-- In the continuous subspace, the two panel polynomials meeting at an interior node take the same
value there. -/
theorem eval_succ_eq_of_mem_continuous {v : BrokenPolynomial x r} (hv : v ∈ continuous x r)
    (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    (v j).eval (x j.succ) = (v ⟨j + 1, hj⟩).eval (x j.succ) := by
  have h := hv ⟨j + 1, hj⟩ (Nat.succ_pos j)
  rw [jump_apply, sub_eq_zero, traceRight_apply] at h
  rw [show (⟨(j : ℕ) + 1, hj⟩ : Fin n).castSucc = j.succ from rfl, traceLeft_succ] at h
  exact h.symm

/-! ### The `L²` inner product -/

/-- **The `L²(x 0, x n)` inner product** of two broken polynomials:
`∑ i, ∫_{x i}^{x (i+1)} v_i w_i`. It is definite when the partition is strictly increasing. -/
instance : Inner ℝ (BrokenPolynomial x r) :=
  ⟨fun v w => ∑ i, ∫ s in x i.castSucc..x i.succ, (v i).eval s * (w i).eval s⟩

/-- The inner product is the sum of the panel integrals of `v_i w_i`. -/
theorem inner_def (v w : BrokenPolynomial x r) :
    ⟪v, w⟫ = ∑ i, ∫ s in x i.castSucc..x i.succ, (v i).eval s * (w i).eval s := rfl

/-- A polynomial whose square integrates to zero over a nondegenerate interval is zero. -/
private theorem eq_zero_of_integral_sq_eq_zero {u v : ℝ} (huv : u < v) {p : ℝ[X]}
    (h : ∫ s in u..v, p.eval s * p.eval s = 0) : p = 0 := by
  by_contra hp
  -- a nonzero polynomial does not vanish on the whole interval
  have hroot : ∃ c ∈ Icc u v, p.eval c ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hp (p.eq_zero_of_infinite_isRoot ((Icc_infinite huv).mono fun c hc => hall c hc))
  obtain ⟨c, hc, hc0⟩ := hroot
  have hpos : 0 < ∫ s in u..v, p.eval s * p.eval s :=
    integral_pos huv (p.continuous.mul p.continuous).continuousOn
      (fun s _ => mul_self_nonneg _) ⟨c, hc, mul_self_pos.2 hc0⟩
  exact hpos.ne' h

instance [hx : Fact (StrictMono x)] : InnerProductSpace.Core ℝ (BrokenPolynomial x r) where
  toInner := inferInstance
  conj_inner_symm v w := by
    simp only [conj_trivial, inner_def]
    exact Finset.sum_congr rfl fun i _ => integral_congr fun s _ => mul_comm _ _
  re_inner_nonneg v := by
    simp only [RCLike.re_to_real, inner_def]
    exact Finset.sum_nonneg fun i _ =>
      integral_nonneg (hx.out (Fin.castSucc_lt_succ (i := i))).le fun s _ => mul_self_nonneg _
  add_left v w z := by
    simp only [inner_def, add_apply, eval_add, add_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact intervalIntegral.integral_add
      (((Polynomial.continuous _).mul (Polynomial.continuous _)).intervalIntegrable _ _)
      (((Polynomial.continuous _).mul (Polynomial.continuous _)).intervalIntegrable _ _)
  smul_left v w c := by
    simp only [inner_def, smul_apply, eval_smul, smul_eq_mul, conj_trivial, Finset.mul_sum,
      mul_assoc, ← intervalIntegral.integral_const_mul]
  definite v hv := by
    simp only [inner_def] at hv
    have hnonneg : ∀ i ∈ Finset.univ,
        0 ≤ ∫ s in x i.castSucc..x i.succ, (v i).eval s * (v i).eval s :=
      fun i _ => integral_nonneg (hx.out (Fin.castSucc_lt_succ (i := i))).le fun s _ =>
        mul_self_nonneg _
    refine BrokenPolynomial.ext fun i => ?_
    rw [zero_apply]
    exact eq_zero_of_integral_sq_eq_zero (hx.out (Fin.castSucc_lt_succ (i := i)))
      ((Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hv i (Finset.mem_univ i))

instance [Fact (StrictMono x)] : NormedAddCommGroup (BrokenPolynomial x r) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance [Fact (StrictMono x)] : InnerProductSpace ℝ (BrokenPolynomial x r) :=
  InnerProductSpace.ofCore _

/-- The squared norm is the sum of the panel integrals of the squares. -/
theorem norm_sq_eq [Fact (StrictMono x)] (v : BrokenPolynomial x r) :
    ‖v‖ ^ 2 = ∑ i, ∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_def]
  exact Finset.sum_congr rfl fun i _ => integral_congr fun s _ => (sq _).symm

/-- **A weighted panel integral dominates a multiple of the squared norm**: if `c ≤ w` on
`[x 0, x n]` then `c ‖v‖²_{L²} ≤ ∑ i, ∫_{x i}^{x (i+1)} w vᵢ²`, since `‖v‖² = ∑ i, ∫ vᵢ²` and the
integrands compare panelwise. With `w = a₀ - a'/2` and `c = μ₀` this is the coercivity behind the
energy estimates of the transport equation ([quarteroni2000numerical] (13.66), (13.69)); with
`c = -μ*` it is the lower bound used when the reaction coefficient has the wrong sign. -/
theorem mul_norm_sq_le_sum_integral [hx : Fact (StrictMono x)] {w : ℝ → ℝ}
    (hw : IntervalIntegrable w volume (x 0) (x (Fin.last n))) {c : ℝ}
    (hc : ∀ s ∈ Icc (x 0) (x (Fin.last n)), c ≤ w s) (v : BrokenPolynomial x r) :
    c * ‖v‖ ^ 2 ≤ ∑ i, ∫ s in x i.castSucc..x i.succ, w s * (v i).eval s ^ 2 := by
  have hm : Monotone x := hx.out.monotone
  have hsub : ∀ i : Fin n, [[x i.castSucc, x i.succ]] ⊆ [[x 0, x (Fin.last n)]] := fun i => by
    rw [uIcc_of_le (hm (Fin.castSucc_lt_succ (i := i)).le), uIcc_of_le (hm (Fin.zero_le _))]
    exact Icc_subset_Icc (hm (Fin.zero_le _)) (hm (Fin.le_last _))
  rw [norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (hm (Fin.castSucc_lt_succ (i := i)).le)
    (((v i).continuous.pow 2).intervalIntegrable _ _ |>.const_mul c)
    ((hw.mono_set (hsub i)).mul_continuousOn ((v i).continuous.pow 2).continuousOn)
    fun s hs => ?_
  have hmem : s ∈ Icc (x 0) (x (Fin.last n)) := by
    have := hsub i (by rw [uIcc_of_le (hm (Fin.castSucc_lt_succ (i := i)).le)]; exact hs)
    rwa [uIcc_of_le (hm (Fin.zero_le _))] at this
  exact mul_le_mul_of_nonneg_right (hc s hmem) (sq_nonneg _)

/-! ### The traces as continuous linear functionals -/

section TraceL

variable [Fact (StrictMono x)]

variable (x r) in
/-- **The right trace as a continuous linear functional** `v ↦ v⁺(x i)`: every linear map on the
finite-dimensional space `BrokenPolynomial x r` is continuous. -/
def traceRightL (i : Fin n) : BrokenPolynomial x r →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (traceRightₗ x r i)

@[simp]
theorem traceRightL_apply (i : Fin n) (v : BrokenPolynomial x r) :
    traceRightL x r i v = traceRight v i := rfl

variable (x r) in
/-- **The left trace as a continuous linear functional** `v ↦ v⁻(x i)`. -/
def traceLeftL (i : Fin (n + 1)) : BrokenPolynomial x r →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (traceLeftₗ x r i)

@[simp]
theorem traceLeftL_apply (i : Fin (n + 1)) (v : BrokenPolynomial x r) :
    traceLeftL x r i v = traceLeft v i := traceLeftₗ_apply i v

variable (x r) in
/-- **The jump as a continuous linear functional** `v ↦ [v]ᵢ`. -/
def jumpL (i : Fin n) : BrokenPolynomial x r →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (jumpₗ x r i)

@[simp]
theorem jumpL_apply (i : Fin n) (v : BrokenPolynomial x r) : jumpL x r i v = jump v i :=
  jumpₗ_apply i v

/-- The right trace is continuous. -/
theorem continuous_traceRight (i : Fin n) :
    Continuous fun v : BrokenPolynomial x r => traceRight v i :=
  (traceRightL x r i).continuous

/-- The left trace is continuous. -/
theorem continuous_traceLeft (i : Fin (n + 1)) :
    Continuous fun v : BrokenPolynomial x r => traceLeft v i :=
  (traceLeftL x r i).continuous.congr fun v => traceLeftL_apply i v

/-- The jump is continuous. -/
theorem continuous_jump (i : Fin n) : Continuous fun v : BrokenPolynomial x r => jump v i :=
  (jumpL x r i).continuous.congr fun v => jumpL_apply i v

end TraceL

/-! ### Integration by parts on the panels -/

/-- **Panel integration by parts**: for `a` differentiable on `[u, v]` with continuous derivative
and a polynomial `p`, `∫_u^v a p p' = ½ [a p²]_u^v - ½ ∫_u^v a' p²`, since `p p' = ½ (p²)'`. -/
theorem integral_mul_deriv_mul_eq {u v : ℝ} {a : ℝ → ℝ}
    (ha : ∀ s ∈ [[u, v]], DifferentiableAt ℝ a s) (ha' : ContinuousOn (deriv a) [[u, v]])
    (p : ℝ[X]) :
    ∫ s in u..v, a s * p.eval s * p.derivative.eval s
      = (a v * p.eval v ^ 2 - a u * p.eval u ^ 2) / 2
        - (1 / 2) * ∫ s in u..v, deriv a s * p.eval s ^ 2 := by
  have hv : ∀ s, HasDerivAt (fun s => p.eval s * p.eval s / 2) (p.eval s * p.derivative.eval s) s :=
    fun s => (((p.hasDerivAt s).mul (p.hasDerivAt s)).div_const 2).congr_deriv (by ring)
  have h := integral_mul_deriv_eq_deriv_mul (fun s hs => (ha s hs).hasDerivAt) (fun s _ => hv s)
    ha'.intervalIntegrable ((p.continuous.mul p.derivative.continuous).intervalIntegrable _ _)
  have e1 : ∫ s in u..v, a s * p.eval s * p.derivative.eval s
      = ∫ s in u..v, a s * (p.eval s * p.derivative.eval s) :=
    integral_congr fun s _ => mul_assoc _ _ _
  have e2 : ∫ s in u..v, deriv a s * (p.eval s * p.eval s / 2)
      = (1 / 2) * ∫ s in u..v, deriv a s * p.eval s ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    exact integral_congr fun s _ => by ring
  rw [e1, h, e2]
  ring

/-- **Integration by parts summed over the panels, in trace form**: for `a` differentiable on
`[x 0, x n]` with continuous derivative and a broken polynomial `v`,
`∑ i, ∫_{x i}^{x (i+1)} a v_i v_i' = ½ a(x n) v⁻(x n)² - ½ ∑ i, a(x i) (v⁺(x i)² - v⁻(x i)²)
- ½ ∑ i, ∫_{x i}^{x (i+1)} a' v_i²`, with `v⁻(x 0) = 0`. This is the identity behind the energy
estimate of the upwind discontinuous Galerkin method ([quarteroni2000numerical] §13.10.1): at each
node `½ a v⁻² - ½ a v⁺² + a [v] v⁺ = ½ a [v]²`. -/
theorem sum_integral_mul_deriv_mul_eq (hx : Monotone x) {a : ℝ → ℝ}
    (ha : ∀ s ∈ Icc (x 0) (x (Fin.last n)), DifferentiableAt ℝ a s)
    (ha' : ContinuousOn (deriv a) (Icc (x 0) (x (Fin.last n)))) (v : BrokenPolynomial x r) :
    ∑ i, ∫ s in x i.castSucc..x i.succ, a s * (v i).eval s * (v i).derivative.eval s
      = a (x (Fin.last n)) * traceLeft v (Fin.last n) ^ 2 / 2
        - ∑ i : Fin n, a (x i.castSucc) * (traceRight v i ^ 2 - traceLeft v i.castSucc ^ 2) / 2
        - (1 / 2) * ∑ i, ∫ s in x i.castSucc..x i.succ, deriv a s * (v i).eval s ^ 2 := by
  have hsub : ∀ i : Fin n, [[x i.castSucc, x i.succ]] ⊆ Icc (x 0) (x (Fin.last n)) := fun i => by
    rw [uIcc_of_le (hx (Fin.castSucc_lt_succ (i := i)).le)]
    exact Icc_subset_Icc (hx (Fin.zero_le _)) (hx (Fin.le_last _))
  -- the panel identities
  have hpanel : ∀ i : Fin n,
      ∫ s in x i.castSucc..x i.succ, a s * (v i).eval s * (v i).derivative.eval s
      = (a (x i.succ) * traceLeft v i.succ ^ 2 - a (x i.castSucc) * traceRight v i ^ 2) / 2
        - (1 / 2) * ∫ s in x i.castSucc..x i.succ, deriv a s * (v i).eval s ^ 2 := fun i =>
    integral_mul_deriv_mul_eq (fun s hs => ha s (hsub i hs)) (ha'.mono (hsub i)) (v i)
  -- the shift of the left traces
  have hshift : ∑ i : Fin n, a (x i.succ) * traceLeft v i.succ ^ 2
      = ∑ i : Fin n, a (x i.castSucc) * traceLeft v i.castSucc ^ 2
        + a (x (Fin.last n)) * traceLeft v (Fin.last n) ^ 2 := by
    have h1 := Fin.sum_univ_succ fun j : Fin (n + 1) => a (x j) * traceLeft v j ^ 2
    have h2 := Fin.sum_univ_castSucc fun j : Fin (n + 1) => a (x j) * traceLeft v j ^ 2
    rw [traceLeft_zero] at h1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add] at h1
    rw [← h1, h2]
  simp only [hpanel, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, hshift]
  ring

/-! ### The inverse inequality -/

/-- The inverse inequality on one panel: for an affine polynomial `p` and `u < v`,
`∫_u^v p'² ≤ 12 (v - u)⁻² ∫_u^v p²`. With `p = c₁ s + c₀`, the difference of the two sides is
`3 (v - u) (c₁ (u + v) + 2 c₀)² ≥ 0`. -/
private theorem integral_sq_derivative_le {u v : ℝ} (huv : u < v) {p : ℝ[X]}
    (hp : p.natDegree ≤ 1) :
    ∫ s in u..v, p.derivative.eval s ^ 2 ≤ 12 / (v - u) ^ 2 * ∫ s in u..v, p.eval s ^ 2 := by
  rw [eq_X_add_C_of_natDegree_le_one hp]
  set c₁ := p.coeff 1
  set c₀ := p.coeff 0
  have hd : ∫ s in u..v, (derivative (C c₁ * X + C c₀)).eval s ^ 2 = c₁ ^ 2 * (v - u) := by
    simp only [derivative_add, derivative_mul, derivative_C, zero_mul, derivative_X, mul_one,
      zero_add, add_zero, eval_C, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hi : ∫ s in u..v, (C c₁ * X + C c₀).eval s ^ 2
      = c₁ ^ 2 * ((v ^ 3 - u ^ 3) / 3) + 2 * c₁ * c₀ * ((v ^ 2 - u ^ 2) / 2)
        + c₀ ^ 2 * (v - u) := by
    have e : ∫ s in u..v, (C c₁ * X + C c₀).eval s ^ 2
        = ∫ s in u..v, (c₁ ^ 2 * s ^ 2 + 2 * c₁ * c₀ * s + c₀ ^ 2) :=
      integral_congr fun s _ => by simp; ring
    have h1 : Continuous fun s : ℝ => c₁ ^ 2 * s ^ 2 := by fun_prop
    have h2 : Continuous fun s : ℝ => 2 * c₁ * c₀ * s := by fun_prop
    have h12 : Continuous fun s : ℝ => c₁ ^ 2 * s ^ 2 + 2 * c₁ * c₀ * s := h1.add h2
    rw [e, intervalIntegral.integral_add (h12.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow,
      integral_id, intervalIntegral.integral_const, smul_eq_mul, mul_comm (v - u)]
    norm_num
  rw [hd, hi]
  have hpos : 0 < v - u := sub_pos.2 huv
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg hpos.le (sq_nonneg (c₁ * (u + v) + 2 * c₀))]

/-- **The inverse inequality for piecewise linear functions**: on a partition whose panels have
length at least `h_min > 0`, every `v : BrokenPolynomial x 1` satisfies
`∑ i, ∫_{x i}^{x (i+1)} v_i'² ≤ 12 h_min⁻² ∑ i, ∫_{x i}^{x (i+1)} v_i²`, i.e.
`‖v'‖²_{L²} ≤ 12 h_min⁻² ‖v‖²_{L²}`. No continuity is needed: the estimate holds panel by panel
(`3 (v - u) (c₁ (u + v) + 2 c₀)² ≥ 0`). For a uniform mesh this is the bound `λ_max ≤ 12 h⁻²` of the
`P₁` stiffness–mass pencil, the `λ_max ≤ c h⁻²` behind the parabolic stability condition
`Δt ≤ C h²` of the θ-method with `θ < 1/2` ([quarteroni2000numerical] §13.4.1). -/
theorem inverseInequality_linear {hmin : ℝ} (h0 : 0 < hmin)
    (hle : ∀ i : Fin n, hmin ≤ x i.succ - x i.castSucc) (v : BrokenPolynomial x 1) :
    ∑ i, ∫ s in x i.castSucc..x i.succ, (v i).derivative.eval s ^ 2
      ≤ 12 / hmin ^ 2 * ∑ i, ∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hlt : x i.castSucc < x i.succ := by linarith [hle i]
  refine (integral_sq_derivative_le hlt (natDegree_le v i)).trans
    (mul_le_mul_of_nonneg_right ?_ (integral_nonneg hlt.le fun s _ => sq_nonneg _))
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_left₀ h0.le (hle i) 2)

/-! ### Gluing the continuous subspace -/

section Glue

open Spline

/-- The panel polynomials of `v`, continued by `0` to all of `ℕ`. -/
def polyExt (v : BrokenPolynomial x r) (j : ℕ) : ℝ[X] :=
  if h : j < n then v ⟨j, h⟩ else 0

theorem polyExt_of_lt (v : BrokenPolynomial x r) {j : ℕ} (hj : j < n) :
    polyExt v j = v ⟨j, hj⟩ := dite_eq_left hj

theorem polyExt_add (v w : BrokenPolynomial x r) (j : ℕ) :
    polyExt (v + w) j = polyExt v j + polyExt w j := by
  unfold polyExt; split_ifs <;> simp

theorem polyExt_smul (c : ℝ) (v : BrokenPolynomial x r) (j : ℕ) :
    polyExt (c • v) j = c • polyExt v j := by
  unfold polyExt; split_ifs <;> simp

/-- **The glued function** of a broken polynomial: the function on `ℝ` equal to `v_i` on the
half-open panel `[x i, x (i+1))`, to `v_0` below `x 0` and to `v_{n-1}` from `x (n-1)` on, through
`Spline.panelGlue` (whose panel `i` is this module's panel `i - 1`). For `v` in the continuous
subspace it is continuous (`continuous_glue`). -/
def glue (v : BrokenPolynomial x r) : ℝ → ℝ :=
  panelGlue n (extendFin x) fun i t => (polyExt v (i - 1)).eval t

theorem glue_add (v w : BrokenPolynomial x r) (t : ℝ) : glue (v + w) t = glue v t + glue w t := by
  simp only [glue, panelGlue, polyExt_add, eval_add]

theorem glue_smul (c : ℝ) (v : BrokenPolynomial x r) (t : ℝ) : glue (c • v) t = c * glue v t := by
  simp only [glue, panelGlue, polyExt_smul, eval_smul, smul_eq_mul]

/-- A strictly increasing `x : Fin (n + 1) → ℝ`, continued to `ℕ`, is a partition of
`[x 0, x n]` in the sense of `Numlib/Approximation/Spline`. -/
theorem isPartition_extendFin (hx : StrictMono x) :
    IsPartition (x 0) (x (Fin.last n)) n (extendFin x) where
  step j hj := by
    rw [extendFin_of_lt x (by omega), extendFin_of_lt x (by omega)]
    exact hx (Fin.mk_lt_mk.2 (Nat.lt_succ_self j))
  first := extendFin_of_lt x (Nat.succ_pos n)
  last := extendFin_of_lt x (Nat.lt_succ_self n)

/-- The panel polynomials of an element of the continuous subspace agree at the interior nodes,
in the indexing of `Spline.panelGlue`. -/
private theorem polyExt_eval_eq_of_mem_continuous {v : BrokenPolynomial x r}
    (hv : v ∈ continuous x r) :
    ∀ i, 1 ≤ i → i < n → (polyExt v (i - 1)).eval (extendFin x i)
      = (polyExt v (i + 1 - 1)).eval (extendFin x i) := by
  intro i hi1 hin
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, polyExt_of_lt v (by omega), polyExt_of_lt v hin,
    extendFin_of_lt x (by omega)]
  exact eval_succ_eq_of_mem_continuous hv ⟨j, by omega⟩ hin

/-- On the closed panel `[x i, x (i+1)]`, the glued function of an element of the continuous
subspace is the panel polynomial `v_i`. -/
theorem glue_eq_of_mem (hx : StrictMono x) {v : BrokenPolynomial x r} (hv : v ∈ continuous x r)
    (i : Fin n) {t : ℝ} (ht : t ∈ Icc (x i.castSucc) (x i.succ)) : glue v t = (v i).eval t := by
  have h := panelGlue_eq_of_mem (isPartition_extendFin hx)
    (Q := fun i t => (polyExt v (i - 1)).eval t) (polyExt_eval_eq_of_mem_continuous hv)
    (i := (i : ℕ) + 1) (by omega) i.2 (Icc_subset_extPanel _ (by
      rw [Nat.add_sub_cancel, extendFin_of_lt x (by omega), extendFin_of_lt x (by omega)]
      exact ht))
  rw [glue, h, Nat.add_sub_cancel, polyExt_of_lt v i.2]

/-- **The glued function of an element of the continuous subspace is continuous.** -/
theorem continuous_glue (hx : StrictMono x) {v : BrokenPolynomial x r} (hv : v ∈ continuous x r) :
    Continuous (glue v) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : glue v = fun _ => 0 := by
      funext t
      change (polyExt v _).eval t = 0
      rw [polyExt, dite_eq_right (Nat.not_lt_zero _), eval_zero]
    rw [this]; exact continuous_const
  · exact continuous_panelGlue (isPartition_extendFin hx) hn (polyExt_eval_eq_of_mem_continuous hv)
      fun i _ _ => (Polynomial.continuous _).continuousOn

/-- **The gluing map** of the continuous subspace: the continuous function on `[x 0, x n]` equal to
`v_i` on the panel `[x i, x (i+1)]`, as a linear map. -/
def toContinuousMap (hx : StrictMono x) :
    continuous x r →ₗ[ℝ] C(Icc (x 0) (x (Fin.last n)), ℝ) where
  toFun v := ⟨fun t => glue v.1 t, (continuous_glue hx v.2).comp continuous_subtype_val⟩
  map_add' v w := ContinuousMap.ext fun t => glue_add v.1 w.1 t
  map_smul' c v := ContinuousMap.ext fun t => glue_smul c v.1 t

theorem toContinuousMap_apply (hx : StrictMono x) (v : continuous x r)
    (t : Icc (x 0) (x (Fin.last n))) : toContinuousMap hx v t = glue v.1 t := rfl

/-- On the panel `[x i, x (i+1)]` the glued function is the panel polynomial. -/
theorem toContinuousMap_apply_of_mem (hx : StrictMono x) (v : continuous x r) (i : Fin n)
    {t : Icc (x 0) (x (Fin.last n))} (ht : (t : ℝ) ∈ Icc (x i.castSucc) (x i.succ)) :
    toContinuousMap hx v t = (v.1 i).eval (t : ℝ) :=
  glue_eq_of_mem hx v.2 i ht

/-- The gluing map is injective: a polynomial is determined by its values on a nondegenerate
panel. -/
theorem toContinuousMap_injective (hx : StrictMono x) :
    Function.Injective (toContinuousMap hx (r := r)) := by
  intro v w hvw
  refine Subtype.ext (BrokenPolynomial.ext fun i => ?_)
  refine Polynomial.eq_of_infinite_eval_eq _ _
    ((Ioo_infinite (hx (Fin.castSucc_lt_succ (i := i)))).mono fun t ht => ?_)
  have hmem : t ∈ Icc (x 0) (x (Fin.last n)) :=
    ⟨(hx.monotone (Fin.zero_le _)).trans ht.1.le, ht.2.le.trans (hx.monotone (Fin.le_last _))⟩
  have := congrArg (fun F : C(Icc (x 0) (x (Fin.last n)), ℝ) => F ⟨t, hmem⟩) hvw
  rwa [toContinuousMap_apply_of_mem hx v i (Ioo_subset_Icc_self ht),
    toContinuousMap_apply_of_mem hx w i (Ioo_subset_Icc_self ht)] at this

/-- **The continuous broken polynomials are the spline space without smoothness**: the gluing map
sends `continuous x r` onto `Spline.splineSpace (x 0) (x n) n x r 0` of
`Numlib/Approximation/Spline`. With `toContinuousMap_injective` the two are isomorphic, so
`finrank (continuous x r) = n r + 1` is `Spline.finrank_splineSpace`; the spline space is the one
definition of the continuous piecewise polynomials, of which `continuous x r` is the per-panel
representation with traces and jumps. -/
theorem toContinuousMap_range_eq_splineSpace (hx : StrictMono x) (hn : 0 < n) :
    LinearMap.range (toContinuousMap hx (r := r))
      = splineSpace (x 0) (x (Fin.last n)) n (extendFin x) r 0 := by
  have hpart := isPartition_extendFin hx
  ext f
  rw [LinearMap.mem_range, mem_splineSpace_iff]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨glue v.1, ?_, fun t => rfl, fun j hj => ⟨v.1 ⟨j, hj⟩,
      degree_le_of_natDegree_le (natDegree_le _ _), fun t ht => ?_⟩⟩
    · rw [Nat.cast_zero, contDiffOn_zero]
      exact (continuous_glue hx v.2).continuousOn
    · rw [extendFin_of_lt x (by omega), extendFin_of_lt x (by omega)] at ht
      exact glue_eq_of_mem hx v.2 ⟨j, hj⟩ ht
  · rintro ⟨g, -, hfg, hp⟩
    choose p hpdeg hpeq using hp
    have hE : ∀ (m : ℕ) (hm : m < n + 1), extendFin x m = x ⟨m, hm⟩ := fun m hm =>
      extendFin_of_lt x hm
    set v : BrokenPolynomial x r := mk x (fun i => p i i.2)
      fun i => natDegree_le_of_degree_le (hpdeg i i.2) with hv
    have hvi : ∀ i : Fin n, v i = p i i.2 := fun i => rfl
    -- the panel polynomials agree at the interior nodes, both being `g` there
    have hvc : v ∈ continuous x r := by
      intro i hi
      set j : Fin n := ⟨i - 1, by omega⟩ with hj
      have hcs : i.castSucc = j.succ := Fin.ext (by simp [hj]; omega)
      have hxi : extendFin x i = x j.succ := (hE i (by omega)).trans (congrArg x hcs)
      have hmem1 : x j.succ ∈ Icc (extendFin x i) (extendFin x (i + 1)) := by
        rw [hxi, hE (i + 1) (by omega)]
        exact ⟨le_rfl, hx.monotone (by simp [Fin.le_def, hj])⟩
      have hmem2 : x j.succ ∈ Icc (extendFin x (i - 1)) (extendFin x (i - 1 + 1)) := by
        rw [Nat.sub_add_cancel hi, hxi, hE (i - 1) (by omega)]
        exact ⟨hx.monotone (by simp [Fin.le_def, hj]), le_rfl⟩
      rw [jump_apply, traceRight_apply, hcs, traceLeft_succ, hvi, hvi, sub_eq_zero]
      exact (hpeq i i.2 hmem1).symm.trans (hpeq (i - 1) (by omega) hmem2)
    refine ⟨⟨v, hvc⟩, ContinuousMap.ext fun t => ?_⟩
    obtain ⟨i, hi1, hin, hti, -⟩ := hpart.exists_mem_panel hn t.2
    set j : Fin n := ⟨i - 1, by omega⟩ with hj
    have hj1 : extendFin x (i - 1) = x j.castSucc := hE (i - 1) (by omega)
    have hj2 : extendFin x i = x j.succ := by
      rw [hE i (by omega)]
      exact congrArg x (Fin.ext (by simp [hj]; omega))
    have hti' : (t : ℝ) ∈ Icc (x j.castSucc) (x j.succ) := by rwa [hj1, hj2] at hti
    rw [toContinuousMap_apply_of_mem hx ⟨v, hvc⟩ j hti', hfg t, hvi]
    exact (hpeq (i - 1) (by omega) (by rwa [Nat.sub_add_cancel hi1])).symm

end Glue

/-- Interval integrals do not see the endpoints: two functions agreeing on the open interval have
the same integral over it. -/
private theorem intervalIntegral_congr_Ioo {u v : ℝ} (huv : u ≤ v) {f g : ℝ → ℝ}
    (h : EqOn f g (Ioo u v)) : ∫ t in u..v, f t = ∫ t in u..v, g t := by
  rw [integral_of_le huv, integral_of_le huv, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-! ### The embedding into `L²` -/

section ToLp

open Spline

/-- **The step function** of a broken polynomial: the function equal to `v_i` on the half-open
panel `[x i, x (i+1))` and to `0` outside `[x 0, x n)`. -/
def stepFun (v : BrokenPolynomial x r) : ℝ → ℝ :=
  ∑ i : Fin n, (Ico (x i.castSucc) (x i.succ)).indicator fun s => (v i).eval s

/-- On the half-open panel `[x i, x (i+1))` the step function is the panel polynomial. -/
theorem stepFun_apply_of_mem (hx : Monotone x) (v : BrokenPolynomial x r) {i : Fin n} {t : ℝ}
    (ht : t ∈ Ico (x i.castSucc) (x i.succ)) : stepFun v t = (v i).eval t := by
  unfold stepFun
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · rw [indicator_of_mem ht]
  · intro j _ hji
    refine indicator_of_notMem (fun hj => ?_) _
    rcases lt_or_gt_of_ne hji with h | h
    · exact absurd ht.1 (not_le.2 (hj.2.trans_le (hx (Fin.succ_le_castSucc_iff.2 h))))
    · exact absurd hj.1 (not_le.2 (ht.2.trans_le (hx (Fin.succ_le_castSucc_iff.2 h))))
  · exact fun h => absurd (Finset.mem_univ i) h

theorem stepFun_add (v w : BrokenPolynomial x r) : stepFun (v + w) = stepFun v + stepFun w := by
  funext t
  simp only [stepFun, add_apply, eval_add, Finset.sum_apply, Pi.add_apply, indicator_add,
    Finset.sum_add_distrib]

theorem stepFun_smul (c : ℝ) (v : BrokenPolynomial x r) : stepFun (c • v) = c • stepFun v := by
  funext t
  simp only [stepFun, smul_apply, eval_smul, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum,
    indicator_const_smul]

/-- The step function is square integrable on `(x 0, x n)`. -/
theorem memLp_stepFun (v : BrokenPolynomial x r) :
    MemLp (stepFun v) 2 (volume.restrict (Ioo (x 0) (x (Fin.last n)))) :=
  memLp_finsetSum' _ fun i _ =>
    ((v i).continuous.continuousOn.memLp_two_restrict_Ioo).indicator measurableSet_Ico

/-- The squared `L²(x 0, x n)` norm of the step function is the sum of the panel integrals. -/
theorem integral_stepFun_sq (hx : StrictMono x) (v : BrokenPolynomial x r) :
    ∫ t in Ioo (x 0) (x (Fin.last n)), stepFun v t ^ 2
      = ∑ i, ∫ s in x i.castSucc..x i.succ, (v i).eval s ^ 2 := by
  have hpart := isPartition_extendFin hx
  have hle : x 0 ≤ x (Fin.last n) := hx.monotone (Fin.zero_le _)
  have hint : IntegrableOn (fun t => stepFun v t ^ 2) (Ioo (x 0) (x (Fin.last n))) :=
    (memLp_two_iff_integrable_sq (memLp_stepFun v).1).1 (memLp_stepFun v)
  have hE : ∀ (m : ℕ) (hm : m < n + 1), extendFin x m = x ⟨m, hm⟩ := fun m hm =>
    extendFin_of_lt x hm
  have hmem : ∀ m ≤ n, extendFin x m ∈ Icc (x 0) (x (Fin.last n)) := fun m hm => by
    rw [hE m (by omega)]
    exact ⟨hx.monotone (Fin.zero_le _), hx.monotone (Fin.le_last _)⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_of_le hle, ← hpart.first, ← hpart.last,
    ← sum_integral_adjacent_intervals (a := extendFin x) (n := n) fun j hj =>
      hint.intervalIntegrable_of_Ioo (hmem j (by omega)) (hmem (j + 1) (by omega)),
    Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hE i (by omega), hE (i + 1) (by omega)]
  exact intervalIntegral_congr_Ioo (hx (Fin.castSucc_lt_succ (i := i))).le fun t ht => by
    rw [stepFun_apply_of_mem hx.monotone v (Ioo_subset_Ico_self ht)]

variable [hx : Fact (StrictMono x)]

variable (x r) in
/-- **The isometric embedding into `L²(x 0, x n)`**: a broken polynomial as the class of its step
function, the function equal to `v_i` on the half-open panel `[x i, x (i+1))`. -/
def toLpₗᵢ : BrokenPolynomial x r →ₗᵢ[ℝ] Lp ℝ 2 (volume.restrict (Ioo (x 0) (x (Fin.last n)))) where
  toFun v := (memLp_stepFun v).toLp (stepFun v)
  map_add' v w := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (stepFun_add v w))
  map_smul' c v := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (stepFun_smul c v))
  norm_map' v := by
    change ‖(memLp_stepFun v).toLp (stepFun v)‖ = ‖v‖
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_sq_eq, norm_sq_eq_integral_sq, ← integral_stepFun_sq hx.out]
    refine integral_congr_ae ((MemLp.coeFn_toLp (memLp_stepFun v)).mono fun t ht => ?_)
    simp only [ht, sq_abs]

/-- The embedding is the step function almost everywhere. -/
theorem coeFn_toLpₗᵢ (v : BrokenPolynomial x r) :
    toLpₗᵢ x r v =ᵐ[volume.restrict (Ioo (x 0) (x (Fin.last n)))] stepFun v :=
  MemLp.coeFn_toLp (memLp_stepFun v)

end ToLp

end BrokenPolynomial

end
