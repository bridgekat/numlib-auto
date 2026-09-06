/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.PerronFrobenius`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Order

/-!
# Perron–Frobenius theory of entrywise nonnegative matrices

The spectral theory of matrices that are nonnegative for the entrywise order `Matrix.EntrywiseLE`
of `Numlib/LinearAlgebra/Matrix/Order.lean`. Two groups of results:

* **Monotonicity.** Powers (`Matrix.EntrywiseLE.pow`), the maximum-absolute-row-sum norm
  (`Matrix.EntrywiseLE.linfty_opNorm_le`), the Euclidean operator norm
  (`Matrix.EntrywiseLE.l2_opNorm_le`) and the spectral radius
  (`Matrix.complexSpectralRadius_le_of_entrywiseLE`) are all monotone in a nonnegative matrix.
  The spectral radius here is `Matrix.complexSpectralRadius` of
  `Numlib/LinearAlgebra/Matrix/Complexify.lean`, the spectral radius of the complexification;
  `spectralRadius ℝ` of a real matrix is not the spectral radius.

* **The Perron–Frobenius theorem for an irreducible matrix.** An irreducible nonnegative matrix on
  a nonempty index type has an entrywise *positive* eigenvector for its spectral radius
  (`Matrix.IsIrreducible.exists_pos_hasEigenvector_complexSpectralRadius`), and that eigenvalue is
  geometrically simple
  (`Matrix.IsIrreducible.finrank_eigenspace_complexSpectralRadius_eq_one`). Irreducibility is
  Mathlib's `Matrix.IsIrreducible`: entrywise nonnegative, with the quiver of its positive entries
  strongly connected.

## Implementation notes

The combinatorial core is `Matrix.IsIrreducible.entrywisePos_one_add_pow`: for irreducible `A` on
`N` indices, `(1 + A) ^ (N - 1)` is entrywise *positive*. It is proved by watching the reach sets
`Sₖ = {j | 0 < ((1 + A) ^ k) i j}` grow: they are nondecreasing, `Sₖ₊₁` is determined by `Sₖ`, so
they stabilise as soon as two consecutive ones agree, and irreducibility forbids stabilising short
of everything. Hence each step before saturation gains at least one index, and `N - 1` steps
suffice. This replaces the argument the standard accounts give — shortening a quiver path below
`N`, as in Seneta, *Non-negative Matrices and Markov Chains* — for which Mathlib has no
lemma.

The Perron eigenvector is obtained without any maximisation. An eigenvalue `μ` of maximal modulus
of the complexification has an eigenvector `y`, and the entrywise modulus `z = ‖y ·‖` satisfies the
*subinvariance* `ρ • z ≤ A *ᵥ z` with `z` nonnegative and nonzero. If the slack were nonzero,
multiplying by the positive matrix `(1 + A) ^ (N - 1)` — which commutes with `A` — would give a
positive `u` with `(ρ + ε) • u ≤ A *ᵥ u` for some `ε > 0`, whence `(ρ + ε) ^ k ≤ ‖A ^ k‖` for every
`k` and `ρ + ε ≤ ρ` by Gelfand's formula. So the slack vanishes, and positivity of `z` follows from
positivity of `(1 + A) ^ (N - 1)`.

Geometric simplicity is then a one-line extremal argument: for another eigenvector `w` of `A` at
`ρ`, the scalar `t = sup_i w i / x i` makes `t • x - w` a nonnegative eigenvector with a vanishing
entry, so it is zero.

*Algebraic* simplicity of the Perron eigenvalue, which is what "simple" means in
[Saad][saad2003iterative] Theorem 1.25, is not proved here: it needs the derivative of the
characteristic polynomial through the adjugate.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace Matrix

variable {m n : Type*}

/-! ### Monotonicity of powers -/

section OrderedSemiring

variable {α : Type*} [Semiring α] [PartialOrder α] [IsOrderedRing α]

/-- **Powers are monotone in a nonnegative matrix**: if `0 ≤ₑ A` and `A ≤ₑ B` then
`A ^ k ≤ₑ B ^ k` (Saad, *Iterative Methods for Sparse Linear Systems*, Corollary 1.27). -/
theorem EntrywiseLE.pow [Fintype n] [DecidableEq n] {A B : Matrix n n α}
    (hA : A.EntrywiseNonneg) (hAB : A ≤ₑ B) (k : ℕ) : A ^ k ≤ₑ B ^ k := by
  have hB : B.EntrywiseNonneg := hA.trans hAB
  induction k with
  | zero => simpa only [pow_zero] using EntrywiseLE.rfl
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (EntrywiseLE.mul_of_entrywiseNonneg_left (hA.pow k) hAB).trans
      (EntrywiseLE.mul_of_entrywiseNonneg_right hB ih)

end OrderedSemiring

/-! ### Monotonicity of the induced norms -/

section Norms

variable [Fintype m] [Fintype n]

/-- Comparison of the absolute values of two comparable nonnegative reals. -/
private theorem nnnorm_le_nnnorm_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : ‖a‖₊ ≤ ‖b‖₊ := by
  rw [← NNReal.coe_le_coe]
  simpa only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg (ha.trans hab)]
    using hab

section Operator

open scoped Matrix.Norms.Operator

/-- **The maximum-absolute-row-sum norm is monotone on nonnegative matrices** (Saad, *Iterative
Methods for Sparse Linear Systems*, Proposition 1.24, clause 5): if `0 ≤ₑ A` and `A ≤ₑ B` then
`‖A‖ ≤ ‖B‖` for the norm scoped in `Matrix.Norms.Operator`. -/
theorem EntrywiseLE.linfty_opNorm_le {A B : Matrix m n ℝ} (hA : A.EntrywiseNonneg)
    (hAB : A ≤ₑ B) : ‖A‖ ≤ ‖B‖ := by
  rw [linfty_opNorm_def, linfty_opNorm_def, NNReal.coe_le_coe]
  refine Finset.sup_mono_fun fun i _ => Finset.sum_le_sum fun j _ => ?_
  exact nnnorm_le_nnnorm_of_le (hA.apply i j) (hAB i j)

/-- The transposed form of `Matrix.EntrywiseLE.linfty_opNorm_le`: the maximum absolute *column*
sum, Saad's `‖·‖₁`, is monotone on nonnegative matrices too. -/
theorem EntrywiseLE.linfty_opNorm_transpose_le {A B : Matrix m n ℝ} (hA : A.EntrywiseNonneg)
    (hAB : A ≤ₑ B) : ‖Aᵀ‖ ≤ ‖Bᵀ‖ :=
  EntrywiseLE.linfty_opNorm_le (fun i j => hA.apply j i) fun i j => hAB j i

end Operator

section L2Operator

open scoped Matrix.Norms.L2Operator

/-- The Euclidean norm is monotone under an entrywise comparison of absolute values. -/
private theorem norm_toLp_le_of_abs_le {a b : n → ℝ} (h : ∀ i, |a i| ≤ |b i|) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ n)‖ ≤ ‖(WithLp.toLp 2 b : EuclideanSpace ℝ n)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  simp only [Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

/-- The Euclidean norm ignores entrywise signs. -/
private theorem norm_toLp_abs (a : n → ℝ) :
    ‖(WithLp.toLp 2 (fun i => |a i|) : EuclideanSpace ℝ n)‖
      = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ n)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp

variable [DecidableEq n]

/-- **The Euclidean operator norm is monotone on nonnegative matrices** (Saad, *Iterative Methods
for Sparse Linear Systems*, Problem P-1.28): if `0 ≤ₑ A` and `A ≤ₑ B` then `‖A‖ ≤ ‖B‖` for the
norm scoped in `Matrix.Norms.L2Operator`.

The argument is entrywise: `|A *ᵥ d| ≤ A *ᵥ |d| ≤ B *ᵥ |d|`, and `|d|` has the norm of `d`. -/
theorem EntrywiseLE.l2_opNorm_le {A B : Matrix n n ℝ} (hA : A.EntrywiseNonneg)
    (hAB : A ≤ₑ B) : ‖A‖ ≤ ‖B‖ := by
  have hB : B.EntrywiseNonneg := hA.trans hAB
  rw [← l2_opNorm_toEuclideanCLM (𝕜 := ℝ) A]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have hx : x = WithLp.toLp 2 (WithLp.ofLp x) := _root_.rfl
  set d : n → ℝ := WithLp.ofLp x with hd
  rw [hx, toEuclideanCLM_toLp]
  have hstep : ∀ i, |(A *ᵥ d) i| ≤ |(B *ᵥ fun j => |d j|) i| := by
    intro i
    have h1 : |(A *ᵥ d) i| ≤ (A *ᵥ fun j => |d j|) i := by
      simp only [mulVec_apply_eq_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_of_nonneg (hA.apply i j)]
    have h2 : (A *ᵥ fun j => |d j|) i ≤ (B *ᵥ fun j => |d j|) i := by
      simp only [mulVec_apply_eq_sum]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hAB i j) (abs_nonneg _)
    have h3 : (0 : ℝ) ≤ (B *ᵥ fun j => |d j|) i :=
      hB.mulVec_nonneg (fun j => abs_nonneg _) i
    rw [abs_of_nonneg h3]
    exact h1.trans h2
  calc ‖(WithLp.toLp 2 (A *ᵥ d) : EuclideanSpace ℝ n)‖
      ≤ ‖(WithLp.toLp 2 (B *ᵥ fun j => |d j|) : EuclideanSpace ℝ n)‖ :=
        norm_toLp_le_of_abs_le hstep
    _ ≤ ‖B‖ * ‖(WithLp.toLp 2 (fun j => |d j|) : EuclideanSpace ℝ n)‖ :=
        l2_opNorm_mulVec _ (WithLp.toLp 2 fun j => |d j|)
    _ = ‖B‖ * ‖(WithLp.toLp 2 d : EuclideanSpace ℝ n)‖ := by rw [norm_toLp_abs]

/-! ### Monotonicity of the spectral radius -/

/-- **The spectral radius is monotone on nonnegative matrices** (Saad, *Iterative Methods for
Sparse Linear Systems*, Theorem 1.28): if `0 ≤ₑ A` and `A ≤ₑ B` then `ρ(A) ≤ ρ(B)`.

Gelfand's formula turns the monotonicity of the powers and of the operator norm into monotonicity
of the limit `‖X ^ k‖ ^ (1 / k) → ρ(X)`. -/
theorem complexSpectralRadius_le_of_entrywiseLE {A B : Matrix n n ℝ} (hA : A.EntrywiseNonneg)
    (hAB : A ≤ₑ B) : complexSpectralRadius A ≤ complexSpectralRadius B := by
  have hreal : (complexSpectralRadius A).toReal ≤ (complexSpectralRadius B).toReal := by
    refine le_of_tendsto_of_tendsto (tendsto_pow_rpow_complexSpectralRadius A)
      (tendsto_pow_rpow_complexSpectralRadius B) (Filter.Eventually.of_forall fun k => ?_)
    exact Real.rpow_le_rpow (norm_nonneg _)
      (EntrywiseLE.l2_opNorm_le (hA.pow k) (EntrywiseLE.pow hA hAB k)) (by positivity)
  exact (ENNReal.toReal_le_toReal (complexSpectralRadius_ne_top A)
    (complexSpectralRadius_ne_top B)).mp hreal

end L2Operator

end Norms

/-! ### The combinatorial core of the irreducible theory -/

section Irreducible

variable [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

omit [Fintype n] in
/-- `1 + A` is entrywise nonnegative when `A` is. -/
private theorem entrywiseNonneg_one_add (hA : ∀ i j, 0 ≤ A i j) :
    (1 + A : Matrix n n ℝ).EntrywiseNonneg :=
  EntrywiseNonneg.add entrywiseNonneg_one hA

omit [Fintype n] in
/-- The identity is entrywise below `1 + A` when `A` is nonnegative. -/
private theorem one_entrywiseLE_one_add (hA : ∀ i j, 0 ≤ A i j) :
    (1 : Matrix n n ℝ) ≤ₑ 1 + A := fun i j => by
  rw [Matrix.add_apply]
  exact le_add_of_nonneg_right (hA i j)

omit [Fintype n] in
/-- A nonnegative matrix is entrywise below `1 + A`. -/
private theorem self_entrywiseLE_one_add (A : Matrix n n ℝ) :
    A ≤ₑ (1 : Matrix n n ℝ) + A := fun i j => by
  rw [Matrix.add_apply]
  exact le_add_of_nonneg_left (by simpa using entrywiseNonneg_one (α := ℝ) (n := n) i j)

/-- The powers of `1 + A` increase entrywise, because `1 + A` dominates the identity. -/
private theorem one_add_pow_entrywiseLE_succ (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    (1 + A : Matrix n n ℝ) ^ k ≤ₑ (1 + A) ^ (k + 1) := by
  have h := EntrywiseLE.mul_of_entrywiseNonneg_left
    ((entrywiseNonneg_one_add hA).pow k) (one_entrywiseLE_one_add hA)
  rw [Matrix.mul_one, ← pow_succ] at h
  exact h

/-- A positive entry of `A ^ k` is a positive entry of `(1 + A) ^ k`. -/
private theorem pow_entrywiseLE_one_add_pow (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    A ^ k ≤ₑ (1 + A : Matrix n n ℝ) ^ k :=
  EntrywiseLE.pow hA (self_entrywiseLE_one_add A) k

open scoped Classical in
/-- The set of indices reached from `i` in exactly `k` steps of `1 + A`, that is, the support of
the `i`-th row of `(1 + A) ^ k`. Since `1 + A` dominates the identity, these sets increase with
`k`, and each one determines the next. -/
private noncomputable def reach (A : Matrix n n ℝ) (i : n) (k : ℕ) : Finset n :=
  Finset.univ.filter fun j => 0 < ((1 + A) ^ k) i j

private theorem mem_reach {i j : n} {k : ℕ} :
    j ∈ reach A i k ↔ 0 < ((1 + A) ^ k) i j := by
  classical
  simp [reach]

private theorem reach_zero (i : n) : reach A i 0 = {i} := by
  ext j
  rw [mem_reach, Finset.mem_singleton, pow_zero, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

private theorem reach_subset_succ (hA : ∀ i j, 0 ≤ A i j) (i : n) (k : ℕ) :
    reach A i k ⊆ reach A i (k + 1) := fun j hj =>
  mem_reach.2 ((mem_reach.1 hj).trans_le (one_add_pow_entrywiseLE_succ hA k i j))

private theorem reach_mono (hA : ∀ i j, 0 ≤ A i j) (i : n) {k l : ℕ} (hkl : k ≤ l) :
    reach A i k ⊆ reach A i l :=
  monotone_nat_of_le_succ (fun k => reach_subset_succ hA i k) hkl

/-- One step of the reach recursion: `reach A i (k + 1)` is the set of indices adjacent, for
`1 + A`, to some index of `reach A i k`. -/
private theorem mem_reach_succ_iff (hA : ∀ i j, 0 ≤ A i j) (i : n) (k : ℕ) (l : n) :
    l ∈ reach A i (k + 1) ↔ ∃ j ∈ reach A i k, 0 < (1 + A) j l := by
  have hB := entrywiseNonneg_one_add hA
  have hBk := hB.pow k
  rw [mem_reach, pow_succ, Matrix.mul_apply,
    Finset.sum_pos_iff_of_nonneg fun j _ => mul_nonneg (hBk.apply i j) (hB.apply j l)]
  constructor
  · rintro ⟨j, -, hj⟩
    rcases mul_pos_iff.1 hj with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact ⟨j, mem_reach.2 h1, h2⟩
    · exact absurd h1 (not_lt.2 (hBk.apply i j))
  · rintro ⟨j, hj, hjl⟩
    exact ⟨j, Finset.mem_univ j, mul_pos (mem_reach.1 hj) hjl⟩

/-- Two consecutive reach sets that agree make the whole sequence constant from then on. -/
private theorem reach_add_eq (hA : ∀ i j, 0 ≤ A i j) (i : n) {k : ℕ}
    (heq : reach A i (k + 1) = reach A i k) (mm : ℕ) : reach A i (k + mm) = reach A i k := by
  induction mm with
  | zero => rfl
  | succ mm ih =>
    ext l
    rw [← Nat.add_assoc, mem_reach_succ_iff hA, ih, ← mem_reach_succ_iff hA, heq]

/-- Irreducibility says that every index is reached at some time. -/
private theorem exists_mem_reach (hA : A.IsIrreducible) (i l : n) : ∃ k, l ∈ reach A i k := by
  obtain ⟨k, -, hk⟩ := (isIrreducible_iff_exists_pow_pos hA.nonneg).1 hA i l
  exact ⟨k, mem_reach.2 (hk.trans_le (pow_entrywiseLE_one_add_pow hA.nonneg k i l))⟩

/-- A reach sequence that has stabilised has already reached everything. -/
private theorem reach_eq_univ_of_succ_eq (hA : A.IsIrreducible) (i : n) {k : ℕ}
    (heq : reach A i (k + 1) = reach A i k) : reach A i k = Finset.univ := by
  refine Finset.eq_univ_iff_forall.2 fun l => ?_
  obtain ⟨mm, hm⟩ := exists_mem_reach hA i l
  have hsub : reach A i mm ⊆ reach A i (k + mm) :=
    reach_mono hA.nonneg i (Nat.le_add_left mm k)
  exact reach_add_eq hA.nonneg i heq mm ▸ hsub hm

/-- Before saturation, each step of the reach sequence gains at least one index. -/
private theorem reach_eq_univ_or_card (hA : A.IsIrreducible) (i : n) (k : ℕ) :
    reach A i k = Finset.univ ∨ k + 1 ≤ (reach A i k).card := by
  induction k with
  | zero => exact Or.inr (by rw [reach_zero, Finset.card_singleton])
  | succ k ih =>
    rcases ih with h | h
    · exact Or.inl (Finset.univ_subset_iff.1 (h ▸ reach_subset_succ hA.nonneg i k))
    by_cases heq : reach A i (k + 1) = reach A i k
    · exact Or.inl (heq.trans (reach_eq_univ_of_succ_eq hA i heq))
    refine Or.inr ?_
    have hss : reach A i k ⊂ reach A i (k + 1) :=
      ⟨reach_subset_succ hA.nonneg i k, fun hsub =>
        heq (Finset.Subset.antisymm hsub (reach_subset_succ hA.nonneg i k))⟩
    have := Finset.card_lt_card hss
    omega

/-- **The Wielandt positivity lemma**: for an irreducible nonnegative matrix on `N` indices,
`(1 + A) ^ (N - 1)` is entrywise positive.

Every positive entry of `(1 + A) ^ k` records a walk of length at most `k` in the pattern of `A`,
and the support of a row of `(1 + A) ^ k` grows by at least one index at every step until it is
everything, so `N - 1` steps suffice. This is the combinatorial kernel of the Perron–Frobenius
theorem below. -/
theorem IsIrreducible.entrywisePos_one_add_pow [Nonempty n] (hA : A.IsIrreducible) (i j : n) :
    0 < ((1 + A) ^ (Fintype.card n - 1)) i j := by
  have huniv : reach A i (Fintype.card n - 1) = Finset.univ := by
    rcases reach_eq_univ_or_card hA i (Fintype.card n - 1) with h | h
    · exact h
    refine Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) ?_)
    have hpos : 0 < Fintype.card n := Fintype.card_pos
    omega
  exact mem_reach.1 (huniv ▸ Finset.mem_univ j)

end Irreducible

/-! ### The Perron–Frobenius theorem for an irreducible matrix -/

section Perron

open scoped Matrix.Norms.L2Operator

variable [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

omit [DecidableEq n] in
/-- An entrywise positive matrix sends a nonzero nonnegative vector to a positive one. -/
private theorem mulVec_pos_of_entrywisePos {P : Matrix n n ℝ} (hP : ∀ i j, 0 < P i j)
    {w : n → ℝ} (hw : ∀ i, 0 ≤ w i) (hwne : w ≠ 0) (i : n) : 0 < (P *ᵥ w) i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hwne
  rw [mulVec_apply_eq_sum]
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hP i k).le (hw k))
    ⟨j, Finset.mem_univ j, mul_pos (hP i j) ((hw j).lt_of_ne' hj)⟩

/-- An eigenvector of `A` for `r` is an eigenvector of `(1 + A) ^ k` for `(1 + r) ^ k`. -/
private theorem mulVec_one_add_pow_of_mulVec_eq {z : n → ℝ} {r : ℝ} (h : A *ᵥ z = r • z) (k : ℕ) :
    ((1 + A) ^ k) *ᵥ z = (1 + r) ^ k • z := by
  have hstep : (1 + A) *ᵥ z = (1 + r) • z := by
    rw [add_mulVec, one_mulVec, h, add_smul, one_smul]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hstep, smul_smul, ← pow_succ]

/-- **Subinvariance.** The entrywise modulus of a complex eigenvector for an eigenvalue of maximal
modulus is a nonzero nonnegative real vector `z` with `ρ • z ≤ A *ᵥ z`, because the triangle
inequality applied to `μ v = A v` reads `|μ| |v| ≤ A |v|` entrywise. -/
private theorem exists_subinvariant [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) :
    ∃ z : n → ℝ, (∀ i, 0 ≤ z i) ∧ z ≠ 0 ∧
      ∀ i, (complexSpectralRadius A).toReal * z i ≤ (A *ᵥ z) i := by
  obtain ⟨μ, v, hv0, heig, hμ⟩ := exists_eigenvector_norm_eq_complexSpectralRadius A
  refine ⟨fun i => ‖v i‖, fun i => norm_nonneg _, ?_, fun i => ?_⟩
  · intro h
    exact hv0 (funext fun i => by simpa using congrFun h i)
  · have hrow : (complexify A *ᵥ v) i = ∑ j, ((A i j : ℝ) : ℂ) * v j := by
      simp [mulVec_apply_eq_sum]
    have hcalc : (complexSpectralRadius A).toReal * ‖v i‖ = ‖(complexify A *ᵥ v) i‖ := by
      rw [heig, ← hμ]
      simp
    rw [hcalc, hrow, mulVec_apply_eq_sum]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA i j)]

/-- **A positive subinvariant vector bounds the spectral radius from below**: if `u` is entrywise
positive and `t • u ≤ A *ᵥ u` for a nonnegative `t`, then `t ≤ ρ(A)`.

Iterating gives `t ^ k • u ≤ A ^ k *ᵥ u`, hence `t ^ k ≤ ‖A ^ k‖`, and Gelfand's formula finishes
it. -/
private theorem le_complexSpectralRadius_of_pos [Nonempty n] (hA : ∀ i j, 0 ≤ A i j) {t : ℝ}
    (ht : 0 ≤ t) {u : n → ℝ} (hu : ∀ i, 0 < u i) (hle : ∀ i, t * u i ≤ (A *ᵥ u) i) :
    t ≤ (complexSpectralRadius A).toReal := by
  have hiter : ∀ k : ℕ, ∀ i, t ^ k * u i ≤ ((A ^ k) *ᵥ u) i := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      have h1 : A *ᵥ ((t ^ k) • u) ≤ A *ᵥ ((A ^ k) *ᵥ u) :=
        EntrywiseNonneg.mulVec_mono hA (Pi.le_def.2 fun i => by simpa using ih i)
      intro i
      have h2 := Pi.le_def.1 h1 i
      rw [mulVec_smul] at h2
      have h3 : t ^ (k + 1) * u i ≤ t ^ k * (A *ᵥ u) i :=
        calc t ^ (k + 1) * u i = t ^ k * (t * u i) := by ring
          _ ≤ t ^ k * (A *ᵥ u) i := mul_le_mul_of_nonneg_left (hle i) (pow_nonneg ht k)
      have h4 : ((A ^ (k + 1)) *ᵥ u) i = (A *ᵥ ((A ^ k) *ᵥ u)) i := by
        rw [mulVec_mulVec, ← pow_succ']
      rw [h4]
      exact h3.trans (by simpa using h2)
  obtain ⟨i₀⟩ := ‹Nonempty n›
  have hune : u ≠ 0 := fun h => (hu i₀).ne' (congrFun h i₀)
  have hupos : 0 < ‖(WithLp.toLp 2 u : EuclideanSpace ℝ n)‖ :=
    norm_pos_iff.2 fun h => hune (by simpa using congrArg (WithLp.ofLp (p := 2)) h)
  have hnorm : ∀ k : ℕ, t ^ k ≤ ‖A ^ k‖ := by
    intro k
    have hcmp : ‖(WithLp.toLp 2 ((t ^ k) • u) : EuclideanSpace ℝ n)‖
        ≤ ‖(WithLp.toLp 2 ((A ^ k) *ᵥ u) : EuclideanSpace ℝ n)‖ := by
      refine norm_toLp_le_of_abs_le fun i => ?_
      have hlo : 0 ≤ t ^ k * u i := mul_nonneg (pow_nonneg ht k) (hu i).le
      rw [Pi.smul_apply, smul_eq_mul, abs_of_nonneg hlo, abs_of_nonneg (hlo.trans (hiter k i))]
      exact hiter k i
    have hsm : (WithLp.toLp 2 ((t ^ k) • u) : EuclideanSpace ℝ n)
        = (t ^ k) • (WithLp.toLp 2 u : EuclideanSpace ℝ n) := _root_.rfl
    rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht k)] at hcmp
    have hbd := l2_opNorm_mulVec (A ^ k) (WithLp.toLp 2 u)
    have := hcmp.trans hbd
    exact le_of_mul_le_mul_right (by linarith) hupos
  refine ge_of_tendsto (tendsto_pow_rpow_complexSpectralRadius A) ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  calc t = (t ^ k) ^ (1 / k : ℝ) := by
        rw [one_div, Real.pow_rpow_inv_natCast ht (by omega)]
    _ ≤ ‖A ^ k‖ ^ (1 / k : ℝ) :=
        Real.rpow_le_rpow (pow_nonneg ht k) (hnorm k) (by positivity)

/-- **The Perron–Frobenius theorem for an irreducible matrix** (Saad, *Iterative Methods for
Sparse Linear Systems*, Theorem 1.25, which the book states without proof): an irreducible
nonnegative real matrix on a nonempty index type has an entrywise *positive* eigenvector for its
spectral radius.

The eigenvector is the entrywise modulus of a complex eigenvector for an eigenvalue of maximal
modulus, which is subinvariant; the Wielandt positivity lemma
`Matrix.IsIrreducible.entrywisePos_one_add_pow` upgrades subinvariance to invariance, and then
nonnegativity to positivity. -/
theorem IsIrreducible.exists_pos_hasEigenvector_complexSpectralRadius [Nonempty n]
    (hA : A.IsIrreducible) :
    ∃ x : n → ℝ, (∀ i, 0 < x i) ∧ A *ᵥ x = (complexSpectralRadius A).toReal • x := by
  set ρ := (complexSpectralRadius A).toReal with hρdef
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
  set P : Matrix n n ℝ := (1 + A) ^ (Fintype.card n - 1) with hPdef
  have hPpos : ∀ i j, 0 < P i j := hA.entrywisePos_one_add_pow
  obtain ⟨z, hz0, hzne, hsub⟩ := exists_subinvariant hA.nonneg
  have hkey : A *ᵥ z = ρ • z := by
    by_contra hne
    have hw0 : ∀ i, 0 ≤ (A *ᵥ z - ρ • z) i := fun i => by
      simpa [sub_nonneg] using hsub i
    have hwne : A *ᵥ z - ρ • z ≠ 0 := fun h => hne (sub_eq_zero.mp h)
    have hupos : ∀ i, 0 < (P *ᵥ z) i := mulVec_pos_of_entrywisePos hPpos hz0 hzne
    have hcomm : P * A = A * P :=
      Commute.pow_left (Commute.add_left (Commute.one_left A) (Commute.refl A)) _
    have hPwEq : P *ᵥ (A *ᵥ z - ρ • z) = A *ᵥ (P *ᵥ z) - ρ • (P *ᵥ z) := by
      rw [mulVec_sub, mulVec_smul, mulVec_mulVec, hcomm, ← mulVec_mulVec]
    have hstrict : ∀ i, ρ * (P *ᵥ z) i < (A *ᵥ (P *ᵥ z)) i := by
      intro i
      have h := mulVec_pos_of_entrywisePos hPpos hw0 hwne i
      rw [hPwEq] at h
      simpa [sub_pos] using h
    set ε : ℝ := Finset.univ.inf' Finset.univ_nonempty
      (fun i => ((A *ᵥ (P *ᵥ z)) i - ρ * (P *ᵥ z) i) / (P *ᵥ z) i) with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef, Finset.lt_inf'_iff]
      exact fun i _ => div_pos (sub_pos.2 (hstrict i)) (hupos i)
    have hεle : ∀ i, (ρ + ε) * (P *ᵥ z) i ≤ (A *ᵥ (P *ᵥ z)) i := by
      intro i
      have h : ε ≤ ((A *ᵥ (P *ᵥ z)) i - ρ * (P *ᵥ z) i) / (P *ᵥ z) i :=
        Finset.inf'_le _ (Finset.mem_univ i)
      rw [le_div_iff₀ (hupos i)] at h
      have hexp : (ρ + ε) * (P *ᵥ z) i = ρ * (P *ᵥ z) i + ε * (P *ᵥ z) i := by ring
      rw [hexp]
      linarith
    have hbound := le_complexSpectralRadius_of_pos hA.nonneg (by positivity) hupos hεle
    rw [← hρdef] at hbound
    linarith
  refine ⟨z, fun i => ?_, hkey⟩
  have h1 : P *ᵥ z = (1 + ρ) ^ (Fintype.card n - 1) • z :=
    mulVec_one_add_pow_of_mulVec_eq hkey _
  have h2 : 0 < (P *ᵥ z) i := mulVec_pos_of_entrywisePos hPpos hz0 hzne i
  rw [h1] at h2
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  rcases (hz0 i).lt_or_eq with h | h
  · exact h
  · rw [← h, mul_zero] at h2
    exact absurd h2 (lt_irrefl 0)

/-- **The Perron eigenvalue of an irreducible matrix is geometrically simple**: the eigenspace of
`A` at its spectral radius, over the reals, has rank one (Saad, *Iterative Methods for Sparse
Linear Systems*, Theorem 1.25; the book says "simple", meaning algebraically simple, which is a
stronger statement not proved here).

If `w` is another eigenvector and `x` the positive Perron vector, then `t = sup_i (w i / x i)`
makes `t • x - w` a nonnegative eigenvector with a vanishing entry, so it is zero. -/
theorem IsIrreducible.finrank_eigenspace_complexSpectralRadius_eq_one [Nonempty n]
    (hA : A.IsIrreducible) :
    Module.finrank ℝ
        (Module.End.eigenspace A.mulVecLin (complexSpectralRadius A).toReal) = 1 := by
  set ρ := (complexSpectralRadius A).toReal with hρdef
  obtain ⟨x, hxpos, hx⟩ := hA.exists_pos_hasEigenvector_complexSpectralRadius
  have hxmem : x ∈ Module.End.eigenspace A.mulVecLin ρ := Module.End.mem_eigenspace_iff.2 hx
  have hxne : x ≠ 0 := fun h => (hxpos (Classical.arbitrary n)).ne' (congrFun h _)
  have hspan : Module.End.eigenspace A.mulVecLin ρ = ℝ ∙ x := by
    refine le_antisymm (fun w hw => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hxmem)
    have hwe : A *ᵥ w = ρ • w := Module.End.mem_eigenspace_iff.1 hw
    set t : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => w i / x i) with htdef
    have hle : ∀ i, w i ≤ t * x i := by
      intro i
      have h : w i / x i ≤ t := Finset.le_sup' (fun i => w i / x i) (Finset.mem_univ i)
      rwa [div_le_iff₀ (hxpos i)] at h
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := n))
      (fun i => w i / x i)
    have hzero : t * x i₀ - w i₀ = 0 := by
      have hx0 : x i₀ ≠ 0 := (hxpos i₀).ne'
      rw [← htdef] at hi₀
      rw [hi₀]
      field_simp
      ring
    have hnn : ∀ i, 0 ≤ (t • x - w) i := fun i => by
      simpa [sub_nonneg] using hle i
    have heig : A *ᵥ (t • x - w) = ρ • (t • x - w) := by
      rw [mulVec_sub, mulVec_smul, hx, hwe, smul_sub, smul_comm]
    by_cases hzz : t • x - w = 0
    · have : w = t • x := by
        have := sub_eq_zero.mp hzz
        rw [this]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    · exfalso
      have hpos := mulVec_pos_of_entrywisePos (hA.entrywisePos_one_add_pow) hnn hzz i₀
      rw [mulVec_one_add_pow_of_mulVec_eq heig] at hpos
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hpos
      rw [hzero] at hpos
      simp at hpos
  rw [hspan, finrank_span_singleton hxne]

end Perron

end Matrix
