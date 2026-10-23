import Numlib.Optimization.Quadratic.Secular.Vector
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Exact factorization solves for secular derivatives

The run records only factorization identities and primitive linear solves. Its
vectors and scalar outputs are subsequently identified with actual derivatives.
The derivative right-hand sides carry the minus sign from the differentiated
shifted equation.
-/

namespace QuadraticSecular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The exact primitive solves of a finite LDL-adjoint secular-derivative computation.
Triangularity and diagonal storage are unnecessary for correctness: only the
actual factorization and solve equations enter this generalized interface. -/
structure DerivativeFactorizationRun (H M : E →L[ℝ] E) (g : E) (τ : ℝ)
    (L D : E →L[ℝ] E) (s y w : ℕ → E) (α : ℕ → ℝ) (steps : ℕ) : Prop where
  factorization : H + τ • M = L.comp (D.comp L.adjoint)
  initial_left : L (y 0) = -g
  next_left : ∀ k < steps, L (y (k + 1)) = -(k + 1 : ℝ) • M (s k)
  diagonal_solve : ∀ k ≤ steps, D (w k) = y k
  adjoint_solve : ∀ k ≤ steps, L.adjoint (s k) = w k
  alpha_zero : α 0 = 1
  alpha_next : ∀ k < steps, α (k + 1) = 2 * ((2 * k + 3 : ℝ) / (k + 1)) * α k

namespace DerivativeFactorizationRun
variable {H M : E →L[ℝ] E} {g : E} {τ : ℝ} {L D : E →L[ℝ] E}
  {s y w : ℕ → E} {α : ℕ → ℝ} {steps : ℕ}
  (h : DerivativeFactorizationRun H M g τ L D s y w α steps)

include h

/-- The initial primitive solves give the actual shifted system. -/
theorem initial_system : (H + τ • M) (s 0) = -g := by
  rw [h.factorization, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    h.adjoint_solve 0 (Nat.zero_le _), h.diagonal_solve 0 (Nat.zero_le _), h.initial_left]

/-- The derivative primitive solves give the differentiated shifted system. -/
theorem next_system {k : ℕ} (hk : k < steps) :
    (H + τ • M) (s (k + 1)) = -(k + 1 : ℝ) • M (s k) := by
  rw [h.factorization, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    h.adjoint_solve (k + 1) hk, h.diagonal_solve (k + 1) hk, h.next_left k hk]

/-- The computed scalar coefficients equal the explicit factorial coefficients. -/
theorem alpha_eq {k : ℕ} (hk : k ≤ steps) : α k = derivativeCoefficient k := by
  induction k with
  | zero => rw [h.alpha_zero, derivativeCoefficient_zero]
  | succ k ih =>
    rw [h.alpha_next k (by omega), ih (by omega), derivativeCoefficient_succ]

/-- The odd scalar output is the contraction of consecutive computed solution vectors. -/
theorem odd_value (hM : M.toLinearMap.IsSymmetric) {k : ℕ} (hk : k < steps) :
    -(2 * α k / (k + 1)) * inner ℝ (y (k + 1)) (w (k + 1)) =
      2 * α k * inner ℝ (s k) (M (s (k + 1))) := by
  have he : inner ℝ (y (k + 1)) (w (k + 1)) =
      -(k + 1 : ℝ) * inner ℝ (s k) (M (s (k + 1))) := by
    rw [← h.adjoint_solve (k + 1) hk, L.adjoint_inner_right,
      h.next_left k hk, real_inner_smul_left]
    exact congrArg (fun a : ℝ => -(k + 1 : ℝ) * a) (hM (s k) (s (k + 1)))
  rw [he]
  have hk0 : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp

end DerivativeFactorizationRun

namespace PencilBasis
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

omit [Fintype ι] in
/-- A factorization run computes the actual inverse-solution derivatives at every computed order. -/
theorem factorizationRun_vector_eq [Finite ι] [FiniteDimensional ℝ E]
    {g : E} {τ : ℝ} {L D : E →L[ℝ] E} {s y w : ℕ → E} {α : ℕ → ℝ} {steps : ℕ}
    (hz : ∀ i, τ + B.eigenvalue i ≠ 0)
    (h : DerivativeFactorizationRun H M g τ L D s y w α steps)
    {k : ℕ} (hk : k ≤ steps) : s k = iteratedDeriv k (solution H M g) τ := by
  have hInv := B.shifted_invertible τ hz
  induction k with
  | zero =>
    apply hInv.injective
    rw [h.initial_system]
    change -g = (H + τ • M) (-((H + τ • M).inverse g))
    rw [map_neg, hInv.self_apply_inverse]
  | succ k ih =>
    apply hInv.injective
    rw [h.next_system (by omega), B.shifted_iteratedDeriv_succ g k hz, ih (by omega)]

omit [Fintype ι] in
/-- Every odd and even output of the primitive factorization run is the true secular derivative. -/
theorem factorizationRun_correct [Finite ι] [FiniteDimensional ℝ E]
    {g : E} {τ : ℝ} {L D : E →L[ℝ] E} {s y w : ℕ → E} {α : ℕ → ℝ} {steps : ℕ}
    (hM : M.toLinearMap.IsSymmetric) (hz : ∀ i, τ + B.eigenvalue i ≠ 0)
    (h : DerivativeFactorizationRun H M g τ L D s y w α steps)
    {k : ℕ} (hk : k < steps) :
    iteratedDeriv (2 * k + 1) (secular H M g) τ =
      -(2 * α k / (k + 1)) * inner ℝ (y (k + 1)) (w (k + 1)) ∧
    iteratedDeriv (2 * k + 1) (secular H M g) τ =
      2 * α k * inner ℝ (s k) (M (s (k + 1))) ∧
    iteratedDeriv (2 * k + 2) (secular H M g) τ =
      α (k + 1) * inner ℝ (s (k + 1)) (M (s (k + 1))) := by
  have hodd : iteratedDeriv (2 * k + 1) (secular H M g) τ =
      2 * α k * inner ℝ (s k) (M (s (k + 1))) := by
    rw [h.alpha_eq (by omega), B.factorizationRun_vector_eq hz h (by omega),
      B.factorizationRun_vector_eq hz h (by omega), B.iteratedDeriv_secular_odd g k hz]
  refine ⟨hodd.trans (h.odd_value hM hk).symm, hodd, ?_⟩
  rw [h.alpha_eq hk, B.factorizationRun_vector_eq hz h hk,
    B.iteratedDeriv_secular_even g k hz]

omit [Fintype ι] in
/-- The exact factorization admits an actual primitive-solve run of any finite length. -/
theorem exists_factorizationRun [Finite ι] [FiniteDimensional ℝ E]
    (g : E) {τ : ℝ} (hz : ∀ i, τ + B.eigenvalue i ≠ 0) (L D : E →L[ℝ] E)
    (hfac : H + τ • M = L.comp (D.comp L.adjoint)) (steps : ℕ) :
    ∃ s y w : ℕ → E, ∃ α : ℕ → ℝ,
      DerivativeFactorizationRun H M g τ L D s y w α steps := by
  let s : ℕ → E := fun k => iteratedDeriv k (solution H M g) τ
  let w : ℕ → E := fun k => L.adjoint (s k)
  let y : ℕ → E := fun k => D (w k)
  refine ⟨s, y, w, derivativeCoefficient, hfac, ?_, ?_, fun _ _ => rfl,
    fun _ _ => rfl, derivativeCoefficient_zero, fun k _ => derivativeCoefficient_succ k⟩
  · change (L.comp (D.comp L.adjoint)) (solution H M g τ) = -g
    rw [← hfac]
    have hInv := B.shifted_invertible τ hz
    unfold solution
    rw [map_neg, hInv.self_apply_inverse]
  · intro k _
    change (L.comp (D.comp L.adjoint)) (iteratedDeriv (k + 1) (solution H M g) τ) = _
    rw [← hfac]
    exact B.shifted_iteratedDeriv_succ g k hz

end PencilBasis
end QuadraticSecular

namespace QuadraticSecular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The primitive solves actually requested for the first `orders` derivatives.
When the last requested derivative is odd, no final adjoint solve or coefficient
update is assumed. -/
structure FiniteDerivativeFactorizationRun (H M : E →L[ℝ] E) (g : E) (τ : ℝ)
    (L D : E →L[ℝ] E) (s y w : ℕ → E) (α : ℕ → ℝ) (orders : ℕ) : Prop where
  factorization : H + τ • M = L.comp (D.comp L.adjoint)
  initial_left : L (y 0) = -g
  next_left : ∀ k, 2 * k + 1 ≤ orders → L (y (k + 1)) = -(k + 1 : ℝ) • M (s k)
  diagonal_solve : ∀ k, 2 * k ≤ orders + 1 → D (w k) = y k
  adjoint_solve : ∀ k, 2 * k ≤ orders → L.adjoint (s k) = w k
  alpha_zero : α 0 = 1
  alpha_next : ∀ k, 2 * k + 2 ≤ orders →
    α (k + 1) = 2 * ((2 * k + 3 : ℝ) / (k + 1)) * α k

namespace FiniteDerivativeFactorizationRun
variable {H M : E →L[ℝ] E} {g : E} {τ : ℝ} {L D : E →L[ℝ] E}
  {s y w : ℕ → E} {α : ℕ → ℝ} {orders : ℕ}
  (h : FiniteDerivativeFactorizationRun H M g τ L D s y w α orders)
include h

omit h in
/-- A completed primitive run restricts to exactly the solves the finite algorithm requests. -/
theorem ofRun (hf : DerivativeFactorizationRun H M g τ L D s y w α orders) :
    FiniteDerivativeFactorizationRun H M g τ L D s y w α orders :=
  ⟨hf.factorization, hf.initial_left, fun _ hk => hf.next_left _ (by omega),
    fun _ hk => hf.diagonal_solve _ (by omega),
    fun _ hk => hf.adjoint_solve _ (by omega), hf.alpha_zero,
    fun _ hk => hf.alpha_next _ (by omega)⟩

/-- The finite algorithm's initial solves give the shifted system. -/
theorem initial_system : (H + τ • M) (s 0) = -g := by
  rw [h.factorization, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    h.adjoint_solve 0 (by omega), h.diagonal_solve 0 (by omega), h.initial_left]

/-- Each computed even-order vector satisfies the differentiated system. -/
theorem next_system {k : ℕ} (hk : 2 * k + 2 ≤ orders) :
    (H + τ • M) (s (k + 1)) = -(k + 1 : ℝ) • M (s k) := by
  rw [h.factorization, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    h.adjoint_solve (k + 1) (by omega), h.diagonal_solve (k + 1) (by omega),
    h.next_left k (by omega)]

/-- The finite coefficient updates give the actual factorial coefficients where requested. -/
theorem alpha_eq {k : ℕ} (hk : 2 * k ≤ orders) : α k = derivativeCoefficient k := by
  induction k with
  | zero => rw [h.alpha_zero, derivativeCoefficient_zero]
  | succ k ih =>
    rw [h.alpha_next k (by omega), ih (by omega), derivativeCoefficient_succ]

end FiniteDerivativeFactorizationRun

namespace PencilBasis
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

omit [Fintype ι] in
/-- A nonsingular finite-dimensional pencil factorization has injective actual solve factors. -/
theorem factorization_factors_injective [Finite ι] [FiniteDimensional ℝ E]
    {τ : ℝ} (hz : ∀ i, τ + B.eigenvalue i ≠ 0) {L D : E →L[ℝ] E}
    (hfac : H + τ • M = L.comp (D.comp L.adjoint)) :
    Function.Injective L ∧ Function.Injective D := by
  have hInv := B.shifted_invertible τ hz
  have hLs : Function.Surjective L := by
    intro v
    obtain ⟨u, hu⟩ := hInv.surjective v
    exact ⟨D (L.adjoint u), by simpa only [hfac, ContinuousLinearMap.comp_apply] using hu⟩
  have hLi : Function.Injective L := LinearMap.injective_iff_surjective.mpr hLs
  have hDs : Function.Surjective D := by
    intro v
    obtain ⟨u, hu⟩ := hInv.surjective (L v)
    exact ⟨L.adjoint u, hLi (by
      simpa only [hfac, ContinuousLinearMap.comp_apply] using hu)⟩
  exact ⟨hLi, (LinearMap.injective_iff_surjective (f := D.toLinearMap)).mpr hDs⟩

omit [Fintype ι] in
/-- Every vector actually computed by the finite algorithm is the corresponding true derivative. -/
theorem finiteFactorizationRun_vector_eq [Finite ι] [FiniteDimensional ℝ E]
    {g : E} {τ : ℝ} {L D : E →L[ℝ] E} {s y w : ℕ → E} {α : ℕ → ℝ} {orders : ℕ}
    (hz : ∀ i, τ + B.eigenvalue i ≠ 0)
    (h : FiniteDerivativeFactorizationRun H M g τ L D s y w α orders)
    {k : ℕ} (hk : 2 * k ≤ orders) : s k = iteratedDeriv k (solution H M g) τ := by
  have hInv := B.shifted_invertible τ hz
  induction k with
  | zero =>
    apply hInv.injective
    rw [h.initial_system]
    change -g = (H + τ • M) (-((H + τ • M).inverse g))
    rw [map_neg, hInv.self_apply_inverse]
  | succ k ih =>
    apply hInv.injective
    rw [h.next_system (by omega), B.shifted_iteratedDeriv_succ g k hz, ih (by omega)]

omit [Fintype ι] in
/-- The last odd branch's computed intermediate vector is the adjoint transform of
an actual derivative, even though the algorithm need not compute that derivative vector. -/
theorem finiteFactorizationRun_intermediate_eq [Finite ι] [FiniteDimensional ℝ E]
    {g : E} {τ : ℝ} {L D : E →L[ℝ] E} {s y w : ℕ → E} {α : ℕ → ℝ} {orders : ℕ}
    (hz : ∀ i, τ + B.eigenvalue i ≠ 0)
    (h : FiniteDerivativeFactorizationRun H M g τ L D s y w α orders)
    {k : ℕ} (hk : 2 * k + 1 ≤ orders) :
    w (k + 1) = L.adjoint (iteratedDeriv (k + 1) (solution H M g) τ) := by
  obtain ⟨hL, hD⟩ := B.factorization_factors_injective hz h.factorization
  apply hD
  apply hL
  rw [h.diagonal_solve (k + 1) (by omega), h.next_left k hk]
  change _ = (L.comp (D.comp L.adjoint)) _
  rw [← h.factorization, B.shifted_iteratedDeriv_succ g k hz,
    B.finiteFactorizationRun_vector_eq hz h (by omega)]

omit [Fintype ι] in
/-- Every requested odd output is the genuine secular derivative, including the
last odd branch where no adjoint solve is performed. -/
theorem finiteFactorizationRun_odd [Finite ι] [FiniteDimensional ℝ E]
    {g : E} {τ : ℝ} {L D : E →L[ℝ] E} {s y w : ℕ → E} {α : ℕ → ℝ} {orders : ℕ}
    (hM : M.toLinearMap.IsSymmetric) (hz : ∀ i, τ + B.eigenvalue i ≠ 0)
    (h : FiniteDerivativeFactorizationRun H M g τ L D s y w α orders)
    {k : ℕ} (hk : 2 * k + 1 ≤ orders) :
    iteratedDeriv (2 * k + 1) (secular H M g) τ =
      -(2 * α k / (k + 1)) * inner ℝ (y (k + 1)) (w (k + 1)) := by
  have he : inner ℝ (y (k + 1)) (w (k + 1)) = -(k + 1 : ℝ) *
      inner ℝ (iteratedDeriv k (solution H M g) τ)
        (M (iteratedDeriv (k + 1) (solution H M g) τ)) := by
    rw [B.finiteFactorizationRun_intermediate_eq hz h hk, L.adjoint_inner_right,
      h.next_left k hk, real_inner_smul_left,
      B.finiteFactorizationRun_vector_eq hz h (by omega)]
    exact congrArg (fun a : ℝ => -(k + 1 : ℝ) * a)
      (hM (iteratedDeriv k (solution H M g) τ) (iteratedDeriv (k + 1) (solution H M g) τ))
  rw [B.iteratedDeriv_secular_odd g k hz, he, h.alpha_eq (by omega)]
  have hk0 : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp

omit [Fintype ι] in
/-- Every requested even output is the genuine secular derivative. -/
theorem finiteFactorizationRun_even [Finite ι] [FiniteDimensional ℝ E]
    {g : E} {τ : ℝ} {L D : E →L[ℝ] E} {s y w : ℕ → E} {α : ℕ → ℝ} {orders : ℕ}
    (hz : ∀ i, τ + B.eigenvalue i ≠ 0)
    (h : FiniteDerivativeFactorizationRun H M g τ L D s y w α orders)
    {k : ℕ} (hk : 2 * k + 2 ≤ orders) :
    iteratedDeriv (2 * k + 2) (secular H M g) τ =
      α (k + 1) * inner ℝ (s (k + 1)) (M (s (k + 1))) := by
  rw [h.alpha_eq (by omega), B.finiteFactorizationRun_vector_eq hz h (by omega),
    B.iteratedDeriv_secular_even g k hz]

omit [Fintype ι] in
/-- An actual finite algorithm run exists for every exact nonsingular factorization. -/
theorem exists_finiteFactorizationRun [Finite ι] [FiniteDimensional ℝ E]
    (g : E) {τ : ℝ} (hz : ∀ i, τ + B.eigenvalue i ≠ 0) (L D : E →L[ℝ] E)
    (hfac : H + τ • M = L.comp (D.comp L.adjoint)) (orders : ℕ) :
    ∃ s y w : ℕ → E, ∃ α : ℕ → ℝ,
      FiniteDerivativeFactorizationRun H M g τ L D s y w α orders := by
  obtain ⟨s, y, w, α, h⟩ := B.exists_factorizationRun g hz L D hfac orders
  exact ⟨s, y, w, α, FiniteDerivativeFactorizationRun.ofRun h⟩

omit [Fintype ι] in
/-- The algorithm's initial metric pairing is the actual secular value. -/
theorem finiteFactorizationRun_initial_value [Finite ι] [FiniteDimensional ℝ E]
    {g : E} {τ : ℝ} {L D : E →L[ℝ] E} {s y w : ℕ → E} {α : ℕ → ℝ} {orders : ℕ}
    (hz : ∀ i, τ + B.eigenvalue i ≠ 0)
    (h : FiniteDerivativeFactorizationRun H M g τ L D s y w α orders) :
    secular H M g τ = inner ℝ (s 0) (M (s 0)) := by
  rw [B.finiteFactorizationRun_vector_eq hz h (by omega : 2 * 0 ≤ orders)]
  exact real_inner_comm _ _

omit [Fintype ι] in
/-- With a Cholesky factorization the odd output is minus beta times the squared
intermediate norm. There is no additional factor of two. -/
theorem finiteFactorizationRun_cholesky_odd [Finite ι] [FiniteDimensional ℝ E]
    {g : E} {τ : ℝ} {L D : E →L[ℝ] E} {s y w : ℕ → E} {α : ℕ → ℝ} {orders : ℕ}
    (hM : M.toLinearMap.IsSymmetric) (hz : ∀ i, τ + B.eigenvalue i ≠ 0)
    (h : FiniteDerivativeFactorizationRun H M g τ L D s y w α orders)
    (hD : D = ContinuousLinearMap.id ℝ E) {k : ℕ} (hk : 2 * k + 1 ≤ orders) :
    iteratedDeriv (2 * k + 1) (secular H M g) τ =
      -(2 * α k / (k + 1)) * ‖y (k + 1)‖ ^ 2 := by
  have hw : w (k + 1) = y (k + 1) := by
    simpa only [hD, ContinuousLinearMap.id_apply] using
      h.diagonal_solve (k + 1) (by omega)
  rw [B.finiteFactorizationRun_odd hM hz h hk, hw, real_inner_self_eq_norm_sq]

end PencilBasis
end QuadraticSecular
