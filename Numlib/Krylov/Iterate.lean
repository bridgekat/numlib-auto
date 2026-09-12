import Mathlib.Algebra.Polynomial.Module.AEval
import Numlib.Krylov.Arnoldi
import Numlib.LinearSolve.Projection.Optimality

/-!
# Krylov iterates: specifications

The canonical specifications of Krylov subspace methods for `A x = b` started at `x₀`, with `r₀ = b
- A x₀` and `𝒦_m = 𝒦_m(A, r₀)`, together with their polynomial characterizations and their behaviour
at the grade of `r₀`.

## Main definitions

* `Krylov.IsMinResidualIterate A b x₀ m x`: `x ∈ x₀ + 𝒦_m` minimizes the residual (GMRES, MINRES, CR,
  GCR, ORTHOMIN/ORTHODIR full versions, MINRES-QLP on nonsingular systems);
* `Krylov.IsGalerkinIterate A b x₀ m x`: `x ∈ x₀ + 𝒦_m`, `r ⟂ 𝒦_m` (FOM, CG, D-Lanczos, the Lanczos
  method);
* `Krylov.IsMinErrorIterate A xstar x₀ m x`: minimal Euclidean error `‖xstar - x‖` over `x₀ + A
  𝒦_m(A, A (xstar - x₀))` (SYMMLQ; CGNE / Craig on `A Aᵀ`);
* `Krylov.IsMinNormMinResidualIterate A b x₀ m x`: least norm among the minimal-residual iterates
  (MINRES-QLP), which is what pins the iterate down on a singular system.

## Main statements

* `Krylov.exists_residual_poly`, `Krylov.exists_mem_of_residual_poly`,
  `Krylov.IsMinResidualIterate.norm_residual_eq_iInf` and
  `Krylov.IsGalerkinIterate.energyNorm_error_eq_iInf`: the polynomial characterizations
  ([saad2003iterative] Lemma 6.28 and Lemma 6.31);
* `Krylov.IsGalerkinIterate.residual_mem_span`: the Galerkin residual is a multiple of the next
  Arnoldi vector ([saad2003iterative] Prop 6.7);
* `Krylov.IsMinResidualIterate.apply_eq_of_grade_le`, `Krylov.IsGalerkinIterate.apply_eq_of_grade_le` and
  `Krylov.grade_le_of_apply_eq`: lucky breakdown and exactness at the grade ([saad2003iterative]
  Prop 6.10);
* `Krylov.existsUnique_isMinNormMinResidualIterate`: the MINRES-QLP iterate is well defined with no
  hypothesis on `A`;
* `Krylov.norm_le_of_apply_eq`: an exact Krylov solution of a compatible symmetric system is the
  minimum-norm solution (core of [choi2006iterative] Thm 2.25).
-/

open Polynomial Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-- Minimal-residual Krylov iterate at step `m` (GMRES / MINRES / CR specification). -/
abbrev IsMinResidualIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsMinResidual A b x₀ (subspace A (b - A x₀) m) x

/-- Galerkin Krylov iterate at step `m` (FOM / CG / Lanczos-method specification). -/
abbrev IsGalerkinIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsGalerkin A b x₀ (subspace A (b - A x₀) m) x

/-- Minimal-error Krylov iterate at step `m` (SYMMLQ / CGNE specification): minimal `‖x* - x‖` over
`x₀ + A 𝒦_m(A, r₀)` with `r₀ = A (x* - x₀)` (`= b - A x₀` when `A x* = b`). The target `x*` is
explicit so that the specification is meaningful for singular `A`. -/
abbrev IsMinErrorIterate (A : E →ₗ[𝕜] E) (xstar x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsMinError xstar x₀ ((subspace A (A (xstar - x₀)) m).map A) x

section PolynomialGlue

/-- `deg (X * g) ≤ m` whenever `deg g < m`. -/
private theorem degree_X_mul_le {g : 𝕜[X]} {m : ℕ} (hg : g.degree < (m : WithBot ℕ)) :
    (X * g).degree ≤ (m : WithBot ℕ) := by
  rcases eq_or_ne g 0 with rfl | h0
  · simp
  rw [degree_eq_natDegree h0] at hg
  have hn : g.natDegree < m := by exact_mod_cast hg
  rw [degree_mul, degree_X, degree_eq_natDegree h0,
    show (1 : WithBot ℕ) + (g.natDegree : WithBot ℕ) = ((1 + g.natDegree : ℕ) : WithBot ℕ) by
      push_cast; ring]
  exact_mod_cast (by omega : 1 + g.natDegree ≤ m)

/-- Conversely `deg g < m` whenever `deg (X * g) ≤ m`. -/
private theorem degree_lt_of_degree_X_mul_le {g : 𝕜[X]} {m : ℕ}
    (h : (X * g).degree ≤ (m : WithBot ℕ)) : g.degree < (m : WithBot ℕ) := by
  rcases eq_or_ne g 0 with rfl | h0
  · simp
  rw [degree_mul, degree_X, degree_eq_natDegree h0,
    show (1 : WithBot ℕ) + (g.natDegree : WithBot ℕ) = ((1 + g.natDegree : ℕ) : WithBot ℕ) by
      push_cast; ring] at h
  have hn : 1 + g.natDegree ≤ m := by exact_mod_cast h
  rw [degree_eq_natDegree h0]
  exact_mod_cast (by omega : g.natDegree < m)

/-- `(1 - X g)(A) v = v - A (g(A) v)`. -/
private theorem aeval_one_sub_X_mul (A : E →ₗ[𝕜] E) (g : 𝕜[X]) (v : E) :
    aeval A (1 - X * g) v = v - A (aeval A g v) := by
  simp [Module.End.mul_apply]

/-- Polynomials in `A` commute with `A`. -/
private theorem aeval_apply_comm (A : E →ₗ[𝕜] E) (p : 𝕜[X]) (u : E) :
    aeval A p (A u) = A (aeval A p u) := by
  have h1 : aeval A p (A u) = (aeval A p * A) u := rfl
  have h2 : A (aeval A p u) = (A * aeval A p) u := rfl
  rw [h1, h2, show (aeval A p * A) = aeval A (p * X) by rw [map_mul, aeval_X],
    show (A * aeval A p) = aeval A (X * p) by rw [map_mul, aeval_X], mul_comm]

/-- The constant polynomial `1` is a residual polynomial for every `m`.  Named apart from Mathlib's
`Polynomial.degree_one_le`, which is the same bound at `m = 0`. -/
private theorem degree_one_le_natCast (m : ℕ) : (1 : 𝕜[X]).degree ≤ (m : WithBot ℕ) :=
  Polynomial.degree_one_le.trans (by exact_mod_cast Nat.zero_le m)

end PolynomialGlue

variable {A : E →ₗ[𝕜] E} {b x₀ : E} {m : ℕ} {x : E}

/-- Residual polynomials: for `x ∈ x₀ + 𝒦_m(A, r₀)` there is `p` with `deg p ≤ m`, `p 0 = 1` and `b
- A x = p(A) r₀`. -/
theorem exists_residual_poly (hx : x - x₀ ∈ subspace A (b - A x₀) m) :
    ∃ p : 𝕜[X], p.degree ≤ m ∧ p.eval 0 = 1 ∧ b - A x = aeval A p (b - A x₀) := by
  obtain ⟨g, hg, hgx⟩ := (mem_subspace_iff_exists_aeval A (b - A x₀)).1 hx
  refine ⟨1 - X * g, ?_, by simp, ?_⟩
  · exact le_trans (degree_sub_le _ _) (max_le (degree_one_le_natCast m) (degree_X_mul_le hg))
  · rw [aeval_one_sub_X_mul, hgx, residual_eq_sub_apply_sub A b x₀ x]

/-- Conversely every such `p` arises from some `x ∈ x₀ + 𝒦_m`. -/
theorem exists_mem_of_residual_poly (p : 𝕜[X]) (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) :
    ∃ x, x - x₀ ∈ subspace A (b - A x₀) m ∧ b - A x = aeval A p (b - A x₀) := by
  obtain ⟨g, hg⟩ : X ∣ (1 - p) := by
    rw [X_dvd_iff, coeff_sub, coeff_one_zero, coeff_zero_eq_eval_zero, hp0, sub_self]
  have hpg : p = 1 - X * g := by rw [← hg]; ring
  have hgdeg : g.degree < (m : WithBot ℕ) := by
    refine degree_lt_of_degree_X_mul_le (m := m) ?_
    rw [← hg]
    exact le_trans (degree_sub_le _ _) (max_le (degree_one_le_natCast m) hp)
  refine ⟨x₀ + aeval A g (b - A x₀), ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact aeval_apply_mem_subspace A (b - A x₀) hgdeg
  rw [hpg, aeval_one_sub_X_mul, residual_eq_sub_apply_sub A b x₀ (x₀ + aeval A g (b - A x₀)),
    add_sub_cancel_left]

/-- The residual of any `x ∈ x₀ + 𝒦_m` lies in `𝒦_{m+1}`. -/
theorem residual_mem_subspace_succ (hx : x - x₀ ∈ subspace A (b - A x₀) m) :
    b - A x ∈ subspace A (b - A x₀) (m + 1) := by
  rw [residual_eq_sub_apply_sub A b x₀ x]
  refine Submodule.sub_mem _ ?_ (map_subspace_le A (b - A x₀) m (Submodule.mem_map_of_mem hx))
  exact self_mem_subspace A (b - A x₀) m.succ_pos

section MinResidual

/-- A minimal-residual iterate always exists. -/
theorem exists_isMinResidualIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) :
    ∃ x, IsMinResidualIterate A b x₀ m x :=
  exists_isMinResidual b x₀ _

/-- With `A` injective the minimal-residual iterate at step `m` exists and is unique. Existence
holds for every `A` (`exists_isMinResidualIterate`), since the minimal residual is the part of `r₀`
orthogonal to `A 𝒦_m`; injectivity is what makes the *iterate* unique and not merely its residual.
-/
theorem existsUnique_isMinResidualIterate_of_injective (hA : Function.Injective A) (b x₀ : E)
    (m : ℕ) : ∃! x, IsMinResidualIterate A b x₀ m x :=
  existsUnique_isMinResidual_of_injOn b x₀ _ hA.injOn

namespace IsMinResidualIterate

/-- The minimal-residual iterate beats every competitor polynomial: `‖b - A x‖ ≤ ‖p(A) r₀‖` for each
`p` of degree at most `m` with `p 0 = 1`. Every such `p` is the residual polynomial of some point of
`x₀ + 𝒦_m` (`exists_mem_of_residual_poly`), over which `x` minimizes. This is the half of
`norm_residual_eq_iInf` that convergence proofs use: exhibit one polynomial small on the spectrum
and its bound transfers to the residual. -/
theorem norm_residual_le_norm_aeval (hx : IsMinResidualIterate A b x₀ m x) (p : 𝕜[X])
    (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) : ‖b - A x‖ ≤ ‖aeval A p (b - A x₀)‖ := by
  obtain ⟨y, hy, hres⟩ := exists_mem_of_residual_poly (A := A) (b := b) (x₀ := x₀) p hp hp0
  rw [← hres]
  exact hx.min y hy

/-- [saad2003iterative], Lemma 6.31: `‖r_m‖ = min {‖p(A) r₀‖ : deg p ≤ m, p 0 = 1}`. -/
theorem norm_residual_eq_iInf (hx : IsMinResidualIterate A b x₀ m x) :
    ‖b - A x‖ = ⨅ p : {p : 𝕜[X] // p.degree ≤ m ∧ p.eval 0 = 1}, ‖aeval A p.1 (b - A x₀)‖ := by
  have : Nonempty {p : 𝕜[X] // p.degree ≤ (m : WithBot ℕ) ∧ p.eval 0 = 1} :=
    ⟨⟨1, degree_one_le_natCast m, by simp⟩⟩
  have hbdd : BddBelow (Set.range
      fun p : {p : 𝕜[X] // p.degree ≤ (m : WithBot ℕ) ∧ p.eval 0 = 1} =>
        ‖aeval A p.1 (b - A x₀)‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact norm_nonneg _
  refine le_antisymm (le_ciInf fun p => hx.norm_residual_le_norm_aeval p.1 p.2.1 p.2.2) ?_
  obtain ⟨p, hp, hp0, hres⟩ := exists_residual_poly hx.mem
  rw [hres]
  exact ciInf_le hbdd ⟨p, hp, hp0⟩

/-- Residual norms are nonincreasing in `m`. -/
theorem norm_residual_antitone {x : ℕ → E} (hx : ∀ k, IsMinResidualIterate A b x₀ k (x k)) :
    Antitone fun k => ‖b - A (x k)‖ :=
  fun k l hkl => (hx k).norm_residual_le (hx l) (subspace_mono A (b - A x₀) hkl)

/-- Lucky breakdown ([saad2003iterative], Prop 6.10): at `m ≥ grade` the minimal-residual iterate is
exact provided `A` is injective on `𝒦_grade`. -/
theorem apply_eq_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hx : IsMinResidualIterate A b x₀ m x) (hm : grade A (b - A x₀) ≤ m)
    (hinj : Set.InjOn A (subspace A (b - A x₀) (grade A (b - A x₀)))) : A x = b := by
  have hKg : subspace A (b - A x₀) m = subspace A (b - A x₀) (grade A (b - A x₀)) :=
    subspace_eq_of_grade_le A (b - A x₀) hm
  have hinvt : subspace A (b - A x₀) m ∈ Module.End.invtSubmodule A := by
    rw [hKg]; exact subspace_grade_mem_invtSubmodule A (b - A x₀)
  have hres : ∀ z ∈ subspace A (b - A x₀) m, A z ∈ subspace A (b - A x₀) m :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hinvt
  have hinj' : Set.InjOn A (subspace A (b - A x₀) m : Set E) := by rw [hKg]; exact hinj
  set f : subspace A (b - A x₀) m →ₗ[𝕜] subspace A (b - A x₀) m := A.restrict hres with hf
  have hval : ∀ z : subspace A (b - A x₀) m, ((f z : subspace A (b - A x₀) m) : E) = A (z : E) :=
    fun z => rfl
  have hfinj : Function.Injective f := by
    intro z w hzw
    exact Subtype.ext (hinj' z.2 w.2 (by rw [← hval z, ← hval w, hzw]))
  have hr₀ : b - A x₀ ∈ subspace A (b - A x₀) m := by
    rw [hKg, subspace_grade_eq_fullSubspace]
    exact Submodule.subset_span ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hfinj) ⟨b - A x₀, hr₀⟩
  refine hx.apply_eq_of_exists (y := x₀ + (z : E)) (by simp) ?_
  have hAz : A (z : E) = b - A x₀ := by rw [← hval z, hz]
  rw [map_add, hAz]
  abel

/-- The residual is orthogonal to `A 𝒦_m` (Petrov–Galerkin with `L = A 𝒦_m`). -/
theorem residual_mem_orthogonal (hx : IsMinResidualIterate A b x₀ m x) :
    b - A x ∈ ((subspace A (b - A x₀) m).map A)ᗮ :=
  hx.isPetrovGalerkin.orth

end IsMinResidualIterate

/-- A nonzero annihilating polynomial of degree at most `m` bounds the grade by `m`. -/
theorem grade_le_of_aeval_eq_zero {v : E} [FiniteDimensional 𝕜 (fullSubspace A v)]
    {s : 𝕜[X]} (hs : s ≠ 0) (hdeg : s.natDegree ≤ m) (h0 : aeval A s v = 0) :
    grade A v ≤ m := by
  have hc : s.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hs
  have hCne : (C s.leadingCoeff⁻¹ : 𝕜[X]) ≠ 0 := by simpa using inv_ne_zero hc
  have hXs : (X ^ (m - s.natDegree) * s : 𝕜[X]) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) hs
  refine (grade_le_iff A v).2 ((pow_apply_mem_subspace_iff_exists_monic A v m).2
    ⟨C s.leadingCoeff⁻¹ * (X ^ (m - s.natDegree) * s), ?_, ?_, ?_⟩)
  · have hlc : (C s.leadingCoeff⁻¹ * (X ^ (m - s.natDegree) * s)).leadingCoeff = 1 := by
      rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow, leadingCoeff_X,
        one_pow, one_mul, inv_mul_cancel₀ hc]
    exact hlc
  · rw [natDegree_mul hCne hXs, natDegree_C, zero_add,
      natDegree_mul (pow_ne_zero _ X_ne_zero) hs, natDegree_pow, natDegree_X, mul_one]
    omega
  · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h0, map_zero, map_zero]

/-- Converse of lucky breakdown ([saad2003iterative], Prop 6.10 ⇐, P-6.13): an exact solution in `x₀
+ 𝒦_m` forces `grade ≤ m`.  No injectivity is needed: `r₀ = A q(A) r₀` gives the annihilator `1 - X
q`. -/
theorem grade_le_of_apply_eq [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hx : x - x₀ ∈ subspace A (b - A x₀) m) (hAx : A x = b) : grade A (b - A x₀) ≤ m := by
  obtain ⟨p, hp, hp0, hres⟩ := exists_residual_poly hx
  refine grade_le_of_aeval_eq_zero (fun h => ?_) (natDegree_le_iff_degree_le.2 hp) ?_
  · rw [h] at hp0; simp at hp0
  · rw [← hres, hAx, sub_self]

/-! ### The minimum-norm minimal-residual iterate -/

/-- The MINRES-QLP specification: the minimum-norm element of the set of minimal-residual iterates
over `x₀ + 𝒦_m`.  On a singular system that set is a whole affine subspace
(`Krylov.isMinResidualIterate_iff_sub_mem`) and the plain minimal-residual specification does not pin the
iterate down; asking in addition for least norm does, with no hypothesis on `A`
(`Krylov.existsUnique_isMinNormMinResidualIterate`).  When `A` is injective this is just
`Krylov.IsMinResidualIterate` again, since that already has a unique solution. -/
structure IsMinNormMinResidualIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) (x : E) : Prop where
  /-- `x` minimizes the residual over `x₀ + 𝒦_m`. -/
  isMinResidualIterate : IsMinResidualIterate A b x₀ m x
  /-- `x` has least norm among the minimizers. -/
  norm_le : ∀ y, IsMinResidualIterate A b x₀ m y → ‖x‖ ≤ ‖y‖

/-- The minimal-residual iterates at step `m` form the affine subspace `x₁ + (𝒦_m ⊓ ker A)` through
any one of them `x₁`: they all share the residual (`Krylov.IsMinResidual.residual_unique`), so they
differ by elements of `𝒦_m` that `A` kills. -/
theorem isMinResidualIterate_iff_sub_mem {x₁ : E} (hx₁ : IsMinResidualIterate A b x₀ m x₁) :
    IsMinResidualIterate A b x₀ m x ↔
      x - x₁ ∈ subspace A (b - A x₀) m ⊓ LinearMap.ker A := by
  constructor
  · intro hx
    have hA : A (x - x₁) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact sub_right_injective (hx.residual_unique hx₁)
    exact ⟨by simpa using Submodule.sub_mem _ hx.mem hx₁.mem, hA⟩
  · rintro ⟨hmem, hker⟩
    have hA : A x = A x₁ := by
      rw [← sub_eq_zero, ← map_sub]
      exact hker
    refine ⟨by simpa using Submodule.add_mem _ hmem hx₁.mem, fun y hy => ?_⟩
    rw [hA]
    exact hx₁.min y hy

/-- The minimum-norm minimal-residual iterate is the best approximation of `0` from the affine
subspace of minimal-residual iterates. -/
private theorem isMinNormMinResidualIterate_iff_isMinError {x₁ : E} (hx₁ : IsMinResidualIterate A b x₀ m x₁) :
    IsMinNormMinResidualIterate A b x₀ m x ↔
      IsMinError 0 x₁ (subspace A (b - A x₀) m ⊓ LinearMap.ker A) x := by
  have hnorm : ∀ y : E, ‖(0 : E) - y‖ = ‖y‖ := fun y => by rw [zero_sub, norm_neg]
  constructor
  · rintro ⟨hx, hmin⟩
    exact ⟨(isMinResidualIterate_iff_sub_mem hx₁).1 hx, fun y hy => by
      rw [hnorm, hnorm]
      exact hmin y ((isMinResidualIterate_iff_sub_mem hx₁).2 hy)⟩
  · rintro ⟨hmem, hmin⟩
    refine ⟨(isMinResidualIterate_iff_sub_mem hx₁).2 hmem, fun y hy => ?_⟩
    have := hmin y ((isMinResidualIterate_iff_sub_mem hx₁).1 hy)
    rwa [hnorm, hnorm] at this

/-- The minimum-norm minimal-residual iterate exists and is unique, with no hypothesis on `A`: the
minimal-residual iterates form a nonempty translate of the finite-dimensional subspace `𝒦_m ⊓ ker
A`, and a nonempty affine subspace of an inner product space has a unique element of least norm.
This is what makes the MINRES-QLP iterate well defined on a singular system, where
`Krylov.existsUnique_isMinResidualIterate_of_injective` does not apply. -/
theorem existsUnique_isMinNormMinResidualIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) :
    ∃! x, IsMinNormMinResidualIterate A b x₀ m x := by
  obtain ⟨x₁, hx₁⟩ := exists_isMinResidualIterate A b x₀ m
  obtain ⟨z, hz⟩ :=
    exists_isMinError x₁ (subspace A (b - A x₀) m ⊓ LinearMap.ker A) 0
  refine ⟨z, (isMinNormMinResidualIterate_iff_isMinError hx₁).2 hz, fun y hy => ?_⟩
  exact IsMinError.unique ((isMinNormMinResidualIterate_iff_isMinError hx₁).1 hy) hz

/-- With `A` injective the minimum-norm condition is vacuous: the minimal-residual iterate is
already unique, so the two specifications agree. -/
theorem isMinNormMinResidualIterate_iff_isMinResidualIterate (hA : Function.Injective A) :
    IsMinNormMinResidualIterate A b x₀ m x ↔ IsMinResidualIterate A b x₀ m x := by
  obtain ⟨x', -, huniq⟩ := existsUnique_isMinResidualIterate_of_injective hA b x₀ m
  exact ⟨fun h => h.isMinResidualIterate,
    fun h => ⟨h, fun y hy => le_of_eq (congrArg norm ((huniq x h).trans (huniq y hy).symm))⟩⟩

end MinResidual

section MinError

/-- A minimal-error iterate always exists (projection of `x* - x₀` onto `A 𝒦_m`). -/
theorem exists_isMinErrorIterate (A : E →ₗ[𝕜] E) (xstar x₀ : E) (m : ℕ) :
    ∃ x, IsMinErrorIterate A xstar x₀ m x :=
  exists_isMinError x₀ _ xstar

/-- The minimal-error iterate is unique, with no hypothesis on `A` at all: it is the nearest point
of the affine space `x₀ + A 𝒦_m` to `x*`, and nearest points are unique by the parallelogram law
however degenerate `A` is. Contrast `existsUnique_isMinResidualIterate_of_injective`, where uniqueness of
the *iterate* costs an injectivity assumption. -/
theorem IsMinErrorIterate.unique {xstar x' : E} (hx : IsMinErrorIterate A xstar x₀ m x)
    (hx' : IsMinErrorIterate A xstar x₀ m x') : x = x' :=
  IsMinError.unique hx hx'

/-- Errors of minimal-error iterates are nonincreasing in `m`. -/
theorem IsMinErrorIterate.norm_error_antitone {xstar : E} {x : ℕ → E}
    (hx : ∀ k, IsMinErrorIterate A xstar x₀ k (x k)) : Antitone fun k => ‖xstar - x k‖ :=
  fun k l hkl => (hx k).norm_error_le_of_le (hx l)
    (Submodule.map_mono (subspace_mono A (A (xstar - x₀)) hkl))

end MinError

section Galerkin

/-- For coercive `A` the Galerkin iterate over `𝒦_m` exists and is unique at every step, so FOM and
CG are well defined with no further hypothesis. Coercivity excludes the one obstruction: a nonzero
`z ∈ 𝒦_m` with `A z ⟂ 𝒦_m`, which would leave the Galerkin condition underdetermined. Without it the
iterate can genuinely fail to exist; `Krylov.existsUnique_isGalerkinIterate_iff_isUnit` ties
existence and uniqueness to invertibility of the compressed Hessenberg matrix. -/
theorem existsUnique_isGalerkinIterate_of_isCoercive (hA : A.IsCoercive) (b x₀ : E) (m : ℕ) :
    ∃! x, IsGalerkinIterate A b x₀ m x :=
  existsUnique_isGalerkin_of_isCoercive b x₀ _ hA

namespace IsGalerkinIterate

/-- For symmetric coercive `A`, a residual polynomial for `y` is an error polynomial for `y`. -/
private theorem error_eq_aeval (hA : A.IsSymmetricCoercive) {xstar y : E} (hstar : A xstar = b)
    {p : 𝕜[X]} (hres : b - A y = aeval A p (b - A x₀)) :
    xstar - y = aeval A p (xstar - x₀) := by
  refine hA.isCoercive.injective ?_
  have hr : b - A x₀ = A (xstar - x₀) := by rw [map_sub, hstar]
  have hl : b - A y = A (xstar - y) := by rw [map_sub, hstar]
  rw [← hl, hres, hr, aeval_apply_comm]

/-- Energy-norm counterpart of `Krylov.IsMinResidualIterate.norm_residual_le_norm_aeval`, for symmetric
coercive `A`: `‖x* - x‖_A ≤ ‖p(A) (x* - x₀)‖_A` for each `p` of degree at most `m` with `p 0 = 1`. A
competitor's residual polynomial doubles as its error polynomial, because `A` commutes with `p(A)`,
so the energy-optimality of the Galerkin iterate turns each such `p` into a bound. This is the half
of `energyNorm_error_eq_iInf` ([saad2003iterative], Lemma 6.28) that the Chebyshev convergence
bounds consume. -/
theorem energyNorm_error_le_energyNorm_aeval (hA : A.IsSymmetricCoercive)
    (hx : IsGalerkinIterate A b x₀ m x) {xstar : E} (hstar : A xstar = b) (p : 𝕜[X])
    (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) :
    energyNorm A (xstar - x) ≤ energyNorm A (aeval A p (xstar - x₀)) := by
  obtain ⟨y, hy, hres⟩ := exists_mem_of_residual_poly (A := A) (b := b) (x₀ := x₀) p hp hp0
  rw [← error_eq_aeval hA hstar hres]
  exact IsGalerkin.energyNorm_le hA hx hstar hy

/-- [saad2003iterative], Lemma 6.28: for symmetric coercive `A`, `‖x* - x_m‖_A = min {‖p(A) (x* -
x₀)‖_A : deg p ≤ m, p 0 = 1}`. -/
theorem energyNorm_error_eq_iInf (hA : A.IsSymmetricCoercive) (hx : IsGalerkinIterate A b x₀ m x)
    {xstar : E} (hstar : A xstar = b) :
    energyNorm A (xstar - x) =
      ⨅ p : {p : 𝕜[X] // p.degree ≤ m ∧ p.eval 0 = 1},
        energyNorm A (aeval A p.1 (xstar - x₀)) := by
  have : Nonempty {p : 𝕜[X] // p.degree ≤ (m : WithBot ℕ) ∧ p.eval 0 = 1} :=
    ⟨⟨1, degree_one_le_natCast m, by simp⟩⟩
  have hbdd : BddBelow (Set.range
      fun p : {p : 𝕜[X] // p.degree ≤ (m : WithBot ℕ) ∧ p.eval 0 = 1} =>
        energyNorm A (aeval A p.1 (xstar - x₀))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact energyNorm_nonneg _ _
  refine le_antisymm
    (le_ciInf fun p => energyNorm_error_le_energyNorm_aeval hA hx hstar p.1 p.2.1 p.2.2) ?_
  obtain ⟨p, hp, hp0, hres⟩ := exists_residual_poly hx.mem
  rw [error_eq_aeval hA hstar hres]
  exact ciInf_le hbdd ⟨p, hp, hp0⟩

/-- [saad2003iterative], Prop 6.7: the Galerkin residual is a multiple of the next Arnoldi vector.
-/
theorem residual_mem_span (hx : IsGalerkinIterate A b x₀ m x) :
    b - A x ∈ 𝕜 ∙ Arnoldi.vec A (b - A x₀) m := by
  have hIio : Set.Iio (m + 1) = Set.Iio m ∪ {m} := by
    ext k; simp
  have hsup : subspace A (b - A x₀) (m + 1)
      = subspace A (b - A x₀) m ⊔ 𝕜 ∙ Arnoldi.vec A (b - A x₀) m := by
    rw [← Arnoldi.span_vec A (b - A x₀) (m + 1), ← Arnoldi.span_vec A (b - A x₀) m, hIio,
      Set.image_union, Submodule.span_union, Set.image_singleton]
  have hmem := residual_mem_subspace_succ hx.mem
  rw [hsup, Submodule.mem_sup] at hmem
  obtain ⟨u, hu, w, hw, huw⟩ := hmem
  have hu0 : u = 0 := by
    have h1 : inner 𝕜 u (b - A x) = (0 : 𝕜) := IsPetrovGalerkin.inner_residual_eq_zero hx hu
    rw [← huw, inner_add_right] at h1
    have h2 : inner 𝕜 u w = (0 : 𝕜) := by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [inner_smul_right, (Submodule.mem_orthogonal _ _).1
        (Arnoldi.vec_mem_orthogonal A (b - A x₀) m) u hu, mul_zero]
    rw [h2, add_zero] at h1
    exact inner_self_eq_zero.1 h1
  rw [← huw, hu0, zero_add]
  exact hw

/-- Galerkin residuals at different steps are orthogonal. -/
theorem inner_residual_eq_zero {m' : ℕ} {x' : E} (hx : IsGalerkinIterate A b x₀ m x)
    (hx' : IsGalerkinIterate A b x₀ m' x') (h : m ≠ m') :
    inner 𝕜 (b - A x) (b - A x') = 0 := by
  have key : ∀ (k l : ℕ) (y y' : E), IsGalerkinIterate A b x₀ k y → IsGalerkinIterate A b x₀ l y' →
      k < l → inner 𝕜 (b - A y) (b - A y') = (0 : 𝕜) := by
    intro k l y y' hy hy' hkl
    exact IsPetrovGalerkin.inner_residual_eq_zero hy'
      (subspace_mono A (b - A x₀) hkl (residual_mem_subspace_succ hy.mem))
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact key m m' x x' hx hx' hlt
  · rw [← inner_conj_symm, key m' m x' x hx' hx hlt, map_zero]

/-- Galerkin iterates are exact at the grade ([saad2003iterative], Prop 5.6 + [saad2003iterative]
Prop 6.10). -/
theorem apply_eq_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hx : IsGalerkinIterate A b x₀ m x) (hm : grade A (b - A x₀) ≤ m) : A x = b := by
  refine hx.eq_of_invt ?_ ?_ ?_
  · rw [subspace_eq_of_grade_le A (b - A x₀) hm]
    exact subspace_grade_mem_invtSubmodule A (b - A x₀)
  · rw [subspace_eq_of_grade_le A (b - A x₀) hm, subspace_grade_eq_fullSubspace]
    exact Submodule.subset_span ⟨0, by simp⟩
  · intro z hz hzo
    exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hzo z hz)

/-- Energy-norm errors are nonincreasing in `m` for symmetric coercive `A`. -/
theorem energyNorm_error_antitone (hA : A.IsSymmetricCoercive) {x : ℕ → E}
    (hx : ∀ k, IsGalerkinIterate A b x₀ k (x k)) {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => energyNorm A (xstar - x k) :=
  fun k l hkl => IsGalerkin.energyNorm_le_of_le hA (hx k) (hx l)
    (subspace_mono A (b - A x₀) hkl) hstar

end IsGalerkinIterate

end Galerkin

/-- For symmetric `A` and a starting vector in the range of `A`, every Krylov subspace of that
vector avoids the kernel: `𝒦_m(A, b) ≤ (ker A)ᗮ`.  This is what makes a Krylov method on a
compatible singular system land on the minimum-norm solution. -/
theorem subspace_le_orthogonal_ker (hA : A.IsSymmetric) {b : E} (hb : b ∈ LinearMap.range A)
    (m : ℕ) : subspace A b m ≤ (LinearMap.ker A)ᗮ := by
  obtain ⟨c, rfl⟩ := hb
  rw [subspace, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine (Submodule.mem_orthogonal _ _).2 fun z hz => ?_
  dsimp only
  have hpow : (A ^ (i : ℕ)) (A c) = (A ^ ((i : ℕ) + 1)) c := by
    rw [pow_succ]
    rfl
  have hz0 : (A ^ ((i : ℕ) + 1)) z = 0 := by
    rw [pow_succ, Module.End.mul_apply, LinearMap.mem_ker.1 hz, map_zero]
  rw [hpow, ← hA.pow ((i : ℕ) + 1) z c, hz0, inner_zero_left]

/-- Any exact Krylov solution of a compatible system with symmetric `A` is the minimum-norm solution
(abstract core of [choi2006iterative], Thm 2.25 / Thm 3.1): `𝒦_m(A, b) ≤ (ker A)ᗮ`. -/
theorem norm_le_of_apply_eq (hA : A.IsSymmetric) {b x : E} {m : ℕ} (hx : x ∈ subspace A b m)
    (hAx : A x = b) (y : E) (hy : A y = b) : ‖x‖ ≤ ‖y‖ := by
  have hker : y - x ∈ LinearMap.ker A := by
    simp [LinearMap.mem_ker, map_sub, hAx, hy]
  have h0 : inner 𝕜 x (y - x) = (0 : 𝕜) :=
    (Submodule.mem_orthogonal' _ _).1 (subspace_le_orthogonal_ker hA ⟨x, hAx⟩ m hx) _ hker
  have hsum : ‖x + (y - x)‖ * ‖x + (y - x)‖ = ‖x‖ * ‖x‖ + ‖y - x‖ * ‖y - x‖ :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [show x + (y - x) = y from by abel] at hsum
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (y - x)]

end Krylov
