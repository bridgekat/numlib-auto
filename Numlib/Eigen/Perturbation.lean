import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Analysis.InnerProductSpace.Coercive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Eigenvalue perturbation and a posteriori bounds

Residual bounds for approximate eigenpairs of symmetric operators (Saad-eig Cor 3.3, Lemma 3.2,
Thm 3.8–3.9 Kato–Temple; Meurant §2.1; Choi §2.4), Bauer–Fike for diagonalizable matrices
(Saad-eig Thm 3.6, Kress Problem 7.6), the backward error of an approximate eigenpair
(Saad-eig Prop 3.4), Bendixson (Saad Thm 1.35) and Rayleigh-quotient bounds.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-! ### Diagonalization bookkeeping

All the symmetric bounds below are inequalities between the sums
`∑ i, f (λ i) ‖⟪v i, x⟫‖²` over an orthonormal eigenbasis `v` with eigenvalues `λ`. -/

private theorem sum_norm_repr_sq {n : ℕ} (hn : Module.finrank 𝕜 E = n) (x : E) :
    ∑ i, ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simpa only [OrthonormalBasis.repr_apply_apply] using
    (hA.eigenvectorBasis hn).sum_sq_norm_inner_right x

private theorem repr_sub_smul {n : ℕ} (hn : Module.finrank 𝕜 E = n) (θ : ℝ) (x : E) (i : Fin n) :
    (hA.eigenvectorBasis hn).repr (A x - (θ : 𝕜) • x) i =
      ((hA.eigenvalues hn i - θ : ℝ) : 𝕜) * (hA.eigenvectorBasis hn).repr x i := by
  rw [map_sub, PiLp.sub_apply, map_smul, PiLp.smul_apply, smul_eq_mul,
    hA.eigenvectorBasis_apply_self_apply hn]
  push_cast
  ring

private theorem norm_residual_sq {n : ℕ} (hn : Module.finrank 𝕜 E = n) (θ : ℝ) (x : E) :
    ‖A x - (θ : 𝕜) • x‖ ^ 2 =
      ∑ i, (hA.eigenvalues hn i - θ) ^ 2 * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [← hA.sum_norm_repr_sq hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA.repr_sub_smul hn, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]

private theorem re_inner_apply_self {n : ℕ} (hn : Module.finrank 𝕜 E = n) (x : E) :
    RCLike.re (inner 𝕜 (A x) x) =
      ∑ i, hA.eigenvalues hn i * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [← (hA.eigenvectorBasis hn).sum_inner_mul_inner (A x) x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA x (hA.eigenvectorBasis hn i), hA.apply_eigenvectorBasis hn, inner_smul_right,
    ← inner_conj_symm x (hA.eigenvectorBasis hn i), mul_assoc, RCLike.conj_mul,
    OrthonormalBasis.repr_apply_apply]
  simp

/-- The identity behind Saad-eig Lemma 3.2 and Kato–Temple: for a unit vector `x` with Rayleigh
quotient `θ` and residual `r`, `∑ (λ - u)(λ - v) ‖c‖² = ‖r‖² + (θ - u)(θ - v)`. -/
private theorem sum_quadratic {n : ℕ} (hn : Module.finrank 𝕜 E = n) {x : E} (hx : ‖x‖ = 1)
    (u v : ℝ) :
    ∑ i, (hA.eigenvalues hn i - u) * (hA.eigenvalues hn i - v) *
        ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 =
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 +
        (RCLike.re (inner 𝕜 (A x) x) - u) * (RCLike.re (inner 𝕜 (A x) x) - v) := by
  set θ := RCLike.re (inner 𝕜 (A x) x) with hθ
  have hs : ∑ i, ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 = 1 := by
    rw [hA.sum_norm_repr_sq hn, hx, one_pow]
  have hth : ∑ i, hA.eigenvalues hn i * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 = θ :=
    (hA.re_inner_apply_self hn x).symm
  have hr : ‖A x - (θ : 𝕜) • x‖ ^ 2 =
      ∑ i, (hA.eigenvalues hn i - θ) ^ 2 * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 :=
    hA.norm_residual_sq hn θ x
  have hsplit : ∀ i : Fin n,
      (hA.eigenvalues hn i - u) * (hA.eigenvalues hn i - v) *
          ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 =
        (hA.eigenvalues hn i - θ) ^ 2 * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 +
          (2 * θ - u - v) * (hA.eigenvalues hn i * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2) +
          (u * v - θ ^ 2) * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hs, hth, ← hr]
  ring

private theorem quadratic_nonneg {n : ℕ} (hn : Module.finrank 𝕜 E = n) {x : E} (hx : ‖x‖ = 1)
    (u v : ℝ) (h : ∀ i, 0 ≤ (hA.eigenvalues hn i - u) * (hA.eigenvalues hn i - v)) :
    0 ≤ ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 +
      (RCLike.re (inner 𝕜 (A x) x) - u) * (RCLike.re (inner 𝕜 (A x) x) - v) := by
  rw [← hA.sum_quadratic hn hx u v]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (h i) (sq_nonneg _)

/-- Residual bound (Saad-eig Cor 3.3): some eigenvalue lies within `‖A x - θ x‖ / ‖x‖` of `θ`. -/
theorem exists_hasEigenvalue_dist_le (θ : ℝ) {x : E} (hx : x ≠ 0) :
    ∃ μ : 𝕜, Module.End.HasEigenvalue A μ ∧ ‖μ - (θ : 𝕜)‖ ≤ ‖A x - (θ : 𝕜) • x‖ / ‖x‖ := by
  set n := Module.finrank 𝕜 E with hn'
  have hn : Module.finrank 𝕜 E = n := rfl
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · have : Subsingleton E := Module.finrank_zero_iff.mp (hn'.symm.trans h)
      exact absurd (Subsingleton.elim x 0) hx
    · exact h
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ
    (fun i => |hA.eigenvalues hn i - θ|) ⟨⟨0, hn0⟩, Finset.mem_univ _⟩
  refine ⟨(hA.eigenvalues hn i₀ : 𝕜), hA.hasEigenvalue_eigenvalues hn i₀, ?_⟩
  have hnorm : ‖((hA.eigenvalues hn i₀ : ℝ) : 𝕜) - (θ : 𝕜)‖ = |hA.eigenvalues hn i₀ - θ| := by
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
  rw [hnorm, le_div_iff₀ (norm_pos_iff.mpr hx)]
  have key : (|hA.eigenvalues hn i₀ - θ| * ‖x‖) ^ 2 ≤ ‖A x - (θ : 𝕜) • x‖ ^ 2 := by
    rw [mul_pow, sq_abs, ← hA.sum_norm_repr_sq hn, hA.norm_residual_sq hn, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have habs := hi₀ i (Finset.mem_univ i)
    nlinarith [abs_nonneg (hA.eigenvalues hn i₀ - θ), abs_nonneg (hA.eigenvalues hn i - θ),
      sq_abs (hA.eigenvalues hn i₀ - θ), sq_abs (hA.eigenvalues hn i - θ)]
  have hsq := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at hsq

/-- Saad-eig Lemma 3.2: with `θ = re⟪A x, x⟫` (`‖x‖ = 1`) and `(α, β) ∋ θ` free of eigenvalues,
`(β - θ)(θ - α) ≤ ‖r‖²`. -/
theorem rayleigh_gap_le_norm_residual_sq {x : E} (hx : ‖x‖ = 1) {α β : ℝ}
    (hαβ : α < RCLike.re (inner 𝕜 (A x) x) ∧ RCLike.re (inner 𝕜 (A x) x) < β)
    (hfree : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∉ Set.Ioo α β) :
    (β - RCLike.re (inner 𝕜 (A x) x)) * (RCLike.re (inner 𝕜 (A x) x) - α) ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 := by
  set n := Module.finrank 𝕜 E with hn'
  have hn : Module.finrank 𝕜 E = n := rfl
  have hout : ∀ i : Fin n, hA.eigenvalues hn i ≤ α ∨ β ≤ hA.eigenvalues hn i := by
    intro i
    have hfi := hfree ((hA.eigenvalues hn i : ℝ) : 𝕜) (hA.hasEigenvalue_eigenvalues hn i)
    rwa [RCLike.ofReal_re, Set.mem_Ioo, not_and_or, not_lt, not_lt] at hfi
  have hab1 := hαβ.1
  have hab2 := hαβ.2
  have h := hA.quadratic_nonneg hn hx α β fun i => by
    rcases hout i with h | h
    · have h1 : hA.eigenvalues hn i - α ≤ 0 := by linarith
      have h2 : hA.eigenvalues hn i - β ≤ 0 := by linarith
      nlinarith
    · exact mul_nonneg (by linarith) (by linarith)
  nlinarith [h]

/-- Kato–Temple (Saad-eig Thm 3.8): if `(a, b)` contains the Rayleigh quotient `θ` and exactly
one eigenvalue `λ`, then `-‖r‖²/(b - θ) ≤ λ - θ ≤ ‖r‖²/(θ - a)`.

The denominators here are the ones the proof produces: the *lower* bound is controlled by the
distance from `θ` to the right end `b`, and the *upper* bound by the distance to the left end `a`.
The version with the two denominators exchanged, which is what the plan (§4.1) wrote down, is
false: for `A = diag(0, 10)`, `x` with `‖x‖ = 1` and `x₂² = 3/5`, one gets `θ = 6`, `‖r‖² = 24`,
and `(a, b) = (5, 20)` contains only the eigenvalue `10`, yet `10 - 6 = 4 > 24/(20 - 6)`. -/
theorem kato_temple {x : E} (hx : ‖x‖ = 1) {a b : ℝ} {μ : 𝕜} (hμ : Module.End.HasEigenvalue A μ)
    (hab : a < RCLike.re (inner 𝕜 (A x) x) ∧ RCLike.re (inner 𝕜 (A x) x) < b)
    (hμab : RCLike.re μ ∈ Set.Ioo a b)
    (hunique : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' → RCLike.re μ' ∈ Set.Ioo a b → μ' = μ) :
    -(‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 / (b - RCLike.re (inner 𝕜 (A x) x))) ≤
        RCLike.re μ - RCLike.re (inner 𝕜 (A x) x) ∧
      RCLike.re μ - RCLike.re (inner 𝕜 (A x) x) ≤
        ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 /
          (RCLike.re (inner 𝕜 (A x) x) - a) := by
  set n := Module.finrank 𝕜 E with hn'
  have hn : Module.finrank 𝕜 E = n := rfl
  set θ := RCLike.re (inner 𝕜 (A x) x) with hθ
  obtain ⟨hab1, hab2⟩ := hab
  obtain ⟨hμa, hμb⟩ := Set.mem_Ioo.mp hμab
  -- every eigenvalue is either `re μ` or outside `(a, b)`
  have hout : ∀ i : Fin n, hA.eigenvalues hn i = RCLike.re μ ∨
      (hA.eigenvalues hn i ≤ a ∨ b ≤ hA.eigenvalues hn i) := by
    intro i
    by_cases hin : a < hA.eigenvalues hn i ∧ hA.eigenvalues hn i < b
    · left
      have heq := hunique ((hA.eigenvalues hn i : ℝ) : 𝕜) (hA.hasEigenvalue_eigenvalues hn i)
        (by rw [RCLike.ofReal_re, Set.mem_Ioo]; exact hin)
      rw [← heq, RCLike.ofReal_re]
    · right
      rwa [not_and_or, not_lt, not_lt] at hin
  constructor
  · have h := hA.quadratic_nonneg hn hx (RCLike.re μ) b fun i => by
      rcases hout i with h | h | h
      · rw [h]; simp
      · have h1 : hA.eigenvalues hn i - RCLike.re μ ≤ 0 := by linarith
        have h2 : hA.eigenvalues hn i - b ≤ 0 := by linarith
        nlinarith
      · exact mul_nonneg (by linarith) (by linarith)
    rw [← hθ] at h
    rw [neg_le, le_div_iff₀ (by linarith : (0 : ℝ) < b - θ)]
    nlinarith [h]
  · have h := hA.quadratic_nonneg hn hx (RCLike.re μ) a fun i => by
      rcases hout i with h | h | h
      · rw [h]; simp
      · have h1 : hA.eigenvalues hn i - RCLike.re μ ≤ 0 := by linarith
        have h2 : hA.eigenvalues hn i - a ≤ 0 := by linarith
        nlinarith
      · exact mul_nonneg (by linarith) (by linarith)
    rw [← hθ] at h
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < θ - a)]
    nlinarith [h]

/-- Saad-eig Cor 3.4: `|λ - θ| ≤ ‖r‖² / δ` with `δ` the gap from `θ` to the other eigenvalues. -/
theorem abs_sub_rayleigh_le_norm_residual_sq_div {x : E} (hx : ‖x‖ = 1) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' → μ' ≠ μ →
      δ ≤ |RCLike.re μ' - RCLike.re (inner 𝕜 (A x) x)|)
    (hclose : |RCLike.re μ - RCLike.re (inner 𝕜 (A x) x)| ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖) :
    |RCLike.re μ - RCLike.re (inner 𝕜 (A x) x)| ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 / δ := by
  set θ := RCLike.re (inner 𝕜 (A x) x) with hθ
  by_cases hlt : |RCLike.re μ - θ| < δ
  · obtain ⟨hlt1, hlt2⟩ := abs_lt.mp hlt
    have hunique : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' →
        RCLike.re μ' ∈ Set.Ioo (θ - δ) (θ + δ) → μ' = μ := by
      intro μ' h1 h2
      by_contra hne
      have hg := hgap μ' h1 hne
      obtain ⟨h21, h22⟩ := Set.mem_Ioo.mp h2
      have hcon : |RCLike.re μ' - θ| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith
    obtain ⟨h1, h2⟩ := hA.kato_temple hx hμ ⟨by linarith, by linarith⟩
      (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩) hunique
    rw [← hθ] at h1 h2
    rw [show θ + δ - θ = δ from by ring] at h1
    rw [show θ - (θ - δ) = δ from by ring] at h2
    exact abs_le.mpr ⟨by linarith, h2⟩
  · rw [not_lt] at hlt
    rw [le_div_iff₀ hδ]
    calc |RCLike.re μ - θ| * δ ≤ ‖A x - (θ : 𝕜) • x‖ * ‖A x - (θ : 𝕜) • x‖ :=
          mul_le_mul hclose (hlt.trans hclose) hδ.le (norm_nonneg _)
      _ = ‖A x - (θ : 𝕜) • x‖ ^ 2 := (sq _).symm

/-- Rayleigh quotient bounds: `λmin ≤ re⟪A x, x⟫ / ‖x‖² ≤ λmax`. -/
theorem rayleigh_mem_Icc {lmin lmax : ℝ}
    (hspec : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∈ Set.Icc lmin lmax) {x : E}
    (hx : x ≠ 0) : RCLike.re (inner 𝕜 (A x) x) / ‖x‖ ^ 2 ∈ Set.Icc lmin lmax := by
  set n := Module.finrank 𝕜 E with hn'
  have hn : Module.finrank 𝕜 E = n := rfl
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  have hbounds : ∀ i : Fin n, hA.eigenvalues hn i ∈ Set.Icc lmin lmax := by
    intro i
    have := hspec ((hA.eigenvalues hn i : ℝ) : 𝕜) (hA.hasEigenvalue_eigenvalues hn i)
    rwa [RCLike.ofReal_re] at this
  rw [Set.mem_Icc]
  constructor
  · rw [le_div_iff₀ hpos, hA.re_inner_apply_self hn, ← hA.sum_norm_repr_sq hn, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hbounds i).1 (sq_nonneg _)
  · rw [div_le_iff₀ hpos, hA.re_inner_apply_self hn, ← hA.sum_norm_repr_sq hn, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hbounds i).2 (sq_nonneg _)

end LinearMap.IsSymmetric

/-- Backward error of an approximate eigenpair (Saad-eig Prop 3.4): the least `‖ΔA‖` with
`(A - ΔA) u = θ u` (`‖u‖ = 1`) is `‖A u - θ u‖`, attained by the rank-one `r uᴴ`. -/
theorem isLeast_eigen_backwardError (A : E →L[𝕜] E) {u : E} (hu : ‖u‖ = 1) (θ : 𝕜) :
    IsLeast {ε : ℝ | ∃ ΔA : E →L[𝕜] E, (A - ΔA) u = θ • u ∧ ‖ΔA‖ = ε} ‖A u - θ • u‖ := by
  have huu : inner 𝕜 u u = (1 : 𝕜) := by
    rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  constructor
  · refine ⟨InnerProductSpace.rankOne 𝕜 (A u - θ • u) u, ?_, ?_⟩
    · have hr : (InnerProductSpace.rankOne 𝕜 (A u - θ • u) u) u = A u - θ • u := by
        rw [InnerProductSpace.rankOne_apply, huu, one_smul]
      rw [sub_apply, hr, sub_sub_cancel]
    · rw [InnerProductSpace.norm_rankOne, hu, mul_one]
  · rintro ε ⟨ΔA, hΔ, rfl⟩
    have hval : ΔA u = A u - θ • u := by
      rw [sub_apply, sub_eq_iff_eq_add] at hΔ
      rw [hΔ]; abel
    calc ‖A u - θ • u‖ = ‖ΔA u‖ := by rw [hval]
      _ ≤ ‖ΔA‖ * ‖u‖ := ΔA.le_opNorm u
      _ = ‖ΔA‖ := by rw [hu, mul_one]

/-- Bendixson (Saad Thm 1.35): the real part of every eigenvalue of a bounded operator lies
between the extreme eigenvalues of its symmetric part `H = (A + A†)/2`. -/
theorem re_hasEigenvalue_mem_Icc_of_symmetricPart {A H : E →ₗ[𝕜] E} {lmin lmax : ℝ}
    (hH : H.IsSymmetricBoundedBy lmin lmax)
    (hHA : ∀ x, RCLike.re (inner 𝕜 (H x) x) = RCLike.re (inner 𝕜 (A x) x)) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) : RCLike.re μ ∈ Set.Icc lmin lmax := by
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  have hAv : A v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv0) 2
  have hkey : RCLike.re (inner 𝕜 (A v) v) = RCLike.re μ * ‖v‖ ^ 2 := by
    rw [hAv, inner_smul_left, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.mul_re]
    simp
  have h1 := hH.le_re_inner v
  have h2 := hH.re_inner_le v
  rw [hHA v, hkey] at h1 h2
  exact ⟨le_of_mul_le_mul_right (by linarith) hpos,
    le_of_mul_le_mul_right (by linarith) hpos⟩

namespace Matrix

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Bauer–Fike (Saad-eig Thm 3.6, Kress Problem 7.6): for `A = X D X⁻¹` and `μ ∈ σ(A + ΔA)`,
`dist(μ, σ(A)) ≤ κ₂(X) ‖ΔA‖₂`. -/
theorem bauer_fike (X : Matrix n n ℂ) (d : n → ℂ) (hX : IsUnit X) (ΔA : Matrix n n ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (X * Matrix.diagonal d * X⁻¹ + ΔA)) :
    ∃ i, ‖μ - d i‖ ≤ NormedRing.condNumber X * ‖ΔA‖ := by
  classical
  have hcond : NormedRing.condNumber X * ‖ΔA‖ = ‖X‖ * ‖X⁻¹‖ * ‖ΔA‖ := by
    rw [NormedRing.condNumber, Matrix.nonsing_inv_eq_ringInverse]
  rw [← Matrix.spectrum_toLin'] at hμ
  obtain ⟨v, hv, hv0⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ).exists_hasEigenvector
  have hveq : (X * Matrix.diagonal d * X⁻¹ + ΔA) *ᵥ v = μ • v := by
    have h := Module.End.mem_eigenspace_iff.mp hv
    rwa [Matrix.toLin'_apply] at h
  have hne : Nonempty n := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    exact hv0 (Subsingleton.elim v 0)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ‖μ - d i‖)
    ⟨Classical.arbitrary n, Finset.mem_univ _⟩
  refine ⟨i₀, ?_⟩
  rw [hcond]
  by_cases hz : μ - d i₀ = 0
  · rw [hz, norm_zero]; positivity
  have hδ : 0 < ‖μ - d i₀‖ := norm_pos_iff.mpr hz
  have hne0 : ∀ i, μ - d i ≠ 0 := fun i hi => by
    have h := hi₀ i (Finset.mem_univ i)
    rw [hi, norm_zero] at h
    exact hz (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  set N : Matrix n n ℂ := Matrix.diagonal (fun i => μ - d i) with hN
  set Ninv : Matrix n n ℂ := Matrix.diagonal (fun i => (μ - d i)⁻¹) with hNinv
  have hNN : Ninv * N = 1 := by
    rw [hNinv, hN, Matrix.diagonal_mul_diagonal,
      show (fun i => (μ - d i)⁻¹ * (μ - d i)) = (1 : n → ℂ) from
        funext fun i => inv_mul_cancel₀ (hne0 i)]
    simp
  have hXd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp hX
  have hXinvX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hXd
  have hXXinv : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hXd
  set w := X⁻¹ *ᵥ v with hw
  have hvw : X *ᵥ w = v := by rw [hw, Matrix.mulVec_mulVec, hXXinv, Matrix.one_mulVec]
  have hw0 : w ≠ 0 := fun h => hv0 (by rw [← hvw, h, Matrix.mulVec_zero])
  have key : N *ᵥ w = (X⁻¹ * ΔA * X) *ᵥ w := by
    have e1 : (X⁻¹ * ΔA * X) *ᵥ w = X⁻¹ *ᵥ (ΔA *ᵥ v) := by
      rw [← hvw, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have e2 : ΔA *ᵥ v = μ • v - (X * Matrix.diagonal d * X⁻¹) *ᵥ v := by
      rw [← hveq, Matrix.add_mulVec]; abel
    have e3 : X⁻¹ *ᵥ ((X * Matrix.diagonal d * X⁻¹) *ᵥ v) = Matrix.diagonal d *ᵥ w := by
      rw [Matrix.mulVec_mulVec, show X⁻¹ * (X * Matrix.diagonal d * X⁻¹)
          = Matrix.diagonal d * X⁻¹ by rw [← mul_assoc, ← mul_assoc, hXinvX, one_mul],
        ← Matrix.mulVec_mulVec]
    rw [e1, e2, Matrix.mulVec_sub, Matrix.mulVec_smul, e3, ← hw, hN]
    funext i
    simp [Matrix.mulVec_diagonal, sub_mul]
  set u : EuclideanSpace ℂ n := WithLp.toLp 2 w with hu
  have hu0 : u ≠ 0 := fun h => hw0 (by simpa [hu] using congrArg WithLp.ofLp h)
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hid : Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv (Matrix.toEuclideanCLM (𝕜 := ℂ) N u) = u := by
    have hmap : Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv * Matrix.toEuclideanCLM (𝕜 := ℂ) N = 1 := by
      rw [← map_mul, hNN, map_one]
    calc Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv (Matrix.toEuclideanCLM (𝕜 := ℂ) N u)
        = (Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv * Matrix.toEuclideanCLM (𝕜 := ℂ) N) u := rfl
      _ = u := by rw [hmap]; rfl
  have hkey2 : Matrix.toEuclideanCLM (𝕜 := ℂ) N u
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (X⁻¹ * ΔA * X) u := by
    rw [hu, Matrix.toEuclideanCLM_toLp, Matrix.toEuclideanCLM_toLp, key]
  have hbound : ‖u‖ ≤ ‖Ninv‖ * (‖X⁻¹ * ΔA * X‖ * ‖u‖) := by
    calc ‖u‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (X⁻¹ * ΔA * X) u)‖ := by rw [← hkey2, hid]
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv‖ *
            ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X⁻¹ * ΔA * X) u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Ninv‖ * (‖X⁻¹ * ΔA * X‖ * ‖u‖) := by
          rw [Matrix.l2_opNorm_toEuclideanCLM]
          exact mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
  have hNinvle : ‖Ninv‖ ≤ ‖μ - d i₀‖⁻¹ := by
    rw [hNinv, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    rw [norm_inv]
    gcongr
    exact hi₀ i (Finset.mem_univ i)
  have hmul : ‖X⁻¹ * ΔA * X‖ ≤ ‖X⁻¹‖ * ‖ΔA‖ * ‖X‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have h1 : 1 ≤ ‖Ninv‖ * ‖X⁻¹ * ΔA * X‖ := by nlinarith [hbound, hupos]
  have h2 : 1 ≤ ‖μ - d i₀‖⁻¹ * (‖X⁻¹‖ * ‖ΔA‖ * ‖X‖) :=
    h1.trans (mul_le_mul hNinvle hmul (norm_nonneg _) (by positivity))
  have h3 : ‖μ - d i₀‖ ≤ ‖X⁻¹‖ * ‖ΔA‖ * ‖X‖ := by
    have h4 := mul_le_mul_of_nonneg_left h2 hδ.le
    rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul] at h4
  calc ‖μ - d i₀‖ ≤ ‖X⁻¹‖ * ‖ΔA‖ * ‖X‖ := h3
    _ = ‖X‖ * ‖X⁻¹‖ * ‖ΔA‖ := by ring

/-- Residual form of Bauer–Fike: for a unit approximate eigenpair `(θ, u)` of `A = X D X⁻¹`,
`dist(θ, σ(A)) ≤ κ₂(X) ‖A u - θ u‖`. -/
theorem bauer_fike_residual (X : Matrix n n ℂ) (d : n → ℂ) (hX : IsUnit X)
    {u : EuclideanSpace ℂ n} (hu : ‖u‖ = 1) (θ : ℂ) :
    ∃ i, ‖θ - d i‖ ≤ NormedRing.condNumber X *
      ‖Matrix.toEuclideanLin (X * Matrix.diagonal d * X⁻¹) u - θ • u‖ := by
  classical
  set A := X * Matrix.diagonal d * X⁻¹ with hA
  set r : EuclideanSpace ℂ n := Matrix.toEuclideanLin A u - θ • u with hr
  -- the rank-one backward perturbation `r uᴴ`
  set M : Matrix n n ℂ :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (InnerProductSpace.rankOne ℂ r u) with hM
  have hMapply : Matrix.toEuclideanCLM (𝕜 := ℂ) M = InnerProductSpace.rankOne ℂ r u := by
    rw [hM, StarAlgEquiv.apply_symm_apply]
  have hMnorm : ‖M‖ = ‖r‖ := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM, hMapply, InnerProductSpace.norm_rankOne, hu, mul_one]
  have huu : inner ℂ u u = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hu0 : WithLp.ofLp u ≠ 0 := by
    intro h
    have : u = 0 := by
      apply WithLp.ofLp_injective
      simpa using h
    rw [this, norm_zero] at hu
    exact one_ne_zero hu.symm
  have hclm : Matrix.toEuclideanCLM (𝕜 := ℂ) (A + (-M)) u = θ • u := by
    rw [map_add, map_neg, hMapply]
    change Matrix.toEuclideanLin A u + -(inner ℂ u u • r) = θ • u
    rw [huu, one_smul, hr]
    abel
  have heig : (A + (-M)) *ᵥ (WithLp.ofLp u) = θ • WithLp.ofLp u := by
    have h := congrArg WithLp.ofLp hclm
    rw [Matrix.add_mulVec, Matrix.neg_mulVec]
    simpa using h
  have hspec : θ ∈ spectrum ℂ (A + (-M)) := by
    rw [← Matrix.spectrum_toLin']
    refine Module.End.hasEigenvalue_iff_mem_spectrum.mp
      (Module.End.hasEigenvalue_of_hasEigenvector (x := WithLp.ofLp u) ⟨?_, hu0⟩)
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact heig
  obtain ⟨i, hi⟩ := bauer_fike X d hX (-M) hspec
  exact ⟨i, by rwa [norm_neg, hMnorm] at hi⟩

/-- Gershgorin discs, union form (Saad-eig Thm 3.11, Kress Thm 7.7); Mathlib's
`eigenvalue_mem_ball` is the pointwise version. -/
theorem spectrum_subset_iUnion_closedBall (A : Matrix n n ℂ) :
    spectrum ℂ A ⊆ ⋃ i, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖) := by
  intro μ hμ
  rw [← Matrix.spectrum_toLin'] at hμ
  obtain ⟨i, hi⟩ := _root_.eigenvalue_mem_ball (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ)
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

end Matrix
