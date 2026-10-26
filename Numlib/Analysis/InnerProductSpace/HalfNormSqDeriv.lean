/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.InnerProductSpace.NormPow

/-!
# Diagonal derivatives along lines and of half squared norms

Directional (diagonal) iterated derivatives `∇ⁿg(x)[d]ⁿ` computed along the line `s ↦ x + s d`,
and the diagonal derivatives of order at most three of `½ ‖u‖²` for `u : E → F` with values in a
real inner product space.

## Main results

* `iteratedFDeriv_apply_eq_iteratedDeriv`: for `g` of class `C^n` at `x`,
  `∇ⁿg(x)[d]ⁿ` is the `n`-th derivative of `s ↦ g(x + s d)` at `0`;
* `iteratedDeriv_two_half_norm_sq`, `iteratedDeriv_three_half_norm_sq`: one-variable formulas
  `(½‖ψ‖²)'' = ‖ψ'‖² + ⟪ψ, ψ''⟫` and `(½‖ψ‖²)⁽³⁾ = 3⟪ψ', ψ''⟫ + ⟪ψ, ψ⁽³⁾⟫`;
* `fderiv_half_norm_sq_apply`, `iteratedFDeriv_two_half_norm_sq_apply`,
  `iteratedFDeriv_three_half_norm_sq_apply`: the corresponding diagonal derivatives of
  `½ ‖u‖²`.
-/

open Filter Set
open scoped Topology RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- Subtracting a constant does not change derivatives of positive order. -/
theorem iteratedFDeriv_sub_const_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E → G} {x : E} {n : ℕ} (hn : n ≠ 0) (hg : ContDiffAt ℝ n g x) (e : G) :
    iteratedFDeriv ℝ n (fun z => g z - e) x = iteratedFDeriv ℝ n g x := by
  have : (fun z => g z - e) = g - fun _ => e := rfl
  rw [this, iteratedFDeriv_sub_apply hg contDiffAt_const, iteratedFDeriv_const_of_ne hn,
    Pi.zero_apply, sub_zero]

section Diagonal

/-- A pointwise form of `iteratedFDeriv_apply_const_eq_iteratedDeriv`: for `g` of class `C^n` at
`x`, `∇^n g(x)[d]^n` is the `n`-th derivative of `s ↦ g(x + s d)` at `0`. -/
theorem iteratedFDeriv_apply_eq_iteratedDeriv {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g : E → G} {x : E} {n : ℕ} (hg : ContDiffAt ℝ n g x) (d : E) :
    iteratedFDeriv ℝ n g x (fun _ => d) = iteratedDeriv n (fun s : ℝ => g (x + s • d)) 0 := by
  obtain ⟨u, hu, hgu⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨t, htu, ht, hxt⟩ := mem_nhds_iff.1 hu
  exact iteratedFDeriv_apply_const_eq_iteratedDeriv ht (hgu.mono htu) hxt d

/-- In one variable, a `C^(n+1)` function has a `C^n` derivative. -/
theorem contDiffAt_deriv_of_succ {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ψ : ℝ → G} {a : ℝ} {n : ℕ} (hψ : ContDiffAt ℝ (n + 1) ψ a) :
    ContDiffAt ℝ n (deriv ψ) a := by
  have h : ContDiffAt ℝ n (fderiv ℝ ψ) a := hψ.fderiv_right le_rfl
  exact h.clm_apply contDiffAt_const

section OneDim

variable {ψ : ℝ → F} {a : ℝ}

/-- First derivative of `½ ‖ψ‖²` in one variable. -/
theorem hasDerivAt_half_norm_sq (hψ : DifferentiableAt ℝ ψ a) :
    HasDerivAt (fun s => ‖ψ s‖ ^ 2 / 2) ⟪ψ a, deriv ψ a⟫ a := by
  have h := (hψ.hasDerivAt.norm_sq).div_const 2
  convert h using 1
  ring

/-- Second derivative of `½ ‖ψ‖²` in one variable: `(½ ‖ψ‖²)'' = ‖ψ'‖² + ⟪ψ, ψ''⟫`. -/
theorem iteratedDeriv_two_half_norm_sq (hψ : ContDiffAt ℝ 2 ψ a) :
    iteratedDeriv 2 (fun s => ‖ψ s‖ ^ 2 / 2) a =
      ‖deriv ψ a‖ ^ 2 + ⟪ψ a, iteratedDeriv 2 ψ a⟫ := by
  have hev : deriv (fun s => ‖ψ s‖ ^ 2 / 2) =ᶠ[𝓝 a] fun s => ⟪ψ s, deriv ψ s⟫ := by
    filter_upwards [hψ.eventually (by simp)] with s hs
    exact (hasDerivAt_half_norm_sq (hs.differentiableAt (by simp))).deriv
  have h1 : DifferentiableAt ℝ (deriv ψ) a :=
    (contDiffAt_deriv_of_succ (n := 1) hψ).differentiableAt (by simp)
  have hd := (hψ.differentiableAt (by simp)).hasDerivAt.inner ℝ h1.hasDerivAt
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, hd.deriv, iteratedDeriv_succ,
    iteratedDeriv_one, real_inner_self_eq_norm_sq]
  ring

/-- Third derivative of `½ ‖ψ‖²` in one variable:
`(½ ‖ψ‖²)⁽³⁾ = 3 ⟪ψ', ψ''⟫ + ⟪ψ, ψ⁽³⁾⟫`. -/
theorem iteratedDeriv_three_half_norm_sq (hψ : ContDiffAt ℝ 3 ψ a) :
    iteratedDeriv 3 (fun s => ‖ψ s‖ ^ 2 / 2) a =
      3 * ⟪deriv ψ a, iteratedDeriv 2 ψ a⟫ + ⟪ψ a, iteratedDeriv 3 ψ a⟫ := by
  have hev : iteratedDeriv 2 (fun s => ‖ψ s‖ ^ 2 / 2) =ᶠ[𝓝 a]
      fun s => ‖deriv ψ s‖ ^ 2 + ⟪ψ s, iteratedDeriv 2 ψ s⟫ := by
    filter_upwards [hψ.eventually (by simp)] with s hs
    exact iteratedDeriv_two_half_norm_sq (hs.of_le (by norm_num))
  have h1 : ContDiffAt ℝ 2 (deriv ψ) a := contDiffAt_deriv_of_succ (n := 2) hψ
  have h2 : DifferentiableAt ℝ (iteratedDeriv 2 ψ) a := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (contDiffAt_deriv_of_succ (n := 1) h1).differentiableAt (by simp)
  have hd1 := (h1.differentiableAt (by simp)).hasDerivAt.norm_sq
  have hd2 := (hψ.differentiableAt (by simp)).hasDerivAt.inner ℝ h2.hasDerivAt
  have hd : HasDerivAt (fun s => ‖deriv ψ s‖ ^ 2 + ⟪ψ s, iteratedDeriv 2 ψ s⟫) _ a :=
    hd1.add hd2
  have h21 : deriv (deriv ψ) = iteratedDeriv 2 ψ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv, iteratedDeriv_succ (n := 2), h21]
  ring

end OneDim

variable {u : E → F} {x d : E}

/-- `∇(½ ‖u‖²)(x)[d] = ⟪u(x), ∇u(x)[d]⟫`. -/
theorem fderiv_half_norm_sq_apply (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun z => ‖u z‖ ^ 2 / 2) x d = ⟪u x, fderiv ℝ u x d⟫ := by
  have h := (hu.hasFDerivAt.norm_sq.const_smul (2⁻¹ : ℝ))
  have hfun : (fun z => ‖u z‖ ^ 2 / 2) = (2⁻¹ : ℝ) • fun z => ‖u z‖ ^ 2 := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, h.fderiv]
  simp

/-- The line through `x` in the direction `d` is smooth. -/
theorem contDiffAt_comp_line {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : E → G}
    {n : ℕ} (hg : ContDiffAt ℝ n g x) (d : E) :
    ContDiffAt ℝ n (fun s : ℝ => g (x + s • d)) 0 := by
  have hl : ContDiffAt ℝ n (fun s : ℝ => x + s • d) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hg' : ContDiffAt ℝ n g (x + (0 : ℝ) • d) := by rwa [zero_smul, add_zero]
  exact hg'.comp 0 hl

/-- The diagonal second derivative of `½ ‖u‖²` ([cartis2022evaluation], (14.3.38)):
`∇²(½ ‖u‖²)(x)[d]² = ‖∇u(x)[d]‖² + ⟪u(x), ∇²u(x)[d]²⟫`. -/
theorem iteratedFDeriv_two_half_norm_sq_apply (hu : ContDiffAt ℝ 2 u x) :
    iteratedFDeriv ℝ 2 (fun z => ‖u z‖ ^ 2 / 2) x (fun _ => d) =
      ‖fderiv ℝ u x d‖ ^ 2 + ⟪u x, iteratedFDeriv ℝ 2 u x (fun _ => d)⟫ := by
  have hG : ContDiffAt ℝ 2 (fun z => ‖u z‖ ^ 2 / 2) x := (hu.norm_sq ℝ).div_const _
  have hψ := contDiffAt_comp_line hu d
  rw [iteratedFDeriv_apply_eq_iteratedDeriv hG d, iteratedFDeriv_apply_eq_iteratedDeriv hu d,
    ← iteratedFDeriv_one_apply (m := fun _ => d),
    iteratedFDeriv_apply_eq_iteratedDeriv (hu.of_le (by norm_num)) d, iteratedDeriv_one]
  have := iteratedDeriv_two_half_norm_sq hψ
  simpa only [zero_smul, add_zero] using this

/-- The diagonal third derivative of `½ ‖u‖²` ([cartis2022evaluation], (14.3.39)):
`∇³(½ ‖u‖²)(x)[d]³ = 3 ⟪∇u(x)[d], ∇²u(x)[d]²⟫ + ⟪u(x), ∇³u(x)[d]³⟫`. -/
theorem iteratedFDeriv_three_half_norm_sq_apply (hu : ContDiffAt ℝ 3 u x) :
    iteratedFDeriv ℝ 3 (fun z => ‖u z‖ ^ 2 / 2) x (fun _ => d) =
      3 * ⟪fderiv ℝ u x d, iteratedFDeriv ℝ 2 u x (fun _ => d)⟫ +
        ⟪u x, iteratedFDeriv ℝ 3 u x (fun _ => d)⟫ := by
  have hG : ContDiffAt ℝ 3 (fun z => ‖u z‖ ^ 2 / 2) x := (hu.norm_sq ℝ).div_const _
  have hψ := contDiffAt_comp_line hu d
  rw [iteratedFDeriv_apply_eq_iteratedDeriv hG d, iteratedFDeriv_apply_eq_iteratedDeriv hu d,
    iteratedFDeriv_apply_eq_iteratedDeriv (hu.of_le (by norm_num)) d,
    ← iteratedFDeriv_one_apply (m := fun _ => d),
    iteratedFDeriv_apply_eq_iteratedDeriv (hu.of_le (by norm_num)) d, iteratedDeriv_one]
  have := iteratedDeriv_three_half_norm_sq hψ
  simpa only [zero_smul, add_zero] using this

end Diagonal
