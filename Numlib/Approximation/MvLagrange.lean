import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.MvPolynomial.Basic
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Approximation.MvPolynomial
import Numlib.RingTheory.MvPolynomial.TotalDegree

/-!
# Multivariate Lagrange interpolation and its derivative error

Polynomial interpolation in `ℝⁿ` ([cartis2022evaluation], (13.2.2)–(13.2.4)). The polynomial
functions of total degree at most `p` form the subspace `Approximation.polyFunLE n p` of `ℝⁿ → ℝ`
(images of `MvPolynomial (Fin n) ℝ` of total degree at most `p` under evaluation). Points
`y_1, …, y_m` are poised (`Approximation.IsPoised`) if no nonzero such function vanishes at all of
them, and `ℓ_1, …, ℓ_m ∈ polyFunLE n p` are their Lagrange polynomials
(`Approximation.IsLagrangeBasis`) if `ℓ_i(y_j) = δ_ij`. Then every `P ∈ polyFunLE n p` is
reproduced, `∑_j P(y_j) ℓ_j = P` (`IsLagrangeBasis.sum_mul_eq`); the Lagrange polynomials are a
basis, so `m = C(n + p, n)` (`IsLagrangeBasis.card_eq`).

Since the Taylor polynomial `y ↦ T_{f,p}(x, y - x)` lies in `polyFunLE n p`
(`taylorPolynomial_comp_sub_mem_polyFunLE`), the interpolation model `w = ∑_j f(y_j) ℓ_j` is
`T_{f,p} + ∑_j R_j ℓ_j` with the Taylor remainders `R_j = f(y_j) - T_{f,p}(x, y_j - x)`, and
differentiating gives the derivative error bound (13.2.4),
`‖∇^i w(x) - ∇^i f(x)‖ ≤ L/(p+1)! ∑_j ‖y_j - x‖^{p+1} ‖∇^i ℓ_j(x)‖`
(`IsLagrangeBasis.norm_iteratedFDeriv_sub_le`). Polynomial functions are invariant under affine
changes of variables (`comp_smul_add_mem_polyFunLE`, from
`MvPolynomial.totalDegree_bind₁_le_of_totalDegree_le_one`), so Lagrange polynomials of scaled and
translated points are scaled and translated Lagrange polynomials (`IsLagrangeBasis.smul_add`),
which gives the scaled bound `L m/(p+1)! Λ_i δ^{p-i+1}`
(`IsLagrangeBasis.norm_iteratedFDeriv_sub_le_of_scaled`).

The same polynomials appear as `Approximation.mvPolyLE D n` inside `C(D, ℝ)`
(`Numlib.Approximation.MvPolynomial`); here they are functions on all of `ℝⁿ`, so that they can be
differentiated. Poisedness is unisolvence (`Approximation.IsUnisolvent`,
`Numlib.Approximation.Unisolvent`) of the point evaluations on `polyFunLE n p`.

## Main definitions

* `Approximation.polyFunLE n p`: polynomial functions of degree at most `p` on `ℝⁿ`;
* `Approximation.IsPoised`, `Approximation.IsLagrangeBasis`.

## Main results

* `Approximation.IsLagrangeBasis.sum_mul_eq`: reproduction of polynomials;
* `Approximation.IsLagrangeBasis.card_eq`, `Approximation.IsLagrangeBasis.card_eq_sum_choose`: the
  number of points is `C(n + p, n) = ∑_{i=0}^p C(n+i-1, i)`;
* `Approximation.IsLagrangeBasis.norm_iteratedFDeriv_sub_le`: the bound (13.2.4);
* `Approximation.IsLagrangeBasis.norm_iteratedFDeriv_sub_le_of_scaled`: its scaled form.
-/

open Finset MvPolynomial
open scoped Nat

namespace Approximation

variable {n : ℕ}

set_option hygiene false in
local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-! ### Polynomial functions of bounded degree -/

section PolyFun

variable (n) in
/-- Evaluation of a polynomial in `n` variables as a function on `ℝⁿ`. -/
noncomputable def evalFun : MvPolynomial (Fin n) ℝ →ₗ[ℝ] (𝔼 → ℝ) where
  toFun P y := eval (fun k => y k) P
  map_add' P Q := by funext y; simp
  map_smul' c P := by funext y; simp

/-- Unfolding lemma for `evalFun`. -/
@[simp]
theorem evalFun_apply (P : MvPolynomial (Fin n) ℝ) (y : 𝔼) :
    evalFun n P y = eval (fun k => y k) P := rfl

variable (n) in
/-- The **polynomial functions of total degree at most `p`** on `ℝⁿ`: the functions
`y ↦ P(y_1, …, y_n)` with `P` a real polynomial in `n` variables of total degree at most `p`. -/
noncomputable def polyFunLE (p : ℕ) : Submodule ℝ (𝔼 → ℝ) :=
  (restrictTotalDegree (Fin n) ℝ p).map (evalFun n)

/-- `g` is a polynomial function of degree at most `p` iff `g(y) = P(y_1, …, y_n)` for a
polynomial `P` of total degree at most `p`. -/
theorem mem_polyFunLE_iff {p : ℕ} {g : 𝔼 → ℝ} :
    g ∈ polyFunLE n p ↔ ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ p ∧
      ∀ y, g y = eval (fun k => y k) P := by
  simp only [polyFunLE, Submodule.mem_map, mem_restrictTotalDegree]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, hP, fun y => rfl⟩
  · rintro ⟨P, hP, hg⟩
    exact ⟨P, hP, funext fun y => (hg y).symm⟩

/-- The spaces of polynomial functions increase with the degree. -/
theorem polyFunLE_mono {p p' : ℕ} (h : p ≤ p') : polyFunLE n p ≤ polyFunLE n p' := by
  intro g hg
  obtain ⟨P, hP, hg⟩ := mem_polyFunLE_iff.1 hg
  exact mem_polyFunLE_iff.2 ⟨P, hP.trans h, hg⟩

/-- Polynomial functions are smooth. -/
theorem contDiff_evalFun (P : MvPolynomial (Fin n) ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (evalFun n P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : evalFun n (C a) = fun _ => a := by funext y; simp
    rw [this]
    exact contDiff_const
  | add P Q hP hQ => rw [map_add]; exact hP.add hQ
  | mul_X P i hP =>
    have : evalFun n (P * X i) = fun y => evalFun n P y * y i := by funext y; simp
    rw [this]
    exact hP.mul (EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).contDiff

/-- Polynomial functions of bounded degree are smooth. -/
theorem contDiff_of_mem_polyFunLE {p : ℕ} {g : 𝔼 → ℝ} (hg : g ∈ polyFunLE n p)
    {k : WithTop ℕ∞} : ContDiff ℝ k g := by
  obtain ⟨P, -, rfl⟩ := Submodule.mem_map.1 hg
  exact contDiff_evalFun P

/-- Polynomial functions of degree at most `p` are invariant under the affine changes of variables
`y ↦ a y + b`. -/
theorem comp_smul_add_mem_polyFunLE {p : ℕ} {g : 𝔼 → ℝ} (hg : g ∈ polyFunLE n p) (a : ℝ)
    (b : 𝔼) : (fun y => g (a • y + b)) ∈ polyFunLE n p := by
  obtain ⟨P, hP, hg⟩ := mem_polyFunLE_iff.1 hg
  refine mem_polyFunLE_iff.2 ⟨bind₁ (fun k => C a * X k + C (b k)) P,
    (MvPolynomial.totalDegree_bind₁_le_of_totalDegree_le_one (fun k => ?_) P).trans hP, fun y => ?_⟩
  · refine (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans ?_) (by simp))
    simp [totalDegree_X]
  · rw [hg]
    change _ = eval₂Hom (RingHom.id ℝ) _ (bind₁ _ P)
    rw [eval₂Hom_bind₁]
    refine congrArg (fun ψ => eval ψ P) (_root_.funext fun k => ?_)
    simp

/-- `y ↦ A[y - x, …, y - x]` is a polynomial function of degree at most `i` for every continuous
`i`-linear form `A`. -/
theorem apply_diag_sub_mem_polyFunLE {i : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin i => 𝔼) ℝ) (x : 𝔼) :
    (fun y => A (fun _ => y - x)) ∈ polyFunLE n i := by
  classical
  refine mem_polyFunLE_iff.2 ⟨∑ σ : Fin i → Fin n,
    C (A (fun s => EuclideanSpace.single (σ s) 1)) * ∏ s, (X (σ s) - C (x (σ s))), ?_,
    fun y => ?_⟩
  · refine totalDegree_finsetSum_le fun σ _ => (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ s, (X (σ s) - C (x (σ s)) : MvPolynomial (Fin n) ℝ).totalDegree
        ≤ ∑ _s : Fin i, 1 :=
          sum_le_sum fun s _ => (totalDegree_sub_C_le _ _).trans (totalDegree_X _).le
      _ = i := by simp
  · have hy : y - x = ∑ k, (y k - x k) • EuclideanSpace.single k (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hy, A.map_sum (fun _ k => (y k - x k) • EuclideanSpace.single k (1 : ℝ))]
    simp only [map_sum, map_mul, map_prod, map_sub, eval_C, eval_X]
    refine sum_congr rfl fun σ _ => ?_
    rw [show (fun s => (y (σ s) - x (σ s)) • EuclideanSpace.single (σ s) (1 : ℝ)) =
      fun s => (fun s => y (σ s) - x (σ s)) s • (fun s => EuclideanSpace.single (σ s) (1 : ℝ)) s
        from rfl, A.map_smul_univ, smul_eq_mul, mul_comm]

/-- The Taylor polynomial `y ↦ T_{f,p}(x, y - x)` is a polynomial function of degree at most
`p`. -/
theorem taylorPolynomial_comp_sub_mem_polyFunLE (f : 𝔼 → ℝ) (p : ℕ) (x : 𝔼) :
    (fun y => taylorPolynomial f p x (y - x)) ∈ polyFunLE n p := by
  have : (fun y => taylorPolynomial f p x (y - x)) =
      ∑ i ∈ range (p + 1), (i ! : ℝ)⁻¹ • fun y => iteratedFDeriv ℝ i f x (fun _ => y - x) := by
    funext y
    simp [taylorPolynomial_apply, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (polyFunLE_mono (Nat.lt_succ_iff.1 (mem_range.1 hi)) (apply_diag_sub_mem_polyFunLE _ x))

end PolyFun

/-! ### Lagrange polynomials -/

section Lagrange

variable {p m : ℕ}

variable (n) in
/-- A family of points `y_1, …, y_m ∈ ℝⁿ` is **poised** for the polynomials of degree at most `p`
if the only such polynomial vanishing at all the points is zero, i.e. evaluation at the points is
injective on `polyFunLE n p`. -/
def IsPoised (p : ℕ) (y : Fin m → 𝔼) : Prop :=
  ∀ P ∈ polyFunLE n p, (∀ j, P (y j) = 0) → P = 0

variable (n) in
/-- The functions `ℓ_1, …, ℓ_m` are the **Lagrange polynomials** of degree `p` of the poised points
`y_1, …, y_m` ([cartis2022evaluation], (13.2.2)): polynomial functions of degree at most `p`
with `ℓ_i(y_j) = δ_ij`. -/
structure IsLagrangeBasis (p : ℕ) (y : Fin m → 𝔼) (ℓ : Fin m → 𝔼 → ℝ) : Prop where
  /-- Each `ℓ_j` is a polynomial function of degree at most `p`. -/
  mem : ∀ j, ℓ j ∈ polyFunLE n p
  /-- `ℓ_i(y_j) = δ_ij`. -/
  apply_node : ∀ i j, ℓ i (y j) = if i = j then 1 else 0
  /-- The points are poised. -/
  poised : IsPoised n p y

variable {y : Fin m → 𝔼} {ℓ : Fin m → 𝔼 → ℝ}

/-- The interpolant `∑_j P(y_j) ℓ_j` of a polynomial function is a polynomial function. -/
theorem IsLagrangeBasis.sum_mul_mem (hℓ : IsLagrangeBasis n p y ℓ) (c : Fin m → ℝ) :
    (fun v => ∑ j, c j * ℓ j v) ∈ polyFunLE n p := by
  have : (fun v => ∑ j, c j * ℓ j v) = ∑ j, c j • ℓ j := by
    funext v
    simp [Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hℓ.mem j)

/-- **Reproduction of polynomials**: `∑_j P(y_j) ℓ_j = P` for every polynomial function `P` of
degree at most `p`. -/
theorem IsLagrangeBasis.sum_mul_eq (hℓ : IsLagrangeBasis n p y ℓ) {P : 𝔼 → ℝ}
    (hP : P ∈ polyFunLE n p) : (fun v => ∑ j, P (y j) * ℓ j v) = P := by
  refine sub_eq_zero.1 (hℓ.poised _ (Submodule.sub_mem _ (hℓ.sum_mul_mem _) hP) fun k => ?_)
  simp [hℓ.apply_node]

/-- **The interpolation error bound** ([cartis2022evaluation], (13.2.4)). Let `ℓ_j` be the Lagrange
polynomials of degree `p` of poised points `y_j`, `f` be `C^p` on a convex set `C` containing `x`
and the `y_j` with `∇^p f` `L`-Lipschitz on `C`, and `w = ∑_j f(y_j) ℓ_j` the interpolation model
(13.2.3). Then for `i ≤ p`,
`‖∇^i w(x) - ∇^i f(x)‖ ≤ L/(p+1)! ∑_j ‖y_j - x‖^{p+1} ‖∇^i ℓ_j(x)‖`. -/
theorem IsLagrangeBasis.norm_iteratedFDeriv_sub_le (hℓ : IsLagrangeBasis n p y ℓ) {f : 𝔼 → ℝ}
    {L : ℝ} {C : Set 𝔼} {x : 𝔼} (hC : Convex ℝ C) (hf : ∀ z ∈ C, ContDiffAt ℝ p f z)
    (hL : IteratedFDerivLipschitzOn f p L C) (hx : x ∈ C) (hy : ∀ j, y j ∈ C) {i : ℕ}
    (hi : i ≤ p) :
    ‖iteratedFDeriv ℝ i (fun v => ∑ j, f (y j) * ℓ j v) x - iteratedFDeriv ℝ i f x‖ ≤
      L / ((p + 1)! : ℝ) * ∑ j, ‖y j - x‖ ^ (p + 1) * ‖iteratedFDeriv ℝ i (ℓ j) x‖ := by
  set T : 𝔼 → ℝ := fun v => taylorPolynomial f p x (v - x) with hT_def
  have hT := taylorPolynomial_comp_sub_mem_polyFunLE f p x
  have hrep : ∀ v, ∑ j, T (y j) * ℓ j v = T v := fun v => congrFun (hℓ.sum_mul_eq hT) v
  set R : Fin m → ℝ := fun j => f (y j) - T (y j)
  have hw : (fun v => ∑ j, f (y j) * ℓ j v) = T + ∑ j, R j • ℓ j := by
    funext v
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hrep v, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [R]
    ring
  have hℓc : ∀ j, ContDiff ℝ i (ℓ j) := fun j => contDiff_of_mem_polyFunLE (hℓ.mem j)
  have hTd : iteratedFDeriv ℝ i T x = iteratedFDeriv ℝ i f x := by
    have : T = fun v => taylorPolynomial f p x (v + -x) := by
      funext v
      simp only [T, sub_eq_add_neg]
    rw [this, iteratedFDeriv_comp_add_right']
    simp only [add_neg_cancel]
    exact iteratedFDeriv_taylorPolynomial_zero (hf x hx) hi
  have hderiv : iteratedFDeriv ℝ i (fun v => ∑ j, f (y j) * ℓ j v) x - iteratedFDeriv ℝ i f x =
      ∑ j, R j • iteratedFDeriv ℝ i (ℓ j) x := by
    have hsum : ContDiff ℝ i (∑ j, R j • ℓ j) := contDiff_of_mem_polyFunLE
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (R j) (hℓ.mem j))
    rw [hw, iteratedFDeriv_add_apply (f := T) (g := ∑ j, R j • ℓ j)
      (contDiff_of_mem_polyFunLE hT).contDiffAt hsum.contDiffAt,
      iteratedFDeriv_sum_apply (f := fun j => R j • ℓ j) fun j _ =>
        ((hℓc j).const_smul (R j)).contDiffAt, hTd,
      add_sub_cancel_left]
    exact sum_congr rfl fun j _ => iteratedFDeriv_const_smul_apply (hℓc j).contDiffAt
  rw [hderiv, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
  rw [norm_smul, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hb := norm_sub_taylorPolynomial_le_of_lipschitz hC hf hL hx
    (show x + (y j - x) ∈ C by rw [add_sub_cancel]; exact hy j)
  rwa [add_sub_cancel] at hb

/-- **Scaling and translation of Lagrange polynomials**: if `ℓ̂_j` are the Lagrange polynomials of
the points `ŷ_j`, then `v ↦ ℓ̂_j((v - x)/δ)` are those of the points `x + δ ŷ_j`, `δ ≠ 0`. -/
theorem IsLagrangeBasis.smul_add (hℓ : IsLagrangeBasis n p y ℓ) (x : 𝔼) {δ : ℝ} (hδ : δ ≠ 0) :
    IsLagrangeBasis n p (fun j => x + δ • y j) (fun j v => ℓ j (δ⁻¹ • (v - x))) where
  mem j := by
    have h := comp_smul_add_mem_polyFunLE (hℓ.mem j) δ⁻¹ (-(δ⁻¹ • x))
    convert h using 3 with v
    rw [smul_sub, sub_eq_add_neg]
  apply_node i j := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hδ, one_smul, hℓ.apply_node]
  poised P hP h0 := by
    have hQ := comp_smul_add_mem_polyFunLE hP δ x
    have hQ0 := hℓ.poised _ hQ fun j => by rw [add_comm]; exact h0 j
    funext v
    have := congrFun hQ0 (δ⁻¹ • (v - x))
    rwa [smul_smul, mul_inv_cancel₀ hδ, one_smul, sub_add_cancel] at this

/-- The `i`-th derivative at `x` of `v ↦ g(c (v - x))` is `c^i ∇^i g(0)`. -/
theorem iteratedFDeriv_comp_smul_sub {i : ℕ} {g : 𝔼 → ℝ} (hg : ContDiff ℝ i g) (c : ℝ) (x : 𝔼) :
    iteratedFDeriv ℝ i (fun v => g (c • (v - x))) x = c ^ i • iteratedFDeriv ℝ i g 0 := by
  have h1 : (fun v => g (c • (v - x))) = fun v => (fun w => g (c • w)) (v + -x) := by
    funext v
    rw [sub_eq_add_neg]
  rw [h1, iteratedFDeriv_comp_add_right' (f := fun w => g (c • w)) i (-x)]
  simp only [add_neg_cancel]
  rw [iteratedFDeriv_comp_const_smul c hg]
  simp only [smul_zero]

/-- **The interpolation error with scaled points** ([cartis2022evaluation], §13.2, the display
after (13.2.4)). Let `ℓ̂_j` be the Lagrange polynomials of degree `p` of `m` poised points `ŷ_j`
in the closed unit ball, `Λ ≥ ‖∇^i ℓ̂_j(0)‖` for all `j`, `δ > 0`, and `w` the interpolation
model of `f` on the points `x + δ ŷ_j`, whose Lagrange polynomials are `v ↦ ℓ̂_j((v - x)/δ)`.
If `f` is `C^p` on a convex set `C` containing `x` and the interpolation points, with `∇^p f`
`L`-Lipschitz on `C`, then for `i ≤ p`, `‖∇^i w(x) - ∇^i f(x)‖ ≤ L m/(p+1)! Λ δ^{p-i+1}`: an
error of the form (13.1.2) with `κ_{∇,i} = L m Λ/(p+1)!` and accuracy `δ^{p-i+1}`. (The book
writes `d + 1` for the number `m` of points.) -/
theorem IsLagrangeBasis.norm_iteratedFDeriv_sub_le_of_scaled (hℓ : IsLagrangeBasis n p y ℓ)
    (hy1 : ∀ j, ‖y j‖ ≤ 1) {i : ℕ} (hi : i ≤ p) {Λ : ℝ}
    (hΛ : ∀ j, ‖iteratedFDeriv ℝ i (ℓ j) 0‖ ≤ Λ) {f : 𝔼 → ℝ} {L δ : ℝ} {C : Set 𝔼} {x : 𝔼}
    (hδ : 0 < δ) (hC : Convex ℝ C) (hf : ∀ z ∈ C, ContDiffAt ℝ p f z)
    (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L) (hx : x ∈ C)
    (hyC : ∀ j, x + δ • y j ∈ C) :
    ‖iteratedFDeriv ℝ i (fun v => ∑ j, f (x + δ • y j) * ℓ j (δ⁻¹ • (v - x))) x -
        iteratedFDeriv ℝ i f x‖ ≤ L * m / ((p + 1)! : ℝ) * Λ * δ ^ (p - i + 1) := by
  have hb := (hℓ.smul_add x hδ.ne').norm_iteratedFDeriv_sub_le hC hf hL hx hyC hi
  refine hb.trans ?_
  have hpow : δ ^ (p + 1) = δ ^ (p - i + 1) * δ ^ i := by
    rw [← pow_add]
    congr 1
    omega
  have hterm : ∀ j, ‖x + δ • y j - x‖ ^ (p + 1) *
      ‖iteratedFDeriv ℝ i (fun v => ℓ j (δ⁻¹ • (v - x))) x‖ ≤ δ ^ (p - i + 1) * Λ := by
    intro j
    rw [iteratedFDeriv_comp_smul_sub (contDiff_of_mem_polyFunLE (hℓ.mem j)), norm_smul,
      add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.le, norm_pow,
      Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
    calc (δ * ‖y j‖) ^ (p + 1) * ((δ⁻¹) ^ i * ‖iteratedFDeriv ℝ i (ℓ j) 0‖)
        ≤ δ ^ (p + 1) * ((δ⁻¹) ^ i * Λ) := by
          gcongr
          · exact mul_le_of_le_one_right hδ.le (hy1 j)
          · exact hΛ j
      _ = δ ^ (p - i + 1) * Λ := by
          rw [hpow, inv_pow]
          field_simp
  calc L / ((p + 1)! : ℝ) * ∑ j, ‖x + δ • y j - x‖ ^ (p + 1) *
        ‖iteratedFDeriv ℝ i (fun v => ℓ j (δ⁻¹ • (v - x))) x‖
      ≤ L / ((p + 1)! : ℝ) * ∑ _j : Fin m, δ ^ (p - i + 1) * Λ := by
        exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => hterm j) (by positivity)
    _ = L * m / ((p + 1)! : ℝ) * Λ * δ ^ (p - i + 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The number of interpolation points** is the dimension `C(n + p, p)` of the space of
polynomials of degree at most `p` in `n` variables: the Lagrange polynomials form a basis of that
space. ([cartis2022evaluation], (13.2.2), defines `d = ∑_{i=0}^p C(n+i-1, i)`, which is this
dimension, and interpolates at the `d + 1` points `y_0, …, y_d`; the number of points must be `d`,
not `d + 1`.) -/
theorem IsLagrangeBasis.card_eq (hℓ : IsLagrangeBasis n p y ℓ) : m = (p + n).choose n := by
  classical
  -- the Lagrange polynomials form a basis of `polyFunLE n p`
  let b : Fin m → polyFunLE n p := fun j => ⟨ℓ j, hℓ.mem j⟩
  have hli : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have := congrFun (congrArg Subtype.val hg) (y k)
    simpa [b, Finset.sum_apply, hℓ.apply_node] using this
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range b) := by
    rintro ⟨P, hP⟩ -
    have hP' : (⟨P, hP⟩ : polyFunLE n p) = ∑ j, P (y j) • b j := by
      ext v
      simp only [Submodule.coe_sum, Submodule.coe_smul, b, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      exact (congrFun (hℓ.sum_mul_eq hP) v).symm
    rw [hP']
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have h1 : Module.finrank ℝ (polyFunLE n p) = m := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_fin]
  -- evaluation is injective on polynomials
  have hinj : Function.Injective (evalFun n) := by
    intro P Q hPQ
    refine MvPolynomial.funext fun z => ?_
    have := congrFun hPQ (WithLp.toLp 2 z)
    simpa using this
  have h2 : Module.finrank ℝ (polyFunLE n p) =
      Module.finrank ℝ (restrictTotalDegree (Fin n) ℝ p) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)).symm
  rw [← h1, h2, MvPolynomial.finrank_restrictTotalDegree, Fintype.card_fin]

/-- The **hockey-stick identity** in the form of [cartis2022evaluation], (13.2.2):
`∑_{i=0}^p C(n+i-1, i) = C(p+n, n)`, the dimension of the polynomials of degree at most `p` in
`n` variables (`C(n-1+i, i)` counts the monomials of degree exactly `i`; for `n = 0` the
truncated subtraction gives `1, 0, 0, …`). -/
theorem sum_range_choose_eq (n p : ℕ) :
    ∑ i ∈ range (p + 1), (n + i - 1).choose i = (p + n).choose n := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [sum_range_succ, ih, show n + (p + 1) - 1 = n + p by omega]
    rcases n with _ | k
    · simp
    · rw [show p + (k + 1) = p + k + 1 by ring, show k + 1 + p = p + k + 1 by ring,
        show p + 1 + (k + 1) = p + k + 1 + 1 by ring,
        Nat.choose_symm_of_eq_add (show p + k + 1 = (p + 1) + k by ring),
        Nat.choose_succ_succ' (p + k + 1) k, add_comm]

/-- **The number of interpolation points is the book's `d`**: `m = ∑_{i=0}^p C(n+i-1, i)`, the
quantity ([cartis2022evaluation], (13.2.2)) calls `d` while indexing the points as
`y_0, …, y_d`. -/
theorem IsLagrangeBasis.card_eq_sum_choose (hℓ : IsLagrangeBasis n p y ℓ) :
    m = ∑ i ∈ range (p + 1), (n + i - 1).choose i := by
  rw [sum_range_choose_eq, hℓ.card_eq]

end Lagrange

end Approximation
