import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder

/-!
# High-order difference formulas for mixed partial derivatives

Derivative tensors of degree `o + r` can be approximated from values of derivatives of degree `o`
by finite differences: for directions `v_1, …, v_o` and `u_1, …, u_r`,
`h^{-r} ∑_k a_k ∇^o f(x + h z_k)[v_1, …, v_o] ≈ ∇^{o+r} f(x)[v_1, …, v_o, u_1, …, u_r]`, with an
error `O(h^{p-(o+r)+1})` when `∇^p f` is Lipschitz ([cartis2022evaluation], (13.2.1); the book
could not find this result in the literature, footnote 93).

The proof separates algebra from analysis. A family of weights and points `(a_k, z_k)` is a stencil
for the mixed derivative in the directions `u`, exact to degree `q`
(`FiniteDifference.IsMixedStencil`), if its moments `∑_k a_k B[z_k^m]` vanish on symmetric
multilinear maps `B` of orders `m ≤ q`, `m ≠ r`, and equal `r! B[u]` for `m = r`. Taylor's theorem
for `∇^o f` (`norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz`) then gives the error bound
(`FiniteDifference.abs_sum_iteratedFDeriv_sub_le`): the stencil reproduces the Taylor polynomial
exactly, and the remainders contribute `L/(p-o+1)! ∑_k |a_k| ‖z_k‖^{p-o+1} h^{p-(o+r)+1}`.

The tensor-product stencil (`FiniteDifference.isMixedStencil_tensor`) has points
`∑_t λ_t u_t`, `λ ∈ [0 : K]^r`, and weights `∏_t w_{λ_t}`, where `w = derivWeights K` are the
one-dimensional weights on the nodes `0, …, K` with `∑_μ w_μ μ^k = δ_{k1}` for `k ≤ K`
(Vandermonde; they are the derivatives at `0` of the Lagrange basis on the nodes, a row of the
differentiation matrix `Lagrange.derivMatrix` of `Numlib.FiniteDifference.Derivative`).
Expanding `B[(∑_t λ_t u_t)^m]` multilinearly, the moment becomes a sum over maps
`σ : [m] → [r]` weighted by `∏_t ∑_μ w_μ μ^{#σ⁻¹(t)}`, which vanishes unless every fibre of `σ` is
a singleton, i.e. `σ` is a bijection (`m = r`); for `K = q + 1 - r` this needs only the moments
of orders `k ≤ K`.

## Main definitions

* `FiniteDifference.derivWeights K`: one-dimensional derivative weights on `0, …, K`;
* `FiniteDifference.tensorWeight`, `FiniteDifference.tensorPoint`: the tensor-product stencil;
* `FiniteDifference.IsMixedStencil a z u q`: the moment conditions;
* `FiniteDifference.fixFirst A v`: a multilinear map with its first arguments fixed.

## Main results

* `FiniteDifference.sum_derivWeights_mul_pow`: the moments of the one-dimensional weights;
* `FiniteDifference.isMixedStencil_tensor`: the tensor-product stencil is exact to degree `q`;
* `FiniteDifference.abs_sum_iteratedFDeriv_sub_le`: the error bound for any stencil.
-/

open Finset
open scoped Nat

namespace FiniteDifference

/-! ### One-dimensional derivative weights -/

section Weights

/-- The **one-dimensional derivative weights** on the nodes `0, 1, …, K`: the unique weights `w`
with `∑_μ w_μ μ^k = δ_{k1}` for `k ∈ [0 : K]`, so that `∑_μ w_μ g(μ h) / h` reproduces `g'(0)` for
every polynomial `g` of degree at most `K`. They are obtained by inverting the (invertible)
Vandermonde matrix of the nodes. -/
noncomputable def derivWeights (K : ℕ) : Fin (K + 1) → ℝ :=
  Matrix.vecMul (fun k : Fin (K + 1) => if (k : ℕ) = 1 then (1 : ℝ) else 0)
    (Matrix.vandermonde fun μ : Fin (K + 1) => (μ : ℝ))⁻¹

/-- The moment conditions of `derivWeights`: `∑_μ w_μ μ^k = δ_{k1}` for `k ≤ K`. -/
theorem sum_derivWeights_mul_pow {K k : ℕ} (hk : k ≤ K) :
    ∑ μ : Fin (K + 1), derivWeights K μ * (μ : ℝ) ^ k = if k = 1 then 1 else 0 := by
  set V := Matrix.vandermonde fun μ : Fin (K + 1) => (μ : ℝ)
  have hV : IsUnit V.det := by
    refine isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 fun a b hab => ?_)
    exact Fin.ext (by exact_mod_cast hab)
  have h := congrFun (congrArg (Matrix.vecMul (fun k : Fin (K + 1) =>
    if (k : ℕ) = 1 then (1 : ℝ) else 0)) (Matrix.nonsing_inv_mul V hV)) ⟨k, by omega⟩
  rw [← Matrix.vecMul_vecMul, Matrix.vecMul_one] at h
  simpa [Matrix.vecMul, dotProduct, V, Matrix.vandermonde_apply, derivWeights] using h

end Weights

/-! ### Moments of the tensor-product stencil -/

section Moments

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Expansion of a multilinear map on the diagonal at a linear combination:
`B[(∑_t c_t u_t)^m] = ∑_{σ : [m] → [r]} (∏_s c_{σ(s)}) B[u_{σ(1)}, …, u_{σ(m)}]`. -/
theorem apply_diag_sum_smul {m r : ℕ}
    (B : MultilinearMap ℝ (fun _ : Fin m => E) ℝ) (c : Fin r → ℝ) (u : Fin r → E) :
    B (fun _ => ∑ t, c t • u t) = ∑ σ : Fin m → Fin r, (∏ s, c (σ s)) * B (u ∘ σ) := by
  rw [B.map_sum (fun _ t => c t • u t)]
  refine sum_congr rfl fun σ _ => ?_
  rw [show (fun s => c (σ s) • u (σ s)) = fun s => (fun s => c (σ s)) s • (u ∘ σ) s from rfl,
    B.map_smul_univ, smul_eq_mul]

/-- `∏_s λ_{σ(s)} = ∏_t λ_t^{#σ⁻¹(t)}`. -/
private theorem prod_comp_eq_prod_pow_card {m r : ℕ} (σ : Fin m → Fin r) (c : Fin r → ℝ) :
    ∏ s, c (σ s) = ∏ t, c t ^ #{s | σ s = t} := by
  rw [← Finset.prod_fiberwise univ σ (fun s => c (σ s))]
  refine prod_congr rfl fun t _ => ?_
  rw [prod_congr rfl (g := fun _ => c t) fun s hs => by rw [(mem_filter.1 hs).2], prod_const]

/-- The fibres of a map `[m] → [r]` have total size `m`. -/
private theorem sum_card_fiber {m r : ℕ} (σ : Fin m → Fin r) : ∑ t, #{s | σ s = t} = m := by
  rw [← card_eq_sum_card_fiberwise (fun s _ => mem_univ (σ s)), card_univ, Fintype.card_fin]

/-- A map `[m] → [r]` all of whose fibres are singletons is a bijection, and `m = r`. -/
private theorem bijective_of_card_fiber_eq_one {r : ℕ} {σ : Fin r → Fin r}
    (h : ∀ t, #{s | σ s = t} = 1) : Function.Bijective σ := by
  rw [Function.bijective_iff_existsUnique]
  intro t
  obtain ⟨s, hs⟩ := card_eq_one.1 (h t)
  have hmem : ∀ s', σ s' = t ↔ s' = s := fun s' => by
    have := congrArg (s' ∈ ·) hs
    simpa using this
  exact ⟨s, (hmem s).2 rfl, fun s' hs' => (hmem s').1 hs'⟩

/-- The fibres of a bijection are singletons. -/
private theorem card_fiber_eq_one_of_bijective {r : ℕ} {σ : Fin r → Fin r}
    (hσ : Function.Bijective σ)
    (t : Fin r) : #{s | σ s = t} = 1 := by
  obtain ⟨s, hs, hu⟩ := (Function.bijective_iff_existsUnique σ).1 hσ t
  rw [card_eq_one]
  exact ⟨s, by ext s'; simpa using ⟨fun h => hu s' h, fun h => h ▸ hs⟩⟩

/-- There are `r!` bijections `[r] → [r]`. -/
private theorem card_bijective_fin (r : ℕ) :
    #{σ : Fin r → Fin r | Function.Bijective σ} = r ! := by
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.bijectiveEquiv), Fintype.card_equiv
    (Equiv.refl _), Fintype.card_fin]

/-- The weights `ω_c = ∑_μ w_μ μ^c` of `derivWeights K`, multiplied over the fibres of a map
`σ : [m] → [r]` with `m + 1 ≤ K + r`, give `1` if every fibre is a singleton and `0` otherwise. -/
theorem prod_sum_derivWeights_mul_pow_card {m r K : ℕ} (hmK : m + 1 ≤ K + r) (σ : Fin m → Fin r) :
    ∏ t, ∑ μ : Fin (K + 1), derivWeights K μ * (μ : ℝ) ^ #{s | σ s = t} =
      if ∀ t, #{s | σ s = t} = 1 then 1 else 0 := by
  have hsum := sum_card_fiber σ
  split_ifs with hall
  · refine prod_eq_one fun t _ => ?_
    have hmr : m = r := by
      rw [← hsum, sum_congr rfl fun t _ => hall t, sum_const, card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
    rw [hall t, sum_derivWeights_mul_pow (by omega), ite_eq_left rfl]
  · push Not at hall
    obtain ⟨t₀, ht₀⟩ := hall
    by_cases h0 : ∃ t, #{s | σ s = t} = 0
    · obtain ⟨t, ht⟩ := h0
      refine prod_eq_zero (mem_univ t) ?_
      rw [ht, sum_derivWeights_mul_pow (Nat.zero_le K)]
      simp
    · push Not at h0
      refine prod_eq_zero (mem_univ t₀) ?_
      have hrest : r - 1 ≤ ∑ t ∈ univ.erase t₀, #{s | σ s = t} := by
        calc r - 1 = ∑ t ∈ univ.erase t₀, 1 := by simp [card_erase_of_mem]
          _ ≤ _ := sum_le_sum fun t _ => Nat.one_le_iff_ne_zero.2 (h0 t)
      have := add_sum_erase univ (fun t => #{s | σ s = t}) (mem_univ t₀)
      have hpos := Nat.one_le_iff_ne_zero.2 (h0 t₀)
      rw [sum_derivWeights_mul_pow (by omega), ite_eq_right ht₀]

/-- The tensor-product stencil weights `∏_t w_{λ_t}` built from `derivWeights K`, indexed by
`λ : [r] → [0 : K]`. -/
noncomputable def tensorWeight (K r : ℕ) (l : Fin r → Fin (K + 1)) : ℝ :=
  ∏ t, derivWeights K (l t)

/-- The tensor-product stencil points `∑_t λ_t u_t`, indexed by `λ : [r] → [0 : K]`. -/
def tensorPoint {K r : ℕ} (u : Fin r → E) (l : Fin r → Fin (K + 1)) : E :=
  ∑ t, ((l t : ℕ) : ℝ) • u t

/-- The moment identity of the tensor-product stencil: for every multilinear `B` of order `m` with
`m + 1 ≤ K + r`, `∑_λ (∏_t w_{λ_t}) B[(∑_t λ_t u_t)^m]` is the sum of `B[u_{σ(1)}, …, u_{σ(m)}]`
over the maps `σ : [m] → [r]` all of whose fibres are singletons. -/
theorem sum_tensorWeight_mul_apply_diag {m r K : ℕ} (hmK : m + 1 ≤ K + r)
    (B : MultilinearMap ℝ (fun _ : Fin m => E) ℝ) (u : Fin r → E) :
    ∑ l, tensorWeight K r l * B (fun _ => tensorPoint u l) =
      ∑ σ : Fin m → Fin r, (if ∀ t, #{s | σ s = t} = 1 then 1 else 0) * B (u ∘ σ) := by
  simp only [tensorPoint, apply_diag_sum_smul B, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  simp_rw [← mul_assoc, ← sum_mul]
  congr 1
  rw [← prod_sum_derivWeights_mul_pow_card hmK σ, Fintype.prod_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [tensorWeight, prod_comp_eq_prod_pow_card σ (fun t => ((l t : ℕ) : ℝ)), ← prod_mul_distrib]

/-- The tensor-product stencil annihilates the diagonal of every multilinear map of order
`m ≠ r` with `m + 1 ≤ K + r`. -/
theorem sum_tensorWeight_mul_apply_diag_of_ne {m r K : ℕ} (hmK : m + 1 ≤ K + r) (hmr : m ≠ r)
    (B : MultilinearMap ℝ (fun _ : Fin m => E) ℝ) (u : Fin r → E) :
    ∑ l, tensorWeight K r l * B (fun _ => tensorPoint u l) = 0 := by
  rw [sum_tensorWeight_mul_apply_diag hmK]
  refine sum_eq_zero fun σ _ => ?_
  rw [ite_eq_right, zero_mul]
  intro hall
  refine hmr ?_
  rw [← sum_card_fiber σ, sum_congr rfl fun t _ => hall t]
  simp

/-- The tensor-product stencil reproduces `r! B[u_1, …, u_r]` for every symmetric multilinear map
of order `r ≤ K`. -/
theorem sum_tensorWeight_mul_apply_diag_self {r K : ℕ} (hrK : 1 ≤ K)
    (B : MultilinearMap ℝ (fun _ : Fin r => E) ℝ)
    (hB : ∀ (σ : Equiv.Perm (Fin r)) (y : Fin r → E), B (y ∘ σ) = B y) (u : Fin r → E) :
    ∑ l, tensorWeight K r l * B (fun _ => tensorPoint u l) = r ! * B u := by
  rw [sum_tensorWeight_mul_apply_diag (by omega)]
  have hterm : ∀ σ : Fin r → Fin r,
      (if ∀ t, #{s | σ s = t} = 1 then (1 : ℝ) else 0) * B (u ∘ σ) =
        if Function.Bijective σ then B u else 0 := by
    intro σ
    by_cases hσ : Function.Bijective σ
    · rw [ite_eq_left (card_fiber_eq_one_of_bijective hσ), ite_eq_left hσ, one_mul]
      exact hB (Equiv.ofBijective σ hσ) u
    · rw [ite_eq_right (fun h => hσ (bijective_of_card_fiber_eq_one h)), ite_eq_right hσ, zero_mul]
  rw [sum_congr rfl fun σ _ => hterm σ, ← sum_filter, sum_const, card_bijective_fin, nsmul_eq_mul]

end Moments

/-! ### Stencils for mixed partial derivatives -/

section Stencil

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A finite family of weights `a_k` and points `z_k` is a **stencil for the mixed derivative in
the directions `u_1, …, u_r`, exact to degree `q`**, if `∑_k a_k B[z_k^m]` vanishes for every
symmetric multilinear map `B` of order `m ≤ q`, `m ≠ r`, and equals `r! B[u_1, …, u_r]` for every
symmetric `B` of order `r`. Applied to the Taylor expansion of a function, this says that
`h^{-r} ∑_k a_k g(x + h z_k)` reproduces `∇^r g(x)[u_1, …, u_r]` for every polynomial `g` of degree
at most `q`. -/
structure IsMixedStencil {ι : Type*} [Fintype ι] (a : ι → ℝ) (z : ι → E) {r : ℕ} (u : Fin r → E)
    (q : ℕ) : Prop where
  /-- The moments of orders `m ≤ q`, `m ≠ r` vanish. -/
  vanish : ∀ m ≤ q, m ≠ r → ∀ B : MultilinearMap ℝ (fun _ : Fin m => E) ℝ,
    (∀ (σ : Equiv.Perm (Fin m)) (y : Fin m → E), B (y ∘ σ) = B y) →
      ∑ k, a k * B (fun _ => z k) = 0
  /-- The moment of order `r` reproduces the mixed derivative. -/
  reproduce : ∀ B : MultilinearMap ℝ (fun _ : Fin r => E) ℝ,
    (∀ (σ : Equiv.Perm (Fin r)) (y : Fin r → E), B (y ∘ σ) = B y) →
      ∑ k, a k * B (fun _ => z k) = r ! * B u

/-- **The tensor-product stencil** `(∏_t w_{λ_t}, ∑_t λ_t u_t)`, `λ ∈ [0 : q - r + 1]^r`, built
from the one-dimensional weights `derivWeights (q + 1 - r)`, is a stencil for the mixed derivative
in the directions `u`, exact to degree `q ≥ r`. -/
theorem isMixedStencil_tensor {r q : ℕ} (hrq : r ≤ q) (u : Fin r → E) :
    IsMixedStencil (tensorWeight (q + 1 - r) r) (tensorPoint u) u q where
  vanish m hm hmr B _ := sum_tensorWeight_mul_apply_diag_of_ne (by omega) hmr B u
  reproduce B hB := sum_tensorWeight_mul_apply_diag_self (by omega) B hB u

end Stencil

/-! ### Error of a stencil applied to derivatives of degree `o` -/

section Error

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The multilinear map of order `m` obtained from one of order `o + m` by fixing its first `o`
arguments: `z ↦ A[v_1, …, v_o, z_1, …, z_m]`. -/
noncomputable def fixFirst {o m : ℕ} (A : MultilinearMap ℝ (fun _ : Fin (o + m) => E) ℝ)
    (v : Fin o → E) : MultilinearMap ℝ (fun _ : Fin m => E) ℝ :=
  (A.domDomCongr finSumFinEquiv.symm).currySum v

/-- Unfolding lemma for `fixFirst`. -/
theorem fixFirst_apply {o m : ℕ} (A : MultilinearMap ℝ (fun _ : Fin (o + m) => E) ℝ)
    (v : Fin o → E) (z : Fin m → E) : fixFirst A v z = A (Fin.append v z) := by
  simp only [fixFirst, MultilinearMap.currySum_apply', MultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- Fixing the first arguments of a symmetric multilinear map gives a symmetric map. -/
theorem fixFirst_comp_perm {o m : ℕ} {A : MultilinearMap ℝ (fun _ : Fin (o + m) => E) ℝ}
    (hA : ∀ (τ : Equiv.Perm (Fin (o + m))) (y : Fin (o + m) → E), A (y ∘ τ) = A y)
    (v : Fin o → E) (σ : Equiv.Perm (Fin m)) (z : Fin m → E) :
    fixFirst A v (z ∘ σ) = fixFirst A v z := by
  rw [fixFirst_apply, fixFirst_apply,
    ← hA ((finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) σ)).trans finSumFinEquiv)
      (Fin.append v z)]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

end Error

section ErrorNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The first `o` arguments of the Taylor-polynomial expansion (A.11), written with `Fin.append`. -/
private theorem dite_lt_eq_append {o m : ℕ} (v : Fin o → E) (s : E) :
    (fun i : Fin (o + m) => if h : (i : ℕ) < o then v ⟨i, h⟩ else s) =
      Fin.append v (fun _ => s) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- The `o`-th derivative of the Taylor polynomial `T_{f,p}(x, ·)` at `s`, applied to `v`, is
`∑_{m=0}^{p-o} (1/m!) ∇^{o+m} f(x)[v, s^m]`. -/
theorem iteratedFDeriv_taylorPolynomial_apply_eq_sum {f : E → ℝ} {p o : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hop : o ≤ p) (s : E) (v : Fin o → E) :
    iteratedFDeriv ℝ o (taylorPolynomial f p x) s v =
      ∑ m ∈ range (p - o + 1), (m ! : ℝ)⁻¹ *
        fixFirst (iteratedFDeriv ℝ (o + m) f x).toMultilinearMap v (fun _ => s) := by
  rw [taylorPolynomial_eq_taylorSum,
    FormalMultilinearSeries.iteratedFDeriv_taylorSum_apply (hf.isSymm_ftaylorSeries le_rfl)]
  have hI : Icc o p = Ico o (p + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
  rw [hI, sum_Ico_eq_sum_range, show p + 1 - o = p - o + 1 by omega]
  refine sum_congr rfl fun m _ => ?_
  rw [fixFirst_apply, smul_eq_mul, Nat.add_sub_cancel_left, dite_lt_eq_append]
  rfl

/-- **Error of a mixed-derivative stencil applied to derivatives of degree `o`.** Let `∇^p f` be
`L`-Lipschitz on the convex set `C` (`f` being `C^p` there), `o + r ≤ p`, and `(a_k, z_k)` a stencil
for the mixed derivative in the directions `u_1, …, u_r`, exact to degree `p - o`. If `x` and all
`x + h z_k` (`h > 0`) lie in `C`, then for all directions `v_1, …, v_o`,
`|h^{-r} ∑_k a_k ∇^o f(x + h z_k)[v] - ∇^{o+r} f(x)[v, u]| ≤
  L/(p-o+1)! (∑_k |a_k| ‖z_k‖^{p-o+1}) ∏_t ‖v_t‖ h^{p-(o+r)+1}`. -/
theorem abs_sum_iteratedFDeriv_sub_le {f : E → ℝ} {p o r : ℕ} {L h : ℝ} {C : Set E} {x : E}
    (hC : Convex ℝ C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C)
    (hx : x ∈ C) (hop : o + r ≤ p) {ι : Type*} [Fintype ι] {a : ι → ℝ} {z : ι → E}
    {u : Fin r → E} (hs : IsMixedStencil a z u (p - o)) (v : Fin o → E) (hh : 0 < h)
    (hz : ∀ k, x + h • z k ∈ C) :
    |∑ k, a k / h ^ r * iteratedFDeriv ℝ o f (x + h • z k) v -
        iteratedFDeriv ℝ (o + r) f x (Fin.append v u)| ≤
      L / ((p - o + 1)! : ℝ) * (∑ k, |a k| * ‖z k‖ ^ (p - o + 1)) * (∏ t, ‖v t‖) *
        h ^ (p - (o + r) + 1) := by
  have hfx := hf x hx
  have hop' : o ≤ p := by omega
  have hsymm : ∀ m ≤ p - o, ∀ (τ : Equiv.Perm (Fin (o + m))) (y : Fin (o + m) → E),
      (iteratedFDeriv ℝ (o + m) f x).toMultilinearMap (y ∘ τ) =
        (iteratedFDeriv ℝ (o + m) f x).toMultilinearMap y := fun m hm τ y =>
    hfx.iteratedFDeriv_comp_perm_of_le (by exact_mod_cast (show o + m ≤ p by omega)) τ y
  -- the stencil applied to the Taylor polynomial is exact
  have hhom : ∀ m (k : ι),
      fixFirst (iteratedFDeriv ℝ (o + m) f x).toMultilinearMap v (fun _ => h • z k) =
        h ^ m * fixFirst (iteratedFDeriv ℝ (o + m) f x).toMultilinearMap v (fun _ => z k) := by
    intro m k
    rw [show (fun _ : Fin m => h • z k) = fun i => (fun _ => h) i • (fun _ => z k) i from rfl,
      MultilinearMap.map_smul_univ, prod_const, card_univ, Fintype.card_fin, smul_eq_mul]
  have hmain : ∑ k, a k / h ^ r * iteratedFDeriv ℝ o (taylorPolynomial f p x) (h • z k) v =
      iteratedFDeriv ℝ (o + r) f x (Fin.append v u) := by
    simp_rw [iteratedFDeriv_taylorPolynomial_apply_eq_sum hfx hop', hhom, mul_sum]
    rw [sum_comm, sum_eq_single r]
    · have hr := hs.reproduce _ (fixFirst_comp_perm (hsymm r (by omega)) v)
      rw [fixFirst_apply] at hr
      have hr0 : (r ! : ℝ) ≠ 0 := by positivity
      have hh0 : h ^ r ≠ 0 := pow_ne_zero _ hh.ne'
      calc ∑ k, a k / h ^ r * ((r ! : ℝ)⁻¹ *
            (h ^ r * fixFirst (iteratedFDeriv ℝ (o + r) f x).toMultilinearMap v (fun _ => z k)))
          = (r ! : ℝ)⁻¹ * ∑ k, a k *
              fixFirst (iteratedFDeriv ℝ (o + r) f x).toMultilinearMap v (fun _ => z k) := by
            rw [mul_sum]
            refine sum_congr rfl fun k _ => ?_
            field_simp
        _ = _ := by
            rw [hr]
            field_simp
            rfl
    · intro m hm hmr
      have hm' : m ≤ p - o := Nat.lt_succ_iff.1 (mem_range.1 hm)
      have hv := hs.vanish m hm' hmr _ (fixFirst_comp_perm (hsymm m hm') v)
      calc ∑ k, a k / h ^ r * ((m ! : ℝ)⁻¹ *
            (h ^ m * fixFirst (iteratedFDeriv ℝ (o + m) f x).toMultilinearMap v (fun _ => z k)))
          = (h ^ m / h ^ r * (m ! : ℝ)⁻¹) * ∑ k, a k *
              fixFirst (iteratedFDeriv ℝ (o + m) f x).toMultilinearMap v (fun _ => z k) := by
            rw [mul_sum]
            refine sum_congr rfl fun k _ => ?_
            ring
        _ = 0 := by rw [hv, mul_zero]
    · intro hr
      exact absurd (mem_range.2 (by omega)) hr
  -- the Taylor remainders
  have hrem : ∀ k, |iteratedFDeriv ℝ o f (x + h • z k) v -
      iteratedFDeriv ℝ o (taylorPolynomial f p x) (h • z k) v| ≤
        L / ((p - o + 1)! : ℝ) * (h * ‖z k‖) ^ (p - o + 1) * ∏ t, ‖v t‖ := by
    intro k
    have hb := norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz hC hf hL hx (hz k) hop'
    rw [norm_smul, Real.norm_of_nonneg hh.le] at hb
    rw [← Real.norm_eq_abs, ← _root_.sub_apply]
    exact ((iteratedFDeriv ℝ o f (x + h • z k) -
      iteratedFDeriv ℝ o (taylorPolynomial f p x) (h • z k)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hb (prod_nonneg fun _ _ => norm_nonneg _))
  have hsplit : ∑ k, a k / h ^ r * iteratedFDeriv ℝ o f (x + h • z k) v -
      iteratedFDeriv ℝ (o + r) f x (Fin.append v u) =
        ∑ k, a k / h ^ r * (iteratedFDeriv ℝ o f (x + h • z k) v -
          iteratedFDeriv ℝ o (taylorPolynomial f p x) (h • z k) v) := by
    rw [← hmain, ← sum_sub_distrib]
    simp_rw [mul_sub]
  rw [hsplit]
  have hpow : h ^ (p - o + 1) = h ^ (p - (o + r) + 1) * h ^ r := by
    rw [← pow_add]
    congr 1
    omega
  have hh0 : h ^ r ≠ 0 := pow_ne_zero _ hh.ne'
  calc _ ≤ ∑ k, |a k / h ^ r * (iteratedFDeriv ℝ o f (x + h • z k) v -
          iteratedFDeriv ℝ o (taylorPolynomial f p x) (h • z k) v)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |a k| / h ^ r *
          (L / ((p - o + 1)! : ℝ) * (h * ‖z k‖) ^ (p - o + 1) * ∏ t, ‖v t‖) := by
        refine sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_div, abs_of_pos (pow_pos hh r)]
        exact mul_le_mul_of_nonneg_left (hrem k) (by positivity)
    _ = _ := by
        rw [mul_sum, sum_mul, sum_mul]
        refine sum_congr rfl fun k _ => ?_
        rw [mul_pow, hpow]
        field_simp

end ErrorNormed

end FiniteDifference
