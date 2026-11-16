/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Multivariate Taylor polynomials from derivative data

Let $E$ and $F$ be real normed spaces. A formal multilinear series $D = (D_0, D_1, \dots)$, with
$D_i$ a continuous $i$-linear map $E^i \to F$, plays the role of the jet
$(f(x), \nabla f(x), \dots, \nabla^p f(x))$ of a function $f : E \to F$ at $x$. This covers
real-valued objectives and vector-valued constraint maps. Exact data is Mathlib's
`ftaylorSeries ℝ f x`, whose $i$-th term is `iteratedFDeriv ℝ i f x`, that is, $\nabla^i f(x)$.
Inexact derivative estimates, as in Chapter 13 of [cartis2022evaluation], are arbitrary data. The
module defines the Taylor sum
$$T_p(s) = \sum_{i=0}^{p} \frac{1}{i!} D_i[s]^i,$$
where $D_i[s]^i$ is $D_i$ evaluated at $(s, \dots, s)$, and the decrement
$\Delta T_p(s) = T_p(0) - T_p(s)$ of real-valued data. It computes the derivatives of $T_p$ for
symmetric data and bounds the decrements.

## Main definitions

* `FormalMultilinearSeries.taylorSum`: the Taylor sum
  $T_p(s) = \sum_{i \le p} \frac{1}{i!} D_i[s]^i$, linear in $D$
  (`FormalMultilinearSeries.taylorSum_add` and the results after it), with the recursion
  `FormalMultilinearSeries.taylorSum_succ`.
* `FormalMultilinearSeries.taylorDecrement`: the decrease $\Delta T_p(s) = T_p(0) - T_p(s)$ for
  real-valued data, (12.1.11) of [cartis2022evaluation].
* `FormalMultilinearSeries.IsSymm`: the data is invariant under permutations of the arguments up to
  order $p$.
* `taylorPolynomial`: the Taylor polynomial $T_{f,p}(x, s)$ of (A.10) of [cartis2022evaluation].

## Main results

* `ContDiffAt.iteratedFDeriv_comp_perm_of_le`: the $i$-th derivative of a function that is $C^n$ at
  $x$ is symmetric for $i \le n$. Mathlib has the second-order case `ContDiffAt.isSymmSndFDerivAt`.
* `ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal_apply_of_comp_perm`: the derivatives of
  $s \mapsto A[s]^n$ for a symmetric $A$.
* `FormalMultilinearSeries.iteratedFDeriv_taylorSum_apply`: formula (A.11) of [cartis2022evaluation]
  for the derivatives of the Taylor sum. Its corollaries are
  `FormalMultilinearSeries.iteratedFDeriv_taylorSum_zero` (the jet at $0$ is the data),
  `FormalMultilinearSeries.iteratedFDeriv_taylorSum_self` (the top derivative is constant) and
  `FormalMultilinearSeries.fderiv_taylorSum_apply`.
* `FormalMultilinearSeries.abs_taylorDecrement_sub_le`: the decrements of exact and inexact data
  differ by at most $\sum_{i=1}^{p} \|D_i - D'_i\| \|s\|^i / i!$, (13.1.3) of
  [cartis2022evaluation].
* `iteratedFDeriv_taylorPolynomial_zero`, `iteratedFDeriv_taylorPolynomial_self`: the jet of the
  Taylor polynomial at $s = 0$, and its constant top derivative.

## Implementation notes

* The notation $\nabla^i f(x)[s]^i$ of [cartis2022evaluation] is
  `iteratedFDeriv ℝ i f x (fun _ => s)`.
* Unlike `FormalMultilinearSeries.partialSum`, which follows the convention of power series, the
  Taylor sums of this module contain the factorials.
-/

open Finset Function
open scoped Nat Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

section Symmetry

/-- A continuous multilinear map that is invariant under every transposition of its arguments is
invariant under every permutation of its arguments. -/
theorem ContinuousMultilinearMap.apply_comp_perm_of_swap {n : ℕ} (A : E [×n]→L[ℝ] F)
    (h : ∀ a b : Fin n, a ≠ b → ∀ v : Fin n → E, A (v ∘ Equiv.swap a b) = A v)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → E) : A (v ∘ σ) = A v := by
  induction σ using Equiv.Perm.swap_induction_on generalizing v with
  | one => rfl
  | swap_mul f a b hab ih =>
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, ih, h a b hab]

/-- The $(k+2)$-nd derivative of $f$ at $x$ is the second derivative of the $k$-th derivative,
applied to the first two directions and then to the others. -/
private theorem iteratedFDeriv_add_two_apply (f : E → F) (x : E) (k : ℕ) (v : Fin (k + 2) → E) :
    iteratedFDeriv ℝ (k + 2) f x v =
      fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ k f)) x (v 0) (v 1) (Fin.tail (Fin.tail v)) := by
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left,
    LinearIsometryEquiv.comp_fderiv]
  simp [continuousMultilinearCurryLeftEquiv_symm_apply, Fin.tail]

/-- If the $k$-th derivative is invariant under a permutation $\tau$ of its arguments near $x$, then
the $(k+1)$-st derivative at $x$ is invariant under $\tau$ acting on its last $k$ arguments. -/
private theorem iteratedFDeriv_succ_apply_cons_comp_perm {f : E → F} {x : E} {k : ℕ}
    (hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x) (τ : Equiv.Perm (Fin k))
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ w : Fin k → E,
      iteratedFDeriv ℝ k f y (w ∘ τ) = iteratedFDeriv ℝ k f y w)
    (a : E) (w : Fin k → E) :
    iteratedFDeriv ℝ (k + 1) f x (Fin.cons a (w ∘ τ)) =
      iteratedFDeriv ℝ (k + 1) f x (Fin.cons a w) := by
  simp only [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
  set L : (E [×k]→L[ℝ] F) →L[ℝ] F := ContinuousMultilinearMap.apply ℝ (fun _ => E) F (w ∘ τ) -
    ContinuousMultilinearMap.apply ℝ (fun _ => E) F w with hL
  have h1 : HasFDerivAt (fun y => L (iteratedFDeriv ℝ k f y))
      (L.comp (fderiv ℝ (iteratedFDeriv ℝ k f) x)) x :=
    L.hasFDerivAt.comp x hd.hasFDerivAt
  have h2 : HasFDerivAt (fun y => L (iteratedFDeriv ℝ k f y)) (0 : E →L[ℝ] F) x := by
    refine (hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq ?_
    filter_upwards [hsymm] with y hy
    simp [hL, hy w]
  have := congrArg (fun T => T a) (h1.unique h2)
  simpa [hL, sub_eq_zero] using this

private theorem iteratedFDeriv_comp_perm_aux {f : E → F} {n : ℕ} :
    ∀ (i : ℕ) {x : E}, ContDiffAt ℝ n f x → i ≤ n → ∀ (σ : Equiv.Perm (Fin i)) (v : Fin i → E),
      iteratedFDeriv ℝ i f x (v ∘ σ) = iteratedFDeriv ℝ i f x v
  | 0, x, _, _, σ, v => by congr 1; exact Subsingleton.elim _ _
  | 1, x, _, _, σ, v => by rw [Subsingleton.elim σ 1]; rfl
  | k + 2, x, hf, hi, σ, v => by
    refine ContinuousMultilinearMap.apply_comp_perm_of_swap _ ?_ σ v
    have hnear : ∀ᶠ y in 𝓝 x, ∀ (τ : Equiv.Perm (Fin (k + 1))) (w : Fin (k + 1) → E),
        iteratedFDeriv ℝ (k + 1) f y (w ∘ τ) = iteratedFDeriv ℝ (k + 1) f y w := by
      filter_upwards [hf.eventually (by simp)] with y hy
      exact iteratedFDeriv_comp_perm_aux (k + 1) hy (by omega)
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ (k + 1) f) x :=
      hf.differentiableAt_iteratedFDeriv (by norm_cast)
    -- transpositions not involving the first argument
    have htail : ∀ a b : Fin (k + 1), ∀ v : Fin (k + 2) → E,
        iteratedFDeriv ℝ (k + 2) f x (v ∘ Equiv.swap a.succ b.succ) =
          iteratedFDeriv ℝ (k + 2) f x v := by
      intro a b v
      have e1 : v ∘ Equiv.swap a.succ b.succ = Fin.cons (v 0) (Fin.tail v ∘ Equiv.swap a b) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a).symm
            (Fin.succ_ne_zero b).symm]
        · simp [Fin.tail, (Fin.succ_injective _).swap_apply]
      rw [e1, iteratedFDeriv_succ_apply_cons_comp_perm hd (Equiv.swap a b)
        (hnear.mono fun y hy => hy (Equiv.swap a b)), Fin.cons_self_tail]
    -- the transposition of the first two arguments
    have h01 : ∀ v : Fin (k + 2) → E,
        iteratedFDeriv ℝ (k + 2) f x (v ∘ Equiv.swap 0 (Fin.succ 0)) =
          iteratedFDeriv ℝ (k + 2) f x v := by
      intro v
      have hs : IsSymmSndFDerivAt ℝ (iteratedFDeriv ℝ k f) x :=
        (hf.iteratedFDeriv_right (m := 2) (by norm_cast; omega)).isSymmSndFDerivAt (by simp)
      have et : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 (Fin.succ 0))) = Fin.tail (Fin.tail v) := by
        funext i
        simp only [Fin.tail, comp_apply, Fin.succ_zero_eq_one]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one i)]
      rw [iteratedFDeriv_add_two_apply, iteratedFDeriv_add_two_apply, et]
      simp only [comp_apply, Equiv.swap_apply_left, Fin.succ_zero_eq_one, Equiv.swap_apply_right]
      rw [hs (v 1) (v 0)]
    -- transpositions involving the first argument
    have h0 : ∀ b : Fin (k + 2), b ≠ 0 → ∀ v : Fin (k + 2) → E,
        iteratedFDeriv ℝ (k + 2) f x (v ∘ Equiv.swap 0 b) = iteratedFDeriv ℝ (k + 2) f x v := by
      intro b hb v
      obtain ⟨b', rfl⟩ := Fin.exists_succ_eq.2 hb
      rcases eq_or_ne b' 0 with rfl | hb'
      · exact h01 v
      have e : Equiv.swap (0 : Fin (k + 2)) b'.succ =
          Equiv.swap (Fin.succ 0) b'.succ * Equiv.swap 0 (Fin.succ 0) *
            Equiv.swap (Fin.succ 0) b'.succ := by
        rw [Equiv.swap_mul_swap_mul_swap (Fin.succ_ne_zero 0).symm hb.symm, Equiv.swap_comm]
      rw [e, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, ← Function.comp_assoc,
        ← Function.comp_assoc, htail, h01, htail]
    intro a b hab v
    rcases eq_or_ne a 0 with rfl | ha
    · exact h0 b hab.symm v
    rcases eq_or_ne b 0 with rfl | hb
    · rw [Equiv.swap_comm]; exact h0 a ha v
    obtain ⟨a', rfl⟩ := Fin.exists_succ_eq.2 ha
    obtain ⟨b', rfl⟩ := Fin.exists_succ_eq.2 hb
    exact htail a' b' v

/-- **Symmetry of iterated derivatives.** Let $f : E \to F$ be $C^n$ at $x$, with
$n \in \mathbb{N} \cup \{\infty, \omega\}$. Then for every $i \le n$, every permutation $\sigma$
of $\{0, \dots, i - 1\}$ and every $v \in E^i$,
$$\nabla^i f(x)[v_{\sigma(0)}, \dots, v_{\sigma(i-1)}] = \nabla^i f(x)[v_0, \dots, v_{i-1}].$$

This is stated in Section A.6 of [cartis2022evaluation]. The proof is by induction from the
symmetry of second derivatives (`ContDiffAt.isSymmSndFDerivAt`), because transpositions generate
the symmetric group. -/
theorem ContDiffAt.iteratedFDeriv_comp_perm_of_le {f : E → F} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f x) {i : ℕ} (hi : (i : WithTop ℕ∞) ≤ n) (σ : Equiv.Perm (Fin i))
    (v : Fin i → E) :
    iteratedFDeriv ℝ i f x (v ∘ σ) = iteratedFDeriv ℝ i f x v :=
  iteratedFDeriv_comp_perm_aux i (hf.of_le hi) le_rfl σ v

end Symmetry

section Diagonal

/-- Homogeneity of a diagonal value: for a continuous $n$-linear map $A$, $t \in \mathbb{R}$ and
$d \in E$, $A[t d]^n = t^n A[d]^n$. -/
theorem ContinuousMultilinearMap.apply_smul_diag {n : ℕ} (A : E [×n]→L[ℝ] F) (t : ℝ) (d : E) :
    A (fun _ => t • d) = t ^ n • A (fun _ => d) := by
  rw [A.map_smul_univ (fun _ => t) (fun _ => d), prod_const, card_univ, Fintype.card_fin]

/-- The iterated derivative at a point $s$ of the restriction $y \mapsto A[y]^n$ of a continuous
$n$-linear map $A$ to the diagonal. For $v \in E^j$, $D^j(y \mapsto A[y]^n)(s)[v]$ is the sum,
over all injections $e : \{0, \dots, j - 1\} \to \{0, \dots, n - 1\}$, of $A$ evaluated with
$v_k$ in the argument $e(k)$ and $s$ in the other arguments.

At $s = 0$ this is Mathlib's `ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal`. -/
theorem ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal_apply {n : ℕ}
    (A : E [×n]→L[ℝ] F) (j : ℕ) (s : E) (v : Fin j → E) :
    iteratedFDeriv ℝ j (fun y => A (fun _ => y)) s v =
      ∑ e : Fin j ↪ Fin n,
        A (fun i => if h : i ∈ Set.range e then v (e.toEquivRange.symm ⟨i, h⟩) else s) := by
  classical
  let g : E →L[ℝ] (Fin n → E) := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ E)
  change iteratedFDeriv ℝ j (A ∘ g) s v = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ A.contDiff _ le_rfl, A.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, _root_.sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, Pi.compRightL_apply]
  refine Finset.sum_congr rfl fun e _ => congrArg A (funext fun i => ?_)
  split_ifs
  · simp only [g, ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply]
    congr!
  · simp only [g, ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply]

end Diagonal

/-- Let $A$ be a continuous $n$-linear map that is invariant under permutations of its arguments.
Then for $s \in E$ and $v \in E^j$, the $j$-th derivative of $y \mapsto A[y]^n$ at $s$ is
$$D^j\big(y \mapsto A[y]^n\big)(s)[v] = n (n-1) \cdots (n-j+1) \, A[v_0, \dots, v_{j-1}, s,
  \dots, s].$$

For $j > n$ the factor $n (n-1) \cdots (n-j+1)$ is $0$. It is `Nat.descFactorial n j`. -/
theorem ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal_apply_of_comp_perm {n : ℕ}
    (A : E [×n]→L[ℝ] F) (hA : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), A (v ∘ σ) = A v)
    (j : ℕ) (s : E) (v : Fin j → E) :
    iteratedFDeriv ℝ j (fun y => A (fun _ => y)) s v =
      (n.descFactorial j : ℝ) • A (fun i => if h : (i : ℕ) < j then v ⟨i, h⟩ else s) := by
  classical
  rw [A.iteratedFDeriv_comp_diagonal_apply]
  have hterm : ∀ e : Fin j ↪ Fin n,
      A (fun i => if h : i ∈ Set.range e then v (e.toEquivRange.symm ⟨i, h⟩) else s) =
        A (fun i => if h : (i : ℕ) < j then v ⟨i, h⟩ else s) := by
    intro e
    have hjn : j ≤ n := by simpa using Fintype.card_le_of_embedding e
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hjn) e
      (Fin.castLE_injective hjn) e.injective
    rw [← hA σ]
    congr 1
    funext i
    by_cases hi : (i : ℕ) < j
    · have h1 : σ i = e ⟨i, hi⟩ := hσ ⟨i, hi⟩
      simp only [comp_apply, h1, Set.mem_range, exists_apply_eq_apply, ↓reduceDIte, hi,
        Function.Embedding.toEquivRange_symm_apply_self]
    · have h1 : σ i ∉ Set.range e := by
        rintro ⟨a, ha⟩
        rw [← hσ a] at ha
        have := congrArg Fin.val (σ.injective ha)
        simp only [Fin.val_castLE] at this
        exact hi (this ▸ a.2)
      simp only [comp_apply, h1, ↓reduceDIte, hi]
  simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]

namespace FormalMultilinearSeries

section TaylorSum

variable (D D' : FormalMultilinearSeries ℝ E F) (p : ℕ)

/-- The **Taylor sum** of degree $p$ of derivative data $D$:
$$T_p(s) = \sum_{i=0}^{p} \frac{1}{i!} D_i[s]^i.$$

With $D$ = `ftaylorSeries ℝ f x` this is the Taylor polynomial $T_{f,p}(x, s)$ of (A.10) of
[cartis2022evaluation]. For inexact derivative data it is the model of (13.1.1) there. The term
$i = 0$ is $D_0$ applied to the empty tuple. -/
noncomputable def taylorSum (s : E) : F :=
  ∑ i ∈ range (p + 1), (i ! : ℝ)⁻¹ • D i (fun _ => s)

/-- The definition of the Taylor sum: $T_p(s) = \sum_{i=0}^{p} \frac{1}{i!} D_i[s]^i$. -/
theorem taylorSum_def (s : E) :
    D.taylorSum p s = ∑ i ∈ range (p + 1), (i ! : ℝ)⁻¹ • D i (fun _ => s) := rfl

/-- Recursion in the degree: $T_{p+1}(s) = T_p(s) + \frac{1}{(p+1)!} D_{p+1}[s]^{p+1}$. -/
theorem taylorSum_succ (s : E) :
    D.taylorSum (p + 1) s = D.taylorSum p s + ((p + 1)! : ℝ)⁻¹ • D (p + 1) (fun _ => s) := by
  rw [taylorSum_def, sum_range_succ, ← taylorSum_def]

/-- The Taylor sum is additive in the data: the Taylor sum of $D + D'$ is the sum of the Taylor sums
of $D$ and $D'$. -/
@[simp]
theorem taylorSum_add (s : E) : (D + D').taylorSum p s = D.taylorSum p s + D'.taylorSum p s := by
  simp [taylorSum_def, sum_add_distrib, smul_add]

/-- The Taylor sum of $D - D'$ is the difference of the Taylor sums of $D$ and $D'$. -/
@[simp]
theorem taylorSum_sub (s : E) : (D - D').taylorSum p s = D.taylorSum p s - D'.taylorSum p s := by
  simp [taylorSum_def, sum_sub_distrib, smul_sub]

/-- The Taylor sum of $-D$ is the negative of the Taylor sum of $D$. -/
@[simp]
theorem taylorSum_neg (s : E) : (-D).taylorSum p s = -D.taylorSum p s := by
  simp [taylorSum_def, sum_neg_distrib, smul_neg]

/-- The Taylor sum is homogeneous in the data: the Taylor sum of $c D$ is $c$ times the Taylor sum
of $D$, for $c \in \mathbb{R}$. -/
@[simp]
theorem taylorSum_smul (c : ℝ) (s : E) : (c • D).taylorSum p s = c • D.taylorSum p s := by
  simp [taylorSum_def, smul_sum, smul_comm c]

/-- The Taylor sum split into its constant term and the terms of order $1$ to $p$: $T_p(s) =
D_0[\,] + \sum_{i=1}^{p} \frac{1}{i!} D_i[s]^i$. -/
theorem taylorSum_eq_add (s : E) :
    D.taylorSum p s = D 0 0 + ∑ i ∈ Icc 1 p, (i ! : ℝ)⁻¹ • D i (fun _ => s) := by
  rw [taylorSum_def, range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos p),
    ← Ico_add_one_right_eq_Icc]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, zero_add]
  congr 2
  exact Subsingleton.elim _ _

/-- At $s = 0$ only the constant term remains: $T_p(0) = D_0[\,]$, the value of $D_0$ at the empty
tuple. -/
@[simp]
theorem taylorSum_zero_right : D.taylorSum p 0 = D 0 0 := by
  rw [taylorSum_eq_add, add_eq_left]
  refine sum_eq_zero fun i hi => ?_
  have : Nonempty (Fin i) := ⟨⟨0, (mem_Icc.1 hi).1⟩⟩
  simp [← Pi.zero_def, ContinuousMultilinearMap.map_zero]

/-- For every $i$ and $s \in E$, $\|D_i[s]^i\| \le \|D_i\| \, \|s\|^i$. -/
theorem norm_apply_diagonal_le (i : ℕ) (s : E) : ‖D i (fun _ => s)‖ ≤ ‖D i‖ * ‖s‖ ^ i := by
  calc ‖D i (fun _ => s)‖ ≤ ‖D i‖ * ∏ _j : Fin i, ‖s‖ := (D i).le_opNorm _
    _ = ‖D i‖ * ‖s‖ ^ i := by rw [prod_const, card_univ, Fintype.card_fin]

/-- The data are **symmetric up to order $p$** if each $D_i$ with $i \le p$ is invariant under
permutations of its arguments, as derivative tensors are (Section A.6 of
[cartis2022evaluation]). -/
def IsSymm : Prop :=
  ∀ i ≤ p, ∀ (σ : Equiv.Perm (Fin i)) (v : Fin i → E), D i (v ∘ σ) = D i v

variable {D p}

/-- Data that are symmetric up to order $p$ are symmetric up to every order $q \le p$. -/
theorem IsSymm.mono {q : ℕ} (hD : D.IsSymm p) (hq : q ≤ p) : D.IsSymm q :=
  fun i hi => hD i (hi.trans hq)

variable (D p)

/-- For each $i$, the term $s \mapsto D_i[s]^i$ is $C^n$ for every $n$. -/
theorem contDiff_apply_diagonal {n : WithTop ℕ∞} (i : ℕ) :
    ContDiff ℝ n (fun s : E => D i (fun _ => s)) :=
  (D i).contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)

/-- The Taylor sum $s \mapsto T_p(s)$ is a polynomial, so it is $C^n$ for every $n$. -/
theorem contDiff_taylorSum {n : WithTop ℕ∞} : ContDiff ℝ n (D.taylorSum p) :=
  ContDiff.sum fun i _ => (D.contDiff_apply_diagonal i).const_smul _

variable {D p}

/-- **Derivatives of the Taylor sum**, (A.11) of [cartis2022evaluation]. Let the data $D$ be
symmetric up to order $p$. Then for $s \in E$ and $v \in E^j$,
$$\nabla^j T_p(s)[v] = \sum_{\ell=j}^{p} \frac{1}{(\ell - j)!} D_\ell[v_0, \dots, v_{j-1}, s,
  \dots, s],$$
where the first $j$ arguments of $D_\ell$ are the directions $v$ and the other $\ell - j$ are
$s$. For $j > p$ the sum is empty, so the derivative is $0$. -/
theorem iteratedFDeriv_taylorSum_apply (hD : D.IsSymm p) (j : ℕ) (s : E) (v : Fin j → E) :
    iteratedFDeriv ℝ j (D.taylorSum p) s v =
      ∑ ℓ ∈ Icc j p, ((ℓ - j)! : ℝ)⁻¹ • D ℓ (fun i => if h : (i : ℕ) < j then v ⟨i, h⟩ else s) := by
  have hfun : D.taylorSum p = fun y => ∑ i ∈ range (p + 1), (i ! : ℝ)⁻¹ • D i (fun _ => y) := rfl
  rw [hfun, iteratedFDeriv_fun_sum_apply fun i _ =>
    ((D.contDiff_apply_diagonal i).const_smul _).contDiffAt, _root_.sum_apply]
  have hterm : ∀ i ∈ range (p + 1),
      iteratedFDeriv ℝ j (fun y => (i ! : ℝ)⁻¹ • D i (fun _ => y)) s v =
        ((i ! : ℝ)⁻¹ * (i.descFactorial j : ℝ)) •
          D i (fun k => if h : (k : ℕ) < j then v ⟨k, h⟩ else s) := by
    intro i hi
    rw [iteratedFDeriv_const_smul_apply' (D.contDiff_apply_diagonal i).contDiffAt,
      _root_.smul_apply, (D i).iteratedFDeriv_comp_diagonal_apply_of_comp_perm
        (hD i (Nat.lt_succ_iff.1 (mem_range.1 hi))), smul_smul]
  rw [sum_congr rfl hterm]
  have hsub : Icc j p ⊆ range (p + 1) :=
    fun ℓ hℓ => mem_range.2 (Nat.lt_succ_of_le (mem_Icc.1 hℓ).2)
  rw [← sum_subset hsub ?_]
  · refine sum_congr rfl fun ℓ hℓ => ?_
    have hjℓ := (mem_Icc.1 hℓ).1
    have hf := Nat.factorial_mul_descFactorial hjℓ
    congr 1
    rw [← hf, Nat.cast_mul]
    have : ((ℓ - j)! : ℝ) ≠ 0 := by positivity
    have : (ℓ.descFactorial j : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.2 hjℓ).ne'
    field_simp
  · intro i hi hi'
    have : i < j := by
      by_contra h
      exact hi' (mem_Icc.2 ⟨not_lt.1 h, Nat.lt_succ_iff.1 (mem_range.1 hi)⟩)
    simp [Nat.descFactorial_eq_zero_iff_lt.2 this]

/-- Let the data $D$ be symmetric up to order $p$. At $s = 0$ the derivatives of the Taylor sum are
the data: $\nabla^j T_p(0) = D_j$ for $j \le p$. -/
theorem iteratedFDeriv_taylorSum_zero (hD : D.IsSymm p) {j : ℕ} (hj : j ≤ p) :
    iteratedFDeriv ℝ j (D.taylorSum p) 0 = D j := by
  ext v
  rw [iteratedFDeriv_taylorSum_apply hD, sum_eq_single_of_mem j (mem_Icc.2 ⟨le_rfl, hj⟩)]
  · simp
  · intro ℓ hℓ hne
    have hjℓ : j < ℓ := lt_of_le_of_ne (mem_Icc.1 hℓ).1 (Ne.symm hne)
    rw [(D ℓ).map_coord_zero ⟨j, hjℓ⟩ (by simp), smul_zero]

/-- Let the data $D$ be symmetric up to order $p$. The top-order derivative of the Taylor sum is
constant: $\nabla^p T_p(s) = D_p$ for every $s \in E$. -/
theorem iteratedFDeriv_taylorSum_self (hD : D.IsSymm p) (s : E) :
    iteratedFDeriv ℝ p (D.taylorSum p) s = D p := by
  ext v
  rw [iteratedFDeriv_taylorSum_apply hD, Icc_self, sum_singleton]
  simp

/-- The derivative of the Taylor sum, the case $j = 1$ of (A.11) of [cartis2022evaluation]. Let the
data $D$ be symmetric up to order $p$. Then for $s, w \in E$
$$\nabla T_p(s)[w] = \sum_{\ell=1}^{p} \frac{1}{(\ell - 1)!} D_\ell[w, s, \dots, s].$$
-/
theorem fderiv_taylorSum_apply (hD : D.IsSymm p) (s w : E) :
    fderiv ℝ (D.taylorSum p) s w =
      ∑ ℓ ∈ Icc 1 p, ((ℓ - 1)! : ℝ)⁻¹ • D ℓ (fun i => if (i : ℕ) = 0 then w else s) := by
  rw [← iteratedFDeriv_one_apply (m := fun _ => w), iteratedFDeriv_taylorSum_apply hD]
  simp

end TaylorSum

section TaylorSumTail

variable (D : FormalMultilinearSeries ℝ E F)

/-- The terms of orders $j + 1, \dots, p$ of a Taylor sum: for $j \le p$, $T_p(s) - T_j(s) =
\sum_{\ell=j+1}^{p} \frac{1}{\ell!} D_\ell[s]^\ell$. -/
theorem taylorSum_sub_taylorSum {j p : ℕ} (hjp : j ≤ p) (s : E) :
    D.taylorSum p s - D.taylorSum j s =
      ∑ ℓ ∈ Icc (j + 1) p, (ℓ ! : ℝ)⁻¹ • D ℓ (fun _ => s) := by
  induction p, hjp using Nat.le_induction with
  | base => simp
  | succ p hjp ih =>
    rw [taylorSum_succ, Finset.sum_Icc_succ_top (by omega), ← ih]
    abel

/-- For $j \le p$, $\|T_p(s) - T_j(s)\| \le \sum_{\ell=j+1}^{p} \|D_\ell\| \, \|s\|^\ell / \ell!$.
-/
theorem norm_taylorSum_sub_taylorSum_le {j p : ℕ} (hjp : j ≤ p) (s : E) :
    ‖D.taylorSum p s - D.taylorSum j s‖ ≤
      ∑ ℓ ∈ Icc (j + 1) p, ‖D ℓ‖ * ‖s‖ ^ ℓ / ℓ ! := by
  rw [D.taylorSum_sub_taylorSum hjp]
  refine (norm_sum_le _ _).trans (sum_le_sum fun ℓ _ => ?_)
  rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div]
  gcongr
  exact D.norm_apply_diagonal_le ℓ s

/-- Let $j \le p$. If $\|D_\ell\| \le K$ for $\ell = j + 1, \dots, p$ and $\|s\| \le \delta$, then
$\|T_p(s) - T_j(s)\| \le K \sum_{\ell=j+1}^{p} \delta^\ell / \ell!$. -/
theorem norm_taylorSum_sub_taylorSum_le_of_norm_le {j p : ℕ} (hjp : j ≤ p) {K δ : ℝ}
    (hD : ∀ ℓ ∈ Icc (j + 1) p, ‖D ℓ‖ ≤ K) {s : E} (hs : ‖s‖ ≤ δ) :
    ‖D.taylorSum p s - D.taylorSum j s‖ ≤ K * ∑ ℓ ∈ Icc (j + 1) p, δ ^ ℓ / ℓ ! := by
  refine (D.norm_taylorSum_sub_taylorSum_le hjp s).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun ℓ hℓ => ?_
  have hK : 0 ≤ K := (norm_nonneg _).trans (hD ℓ hℓ)
  rw [← mul_div_assoc]
  gcongr
  exact hD ℓ hℓ

/-- For every $j$ and $s \in E$, $\|T_j(s)\| \le \sum_{i=0}^{j} \|D_i\| \, \|s\|^i / i!$. -/
theorem norm_taylorSum_le (j : ℕ) (s : E) :
    ‖D.taylorSum j s‖ ≤ ∑ i ∈ range (j + 1), ‖D i‖ * ‖s‖ ^ i / i ! := by
  rw [taylorSum_def]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div]
  gcongr
  exact D.norm_apply_diagonal_le i s


/-- The Taylor sum of degree $j$ depends only on the terms of order at most $j$: if $D_i = D'_i$ for
all $i \le j$, then the Taylor sums of degree $j$ of $D$ and $D'$ are equal. -/
theorem taylorSum_congr {D D' : FormalMultilinearSeries ℝ E F} {j : ℕ}
    (h : ∀ i ≤ j, D i = D' i) : D.taylorSum j = D'.taylorSum j := by
  funext d
  simp only [taylorSum_def]
  exact sum_congr rfl fun i hi => by rw [h i (Nat.lt_succ_iff.1 (mem_range.1 hi))]

end TaylorSumTail

section Decrement

variable (D D' : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)

/-- The **decrement** of the Taylor sum of real-valued data along $s$:
$$\Delta T_p(s) = T_p(0) - T_p(s).$$

This is (12.1.11) of [cartis2022evaluation], the predicted decrease of model-based methods. -/
noncomputable def taylorDecrement (s : E) : ℝ :=
  D.taylorSum p 0 - D.taylorSum p s

/-- The definition of the decrement: $\Delta T_p(s) = T_p(0) - T_p(s)$. -/
theorem taylorDecrement_def (s : E) :
    D.taylorDecrement p s = D.taylorSum p 0 - D.taylorSum p s :=
  rfl

/-- The constant terms cancel in the decrement: $\Delta T_p(s) = -\sum_{i=1}^{p} \frac{1}{i!}
D_i[s]^i$. -/
theorem taylorDecrement_eq (s : E) :
    D.taylorDecrement p s = -∑ i ∈ Icc 1 p, (i ! : ℝ)⁻¹ * D i (fun _ => s) := by
  rw [taylorDecrement, taylorSum_zero_right, taylorSum_eq_add]
  simp only [smul_eq_mul]
  ring

/-- The decrement at $s = 0$ is $0$. -/
@[simp]
theorem taylorDecrement_zero_right : D.taylorDecrement p 0 = 0 := sub_self _

/-- The decrement of $D - D'$ is the difference of the decrements of $D$ and $D'$. -/
@[simp]
theorem taylorDecrement_sub (s : E) :
    (D - D').taylorDecrement p s = D.taylorDecrement p s - D'.taylorDecrement p s := by
  simp only [taylorDecrement, taylorSum_sub]
  ring

/-- For every $s \in E$, $|\Delta T_p(s)| \le \sum_{i=1}^{p} \|D_i\| \, \|s\|^i / i!$. -/
theorem abs_taylorDecrement_le (s : E) :
    |D.taylorDecrement p s| ≤ ∑ i ∈ Icc 1 p, ‖D i‖ * ‖s‖ ^ i / i ! := by
  rw [taylorDecrement_eq, abs_neg]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_inv, Nat.abs_cast, inv_mul_eq_div]
  gcongr
  exact D.norm_apply_diagonal_le i s

/-- Comparison of the decrements of two derivative data $D$ (exact) and $D'$ (inexact), (13.1.3) of
[cartis2022evaluation]. For every $s \in E$,
$$|\Delta T_p(s) - \Delta T'_p(s)| \le \sum_{i=1}^{p} \|D_i - D'_i\| \, \|s\|^i / i!,$$
where $\Delta T'_p$ is the decrement of $D'$. -/
theorem abs_taylorDecrement_sub_le (s : E) :
    |D.taylorDecrement p s - D'.taylorDecrement p s| ≤
      ∑ i ∈ Icc 1 p, ‖D i - D' i‖ * ‖s‖ ^ i / i ! := by
  rw [← taylorDecrement_sub]
  exact abs_taylorDecrement_le (D - D') p s

/-- The decrement is bounded on balls: if $\|s\| \le \delta$, then $|\Delta T_p(s)| \le
\sum_{i=1}^{p} \|D_i\| \, \delta^i / i!$. -/
theorem abs_taylorDecrement_le_of_norm_le {s : E} {δ : ℝ} (hs : ‖s‖ ≤ δ) :
    |D.taylorDecrement p s| ≤ ∑ i ∈ Icc 1 p, ‖D i‖ * δ ^ i / i ! := by
  refine (D.abs_taylorDecrement_le p s).trans (sum_le_sum fun i _ => ?_)
  gcongr

/-- The first-order decrement is $\Delta T_1(s) = -D_1[s]$. -/
theorem taylorDecrement_one_apply (s : E) : D.taylorDecrement 1 s = -D 1 (fun _ => s) := by
  rw [taylorDecrement_eq]
  simp

/-- Recursion in the degree: $\Delta T_{j+1}(s) = \Delta T_j(s) - \frac{1}{(j+1)!}
D_{j+1}[s]^{j+1}$. -/
theorem taylorDecrement_succ (j : ℕ) (s : E) :
    D.taylorDecrement (j + 1) s =
      D.taylorDecrement j s - ((j + 1)! : ℝ)⁻¹ * D (j + 1) fun _ => s := by
  have h0 : (D (j + 1) fun _ => (0 : E)) = 0 := (D (j + 1)).map_coord_zero (0 : Fin (j + 1)) rfl
  simp only [taylorDecrement, taylorSum_succ, smul_eq_mul, h0, mul_zero, add_zero]
  ring

/-- The second-order decrement is $\Delta T_2(s) = -D_1[s] - \frac{1}{2} D_2[s]^2$. -/
theorem taylorDecrement_two (s : E) :
    D.taylorDecrement 2 s = -(D 1 fun _ => s) - 2⁻¹ * D 2 fun _ => s := by
  rw [taylorDecrement_succ, taylorDecrement_one_apply]
  norm_num [Nat.factorial]

/-- The third-order decrement is $\Delta T_3(s) = -D_1[s] - \frac{1}{2} D_2[s]^2 - \frac{1}{6}
D_3[s]^3$. -/
theorem taylorDecrement_three (s : E) :
    D.taylorDecrement 3 s = -(D 1 fun _ => s) - 2⁻¹ * (D 2 fun _ => s) - 6⁻¹ * D 3 fun _ => s := by
  rw [taylorDecrement_succ, taylorDecrement_two]
  norm_num [Nat.factorial]

/-- For $j \le p$, $\Delta T_p(s) = \Delta T_j(s) - \sum_{\ell=j+1}^{p} \frac{1}{\ell!}
D_\ell[s]^\ell$. -/
theorem taylorDecrement_eq_sub_sum {j p : ℕ} (hjp : j ≤ p) (s : E) :
    D.taylorDecrement p s =
      D.taylorDecrement j s - ∑ ℓ ∈ Finset.Icc (j + 1) p, ((ℓ ! : ℝ))⁻¹ * D ℓ fun _ => s := by
  have h := D.taylorSum_sub_taylorSum hjp s
  simp only [smul_eq_mul] at h
  rw [taylorDecrement, taylorDecrement, taylorSum_zero_right, taylorSum_zero_right, ← h]
  ring

/-- The decrement $s \mapsto \Delta T_p(s)$ is continuous. -/
theorem continuous_taylorDecrement : Continuous (D.taylorDecrement p) :=
  continuous_const.sub (D.contDiff_taylorSum p (n := 0)).continuous

end Decrement

end FormalMultilinearSeries

section TaylorPolynomial

/-- The **Taylor polynomial** of degree $p$ of $f : E \to F$ at $x$, as a function of the increment
$s$:
$$T_{f,p}(x, s) = \sum_{i=0}^{p} \frac{1}{i!} \nabla^i f(x)[s]^i.$$

This is the $T_{f,p}(x, s)$ of (A.10) of [cartis2022evaluation]. It is the Taylor sum of the jet
`ftaylorSeries ℝ f x`. No smoothness of $f$ is assumed: where $f$ is not differentiable,
$\nabla^i f(x)$ has the value that Mathlib gives to `iteratedFDeriv`. -/
noncomputable def taylorPolynomial (f : E → F) (p : ℕ) (x : E) : E → F :=
  (ftaylorSeries ℝ f x).taylorSum p

/-- The Taylor polynomial of $f$ at $x$ is the Taylor sum of the jet `ftaylorSeries ℝ f x`. -/
theorem taylorPolynomial_eq_taylorSum (f : E → F) (p : ℕ) (x : E) :
    taylorPolynomial f p x = (ftaylorSeries ℝ f x).taylorSum p := rfl

/-- The Taylor polynomial in expanded form: $T_{f,p}(x, s) = \sum_{i=0}^{p} \frac{1}{i!} \nabla^i
f(x)[s]^i$. -/
theorem taylorPolynomial_apply (f : E → F) (p : ℕ) (x s : E) :
    taylorPolynomial f p x s =
      ∑ i ∈ range (p + 1), (i ! : ℝ)⁻¹ • iteratedFDeriv ℝ i f x (fun _ => s) := rfl

/-- The Taylor polynomial of the zero function is $0$. -/
@[simp]
theorem taylorPolynomial_zero_fun (p : ℕ) (x s : E) :
    taylorPolynomial (fun _ : E => (0 : F)) p x s = 0 := by
  rw [taylorPolynomial_apply]
  simp

/-- At the increment $s = 0$ the Taylor polynomial is the value: $T_{f,p}(x, 0) = f(x)$. -/
@[simp]
theorem taylorPolynomial_zero_right (f : E → F) (p : ℕ) (x : E) :
    taylorPolynomial f p x 0 = f x := by
  simp [taylorPolynomial_eq_taylorSum, ftaylorSeries, iteratedFDeriv_zero_apply]

/-- The decrement of the exact data of $f : E \to \mathbb{R}$ is
$\Delta T_{f,p}(x, s) = f(x) - T_{f,p}(x, s)$, as in (12.1.11) of [cartis2022evaluation]. -/
theorem ftaylorSeries_taylorDecrement_eq (f : E → ℝ) (p : ℕ) (x s : E) :
    (ftaylorSeries ℝ f x).taylorDecrement p s = f x - taylorPolynomial f p x s := by
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_right]

/-- The Taylor polynomial $s \mapsto T_{f,p}(x, s)$ is $C^n$ for every $n$. -/
theorem contDiff_taylorPolynomial (f : E → F) (p : ℕ) (x : E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (taylorPolynomial f p x) :=
  FormalMultilinearSeries.contDiff_taylorSum _ _

/-- If $f$ is $C^n$ at $x$, then its jet `ftaylorSeries ℝ f x` is symmetric up to every order
$p \le n$. -/
theorem ContDiffAt.isSymm_ftaylorSeries {f : E → F} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f x) {p : ℕ} (hp : (p : WithTop ℕ∞) ≤ n) :
    (ftaylorSeries ℝ f x).IsSymm p :=
  fun _ hi σ v => hf.iteratedFDeriv_comp_perm_of_le ((Nat.cast_le.2 hi).trans hp) σ v

/-- The Taylor polynomial has the jet of $f$ at $s = 0$. If $f$ is $C^p$ at $x$, then for $j \le p$
$$\nabla^j_s T_{f,p}(x, 0) = \nabla^j f(x).$$

This is (A.11) of [cartis2022evaluation] at $s = 0$. -/
theorem iteratedFDeriv_taylorPolynomial_zero {f : E → F} {x : E} {p : ℕ}
    (hf : ContDiffAt ℝ p f x) {j : ℕ} (hj : j ≤ p) :
    iteratedFDeriv ℝ j (taylorPolynomial f p x) 0 = iteratedFDeriv ℝ j f x :=
  FormalMultilinearSeries.iteratedFDeriv_taylorSum_zero (hf.isSymm_ftaylorSeries le_rfl) hj

/-- The top derivative of the Taylor polynomial is constant. If $f$ is $C^p$ at $x$, then
$\nabla^p_s T_{f,p}(x, s) = \nabla^p f(x)$ for every $s \in E$. -/
theorem iteratedFDeriv_taylorPolynomial_self {f : E → F} {x : E} {p : ℕ}
    (hf : ContDiffAt ℝ p f x) (s : E) :
    iteratedFDeriv ℝ p (taylorPolynomial f p x) s = iteratedFDeriv ℝ p f x :=
  FormalMultilinearSeries.iteratedFDeriv_taylorSum_self (hf.isSymm_ftaylorSeries le_rfl) s

end TaylorPolynomial
