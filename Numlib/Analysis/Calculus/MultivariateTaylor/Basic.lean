import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Multivariate Taylor polynomials from derivative data

Derivative data `D : FormalMultilinearSeries ℝ E F` (`D i : E [×i]→L[ℝ] F`, `E`, `F` real normed
spaces) plays the role of the jet `(f(x), ∇f(x), …, ∇^p f(x))` of a function `f : E → F` at `x`
(real-valued objectives and vector-valued constraint maps alike); exact data is Mathlib's
`ftaylorSeries ℝ f x`, whose `i`-th term is `iteratedFDeriv ℝ i f x`, while inexact derivative
estimates ([cartis2022evaluation], Chapter 13) are arbitrary data. The book's `∇^i f(x)[s]^i` is
`iteratedFDeriv ℝ i f x (fun _ => s)`. Unlike `FormalMultilinearSeries.partialSum` (power series
convention), the Taylor sums here carry the factorials.

## Main definitions

* `FormalMultilinearSeries.taylorSum D p s = ∑_{i ≤ p} (1/i!) D_i [s]^i`, linear in `D`
  (`taylorSum_add`, …) with the recursion `taylorSum_succ`;
* `FormalMultilinearSeries.taylorDecrement D p s = T_p(0) - T_p(s)` for real-valued data, the
  decrease `ΔT_p` of [cartis2022evaluation], (12.1.11);
* `FormalMultilinearSeries.IsSymm D p`: the data is invariant under permutations of arguments up
  to order `p`;
* `taylorPolynomial f p x s`, the Taylor polynomial `T_{f,p}(x, s)` of (A.10).

## Main results

* `ContDiffAt.iteratedFDeriv_comp_perm_of_le`: the `i`-th derivative of a function that is `C^n`
  at `x` is symmetric for `i ≤ n` (Mathlib has the second-order case
  `ContDiffAt.isSymmSndFDerivAt`);
* `ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal_apply_of_comp_perm`: the derivatives of
  `s ↦ A[s]^n` for symmetric `A`;
* `FormalMultilinearSeries.iteratedFDeriv_taylorSum_apply`: formula (A.11) for the derivatives
  of the Taylor sum, with the corollaries `iteratedFDeriv_taylorSum_zero` (the jet at `0` is the
  data), `iteratedFDeriv_taylorSum_self` (constant top derivative) and `fderiv_taylorSum_apply`;
* `FormalMultilinearSeries.abs_taylorDecrement_sub_le`: decrements of exact and inexact data
  differ by at most `∑ ‖D_i - D'_i‖ ‖s‖^i / i!` ((13.1.3));
* `iteratedFDeriv_taylorPolynomial_zero`, `iteratedFDeriv_taylorPolynomial_self`.
-/

open Finset Function
open scoped Nat Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

section Symmetry

/-- A continuous multilinear map invariant under every transposition of its arguments is invariant
under every permutation of its arguments. -/
theorem ContinuousMultilinearMap.apply_comp_perm_of_swap {n : ℕ} (A : E [×n]→L[ℝ] F)
    (h : ∀ a b : Fin n, a ≠ b → ∀ v : Fin n → E, A (v ∘ Equiv.swap a b) = A v)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → E) : A (v ∘ σ) = A v := by
  induction σ using Equiv.Perm.swap_induction_on generalizing v with
  | one => rfl
  | swap_mul f a b hab ih =>
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, ih, h a b hab]

/-- The `(k+2)`-nd derivative as the second derivative of the `k`-th derivative. -/
private theorem iteratedFDeriv_add_two_apply (f : E → F) (x : E) (k : ℕ) (v : Fin (k + 2) → E) :
    iteratedFDeriv ℝ (k + 2) f x v =
      fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ k f)) x (v 0) (v 1) (Fin.tail (Fin.tail v)) := by
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left,
    LinearIsometryEquiv.comp_fderiv]
  simp [continuousMultilinearCurryLeftEquiv_symm_apply, Fin.tail]

/-- If the `k`-th derivative is invariant under a permutation `τ` of its arguments near `x`, then
the `(k+1)`-st derivative at `x` is invariant under `τ` acting on its last `k` arguments. -/
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

/-- **Symmetry of iterated derivatives.** If `f` is `C^n` at `x`, then for every `i ≤ n` the
`i`-th derivative `iteratedFDeriv ℝ i f x` is invariant under permutations of its arguments
([cartis2022evaluation], Section A.6). Proved by induction from the symmetry of second derivatives
(`ContDiffAt.isSymmSndFDerivAt`), transpositions generating the symmetric group. -/
theorem ContDiffAt.iteratedFDeriv_comp_perm_of_le {f : E → F} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f x) {i : ℕ} (hi : (i : WithTop ℕ∞) ≤ n) (σ : Equiv.Perm (Fin i))
    (v : Fin i → E) :
    iteratedFDeriv ℝ i f x (v ∘ σ) = iteratedFDeriv ℝ i f x v :=
  iteratedFDeriv_comp_perm_aux i (hf.of_le hi) le_rfl σ v

end Symmetry

section Diagonal

/-- Homogeneity of a diagonal value: `A[t d]^n = t^n A[d]^n`. -/
theorem ContinuousMultilinearMap.apply_smul_diag {n : ℕ} (A : E [×n]→L[ℝ] F) (t : ℝ) (d : E) :
    A (fun _ => t • d) = t ^ n • A (fun _ => d) := by
  rw [A.map_smul_univ (fun _ => t) (fun _ => d), prod_const, card_univ, Fintype.card_fin]

/-- The iterated derivative at an arbitrary point `s` of the restriction `y ↦ A (y, …, y)` of a
continuous multilinear map to the diagonal: the sum over all placements (embeddings
`Fin j ↪ Fin n`) of the `j` directions `v` among the `n` arguments, the other arguments being `s`.
At `s = 0` this is `ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal`. -/
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

/-- For a continuous multilinear map `A` of order `n` invariant under permutations of its
arguments, the `j`-th derivative of `y ↦ A (y, …, y)` at `s` is
`n (n-1) ⋯ (n-j+1) · A (v₀, …, v_{j-1}, s, …, s)`. -/
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

/-- The degree-`p` Taylor sum of derivative data `D`:
`D.taylorSum p s = ∑_{i ≤ p} (1/i!) D_i [s]^i`. With `D = ftaylorSeries ℝ f x` this is the Taylor
polynomial `T_{f,p}(x, s)` of [cartis2022evaluation], (A.10); for inexact derivative data it is the
model of their (13.1.1). The `i = 0` term is `D 0` applied to the empty tuple. -/
noncomputable def taylorSum (s : E) : F :=
  ∑ i ∈ range (p + 1), (i ! : ℝ)⁻¹ • D i (fun _ => s)

theorem taylorSum_def (s : E) :
    D.taylorSum p s = ∑ i ∈ range (p + 1), (i ! : ℝ)⁻¹ • D i (fun _ => s) := rfl

/-- Recursion in the degree: `T_{p+1}(s) = T_p(s) + (1/(p+1)!) D_{p+1}[s]^{p+1}`. -/
theorem taylorSum_succ (s : E) :
    D.taylorSum (p + 1) s = D.taylorSum p s + ((p + 1)! : ℝ)⁻¹ • D (p + 1) (fun _ => s) := by
  rw [taylorSum_def, sum_range_succ, ← taylorSum_def]

@[simp]
theorem taylorSum_add (s : E) : (D + D').taylorSum p s = D.taylorSum p s + D'.taylorSum p s := by
  simp [taylorSum_def, sum_add_distrib, smul_add]

@[simp]
theorem taylorSum_sub (s : E) : (D - D').taylorSum p s = D.taylorSum p s - D'.taylorSum p s := by
  simp [taylorSum_def, sum_sub_distrib, smul_sub]

@[simp]
theorem taylorSum_neg (s : E) : (-D).taylorSum p s = -D.taylorSum p s := by
  simp [taylorSum_def, sum_neg_distrib, smul_neg]

@[simp]
theorem taylorSum_smul (c : ℝ) (s : E) : (c • D).taylorSum p s = c • D.taylorSum p s := by
  simp [taylorSum_def, smul_sum, smul_comm c]

/-- The Taylor sum split into its constant term and the terms of order `1` to `p`. -/
theorem taylorSum_eq_add (s : E) :
    D.taylorSum p s = D 0 0 + ∑ i ∈ Icc 1 p, (i ! : ℝ)⁻¹ • D i (fun _ => s) := by
  rw [taylorSum_def, range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos p),
    ← Ico_add_one_right_eq_Icc]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, zero_add]
  congr 2
  exact Subsingleton.elim _ _

/-- At `s = 0` only the constant term survives. -/
@[simp]
theorem taylorSum_zero_right : D.taylorSum p 0 = D 0 0 := by
  rw [taylorSum_eq_add, add_eq_left]
  refine sum_eq_zero fun i hi => ?_
  have : Nonempty (Fin i) := ⟨⟨0, (mem_Icc.1 hi).1⟩⟩
  simp [← Pi.zero_def, ContinuousMultilinearMap.map_zero]

/-- `‖D_i [s]^i‖ ≤ ‖D_i‖ ‖s‖^i`. -/
theorem norm_apply_diagonal_le (i : ℕ) (s : E) : ‖D i (fun _ => s)‖ ≤ ‖D i‖ * ‖s‖ ^ i := by
  calc ‖D i (fun _ => s)‖ ≤ ‖D i‖ * ∏ _j : Fin i, ‖s‖ := (D i).le_opNorm _
    _ = ‖D i‖ * ‖s‖ ^ i := by rw [prod_const, card_univ, Fintype.card_fin]

/-- The data are *symmetric up to order `p`*: each `D i`, `i ≤ p`, is invariant under
permutations of its arguments, as derivative tensors are ([cartis2022evaluation], Section A.6). -/
def IsSymm : Prop :=
  ∀ i ≤ p, ∀ (σ : Equiv.Perm (Fin i)) (v : Fin i → E), D i (v ∘ σ) = D i v

variable {D p}

theorem IsSymm.mono {q : ℕ} (hD : D.IsSymm p) (hq : q ≤ p) : D.IsSymm q :=
  fun i hi => hD i (hi.trans hq)

variable (D p)

/-- Each term `s ↦ D_i [s]^i` is smooth. -/
theorem contDiff_apply_diagonal {n : WithTop ℕ∞} (i : ℕ) :
    ContDiff ℝ n (fun s : E => D i (fun _ => s)) :=
  (D i).contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)

/-- The Taylor sum is smooth (a polynomial) in `s`. -/
theorem contDiff_taylorSum {n : WithTop ℕ∞} : ContDiff ℝ n (D.taylorSum p) :=
  ContDiff.sum fun i _ => (D.contDiff_apply_diagonal i).const_smul _

variable {D p}

/-- **Derivatives of the Taylor sum** ([cartis2022evaluation], (A.11)). For symmetric data, the
`j`-th derivative of `s ↦ T_p(s)` is `∑_{ℓ=j}^p (1/(ℓ-j)!) D_ℓ [v, s^{ℓ-j}]`, the first `j`
arguments of `D_ℓ` being the directions `v` and the remaining `ℓ - j` being `s`; it vanishes for
`j > p`. -/
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

/-- At `s = 0` the derivatives of the Taylor sum are the data: `∇^j T_p(0) = D_j` for `j ≤ p`. -/
theorem iteratedFDeriv_taylorSum_zero (hD : D.IsSymm p) {j : ℕ} (hj : j ≤ p) :
    iteratedFDeriv ℝ j (D.taylorSum p) 0 = D j := by
  ext v
  rw [iteratedFDeriv_taylorSum_apply hD, sum_eq_single_of_mem j (mem_Icc.2 ⟨le_rfl, hj⟩)]
  · simp
  · intro ℓ hℓ hne
    have hjℓ : j < ℓ := lt_of_le_of_ne (mem_Icc.1 hℓ).1 (Ne.symm hne)
    rw [(D ℓ).map_coord_zero ⟨j, hjℓ⟩ (by simp), smul_zero]

/-- The top-order derivative of the Taylor sum is constant: `∇^p T_p(s) = D_p`. -/
theorem iteratedFDeriv_taylorSum_self (hD : D.IsSymm p) (s : E) :
    iteratedFDeriv ℝ p (D.taylorSum p) s = D p := by
  ext v
  rw [iteratedFDeriv_taylorSum_apply hD, Icc_self, sum_singleton]
  simp

/-- The derivative of the Taylor sum (case `j = 1` of (A.11)):
`∇T_p(s)[w] = ∑_{ℓ=1}^p (1/(ℓ-1)!) D_ℓ [w, s^{ℓ-1}]`. -/
theorem fderiv_taylorSum_apply (hD : D.IsSymm p) (s w : E) :
    fderiv ℝ (D.taylorSum p) s w =
      ∑ ℓ ∈ Icc 1 p, ((ℓ - 1)! : ℝ)⁻¹ • D ℓ (fun i => if (i : ℕ) = 0 then w else s) := by
  rw [← iteratedFDeriv_one_apply (m := fun _ => w), iteratedFDeriv_taylorSum_apply hD]
  simp

end TaylorSum

section Decrement

variable (D D' : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)

/-- The decrease `ΔT_p(s) = T_p(0) - T_p(s)` of the Taylor sum along `s`
([cartis2022evaluation], (12.1.11)), the "predicted decrease" of model-based methods. -/
noncomputable def taylorDecrement (s : E) : ℝ :=
  D.taylorSum p 0 - D.taylorSum p s

/-- `ΔT_p(s) = -∑_{i=1}^p (1/i!) D_i [s]^i`: the constant terms cancel. -/
theorem taylorDecrement_eq (s : E) :
    D.taylorDecrement p s = -∑ i ∈ Icc 1 p, (i ! : ℝ)⁻¹ * D i (fun _ => s) := by
  rw [taylorDecrement, taylorSum_zero_right, taylorSum_eq_add]
  simp only [smul_eq_mul]
  ring

@[simp]
theorem taylorDecrement_zero_right : D.taylorDecrement p 0 = 0 := sub_self _

@[simp]
theorem taylorDecrement_sub (s : E) :
    (D - D').taylorDecrement p s = D.taylorDecrement p s - D'.taylorDecrement p s := by
  simp only [taylorDecrement, taylorSum_sub]
  ring

/-- `|ΔT_p(s)| ≤ ∑_{i=1}^p ‖D_i‖ ‖s‖^i / i!`. -/
theorem abs_taylorDecrement_le (s : E) :
    |D.taylorDecrement p s| ≤ ∑ i ∈ Icc 1 p, ‖D i‖ * ‖s‖ ^ i / i ! := by
  rw [taylorDecrement_eq, abs_neg]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_inv, Nat.abs_cast, inv_mul_eq_div]
  gcongr
  exact D.norm_apply_diagonal_le i s

/-- Comparison of the decrements of two derivative data `D` (exact) and `D'` (inexact)
([cartis2022evaluation], (13.1.3)):
`|ΔT_p(s) - ΔT'_p(s)| ≤ ∑_{i=1}^p ‖D_i - D'_i‖ ‖s‖^i / i!`. -/
theorem abs_taylorDecrement_sub_le (s : E) :
    |D.taylorDecrement p s - D'.taylorDecrement p s| ≤
      ∑ i ∈ Icc 1 p, ‖D i - D' i‖ * ‖s‖ ^ i / i ! := by
  rw [← taylorDecrement_sub]
  exact abs_taylorDecrement_le (D - D') p s

/-- The Taylor decrement is bounded on balls: `|ΔT_p(s)| ≤ ∑_{i=1}^p ‖D_i‖ δ^i / i!` for
`‖s‖ ≤ δ`. -/
theorem abs_taylorDecrement_le_of_norm_le {s : E} {δ : ℝ} (hs : ‖s‖ ≤ δ) :
    |D.taylorDecrement p s| ≤ ∑ i ∈ Icc 1 p, ‖D i‖ * δ ^ i / i ! := by
  refine (D.abs_taylorDecrement_le p s).trans (sum_le_sum fun i _ => ?_)
  gcongr

/-- The first-order Taylor decrement is `-D₁[s]`. -/
theorem taylorDecrement_one_apply (s : E) : D.taylorDecrement 1 s = -D 1 (fun _ => s) := by
  rw [taylorDecrement_eq]
  simp

/-- `ΔT_{j+1}(s) = ΔT_j(s) - (1/(j+1)!) D_{j+1}[s]^{j+1}`. -/
theorem taylorDecrement_succ (j : ℕ) (s : E) :
    D.taylorDecrement (j + 1) s =
      D.taylorDecrement j s - ((j + 1)! : ℝ)⁻¹ * D (j + 1) fun _ => s := by
  have h0 : (D (j + 1) fun _ => (0 : E)) = 0 := (D (j + 1)).map_coord_zero (0 : Fin (j + 1)) rfl
  simp only [taylorDecrement, taylorSum_succ, smul_eq_mul, h0, mul_zero, add_zero]
  ring

/-- `ΔT_2(s) = -D_1[s] - ½ D_2[s]^2`. -/
theorem taylorDecrement_two (s : E) :
    D.taylorDecrement 2 s = -(D 1 fun _ => s) - 2⁻¹ * D 2 fun _ => s := by
  rw [taylorDecrement_succ, taylorDecrement_one_apply]
  norm_num [Nat.factorial]

/-- `ΔT_3(s) = -D_1[s] - ½ D_2[s]^2 - (1/6) D_3[s]^3`. -/
theorem taylorDecrement_three (s : E) :
    D.taylorDecrement 3 s = -(D 1 fun _ => s) - 2⁻¹ * (D 2 fun _ => s) - 6⁻¹ * D 3 fun _ => s := by
  rw [taylorDecrement_succ, taylorDecrement_two]
  norm_num [Nat.factorial]

/-- `ΔT_p(s) = ΔT_j(s) - ∑_{ℓ=j+1}^{p} (1/ℓ!) D_ℓ[s]^ℓ` for `j ≤ p`. -/
theorem taylorDecrement_eq_sub_sum {j p : ℕ} (hjp : j ≤ p) (s : E) :
    D.taylorDecrement p s =
      D.taylorDecrement j s - ∑ ℓ ∈ Finset.Icc (j + 1) p, ((ℓ ! : ℝ))⁻¹ * D ℓ fun _ => s := by
  induction p, hjp using Nat.le_induction with
  | base => simp
  | succ p hjp ih =>
    rw [taylorDecrement_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    ring

/-- The Taylor decrement is continuous. -/
theorem continuous_taylorDecrement : Continuous (D.taylorDecrement p) :=
  continuous_const.sub (D.contDiff_taylorSum p (n := 0)).continuous

end Decrement

end FormalMultilinearSeries

section TaylorPolynomial

/-- The degree-`p` Taylor polynomial of `f` at `x`, as a function of the increment `s`:
`taylorPolynomial f p x s = ∑_{i ≤ p} (1/i!) ∇^i f(x)[s]^i`, the `T_{f,p}(x, s)` of
[cartis2022evaluation], (A.10). It is the Taylor sum of the jet `ftaylorSeries ℝ f x`. -/
noncomputable def taylorPolynomial (f : E → F) (p : ℕ) (x : E) : E → F :=
  (ftaylorSeries ℝ f x).taylorSum p

theorem taylorPolynomial_eq_taylorSum (f : E → F) (p : ℕ) (x : E) :
    taylorPolynomial f p x = (ftaylorSeries ℝ f x).taylorSum p := rfl

theorem taylorPolynomial_apply (f : E → F) (p : ℕ) (x s : E) :
    taylorPolynomial f p x s =
      ∑ i ∈ range (p + 1), (i ! : ℝ)⁻¹ • iteratedFDeriv ℝ i f x (fun _ => s) := rfl

/-- At zero increment the Taylor polynomial is the value: `T_{f,p}(x, 0) = f(x)`. -/
@[simp]
theorem taylorPolynomial_zero_right (f : E → F) (p : ℕ) (x : E) :
    taylorPolynomial f p x 0 = f x := by
  simp [taylorPolynomial_eq_taylorSum, ftaylorSeries, iteratedFDeriv_zero_apply]

/-- The Taylor decrement of exact data is `ΔT_{f,p}(x, s) = f(x) - T_{f,p}(x, s)`
([cartis2022evaluation], (12.1.11)). -/
theorem ftaylorSeries_taylorDecrement_eq (f : E → ℝ) (p : ℕ) (x s : E) :
    (ftaylorSeries ℝ f x).taylorDecrement p s = f x - taylorPolynomial f p x s := by
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_right]

/-- The Taylor polynomial is smooth in the increment. -/
theorem contDiff_taylorPolynomial (f : E → F) (p : ℕ) (x : E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (taylorPolynomial f p x) :=
  FormalMultilinearSeries.contDiff_taylorSum _ _

/-- The jet of a function `C^n` at `x` is symmetric up to every order `p ≤ n`. -/
theorem ContDiffAt.isSymm_ftaylorSeries {f : E → F} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f x) {p : ℕ} (hp : (p : WithTop ℕ∞) ≤ n) :
    (ftaylorSeries ℝ f x).IsSymm p :=
  fun _ hi σ v => hf.iteratedFDeriv_comp_perm_of_le ((Nat.cast_le.2 hi).trans hp) σ v

/-- The Taylor polynomial has the jet of `f` at `s = 0`: `∇^j_s T_{f,p}(x, 0) = ∇^j f(x)` for
`j ≤ p` ([cartis2022evaluation], (A.11) at `s = 0`). -/
theorem iteratedFDeriv_taylorPolynomial_zero {f : E → F} {x : E} {p : ℕ}
    (hf : ContDiffAt ℝ p f x) {j : ℕ} (hj : j ≤ p) :
    iteratedFDeriv ℝ j (taylorPolynomial f p x) 0 = iteratedFDeriv ℝ j f x :=
  FormalMultilinearSeries.iteratedFDeriv_taylorSum_zero (hf.isSymm_ftaylorSeries le_rfl) hj

/-- The top derivative of the Taylor polynomial is constant: `∇^p_s T_{f,p}(x, s) = ∇^p f(x)`. -/
theorem iteratedFDeriv_taylorPolynomial_self {f : E → F} {x : E} {p : ℕ}
    (hf : ContDiffAt ℝ p f x) (s : E) :
    iteratedFDeriv ℝ p (taylorPolynomial f p x) s = iteratedFDeriv ℝ p f x :=
  FormalMultilinearSeries.iteratedFDeriv_taylorSum_self (hf.isSymm_ftaylorSeries le_rfl) s

end TaylorPolynomial
