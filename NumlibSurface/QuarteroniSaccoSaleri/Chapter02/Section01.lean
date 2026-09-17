import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Conditioning.Problem

/-!
# Quarteroni–Sacco–Saleri §2.1: well-posedness and condition number of a problem

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §2.1. The book's problem is `F(x, d) = 0` with datum `d` and solution
`x = G(d)`; its vocabulary — the continuous-dependence condition (2.3), the relative and absolute
condition numbers of Definition 2.1 and the first-order formula (2.7) — is the backbone
`Numlib/Conditioning/Problem`, read here over `ℝ` and on the book's concrete data.

## Definitions and their bridges

* `definition_2_1_rel`, `definition_2_1_abs` — the relative and absolute condition numbers (2.4)
  and (2.5), as suprema over a set `N` of admissible perturbations, valued in `ℝ≥0∞` as in the
  backbone so that "the condition number is infinite" (Remark 2.1) is a value. They are
  `Conditioning.relCondNumberOn` and `Conditioning.absCondNumberOn` by `rfl`
  (`definition_2_1_rel_eq`, `definition_2_1_abs_eq`), and `definition_2_1_rel_eq_abs_mul` is the
  relation between the two.
* `equation_2_3_iff` — the Lipschitz condition (2.3) at radius `η` is finiteness of the absolute
  condition number over the perturbations of size `< η`.

## The first-order formula

* `equation_2_7_abs`, `equation_2_7_rel` — (2.7) as equalities for the first-order condition
  numbers `Conditioning.absCondNumber`, `Conditioning.relCondNumber` (the limits as the
  perturbation size tends to zero, which is what the book's `≃` computes).
* `equation_2_7_jacobian` — the case `G : ℝⁿ → ℝᵐ` with a Jacobian matrix and the `2`-operator
  norm "associated with the vector norm (1.19)".
* `equation_2_7_rel_deriv` — the relative form for a scalar datum `d : ℝ`, in real numbers, which
  is how Examples 2.2 and 2.7 read it.

## The Examples

Each Example states a computable fact and is a theorem. `example_2_1` counts the real roots of
`x⁴ - x²(2a - 1) + a(a - 1)` with multiplicity; `example_2_2` is (2.8) made exact in the Euclidean
norm, with `example_2_2_le_sqrt_two` for the separated roots and `example_2_2_reparam` for the
reparametrized problem; `remark_2_1` is the double root at `p = 1`, continuous dependence on
`[1, ∞)` with infinite condition number; `example_2_3` is (2.9), the bound `K(b) ≤ κ(A)` for a
linear system perturbed in its right-hand side, with the first equality of (2.9) as
`example_2_3_eq`; `example_2_4` and `example_2_4_rel` are (2.11) and (2.10) for the root of
`φ(x) = d`, and `example_2_4_multiple_root` the multiple root; `cosSubOne_absCondNumberWithin` is
the unnumbered example closing the section, where the first-order number underestimates the true
one.

## Readings

The book's `≃` in (2.7)–(2.11) is read as an equality for the first-order condition number, and
the book's "the problem is thus ill posed if `x` is a multiple root" (Example 2.4) as infinite
conditioning: the root may depend continuously on the datum, as the book's own Remark 2.1
observes one page earlier. The book's real values appear through `ENNReal.ofReal`.
-/

open Conditioning Filter Polynomial Set Topology
open scoped ENNReal Real

namespace QuarteroniSaccoSaleri.Chapter02

/-! ### Example 2.1: counting real roots is ill posed -/

/-- The polynomial `x⁴ - x²(2a - 1) + a(a - 1)` of Example 2.1, a real polynomial depending on
the parameter `a`. -/
noncomputable def example_2_1_polynomial (a : ℝ) : ℝ[X] :=
  X ^ 4 - C (2 * a - 1) * X ^ 2 + C (a * (a - 1))

-- TODO(backbone): a Mathlib-shaped fact about real quadratics, with no home in the backbone yet.
/-- The real roots of `X ^ 2 - C c`, counted with multiplicity: two (`±√c`, a double root `0` at
`c = 0`) when `0 ≤ c`, none when `c < 0`. -/
theorem card_roots_X_sq_sub_C (c : ℝ) :
    Multiset.card (X ^ 2 - C c : ℝ[X]).roots = if 0 ≤ c then 2 else 0 := by
  split_ifs with hc
  · have h : (X ^ 2 - C c : ℝ[X]) = (X - C √c) * (X - C (-√c)) := by
      conv_lhs => rw [← Real.sq_sqrt hc, C_pow]
      rw [C_neg]; ring
    rw [h, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
      roots_X_sub_C]
    simp
  · rw [Multiset.card_eq_zero]
    refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
    rw [mem_roots (X_pow_sub_C_ne_zero two_pos c), IsRoot.def] at hx
    simp at hx
    nlinarith [sq_nonneg x]

/-- **Example 2.1.** The number of real roots of `x⁴ - x²(2a - 1) + a(a - 1)`, counted with
multiplicity, is `4` if `a ≥ 1`, `2` if `a ∈ [0, 1)` and `0` if `a < 0`: it varies discontinuously
as `a` varies continuously, so finding the number of real roots of a polynomial is an ill-posed
problem. (The polynomial is `(x² - a)(x² - (a - 1))`; the book's counts are with multiplicity,
`a = 1` giving `±1` and a double root `0`.) -/
theorem example_2_1 (a : ℝ) :
    Multiset.card (example_2_1_polynomial a).roots =
      if 1 ≤ a then 4 else if 0 ≤ a then 2 else 0 := by
  have h : example_2_1_polynomial a = (X ^ 2 - C a) * (X ^ 2 - C (a - 1)) := by
    simp only [example_2_1_polynomial, map_sub, map_mul, map_one, map_ofNat]; ring
  rw [h, roots_mul (mul_ne_zero (X_pow_sub_C_ne_zero two_pos _) (X_pow_sub_C_ne_zero two_pos _)),
    Multiset.card_add, card_roots_X_sq_sub_C, card_roots_X_sq_sub_C]
  split_ifs <;> first | (exfalso; linarith) | norm_num

/-! ### Definition 2.1 and the condition (2.3) -/

section Definition21

variable {D X : Type*} [NormedAddCommGroup D] [NormedAddCommGroup X]

/-- **Definition 2.1, (2.4).** For the problem with resolvent `G : D → X`, the *relative condition
number* at the datum `d` over the set `N` of admissible perturbations is
`K(d) = sup_{δd ∈ N} (‖δx‖ / ‖x‖) / (‖δd‖ / ‖d‖)` with `x = G d` and `δx = G (d + δd) - G d`,
the supremum taken over the nonzero perturbations and valued in `ℝ≥0∞`. This is the backbone's
`Conditioning.relCondNumberOn` (`definition_2_1_rel_eq`). -/
noncomputable def definition_2_1_rel (G : D → X) (N : Set D) (d : D) : ℝ≥0∞ :=
  ⨆ (δd : D) (_ : δd ∈ N) (_ : δd ≠ 0), (‖G (d + δd) - G d‖ₑ / ‖G d‖ₑ) / (‖δd‖ₑ / ‖d‖ₑ)

/-- Definition 2.1's relative condition number is the backbone's `Conditioning.relCondNumberOn`. -/
theorem definition_2_1_rel_eq (G : D → X) (N : Set D) (d : D) :
    definition_2_1_rel G N d = relCondNumberOn G N d :=
  rfl

/-- **Definition 2.1, (2.5).** The *absolute condition number*
`K_abs(d) = sup_{δd ∈ N} ‖δx‖ / ‖δd‖`, "necessary whenever `d = 0` or `x = 0`". This is the
backbone's `Conditioning.absCondNumberOn` (`definition_2_1_abs_eq`). -/
noncomputable def definition_2_1_abs (G : D → X) (N : Set D) (d : D) : ℝ≥0∞ :=
  ⨆ (δd : D) (_ : δd ∈ N) (_ : δd ≠ 0), ‖G (d + δd) - G d‖ₑ / ‖δd‖ₑ

/-- Definition 2.1's absolute condition number is the backbone's `Conditioning.absCondNumberOn`. -/
theorem definition_2_1_abs_eq (G : D → X) (N : Set D) (d : D) :
    definition_2_1_abs G N d = absCondNumberOn G N d :=
  rfl

/-- The two numbers of Definition 2.1 differ by the scale factor `‖d‖ / ‖G d‖`:
`K(d) = K_abs(d) · ‖d‖ / ‖x‖`. In `ℝ≥0∞` the identity holds without hypotheses; it is
meaningful when `d ≠ 0` and `x ≠ 0`, which is why the book introduces the absolute number exactly
when `d = 0` or `x = 0`. -/
theorem definition_2_1_rel_eq_abs_mul (G : D → X) (N : Set D) (d : D) :
    definition_2_1_rel G N d = definition_2_1_abs G N d * (‖d‖ₑ / ‖G d‖ₑ) :=
  relCondNumberOn_eq G N d

/-- **(2.3) is finiteness of the condition number.** For the resolvent `G` on the admissible data
`S` and a radius `η`, the continuous-dependence condition (2.3), "there is `K(η, d)` with
`‖δd‖ < η ⇒ ‖δx‖ ≤ K(η, d) ‖δd‖`" for the admissible perturbations, holds iff the absolute
condition number over the admissible perturbations of size `< η` is finite. The book's (2.3) is
this for every `η > 0`. -/
theorem equation_2_3_iff (G : D → X) (S : Set D) (d : D) (η : ℝ) :
    (∃ K : ℝ, ∀ δd, ‖δd‖ < η → d + δd ∈ S → ‖G (d + δd) - G d‖ ≤ K * ‖δd‖) ↔
      absCondNumberWithin G S d η ≠ ⊤ :=
  (absCondNumberWithin_ne_top_iff G S d η).symm

end Definition21

/-! ### The first-order formula (2.7) -/

section Equation27

variable {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup X]
  [NormedSpace ℝ X] {G : D → X} {G' : D →L[ℝ] X} {d : D} {S : Set D}

/-- **(2.7), absolute form.** If the resolvent `G` is differentiable at the datum `d`, an interior
point of the admissible data `S`, then `K_abs(d) ≃ ‖G'(d)‖`: the first-order absolute condition
number, the limit of the Lipschitz constant of `G` as the perturbation size tends to zero, is
exactly the norm of the derivative. -/
theorem equation_2_7_abs (hG : HasFDerivAt G G' d) (hS : S ∈ 𝓝 d) :
    absCondNumber G S d = ‖G'‖ₑ :=
  absCondNumber_eq_enorm_fderiv hG hS

/-- **(2.7), relative form.** Under the same hypotheses, for `d ≠ 0` and `G d ≠ 0`,
`K(d) ≃ ‖G'(d)‖ ‖d‖ / ‖G(d)‖`, as an equality for the first-order relative condition number. -/
theorem equation_2_7_rel (hG : HasFDerivAt G G' d) (hS : S ∈ 𝓝 d) (hd : d ≠ 0) (hx : G d ≠ 0) :
    relCondNumber G S d = ‖G'‖ₑ * (‖d‖ₑ / ‖G d‖ₑ) :=
  relCondNumber_eq_enorm_fderiv hG hS hd hx

/-- **(2.7), relative form, for a scalar datum.** For `G : ℝ → E` with derivative `v` at `d ≠ 0`
and `G d ≠ 0`, `K(d) = ‖v‖ |d| / ‖G(d)‖`, in real numbers. This is how the Examples of the book
read (2.7) when the datum is a single number. -/
theorem equation_2_7_rel_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : ℝ → E}
    {v : E} {d : ℝ} (hG : HasDerivAt G v d) (hd : d ≠ 0) (hx : G d ≠ 0) :
    relCondNumber G univ d = ENNReal.ofReal (‖v‖ * |d| / ‖G d‖) := by
  rw [relCondNumber_eq_enorm_fderiv hG.hasFDerivAt univ_mem hd hx, ← ofReal_norm, ← ofReal_norm,
    ← ofReal_norm, ← ENNReal.ofReal_div_of_pos (norm_pos_iff.2 hx),
    ← ENNReal.ofReal_mul (norm_nonneg _), ContinuousLinearMap.norm_toSpanSingleton,
    Real.norm_eq_abs, mul_div_assoc]

open scoped Matrix.Norms.L2Operator in
/-- **(2.7) for `G : ℝⁿ → ℝᵐ`.** When the derivative of `G` at `d` is the Jacobian matrix `J`
acting on Euclidean space, `K_abs(d) = ‖J‖`, "the matrix norm associated with the vector norm
(1.19)": the `2`-operator norm of `J`. -/
theorem equation_2_7_jacobian {m n : ℕ} {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {J : Matrix (Fin m) (Fin n) ℝ} {d : EuclideanSpace ℝ (Fin n)}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hG : HasFDerivAt G (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin J)) d)
    (hS : S ∈ 𝓝 d) : absCondNumber G S d = ENNReal.ofReal ‖J‖ := by
  rw [equation_2_7_abs hG hS, ← ofReal_norm, Matrix.l2_opNorm_def]
  rfl

end Equation27

/-! ### Example 2.2: the roots of `x² - 2px + 1` -/

/-- The norm of a vector of `ℝ²` in the Euclidean norm `‖·‖₂`. -/
private theorem norm_fin_two (a b : ℝ) :
    ‖(!₂[a, b] : EuclideanSpace ℝ (Fin 2))‖ = √(a ^ 2 + b ^ 2) := by
  rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]

/-- The resolvent of Example 2.2: `G : ℝ → ℝ²`, `G(p) = (x₊, x₋)` with `x± = p ± √(p² - 1)` the
roots of `x² - 2px + 1 = 0`. It is a genuine resolvent for `p ≥ 1`; `Real.sqrt` is `0` on
negatives, so the map is total. -/
noncomputable def example_2_2_resolvent (p : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[p + √(p ^ 2 - 1), p - √(p ^ 2 - 1)]

/-- The derivative of the resolvent of Example 2.2 for `p > 1`: `G'±(p) = 1 ± p / √(p² - 1)`. -/
theorem example_2_2_hasDerivAt {p : ℝ} (hp : 1 < p) :
    HasDerivAt example_2_2_resolvent !₂[1 + p / √(p ^ 2 - 1), 1 - p / √(p ^ 2 - 1)] p := by
  have h1 : p ^ 2 - 1 ≠ 0 := by nlinarith
  have hs : HasDerivAt (fun x : ℝ => √(x ^ 2 - 1)) (p / √(p ^ 2 - 1)) p := by
    have := ((hasDerivAt_pow 2 p).sub_const 1).sqrt h1
    convert this using 1
    field_simp
    ring
  have hg : HasDerivAt (fun x : ℝ => ![x + √(x ^ 2 - 1), x - √(x ^ 2 - 1)])
      ![1 + p / √(p ^ 2 - 1), 1 - p / √(p ^ 2 - 1)] p := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact (hasDerivAt_id' p).add hs
    · exact (hasDerivAt_id' p).sub hs
  exact (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt p hg

/-- **Example 2.2, (2.8).** For `p > 1`, the relative condition number of the roots of
`x² - 2px + 1 = 0` with respect to the coefficient `p`, in the Euclidean norm on `ℝ²`, is
`K(p) = |p| / √(p² - 1)`. The book writes `≃`; in the `2`-norm, (2.7) gives an identity:
`‖G'(p)‖² = 2(2p² - 1)/(p² - 1)`, `‖G(p)‖² = 4p² - 2`, and `‖G'(p)‖ |p| / ‖G(p)‖ = |p| / √(p² - 1)`.
-/
theorem example_2_2 {p : ℝ} (hp : 1 < p) :
    relCondNumber example_2_2_resolvent univ p = ENNReal.ofReal (|p| / √(p ^ 2 - 1)) := by
  have h1 : 0 < p ^ 2 - 1 := by nlinarith
  have hs : 0 < √(p ^ 2 - 1) := Real.sqrt_pos.2 h1
  have hp0 : 0 < p := by linarith
  have hG : example_2_2_resolvent p ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h
    simp [example_2_2_resolvent] at this
    linarith
  rw [equation_2_7_rel_deriv (example_2_2_hasDerivAt hp) hp0.ne' hG]
  congr 1
  rw [example_2_2_resolvent, norm_fin_two, norm_fin_two, abs_of_pos hp0]
  have hA : (1 + p / √(p ^ 2 - 1)) ^ 2 + (1 - p / √(p ^ 2 - 1)) ^ 2 =
      ((p + √(p ^ 2 - 1)) ^ 2 + (p - √(p ^ 2 - 1)) ^ 2) / √(p ^ 2 - 1) ^ 2 := by
    field_simp
    ring
  have hB : 0 < (p + √(p ^ 2 - 1)) ^ 2 + (p - √(p ^ 2 - 1)) ^ 2 := by positivity
  rw [hA, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hs.le]
  field_simp

/-- **Example 2.2, separated roots.** "In the case of separated roots (say, if `p ≥ √2`) the
problem is well conditioned": `K(p) ≤ √2`, since `|p| / √(p² - 1) ≤ √2 ⟺ 2 ≤ p²`. -/
theorem example_2_2_le_sqrt_two {p : ℝ} (hp : √2 ≤ p) :
    relCondNumber example_2_2_resolvent univ p ≤ ENNReal.ofReal (√2) := by
  have h2 : (1 : ℝ) < √2 := by rw [Real.lt_sqrt] <;> norm_num
  have hp1 : 1 < p := h2.trans_le hp
  have hsq : 2 ≤ p ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  rw [example_2_2 hp1]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (Real.sqrt_pos.2 (by nlinarith)), abs_of_pos (by linarith),
    ← Real.sqrt_mul (by norm_num), Real.le_sqrt (by linarith) (by nlinarith)]
  nlinarith

/-- **Example 2.2, the reparametrized problem.** With `t = p + √(p² - 1)` the roots are `x₋ = t`
and `x₊ = 1/t`, "regular functions of `t`", and (2.7) gives `K(t) ≃ 1` "for any value of `t`":
here an identity, `‖G'(t)‖ |t| / ‖G(t)‖ = √(1 + t⁻⁴) |t| / √(t² + t⁻²) = 1`. The transformed
problem is well conditioned, and at `t = 1` the double root is no longer singular. -/
theorem example_2_2_reparam {t : ℝ} (ht : t ≠ 0) :
    relCondNumber (fun t : ℝ => (!₂[t, 1 / t] : EuclideanSpace ℝ (Fin 2))) univ t = 1 := by
  have hd : HasDerivAt (fun t : ℝ => (!₂[t, 1 / t] : EuclideanSpace ℝ (Fin 2)))
      !₂[1, -1 / t ^ 2] t := by
    have hg : HasDerivAt (fun x : ℝ => ![x, 1 / x]) ![1, -1 / t ^ 2] t := by
      rw [hasDerivAt_pi]
      intro i
      fin_cases i
      · exact hasDerivAt_id' t
      · simpa [one_div, neg_div] using hasDerivAt_inv ht
    exact (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt t hg
  have hG : (!₂[t, 1 / t] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h)
  rw [equation_2_7_rel_deriv hd ht hG, norm_fin_two, norm_fin_two, ENNReal.ofReal_eq_one,
    div_eq_one_iff_eq (by positivity), ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- **Remark 2.1 (ill-posed problems).** "There exist well posed problems (for instance, the
search of multiple roots of algebraic equations, see Example 2.2) for which the condition number
is infinite": the roots of `x² - 2px + 1` depend continuously on `p` over the admissible data
`[1, ∞)`, so the problem is well posed there, yet at the double root `p = 1` the absolute
condition number is `⊤`. The second clause is the instance `φ(x₊) = (x₊² + 1) / (2x₊)`,
`φ'(1) = 0`, of the backbone's `Conditioning.absCondNumber_eq_top_of_fderiv_eq_zero`, stated
within `S = [1, ∞)` because the root exists only on one side of `p = 1`. -/
theorem remark_2_1 :
    ContinuousOn example_2_2_resolvent (Ici 1) ∧
      absCondNumber example_2_2_resolvent (Ici 1) 1 = ⊤ := by
  have hcont : Continuous example_2_2_resolvent := by unfold example_2_2_resolvent; fun_prop
  refine ⟨hcont.continuousOn, ?_⟩
  have : NeBot (𝓝[Ici (1 : ℝ) \ {1}] 1) := by rw [Set.Ici_sdiff_left]; infer_instance
  set ψ : ℝ → ℝ := fun u => (u ^ 2 + 1) / (2 * u) with hψdef
  have h0 : example_2_2_resolvent 1 0 = 1 := by simp [example_2_2_resolvent]
  have hψ : HasDerivAt ψ 0 (example_2_2_resolvent 1 0) := by
    rw [h0]
    have h := ((hasDerivAt_pow 2 (1 : ℝ)).add_const 1).div
      ((hasDerivAt_id' (1 : ℝ)).const_mul 2) (by norm_num)
    exact h.congr_deriv (by norm_num)
  refine absCondNumber_eq_top_of_fderiv_eq_zero (𝕜 := ℝ)
    (φ := fun x : EuclideanSpace ℝ (Fin 2) => ψ (x 0)) hcont.continuousWithinAt ?_ ?_
  · have := hψ.comp_hasFDerivAt (example_2_2_resolvent 1)
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (example_2_2_resolvent 1) 0)
    rw [zero_smul] at this
    exact this
  · filter_upwards [eventually_mem_nhdsWithin] with y (hy : 1 ≤ y)
    have hs : √(y ^ 2 - 1) ^ 2 = y ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
    have hpos : 0 < y + √(y ^ 2 - 1) := by positivity
    simp only [example_2_2_resolvent, hψdef, PiLp.toLp_apply, Matrix.cons_val_zero]
    rw [div_eq_iff (by positivity)]
    linear_combination hs

/-! ### Example 2.3: a linear system perturbed in its right-hand side -/

section Example23

open scoped Matrix.Norms.L2Operator

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Example 2.3, the first equality of (2.9).** For a nonsingular `A` and `b ≠ 0`, the problem
`A x = b` perturbed in the right-hand side `b` alone has resolvent `G(b) = A⁻¹ b`, `G'(b) = A⁻¹`,
and (2.7) gives `K(b) = ‖A⁻¹‖ ‖b‖ / ‖A⁻¹ b‖` in the Euclidean norms — the `2`-operator norm of
`A⁻¹` and the `2`-norm of the vectors. -/
theorem example_2_3_eq (hA : IsUnit A) {b : EuclideanSpace ℝ (Fin n)} (hb : b ≠ 0) :
    relCondNumber (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹) univ b =
      ENNReal.ofReal (‖A⁻¹‖ * ‖b‖ / ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ b‖) := by
  have hAb : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ b ≠ 0 := by
    intro h
    have := Matrix.toEuclideanLin_mul_nonsing_inv_apply hA b
    change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ b) = b at this
    rw [h, map_zero] at this
    exact hb this.symm
  rw [relCondNumber_eq _ _ hb hAb, absCondNumber_continuousLinearMap _ univ_mem, ← ofReal_norm,
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_div_of_pos (norm_pos_iff.2 hAb),
    ← ENNReal.ofReal_mul (norm_nonneg _), Matrix.cstar_norm_def, mul_div_assoc]

/-- **Example 2.3, (2.9).** For a nonsingular `A` and `b ≠ 0`,
`K(b) ≃ ‖A⁻¹‖ ‖b‖ / ‖A⁻¹ b‖ ≤ ‖A‖ ‖A⁻¹‖ = K(A)`, the condition number of the matrix `A` in the
Euclidean operator norm: "if `A` is well conditioned, solving the linear system `A x = b` is a
stable problem with respect to perturbations of the right-hand side `b`". -/
theorem example_2_3 (hA : IsUnit A) {b : EuclideanSpace ℝ (Fin n)} (hb : b ≠ 0) :
    relCondNumber (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹) univ b ≤
      ENNReal.ofReal (NormedRing.condNumber A) := by
  have hu : IsUnit (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) := hA.map _
  set e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofUnit hu.unit with he_def
  have he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A := by
    ext x; rfl
  have hsymm : (e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ := by
    rw [← ContinuousLinearEquiv.ring_inverse_coe, he, Matrix.toEuclideanCLM_nonsing_inv hA]
  have hκ : e.condNumber = NormedRing.condNumber A := by
    rw [ContinuousLinearEquiv.condNumber, he, hsymm, NormedRing.condNumber,
      ← Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have hfun : (⇑e.symm : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
      ⇑(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹) := by
    rw [← hsymm]; rfl
  rw [← hfun, ← hκ]
  exact relCondNumber_symm_le_condNumber e hb

end Example23

/-! ### Example 2.4: the root of a nonlinear equation -/

section Example24

variable {φ G : ℝ → ℝ} {d : ℝ}

/-- **Example 2.4, (2.11).** For the nonlinear equation `φ(x) - d = 0` with `φ` of class `C¹`,
invertible near `d` with continuous local inverse `G = φ⁻¹` (so `φ (G y) = y` near `d`), and a
simple root, `φ'(x) ≠ 0` at `x = G d`: `K_abs(d) ≃ |[φ'(x)]⁻¹|`. The problem "is ill conditioned
when `φ'(x)` is small, well conditioned when `φ'(x)` is large". -/
theorem example_2_4 (hφ : ContDiff ℝ 1 φ) (hG : ContinuousAt G d)
    (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) (hφ' : deriv φ (G d) ≠ 0) :
    absCondNumber G univ d = ENNReal.ofReal |deriv φ (G d)|⁻¹ := by
  rw [absCondNumber_of_local_left_inverse hG (ContDiffAt.hasStrictDerivAt hφ.contDiffAt one_ne_zero)
    hφ' hinv, ← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_inv_of_pos (abs_pos.2 hφ')]

/-- **Example 2.4, (2.10).** Under the hypotheses of `example_2_4`, for `d ≠ 0` and a nonzero
root `x = G d`, the relative condition number is `K(d) ≃ (|d| / |x|) |[φ'(x)]⁻¹|`. -/
theorem example_2_4_rel (hφ : ContDiff ℝ 1 φ) (hG : ContinuousAt G d)
    (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) (hφ' : deriv φ (G d) ≠ 0) (hd : d ≠ 0) (hx : G d ≠ 0) :
    relCondNumber G univ d = ENNReal.ofReal (|d| / |G d| * |deriv φ (G d)|⁻¹) := by
  rw [relCondNumber_of_local_left_inverse hG (ContDiffAt.hasStrictDerivAt hφ.contDiffAt one_ne_zero)
    hφ' hinv hd hx, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, ← ENNReal.ofReal_inv_of_pos (abs_pos.2 hφ'),
    ← ENNReal.ofReal_div_of_pos (abs_pos.2 hx), ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- **Example 2.4, the multiple root.** With `φ`, `G` as in `example_2_4` but `φ'(x) = 0` at the
root `x = G d`, the absolute condition number is infinite: `K_abs(d) = ⊤`. The book says "the
problem is thus ill posed if `x` is a multiple root"; read as infinite conditioning, since `G`
is continuous by hypothesis and the problem may well be well posed (Remark 2.1). -/
theorem example_2_4_multiple_root (hφ : ContDiff ℝ 1 φ) (hG : ContinuousAt G d)
    (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) (hφ' : deriv φ (G d) = 0) :
    absCondNumber G univ d = ⊤ := by
  have : NeBot (𝓝[(univ : Set ℝ) \ {d}] d) := by rw [← Set.compl_eq_univ_sdiff]; infer_instance
  refine absCondNumber_eq_top_of_deriv_eq_zero hG.continuousWithinAt ?_ (by rwa [nhdsWithin_univ])
  have h : HasDerivAt φ (deriv φ (G d)) (G d) :=
    (ContDiffAt.hasStrictDerivAt hφ.contDiffAt one_ne_zero).hasDerivAt
  rwa [hφ'] at h

end Example24

/-! ### The first-order condition number can underestimate the true one -/

/-- **The example closing §2.1.** The first-order absolute condition number `‖G'(d)‖` "does not
always provide a sound estimate of the condition number `K_abs(d)`": for `G(d) = cos d - 1` on
`(-π/2, π/2)`, `G'(0) = 0` while `K_abs(0) = 2/π`. Here the latter is the absolute condition
number over the perturbations `|δd| < π/2`: the ratio `(1 - cos δd) / |δd|` is bounded by `2/π`
(the chord of the convex function `1 - cos` from `0` to `π/2`) and tends to `2/π` as
`δd → π/2`, so the supremum over the open interval is `2/π`, not attained. Consistent with the
backbone's `Conditioning.enorm_fderiv_le_absCondNumberWithin`, `0 ≤ 2/π`, and with
`Conditioning.absCondNumber G univ 0 = 0` from (2.7). -/
theorem cosSubOne_absCondNumberWithin :
    absCondNumberWithin (fun d : ℝ => Real.cos d - 1) univ 0 (π / 2) =
      ENNReal.ofReal (2 / π) := by
  refine le_antisymm ?_ ?_
  · refine absCondNumberOn_le_of_forall_norm_sub_le (by positivity) fun δd hδd _ => ?_
    have h1 : |δd| ≤ π / 2 := (Real.norm_eq_abs δd ▸ hδd.1).le
    simp only [zero_add, Real.cos_zero, sub_self, sub_zero, Real.norm_eq_abs]
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Real.cos_le_one _)), ← Real.cos_abs]
    linarith [Real.one_sub_mul_le_cos (abs_nonneg δd) h1]
  · have hlim : Tendsto (fun x : ℝ => ‖(Real.cos (0 + x) - 1) - (Real.cos 0 - 1)‖ₑ / ‖x‖ₑ)
        (𝓝[<] (π / 2)) (𝓝 (ENNReal.ofReal (2 / π))) := by
      have hnum : Tendsto (fun x : ℝ => ‖(Real.cos (0 + x) - 1) - (Real.cos 0 - 1)‖ₑ)
          (𝓝[<] (π / 2)) (𝓝 ‖(Real.cos (0 + π / 2) - 1) - (Real.cos 0 - 1)‖ₑ) :=
        ((continuous_enorm.comp (by fun_prop)).tendsto _).mono_left nhdsWithin_le_nhds
      have hden : Tendsto (fun x : ℝ => ‖x‖ₑ) (𝓝[<] (π / 2)) (𝓝 ‖π / 2‖ₑ) :=
        (continuous_enorm.tendsto _).mono_left nhdsWithin_le_nhds
      have := ENNReal.Tendsto.div hnum (Or.inr (enorm_ne_zero.2 (by positivity))) hden
        (Or.inl enorm_ne_top)
      convert this using 2
      simp only [zero_add, Real.cos_pi_div_two, Real.cos_zero, sub_self, sub_zero, zero_sub,
        enorm_neg, enorm_one]
      rw [Real.enorm_eq_ofReal (by positivity), one_div,
        ← ENNReal.ofReal_inv_of_pos (by positivity)]
      congr 1
      field_simp
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (by positivity : (0 : ℝ) < π / 2)] with x hx
    refine le_absCondNumberOn (G := fun d : ℝ => Real.cos d - 1)
      (N := perturbations univ 0 (π / 2)) (d := 0) ?_ hx.1.ne'
    exact ⟨by rw [Real.norm_eq_abs, abs_of_pos hx.1]; exact hx.2, mem_univ _⟩

end QuarteroniSaccoSaleri.Chapter02
