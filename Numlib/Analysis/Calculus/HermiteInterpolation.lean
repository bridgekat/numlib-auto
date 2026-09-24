import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Numlib.RingTheory.Polynomial.HermiteInterpolation

/-!
# Jets and divided differences of functions

The analytic side of Hermite interpolation on a multiset of nodes, on top of the field-level
theory of `Numlib/RingTheory/Polynomial/HermiteInterpolation`, for functions `f : 𝕜 → 𝕜` on a
nontrivially normed field.

## Main definitions

* `Hermite.taylorJet f x j = f⁽ʲ⁾(x) / j!`: the Taylor coefficients of `f` at `x`. The definition is
  total: where `f` is not differentiable Mathlib's junk value `0` of `iteratedDeriv` enters, and
  every consumer carries the smoothness it needs as a hypothesis.
* `Hermite.divDiff f s`: the divided difference of `f` at a multiset of possibly repeated nodes, the
  coefficient of `X^{card s - 1}` in the Hermite interpolant of the jets of `f` on `s`
  ([golub2013matrix] §9.1.4's `f[λ₀, …, λ_k]`, confluent where the nodes repeat).

## Main results

* `Hermite.isJetInterpolant_taylorJet_iff`: in characteristic `0`, interpolating the jets of `f` is
  agreement of derivatives, `p⁽ʲ⁾(x) = f⁽ʲ⁾(x)` for `j < count x s`.
* `Hermite.taylorJet_polynomial`: the jet of a polynomial function is its Taylor expansion.
* `Hermite.taylorJet_add`, `Hermite.taylorJet_mul` (Leibniz): the jet calculus for smooth functions.
* `Hermite.divDiff_congr`, `Hermite.IsJetInterpolant.divDiff_eq`: the divided difference depends
  only on the jets it uses, and may be computed from any polynomial interpolating on more nodes.
* `Hermite.divDiff_replicate`: at `k + 1` copies of one node, `f[x, …, x] = f⁽ᵏ⁾(x)/k!`.
* `Hermite.divDiff_cons_cons`: the recursion
  `f[x, x', s] = (f[x, s] - f[x', s]) / (x - x')` for `x ≠ x'`.
* `Hermite.divDiff_X_pow`: the divided differences of monomials satisfy
  `z^{m+1}[x, s] = x · z^m[x, s] + z^m[s]` (they are complete homogeneous symmetric polynomials of
  the nodes).

## Implementation notes

Placed at the Golub–Van Loan review out of `Numlib/Approximation/Hermite`: `taylorJet` needs
`iteratedDeriv`, and the primary functional calculus must not import the numerical `Approximation`
layer. The real, `Fin`-indexed Hermite interpolation of that module is the instance
`Hermite.interpolate_eq_interpolateJet`, and its classical divided difference is the instance
`DividedDifference.newtonOn_eq_divDiff` (`Numlib/Approximation/NewtonForm`).
-/

open Polynomial

namespace Hermite

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The iterated derivative of a polynomial function over a nontrivially normed field is the
function of the iterated `derivative`. (Local generalization of the real
`Polynomial.iteratedDeriv_eval` of `Numlib/Analysis/Calculus/RootMultiplicity`.) -/
theorem iteratedDeriv_eval (p : 𝕜[X]) (n : ℕ) :
    iteratedDeriv n (fun x => p.eval x) = fun x => (derivative^[n] p).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    ext x
    exact Polynomial.deriv _

/-! ### Jets of functions -/

/-- The **Taylor coefficients** `f⁽ʲ⁾(x) / j!` of a function on a nontrivially normed field. -/
noncomputable def taylorJet (f : 𝕜 → 𝕜) (x : 𝕜) (j : ℕ) : 𝕜 :=
  iteratedDeriv j f x / j.factorial

@[simp]
theorem taylorJet_zero (f : 𝕜 → 𝕜) (x : 𝕜) : taylorJet f x 0 = f x := by
  simp [taylorJet]

/-- The Taylor coefficients of a polynomial at `x` are the derivatives there divided by the
factorials. -/
theorem coeff_taylor_eq_eval_iterate_derivative_div [CharZero 𝕜] (p : 𝕜[X]) (x : 𝕜) (j : ℕ) :
    (taylor x p).coeff j = (derivative^[j] p).eval x / j.factorial := by
  have hj : (j.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  rw [eq_div_iff hj, taylor_coeff, ← factorial_smul_hasseDeriv, LinearMap.smul_apply, eval_smul,
    nsmul_eq_mul, mul_comm]

/-- **The jet of a polynomial function is its Taylor expansion.** -/
theorem taylorJet_polynomial [CharZero 𝕜] (p : 𝕜[X]) (x : 𝕜) (j : ℕ) :
    taylorJet (fun z => p.eval z) x j = (taylor x p).coeff j := by
  rw [taylorJet, iteratedDeriv_eval, coeff_taylor_eq_eval_iterate_derivative_div]

/-- Jets are additive at points where both functions are smooth enough. -/
theorem taylorJet_add {f g : 𝕜 → 𝕜} {x : 𝕜} {j : ℕ} (hf : ContDiffAt 𝕜 j f x)
    (hg : ContDiffAt 𝕜 j g x) : taylorJet (f + g) x j = taylorJet f x j + taylorJet g x j := by
  rw [taylorJet, iteratedDeriv_add hf hg, add_div, taylorJet, taylorJet]

theorem taylorJet_sub {f g : 𝕜 → 𝕜} {x : 𝕜} {j : ℕ} (hf : ContDiffAt 𝕜 j f x)
    (hg : ContDiffAt 𝕜 j g x) : taylorJet (f - g) x j = taylorJet f x j - taylorJet g x j := by
  rw [taylorJet, iteratedDeriv_sub hf hg, sub_div, taylorJet, taylorJet]

theorem taylorJet_const_smul (c : 𝕜) (f : 𝕜 → 𝕜) (x : 𝕜) (j : ℕ) :
    taylorJet (c • f) x j = c * taylorJet f x j := by
  rw [taylorJet, iteratedDeriv_const_smul_field, smul_eq_mul, mul_div_assoc, taylorJet]

/-- **Leibniz's rule for jets**: the jet of a product is the Cauchy product of the jets. -/
theorem taylorJet_mul [CharZero 𝕜] {f g : 𝕜 → 𝕜} {x : 𝕜} {n : ℕ} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) :
    taylorJet (f * g) x n =
      ∑ i ∈ Finset.range (n + 1), taylorJet f x i * taylorJet g x (n - i) := by
  rw [taylorJet, iteratedDeriv_mul hf hg, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h := Nat.choose_mul_factorial_mul_factorial hin
  have h1 : (i.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  have h2 : ((n - i).factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (n - i).factorial_ne_zero
  have h3 : (n.choose i : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hin).ne'
  rw [taylorJet, taylorJet, ← h]
  push_cast
  field_simp

variable [DecidableEq 𝕜]

/-- In characteristic `0`, **interpolating the jets of `f` is agreement of derivatives**: `p`
interpolates the jets of `f` on `s` exactly when `p⁽ʲ⁾(x) = f⁽ʲ⁾(x)` at every node `x` for
`j < count x s`. -/
theorem isJetInterpolant_taylorJet_iff [CharZero 𝕜] {s : Multiset 𝕜} {f : 𝕜 → 𝕜} {p : 𝕜[X]} :
    IsJetInterpolant s (taylorJet f) p ↔
      ∀ x ∈ s, ∀ j < s.count x, (derivative^[j] p).eval x = iteratedDeriv j f x := by
  rw [isJetInterpolant_iff_coeff_taylor]
  refine forall₂_congr fun x _ => forall₂_congr fun j _ => ?_
  have hj : (j.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  rw [coeff_taylor_eq_eval_iterate_derivative_div, taylorJet, div_left_inj' hj]

/-- A polynomial interpolates the jets of its own polynomial function. -/
theorem isJetInterpolant_taylorJet_polynomial [CharZero 𝕜] (s : Multiset 𝕜) (p : 𝕜[X]) :
    IsJetInterpolant s (taylorJet fun z => p.eval z) p := by
  have h : (taylorJet fun z => p.eval z) = fun x j => (taylor x p).coeff j := by
    ext x j
    exact taylorJet_polynomial p x j
  rw [h]
  exact isJetInterpolant_coeff_taylor s p

/-! ### Divided differences at repeated nodes -/

/-- The **divided difference** of `f` at a multiset `s` of possibly repeated nodes: the coefficient
of `X^{card s - 1}` in the Hermite interpolant of the jets of `f` on `s`. At distinct nodes it is
the classical divided difference `f[x₀, …, x_k]`; at `k + 1` copies of one node it is `f⁽ᵏ⁾(x)/k!`
(`Hermite.divDiff_replicate`). The value at the empty multiset is `0`. -/
noncomputable def divDiff (f : 𝕜 → 𝕜) (s : Multiset 𝕜) : 𝕜 :=
  (interpolateJet s (taylorJet f)).coeff (Multiset.card s - 1)

@[simp]
theorem divDiff_zero (f : 𝕜 → 𝕜) : divDiff f 0 = 0 := by
  simp [divDiff]

/-- **The divided difference depends only on the jets it uses.** -/
theorem divDiff_congr {f g : 𝕜 → 𝕜} {s : Multiset 𝕜}
    (h : ∀ x ∈ s, ∀ j < s.count x, taylorJet f x j = taylorJet g x j) :
    divDiff f s = divDiff g s := by
  rw [divDiff, divDiff, interpolateJet_congr h]

/-- The divided difference read off an interpolant: if `p` interpolates the jets of `f` on `s`,
then `f[s]` is the coefficient of `X^{card s - 1}` of `p` reduced modulo the nodal polynomial. -/
theorem IsJetInterpolant.divDiff_eq_coeff {f : 𝕜 → 𝕜} {s : Multiset 𝕜} {p : 𝕜[X]}
    (hp : IsJetInterpolant s (taylorJet f) p) :
    divDiff f s = (p %ₘ nodalMultiset s).coeff (Multiset.card s - 1) := by
  rw [divDiff, hp.modByMonic_eq_interpolateJet]

/-- The divided difference of a polynomial function reads off its remainder modulo the nodal
polynomial. -/
theorem divDiff_polynomial [CharZero 𝕜] (p : 𝕜[X]) (s : Multiset 𝕜) :
    divDiff (fun z => p.eval z) s = (p %ₘ nodalMultiset s).coeff (Multiset.card s - 1) :=
  (isJetInterpolant_taylorJet_polynomial s p).divDiff_eq_coeff

/-- **Divided differences through an interpolant on more nodes**: if `p` interpolates the jets of
`f` on `t` and `s ≤ t`, then `f[s] = p[s]`. -/
theorem IsJetInterpolant.divDiff_eq [CharZero 𝕜] {f : 𝕜 → 𝕜} {s t : Multiset 𝕜} {p : 𝕜[X]}
    (hp : IsJetInterpolant t (taylorJet f) p) (hst : s ≤ t) :
    divDiff f s = divDiff (fun z => p.eval z) s := by
  rw [(hp.of_le hst).divDiff_eq_coeff, divDiff_polynomial]

/-- On a polynomial of degree `< card s`, the divided difference is the coefficient of
`X^{card s - 1}`. -/
theorem divDiff_polynomial_of_degree_lt [CharZero 𝕜] {p : 𝕜[X]} {s : Multiset 𝕜}
    (hp : p.degree < Multiset.card s) :
    divDiff (fun z => p.eval z) s = p.coeff (Multiset.card s - 1) := by
  rw [divDiff_polynomial, (modByMonic_eq_self_iff (monic_nodalMultiset s)).mpr
    (by rwa [degree_nodalMultiset])]

/-- Divided differences are additive in the function, for functions smooth enough at the
nodes. -/
theorem divDiff_add {f g : 𝕜 → 𝕜} {s : Multiset 𝕜}
    (hf : ∀ x ∈ s, ContDiffAt 𝕜 (s.count x - 1 : ℕ) f x)
    (hg : ∀ x ∈ s, ContDiffAt 𝕜 (s.count x - 1 : ℕ) g x) :
    divDiff (f + g) s = divDiff f s + divDiff g s := by
  have h : ∀ x ∈ s, ∀ j < s.count x,
      taylorJet (f + g) x j = (taylorJet f + taylorJet g) x j := fun x hx j hj => by
    have hj : (j : WithTop ℕ∞) ≤ (s.count x - 1 : ℕ) := by exact_mod_cast (by omega : j ≤ _)
    rw [Pi.add_apply, Pi.add_apply, taylorJet_add ((hf x hx).of_le hj) ((hg x hx).of_le hj)]
  rw [divDiff, interpolateJet_congr h, interpolateJet_add, coeff_add, divDiff, divDiff]

/-- Divided differences are homogeneous in the function. -/
theorem divDiff_const_smul (c : 𝕜) (f : 𝕜 → 𝕜) (s : Multiset 𝕜) :
    divDiff (c • f) s = c * divDiff f s := by
  have h : taylorJet (c • f) = c • taylorJet f := by
    ext x j
    rw [taylorJet_const_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [divDiff, h, interpolateJet_smul, coeff_smul, smul_eq_mul, divDiff]

/-- At `k + 1` copies of one node, the divided difference is the Taylor coefficient
`f⁽ᵏ⁾(x)/k!`. -/
theorem divDiff_replicate (f : 𝕜 → 𝕜) (x : 𝕜) (k : ℕ) :
    divDiff f (Multiset.replicate (k + 1) x) = taylorJet f x k := by
  have hP : IsJetInterpolant (Multiset.replicate (k + 1) x) (taylorJet f)
      (jetPoly (taylorJet f x) x (k + 1)) := by
    intro z hz
    rw [Multiset.eq_of_mem_replicate hz, Multiset.count_replicate_self, sub_self]
    exact dvd_zero _
  rw [divDiff, ← eq_interpolateJet (by simpa using degree_jetPoly_lt _ x (k + 1)) hP,
    Multiset.card_replicate, Nat.add_sub_cancel, coeff_jetPoly_succ_self]

/-- At a single node the divided difference is the value. -/
@[simp]
theorem divDiff_singleton (f : 𝕜 → 𝕜) (x : 𝕜) : divDiff f {x} = f x := by
  simpa using divDiff_replicate f x 0

/-- **The recursion of divided differences** in two distinct nodes, valid at repeated nodes:
`f[x, x', s] = (f[x, s] - f[x', s]) / (x - x')`. -/
theorem divDiff_cons_cons (f : 𝕜 → 𝕜) {x x' : 𝕜} (h : x ≠ x') (s : Multiset 𝕜) :
    divDiff f (x ::ₘ x' ::ₘ s) = (divDiff f (x ::ₘ s) - divDiff f (x' ::ₘ s)) / (x - x') := by
  rw [eq_div_iff (sub_ne_zero.mpr h)]
  set Q := interpolateJet (x ::ₘ x' ::ₘ s) (taylorJet f)
  have h1 := interpolateJet_cons_sub x' (x ::ₘ s) (taylorJet f)
  have h2 := interpolateJet_cons_sub x (x' ::ₘ s) (taylorJet f)
  rw [Multiset.cons_swap] at h1
  simp only [Multiset.card_cons, nodalMultiset_cons] at h1 h2
  have key : interpolateJet (x ::ₘ s) (taylorJet f) - interpolateJet (x' ::ₘ s) (taylorJet f)
      = C (Q.coeff (Multiset.card s + 1) * (x - x')) * nodalMultiset s := by
    rw [map_mul, map_sub]
    linear_combination h2 - h1
  have hc := congrArg (coeff · (Multiset.card s)) key
  simp only [coeff_sub, coeff_C_mul] at hc
  rw [← natDegree_nodalMultiset s, (monic_nodalMultiset s).coeff_natDegree, mul_one,
    natDegree_nodalMultiset] at hc
  simp only [divDiff, Multiset.card_cons, Nat.add_sub_cancel]
  rw [hc]

/-- **Multiplying by the identity** adds one node to the divided difference of a polynomial
function: `(z p)[x, s] = x · p[x, s] + p[s]`. -/
theorem divDiff_X_mul [CharZero 𝕜] (p : 𝕜[X]) (x : 𝕜) (s : Multiset 𝕜) :
    divDiff (fun z => z * p.eval z) (x ::ₘ s)
      = x * divDiff (fun z => p.eval z) (x ::ₘ s) + divDiff (fun z => p.eval z) s := by
  have hXp : (fun z => z * p.eval z) = fun z => (X * p).eval z := by
    ext z
    simp
  set k := Multiset.card s
  set N := nodalMultiset s
  set q := p %ₘ nodalMultiset (x ::ₘ s)
  set q' := p %ₘ N
  set c := q.coeff k
  have hq : q - q' = C c * N := by
    have := interpolateJet_cons_sub x s fun z j => (taylor z p).coeff j
    rwa [interpolateJet_coeff_taylor, interpolateJet_coeff_taylor] at this
  have hq'deg : q'.degree < k := by
    rw [← degree_nodalMultiset s]
    exact degree_modByMonic_lt _ (monic_nodalMultiset s)
  -- the remainder of `X * p`
  have hrem : (X * p) %ₘ nodalMultiset (x ::ₘ s) = X * q' + C (c * x) * N := by
    have hdvd : nodalMultiset (x ::ₘ s) ∣ X * p - (X * q' + C (c * x) * N) := by
      have hpq : nodalMultiset (x ::ₘ s) ∣ p - q := by
        rw [← dvd_neg, neg_sub]
        exact dvd_modByMonic_sub p _
      have e : X * p - (X * q' + C (c * x) * N) = X * (p - q) + C c * nodalMultiset (x ::ₘ s) := by
        rw [nodalMultiset_cons, map_mul]
        linear_combination X * hq
      rw [e]
      exact dvd_add (hpq.mul_left X) (dvd_mul_left _ _)
    rw [modByMonic_eq_of_dvd_sub (monic_nodalMultiset _) hdvd,
      (modByMonic_eq_self_iff (monic_nodalMultiset _)).mpr]
    rw [degree_nodalMultiset, Multiset.card_cons]
    refine (degree_lt_iff_coeff_zero _ _).mpr fun m hm => ?_
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [coeff_add, coeff_X_mul, coeff_C_mul, coeff_eq_zero_of_degree_lt
      (hq'deg.trans_le (by exact_mod_cast (by omega : k ≤ m))),
      coeff_eq_zero_of_natDegree_lt (by rw [natDegree_nodalMultiset]; omega), mul_zero, add_zero]
  rw [hXp, divDiff_polynomial, divDiff_polynomial, divDiff_polynomial, hrem, Multiset.card_cons,
    Nat.add_sub_cancel, coeff_add, coeff_C_mul, ← natDegree_nodalMultiset s,
    (monic_nodalMultiset s).coeff_natDegree, natDegree_nodalMultiset]
  change (X * q').coeff k + c * x * 1 = x * c + q'.coeff (k - 1)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, coeff_X_mul_zero, coeff_eq_zero_of_degree_lt (hq'deg.trans_le (by rw [hk]))]
    ring
  · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk', coeff_X_mul, Nat.add_sub_cancel]
    ring

/-- **The divided differences of monomials**: `z^{m+1}[x, s] = x · z^m[x, s] + z^m[s]`. With
`z^m[s] = 0` for `card s > m + 1` and `z^m[s] = 1` for `card s = m + 1`, this recursion makes
`z^m[s]` the complete homogeneous symmetric polynomial of degree `m + 1 - card s` in the nodes. -/
theorem divDiff_X_pow [CharZero 𝕜] (m : ℕ) (x : 𝕜) (s : Multiset 𝕜) :
    divDiff (fun z => z ^ (m + 1)) (x ::ₘ s)
      = x * divDiff (fun z => z ^ m) (x ::ₘ s) + divDiff (fun z => z ^ m) s := by
  have h := divDiff_X_mul (X ^ m) x s
  simp only [eval_pow, eval_X] at h
  rw [← h]
  congr 1
  ext z
  ring

end Hermite
