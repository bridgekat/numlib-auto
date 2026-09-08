/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.MvPolynomial.Degrees`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Total degree under substitution

Substituting a polynomial for each variable multiplies the total degree by at most the degree of
the substituted polynomials: `bind₁ f p` has total degree at most `k · deg p` when every `f i` has
total degree at most `k`.  The case `k = 1` is a change of variables by an affine map, under which
`Π_n = MvPolynomial.restrictTotalDegree` is therefore stable — and, when the substitution is
invertible with an inverse of the same kind, stable both ways, so the total degree is preserved
exactly.

The `k = 1` statements are what makes an approximation-theoretic problem on an ellipsoid the same
problem on a ball: the affine map carrying one onto the other carries the polynomials of degree at
most `n` onto the polynomials of degree at most `n`.

## Main results

* `MvPolynomial.totalDegree_bind₁_le`: `deg (bind₁ f p) ≤ k · deg p`.
* `MvPolynomial.totalDegree_aeval_le`: `deg (aeval q p) ≤ k · deg p` for a one-variable `p`.
* `MvPolynomial.totalDegree_bind₁_eq_of_leftInverse`: exact preservation for an invertible
  substitution by polynomials of degree at most one.
* `MvPolynomial.restrictTotalDegree_map_bind₁`: `Π_n` maps onto `Π_n`.
-/

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- **The total degree of a substitution.**  Substituting for each variable a polynomial of total
degree at most `k` multiplies the total degree by at most `k`. -/
theorem totalDegree_bind₁_le {k : ℕ} {f : σ → MvPolynomial τ R} (hf : ∀ i, (f i).totalDegree ≤ k)
    (p : MvPolynomial σ R) : (bind₁ f p).totalDegree ≤ k * p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun m hm => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  have hterm : ∀ i ∈ m.support, (f i ^ m i).totalDegree ≤ k * m i := fun i _ =>
    (totalDegree_pow _ _).trans <| calc
      m i * (f i).totalDegree ≤ m i * k := Nat.mul_le_mul_left _ (hf i)
      _ = k * m i := Nat.mul_comm _ _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  exact Nat.mul_le_mul_left _ (le_totalDegree hm)

/-- **The total degree of a one-variable polynomial evaluated at a multivariable one.**
Substituting a polynomial of total degree at most `k` for the variable of a one-variable polynomial
of degree `d` gives total degree at most `k · d`. It is the one-variable counterpart of
`MvPolynomial.totalDegree_bind₁_le`, and the case `k = 1` says that a *ridge* polynomial — a
one-variable polynomial of a linear form — has the degree of the one-variable polynomial. -/
theorem totalDegree_aeval_le {k : ℕ} {q : MvPolynomial τ R} (hq : q.totalDegree ≤ k)
    (p : Polynomial R) : (Polynomial.aeval q p).totalDegree ≤ k * p.natDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  refine totalDegree_finsetSum_le fun i hi => ?_
  refine (totalDegree_smul_le _ _).trans ((totalDegree_pow _ _).trans ?_)
  rw [Finset.mem_range] at hi
  calc i * q.totalDegree ≤ p.natDegree * k := Nat.mul_le_mul (by omega) hq
    _ = k * p.natDegree := Nat.mul_comm _ _

/-- A substitution by polynomials of total degree at most one does not raise the total degree. -/
theorem totalDegree_bind₁_le_of_totalDegree_le_one {f : σ → MvPolynomial τ R}
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  simpa using totalDegree_bind₁_le hf p

/-- **An invertible substitution by degree-one polynomials preserves the total degree exactly.**
The affine changes of variables are of this kind, so a linear change of coordinates on the domain
neither raises nor lowers the degree of a polynomial. -/
theorem totalDegree_bind₁_eq_of_leftInverse {f : σ → MvPolynomial τ R} {g : τ → MvPolynomial σ R}
    (hf : ∀ i, (f i).totalDegree ≤ 1) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (hgf : ∀ p : MvPolynomial σ R, bind₁ g (bind₁ f p) = p) (p : MvPolynomial σ R) :
    (bind₁ f p).totalDegree = p.totalDegree :=
  le_antisymm (totalDegree_bind₁_le_of_totalDegree_le_one hf p)
    (by
      conv_lhs => rw [← hgf p]
      exact totalDegree_bind₁_le_of_totalDegree_le_one hg _)

/-- **The polynomials of degree at most `n` are stable under an invertible substitution by
degree-one polynomials**, and the substitution maps that space *onto* itself. -/
theorem restrictTotalDegree_map_bind₁ {f : σ → MvPolynomial τ R} {g : τ → MvPolynomial σ R}
    (hf : ∀ i, (f i).totalDegree ≤ 1) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (hgf : ∀ p : MvPolynomial σ R, bind₁ g (bind₁ f p) = p)
    (hfg : ∀ q : MvPolynomial τ R, bind₁ f (bind₁ g q) = q) (n : ℕ) :
    (restrictTotalDegree σ R n).map (bind₁ f).toLinearMap = restrictTotalDegree τ R n := by
  ext q
  simp only [Submodule.mem_map, mem_restrictTotalDegree, AlgHom.toLinearMap_apply]
  refine ⟨?_, fun hq => ⟨bind₁ g q, ?_, hfg q⟩⟩
  · rintro ⟨p, hp, rfl⟩
    exact (totalDegree_bind₁_eq_of_leftInverse hf hg hgf p).trans_le hp
  · rw [totalDegree_bind₁_eq_of_leftInverse hg hf hfg q]
    exact hq

end MvPolynomial
