import Numlib.Algebra.Polynomial.MinDegreeRepresentation
import NumlibSurface.LiesenStrakos.Chapter04.Section03

/-!
# Liesen and Strakoš, Section 4.4: Sufficient conditions

Section 4.4 of [liesen2013krylov] proves that a degree-$s$ polynomial adjoint yields
Arnoldi recurrences of length at most $s+2$. For starts of grade at least $s+2$, this
upper bound is sharp. The bandwidth arguments are in `Numlib.Krylov.ShortRecurrence`.

## Main definitions

* Definition 4.4.1, `LiesenStrakos.IsNormalOfDegree`: the adjoint is a polynomial
  in the operator of minimum degree $s$.

## Main results

* Lemma 4.4.2, `LiesenStrakos.lemma_4_4_2`: exact bandwidth for starts of sufficiently high
  grade.
* Theorem 4.4.3, `LiesenStrakos.theorem_4_4_3`: the bandwidth bound for all starts and exact
  recurrence length for starts of sufficiently high grade.
* Theorem 4.4.3, `LiesenStrakos.theorem_4_4_3_admits`: a normal operator of the given degree
  admits the corresponding optimal recurrence.

## Deviations from the source

* **Definition 4.4.1, Lemma 4.4.2 and Theorem 4.4.3** (generalization). The degree
  of normality and its sufficient conditions for the recurrence also apply over the reals.
  See `LiesenStrakos.IsNormalOfDegree`, `LiesenStrakos.lemma_4_4_2` and
  `LiesenStrakos.theorem_4_4_3`.
-/

namespace LiesenStrakos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- An endomorphism is normal of degree $s$ if its adjoint is a polynomial in it of least degree
$s$. This is Definition 4.4.1 of [liesen2013krylov].

**Generalization.** The source uses complex scalars. The same polynomial condition
defines the degree of normality for real operators. -/
def IsNormalOfDegree (A : Module.End 𝕜 E) (s : ℕ) : Prop :=
  Polynomial.IsMinDegreeRepresentation (R := 𝕜) A A.adjoint s

/-- If $A$ is normal of degree $s$, $s+2<d_{\min}(A)$, and the starting vector has grade at
least $s+2$, then its rectangular Arnoldi matrix is $(s+2)$-band Hessenberg.
This is Lemma 4.4.2 of [liesen2013krylov].

**Generalization.** The sufficient condition extends to real inner product spaces. -/
theorem lemma_4_4_2 (A : Module.End 𝕜 E) (v : E) {s : ℕ}
    (hs : s + 2 < operatorMinimalDegree A) (hgrade : s + 2 ≤ vectorGrade A v)
    (hA : IsNormalOfDegree A s) : AdmitsOptimalRecurrenceFor A v s := by
  obtain ⟨p, hpdeg, hp, -⟩ := hA
  refine ⟨hs.le, Arnoldi.hessenberg_isUpperHessenbergRect A v _, ?_,
    Arnoldi.hasUpperBandwidth_of_adjoint_eq_aeval A v hpdeg.le hp.symm, ?_⟩
  · intro j
    apply mt ((Arnoldi.coeff_succ_self_eq_zero_iff A v j).1)
    have hj : (j : ℕ) < Krylov.grade A v - 1 := j.isLt
    change s + 2 ≤ Krylov.grade A v at hgrade
    omega
  · let j : Fin (vectorGrade A v - 1) := ⟨s, by omega⟩
    let i : Fin (vectorGrade A v - 1 + 1) := ⟨0, Nat.zero_lt_succ _⟩
    exact ⟨i, j, by simp [i, j],
      Arnoldi.coeff_ne_zero_of_adjoint_eq_aeval A v hpdeg hp.symm hgrade⟩

/-- If $A$ is normal of degree $s$ and $s+2<d_{\min}(A)$, then every starting vector has
pre-breakdown Arnoldi upper bandwidth at most $s$. Each start of grade at least $s+2$ gives
an optimal $(s+2)$-term recurrence. This is Theorem 4.4.3 of [liesen2013krylov].

**Generalization.** The source states the result over the complex numbers. The bandwidth
and exact-length conclusions also hold over the reals. -/
theorem theorem_4_4_3 (A : Module.End 𝕜 E) {s : ℕ}
    (hs : s + 2 < operatorMinimalDegree A) (hA : IsNormalOfDegree A s) :
    (∀ v : E, Arnoldi.HasUpperBandwidth A v s) ∧
      ∀ v : E, s + 2 ≤ vectorGrade A v → AdmitsOptimalRecurrenceFor A v s := by
  refine ⟨?_, fun v hv => lemma_4_4_2 A v hs hv hA⟩
  obtain ⟨p, hpdeg, hp, -⟩ := hA
  exact fun v => Arnoldi.hasUpperBandwidth_of_adjoint_eq_aeval A v hpdeg.le hp.symm

/-- Normality of degree $s$ implies uniform admissibility of an optimal $(s+2)$-term recurrence
when $s+2<d_{\min}(A)$. A full-grade starting vector attains the bound. This is the conclusion
of Theorem 4.4.3 of [liesen2013krylov].

**Generalization.** The existence of a starting vector attaining the length holds over
the reals as well as the complex numbers. -/
theorem theorem_4_4_3_admits (A : Module.End 𝕜 E) {s : ℕ}
    (hs : s + 2 < operatorMinimalDegree A) (hA : IsNormalOfDegree A s) :
    AdmitsOptimalRecurrence A s := by
  obtain ⟨v, hv⟩ := A.exists_minpolyVec_eq_minpoly
  have hgrade : vectorGrade A v = operatorMinimalDegree A := by
    change Krylov.grade A v = (minpoly 𝕜 A).natDegree
    rw [← Krylov.natDegree_minpolyVec, hv]
  have h := theorem_4_4_3 A hs hA
  exact ⟨h.1, v, h.2 v (hgrade.symm ▸ hs.le)⟩

end LiesenStrakos
