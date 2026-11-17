import Mathlib.FieldTheory.Minpoly.Field

/-!
# Polynomial representations of least degree

A polynomial representation $b=p(a)$ has least degree $s$ if $\deg p=s$ and every
polynomial representing $b$ at $a$ has degree at least $s$.

## Main definitions

* `Polynomial.IsMinDegreeRepresentation`: polynomial representability of exact least degree.

## Implementation notes

The zero polynomial has degree $\bot$ and hence never has exact degree $s\in\mathbb N$.
-/

open Polynomial

namespace Polynomial

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- There is a polynomial $p$ of degree $s$ with $p(a)=b$, and every polynomial $q$
with $q(a)=b$ has $\deg q\ge s$. -/
def IsMinDegreeRepresentation (a b : A) (s : ℕ) : Prop :=
  ∃ p : R[X], p.degree = s ∧ aeval a p = b ∧
    ∀ q : R[X], aeval a q = b → (s : WithBot ℕ) ≤ q.degree

variable {A' : Type*} [Semiring A'] [Algebra R A']

/-- An algebra equivalence preserves polynomial representations and their least degree. -/
theorem isMinDegreeRepresentation_algEquiv_iff (e : A ≃ₐ[R] A') (a b : A) (s : ℕ) :
    IsMinDegreeRepresentation (R := R) (e a) (e b) s ↔
      IsMinDegreeRepresentation (R := R) a b s := by
  have h (p : R[X]) : aeval (e a) p = e b ↔ aeval a p = b := by
    rw [aeval_algHom_apply e, e.injective.eq_iff]
  simp only [IsMinDegreeRepresentation, h]

variable {K B : Type*} [Field K] [Ring B] [Algebra K B]

/-- When $a$ is integral, the least degree of a polynomial representing $b$ at $a$ is
strictly less than the degree of the minimal polynomial of $a$. -/
theorem IsMinDegreeRepresentation.degree_lt_minpoly {a b : B} {s : ℕ}
    (h : IsMinDegreeRepresentation (R := K) a b s) (ha : IsIntegral K a) :
    (s : WithBot ℕ) < (minpoly K a).degree := by
  obtain ⟨p, -, hp, hmin⟩ := h
  have hmod : aeval a (p %ₘ minpoly K a) = b :=
    (minpoly.aeval_modByMonic_minpoly p a).trans hp
  exact (hmin _ hmod).trans_lt (Polynomial.degree_modByMonic_lt _ (minpoly.monic ha))

/-- The least-degree polynomial representing $b$ at an integral $a$ is unique. -/
theorem IsMinDegreeRepresentation.existsUnique {a b : B} {s : ℕ}
    (h : IsMinDegreeRepresentation (R := K) a b s) (ha : IsIntegral K a) :
    ∃! p : K[X], p.degree = s ∧ aeval a p = b ∧
      ∀ q : K[X], aeval a q = b → (s : WithBot ℕ) ≤ q.degree := by
  have hbound := h.degree_lt_minpoly ha
  obtain ⟨p, hpdeg, hp, hmin⟩ := h
  refine ⟨p, ⟨hpdeg, hp, hmin⟩, ?_⟩
  rintro q ⟨hqdeg, hq, -⟩
  apply sub_eq_zero.mp
  by_contra hne
  have hann : aeval a (q - p) = 0 := by rw [map_sub, hq, hp, sub_self]
  apply (not_lt_of_ge (minpoly.degree_le_of_ne_zero K a hne hann))
  exact (degree_sub_le q p).trans_lt (by rwa [hqdeg, hpdeg, max_self])

end Polynomial
