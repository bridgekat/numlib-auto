/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Numlib.Approximation.OrthogonalDecomposition
import Numlib.LinearAlgebra.Dimension.Finrank

/-!
# Multivariate polynomials in $L^2$ of a domain

Let $\Pi_n^d$ be the space of real polynomials in $d$ variables of total degree at most $n$. This
module views $\Pi_n^d$ inside $L^2(\mu)$ for a measure $\mu$ on $\mathbb{R}^d$, and studies the
orthogonal components that the chain $\Pi_0^d \subseteq \Pi_1^d \subseteq \cdots$ induces. These are
the spaces of multivariable approximation theory. The dimension of $\Pi_n^d$ is $\binom{n + d}{d}$.

Two conditions on $\mu$ make this picture faithful: every polynomial is square integrable, and no
nonzero polynomial vanishes $\mu$-almost everywhere. The second condition makes the $L^2(\mu)$ inner
product definite on polynomials, so that the image of $\Pi_n^d$ in $L^2(\mu)$ has the same
dimension. Both conditions hold for Lebesgue measure on a compact set with nonempty interior, such
as the unit ball, the unit cube or the simplex. The same polynomials also form a subspace of
$C(D, \mathbb{R})$ for a set $D \subseteq \mathbb{R}^d$, and the distance of $f$ to that subspace is
the minimax error $E_n(f)$. Both pictures rest on one fact: a polynomial that vanishes on a set with
nonempty interior is the zero polynomial.

## Main definitions

* `Approximation.IsMvWeight`: the two conditions on $\mu$ above.
* `Approximation.IsMvWeight.toL2`: the linear map that takes a polynomial to its class in
  $L^2(\mu)$.
* `Approximation.IsMvWeight.polyLE`: the image of $\Pi_n^d$ in $L^2(\mu)$. Then
  `Approximation.orthogonalComponent hw.polyLE n` is the space of orthogonal polynomials of exact
  degree $n$ for $\mu$.
* `Approximation.toContinuousMapOn`, `Approximation.mvPolyLE`: the same passage into
  $C(D, \mathbb{R})$, where the distance to `Approximation.mvPolyLE D n` in the sup norm is the
  minimax error $E_n(f)$.

## Main results

* `MvPolynomial.finrank_restrictTotalDegree`: $\dim \Pi_n^d = \binom{n + d}{d}$.
* `MvPolynomial.eq_zero_of_eval_eq_zero_of_mem_interior`: a real polynomial that vanishes on the
  interior of a set with nonempty interior is zero.
* `Approximation.IsMvWeight.toL2_injective`, `Approximation.IsMvWeight.finrank_polyLE`: the passage
  to $L^2(\mu)$ is injective, so its image again has dimension $\binom{n + d}{d}$.
* `Approximation.toContinuousMapOn_injective`, `Approximation.finrank_mvPolyLE`: the same for the
  passage to $C(D, \mathbb{R})$, when $D$ has nonempty interior.
* `Approximation.IsMvWeight.inner_toL2_mul_left`: multiplication by a polynomial is symmetric for
  the $L^2(\mu)$ inner product.
* `Approximation.IsMvWeight.finrank_orthogonalComponent_add`: the $(n + 1)$-st orthogonal component
  has the dimension $\binom{n + 1 + d}{d} - \binom{n + d}{d}$ of the space of homogeneous
  polynomials of degree $n + 1$.
* `Approximation.isMvWeight_restrict`: a measure that charges every nonempty open set, restricted to
  a compact set of finite measure with nonempty interior, satisfies the two conditions.

## Proof outline

The dimension of $\Pi_n^d$ comes from a stars-and-bars bijection: one slack coordinate matches the
monomials of degree at most $n$ in $d$ variables with the monomials of degree exactly $n$ in $d + 1$
variables. A polynomial that vanishes on a set with nonempty interior vanishes on a box whose sides
are infinite sets, and a polynomial is determined by its values on such a box.

## Implementation notes

* The variables are indexed by a type `ι`, and the number $d$ of variables is `Fintype.card ι`.
  Points of $\mathbb{R}^d$ are functions `ι → ℝ`. The space $\Pi_n^d$ is the submodule
  `MvPolynomial.restrictTotalDegree ι ℝ n`.
* The orthogonal components are `Approximation.orthogonalComponent` of
  `Numlib.Approximation.OrthogonalDecomposition`, applied to the chain `hw.polyLE`.
-/

open Finset MeasureTheory Module

namespace MvPolynomial

section Card

variable (σ : Type*) [Fintype σ] (n : ℕ)

/-- **Stars and bars**: adding one slack coordinate gives a bijection from the exponent vectors on
$\sigma$ of total degree at most $n$ to the exponent vectors on $\sigma \cup \{\ast\}$ (the type
`Option σ`) of total degree exactly $n$.

The slack coordinate of $m$ is $n - \sum_i m_i$. -/
noncomputable def slackEquiv [DecidableEq σ] :
    ↑{m : σ →₀ ℕ | m.sum (fun _ e => e) ≤ n} ≃
      ((univ : Finset (Option σ)).finsuppAntidiag n : Finset (Option σ →₀ ℕ)) where
  toFun m := ⟨Finsupp.equivFunOnFinite.symm
      (fun o => o.elim (n - ∑ i, m.1 i) m.1), by
    have h : ∑ i, m.1 i ≤ n := by simpa [Finsupp.sum_fintype] using m.2
    simp [Finset.mem_finsuppAntidiag, Fintype.sum_option]
    omega⟩
  invFun g := ⟨Finsupp.equivFunOnFinite.symm (fun i => g.1 (some i)), by
    have h := (Finset.mem_finsuppAntidiag.1 g.2).1
    rw [Fintype.sum_option] at h
    simp [Finsupp.sum_fintype]
    omega⟩
  left_inv m := by ext i; simp
  right_inv g := by
    have h := (Finset.mem_finsuppAntidiag.1 g.2).1
    rw [Fintype.sum_option] at h
    ext o
    cases o with
    | none => simp; omega
    | some i => simp

/-- For a finite type $\sigma$ with $d$ elements, the number of exponent vectors
$m : \sigma \to \mathbb{N}$ with $\sum_i m_i \le n$, that is, of monomials in $\sigma$ of total
degree at most $n$, is $\binom{n + d}{n}$. -/
theorem card_setOf_sum_le :
    Nat.card ↑{m : σ →₀ ℕ | m.sum (fun _ e => e) ≤ n} = (n + Fintype.card σ).choose n := by
  classical
  rw [Nat.card_congr (slackEquiv σ n), Nat.card_eq_finsetCard,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp [Nat.add_comm]

/-- **The dimension of $\Pi_n^d$**: let $\sigma$ be a finite type with $d$ elements, and let $R$ be
a commutative ring that satisfies the strong rank condition (for example, any nontrivial
commutative ring). Then the module of polynomials over $R$ in the variables $\sigma$ of total
degree at most $n$ has rank
$$\operatorname{finrank}_R \Pi_n^d = \binom{n + d}{d}.$$
-/
theorem finrank_restrictTotalDegree (R : Type*) [CommRing R] [StrongRankCondition R] :
    finrank R (restrictTotalDegree σ R n) = (n + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  have hfin : Fintype ↑{m : σ →₀ ℕ | m.sum (fun _ e => e) ≤ n} :=
    Fintype.ofEquiv _ (slackEquiv σ n).symm
  rw [show restrictTotalDegree σ R n
      = restrictSupport R {m : σ →₀ ℕ | m.sum (fun _ e => e) ≤ n} from rfl,
    finrank_eq_card_basis (basisRestrictSupport R {m : σ →₀ ℕ | m.sum (fun _ e => e) ≤ n}),
    ← Nat.card_eq_fintype_card, card_setOf_sum_le,
    ← Nat.choose_symm (Nat.le_add_right n (Fintype.card σ))]
  congr 1
  omega

end Card

/-- For every commutative semiring $R$ and every type $\sigma$, if $m \le n$ then the polynomials of
total degree at most $m$ form a submodule of the polynomials of total degree at most $n$. -/
theorem restrictTotalDegree_mono (σ R : Type*) [CommSemiring R] {m n : ℕ} (h : m ≤ n) :
    restrictTotalDegree σ R m ≤ restrictTotalDegree σ R n := by
  intro p hp
  rw [mem_restrictTotalDegree] at hp ⊢
  exact hp.trans h

/-- Let $D \subseteq \mathbb{R}^\iota$ have nonempty interior, for an arbitrary index type $\iota$.
If a real polynomial $p$ in the variables $\iota$ vanishes at every point of the interior of
$D$, then $p = 0$.

The interior contains a box whose sides are infinite sets, and a polynomial is determined by its
values on such a box. -/
theorem eq_zero_of_eval_eq_zero_of_mem_interior {ι : Type*} {D : Set (ι → ℝ)}
    (hint : (interior D).Nonempty) {p : MvPolynomial ι ℝ}
    (h : ∀ x ∈ interior D, eval x p = 0) : p = 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hint
  obtain ⟨I, u, hu, hbox⟩ := isOpen_pi_iff.1 isOpen_interior x₀ hx₀
  have hsI : ∀ i ∈ I, (if i ∈ I then u i else Set.univ) = u i := fun i hi => by simp [hi]
  have hsinf : ∀ i, (if i ∈ I then u i else Set.univ : Set ℝ).Infinite := by
    intro i
    by_cases hi : i ∈ I
    · rw [hsI i hi]
      obtain ⟨a, b, hab, hsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.1 ((hu i hi).1.mem_nhds (hu i hi).2)
      exact Set.Infinite.mono hsub (Set.Ioo_infinite (hab.1.trans hab.2))
    · simp [hi, Set.infinite_univ]
  refine funext_set _ hsinf (q := 0) fun x hx => ?_
  rw [map_zero]
  refine h x (hbox fun i hi => ?_)
  rw [← hsI i hi]
  exact hx i (Set.mem_univ i)

end MvPolynomial

namespace Approximation

section ContinuousMap

variable {ι : Type*}

/-- For a set $D \subseteq \mathbb{R}^\iota$, the linear map that takes a real polynomial $p$ to the
continuous function $x \mapsto p(x)$ on $D$. -/
noncomputable def toContinuousMapOn (D : Set (ι → ℝ)) : MvPolynomial ι ℝ →ₗ[ℝ] C(D, ℝ) where
  toFun p := ⟨fun x => MvPolynomial.eval (x : ι → ℝ) p,
    (MvPolynomial.continuous_eval p).comp continuous_subtype_val⟩
  map_add' _ _ := by ext x; simp
  map_smul' _ _ := by ext x; simp

/-- The value of `Approximation.toContinuousMapOn D p` at $x \in D$ is $p(x)$. -/
@[simp]
theorem toContinuousMapOn_apply {D : Set (ι → ℝ)} (p : MvPolynomial ι ℝ) (x : D) :
    toContinuousMapOn D p x = MvPolynomial.eval (x : ι → ℝ) p := rfl

/-- For a set $D \subseteq \mathbb{R}^\iota$, **$\Pi_n$ inside $C(D, \mathbb{R})$** is the subspace
of the restrictions to $D$ of the real polynomials of total degree at most $n$.

The distance from $f \in C(D, \mathbb{R})$ to this subspace is the minimax error $E_n(f)$ of
multivariable approximation theory. This is the multivariate counterpart of `polyLE` of
`Numlib.Approximation.Chebyshev`. -/
noncomputable def mvPolyLE (D : Set (ι → ℝ)) (n : ℕ) : Submodule ℝ C(D, ℝ) :=
  (MvPolynomial.restrictTotalDegree ι ℝ n).map (toContinuousMapOn D)

/-- A function $f \in C(D, \mathbb{R})$ is in `Approximation.mvPolyLE D n` if and only if it is the
restriction to $D$ of a real polynomial of total degree at most $n$. -/
theorem mem_mvPolyLE_iff {D : Set (ι → ℝ)} {n : ℕ} {f : C(D, ℝ)} :
    f ∈ mvPolyLE D n ↔ ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ n ∧ toContinuousMapOn D p = f := by
  simp only [mvPolyLE, Submodule.mem_map, MvPolynomial.mem_restrictTotalDegree]

/-- The subspaces `Approximation.mvPolyLE D n` increase with $n$. -/
theorem mvPolyLE_mono {D : Set (ι → ℝ)} : Monotone (mvPolyLE D) := fun _ _ h =>
  Submodule.map_mono (MvPolynomial.restrictTotalDegree_mono ι ℝ h)

/-- If $D \subseteq \mathbb{R}^\iota$ has nonempty interior, then a real polynomial is determined by
its restriction to $D$: the map `Approximation.toContinuousMapOn D` is injective. -/
theorem toContinuousMapOn_injective {D : Set (ι → ℝ)} (hint : (interior D).Nonempty) :
    Function.Injective (toContinuousMapOn D) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
  refine MvPolynomial.eq_zero_of_eval_eq_zero_of_mem_interior hint fun x hx => ?_
  exact congrFun (congrArg DFunLike.coe hp) ⟨x, interior_subset hx⟩

/-- Let $\iota$ be a finite type with $d$ elements, and let $D \subseteq \mathbb{R}^\iota$ have
nonempty interior. Then the subspace `Approximation.mvPolyLE D n` of $C(D, \mathbb{R})$ has
dimension $\binom{n + d}{d}$. -/
theorem finrank_mvPolyLE [Fintype ι] {D : Set (ι → ℝ)} (hint : (interior D).Nonempty) (n : ℕ) :
    finrank ℝ (mvPolyLE D n) = (n + Fintype.card ι).choose (Fintype.card ι) := by
  rw [← MvPolynomial.finrank_restrictTotalDegree ι n ℝ]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (toContinuousMapOn_injective hint) _)).symm

end ContinuousMap

variable {ι : Type*} [MeasurableSpace (ι → ℝ)] {μ : Measure (ι → ℝ)}

/-- A measure $\mu$ on $\mathbb{R}^\iota$ is a **multivariate weight** if every real polynomial is
square integrable for $\mu$, and no nonzero polynomial vanishes $\mu$-almost everywhere.

The second condition is the $d$-dimensional counterpart of the second condition of
`OrthogonalPolynomial.IsWeight`, which asks that a weight on $\mathbb{R}$ is not carried by a
finite set. Here the exceptional sets are the zero sets of polynomials, which are the algebraic
hypersurfaces. -/
structure IsMvWeight (μ : Measure (ι → ℝ)) : Prop where
  /-- Every real polynomial is square integrable for $\mu$. -/
  memLp_eval (p : MvPolynomial ι ℝ) : MemLp (fun x => MvPolynomial.eval x p) 2 μ
  /-- A real polynomial that vanishes $\mu$-almost everywhere is zero. -/
  eq_zero_of_ae_eq_zero {p : MvPolynomial ι ℝ}
    (h : (fun x => MvPolynomial.eval x p) =ᵐ[μ] 0) : p = 0

namespace IsMvWeight

variable (hw : IsMvWeight μ)

/-- For a multivariate weight $\mu$, the linear map that takes a real polynomial to its class in
$L^2(\mu)$. -/
noncomputable def toL2 : MvPolynomial ι ℝ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun p := (hw.memLp_eval p).toLp _
  map_add' p q := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (by filter_upwards with x; simp)
  map_smul' c p := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (by filter_upwards with x; simp)

/-- The class `hw.toL2 p` in $L^2(\mu)$ is represented $\mu$-almost everywhere by the function
$x \mapsto p(x)$. -/
theorem coeFn_toL2 (p : MvPolynomial ι ℝ) :
    hw.toL2 p =ᵐ[μ] fun x => MvPolynomial.eval x p :=
  MemLp.coeFn_toLp (hw.memLp_eval p)

/-- For a multivariate weight $\mu$ and real polynomials $p, q$, the $L^2(\mu)$ inner product of
their classes is
$$\langle p, q \rangle = \int p(x) \, q(x) \, d\mu(x).$$
-/
theorem inner_toL2 (p q : MvPolynomial ι ℝ) :
    inner ℝ (hw.toL2 p) (hw.toL2 q) =
      ∫ x, MvPolynomial.eval x p * MvPolynomial.eval x q ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toL2 p, hw.coeFn_toL2 q] with x hp hq
  simp [hp, hq, mul_comm]

/-- Multiplication by a polynomial is symmetric for the $L^2(\mu)$ inner product: for a multivariate
weight $\mu$ and real polynomials $r, p, q$,
$$\langle r p, q \rangle = \langle p, r q \rangle.$$

This is the one analytic input of a three-term recursion for multivariable orthogonal
polynomials. For an integral inner product it holds by the commutativity of multiplication
alone. -/
theorem inner_toL2_mul_left (r p q : MvPolynomial ι ℝ) :
    inner ℝ (hw.toL2 (r * p)) (hw.toL2 q) = inner ℝ (hw.toL2 p) (hw.toL2 (r * q)) := by
  rw [hw.inner_toL2, hw.inner_toL2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul]
  ring

/-- For a multivariate weight $\mu$, the class of a real polynomial $p$ in $L^2(\mu)$ is zero if and
only if $p = 0$. -/
@[simp]
theorem toL2_eq_zero_iff {p : MvPolynomial ι ℝ} : hw.toL2 p = 0 ↔ p = 0 := by
  refine ⟨fun h => hw.eq_zero_of_ae_eq_zero ?_, fun h => by simp [h, map_zero]⟩
  have h0 : ⇑(hw.toL2 p) =ᵐ[μ] 0 := by rw [h]; exact Lp.coeFn_zero ℝ 2 μ
  exact (hw.coeFn_toL2 p).symm.trans h0

/-- For a multivariate weight $\mu$, distinct real polynomials have distinct classes in $L^2(\mu)$.
-/
theorem toL2_injective : Function.Injective hw.toL2 :=
  (injective_iff_map_eq_zero _).2 fun _ h => hw.toL2_eq_zero_iff.1 h

/-- For a multivariate weight $\mu$, **$\Pi_n$ inside $L^2(\mu)$** is the subspace of the classes in
$L^2(\mu)$ of the real polynomials of total degree at most $n$. -/
noncomputable def polyLE (n : ℕ) : Submodule ℝ (Lp ℝ 2 μ) :=
  (MvPolynomial.restrictTotalDegree ι ℝ n).map hw.toL2

/-- An element $f$ of $L^2(\mu)$ is in `hw.polyLE n` if and only if it is the class of a real
polynomial of total degree at most $n$. -/
theorem mem_polyLE_iff {n : ℕ} {f : Lp ℝ 2 μ} :
    f ∈ hw.polyLE n ↔ ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ n ∧ hw.toL2 p = f := by
  simp only [polyLE, Submodule.mem_map, MvPolynomial.mem_restrictTotalDegree]

/-- If a real polynomial $p$ has total degree at most $n$, then its class in $L^2(\mu)$ is in
`hw.polyLE n`. -/
theorem toL2_mem_polyLE {n : ℕ} {p : MvPolynomial ι ℝ} (hp : p.totalDegree ≤ n) :
    hw.toL2 p ∈ hw.polyLE n :=
  hw.mem_polyLE_iff.2 ⟨p, hp, rfl⟩

/-- The subspaces `hw.polyLE n` of $L^2(\mu)$ increase with $n$. -/
theorem monotone_polyLE : Monotone hw.polyLE := fun _ _ h =>
  Submodule.map_mono (MvPolynomial.restrictTotalDegree_mono ι ℝ h)

instance finiteDimensional_polyLE [Finite ι] (n : ℕ) : FiniteDimensional ℝ (hw.polyLE n) := by
  have h : Module.Finite ℝ (MvPolynomial.restrictTotalDegree ι ℝ n) := inferInstance
  exact Module.Finite.equiv (Submodule.equivMapOfInjective _ hw.toL2_injective _)

/-- Let $\mu$ be a multivariate weight on $\mathbb{R}^\iota$, with $\iota$ a finite type with $d$
elements. Then the subspace `hw.polyLE n` of $L^2(\mu)$ has dimension $\binom{n + d}{d}$. -/
theorem finrank_polyLE [Fintype ι] (n : ℕ) :
    finrank ℝ (hw.polyLE n) = (n + Fintype.card ι).choose (Fintype.card ι) := by
  rw [← MvPolynomial.finrank_restrictTotalDegree ι n ℝ]
  exact LinearMap.finrank_map_of_injective _ hw.toL2_injective _

/-- Let $\mu$ be a multivariate weight on $\mathbb{R}^\iota$, with $\iota$ a finite type with $d$
elements, and let $V_{n+1}$ be the $(n + 1)$-st orthogonal component of the chain
$\Pi_0^d \subseteq \Pi_1^d \subseteq \cdots$ in $L^2(\mu)$. Then
$$\dim V_{n+1} + \binom{n + d}{d} = \binom{n + 1 + d}{d}.$$

So $\dim V_{n+1}$ is the dimension of the space of homogeneous polynomials of degree $n + 1$ in
$d$ variables, which is $\binom{n + d}{d - 1}$ for $d \ge 1$. -/
theorem finrank_orthogonalComponent_add [Fintype ι] (n : ℕ) :
    finrank ℝ (orthogonalComponent hw.polyLE (n + 1)) +
        (n + Fintype.card ι).choose (Fintype.card ι) =
      (n + 1 + Fintype.card ι).choose (Fintype.card ι) := by
  rw [← hw.finrank_polyLE n, ← hw.finrank_polyLE (n + 1)]
  exact Approximation.finrank_orthogonalComponent_add hw.monotone_polyLE
    (fun _ => inferInstance) n

end IsMvWeight

/-- Let $\mu$ be a measure on $\mathbb{R}^\iota$ that gives positive measure to every nonempty open
set, and let $D \subseteq \mathbb{R}^\iota$ be compact and measurable, with $\mu(D) < \infty$
and nonempty interior. Then the restriction of $\mu$ to $D$ is a multivariate weight.

Polynomials are bounded on $D$, so they are square integrable. A polynomial that vanishes almost
everywhere on $D$ vanishes on a box, so it is the zero polynomial. The motivating example is
Lebesgue measure on the closed unit ball of $\mathbb{R}^d$. -/
theorem isMvWeight_restrict [OpensMeasurableSpace (ι → ℝ)] [μ.IsOpenPosMeasure]
    {D : Set (ι → ℝ)} (hD : IsCompact D) (hDm : MeasurableSet D) (hμ : μ D ≠ ⊤)
    (hint : (interior D).Nonempty) :
    IsMvWeight (μ.restrict D) := by
  have hfin : IsFiniteMeasure (μ.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hμ⟩
  refine ⟨fun p => ?_, fun {p} hp => ?_⟩
  · obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn (MvPolynomial.continuous_eval p).continuousOn
    exact MemLp.of_bound (MvPolynomial.continuous_eval p).aestronglyMeasurable C
      ((ae_restrict_iff' hDm).2 (Filter.Eventually.of_forall hC))
  · have hzero : ∀ x ∈ interior D, MvPolynomial.eval x p = 0 := by
      have hae : ∀ᵐ x ∂μ, x ∈ D → MvPolynomial.eval x p = 0 := by
        rw [← ae_restrict_iff' hDm]
        filter_upwards [hp] with x hx using hx
      have hnull : μ {x | x ∈ interior D ∧ MvPolynomial.eval x p ≠ 0} = 0 := by
        refine measure_mono_null ?_ (ae_iff.1 hae)
        rintro x ⟨hx1, hx2⟩
        simp only [Set.mem_ofPred_eq, Classical.not_imp]
        exact ⟨interior_subset hx1, hx2⟩
      have hopen : IsOpen {x | x ∈ interior D ∧ MvPolynomial.eval x p ≠ 0} :=
        isOpen_interior.inter (isOpen_ne_fun (MvPolynomial.continuous_eval p) continuous_const)
      have hempty := (IsOpen.measure_eq_zero_iff μ hopen).1 hnull
      intro x hx
      by_contra hne
      exact Set.eq_empty_iff_forall_notMem.1 hempty x ⟨hx, hne⟩
    exact MvPolynomial.eq_zero_of_eval_eq_zero_of_mem_interior hint hzero

end Approximation
