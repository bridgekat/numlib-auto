/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.HermiteInterpolation
import NumlibSurface.LiesenStrakos.Chapter03.Section01

/-!
# Model reduction via orthogonal polynomials

The Gauss–Christoffel rule uses the roots of the monic orthogonal polynomial of degree $n$
as nodes and the integrals of their Lagrange basis polynomials as weights. It is exact through
degree $2n-1$ and yields the reduced distribution in the simplified Stieltjes moment problem
of [liesen2013krylov].

## Main definitions

* `LiesenStrakos.Chapter03.interpolatoryWeight` is the integral of a Lagrange basis polynomial.
* `LiesenStrakos.Chapter03.monicOrthogonalPolynomial` is the monic orthogonal polynomial.
* `LiesenStrakos.Chapter03.IsGaussChristoffel` specifies the maximal-degree interpolatory rule.

## Main results

* `LiesenStrakos.Chapter03.lemma_3_2_1` characterizes the exactness of interpolatory rules.
* `LiesenStrakos.Chapter03.lemma_3_2_5` characterizes maximal exactness by the nodal polynomial.
* `LiesenStrakos.Chapter03.theorem_3_2_7` gives the divided-difference formulas for the error.
* `LiesenStrakos.Chapter03.theorem_3_2_8` gives existence and uniqueness of the compact rule.
* `LiesenStrakos.Chapter03.gaussChristoffel_tendsto_integral` gives convergence on continuous
  functions.

## Deviations from the source

* **Section 3.2** (generalization). The basic definitions are total. The hypotheses in the
  orthogonal polynomial results permit measures that charge the left endpoint where the
  displayed interval is closed.
* **Theorem 3.2.7** (generalization). The error identities use total Hermite divided
  differences, integrable data and multiset extra nodes.
* **Theorem 3.2.8** (reading). The existence and uniqueness statement uses the rule
  predicate with nodes in $(a,b]$. Interior location and the node and weight formulas
  are treated separately. See `LiesenStrakos.Chapter03.theorem_3_2_8`.

-/

open Filter MeasureTheory OrthogonalPolynomial Polynomial Topology
open scoped Polynomial

namespace LiesenStrakos.Chapter03

variable {μ : Measure ℝ} {n : ℕ}

/-- The interpolatory weight at node $i$ is the integral of the corresponding Lagrange basis
polynomial, as in (3.2.5) of [liesen2013krylov].

**Generalization.** The formula uses total integration and accepts arbitrary nodes. -/
noncomputable def interpolatoryWeight (μ : Measure ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ

/-- The monic orthogonal polynomial of degree $n$ for $\mu$ is the monic polynomial formed
by Gram–Schmidt orthogonalization of the monomials with respect to the integral pairing.
This is $\psi_n$ in (3.2.7) of [liesen2013krylov].

**Generalization.** The Gram–Schmidt recurrence is total. Its orthogonality properties use
integrability and sufficient support of the measure. -/
noncomputable def monicOrthogonalPolynomial (μ : Measure ℝ) (n : ℕ) : ℝ[X] :=
  OrthogonalPolynomial.family μ n

/-- The polynomial pairing induced by the distribution $\mu$ is $(p,q)=\int pq\,d\mu$.
This is (3.2.8) of [liesen2013krylov].

**Generalization.** The integral pairing is defined even when it is degenerate. -/
noncomputable def polynomialInner (μ : Measure ℝ) (p q : ℝ[X]) : ℝ :=
  ∫ t, p.eval t * q.eval t ∂μ

/-- **Lemma 3.2.1** of [liesen2013krylov]. A rule on $n+1$ distinct nodes is exact through
degree $n$ if and only if it is interpolatory. The basis polynomials are integrable, as holds
for a finite measure supported on a closed bounded interval.

**Generalization.** Integrability of the Lagrange basis suffices. The nodes and measure need no
common compact interval. -/
theorem lemma_3_2_1 {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hint : ∀ i, Integrable (fun t => (Lagrange.basis Finset.univ x i).eval t) μ) :
    Quadrature.IsExactOnMeasure μ w x n ↔ ∀ i, w i = interpolatoryWeight μ x i :=
  (Quadrature.isInterpolatoryMeasure_iff_isExactOnMeasure_of_integrable_basis hx hint).symm

/-- **Lemma 3.2.2** of [liesen2013krylov]. The monic orthogonal polynomial uniquely minimizes
the squared norm among monic polynomials of degree $n$ if the measure on $[a,b]$ is carried by
no set of fewer than $n$ points. This includes the orthogonal polynomial of degree equal to
the support size of a finite distribution.

**Generalization.** The strict comparison also applies at the terminal degree of a finite
support. -/
theorem lemma_3_2_2 [IsFiniteMeasure μ] {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (hm : ∀ s : Finset ℝ, s.card < n → μ (↑s : Set ℝ)ᶜ ≠ 0)
    {p : ℝ[X]} (hp : p.Monic) (hdeg : p.degree = n) (hne : p ≠ monicOrthogonalPolynomial μ n) :
    polynomialInner μ (monicOrthogonalPolynomial μ n) (monicOrthogonalPolynomial μ n) <
      polynomialInner μ p p := by
  let q := family μ n
  let r := p - q
  let hint := integrable_eval_of_measure_compl_Icc_eq_zero hsupp
  have hintmul (u v : ℝ[X]) : Integrable (fun t => u.eval t * v.eval t) μ := by
    simpa only [eval_mul] using hint (u * v)
  have hrdeg : r.degree < n := by
    have h := degree_sub_lt_left (hdeg.trans (degree_family μ n).symm) hp.ne_zero
      (hp.leadingCoeff.trans (monic_family μ n).leadingCoeff.symm)
    rwa [hdeg] at h
  have hne' : r ≠ 0 := sub_ne_zero.mpr hne
  have horth : (∫ t, q.eval t * r.eval t ∂μ) = 0 :=
    integral_family_mul_of_degree_lt_of_integrable hint
      (fun _ hj => normSq_ne_zero_of_card_lt hint hm hj) hrdeg
  have hrd : r.natDegree < n := (natDegree_lt_iff_degree_lt hne').2 hrdeg
  have hsq : 0 < ∫ t, (r.eval t) ^ 2 ∂μ :=
    integral_eval_sq_pos_of_degree_le hint (fun s hs => hm s (hs.trans_lt hrd))
      hne' degree_le_natDegree
  have heq (t : ℝ) : p.eval t * p.eval t =
      q.eval t * q.eval t + 2 * (q.eval t * r.eval t) + (r.eval t) ^ 2 := by
    simp [r, eval_sub]
    ring
  have hint₁ : Integrable (fun t => 2 * (q.eval t * r.eval t)) μ :=
    (hintmul q r).const_mul 2
  have hint₂ : Integrable (fun t => q.eval t * q.eval t + 2 * (q.eval t * r.eval t)) μ :=
    (hintmul q q).add hint₁
  have hint₃ : Integrable (fun t => r.eval t ^ 2) μ := by simpa only [pow_two] using hintmul r r
  unfold polynomialInner
  rw [integral_congr_ae (Filter.Eventually.of_forall heq),
    integral_add hint₂ hint₃, integral_add (hintmul q q) hint₁,
    integral_const_mul, horth, mul_zero, add_zero]
  change (∫ t, q.eval t * q.eval t ∂μ) <
    (∫ t, q.eval t * q.eval t ∂μ) + ∫ t, r.eval t ^ 2 ∂μ
  exact lt_add_of_pos_right _ hsq

/-- **Remark 3.2.3** of [liesen2013krylov]. For any symmetric positive definite polynomial
pairing $B$, a monic degree-$n$ polynomial $q_n$ orthogonal to the preceding monic polynomials
of degrees $0,\ldots,n-1$ uniquely minimizes $B(p,p)$ among monic polynomials of degree $n$.
Positive definiteness is required only through degree $n$.

**Generalization.** Positivity is required only through degree $n$, and the orthogonality
hypothesis concerns the $n$th polynomial and its predecessors. -/
theorem remark_3_2_3 (B : ℝ[X] →ₗ[ℝ] ℝ[X] →ₗ[ℝ] ℝ)
    (hsym : ∀ u v, B u v = B v u) (hpos : ∀ u : ℝ[X], u.degree ≤ n → u ≠ 0 → 0 < B u u)
    (q : ℕ → ℝ[X]) (hq : ∀ i, (q i).Monic) (hdeg : ∀ i, (q i).degree = i)
    (horth : ∀ i < n, B (q n) (q i) = 0)
    {p : ℝ[X]} (hp : p.Monic) (hpdeg : p.degree = n) (hne : p ≠ q n) :
    B (q n) (q n) < B p p := by
  let r := p - q n
  have hrdeg : r.degree < n := by
    have h := degree_sub_lt_left (hpdeg.trans (hdeg n).symm) hp.ne_zero
      (hp.leadingCoeff.trans (hq n).leadingCoeff.symm)
    rwa [hpdeg] at h
  have hspace : Polynomial.degreeLT ℝ n ≤ LinearMap.ker (B (q n)) := by
    rw [← Polynomial.Sequence.span_degreeLT (⟨q, hdeg⟩ : Polynomial.Sequence ℝ)
      (fun i _ => by simp [(hq i).leadingCoeff]), Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact LinearMap.mem_ker.2 (horth i hi)
  have hb := LinearMap.mem_ker.1 (hspace (Polynomial.mem_degreeLT.2 hrdeg))
  have hb' : B r (q n) = 0 := (hsym r (q n)).trans hb
  have hdecomp : p = q n + r := by dsimp [r]; abel
  calc
    B (q n) (q n) < B (q n) (q n) + B r r :=
      lt_add_of_pos_right _ (hpos r hrdeg.le (sub_ne_zero.2 hne))
    _ = B p p := by
      rw [hdecomp]
      simp only [map_add, LinearMap.add_apply, hb, hb', add_zero, zero_add]

/-- **Lemma 3.2.4** of [liesen2013krylov]. If the measure is carried by no set of at most $n$
points, then the $n$ distinct zeros of its monic orthogonal polynomial are interior to the
interval carrying the measure.

**Generalization.** The measure may charge the left endpoint and the statement also includes
degree zero. -/
theorem lemma_3_2_4 [IsFiniteMeasure μ] {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (hm : ∀ s : Finset ℝ, s.card ≤ n → μ (↑s : Set ℝ)ᶜ ≠ 0) :
    ∃ x : Fin n → ℝ, Function.Injective x ∧ (∀ i, x i ∈ Set.Ioo a b) ∧
      monicOrthogonalPolynomial μ n = ∏ i, (X - C (x i)) := by
  classical
  obtain ⟨x, hinj, hprod⟩ := exists_injective_family_eq_prod_of_measure_compl_ne_zero
    (integrable_eval_of_measure_compl_Icc_eq_zero hsupp) n hm
  refine ⟨x, hinj, fun i => root_family_mem_Ioo_of_measure_compl_ne_zero hsupp hm ?_, hprod⟩
  rw [hprod, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- **Lemma 3.2.4** of [liesen2013krylov], terminal case. If the support consists of exactly $n$
points $x_i$, the $n$th monic orthogonal polynomial has precisely those points as its roots.

**Generalization.** The support enumeration need no specified order and may include the left
endpoint. -/
theorem lemma_3_2_4_terminal [IsFiniteMeasure μ] {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    {x : Fin n → ℝ} (hx : μ (Set.range x)ᶜ = 0)
    (hm : ∀ s : Finset ℝ, s.card < n → μ (↑s : Set ℝ)ᶜ ≠ 0) :
    monicOrthogonalPolynomial μ n = Lagrange.nodal Finset.univ x := by
  by_contra h
  have hdeg : (Lagrange.nodal Finset.univ x).degree = n := by rw [Lagrange.degree_nodal]; simp
  have hpos := lemma_3_2_2 hsupp hm Lagrange.nodal_monic hdeg (fun he => h he.symm)
  have hzero : polynomialInner μ (Lagrange.nodal Finset.univ x) (Lagrange.nodal Finset.univ x) =
      0 := by
    have hae : ∀ᵐ t ∂μ, t ∈ Set.range x := MeasureTheory.ae_iff.2 hx
    rw [polynomialInner, integral_congr_ae (hae.mono ?_), integral_zero]
    rintro _ ⟨i, rfl⟩
    simp only [Lagrange.eval_nodal_at_node (Finset.mem_univ i), mul_zero]
  rw [hzero] at hpos
  exact hpos.not_ge (integral_nonneg fun _ => mul_self_nonneg _)

/-- The Gauss–Christoffel rule of Definition 3.2.6 in [liesen2013krylov] is an interpolatory
rule on distinct nodes with exactness degree $2n+1$ for a rule of size $n+1$. -/
def IsGaussChristoffel (μ : Measure ℝ) (x w : Fin (n + 1) → ℝ) : Prop :=
  Function.Injective x ∧ Quadrature.IsInterpolatoryMeasure μ w x ∧
    HasQuadratureDegree μ x w (2 * n + 1)

/-- **Lemma 3.2.5** of [liesen2013krylov]. If the support has more than $n+1$ points, a rule with
$n+1$ distinct nodes has exactness degree $2n+1$ if and only if it is interpolatory and its nodal
polynomial is the monic orthogonal polynomial of degree $n+1$.

**Generalization.** The measure may charge the left endpoint. -/
theorem lemma_3_2_5 [IsFiniteMeasure μ] {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (hm : ∀ s : Finset ℝ, s.card ≤ n + 1 → μ (↑s : Set ℝ)ᶜ ≠ 0)
    {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x) :
    HasQuadratureDegree μ x w (2 * n + 1) ↔
      Lagrange.nodal Finset.univ x = monicOrthogonalPolynomial μ (n + 1) ∧
      Quadrature.IsInterpolatoryMeasure μ w x := by
  let hint := integrable_eval_of_measure_compl_Icc_eq_zero hsupp
  have hmax : ¬ Quadrature.IsExactOnMeasure μ w x (2 * n + 1 + 1) :=
    Quadrature.not_isExactOnMeasure_two_mul_add_two_of_card_le hint hm w x
  rw [HasQuadratureDegree, and_iff_left hmax]
  exact Quadrature.isExactOnMeasure_two_mul_add_one_iff_of_card_lt hint
    (fun s hs => hm s hs.le) hx w

private theorem error_eq_integral_divDiff [IsFiniteMeasure μ] {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {x w : Fin n → ℝ} {d : ℕ}
    (hexact : Quadrature.IsExactOnMeasure μ w x d) {f : ℝ → ℝ} (hf : Integrable f μ)
    (s : Multiset ℝ) (hs : s.card ≤ d + 1) (hx : ∀ i, x i ∈ s) :
    (∫ z, f z ∂μ) - ∑ i, w i * f (x i) =
      ∫ z, (Hermite.nodalMultiset s).eval z * Hermite.divDiff f (z ::ₘ s) ∂μ := by
  let p := Hermite.interpolateJet s (Hermite.taylorJet f)
  have hdeg : p.degree < ↑(d + 1) :=
    (Hermite.degree_interpolateJet_lt s (Hermite.taylorJet f)).trans_le (by exact_mod_cast hs)
  have heq := (Quadrature.isExactOnMeasure_iff_forall_degree_lt.1 hexact) p hdeg
  have hnode (i : Fin n) : p.eval (x i) = f (x i) :=
    Hermite.eval_interpolateJet_taylorJet (hx i)
  simp only [hnode] at heq
  have hp := integrable_eval_of_measure_compl_Icc_eq_zero hsupp p
  rw [heq, ← integral_sub hf hp]
  congr 1
  funext z
  have hz := congrArg (fun q : ℝ[X] => q.eval z)
    (Hermite.interpolateJet_cons_sub z s (Hermite.taylorJet f))
  simp only [eval_sub, eval_mul, eval_C, Hermite.eval_interpolateJet_taylorJet
    (Multiset.mem_cons_self z s)] at hz
  rw [Hermite.divDiff, Multiset.card_cons, Nat.add_sub_cancel, mul_comm]
  exact hz

/-- **Theorem 3.2.7** of [liesen2013krylov], equations (3.2.14) and (3.2.15).
The error of an $n$-node Gauss rule is the integral of its nodal polynomial times the divided
difference at its nodes and the argument. Adding up to $n$ interpolation nodes leaves the integral
unchanged when the extra factors are included and the divided difference uses all the nodes.
Multisets give confluent divided differences at repeated nodes. The weighted remainder identity
uses only integrability of $f$, since the interpolation jets at a node are total in Lean.

**Generalization.** The identities use total Hermite divided differences and require
integrability of $f$. Extra nodes are supplied as a multiset, so repeats and coincidences with
quadrature nodes are allowed. -/
theorem theorem_3_2_7 [IsFiniteMeasure μ] {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (hn : 0 < n) {x w : Fin n → ℝ} (hexact : Quadrature.IsExactOnMeasure μ w x (2 * n - 1))
    {f : ℝ → ℝ} (hf : Integrable f μ) (extra : Multiset ℝ) (hm : extra.card ≤ n) :
    let s := (Finset.univ : Finset (Fin n)).val.map x
    let err := (∫ z, f z ∂μ) - ∑ i, w i * f (x i)
    err = (∫ z, (Hermite.nodalMultiset s).eval z * Hermite.divDiff f (z ::ₘ s) ∂μ) ∧
    err = ∫ z, (Hermite.nodalMultiset s).eval z * (Hermite.nodalMultiset extra).eval z *
      Hermite.divDiff f (z ::ₘ (s + extra)) ∂μ := by
  dsimp only
  let s := (Finset.univ : Finset (Fin n)).val.map x
  have hs : s.card = n := by simp [s]
  have hx (i : Fin n) : x i ∈ s := Multiset.mem_map_of_mem _ (by simp)
  refine ⟨error_eq_integral_divDiff hsupp hexact hf s (by omega) hx, ?_⟩
  have h := error_eq_integral_divDiff hsupp hexact hf (s + extra)
    (by rw [Multiset.card_add]; omega) (fun i => Multiset.mem_add.2 (Or.inl (hx i)))
  simpa only [Hermite.nodalMultiset_add, eval_mul] using h

/-- **Theorem 3.2.8** of [liesen2013krylov]. A probability measure carried by $[a,b]$ with more
than $n+1$ support points has a unique positive, normalized, strictly ordered rule with $n+1$
nodes in $(a,b]$ matching its first $2(n+1)$ moments.

**Reading.** The printed theorem also gives the strict interior location of the nodes and
identifies the nodes and weights. The existence and uniqueness conclusion uses the predicate
for Problem 3.1.1, which allows the right endpoint. The root description and interiority are
given by `LiesenStrakos.Chapter03.lemma_3_2_5` and `LiesenStrakos.Chapter03.lemma_3_2_4`.
The weights are the interpolatory weights from `LiesenStrakos.Chapter03.interpolatoryWeight`. -/
theorem theorem_3_2_8 [IsProbabilityMeasure μ] {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (hcard : ∀ s : Finset ℝ, s.card ≤ n + 1 → μ (↑s : Set ℝ)ᶜ ≠ 0) :
    ∃! rule : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ),
      SolvesStieltjesProblem μ a b rule.1 rule.2 := by
  classical
  let hint := integrable_eval_of_measure_compl_Icc_eq_zero hsupp
  have hpow (k : ℕ) : Integrable (fun t : ℝ => t ^ k) μ := by
    simpa only [eval_pow, eval_X] using hint (X ^ k)
  obtain ⟨x, w, hx, hwpos, h⟩ := Quadrature.exists_gauss_of_measure_compl_ne_zero
    hint (n + 1) hcard
  have hxexact : Quadrature.IsExactOnMeasure μ w x (2 * n + 1) := by
    apply (Quadrature.isExactOnMeasure_iff_forall_degree_lt).2
    rwa [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
  let s := Finset.univ.image x
  have hs : s.card = n + 1 := by simp [s, Finset.card_image_of_injective _ hx]
  let z := s.orderEmbOfFin hs
  have hzrange : Set.range z = Set.range x := by
    rw [Finset.range_orderEmbOfFin, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hex (i : Fin (n + 1)) : ∃ j, x j = z i := by
    have : z i ∈ Set.range x := hzrange ▸ Set.mem_range_self i
    exact this
  choose f hf using hex
  have hfinj : Function.Injective f := fun i j hij => z.injective (by rw [← hf i, ← hf j, hij])
  let σ := Equiv.ofBijective f ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  have hz : (⇑z : Fin (n + 1) → ℝ) = x ∘ σ := funext fun i => (hf i).symm
  let v := w ∘ σ
  have hzexact : Quadrature.IsExactOnMeasure μ v z (2 * n + 1) := by
    rw [hz]
    exact (Quadrature.isExactOnMeasure_comp_equiv σ).2 hxexact
  have hnorm : ∑ i, v i = 1 := by
    simpa using hzexact (1 : ℝ[X]) (by rw [degree_one]; exact_mod_cast Nat.zero_le (2 * n + 1))
  have hzpos (i : Fin (n + 1)) : 0 < v i := hwpos (σ i)
  have hnodal := (Quadrature.isExactOnMeasure_two_mul_add_one_iff_of_card_lt hint
    (fun s hs => hcard s hs.le) z.injective v).1 hzexact
  have hmem (i : Fin (n + 1)) : z i ∈ Set.Ioc a b := by
    refine Set.Ioo_subset_Ioc_self (root_family_mem_Ioo_of_measure_compl_ne_zero hsupp hcard ?_)
    rw [← hnodal.1]
    exact Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have hsimp : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  refine ⟨(z, v), ?_, ?_⟩
  · apply (solvesStieltjesProblem_iff hpow n.succ_pos z.strictMono hmem hzpos hnorm).2
    rwa [hsimp]
  · rintro ⟨y, u⟩ ⟨_, hy, hm, hu, ht, he⟩
    have hyexact :=
      (solvesStieltjesProblem_iff hpow n.succ_pos hy hm hu ht).1
        ⟨n.succ_pos, hy, hm, hu, ht, he⟩
    rw [hsimp] at hyexact
    have hynodal := (Quadrature.isExactOnMeasure_two_mul_add_one_iff_of_card_lt hint
      (fun s hs => hcard s hs.le) hy.injective u).1 hyexact
    have hroots (p : Fin (n + 1) → ℝ) (hp : Lagrange.nodal Finset.univ p = family μ (n + 1)) :
        Set.range p = {t | (family μ (n + 1)).eval t = 0} := by
      rw [← hp]
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_range, Lagrange.eval_nodal, Finset.prod_eq_zero_iff,
        Finset.mem_univ, true_and, sub_eq_zero]
      exact exists_congr fun _ => eq_comm
    have heq : y = z :=
      (hy.range_inj_of_wellFoundedLT z.strictMono).1
        ((hroots y hynodal.1).trans (hroots z hnodal.1).symm)
    subst y
    exact Prod.ext rfl (funext fun i => (hynodal.2 i).trans (hnodal.2 i).symm)

/-- A sequence of positive quadratures on $[a,b]$ whose degrees of exactness tend to infinity
converges to the integral on every continuous function, as in Remark 3.2.9 of
[liesen2013krylov].

**Generalization.** The convergence applies to nonnegative rules with increasing degrees of
exactness for any finite measure carried by the interval. -/
theorem gaussChristoffel_tendsto_integral [IsFiniteMeasure μ] {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {m d : ℕ → ℕ} {x w : ∀ k, Fin (m k) → ℝ}
    (hinj : ∀ k, Function.Injective (x k)) (hmem : ∀ k i, x k i ∈ Set.Icc a b)
    (hw : ∀ k i, 0 ≤ w k i) (hd : Tendsto d atTop atTop)
    (hexact : ∀ k, Quadrature.IsExactOnMeasure μ (w k) (x k) (d k))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    Tendsto (fun k => mechanicalQuadrature (x k) (w k) f) atTop (𝓝 (∫ t, f t ∂μ)) :=
  Quadrature.tendsto_of_isExactOnMeasure hsupp hinj hmem hw hd hexact hf

end LiesenStrakos.Chapter03
