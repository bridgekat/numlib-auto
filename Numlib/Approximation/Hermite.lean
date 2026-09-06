import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.DegreeLT
import Numlib.Approximation.Interpolation

/-!
# Hermite interpolation

Interpolation of a function and its derivatives at finitely many nodes: given distinct nodes
`x i` and multiplicities `m i`, the Hermite interpolant is the polynomial of degree less than
`∑ i, (m i + 1)` whose derivatives of order `j ≤ m i` agree with those of `f` at `x i`. The
material is Atkinson–Han, *Theoretical Numerical Analysis*[^atkinson-han] §3.2.2 and Kress,
*Numerical Analysis*[^kress] §8.1.

## Main definitions

* `Hermite.nodal x m` is the nodal polynomial `∏ i, (X - x i) ^ (m i + 1)`, which carries the
  interpolation error.
* `Hermite.interpolate x m f` is the interpolant itself, with `Hermite.degree_interpolate_lt`,
  `Hermite.eval_iterate_derivative_interpolate` and `Hermite.eq_interpolate` for its defining
  properties, and `Hermite.interpolate_zero_eq_lagrange` for the simple-node case.

## Main results

* `Hermite.exists_iteratedDeriv_eq_zero` is **Rolle's theorem with multiplicities**: a function
  whose zeros in `[a, b]`, counted with multiplicity, number `N + 2` has a vanishing derivative
  of order `N + 1` somewhere in `[a, b]`. It strengthens the
  `exists_iteratedDeriv_eq_zero_of_forall_eq_zero` of `Numlib/Approximation/Interpolation`, which
  is the case of simple zeros, and it is the only real work of the module.
* `Hermite.isUnisolvent` is unique solvability of the Hermite problem. Injectivity of the
  problem is that a nonzero polynomial cannot have more roots, counted with multiplicity, than
  its degree; surjectivity is then a dimension count, the data space and the polynomials of
  degree less than `∑ (m i + 1)` having the same finite dimension.
* `Hermite.exists_sub_interpolate_eq` is the error formula
  `f(t) - p(t) = f^{(N+1)}(ξ)/(N+1)! ∏ (t - x i)^{m i + 1}`, proved from the Rolle theorem exactly
  as the Lagrange error formula is proved from the simple one.

## Implementation notes

Divided-difference forms of the error and the Newton form of the interpolant are not developed:
nothing downstream uses them.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009. (§3.2.2, (3.2.6), Exercise 3.2.6.)
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
  (§8.1.)
-/

open scoped Polynomial

namespace Hermite

/-! ### Rolle's theorem with multiplicities -/

/-- The induction behind Rolle's theorem with multiplicities, phrased over an explicit sequence
`F` of successive derivatives and a multiplicity function `Z`: if `F 0` vanishes at each point of
`s` to the order `Z` prescribes, and those orders sum to `k + 1`, then `F k` vanishes somewhere
in `[a, b]`.

Each node of multiplicity `Z t` contributes a zero of multiplicity `Z t - 1` of `F 1`, and each
of the `s.card - 1` gaps between consecutive nodes contributes one more by Rolle's theorem, so
the orders available to `F 1` sum to `k`. -/
private theorem exists_eq_zero_mult_aux {a b : ℝ} :
    ∀ (k : ℕ) (F : ℕ → ℝ → ℝ),
      (∀ j < k, ∀ t : ℝ, HasDerivAt (F j) (F (j + 1) t) t) →
      ∀ (s : Finset ℝ) (Z : ℝ → ℕ), (∀ t ∈ s, 1 ≤ Z t) → (∀ t ∈ s, t ∈ Set.Icc a b) →
        (∀ t ∈ s, ∀ j < Z t, F j t = 0) → ∑ t ∈ s, Z t = k + 1 →
        ∃ ξ ∈ Set.Icc a b, F k ξ = 0 := by
  intro k
  induction k with
  | zero =>
    intro F _ s Z hpos hsub hzero hsum
    obtain ⟨t, ht⟩ : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp at hsum
    exact ⟨t, hsub t ht, hzero t ht 0 (hpos t ht)⟩
  | succ k ih =>
    intro F hF s Z hpos hsub hzero hsum
    classical
    -- the nodes, in increasing order
    obtain ⟨p, hcard⟩ : ∃ p, s.card = p + 1 := by
      refine ⟨s.card - 1, ?_⟩
      have : s.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp at hsum
      have := Finset.card_pos.mpr this
      omega
    set y : Fin (p + 1) → ℝ := ⇑(s.orderEmbOfFin hcard) with hy
    have hymono : StrictMono y := (s.orderEmbOfFin hcard).strictMono
    have hymem : ∀ i, y i ∈ s := fun i => Finset.orderEmbOfFin_mem s hcard i
    have hyrange : ∀ t ∈ s, ∃ i, y i = t := by
      intro t ht
      have : t ∈ Set.range y := by
        rw [hy, Finset.range_orderEmbOfFin]
        exact ht
      exact this
    have hdiff0 : Differentiable ℝ (F 0) := fun t => (hF 0 (Nat.succ_pos k) t).differentiableAt
    have hcont : Continuous (F 0) := hdiff0.continuous
    -- one Rolle step in each gap
    have hrolle : ∀ i : Fin p, ∃ c ∈ Set.Ioo (y i.castSucc) (y i.succ), F 1 c = 0 := by
      intro i
      refine exists_hasDerivAt_eq_zero (f := F 0) (hymono (Fin.castSucc_lt_succ (i := i)))
        hcont.continuousOn ?_ fun t _ => hF 0 (Nat.succ_pos k) t
      rw [hzero _ (hymem _) 0 (hpos _ (hymem _)), hzero _ (hymem _) 0 (hpos _ (hymem _))]
    choose c hc hc0 using hrolle
    have hcmono : StrictMono c := by
      intro i j hij
      calc c i < y i.succ := (hc i).2
        _ ≤ y j.castSucc := hymono.monotone (by
            simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
            omega)
        _ < c j := (hc j).1
    have hcnots : ∀ i, c i ∉ s := by
      intro i hci
      obtain ⟨j, hj⟩ := hyrange _ hci
      have h1 : i.castSucc < j := hymono.lt_iff_lt.mp (hj ▸ (hc i).1)
      have h2 : j < i.succ := hymono.lt_iff_lt.mp (hj ▸ (hc i).2)
      simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at h1 h2
      omega
    -- the nodes of `F 1`, with their multiplicities
    set G : Finset ℝ := Finset.image c Finset.univ with hG
    set s' : Finset ℝ := s.filter (fun t => 2 ≤ Z t) ∪ G with hs'
    set Z' : ℝ → ℕ := fun t => if t ∈ s then Z t - 1 else 1 with hZ'
    have hZ's : ∀ t ∈ s, Z' t = Z t - 1 := fun t ht => ite_eq_left ht
    have hZ'n : ∀ t ∉ s, Z' t = 1 := fun t ht => ite_eq_right ht
    have hGcard : G.card = p := by
      rw [hG, Finset.card_image_of_injective _ hcmono.injective, Finset.card_univ,
        Fintype.card_fin]
    have hGnots : ∀ t ∈ G, t ∉ s := by
      intro t ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      exact hcnots i
    have hdisj : Disjoint (s.filter (fun t => 2 ≤ Z t)) G := by
      rw [Finset.disjoint_right]
      exact fun t ht htf => hGnots t ht (Finset.mem_filter.mp htf).1
    -- the orders available to `F 1` sum to `k + 1`
    have hsum' : ∑ t ∈ s', Z' t = k + 1 := by
      have hsplit : ∑ t ∈ s', Z' t
          = (∑ t ∈ s.filter (fun t => 2 ≤ Z t), Z' t) + ∑ t ∈ G, Z' t := by
        rw [hs', Finset.sum_union hdisj]
      have hG' : ∑ t ∈ G, Z' t = p := by
        rw [← hGcard, Finset.card_eq_sum_ones]
        exact Finset.sum_congr rfl fun t ht => hZ'n t (hGnots t ht)
      have hfil : ∑ t ∈ s.filter (fun t => 2 ≤ Z t), Z' t = ∑ t ∈ s, (Z t - 1) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [hZ's t ht]
        by_cases h2 : 2 ≤ Z t
        · rw [ite_eq_left h2]
        · rw [ite_eq_right h2]
          have := hpos t ht
          omega
      have hZsum : ∑ t ∈ s, (Z t - 1) + s.card = k + 2 := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib, ← hsum]
        refine Finset.sum_congr rfl fun t ht => ?_
        have := hpos t ht
        omega
      rw [hsplit, hfil, hG']
      omega
    have hpos' : ∀ t ∈ s', 1 ≤ Z' t := by
      intro t ht
      rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨hts, h2⟩ := Finset.mem_filter.mp ht
        rw [hZ's t hts]
        omega
      · rw [hZ'n t (hGnots t ht)]
    have hsub' : ∀ t ∈ s', t ∈ Set.Icc a b := by
      intro t ht
      rcases Finset.mem_union.mp ht with ht | ht
      · exact hsub t (Finset.mem_filter.mp ht).1
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
        exact ⟨le_trans (hsub _ (hymem i.castSucc)).1 (hc i).1.le,
          le_trans (hc i).2.le (hsub _ (hymem i.succ)).2⟩
    have hzero' : ∀ t ∈ s', ∀ j < Z' t, F (j + 1) t = 0 := by
      intro t ht j hj
      rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨hts, -⟩ := Finset.mem_filter.mp ht
        rw [hZ's t hts] at hj
        exact hzero t hts (j + 1) (by omega)
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
        rw [hZ'n _ (hcnots i)] at hj
        interval_cases j
        exact hc0 i
    obtain ⟨ξ, hξ, hξ0⟩ := ih (fun j => F (j + 1))
      (fun j hj t => hF (j + 1) (by omega) t) s' Z' hpos' hsub' hzero' hsum'
    exact ⟨ξ, hξ, hξ0⟩

/-- **Rolle's theorem with multiplicities.** If `g` is of class `C^{N+1}`, the nodes `x` are
distinct points of `[a, b]`, `g` vanishes at `x i` together with its first `m i` derivatives, and
the multiplicities `m i + 1` sum to `N + 2`, then the `(N + 1)`-st derivative of `g` vanishes
somewhere in `[a, b]`.

For `m = 0` and `n = N + 2` this is `exists_iteratedDeriv_eq_zero_of_forall_eq_zero`, whose
conclusion is the sharper `Set.Ioo a b`; with multiplicities the open interval is out of reach,
since a single node of multiplicity `N + 2` may be an endpoint.

Reference: Kress, *Numerical Analysis*, §8.1; Atkinson–Han, *Theoretical Numerical Analysis*,
§3.2.2. -/
theorem exists_iteratedDeriv_eq_zero {N n : ℕ} {a b : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) g) {x : Fin n → ℝ}
    (hx : Function.Injective x) (hmem : ∀ i, x i ∈ Set.Icc a b) {m : Fin n → ℕ}
    (hsum : ∑ i, (m i + 1) = N + 2)
    (hzero : ∀ i, ∀ j ≤ m i, iteratedDeriv j g (x i) = 0) :
    ∃ ξ ∈ Set.Icc a b, iteratedDeriv (N + 1) g ξ = 0 := by
  classical
  -- the successive derivatives of `g`
  have hdiff : ∀ j < N + 1, Differentiable ℝ (iteratedDeriv j g) := fun j hj =>
    hg.differentiable_iteratedDeriv j (by exact_mod_cast hj)
  have hstep : ∀ j < N + 1, ∀ t : ℝ,
      HasDerivAt (iteratedDeriv j g) (iteratedDeriv (j + 1) g t) t := by
    intro j hj t
    have h := ((hdiff j hj) t).hasDerivAt
    rwa [← iteratedDeriv_succ] at h
  -- the multiplicity function of the nodes
  set s : Finset ℝ := Finset.image x Finset.univ with hs
  set Z : ℝ → ℕ := fun t => ∑ i, if x i = t then m i + 1 else 0 with hZ
  have hZx : ∀ i, Z (x i) = m i + 1 := by
    intro i
    rw [hZ]
    simp only
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [ite_eq_right fun h => hj (hx h)]
    · simp
  refine exists_eq_zero_mult_aux (N + 1) (fun j => iteratedDeriv j g) hstep s Z ?_ ?_ ?_ ?_
  · rintro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    rw [hZx]
    omega
  · rintro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    exact hmem i
  · rintro t ht j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
    rw [hZx] at hj
    exact hzero i j (by omega)
  · rw [hs, Finset.sum_image fun i _ j _ h => hx h]
    simpa only [hZx] using hsum

/-! ### The nodal polynomial -/

section Nodal

variable {n : ℕ}

/-- The **nodal polynomial** of nodes `x` with multiplicities `m`: the monic polynomial
`∏ i, (X - x i) ^ (m i + 1)`, of degree `∑ i, (m i + 1)`. It vanishes at `x i` together with its
first `m i` derivatives, and it carries the error of Hermite interpolation. -/
noncomputable def nodal (x : Fin n → ℝ) (m : Fin n → ℕ) : ℝ[X] :=
  ∏ i, (Polynomial.X - Polynomial.C (x i)) ^ (m i + 1)

/-- The nodal polynomial is monic. -/
theorem monic_nodal (x : Fin n → ℝ) (m : Fin n → ℕ) : (nodal x m).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => (Polynomial.monic_X_sub_C (x i)).pow _

/-- The nodal polynomial has degree the total number of interpolation conditions. -/
theorem natDegree_nodal (x : Fin n → ℝ) (m : Fin n → ℕ) :
    (nodal x m).natDegree = ∑ i, (m i + 1) := by
  rw [nodal, Polynomial.natDegree_prod _ _ fun i _ =>
    ((Polynomial.monic_X_sub_C (x i)).pow _).ne_zero]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

/-- The value of the nodal polynomial, as the product it is defined by. -/
@[simp]
theorem eval_nodal (x : Fin n → ℝ) (m : Fin n → ℕ) (t : ℝ) :
    (nodal x m).eval t = ∏ i, (t - x i) ^ (m i + 1) := by
  simp [nodal, Polynomial.eval_prod]

/-- Each linear factor divides the nodal polynomial to its full multiplicity. -/
theorem pow_dvd_nodal (x : Fin n → ℝ) (m : Fin n → ℕ) (i : Fin n) :
    (Polynomial.X - Polynomial.C (x i)) ^ (m i + 1) ∣ nodal x m :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- The nodal polynomial vanishes at each node together with its first `m i` derivatives. -/
theorem eval_iterate_derivative_nodal {x : Fin n → ℝ} {m : Fin n → ℕ} (i : Fin n) {j : ℕ}
    (hj : j ≤ m i) : (Polynomial.derivative^[j] (nodal x m)).eval (x i) = 0 := by
  have hdvd : (Polynomial.X - Polynomial.C (x i)) ^ (m i + 1 - j) ∣
      Polynomial.derivative^[j] (nodal x m) :=
    Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd j (pow_dvd_nodal x m i)
  have hone : (Polynomial.X - Polynomial.C (x i)) ∣ Polynomial.derivative^[j] (nodal x m) :=
    (dvd_pow_self _ (by omega)).trans hdvd
  exact Polynomial.dvd_iff_isRoot.mp hone

/-- The top iterated derivative of a monic polynomial is the factorial of its degree. -/
private theorem iterate_derivative_of_monic {P : ℝ[X]} (hP : P.Monic) :
    Polynomial.derivative^[P.natDegree] P = Polynomial.C (P.natDegree.factorial : ℝ) := by
  have hle : (Polynomial.derivative^[P.natDegree] P).natDegree = 0 :=
    Nat.le_zero.mp (by simpa using Polynomial.natDegree_iterate_derivative P P.natDegree)
  have h0 : (Polynomial.derivative^[P.natDegree] P).coeff 0 = (P.natDegree.factorial : ℝ) := by
    rw [Polynomial.coeff_iterate_derivative]
    simp [hP.coeff_natDegree, Nat.descFactorial_self]
  calc Polynomial.derivative^[P.natDegree] P
      = Polynomial.C ((Polynomial.derivative^[P.natDegree] P).coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hle
    _ = Polynomial.C ((P.natDegree.factorial : ℝ)) := by rw [h0]

/-- The top iterated derivative of the nodal polynomial is `(∑ i, (m i + 1))!`. -/
theorem iterate_derivative_nodal (x : Fin n → ℝ) (m : Fin n → ℕ) {M : ℕ}
    (hM : ∑ i, (m i + 1) = M) :
    Polynomial.derivative^[M] (nodal x m) = Polynomial.C ((M.factorial : ℝ)) := by
  have hdeg : (nodal x m).natDegree = M := (natDegree_nodal x m).trans hM
  simpa [hdeg] using iterate_derivative_of_monic (monic_nodal x m)

end Nodal

/-! ### Unique solvability of the Hermite problem -/

section Unisolvent

variable {n : ℕ}

/-- **A polynomial of degree less than `∑ (m i + 1)` vanishing to order `m i + 1` at each node
is zero.** This is the injectivity half of unisolvence: the nodal polynomial would divide it,
and the nodal polynomial has degree `∑ (m i + 1)`. -/
theorem eq_zero_of_forall_eval_iterate_derivative_eq_zero {M : ℕ} {x : Fin n → ℝ}
    (hx : Function.Injective x) {m : Fin n → ℕ} (hM : ∑ i, (m i + 1) = M) {p : ℝ[X]}
    (hdeg : p.degree < (M : WithBot ℕ))
    (hzero : ∀ i, ∀ j ≤ m i, (Polynomial.derivative^[j] p).eval (x i) = 0) : p = 0 := by
  by_contra hp0
  have hdvd : nodal x m ∣ p := by
    rw [nodal]
    refine Fintype.prod_dvd_of_coprime (fun i j hij => ?_) fun i => ?_
    · exact ((Polynomial.pairwise_coprime_X_sub_C hx) hij).pow
    · exact (Polynomial.le_rootMultiplicity_iff hp0).mp
        (Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hp0 fun j hj => hzero i j hj)
  have hnodal : (nodal x m).degree = (M : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (monic_nodal x m).ne_zero, natDegree_nodal, hM]
  exact absurd (hnodal ▸ Polynomial.degree_le_of_dvd hdvd hp0) (not_le.mpr hdeg)

/-- The Hermite data of a polynomial of degree less than `M`: the values at `x i` of its
derivatives of order `j ≤ m i`, as a linear map. -/
private noncomputable def dataMap (x : Fin n → ℝ) (m : Fin n → ℕ) (M : ℕ) :
    Polynomial.degreeLT ℝ M →ₗ[ℝ] ((i : Fin n) × Fin (m i + 1)) → ℝ where
  toFun p k := (Polynomial.derivative^[(k.2 : ℕ)] (p : ℝ[X])).eval (x k.1)
  map_add' p q := by
    funext k
    simp
  map_smul' c p := by
    funext k
    simp [Polynomial.iterate_derivative_smul]

private theorem dataMap_bijective {M : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x)
    {m : Fin n → ℕ} (hM : ∑ i, (m i + 1) = M) : Function.Bijective (dataMap x m M) := by
  have hinj : Function.Injective (dataMap x m M) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    refine Subtype.ext (eq_zero_of_forall_eval_iterate_derivative_eq_zero hx hM
      (Polynomial.mem_degreeLT.mp p.2) fun i j hj => ?_)
    exact congrFun hp ⟨i, ⟨j, by omega⟩⟩
  have hdim : Module.finrank ℝ (Polynomial.degreeLT ℝ M)
      = Module.finrank ℝ (((i : Fin n) × Fin (m i + 1)) → ℝ) := by
    rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℝ M),
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_sigma]
    simpa using hM.symm
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

/-- **Unisolvence of the Hermite interpolation problem**: for distinct nodes `x i` with
multiplicities `m i` summing to `M`, and prescribed values `y i j`, there is exactly one
polynomial of degree less than `M` whose `j`-th derivative takes the value `y i j` at `x i` for
every `j ≤ m i`.

Injectivity is `eq_zero_of_forall_eval_iterate_derivative_eq_zero`; existence is then the
equality of dimensions of the polynomials of degree less than `M` and of the data.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, §3.2.2 and (3.2.6). -/
theorem isUnisolvent {M : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) {m : Fin n → ℕ}
    (hM : ∑ i, (m i + 1) = M) (y : Fin n → ℕ → ℝ) :
    ∃! p : ℝ[X], p.degree < (M : WithBot ℕ) ∧
      ∀ i, ∀ j ≤ m i, (Polynomial.derivative^[j] p).eval (x i) = y i j := by
  obtain ⟨q, hq⟩ := (dataMap_bijective hx hM).2 fun k => y k.1 k.2
  refine ⟨(q : ℝ[X]), ⟨Polynomial.mem_degreeLT.mp q.2, fun i j hj => ?_⟩, ?_⟩
  · exact congrFun hq ⟨i, ⟨j, by omega⟩⟩
  · rintro p ⟨hpdeg, hpval⟩
    have hqval : ∀ i, ∀ j ≤ m i, (Polynomial.derivative^[j] (q : ℝ[X])).eval (x i) = y i j :=
      fun i j hj => congrFun hq ⟨i, ⟨j, by omega⟩⟩
    have hsub : p - (q : ℝ[X]) = 0 := by
      refine eq_zero_of_forall_eval_iterate_derivative_eq_zero hx hM
        (lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
          (max_lt hpdeg (Polynomial.mem_degreeLT.mp q.2))) fun i j hj => ?_
      rw [Polynomial.iterate_derivative_sub, Polynomial.eval_sub, hpval i j hj, hqval i j hj]
      simp
    exact sub_eq_zero.mp hsub

end Unisolvent

/-! ### The Hermite interpolant -/

section Interpolate

variable {n : ℕ} {x : Fin n → ℝ} {m : Fin n → ℕ} {f : ℝ → ℝ}

open scoped Classical in
/-- **The Hermite interpolant** of `f` at the nodes `x` with multiplicities `m`: the unique
polynomial of degree less than `∑ i, (m i + 1)` whose derivatives of order `j ≤ m i` agree at
`x i` with those of `f`. For `m = 0` it is `Lagrange.interpolate`
(`Hermite.interpolate_zero_eq_lagrange`).

It is junk (namely `0`) when the nodes are not distinct, in which case the interpolation problem
is not solvable in general.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, §3.2.2. -/
noncomputable def interpolate (x : Fin n → ℝ) (m : Fin n → ℕ) (f : ℝ → ℝ) : ℝ[X] :=
  if h : Function.Injective x then
    (isUnisolvent h (M := ∑ i, (m i + 1)) rfl fun i j => iteratedDeriv j f (x i)).choose
  else 0

private theorem interpolate_spec (hx : Function.Injective x) (m : Fin n → ℕ) (f : ℝ → ℝ) :
    (interpolate x m f).degree < ((∑ i, (m i + 1) : ℕ) : WithBot ℕ) ∧
      ∀ i, ∀ j ≤ m i,
        (Polynomial.derivative^[j] (interpolate x m f)).eval (x i) = iteratedDeriv j f (x i) := by
  classical
  rw [interpolate, dite_eq_left hx]
  exact (isUnisolvent hx (M := ∑ i, (m i + 1)) rfl fun i j => iteratedDeriv j f (x i)).choose_spec.1

/-- The Hermite interpolant has degree less than the number of interpolation conditions. -/
theorem degree_interpolate_lt (hx : Function.Injective x) (m : Fin n → ℕ) (f : ℝ → ℝ) :
    (interpolate x m f).degree < ((∑ i, (m i + 1) : ℕ) : WithBot ℕ) :=
  (interpolate_spec hx m f).1

/-- The Hermite interpolant matches `f` and its first `m i` derivatives at the node `x i`. -/
theorem eval_iterate_derivative_interpolate (hx : Function.Injective x) (i : Fin n) {j : ℕ}
    (hj : j ≤ m i) :
    (Polynomial.derivative^[j] (interpolate x m f)).eval (x i) = iteratedDeriv j f (x i) :=
  (interpolate_spec hx m f).2 i j hj

/-- The Hermite interpolant is the only polynomial of degree less than `∑ (m i + 1)` matching
`f` and its derivatives at the nodes. -/
theorem eq_interpolate (hx : Function.Injective x) {p : ℝ[X]}
    (hdeg : p.degree < ((∑ i, (m i + 1) : ℕ) : WithBot ℕ))
    (hval : ∀ i, ∀ j ≤ m i,
      (Polynomial.derivative^[j] p).eval (x i) = iteratedDeriv j f (x i)) :
    p = interpolate x m f := by
  have h := isUnisolvent hx (M := ∑ i, (m i + 1)) rfl fun i j => iteratedDeriv j f (x i)
  exact (h.unique ⟨hdeg, hval⟩ ⟨degree_interpolate_lt hx m f,
    fun i j hj => eval_iterate_derivative_interpolate hx i hj⟩)

/-- **At simple nodes the Hermite interpolant is the Lagrange interpolant.** -/
theorem interpolate_zero_eq_lagrange (hx : Function.Injective x) (f : ℝ → ℝ) :
    interpolate x (fun _ => 0) f = Lagrange.interpolate Finset.univ x fun i => f (x i) := by
  classical
  refine (eq_interpolate hx ?_ ?_).symm
  · have hdeg : (Lagrange.interpolate Finset.univ x fun i => f (x i)).degree
        < (((Finset.univ : Finset (Fin n)).card : ℕ) : WithBot ℕ) :=
      Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin n)))
        (r := fun i => f (x i)) hx.injOn
    simpa using hdeg
  · intro i j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    simpa using Lagrange.eval_interpolate_at_node _ hx.injOn (Finset.mem_univ i)

end Interpolate

/-! ### The interpolation error -/

/-- **The Hermite interpolation error formula.** For `f` of class `C^{N+1}` on `[a, b]`, distinct
nodes `x i` in `[a, b]` with multiplicities `m i` summing to `N + 1`, and any `t ∈ [a, b]`, the
error of the Hermite interpolant at `t` is `f^{(N+1)}(ξ)/(N+1)!` times the nodal polynomial
`∏ i, (t - x i)^{m i + 1}`, for some `ξ ∈ [a, b]`.

As in the Lagrange case the proof subtracts a multiple of the nodal polynomial chosen so that the
auxiliary function vanishes at `t` as well; its zeros then number `N + 2` with multiplicity, and
`Hermite.exists_iteratedDeriv_eq_zero` applies.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, §3.2.2; Kress, *Numerical Analysis*,
§8.1. -/
theorem exists_sub_interpolate_eq {N n : ℕ} {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) f) {x : Fin n → ℝ}
    (hx : Function.Injective x) (hxmem : ∀ i, x i ∈ Set.Icc a b) {m : Fin n → ℕ}
    (hsum : ∑ i, (m i + 1) = N + 1) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Icc a b, f t - (interpolate x m f).eval t
      = iteratedDeriv (N + 1) f ξ / (N + 1).factorial * ∏ i, (t - x i) ^ (m i + 1) := by
  classical
  set p : ℝ[X] := interpolate x m f with hp
  by_cases hcase : ∃ i, t = x i
  · -- at a node both sides vanish
    obtain ⟨i, rfl⟩ := hcase
    refine ⟨x i, hxmem i, ?_⟩
    have h0 := eval_iterate_derivative_interpolate (f := f) hx i (Nat.zero_le (m i))
    simp only [Function.iterate_zero, id_eq, iteratedDeriv_zero] at h0
    rw [hp, h0, sub_self,
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [sub_self]; exact zero_pow (by omega)),
      mul_zero]
  · push Not at hcase
    set W : ℝ[X] := nodal x m with hW
    have hWt : W.eval t ≠ 0 := by
      rw [hW, eval_nodal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (sub_ne_zero.mpr (hcase i))
    set c : ℝ := (f t - p.eval t) / W.eval t with hc
    set Q : ℝ[X] := p + Polynomial.C c * W with hQ
    have hQder : ∀ j : ℕ, Polynomial.derivative^[j] Q
        = Polynomial.derivative^[j] p + Polynomial.C c * Polynomial.derivative^[j] W := fun j => by
      rw [hQ, Polynomial.iterate_derivative_add, Polynomial.iterate_derivative_C_mul]
    -- the auxiliary function and its zeros, counted with multiplicity
    have hQdiff : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) fun u => Q.eval u := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        Q.contDiff_aeval (𝕜 := ℝ) ((N + 1 : ℕ) : WithTop ℕ∞)
    have hgdiff : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) fun u => f u - Q.eval u := hf.sub hQdiff
    have hgder : ∀ j ≤ N + 1, ∀ u : ℝ, iteratedDeriv j (fun u => f u - Q.eval u) u
        = iteratedDeriv j f u - (Polynomial.derivative^[j] Q).eval u := by
      intro j hj u
      have hjle : ((j : ℕ) : WithTop ℕ∞) ≤ ((N + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj
      rw [iteratedDeriv_fun_sub (hf.of_le hjle).contDiffAt (hQdiff.of_le hjle).contDiffAt,
        Polynomial.iteratedDeriv_eval]
    have hmle : ∀ i, m i ≤ N := by
      intro i
      have := Finset.single_le_sum (f := fun i => m i + 1) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ i)
      omega
    have hzeronode : ∀ i, ∀ j ≤ m i, iteratedDeriv j (fun u => f u - Q.eval u) (x i) = 0 := by
      intro i j hj
      rw [hgder j (by have := hmle i; omega), hQder, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, eval_iterate_derivative_interpolate hx i hj, hW,
        eval_iterate_derivative_nodal i hj]
      ring
    have hzerot : (fun u => f u - Q.eval u) t = 0 := by
      simp only [hQ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hc]
      field_simp
      ring
    -- Rolle with multiplicities on the nodes together with `t`
    have hxc : Function.Injective (Fin.cons t x : Fin (n + 1) → ℝ) :=
      Fin.cons_injective_iff.mpr ⟨by rintro ⟨i, hi⟩; exact hcase i hi.symm, hx⟩
    have hsum' : ∑ i, ((Fin.cons 0 m : Fin (n + 1) → ℕ) i + 1) = N + 2 := by
      have : ∀ i : Fin (n + 1), (Fin.cons 0 m : Fin (n + 1) → ℕ) i + 1
          = (Fin.cons 1 (fun i => m i + 1) : Fin (n + 1) → ℕ) i := by
        refine Fin.cases ?_ ?_ <;> simp
      rw [Finset.sum_congr rfl fun i _ => this i, Fin.sum_cons, hsum]
      omega
    have hmem' : ∀ i : Fin (n + 1), (Fin.cons t x : Fin (n + 1) → ℝ) i ∈ Set.Icc a b := by
      refine Fin.cases ?_ fun i => ?_
      · simpa using ht
      · simpa using hxmem i
    have hzero' : ∀ i : Fin (n + 1), ∀ j ≤ (Fin.cons 0 m : Fin (n + 1) → ℕ) i,
        iteratedDeriv j (fun u => f u - Q.eval u) ((Fin.cons t x : Fin (n + 1) → ℝ) i) = 0 := by
      refine Fin.cases ?_ fun i j hj => ?_
      · intro j hj
        have hj0 : j = 0 := Nat.le_zero.mp (by simpa using hj)
        subst hj0
        simpa using hzerot
      · simpa using hzeronode i j (by simpa using hj)
    obtain ⟨ξ, hξ, hξ0⟩ := exists_iteratedDeriv_eq_zero (N := N) hgdiff hxc hmem' hsum' hzero'
    -- compute the top derivative of the auxiliary function
    refine ⟨ξ, hξ, ?_⟩
    have hpder : Polynomial.derivative^[N + 1] p = 0 :=
      Polynomial.iterate_derivative_eq_zero_of_degree_lt
        (by simpa [hsum] using degree_interpolate_lt hx m f)
    have hWder : Polynomial.derivative^[N + 1] W = Polynomial.C (((N + 1).factorial : ℝ)) :=
      iterate_derivative_nodal x m hsum
    rw [hgder (N + 1) le_rfl, hQder, hpder, hWder] at hξ0
    simp only [Polynomial.eval_mul, Polynomial.eval_C, zero_add] at hξ0
    have hfact : (((N + 1).factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hceq : c = iteratedDeriv (N + 1) f ξ / (N + 1).factorial := by
      field_simp
      linarith [hξ0]
    have hres : f t - p.eval t = c * W.eval t := by
      rw [hc]
      field_simp
    rw [hres, hceq, hW, eval_nodal]

end Hermite
