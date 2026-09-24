import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Hermite interpolation on a multiset of nodes

The algebraic half of Hermite interpolation, over any field: a polynomial interpolates *jets*
(finitely many Taylor coefficients) at a multiset of nodes, each node carrying as many
coefficients as its multiplicity. This is the companion of Mathlib's `Lagrange` interpolation
(`Mathlib/LinearAlgebra/Lagrange`), which is the case of a multiset without repetitions.

## Main definitions

* `Hermite.jetPoly y x m = ∑_{j < m} y j (X - x)ʲ`: the Taylor polynomial at `x` of a jet
  `y : ℕ → R`, truncated at order `m`.
* `Hermite.nodalMultiset s = ∏_{x ∈ s} (X - x)`: the nodal polynomial of a multiset of nodes, monic
  of degree `card s`.
* `Hermite.IsJetInterpolant s y p`: `p` interpolates the jets `y x` at the nodes of `s`, to the
  multiplicity of each node: `(X - x)^{count x s} ∣ p - jetPoly (y x) x (count x s)`. The
  divisibility form needs no characteristic assumption; it says that the first `count x s` Taylor
  coefficients of `p` at `x` are `y x 0, y x 1, …` (`Hermite.isJetInterpolant_iff_coeff_taylor`).
* `Hermite.interpolateJet s y`: the unique interpolant of degree `< card s`.

## Main results

* `Hermite.existsUnique_isJetInterpolant`: unisolvence. Existence is the Chinese remainder theorem
  in the Dedekind domain `K[X]`, followed by reduction modulo the nodal polynomial; uniqueness holds
  because the difference of two interpolants is divisible by the nodal polynomial
  (`Hermite.IsJetInterpolant.nodalMultiset_dvd_sub`).
* `Hermite.IsJetInterpolant.of_le`: restriction to a sub-multiset of nodes.
* `Hermite.interpolateJet_congr`, `Hermite.interpolateJet_add`, `Hermite.interpolateJet_smul`: the
  interpolant depends only on the jets it uses, and linearly on them.
* `Hermite.interpolateJet_cons_sub`: the Newton step — adding a node adds a multiple of the nodal
  polynomial of the old nodes, the multiple being the new leading coefficient.

## Implementation notes

The consumers are the jets and divided differences of functions of
`Numlib/Analysis/Calculus/HermiteInterpolation` (`Hermite.taylorJet`, `Hermite.divDiff`), the
primary functional calculus of `Numlib/Analysis/Normed/Algebra/PrimaryFunctionalCalculus`, and the
real Hermite interpolation of `Numlib/Approximation/Hermite`. Upstreaming candidate: natural home
`Mathlib/LinearAlgebra/Lagrange` or a sibling file (Mathlib's `Polynomial.hermite` is the unrelated
probabilists' Hermite polynomial, so the namespace would need renaming there).
-/

open Polynomial

namespace Hermite

section CommRing

variable {R : Type*} [CommRing R]

/-! ### Jets and their Taylor polynomials -/

/-- The Taylor polynomial `∑_{j < m} y j (X - x)ʲ` at `x` of a jet `y : ℕ → R`, truncated at
order `m`. -/
noncomputable def jetPoly (y : ℕ → R) (x : R) (m : ℕ) : R[X] :=
  ∑ j ∈ Finset.range m, C (y j) * (X - C x) ^ j

@[simp]
theorem jetPoly_zero (y : ℕ → R) (x : R) : jetPoly y x 0 = 0 := by
  simp [jetPoly]

theorem jetPoly_succ (y : ℕ → R) (x : R) (m : ℕ) :
    jetPoly y x (m + 1) = jetPoly y x m + C (y m) * (X - C x) ^ m :=
  Finset.sum_range_succ _ _

/-- Seen from `x`, the Taylor polynomial of a jet has the jet as its coefficients. -/
theorem taylor_jetPoly (y : ℕ → R) (x : R) (m : ℕ) :
    taylor x (jetPoly y x m) = ∑ j ∈ Finset.range m, C (y j) * X ^ j := by
  simp [jetPoly, map_sum, taylor_mul, taylor_pow, taylor_X, taylor_C]

theorem coeff_taylor_jetPoly (y : ℕ → R) (x : R) (m j : ℕ) :
    (taylor x (jetPoly y x m)).coeff j = if j < m then y j else 0 := by
  rw [taylor_jetPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  simp [Finset.sum_ite_eq, Finset.mem_range]

/-- The Taylor polynomial depends only on the first `m` entries of the jet. -/
theorem jetPoly_congr {y y' : ℕ → R} {x : R} {m : ℕ} (h : ∀ j < m, y j = y' j) :
    jetPoly y x m = jetPoly y' x m :=
  Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]

theorem jetPoly_add (y y' : ℕ → R) (x : R) (m : ℕ) :
    jetPoly (y + y') x m = jetPoly y x m + jetPoly y' x m := by
  simp [jetPoly, add_mul, Finset.sum_add_distrib]

theorem jetPoly_smul (c : R) (y : ℕ → R) (x : R) (m : ℕ) :
    jetPoly (c • y) x m = c • jetPoly y x m := by
  simp [jetPoly, Finset.smul_sum, smul_eq_C_mul, mul_assoc]

/-- Truncations of one Taylor polynomial at two orders `m ≤ n` agree to order `m`. -/
theorem pow_dvd_jetPoly_sub_jetPoly (y : ℕ → R) (x : R) {m n : ℕ} (h : m ≤ n) :
    (X - C x) ^ m ∣ jetPoly y x n - jetPoly y x m := by
  rw [jetPoly, jetPoly, ← Finset.sum_range_add_sum_Ico _ h, add_sub_cancel_left]
  exact Finset.dvd_sum fun j hj =>
    (pow_dvd_pow _ (Finset.mem_Ico.mp hj).1).mul_left _

/-- `(X - x)^m` divides `q` exactly when the first `m` Taylor coefficients of `q` at `x`
vanish. -/
theorem pow_X_sub_C_dvd_iff {x : R} {m : ℕ} {q : R[X]} :
    (X - C x) ^ m ∣ q ↔ ∀ j < m, (taylor x q).coeff j = 0 := by
  have h : taylor x ((X - C x) ^ m) = X ^ m := by simp [taylor_pow, taylor_X]
  rw [← map_dvd_iff (taylorEquiv x)]
  change taylor x _ ∣ taylor x q ↔ _
  rw [h, X_pow_dvd_iff]

/-- The Taylor polynomial of a jet truncated at order `m` has degree less than `m`. -/
theorem degree_jetPoly_lt (y : ℕ → R) (x : R) (m : ℕ) : (jetPoly y x m).degree < m := by
  rw [← degree_taylor _ x, taylor_jetPoly, ← mem_degreeLT]
  exact Submodule.sum_mem _ fun j hj => mem_degreeLT.mpr
    ((degree_C_mul_X_pow_le j _).trans_lt (by exact_mod_cast Finset.mem_range.mp hj))

/-- The top coefficient of a truncated Taylor polynomial is the last entry of the jet used. -/
theorem coeff_jetPoly_succ_self [Nontrivial R] (y : ℕ → R) (x : R) (m : ℕ) :
    (jetPoly y x (m + 1)).coeff m = y m := by
  have h1 : (jetPoly y x m).coeff m = 0 := coeff_eq_zero_of_degree_lt (degree_jetPoly_lt y x m)
  have hd : ((X - C x) ^ m).natDegree = m := by
    rw [(monic_X_sub_C x).natDegree_pow, natDegree_X_sub_C, mul_one]
  have h2 : ((X - C x) ^ m).coeff m = 1 := by
    have := ((monic_X_sub_C x).pow m).coeff_natDegree
    rwa [hd] at this
  rw [jetPoly_succ, coeff_add, h1, coeff_C_mul, h2, zero_add, mul_one]

/-! ### The nodal polynomial of a multiset -/

/-- The **nodal polynomial** `∏_{x ∈ s} (X - x)` of a multiset of nodes, each node counted with
its multiplicity. -/
noncomputable def nodalMultiset (s : Multiset R) : R[X] :=
  (s.map fun x => X - C x).prod

@[simp]
theorem nodalMultiset_zero : nodalMultiset (0 : Multiset R) = 1 := by
  simp [nodalMultiset]

@[simp]
theorem nodalMultiset_cons (x : R) (s : Multiset R) :
    nodalMultiset (x ::ₘ s) = (X - C x) * nodalMultiset s := by
  simp [nodalMultiset]

theorem nodalMultiset_add (s t : Multiset R) :
    nodalMultiset (s + t) = nodalMultiset s * nodalMultiset t := by
  simp [nodalMultiset]

@[simp]
theorem nodalMultiset_singleton (x : R) : nodalMultiset {x} = X - C x := by
  simp [nodalMultiset]

theorem nodalMultiset_nsmul (k : ℕ) (s : Multiset R) :
    nodalMultiset (k • s) = nodalMultiset s ^ k := by
  simp [nodalMultiset, Multiset.map_nsmul, Multiset.prod_nsmul]

theorem nodalMultiset_sum {ι : Type*} (t : Finset ι) (s : ι → Multiset R) :
    nodalMultiset (∑ i ∈ t, s i) = ∏ i ∈ t, nodalMultiset (s i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, nodalMultiset_add, ih]

theorem monic_nodalMultiset (s : Multiset R) : (nodalMultiset s).Monic :=
  monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x

@[simp]
theorem natDegree_nodalMultiset [Nontrivial R] (s : Multiset R) :
    (nodalMultiset s).natDegree = Multiset.card s :=
  natDegree_multiset_prod_X_sub_C_eq_card s

theorem degree_nodalMultiset [Nontrivial R] (s : Multiset R) :
    (nodalMultiset s).degree = Multiset.card s := by
  rw [degree_eq_natDegree (monic_nodalMultiset s).ne_zero, natDegree_nodalMultiset]

theorem eval_nodalMultiset (s : Multiset R) (t : R) :
    (nodalMultiset s).eval t = (s.map fun x => t - x).prod := by
  simp [nodalMultiset, eval_multiset_prod, Multiset.map_map]

theorem nodalMultiset_dvd_nodalMultiset {s t : Multiset R} (h : s ≤ t) :
    nodalMultiset s ∣ nodalMultiset t := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp h
  rw [nodalMultiset_add]
  exact dvd_mul_right _ _

/-- The nodal polynomial grouped by distinct nodes. -/
theorem nodalMultiset_eq_prod_count [DecidableEq R] (s : Multiset R) :
    nodalMultiset s = ∏ x ∈ s.toFinset, (X - C x) ^ s.count x :=
  Finset.prod_multiset_map_count s _

theorem pow_count_dvd_nodalMultiset [DecidableEq R] (s : Multiset R) (x : R) :
    (X - C x) ^ s.count x ∣ nodalMultiset s := by
  by_cases hx : x ∈ s
  · rw [nodalMultiset_eq_prod_count]
    exact Finset.dvd_prod_of_mem _ (Multiset.mem_toFinset.mpr hx)
  · rw [Multiset.count_eq_zero_of_notMem hx, pow_zero]
    exact one_dvd _

/-! ### Jet interpolation -/

variable [DecidableEq R]

/-- `p` **interpolates the jets** `y x` at the nodes `x` of the multiset `s`, each to the
multiplicity of the node: `(X - x)^{count x s}` divides `p - jetPoly (y x) x (count x s)`. At a
multiset without repetitions this is Lagrange interpolation of the values `y x 0`. -/
def IsJetInterpolant (s : Multiset R) (y : R → ℕ → R) (p : R[X]) : Prop :=
  ∀ x ∈ s, (X - C x) ^ s.count x ∣ p - jetPoly (y x) x (s.count x)

/-- Jet interpolation prescribes the first `count x s` Taylor coefficients at each node `x`. -/
theorem isJetInterpolant_iff_coeff_taylor {s : Multiset R} {y : R → ℕ → R} {p : R[X]} :
    IsJetInterpolant s y p ↔ ∀ x ∈ s, ∀ j < s.count x, (taylor x p).coeff j = y x j := by
  refine forall₂_congr fun x _ => ?_
  rw [pow_X_sub_C_dvd_iff]
  refine forall₂_congr fun j hj => ?_
  rw [map_sub, coeff_sub, coeff_taylor_jetPoly, ite_eq_left hj, sub_eq_zero]

/-- Every polynomial interpolates its own Taylor coefficients. -/
theorem isJetInterpolant_coeff_taylor (s : Multiset R) (p : R[X]) :
    IsJetInterpolant s (fun x j => (taylor x p).coeff j) p :=
  isJetInterpolant_iff_coeff_taylor.mpr fun _ _ _ _ => rfl

/-- Interpolation uses only the jets up to the multiplicities. -/
theorem isJetInterpolant_congr {s : Multiset R} {y y' : R → ℕ → R}
    (h : ∀ x ∈ s, ∀ j < s.count x, y x j = y' x j) {p : R[X]} :
    IsJetInterpolant s y p ↔ IsJetInterpolant s y' p := by
  refine forall₂_congr fun x hx => ?_
  rw [jetPoly_congr (h x hx)]

theorem IsJetInterpolant.add {s : Multiset R} {y y' : R → ℕ → R} {p p' : R[X]}
    (hp : IsJetInterpolant s y p) (hp' : IsJetInterpolant s y' p') :
    IsJetInterpolant s (y + y') (p + p') := by
  intro x hx
  have h : p + p' - jetPoly ((y + y') x) x (s.count x)
      = (p - jetPoly (y x) x (s.count x)) + (p' - jetPoly (y' x) x (s.count x)) := by
    rw [Pi.add_apply, jetPoly_add]
    ring
  rw [h]
  exact dvd_add (hp x hx) (hp' x hx)

theorem IsJetInterpolant.smul {s : Multiset R} {y : R → ℕ → R} {p : R[X]}
    (hp : IsJetInterpolant s y p) (c : R) : IsJetInterpolant s (c • y) (c • p) := by
  intro x hx
  rw [Pi.smul_apply, jetPoly_smul, ← smul_sub, smul_eq_C_mul]
  exact (hp x hx).mul_left _

/-- The zero polynomial interpolates the zero jets. -/
theorem isJetInterpolant_zero (s : Multiset R) : IsJetInterpolant s 0 0 := by
  intro x _
  simp [jetPoly]

/-- **Products of interpolants** interpolate the Cauchy products of the jets. -/
theorem IsJetInterpolant.mul {s : Multiset R} {y z : R → ℕ → R} {p q : R[X]}
    (hp : IsJetInterpolant s y p) (hq : IsJetInterpolant s z q) :
    IsJetInterpolant s (fun x n => ∑ i ∈ Finset.range (n + 1), y x i * z x (n - i)) (p * q) := by
  rw [isJetInterpolant_iff_coeff_taylor] at hp hq ⊢
  intro x hx n hn
  rw [taylor_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (taylor x p).coeff i * (taylor x q).coeff j)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [hp x hx i (by omega), hq x hx (n - i) (by omega)]

/-- Finite sums of interpolants interpolate the sums of the jets. -/
theorem IsJetInterpolant.sum {ι : Type*} {s : Multiset R} (t : Finset ι) {y : ι → R → ℕ → R}
    {p : ι → R[X]} (h : ∀ i ∈ t, IsJetInterpolant s (y i) (p i)) :
    IsJetInterpolant s (∑ i ∈ t, y i) (∑ i ∈ t, p i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isJetInterpolant_zero s
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i t)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- **Restriction**: an interpolant on `t` interpolates on every sub-multiset `s ≤ t`. -/
theorem IsJetInterpolant.of_le {s t : Multiset R} {y : R → ℕ → R} {p : R[X]}
    (hp : IsJetInterpolant t y p) (hst : s ≤ t) : IsJetInterpolant s y p := by
  intro x hx
  have hc : s.count x ≤ t.count x := Multiset.count_le_of_le x hst
  have h : p - jetPoly (y x) x (s.count x)
      = (p - jetPoly (y x) x (t.count x))
        + (jetPoly (y x) x (t.count x) - jetPoly (y x) x (s.count x)) := by ring
  rw [h]
  exact dvd_add ((pow_dvd_pow _ hc).trans (hp x (Multiset.mem_of_le hst hx)))
    (pow_dvd_jetPoly_sub_jetPoly _ _ hc)

end CommRing

section Field

variable {K : Type*} [Field K]

/-- The nodal polynomial splits. -/
theorem splits_nodalMultiset (s : Multiset K) : (nodalMultiset s).Splits :=
  Splits.multisetProd fun _ hf => by
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hf
    exact Splits.X_sub_C x

@[simp]
theorem roots_nodalMultiset (s : Multiset K) : (nodalMultiset s).roots = s :=
  roots_multiset_prod_X_sub_C s

/-- A monic split polynomial is the nodal polynomial of its roots. -/
theorem eq_nodalMultiset_roots {p : K[X]} (hp : p.Monic) (hs : p.Splits) :
    p = nodalMultiset p.roots :=
  hs.eq_prod_roots_of_monic hp

variable [DecidableEq K]

/-- A polynomial is divisible by the nodal polynomial exactly when it is divisible by the power of
each linear factor. -/
theorem nodalMultiset_dvd_iff {s : Multiset K} {p : K[X]} :
    nodalMultiset s ∣ p ↔ ∀ x ∈ s, (X - C x) ^ s.count x ∣ p := by
  refine ⟨fun h x _ => (pow_count_dvd_nodalMultiset s x).trans h, fun h => ?_⟩
  rw [nodalMultiset_eq_prod_count]
  refine Finset.prod_dvd_of_coprime (fun x _ x' _ hxx' => ?_)
    fun x hx => h x (Multiset.mem_toFinset.mp hx)
  exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hxx').isUnit).pow

/-- **Two interpolants of the same jets differ by a multiple of the nodal polynomial.** -/
theorem IsJetInterpolant.nodalMultiset_dvd_sub {s : Multiset K} {y : K → ℕ → K} {p q : K[X]}
    (hp : IsJetInterpolant s y p) (hq : IsJetInterpolant s y q) : nodalMultiset s ∣ p - q := by
  refine nodalMultiset_dvd_iff.mpr fun x hx => ?_
  have h : p - q = (p - jetPoly (y x) x (s.count x)) - (q - jetPoly (y x) x (s.count x)) := by
    ring
  rw [h]
  exact dvd_sub (hp x hx) (hq x hx)

/-- A polynomial interpolates the zero jets exactly when the nodal polynomial divides it. -/
theorem isJetInterpolant_zero_iff {s : Multiset K} {p : K[X]} :
    IsJetInterpolant s 0 p ↔ nodalMultiset s ∣ p := by
  refine ⟨fun h => by simpa using h.nodalMultiset_dvd_sub (isJetInterpolant_zero s), fun h => ?_⟩
  intro x hx
  simpa [jetPoly] using (pow_count_dvd_nodalMultiset s x).trans h

/-- Changing an interpolant by a multiple of the nodal polynomial gives an interpolant. -/
theorem IsJetInterpolant.of_nodalMultiset_dvd_sub {s : Multiset K} {y : K → ℕ → K} {p q : K[X]}
    (hp : IsJetInterpolant s y p) (h : nodalMultiset s ∣ p - q) : IsJetInterpolant s y q := by
  intro x hx
  have e : q - jetPoly (y x) x (s.count x) = (p - jetPoly (y x) x (s.count x)) - (p - q) := by
    ring
  rw [e]
  exact dvd_sub (hp x hx) ((pow_count_dvd_nodalMultiset s x).trans h)

/-- Two polynomials interpolating the same jets agree modulo the nodal polynomial. -/
theorem IsJetInterpolant.modByMonic_eq {s : Multiset K} {y : K → ℕ → K} {p q : K[X]}
    (hp : IsJetInterpolant s y p) (hq : IsJetInterpolant s y q) :
    p %ₘ nodalMultiset s = q %ₘ nodalMultiset s :=
  modByMonic_eq_of_dvd_sub (monic_nodalMultiset s) (hp.nodalMultiset_dvd_sub hq)

/-- Reducing an interpolant modulo the nodal polynomial gives an interpolant. -/
theorem IsJetInterpolant.modByMonic {s : Multiset K} {y : K → ℕ → K} {p : K[X]}
    (hp : IsJetInterpolant s y p) : IsJetInterpolant s y (p %ₘ nodalMultiset s) :=
  hp.of_nodalMultiset_dvd_sub (by
    rw [← dvd_neg, neg_sub]
    exact dvd_modByMonic_sub p _)

/-- **An interpolant exists.** By the Chinese remainder theorem in the Dedekind domain `K[X]`,
applied to the pairwise distinct prime ideals `(X - x)` raised to the multiplicities. -/
theorem exists_isJetInterpolant (s : Multiset K) (y : K → ℕ → K) :
    ∃ p : K[X], IsJetInterpolant s y p := by
  obtain ⟨p, hp⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := s.toFinset) (fun x => Ideal.span {X - C x}) s.count
    (fun x _ => Ideal.prime_span_singleton_iff.mpr (prime_X_sub_C x))
    (fun x _ x' _ hxx' h => hxx' (by
      have := eq_of_monic_of_associated (monic_X_sub_C x) (monic_X_sub_C x')
        (Ideal.span_singleton_eq_span_singleton.mp h)
      simpa using congrArg (eval 0) this))
    (fun x => jetPoly (y x.1) x.1 (s.count x.1))
  refine ⟨p, fun x hx => ?_⟩
  have := hp x (Multiset.mem_toFinset.mpr hx)
  rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this

/-- **Unisolvence of Hermite interpolation on a multiset**: exactly one polynomial of degree less
than `card s` interpolates given jets at the nodes of `s`. -/
theorem existsUnique_isJetInterpolant (s : Multiset K) (y : K → ℕ → K) :
    ∃! p : K[X], p.degree < Multiset.card s ∧ IsJetInterpolant s y p := by
  obtain ⟨p, hp⟩ := exists_isJetInterpolant s y
  refine ⟨p %ₘ nodalMultiset s, ⟨?_, hp.modByMonic⟩, fun q ⟨hqdeg, hq⟩ => ?_⟩
  · rw [← degree_nodalMultiset]
    exact degree_modByMonic_lt _ (monic_nodalMultiset s)
  · rw [hq.modByMonic_eq hp |>.symm, (modByMonic_eq_self_iff (monic_nodalMultiset s)).mpr]
    rwa [degree_nodalMultiset]

/-- **The Hermite interpolant** of the jets `y` on the multiset of nodes `s`: the unique polynomial
of degree less than `card s` interpolating them (`Hermite.existsUnique_isJetInterpolant`). -/
noncomputable def interpolateJet (s : Multiset K) (y : K → ℕ → K) : K[X] :=
  (existsUnique_isJetInterpolant s y).exists.choose

theorem degree_interpolateJet_lt (s : Multiset K) (y : K → ℕ → K) :
    (interpolateJet s y).degree < Multiset.card s :=
  (existsUnique_isJetInterpolant s y).exists.choose_spec.1

/-- The Hermite interpolant interpolates. -/
theorem isJetInterpolant_interpolateJet (s : Multiset K) (y : K → ℕ → K) :
    IsJetInterpolant s y (interpolateJet s y) :=
  (existsUnique_isJetInterpolant s y).exists.choose_spec.2

/-- Uniqueness: every interpolant of degree `< card s` is the Hermite interpolant. -/
theorem eq_interpolateJet {s : Multiset K} {y : K → ℕ → K} {p : K[X]}
    (hdeg : p.degree < Multiset.card s) (hp : IsJetInterpolant s y p) :
    p = interpolateJet s y :=
  (existsUnique_isJetInterpolant s y).unique ⟨hdeg, hp⟩
    ⟨degree_interpolateJet_lt s y, isJetInterpolant_interpolateJet s y⟩

/-- Any interpolant reduces modulo the nodal polynomial to the Hermite interpolant. -/
theorem IsJetInterpolant.modByMonic_eq_interpolateJet {s : Multiset K} {y : K → ℕ → K}
    {p : K[X]} (hp : IsJetInterpolant s y p) : p %ₘ nodalMultiset s = interpolateJet s y := by
  refine eq_interpolateJet ?_ hp.modByMonic
  rw [← degree_nodalMultiset]
  exact degree_modByMonic_lt _ (monic_nodalMultiset s)

/-- The Hermite interpolant of the Taylor coefficients of a polynomial is its remainder modulo the
nodal polynomial. -/
theorem interpolateJet_coeff_taylor (s : Multiset K) (p : K[X]) :
    interpolateJet s (fun x j => (taylor x p).coeff j) = p %ₘ nodalMultiset s :=
  (isJetInterpolant_coeff_taylor s p).modByMonic_eq_interpolateJet.symm

/-- The Hermite interpolant depends only on the jets it uses. -/
theorem interpolateJet_congr {s : Multiset K} {y y' : K → ℕ → K}
    (h : ∀ x ∈ s, ∀ j < s.count x, y x j = y' x j) :
    interpolateJet s y = interpolateJet s y' :=
  eq_interpolateJet (degree_interpolateJet_lt s y)
    ((isJetInterpolant_congr h).mp (isJetInterpolant_interpolateJet s y))

theorem interpolateJet_add (s : Multiset K) (y y' : K → ℕ → K) :
    interpolateJet s (y + y') = interpolateJet s y + interpolateJet s y' :=
  (eq_interpolateJet ((degree_add_le _ _).trans_lt
      (max_lt (degree_interpolateJet_lt s y) (degree_interpolateJet_lt s y')))
    ((isJetInterpolant_interpolateJet s y).add (isJetInterpolant_interpolateJet s y'))).symm

theorem interpolateJet_smul (s : Multiset K) (c : K) (y : K → ℕ → K) :
    interpolateJet s (c • y) = c • interpolateJet s y :=
  (eq_interpolateJet ((degree_smul_le _ _).trans_lt (degree_interpolateJet_lt s y))
    ((isJetInterpolant_interpolateJet s y).smul c)).symm

@[simp]
theorem interpolateJet_zero (y : K → ℕ → K) : interpolateJet 0 y = 0 := by
  have h := degree_interpolateJet_lt 0 y
  rw [Multiset.card_zero, Nat.cast_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot] at h
  exact h

/-- **The Newton step**: adding a node `x` to `s` adds to the interpolant a multiple of the nodal
polynomial of `s`, the multiple being the leading coefficient `[X^{card s}]` of the new
interpolant. -/
theorem interpolateJet_cons_sub (x : K) (s : Multiset K) (y : K → ℕ → K) :
    interpolateJet (x ::ₘ s) y - interpolateJet s y
      = C ((interpolateJet (x ::ₘ s) y).coeff (Multiset.card s)) * nodalMultiset s := by
  set P := interpolateJet (x ::ₘ s) y
  set I := interpolateJet s y
  obtain ⟨q, hq⟩ : nodalMultiset s ∣ P - I :=
    ((isJetInterpolant_interpolateJet _ y).of_le (Multiset.le_cons_self s x)).nodalMultiset_dvd_sub
      (isJetInterpolant_interpolateJet s y)
  have hIdeg : I.degree < Multiset.card s := degree_interpolateJet_lt s y
  have hPdeg : P.natDegree ≤ Multiset.card s := by
    have := degree_interpolateJet_lt (x ::ₘ s) y
    rw [Multiset.card_cons] at this
    exact natDegree_le_iff_coeff_eq_zero.mpr fun N hN =>
      (degree_lt_iff_coeff_zero _ _).mp this N (by omega)
  have hIcoeff : I.coeff (Multiset.card s) = 0 := coeff_eq_zero_of_degree_lt hIdeg
  have hqC : q = C (q.coeff 0) := by
    by_cases hq0 : q = 0
    · simp [hq0]
    refine eq_C_of_natDegree_eq_zero ?_
    have h1 : (P - I).natDegree ≤ Multiset.card s :=
      (natDegree_sub_le _ _).trans (max_le hPdeg (natDegree_le_of_degree_le hIdeg.le))
    rw [hq, (monic_nodalMultiset s).natDegree_mul' hq0, natDegree_nodalMultiset] at h1
    omega
  have hc : P.coeff (Multiset.card s) = q.coeff 0 := by
    have h := congrArg (coeff · (Multiset.card s)) hq
    simp only [coeff_sub, hIcoeff, sub_zero] at h
    rw [h, hqC, coeff_mul_C, coeff_C_zero, ← natDegree_nodalMultiset s,
      (monic_nodalMultiset s).coeff_natDegree, one_mul]
  rw [hq, hc, ← hqC, mul_comm]

end Field

end Hermite
