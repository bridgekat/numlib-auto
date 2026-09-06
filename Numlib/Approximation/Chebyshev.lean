import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Approximation.BestApprox

/-!
# Best uniform approximation and equioscillation

Best uniform approximation of a continuous function on a compact subset of the line by polynomials
of degree at most `n`, and the alternation (equioscillation) that characterizes it. The material is
[han2009theoretical] Thm 3.3.19 and [kress1998numerical] §8.2.

## Main definitions

* `polyLE X n` is the subspace of `C(X, ℝ)` of the restrictions of the real polynomials of degree at
  most `n`.
* `HaarCondition V d` says that no nonzero element of `V` vanishes at `d` distinct points of `X`. It
  is what the alternation arguments use about polynomials, and it holds for `polyLE X n` with `d = n
  + 1` (`haarCondition_polyLE`), as it does for the trigonometric polynomials of degree at most `n`
  on a circle. The dimension is carried as a parameter rather than read off as `Module.finrank`, so
  that no rank computation is needed at a use site.
* `Equioscillates g m` says that `g` attains `± ‖g‖` with alternating signs at `m` increasing points
  of `X`.

## Main results

* `le_infDist_of_alternates` is the de la Vallée-Poussin lower bound: an alternation of length `n +
  2` for the error of *any* competitor bounds the distance to `polyLE X n` from below. Its immediate
  consequence `isBestApprox_of_equioscillates` is the sufficiency half of Chebyshev's
  equioscillation theorem.
* `IsBestApprox.exists_card_eq_of_interpolation` is the half with content in the other direction:
  the error of a best approximation attains its maximum modulus at `d` distinct points, because
  otherwise an element of the subspace interpolating the error at the extreme points gives a
  direction of improvement. Its hypothesis, that the subspace takes prescribed values at fewer than
  `d` points, holds for `polyLE X n` by Lagrange's formula (`IsBestApprox.exists_card_eq_of_polyLE`)
  and for a `d`-dimensional Haar subspace by `HaarCondition.exists_mem_forall_eq`, the interpolation
  property of a Haar system.
* `IsBestApprox.unique_of_polyLE` and `IsBestApprox.unique_of_haarCondition`, the uniqueness of the
  best uniform approximation, follow from it and the Haar condition through the midpoint of two best
  approximations.
* `isBestApprox_iff_equioscillates` is **Chebyshev's equioscillation theorem** itself, of which
  `IsBestApprox.equioscillates_of_polyLE` is the direction with content: the exchange argument
  builds, out of a maximal alternation shorter than `n + 2`, a polynomial that
  `IsBestApprox.exists_mul_nonpos` — Kolmogorov's criterion — forbids.
* `card_le_two_mul_of_forall_trigFun_eq_zero` is the Haar condition for the trigonometric
  polynomials: a nonzero one of degree at most `n` has at most `2 n` zeros in a period.
-/

open scoped Polynomial

/-- The subspace of `C(X, ℝ)` of the restrictions to `X` of the real polynomial functions of degree
at most `n`. -/
noncomputable def polyLE (X : Set ℝ) (n : ℕ) : Submodule ℝ C(X, ℝ) :=
  (Polynomial.degreeLE ℝ n).map (Polynomial.toContinuousMapOnAlgHom X).toLinearMap

/-- An element of `polyLE X n` is exactly a continuous function on `X` given by a polynomial of
degree at most `n`. -/
theorem mem_polyLE_iff {X : Set ℝ} {n : ℕ} {g : C(X, ℝ)} :
    g ∈ polyLE X n ↔ ∃ P : ℝ[X], P.degree ≤ n ∧ ∀ t : X, g t = P.eval (t : ℝ) := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, Polynomial.mem_degreeLE.mp hP, fun t => by simp⟩
  · rintro ⟨P, hP, hg⟩
    refine ⟨P, Polynomial.mem_degreeLE.mpr hP, ?_⟩
    ext t
    simpa using (hg t).symm

/-- A subspace `V` of `C(X, ℝ)` satisfies the **Haar condition in dimension `d`** when no nonzero
element of `V` vanishes at `d` distinct points of `X`. For a `d`-dimensional space this is the
classical Haar condition; carrying `d` as a parameter keeps every use site free of a rank
computation. -/
def HaarCondition {X : Type*} [TopologicalSpace X] (V : Submodule ℝ C(X, ℝ)) (d : ℕ) : Prop :=
  ∀ g ∈ V, g ≠ 0 → ∀ s : Finset X, (∀ t ∈ s, g t = 0) → s.card < d

/-- The polynomials of degree at most `n` satisfy the Haar condition in dimension `n + 1`: a nonzero
polynomial of degree at most `n` has at most `n` roots. -/
theorem haarCondition_polyLE (X : Set ℝ) (n : ℕ) : HaarCondition (polyLE X n) (n + 1) := by
  intro g hg hg0 s hs
  by_contra hcard
  push Not at hcard
  obtain ⟨P, hP, hgP⟩ := mem_polyLE_iff.mp hg
  have himg : (s.image Subtype.val).card = s.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P (s.image Subtype.val)
      (fun t ht => ?_) ?_
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      rw [← hgP u]
      exact hs u hu
    · rw [himg]
      exact lt_of_le_of_lt (Polynomial.natDegree_le_of_degree_le hP) (by omega)
  refine hg0 ?_
  ext t
  simp [hgP t, hP0]

/-- **A Haar system interpolates.** A subspace of dimension `d` satisfying the Haar condition in
dimension `d` takes prescribed values at any `d` distinct points: the evaluation map into `Fin d →
ℝ` is injective by the Haar condition, hence surjective because the dimensions agree. -/
theorem HaarCondition.exists_forall_apply_eq {X : Type*} [TopologicalSpace X]
    {V : Submodule ℝ C(X, ℝ)} {d : ℕ} [FiniteDimensional ℝ V] (hV : HaarCondition V d)
    (hdim : Module.finrank ℝ V = d) {x : Fin d → X} (hx : Function.Injective x)
    (y : Fin d → ℝ) : ∃ g ∈ V, ∀ i, g (x i) = y i := by
  classical
  set ev : V →ₗ[ℝ] Fin d → ℝ :=
    { toFun := fun g i => (g : C(X, ℝ)) (x i)
      map_add' := fun g g' => by ext i; simp
      map_smul' := fun c g => by ext i; simp } with hev
  have hevapp : ∀ (g : V) (i : Fin d), ev g i = (g : C(X, ℝ)) (x i) := fun _ _ => rfl
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    by_contra hg0
    have hne : (g : C(X, ℝ)) ≠ 0 := fun h => hg0 (Subtype.ext h)
    have hzero : ∀ t ∈ Finset.univ.image x, (g : C(X, ℝ)) t = 0 := by
      rintro t ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      rw [← hevapp g i, hg]
      rfl
    have hcard : (Finset.univ.image x).card = d := by
      rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
    exact absurd (hV _ g.2 hne _ hzero) (by omega)
  have hrank : Module.finrank ℝ V = Module.finrank ℝ (Fin d → ℝ) := by
    rw [hdim, Module.finrank_fin_fun]
  obtain ⟨g, hg⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj y
  exact ⟨g, g.2, fun i => by rw [← hevapp g i, hg]⟩

/-- The interpolation property of a Haar system in the form the exchange argument uses: fewer than
`d` points can be prescribed arbitrarily, by padding them out to `d` distinct points. -/
theorem HaarCondition.exists_mem_forall_eq {X : Type*} [TopologicalSpace X] [Infinite X]
    {V : Submodule ℝ C(X, ℝ)} {d : ℕ} [FiniteDimensional ℝ V] (hV : HaarCondition V d)
    (hdim : Module.finrank ℝ V = d) (S : Finset X) (hS : S.card < d) (y : X → ℝ) :
    ∃ q ∈ V, ∀ t ∈ S, q t = y t := by
  classical
  obtain ⟨T, hTsub, hTcard⟩ :=
    (Set.Finite.infinite_compl S.finite_toSet).exists_subset_card_eq (d - S.card)
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    exact fun a haS haT => hTsub haT haS
  have hcard : (S ∪ T).card = d := by
    rw [Finset.card_union_of_disjoint hdisj, hTcard]
    omega
  set e := Finset.equivFinOfCardEq hcard with he
  set x : Fin d → X := fun i => ((e.symm i : (S ∪ T : Finset X)) : X) with hx
  have hxinj : Function.Injective x := fun i j hij => e.symm.injective (Subtype.ext hij)
  obtain ⟨g, hgV, hgval⟩ := hV.exists_forall_apply_eq hdim hxinj fun i => y (x i)
  refine ⟨g, hgV, fun t ht => ?_⟩
  have hval := hgval (e ⟨t, Finset.mem_union_left _ ht⟩)
  simpa [hx] using hval

/-- `Equioscillates g m`: the function `g` attains `± ‖g‖` with alternating signs at `m` increasing
points of `X`, the alternation condition in Chebyshev's characterization of a best uniform
approximation. -/
def Equioscillates {X : Set ℝ} [CompactSpace X] (g : C(X, ℝ)) (m : ℕ) : Prop :=
  ∃ (σ : ℝ) (x : Fin m → X), (σ = 1 ∨ σ = -1) ∧ StrictMono (fun i => (x i : ℝ)) ∧
    ∀ i : Fin m, g (x i) = σ * (-1) ^ (i : ℕ) * ‖g‖

/-- A continuous function changing sign on an interval has a root strictly inside it. -/
private theorem exists_root_of_mul_neg {F : ℝ → ℝ} (hF : Continuous F) {u v : ℝ} (huv : u < v)
    (h : F u * F v < 0) : ∃ z ∈ Set.Ioo u v, F z = 0 := by
  rcases mul_neg_iff.mp h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · obtain ⟨z, hz, hz0⟩ :=
      intermediate_value_Ioo' huv.le hF.continuousOn (Set.mem_Ioo.mpr ⟨hv, hu⟩)
    exact ⟨z, hz, hz0⟩
  · obtain ⟨z, hz, hz0⟩ :=
      intermediate_value_Ioo huv.le hF.continuousOn (Set.mem_Ioo.mpr ⟨hu, hv⟩)
    exact ⟨z, hz, hz0⟩

/-- **De la Vallée-Poussin's lower bound.** If the error `f - q` of some competitor `q` of degree at
most `n` alternates in sign at `n + 2` increasing points of `X` with values of modulus at least `ε`,
then no polynomial of degree at most `n` approximates `f` better than `ε`.

The proof is the Haar condition for `polyLE X n`: were some `p` closer than `ε`, the difference `p -
q` would inherit the alternation, hence have `n + 1` roots by the intermediate value theorem, hence
vanish — contradicting the alternation itself.

Reference: [han2009theoretical], Theorem 3.3.19. -/
theorem le_infDist_of_alternates {X : Set ℝ} [CompactSpace X] {n : ℕ} {f q : C(X, ℝ)}
    (hq : q ∈ polyLE X n) {ε σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {x : Fin (n + 2) → X}
    (hmono : StrictMono fun i => (x i : ℝ))
    (hval : ∀ i : Fin (n + 2), ε ≤ σ * (-1) ^ (i : ℕ) * (f (x i) - q (x i))) :
    ε ≤ Metric.infDist f (polyLE X n : Set C(X, ℝ)) := by
  have hsgn : ∀ i : Fin (n + 2), |σ * (-1) ^ (i : ℕ)| = 1 := by
    intro i
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
    rcases hσ with h | h <;> simp [h]
  refine (Metric.le_infDist ⟨0, (polyLE X n).zero_mem⟩).2 ?_
  rintro p hp
  rw [dist_eq_norm]
  by_contra hcon
  push Not at hcon
  -- the difference of the two competitors inherits the alternation
  have hgpos : ∀ i : Fin (n + 2), 0 < σ * (-1) ^ (i : ℕ) * (p (x i) - q (x i)) := by
    intro i
    have h1 : |f (x i) - p (x i)| ≤ ‖f - p‖ := by
      have := (f - p).norm_coe_le_norm (x i)
      simpa using this
    have h2 : σ * (-1) ^ (i : ℕ) * (f (x i) - p (x i)) ≤ ‖f - p‖ := by
      calc σ * (-1) ^ (i : ℕ) * (f (x i) - p (x i))
          ≤ |σ * (-1) ^ (i : ℕ) * (f (x i) - p (x i))| := le_abs_self _
        _ = |f (x i) - p (x i)| := by rw [abs_mul, hsgn i, one_mul]
        _ ≤ ‖f - p‖ := h1
    have h3 := hval i
    nlinarith [h3, h2, hcon]
  -- read the difference off as a polynomial of degree at most `n`
  obtain ⟨P, hPdeg, hPval⟩ := mem_polyLE_iff.mp hp
  obtain ⟨Q, hQdeg, hQval⟩ := mem_polyLE_iff.mp hq
  have hRdeg : (P - Q).degree ≤ (n : ℕ) := (Polynomial.degree_sub_le _ _).trans (max_le hPdeg hQdeg)
  have hRval : ∀ i : Fin (n + 2), 0 < σ * (-1) ^ (i : ℕ) * (P - Q).eval (x i : ℝ) := by
    intro i
    have := hgpos i
    rwa [hPval, hQval, ← Polynomial.eval_sub] at this
  -- the intermediate value theorem produces `n + 1` roots
  have hroot : ∀ i : Fin (n + 1), ∃ z ∈ Set.Ioo (x i.castSucc : ℝ) (x i.succ : ℝ),
      (P - Q).eval z = 0 := by
    intro i
    refine exists_root_of_mul_neg (P - Q).continuous (hmono (Fin.castSucc_lt_succ (i := i))) ?_
    have h1 := hRval i.castSucc
    have h2 := hRval i.succ
    have hpar : ((-1 : ℝ)) ^ (i.succ : ℕ) = -((-1 : ℝ) ^ (i.castSucc : ℕ)) := by
      have : (i.succ : ℕ) = (i.castSucc : ℕ) + 1 := by simp
      rw [this, pow_succ]
      ring
    rw [hpar] at h2
    nlinarith [h1, h2, sq_nonneg (σ * (-1) ^ (i.castSucc : ℕ))]
  choose z hz hz0 using hroot
  have hzmono : StrictMono z := by
    intro i j hij
    calc z i < (x i.succ : ℝ) := (hz i).2
      _ ≤ (x j.castSucc : ℝ) := hmono.monotone (by
          simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          omega)
      _ < z j := (hz j).1
  have hcard : (Finset.univ.image z).card = n + 1 := by
    rw [Finset.card_image_of_injective _ hzmono.injective, Finset.card_univ, Fintype.card_fin]
  have hR0 : P - Q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (Finset.univ.image z)
      (fun t ht => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      exact hz0 i
    · rw [hcard]
      exact lt_of_le_of_lt (Polynomial.natDegree_le_of_degree_le hRdeg) (by omega)
  have := hRval 0
  rw [hR0] at this
  simp at this

/-- The sufficiency half of Chebyshev's equioscillation theorem: a polynomial whose error
equioscillates at `n + 2` points is a best uniform approximation.

Reference: [han2009theoretical], Theorem 3.3.19. -/
theorem isBestApprox_of_equioscillates {X : Set ℝ} [CompactSpace X] {n : ℕ} {f p : C(X, ℝ)}
    (hp : p ∈ polyLE X n) (h : Equioscillates (f - p) (n + 2)) :
    IsBestApprox (polyLE X n : Set C(X, ℝ)) f p := by
  obtain ⟨σ, x, hσ, hmono, hvals⟩ := h
  have hle : ‖f - p‖ ≤ Metric.infDist f (polyLE X n : Set C(X, ℝ)) := by
    refine le_infDist_of_alternates hp hσ hmono fun i => ?_
    have hv : f (x i) - p (x i) = σ * (-1) ^ (i : ℕ) * ‖f - p‖ := by
      simpa using hvals i
    rw [hv, ← mul_assoc]
    have hsq : σ * (-1) ^ (i : ℕ) * (σ * (-1) ^ (i : ℕ)) = 1 := by
      have h1 : ((-1 : ℝ) ^ (i : ℕ)) * ((-1 : ℝ) ^ (i : ℕ)) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      rcases hσ with h | h <;> subst h <;> linear_combination h1
    rw [hsq, one_mul]
  rw [isBestApprox_iff_norm_sub_eq_infDist hp]
  exact le_antisymm hle (by rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hp)

/-! ### The extreme set of a best approximation, and uniqueness -/

/-- On a compact nonempty space the maximum modulus of a continuous function is attained. -/
private theorem exists_abs_eq_norm {X : Set ℝ} [CompactSpace X] [Nonempty X] (g : C(X, ℝ)) :
    ∃ t : X, |g t| = ‖g‖ := by
  obtain ⟨t, -, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_abs.comp g.continuous).continuousOn
  refine ⟨t, le_antisymm (by simpa using g.norm_coe_le_norm t) ?_⟩
  rw [ContinuousMap.norm_le _ (abs_nonneg _)]
  intro u
  simpa using hmax (Set.mem_univ u)

/-- **A direction of improvement.** If some `q` has the same strict sign as `g` at every point where
`|g|` attains its maximum, then `g - λ q` is strictly smaller than `g` in sup norm for all small `λ
> 0`: away from the extreme set there is room to spare, and at the extreme set the correction has
the right sign. -/
private theorem exists_norm_sub_smul_lt {X : Set ℝ} [CompactSpace X] [Nonempty X]
    {g q : C(X, ℝ)} (hE : 0 < ‖g‖) (hsign : ∀ t : X, |g t| = ‖g‖ → 0 < g t * q t) :
    ∃ lam : ℝ, 0 < lam ∧ ‖g - lam • q‖ < ‖g‖ := by
  classical
  -- away from the extreme set the modulus of `g` stays below its maximum by a fixed margin
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ, 0 < δ ∧ ∀ t : X, g t * q t ≤ 0 → |g t| ≤ ‖g‖ - δ := by
    rcases Set.eq_empty_or_nonempty {t : X | g t * q t ≤ 0} with hempty | hne
    · refine ⟨‖g‖, hE, fun t ht => ?_⟩
      exact absurd (show t ∈ {t : X | g t * q t ≤ 0} from ht)
        (by rw [hempty]; exact Set.notMem_empty t)
    · have hclosed : IsClosed {t : X | g t * q t ≤ 0} :=
        isClosed_le (g.continuous.mul q.continuous) continuous_const
      obtain ⟨t₀, ht₀, hmax⟩ := hclosed.isCompact.exists_isMaxOn hne
        (continuous_abs.comp g.continuous).continuousOn
      have hlt : |g t₀| < ‖g‖ := by
        refine lt_of_le_of_ne (by simpa using g.norm_coe_le_norm t₀) fun heq => ?_
        exact absurd (hsign t₀ heq) (not_lt.mpr ht₀)
      exact ⟨‖g‖ - |g t₀|, by linarith, fun t ht => by
        have hle : |g t| ≤ |g t₀| := hmax (show t ∈ {t : X | g t * q t ≤ 0} from ht)
        linarith⟩
  -- a small enough step
  have hmin : 0 < min δ ‖g‖ := lt_min hδ0 hE
  refine ⟨min δ ‖g‖ / (‖q‖ + 1), by positivity, ?_⟩
  set lam : ℝ := min δ ‖g‖ / (‖q‖ + 1) with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  have hlamq : lam * ‖q‖ < min δ ‖g‖ := by
    rw [hlamdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg q]
  obtain ⟨t, ht⟩ := exists_abs_eq_norm (g - lam • q)
  rw [← ht]
  have happ : (g - lam • q) t = g t - lam * q t := by simp
  have hqt : |q t| ≤ ‖q‖ := by simpa using q.norm_coe_le_norm t
  have hgt : |g t| ≤ ‖g‖ := by simpa using g.norm_coe_le_norm t
  have hqt' : q t ≤ ‖q‖ := le_trans (le_abs_self _) hqt
  have hqt'' : -‖q‖ ≤ q t := by
    have := neg_abs_le (q t)
    linarith
  rw [happ]
  rcases le_or_gt (g t * q t) 0 with hcase | hcase
  · have hbound := hδ t hcase
    have habs : |g t - lam * q t| ≤ |g t| + |lam * q t| := by
      simpa using abs_sub_le (g t) 0 (lam * q t)
    rw [abs_mul, abs_of_pos hlam0] at habs
    have : lam * |q t| ≤ lam * ‖q‖ := by nlinarith
    have hlt : lam * ‖q‖ < δ := lt_of_lt_of_le hlamq (min_le_left _ _)
    linarith
  · have hlt : lam * ‖q‖ < ‖g‖ := lt_of_lt_of_le hlamq (min_le_right _ _)
    rcases mul_pos_iff.mp hcase with ⟨hg, hq⟩ | ⟨hg, hq⟩
    · refine abs_lt.mpr ⟨?_, ?_⟩
      · nlinarith
      · nlinarith [le_abs_self (g t)]
    · refine abs_lt.mpr ⟨?_, ?_⟩
      · nlinarith [neg_abs_le (g t)]
      · nlinarith

/-- **The error of a best uniform approximation from an interpolating subspace attains its maximum
modulus at `d` points.** This is the half of the Chebyshev characterization that has content: if the
error attained its maximum modulus at fewer than `d` points, then an element `q` of the subspace
interpolating the error at those points makes `p + c q` a strictly better approximation once `c > 0`
is small enough.

The hypothesis is what a Haar system of dimension `d` supplies
(`HaarCondition.exists_mem_forall_eq`), and what Lagrange interpolation supplies for the polynomials
of degree at most `n`, with `d = n + 1`.

Reference: [han2009theoretical], Theorem 3.3.19. -/
theorem IsBestApprox.exists_card_eq_of_interpolation {X : Set ℝ} [CompactSpace X] [Infinite X]
    {d : ℕ} {V : Submodule ℝ C(X, ℝ)} {f p : C(X, ℝ)}
    (hinterp : ∀ S : Finset X, S.card < d → ∀ y : X → ℝ, ∃ q ∈ V, ∀ t ∈ S, q t = y t)
    (hp : IsBestApprox (V : Set C(X, ℝ)) f p) :
    ∃ S : Finset X, S.card = d ∧ ∀ t ∈ S, |(f - p) t| = ‖f - p‖ := by
  classical
  set g : C(X, ℝ) := f - p with hgdef
  by_cases hbig : ∃ S : Finset X, S.card = d ∧ ∀ t ∈ S, |g t| = ‖g‖
  · exact hbig
  exfalso
  set E : Set X := {t | |g t| = ‖g‖} with hEdef
  have hEfin : E.Finite := by
    by_contra hinf
    obtain ⟨S, hSsub, hScard⟩ := Set.Infinite.exists_subset_card_eq hinf d
    exact hbig ⟨S, hScard, fun t ht => hSsub (Finset.mem_coe.mpr ht)⟩
  have hEcard : hEfin.toFinset.card < d := by
    by_contra hlt
    push Not at hlt
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hlt
    exact hbig ⟨S, hScard, fun t ht => hEfin.mem_toFinset.mp (hSsub ht)⟩
  -- the error is not identically zero
  have hgpos : 0 < ‖g‖ := by
    rcases (norm_nonneg g).lt_or_eq with h | h
    · exact h
    · exfalso
      have huniv : E = Set.univ := by
        ext t
        simp only [hEdef, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        have h1 : |g t| ≤ ‖g‖ := by simpa using g.norm_coe_le_norm t
        have h2 : (0 : ℝ) ≤ |g t| := abs_nonneg _
        linarith
      exact Set.infinite_univ (α := X) (huniv ▸ hEfin)
  set S : Finset X := hEfin.toFinset with hSdef
  -- interpolate the error at the extreme points
  obtain ⟨q, hqmem, hqval⟩ := hinterp S hEcard fun t => g t
  -- at every extreme point the interpolant has the sign of the error, so it is a direction of
  -- improvement
  have hsign : ∀ t : X, |g t| = ‖g‖ → 0 < g t * q t := by
    intro t ht
    have htS : t ∈ S := by
      rw [hSdef]
      exact hEfin.mem_toFinset.mpr ht
    have h3 : g t * q t = ‖g‖ * ‖g‖ := by
      rw [hqval t htS, ← abs_mul_abs_self (g t), ht]
    rw [h3]
    exact mul_pos hgpos hgpos
  obtain ⟨c, -, hlt⟩ := exists_norm_sub_smul_lt hgpos hsign
  -- contradiction with best approximation
  have hmem : p + c • q ∈ (V : Set C(X, ℝ)) := V.add_mem hp.1 (V.smul_mem c hqmem)
  have hbetter := hp.2 (p + c • q) hmem
  have heq : f - (p + c • q) = g - c • q := by
    rw [hgdef]
    abel
  rw [heq] at hbetter
  exact absurd hbetter (not_le.mpr hlt)

/-- **The error of a best uniform approximation attains its maximum modulus at `n + 1` distinct
points.** The polynomial case of `IsBestApprox.exists_card_eq_of_interpolation`, whose interpolation
hypothesis is Lagrange's formula at the extreme points.

Reference: [han2009theoretical], Theorem 3.3.19. -/
theorem IsBestApprox.exists_card_eq_of_polyLE {X : Set ℝ} [CompactSpace X] [Infinite X] {n : ℕ}
    {f p : C(X, ℝ)} (hp : IsBestApprox (polyLE X n : Set C(X, ℝ)) f p) :
    ∃ S : Finset X, S.card = n + 1 ∧ ∀ t ∈ S, |(f - p) t| = ‖f - p‖ := by
  classical
  refine hp.exists_card_eq_of_interpolation fun S hS y => ?_
  have hinj : Set.InjOn (fun u : X => (u : ℝ)) ↑S := fun a _ b _ h => Subtype.val_injective h
  set Q : ℝ[X] := Lagrange.interpolate S (fun u : X => (u : ℝ)) (fun u => y u) with hQdef
  have hQdeg : Q.degree ≤ (n : ℕ) := by
    have h1 : Q.degree < (S.card : WithBot ℕ) := Lagrange.degree_interpolate_lt _ hinj
    have h2 : (S.card : WithBot ℕ) ≤ (n : ℕ) := by
      exact_mod_cast Nat.lt_succ_iff.mp hS
    exact le_of_lt (lt_of_lt_of_le h1 h2)
  refine ⟨Q.toContinuousMapOn X, mem_polyLE_iff.mpr ⟨Q, hQdeg, fun t => rfl⟩, fun t ht => ?_⟩
  exact Lagrange.eval_interpolate_at_node _ hinj ht

/-- **Two best approximations agree wherever the error of their midpoint is extreme.** The two
errors have the common minimal norm `ρ`, so each has modulus at most `ρ` everywhere; where their
average has modulus exactly `ρ` neither can fall short, and both have the same sign. This is the
step both uniqueness theorems below take. -/
private theorem eq_of_abs_sub_midpoint_eq {X : Set ℝ} [CompactSpace X] {K : Set C(X, ℝ)}
    {f p₁ p₂ : C(X, ℝ)} (h₁ : IsBestApprox K f p₁) (h₂ : IsBestApprox K f p₂)
    (hmid : IsBestApprox K f ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂)) {t : X}
    (hmax : |(f - ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂)) t|
      = ‖f - ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂)‖) :
    p₁ t = p₂ t := by
  set ρ : ℝ := ‖f - ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂)‖ with hρ
  have hρ₁ : ‖f - p₁‖ = ρ := by
    rw [hρ, h₁.norm_sub_eq_infDist, hmid.norm_sub_eq_infDist]
  have hρ₂ : ‖f - p₂‖ = ρ := by
    rw [hρ, h₂.norm_sub_eq_infDist, hmid.norm_sub_eq_infDist]
  have hb₁ : |f t - p₁ t| ≤ ρ := by
    rw [← hρ₁]
    simpa using (f - p₁).norm_coe_le_norm t
  have hb₂ : |f t - p₂ t| ≤ ρ := by
    rw [← hρ₂]
    simpa using (f - p₂).norm_coe_le_norm t
  have hsplit : (f - ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂)) t
      = (2 : ℝ)⁻¹ * (f t - p₁ t) + (2 : ℝ)⁻¹ * (f t - p₂ t) := by
    simp
    ring
  rw [hsplit] at hmax
  rcases abs_le.mp hb₁ with ⟨ha₁, ha₂⟩
  rcases abs_le.mp hb₂ with ⟨hc₁, hc₂⟩
  rcases abs_cases ((2 : ℝ)⁻¹ * (f t - p₁ t) + (2 : ℝ)⁻¹ * (f t - p₂ t)) with
    ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at hmax <;> linarith

/-- **Uniqueness of the best uniform approximation from a Haar subspace.** Two best approximations
of the same function by elements of a `d`-dimensional subspace satisfying the Haar condition in
dimension `d` agree.

Their midpoint is a best approximation too, its error attains the common minimal norm at `d` points,
and at each of those the two errors must agree; the Haar condition then forces the two elements to
be equal.

Reference: [han2009theoretical], Theorem 3.3.19; [kress1998numerical], §8.2. -/
theorem IsBestApprox.unique_of_haarCondition {X : Set ℝ} [CompactSpace X] [Infinite X] {d : ℕ}
    {V : Submodule ℝ C(X, ℝ)} [FiniteDimensional ℝ V] (hV : HaarCondition V d)
    (hdim : Module.finrank ℝ V = d) {f p₁ p₂ : C(X, ℝ)}
    (h₁ : IsBestApprox (V : Set C(X, ℝ)) f p₁) (h₂ : IsBestApprox (V : Set C(X, ℝ)) f p₂) :
    p₁ = p₂ := by
  have hmid : IsBestApprox (V : Set C(X, ℝ)) f ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂) :=
    convex_setOf_isBestApprox V.convex f h₁ h₂ (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨S, hScard, hSext⟩ :=
    hmid.exists_card_eq_of_interpolation (hV.exists_mem_forall_eq hdim)
  have hagree : ∀ t ∈ S, p₁ t = p₂ t := fun t ht =>
    eq_of_abs_sub_midpoint_eq h₁ h₂ hmid (hSext t ht)
  have hzero : p₁ - p₂ = 0 := by
    by_contra hne
    have hcard := hV (p₁ - p₂) (V.sub_mem h₁.1 h₂.1) hne S (fun t ht => by
      simpa using sub_eq_zero.mpr (hagree t ht))
    omega
  exact sub_eq_zero.mp hzero

/-- **Uniqueness of the best uniform approximation** by polynomials of degree at most `n` on a
compact infinite subset of the line: two best approximations of the same function agree.

Their midpoint is a best approximation too, its error attains the common minimal norm at `n + 1`
points, and at each of those the two errors must agree; the Haar condition then forces the two
polynomials to be equal.

Reference: [han2009theoretical], Theorem 3.3.19. -/
theorem IsBestApprox.unique_of_polyLE {X : Set ℝ} [CompactSpace X] [Infinite X] {n : ℕ}
    {f p₁ p₂ : C(X, ℝ)} (h₁ : IsBestApprox (polyLE X n : Set C(X, ℝ)) f p₁)
    (h₂ : IsBestApprox (polyLE X n : Set C(X, ℝ)) f p₂) : p₁ = p₂ := by
  have hconv : Convex ℝ ((polyLE X n : Set C(X, ℝ))) := (polyLE X n).convex
  have hmid : IsBestApprox (polyLE X n : Set C(X, ℝ)) f
      ((2 : ℝ)⁻¹ • p₁ + (2 : ℝ)⁻¹ • p₂) :=
    convex_setOf_isBestApprox hconv f h₁ h₂ (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨S, hScard, hSext⟩ := hmid.exists_card_eq_of_polyLE
  have hagree : ∀ t ∈ S, p₁ t = p₂ t := fun t ht =>
    eq_of_abs_sub_midpoint_eq h₁ h₂ hmid (hSext t ht)
  have hsubmem : p₁ - p₂ ∈ polyLE X n := (polyLE X n).sub_mem h₁.1 h₂.1
  have hzero : p₁ - p₂ = 0 := by
    by_contra hne
    have hcard := haarCondition_polyLE X n (p₁ - p₂) hsubmem hne S (fun t ht => by
      simpa using sub_eq_zero.mpr (hagree t ht))
    omega
  exact sub_eq_zero.mp hzero

/-! ### Kolmogorov's improvement criterion -/

/-- An alternation of length `m` contains one of every shorter length. -/
theorem Equioscillates.mono {X : Set ℝ} [CompactSpace X] {g : C(X, ℝ)} {m k : ℕ}
    (h : Equioscillates g m) (hk : k ≤ m) : Equioscillates g k := by
  obtain ⟨σ, x, hσ, hmono, hval⟩ := h
  refine ⟨σ, fun i => x (Fin.castLE hk i), hσ, fun i j hij => hmono ?_, fun i => ?_⟩
  · have hlt : ((Fin.castLE hk i : Fin m) : ℕ) < ((Fin.castLE hk j : Fin m) : ℕ) := by
      simpa only [Fin.val_castLE] using (Fin.lt_def.mp hij)
    exact hlt
  · change g (x (Fin.castLE hk i)) = σ * (-1) ^ (i : ℕ) * ‖g‖
    rw [hval (Fin.castLE hk i), Fin.val_castLE]

/-- **Kolmogorov's criterion, the half with content.** At a best approximation no element of the
subspace has the same strict sign as the error at every point of the extreme set: such an element
would be a direction of improvement.

It is the analytic half of Chebyshev's equioscillation theorem — the other half is the combinatorial
construction of such an element out of a short alternation.

Reference: [han2009theoretical], Theorem 3.3.19; [kress1998numerical], §8.2. -/
theorem IsBestApprox.exists_mul_nonpos {X : Set ℝ} [CompactSpace X] [Nonempty X]
    {V : Submodule ℝ C(X, ℝ)} {f p : C(X, ℝ)} (hp : IsBestApprox (V : Set C(X, ℝ)) f p)
    (hE : 0 < ‖f - p‖) {q : C(X, ℝ)} (hq : q ∈ V) :
    ∃ t : X, |(f - p) t| = ‖f - p‖ ∧ (f - p) t * q t ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨lam, hlam0, hlt⟩ := exists_norm_sub_smul_lt hE fun t ht => hcon t ht
  have hmem : p + lam • q ∈ (V : Set C(X, ℝ)) := V.add_mem hp.1 (V.smul_mem lam hq)
  have heq : f - (p + lam • q) = f - p - lam • q := by abel
  exact absurd (hp.2 _ hmem) (not_le.mpr (by rw [heq]; exact hlt))

/-! ### Chebyshev's equioscillation theorem -/

/-- An alternation written with a single constant: `g` takes the values `± c` alternately, with `|c|
= ‖g‖`. This is the form the construction below produces, and it is an alternation. -/
private theorem equioscillates_of_alternating {X : Set ℝ} [CompactSpace X] {g : C(X, ℝ)} {m : ℕ}
    {w : Fin m → X} (hmono : StrictMono fun i => (w i : ℝ)) {c : ℝ} (hc : |c| = ‖g‖)
    (hval : ∀ i, g (w i) = (-1) ^ (i : ℕ) * c) : Equioscillates g m := by
  rcases eq_or_ne ‖g‖ 0 with h0 | h0
  · refine ⟨1, w, Or.inl rfl, hmono, fun i => ?_⟩
    have hc0 : c = 0 := by
      rw [h0] at hc
      exact abs_eq_zero.mp hc
    rw [hval i, hc0, h0]
    ring
  · refine ⟨c / ‖g‖, w, ?_, hmono, fun i => ?_⟩
    · rcases (abs_eq (norm_nonneg g)).mp hc with h | h
      · exact Or.inl (by rw [h]; field_simp)
      · exact Or.inr (by rw [h]; field_simp)
    · rw [hval i]
      field_simp

/-- Prepending a point to the left of an alternation, with the opposite sign, lengthens it. -/
private theorem equioscillates_succ_of_forall_lt {X : Set ℝ} [CompactSpace X] {g : C(X, ℝ)}
    {m : ℕ} {w : Fin m → X} (hmono : StrictMono fun i => (w i : ℝ)) {c : ℝ} (hc : |c| = ‖g‖)
    (hval : ∀ i, g (w i) = (-1) ^ (i : ℕ) * c) {t : X} (hlt : ∀ i, (t : ℝ) < (w i : ℝ))
    (hgt : g t = -c) : Equioscillates g (m + 1) := by
  refine equioscillates_of_alternating (w := Fin.cons t w) (c := -c) ?_ (by rwa [abs_neg]) ?_
  · intro a b hab
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact absurd hab (lt_irrefl _)
      | succ b' => simpa using hlt b'
    | succ a' =>
      cases b using Fin.cases with
      | zero => exact absurd hab (by simp)
      | succ b' =>
        simp only [Fin.cons_succ]
        exact hmono (by simpa using hab)
  · intro i
    cases i using Fin.cases with
    | zero => simpa using hgt
    | succ i' =>
      simp only [Fin.cons_succ, Fin.val_succ]
      rw [hval i']
      ring

/-- Appending a point to the right of an alternation, with the opposite sign, lengthens it. -/
private theorem equioscillates_succ_of_forall_gt {X : Set ℝ} [CompactSpace X] {g : C(X, ℝ)}
    {m : ℕ} {w : Fin m → X} (hmono : StrictMono fun i => (w i : ℝ)) {c : ℝ} (hc : |c| = ‖g‖)
    (hval : ∀ i, g (w i) = (-1) ^ (i : ℕ) * c) {t : X} (hgt : ∀ i, (w i : ℝ) < (t : ℝ))
    (hgv : g t = (-1) ^ m * c) : Equioscillates g (m + 1) := by
  refine equioscillates_of_alternating (w := Fin.snoc w t) (c := c) ?_ hc ?_
  · intro a b hab
    cases a using Fin.lastCases with
    | last => exact absurd hab (not_lt.mpr (Fin.le_last b))
    | cast a' =>
      cases b using Fin.lastCases with
      | last => simpa using hgt a'
      | cast b' =>
        simp only [Fin.snoc_castSucc]
        exact hmono (by simpa using hab)
  · intro i
    cases i using Fin.lastCases with
    | last => simpa using hgv
    | cast i' =>
      simp only [Fin.snoc_castSucc, Fin.val_castSucc]
      exact hval i'

/-! ### The Haar condition for trigonometric polynomials -/

/-- **A nonzero real trigonometric polynomial of degree at most `n` has at most `2 n` zeros in a
period.** This is the Haar condition for the trigonometric polynomials — the analogue of
`haarCondition_polyLE`, in the dimension `2 n + 1` of that space — and it is what the trigonometric
equioscillation theorem and trigonometric interpolation rest on.

The proof is the substitution `z = exp (2 π i x / T)`, which is injective on a period: under it a
real trigonometric polynomial of degree at most `n` becomes `z ^ (-n)` times an algebraic polynomial
of degree at most `2 n` evaluated at `z`, and a nonzero polynomial has no more roots than its
degree.

The hypothesis is stated as an explicit combination of the real trigonometric system rather than as
membership in a subspace of trigonometric polynomials, so that this file needs nothing from the
Fourier layer beyond `Numlib/Analysis/Fourier/TrigonometricBasis`'s system itself.

Reference: [han2009theoretical], Theorem 3.3.20. -/
theorem card_le_two_mul_of_forall_trigFun_eq_zero {T : ℝ} (hT : T ≠ 0) {n : ℕ}
    {f : C(AddCircle T, ℝ)} {c : ℤ → ℝ}
    (hf : f = ∑ m ∈ Finset.Icc (-(n : ℤ)) n, c m • trigFun T m) (hne : f ≠ 0)
    {s : Finset (AddCircle T)} (hs : ∀ x ∈ s, f x = 0) : s.card ≤ 2 * n := by
  classical
  -- the exponential variable, and its elementary properties
  have hpow : ∀ (m : ℤ) (x : AddCircle T), fourier m x = fourier 1 x ^ m := by
    intro m x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_int_mul]
      congr 1
      push_cast
      ring
  have hnorm : ∀ (m : ℤ) (x : AddCircle T), ‖fourier m x‖ = 1 := fun m x => by
    rw [fourier_apply]; exact Circle.norm_coe _
  have hne0 : ∀ x : AddCircle T, fourier 1 x ≠ 0 := fun x h => by
    have h1 := hnorm 1 x
    rw [h, norm_zero] at h1
    exact absurd h1 (by norm_num)
  have hinj : Function.Injective fun x : AddCircle T => fourier 1 x := by
    intro x y hxy
    simp only [fourier_one] at hxy
    exact AddCircle.injective_toCircle hT (Circle.ext hxy)
  -- the complex coefficients of the trigonometric polynomial
  obtain ⟨d, hd⟩ : ∃ d : ℤ → ℂ, ∀ m : ℤ,
      d m = (c m * trigWeight m + c (-m) * (starRingEnd ℂ) (trigWeight (-m))) / 2 :=
    ⟨_, fun _ => rfl⟩
  have hre : ∀ z : ℂ, ((z.re : ℝ) : ℂ) = (z + (starRingEnd ℂ) z) / 2 := by
    intro z
    rw [Complex.add_conj]
    push_cast
    ring
  have hfc : ∀ x : AddCircle T,
      ((f x : ℝ) : ℂ) = ∑ m ∈ Finset.Icc (-(n : ℤ)) n, d m * fourier m x := by
    intro x
    have hfx : f x = ∑ m ∈ Finset.Icc (-(n : ℤ)) n, c m * (trigWeight m * fourier m x).re := by
      rw [hf]
      simp
    have hterm : ∀ m : ℤ, ((c m * (trigWeight m * fourier m x).re : ℝ) : ℂ)
        = (c m * trigWeight m * fourier m x) / 2
          + (c m * (starRingEnd ℂ) (trigWeight m) * fourier (-m) x) / 2 := by
      intro m
      rw [Complex.ofReal_mul, hre, fourier_neg, map_mul]
      ring
    rw [hfx, Complex.ofReal_sum, Finset.sum_congr rfl fun m _ => hterm m,
      Finset.sum_add_distrib]
    have hreindex :
        ∑ m ∈ Finset.Icc (-(n : ℤ)) n, (c m * (starRingEnd ℂ) (trigWeight m) * fourier (-m) x) / 2
          = ∑ m ∈ Finset.Icc (-(n : ℤ)) n,
              (c (-m) * (starRingEnd ℂ) (trigWeight (-m)) * fourier m x) / 2 := by
      refine Finset.sum_equiv (Equiv.neg ℤ) (fun i => ?_) (fun i _ => ?_)
      · simp only [Equiv.neg_apply, Finset.mem_Icc]
        omega
      · simp only [Equiv.neg_apply, neg_neg]
    rw [hreindex, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hd m]
    ring
  -- the algebraic polynomial of the substitution
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℂ, Q = ∑ m ∈ Finset.Icc (-(n : ℤ)) n,
      Polynomial.C (d m) * Polynomial.X ^ (m + (n : ℤ)).toNat := ⟨_, rfl⟩
  have hQdeg : Q.natDegree ≤ 2 * n := by
    rw [hQ]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    have := Finset.mem_Icc.mp hm
    omega
  have hQeval : ∀ x : AddCircle T,
      Q.eval (fourier 1 x) = ((f x : ℝ) : ℂ) * fourier 1 x ^ (n : ℕ) := by
    intro x
    rw [hQ, Polynomial.eval_finsetSum, hfc x, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn := Finset.mem_Icc.mp hm
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, hpow m x,
      ← zpow_natCast (fourier 1 x) ((m + (n : ℤ)).toNat), Int.toNat_of_nonneg (by omega),
      zpow_add₀ (hne0 x), zpow_natCast]
    ring
  have hQne : Q ≠ 0 := by
    intro h0
    refine hne (ContinuousMap.ext fun x => ?_)
    have hx := hQeval x
    rw [h0, Polynomial.eval_zero] at hx
    have hxne : fourier 1 x ^ (n : ℕ) ≠ 0 := pow_ne_zero _ (hne0 x)
    have hzero : ((f x : ℝ) : ℂ) = 0 := by
      rcases mul_eq_zero.mp hx.symm with h | h
      · exact h
      · exact absurd h hxne
    simpa using hzero
  -- the zeros of the trigonometric polynomial are roots of `Q`
  have hsub : s.image (fun x => fourier 1 x) ⊆ Q.roots.toFinset := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQne]
    have hx' := hQeval x
    rw [hs x hx] at hx'
    simpa [Polynomial.IsRoot] using hx'
  calc s.card = (s.image (fun x => fourier 1 x)).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ Q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := Polynomial.card_roots' Q
    _ ≤ 2 * n := hQdeg

/-- **A longest alternation.** A nonzero `g` on a compact nonempty space alternates once, at a point
of maximum modulus; so if it does not alternate `n + 2` times, there is a greatest length `m` at
which it alternates, and `1 ≤ m ≤ n + 1`. -/
private theorem exists_maximal_equioscillates {X : Set ℝ} [CompactSpace X] [Nonempty X] {n : ℕ}
    {g : C(X, ℝ)} (hcon : ¬ Equioscillates g (n + 2)) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n + 1 ∧ Equioscillates g m ∧ ∀ k, m < k → ¬ Equioscillates g k := by
  classical
  obtain ⟨t₀, ht₀⟩ := exists_abs_eq_norm g
  have halt1 : Equioscillates g 1 := by
    refine equioscillates_of_alternating (w := fun _ : Fin 1 => t₀) (c := g t₀) ?_ ht₀ ?_
    · intro a b hab
      have ha := a.isLt
      have hb := b.isLt
      exact absurd (Fin.lt_def.mp hab) (by omega)
    · intro i
      have hi : (i : ℕ) = 0 := by have := i.isLt; omega
      rw [hi, pow_zero, one_mul]
  refine ⟨Nat.findGreatest (fun k => Equioscillates g k) (n + 1),
    Nat.le_findGreatest (by omega) halt1, Nat.findGreatest_le _,
    Nat.findGreatest_spec (m := 1) (by omega) halt1, fun k hk hk' => ?_⟩
  rcases Nat.lt_or_ge (n + 1) k with h | h
  · exact hcon (hk'.mono (by omega))
  · exact Nat.findGreatest_is_greatest hk h hk'

/-- **The exchange argument.** If the error of a best approximation does not alternate `n + 2`
times, then a polynomial of degree at most `n` has the sign of the error at every extreme point,
which `IsBestApprox.exists_mul_nonpos` forbids.

The polynomial is built from an alternation `z` of the greatest possible length `m ≤ n + 1`, chosen
among those of length `m` to minimize `∑ z i`. Minimality says that no extreme point of the sign of
`z j` lies strictly between `z (j-1)` and `z j`; maximality says that the alternation cannot be
extended at either end. Between consecutive `z j` the last extreme point of the sign of `z j` is
separated from `z (j+1)` by a point `y j`, and `∏ (y j - x)`, scaled by the sign of `z 0`, is the
polynomial. -/
private theorem exists_improving_of_not_equioscillates {X : Set ℝ} [CompactSpace X] [Nonempty X]
    {n : ℕ} {g : C(X, ℝ)} (hE : 0 < ‖g‖) (hcon : ¬ Equioscillates g (n + 2)) :
    ∃ q ∈ polyLE X n, ∀ t : X, |g t| = ‖g‖ → 0 < g t * q t := by
  classical
  -- the greatest length of an alternation
  obtain ⟨m, hm1, hmle, hmspec, hmmax⟩ := exists_maximal_equioscillates hcon
  have : NeZero m := ⟨by omega⟩
  -- the alternations of length `m`, as a compact set of tuples
  obtain ⟨σ, x, hσ, hxmono, hxval⟩ := hmspec
  have hcontw : ∀ i : Fin m, Continuous fun w : Fin m → X => (w i : ℝ) :=
    fun i => continuous_subtype_val.comp (continuous_apply i)
  have hcontg : ∀ i : Fin m, Continuous fun w : Fin m → X => g (w i) :=
    fun i => g.continuous.comp (continuous_apply i)
  set S : Set (Fin m → X) := {w | ∀ i j : Fin m, i ≤ j → (w i : ℝ) ≤ (w j : ℝ)} ∩
    ({w | ∀ i, g (w i) = (-1) ^ (i : ℕ) * g (w 0)} ∩ {w | |g (w 0)| = ‖g‖}) with hSdef
  have hxS : x ∈ S := by
    refine ⟨fun i j hij => hxmono.monotone hij, fun i => ?_, ?_⟩
    · rw [hxval i, hxval 0]
      simp
      ring
    · change |g (x 0)| = ‖g‖
      rw [hxval 0]
      rcases hσ with h | h <;> simp [h, abs_of_nonneg (norm_nonneg g)]
  have hSclosed : IsClosed S := by
    have h1 : IsClosed {w : Fin m → X | ∀ i j : Fin m, i ≤ j → (w i : ℝ) ≤ (w j : ℝ)} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le (hcontw i) (hcontw j)
    have h2 : IsClosed {w : Fin m → X | ∀ i, g (w i) = (-1) ^ (i : ℕ) * g (w 0)} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_eq (hcontg i) (continuous_const.mul (hcontg 0))
    have h3 : IsClosed {w : Fin m → X | |g (w 0)| = ‖g‖} :=
      isClosed_eq (continuous_abs.comp (hcontg 0)) continuous_const
    exact h1.inter (h2.inter h3)
  obtain ⟨z, hzS, hzmin⟩ := hSclosed.isCompact.exists_isMinOn ⟨x, hxS⟩
    (continuous_finsetSum Finset.univ fun i _ => hcontw i).continuousOn
  obtain ⟨hzmono, hzval, hznorm⟩ := hzS
  have hznorm' : |g (z 0)| = ‖g‖ := hznorm
  have hzne : g (z 0) ≠ 0 := fun h => by
    rw [h, abs_zero] at hznorm'
    exact absurd hznorm'.symm hE.ne'
  have hzabs : ∀ i, |g (z i)| = ‖g‖ := fun i => by
    rw [hzval i, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, hznorm']
  -- the minimizing alternation is strictly monotone
  have hzstrict : ∀ i j : Fin m, i < j → (z i : ℝ) < (z j : ℝ) := by
    intro a b hab
    refine lt_of_le_of_ne (hzmono a b hab.le) fun heq => ?_
    have hb := b.isLt
    have ha1 : (a : ℕ) + 1 < m := by
      have := Fin.lt_def.mp hab
      omega
    have h1 : (z a : ℝ) ≤ (z ⟨(a : ℕ) + 1, ha1⟩ : ℝ) := hzmono _ _ (by simp [Fin.le_def])
    have h2 : (z ⟨(a : ℕ) + 1, ha1⟩ : ℝ) ≤ (z b : ℝ) := hzmono _ _ (by
      simp only [Fin.le_def]
      have := Fin.lt_def.mp hab
      omega)
    have h3 : z ⟨(a : ℕ) + 1, ha1⟩ = z a := Subtype.ext (le_antisymm (heq ▸ h2) h1)
    have h5 : g (z ⟨(a : ℕ) + 1, ha1⟩) = g (z a) := by rw [h3]
    rw [hzval ⟨(a : ℕ) + 1, ha1⟩, hzval a] at h5
    simp only at h5
    rw [pow_succ, mul_assoc] at h5
    have hu : ((-1 : ℝ) ^ (a : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h7 := mul_left_cancel₀ hu h5
    exact hzne (by linarith)
  -- the alternation as a family indexed by `ℕ`
  obtain ⟨zz, hzz⟩ : ∃ zz : ℕ → X, ∀ (j : ℕ) (h : j < m), zz j = z ⟨j, h⟩ :=
    ⟨fun j => if h : j < m then z ⟨j, h⟩ else z ⟨0, by omega⟩, fun j h => by simp [h]⟩
  have hzz0 : zz 0 = z 0 := by
    rw [hzz 0 (by omega)]
    exact congrArg z (by ext; simp)
  have hzzval : ∀ j, ∀ h : j < m, g (zz j) = (-1) ^ j * g (zz 0) := by
    intro j h
    rw [hzz j h, hzz0, hzval ⟨j, h⟩]
  have hzzabs : ∀ j, j < m → |g (zz j)| = ‖g‖ := fun j h => by
    rw [hzz j h]; exact hzabs _
  have hzzne : g (zz 0) ≠ 0 := by rw [hzz0]; exact hzne
  have hzzmono : ∀ i j, i ≤ j → ∀ h : j < m, (zz i : ℝ) ≤ (zz j : ℝ) := by
    intro i j hij h
    rw [hzz i (by omega), hzz j h]
    exact hzmono _ _ (by simp [Fin.le_def]; omega)
  have hzzstrict : ∀ i j, i < j → ∀ h : j < m, (zz i : ℝ) < (zz j : ℝ) := by
    intro i j hij h
    rw [hzz i (by omega), hzz j h]
    exact hzstrict _ _ (by simp [Fin.lt_def]; omega)
  -- minimality: no extreme point of the sign of `zz j` lies just to the left of `zz j`
  have hMin : ∀ j, ∀ hj : j < m, ∀ t : X, g t = g (zz j) → (t : ℝ) < (zz j : ℝ) →
      (∀ i, i < j → (zz i : ℝ) < (t : ℝ)) → False := by
    intro j hj t hgt hlt hlow
    set jf : Fin m := ⟨j, hj⟩ with hjf
    have hgtz : g t = g (z jf) := by rwa [hzz j hj] at hgt
    have hltz : (t : ℝ) < (z jf : ℝ) := by rwa [hzz j hj] at hlt
    have hlowz : ∀ i : Fin m, i < jf → (z i : ℝ) < (t : ℝ) := by
      intro i hi
      rw [← hzz (i : ℕ) i.isLt]
      exact hlow _ (Fin.lt_def.mp hi)
    set w : Fin m → X := Function.update z jf t with hwdef
    have hwj : w jf = t := by rw [hwdef, Function.update_self]
    have hwne : ∀ i : Fin m, i ≠ jf → w i = z i := fun i hi => by
      rw [hwdef, Function.update_of_ne hi]
    have hwval : ∀ i, g (w i) = g (z i) := by
      intro i
      by_cases h : i = jf
      · rw [h, hwj, hgtz]
      · rw [hwne i h]
    have hwS : w ∈ S := by
      refine ⟨fun a b hab => ?_, fun i => ?_, ?_⟩
      · by_cases ha : a = jf
        · by_cases hb : b = jf
          · rw [ha, hb]
          · rw [ha, hwj, hwne b hb]
            exact le_trans hltz.le (hzmono jf b (ha ▸ hab))
        · by_cases hb : b = jf
          · rw [hwne a ha, hb, hwj]
            exact (hlowz a (lt_of_le_of_ne (hb ▸ hab) ha)).le
          · rw [hwne a ha, hwne b hb]
            exact hzmono a b hab
      · rw [hwval i, hwval 0, hzval i]
      · change |g (w 0)| = ‖g‖
        rw [hwval 0]
        exact hznorm'
    have hsumlt : ∑ i, (w i : ℝ) < ∑ i, (z i : ℝ) := by
      have h2 : ∑ i, ((w i : ℝ) - (z i : ℝ)) = (t : ℝ) - (z jf : ℝ) := by
        rw [Finset.sum_eq_single jf]
        · rw [hwj]
        · intro i _ hi
          rw [hwne i hi]
          ring
        · intro h
          exact absurd (Finset.mem_univ jf) h
      rw [Finset.sum_sub_distrib] at h2
      linarith
    exact absurd (isMinOn_iff.mp hzmin w hwS) (not_le.mpr hsumlt)
  -- maximality: the alternation extends neither to the left nor to the right
  have hzcval : ∀ i : Fin m, g (z i) = (-1) ^ (i : ℕ) * g (z 0) := hzval
  have hNoLeft : ∀ t : X, g t = -g (zz 0) → (t : ℝ) < (zz 0 : ℝ) → False := by
    intro t hgt hlt
    refine hmmax (m + 1) (by omega) ?_
    refine equioscillates_succ_of_forall_lt (w := z) (fun a b hab => hzstrict a b hab)
      (c := g (z 0)) hznorm hzcval (t := t) (fun i => ?_) ?_
    · refine lt_of_lt_of_le (by rwa [hzz0] at hlt) ?_
      exact hzmono 0 i (Fin.zero_le i)
    · rwa [hzz0] at hgt
  have hNoRight : ∀ t : X, g t = (-1) ^ m * g (zz 0) →
      (zz (m - 1) : ℝ) < (t : ℝ) → False := by
    intro t hgt hgtlt
    refine hmmax (m + 1) (by omega) ?_
    refine equioscillates_succ_of_forall_gt (w := z) (fun a b hab => hzstrict a b hab)
      (c := g (z 0)) hznorm hzcval (t := t) (fun i => ?_) ?_
    · refine lt_of_le_of_lt ?_ hgtlt
      rw [hzz (m - 1) (by omega)]
      exact hzmono i _ (by simp [Fin.le_def]; omega)
    · rwa [hzz0] at hgt
  -- the last extreme point of each sign block, and the separators
  have hex : ∀ j : ℕ, ∃ u : X, j + 1 < m →
      ((g u = g (zz j) ∧ (zz j : ℝ) ≤ (u : ℝ) ∧ (u : ℝ) ≤ (zz (j + 1) : ℝ)) ∧
        ∀ v : X, (g v = g (zz j) ∧ (zz j : ℝ) ≤ (v : ℝ) ∧ (v : ℝ) ≤ (zz (j + 1) : ℝ)) →
          (v : ℝ) ≤ (u : ℝ)) := by
    intro j
    by_cases hj : j + 1 < m
    · have hset : IsClosed {u : X | g u = g (zz j) ∧ (zz j : ℝ) ≤ (u : ℝ) ∧
          (u : ℝ) ≤ (zz (j + 1) : ℝ)} := by
        refine IsClosed.inter (isClosed_eq g.continuous continuous_const) ?_
        exact IsClosed.inter (isClosed_le continuous_const continuous_subtype_val)
          (isClosed_le continuous_subtype_val continuous_const)
      have hne : {u : X | g u = g (zz j) ∧ (zz j : ℝ) ≤ (u : ℝ) ∧
          (u : ℝ) ≤ (zz (j + 1) : ℝ)}.Nonempty :=
        ⟨zz j, rfl, le_rfl, hzzmono j (j + 1) (by omega) hj⟩
      obtain ⟨u, hu, hmax⟩ := hset.isCompact.exists_isMaxOn hne
        continuous_subtype_val.continuousOn
      exact ⟨u, fun _ => ⟨hu, fun v hv => hmax hv⟩⟩
    · exact ⟨zz 0, fun h => absurd h hj⟩
  choose a ha using hex
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℝ, ∀ j, y j = ((a j : ℝ) + (zz (j + 1) : ℝ)) / 2 :=
    ⟨_, fun _ => rfl⟩
  have haval : ∀ j, j + 1 < m → g (a j) = g (zz j) := fun j hj => (ha j hj).1.1
  have halow : ∀ j, j + 1 < m → (zz j : ℝ) ≤ (a j : ℝ) := fun j hj => (ha j hj).1.2.1
  have hahigh : ∀ j, j + 1 < m → (a j : ℝ) ≤ (zz (j + 1) : ℝ) := fun j hj => (ha j hj).1.2.2
  have halt : ∀ j, j + 1 < m → (a j : ℝ) < (zz (j + 1) : ℝ) := by
    intro j hj
    refine lt_of_le_of_ne (hahigh j hj) fun heq => ?_
    have h1 : a j = zz (j + 1) := Subtype.ext heq
    have h2 : g (zz (j + 1)) = g (zz j) := by rw [← h1, haval j hj]
    rw [hzzval (j + 1) hj, hzzval j (by omega), pow_succ] at h2
    have hu : ((-1 : ℝ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [mul_assoc] at h2
    exact hzzne (by linarith [mul_left_cancel₀ hu h2])
  have hyl : ∀ j, j + 1 < m → (a j : ℝ) < y j := fun j hj => by
    rw [hy j]; linarith [halt j hj]
  have hyr : ∀ j, j + 1 < m → y j < (zz (j + 1) : ℝ) := fun j hj => by
    rw [hy j]; linarith [halt j hj]
  have hymono : ∀ i j, i < j → j + 1 < m → y i < y j := by
    intro i j hij hj
    calc y i < (zz (i + 1) : ℝ) := hyr i (by omega)
      _ ≤ (a j : ℝ) := le_trans (hzzmono (i + 1) j (by omega) (by omega)) (halow j hj)
      _ < y j := hyl j hj
  -- no separator is an extreme point
  have hyne : ∀ j, j + 1 < m → ∀ t : X, |g t| = ‖g‖ → (t : ℝ) ≠ y j := by
    intro j hj t htabs heq
    have hgcases : g t = g (zz j) ∨ g t = -g (zz j) := by
      have h1 : |g t| = |g (zz j)| := by rw [htabs, hzzabs j (by omega)]
      rcases abs_eq_abs.mp h1 with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hgcases with hcase | hcase
    · have hmem : g t = g (zz j) ∧ (zz j : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (zz (j + 1) : ℝ) := by
        refine ⟨hcase, ?_, ?_⟩
        · rw [heq]
          exact le_trans (halow j hj) (hyl j hj).le
        · rw [heq]
          exact (hyr j hj).le
      have hle := (ha j hj).2 t hmem
      rw [heq] at hle
      exact absurd hle (not_le.mpr (hyl j hj))
    · refine hMin (j + 1) (by omega) t ?_ ?_ ?_
      · rw [hcase, hzzval (j + 1) (by omega), hzzval j (by omega), pow_succ]
        ring
      · rw [heq]
        exact hyr j hj
      · intro i hi
        rw [heq]
        exact lt_of_le_of_lt (le_trans (hzzmono i j (by omega) (by omega)) (halow j hj))
          (hyl j hj)
  -- the sign of the candidate polynomial matches the sign of the error at every extreme point
  have hmain : ∀ t : X, |g t| = ‖g‖ →
      0 < g t * (g (zz 0) * ∏ j ∈ Finset.range (m - 1), (y j - (t : ℝ))) := by
    intro t htabs
    set Tf : Finset ℕ := (Finset.range (m - 1)).filter (fun j => y j < (t : ℝ)) with hTf
    set J : ℕ := Tf.card with hJdef
    have hJle : J ≤ m - 1 := by
      rw [hJdef, hTf]
      exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])
    have hdown : ∀ j ∈ Tf, ∀ i, i ≤ j → i ∈ Tf := by
      intro j hj i hij
      rw [hTf, Finset.mem_filter, Finset.mem_range] at hj ⊢
      refine ⟨by omega, ?_⟩
      rcases eq_or_lt_of_le hij with rfl | hlt
      · exact hj.2
      · exact lt_trans (hymono i j hlt (by omega)) hj.2
    have hsub : Tf ⊆ Finset.range J := by
      intro j hj
      rw [Finset.mem_range]
      by_contra hcon2
      push Not at hcon2
      have hsub2 : Finset.range (j + 1) ⊆ Tf := fun i hi =>
        hdown j hj i (by have := Finset.mem_range.mp hi; omega)
      have hcard := Finset.card_le_card hsub2
      rw [Finset.card_range] at hcard
      omega
    have hTfeq : Tf = Finset.range J :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range])
    have hJ : ∀ j, j < m - 1 → (y j < (t : ℝ) ↔ j < J) := by
      intro j hj
      constructor
      · intro h
        have hmem : j ∈ Tf := by
          rw [hTf, Finset.mem_filter, Finset.mem_range]
          exact ⟨hj, h⟩
        rw [hTfeq, Finset.mem_range] at hmem
        exact hmem
      · intro h
        have hmem : j ∈ Finset.range J := Finset.mem_range.mpr h
        rw [← hTfeq, hTf, Finset.mem_filter] at hmem
        exact hmem.2
    -- the error has the sign of the `J`-th node at `t`
    have hsign : g t = g (zz J) := by
      by_contra hcon2
      have hopp : g t = -g (zz J) := by
        have h1 : |g t| = |g (zz J)| := by rw [htabs, hzzabs J (by omega)]
        rcases abs_eq_abs.mp h1 with h | h
        · exact absurd h hcon2
        · exact h
      rcases lt_trichotomy ((t : ℝ)) ((zz J : ℝ)) with hlt | heq | hgt
      · rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
        · refine hNoLeft t ?_ ?_
          · rw [hopp, hJ0]
          · rw [← hJ0]
            exact hlt
        · have hj1 : (J - 1) + 1 = J := by omega
          have hjm : (J - 1) + 1 < m := by omega
          have hylt : y (J - 1) < (t : ℝ) := (hJ (J - 1) (by omega)).mpr (by omega)
          have hpowJ : ((-1 : ℝ)) ^ J = -((-1 : ℝ) ^ (J - 1)) := by
            conv_lhs => rw [← hj1]
            rw [pow_succ]
            ring
          have hgeq : g t = g (zz (J - 1)) := by
            rw [hopp, hzzval J (by omega), hzzval (J - 1) (by omega), hpowJ]
            ring
          have hmem : g t = g (zz (J - 1)) ∧ (zz (J - 1) : ℝ) ≤ (t : ℝ) ∧
              (t : ℝ) ≤ (zz ((J - 1) + 1) : ℝ) := by
            refine ⟨hgeq, ?_, ?_⟩
            · exact le_trans (le_trans (halow (J - 1) hjm) (hyl (J - 1) hjm).le) hylt.le
            · rw [hj1]
              exact hlt.le
          exact absurd ((ha (J - 1) hjm).2 t hmem)
            (not_le.mpr (lt_trans (hyl (J - 1) hjm) hylt))
      · have hteq : t = zz J := Subtype.ext heq
        rw [hteq] at hopp
        have hz0 : g (zz J) = 0 := by linarith
        have habs := hzzabs J (by omega)
        rw [hz0, abs_zero] at habs
        exact absurd habs hE.ne
      · rcases eq_or_lt_of_le hJle with hJlast | hJlt
        · refine hNoRight t ?_ ?_
          · have hm' : ((-1 : ℝ)) ^ m = -((-1 : ℝ) ^ (m - 1)) := by
              conv_lhs => rw [show m = (m - 1) + 1 from by omega]
              rw [pow_succ]
              ring
            rw [hopp, hzzval J (by omega), hJlast, hm']
            ring
          · rw [← hJlast]
            exact hgt
        · have hjm : J + 1 < m := by omega
          have htlt : (t : ℝ) < y J := by
            rcases lt_trichotomy ((t : ℝ)) (y J) with h | h | h
            · exact h
            · exact absurd h (hyne J hjm t htabs)
            · exact absurd ((hJ J (by omega)).mp h) (lt_irrefl J)
          refine hMin (J + 1) (by omega) t ?_ ?_ ?_
          · rw [hopp, hzzval (J + 1) (by omega), hzzval J (by omega), pow_succ]
            ring
          · exact lt_trans htlt (hyr J hjm)
          · intro i hi
            exact lt_of_le_of_lt (hzzmono i J (by omega) (by omega)) hgt
    -- the sign of the product of the separators
    have hpos1 : 0 < ∏ j ∈ Tf, ((t : ℝ) - y j) := by
      refine Finset.prod_pos fun j hj => ?_
      rw [hTf, Finset.mem_filter] at hj
      linarith [hj.2]
    have hpos2 : 0 < ∏ j ∈ (Finset.range (m - 1)).filter (fun j => ¬ (y j < (t : ℝ))),
        (y j - (t : ℝ)) := by
      refine Finset.prod_pos fun j hj => ?_
      rw [Finset.mem_filter, Finset.mem_range] at hj
      have hne' : y j ≠ (t : ℝ) := Ne.symm (hyne j (by omega) t htabs)
      rcases lt_trichotomy (y j) ((t : ℝ)) with h | h | h
      · exact absurd h hj.2
      · exact absurd h hne'
      · linarith
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∏ j ∈ Tf, ((t : ℝ) - y j) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∏ j ∈ (Finset.range (m - 1)).filter
        (fun j => ¬ (y j < (t : ℝ))), (y j - (t : ℝ)) := ⟨_, rfl⟩
    have hnegprod : ∏ j ∈ Tf, (y j - (t : ℝ)) = (-1 : ℝ) ^ J * A := by
      rw [hA]
      calc ∏ j ∈ Tf, (y j - (t : ℝ)) = ∏ j ∈ Tf, ((-1 : ℝ) * ((t : ℝ) - y j)) :=
            Finset.prod_congr rfl fun j _ => by ring
        _ = (∏ _j ∈ Tf, (-1 : ℝ)) * ∏ j ∈ Tf, ((t : ℝ) - y j) := Finset.prod_mul_distrib
        _ = (-1 : ℝ) ^ J * ∏ j ∈ Tf, ((t : ℝ) - y j) := by rw [Finset.prod_const, hJdef]
    have hprod : ∏ j ∈ Finset.range (m - 1), (y j - (t : ℝ)) = ((-1 : ℝ) ^ J * A) * B := by
      rw [← hnegprod, hB, hTf]
      exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have hsqpos : 0 < (g (zz 0)) ^ 2 := by
      rcases lt_or_gt_of_ne hzzne with h | h <;> nlinarith
    have hsq : ((-1 : ℝ) ^ J) * ((-1 : ℝ) ^ J) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hsign, hzzval J (by omega), hprod]
    have hexpand : ((-1 : ℝ) ^ J * g (zz 0)) * (g (zz 0) * (((-1 : ℝ) ^ J * A) * B))
        = (((-1 : ℝ) ^ J) * ((-1 : ℝ) ^ J)) * ((g (zz 0)) ^ 2 * (A * B)) := by ring
    rw [hexpand, hsq, one_mul]
    exact mul_pos hsqpos (mul_pos (hA ▸ hpos1) (hB ▸ hpos2))
  -- the improving polynomial
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℝ, Q = Polynomial.C (g (zz 0)) *
      ∏ j ∈ Finset.range (m - 1), (Polynomial.C (y j) - Polynomial.X) := ⟨_, rfl⟩
  have hQnat : Q.natDegree ≤ m - 1 := by
    rw [hQ]
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    have hbound : ∀ j ∈ Finset.range (m - 1),
        ((Polynomial.C (y j) - Polynomial.X : Polynomial ℝ)).natDegree ≤ 1 := by
      intro j _
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      simp
    refine le_trans (Finset.sum_le_sum hbound) ?_
    simp
  have hQdeg : Q.degree ≤ (n : ℕ) := by
    refine le_trans Q.degree_le_natDegree ?_
    exact_mod_cast le_trans hQnat (by omega)
  have hQeval : ∀ t : X, Q.eval (t : ℝ)
      = g (zz 0) * ∏ j ∈ Finset.range (m - 1), (y j - (t : ℝ)) := by
    intro t
    rw [hQ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    simp
  refine ⟨(Polynomial.toContinuousMapOnAlgHom X) Q, mem_polyLE_iff.mpr ⟨Q, hQdeg, fun t => by simp⟩,
    fun t htabs => ?_⟩
  have happ : ((Polynomial.toContinuousMapOnAlgHom X) Q) t = Q.eval (t : ℝ) := by simp
  rw [happ, hQeval t]
  exact hmain t htabs

/-- **Chebyshev's equioscillation theorem, the direction with content**: the error of a best uniform
approximation of degree at most `n` attains `± ‖f - p‖` with alternating signs at `n + 2` increasing
points.

Reference: [han2009theoretical], Theorem 3.3.19; [kress1998numerical], §8.2. -/
theorem IsBestApprox.equioscillates_of_polyLE {X : Set ℝ} [CompactSpace X] [Infinite X] {n : ℕ}
    {f p : C(X, ℝ)} (hp : IsBestApprox (polyLE X n : Set C(X, ℝ)) f p) :
    Equioscillates (f - p) (n + 2) := by
  rcases eq_or_lt_of_le (norm_nonneg (f - p)) with hE | hE
  · obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq X (n + 2)
    refine ⟨1, ⇑(S.orderEmbOfFin hS), Or.inl rfl, fun a b hab => ?_, fun i => ?_⟩
    · exact (S.orderEmbOfFin hS).strictMono hab
    · have hg0 : f - p = 0 := norm_eq_zero.mp hE.symm
      rw [hg0]
      simp
  · by_contra hcon
    obtain ⟨q, hq, hsign⟩ := exists_improving_of_not_equioscillates hE hcon
    obtain ⟨t, ht, hle⟩ := hp.exists_mul_nonpos hE hq
    exact absurd (hsign t ht) (not_lt.mpr hle)

/-- **Chebyshev's equioscillation theorem.** A polynomial of degree at most `n` is a best uniform
approximation of `f` on a compact infinite subset of the line exactly when its error attains `± ‖f -
p‖` with alternating signs at `n + 2` increasing points.

Sufficiency is `isBestApprox_of_equioscillates`, from de la Vallée-Poussin's bound; necessity is
`IsBestApprox.equioscillates_of_polyLE`, the exchange argument.

Reference: [han2009theoretical], Theorem 3.3.19; [kress1998numerical], §8.2. -/
theorem isBestApprox_iff_equioscillates {X : Set ℝ} [CompactSpace X] [Infinite X] {n : ℕ}
    {f p : C(X, ℝ)} (hp : p ∈ polyLE X n) :
    IsBestApprox (polyLE X n : Set C(X, ℝ)) f p ↔ Equioscillates (f - p) (n + 2) :=
  ⟨fun h => h.equioscillates_of_polyLE, isBestApprox_of_equioscillates hp⟩
