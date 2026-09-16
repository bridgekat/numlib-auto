import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Numlib.Algebra.LinearRecurrence
import Numlib.RingTheory.Polynomial.SchurCohn

/-!
# Linear difference equations: the root condition and bounded solutions

The analytic half of the theory of linear difference equations with constant coefficients, as
[quarteroni2000numerical] §11.4 and §11.6 present it for the analysis of multistep methods: the
root condition of a polynomial, and the characterization of the recurrences all of whose solutions
are bounded (the book's Lemma 11.3) or decay (the criterion behind absolute stability). The
algebra — Mathlib's `LinearRecurrence`, the Kronecker fundamental solutions `ψ_j`, the discrete
Duhamel formula and the fundamental system of binomial sequences `n.choose s * r ^ (n - s)` —
is `Numlib/Algebra/LinearRecurrence`; this module adds the norms.

## The root conditions

* `Polynomial.SatisfiesRootCondition P` — every root of `P` lies in the closed unit disc and the
  roots on the unit circle are simple ([quarteroni2000numerical] Definition 11.10, (11.56));
  `Polynomial.satisfiesRootCondition_iff_derivative` is the book's formulation of simplicity,
  `P' (r) ≠ 0`.
* `Polynomial.SatisfiesStrongRootCondition P` — the root condition, and `1` is the only root on
  the unit circle (Definition 11.11, (11.57)).
* `Polynomial.satisfiesRootCondition_of_roots` reads the condition off the multiset of roots, and
  `Polynomial.satisfiesRootCondition_of_isSchurStable` establishes it for `c (X - 1) Q` with `Q`
  Schur stable (`Numlib/RingTheory/Polynomial/SchurCohn`) — the shape of the first characteristic
  polynomial of a consistent multistep method.
* `Polynomial.satisfiesRootCondition_C_mul_iff` — the condition is invariant under multiplication
  by a nonzero constant, which is how the absolute stability region reads it off `Π(z)`.

Both are stated for a polynomial over any normed field; for a real polynomial the condition of
interest is that of its image in `ℂ[X]`, which is how `ODE/Multistep` reads the first
characteristic polynomial `ρ` of a real method.

## Bounded and decaying solutions

The results are stated over an `RCLike` field `𝕜` — the necessity directions need `‖(n : 𝕜)‖ = n`
to see that `n * r ^ n` is unbounded — with the splitting of the characteristic polynomial as an
explicit hypothesis wherever the fundamental system is used; the `ℂ` forms, where it is automatic,
carry the names of the book's statements.

* `LinearRecurrence.bddAbove_range_norm_of_satisfiesRootCondition_of_splits` — under the root
  condition every solution is bounded: each fundamental solution is, since `n.choose s * r ^ (n-s)`
  tends to zero for `‖r‖ < 1` and is `r ^ n` of norm one when `‖r‖ = 1`, `s = 0`.
* `LinearRecurrence.norm_le_of_satisfiesRootCondition` — Lemma 11.3, sufficiency, (11.63): under
  the root condition there is `M > 0` with
  `‖u n‖ ≤ M * (max_{j < k} ‖u j‖ + ∑_{l = k}^{n} ‖φ l‖)` for every solution `u` of the recurrence
  with source `φ`. The proof is the Duhamel formula with a uniform bound on the `ψ_j`
  (`norm_kroneckerSol_le_of_satisfiesRootCondition`).
* `LinearRecurrence.exists_isSolution_not_bddAbove_of_not_satisfiesRootCondition` — Lemma 11.3,
  necessity: when the root condition fails there is an unbounded solution, `r ^ n` for a root with
  `‖r‖ > 1` and `n * r ^ n` for a multiple root on the circle.
* `LinearRecurrence.exists_forall_norm_le_iff_satisfiesRootCondition`,
  `LinearRecurrence.forall_bddAbove_iff_satisfiesRootCondition` — Lemma 11.3 as an equivalence,
  and its homogeneous form (the region `𝒜*` of the book's Remark 11.3).
* `LinearRecurrence.forall_tendsto_zero_iff` — every solution tends to zero iff every root lies
  in the open unit disc.
* `LinearRecurrence.exists_isSolution_real_not_bddAbove_of_not_satisfiesRootCondition` — the real
  form of the necessity: a real recurrence whose complexification violates the root condition has
  an unbounded *real* solution, the real or imaginary part of the complex one. This is the witness
  the necessity halves of the book's Theorems 11.4 and 11.5 need; the book's `ε (r + r̄) ^ n` is not
  a solution.
* `LinearRecurrence.norm_le_of_satisfiesRootCondition_of_le` and
  `LinearRecurrence.norm_le_of_satisfiesRootCondition_smul_of_le` — the two forms of (11.63) that a
  perturbed orbit needs: the hypothesis restricted to the steps `n + k ≤ N` (the recursion of a
  perturbed orbit is controlled only while its nodes stay inside the horizon), and the sequence
  with values in a real normed space (the difference of two orbits). The horizon form extends the
  sequence by `mkSolWith` (`LinearRecurrence.eq_mkSolWith_of_le`); the vector form reduces to the
  complex scalar form through a norming functional (Hahn–Banach, `exists_dual_vector''`).
* `LinearRecurrence.exists_isSolution_norm_ge_of_not_satisfiesRootCondition` and
  `LinearRecurrence.exists_isSolution_real_frequently_le` — the necessity witnesses made
  quantitative: when the root condition fails there is a complex solution with `c n ≤ ‖w n‖` for
  every `n`, and a real solution with `c n ≤ |u n|` for infinitely many `n`. A convergence proof
  that scales the counterexample by `h ≈ T/n` needs this, not mere unboundedness.

Consumers: `ODE/Multistep` (zero-stability, convergence, absolute stability) and the boundary-value
difference equations of chapter 12.
-/

open Filter Finset Polynomial Topology

namespace Polynomial

variable {K : Type*} [NormedField K]

/-- **The root condition** ([quarteroni2000numerical] Definition 11.10, (11.56)): every root of
`P` lies in the closed unit disc, and the roots of modulus one are simple. -/
def SatisfiesRootCondition (P : K[X]) : Prop :=
  ∀ r : K, P.IsRoot r → ‖r‖ ≤ 1 ∧ (‖r‖ = 1 → P.rootMultiplicity r = 1)

/-- The book's formulation of the root condition: a root of modulus one is simple iff it is not a
root of the derivative. -/
theorem satisfiesRootCondition_iff_derivative {P : K[X]} (hP : P ≠ 0) :
    P.SatisfiesRootCondition ↔
      ∀ r : K, P.IsRoot r → ‖r‖ ≤ 1 ∧ (‖r‖ = 1 → ¬ (derivative P).IsRoot r) := by
  refine forall_congr' fun r => forall_congr' fun hr => and_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  have h1 : 0 < P.rootMultiplicity r := (rootMultiplicity_pos hP).2 hr
  have h2 := one_lt_rootMultiplicity_iff_isRoot (t := r) hP
  constructor
  · intro h hd
    have := h2.2 ⟨hr, hd⟩
    omega
  · intro hd
    by_contra hne
    exact hd (h2.1 (by omega)).2

/-- The root condition is invariant under a nonzero constant factor. -/
theorem satisfiesRootCondition_C_mul_iff {c : K} (hc : c ≠ 0) (P : K[X]) :
    (C c * P).SatisfiesRootCondition ↔ P.SatisfiesRootCondition := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  · have hne : C c * P ≠ 0 := mul_ne_zero (C_ne_zero.2 hc) hP
    simp only [Polynomial.SatisfiesRootCondition, IsRoot, eval_mul, eval_C, mul_eq_zero, hc,
      false_or, rootMultiplicity_mul hne, rootMultiplicity_C, zero_add]

/-- **The strong root condition** ([quarteroni2000numerical] Definition 11.11, (11.57)): the root
condition, and `1` is the only root of modulus one. -/
def SatisfiesStrongRootCondition (P : K[X]) : Prop :=
  P.SatisfiesRootCondition ∧ ∀ r : K, P.IsRoot r → r ≠ 1 → ‖r‖ < 1

/-- The strong root condition implies the root condition. -/
theorem SatisfiesStrongRootCondition.satisfiesRootCondition {P : K[X]}
    (h : P.SatisfiesStrongRootCondition) : P.SatisfiesRootCondition :=
  h.1

section Roots

variable [DecidableEq K]

/-- A nonzero polynomial whose roots lie in the closed unit disc, the roots of modulus one being
simple (`count = 1` in the multiset of roots), satisfies the root condition. -/
theorem satisfiesRootCondition_of_roots {P : K[X]} (hP : P ≠ 0) (h1 : ∀ r ∈ P.roots, ‖r‖ ≤ 1)
    (h2 : ∀ r ∈ P.roots, ‖r‖ = 1 → P.roots.count r = 1) : P.SatisfiesRootCondition := by
  intro r hr
  have hmem : r ∈ P.roots := (mem_roots hP).2 hr
  exact ⟨h1 r hmem, fun h => by rw [← count_roots]; exact h2 r hmem h⟩

end Roots

/-- **From Schur stability to the root condition**: if `P = c (X - 1) Q` with `c ≠ 0` and every
complex root of `Q` has modulus `< 1` (`Polynomial.IsSchurStable`), then `P`, read in `ℂ[X]`,
satisfies the root condition — its roots lie in the closed unit disc and the only one of modulus
one is the simple root `1`. -/
theorem satisfiesRootCondition_of_isSchurStable {P Q : ℝ[X]} {c : ℝ} (hc : c ≠ 0)
    (hQ : Q.IsSchurStable) (hP : P = C c * ((X - C 1) * Q)) :
    (P.map (algebraMap ℝ ℂ)).SatisfiesRootCondition := by
  classical
  set Qc : ℂ[X] := Q.map (algebraMap ℝ ℂ) with hQc
  have hQeval : ∀ z : ℂ, Qc.eval z = aeval z Q := fun z => by rw [hQc, eval_map, aeval_def]
  have hQ1 : Qc.eval 1 ≠ 0 := by
    rw [hQeval]
    exact hQ.aeval_ne_zero (by simp)
  have hQ0 : Qc ≠ 0 := fun h0 => hQ1 (by rw [h0]; simp)
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hmap : P.map (algebraMap ℝ ℂ) = C (c : ℂ) * ((X - C 1) * Qc) := by
    rw [hP, hQc]
    simp [Polynomial.map_mul, Polynomial.map_sub]
  have hXne : (X - C 1 : ℂ[X]) ≠ 0 := X_sub_C_ne_zero 1
  have hprod : (X - C 1 : ℂ[X]) * Qc ≠ 0 := mul_ne_zero hXne hQ0
  have hall : C (c : ℂ) * ((X - C 1) * Qc) ≠ 0 := mul_ne_zero (by simpa using hcne) hprod
  rw [hmap]
  intro r hr
  have hfac : (r - 1) * Qc.eval r = 0 := by
    have h := hr
    simp only [IsRoot, eval_mul, eval_C, eval_sub, eval_X] at h
    exact (mul_eq_zero.1 h).resolve_left hcne
  rcases mul_eq_zero.1 hfac with h1 | h2
  · have hr1 : r = 1 := by linear_combination h1
    subst hr1
    refine ⟨by simp, fun _ => ?_⟩
    have hc1 : ¬ (C (c : ℂ)).IsRoot 1 := by simp [IsRoot, hcne]
    have hq1 : ¬ Qc.IsRoot 1 := hQ1
    rw [rootMultiplicity_mul hall, rootMultiplicity_mul hprod,
      rootMultiplicity_eq_zero hc1, rootMultiplicity_eq_zero hq1,
      rootMultiplicity_X_sub_C_self]
  · rw [hQeval] at h2
    have hlt : ‖r‖ < 1 := hQ r h2
    exact ⟨hlt.le, fun h => absurd h hlt.ne⟩

end Polynomial

namespace LinearRecurrence

/-! ### Solutions on a finite horizon -/

/-- A sequence satisfying the inhomogeneous recurrence for the steps `n + k ≤ N` agrees, up to
`N`, with the solution `mkSolWith` of the recurrence whose source is truncated after `N` and whose
initial data are its own. -/
theorem eq_mkSolWith_of_le {R : Type*} [CommSemiring R] (E : LinearRecurrence R) {φ u : ℕ → R}
    {N : ℕ}
    (hu : ∀ n, n + E.order ≤ N →
      u (n + E.order) = ∑ i, E.coeffs i * u (n + i) + φ (n + E.order)) :
    ∀ n ≤ N, u n = E.mkSolWith (fun l => if l ≤ N then φ l else 0) (fun j => u j) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h' : n < E.order
    · exact (E.mkSolWith_eq_init (fun l => if l ≤ N then φ l else 0) (fun j => u j) ⟨n, h'⟩).symm
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + E.order := ⟨n - E.order, by omega⟩
      rw [hu m hn, E.isSolutionWith_mkSolWith _ _ m]
      simp only [hn, ite_true]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ih (m + k) (by have := k.is_lt; omega) (by have := k.is_lt; omega)]

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The fundamental solutions -/

/-- The binomial sequence `n.choose s * r ^ (n - s)` tends to zero when `‖r‖ < 1`. -/
theorem tendsto_chooseMulPow_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) (s : ℕ) :
    Tendsto (chooseMulPow r s) atTop (𝓝 0) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [chooseMulPow_zero_left]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop s] with n hn
    rw [Pi.single_eq_of_ne hn.ne']
  · have hr' : 0 < ‖r‖ := norm_pos_iff.2 hr0
    have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one s
      (by rwa [abs_of_nonneg (norm_nonneg r)])).div_const (‖r‖ ^ s)
    rw [zero_div] at h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ h
    filter_upwards [eventually_ge_atTop s] with n hn
    rw [chooseMulPow_apply, norm_mul, norm_pow, RCLike.norm_natCast, le_div_iff₀ (by positivity),
      mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
    gcongr
    exact_mod_cast Nat.choose_le_pow n s

/-- The binomial sequences are bounded when `‖r‖ < 1`. -/
theorem bddAbove_range_norm_chooseMulPow_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) (s : ℕ) :
    BddAbove (Set.range fun n => ‖chooseMulPow r s n‖) :=
  ((tendsto_chooseMulPow_of_norm_lt_one hr s).norm).bddAbove_range

/-- The geometric sequence of a root of modulus one has norm one. -/
theorem norm_chooseMulPow_zero_of_norm_eq_one {r : 𝕜} (hr : ‖r‖ = 1) (n : ℕ) :
    ‖chooseMulPow r 0 n‖ = 1 := by
  simp [hr]

/-- A finite combination of bounded sequences is bounded. -/
theorem bddAbove_range_norm_sum_smul {ι : Type*} [Fintype ι] {c : ι → 𝕜} {v : ι → ℕ → 𝕜}
    (hv : ∀ i, BddAbove (Set.range fun n => ‖v i n‖)) :
    BddAbove (Set.range fun n => ‖(∑ i, c i • v i) n‖) := by
  choose M hM using hv
  refine ⟨∑ i, ‖c i‖ * M i, ?_⟩
  rintro _ ⟨n, rfl⟩
  change ‖(∑ i, c i • v i) n‖ ≤ _
  rw [Finset.sum_apply]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hM i ⟨n, rfl⟩) (norm_nonneg _)

variable (E : LinearRecurrence 𝕜)

/-- Under the root condition every fundamental solution is bounded: for `‖r‖ < 1` it tends to
zero, and for `‖r‖ = 1` the root is simple, so the sequence is `r ^ n`, of norm one. -/
theorem bddAbove_range_norm_fundamentalSol_of_satisfiesRootCondition [DecidableEq 𝕜]
    (hE : E.charPoly.SatisfiesRootCondition) (p : E.RootIndex) :
    BddAbove (Set.range fun n => ‖E.fundamentalSol p n‖) := by
  obtain ⟨r, s⟩ := p
  have hroot : E.charPoly.IsRoot r := by
    have hr := r.2
    rwa [Multiset.mem_toFinset, mem_roots E.charPoly_monic.ne_zero] at hr
  obtain ⟨hle, heq⟩ := hE r hroot
  rcases hle.lt_or_eq with hlt | h1
  · exact bddAbove_range_norm_chooseMulPow_of_norm_lt_one hlt _
  · have hs : (s : ℕ) = 0 := by have := s.is_lt; have := heq h1; omega
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    simp only [fundamentalSol, hs]
    exact (norm_chooseMulPow_zero_of_norm_eq_one h1 n).le

/-- Under the root condition, every solution of a recurrence whose characteristic polynomial
splits is bounded ([quarteroni2000numerical] Lemma 11.3, the homogeneous case): it is a finite
combination of bounded fundamental solutions. -/
theorem bddAbove_range_norm_of_satisfiesRootCondition_of_splits (hs : E.charPoly.Splits)
    (hE : E.charPoly.SatisfiesRootCondition) {u : ℕ → 𝕜} (hu : E.IsSolution u) :
    BddAbove (Set.range fun n => ‖u n‖) := by
  classical
  obtain ⟨c, rfl⟩ := E.exists_eq_sum_smul_fundamentalSol hs hu
  exact bddAbove_range_norm_sum_smul fun p =>
    E.bddAbove_range_norm_fundamentalSol_of_satisfiesRootCondition hE p

/-- Under the root condition, the Kronecker fundamental solutions of a recurrence whose
characteristic polynomial splits are uniformly bounded: there is `M` with `‖ψ_j (n)‖ ≤ M` for all
`j` and `n`. -/
theorem norm_kroneckerSol_le_of_satisfiesRootCondition_of_splits (hs : E.charPoly.Splits)
    (hE : E.charPoly.SatisfiesRootCondition) :
    ∃ M : ℝ, ∀ (j : Fin E.order) (n : ℕ), ‖E.kroneckerSol j n‖ ≤ M := by
  have h : ∀ j : Fin E.order, ∃ M : ℝ, ∀ n, ‖E.kroneckerSol j n‖ ≤ M := fun j => by
    obtain ⟨M, hM⟩ := E.bddAbove_range_norm_of_satisfiesRootCondition_of_splits hs hE
      (E.isSolution_kroneckerSol j)
    exact ⟨M, fun n => hM ⟨n, rfl⟩⟩
  choose M hM using h
  refine ⟨∑ j, max (M j) 0, fun j n => (hM j n).trans ((le_max_left (M j) 0).trans ?_)⟩
  exact single_le_sum (f := fun j => max (M j) 0) (fun j _ => le_max_right _ _) (mem_univ j)

/-! ### Lemma 11.3 -/

/-- **Lemma 11.3, sufficiency** ([quarteroni2000numerical] (11.63)), for a recurrence of positive
order whose characteristic polynomial splits and satisfies the root condition: there is `M > 0`
such that every solution `u` of the recurrence with source `φ` satisfies
`‖u n‖ ≤ M * (max_{j < k} ‖u j‖ + ∑_{l = k}^{n} ‖φ l‖)` for every `n`. The proof is the Duhamel
formula `eq_sum_kroneckerSol_add_sum` with the uniform bound on the Kronecker solutions;
`M = k * M₀ + 1` works. -/
theorem norm_le_of_satisfiesRootCondition_of_splits (hk : 0 < E.order) (hs : E.charPoly.Splits)
    (hE : E.charPoly.SatisfiesRootCondition) :
    ∃ M : ℝ, 0 < M ∧ ∀ φ u : ℕ → 𝕜, E.IsSolutionWith φ u → ∀ n,
      ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖) := by
  obtain ⟨M₀, hM₀⟩ := E.norm_kroneckerSol_le_of_satisfiesRootCondition_of_splits hs hE
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ ⟨0, hk⟩ 0)
  have : Nonempty (Fin E.order) := ⟨⟨0, hk⟩⟩
  refine ⟨E.order * M₀ + 1, by positivity, fun φ u hu n => ?_⟩
  have hsup : ∀ j : Fin E.order, ‖u j‖ ≤ ⨆ j : Fin E.order, ‖u j‖ := fun j =>
    le_ciSup (f := fun j : Fin E.order => ‖u j‖) (Set.finite_range _).bddAbove j
  have hsup0 : 0 ≤ ⨆ j : Fin E.order, ‖u j‖ := (norm_nonneg _).trans (hsup ⟨0, hk⟩)
  have hφ0 : 0 ≤ ∑ l ∈ Icc E.order n, ‖φ l‖ := sum_nonneg fun _ _ => norm_nonneg _
  calc ‖u n‖ = ‖(∑ j : Fin E.order, u j * E.kroneckerSol j n) + ∑ l ∈ Icc E.order n,
        φ l * E.kroneckerSol ⟨E.order - 1, by omega⟩ (n - l + (E.order - 1))‖ := by
        rw [← eq_sum_kroneckerSol_add_sum hk hu n]
    _ ≤ ∑ j : Fin E.order, ‖u j‖ * M₀ + ∑ l ∈ Icc E.order n, ‖φ l‖ * M₀ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (sum_le_sum
          fun j _ => ?_)) ((norm_sum_le _ _).trans (sum_le_sum fun l _ => ?_)))
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hM₀ j n) (norm_nonneg _)
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hM₀ _ _) (norm_nonneg _)
    _ ≤ (E.order * ⨆ j : Fin E.order, ‖u j‖) * M₀ + (∑ l ∈ Icc E.order n, ‖φ l‖) * M₀ := by
        rw [← sum_mul, ← sum_mul]
        gcongr
        refine (sum_le_sum fun j _ => hsup j).trans ?_
        simp
    _ = E.order * M₀ * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖) -
        (E.order - 1) * M₀ * ∑ l ∈ Icc E.order n, ‖φ l‖ := by ring
    _ ≤ E.order * M₀ * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖) := by
        have : (1 : ℝ) ≤ E.order := by exact_mod_cast hk
        nlinarith [mul_nonneg hM₀0 hφ0]
    _ ≤ (E.order * M₀ + 1) * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖) := by
        nlinarith

/-- **Lemma 11.3, necessity**: when the root condition fails, the recurrence has an unbounded
solution — `r ^ n` for a root `r` with `‖r‖ > 1`, and `n * r ^ n` for a multiple root of modulus
one. Over any `RCLike` field, with no splitting hypothesis. -/
theorem exists_isSolution_not_bddAbove_of_not_satisfiesRootCondition
    (h : ¬ E.charPoly.SatisfiesRootCondition) :
    ∃ u : ℕ → 𝕜, E.IsSolution u ∧ ¬ BddAbove (Set.range fun n => ‖u n‖) := by
  simp only [Polynomial.SatisfiesRootCondition, not_forall, not_and] at h
  obtain ⟨r, hr, hr'⟩ := h
  by_cases h1 : 1 < ‖r‖
  · refine ⟨fun n => r ^ n, (E.geom_sol_iff_root_charPoly r).2 hr, ?_⟩
    simp only [norm_pow]
    exact not_bddAbove_of_tendsto_atTop (tendsto_pow_atTop_atTop_of_one_lt h1)
  · obtain ⟨hle, hmult⟩ := hr' (not_lt.1 h1)
    have hpos : 0 < E.charPoly.rootMultiplicity r :=
      (rootMultiplicity_pos E.charPoly_monic.ne_zero).2 hr
    refine ⟨fun n => (n : 𝕜) * r ^ n,
      E.isSolution_mul_pow_of_one_lt_rootMultiplicity (by omega), ?_⟩
    simp only [norm_mul, norm_pow, hle, one_pow, mul_one, RCLike.norm_natCast]
    exact not_bddAbove_of_tendsto_atTop tendsto_natCast_atTop_atTop

/-- The uniform bound (11.63) forces the root condition: the direction of Lemma 11.3 that reads
the estimate on the homogeneous equation, against the unbounded solution of the previous node. -/
theorem satisfiesRootCondition_of_forall_norm_le {M : ℝ}
    (hM : ∀ φ u : ℕ → 𝕜, E.IsSolutionWith φ u → ∀ n,
      ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖)) :
    E.charPoly.SatisfiesRootCondition := by
  by_contra h
  obtain ⟨u, hu, hu'⟩ := E.exists_isSolution_not_bddAbove_of_not_satisfiesRootCondition h
  refine hu' ⟨M * ⨆ j : Fin E.order, ‖u j‖, ?_⟩
  rintro _ ⟨n, rfl⟩
  simpa using hM 0 u ((E.isSolutionWith_zero_iff u).2 hu) n

/-- **Lemma 11.3** as an equivalence, for a recurrence of positive order whose characteristic
polynomial splits: the uniform bound (11.63) holds for some `M > 0` iff the characteristic
polynomial satisfies the root condition. -/
theorem exists_forall_norm_le_iff_satisfiesRootCondition_of_splits (hk : 0 < E.order)
    (hs : E.charPoly.Splits) :
    (∃ M : ℝ, 0 < M ∧ ∀ φ u : ℕ → 𝕜, E.IsSolutionWith φ u → ∀ n,
      ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖)) ↔
      E.charPoly.SatisfiesRootCondition :=
  ⟨fun ⟨_, _, hM⟩ => E.satisfiesRootCondition_of_forall_norm_le hM,
    E.norm_le_of_satisfiesRootCondition_of_splits hk hs⟩

/-- The homogeneous form of Lemma 11.3 (the region `𝒜*` of [quarteroni2000numerical] Remark
11.3), for a recurrence whose characteristic polynomial splits: every solution is bounded iff the
characteristic polynomial satisfies the root condition. -/
theorem forall_bddAbove_iff_satisfiesRootCondition_of_splits (hs : E.charPoly.Splits) :
    (∀ u : ℕ → 𝕜, E.IsSolution u → BddAbove (Set.range fun n => ‖u n‖)) ↔
      E.charPoly.SatisfiesRootCondition := by
  refine ⟨fun h => by_contra fun hE => ?_,
    fun hE u hu => E.bddAbove_range_norm_of_satisfiesRootCondition_of_splits hs hE hu⟩
  obtain ⟨u, hu, hu'⟩ := E.exists_isSolution_not_bddAbove_of_not_satisfiesRootCondition hE
  exact hu' (h u hu)

/-! ### Decay -/

/-- When every root of the characteristic polynomial lies in the open unit disc and the
polynomial splits, every solution tends to zero: each fundamental solution does. -/
theorem tendsto_zero_of_forall_norm_lt_one_of_splits (hs : E.charPoly.Splits)
    (hE : ∀ r : 𝕜, E.charPoly.IsRoot r → ‖r‖ < 1) {u : ℕ → 𝕜} (hu : E.IsSolution u) :
    Tendsto u atTop (𝓝 0) := by
  classical
  obtain ⟨c, rfl⟩ := E.exists_eq_sum_smul_fundamentalSol hs hu
  have : Tendsto (fun n => ∑ p : E.RootIndex, c p • E.fundamentalSol p n) atTop (𝓝 0) := by
    rw [show (0 : 𝕜) = ∑ p : E.RootIndex, c p • (0 : 𝕜) by simp]
    refine tendsto_finsetSum _ fun p _ => (tendsto_chooseMulPow_of_norm_lt_one ?_ _).const_smul _
    obtain ⟨⟨r, hr⟩, s⟩ := p
    rw [Multiset.mem_toFinset, mem_roots E.charPoly_monic.ne_zero] at hr
    exact hE r hr
  refine this.congr fun n => ?_
  simp [Finset.sum_apply]

/-- A root of modulus at least one gives the solution `r ^ n`, which does not tend to zero. -/
theorem exists_isSolution_not_tendsto_zero_of_one_le_norm {r : 𝕜} (hr : E.charPoly.IsRoot r)
    (h1 : 1 ≤ ‖r‖) : ∃ u : ℕ → 𝕜, E.IsSolution u ∧ ¬ Tendsto u atTop (𝓝 0) := by
  refine ⟨fun n => r ^ n, (E.geom_sol_iff_root_charPoly r).2 hr, fun h => ?_⟩
  rw [tendsto_zero_iff_norm_tendsto_zero] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds one_pos)).exists
  simp only [norm_pow] at hn
  exact hn.not_ge (one_le_pow₀ h1)

/-- The decay criterion for a recurrence whose characteristic polynomial splits: every solution
tends to zero iff every root lies in the open unit disc. -/
theorem forall_tendsto_zero_iff_of_splits (hs : E.charPoly.Splits) :
    (∀ u : ℕ → 𝕜, E.IsSolution u → Tendsto u atTop (𝓝 0)) ↔
      ∀ r : 𝕜, E.charPoly.IsRoot r → ‖r‖ < 1 := by
  refine ⟨fun h r hr => by_contra fun h1 => ?_,
    fun hE u hu => E.tendsto_zero_of_forall_norm_lt_one_of_splits hs hE hu⟩
  obtain ⟨u, hu, hu'⟩ := E.exists_isSolution_not_tendsto_zero_of_one_le_norm hr (not_lt.1 h1)
  exact hu' (h u hu)

end RCLike

/-! ### Over the complex numbers -/

section Complex

variable (E : LinearRecurrence ℂ)

/-- Under the root condition, the Kronecker fundamental solutions of a complex recurrence are
uniformly bounded: there is `M` with `‖ψ_j (n)‖ ≤ M` for all `j` and `n`. -/
theorem norm_kroneckerSol_le_of_satisfiesRootCondition (hE : E.charPoly.SatisfiesRootCondition) :
    ∃ M : ℝ, ∀ (j : Fin E.order) (n : ℕ), ‖E.kroneckerSol j n‖ ≤ M :=
  E.norm_kroneckerSol_le_of_satisfiesRootCondition_of_splits (IsAlgClosed.splits _) hE

/-- **Lemma 11.3, sufficiency** ([quarteroni2000numerical] (11.63)) over `ℂ`: for a recurrence of
positive order satisfying the root condition there is `M > 0` such that every solution `u` with
source `φ` satisfies `‖u n‖ ≤ M * (max_{j < k} ‖u j‖ + ∑_{l = k}^{n} ‖φ l‖)`. -/
theorem norm_le_of_satisfiesRootCondition (hk : 0 < E.order)
    (hE : E.charPoly.SatisfiesRootCondition) :
    ∃ M : ℝ, 0 < M ∧ ∀ φ u : ℕ → ℂ, E.IsSolutionWith φ u → ∀ n,
      ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖) :=
  E.norm_le_of_satisfiesRootCondition_of_splits hk (IsAlgClosed.splits _) hE

/-- **Lemma 11.3 on a finite horizon** ([quarteroni2000numerical] (11.63)), over `ℂ`: for a
recurrence of positive order satisfying the root condition there is `M > 0` such that every
sequence `u` satisfying the recurrence with source `φ` for the steps `n + k ≤ N` obeys
`‖u n‖ ≤ M (max_{j<k} ‖u j‖ + ∑_{l=k}^n ‖φ l‖)` for `n ≤ N`. -/
theorem norm_le_of_satisfiesRootCondition_of_le (hk : 0 < E.order)
    (hE : E.charPoly.SatisfiesRootCondition) :
    ∃ M : ℝ, 0 < M ∧ ∀ (N : ℕ) (φ u : ℕ → ℂ),
      (∀ n, n + E.order ≤ N → u (n + E.order) = ∑ i, E.coeffs i * u (n + i) + φ (n + E.order)) →
      ∀ n ≤ N, ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Finset.Icc E.order n, ‖φ l‖) := by
  obtain ⟨M, hM0, hM⟩ := E.norm_le_of_satisfiesRootCondition hk hE
  refine ⟨M, hM0, fun N φ u hu n hn => ?_⟩
  set φ' : ℕ → ℂ := fun l => if l ≤ N then φ l else 0
  have key := hM φ' (E.mkSolWith φ' fun j => u j) (E.isSolutionWith_mkSolWith φ' _) n
  rw [← E.eq_mkSolWith_of_le hu n hn] at key
  refine key.trans (le_of_eq ?_)
  congr 2
  · exact iSup_congr fun j => by rw [E.mkSolWith_eq_init]
  · refine Finset.sum_congr rfl fun l hl => ?_
    simp only [φ', (Finset.mem_Icc.1 hl).2.trans hn, ite_true]

/-- **Lemma 11.3** ([quarteroni2000numerical]) over `ℂ`: for a recurrence of positive order, the
uniform bound (11.63) holds for some `M > 0` iff the characteristic polynomial satisfies the root
condition. -/
theorem exists_forall_norm_le_iff_satisfiesRootCondition (hk : 0 < E.order) :
    (∃ M : ℝ, 0 < M ∧ ∀ φ u : ℕ → ℂ, E.IsSolutionWith φ u → ∀ n,
      ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖)) ↔
      E.charPoly.SatisfiesRootCondition :=
  E.exists_forall_norm_le_iff_satisfiesRootCondition_of_splits hk (IsAlgClosed.splits _)

/-- The homogeneous form of Lemma 11.3 over `ℂ` (the region `𝒜*` of [quarteroni2000numerical]
Remark 11.3): every solution is bounded iff the characteristic polynomial satisfies the root
condition. -/
theorem forall_bddAbove_iff_satisfiesRootCondition :
    (∀ u : ℕ → ℂ, E.IsSolution u → BddAbove (Set.range fun n => ‖u n‖)) ↔
      E.charPoly.SatisfiesRootCondition :=
  E.forall_bddAbove_iff_satisfiesRootCondition_of_splits (IsAlgClosed.splits _)

/-- The decay criterion over `ℂ` (behind the absolute root condition of [quarteroni2000numerical]
§11.6.4): every solution tends to zero iff every root of the characteristic polynomial lies in the
open unit disc. -/
theorem forall_tendsto_zero_iff :
    (∀ u : ℕ → ℂ, E.IsSolution u → Tendsto u atTop (𝓝 0)) ↔
      ∀ r : ℂ, E.charPoly.IsRoot r → ‖r‖ < 1 :=
  E.forall_tendsto_zero_iff_of_splits (IsAlgClosed.splits _)

/-- When the root condition fails there is a complex solution with `‖w n‖ ≥ c n` for all `n`,
`c > 0`. -/
theorem exists_isSolution_norm_ge_of_not_satisfiesRootCondition
    (h : ¬ E.charPoly.SatisfiesRootCondition) :
    ∃ w : ℕ → ℂ, E.IsSolution w ∧ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c * n ≤ ‖w n‖ := by
  simp only [Polynomial.SatisfiesRootCondition, not_forall, not_and] at h
  obtain ⟨r, hr, hr'⟩ := h
  by_cases h1 : 1 < ‖r‖
  · refine ⟨fun n => r ^ n, (E.geom_sol_iff_root_charPoly r).2 hr, ‖r‖ - 1, by linarith,
      fun n => ?_⟩
    rw [norm_pow]
    have := one_add_mul_le_pow (a := ‖r‖ - 1) (by linarith) n
    rw [add_sub_cancel] at this
    linarith
  · obtain ⟨hle, hmult⟩ := hr' (not_lt.1 h1)
    have hpos : 0 < E.charPoly.rootMultiplicity r :=
      (rootMultiplicity_pos E.charPoly_monic.ne_zero).2 hr
    refine ⟨fun n => (n : ℂ) * r ^ n,
      E.isSolution_mul_pow_of_one_lt_rootMultiplicity (by omega), 1, one_pos, fun n => ?_⟩
    simp [norm_pow, hle]

end Complex

/-! ### Real recurrences -/

section Real

variable (E : LinearRecurrence ℝ)

/-- The real part of a solution of the complexification of a real recurrence is a solution. -/
theorem isSolution_re_of_map {w : ℕ → ℂ} (hw : (E.map (algebraMap ℝ ℂ)).IsSolution w) :
    E.IsSolution fun n => (w n).re := by
  intro n
  have := congrArg Complex.re (hw n)
  simp only [map, Complex.coe_algebraMap, Complex.re_sum, Complex.re_ofReal_mul] at this
  exact this

/-- The imaginary part of a solution of the complexification of a real recurrence is a
solution. -/
theorem isSolution_im_of_map {w : ℕ → ℂ} (hw : (E.map (algebraMap ℝ ℂ)).IsSolution w) :
    E.IsSolution fun n => (w n).im := by
  intro n
  have := congrArg Complex.im (hw n)
  simp only [map, Complex.coe_algebraMap, Complex.im_sum, Complex.im_ofReal_mul] at this
  exact this

/-- **Lemma 11.3, necessity, real form**: a real recurrence whose complexification violates the
root condition has an unbounded *real* solution — the real or the imaginary part of the unbounded
complex solution, since `‖w n‖ ≤ |Re (w n)| + |Im (w n)|`. This is the witness that the necessity
halves of [quarteroni2000numerical] Theorems 11.4 and 11.5 need; the book's `ε (r + r̄) ^ n` for a
complex root `r` is not a solution. -/
theorem exists_isSolution_real_not_bddAbove_of_not_satisfiesRootCondition
    (h : ¬ (E.map (algebraMap ℝ ℂ)).charPoly.SatisfiesRootCondition) :
    ∃ u : ℕ → ℝ, E.IsSolution u ∧ ¬ BddAbove (Set.range fun n => |u n|) := by
  obtain ⟨w, hw, hw'⟩ :=
    (E.map (algebraMap ℝ ℂ)).exists_isSolution_not_bddAbove_of_not_satisfiesRootCondition h
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  obtain ⟨A, hA⟩ := hcon _ (E.isSolution_re_of_map hw)
  obtain ⟨B, hB⟩ := hcon _ (E.isSolution_im_of_map hw)
  refine hw' ⟨A + B, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add (hA ⟨n, rfl⟩) (hB ⟨n, rfl⟩))

/-- **A real solution growing at least linearly along a subsequence**: a real recurrence whose
complexification violates the root condition has a real solution `u` with `c n ≤ |u n|` for
infinitely many `n`, for some `c > 0`. -/
theorem exists_isSolution_real_frequently_le
    (h : ¬ (E.map (algebraMap ℝ ℂ)).charPoly.SatisfiesRootCondition) :
    ∃ u : ℕ → ℝ, E.IsSolution u ∧ ∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop, c * n ≤ |u n| := by
  obtain ⟨w, hw, c, hc, hcw⟩ :=
    (E.map (algebraMap ℝ ℂ)).exists_isSolution_norm_ge_of_not_satisfiesRootCondition h
  have hor : ∃ᶠ n in atTop, c / 2 * n ≤ |(w n).re| ∨ c / 2 * n ≤ |(w n).im| := by
    refine Eventually.frequently (Eventually.of_forall fun n => ?_)
    have := (hcw n).trans (Complex.norm_le_abs_re_add_abs_im (w n))
    by_contra hcon
    push Not at hcon
    linarith [hcon.1, hcon.2]
  rcases Filter.frequently_or_distrib.1 hor with H | H
  · exact ⟨_, E.isSolution_re_of_map hw, c / 2, by positivity, H⟩
  · exact ⟨_, E.isSolution_im_of_map hw, c / 2, by positivity, H⟩

/-- **Lemma 11.3 on a finite horizon, for sequences in a normed space**: for a real recurrence of
positive order whose complexification satisfies the root condition, there is `M > 0` such that
every sequence `u` in a real normed space `V` satisfying
`u (n + k) = ∑ α_i • u (n + i) + φ (n + k)` for the steps `n + k ≤ N` obeys
`‖u n‖ ≤ M (max_{j<k} ‖u j‖ + ∑_{l=k}^n ‖φ l‖)` for `n ≤ N`. By the complex scalar case applied
to `g ∘ u` for a norming functional `g` of `u n`. -/
theorem norm_le_of_satisfiesRootCondition_smul_of_le (hk : 0 < E.order)
    (hE : (E.map (algebraMap ℝ ℂ)).charPoly.SatisfiesRootCondition)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ∃ M : ℝ, 0 < M ∧ ∀ (N : ℕ) (φ u : ℕ → V),
      (∀ n, n + E.order ≤ N → u (n + E.order) = ∑ i, E.coeffs i • u (n + i) + φ (n + E.order)) →
      ∀ n ≤ N, ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Finset.Icc E.order n, ‖φ l‖) := by
  obtain ⟨M, hM0, hM⟩ := (E.map (algebraMap ℝ ℂ)).norm_le_of_satisfiesRootCondition_of_le hk hE
  refine ⟨M, hM0, fun N φ u hu n hn => ?_⟩
  obtain ⟨g, hg1, hgx⟩ := exists_dual_vector'' ℝ (u n)
  set v : ℕ → ℂ := fun l => ((g (u l) : ℝ) : ℂ)
  set ψ : ℕ → ℂ := fun l => ((g (φ l) : ℝ) : ℂ)
  have hv : ∀ m, m + (E.map (algebraMap ℝ ℂ)).order ≤ N →
      v (m + (E.map (algebraMap ℝ ℂ)).order) =
        ∑ i, (E.map (algebraMap ℝ ℂ)).coeffs i * v (m + i) +
          ψ (m + (E.map (algebraMap ℝ ℂ)).order) := by
    intro m hm
    simp only [v, ψ, map_order, hu m hm, map_add, map_sum, map_smul, smul_eq_mul]
    push_cast
    rfl
  have key := hM N ψ v hv n hn
  have hvn : ‖v n‖ = ‖u n‖ := by
    simp only [v, hgx, Complex.norm_real, RCLike.ofReal_real_eq_id, id, Real.norm_eq_abs,
      abs_norm]
  have hle : ∀ x : V, ‖((g x : ℝ) : ℂ)‖ ≤ ‖x‖ := fun x => by
    rw [Complex.norm_real]
    exact (g.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) hg1)
  rw [hvn] at key
  refine key.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hM0.le)
  · exact ciSup_mono (Finite.bddAbove_range _) fun j => hle (u j)
  · exact Finset.sum_le_sum fun l _ => hle (φ l)

end Real

end LinearRecurrence
