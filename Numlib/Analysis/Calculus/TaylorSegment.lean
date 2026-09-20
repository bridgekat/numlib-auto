/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.Taylor` (the segment expansion) and
`Mathlib.Algebra.MvPolynomial.Basic` (the polynomial nature of a diagonal multilinear form).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Numlib.Analysis.Calculus.Taylor
import Numlib.RingTheory.MvPolynomial.TotalDegree

/-!
# Taylor's theorem along a segment, with the Lagrange bound

The multivariate Taylor expansion of `f : E → F` at `a` in the direction `w`, obtained by
restricting `f` to the segment `s ↦ a + s • w`, `s ∈ [0, 1]`, and applying the one-dimensional
Lagrange bound `norm_sub_taylorSum_le` of `Numlib/Analysis/Calculus/Taylor` to the curve. The
`k`-th derivative of the restricted function is the `k`-th Fréchet derivative of `f` applied to
`w` in every slot (`hasDerivAt_iteratedFDeriv_segment`), so that the Taylor polynomial of `f` at
`a` of degree `n` reads `∑_{k ≤ n} (1/k!) D^k f(a)[w, …, w]` and the remainder is bounded by
`M ‖w‖^{n+1}/(n+1)!` when `‖D^{n+1} f‖ ≤ M` along the segment
(`norm_sub_taylorSum_segment_le`). The hypothesis is `C^{n+1}` *at each point of the segment*
(`ContDiffAt`), so the statement applies to a function of class `C^{n+1}` on any open set
containing the segment, with the two-sided derivatives `iteratedFDeriv`.

For `f` real-valued and `w = ∑_i c_i w_i` a linear combination of fixed vectors, the Taylor
polynomial is a polynomial of total degree `≤ n` in the coefficients `c`
(`exists_mvPolynomial_taylorSum`), because a multilinear form evaluated on the diagonal of a
linear combination is a polynomial (`ContinuousMultilinearMap.exists_mvPolynomial_apply_sum_smul`,
by expanding multilinearly); on `ι → ℝ` itself the Taylor polynomial at `a` is a polynomial of
total degree `≤ n` in the point (`exists_mvPolynomial_taylorSum_pi`). This is what identifies the
Taylor polynomial of `f` composed with an affine parametrization of a simplex as an element of
`𝒫_n`, which the sup-norm interpolation and quadrature error estimates on a triangle rest on.
-/

open Set
open scoped Nat

section Segment

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The derivative along a segment of an iterated derivative applied to the direction**: if `f`
is `C^{n+1}` at `a + s • w`, then `s ↦ D^n f(a + s • w)[w, …, w]` has derivative
`D^{n+1} f(a + s • w)[w, …, w]` at `s`. -/
theorem hasDerivAt_iteratedFDeriv_segment {f : E → F} {n : ℕ} {a w : E} {s : ℝ}
    (hf : ContDiffAt ℝ (n + 1) f (a + s • w)) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n f (a + s • w) (fun _ => w))
      (iteratedFDeriv ℝ (n + 1) f (a + s • w) (fun _ => w)) s := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) (a + s • w) :=
    hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
  have hseg : HasDerivAt (fun s : ℝ => a + s • w) w s := by
    simpa using ((hasDerivAt_id s).smul_const w).const_add a
  have h1 : HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n f (a + s • w))
      (fderiv ℝ (iteratedFDeriv ℝ n f) (a + s • w) w) s :=
    hd.hasFDerivAt.comp_hasDerivAt s hseg
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F
    (fun _ => w)).hasFDerivAt.comp_hasDerivAt s h1
  exact h2

/-- **Taylor's theorem along a segment, with the Lagrange bound.** If `f : E → F` is `C^{n+1}` at
every point of the segment `a + s • w`, `s ∈ [0, 1]`, and `‖D^{n+1} f‖ ≤ M` along it, then
`‖f(a + w) - ∑_{k ≤ n} (1/k!) D^k f(a)[w, …, w]‖ ≤ M ‖w‖^{n+1}/(n+1)!`. The curve
`s ↦ f(a + s • w)` has the derivative chain `s ↦ D^k f(a + s • w)[w, …, w]`
(`hasDerivAt_iteratedFDeriv_segment`), and `norm_sub_taylorSum_le` bounds its expansion on
`[0, 1]`. -/
theorem norm_sub_taylorSum_segment_le {f : E → F} {n : ℕ} {a w : E} {M : ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (a + s • w))
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (a + s • w)‖ ≤ M) :
    ‖f (a + w) - ∑ k ∈ Finset.range (n + 1),
        ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f a (fun _ => w)‖
      ≤ M * ‖w‖ ^ (n + 1) / (n + 1)! := by
  set Y : ℕ → ℝ → F := fun k s => iteratedFDeriv ℝ k f (a + s • w) (fun _ => w) with hY
  have hchain : ∀ k ≤ n, ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (Y k) (Y (k + 1) s) (Icc 0 1) s :=
    fun k hk s hs => (hasDerivAt_iteratedFDeriv_segment
      ((hf s hs).of_le (by exact_mod_cast Nat.succ_le_succ hk))).hasDerivWithinAt
  have hbound : ∀ s ∈ Icc (0 : ℝ) 1, ‖Y (n + 1) s‖ ≤ M * ‖w‖ ^ (n + 1) := by
    intro s hs
    calc ‖Y (n + 1) s‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f (a + s • w)‖ * ∏ _i : Fin (n + 1), ‖w‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ (n + 1) f (a + s • w)‖ * ‖w‖ ^ (n + 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ M * ‖w‖ ^ (n + 1) := by gcongr; exact hM s hs
  have key := norm_sub_taylorSum_le zero_le_one hchain hbound
  have e0 : Y 0 1 = f (a + w) := by simp [hY]
  have e1 : ∀ k, Y k 0 = iteratedFDeriv ℝ k f a (fun _ => w) := fun k => by simp [hY]
  simp only [e0, e1, sub_zero, one_pow, one_div] at key
  simpa [div_eq_mul_inv] using key

/-- The remainder bound `norm_sub_taylorSum_segment_le` for a function of class `C^{n+1}` on the
whole space, the bound `M` on `‖D^{n+1} f‖` being required along the segment only. -/
theorem ContDiff.norm_sub_taylorSum_segment_le {f : E → F} {n : ℕ} (hf : ContDiff ℝ (n + 1) f)
    {a w : E} {M : ℝ} (hM : ∀ s ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (a + s • w)‖ ≤ M) :
    ‖f (a + w) - ∑ k ∈ Finset.range (n + 1),
        ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f a (fun _ => w)‖
      ≤ M * ‖w‖ ^ (n + 1) / (n + 1)! :=
  _root_.norm_sub_taylorSum_segment_le (fun _ _ => hf.contDiffAt) hM

end Segment

section Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

/-- **A multilinear form on the diagonal of a linear combination is a polynomial in the
coefficients**: for `A` continuous `j`-linear on `E` and vectors `w_i`, `i ∈ ι`, the function
`c ↦ A(∑_i c_i w_i, …, ∑_i c_i w_i)` is `MvPolynomial.eval c q` for a polynomial `q` in the
variables `ι` of total degree at most `j`, namely
`q = ∑_{r : Fin j → ι} A(w_{r 0}, …, w_{r (j-1)}) ∏_l X_{r l}` (multilinear expansion). -/
theorem ContinuousMultilinearMap.exists_mvPolynomial_apply_sum_smul {j : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) (w : ι → E) :
    ∃ q : MvPolynomial ι ℝ, q.totalDegree ≤ j ∧
      ∀ c : ι → ℝ, A (fun _ => ∑ i, c i • w i) = MvPolynomial.eval c q := by
  classical
  refine ⟨∑ r : Fin j → ι, MvPolynomial.C (A fun l => w (r l)) * ∏ l, MvPolynomial.X (r l),
    ?_, fun c => ?_⟩
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun r _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    simp only [MvPolynomial.totalDegree_X, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, le_refl]
  · rw [ContinuousMultilinearMap.map_sum (f := A) (g := fun _ i => c i • w i), _root_.map_sum]
    simp only [_root_.map_mul, MvPolynomial.eval_C, _root_.map_prod, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]

/-- **The Taylor polynomial along a linear parametrization is a polynomial**: for `f : E → ℝ`,
a point `a` and vectors `w_i`, `i ∈ ι`, the degree-`n` Taylor polynomial of `f` at `a`, evaluated
in the direction `∑_i c_i w_i`, is `MvPolynomial.eval c q` for a polynomial `q` of total degree at
most `n` in the coefficients `c`. -/
theorem exists_mvPolynomial_taylorSum {f : E → ℝ} (a : E) (n : ℕ) (w : ι → E) :
    ∃ q : MvPolynomial ι ℝ, q.totalDegree ≤ n ∧ ∀ c : ι → ℝ,
      ∑ k ∈ Finset.range (n + 1),
        ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f a (fun _ => ∑ i, c i • w i)
        = MvPolynomial.eval c q := by
  classical
  have h : ∀ k, ∃ q : MvPolynomial ι ℝ, q.totalDegree ≤ k ∧
      ∀ c : ι → ℝ, iteratedFDeriv ℝ k f a (fun _ => ∑ i, c i • w i) = MvPolynomial.eval c q :=
    fun k => (iteratedFDeriv ℝ k f a).exists_mvPolynomial_apply_sum_smul w
  choose q hq using h
  refine ⟨∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) • q k, ?_, fun c => ?_⟩
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun k hk => ?_)
    exact (MvPolynomial.totalDegree_smul_le _ _).trans
      ((hq k).1.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  · simp only [map_sum, MvPolynomial.smul_eval, (hq _).2, smul_eq_mul]

/-- **The Taylor polynomial of a function on `ι → ℝ` is a polynomial in the point**: for
`f : (ι → ℝ) → ℝ` and `a : ι → ℝ`, the degree-`n` Taylor polynomial of `f` at `a`,
`y ↦ ∑_{k ≤ n} (1/k!) D^k f(a)[y - a, …, y - a]`, is `MvPolynomial.eval y q` for a polynomial `q`
of total degree at most `n` — `exists_mvPolynomial_taylorSum` along the standard basis, followed
by the substitution `X_i ↦ X_i - a_i`, which does not raise the total degree. -/
theorem exists_mvPolynomial_taylorSum_pi {f : (ι → ℝ) → ℝ} (a : ι → ℝ) (n : ℕ) :
    ∃ q : MvPolynomial ι ℝ, q.totalDegree ≤ n ∧ ∀ y : ι → ℝ,
      ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f a (fun _ => y - a)
        = MvPolynomial.eval y q := by
  classical
  obtain ⟨q, hqdeg, hq⟩ :=
    exists_mvPolynomial_taylorSum (f := f) a n fun i : ι => (Pi.single i 1 : ι → ℝ)
  refine ⟨MvPolynomial.bind₁ (fun i => MvPolynomial.X i - MvPolynomial.C (a i)) q, ?_, fun y => ?_⟩
  · refine (MvPolynomial.totalDegree_bind₁_le_of_totalDegree_le_one (fun i => ?_) q).trans hqdeg
    exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (MvPolynomial.totalDegree_X i).le
  · have e : (∑ i, (y - a) i • (Pi.single i 1 : ι → ℝ)) = y - a := by
      simp only [← Pi.single_smul, smul_eq_mul, mul_one, Finset.univ_sum_single]
    rw [← e, hq]
    change MvPolynomial.eval₂Hom (RingHom.id ℝ) _ q
      = MvPolynomial.eval₂Hom (RingHom.id ℝ) y (MvPolynomial.bind₁ _ q)
    rw [MvPolynomial.eval₂Hom_bind₁]
    congr 2
    funext i
    simp

end Polynomial
