import Numlib.Analysis.InnerProductSpace.WeakCompactness
import Numlib.Variational.Inequality.Basic

/-!
# Numerical approximation of elliptic variational inequalities

An *approximation* of the elliptic variational inequality over `K` is the same inequality over
another set `K_h`: no new notion of discrete solution is needed, and unique solvability of the
discrete problem is `existsUnique_isVariationalInequalitySolution` again.  `K_h` need not be
contained in `K`.

Everything here rests on one inequality.  Write

  `R j' v w = ⟪A u, v - w⟫ + j' v - j' w - ⟪f, v - w⟫`

for the residual of the continuous solution `u`, measured with the functional `j'`.  If `u` solves
the inequality over `K` with `j` and `u_h` solves it over `K_h` with `j_h`, then for every `v ∈ K`
and `v_h ∈ K_h`

  `c ‖u - u_h‖² ≤ R j v u_h + R j_h v_h u + ⟪A u - A u_h, u - v_h⟫`,

by adding the two inequalities to the strong monotonicity inequality; bounding the last term by
Cauchy–Schwarz, Lipschitz continuity and Young's inequality turns it into

  `(c/2) ‖u - u_h‖² ≤ R j v u_h + R j v_h u + (L²/(2c)) ‖u - v_h‖²`,

which is `norm_sub_le_of_isVariationalInequalitySolution`, [falk1974error] generalized Céa lemma.
It is pure algebra: no closedness, no convexity, no topology and no limit.  Everything else in the
module is a specialization.

* `norm_sub_le_of_isVariationalInequalitySolution_of_subset`: for an *internal* approximation, `K_h
  ⊆ K`, the choice `v = u_h` kills the first residual.
* `tendsto_of_isVariationalInequalitySolution_of_subset`: hence internal approximations converge as
  soon as the constraint sets approximate `K` pointwise and `j` is continuous on `K`.  **No weak
  compactness is used**, which is why this and not the external theorem is the statement a
  finite-element analysis should cite.
* `tendsto_of_isVariationalInequalitySolution`: the general external case, where the discrete sets
  are not inside `K`.  This one does need weak compactness — a bounded sequence has a weakly
  convergent subsequence, whose limit lies in `K` by hypothesis and solves the continuous inequality
  by Minty's lemma, which is stable under weak limits precisely because it evaluates the operator at
  the *test* point.
* `norm_sub_le_of_isVariationalInequalitySolution_of_le`: replacing `j` on the discrete set by a
  larger `j_h` costs one insertion of `j u_h ≤ j_h u_h`.
* `norm_sub_le_of_regularization`: two problems on the whole space whose functionals differ by `c₁
  ε` have solutions within `√(2 c₁ ε / c)`.

The bounds are stated squared, as the proofs establish them, rather than as the book's `‖u - u_h‖ ≤
C inf (‖u - v_h‖ + |R v_h u|^{1/2})`: the infima follow by `le_ciInf` and the square root by
`Real.sqrt_le_sqrt` together with `√(x + y) ≤ √x + √y`, and neither step belongs in the statement of
the estimate.

The material is Section 11.4 of [han2009theoretical] — Theorems 11.4.1, 11.4.2 and 11.4.7 and
Exercises 11.4.2 and 11.4.3 — and the error bound is due to [falk1974error].
-/

open Filter Set Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The algebraic core -/

section Core

variable {A : V → V} {j jh : V → ℝ} {f : V} {K Kh : Set V} {c L : ℝ} {u uh v vh : V}

/-- **The core estimate.**  Adding the two variational inequalities — the continuous one tested at
`v ∈ K` and the discrete one tested at `v_h ∈ K_h` — to the strong monotonicity inequality between
the two solutions leaves the cross term `⟪A u - A u_h, u - v_h⟫` and the two residuals of the
continuous solution.  Nothing but bilinearity is used, and the two problems may carry different
functionals. -/
private theorem varIneq_core (hmono : IsStronglyMonotoneWith ℝ A c)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : IsVariationalInequalitySolution A jh f Kh uh) (hv : v ∈ K) (hvh : vh ∈ Kh) :
    c * ‖u - uh‖ ^ 2 ≤
      (inner ℝ (A u) (v - uh) + j v - jh uh - inner ℝ f (v - uh))
        + (inner ℝ (A u) (vh - u) + jh vh - j u - inner ℝ f (vh - u))
        + inner ℝ (A u - A uh) (u - vh) := by
  have hm := hmono u uh
  have h1 := hu.2 v hv
  have h2 := huh.2 vh hvh
  simp only [RCLike.re_to_real, inner_sub_left, inner_sub_right] at hm h1 h2 ⊢
  linarith

/-- Young's inequality in the shape [falk1974error] lemma needs: `c p² ≤ R + M p q` with `M² ≤ L²`
gives `(c/2) p² ≤ R + (L²/(2c)) q²`. -/
private theorem sq_le_of_le_add_mul {c M Lr p q R : ℝ} (hc : 0 < c) (hML : M ^ 2 ≤ Lr ^ 2)
    (h : c * p ^ 2 ≤ R + M * p * q) : c / 2 * p ^ 2 ≤ R + Lr ^ 2 / (2 * c) * q ^ 2 := by
  have h2c : (0 : ℝ) < 2 * c := by linarith
  rw [← sub_nonneg]
  have hid : R + Lr ^ 2 / (2 * c) * q ^ 2 - c / 2 * p ^ 2
      = (2 * c * R + Lr ^ 2 * q ^ 2 - c ^ 2 * p ^ 2) / (2 * c) := by
    field_simp
  rw [hid]
  refine div_nonneg ?_ h2c.le
  nlinarith [sq_nonneg (c * p - M * q), mul_le_mul_of_nonneg_left h h2c.le,
    mul_le_mul_of_nonneg_right hML (sq_nonneg q)]

/-- The cross term of the core estimate, bounded by Cauchy–Schwarz and Lipschitz continuity. -/
private theorem inner_sub_apply_le (hlip : LipschitzWith L.toNNReal A) (x y z : V) :
    inner ℝ (A x - A y) z ≤ (L.toNNReal : ℝ) * ‖x - y‖ * ‖z‖ := by
  refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  simpa only [dist_eq_norm] using hlip.dist_le_mul x y

/-- **[falk1974error] generalized Céa lemma.**  Let `u` solve the variational inequality over `K`
and let `u_h` solve it over `K_h`, with the same strongly monotone Lipschitz operator, the same
datum and the same convex term.  Then for every `v ∈ K` and every `v_h ∈ K_h`

  `(c/2) ‖u - u_h‖² ≤ R v u_h + R v_h u + (L²/(2c)) ‖u - v_h‖²`,

where `R v w = ⟪A u, v - w⟫ + j v - j w - ⟪f, v - w⟫` is the residual of the *continuous* solution,
`c` its strong monotonicity constant and `L` its Lipschitz constant.

Purely algebraic: no closedness, convexity, topology or limit is used, and `K_h` need not meet `K`.
For a variational equation — `K` a subspace, `j = 0`, `K_h ⊆ K` — both residuals vanish and this is
Céa's lemma.

[han2009theoretical], Theorem 11.4.2 and (11.4.7). -/
theorem norm_sub_le_of_isVariationalInequalitySolution (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith L.toNNReal A)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : IsVariationalInequalitySolution A j f Kh uh) (hv : v ∈ K) (hvh : vh ∈ Kh) :
    c / 2 * ‖u - uh‖ ^ 2 ≤
      (inner ℝ (A u) (v - uh) + j v - j uh - inner ℝ f (v - uh))
        + (inner ℝ (A u) (vh - u) + j vh - j u - inner ℝ f (vh - u))
        + L ^ 2 / (2 * c) * ‖u - vh‖ ^ 2 := by
  refine sq_le_of_le_add_mul (M := (L.toNNReal : ℝ)) hc ?_ ?_
  · rcases le_or_gt 0 L with hL | hL
    · rw [Real.coe_toNNReal L hL]
    · rw [Real.toNNReal_of_nonpos hL.le]
      simpa using sq_nonneg L
  · exact (varIneq_core hmono hu huh hv hvh).trans
      (by linarith [inner_sub_apply_le hlip u uh (u - vh)])

/-- **The internal-approximation form of [falk1974error] lemma.**  When the discrete solution lies
in `K` — in particular when `K_h ⊆ K` — the first residual of
`norm_sub_le_of_isVariationalInequalitySolution` vanishes, at `v = u_h`, and only the residual at
the discrete test point remains:

  `(c/2) ‖u - u_h‖² ≤ R v_h u + (L²/(2c)) ‖u - v_h‖²`.

[han2009theoretical], the display following Theorem 11.4.2. -/
theorem norm_sub_le_of_isVariationalInequalitySolution_of_subset (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith L.toNNReal A)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : IsVariationalInequalitySolution A j f Kh uh) (huhK : uh ∈ K) (hvh : vh ∈ Kh) :
    c / 2 * ‖u - uh‖ ^ 2 ≤
      (inner ℝ (A u) (vh - u) + j vh - j u - inner ℝ f (vh - u))
        + L ^ 2 / (2 * c) * ‖u - vh‖ ^ 2 := by
  have h := norm_sub_le_of_isVariationalInequalitySolution hc hmono hlip hu huh huhK hvh
  simpa using h

/-- **[han2009theoretical], Theorem 11.4.7.**  A method that replaces the convex term `j` on the
discrete set by a *larger* functional `j_h` — the property enjoyed by the numerical-integration
construction of the book's (11.4.28) — obeys the same estimate with the residual measured by `j_h`:

  `(c/2) ‖u - u_h‖² ≤ R_h v_h u + (L²/(2c)) ‖u - v_h‖²`, `R_h v_h u = ⟪A u, v_h - u⟫ + j_h v_h - j u
  - ⟪f, v_h - u⟫`.

The algebra is [falk1974error], with the single inequality `j u_h ≤ j_h u_h` inserted at `v = u_h`.
-/
theorem norm_sub_le_of_isVariationalInequalitySolution_of_le (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith L.toNNReal A)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : IsVariationalInequalitySolution A jh f Kh uh) (huhK : uh ∈ K)
    (hjle : j uh ≤ jh uh) (hvh : vh ∈ Kh) :
    c / 2 * ‖u - uh‖ ^ 2 ≤
      (inner ℝ (A u) (vh - u) + jh vh - j u - inner ℝ f (vh - u))
        + L ^ 2 / (2 * c) * ‖u - vh‖ ^ 2 := by
  refine sq_le_of_le_add_mul (M := (L.toNNReal : ℝ)) hc ?_ ?_
  · rcases le_or_gt 0 L with hL | hL
    · rw [Real.coe_toNNReal L hL]
    · rw [Real.toNNReal_of_nonpos hL.le]
      simpa using sq_nonneg L
  · have hcore := varIneq_core hmono hu huh huhK hvh
    simp only [sub_self, inner_zero_right] at hcore
    linarith [inner_sub_apply_le hlip u uh (u - vh)]

/-- **[han2009theoretical], Exercise 11.4.3 and (11.4.20).**  If a regularized functional satisfies
`|j_ε v - j v| ≤ c₁ ε` everywhere, then the solution of the regularized inequality on the whole
space is within `√(2 c₁ ε / c)` of the solution of the original one: the a priori bound with
exponent `β = 1/2`.

Both residuals of the core estimate are bounded by `c₁ ε` and its cross term vanishes, at `v = u_ε`
and `v_h = u`, so neither Lipschitz continuity nor Young's inequality is used and the constant is
the sharp one. -/
theorem norm_sub_le_of_regularization {jeps : V → ℝ} {c₁ ε : ℝ} (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c)
    (hu : IsVariationalInequalitySolution A j f univ u)
    (hueps : IsVariationalInequalitySolution A jeps f univ uh)
    (hreg : ∀ w, |jeps w - j w| ≤ c₁ * ε) : ‖u - uh‖ ≤ Real.sqrt (2 * c₁ * ε / c) := by
  have hcore := varIneq_core hmono hu hueps (mem_univ uh) (mem_univ u)
  simp only [sub_self, inner_zero_right] at hcore
  have h1 : j uh - jeps uh ≤ c₁ * ε := by
    have := abs_le.1 (hreg uh)
    linarith [this.1]
  have h2 : jeps u - j u ≤ c₁ * ε := by
    have := abs_le.1 (hreg u)
    linarith [this.2]
  have hsq : ‖u - uh‖ ^ 2 ≤ 2 * c₁ * ε / c := by
    rw [le_div_iff₀ hc]
    nlinarith
  calc ‖u - uh‖ = Real.sqrt (‖u - uh‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * c₁ * ε / c) := Real.sqrt_le_sqrt hsq

end Core

/-- The part of [falk1974error] bound that does not see the discrete solution — the residual of the
continuous solution at the approximating point, together with the Young term — tends to zero along
any sequence `w n → u` on which the values of `j` converge.  Both convergence theorems below run the
same argument on it, differing only in how they get `hjw`: the internal one from continuity of `j`
on `K`, the external one from continuity on the whole space. -/
private theorem tendsto_falk_majorant {A : V → V} {j : V → ℝ} {f u : V} {c L : ℝ} {w : ℕ → V}
    (hw : Tendsto w atTop (𝓝 u)) (hjw : Tendsto (fun n => j (w n)) atTop (𝓝 (j u))) :
    Tendsto (fun n => (inner ℝ (A u) (w n - u) + j (w n) - j u - inner ℝ f (w n - u))
      + L ^ 2 / (2 * c) * ‖u - w n‖ ^ 2) atTop (𝓝 0) := by
  have hwu : Tendsto (fun n => w n - u) atTop (𝓝 0) := by
    simpa using hw.sub (tendsto_const_nhds (x := u))
  have hinner : ∀ y : V, Tendsto (fun n => inner ℝ y (w n - u)) atTop (𝓝 0) := fun y => by
    have hcont : Continuous fun x : V => inner ℝ y x :=
      continuous_inner.comp (continuous_const.prodMk continuous_id)
    simpa [Function.comp_def] using (hcont.tendsto (0 : V)).comp hwu
  have hnormw : Tendsto (fun n => ‖u - w n‖ ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ‖u - w n‖) atTop (𝓝 0) := by
      have h := (tendsto_const_nhds (x := u) (f := atTop (α := ℕ))).sub hw
      simpa using h.norm
    simpa using h1.pow 2
  have h := (((hinner (A u)).add hjw).sub (tendsto_const_nhds (x := j u))).sub (hinner f)
  simpa using h.add (hnormw.const_mul (L ^ 2 / (2 * c)))

/-! ### Convergence of internal approximations -/

section Internal

variable {A : V → V} {j : V → ℝ} {f : V} {K : Set V} {Kh : ℕ → Set V} {c L : ℝ} {u : V}
  {uh : ℕ → V}

/-- **Convergence of internal approximations.** [han2009theoretical], Exercise 11.4.2.  Let `K_h n ⊆
K` be nonempty sets whose points approximate `u` — there is a sequence `w n ∈ K_h n` with `w n → u`
— and let `j` be continuous on `K`.  Then the discrete solutions converge to `u` in norm.

Straight from `norm_sub_le_of_isVariationalInequalitySolution_of_subset`: the residual `R (w n) u`
tends to `0` along the approximating sequence, and so does `‖u - w n‖`.  **No weak compactness is
used**, which is what makes this, and not the external Theorem 11.4.1, the statement a
finite-element analysis should cite. -/
theorem tendsto_of_isVariationalInequalitySolution_of_subset (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith L.toNNReal A)
    (hsub : ∀ n, Kh n ⊆ K) (hjc : ContinuousOn j K)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : ∀ n, IsVariationalInequalitySolution A j f (Kh n) (uh n))
    {w : ℕ → V} (hwmem : ∀ n, w n ∈ Kh n) (hw : Tendsto w atTop (𝓝 u)) :
    Tendsto uh atTop (𝓝 u) := by
  set B : ℕ → ℝ := fun n => (inner ℝ (A u) (w n - u) + j (w n) - j u - inner ℝ f (w n - u))
    + L ^ 2 / (2 * c) * ‖u - w n‖ ^ 2 with hB
  have hbound : ∀ n, c / 2 * ‖u - uh n‖ ^ 2 ≤ B n := fun n =>
    norm_sub_le_of_isVariationalInequalitySolution_of_subset hc hmono hlip hu (huh n)
      (hsub n (huh n).1) (hwmem n)
  -- the majorant tends to zero
  have hjw : Tendsto (fun n => j (w n)) atTop (𝓝 (j u)) := by
    have hwK : Tendsto w atTop (𝓝[K] u) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w hw
        (Eventually.of_forall fun n => hsub n (hwmem n))
    simpa [Function.comp_def] using (hjc u hu.1).tendsto.comp hwK
  have hBzero : Tendsto B atTop (𝓝 0) := by
    rw [hB]
    exact tendsto_falk_majorant hw hjw
  -- hence so does the error
  have hzero : Tendsto (fun n => ‖u - uh n‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_)
      (by simpa using hBzero.const_mul (2 / c))
    have h := hbound n
    have hcpos : (0 : ℝ) ≤ 2 / c := (div_pos two_pos hc).le
    calc ‖u - uh n‖ ^ 2 = 2 / c * (c / 2 * ‖u - uh n‖ ^ 2) := by field_simp
      _ ≤ 2 / c * B n := mul_le_mul_of_nonneg_left h hcpos
  have hnorm : Tendsto (fun n => ‖u - uh n‖) atTop (𝓝 0) := by
    have h := hzero.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using h
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hrev : (fun n => ‖uh n - u‖) = fun n => ‖u - uh n‖ := funext fun n => norm_sub_rev _ _
  rw [hrev]
  exact hnorm

end Internal

/-! ### Weak sequential lower semicontinuity of a convex continuous functional -/

/-- Symmetry of the real inner product, with the arguments in the order they appear on the left.
Mathlib's `real_inner_comm a b` is `⟪b, a⟫ = ⟪a, b⟫`, so aiming it at a particular occurrence needs
the arguments reversed; this wrapper spares every call site that reversal. -/
private theorem inner_comm' (a b : V) : inner ℝ a b = inner ℝ b a := real_inner_comm _ _

/-- Weak convergence written with the vector on the left is weak convergence with it on the right;
over `ℝ` the inner product is symmetric. -/
private theorem tendsto_inner_of_weak {v : ℕ → V} {z : V}
    (hw : ∀ y : V, Tendsto (fun k => inner ℝ (v k) y) atTop (𝓝 (inner ℝ z y))) (y : V) :
    Tendsto (fun k => inner ℝ y (v k)) atTop (𝓝 (inner ℝ y z)) := by
  rw [inner_comm' y z]
  exact Filter.Tendsto.congr (fun k => inner_comm' (v k) y) (hw y)

section WeakLsc

variable [CompleteSpace V]

/-- Mazur's lemma in the inner-product form: a closed convex set contains the weak limit of any
sequence of its points. -/
private theorem mem_of_weak_tendsto {S : Set V} (hconv : Convex ℝ S) (hclosed : IsClosed S)
    {v : ℕ → V} {z : V} (hmem : ∀ k, v k ∈ S)
    (hw : ∀ y : V, Tendsto (fun k => inner ℝ (v k) y) atTop (𝓝 (inner ℝ z y))) : z ∈ S := by
  refine mem_of_weak_tendsto_of_convex hconv hclosed hmem fun l => ?_
  have hcomm : ∀ x : V, inner ℝ x (SesqForm.rieszRep l) = l x := fun x => by
    rw [inner_comm' x (SesqForm.rieszRep l), SesqForm.inner_rieszRep]
  simpa only [hcomm] using hw (SesqForm.rieszRep l)

/-- **A convex continuous functional is weakly sequentially lower semicontinuous.**  Its sublevel
sets are closed and convex, so Mazur's lemma applies to them. -/
private theorem le_of_weak_tendsto_of_eventually_le {j : V → ℝ} {α : ℝ}
    (hjcv : ConvexOn ℝ univ j) (hjc : Continuous j) {v : ℕ → V} {z : V}
    (hw : ∀ y : V, Tendsto (fun k => inner ℝ (v k) y) atTop (𝓝 (inner ℝ z y)))
    (hle : ∀ᶠ k in atTop, j (v k) ≤ α) : j z ≤ α := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hle
  have hconv : Convex ℝ {x : V | j x ≤ α} := by simpa using hjcv.convex_le α
  have hclosed : IsClosed {x : V | j x ≤ α} := isClosed_le hjc continuous_const
  have hshift : ∀ y : V, Tendsto (fun k => inner ℝ (v (k + N)) y) atTop (𝓝 (inner ℝ z y)) :=
    fun y => (hw y).comp (tendsto_add_atTop_nat N)
  exact mem_of_weak_tendsto hconv hclosed (fun k => hN (k + N) (Nat.le_add_left N k)) hshift

/-- The eventual form of weak lower semicontinuity: below the value at the weak limit, the values
along the sequence are eventually larger. -/
private theorem eventually_lt_of_weak_tendsto {j : V → ℝ} {α : ℝ} (hjcv : ConvexOn ℝ univ j)
    (hjc : Continuous j) {v : ℕ → V} {z : V} (hα : α < j z)
    (hw : ∀ y : V, Tendsto (fun k => inner ℝ (v k) y) atTop (𝓝 (inner ℝ z y))) :
    ∀ᶠ k in atTop, α < j (v k) := by
  by_contra hcon
  rw [not_eventually] at hcon
  simp only [not_lt] at hcon
  obtain ⟨φ, hφ, hφle⟩ := Filter.extraction_of_frequently_atTop hcon
  have hwφ : ∀ y : V, Tendsto (fun k => inner ℝ (v (φ k)) y) atTop (𝓝 (inner ℝ z y)) := fun y =>
    (hw y).comp hφ.tendsto_atTop
  exact absurd
    (le_of_weak_tendsto_of_eventually_le hjcv hjc hwφ (Eventually.of_forall hφle)) (not_le.2 hα)

end WeakLsc

/-! ### Convergence of external approximations -/

section External

variable [CompleteSpace V] {A : V → V} {j : V → ℝ} {f : V} {K : Set V} {Kh : ℕ → Set V}
  {c L : ℝ} {u : V} {uh : ℕ → V}

/-- **[han2009theoretical], Theorem 11.4.1.**  The general convergence theorem, in which the
discrete constraint sets need not lie inside `K`.  Assume

* `j` is convex and continuous on the whole space;
* every point of `K` is a limit of points of the `K_h n`;
* every weak limit of a sequence taken from the `K_h n` along any reindexing lies in `K`.

Then the discrete solutions converge to `u` in norm.

Three steps.  The discrete solutions are bounded, by testing at an approximation of `u` and using an
affine minorant of `j`.  A weakly convergent subsequence has its limit `z` in `K`, and `z` solves
the continuous inequality: the discrete inequalities in Minty's form pass to the weak limit, because
Minty's form evaluates the operator at the *test* point, and `j` is weakly sequentially lower
semicontinuous, being convex and continuous.  Hence `z = u`, and the same estimate upgrades weak
convergence to norm convergence.

For internal approximations the third hypothesis is `mem_of_weak_tendsto_of_convex`, and the
weak-compactness step is not needed at all — see
`tendsto_of_isVariationalInequalitySolution_of_subset`. -/
theorem tendsto_of_isVariationalInequalitySolution (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith L.toNNReal A)
    (hKcv : Convex ℝ K) (hjcv : ConvexOn ℝ univ j) (hjc : Continuous j)
    (happrox : ∀ v ∈ K, ∃ w : ℕ → V, (∀ n, w n ∈ Kh n) ∧ Tendsto w atTop (𝓝 v))
    (hweak : ∀ (σ : ℕ → ℕ) (v : ℕ → V) (z : V), (∀ k, v k ∈ Kh (σ k)) →
      (∀ y : V, Tendsto (fun k => inner ℝ (v k) y) atTop (𝓝 (inner ℝ z y))) → z ∈ K)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : ∀ n, IsVariationalInequalitySolution A j f (Kh n) (uh n)) :
    Tendsto uh atTop (𝓝 u) := by
  have hAcont : Continuous A := hlip.continuous
  have hAlip : ∀ x y : V, ‖A x - A y‖ ≤ (L.toNNReal : ℝ) * ‖x - y‖ := fun x y => by
    simpa only [dist_eq_norm] using hlip.dist_le_mul x y
  have hjK : ConvexOn ℝ K j := hjcv.subset (subset_univ K) hKcv
  have hmono0 : IsStronglyMonotoneWith ℝ A 0 := IsStronglyMonotoneWith.mono hmono hc.le
  have hmono0' : ∀ x y : V, (0 : ℝ) ≤ inner ℝ (A x - A y) (x - y) := fun x y => by
    simpa using hmono0 x y
  -- an affine minorant of the convex continuous `j`
  obtain ⟨lin, bb, hminor⟩ : ∃ (lin : V →L[ℝ] ℝ) (bb : ℝ), ∀ x : V, lin x + bb ≤ j x := by
    obtain ⟨l0, c0, hle, -⟩ := ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ) (a := j 0 - 1)
      (mem_univ (0 : V)) (by linarith) isClosed_univ
      (hjc.lowerSemicontinuous.lowerSemicontinuousOn univ) hjcv
    exact ⟨l0, c0, fun x => by simpa using hle ⟨x, mem_univ x⟩⟩
  -- an approximating sequence for `u`, and the part of Falk's bound that does not see `u_h`
  obtain ⟨w, hwmem, hw⟩ := happrox u hu.1
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : ℕ → ℝ, ∀ n, Ψ n =
      (inner ℝ (A u) (w n - u) + j (w n) - j u - inner ℝ f (w n - u))
        + L ^ 2 / (2 * c) * ‖u - w n‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hjw : Tendsto (fun n => j (w n)) atTop (𝓝 (j u)) := by
    simpa [Function.comp_def] using (hjc.tendsto u).comp hw
  have hΨ0 : Tendsto Ψ atTop (𝓝 0) :=
    Filter.Tendsto.congr (fun n => (hΨdef n).symm) (tendsto_falk_majorant hw hjw)
  -- Falk's bound at `v = u` and `v_h = w n`
  have hfalk : ∀ n, c / 2 * ‖u - uh n‖ ^ 2
      ≤ (inner ℝ (A u) (u - uh n) - inner ℝ f (u - uh n)) + (j u - j (uh n)) + Ψ n := by
    intro n
    have h := norm_sub_le_of_isVariationalInequalitySolution hc hmono hlip hu (huh n) hu.1
      (hwmem n)
    rw [hΨdef]
    linarith
  -- the discrete solutions are bounded
  have hC₁0 : (0 : ℝ) ≤ ‖A u - f‖ + ‖lin‖ := by positivity
  have hbnd : ∀ n, c / 2 * ‖u - uh n‖ ^ 2
      ≤ (‖A u - f‖ + ‖lin‖) * ‖u - uh n‖ + ((j u - lin u - bb) + Ψ n) := by
    intro n
    have h := hfalk n
    have h1 : inner ℝ (A u) (u - uh n) - inner ℝ f (u - uh n) ≤ ‖A u - f‖ * ‖u - uh n‖ := by
      rw [← inner_sub_left]
      exact real_inner_le_norm _ _
    have h2 : -j (uh n) ≤ lin (u - uh n) - lin u - bb := by
      have h3 := hminor (uh n)
      rw [map_sub]
      linarith
    have h4 : lin (u - uh n) ≤ ‖lin‖ * ‖u - uh n‖ :=
      le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using lin.le_opNorm (u - uh n))
    linarith
  obtain ⟨C₂, hC₂⟩ := (Filter.Tendsto.const_add (j u - lin u - bb) hΨ0).bddAbove_range
  have hGle : ∀ n, (j u - lin u - bb) + Ψ n ≤ max C₂ 0 :=
    fun n => le_trans (hC₂ ⟨n, rfl⟩) (le_max_left _ _)
  have hC₂0 : (0 : ℝ) ≤ max C₂ 0 := le_max_right _ _
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = max 1 (2 * ((‖A u - f‖ + ‖lin‖) + max C₂ 0) / c) :=
    ⟨_, rfl⟩
  have hD1 : (1 : ℝ) ≤ D := hDdef ▸ le_max_left _ _
  have hDbnd : ∀ n, ‖u - uh n‖ ≤ D := by
    intro n
    rcases le_or_gt (‖u - uh n‖) 1 with h | h
    · exact h.trans hD1
    · rw [hDdef]
      refine le_max_of_le_right ?_
      rw [le_div_iff₀ hc]
      have hd0 : (0 : ℝ) < ‖u - uh n‖ := lt_trans zero_lt_one h
      have hkey := hbnd n
      have hG := hGle n
      have hstep : ‖u - uh n‖ * (c / 2 * ‖u - uh n‖)
          ≤ ‖u - uh n‖ * ((‖A u - f‖ + ‖lin‖) + max C₂ 0) := by
        nlinarith [mul_nonneg hC₂0 (le_of_lt (sub_pos.2 h))]
      have hfin := le_of_mul_le_mul_left hstep hd0
      linarith
  have hUB : ∀ n, ‖uh n‖ ≤ ‖u‖ + D := by
    intro n
    have h : ‖uh n‖ = ‖u - (u - uh n)‖ := by congr 1; abel
    rw [h]
    exact le_trans (norm_sub_le _ _) (by linarith [hDbnd n])
  -- every subsequence has a further subsequence converging in norm
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨σ, z, hσ, hweakconv⟩ :=
    exists_subseq_weak_tendsto (𝕜 := ℝ) (u := fun k => uh (ns k)) (C := ‖u‖ + D)
      (fun k => hUB (ns k))
  refine ⟨σ, ?_⟩
  have hmtop : Tendsto (fun k => ns (σ k)) atTop atTop := by
    simpa [Function.comp_def] using hns.comp hσ.tendsto_atTop
  have hzK : z ∈ K := hweak (fun k => ns (σ k)) (fun k => uh (ns (σ k))) z
    (fun k => (huh (ns (σ k))).1) hweakconv
  -- the weak limit satisfies the Minty form of the inequality
  have hzminty : ∀ v ∈ K, inner ℝ f (v - z) ≤ inner ℝ (A v) (v - z) + j v - j z := by
    intro v hv
    obtain ⟨p, hpmem, hp⟩ := happrox v hv
    obtain ⟨E, hEdef⟩ : ∃ E : ℕ → ℝ, ∀ n, E n =
        inner ℝ (A v) (p n - uh n) - inner ℝ f (p n - uh n) + j (p n)
          + ‖A (p n) - A v‖ * ‖p n - uh n‖ := ⟨_, fun _ => rfl⟩
    have hjle : ∀ n, j (uh n) ≤ E n := by
      intro n
      have h1 := (huh n).2 (p n) (hpmem n)
      have h2 := hmono0' (p n) (uh n)
      have h3 : inner ℝ (A (p n) - A v) (p n - uh n) ≤ ‖A (p n) - A v‖ * ‖p n - uh n‖ :=
        real_inner_le_norm _ _
      rw [inner_sub_left] at h2 h3
      rw [hEdef]
      linarith
    have hpm : Tendsto (fun k => p (ns (σ k))) atTop (𝓝 v) := by
      simpa [Function.comp_def] using hp.comp hmtop
    have hpair : ∀ y : V, Tendsto (fun k => inner ℝ y (p (ns (σ k)) - uh (ns (σ k)))) atTop
        (𝓝 (inner ℝ y (v - z))) := by
      intro y
      have hcont : Continuous fun x : V => inner ℝ y x :=
        continuous_inner.comp (continuous_const.prodMk continuous_id)
      have h1 : Tendsto (fun k => inner ℝ y (p (ns (σ k)))) atTop (𝓝 (inner ℝ y v)) := by
        simpa [Function.comp_def] using (hcont.tendsto v).comp hpm
      have h2 := tendsto_inner_of_weak hweakconv y
      have h3 : (fun k => inner ℝ y (p (ns (σ k)) - uh (ns (σ k))))
          = fun k => inner ℝ y (p (ns (σ k))) - inner ℝ y (uh (ns (σ k))) := by
        funext k
        rw [inner_sub_right]
      have h4 : inner ℝ y (v - z) = inner ℝ y v - inner ℝ y z := inner_sub_right _ _ _
      rw [h3, h4]
      exact h1.sub h2
    have hjp : Tendsto (fun k => j (p (ns (σ k)))) atTop (𝓝 (j v)) := by
      simpa [Function.comp_def] using (hjc.tendsto v).comp hpm
    have hq : Tendsto (fun k => ‖p (ns (σ k)) - v‖) atTop (𝓝 0) := by
      have h := hpm.sub (tendsto_const_nhds (x := v))
      simpa using h.norm
    have herr : Tendsto
        (fun k => ‖A (p (ns (σ k))) - A v‖ * ‖p (ns (σ k)) - uh (ns (σ k))‖) atTop (𝓝 0) := by
      have hmaj : Tendsto (fun k => (L.toNNReal : ℝ) * ‖p (ns (σ k)) - v‖
          * (‖p (ns (σ k)) - v‖ + (‖v - u‖ + D))) atTop (𝓝 0) := by
        have h := ((tendsto_const_nhds (x := ((L.toNNReal : ℝ)))).mul hq).mul
          (hq.add (tendsto_const_nhds (x := ‖v - u‖ + D)))
        simpa using h
      refine squeeze_zero (fun k => by positivity) (fun k => ?_) hmaj
      have hb1 : ‖A (p (ns (σ k))) - A v‖ ≤ (L.toNNReal : ℝ) * ‖p (ns (σ k)) - v‖ := hAlip _ _
      have ht1 : ‖p (ns (σ k)) - uh (ns (σ k))‖
          ≤ ‖p (ns (σ k)) - v‖ + ‖v - uh (ns (σ k))‖ := by
        simpa only [dist_eq_norm] using dist_triangle (p (ns (σ k))) v (uh (ns (σ k)))
      have ht2 : ‖v - uh (ns (σ k))‖ ≤ ‖v - u‖ + ‖u - uh (ns (σ k))‖ := by
        simpa only [dist_eq_norm] using dist_triangle v u (uh (ns (σ k)))
      have hb2 : ‖p (ns (σ k)) - uh (ns (σ k))‖
          ≤ ‖p (ns (σ k)) - v‖ + (‖v - u‖ + D) := by
        have hdb := hDbnd (ns (σ k))
        linarith
      exact mul_le_mul hb1 hb2 (norm_nonneg _)
        (mul_nonneg (L.toNNReal).coe_nonneg (norm_nonneg _))
    have hE : Tendsto (fun k => E (ns (σ k))) atTop
        (𝓝 (inner ℝ (A v) (v - z) - inner ℝ f (v - z) + j v)) := by
      have h := (((hpair (A v)).sub (hpair f)).add hjp).add herr
      simpa [hEdef] using h
    have hkey : j z ≤ inner ℝ (A v) (v - z) - inner ℝ f (v - z) + j v := by
      by_contra hcon
      push Not at hcon
      obtain ⟨α, hα1, hα2⟩ := exists_between hcon
      have h1 : ∀ᶠ k in atTop, α < j (uh (ns (σ k))) :=
        eventually_lt_of_weak_tendsto hjcv hjc hα2 hweakconv
      have h2 : ∀ᶠ k in atTop, E (ns (σ k)) < α := hE.eventually (eventually_lt_nhds hα1)
      obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
      exact absurd (hjle (ns (σ k))) (not_le.2 (lt_trans hk2 hk1))
    linarith
  have hzsol : IsVariationalInequalitySolution A j f K z := by
    refine (IsVariationalInequalitySolution.iff_minty hKcv hjK hmono0 hzK ?_).2 hzminty
    intro y _
    exact (hAcont.comp
      (continuous_const.add (continuous_id.smul continuous_const))).continuousWithinAt
  have hzu : z = u := IsVariationalInequalitySolution.unique hc hmono hzsol hu
  rw [hzu] at hweakconv
  -- and then the error tends to zero along that subsequence
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hrev : (fun k => ‖uh (ns (σ k)) - u‖) = fun k => ‖u - uh (ns (σ k))‖ :=
    funext fun k => norm_sub_rev _ _
  rw [hrev]
  refine tendsto_order.2
    ⟨fun b hb => Eventually.of_forall fun k => lt_of_lt_of_le hb (norm_nonneg _), fun b hb => ?_⟩
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = c / 2 * b ^ 2 / 3 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hP1 : Tendsto (fun k => inner ℝ (A u) (u - uh (ns (σ k)))
      - inner ℝ f (u - uh (ns (σ k)))) atTop (𝓝 0) := by
    have h : ∀ y : V, Tendsto (fun k => inner ℝ y (u - uh (ns (σ k)))) atTop (𝓝 0) := by
      intro y
      have h1 : Tendsto (fun k => inner ℝ y (uh (ns (σ k)))) atTop (𝓝 (inner ℝ y u)) :=
        tendsto_inner_of_weak hweakconv y
      have h3 : (fun k => inner ℝ y (u - uh (ns (σ k))))
          = fun k => inner ℝ y u - inner ℝ y (uh (ns (σ k))) := by
        funext k
        rw [inner_sub_right]
      rw [h3]
      simpa using (tendsto_const_nhds (x := inner ℝ y u)).sub h1
    simpa using (h (A u)).sub (h f)
  have hP2 : ∀ᶠ k in atTop, j u - j (uh (ns (σ k))) < ε := by
    have h := eventually_lt_of_weak_tendsto hjcv hjc (α := j u - ε) (by linarith) hweakconv
    filter_upwards [h] with k hk
    linarith
  have hP3 : ∀ᶠ k in atTop, Ψ (ns (σ k)) < ε := by
    have hΨm : Tendsto (fun k => Ψ (ns (σ k))) atTop (𝓝 0) := by
      simpa [Function.comp_def] using hΨ0.comp hmtop
    exact hΨm.eventually (eventually_lt_nhds hε)
  filter_upwards [hP1.eventually (eventually_lt_nhds hε), hP2, hP3] with k h1 h2 h3
  have hf := hfalk (ns (σ k))
  have h3ε : (3 : ℝ) * ε = c / 2 * b ^ 2 := by rw [hεdef]; ring
  have hd2 : ‖u - uh (ns (σ k))‖ ^ 2 < b ^ 2 := by
    have hlt : c / 2 * ‖u - uh (ns (σ k))‖ ^ 2 < c / 2 * b ^ 2 := by linarith
    nlinarith
  have hsq := Real.sqrt_lt_sqrt (sq_nonneg _) hd2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hb.le] at hsq

end External
