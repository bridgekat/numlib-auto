import Numlib.Analysis.Convex.Gateaux
import Numlib.Approximation.BestApprox
import Numlib.Variational.LaxMilgram
import Mathlib.Analysis.Convex.Approximation

/-!
# Elliptic variational inequalities

For a real Hilbert space `V`, a nonempty closed convex `K ⊆ V`, an operator `A : V → V`, a
functional `j : V → ℝ` and a datum `f : V`, the *elliptic variational inequality* asks for

  `u ∈ K`,  `⟪f, v - u⟫ ≤ ⟪A u, v - u⟫ + j v - j u`  for every `v ∈ K`.

`IsVariationalInequalitySolution A j f K u` is that specification. One predicate covers all the
forms the literature distinguishes: the inequality *of the first kind* is `j = 0`, the inequality
*of the second kind* is `K = Set.univ`, and the bilinear-form problems are `A = a.toOperator`.
The datum is a vector rather than a functional, the two being interchangeable by the Riesz
representation.

* `IsVariationalInequalitySolution.norm_sub_le` and `.unique`: strong monotonicity alone gives
  `‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ / c`, hence uniqueness.
* `existsUnique_isMinOn_energy_add`: the minimizer of `E v = ½ a v v + j v - ℓ v` over a nonempty
  closed convex set exists and is unique.  This is the existence engine, proved in the Hilbert
  space itself: `j` has a continuous affine minorant, so `E` is bounded below, and the
  parallelogram identity `E x + E y - 2 E ((x + y)/2) ≥ (c/4) ‖x - y‖²` makes every minimizing
  sequence Cauchy.
* `isMinOn_energy_add_iff`: that minimizer is characterized by the variational inequality — the
  specialization of `isMinOn_add_iff_forall_le` to the quadratic functional.
* `existsUnique_isVariationalInequalitySolution`: unique solvability for a strongly monotone
  Lipschitz `A` and a convex lower semicontinuous `j`, by a fixed point of the map sending `u` to
  the solution of the auxiliary inequality with operator the identity and datum
  `u - θ (A u - f)`; that map is nonexpansive in its datum, and the damping step is a contraction
  with factor `√(1 - 2 c θ + L² θ²)`.  `stampacchia` is the case `j = 0` and
  `existsUnique_isVariationalInequalitySolution_of_isCoercive` the bilinear-form case.
* `IsVariationalInequalitySolution.iff_minty`: Minty's lemma, the equivalent form with `A`
  evaluated at the test point.  It needs no Lipschitz continuity, only continuity of `A` along the
  segments of `K` issuing from `u`.
* `IsVariationalInequalitySolution.isBestApprox_energy`, `.iff_of_isCone` and
  `.iff_of_isPositiveHomogeneous`: the energy-projection reading, the cone form and the
  positively homogeneous form.

`IsVariationalInequalitySolution` unfolds to `And` and `IsStronglyMonotoneWith` to a `∀`, so dot
notation on a hypothesis of either type can resolve in the wrong namespace; write the lemma names
out in full.

Strong monotonicity is bundled here as `IsStronglyMonotoneWith`, whose unfolding is exactly the
hypothesis `zarantonello` and `contractingWith_damped` take, so the two compose with no
translation lemma.

The material is Chapter 11 of Atkinson–Han[^atkinson-han]: (11.3.3), (11.3.8), (11.3.9) and
(11.3.12)–(11.3.14) for the problem, Theorem 11.2.2 for the equivalence with minimization,
Theorem 11.3.1 for unique solvability, Theorem 11.3.6 (Stampacchia) and Theorem 11.3.9 for its
specializations, Lemma 11.3.8 for Minty's lemma, and Exercises 11.3.3 and 11.3.10 for the last
two.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

open Filter Set Topology

/-- **Strong monotonicity.**  `IsStronglyMonotoneWith 𝕜 A c` is
`c ‖x - y‖² ≤ re ⟪A x - A y, x - y⟫` for all `x, y`: the nonlinear counterpart of coercivity of an
operator, and the hypothesis of Zarantonello's theorem and of the existence theory for variational
inequalities.  For a linear `A` it is `LinearMap.IsCoerciveWith`.

The scalar field is an explicit argument, as in `inner 𝕜 x y`, because it is not determined by
`A : E → E`. -/
def IsStronglyMonotoneWith (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (A : E → E) (c : ℝ) : Prop :=
  ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x - A y) (x - y))

section StronglyMonotone

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Strong monotonicity only weakens as its constant shrinks. -/
theorem IsStronglyMonotoneWith.mono {A : E → E} {c c' : ℝ} (h : IsStronglyMonotoneWith 𝕜 A c)
    (hc : c' ≤ c) : IsStronglyMonotoneWith 𝕜 A c' := fun x y =>
  (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans (h x y)

/-- Real spaces: strong monotonicity without `re`. -/
theorem isStronglyMonotoneWith_real_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (A : F → F) (c : ℝ) :
    IsStronglyMonotoneWith ℝ A c ↔ ∀ x y, c * ‖x - y‖ ^ 2 ≤ inner ℝ (A x - A y) (x - y) :=
  Iff.rfl

/-- The identity is strongly monotone with constant `1`. -/
theorem isStronglyMonotoneWith_id : IsStronglyMonotoneWith 𝕜 (fun x : E => x) 1 := fun x y => by
  rw [one_mul, inner_self_eq_norm_sq]

/-- A coercive operator is strongly monotone with the same constant. -/
theorem LinearMap.IsCoerciveWith.isStronglyMonotoneWith {A : E →ₗ[𝕜] E} {c : ℝ}
    (h : A.IsCoerciveWith c) : IsStronglyMonotoneWith 𝕜 (A : E → E) c := fun x y => by
  simpa only [map_sub] using h (x - y)

end StronglyMonotone

/-- Scaling by a positive constant preserves lower semicontinuity on a set. -/
private theorem lowerSemicontinuousOn_const_mul {α : Type*} [TopologicalSpace α] {j : α → ℝ}
    {K : Set α} {θ : ℝ} (hθ : 0 < θ) (hj : LowerSemicontinuousOn j K) :
    LowerSemicontinuousOn (fun v => θ * j v) K := by
  intro x hx y hy
  have hy' : y / θ < j x := by rwa [div_lt_iff₀ hθ, mul_comm]
  filter_upwards [hj x hx (y / θ) hy'] with x' hx'
  rw [gt_iff_lt, div_lt_iff₀ hθ, mul_comm] at hx'
  exact hx'

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The elliptic variational inequality.**  `IsVariationalInequalitySolution A j f K u` says
that `u` lies in `K` and

  `⟪f, v - u⟫ ≤ ⟪A u, v - u⟫ + j v - j u`  for every `v ∈ K`.

The inequality of the first kind is `j = 0`, the inequality of the second kind is `K = Set.univ`,
and the bilinear-form problems are `A = a.toOperator`; the datum is a vector `f`, which the Riesz
representation makes interchangeable with a functional.

Atkinson–Han, *Theoretical Numerical Analysis*, (11.3.3), (11.3.8), (11.3.9) and
(11.3.12)–(11.3.14). -/
def IsVariationalInequalitySolution (A : V → V) (j : V → ℝ) (f : V) (K : Set V) (u : V) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, inner ℝ f (v - u) ≤ inner ℝ (A u) (v - u) + j v - j u

section Uniqueness

variable {A : V → V} {j : V → ℝ} {K : Set V} {c : ℝ}

/-- **Lipschitz dependence on the datum.**  Two solutions of the same variational inequality with
data `f₁` and `f₂` and a `c`-strongly monotone operator satisfy `‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ / c`.

Neither Lipschitz continuity of `A`, nor convexity of `j`, nor closedness of `K` is used.
Atkinson–Han, *Theoretical Numerical Analysis*, Theorem 11.3.1, last clause; the linear case is
`norm_sub_le_of_strongly_monotone`. -/
theorem IsVariationalInequalitySolution.norm_sub_le (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) {f₁ f₂ u₁ u₂ : V}
    (h₁ : IsVariationalInequalitySolution A j f₁ K u₁)
    (h₂ : IsVariationalInequalitySolution A j f₂ K u₂) : ‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ / c := by
  have e₁ := h₁.2 u₂ h₂.1
  have e₂ := h₂.2 u₁ h₁.1
  have hneg₁ : inner ℝ f₁ (u₂ - u₁) = -inner ℝ f₁ (u₁ - u₂) := by
    rw [← inner_neg_right]; congr 1; abel
  have hneg₂ : inner ℝ (A u₁) (u₂ - u₁) = -inner ℝ (A u₁) (u₁ - u₂) := by
    rw [← inner_neg_right]; congr 1; abel
  rw [hneg₁, hneg₂] at e₁
  -- adding the two inequalities, each tested at the other solution, cancels the values of `j`
  have hkey : inner ℝ (A u₁ - A u₂) (u₁ - u₂) ≤ inner ℝ (f₁ - f₂) (u₁ - u₂) := by
    rw [inner_sub_left, inner_sub_left]
    linarith
  have hmono' : c * ‖u₁ - u₂‖ ^ 2 ≤ inner ℝ (f₁ - f₂) (u₁ - u₂) := (hmono u₁ u₂).trans hkey
  have hcs : inner ℝ (f₁ - f₂) (u₁ - u₂) ≤ ‖f₁ - f₂‖ * ‖u₁ - u₂‖ := real_inner_le_norm _ _
  rw [le_div_iff₀ hc]
  rcases eq_or_lt_of_le (norm_nonneg (u₁ - u₂)) with h | h
  · simp [← h]
  · refine le_of_mul_le_mul_right ?_ h
    calc ‖u₁ - u₂‖ * c * ‖u₁ - u₂‖ = c * ‖u₁ - u₂‖ ^ 2 := by ring
      _ ≤ ‖f₁ - f₂‖ * ‖u₁ - u₂‖ := hmono'.trans hcs

/-- **Uniqueness.**  Two solutions of the same variational inequality with a strongly monotone
operator coincide.  Atkinson–Han, *Theoretical Numerical Analysis*, Theorem 11.3.1, uniqueness
clause. -/
theorem IsVariationalInequalitySolution.unique (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) {f u₁ u₂ : V}
    (h₁ : IsVariationalInequalitySolution A j f K u₁)
    (h₂ : IsVariationalInequalitySolution A j f K u₂) : u₁ = u₂ := by
  have h := IsVariationalInequalitySolution.norm_sub_le hc hmono h₁ h₂
  simp only [sub_self, norm_zero, zero_div] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

end Uniqueness

/-! ### The energy functional of a symmetric form -/

section Energy

/-- Expansion of the energy around a point: `E (u + w) = E u + (a u w - ℓ w) + ½ a w w`. -/
private theorem energy_add (a : SesqForm ℝ V) (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ) (u w : V) :
    a.energy ℓ (u + w) = a.energy ℓ u + (a u w - ℓ w) + 1 / 2 * a w w := by
  have hsym : a w u = a u w := (SesqForm.isHermitian_real_iff a).mp ha w u
  simp only [SesqForm.energy, RCLike.re_to_real, map_add, add_apply]
  rw [hsym]
  ring

/-- Parallelogram identity for the energy of a symmetric real form:
`E x + E y - 2 E ((x + y) / 2) = ¼ a (x - y) (x - y)`. -/
private theorem energy_parallelogram (a : SesqForm ℝ V) (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ)
    (x y : V) :
    a.energy ℓ x + a.energy ℓ y - 2 * a.energy ℓ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
      = 1 / 4 * a (x - y) (x - y) := by
  have hsym : a y x = a x y := (SesqForm.isHermitian_real_iff a).mp ha y x
  simp only [SesqForm.energy, RCLike.re_to_real, map_smulₛₗ, map_add, map_sub, add_apply,
    sub_apply, smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply, star_trivial]
  rw [hsym]
  ring

/-- The energy functional is continuous (its quadratic part is a bounded bilinear map). -/
private theorem continuous_energy (a : SesqForm ℝ V) (ℓ : V →L[ℝ] ℝ) :
    Continuous (a.energy ℓ) := by
  have h1 : Continuous fun v : V => ((a v : V →L[ℝ] ℝ), v) := a.continuous.prodMk continuous_id
  have h2 : Continuous fun p : (V →L[ℝ] ℝ) × V => p.1 p.2 := isBoundedBilinearMap_apply.continuous
  have hq : Continuous fun v : V => a v v := h2.comp h1
  have hE : a.energy ℓ = fun v : V => (1 / 2 : ℝ) * a v v - ℓ v := by
    funext v
    simp [SesqForm.energy]
  rw [hE]
  exact (continuous_const.mul hq).sub ℓ.continuous

/-- The Gâteaux derivative of the energy of a symmetric form at `u` is `v ↦ a u v - ℓ v`. -/
private theorem hasLineDerivAt_energy (a : SesqForm ℝ V) (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ)
    (u h : V) : HasLineDerivAt ℝ (a.energy ℓ) ((a u - ℓ) h) u h := by
  have hfun : (fun t : ℝ => a.energy ℓ (u + t • h))
      = fun t : ℝ => a.energy ℓ u + t * (a u h - ℓ h) + 1 / 2 * t ^ 2 * a h h := by
    funext t
    rw [energy_add a ha ℓ u (t • h)]
    simp only [map_smulₛₗ, smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply,
      star_trivial]
    ring
  have hd : HasDerivAt (fun t : ℝ => a.energy ℓ (u + t • h)) ((a u - ℓ) h) 0 := by
    rw [hfun]
    have h1 : HasDerivAt (fun t : ℝ => a.energy ℓ u + t * (a u h - ℓ h)) (a u h - ℓ h) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a u h - ℓ h)).const_add (a.energy ℓ u)
    have h2 : HasDerivAt (fun t : ℝ => 1 / 2 * t ^ 2 * a h h) 0 0 := by
      simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (1 / 2 : ℝ)).mul_const (a h h)
    have h3 := h1.add h2
    have hval : (a u - ℓ) h = (a u h - ℓ h) + 0 := by simp
    rw [hval]
    exact h3
  exact hd

/-- The energy of a positive semidefinite symmetric form is convex on every convex set. -/
private theorem convexOn_energy (a : SesqForm ℝ V) (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ)
    (hpos : ∀ w : V, 0 ≤ a w w) {K : Set V} (hK : Convex ℝ K) : ConvexOn ℝ K (a.energy ℓ) := by
  refine convexOn_of_add_lineDeriv_le (f' := fun w => a w - ℓ) hK fun u _ v _ => ?_
  have hexp := energy_add a ha ℓ u (v - u)
  rw [show u + (v - u) = v by abel] at hexp
  have hq := hpos (v - u)
  simp only [sub_apply]
  linarith

end Energy

/-! ### Existence and characterization of the constrained minimizer -/

section Minimization

variable [CompleteSpace V]

/-- **Existence and uniqueness of the constrained minimizer.**  For a bounded symmetric
`V`-elliptic form `a`, a functional `ℓ`, and a `j` convex and lower semicontinuous on a nonempty
closed convex `K`, the functional `E v = ½ a v v + j v - ℓ v` has exactly one minimizer on `K`.

Atkinson–Han, *Theoretical Numerical Analysis*, Theorem 11.2.2, existence clause.  The proof
stays in the Hilbert space instead of invoking the direct method in a reflexive space: `j` has a
continuous affine minorant (`ConvexOn.exists_affine_le_of_lt`, the book's Lemma 11.3.5), so `E` is
bounded below, and ellipticity together with convexity of `j` gives
`E v + E w - 2 E ((v + w)/2) ≥ (c/4) ‖v - w‖²`, which makes every minimizing sequence Cauchy.
Mathlib's `exists_norm_eq_iInf_of_complete_convex` is the case `a = inner`, `j = 0`. -/
theorem existsUnique_isMinOn_energy_add {a : SesqForm ℝ V} (ha : a.IsHermitian) {c : ℝ}
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) (ℓ : V →L[ℝ] ℝ) {j : V → ℝ} {K : Set V}
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hj : ConvexOn ℝ K j)
    (hjlsc : LowerSemicontinuousOn j K) :
    ∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ + j) K u := by
  obtain ⟨x₀, hx₀⟩ := hKne
  -- a continuous affine minorant of `j` on `K`
  obtain ⟨lin, cc, hle, -⟩ := ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ) (a := j x₀ - 1) hx₀
    (by linarith) hKcl hjlsc hj
  have hminor : ∀ z ∈ K, lin z + cc ≤ j z := fun z hz => by simpa using hle ⟨z, hz⟩
  set E : V → ℝ := a.energy ℓ + j with hEdef
  have hEapply : ∀ v : V, E v = 1 / 2 * a v v - ℓ v + j v := by
    intro v
    simp [hEdef, SesqForm.energy]
  -- `E` is bounded below on `K` by a quadratic in `‖v‖`
  have hbelow : ∀ v ∈ K, cc - (‖ℓ‖ + ‖lin‖) ^ 2 / (2 * c) ≤ E v := by
    intro v hv
    have h1 : c * ‖v‖ ^ 2 ≤ a v v := hcoer v
    have h2 : ℓ v ≤ ‖ℓ‖ * ‖v‖ :=
      le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using ℓ.le_opNorm v)
    have h3 : -(‖lin‖ * ‖v‖) ≤ lin v :=
      neg_le_of_neg_le (le_trans (neg_le_abs _) (by simpa [Real.norm_eq_abs] using lin.le_opNorm v))
    have h4 := hminor v hv
    have hsq : 0 ≤ (c * ‖v‖ - (‖ℓ‖ + ‖lin‖)) ^ 2 / (2 * c) := by positivity
    have hid : (c * ‖v‖ - (‖ℓ‖ + ‖lin‖)) ^ 2 / (2 * c)
        = c / 2 * ‖v‖ ^ 2 - (‖ℓ‖ + ‖lin‖) * ‖v‖ + (‖ℓ‖ + ‖lin‖) ^ 2 / (2 * c) := by
      field_simp
      ring
    rw [hEapply v]
    nlinarith [norm_nonneg v]
  have hSne : (E '' K).Nonempty := ⟨E x₀, x₀, hx₀, rfl⟩
  have hSbdd : BddBelow (E '' K) :=
    ⟨cc - (‖ℓ‖ + ‖lin‖) ^ 2 / (2 * c), by rintro _ ⟨v, hv, rfl⟩; exact hbelow v hv⟩
  set d : ℝ := sInf (E '' K) with hddef
  have hdle : ∀ v ∈ K, d ≤ E v := fun v hv => csInf_le hSbdd ⟨v, hv, rfl⟩
  -- the parallelogram estimate: `E` is uniformly convex along `K`
  have hpara : ∀ x ∈ K, ∀ y ∈ K, c / 4 * ‖x - y‖ ^ 2 ≤ E x + E y - 2 * d := by
    intro x hx y hy
    have hm : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ K :=
      hKcv hx hy (by norm_num) (by norm_num) (by norm_num)
    have hjm : j ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≤ 1 / 2 * j x + 1 / 2 * j y := by
      simpa using hj.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)
    have hpar := energy_parallelogram a ha ℓ x y
    have hq : c * ‖x - y‖ ^ 2 ≤ a (x - y) (x - y) := hcoer (x - y)
    have hd := hdle _ hm
    simp only [hEdef, Pi.add_apply] at hd ⊢
    linarith
  -- a minimizing sequence, which the estimate makes Cauchy
  have hex : ∀ n : ℕ, ∃ v, v ∈ K ∧ E v < d + 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨_, ⟨v, hv, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hSne (by linarith : d < d + 1 / (n + 1))
    exact ⟨v, hv, hlt⟩
  choose w hwK hwlt using hex
  have hbnd : ∀ n m N : ℕ, N ≤ n → N ≤ m →
      dist (w n) (w m) ≤ Real.sqrt (8 / c * (1 / (N + 1))) := by
    intro n m N hn hm
    have h1 := hpara _ (hwK n) _ (hwK m)
    have h2 : E (w n) < d + 1 / (n + 1) := hwlt n
    have h3 : E (w m) < d + 1 / (m + 1) := hwlt m
    have h4 : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    have h5 : (1 : ℝ) / (m + 1) ≤ 1 / (N + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
    have hsq : ‖w n - w m‖ ^ 2 ≤ 8 / c * (1 / (N + 1)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      nlinarith
    rw [dist_eq_norm]
    calc ‖w n - w m‖ = Real.sqrt (‖w n - w m‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (8 / c * (1 / (N + 1))) := Real.sqrt_le_sqrt hsq
  have hb0 : Tendsto (fun N : ℕ => Real.sqrt (8 / c * (1 / (N + 1)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 8 / c * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using Filter.Tendsto.const_mul (8 / c) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.sqrt
  obtain ⟨u, htend⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_tendsto_0 _ hbnd hb0)
  have huK : u ∈ K := hKcl.mem_of_tendsto htend (Eventually.of_forall hwK)
  -- the limit attains the infimum, by continuity of the energy and semicontinuity of `j`
  have henergy : Tendsto (fun n => a.energy ℓ (w n)) atTop (𝓝 (a.energy ℓ u)) :=
    ((continuous_energy a ℓ).tendsto u).comp htend
  have hEtend : Tendsto (fun n => E (w n)) atTop (𝓝 d) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => hdle _ (hwK n)) (fun n => (hwlt n).le)
    have hlim : Tendsto (fun n : ℕ => d + 1 / ((n : ℝ) + 1)) atTop (𝓝 (d + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using hlim
  have hjtend : Tendsto (fun n => j (w n)) atTop (𝓝 (d - a.energy ℓ u)) := by
    have heq : (fun n => j (w n)) = fun n => E (w n) - a.energy ℓ (w n) := by
      funext n
      simp [hEdef]
    rw [heq]
    exact hEtend.sub henergy
  have hju : j u ≤ d - a.energy ℓ u := by
    by_contra hcon
    push Not at hcon
    have hy1 : d - a.energy ℓ u < (d - a.energy ℓ u + j u) / 2 := by linarith
    have hy2 : (d - a.energy ℓ u + j u) / 2 < j u := by linarith
    have hwithin : Tendsto w atTop (𝓝[K] u) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w htend (Eventually.of_forall hwK)
    have hev : ∀ᶠ n in atTop, (d - a.energy ℓ u + j u) / 2 ≤ j (w n) :=
      (hwithin.eventually (hjlsc u huK _ hy2)).mono fun n hn => hn.le
    exact absurd (ge_of_tendsto hjtend hev) (not_le.2 hy1)
  have hEu : E u ≤ d := by
    simp only [hEdef, Pi.add_apply]
    linarith
  have hminon : IsMinOn E K u := isMinOn_iff.2 fun x hx => hEu.trans (hdle x hx)
  -- uniqueness, from the same estimate
  have huniq : ∀ u₁ ∈ K, IsMinOn E K u₁ → ∀ u₂ ∈ K, IsMinOn E K u₂ → u₁ = u₂ := by
    intro u₁ h1 hm1 u₂ h2 hm2
    have hd1 : E u₁ = d :=
      le_antisymm (le_csInf hSne (by rintro _ ⟨v, hv, rfl⟩; exact isMinOn_iff.1 hm1 v hv))
        (hdle _ h1)
    have hd2 : E u₂ = d :=
      le_antisymm (le_csInf hSne (by rintro _ ⟨v, hv, rfl⟩; exact isMinOn_iff.1 hm2 v hv))
        (hdle _ h2)
    have hp := hpara _ h1 _ h2
    rw [hd1, hd2] at hp
    have hp0 : ‖u₁ - u₂‖ ^ 2 ≤ 0 := by nlinarith
    have hz : ‖u₁ - u₂‖ = 0 :=
      (pow_eq_zero_iff (n := 2) (by norm_num)).mp (le_antisymm hp0 (sq_nonneg _))
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  exact ⟨u, ⟨huK, hminon⟩, fun z hz => huniq z hz.1 hz.2 u huK hminon⟩

/-- **The constrained minimizer is characterized by a variational inequality.**  For a symmetric
positive semidefinite form `a`, a functional `ℓ` and a `j` convex on a convex `K`, a point
`u ∈ K` minimizes `E v = ½ a v v + j v - ℓ v` over `K` if and only if

  `ℓ (v - u) ≤ a u (v - u) + j v - j u`  for every `v ∈ K`,

which is the variational inequality with operator `a.toOperator` and datum `rieszRep ℓ`.

This is the specialization of `isMinOn_add_iff_forall_le` to the quadratic functional, whose
Gâteaux derivative at `u` is `v ↦ a u v - ℓ v`.  Atkinson–Han, *Theoretical Numerical Analysis*,
Theorem 11.2.2, characterization clause; the case `j = 0` with `K` a subspace is
`SesqForm.isMinOn_energy_iff`. -/
theorem isMinOn_energy_add_iff {a : SesqForm ℝ V} (ha : a.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (hcoer : a.IsCoerciveWith c) (ℓ : V →L[ℝ] ℝ) {j : V → ℝ} {K : Set V} (hKcv : Convex ℝ K)
    (hj : ConvexOn ℝ K j) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ + j) K u ↔
      IsVariationalInequalitySolution a.toOperator j (SesqForm.rieszRep ℓ) K u := by
  have hpos : ∀ w : V, 0 ≤ a w w := fun w => le_trans (mul_nonneg hc (sq_nonneg _)) (hcoer w)
  have hG : ∀ z ∈ K, ∀ h : V, HasLineDerivAt ℝ (a.energy ℓ) ((fun z => a z - ℓ) z h) z h :=
    fun z _ h => hasLineDerivAt_energy a ha ℓ z h
  rw [isMinOn_add_iff_forall_le (convexOn_energy a ha ℓ hpos hKcv) hj hG hu]
  constructor
  · refine fun h => ⟨hu, fun v hv => ?_⟩
    have hv' := h v hv
    rw [SesqForm.inner_rieszRep, SesqForm.inner_toOperator]
    simp only [sub_apply] at hv'
    linarith
  · rintro ⟨-, h⟩ v hv
    have hv' := h v hv
    rw [SesqForm.inner_rieszRep, SesqForm.inner_toOperator] at hv'
    simp only [sub_apply]
    linarith

end Minimization

/-! ### Unique solvability -/

section Existence

/-- The fixed-point reformulation: `u` solves the variational inequality exactly when it solves
the auxiliary inequality with operator the identity and datum `u - θ (A u - f)`. -/
private theorem isVarIneq_aux_iff {A : V → V} {j : V → ℝ} {f : V} {K : Set V} {θ : ℝ}
    (hθ : 0 < θ) {u : V} :
    IsVariationalInequalitySolution (fun w => w) (fun v => θ * j v) (u - θ • (A u - f)) K u ↔
      IsVariationalInequalitySolution A j f K u := by
  have hexp : ∀ v : V, inner ℝ (u - θ • (A u - f)) (v - u)
      = inner ℝ u (v - u) - θ * (inner ℝ (A u) (v - u) - inner ℝ f (v - u)) := by
    intro v
    rw [inner_sub_left, real_inner_smul_left, inner_sub_left]
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun v hv => ?_⟩
    have hv' := h v hv
    rw [hexp v] at hv'
    have hmul : θ * (inner ℝ f (v - u) - inner ℝ (A u) (v - u)) ≤ θ * (j v - j u) := by linarith
    have := le_of_mul_le_mul_left hmul hθ
    linarith
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun v hv => ?_⟩
    have hv' := h v hv
    rw [hexp v]
    nlinarith [hv']

variable [CompleteSpace V]

/-- The operator of the inner product form is the identity. -/
private theorem coe_toOperator_innerSL :
    ⇑(SesqForm.toOperator (innerSL ℝ : SesqForm ℝ V)) = fun w : V => w := by
  funext y
  refine ext_inner_right ℝ fun v => ?_
  rw [SesqForm.inner_toOperator]
  rfl

/-- The Riesz representative of `⟪y, ·⟫` is `y`. -/
private theorem rieszRep_innerSL (y : V) : SesqForm.rieszRep (innerSL ℝ y : V →L[ℝ] ℝ) = y := by
  refine ext_inner_right ℝ fun v => ?_
  rw [SesqForm.inner_rieszRep]
  rfl

/-- **The auxiliary problem.**  The variational inequality with the identity operator is uniquely
solvable, being the minimization of `½ ‖w‖² + j w - ⟪y, w⟫` over `K`. -/
private theorem existsUnique_id {K : Set V} (hKne : K.Nonempty) (hKcl : IsClosed K)
    (hKcv : Convex ℝ K) {j : V → ℝ} (hj : ConvexOn ℝ K j) (hjlsc : LowerSemicontinuousOn j K)
    (y : V) : ∃! z, IsVariationalInequalitySolution (fun w => w) j y K z := by
  have hiff : ∀ z ∈ K,
      (IsMinOn (SesqForm.energy (innerSL ℝ : SesqForm ℝ V) (innerSL ℝ y) + j) K z ↔
        IsVariationalInequalitySolution (fun w : V => w) j y K z) := by
    intro z hz
    have h := isMinOn_energy_add_iff (a := (innerSL ℝ : SesqForm ℝ V))
      SesqForm.innerSL_isHermitian zero_le_one SesqForm.innerSL_isCoerciveWith
      (innerSL ℝ y) hKcv hj hz
    rwa [coe_toOperator_innerSL, rieszRep_innerSL] at h
  obtain ⟨z, ⟨hzK, hzmin⟩, huniq⟩ := existsUnique_isMinOn_energy_add
    (a := (innerSL ℝ : SesqForm ℝ V)) SesqForm.innerSL_isHermitian one_pos
    SesqForm.innerSL_isCoerciveWith (innerSL ℝ y) hKne hKcl hKcv hj hjlsc
  exact ⟨z, (hiff z hzK).mp hzmin, fun x hx => huniq x ⟨hx.1, (hiff x hx.1).mpr hx⟩⟩

/-- **Unique solvability of the elliptic variational inequality.**  Atkinson–Han, *Theoretical
Numerical Analysis*, Theorem 11.3.1: for a nonempty closed convex `K` in a real Hilbert space, an
`A` strongly monotone with constant `c > 0` and Lipschitz with constant `L`, and a `j` convex and
lower semicontinuous on `K`, the variational inequality has exactly one solution for every datum
`f`.

The map sending `u` to the solution of the auxiliary inequality with operator the identity and
datum `u - θ (A u - f)` is nonexpansive in its datum, and the damping step `u ↦ u - θ (A u - f)`
contracts with factor `√(1 - 2 c θ + L² θ²)` for `0 < θ < 2c/L²` (`contractingWith_damped`); the
Banach fixed point theorem on the closed set `K` then produces the solution, and
`IsVariationalInequalitySolution.unique` its uniqueness. -/
theorem existsUnique_isVariationalInequalitySolution {K : Set V} (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K) {A : V → V} {c L : ℝ} (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith (Real.toNNReal L) A)
    {j : V → ℝ} (hj : ConvexOn ℝ K j) (hjlsc : LowerSemicontinuousOn j K) (f : V) :
    ∃! u, IsVariationalInequalitySolution A j f K u := by
  -- replace `L` by `L' = max L 1 > 0`, so that the damping parameter `θ = c / L'²` makes sense
  have hL' : (0 : ℝ) < max L 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlip' : LipschitzWith (Real.toNNReal (max L 1)) A :=
    hlip.weaken (Real.toNNReal_mono (le_max_left _ _))
  have hθ : 0 < c / max L 1 ^ 2 := by positivity
  have hθ' : c / max L 1 ^ 2 < 2 * c / max L 1 ^ 2 := by
    have h2 : 2 * c / max L 1 ^ 2 = c / max L 1 ^ 2 + c / max L 1 ^ 2 := by ring
    linarith
  have hcon := contractingWith_damped (𝕜 := ℝ) hc hL' hmono hlip' f hθ hθ'
  have hk0 : 0 ≤ Real.sqrt (1 - 2 * (c / max L 1 ^ 2) * c
      + (c / max L 1 ^ 2) ^ 2 * max L 1 ^ 2) := Real.sqrt_nonneg _
  have hk1 : Real.sqrt (1 - 2 * (c / max L 1 ^ 2) * c
      + (c / max L 1 ^ 2) ^ 2 * max L 1 ^ 2) < 1 := by
    have h := hcon.1
    rw [← NNReal.coe_lt_one, Real.coe_toNNReal _ (Real.sqrt_nonneg _)] at h
    exact h
  -- the damping step is a contraction
  have hdamp : ∀ x y : V, ‖x - (c / max L 1 ^ 2) • (A x - f)
      - (y - (c / max L 1 ^ 2) • (A y - f))‖
      ≤ Real.sqrt (1 - 2 * (c / max L 1 ^ 2) * c + (c / max L 1 ^ 2) ^ 2 * max L 1 ^ 2)
        * ‖x - y‖ := by
    intro x y
    have h := LipschitzWith.dist_le_mul hcon.2 x y
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _)] at h
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using h
  -- the auxiliary problem is uniquely solvable for every datum
  have hjθ : ConvexOn ℝ K (fun v => c / max L 1 ^ 2 * j v) := by
    simpa only [smul_eq_mul] using ConvexOn.smul hθ.le hj
  have hjθlsc : LowerSemicontinuousOn (fun v => c / max L 1 ^ 2 * j v) K :=
    lowerSemicontinuousOn_const_mul hθ hjlsc
  choose P hP _ using fun y : V => existsUnique_id hKne hKcl hKcv hjθ hjθlsc y
  have hmaps : Set.MapsTo (fun u => P (u - (c / max L 1 ^ 2) • (A u - f))) K K :=
    fun u _ => (hP _).1
  have hcontr : ∀ x ∈ K, ∀ y ∈ K,
      dist ((fun u => P (u - (c / max L 1 ^ 2) • (A u - f))) x)
        ((fun u => P (u - (c / max L 1 ^ 2) • (A u - f))) y)
      ≤ Real.sqrt (1 - 2 * (c / max L 1 ^ 2) * c + (c / max L 1 ^ 2) ^ 2 * max L 1 ^ 2)
        * dist x y := by
    intro x _ y _
    have hne := IsVariationalInequalitySolution.norm_sub_le one_pos
      (isStronglyMonotoneWith_id (𝕜 := ℝ) (E := V)) (hP (x - (c / max L 1 ^ 2) • (A x - f)))
      (hP (y - (c / max L 1 ^ 2) • (A y - f)))
    rw [div_one] at hne
    rw [dist_eq_norm, dist_eq_norm]
    exact hne.trans (hdamp x y)
  obtain ⟨x, ⟨hxK, hxfix⟩, -⟩ :=
    exists_unique_fixedPoint_of_mapsTo hKcl hKne hmaps hk0 hk1 hcontr
  have hsol : IsVariationalInequalitySolution A j f K x := by
    refine (isVarIneq_aux_iff hθ).mp ?_
    have h := hP (x - (c / max L 1 ^ 2) • (A x - f))
    rwa [hxfix] at h
  exact ⟨x, hsol, fun y hy => IsVariationalInequalitySolution.unique hc hmono hy hsol⟩

/-- **Stampacchia's theorem.**  Atkinson–Han, *Theoretical Numerical Analysis*, Theorem 11.3.6:
a variational inequality of the first kind — `j = 0` — over a nonempty closed convex set with a
strongly monotone Lipschitz operator has exactly one solution; it depends Lipschitz continuously
on the datum by `IsVariationalInequalitySolution.norm_sub_le`.

Kept under its classical name because that is what a reader looks for.  It generalizes the
Lax–Milgram lemma `SesqForm.laxMilgram`, which is the case where `K` is the whole space and `A` is
linear. -/
theorem stampacchia {K : Set V} (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K)
    {A : V → V} {c L : ℝ} (hc : 0 < c) (hmono : IsStronglyMonotoneWith ℝ A c)
    (hlip : LipschitzWith (Real.toNNReal L) A) (f : V) :
    ∃! u, IsVariationalInequalitySolution A 0 f K u :=
  existsUnique_isVariationalInequalitySolution hKne hKcl hKcv hc hmono hlip
    (convexOn_const 0 hKcv) lowerSemicontinuousOn_const f

/-- **The bilinear-form version.**  Atkinson–Han, *Theoretical Numerical Analysis*,
Theorem 11.3.9: for a bounded `V`-elliptic form `a` — not assumed symmetric — a functional `ℓ`,
and a `j` convex and lower semicontinuous on a nonempty closed convex `K`, the variational
inequality

  `u ∈ K`,  `ℓ (v - u) ≤ a u (v - u) + j v - j u`  for all `v ∈ K`

has exactly one solution.  Taking `j = 0` gives the inequality of the first kind and
`K = Set.univ` that of the second kind, and the solution depends Lipschitz continuously on `ℓ` by
`IsVariationalInequalitySolution.norm_sub_le`.

Immediate from `existsUnique_isVariationalInequalitySolution` applied to `A = a.toOperator`, whose
strong monotonicity is `SesqForm.isCoerciveWith_iff_toOperator` and whose Lipschitz constant is
`SesqForm.norm_toOperator`. -/
theorem existsUnique_isVariationalInequalitySolution_of_isCoercive {a : SesqForm ℝ V} {c : ℝ}
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) {K : Set V} (hKne : K.Nonempty) (hKcl : IsClosed K)
    (hKcv : Convex ℝ K) {j : V → ℝ} (hj : ConvexOn ℝ K j) (hjlsc : LowerSemicontinuousOn j K)
    (ℓ : V →L[ℝ] ℝ) :
    ∃! u, IsVariationalInequalitySolution a.toOperator j (SesqForm.rieszRep ℓ) K u := by
  have hmono : IsStronglyMonotoneWith ℝ (SesqForm.toOperator a : V → V) c :=
    LinearMap.IsCoerciveWith.isStronglyMonotoneWith
      ((SesqForm.isCoerciveWith_iff_toOperator a c).mp hcoer)
  have hlip : LipschitzWith (Real.toNNReal ‖a‖) (SesqForm.toOperator a : V → V) := by
    rw [← SesqForm.norm_toOperator a, ← coe_nnnorm, Real.toNNReal_coe]
    exact (SesqForm.toOperator a).lipschitzWith
  exact existsUnique_isVariationalInequalitySolution hKne hKcl hKcv hc hmono hlip hj hjlsc _

end Existence

/-! ### Minty's lemma and the special forms -/

/-- **Minty's lemma.**  Atkinson–Han, *Theoretical Numerical Analysis*, Lemma 11.3.8: for a
monotone `A` and a `j` convex on a convex `K`, a point `u ∈ K` solves the variational inequality
if and only if the *test* inequality

  `⟪f, v - u⟫ ≤ ⟪A v, v - u⟫ + j v - j u`  for every `v ∈ K`

holds, that is, with `A` evaluated at the test point rather than at the solution.

One direction is monotonicity; the other substitutes `u + t (v - u)`, uses convexity of `j` and
lets `t` tend to `0`, so that only continuity of `A` along the segments of `K` issuing from `u` is
needed — no Lipschitz continuity anywhere.  The value of the lemma is that the Minty form is
stable under weak limits. -/
theorem IsVariationalInequalitySolution.iff_minty {A : V → V} {j : V → ℝ} {f : V} {K : Set V}
    (hKcv : Convex ℝ K) (hj : ConvexOn ℝ K j) (hmono : IsStronglyMonotoneWith ℝ A 0) {u : V}
    (hu : u ∈ K)
    (hA : ∀ v ∈ K, ContinuousWithinAt (fun t : ℝ => A (u + t • (v - u))) (Ioi 0) 0) :
    IsVariationalInequalitySolution A j f K u ↔
      ∀ v ∈ K, inner ℝ f (v - u) ≤ inner ℝ (A v) (v - u) + j v - j u := by
  constructor
  · rintro ⟨-, h⟩ v hv
    have h1 := h v hv
    have h2 : 0 ≤ inner ℝ (A v - A u) (v - u) := by simpa using hmono v u
    rw [inner_sub_left] at h2
    linarith
  · intro h
    refine ⟨hu, fun v hv => ?_⟩
    -- the test inequality along the segment `[u, v]`, after dividing by `t`
    have hseg : ∀ t ∈ Ioo (0 : ℝ) 1,
        inner ℝ f (v - u) ≤ inner ℝ (A (u + t • (v - u))) (v - u) + j v - j u := by
      intro t ht
      have hmem : u + t • (v - u) ∈ K := Convex.add_smul_sub_mem hKcv hu hv ⟨ht.1.le, ht.2.le⟩
      have h1 := h _ hmem
      rw [show u + t • (v - u) - u = t • (v - u) by abel, real_inner_smul_right,
        real_inner_smul_right] at h1
      have hjc : j (u + t • (v - u)) ≤ (1 - t) * j u + t * j v := by
        have hcv := hj.2 hu hv (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
        rw [show (1 - t) • u + t • v = u + t • (v - u) by module] at hcv
        simpa using hcv
      have ht0 := ht.1
      nlinarith
    have hcont : ContinuousWithinAt
        (fun t : ℝ => inner ℝ (A (u + t • (v - u))) (v - u) + j v - j u) (Ioi 0) 0 := by
      have hin : Continuous fun x : V => inner ℝ x (v - u) :=
        continuous_inner.comp (continuous_id.prodMk continuous_const)
      exact ((hin.continuousAt.comp_continuousWithinAt (hA v hv)).add
        continuousWithinAt_const).sub continuousWithinAt_const
    have hlim : Tendsto (fun t : ℝ => inner ℝ (A (u + t • (v - u))) (v - u) + j v - j u)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (A u) (v - u) + j v - j u)) := by
      have hc := hcont
      simp only [ContinuousWithinAt, zero_smul, add_zero] at hc
      exact hc
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht using hseg t ht

/-- **The variational inequality as an energy projection.**  For a symmetric coercive `A` and
`j = 0`, the solution `u` of the variational inequality over a convex `K` is the best
approximation, in the energy inner product of `A`, to the solution `w` of the unconstrained
equation `A w = f`.

So the inequality is solved by solving the variational equation and projecting onto `K` in the
energy inner product.  Atkinson–Han, *Theoretical Numerical Analysis*, the remark following
Example 11.3.11. -/
theorem IsVariationalInequalitySolution.isBestApprox_energy {A : V →ₗ[ℝ] V}
    (hA : A.IsSymmetricCoercive) {K : Set V} (hKcv : Convex ℝ K) {f w u : V} (hw : A w = f)
    (hsol : IsVariationalInequalitySolution A 0 f K u) :
    IsBestApprox (WithEnergy.equiv A hA '' K) (WithEnergy.equiv A hA w)
      (WithEnergy.equiv A hA u) := by
  have hK' : Convex ℝ (WithEnergy.equiv A hA '' K) := by
    simpa using Convex.linear_image hKcv (WithEnergy.equiv A hA).toLinearMap
  have hmem : WithEnergy.equiv A hA u ∈ WithEnergy.equiv A hA '' K := ⟨u, hsol.1, rfl⟩
  refine (isBestApprox_iff_inner_le_zero hK' hmem).2 ?_
  rintro _ ⟨v, hv, rfl⟩
  have hvi := hsol.2 v hv
  simp only [Pi.zero_apply, sub_zero, add_zero] at hvi
  rw [← map_sub, ← map_sub, WithEnergy.inner_equiv, energyInner, map_sub, hw, inner_sub_left]
  linarith

/-- **The cone form.**  Atkinson–Han, *Theoretical Numerical Analysis*, Exercise 11.3.3: when `K`
is a convex cone and `j = 0`, the variational inequality is equivalent to the pair of relations
`⟪f, v⟫ ≤ ⟪A u, v⟫` for all `v ∈ K` and `⟪A u, u⟫ = ⟪f, u⟫`.

Testing at `2u` and at `0` gives the equality, and testing at `u + v` the inequality; conversely
subtracting the equality from the inequality at `v` returns the variational inequality. -/
theorem IsVariationalInequalitySolution.iff_of_isCone {A : V → V} {f : V} {K : Set V}
    (hKcv : Convex ℝ K) (hKcone : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K, t • x ∈ K) {u : V} (hu : u ∈ K) :
    IsVariationalInequalitySolution A 0 f K u ↔
      (∀ v ∈ K, inner ℝ f v ≤ inner ℝ (A u) v) ∧ inner ℝ (A u) u = inner ℝ f u := by
  have hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K := by
    intro x hx y hy
    have hm : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ K :=
      hKcv hx hy (by norm_num) (by norm_num) (by norm_num)
    have h2 := hKcone 2 (by norm_num) _ hm
    rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
      one_smul] at h2
  constructor
  · rintro ⟨-, h⟩
    have h2u := h ((2 : ℝ) • u) (hKcone 2 (by norm_num) _ hu)
    have h0 := h 0 (by simpa using hKcone 0 le_rfl _ hu)
    rw [show (2 : ℝ) • u - u = u by module] at h2u
    rw [zero_sub, inner_neg_right, inner_neg_right] at h0
    simp only [Pi.zero_apply, sub_zero, add_zero] at h2u h0
    have heq : inner ℝ (A u) u = inner ℝ f u := le_antisymm (by linarith) h2u
    refine ⟨fun v hv => ?_, heq⟩
    have hv' := h (u + v) (hadd u hu v hv)
    rw [show u + v - u = v by abel] at hv'
    simpa using hv'
  · rintro ⟨hle, heq⟩
    refine ⟨hu, fun v hv => ?_⟩
    have hv' := hle v hv
    rw [inner_sub_right, inner_sub_right]
    simp only [Pi.zero_apply, sub_zero, add_zero]
    linarith

/-- **The positively homogeneous form.**  Atkinson–Han, *Theoretical Numerical Analysis*,
Exercise 11.3.10: for an inequality of the second kind — `K = Set.univ` — whose `j` is convex and
positively homogeneous, the inequality is equivalent to `⟪f, v⟫ ≤ ⟪A u, v⟫ + j v` for every `v`
together with `⟪A u, u⟫ + j u = ⟪f, u⟫`.

Convexity and positive homogeneity make `j` subadditive, which is what turns the test at `u + v`
into the inequality at `v`; this identity is behind the Lagrange multiplier reformulation of a
friction problem. -/
theorem IsVariationalInequalitySolution.iff_of_isPositiveHomogeneous {A : V → V} {j : V → ℝ}
    {f : V} (hj : ConvexOn ℝ univ j) (hhom : ∀ t : ℝ, 0 < t → ∀ v, j (t • v) = t * j v) {u : V} :
    IsVariationalInequalitySolution A j f univ u ↔
      (∀ v, inner ℝ f v ≤ inner ℝ (A u) v + j v) ∧ inner ℝ (A u) u + j u = inner ℝ f u := by
  have hj0 : j 0 = 0 := by
    have h := hhom 2 (by norm_num) 0
    rw [smul_zero] at h
    linarith
  have hsub : ∀ x y : V, j (x + y) ≤ j x + j y := by
    intro x y
    have hm := hj.2 (mem_univ x) (mem_univ y) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [show (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = (1 / 2 : ℝ) • (x + y) by module,
      hhom _ (by norm_num) _] at hm
    simp only [smul_eq_mul] at hm
    linarith
  constructor
  · rintro ⟨-, h⟩
    have h2u := h ((2 : ℝ) • u) (mem_univ _)
    have h0 := h 0 (mem_univ _)
    rw [show (2 : ℝ) • u - u = u by module, hhom 2 (by norm_num) u] at h2u
    rw [zero_sub, inner_neg_right, inner_neg_right, hj0] at h0
    have heq : inner ℝ (A u) u + j u = inner ℝ f u := le_antisymm (by linarith) (by linarith)
    refine ⟨fun v => ?_, heq⟩
    have hv' := h (u + v) (mem_univ _)
    rw [show u + v - u = v by abel] at hv'
    have hs := hsub u v
    linarith
  · rintro ⟨hle, heq⟩
    refine ⟨mem_univ _, fun v _ => ?_⟩
    have hv' := hle v
    rw [inner_sub_right, inner_sub_right]
    linarith
