import Numlib.Variational.Galerkin

/-!
# The Aubin–Nitsche duality argument

An error bound for a Galerkin approximation measured in a norm *weaker* than the one the form is
coercive in.  The setting is two inner product spaces `V` and `H` and a continuous linear map
`ι : V →L[𝕜] H`, standing for the embedding of the energy space into the pivot space; in the
finite element application it is `H¹(Ω) ⊆ L²(Ω)`, but nothing below needs a function space.

Given an error `e : V` that is orthogonal to a subspace `K` in the form `a`, and a solution `φ` of
the *dual* problem `a v φ = ⟪ι v, ι e⟫` for all `v`, testing the dual problem at `v = e` gives
`‖ι e‖² = a e φ`; orthogonality then replaces `φ` by `φ - w` for any `w ∈ K`, and boundedness of
the form finishes:

  `‖ι e‖² ≤ M ‖e‖ ‖φ - w‖`.

That is the whole of the argument, and `norm_map_sq_le_of_dual` states it pointwise — no
infimum, no supremum, and no existence claim for `φ`.  `norm_map_le_of_dual_approx` is the form in
which it is used: if the dual solutions can be approximated from `K` to within `δ` times the norm
of the datum, the error in the weaker norm gains the whole factor `δ`, `‖ι e‖ ≤ M δ ‖e‖`.  In a
finite element space `δ` is of order `h`, which is where the extra power of `h` in an `L²` error
estimate comes from; the bound on `δ` itself is elliptic regularity theory and is not part of the
argument.

The theorem is due to Aubin and to Nitsche; the account followed here is Theorem 10.4.3 and
Corollary 10.4.4 of Atkinson–Han[^atkinson-han].

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

variable {𝕜 V H : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The Aubin–Nitsche estimate, pointwise form: for a form `a` bounded with constant `M`, an error
`e` orthogonal to `K` in `a`, and a solution `φ` of the dual problem `a v φ = ⟪ι v, ι e⟫`,

  `‖ι e‖ ^ 2 ≤ M * ‖e‖ * ‖φ - w‖`  for every `w ∈ K`.

Testing the dual problem at `v = e` turns `‖ι e‖ ^ 2` into `a e φ`, orthogonality replaces `φ` by
`φ - w`, and boundedness of `a` does the rest. -/
theorem norm_map_sq_le_of_dual {a : SesqForm 𝕜 V} {M : ℝ} (hM : a.IsBoundedWith M)
    {K : Submodule 𝕜 V} (ι : V →L[𝕜] H) {e : V} (horth : ∀ v ∈ K, a e v = 0) {φ : V}
    (hφ : ∀ v : V, a v φ = inner 𝕜 (ι v) (ι e)) {w : V} (hw : w ∈ K) :
    ‖ι e‖ ^ 2 ≤ M * ‖e‖ * ‖φ - w‖ := by
  have hsub : a e (φ - w) = a e φ := by rw [map_sub, horth w hw, sub_zero]
  calc ‖ι e‖ ^ 2 = RCLike.re (inner 𝕜 (ι e) (ι e) : 𝕜) := by
        rw [inner_self_eq_norm_sq_to_K]; simp
    _ = RCLike.re (a e (φ - w)) := by rw [hsub, hφ e]
    _ ≤ ‖a e (φ - w)‖ := RCLike.re_le_norm _
    _ ≤ M * ‖e‖ * ‖φ - w‖ := hM _ _

/-- The Aubin–Nitsche estimate with a uniform bound on the approximation of the dual solutions: if
every datum `g : H` gives a dual solution `φ` whose distance to `K` is at most `δ ‖g‖`, then an
error `e` orthogonal to `K` in `a` satisfies `‖ι e‖ ≤ M * δ * ‖e‖`.

The duality argument gains exactly the approximation power of the dual problem, which is one power
of the mesh size more than the energy-norm estimate has. -/
theorem norm_map_le_of_dual_approx {a : SesqForm 𝕜 V} {M δ : ℝ} (hM : a.IsBoundedWith M)
    (hδ : 0 ≤ δ) {K : Submodule 𝕜 V} (ι : V →L[𝕜] H) {e : V} (horth : ∀ v ∈ K, a e v = 0)
    (hdual : ∀ g : H, ∃ φ : V, (∀ v : V, a v φ = inner 𝕜 (ι v) g) ∧
      Metric.infDist φ (K : Set V) ≤ δ * ‖g‖) :
    ‖ι e‖ ≤ M * δ * ‖e‖ := by
  have hKne : (K : Set V).Nonempty := ⟨0, K.zero_mem⟩
  have hMe : 0 ≤ M * ‖e‖ := by
    rcases eq_or_lt_of_le (norm_nonneg e) with h | h
    · simp [← h]
    · nlinarith [norm_nonneg (a e e), hM e e]
  obtain ⟨φ, hφ, hφd⟩ := hdual (ι e)
  rcases eq_or_lt_of_le (norm_nonneg (ι e)) with h0 | h0
  · rw [← h0]
    linarith [mul_nonneg hδ hMe]
  · have key : ‖ι e‖ ^ 2 ≤ M * ‖e‖ * Metric.infDist φ (K : Set V) := by
      rcases eq_or_lt_of_le hMe with hMe0 | hMe0
      · have := norm_map_sq_le_of_dual hM ι horth hφ K.zero_mem
        rw [← hMe0] at this ⊢
        simpa using this
      · have hne : M * ‖e‖ ≠ 0 := ne_of_gt hMe0
        refine le_of_forall_pos_le_add fun ε hε => ?_
        have hcancel : M * ‖e‖ * (ε / (M * ‖e‖)) = ε := by
          rw [mul_comm, div_mul_cancel₀ ε hne]
        obtain ⟨w, hw, hwd⟩ := (Metric.infDist_lt_iff hKne).mp
          (lt_add_of_pos_right (Metric.infDist φ (K : Set V)) (div_pos hε hMe0))
        calc ‖ι e‖ ^ 2 ≤ M * ‖e‖ * ‖φ - w‖ := norm_map_sq_le_of_dual hM ι horth hφ hw
          _ = M * ‖e‖ * dist φ w := by rw [dist_eq_norm]
          _ ≤ M * ‖e‖ * (Metric.infDist φ (K : Set V) + ε / (M * ‖e‖)) :=
              mul_le_mul_of_nonneg_left hwd.le hMe
          _ = M * ‖e‖ * Metric.infDist φ (K : Set V) + ε := by rw [mul_add, hcancel]
    have hle : ‖ι e‖ ^ 2 ≤ M * ‖e‖ * (δ * ‖ι e‖) :=
      key.trans (mul_le_mul_of_nonneg_left hφd hMe)
    exact le_of_mul_le_mul_right (by linarith : ‖ι e‖ * ‖ι e‖ ≤ M * δ * ‖e‖ * ‖ι e‖) h0
