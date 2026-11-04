/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Polynomial.SignRight
import NumlibSurface.ConnGouldToint.Chapter07.Section03Cholesky

/-!
# One-sided stabilization in the hard case

A greedy Cholesky row comparison is rational once its previous signs
are fixed. Polynomial right-hand signs then control the branch decisions
in the corrected LINPACK recurrence of [conn2000trust].
-/

namespace ConnGouldToint.Chapter07

open Matrix Filter Set Polynomial WithLp Subproblem
open scoped Topology RealInnerProductSpace

private noncomputable def linpackRowSum {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (· < i), L i j * linpackForwardSubst L j

/-- The right-hand-side signs selected in the shifted greedy forward solve. -/
noncomputable def linpackShiftedSigns {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (x : ℝ) (i : Fin n) : ℝ :=
  linpackSign (linpackRowSum (cholesky (M + x • 1)) i)

private theorem linpackSign_eq_of_sign_eq {x y : ℝ} (h : SignType.sign x = SignType.sign y) :
    linpackSign x = linpackSign y := by
  have hchoice (t : ℝ) : |(1 : ℝ) - t| ≥ |-1 - t| ↔ t ≤ 0 := by
    change |-1 - t| ≤ |1 - t| ↔ t ≤ 0
    rw [← sq_le_sq₀ (abs_nonneg ((-1 : ℝ) - t)) (abs_nonneg ((1 : ℝ) - t)), sq_abs, sq_abs]
    constructor <;> intro ht <;> nlinarith
  have hs : x ≤ 0 ↔ y ≤ 0 := by
    rw [← sign_nonpos_iff (a := x), ← sign_nonpos_iff (a := y), h]
  simp only [linpackSign, hchoice, hs]

private theorem linpack_row_sum_mul_det {n : ℕ} {A L : Matrix (Fin n) (Fin n) ℝ}
    (hL : L.IsLowerTriangular) (hd : ∀ j, L j j ≠ 0) (hfact : L * Lᵀ = A)
    (i : Fin n) :
    let ι := {j : Fin n // j < i}
    let B := A.submatrix (Subtype.val : ι → Fin n) (Subtype.val : ι → Fin n)
    let c : ι → ℝ := fun j => A i j
    let v : ι → ℝ := fun j => linpackSign (linpackRowSum L j)
    B.det * linpackRowSum L i = c ⬝ᵥ B.adjugate *ᵥ v := by
  let ι := {j : Fin n // j < i}
  let B := A.submatrix (Subtype.val : ι → Fin n) (Subtype.val : ι → Fin n)
  let P := L.submatrix (Subtype.val : ι → Fin n) (Subtype.val : ι → Fin n)
  let ℓ : ι → ℝ := fun j => L i j
  let c : ι → ℝ := fun j => A i j
  let w : ι → ℝ := fun j => linpackForwardSubst L j
  let v : ι → ℝ := fun j => linpackSign (linpackRowSum L j)
  have hsub (f : Fin n → ℝ) :
      (∑ j : ι, f j) = ∑ j ∈ Finset.univ.filter (· < i), f j :=
    (Finset.sum_subtype _ Finset.mem_filter_univ f).symm
  have hrestrict (j : ι) (f : Fin n → ℝ) :
      (∑ t : ι, L j t * f t) = ∑ t : Fin n, L j t * f t := by
    rw [hsub (fun t => L j t * f t)]
    exact Finset.sum_filter_of_ne fun t _ ht => by
      by_contra! hti
      exact ht (by rw [hL (j.2.trans_le hti), zero_mul])
  have hP : P.IsLowerTriangular := fun j t hjt => hL (show (j : Fin n) < t from hjt)
  have hPB : P * Pᵀ = B := by
    ext j t
    change (∑ l : ι, L j l * L t l) = A j t
    rw [hrestrict j (L t)]
    exact congrFun (congrFun hfact j.val) t.val
  have hc : P *ᵥ ℓ = c := by
    ext j
    change (∑ t : ι, L j t * L i t) = A i j
    rw [hrestrict j (L i)]
    simpa [Matrix.mul_apply, mul_comm] using congrFun (congrFun hfact i) j.val
  have hw : P *ᵥ w = v := by
    have h := (linpack_triangular_solves hL hd).1
    ext j
    change (∑ t : ι, L j t * linpackForwardSubst L t) = _
    rw [hrestrict j (linpackForwardSubst L)]
    exact congrFun h j.val
  let y := Pᵀ.backSubst w
  have hy : Pᵀ *ᵥ y = w := Matrix.mulVec_backSubst _ (fun _ _ hjt => hP hjt) (fun j => hd j)
  have hsolve : B *ᵥ y = v := by
    rw [← hPB, ← Matrix.mulVec_mulVec, hy, hw]
  have hdet : B.adjugate *ᵥ v = B.det • y := by
    rw [← hsolve, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hrow : linpackRowSum L i = c ⬝ᵥ y := by
    unfold linpackRowSum
    rw [← hsub (fun t => L i t * linpackForwardSubst L t), ← hc,
      dotProduct_comm (P *ᵥ ℓ) y, ← Matrix.dotProduct_transpose_mulVec, hy]
    rfl
  change B.det * linpackRowSum L i = c ⬝ᵥ B.adjugate *ᵥ v
  rw [hrow, hdet, dotProduct_smul, smul_eq_mul]

private noncomputable def polynomialShift {ι : Type*} [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Matrix ι ι ℝ[X] :=
  A.map Polynomial.C + (Polynomial.X : ℝ[X]) • (1 : Matrix ι ι ℝ[X])

private theorem eval_polynomialShift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : ℝ) :
    (Polynomial.evalRingHom x).mapMatrix (polynomialShift A) = A + x • 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [polynomialShift, RingHom.mapMatrix_apply, Matrix.one_apply_eq]
  · simp [polynomialShift, RingHom.mapMatrix_apply, Matrix.one_apply_ne h]

/-- The signs in the corrected greedy solve are constant sufficiently near
the pole on its positive-definite side. Each row uses a polynomial numerator
for its forward contribution after fixing the signs of its predecessors. -/
theorem linpackShiftedSigns_eventually_constant {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    {a : ℝ} (hpos : ∀ᶠ x in 𝓝[>] a, (M + x • 1).PosDef) :
    ∃ v : Fin n → ℝ, ∀ᶠ x in 𝓝[>] a, linpackShiftedSigns M x = v := by
  classical
  have hsingle (i : Fin n) : ∃ v : ℝ, ∀ᶠ x in 𝓝[>] a, linpackShiftedSigns M x i = v := by
    induction i using WellFounded.induction (wellFounded_lt (α := Fin n)) with
    | h i ih =>
      let ι := {j : Fin n // j < i}
      have hprev (j : ι) := ih j.val j.2
      choose v hv using hprev
      have hvall : ∀ᶠ x in 𝓝[>] a, ∀ j : ι, linpackShiftedSigns M x j = v j :=
        Filter.eventually_all.mpr hv
      let P := M.submatrix (Subtype.val : ι → Fin n) (Subtype.val : ι → Fin n)
      let c : ι → ℝ := fun j => M i j
      let p : ℝ[X] := (fun j => Polynomial.C (c j)) ⬝ᵥ
        (polynomialShift P).adjugate *ᵥ (fun j => Polynomial.C (v j))
      have heval (x : ℝ) : p.eval x = c ⬝ᵥ (P + x • 1).adjugate *ᵥ v := by
        have hm := (Polynomial.evalRingHom x).map_adjugate (polynomialShift P)
        rw [eval_polynomialShift] at hm
        change ((fun j => Polynomial.C (c j)) ⬝ᵥ
          (polynomialShift P).adjugate *ᵥ (fun j => Polynomial.C (v j))).eval x = _
        have hentry (j k : ι) : ((polynomialShift P).adjugate j k).eval x =
            (P + x • 1).adjugate j k := congrFun (congrFun hm j) k
        simp only [dotProduct, Matrix.mulVec, Polynomial.eval_finsetSum, Polynomial.eval_mul,
          Polynomial.eval_C, hentry]
      obtain ⟨s, hs⟩ := Polynomial.exists_eventually_sign_eq a p
      have hsgn : ∀ᶠ x in 𝓝[>] a, SignType.sign
          (linpackRowSum (cholesky (M + x • 1)) i) = s := by
        filter_upwards [hpos, hvall, hs] with x hpd hx hsign
        let A := M + x • 1
        let L := cholesky A
        have hchol := isCholesky_cholesky hpd
        have hL : L.IsLowerTriangular := isLowerTriangular_cholesky A
        have hd (j : Fin n) : L j j ≠ 0 := by
          simpa [L, Matrix.conjTranspose_eq_transpose_of_trivial] using hchol.diag_ne_zero j
        have hf : L * Lᵀ = A := by
          simpa [L, Matrix.conjTranspose_eq_transpose_of_trivial] using hchol.conjTranspose_mul_self
        have hB : A.submatrix (Subtype.val : ι → Fin n) (Subtype.val : ι → Fin n) = P + x • 1 := by
          ext j k
          by_cases hjk : j = k
          · subst k
            simp [A, P, Matrix.one_apply_eq]
          · have hne : (j : Fin n) ≠ k := fun h => hjk (Subtype.ext h)
            simp [A, P, Matrix.one_apply_ne hjk, Matrix.one_apply_ne hne]
        have hc : (fun j : ι => A i j) = c := by
          funext j
          simp [A, c, Matrix.one_apply_ne (ne_of_gt j.2)]
        have hv' : (fun j : ι => linpackSign (linpackRowSum L j)) = v := funext hx
        have hp := linpack_row_sum_mul_det hL hd hf i
        dsimp only at hp
        rw [hB, hc, hv', ← heval x] at hp
        have hdet : 0 < (P + x • 1).det := by
          rw [← hB]
          exact (hpd.submatrix Subtype.val_injective).det_pos
        rw [← hp, sign_mul, sign_pos hdet, one_mul] at hsign
        exact hsign
      obtain ⟨x₀, hx₀⟩ := hsgn.exists
      exact ⟨linpackShiftedSigns M x₀ i, hsgn.mono fun x hx =>
        linpackSign_eq_of_sign_eq (hx.trans hx₀.symm)⟩
  choose v hv using hsingle
  exact ⟨v, (Filter.eventually_all.mpr hv).mono fun _ h => funext h⟩

private theorem linpackEuclideanDirection_smul {n : ℕ} (y : Fin n → ℝ)
    {c : ℝ} (hc : 0 < c) :
    linpackEuclideanDirection (c • y) = linpackEuclideanDirection y := by
  unfold linpackEuclideanDirection
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc, _root_.mul_inv_rev, smul_smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

private theorem normalizedPolynomialVector_tendsto {n : ℕ} (a : ℝ)
    (p : Fin n → ℝ[X]) (hp : ∃ i, p i ≠ 0) :
    ∃ u : EuclideanSpace ℝ (Fin n), Tendsto
      (fun x => linpackEuclideanDirection (fun i => (p i).eval x)) (𝓝[>] a) (𝓝 u) := by
  classical
  have hex : ∃ m, ∃ i, p i ≠ 0 ∧ (p i).rootMultiplicity a = m := by
    obtain ⟨i, hi⟩ := hp
    exact ⟨_, i, hi, rfl⟩
  let m := Nat.find hex
  obtain ⟨i₀, hi₀, hm⟩ := Nat.find_spec hex
  have hdvd (i : Fin n) : (X - C a)^m ∣ p i := by
    by_cases h : p i = 0
    · simp [h]
    have hmin : m ≤ (p i).rootMultiplicity a := Nat.find_min' hex ⟨i, h, rfl⟩
    exact (le_rootMultiplicity_iff h).1 hmin
  choose q hq using hdvd
  have hq₀ : (q i₀).eval a ≠ 0 := by
    intro hz
    have hdz : X - C a ∣ q i₀ := dvd_iff_isRoot.mpr hz
    have hmore : (X - C a)^((p i₀).rootMultiplicity a + 1) ∣ p i₀ := by
      rw [hm, hq i₀, pow_succ]
      exact mul_dvd_mul_left _ hdz
    exact pow_rootMultiplicity_not_dvd hi₀ a hmore
  let f := fun x => (toLp 2 (fun i => (q i).eval x) : EuclideanSpace ℝ (Fin n))
  have hf : Continuous f := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => (q i).continuous)
  have hf₀ : f a ≠ 0 := fun hz => hq₀ (congrFun (congrArg ofLp hz) i₀)
  have ht : Tendsto f (𝓝[>] a) (𝓝 (f a)) := hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨‖f a‖⁻¹ • f a, ((ht.norm.inv₀ (norm_ne_zero_iff.mpr hf₀)).smul ht).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  have heq : (fun i => (p i).eval x) = (x - a)^m • (fun i => (q i).eval x) := by
    funext i
    rw [hq i, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    rfl
  change linpackEuclideanDirection (fun i => (q i).eval x) =
    linpackEuclideanDirection (fun i => (p i).eval x)
  rw [heq, linpackEuclideanDirection_smul _ (pow_pos (sub_pos.mpr hx) _)]

private noncomputable def adjugatePolynomialVec {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : Fin n → ℝ[X] :=
  (polynomialShift M).adjugate *ᵥ (fun i => C (v i))

private theorem eval_adjugatePolynomialVec {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (x : ℝ) :
    (fun i => (adjugatePolynomialVec M v i).eval x) = (M + x • 1).adjugate *ᵥ v := by
  have hm := (Polynomial.evalRingHom x).map_adjugate (polynomialShift M)
  rw [eval_polynomialShift] at hm
  have he (i j : Fin n) : ((polynomialShift M).adjugate i j).eval x =
      (M + x • 1).adjugate i j := congrFun (congrFun hm i) j
  funext i
  simp only [adjugatePolynomialVec, Matrix.mulVec, dotProduct, eval_finsetSum,
    eval_mul, eval_C, he]

private theorem linpack_backsolve_mul_shift {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    {x : ℝ} (hpd : (M + x • 1).PosDef) :
    let A := M + x • 1
    let L := cholesky A
    let y := Lᵀ.backSubst (linpackForwardSubst L)
    A *ᵥ y = linpackShiftedSigns M x := by
  have hchol := isCholesky_cholesky hpd
  let A := M + x • 1
  let L := cholesky A
  have hd (j : Fin n) : L j j ≠ 0 := by
    simpa [L, Matrix.conjTranspose_eq_transpose_of_trivial] using hchol.diag_ne_zero j
  have hf : L * Lᵀ = A := by
    simpa [L, Matrix.conjTranspose_eq_transpose_of_trivial] using hchol.conjTranspose_mul_self
  obtain ⟨hw, hy, -⟩ := linpack_triangular_solves (isLowerTriangular_cholesky A) hd
  change A *ᵥ (Lᵀ.backSubst (linpackForwardSubst L)) = _
  rw [← hf, ← Matrix.mulVec_mulVec, hy]
  exact hw

/-- The actual normalized back solve has a one-sided vector limit. Its
eventually fixed signs make it an adjugate polynomial vector up to a
positive scalar. Removing the common vanishing factor gives the limit. -/
theorem linpackDirection_eventually_tendsto {n : ℕ} (hn : 0 < n)
    {M : Matrix (Fin n) (Fin n) ℝ} {a : ℝ}
    (hpos : ∀ᶠ x in 𝓝[>] a, (M + x • 1).PosDef) :
    ∃ v : Fin n → ℝ, (∀ᶠ x in 𝓝[>] a, linpackShiftedSigns M x = v) ∧
      ∃ u : EuclideanSpace ℝ (Fin n),
        Tendsto (fun x =>
          let L := cholesky (M + x • 1)
          linpackEuclideanDirection (Lᵀ.backSubst (linpackForwardSubst L))) (𝓝[>] a) (𝓝 u) := by
  obtain ⟨v, hv⟩ := linpackShiftedSigns_eventually_constant hpos
  let p := adjugatePolynomialVec M v
  obtain ⟨x₀, hpd₀, hv₀⟩ := (hpos.and hv).exists
  have hvne : v ≠ 0 := by
    intro h
    let i : Fin n := ⟨0, hn⟩
    have hs := abs_linpackSign (linpackRowSum (cholesky (M + x₀ • 1)) i)
    change |linpackShiftedSigns M x₀ i| = 1 at hs
    rw [hv₀, h] at hs
    norm_num at hs
  have hp : ∃ i, p i ≠ 0 := by
    by_contra! hall
    have hzero : (M + x₀ • 1).adjugate *ᵥ v = 0 := by
      rw [← eval_adjugatePolynomialVec]
      ext i
      simp only [← show p = adjugatePolynomialVec M v from rfl, hall, eval_zero, Pi.zero_apply]
    have hz := congrArg (fun z => (M + x₀ • 1) *ᵥ z) hzero
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_zero] at hz
    exact hvne ((smul_eq_zero.mp hz).resolve_left hpd₀.det_pos.ne')
  obtain ⟨u, hu⟩ := normalizedPolynomialVector_tendsto a p hp
  refine ⟨v, hv, u, hu.congr' ?_⟩
  filter_upwards [hpos, hv] with x hpd hx
  let A := M + x • 1
  let L := cholesky A
  let y := Lᵀ.backSubst (linpackForwardSubst L)
  have hsol : A *ᵥ y = v := (linpack_backsolve_mul_shift hpd).trans hx
  have heq : (fun i => (p i).eval x) = A.det • y := by
    change (fun i => (adjugatePolynomialVec M v i).eval x) = A.det • y
    rw [eval_adjugatePolynomialVec, ← hsol, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  change linpackEuclideanDirection (fun i => (p i).eval x) = linpackEuclideanDirection y
  rw [heq, linpackEuclideanDirection_smul _ hpd.det_pos]

/-- For a strict interior shifted solve, the sign of its inner product with
the correction direction determines which of the two roots minimizes the
model. A zero inner product uses the positive-square-root convention. -/
theorem moreSorensenBestBoundaryCoefficient_eq_ite_inner {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g s u : E} {H : E →L[ℝ] E} {x Δ : ℝ}
    (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (hs : (H + x • (1 : E →L[ℝ] E)) s = -g) (hraw : ‖s‖ < Δ) (hu : ‖u‖ = 1)
    (hcurv : 0 < ⟪u, (H + x • (1 : E →L[ℝ] E)) u⟫) :
    moreSorensenBestBoundaryCoefficient g H Δ s u =
      if 0 ≤ ⟪s, u⟫ then moreSorensenBoundaryCoefficient Δ s u
      else -moreSorensenBoundaryCoefficient Δ s (-u) := by
  let a := moreSorensenBoundaryCoefficient Δ s u
  let b := -moreSorensenBoundaryCoefficient Δ s (-u)
  let c := ⟪s, u⟫
  let d := √(Δ ^ 2 - ‖s‖ ^ 2 + c ^ 2)
  let curv := ⟪u, (H + x • (1 : E →L[ℝ] E)) u⟫
  have hd : 0 < d := Real.sqrt_pos.2
    (add_pos_of_pos_of_nonneg
      (sub_pos.2 (pow_lt_pow_left₀ hraw (norm_nonneg _) two_ne_zero)) (sq_nonneg _))
  have ha : ‖s + a • u‖ = Δ := norm_add_boundaryCorrection hraw.le hu
  have hb : ‖s + b • u‖ = Δ := by
    simpa only [b, neg_smul, smul_neg] using
      norm_add_boundaryCorrection (u := -u) hraw.le (by simpa using hu)
  have ha' : a = d - c := rfl
  have hb' : b = -d - c := by
    simp only [b, d, c, moreSorensenBoundaryCoefficient, inner_neg_right, neg_sq]
    ring
  have hq (t : ℝ) (ht : ‖s + t • u‖ = Δ) :
      quadModel g H (s + t • u) - quadModel g H s =
        (1 / 2) * t^2 * curv + x / 2 * (‖s‖ ^ 2 - Δ ^ 2) := by
    have h := quadModel_sub_eq_of_shifted hH hs (s + t • u)
    rw [add_sub_cancel_left, ht, map_smul, real_inner_smul_left, real_inner_smul_right] at h
    dsimp only [curv]
    rw [h]
    ring
  have hdiff : quadModel g H (s + a • u) - quadModel g H (s + b • u) =
      -(2 * d * curv * c) := by
    calc
      _ = (quadModel g H (s + a • u) - quadModel g H s) -
          (quadModel g H (s + b • u) - quadModel g H s) := by ring
      _ = _ := by rw [hq a ha, hq b hb, ha', hb']; ring
  have hchoice : quadModel g H (s + a • u) ≤ quadModel g H (s + b • u) ↔ 0 ≤ c := by
    rw [← sub_nonpos, hdiff, neg_nonpos, mul_nonneg_iff_of_pos_left]
    exact mul_pos (mul_pos two_pos hd) hcurv
  unfold moreSorensenBestBoundaryCoefficient
  exact if_congr hchoice rfl rfl

section Shifted

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
local notation "Mop" => toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M

private theorem computedStep_inner_nonneg_eventually (hn : 0 < n) {a : ℝ}
    (hM : (Mop : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    (g : EuclideanSpace ℝ (Fin n)) (hapos : a = -leftmost hM)
    {v : Fin n → ℝ} (hv : ∀ᶠ x in 𝓝[>] a, linpackShiftedSigns M x = v)
    (hpd : ∀ᶠ x in 𝓝[>] a, (M + x • 1).PosDef) :
    ∃ c : Prop, ∀ᶠ x in 𝓝[>] a,
      let L := cholesky (M + x • 1)
      let y := Lᵀ.backSubst (linpackForwardSubst L)
      (0 ≤ ⟪shiftedStep g Mop x, linpackEuclideanDirection y⟫) ↔ c := by
  let P := adjugatePolynomialVec M (-ofLp g)
  let Q := adjugatePolynomialVec M v
  let p := P ⬝ᵥ Q
  obtain ⟨sgn, hsgn⟩ := Polynomial.exists_eventually_sign_eq a p
  refine ⟨0 ≤ sgn, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hv, hpd, hsgn] with x hx hvx hpx hs
  have hx' : -leftmost hM < x := hapos ▸ hx
  let A := M + x • 1
  let L := cholesky A
  let y := Lᵀ.backSubst (linpackForwardSubst L)
  let z := shiftedStep g Mop x
  have hzsolve : A *ᵥ ofLp z = -ofLp g := by
    have hz := (step_spec (g := g) (H := Mop) (hH := hM) hx').1
    change (Mop + x • 1) z = -g at hz
    rw [← toEuclideanCLM_add_smul_one, ← WithLp.toLp_ofLp 2 z, toEuclideanCLM_toLp] at hz
    exact congrArg ofLp hz
  have hysolve : A *ᵥ y = v := (linpack_backsolve_mul_shift hpx).trans hvx
  have hP : (fun i => (P i).eval x) = A.det • ofLp z := by
    change (fun i => (adjugatePolynomialVec M (-ofLp g) i).eval x) = _
    rw [eval_adjugatePolynomialVec, ← hzsolve, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hQ : (fun i => (Q i).eval x) = A.det • y := by
    change (fun i => (adjugatePolynomialVec M v i).eval x) = _
    rw [eval_adjugatePolynomialVec, ← hysolve, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hpe : p.eval x = A.det^2 * (ofLp z ⬝ᵥ y) := by
    have he : p.eval x = (fun i => (P i).eval x) ⬝ᵥ (fun i => (Q i).eval x) := by
      simp [p, dotProduct, eval_finsetSum]
    rw [he, hP, hQ, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hchol := isCholesky_cholesky hpx
  have hd (i : Fin n) : L i i ≠ 0 := by
    simpa [L, A, conjTranspose_eq_transpose_of_trivial] using hchol.diag_ne_zero i
  obtain ⟨hw, hy, hc⟩ := linpack_triangular_solves (isLowerTriangular_cholesky A) hd
  have hunit : ‖linpackEuclideanDirection y‖ = 1 :=
    (linpackEuclideanDirection_spec hn hw hy hc).1
  have hynorm : 0 < ‖(toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := by
    apply norm_pos_iff.mpr
    intro hz
    simp [linpackEuclideanDirection, hz] at hunit
  change (0 ≤ ⟪z, linpackEuclideanDirection y⟫) ↔ 0 ≤ sgn
  rw [← hs, sign_nonneg_iff, hpe, mul_nonneg_iff_of_pos_left (pow_pos hpx.det_pos _)]
  unfold linpackEuclideanDirection
  rw [real_inner_smul_right, ← WithLp.toLp_ofLp 2 z, EuclideanSpace.inner_toLp_toLp_real,
    mul_nonneg_iff_of_pos_left (inv_pos.mpr hynorm)]

private theorem shifted_posDef_of_gt (hn : 0 < n)
    (hM : (Mop : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    {x : ℝ} (hx : -leftmost hM < x) : (M + x • 1).PosDef := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [posDef_iff_isSymmetricCoercive, ← coe_toEuclideanCLM_eq_toEuclideanLin,
    toEuclideanCLM_add_smul_one]
  exact (isSymmetricCoercive_add_smul_iff (H := Mop) (hH := hM) x).2 hx

private theorem shiftedStep_norm_lt_of_hard
    (hM : (Mop : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    {g sM : EuclideanSpace ℝ (Fin n)} {Δ x : ℝ} (hΔ : 0 < Δ)
    (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g Mop Δ sM (-leftmost hM))
    (hx : -leftmost hM < x) : ‖shiftedStep g Mop x‖ < Δ := by
  by_cases hg : g = 0
  · simp [hg, shiftedStep, step, hΔ]
  · have hsq := (secular_lt_norm_sq_of_shifted (H := Mop) (hH := hM)
      hg le_rfl hmul.shifted hx).trans_le
      (pow_le_pow_left₀ (norm_nonneg sM) hsM 2)
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hΔ.le two_ne_zero).mp hsq

/-- The actual corrected hard step at a successful matrix trial. -/
noncomputable def moreSorensenComputedHardStep (M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (Δ x : ℝ) : EuclideanSpace ℝ (Fin n) :=
  let H := toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M
  let L := cholesky (M + x • 1)
  let u := linpackEuclideanDirection (Lᵀ.backSubst (linpackForwardSubst L))
  let s := shiftedStep g H x
  s + moreSorensenBestBoundaryCoefficient g H Δ s u • u

/-- The computed hard correction has a one-sided vector limit at the pole.
Both the normalized direction and the deterministic boundary branch
stabilize sufficiently to pass to the limit. -/
theorem moreSorensen_computed_hard_step_tendsto (hn : 0 < n)
    (hM : (Mop : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    {g sM : EuclideanSpace ℝ (Fin n)} {Δ : ℝ} (hΔ : 0 < Δ)
    (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g Mop Δ sM (-leftmost hM)) :
    ∃ z : EuclideanSpace ℝ (Fin n),
      Tendsto (moreSorensenComputedHardStep M g Δ) (𝓝[>] (-leftmost hM)) (𝓝 z) := by
  let a := -leftmost hM
  have hpd (x : ℝ) (hx : a < x) : (M + x • 1).PosDef := shifted_posDef_of_gt hn hM hx
  have hpdEv : ∀ᶠ x in 𝓝[>] a, (M + x • 1).PosDef :=
    eventually_nhdsWithin_of_forall hpd
  obtain ⟨v, hv, u₀, hu⟩ := linpackDirection_eventually_tendsto hn hpdEv
  obtain ⟨c, hc⟩ := computedStep_inner_nonneg_eventually hn hM g rfl hv hpdEv
  let s₀ := particular hM g a
  have hs : Tendsto (shiftedStep g Mop) (𝓝[>] a) (𝓝 s₀) :=
    ((tendsto_step_threshold (H := Mop) (hH := hM)).1
      (particular_add_of_shifted (hH := hM) hmul.shifted).1).1
  let E := EuclideanSpace ℝ (Fin n)
  let fPlus := fun p : E × E => p.1 + moreSorensenBoundaryCoefficient Δ p.1 p.2 • p.2
  let fMinus := fun p : E × E => p.1 - moreSorensenBoundaryCoefficient Δ p.1 (-p.2) • p.2
  have hfPlus : Continuous fPlus := by
    unfold fPlus moreSorensenBoundaryCoefficient
    fun_prop
  have hfMinus : Continuous fMinus := by
    unfold fMinus moreSorensenBoundaryCoefficient
    fun_prop
  let y := fun x : ℝ => (cholesky (M + x • 1))ᵀ.backSubst
    (linpackForwardSubst (cholesky (M + x • 1)))
  let u := fun x => linpackEuclideanDirection (y x)
  have ht : Tendsto (fun x => (shiftedStep g Mop x, u x)) (𝓝[>] a) (𝓝 (s₀, u₀)) :=
    hs.prodMk_nhds hu
  have hchoice : ∀ᶠ x in 𝓝[>] a, moreSorensenBestBoundaryCoefficient g Mop Δ
      (shiftedStep g Mop x) (u x) =
        if 0 ≤ ⟪shiftedStep g Mop x, u x⟫ then
          moreSorensenBoundaryCoefficient Δ (shiftedStep g Mop x) (u x)
        else -moreSorensenBoundaryCoefficient Δ (shiftedStep g Mop x) (-u x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hpx := hpd x hx
    have hchol := isCholesky_cholesky hpx
    have hd (i : Fin n) : cholesky (M + x • 1) i i ≠ 0 := by
      simpa [conjTranspose_eq_transpose_of_trivial] using hchol.diag_ne_zero i
    obtain ⟨hw, hy, hsign⟩ := linpack_triangular_solves (isLowerTriangular_cholesky _) hd
    have hunit : ‖u x‖ = 1 := (linpackEuclideanDirection_spec hn hw hy hsign).1
    have hraw := shiftedStep_norm_lt_of_hard hM hΔ hsM hmul hx
    have hcurv := add_leftmost_mul_norm_sq_le (H := Mop) (hH := hM) x (u x)
    rw [hunit, one_pow, mul_one, real_inner_comm] at hcurv
    exact moreSorensenBestBoundaryCoefficient_eq_ite_inner hM
      (step_spec (H := Mop) (hH := hM) hx).1 hraw hunit
      ((neg_lt_iff_pos_add.mp hx).trans_le hcurv)
  by_cases hc₀ : c
  · refine ⟨fPlus (s₀, u₀), (hfPlus.continuousAt.tendsto.comp ht).congr' ?_⟩
    filter_upwards [hc, hchoice] with x hx hcx
    change fPlus (shiftedStep g Mop x, u x) = moreSorensenComputedHardStep M g Δ x
    unfold fPlus moreSorensenComputedHardStep
    change _ = shiftedStep g Mop x +
      moreSorensenBestBoundaryCoefficient g Mop Δ (shiftedStep g Mop x) (u x) • u x
    rw [hcx, ite_eq_left (hx.mpr hc₀)]
  · refine ⟨fMinus (s₀, u₀), (hfMinus.continuousAt.tendsto.comp ht).congr' ?_⟩
    filter_upwards [hc, hchoice] with x hx hcx
    change fMinus (shiftedStep g Mop x, u x) = moreSorensenComputedHardStep M g Δ x
    unfold fMinus moreSorensenComputedHardStep
    change _ = shiftedStep g Mop x +
      moreSorensenBestBoundaryCoefficient g Mop Δ (shiftedStep g Mop x) (u x) • u x
    rw [hcx, ite_eq_right (fun h => hc₀ (hx.mp h)), neg_smul, sub_eq_add_neg]

/-- The actual deterministic hard-case run converges to a single model
minimizer along its successful factorizations, even if the minimizer is
nonunique. The starting upper endpoint must exceed the pole. -/
theorem moreSorensen_computed_hard_matrix_run_vector_limit (hn : 0 < n)
    (hM : (Mop : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    {g sM : EuclideanSpace ℝ (Fin n)}
    {Δ θ : ℝ} {initial : ℝ × ℝ × ℝ}
    (hΔ : 0 < Δ) (hθ : θ ∈ Ioo 0 1)
    (hsM : ‖sM‖ ≤ Δ) (hmul : IsTrustRegionMultiplier g Mop Δ sM (-leftmost hM))
    (hlo : 0 ≤ initial.1) (hlr : initial.1 ≤ -leftmost hM)
    (hhi : -leftmost hM < initial.2.1) (hx0 : initial.2.2 ∈ Icc initial.1 initial.2.1) :
    let x := fun k => (moreSorensenMatrixIterates M g Δ θ initial k).2.2
    Tendsto x atTop (𝓝 (-leftmost hM)) ∧
      (∃ᶠ k in atTop, -leftmost hM < x k) ∧
      ∃ z : EuclideanSpace ℝ (Fin n), z ∈ Metric.closedBall 0 Δ ∧
        IsMinOn (quadModel g Mop) (Metric.closedBall 0 Δ) z ∧
        Tendsto (fun k => moreSorensenComputedHardStep M g Δ (x k))
          (atTop ⊓ 𝓟 {k | -leftmost hM < x k}) (𝓝 z) := by
  let states := moreSorensenMatrixIterates M g Δ θ initial
  let lo := fun k => (states k).1
  let hi := fun k => (states k).2.1
  let x := fun k => (states k).2.2
  let b := fun k => moreSorensenMatrixLowerEstimate M (x k)
  have hb (k : ℕ) : b k ≤ -leftmost hM := (moreSorensenMatrixLowerEstimate_spec hn hM (x k)).1
  have hrec (k : ℕ) : (lo (k + 1), hi (k + 1), x (k + 1)) =
      moreSorensenSafeguardedStep g Mop (-leftmost hM) Δ θ (lo k) (hi k) (x k) (b k) :=
    moreSorensenMatrixIterates_succ hn hM g Δ θ initial k
  obtain ⟨hrun, hxlim⟩ : IsBracketRun (-leftmost hM) (-leftmost hM) θ θ lo hi x ∧
      Tendsto x atTop (𝓝 (-leftmost hM)) := by
    rcases eq_or_ne g 0 with hg | hg
    · subst g
      exact moreSorensen_zero_gradient_run (H := Mop) hθ hlo hlr hhi.le hx0 hb hrec
    · exact moreSorensen_hard_safeguarded_run (H := Mop) (hH := hM) hg hΔ hθ hsM hmul
        hlo hlr hhi.le hx0 hb hrec
  obtain ⟨j, hj, hjpos⟩ := moreSorensen_hard_bracketing_subsequence (hH := hM) hθ hrun hhi
  let lam := x ∘ j
  let L := fun k => cholesky (M + lam k • 1)
  let w := fun k => linpackForwardSubst (L k)
  let v := fun k => linpackShiftedSigns M (lam k)
  let y := fun k => (L k)ᵀ.backSubst (w k)
  let u := fun k => linpackEuclideanDirection (y k)
  let α := fun k => moreSorensenBestBoundaryCoefficient g Mop Δ (shiftedStep g Mop (lam k)) (u k)
  have hcert (k : ℕ) : L k * (L k)ᵀ = M + lam k • 1 ∧
      (L k).IsLowerTriangular ∧ (∀ i, 0 < L k i i) ∧
      L k *ᵥ w k = v k ∧ (L k)ᵀ *ᵥ y k = w k ∧
      ∀ i, v k i = linpackSign (v k i - L k i i * w k i) := by
    have hpd := shifted_posDef_of_gt hn hM (hjpos k)
    exact cholesky_linpack_certificate (isHermitian_iff_isSymm.mp hpd.isHermitian)
      ((shiftedCholesky_succeeds_iff hn hM (lam k)).mpr (hjpos k))
  have hunit (k : ℕ) : ‖u k‖ = 1 := by
    obtain ⟨_, _, _, hw, hy, hv⟩ := hcert k
    exact (linpackEuclideanDirection_spec hn hw hy hv).1
  have hraw (k : ℕ) : ‖shiftedStep g Mop (lam k)‖ ≤ Δ :=
    (shiftedStep_norm_lt_of_hard hM hΔ hsM hmul (hjpos k)).le
  have hboundary (k : ℕ) : ‖shiftedStep g Mop (lam k) + α k • u k‖ = Δ :=
    (moreSorensenBestBoundaryCoefficient_spec g Mop (hraw k) (hunit k)).1
  have hcurv := linpackEuclideanCurvature_tendsto hn hM (hxlim.comp hj)
    (Eventually.of_forall hcert)
  have hvc := moreSorensen_hard_correction_curvature_tendsto (H := Mop) (hH := hM)
    lam α u hjpos hraw hunit hboundary hcurv
  have hmodel := moreSorensen_hard_model_convergence (H := Mop) (hH := hM) hsM (hmul.isMinOn hM)
    lam (fun k => α k • u k) (fun k => hmul.nonneg.trans (hjpos k).le) hjpos hboundary hvc
  obtain ⟨z, hz⟩ := moreSorensen_computed_hard_step_tendsto hn hM hΔ hsM hmul
  have hlim : Tendsto (fun k => moreSorensenComputedHardStep M g Δ (lam k)) atTop (𝓝 z) :=
    hz.comp (tendsto_nhdsWithin_iff.2 ⟨hxlim.comp hj, Eventually.of_forall hjpos⟩)
  obtain ⟨hzf, hzm⟩ := hmodel.2.1 id z tendsto_id hlim
  refine ⟨hxlim, frequently_iff_seq_forall.mpr ⟨j, hj, hjpos⟩, z, hzf, hzm,
    hz.comp (tendsto_nhdsWithin_iff.2 ⟨hxlim.mono_left inf_le_left, ?_⟩)⟩
  exact mem_inf_of_right (mem_principal_self _)

end Shifted

end ConnGouldToint.Chapter07
