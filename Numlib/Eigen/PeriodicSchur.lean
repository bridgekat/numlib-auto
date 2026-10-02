import Numlib.LinearAlgebra.Matrix.GeneralizedSchur
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.RealSchur
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.Triangular

/-!
# The periodic Schur form and the product eigenvalue problem

The product eigenvalue problem ([golub2013matrix] §7.8.2): condensed and Schur forms of a product
`A_p ⋯ A_1 A_0` computed through the factors, and the block-cyclic matrix that turns it into a
structured single-matrix problem.

For a family `A : Fin (p+1) → Matrix (Fin n) (Fin n) 𝕜`, a *periodic* decomposition is a family of
unitary `U : Fin (p+1) → Matrix …` with `U (i+1)ᴴ A i U i` upper triangular for `i < p` and
`U 0ᴴ A p U p` of a prescribed shape: upper Hessenberg ((7.8.5),
"Hessenberg–triangular–triangular"),
upper quasi-triangular ((7.8.6), the periodic real Schur form), or — over `ℂ` — upper triangular
(the complex periodic Schur form of Bojanczyk, Golub and Van Dooren 1992). Then
`U 0ᴴ (A p ⋯ A 0) U 0` is the product of the transformed factors.

## Main results

* The common engine for nonsingular factors (a private lemma) — start from any
  unitary `U 0` that puts the product in a shape stable under right multiplication by upper
  triangular matrices, then QR-factor successively, `A i U i = U (i+1) T i`; the last factor is
  forced, `U 0ᴴ A p U p = (U 0ᴴ Π U 0)(T_{p-1} ⋯ T_0)⁻¹`.
* `Matrix.exists_orthogonal_periodicHessenberg_of_isUnit` and, for arbitrary factors,
  `Matrix.exists_orthogonal_periodicHessenberg` ((7.8.5)): perturb `A i + t I` to nonsingular for
  `i < p` (`Matrix.exists_forall_isUnit_det_add_smul_one`), extract a convergent subsequence of the
  orthogonal families (`Matrix.isCompact_orthogonalGroup`), and pass to the limit in the closed
  vanishing conditions.
* `Matrix.exists_orthogonal_periodicRealSchur_of_isUnit` and
  `Matrix.exists_orthogonal_periodicRealSchur` ((7.8.6)): the periodic real Schur form, from the
  real Schur form of the product (`Matrix.exists_orthogonal_conj_isQuasiUpperTriangular`); in the
  limit the block pattern of the quasi-triangular factor is fixed by a pigeonhole over the finitely
  many relations `q j < q i` on `Fin n`.
* `Matrix.exists_unitary_periodicSchur_of_isUnit` and `Matrix.exists_unitary_periodicSchur`: the
  complex periodic Schur form, all transformed factors triangular, for nonsingular and then
  arbitrary factors (`Matrix.isCompact_unitaryGroup`).
* `Matrix.blockCyclic`, `Matrix.blockDiagonal_conj_blockCyclic` and
  `Matrix.isUpperHessenberg_reindex_blockCyclic`: the block-cyclic matrix of the family is
  conjugated by `blockDiagonal U` into that of the transformed factors, and in the interleaved
  ordering (the perfect shuffle of [golub2013matrix] §1.2.11) it is upper Hessenberg when the
  transformed factors are triangular except one Hessenberg factor.

The book states the convergence of a product QR iteration ((7.8.7)) without content; nothing is
formalized for it. Mathlib has nothing on periodic forms.
-/

open Filter Topology

namespace Matrix

variable {n : ℕ}

section Engine

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The descending product `B (k-1) ⋯ B 1 B 0`. -/
private def prodDown {R : Type*} [Monoid R] (B : ℕ → R) : ℕ → R
  | 0 => 1
  | k + 1 => B k * prodDown B k

/-- The engine of the periodic forms: successive QR factorizations. Let `P` be a shape stable under
right multiplication by upper triangular matrices, `B 0, …, B p` square matrices with `B i`
nonsingular for `i < p`, and `U₀` unitary with `P (U₀ᴴ (B p ⋯ B 0) U₀)`. Then there are unitary
`U 0 = U₀, U 1, …, U p` with `U (i+1)ᴴ B i U i` upper triangular for `i < p` and
`P (U₀ᴴ B p U p)`: `B i U i = U (i+1) T i` by QR, so `(B (p-1) ⋯ B 0) U₀ = U p (T (p-1) ⋯ T 0)`,
and `U₀ᴴ B p U p = (U₀ᴴ Π U₀) (T (p-1) ⋯ T 0)⁻¹`. -/
private theorem exists_periodic_of_isUnit (P : Matrix (Fin n) (Fin n) 𝕜 → Prop)
    (hP : ∀ S T : Matrix (Fin n) (Fin n) 𝕜, P S → T.IsUpperTriangular → P (S * T)) (p : ℕ)
    (B : ℕ → Matrix (Fin n) (Fin n) 𝕜) (hB : ∀ i < p, IsUnit (B i))
    (U₀ : Matrix (Fin n) (Fin n) 𝕜) (hU₀ : U₀ ∈ unitaryGroup (Fin n) 𝕜)
    (hprod : P (star U₀ * (B p * prodDown B p) * U₀)) :
    ∃ U : ℕ → Matrix (Fin n) (Fin n) 𝕜, U 0 = U₀ ∧ (∀ i, U i ∈ unitaryGroup (Fin n) 𝕜) ∧
      (∀ i < p, (star (U (i + 1)) * B i * U i).IsUpperTriangular) ∧
      P (star (U 0) * B p * U p) := by
  choose V hV hVT using fun M : Matrix (Fin n) (Fin n) 𝕜 => exists_unitary_mul_isUpperTriangular M
  let U : ℕ → Matrix (Fin n) (Fin n) 𝕜 := fun k => Nat.rec U₀ (fun k Uk => star (V (B k * Uk))) k
  have hU0 : U 0 = U₀ := rfl
  have hUs : ∀ k, U (k + 1) = star (V (B k * U k)) := fun k => rfl
  have hUu : ∀ k, U k ∈ unitaryGroup (Fin n) 𝕜 := by
    intro k
    induction k with
    | zero => exact hU₀
    | succ k _ => rw [hUs]; exact Unitary.star_mem (hV _)
  set T : ℕ → Matrix (Fin n) (Fin n) 𝕜 := fun k => star (U (k + 1)) * B k * U k with hTdef
  have hTu : ∀ k, (T k).IsUpperTriangular := fun k => by
    simp only [hTdef, hUs, star_star, Matrix.mul_assoc]
    exact hVT _
  have hBU : ∀ k, B k * U k = U (k + 1) * T k := fun k => by
    simp only [hTdef, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 (hUu (k + 1)), Matrix.one_mul]
  -- the partial products
  have hpr : ∀ k, prodDown B (k + 1) = B k * prodDown B k := fun k => rfl
  let tr : ℕ → Matrix (Fin n) (Fin n) 𝕜 := fun k => Nat.rec 1 (fun k t => T k * t) k
  have htrs : ∀ k, tr (k + 1) = T k * tr k := fun k => rfl
  have hprU : ∀ k, prodDown B k * U₀ = U k * tr k := by
    intro k
    induction k with
    | zero => simp [prodDown, tr, hU0]
    | succ k ih => rw [hpr, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hBU, htrs,
        Matrix.mul_assoc]
  have htru : ∀ k, (tr k).IsUpperTriangular := by
    intro k
    induction k with
    | zero => exact blockTriangular_one
    | succ k ih => rw [htrs]; exact (hTu k).mul ih
  have htrunit : ∀ k ≤ p, IsUnit (tr k) := by
    intro k
    induction k with
    | zero => intro _; exact isUnit_one
    | succ k ih =>
      intro hk
      rw [htrs]
      refine IsUnit.mul ?_ (ih (by omega))
      simp only [hTdef]
      exact ((Unitary.isUnit_coe (U := ⟨_, Unitary.star_mem (hUu (k + 1))⟩)).mul
        (hB k (by omega))).mul
        (Unitary.isUnit_coe (U := ⟨_, hUu k⟩))
  refine ⟨U, hU0, hUu, fun i _ => hTu i, ?_⟩
  -- the last factor
  have hkey : star (U 0) * B p * U p * tr p =
      star U₀ * (B p * prodDown B p) * U₀ := by
    rw [Matrix.mul_assoc, ← hprU p, hU0]
    simp only [Matrix.mul_assoc]
  have hinv : star (U 0) * B p * U p =
      star U₀ * (B p * prodDown B p) * U₀ * (tr p)⁻¹ := by
    rw [← hkey, Matrix.mul_assoc _ (tr p),
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (htrunit p le_rfl)), Matrix.mul_one]
  rw [hinv]
  exact hP _ _ hprod (htru p).inv

end Engine

/-- The shifted index family of the engine: `A` extended by `1` beyond `p`. -/
private noncomputable def extendFamily {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜) (j : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  if h : j < p + 1 then A ⟨j, h⟩ else 1

private theorem extendFamily_castSucc {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜) (i : Fin p) :
    extendFamily A i = A i.castSucc := by
  rw [extendFamily, dite_eq_left (by omega)]; rfl

private theorem extendFamily_last {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜) : extendFamily A p = A (Fin.last p) := by
  rw [extendFamily, dite_eq_left (by omega)]; rfl

private theorem star_eq_transpose_real (M : Matrix (Fin n) (Fin n) ℝ) : star M = Mᵀ := by
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-- [golub2013matrix] (7.8.5), nonsingular factors: for `A : Fin (p+1) → Matrix (Fin n) (Fin n) ℝ`
with `A i` nonsingular for `i < p` there are orthogonal `U : Fin (p+1) → Matrix (Fin n) (Fin n) ℝ`
with `(U (i+1))ᵀ A i U i` upper triangular for `i < p` and `(U 0)ᵀ A p U p` upper Hessenberg
("Hessenberg–triangular–triangular"): a Hessenberg reduction `U 0` of the product
`A p ⋯ A 0` (`Matrix.exists_unitary_conj_isUpperHessenberg`), then successive QR
factorizations. -/
theorem exists_orthogonal_periodicHessenberg_of_isUnit {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i : Fin p, IsUnit (A i.castSucc)) :
    ∃ U : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ, (∀ i, U i ∈ orthogonalGroup (Fin n) ℝ) ∧
      (∀ i : Fin p, ((U i.succ)ᵀ * A i.castSucc * U i.castSucc).IsUpperTriangular) ∧
      ((U 0)ᵀ * A (Fin.last p) * U (Fin.last p)).IsUpperHessenberg := by
  obtain ⟨U₀, hU₀, hH⟩ := exists_unitary_conj_isUpperHessenberg
    (extendFamily A p * prodDown (extendFamily A) p)
  obtain ⟨U, -, hUu, hT, hlast⟩ := exists_periodic_of_isUnit (𝕜 := ℝ) IsUpperHessenberg
    (fun S T hS hT => hS.mul_isUpperTriangular hT) p (extendFamily A)
    (fun i hi => by simpa [extendFamily_castSucc A ⟨i, hi⟩] using hA ⟨i, hi⟩) U₀ hU₀
    (by rwa [star_eq_conjTranspose])
  refine ⟨fun i => U i, fun i => hUu i, fun i => ?_, ?_⟩
  · have h := hT i i.2
    rw [star_eq_transpose_real, extendFamily_castSucc] at h
    simpa using h
  · rw [star_eq_transpose_real, extendFamily_last] at hlast
    simpa using hlast

/-- **The complex periodic Schur decomposition, nonsingular factors** (Bojanczyk, Golub and Van
Dooren 1992; the complex analogue of [golub2013matrix] (7.8.6)): over an algebraically closed
`RCLike` field, if `A i` is nonsingular for `i < p` there are unitary `U i` with
`(U (i+1))ᴴ A i U i` upper triangular for **every** `i` (indices mod `p + 1`): the Schur form of
the product (`Matrix.exists_unitary_conj_upperTriangular`) followed by successive QR
factorizations. -/
theorem exists_unitary_periodicSchur_of_isUnit {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜) (hA : ∀ i : Fin p, IsUnit (A i.castSucc)) :
    ∃ U : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜, (∀ i, U i ∈ unitaryGroup (Fin n) 𝕜) ∧
      ∀ i : Fin (p + 1), (star (U (i + 1)) * A i * U i).IsUpperTriangular := by
  obtain ⟨U₀, hU₀, hS, -⟩ := exists_unitary_conj_upperTriangular
    (extendFamily A p * prodDown (extendFamily A) p)
  obtain ⟨U, -, hUu, hT, hlast⟩ := exists_periodic_of_isUnit IsUpperTriangular
    (fun S T hS hT => hS.mul hT) p (extendFamily A)
    (fun i hi => by simpa [extendFamily_castSucc A ⟨i, hi⟩] using hA ⟨i, hi⟩) U₀ hU₀ hS
  refine ⟨fun i => U i, fun i => hUu i, fun i => ?_⟩
  induction i using Fin.lastCases with
  | last =>
    rw [extendFamily_last] at hlast
    simpa [Fin.last_add_one] using hlast
  | cast i =>
    have h := hT i i.2
    rw [extendFamily_castSucc] at h
    simpa [Fin.coeSucc_eq_succ] using h

/-! ### Limits of perturbed families -/

section Limits

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Perturbations `A i + t_k I` (`i < p`, `t_k → 0`) of a family of square matrices, nonsingular for
every `k` (`Matrix.exists_forall_isUnit_det_add_smul_one` for each factor, with a common
threshold). The last factor is left alone. -/
private theorem exists_perturbed_family {p : ℕ} (A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜) :
    ∃ Ak : ℕ → Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜,
      (∀ k (i : Fin p), IsUnit (Ak k i.castSucc)) ∧ (∀ k, Ak k (Fin.last p) = A (Fin.last p)) ∧
      ∀ i, Tendsto (fun k => Ak k i) atTop (𝓝 (A i)) := by
  choose δ hδ hδu using fun i : Fin p => exists_forall_isUnit_det_add_smul_one (A i.castSucc)
  set δ₀ := (insert 1 (Finset.univ.image δ)).min' (Finset.insert_nonempty _ _) with hδ₀
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy; exact hδ i
  have hδ₀le : ∀ i, δ₀ ≤ δ i := fun i =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  set t : ℕ → ℝ := fun k => δ₀ / (k + 2) with ht
  have ht0 : ∀ k, 0 < t k := fun k => by positivity
  have htδ : ∀ k, t k < δ₀ := fun k => by
    rw [ht, div_lt_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have htlim : Tendsto t atTop (𝓝 0) := by
    have h := tendsto_const_nhds (x := δ₀).div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ))))
    simpa [ht] using h
  refine ⟨fun k i => if (i : ℕ) < p then A i + t k • (1 : Matrix (Fin n) (Fin n) 𝕜) else A i,
    fun k i => ?_, fun k => by simp, fun i => ?_⟩
  · simp only [Fin.val_castSucc, i.2, ite_true]
    rw [isUnit_iff_isUnit_det]
    exact hδu i (t k) (ht0 k) ((htδ k).trans_le (hδ₀le i))
  · by_cases hi : (i : ℕ) < p
    · simp only [hi, ite_true]
      have h := tendsto_const_nhds (x := A i).add (htlim.smul_const (1 : Matrix (Fin n) (Fin n) 𝕜))
      simpa using h
    · simp only [hi, ite_false]
      exact tendsto_const_nhds

/-- An entry of `Vᴴ M W` that vanishes along convergent sequences `V_k → V`, `M_k → M`,
`W_k → W` vanishes in the limit. -/
private theorem entry_eq_zero_of_tendsto {V W M : ℕ → Matrix (Fin n) (Fin n) 𝕜}
    {V₀ W₀ M₀ : Matrix (Fin n) (Fin n) 𝕜} (hV : Tendsto V atTop (𝓝 V₀))
    (hW : Tendsto W atTop (𝓝 W₀)) (hM : Tendsto M atTop (𝓝 M₀)) (r c : Fin n)
    (hz : ∀ k, (star (V k) * M k * W k) r c = 0) : (star V₀ * M₀ * W₀) r c = 0 := by
  have h := ((hV.star.mul hM).mul hW)
  have ht : Tendsto (fun k => (star (V k) * M k * W k) r c) atTop
      (𝓝 ((star V₀ * M₀ * W₀) r c)) :=
    ((continuous_id.matrix_elem r c).tendsto _).comp h
  simp only [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- A convergent subsequence of a sequence of unitary families. -/
private theorem exists_tendsto_subseq_unitary {p : ℕ}
    {U : ℕ → Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜}
    (hU : ∀ k i, U k i ∈ unitaryGroup (Fin n) 𝕜) :
    ∃ U₀ : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜, (∀ i, U₀ i ∈ unitaryGroup (Fin n) 𝕜) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, Tendsto (fun k => U (φ k) i) atTop (𝓝 (U₀ i)) := by
  set s := Set.pi Set.univ fun _ : Fin (p + 1) =>
    ((unitaryGroup (Fin n) 𝕜 : Submonoid _) : Set (Matrix (Fin n) (Fin n) 𝕜))
  have hs : IsCompact s := isCompact_univ_pi fun _ => isCompact_unitaryGroup
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) 𝕜) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → 𝕜))
  obtain ⟨U₀, hUs, φ, hφ, hlim⟩ := hs.tendsto_subseq (x := U)
    (fun k => Set.mem_univ_pi.2 fun i => hU k i)
  exact ⟨U₀, fun i => (Set.mem_univ_pi.1 hUs) i, φ, hφ, fun i => tendsto_pi_nhds.1 hlim i⟩

end Limits

/-- [golub2013matrix] (7.8.5) for arbitrary factors (the book describes the computation, QR
factorizations and Givens bulge chasing, without proof): the conclusion of
`Matrix.exists_orthogonal_periodicHessenberg_of_isUnit` without any nonsingularity. The factors
`A i + t I` (`i < p`) are nonsingular for small `t > 0`
(`Matrix.exists_forall_isUnit_det_add_smul_one`); a subsequence of the orthogonal families for
`t → 0` converges (`Matrix.isCompact_orthogonalGroup`), and triangular and Hessenberg shapes are
closed conditions. -/
theorem exists_orthogonal_periodicHessenberg {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ) :
    ∃ U : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ, (∀ i, U i ∈ orthogonalGroup (Fin n) ℝ) ∧
      (∀ i : Fin p, ((U i.succ)ᵀ * A i.castSucc * U i.castSucc).IsUpperTriangular) ∧
      ((U 0)ᵀ * A (Fin.last p) * U (Fin.last p)).IsUpperHessenberg := by
  obtain ⟨Ak, hAku, -, hAkt⟩ := exists_perturbed_family A
  choose Uk hUk hTk hHk using fun k =>
    exists_orthogonal_periodicHessenberg_of_isUnit (Ak k) (hAku k)
  obtain ⟨U, hU, φ, hφ, hlim⟩ := exists_tendsto_subseq_unitary (𝕜 := ℝ) hUk
  refine ⟨U, hU, fun i r c hrc => ?_, fun r c hrc => ?_⟩
  · have h := entry_eq_zero_of_tendsto (hlim i.succ) (hlim i.castSucc)
      ((hAkt i.castSucc).comp hφ.tendsto_atTop) r c fun k => by
        have := hTk (φ k) i hrc
        rwa [← star_eq_transpose_real] at this
    rwa [star_eq_transpose_real] at h
  · have h := entry_eq_zero_of_tendsto (hlim 0) (hlim (Fin.last p))
      ((hAkt (Fin.last p)).comp hφ.tendsto_atTop) r c fun k => by
        have := hHk (φ k) r c hrc
        rwa [← star_eq_transpose_real] at this
    rwa [star_eq_transpose_real] at h

/-- **The complex periodic Schur decomposition** (Bojanczyk, Golub and Van Dooren 1992; the complex
analogue of [golub2013matrix] (7.8.6)): for any family `A : Fin (p+1) → Matrix (Fin n) (Fin n) 𝕜`
over an algebraically closed `RCLike` field (that is, over `ℂ`) there are unitary `U i` with
`(U (i+1))ᴴ A i U i` upper triangular for **every** `i` (indices mod `p + 1`); then
`U 0ᴴ (A p ⋯ A 0) U 0` is upper triangular, its diagonal the products of the factors' diagonals.
The nonsingular case is `Matrix.exists_unitary_periodicSchur_of_isUnit`; in general the factors
`A i + t I` (`i < p`) are nonsingular for small `t > 0`, a subsequence of the unitary families
converges (`Matrix.isCompact_unitaryGroup`), and triangularity of each factor is a closed
condition. -/
theorem exists_unitary_periodicSchur {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜) :
    ∃ U : Fin (p + 1) → Matrix (Fin n) (Fin n) 𝕜, (∀ i, U i ∈ unitaryGroup (Fin n) 𝕜) ∧
      ∀ i : Fin (p + 1), (star (U (i + 1)) * A i * U i).IsUpperTriangular := by
  obtain ⟨Ak, hAku, -, hAkt⟩ := exists_perturbed_family A
  choose Uk hUk hTk using fun k => exists_unitary_periodicSchur_of_isUnit (Ak k) (hAku k)
  obtain ⟨U, hU, φ, hφ, hlim⟩ := exists_tendsto_subseq_unitary hUk
  refine ⟨U, hU, fun i => ?_⟩
  intro r c hrc
  exact entry_eq_zero_of_tendsto (hlim (i + 1)) (hlim i)
    ((hAkt i).comp hφ.tendsto_atTop) r c fun k => hTk (φ k) i hrc

/-- [golub2013matrix] (7.8.6), nonsingular factors: as
`Matrix.exists_orthogonal_periodicHessenberg_of_isUnit` with `(U 0)ᵀ A p U p` upper
quasi-triangular,
starting from the real Schur form of the product
(`Matrix.exists_orthogonal_conj_isQuasiUpperTriangular`) and using that quasi-triangularity survives
right multiplication by upper triangular matrices
(`Matrix.IsQuasiUpperTriangular.mul_isUpperTriangular`). -/
theorem exists_orthogonal_periodicRealSchur_of_isUnit {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i : Fin p, IsUnit (A i.castSucc)) :
    ∃ U : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ, (∀ i, U i ∈ orthogonalGroup (Fin n) ℝ) ∧
      (∀ i : Fin p, ((U i.succ)ᵀ * A i.castSucc * U i.castSucc).IsUpperTriangular) ∧
      ((U 0)ᵀ * A (Fin.last p) * U (Fin.last p)).IsQuasiUpperTriangular := by
  obtain ⟨U₀, hU₀, hH⟩ := exists_orthogonal_conj_isQuasiUpperTriangular
    (extendFamily A p * prodDown (extendFamily A) p)
  obtain ⟨U, -, hUu, hT, hlast⟩ := exists_periodic_of_isUnit (𝕜 := ℝ) IsQuasiUpperTriangular
    (fun S T hS hT => hS.mul_isUpperTriangular hT) p (extendFamily A)
    (fun i hi => by simpa [extendFamily_castSucc A ⟨i, hi⟩] using hA ⟨i, hi⟩) U₀ hU₀
    (by rwa [star_eq_transpose_real])
  refine ⟨fun i => U i, fun i => hUu i, fun i => ?_, ?_⟩
  · have h := hT i i.2
    rw [star_eq_transpose_real, extendFamily_castSucc] at h
    simpa using h
  · rw [star_eq_transpose_real, extendFamily_last] at hlast
    simpa using hlast

/-- [golub2013matrix] (7.8.6) for arbitrary factors, **the periodic real Schur form** (quoted by the
book without proof): orthogonal `U i` with `(U (i+1))ᵀ A i U i` upper triangular for `i < p` and
`(U 0)ᵀ A p U p` upper quasi-triangular. The factors `A i + t I` (`i < p`) are nonsingular for
small `t > 0`; along `t_k → 0` infinitely many `k` share the relation `q_k j < q_k i` of the block
patterns `q_k` of the last factor (a pigeonhole over the finitely many relations on `Fin n`), a
further subsequence of the orthogonal families converges (`Matrix.isCompact_orthogonalGroup`), and
the vanishing entries — triangular for `i < p`, block triangular for the common pattern at `p` —
pass to the limit. -/
theorem exists_orthogonal_periodicRealSchur {p : ℕ}
    (A : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ) :
    ∃ U : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ, (∀ i, U i ∈ orthogonalGroup (Fin n) ℝ) ∧
      (∀ i : Fin p, ((U i.succ)ᵀ * A i.castSucc * U i.castSucc).IsUpperTriangular) ∧
      ((U 0)ᵀ * A (Fin.last p) * U (Fin.last p)).IsQuasiUpperTriangular := by
  classical
  obtain ⟨Ak, hAku, hAkl, hAkt⟩ := exists_perturbed_family A
  choose Uk hUk hTk hQk using fun k => exists_orthogonal_periodicRealSchur_of_isUnit (Ak k)
    (hAku k)
  choose q hmono hcard htri using hQk
  -- infinitely many `k` share the relation `q_k j < q_k i`
  obtain ⟨R, hR⟩ := Finite.exists_infinite_fiber
    (fun k => fun i j : Fin n => decide (q k j < q k i))
  have hS : (Set.ofPred fun k => (fun i j : Fin n => decide (q k j < q k i)) = R).Infinite := by
    rw [← Set.infinite_coe_iff]
    exact hR
  set φ := Nat.nth fun k => (fun i j : Fin n => decide (q k j < q k i)) = R with hφ
  have hφmono : StrictMono φ := Nat.nth_strictMono hS
  have hφmem : ∀ k, (fun i j : Fin n => decide (q (φ k) j < q (φ k) i)) = R :=
    Nat.nth_mem_of_infinite hS
  have hrel : ∀ k i j, q (φ k) j < q (φ k) i ↔ q (φ 0) j < q (φ 0) i := by
    intro k i j
    have h1 := congrFun (congrFun (hφmem k) i) j
    have h2 := congrFun (congrFun (hφmem 0) i) j
    rw [← decide_eq_true_iff (p := q (φ k) j < q (φ k) i), ← decide_eq_true_iff
      (p := q (φ 0) j < q (φ 0) i), h1, h2]
  -- a convergent subsequence
  obtain ⟨U, hU, ψ, hψ, hlim⟩ := exists_tendsto_subseq_unitary (𝕜 := ℝ)
    (U := fun k => Uk (φ k)) fun k i => hUk (φ k) i
  have hχ : Tendsto (fun k => φ (ψ k)) atTop atTop := (hφmono.comp hψ).tendsto_atTop
  refine ⟨U, hU, fun i => ?_, ⟨q (φ 0), hmono _, hcard _, ?_⟩⟩
  · intro r c hrc
    have h := entry_eq_zero_of_tendsto (hlim i.succ) (hlim i.castSucc)
      ((hAkt i.castSucc).comp hχ) r c fun k => by
        have := hTk (φ (ψ k)) i hrc
        rw [← star_eq_transpose_real] at this
        exact this
    rwa [star_eq_transpose_real] at h
  · intro r c hrc
    have h := entry_eq_zero_of_tendsto (hlim 0) (hlim (Fin.last p))
      ((hAkt (Fin.last p)).comp hχ) r c fun k => by
        have := htri (φ (ψ k)) ((hrel (ψ k) r c).2 hrc)
        rw [← star_eq_transpose_real] at this
        exact this
    rwa [star_eq_transpose_real] at h

/-! ### The block-cyclic matrix -/

/-- **The block-cyclic matrix** of a family ([golub2013matrix] §7.8.2): block `(i+1, i)` is
`A i` (indices mod `p+1`, so block `(0, p)` is `A p`), all other blocks zero — the book's
`[0 0 A₃; A₁ 0 0; 0 A₂ 0]`. The block index is the *second* coordinate, as in Mathlib's
`Matrix.blockDiagonal`. -/
def blockCyclic {R : Type*} [Zero R] {m : Type*} {p : ℕ} (A : Fin (p + 1) → Matrix m m R) :
    Matrix (m × Fin (p + 1)) (m × Fin (p + 1)) R :=
  of fun x y => if x.2 = y.2 + 1 then A y.2 x.1 y.1 else 0

/-- `(blockDiagonal U)ᵀ (blockCyclic A) (blockDiagonal U)` is the block-cyclic matrix of the
transformed factors `(U (i+1))ᵀ A i U i` — the book's restatement of (7.8.5) as
`Uᵀ [0 0 A₃; A₁ 0 0; 0 A₂ 0] U = H̃` ([golub2013matrix] §7.8.2). -/
theorem blockDiagonal_conj_blockCyclic {R : Type*} [CommRing R] {m : Type*} [Fintype m]
    {p : ℕ} (A U : Fin (p + 1) → Matrix m m R) :
    (blockDiagonal U)ᵀ * blockCyclic A * blockDiagonal U =
      blockCyclic fun i => (U (i + 1))ᵀ * A i * U i := by
  classical
  ext ⟨r, b⟩ ⟨c, d⟩
  simp only [mul_apply, Fintype.sum_prod_type, blockDiagonal_transpose, blockDiagonal_apply,
    blockCyclic, of_apply, transpose_apply]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  split_ifs with h
  · subst h
    simp [Finset.sum_mul]
  · simp

/-- [golub2013matrix] §7.8.2 ("a highly structured upper Hessenberg matrix"): if `A i` is upper
triangular for `i < p` and `A p` is upper Hessenberg, the block-cyclic matrix is upper Hessenberg
in the interleaved order `(i, b) ↦ (p+1) i + b` (`finProdFinEquiv`; the book's perfect shuffle
`𝒫` applied to its block-major ordering). A nonzero entry of block `(b+1, b)` at `(i, j)`, `i ≤ j`,
sits at row `(p+1) i + b + 1` and column `(p+1) j + b`; one of block `(0, p)` with `i ≤ j + 1` at
row `(p+1) i` and column `(p+1) j + p`. -/
theorem isUpperHessenberg_reindex_blockCyclic {R : Type*} [Zero R] {p : ℕ}
    {A : Fin (p + 1) → Matrix (Fin n) (Fin n) R}
    (hA : ∀ i : Fin p, (A i.castSucc).IsUpperTriangular)
    (hH : (A (Fin.last p)).IsUpperHessenberg) :
    ((blockCyclic A).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).IsUpperHessenberg := by
  intro r s ⟨k, hsk, hkr⟩
  obtain ⟨⟨i, b⟩, rfl⟩ := finProdFinEquiv.surjective r
  obtain ⟨⟨j, c⟩, rfl⟩ := finProdFinEquiv.surjective s
  have hlt : (c : ℕ) + (p + 1) * j + 1 < b + (p + 1) * i := by
    have h1 := Fin.lt_def.1 hsk
    have h2 := Fin.lt_def.1 hkr
    simp only [finProdFinEquiv_apply_val] at h1 h2
    omega
  simp only [submatrix_apply, Equiv.symm_apply_apply, blockCyclic, of_apply]
  split_ifs with hbc
  · induction c using Fin.lastCases with
    | last =>
      have hb : b = 0 := by rw [hbc, Fin.last_add_one]
      subst hb
      simp only [Fin.val_zero, Fin.val_last] at hlt
      refine hH i j ⟨⟨j + 1, by
        have : (j : ℕ) + 1 < i := by nlinarith
        omega⟩, ?_, ?_⟩
      · rw [Fin.lt_def]; simp
      · rw [Fin.lt_def]; simp only
        nlinarith
    | cast c =>
      have hb : (b : ℕ) = c + 1 := by rw [hbc, Fin.coeSucc_eq_succ, Fin.val_succ]
      rw [hb, Fin.val_castSucc] at hlt
      refine hA c (?_ : j < i)
      rw [Fin.lt_def]
      nlinarith
  · rfl

end Matrix
