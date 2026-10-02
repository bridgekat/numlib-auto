import Mathlib.Analysis.CStarAlgebra.Matrix
import Numlib.Analysis.Calculus.HermiteGenocchi
import Numlib.Analysis.Matrix.Function.Approximation
import Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Cauchy
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter09.Section01

/-!
# Golub–Van Loan §9.2: approximation methods

Surface file for [golub2013matrix] §9.2: the Jordan analysis (Theorem 9.2.1), the Schur analysis
(Theorem 9.2.2 with its ingredients (9.2.1) and (9.2.2)), Taylor truncation (Theorem 9.2.3), the
double-angle formulas, Horner's scheme for matrix polynomials (Algorithm 9.2.1) and the
Paterson–Stockmeyer regrouping (9.2.5), binary powering (Algorithm 9.2.2), Simpson's rule for
`∫ f(At) dt` ((9.2.6)–(9.2.7)), and the Cauchy integral (9.2.8) over circles.

## Conventions

As in §9.1: `A : Matrix (Fin n) (Fin n) ℂ`, `f(A) = pfc f A`. `‖·‖₂` is Mathlib's scoped
`Matrix.Norms.L2Operator`, also the norm in which (9.2.8)'s contour integral is taken (every norm
on `ℂ^{n×n}` gives the same integral). `|N|` is `N.map (‖·‖)`. Algorithms 9.2.1 and 9.2.2 are real
(`Matrix (Fin n) (Fin n) ℝ`) and compute every matrix product by chapter 1's `algorithm_1_1_5`
(`C ← C + A B`, with `C = 0` or `C = b_k I`); the integer computations on the exponent of
Algorithm 9.2.2 (its binary expansion) are exact.

## Sources

`Numlib/Analysis/Calculus/HermiteGenocchi` (`Hermite.norm_divDiff_le`),
`Numlib/Analysis/Matrix/Function/Triangular` (`Matrix.pow_succ_apply_eq_sum_pathProd`),
`Numlib/Analysis/Normed/Algebra/PrimaryFunctionalCalculus/{Basic,Analytic,Cauchy}` (`pfc_comp`,
`norm_pfc_sub_sum_le`, `pfc_eq_circleIntegral`), `Numlib/Analysis/Matrix/Function/Approximation`
(`Matrix.l2_opNorm_pfc_sub_le_of_conj_jordanForm`, `Matrix.frobenius_norm_pfc_sub_le_of_isCompact`,
`Matrix.norm_integral_pfc_smul_sub_simpsonSum_le`).

## Not formalized

(9.2.3) (notation for the Taylor remainder `E(s)`) and (9.2.4) (the entrywise mean-value remainder,
a step of the book's proof of Theorem 9.2.3); the numerical examples (after Theorem 9.2.2, the
`[-49 24; -64 31]` matrix, `q = 9`); the multiplication counts; the sin/cos scaling loop (its exact
content is the double-angle formulas).

## Errata

Theorem 9.2.1's `max` over `1 ≤ i ≤ p` is over `1 ≤ i ≤ q`. The proof of Theorem 9.2.2 cites
"Theorem 9.1.3" for Theorem 9.1.4 and sums `r` to `j - 1` for `j - i`; its `δ_r` is a supremum
over a closed convex `Ω`, finite only for bounded `Ω`. (9.2.4) applies the real mean-value form of
Taylor's remainder to complex-valued entries, where no `ε_ij` need exist; the bound of
Theorem 9.2.3 survives by the vector-valued integral remainder, even without the factor `n` (as the
book remarks after the proof, citing Mathias). The proof of Theorem 9.2.3 also writes
`f_ij^{(q-1)}` for `f_ij^{(q+1)}`, and needs the disk centred at `0`. (9.2.7) omits the factor `A⁴`
(`d⁴/dt⁴ f(At) = A⁴ f⁽⁴⁾(At)`).
-/

open Polynomial Finset Filter Topology
open scoped Nat ENNReal Real

namespace GolubVanLoan.Chapter09

variable {n : ℕ}

/-! ### §9.2.1 A Jordan analysis -/

section Jordan

open scoped Matrix.Norms.L2Operator

/-- **Theorem 9.2.1.** Let `A = X · diag(J₁, …, J_q) · X⁻¹` be a Jordan decomposition of
`A ∈ ℂ^{n×n}` (as in (9.1.3): `J_i` the `n_i × n_i` Jordan block at `λ_i`), and let `f`, `g` be
analytic on an open set containing `λ(A)` (analytic at every eigenvalue). Then
`‖f(A) - g(A)‖₂ ≤ κ₂(X) · max_{1 ≤ i ≤ q, 0 ≤ r ≤ n_i - 1} n_i |f⁽ʳ⁾(λ_i) - g⁽ʳ⁾(λ_i)| / r!`,
`κ₂(X) = ‖X‖₂ ‖X⁻¹‖₂` (the book's `max` over `1 ≤ i ≤ p` is over `i ≤ q`). Backbone
`Matrix.l2_opNorm_pfc_sub_le_of_conj_jordanForm`. -/
theorem theorem_9_2_1 {q : ℕ} (e : Fin q → ℕ) (μ : Fin q → ℂ) (σ : (Σ i, Fin (e i)) ≃ Fin n)
    {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X)
    (h : X⁻¹ * A * X = Matrix.reindex σ σ (Matrix.jordanForm e μ)) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z) (hg : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ g z) :
    ‖pfc f A - pfc g A‖ ≤ ‖X‖ * ‖X⁻¹‖ * ⨆ i, ⨆ r : Fin (e i),
      (e i : ℝ) * (‖iteratedDeriv r f (μ i) - iteratedDeriv r g (μ i)‖ / (r : ℕ)!) := by
  refine Matrix.l2_opNorm_pfc_sub_le_of_conj_jordanForm σ hX h hf hg
    (Real.iSup_nonneg fun i => Real.iSup_nonneg fun r => by positivity) fun i r hr => ?_
  refine le_ciSup_of_le (Set.finite_range _).bddAbove i ?_
  exact le_ciSup (f := fun r : Fin (e i) => (e i : ℝ) *
    (‖iteratedDeriv r f (μ i) - iteratedDeriv r g (μ i)‖ / (r : ℕ)!))
    (Set.finite_range _).bddAbove ⟨r, hr⟩

end Jordan

/-! ### §9.2.2 A Schur analysis -/

/-- **(9.2.1)**: if `Ω` is convex (and compact, so that the supremum is finite) and `h` is analytic
on a neighbourhood of `Ω`, then for nodes `λ_{s₀}, …, λ_{s_r} ∈ Ω`, repeated or not,
`|h[λ_{s₀}, …, λ_{s_r}]| ≤ sup_{z ∈ Ω} |h⁽ʳ⁾(z)| / r!`. -/
theorem equation_9_2_1 {Ω : Set ℂ} (hΩ : Convex ℝ Ω) (hΩc : IsCompact Ω) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h Ω) {r : ℕ} {s : Multiset ℂ} (hs : Multiset.card s = r + 1)
    (hsΩ : ∀ x ∈ s, x ∈ Ω) :
    ‖Hermite.divDiff h s‖ ≤ sSup ((fun z => ‖iteratedDeriv r h z‖) '' Ω) / r ! := by
  have hc : ContinuousOn (fun z => ‖iteratedDeriv r h z‖) Ω := by
    rw [iteratedDeriv_eq_iterate]
    exact (hh.iterated_deriv r).continuousOn.norm
  exact Hermite.norm_divDiff_le hΩ hh hs hsΩ fun z hz =>
    le_csSup (hΩc.bddAbove_image hc) ⟨z, hz, rfl⟩

/-- The path products of `|N|` are the absolute values of those of `N`. -/
private theorem pathProd_map_norm (N : Matrix (Fin n) (Fin n) ℂ) (l : List (Fin n)) :
    Matrix.pathProd (N.map (‖·‖)) l = ‖Matrix.pathProd N l‖ := by
  induction l with
  | nil => simp [Matrix.pathProd_nil]
  | cons i l ih =>
    cases l with
    | nil => simp [Matrix.pathProd_singleton]
    | cons j l =>
      rw [Matrix.pathProd_cons_cons, Matrix.pathProd_cons_cons, ih, norm_mul, Matrix.map_apply]

/-- **(9.2.2)** (the book's P9.2.1): for `N` strictly upper triangular and `r ≥ 1`, the entries of
`|N|^r` are `0` for `j < i + r` and otherwise
`∑_{s ∈ S_ij^{(r)}} |n_{s₀s₁} ⋯ n_{s_{r-1}s_r}|`, over the strictly increasing sequences
`i = s₀ < ⋯ < s_r = j` (interior indices `s ⊆ (i, j)` of size `r - 1`). Stated at the exponent
`r + 1`. -/
theorem equation_9_2_2 {N : Matrix (Fin n) (Fin n) ℂ} (hN : ∀ i j, j ≤ i → N i j = 0) (r : ℕ)
    (i j : Fin n) :
    ((j : ℕ) < i + (r + 1) → ((N.map (‖·‖)) ^ (r + 1)) i j = 0) ∧
    (i + (r + 1) ≤ (j : ℕ) → ((N.map (‖·‖)) ^ (r + 1)) i j =
      ∑ s ∈ (Ioo i j).powersetCard r, ‖Matrix.pathProd N (Matrix.path i s j)‖) := by
  have hN' : ∀ a b, b ≤ a → N.map (‖·‖) a b = 0 := fun a b h => by simp [hN a b h]
  have hsum : ∀ {a b : Fin n}, a < b → ((N.map (‖·‖)) ^ (r + 1)) a b =
      ∑ s ∈ (Ioo a b).powersetCard r, ‖Matrix.pathProd N (Matrix.path a s b)‖ := fun hab => by
    rw [Matrix.pow_succ_apply_eq_sum_pathProd hN' r hab]
    exact Finset.sum_congr rfl fun s _ => pathProd_map_norm N _
  refine ⟨fun hji => ?_, fun hij => hsum (Fin.lt_def.mpr (by omega))⟩
  rcases lt_or_ge i j with hij | hji'
  · rw [hsum hij, Finset.powersetCard_eq_empty.mpr, Finset.sum_empty]
    rw [Fin.card_Ioo]
    omega
  · have hup : (N.map (‖·‖)).IsUpperTriangular := fun a b hba => hN' a b (le_of_lt hba)
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases le_or_gt k i with hki | hik
    · rw [hN' i k hki, zero_mul]
    · rw [(hup.pow r) (show id j < id k from lt_of_le_of_lt hji' hik), mul_zero]

section Schur

open scoped Matrix Matrix.Norms.Frobenius

/-- **Theorem 9.2.2.** Let `Qᴴ A Q = T = diag(λ_i) + N` be a Schur decomposition of
`A ∈ ℂ^{n×n}` (`N` the strictly upper triangular part of `T`). If `f` and `g` are analytic on a
closed convex set `Ω` whose interior contains `λ(A)`, then
`‖f(A) - g(A)‖_F ≤ ∑_{r=0}^{n-1} δ_r ‖|N|^r‖_F / r!`,
`δ_r = sup_{z ∈ Ω} |f⁽ʳ⁾(z) - g⁽ʳ⁾(z)|`. `Ω` is taken **compact**, so that `δ_r` is finite (for an
unbounded `Ω` the supremum may be `+∞`, and Lean's `sSup` of an unbounded set of reals is `0`).
Backbone `Matrix.frobenius_norm_pfc_sub_le_of_isCompact`. -/
theorem theorem_9_2_2 {A Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hT : (Qᴴ * A * Q).IsUpperTriangular) {Ω : Set ℂ} (hΩc : IsCompact Ω) (hΩ : Convex ℝ Ω)
    (hAΩ : spectrum ℂ A ⊆ interior Ω) {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (hg : AnalyticOnNhd ℂ g Ω) :
    ‖pfc f A - pfc g A‖ ≤ ∑ r ∈ range n,
      sSup ((fun z => ‖iteratedDeriv r f z - iteratedDeriv r g z‖) '' Ω) *
        ‖((Qᴴ * A * Q - Matrix.diagonal (Qᴴ * A * Q).diag).map fun z => ‖z‖) ^ r‖ / r ! := by
  rw [← Matrix.star_eq_conjTranspose] at hT ⊢
  have h := Matrix.frobenius_norm_pfc_sub_le_of_isCompact hQ hT hΩc hΩ
    (hAΩ.trans interior_subset) hf hg
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun r _ => ?_))
  congr 3
  refine Set.image_congr fun z hz => ?_
  rw [iteratedDeriv_sub ((hf z hz).contDiffAt) ((hg z hz).contDiffAt)]

end Schur

/-! ### §9.2.3 Taylor approximants -/

section Taylor

open scoped Matrix.Norms.L2Operator

/-- **Theorem 9.2.3**: if `f(z) = ∑ α_k zᵏ` on an open disk centred at `0` containing `λ(A)`, then
`‖f(A) - ∑_{k=0}^{q} α_k Aᵏ‖₂ ≤ n/(q+1)! · max_{0 ≤ s ≤ 1} ‖A^{q+1} f^{(q+1)}(As)‖₂`, stated for
every bound `M` of the maximum. -/
theorem theorem_9_2_3 {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 r) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ μ ∈ spectrum ℂ A, μ ∈ Metric.eball 0 r) (q : ℕ) {M : ℝ}
    (hM : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖A ^ (q + 1) * pfc (iteratedDeriv (q + 1) f) ((s : ℂ) • A)‖ ≤ M) :
    ‖pfc f A - ∑ k ∈ range (q + 1), p.coeff k • A ^ k‖ ≤ n / (q + 1)! * M := by
  have h := norm_pfc_sub_sum_le hf (Algebra.IsIntegral.isIntegral A) hA q hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : pfc f A - ∑ k ∈ range (q + 1), p.coeff k • A ^ k = 0 := Subsingleton.elim _ _
    rw [this, norm_zero]
    simp
  · refine h.trans ?_
    rw [div_mul_eq_mul_div, mul_comm]
    gcongr
    exact le_mul_of_one_le_right hM0 (by exact_mod_cast hn)

end Taylor

/-- **The double-angle formulas** of §9.2.3: `cos(2A) = 2 cos(A)² - I` and
`sin(2A) = 2 sin(A) cos(A)`. -/
theorem double_angle (A : Matrix (Fin n) (Fin n) ℂ) :
    pfc Complex.cos ((2 : ℂ) • A) = (2 : ℂ) • pfc Complex.cos A ^ 2 - 1 ∧
    pfc Complex.sin ((2 : ℂ) • A) = (2 : ℂ) • (pfc Complex.sin A * pfc Complex.cos A) := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral A
  have hs := IsAlgClosed.splits (minpoly ℂ A)
  have htwo : pfc ((2 : ℂ) • fun z : ℂ => z) A = (2 : ℂ) • A := by
    rw [pfc_const_smul, pfc_id hI hs]
  have hlin : ContDiff ℂ ⊤ ((2 : ℂ) • fun z : ℂ => z) := contDiff_const.smul contDiff_id
  have hcos : ContDiff ℂ ⊤ Complex.cos := Complex.contDiff_cos
  have hsin : ContDiff ℂ ⊤ Complex.sin := Complex.contDiff_sin
  have hcomp : ∀ g : ℂ → ℂ, ContDiff ℂ ⊤ g →
      pfc g ((2 : ℂ) • A) = pfc (g ∘ ((2 : ℂ) • fun z : ℂ => z)) A := fun g hg => by
    rw [pfc_comp hI hs (fun μ _ => hlin.contDiffAt.of_le le_top)
      (fun μ _ => hg.contDiffAt.of_le le_top), htwo]
  constructor
  · have hf : Complex.cos ∘ ((2 : ℂ) • fun z : ℂ => z) =
        ((2 : ℂ) • (Complex.cos * Complex.cos)) - fun _ => (1 : ℂ) := by
      funext z
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.mul_apply,
        Complex.cos_two_mul]
      ring
    rw [hcomp _ hcos, hf, pfc_sub (f := (2 : ℂ) • (Complex.cos * Complex.cos))
      (g := fun _ => (1 : ℂ))
      (fun μ _ => (contDiff_const.smul (hcos.mul hcos)).contDiffAt.of_le le_top)
      (fun μ _ => contDiff_const.contDiffAt.of_le le_top), pfc_const_smul,
      pfc_mul hI hs (fun μ _ => hcos.contDiffAt.of_le le_top)
        (fun μ _ => hcos.contDiffAt.of_le le_top), pfc_const hI hs, map_one, sq]
  · have hf : Complex.sin ∘ ((2 : ℂ) • fun z : ℂ => z) = (2 : ℂ) • (Complex.sin * Complex.cos) := by
      funext z
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
        Complex.sin_two_mul]
      ring
    rw [hcomp _ hsin, hf, pfc_const_smul, pfc_mul hI hs (fun μ _ => hsin.contDiffAt.of_le le_top)
      (fun μ _ => hcos.contDiffAt.of_le le_top)]

/-! ### §9.2.4 Evaluating matrix polynomials -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 9.2.1 (Horner's scheme)**: given `A` and `b(0:q)`, compute
`F = b_q A^q + ⋯ + b₁ A + b₀ I`.
```
F = b_q A + b_{q-1} I
for k = q-2:-1:0
    F = A F + b_k I
end
```
The first step rounds each product `b_q a_ij`, then each diagonal sum `b_q a_ii + b_{q-1}`; each
update `F = A F + b_k I`
is chapter 1's `C ← C + A B` (Algorithm 1.1.5) with `C = b_k I`. -/
def algorithm_9_2_1 (A : Matrix (Fin n) (Fin n) ℝ) (q : ℕ) (b : ℕ → ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) := do
  let F ← (List.finRange n).foldlM (fun F i =>
    (List.finRange n).foldlM (fun (F : Matrix (Fin n) (Fin n) ℝ) j => do
      let v ← rnd (b q * A i j)
      pure (F.updateRow i (Function.update (F i) j v))) F) (0 : Matrix (Fin n) (Fin n) ℝ)
  let F ← (List.finRange n).foldlM (fun (F : Matrix (Fin n) (Fin n) ℝ) i => do
      let v ← rnd (F i i + b (q - 1))
      pure (F.updateRow i (Function.update (F i) i v))) F
  (List.range (q - 1)).reverse.foldlM (fun F k =>
    GolubVanLoan.Chapter01.algorithm_1_1_5 rnd A F (b k • (1 : Matrix (Fin n) (Fin n) ℝ))) F

/-- The least `k` with `β_k ≠ 0` in the binary expansion `s = ∑ β_k 2ᵏ` (`0` for `s = 0`). -/
noncomputable def lowestSetBit (s : ℕ) : ℕ :=
  open Classical in if h : ∃ k, s.testBit k then Nat.find h else 0

/-- **Algorithm 9.2.2 (Binary Powering)**: `F = Aˢ` for a positive integer `s`.
```
Let s = ∑_{k=0}^{t} β_k 2^k be the binary expansion of s with β_t ≠ 0
Z = A; q = 0
while β_q = 0
    Z = Z²; q = q + 1
end
F = Z
for k = q+1:t
    Z = Z²
    if β_k ≠ 0
        F = F Z
    end
end
```
The binary expansion is exact integer arithmetic (`t = ⌊log₂ s⌋`, `q = lowestSetBit s`); every
matrix product is chapter 1's Algorithm 1.1.5 with `C = 0`. -/
noncomputable def algorithm_9_2_2 (A : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) :
    M (Matrix (Fin n) (Fin n) ℝ) := do
  let t := Nat.log 2 s
  let q := lowestSetBit s
  let Z ← (List.range q).foldlM (fun Z _ =>
    GolubVanLoan.Chapter01.algorithm_1_1_5 rnd Z Z (0 : Matrix (Fin n) (Fin n) ℝ)) A
  let ZF ← (List.range' (q + 1) (t - q)).foldlM
    (fun (ZF : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) k => do
      let Z ← GolubVanLoan.Chapter01.algorithm_1_1_5 rnd ZF.1 ZF.1 0
      if s.testBit k then do
        let F ← GolubVanLoan.Chapter01.algorithm_1_1_5 rnd ZF.2 Z 0
        pure (Z, F)
      else pure (Z, ZF.2)) (Z, Z)
  pure ZF.2

end Programs

/-- Two nested loops over a duplicate-free row list writing each entry `(i, j)` once, from
`g i j`: on each row `List.foldl_update_self` and `List.foldl_update_eq_ite`, over the rows
`List.foldl_update_of_nodup`. -/
private theorem foldl_foldl_updateRow {α : Type*} (g : Fin n → Fin n → α) {l₁ : List (Fin n)}
    (hl₁ : l₁.Nodup) (l₂ : List (Fin n)) (F : Matrix (Fin n) (Fin n) α) (a c : Fin n) :
    (l₁.foldl (fun F i => l₂.foldl (fun F j => F.updateRow i (Function.update (F i) j (g i j))) F)
      F) a c = if a ∈ l₁ ∧ c ∈ l₂ then g a c else F a c := by
  have row : ∀ (F : Matrix (Fin n) (Fin n) α) i,
      l₂.foldl (fun F j => F.updateRow i (Function.update (F i) j (g i j))) F =
        Function.update F i (fun c => if c ∈ l₂ then g i c else F i c) := fun F i =>
    (List.foldl_update_self (fun j r => Function.update r j (g i j)) i l₂ F).trans
      (congrArg _ (List.foldl_update_eq_ite (g i) l₂ (F i)))
  have h := List.foldl_update_of_nodup hl₁ (fun i (y : Fin n → Fin n → α) c =>
    if c ∈ l₂ then g i c else y i c) (fun i _ y y' _ h => by rw [h]) F
  refine (congrFun (congrFun ((congrArg (fun G => l₁.foldl G F) (funext₂ row)).trans h) a)
    c).trans ?_
  by_cases ha : a ∈ l₁ <;> simp [ha]

/-- A loop adding `c` to each diagonal entry listed once: `List.foldl_update_of_nodup` on the
rows. -/
private theorem foldl_diag_add (c : ℝ) {l : List (Fin n)} (hl : l.Nodup)
    (F : Matrix (Fin n) (Fin n) ℝ) (a d : Fin n) :
    (l.foldl (fun (F : Matrix (Fin n) (Fin n) ℝ) i =>
      F.updateRow i (Function.update (F i) i (F i i + c))) F) a d =
      if a = d ∧ a ∈ l then F a a + c else F a d := by
  refine (congrFun (congrFun (List.foldl_update_of_nodup hl
    (fun i (y : Fin n → Fin n → ℝ) => Function.update (y i) i (y i i + c))
    (fun i _ y y' _ h => by rw [h]) F) a) d).trans ?_
  by_cases had : a = d
  · subst had
    by_cases ha : a ∈ l <;> simp [ha]
  · by_cases ha : a ∈ l <;> simp [ha, had, Ne.symm had]

/-- The Horner loop: from `F`, the updates `F ← A F + b_k I` for `k = m-1, …, 0` give
`∑_{i<m} b_i Aⁱ + Aᵐ F`. -/
private theorem foldl_horner (A : Matrix (Fin n) (Fin n) ℝ) (b : ℕ → ℝ) (m : ℕ)
    (F : Matrix (Fin n) (Fin n) ℝ) :
    (List.range m).reverse.foldl (fun F k => b k • (1 : Matrix (Fin n) (Fin n) ℝ) + A * F) F =
      ∑ i ∈ range m, b i • A ^ i + A ^ m * F := by
  induction m generalizing F with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons, ih, Finset.sum_range_succ, mul_add, ← mul_assoc, ← pow_succ, mul_smul_comm,
      mul_one]
    abel

/-- **Exact semantics of Algorithm 9.2.1**: for `q ≥ 1` it returns `∑_{k=0}^{q} b_k Aᵏ`. -/
theorem algorithm_9_2_1_spec (A : Matrix (Fin n) (Fin n) ℝ) {q : ℕ} (hq : 1 ≤ q) (b : ℕ → ℝ) :
    Id.run (algorithm_9_2_1 pure A q b) = ∑ k ∈ range (q + 1), b k • A ^ k := by
  have key : ∀ F₀ : Matrix (Fin n) (Fin n) ℝ,
      F₀ = b q • A + b (q - 1) • (1 : Matrix (Fin n) (Fin n) ℝ) →
      (List.range (q - 1)).reverse.foldl
        (fun F k => b k • (1 : Matrix (Fin n) (Fin n) ℝ) + A * F) F₀ =
        ∑ k ∈ range (q + 1), b k • A ^ k := by
    rintro F₀ rfl
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [foldl_horner, mul_add, mul_smul_comm, ← pow_succ, mul_smul_comm, mul_one,
      Finset.sum_range_succ, Finset.sum_range_succ]
    abel
  simp only [algorithm_9_2_1, Id.run_bind, List.idRun_foldlM, Id.run_pure,
    GolubVanLoan.Chapter01.algorithm_1_1_5_spec]
  refine key _ ?_
  ext a c
  rw [foldl_diag_add _ (List.nodup_finRange n),
    foldl_foldl_updateRow (fun i j => b q * A i j) (List.nodup_finRange n),
    foldl_foldl_updateRow (fun i j => b q * A i j) (List.nodup_finRange n)]
  by_cases hac : a = c
  · subst hac; simp
  · simp [hac, Matrix.one_apply_ne hac]

/-- **(9.2.5), Paterson–Stockmeyer**: for `r = ⌊q/s⌋`,
`p(A) = ∑_{k=0}^{r} B_k (A^s)^k` with `B_k = b_{sk+s-1} A^{s-1} + ⋯ + b_{sk} I` for `k < r` and
`B_r = b_q A^{q-sr} + ⋯ + b_{sr} I` — in any algebra (the book's `s ≤ √q` only minimizes the
number of multiplications; the identity even holds for `s = 0`, where `r = 0`). -/
theorem equation_9_2_5 {K R : Type*} [CommSemiring K] [Semiring R] [Algebra K R] (b : ℕ → K)
    (A : R) (s q : ℕ) :
    ∑ k ∈ range (q + 1), b k • A ^ k =
      ∑ k ∈ range (q / s + 1),
        (if k < q / s then ∑ i ∈ range s, b (s * k + i) • A ^ i
          else ∑ i ∈ range (q - s * (q / s) + 1), b (s * (q / s) + i) • A ^ i) * (A ^ s) ^ k := by
  set r := q / s
  have hblock : ∀ m, ∑ x ∈ range (s * m), b x • A ^ x =
      ∑ k ∈ range m, ∑ i ∈ range s, b (s * k + i) • A ^ (s * k + i) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
  have hqr : s * r ≤ q := Nat.mul_div_le q s
  have hmul : ∀ (k : ℕ) (t : Finset ℕ), (∑ i ∈ t, b (s * k + i) • A ^ i) * (A ^ s) ^ k =
      ∑ i ∈ t, b (s * k + i) • A ^ (s * k + i) := fun k t => by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, ← pow_mul, ← pow_add, add_comm]
  have h1 : ∑ k ∈ range r, (if k < r then ∑ i ∈ range s, b (s * k + i) • A ^ i
      else ∑ i ∈ range (q - s * r + 1), b (s * r + i) • A ^ i) * (A ^ s) ^ k =
      ∑ k ∈ range r, ∑ i ∈ range s, b (s * k + i) • A ^ (s * k + i) :=
    Finset.sum_congr rfl fun k hk => by rw [ite_eq_left (Finset.mem_range.mp hk), hmul]
  symm
  rw [Finset.sum_range_succ, h1, ite_eq_right (lt_irrefl r), hmul]
  conv_rhs => rw [show q + 1 = s * r + (q - s * r + 1) by omega, Finset.sum_range_add, hblock]

/-! ### §9.2.5 Computing powers of a matrix -/

/-- The bits below the lowest set bit vanish, and the lowest set bit is set. -/
private theorem mod_two_pow_succ_lowestSetBit {s : ℕ} (hs : s ≠ 0) :
    s % 2 ^ (lowestSetBit s + 1) = 2 ^ lowestSetBit s ∧ s.testBit (lowestSetBit s) := by
  have hex : ∃ k, s.testBit k := Nat.exists_testBit_of_ne_zero hs
  have hq : lowestSetBit s = Nat.find hex := by
    classical
    rw [lowestSetBit, dite_eq_left hex]
  have hbit : s.testBit (lowestSetBit s) := hq ▸ Nat.find_spec hex
  refine ⟨?_, hbit⟩
  have hlow : s % 2 ^ lowestSetBit s = 0 := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < lowestSetBit s
    · have := Nat.find_min hex (hq ▸ hi)
      simp [hi, this]
    · simp [hi]
  rw [Nat.mod_pow_succ, hlow, zero_add]
  have h1 : s / 2 ^ lowestSetBit s % 2 = 1 := by
    have := Nat.testBit_eq_decide_div_mod_eq (x := s) (i := lowestSetBit s)
    rw [hbit] at this
    exact of_decide_eq_true this.symm
  rw [h1, mul_one]

/-- One step of the main loop of Algorithm 9.2.2 in exact arithmetic. -/
private theorem binaryPower_step (A : Matrix (Fin n) (Fin n) ℝ) (s k : ℕ) :
    (if s.testBit k then A ^ (s % 2 ^ k) * A ^ 2 ^ k else A ^ (s % 2 ^ k)) =
      A ^ (s % 2 ^ (k + 1)) := by
  rw [Nat.mod_pow_succ]
  have := Nat.testBit_eq_decide_div_mod_eq (x := s) (i := k)
  cases h : s.testBit k
  · have h0 : s / 2 ^ k % 2 = 0 := by
      rw [h] at this
      have := of_decide_eq_false this.symm
      omega
    simp [h0]
  · have h1 : s / 2 ^ k % 2 = 1 := of_decide_eq_true (by rw [← this, h])
    simp [h1, pow_add]

/-- **Exact semantics of Algorithm 9.2.2**: for `s ≥ 1` it returns `Aˢ`. After the squaring loop
`Z = A^{2^q}`; after step `k` of the main loop `Z = A^{2^k}` and `F = A^{s mod 2^{k+1}}`; at
`k = t`, `s mod 2^{t+1} = s`. -/
theorem algorithm_9_2_2_spec (A : Matrix (Fin n) (Fin n) ℝ) {s : ℕ} (hs : 1 ≤ s) :
    Id.run (algorithm_9_2_2 pure A s) = A ^ s := by
  have hs0 : s ≠ 0 := by omega
  obtain ⟨hmod, hbit⟩ := mod_two_pow_succ_lowestSetBit hs0
  set q := lowestSetBit s with hqdef
  set t := Nat.log 2 s with htdef
  have hqt : q ≤ t := by
    have := Nat.ge_two_pow_of_testBit hbit
    exact Nat.le_log_of_pow_le (by norm_num) this
  have hst : s % 2 ^ (t + 1) = s :=
    Nat.mod_eq_of_lt (Nat.lt_pow_succ_log_self (by norm_num) s)
  have hsq : ∀ m, (List.range m).foldl (fun Z (_ : ℕ) => Z * Z) A = A ^ 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [List.range_succ, List.foldl_append, ih]; simp [pow_succ, pow_mul]
  have hmain : ∀ (m k₀ : ℕ), (List.range' (k₀ + 1) m).foldl
      (fun (ZF : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) k =>
        if s.testBit k then (ZF.1 * ZF.1, ZF.2 * (ZF.1 * ZF.1)) else (ZF.1 * ZF.1, ZF.2))
      (A ^ 2 ^ k₀, A ^ (s % 2 ^ (k₀ + 1))) = (A ^ 2 ^ (k₀ + m), A ^ (s % 2 ^ (k₀ + m + 1))) := by
    intro m
    induction m with
    | zero => intro k₀; simp
    | succ m ih =>
      intro k₀
      rw [List.range'_succ, List.foldl_cons]
      have hZ : A ^ 2 ^ k₀ * A ^ 2 ^ k₀ = A ^ 2 ^ (k₀ + 1) := by rw [← pow_add, pow_succ, mul_two]
      have hstep := binaryPower_step A s (k₀ + 1)
      have : (if s.testBit (k₀ + 1) then (A ^ 2 ^ k₀ * A ^ 2 ^ k₀,
          A ^ (s % 2 ^ (k₀ + 1)) * (A ^ 2 ^ k₀ * A ^ 2 ^ k₀))
          else (A ^ 2 ^ k₀ * A ^ 2 ^ k₀, A ^ (s % 2 ^ (k₀ + 1)))) =
          (A ^ 2 ^ (k₀ + 1), A ^ (s % 2 ^ (k₀ + 1 + 1))) := by
        rw [hZ, ← hstep]
        split_ifs <;> rfl
      rw [this, ih (k₀ + 1), show k₀ + 1 + m = k₀ + (m + 1) by omega]
  simp only [algorithm_9_2_2, Id.run_bind, List.idRun_foldlM, apply_ite Id.run, Id.run_pure,
    GolubVanLoan.Chapter01.algorithm_1_1_5_spec, zero_add]
  rw [← htdef, ← hqdef, hsq]
  have h0 : (A ^ 2 ^ q, A ^ 2 ^ q) = (A ^ 2 ^ q, A ^ (s % 2 ^ (q + 1))) := by rw [hmod]
  rw [h0, hmain]
  simp only
  rw [show q + (t - q) + 1 = t + 1 by omega, hst]

/-! ### §9.2.6 Integrating matrix functions -/

/-- The composite Simpson weights `w_0, …, w_m = 1, 4, 2, 4, …, 2, 4, 1` of (9.2.6), `m = 2N`,
regrouped by panels: `∑_{k=0}^{2N} w_k g_k = ∑_{j<N} (g_{2j} + 4 g_{2j+1} + g_{2j+2})`. -/
private theorem sum_simpsonWeight_smul {M : Type*} [AddCommGroup M] [Module ℝ M] (g : ℕ → M)
    {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ range (2 * N + 1),
        (if k = 0 ∨ k = 2 * N then (1 : ℝ) else if Odd k then 4 else 2) • g k =
      ∑ j ∈ range N, (g (2 * j) + (4 : ℝ) • g (2 * j + 1) + g (2 * j + 2)) := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp [Finset.sum_range_succ]
  | succ N hN ih =>
    have hint : ∀ c : ℕ, 2 * N ≤ c → ∑ k ∈ range (2 * N),
        (if k = 0 ∨ k = c then (1 : ℝ) else if Odd k then 4 else 2) • g k =
          ∑ k ∈ range (2 * N), (if k = 0 then (1 : ℝ) else if Odd k then 4 else 2) • g k :=
      fun c hc => Finset.sum_congr rfl fun k hk => by
        have hk' : k ≠ c := by have := Finset.mem_range.1 hk; omega
        simp [hk']
    rw [Finset.sum_range_succ, hint (2 * N) le_rfl] at ih
    rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, hint (2 * (N + 1)) (by omega),
      Finset.sum_range_succ, ← ih]
    have h1 : ¬ (2 * N = 0 ∨ 2 * N = 2 * (N + 1)) := by omega
    have h2 : ¬ (2 * N + 1 = 0 ∨ 2 * N + 1 = 2 * (N + 1)) := by omega
    have h3 : 2 * N + 1 + 1 = 0 ∨ 2 * N + 1 + 1 = 2 * (N + 1) := Or.inr (by ring)
    have h4 : ¬ Odd (2 * N) := by simp
    have h5 : Odd (2 * N + 1) := odd_two_mul_add_one N
    have h6 : 2 * N = 0 ∨ 2 * N = 2 * N := Or.inr rfl
    rw [ite_eq_right h1, ite_eq_right h4, ite_eq_right h2, ite_eq_left h5, ite_eq_left h3,
      ite_eq_left h6]
    rw [show 2 * N + 1 + 1 = 2 * N + 2 by ring]
    module

section Simpson

open scoped Matrix.Norms.L2Operator

/-- **(9.2.6)–(9.2.7), corrected.** For `A ∈ ℂ^{n×n}` and `f` analytic at `t μ` for every
`t ∈ [a, b]` and every eigenvalue `μ` of `A`, `m` even, `h = (b - a)/m` and the Simpson
approximation `F̃ = (h/3) ∑_{k=0}^m w_k f(A(a + kh))` (`w = 1, 4, 2, …, 2, 4, 1`) of
`F = ∫_a^b f(At) dt`, `F̃ = F + E` with
`‖E‖₂ ≤ n h⁴ (b - a)/180 · max_{a ≤ t ≤ b} ‖A⁴ f⁽⁴⁾(At)‖₂`. The book prints `‖f⁽⁴⁾(At)‖₂` without
the factor `A⁴`, which is false (`n = 1`, `f = exp`, `A = 2`: `d⁴/dt⁴ e^{2t} = 16 e^{2t}`). Backbone
`Matrix.norm_integral_pfc_smul_sub_simpsonSum_le` (without the factor `n`), on `m/2` panels of
width `2h`. -/
theorem equation_9_2_7 (A : Matrix (Fin n) (Fin n) ℂ) {f : ℂ → ℂ} {a b h : ℝ} (hab : a < b)
    {m : ℕ} (hm : Even m) (hm0 : 0 < m) (hh : h = (b - a) / m)
    (hf : ∀ t ∈ Set.Icc a b, ∀ μ ∈ spectrum ℂ A, AnalyticAt ℂ f (t * μ)) :
    ‖(h / 3) • ∑ k ∈ range (m + 1), (if k = 0 ∨ k = m then (1 : ℝ) else if Odd k then 4 else 2) •
          pfc f (((a + k * h : ℝ) : ℂ) • A) - ∫ t in a..b, pfc f ((t : ℂ) • A)‖ ≤
      n * h ^ 4 * (b - a) / 180 *
        sSup ((fun t : ℝ => ‖A ^ 4 * pfc (iteratedDeriv 4 f) ((t : ℂ) • A)‖) '' Set.Icc a b) := by
  obtain ⟨N, rfl⟩ := hm
  have hN : 0 < N := by omega
  rw [← two_mul] at hh ⊢
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · calc _ = (0 : ℝ) := by rw [norm_eq_zero]; exact Subsingleton.elim _ _
      _ ≤ _ := by simp
  set S := sSup ((fun t : ℝ => ‖A ^ 4 * pfc (iteratedDeriv 4 f) ((t : ℂ) • A)‖) '' Set.Icc a b)
  have hS : 0 ≤ S := Real.sSup_nonneg fun x ⟨t, _, ht⟩ => ht ▸ norm_nonneg _
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have key := Matrix.norm_integral_pfc_smul_sub_simpsonSum_le A hab hN (H := 2 * h)
    (by rw [hh]; push_cast; field_simp) hf
  have e : ∀ x y : ℝ, x = y → pfc f ((x : ℂ) • A) = pfc f ((y : ℂ) • A) := fun x y hxy => by
    rw [hxy]
  have hF : (h / 3) • ∑ k ∈ range (2 * N + 1),
      (if k = 0 ∨ k = 2 * N then (1 : ℝ) else if Odd k then 4 else 2) •
        pfc f (((a + k * h : ℝ) : ℂ) • A) =
      ∑ j ∈ range N, (2 * h / 6) • (pfc f (((a + j * (2 * h) : ℝ) : ℂ) • A) +
        (4 : ℝ) • pfc f (((a + j * (2 * h) + 2 * h / 2 : ℝ) : ℂ) • A) +
          pfc f (((a + (j + 1) * (2 * h) : ℝ) : ℂ) • A)) := by
    rw [sum_simpsonWeight_smul (fun k : ℕ => pfc f (((a + k * h : ℝ) : ℂ) • A)) hN,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 2 * h / 6 = h / 3 by ring,
      e (a + ((2 * j : ℕ) : ℝ) * h) (a + j * (2 * h)) (by push_cast; ring),
      e (a + ((2 * j + 1 : ℕ) : ℝ) * h) (a + j * (2 * h) + 2 * h / 2) (by push_cast; ring),
      e (a + ((2 * j + 2 : ℕ) : ℝ) * h) (a + (j + 1) * (2 * h)) (by push_cast; ring)]
  rw [norm_sub_rev, hF]
  refine key.trans ?_
  have hq : 0 ≤ h ^ 4 * (b - a) / 180 * S :=
    mul_nonneg (div_nonneg (mul_nonneg (by positivity) (by linarith)) (by norm_num)) hS
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc (2 * h / 2) ^ 4 * (b - a) / 180 * S = h ^ 4 * (b - a) / 180 * S := by ring
    _ ≤ n * (h ^ 4 * (b - a) / 180 * S) := le_mul_of_one_le_left hq hn1
    _ = n * h ^ 4 * (b - a) / 180 * S := by ring

end Simpson

/-! ### §9.2.7 The Cauchy integral formulation -/

section Cauchy

open scoped Matrix.Norms.L2Operator

/-- **(9.2.8)**, for circular contours: if `f` is analytic on a neighbourhood of the closed disk
`|z - c| ≤ R` whose interior contains `λ(A)`, then
`f(A) = (2πi)⁻¹ ∮_{|z - c| = R} f(z) (zI - A)⁻¹ dz`. -/
theorem equation_9_2_8 {A : Matrix (Fin n) (Fin n) ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R)) (hA : spectrum ℂ A ⊆ Metric.ball c R) :
    pfc f A = (2 * π * Complex.I)⁻¹ •
      ∮ z in C(c, R), f z • (z • (1 : Matrix (Fin n) (Fin n) ℂ) - A)⁻¹ := by
  rw [pfc_eq_circleIntegral (Algebra.IsIntegral.isIntegral A) hf hA]
  congr 2
  funext z
  rw [Algebra.algebraMap_eq_smul_one, Matrix.nonsing_inv_eq_ringInverse]

end Cauchy

end GolubVanLoan.Chapter09
