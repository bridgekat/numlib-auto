import Numlib.Analysis.Fourier.SineCosineTransform
import NumlibSurface.GolubVanLoan.Chapter01.Section03

/-!
# Golub–Van Loan §1.4: fast matrix-vector products

Surface file for §1.4 of Golub and Van Loan, *Matrix Computations* (4th edition): the DFT matrix and
the radix-2 FFT (Algorithm 1.4.1), the block structure of `F_{2m}` (Theorem 1.4.1), the fast sine
and cosine transforms through it ((1.4.3)–(1.4.11), Algorithms 1.4.2–1.4.3), and the Haar wavelet
transform ((1.4.13), Algorithm 1.4.4).

## Design

The book's `F_n = (ω_n^{kj})`, `ω_n = exp(−2πi/n)` ((1.4.1)–(1.4.2)) is `fourierMatrix n`, the
conjugate transpose of the backbone's `Matrix.dft n` (whose root is `exp(+2πi/n)`); its radix-2
splitting is the backbone's `Matrix.dft_radix_two`/`Matrix.dft_radix_two_add`. `S_r`, `C_r` of
(1.4.6) are `Matrix.dst1 r` and `Matrix.cosMatrix r`, `DCT(m+1)` of (1.4.10) is `Matrix.dct1 m`, and
`x_sin`, `x_cos` ((1.4.9), (1.4.11)) are `Matrix.oddExtensionVec` and `Matrix.evenExtensionVec`
(`Numlib/Analysis/Fourier/SineCosineTransform`); the exchange `E` is `Matrix.exchange` (§1.2). The
book's indices `k, j` in (1.4.3)–(1.4.5) already start at `0`; 0-based `Fin` indices shift the
others by one, as stated per declaration.

The fast transforms are complex algorithms: their hook is `rnd : ℂ → M ℂ`, through which every
complex `+`, `−`, `×`, `/`, the root `ω = exp(−2πi/n)` and each twiddle factor `ω^k` (by the
recurrence `ω^k = ω^{k−1} ω`) pass; multiplication by `i` is exact (it swaps the real and imaginary
parts with a negation, convention 1). Their exact semantics is the same as in the real case; no
complex rounding model exists in the backbone, and the book analyses none. The Haar transform is a
real algorithm. The recursive algorithms recurse on `t` with `n = 2^t`; the halves of
`Fin (2^(t+1))` are `GolubVanLoan.Chapter01.twoPowSplit` and the even/odd positions are
`finProdFinEquiv` on `Fin (2^t * 2)`, which is `Fin (2^(t+1))` definitionally.

The Haar matrix `W_n` is surface-only: no other source uses the discrete Haar transform (the
backbone's `Numlib/Analysis/Wavelet/Haar` is the continuous system on `L²(ℝ)`).

## Main results

* `fourierMatrix`, `equation_1_4_5` — `F_n` and its entries in real form.
* `algorithm_1_4_1`, `algorithm_1_4_1_spec` — the radix-2 FFT.
* `theorem_1_4_1` — the block structure (1.4.7) of `F_{2m}`.
* `dstTransform`, `dctTransform`, `equation_1_4_8`, `equation_1_4_10` — the DST and DCT.
* `algorithm_1_4_2`, `algorithm_1_4_3` and their specifications — the DST and DCT through the FFT.
* `haarMatrix`, `equation_1_4_13`, `algorithm_1_4_4`, `algorithm_1_4_4_spec` — the Haar transform.

## Not formalized here

The flop analyses (`8n log₂ n`, `5n log₂ n`, `2n`), the display of `F_8(:,cols)` as a worked
example (its content is the radix-2 splitting), the definitions DST-II … DCT-IV of (1.4.12) and the
remark that DST-II is a subvector of a DST of an interleaved vector (the backbone's `Matrix.dst2`,
`Matrix.dct2` serve chapter 4), the examples `F_4`, `W_2`, `W_4`, `W_8`.
-/

open Matrix Complex
open scoped Real

namespace GolubVanLoan.Chapter01

/-! ### Vector operations with a rounding hook -/

section VectorOps

variable {M : Type → Type} [Monad M] {K : Type} (rnd : K → M K)

/-- The entrywise rounded sum `fl(u + v)` of two vectors, `u(k) = u(k) + v(k)` over `k`. -/
def vecAdd [Add K] {n : ℕ} (u v : Fin n → K) : M (Fin n → K) :=
  (List.finRange n).foldlM (fun y k => do
    let s ← rnd (y k + v k)
    pure (Function.update y k s)) u

/-- The entrywise rounded difference `fl(u − v)` of two vectors. -/
def vecSub [Sub K] {n : ℕ} (u v : Fin n → K) : M (Fin n → K) :=
  (List.finRange n).foldlM (fun y k => do
    let s ← rnd (y k - v k)
    pure (Function.update y k s)) u

/-- The entrywise rounded product `fl(d .* v)` of two vectors, the book's `d .* y`. -/
def vecPointwiseMul [Mul K] {n : ℕ} (d v : Fin n → K) : M (Fin n → K) :=
  (List.finRange n).foldlM (fun y k => do
    let s ← rnd (d k * y k)
    pure (Function.update y k s)) v

end VectorOps

/-- In exact arithmetic `vecAdd` is the sum. -/
theorem vecAdd_spec {K : Type} [Add K] {n : ℕ} (u v : Fin n → K) :
    Id.run (vecAdd pure u v) = u + v := by
  funext k
  rw [vecAdd, List.idRun_foldlM_update_apply (fun k b => (pure (b + v k) : Id K)) _
    (List.nodup_finRange n), ite_eq_left (List.mem_finRange k)]
  rfl

/-- In exact arithmetic `vecSub` is the difference. -/
theorem vecSub_spec {K : Type} [Sub K] {n : ℕ} (u v : Fin n → K) :
    Id.run (vecSub pure u v) = u - v := by
  funext k
  rw [vecSub, List.idRun_foldlM_update_apply (fun k b => (pure (b - v k) : Id K)) _
    (List.nodup_finRange n), ite_eq_left (List.mem_finRange k)]
  rfl

/-- In exact arithmetic `vecPointwiseMul` is the entrywise product. -/
theorem vecPointwiseMul_spec {K : Type} [Mul K] {n : ℕ} (d v : Fin n → K) :
    Id.run (vecPointwiseMul pure d v) = d * v := by
  funext k
  rw [vecPointwiseMul, List.idRun_foldlM_update_apply (fun k b => (pure (d k * b) : Id K)) _
    (List.nodup_finRange n), ite_eq_left (List.mem_finRange k)]
  rfl

/-- In exact arithmetic, a loop writing entry `k` of a vector with a value not depending on the
state sets the vector to those values. -/
private theorem idRun_foldlM_finRange_set {K : Type} {n : ℕ} (f : Fin n → K) (y₀ : Fin n → K) :
    Id.run ((List.finRange n).foldlM (fun (y : Fin n → K) k => do
      let v ← (pure (f k) : Id K); pure (Function.update y k v)) y₀) = f := by
  funext k
  rw [List.idRun_foldlM_update_apply (fun k _ => (pure (f k) : Id K)) _ (List.nodup_finRange n),
    ite_eq_left (List.mem_finRange k)]
  rfl

/-- **An invariant of a `finRange` loop in exact arithmetic**, indexed by the step count. -/
private theorem foldl_finRange_invariant {β : Type} {n : ℕ} (f : β → Fin n → β) (a : β)
    (I : ℕ → β → Prop) (h0 : I 0 a) (hstep : ∀ (k : Fin n) c, I k c → I (k + 1) (f c k)) :
    I n ((List.finRange n).foldl f a) := by
  have h := SetM.forall_mem_run_foldlM_finRange (f := fun c k => (pure (f c k) : SetM β)) I h0
    fun k c hc c' hc' => by
      rw [SetM.mem_run_pure] at hc'
      subst hc'
      exact hstep k c hc
  exact h _ (by rw [List.foldlM_pure]; exact SetM.mem_run_pure.2 rfl)

/-! ### The DFT matrix -/

/-- **(1.4.1)–(1.4.2)**: the DFT matrix `F_n = (f_kj)`, `f_kj = ω_n^{(k−1)(j−1)}` (1-based),
`ω_n = exp(−2πi/n) = cos(2π/n) − i sin(2π/n)`: the conjugate transpose of the backbone's
`Matrix.dft n`, whose root is `exp(+2πi/n)` (`fourierMatrix_apply`). -/
noncomputable def fourierMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (dft n)ᴴ

/-- The entries of `F_n`, 0-based: `F_n k j = ω_n^{kj}`, `ω_n = exp(−2πi/n)`. -/
theorem fourierMatrix_apply {n : ℕ} (k j : Fin n) :
    fourierMatrix n k j = Complex.exp (-2 * π * I / n) ^ ((k : ℕ) * (j : ℕ)) := by
  rw [fourierMatrix, conjTranspose_dft_apply, ← Complex.exp_neg]
  congr 2
  ring

/-- **(1.4.5)**: for `k, j = 0 : 2m − 1`, `[F_{2m}]_{k+1, j+1} = ω_{2m}^{kj} = cos(kjπ/m) −
i sin(kjπ/m)` (the book's `k, j` are already 0-based here). -/
theorem equation_1_4_5 {m : ℕ} (k j : Fin (2 * m)) :
    fourierMatrix (2 * m) k j =
      (Real.cos ((k : ℕ) * (j : ℕ) * π / m) : ℂ) -
        I * (Real.sin ((k : ℕ) * (j : ℕ) * π / m) : ℂ) := by
  have h : 2 * π * ((k : ℕ) : ℝ) * ((j : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ) =
      (k : ℕ) * (j : ℕ) * π / m := by
    push_cast
    rw [show (2 : ℝ) * π * (k : ℕ) * (j : ℕ) = 2 * ((k : ℕ) * (j : ℕ) * π) by ring,
      mul_div_mul_left _ _ two_ne_zero]
  rw [fourierMatrix, conjTranspose_dft_apply_eq_cos_sub_sin, h]

/-- `F_1 = [1]`. -/
private theorem fourierMatrix_one : fourierMatrix 1 = 1 := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, fourierMatrix_apply, one_apply_eq]
  simp

/-- `F_N` along an equality of orders. -/
private theorem fourierMatrix_mulVec_cast {N N' : ℕ} (h : N = N') (v : Fin N' → ℂ) (i : Fin N) :
    (fourierMatrix N *ᵥ (v ∘ Fin.cast h)) i = (fourierMatrix N' *ᵥ v) (Fin.cast h i) := by
  subst h
  rfl

/-- **The radix-2 splitting** of `F_N`, `N = 2n`: `y(1:n) = y_T + d .* y_B`,
`y(n+1:N) = y_T − d .* y_B` with `y_T = F_n x(1:2:N)`, `y_B = F_n x(2:2:N)` and
`d = [1, ω_N, …, ω_N^{n−1}]` — the backbone's `Matrix.dft_radix_two`, `Matrix.dft_radix_two_add`. -/
private theorem fourier_radix_two {N n : ℕ} (hN : N = 2 * n) (x : Fin N → ℂ) (k : Fin n) :
    (fourierMatrix N *ᵥ x) ⟨k, by omega⟩ =
        (fourierMatrix n *ᵥ fun l : Fin n => x ⟨2 * l, by omega⟩) k +
          Complex.exp (-2 * π * I / N) ^ (k : ℕ) *
            (fourierMatrix n *ᵥ fun l : Fin n => x ⟨2 * l + 1, by omega⟩) k ∧
      (fourierMatrix N *ᵥ x) ⟨k + n, by omega⟩ =
        (fourierMatrix n *ᵥ fun l : Fin n => x ⟨2 * l, by omega⟩) k -
          Complex.exp (-2 * π * I / N) ^ (k : ℕ) *
            (fourierMatrix n *ᵥ fun l : Fin n => x ⟨2 * l + 1, by omega⟩) k := by
  subst hN
  have hω : Complex.exp (-2 * π * I / ((2 * n : ℕ) : ℂ)) =
      (Complex.exp (2 * π * I / (2 * n)))⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [hω]
  exact ⟨dft_radix_two x k, dft_radix_two_add x k⟩

/-! ### Algorithm 1.4.1: the radix-2 FFT -/

section FFT

variable {M : Type → Type} [Monad M] (rnd : ℂ → M ℂ)

/-- The twiddle factors `d = [1, ω, …, ω^{m−1}]` of Algorithm 1.4.1, each power formed from the
previous one by a rounded multiplication: `d_0 = 1`, `d_k = fl(d_{k−1} ω)`. -/
def fftTwiddles (m : ℕ) (ω : ℂ) : M (Fin m → ℂ) := do
  let st ← (List.finRange m).foldlM (fun (st : (Fin m → ℂ) × ℂ) (k : Fin m) => do
    let c ← (if (k : ℕ) = 0 then pure 1 else rnd (st.2 * ω) : M ℂ)
    pure (Function.update st.1 k c, c)) (fun _ => 0, 1)
  pure st.1

/-- **Algorithm 1.4.1** (radix-2 FFT). "If `x ∈ ℂⁿ` and `n = 2^t`, then this algorithm computes the
discrete Fourier transform `y = F_n x`":
```
function y = fft(x, n)
    if n = 1
        y = x
    else
        m = n/2
        y_T = fft(x(1:2:n), m)
        y_B = fft(x(2:2:n), m)
        ω = exp(−2πi/n)
        d = [1, ω, ⋯, ω^{m−1}]ᵀ
        z = d .* y_B
        y = [y_T + z; y_T − z]
    end
```
-/
noncomputable def algorithm_1_4_1 : (t : ℕ) → (Fin (2 ^ t) → ℂ) → M (Fin (2 ^ t) → ℂ)
  | 0, x => pure x
  | t + 1, x => do
    let yT ← algorithm_1_4_1 t fun l : Fin (2 ^ t) =>
      x ⟨2 * l, by have := l.isLt; rw [pow_succ]; omega⟩
    let yB ← algorithm_1_4_1 t fun l : Fin (2 ^ t) =>
      x ⟨2 * l + 1, by have := l.isLt; rw [pow_succ]; omega⟩
    let ω ← rnd (Complex.exp (-2 * π * I / (2 ^ (t + 1) : ℕ)))
    let d ← fftTwiddles rnd (2 ^ t) ω
    let z ← vecPointwiseMul rnd d yB
    let top ← vecAdd rnd yT z
    let bot ← vecSub rnd yT z
    pure (Sum.elim top bot ∘ (twoPowSplit t).symm)

end FFT

/-- In exact arithmetic the twiddle factors are the powers `ω^k`. -/
theorem fftTwiddles_spec (m : ℕ) (ω : ℂ) :
    Id.run (fftTwiddles pure m ω) = fun k : Fin m => ω ^ (k : ℕ) := by
  have key := foldl_finRange_invariant
    (fun (st : (Fin m → ℂ) × ℂ) (k : Fin m) =>
      (Function.update st.1 k (if (k : ℕ) = 0 then 1 else st.2 * ω),
        if (k : ℕ) = 0 then 1 else st.2 * ω)) ((fun _ => 0), 1)
    (fun j (st : (Fin m → ℂ) × ℂ) =>
      (∀ l : Fin m, (l : ℕ) < j → st.1 l = ω ^ (l : ℕ)) ∧ (0 < j → st.2 = ω ^ (j - 1)))
    ⟨fun l hl => absurd hl (Nat.not_lt_zero _), fun h => absurd h (lt_irrefl 0)⟩
    (fun k st ⟨h₁, h₂⟩ => by
      have hc : (if (k : ℕ) = 0 then (1 : ℂ) else st.2 * ω) = ω ^ (k : ℕ) := by
        split_ifs with hk
        · rw [hk, pow_zero]
        · rw [h₂ (Nat.pos_of_ne_zero hk), ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk)]
      refine ⟨fun l hl => ?_, fun _ => ?_⟩
      · dsimp only
        rw [hc]
        by_cases hlk : l = k
        · rw [hlk, Function.update_self]
        · rw [Function.update_of_ne hlk]
          exact h₁ l (by have : (l : ℕ) ≠ k := fun h => hlk (Fin.ext h); omega)
      · dsimp only
        rw [hc, Nat.add_sub_cancel])
  funext l
  rw [fftTwiddles, Id.run_bind, Id.run_pure, List.idRun_foldlM]
  exact key.1 l l.isLt

/-- **Algorithm 1.4.1 computes `y = F_n x`**: by induction on `t`, `F_1 x = x` and the radix-2
splitting of `F_{2m}`. -/
theorem algorithm_1_4_1_spec :
    ∀ (t : ℕ) (x : Fin (2 ^ t) → ℂ), Id.run (algorithm_1_4_1 pure t x) = fourierMatrix (2 ^ t) *ᵥ x
  | 0, x => by
    have h : fourierMatrix (2 ^ 0) = 1 := fourierMatrix_one
    rw [algorithm_1_4_1, Id.run_pure, h, one_mulVec]
  | t + 1, x => by
    simp only [algorithm_1_4_1, Id.run_bind, Id.run_pure, algorithm_1_4_1_spec t, fftTwiddles_spec,
      vecPointwiseMul_spec, vecAdd_spec, vecSub_spec]
    funext i
    obtain ⟨k | k, rfl⟩ := (twoPowSplit t).surjective i
    · have hi : twoPowSplit t (.inl k) = ⟨k, by have := k.isLt; rw [pow_succ]; omega⟩ := by
        ext; simp [twoPowSplit]
      simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Pi.add_apply,
        Pi.mul_apply]
      rw [hi, (fourier_radix_two (pow_succ' 2 t) x k).1]
    · have hi : twoPowSplit t (.inr k) = ⟨k + 2 ^ t, by have := k.isLt; rw [pow_succ]; omega⟩ := by
        ext; simp [twoPowSplit]
      simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, Pi.sub_apply,
        Pi.mul_apply]
      rw [hi, (fourier_radix_two (pow_succ' 2 t) x k).2]

/-! ### Theorem 1.4.1: the block structure of `F_{2m}` -/

section Theorem141

variable (m : ℕ) [NeZero m]

/-- The rows and columns of the blocks of (1.4.7), 0-based: `0`, `1 : m − 1`, `m` and
`m + 1 : 2m − 1` of `Fin (2m)`. -/
def dftBlockIdx₀ : Fin 1 → Fin (2 * m) := fun _ => ⟨0, by have := NeZero.pos m; omega⟩

/-- The rows and columns `1 : m − 1` of `F_{2m}` (0-based), the book's `2 : m`. -/
def dftBlockIdx₁ : Fin (m - 1) → Fin (2 * m) := fun j => ⟨j + 1, by omega⟩

/-- The row and column `m` of `F_{2m}` (0-based), the book's `m + 1`. -/
def dftBlockIdx₂ : Fin 1 → Fin (2 * m) := fun _ => ⟨m, by have := NeZero.pos m; omega⟩

/-- The rows and columns `m + 1 : 2m − 1` of `F_{2m}` (0-based), the book's `m + 2 : 2m`. -/
def dftBlockIdx₃ : Fin (m - 1) → Fin (2 * m) := fun j => ⟨m + 1 + j, by omega⟩

/-- The book's `C_{m−1}` of (1.4.6) as a complex matrix. -/
noncomputable abbrev cosMatrixC : Matrix (Fin (m - 1)) (Fin (m - 1)) ℂ :=
  (cosMatrix (m - 1)).map (↑)

/-- The book's `S_{m−1}` of (1.4.6) as a complex matrix. -/
noncomputable abbrev dst1C : Matrix (Fin (m - 1)) (Fin (m - 1)) ℂ :=
  (dst1 (m - 1)).map (↑)

/-- The book's `v = (−1, 1, …, (−1)^{m−1})` of Theorem 1.4.1, 0-based `v_j = (−1)^{j+1}`. -/
abbrev altSignVec : Fin (m - 1) → ℂ := fun j => (-1) ^ ((j : ℕ) + 1)

omit [NeZero m] in
/-- An entry of `F_{2m}` as an exponential, `ω_{2m}^{ab} = exp(−(abπ/m) i)`. -/
private theorem fourierMatrix_two_mul_apply' (hm : 0 < m) {a b : ℕ} (ha : a < 2 * m)
    (hb : b < 2 * m) :
    fourierMatrix (2 * m) ⟨a, ha⟩ ⟨b, hb⟩ = Complex.exp (-((a : ℂ) * b * π / m) * I) := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [fourierMatrix_apply, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- `cos θ + i sin θ = exp(θ i)`, the entries of `C + iS`. -/
private theorem cos_add_I_mul_sin (θ : ℝ) :
    (Real.cos θ : ℂ) + I * (Real.sin θ : ℂ) = Complex.exp ((θ : ℂ) * I) := by
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

/-- `cos θ − i sin θ = exp(−θ i)`, the entries of `C − iS`. -/
private theorem cos_sub_I_mul_sin (θ : ℝ) :
    (Real.cos θ : ℂ) - I * (Real.sin θ : ℂ) = Complex.exp (-(θ : ℂ) * I) := by
  rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos,
    Complex.ofReal_sin]
  ring

/-- `(−1)^n = exp(nπ i)`. -/
private theorem neg_one_pow_eq_exp (n : ℕ) :
    ((-1 : ℂ)) ^ n = Complex.exp ((n : ℂ) * π * I) := by
  rw [show (n : ℂ) * π * I = n * (π * I) by ring, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- Two exponentials `exp(x i)`, `exp(y i)` whose arguments differ by `2πn` agree. -/
private theorem exp_mul_I_eq_of_eq_add {x y : ℂ} (n : ℤ) (h : x = y + n * (2 * π)) :
    Complex.exp (x * I) = Complex.exp (y * I) :=
  Complex.exp_eq_exp_iff_exists_int.2 ⟨n, by rw [h]; ring⟩

/-- **Theorem 1.4.1.** Let `m` be a positive integer, `eᵀ = (1, …, 1)` and
`vᵀ = (−1, 1, …, (−1)^{m−1})` of length `m − 1`, `E = ℰ_{m−1}`, `C = C_{m−1}` and `S = S_{m−1}`.
Then
```
         ⎡ 1   eᵀ          1        eᵀ         ⎤
F_{2m} = ⎢ e   C − iS      v        (C + iS)E  ⎥
         ⎢ 1   vᵀ          (−1)^m   vᵀE        ⎥
         ⎣ e   E(C + iS)   Ev       E(C − iS)E ⎦
```
(1.4.7), stated block by block: the blocks sit at the 0-based rows and columns `0`, `1:m−1`, `m`,
`m+1:2m−1` of `F_{2m}` (`dftBlockIdx₀` … `dftBlockIdx₃`), and a `1 × 1` block `c`, a row `eᵀ`
or a column `e` is the constant matrix `of fun _ _ => c`. -/
theorem theorem_1_4_1 :
    let F := fourierMatrix (2 * m)
    let E : Matrix (Fin (m - 1)) (Fin (m - 1)) ℂ := exchange (m - 1)
    let C := cosMatrixC m
    let S := dst1C m
    let v := altSignVec m
    -- the first block row
    (F.submatrix (dftBlockIdx₀ m) (dftBlockIdx₀ m) = of fun _ _ => 1) ∧
    (F.submatrix (dftBlockIdx₀ m) (dftBlockIdx₁ m) = of fun _ _ => 1) ∧
    (F.submatrix (dftBlockIdx₀ m) (dftBlockIdx₂ m) = of fun _ _ => 1) ∧
    (F.submatrix (dftBlockIdx₀ m) (dftBlockIdx₃ m) = of fun _ _ => 1) ∧
    -- the second block row
    (F.submatrix (dftBlockIdx₁ m) (dftBlockIdx₀ m) = of fun _ _ => 1) ∧
    (F.submatrix (dftBlockIdx₁ m) (dftBlockIdx₁ m) = C - I • S) ∧
    (F.submatrix (dftBlockIdx₁ m) (dftBlockIdx₂ m) = of fun k _ => v k) ∧
    (F.submatrix (dftBlockIdx₁ m) (dftBlockIdx₃ m) = (C + I • S) * E) ∧
    -- the third block row
    (F.submatrix (dftBlockIdx₂ m) (dftBlockIdx₀ m) = of fun _ _ => 1) ∧
    (F.submatrix (dftBlockIdx₂ m) (dftBlockIdx₁ m) = of fun _ j => v j) ∧
    (F.submatrix (dftBlockIdx₂ m) (dftBlockIdx₂ m) = of fun _ _ => (-1) ^ m) ∧
    (F.submatrix (dftBlockIdx₂ m) (dftBlockIdx₃ m) = of fun _ j => (v ᵥ* E) j) ∧
    -- the fourth block row
    (F.submatrix (dftBlockIdx₃ m) (dftBlockIdx₀ m) = of fun _ _ => 1) ∧
    (F.submatrix (dftBlockIdx₃ m) (dftBlockIdx₁ m) = E * (C + I • S)) ∧
    (F.submatrix (dftBlockIdx₃ m) (dftBlockIdx₂ m) = of fun k _ => (E *ᵥ v) k) ∧
    (F.submatrix (dftBlockIdx₃ m) (dftBlockIdx₃ m) = E * (C - I • S) * E) := by
  intro F E C S v
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos m)).symm⟩
  have hF := @fourierMatrix_two_mul_apply' (m + 1) (Nat.succ_pos m)
  have hmC : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  -- the reversal `rev j = m − 1 − j` of `Fin m`, as a complex number
  have hrev : ∀ j : Fin (m + 1 - 1), ((Fin.rev j : ℕ) : ℂ) = m - 1 - (j : ℕ) := fun j => by
    have hj : (j : ℕ) < m := by have := j.isLt; omega
    rw [Fin.val_rev, show m + 1 - 1 - ((j : ℕ) + 1) = m - 1 - j by omega,
      Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  -- the entries of `C ± iS`
  have hCS : ∀ k j : Fin (m + 1 - 1), (C + I • S) k j =
      Complex.exp ((((k : ℕ) + 1 : ℂ) * ((j : ℕ) + 1) * π / (m + 1)) * I) := fun k j => by
    simp only [C, S, cosMatrixC, dst1C, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      cosMatrix_apply, dst1_apply, smul_eq_mul, Nat.add_sub_cancel]
    rw [cos_add_I_mul_sin]
    congr 2
    push_cast
    ring
  have hCS' : ∀ k j : Fin (m + 1 - 1), (C - I • S) k j =
      Complex.exp (-(((k : ℕ) + 1 : ℂ) * ((j : ℕ) + 1) * π / (m + 1)) * I) := fun k j => by
    simp only [C, S, cosMatrixC, dst1C, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
      cosMatrix_apply, dst1_apply, smul_eq_mul, Nat.add_sub_cancel]
    rw [cos_sub_I_mul_sin]
    congr 2
    push_cast
    ring
  have hv : ∀ j : Fin (m + 1 - 1), v j = Complex.exp ((((j : ℕ) : ℂ) + 1) * π * I) := fun j => by
    simp only [v, altSignVec]
    rw [neg_one_pow_eq_exp]
    push_cast
    ring
  -- every block, entry by entry, as an equality of exponentials
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext k j <;>
    simp only [F, E, submatrix_apply, of_apply, dftBlockIdx₀, dftBlockIdx₁, dftBlockIdx₂,
      dftBlockIdx₃, hF, mul_exchange_apply, exchange_mul_apply, vecMul_exchange_apply,
      exchange_mulVec_apply, hCS, hCS', hv, neg_one_pow_eq_exp]
  · simp
  · simp
  · simp
  · simp
  · simp
  · refine exp_mul_I_eq_of_eq_add 0 ?_
    push_cast
    ring
  · refine exp_mul_I_eq_of_eq_add (-((k : ℕ) + 1 : ℤ)) ?_
    push_cast
    field_simp
    ring
  · refine exp_mul_I_eq_of_eq_add (-((k : ℕ) + 1 : ℤ)) ?_
    rw [hrev]
    push_cast
    field_simp
    ring
  · simp
  · refine exp_mul_I_eq_of_eq_add (-((j : ℕ) + 1 : ℤ)) ?_
    push_cast
    field_simp
    ring
  · refine exp_mul_I_eq_of_eq_add (-((m : ℤ) + 1)) ?_
    push_cast
    field_simp
    ring
  · refine exp_mul_I_eq_of_eq_add (-((m : ℤ) + 1)) ?_
    rw [hrev]
    push_cast
    field_simp
    ring
  · simp
  · refine exp_mul_I_eq_of_eq_add (-((j : ℕ) + 1 : ℤ)) ?_
    rw [hrev]
    push_cast
    field_simp
    ring
  · refine exp_mul_I_eq_of_eq_add (-((m : ℤ) + 1)) ?_
    rw [hrev]
    push_cast
    field_simp
    ring
  · refine exp_mul_I_eq_of_eq_add (-(2 + (k : ℕ) + (j : ℕ) : ℤ)) ?_
    rw [hrev, hrev]
    push_cast
    field_simp
    ring

end Theorem141

/-! ### The sine and cosine transforms (1.4.3)–(1.4.11) -/

/-- **(1.4.3)**: the discrete sine transform of `x_1, …, x_{m−1}`,
`y_k = ∑_{j=1}^{m−1} sin(kjπ/m) x_j`, `k = 1 : m − 1` (0-based: `x j` is the book's `x_{j+1}`). -/
noncomputable def dstTransform (m : ℕ) (x : Fin (m - 1) → ℝ) : Fin (m - 1) → ℝ := fun k =>
  ∑ j : Fin (m - 1), Real.sin (((k : ℕ) + 1) * ((j : ℕ) + 1) * π / m) * x j

/-- **(1.4.4)**: the discrete cosine transform of `x_0, …, x_m`,
`y_k = x_0/2 + ∑_{j=1}^{m−1} cos(kjπ/m) x_j + (−1)^k x_m/2`, `k = 0 : m`, with the three terms as
printed (the middle sum over `j : Fin (m − 1)` shifted by one). -/
noncomputable def dctTransform (m : ℕ) (x : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ := fun k =>
  x 0 / 2 + ∑ j : Fin (m - 1), Real.cos ((k : ℕ) * ((j : ℕ) + 1) * π / m) * x ⟨j + 1, by omega⟩ +
    (-1) ^ (k : ℕ) * x (Fin.last m) / 2

/-- **(1.4.8)**: `DST(m − 1) = S_{m−1}`, the sine transform (1.4.3) is the matrix-vector product
with `S_{m−1}` of (1.4.6). -/
theorem equation_1_4_8 (m : ℕ) (x : Fin (m - 1) → ℝ) : dstTransform m x = dst1 (m - 1) *ᵥ x := by
  funext k
  have hm : 0 < m := by have := k.isLt; omega
  simp only [dstTransform, mulVec, dotProduct, dst1_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.cast_pred hm, sub_add_cancel]

/-- **(1.4.10)**: for `0 < m`, the cosine transform (1.4.4) is the matrix-vector product with
`DCT(m + 1) = [1/2, eᵀ, 1/2; e/2, C_{m−1}, v/2; 1/2, vᵀ, (−1)^m/2]` (the backbone's
`Matrix.dct1 m`, whose block form is its docstring). -/
theorem equation_1_4_10 {m : ℕ} (hm : 0 < m) (x : Fin (m + 1) → ℝ) :
    dctTransform m x = dct1 m *ᵥ x := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  funext k
  simp only [dctTransform, mulVec, dotProduct]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, add_assoc]
  congr 1
  · rw [dct1_apply, ite_eq_left (Or.inl (Fin.val_zero _))]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_mul, zero_div, Real.cos_zero, mul_one]
    ring
  congr 1
  · refine Fintype.sum_equiv (finCongr (Nat.add_sub_cancel m 1)) _ _ fun i => ?_
    have hi : (i : ℕ) < m := by have := i.isLt; omega
    have hv : ((((finCongr (Nat.add_sub_cancel m 1)) i).castSucc.succ : Fin (m + 2)) : ℕ) =
        i + 1 := by simp
    rw [dct1_apply, ite_eq_right (by rw [hv]; omega), one_mul, hv]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
  · rw [Fin.succ_last, dct1_apply, ite_eq_left (Or.inr (Fin.val_last _)), Fin.val_last]
    have hm' : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show ((k : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * π / ((m + 1 : ℕ) : ℝ) = (k : ℕ) * π by
      field_simp, Real.cos_nat_mul_pi]
    ring

/-! ### Algorithms 1.4.2 and 1.4.3: the DST and the DCT through the FFT -/

/-- `2^(t+1) = 2 ((2^t − 1) + 1)`: the order of `x_sin`. -/
private theorem two_pow_succ_eq (t : ℕ) : 2 ^ (t + 1) = 2 * (2 ^ t - 1 + 1) := by
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, pow_succ']

section Transforms

variable {M : Type → Type} [Monad M] (rnd : ℂ → M ℂ)

/-- **Algorithm 1.4.2** (DST through the FFT), for `m = 2^t`: "The following algorithm assigns the
DST of `x_1, …, x_{m−1}` to `y`":
```
Set up the vector x_sin defined by (1.4.9).
Use fft (e.g., Algorithm 1.4.1) to compute ỹ = F_{2m} x_sin
y = i · ỹ(2:m)/2
```
Setting up `x_sin` involves no arithmetic but negation. The output is complex: in floating point
`y` acquires an imaginary part. -/
noncomputable def algorithm_1_4_2 (t : ℕ) (x : Fin (2 ^ t - 1) → ℝ) :
    M (Fin (2 ^ t - 1) → ℂ) := do
  let xsin : Fin (2 ^ (t + 1)) → ℂ := fun l =>
    (oddExtensionVec x (Fin.cast (two_pow_succ_eq t) l) : ℂ)
  let yt ← algorithm_1_4_1 rnd (t + 1) xsin
  (List.finRange (2 ^ t - 1)).foldlM (fun (y : Fin (2 ^ t - 1) → ℂ) (k : Fin (2 ^ t - 1)) => do
    let v ← rnd (I * yt ⟨k + 1, by have := k.isLt; rw [two_pow_succ_eq]; omega⟩ / 2)
    pure (Function.update y k v)) (fun _ => 0)

/-- **Algorithm 1.4.3** (DCT through the FFT), for `m = 2^t`: "The following algorithm assigns to
`y ∈ ℝ^{m+1}` the DCT of `x_0, …, x_m`":
```
Set up the vector x_cos ∈ ℝ^{2m} defined by (1.4.11).
Use fft (e.g., Algorithm 1.4.1) to compute ỹ = F_{2m} x_cos
y = ỹ(1:m+1)/2
```
-/
noncomputable def algorithm_1_4_3 (t : ℕ) (x : Fin (2 ^ t + 1) → ℝ) :
    M (Fin (2 ^ t + 1) → ℂ) := do
  let xcos : Fin (2 ^ (t + 1)) → ℂ := fun l => (evenExtensionVec x (Fin.cast (pow_succ' 2 t) l) : ℂ)
  let yt ← algorithm_1_4_1 rnd (t + 1) xcos
  (List.finRange (2 ^ t + 1)).foldlM (fun (y : Fin (2 ^ t + 1) → ℂ) (k : Fin (2 ^ t + 1)) => do
    let v ← rnd (yt ⟨k, by
      have := k.isLt; have := Nat.one_le_two_pow (n := t); rw [pow_succ]; omega⟩ / 2)
    pure (Function.update y k v)) (fun _ => 0)

end Transforms

/-- **Algorithm 1.4.2 computes the DST**: its output is `DST(m − 1) x` of (1.4.3), `m = 2^t`. -/
theorem algorithm_1_4_2_spec (t : ℕ) (x : Fin (2 ^ t - 1) → ℝ) :
    Id.run (algorithm_1_4_2 pure t x) = fun k => (dstTransform (2 ^ t) x k : ℂ) := by
  simp only [algorithm_1_4_2, Id.run_bind, algorithm_1_4_1_spec]
  rw [idRun_foldlM_finRange_set]
  funext k
  rw [equation_1_4_8, dst1_mulVec_eq_dft]
  have h := fourierMatrix_mulVec_cast (two_pow_succ_eq t)
    (fun l => (oddExtensionVec x l : ℂ)) ⟨k + 1, by have := k.isLt; rw [two_pow_succ_eq]; omega⟩
  rw [show (fun l => (oddExtensionVec x (Fin.cast (two_pow_succ_eq t) l) : ℂ)) =
    (fun l => (oddExtensionVec x l : ℂ)) ∘ Fin.cast (two_pow_succ_eq t) from rfl, h, Fin.cast_mk,
    fourierMatrix]
  ring

/-- **Algorithm 1.4.3 computes the DCT**: its output is `DCT(m + 1) x` of (1.4.4), `m = 2^t`. -/
theorem algorithm_1_4_3_spec (t : ℕ) (x : Fin (2 ^ t + 1) → ℝ) :
    Id.run (algorithm_1_4_3 pure t x) = fun k => (dctTransform (2 ^ t) x k : ℂ) := by
  simp only [algorithm_1_4_3, Id.run_bind, algorithm_1_4_1_spec]
  rw [idRun_foldlM_finRange_set]
  funext k
  rw [equation_1_4_10 (Nat.two_pow_pos t), dct1_mulVec_eq_dft (Nat.two_pow_pos t)]
  have h := fourierMatrix_mulVec_cast (pow_succ' 2 t) (fun l => (evenExtensionVec x l : ℂ))
    ⟨k, by have := k.isLt; have := Nat.one_le_two_pow (n := t); rw [pow_succ]; omega⟩
  rw [show (fun l => (evenExtensionVec x (Fin.cast (pow_succ' 2 t) l) : ℂ)) =
    (fun l => (evenExtensionVec x l : ℂ)) ∘ Fin.cast (pow_succ' 2 t) from rfl, h, Fin.cast_mk,
    fourierMatrix]
  ring

/-! ### The Haar wavelet transform (§1.4.3) -/

/-- **§1.4.3**: the Haar wavelet transform matrix `W_n`, `n = 2^t`, defined recursively by
`W_1 = [1]` and `W_{2m} = [W_m ⊗ (1; 1) | I_m ⊗ (1; −1)]`. (The printed recursion lost its brackets
in conversion; `W_2` and `W_4` fix the meaning. The printed `W_8` has a garbled sixth row and is not
used as evidence.) Column `j < m` of `W_{2m}` is `W_m(⌊i/2⌋, j)`, column `m + j` is `(−1)^{i mod 2}`
where `⌊i/2⌋ = j` and `0` elsewhere (`haarMatrix_succ_apply`). -/
def haarMatrix : (t : ℕ) → Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℝ
  | 0 => 1
  | t + 1 => of fun i j => Sum.elim
      (fun j' : Fin (2 ^ t) => kroneckerFin (haarMatrix t) !![1; 1] (Fin.cast (pow_succ 2 t) i)
        (Fin.cast (Nat.mul_one _).symm j'))
      (fun j' : Fin (2 ^ t) => kroneckerFin (1 : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℝ) !![1; -1]
        (Fin.cast (pow_succ 2 t) i) (Fin.cast (Nat.mul_one _).symm j'))
      ((twoPowSplit t).symm j)

/-- Row `2i + a` of `W_{2m}` (0-based, `a ∈ {0, 1}`; the position `finProdFinEquiv (i, a)` of
`Fin (2^t * 2) = Fin (2^(t+1))`): `W_m(i, j)` in column `j < m`, and `(−1)^a δ_{ij}` in column
`m + j`. -/
theorem haarMatrix_succ_apply (t : ℕ) (i : Fin (2 ^ t)) (a : Fin 2) (j : Fin (2 ^ t)) :
    haarMatrix (t + 1) (Fin.cast (pow_succ 2 t).symm (finProdFinEquiv (i, a)))
        (twoPowSplit t (.inl j)) = haarMatrix t i j ∧
      haarMatrix (t + 1) (Fin.cast (pow_succ 2 t).symm (finProdFinEquiv (i, a)))
        (twoPowSplit t (.inr j)) = if i = j then (-1) ^ (a : ℕ) else 0 := by
  have hj : Fin.cast (Nat.mul_one (2 ^ t)).symm j = finProdFinEquiv (j, (0 : Fin 1)) := by
    ext; simp
  simp only [haarMatrix, of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, hj,
    Fin.cast_cast, Fin.cast_eq_self, kroneckerFin_apply, one_apply]
  obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  · constructor
    · simp
    · split_ifs <;> simp
  · constructor
    · simp
    · split_ifs <;> simp

/-- **(1.4.13)**: reordering the rows of `W_n`, `n = 2m`, so that the odd-indexed rows come first,
`𝒫_{2,m}ᵀ W_n = [W_m, I_m; W_m, −I_m] = (W_2 ⊗ I_m) [W_m, 0; 0, I_m]` with
`W_2 = [1, 1; 1, −1]`, the blocks sitting at the first and second halves of the rows (`rows`) and of
the columns (`twoPowSplit`). -/
theorem equation_1_4_13 (t : ℕ) :
    let W : Matrix (Fin (2 ^ t * 2)) (Fin (2 ^ (t + 1))) ℝ := haarMatrix (t + 1)
    let rows : Fin (2 * 2 ^ t) ≃ Fin (2 ^ t) ⊕ Fin (2 ^ t) :=
      (finCongr (two_mul _)).trans finSumFinEquiv.symm
    (perfectShuffle 2 (2 ^ t) : Matrix (Fin (2 ^ t * 2)) (Fin (2 * 2 ^ t)) ℝ)ᵀ * W =
        (fromBlocks (haarMatrix t) 1 (haarMatrix t) (-1)).submatrix rows (twoPowSplit t).symm ∧
      (perfectShuffle 2 (2 ^ t) : Matrix (Fin (2 ^ t * 2)) (Fin (2 * 2 ^ t)) ℝ)ᵀ * W =
        kroneckerFin !![1, 1; 1, -1] (1 : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℝ) *
          (fromBlocks (haarMatrix t) 0 0 1).submatrix rows (twoPowSplit t).symm := by
  intro W rows
  have hrows0 : ∀ i, rows (finProdFinEquiv ((0 : Fin 2), i)) = .inl i := fun i => by
    simp only [rows, Equiv.trans_apply]
    rw [Equiv.symm_apply_eq]
    ext
    rw [finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val, finSumFinEquiv_apply_left,
      Fin.val_castAdd, Fin.val_zero, mul_zero, add_zero]
  have hrows1 : ∀ i, rows (finProdFinEquiv ((1 : Fin 2), i)) = .inr i := fun i => by
    simp only [rows, Equiv.trans_apply]
    rw [Equiv.symm_apply_eq]
    ext
    rw [finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val, finSumFinEquiv_apply_right,
      Fin.val_natAdd, Fin.val_one, mul_one, add_comm]
  have hL : ∀ (a : Fin 2) (i : Fin (2 ^ t)) (c : Fin (2 ^ (t + 1))),
      ((perfectShuffle 2 (2 ^ t) : Matrix (Fin (2 ^ t * 2)) (Fin (2 * 2 ^ t)) ℝ)ᵀ * W)
        (finProdFinEquiv (a, i)) c =
          haarMatrix (t + 1) (Fin.cast (pow_succ 2 t).symm (finProdFinEquiv (i, a))) c := by
    intro a i c
    rw [transpose_perfectShuffle, perfectShuffle, PEquiv.toMatrix_toPEquiv_mul, submatrix_apply,
      finPerfectShuffle_symm, finPerfectShuffle_apply]
    rfl
  have h₁ : (perfectShuffle 2 (2 ^ t) : Matrix (Fin (2 ^ t * 2)) (Fin (2 * 2 ^ t)) ℝ)ᵀ * W =
      (fromBlocks (haarMatrix t) 1 (haarMatrix t) (-1)).submatrix rows (twoPowSplit t).symm := by
    ext r c
    obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective r
    obtain ⟨c | c, rfl⟩ := (twoPowSplit t).surjective c
    all_goals
      rw [hL, submatrix_apply, Equiv.symm_apply_apply]
      obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    · rw [(haarMatrix_succ_apply t i 0 c).1, hrows0, fromBlocks_apply₁₁]
    · rw [(haarMatrix_succ_apply t i 1 c).1, hrows1, fromBlocks_apply₂₁]
    · rw [(haarMatrix_succ_apply t i 0 c).2, hrows0, fromBlocks_apply₁₂, one_apply]
      simp
    · rw [(haarMatrix_succ_apply t i 1 c).2, hrows1, fromBlocks_apply₂₂, neg_apply, one_apply]
      split_ifs <;> simp
  have hK : kroneckerFin !![1, 1; 1, -1] (1 : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℝ) =
      (fromBlocks 1 1 1 (-1)).submatrix rows rows := by
    ext r s
    obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective r
    obtain ⟨⟨b, j⟩, rfl⟩ := finProdFinEquiv.surjective s
    rw [kroneckerFin_apply, submatrix_apply]
    obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    all_goals obtain rfl | rfl : b = 0 ∨ b = 1 := by fin_cases b <;> simp
    all_goals simp [hrows0, hrows1]
  refine ⟨h₁, h₁.trans ?_⟩
  rw [hK, submatrix_mul_equiv, fromBlocks_multiply]
  simp

/-- The row form of (1.4.13): `y(1:2:n) = W_m x_T + x_B`, `y(2:2:n) = W_m x_T − x_B` for
`y = W_n x`, `x_T = x(1:m)`, `x_B = x(m+1:n)`. -/
theorem haarMatrix_succ_mulVec (t : ℕ) (x : Fin (2 ^ (t + 1)) → ℝ) (i : Fin (2 ^ t)) (a : Fin 2) :
    (haarMatrix (t + 1) *ᵥ x) (Fin.cast (pow_succ 2 t).symm (finProdFinEquiv (i, a))) =
      (haarMatrix t *ᵥ fun l => x (twoPowSplit t (.inl l))) i +
        (-1) ^ (a : ℕ) * x (twoPowSplit t (.inr i)) := by
  rw [mulVec, dotProduct, ← (twoPowSplit t).sum_comp, Fintype.sum_sum_type]
  simp only [(haarMatrix_succ_apply t i a _).1, (haarMatrix_succ_apply t i a _).2, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

section Haar

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 1.4.4 (Haar Wavelet Transform).** "If `x ∈ ℝⁿ` and `n = 2^t`, then this algorithm
computes the Haar transform `y = W_n x`":
```
function y = fht(x, n)
    if n = 1
        y = x
    else
        m = n/2
        z = fht(x(1:m), m)
        y(1:2:n) = z + x(m+1:n)
        y(2:2:n) = z − x(m+1:n)
    end
```
(The book's `y(1:2:m)`, `y(2:2:m)` are misprints for `y(1:2:n)`, `y(2:2:n)`.) Position `2k + a`
of `y` is `finProdFinEquiv (k, a)` of `Fin (2^t * 2)`. -/
def algorithm_1_4_4 : (t : ℕ) → (Fin (2 ^ t) → ℝ) → M (Fin (2 ^ t) → ℝ)
  | 0, x => pure x
  | t + 1, x => do
    let z ← algorithm_1_4_4 t fun l => x (twoPowSplit t (.inl l))
    let yOdd ← vecAdd rnd z fun l => x (twoPowSplit t (.inr l))
    let yEven ← vecSub rnd z fun l => x (twoPowSplit t (.inr l))
    pure fun i =>
      let p := finProdFinEquiv.symm (Fin.cast (pow_succ 2 t) i)
      if (p.2 : ℕ) = 0 then yOdd p.1 else yEven p.1

end Haar

/-- **Algorithm 1.4.4 computes `y = W_n x`**: induction on `t` with the row form of (1.4.13). -/
theorem algorithm_1_4_4_spec :
    ∀ (t : ℕ) (x : Fin (2 ^ t) → ℝ), Id.run (algorithm_1_4_4 pure t x) = haarMatrix t *ᵥ x
  | 0, x => by rw [algorithm_1_4_4, Id.run_pure, haarMatrix, one_mulVec]
  | t + 1, x => by
    simp only [algorithm_1_4_4, Id.run_bind, Id.run_pure, algorithm_1_4_4_spec t, vecAdd_spec,
      vecSub_spec]
    funext r
    obtain ⟨⟨i, a⟩, hr⟩ := finProdFinEquiv.surjective (Fin.cast (pow_succ 2 t) r)
    have hr' : r = Fin.cast (pow_succ 2 t).symm (finProdFinEquiv (i, a)) := by
      rw [hr, Fin.cast_cast, Fin.cast_eq_self]
    subst hr'
    rw [haarMatrix_succ_mulVec]
    simp only [Fin.cast_cast, Fin.cast_eq_self, Equiv.symm_apply_apply, Pi.add_apply,
      Pi.sub_apply]
    obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    · simp
    · simp [sub_eq_add_neg]

end GolubVanLoan.Chapter01
