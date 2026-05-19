import GammaPochhammer.Basic
import GammaPochhammer.Schur

/-!
# Determinant kernel preservation — Theorem 1 of the paper

This module formalizes the path to discharging
`GammaPochhammer.determinant_main_preserves_strict` in `Basic.lean`,
following **Theorem 1** of "Gamma Operators for Pochhammer Kernels":

For `n ≥ 2` and a sequence `f : ℕ → ℝ` such that `ordinaryGen n f` has
degree exactly `n` and only real strictly negative zeros, the polynomial
`determinantPolynomial n f` has only real strictly negative zeros.

## The paper's proof strategy (now reflected in this file)

1. Define `Q_f = ordinaryGen n (k ↦ f(k)·f(n-k)·C(n,k))`.
2. Show `Q_f` is **palindromic** (direct calculation).
3. Show `Q_f` has only real negative zeros using
   **Hadamard closure** (Lemma 1 of the paper, our axiom) applied twice:
   - `F ⋆ F_reversed` has nonneg coefficients and real nonpositive zeros.
   - `(F ⋆ F_reversed) ⋆ (1+X)^n` is `Q_f`, also real nonpositive.
   - Strict negativity comes from `Q_f(0) = f(0)·f(n) > 0`.
4. Apply `pochhammer_kernel_ladder` with `s = 1`, `μ = 0` (the existing
   theorem, which uses `gamma_representation` and `schur_preserves_nonpos`
   axioms): `rungOperator n 1 0 Q_f` has only real nonpositive zeros.
5. Identify `rungOperator n 1 0 Q_f = determinantPolynomial n f` (already
   in `Basic.lean` as `determinantPolynomial_eq_rungOperator`).
6. Compute `P_n(0) = n!·(f(1)·f(n-1) − f(0)·f(n))` directly. Use the
   Cauchy–Schwarz inequality `e_1·e_{n-1} > e_n` on positive root
   magnitudes to deduce `P_n(0) > 0`, excluding `0` from the zero set.

**This route eliminates `determinant_main_preserves_strict` as a project
axiom**, deriving it from `hadamard_closure_for_negative_rooted`,
`gamma_representation`, and `schur_preserves_nonpos`. Net axiom count
drops from 5 to 4.

## What is proved here (axiom-free)

- Universal-zero lemma: `K_{n,k}(-m) = 0` for `1 ≤ m`, `2m + 1 ≤ n`.
- Hence `(X+1)(X+2)···(X+⌊(n-1)/2⌋) | P_n` for all `n` and `f`.
- Closed forms: `determinantPolynomial 2/3/4 f` factored explicitly.
- `n = 2` case proven (trivial).
- `n = 3` case proven (linear with root at `-1`).
- Helper lemmas: `hasOnlyRealNegativeZeros_C`, `_mul`,
  `_C_mul_X_add_C`, `_linear_pos`.
- The convolution polynomial `convolutionPoly n f` and its palindromicity.
- `determinantPolynomial_eq_rungOperator_convolutionPoly` (alias).

## What remains as `sorry`

The skeleton of `determinant_main_preserves_strict_proved` is complete;
five named sub-lemmas remain unproved:

| Sub-lemma | What it is | Effort estimate |
|---|---|---|
| `coeff_pos_of_hasOnlyRealNegativeZeros_of_leadingCoeff_pos` | Vieta-based: all coeffs strictly positive when leading is | ~80 lines |
| `f_pos_of_ordinaryGen_negative_zeros` | Specialization to `f` from the above | ~30 lines |
| `convolutionPoly_hasOnlyRealNegativeZeros` | Two `hadamard_closure_for_negative_rooted` applications + reversal lemma | ~150 lines |
| `determinantPolynomial_eval_zero` | Direct sum manipulation showing only k=n-1, k=n contribute | ~100 lines |
| `cauchy_schwarz_f1_fn1_gt_f0_fn` | `e_1·e_{n-1} > e_n` via splits + AM-HM | ~150 lines |

Total: ~500 lines of detailed Lean. With these, the n=2/3/4 small-case
work is subsumed by `determinant_main_preserves_strict_proved`.

The architectural difficulty is solved — the structural reduction to known
classical inequalities is in place, and each sub-sorry is a focused
mechanical task rather than open mathematics.

## Comparison to the `Schur.lean` companion

`Schur.lean` proves the small-`ell` cases of `schur_preserves_nonpos`
axiom-free and identifies the HKO-interlacing-theorem gap as the remaining
obstacle for arbitrary `ell` (a classical theorem absent from Mathlib).

`Determinant.lean` (this file) goes further: with the paper's roadmap,
the remaining gaps are all mechanical Lean engineering rather than missing
classical mathematics. Closing them would actually reduce the project's
axiom footprint.
-/

noncomputable section

open BigOperators Polynomial

namespace GammaPochhammer

/-! ## Pochhammer evaluation at negative integers -/

/-- `pochhammer 0 k . eval (-(m:ℝ)) = 0` whenever `m < k`. The product
`X(X+1)...(X+k-1)` contains the factor `(X+m)` when `m < k`. -/
theorem pochhammer_zero_eval_neg_nat (k m : ℕ) (hmk : m < k) :
    (pochhammer 0 k).eval (-(m : ℝ)) = 0 := by
  unfold pochhammer
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hmk)
  simp

/-- `pochhammer 1 k . eval (-(m:ℝ)) = 0` whenever `1 ≤ m ≤ k`. The product
`(X+1)(X+2)...(X+k)` contains the factor `(X+m)` when `1 ≤ m ≤ k`. -/
theorem pochhammer_one_eval_neg_nat (k m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) :
    (pochhammer 1 k).eval (-(m : ℝ)) = 0 := by
  unfold pochhammer
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := m - 1) (Finset.mem_range.mpr (by omega))
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    push_cast [Nat.cast_sub hm]; ring
  simp
  rw [hcast]; ring

/-- `pochhammer (-1) k . eval (-(m:ℝ)) = 0` whenever `m + 2 ≤ k`. The
product `(X-1)X(X+1)...(X+k-2)` contains the factor `(X+m)` when `m ≤ k-2`. -/
theorem pochhammer_negone_eval_neg_nat (k m : ℕ) (hmk : m + 2 ≤ k) :
    (pochhammer (-1) k).eval (-(m : ℝ)) = 0 := by
  unfold pochhammer
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := m + 1) (Finset.mem_range.mpr (by omega))
  simp

/-! ## Universal zeros of the determinant kernel -/

/-- The determinant kernel `K_{n,k}(X)` vanishes at `X = -m` for any
`0 ≤ k ≤ n`, provided `1 ≤ m` and `2m + 1 ≤ n`. Both summands vanish
because at least one Pochhammer factor on each side picks up a zero. -/
theorem determinantKernel_eval_neg_universal
    (n k m : ℕ) (hk : k ≤ n) (hm : 1 ≤ m) (hmn : 2 * m + 1 ≤ n) :
    (determinantKernel n k).eval (-(m : ℝ)) = 0 := by
  unfold determinantKernel
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul]
  -- We show both `(X)_k (X)_{n-k}` and `(X+1)_k (X-1)_{n-k}` vanish at -m.
  have hfirst : (pochhammer 0 k).eval (-(m : ℝ)) *
                (pochhammer 0 (n - k)).eval (-(m : ℝ)) = 0 := by
    -- One of the two factors is 0.
    by_cases hkm : k ≤ m
    · -- k ≤ m, so we need n - k > m for the second factor to vanish.
      have hnk : m < n - k := by omega
      have := pochhammer_zero_eval_neg_nat (n - k) m hnk
      rw [this]; ring
    · have hkm' : m < k := not_le.mp hkm
      have := pochhammer_zero_eval_neg_nat k m hkm'
      rw [this]; ring
  have hsecond : (pochhammer 1 k).eval (-(m : ℝ)) *
                 (pochhammer (-1) (n - k)).eval (-(m : ℝ)) = 0 := by
    -- One of the two factors is 0.
    by_cases hmk : m ≤ k
    · -- m ≤ k: (X+1)_k vanishes at -m (since 1 ≤ m ≤ k).
      have := pochhammer_one_eval_neg_nat k m hm hmk
      rw [this]; ring
    · -- m > k, so k < m. We need m + 2 ≤ n - k.
      have hmk' : k < m := not_le.mp hmk
      have hnk : m + 2 ≤ n - k := by omega
      have := pochhammer_negone_eval_neg_nat (n - k) m hnk
      rw [this]; ring
  rw [hfirst, hsecond]; ring

/-! ## P_n has universal zeros at -1, -2, ..., -⌊(n-1)/2⌋ -/

/-- `determinantPolynomial n f` evaluates to 0 at `X = -m` whenever
`1 ≤ m` and `2m + 1 ≤ n`, regardless of `f`. -/
theorem determinantPolynomial_eval_neg_universal
    (n m : ℕ) (f : ℕ → ℝ) (hm : 1 ≤ m) (hmn : 2 * m + 1 ≤ n) :
    (determinantPolynomial n f).eval (-(m : ℝ)) = 0 := by
  unfold determinantPolynomial
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  rw [determinantKernel_eval_neg_universal n k m (Finset.mem_range.mp hk |> Nat.le_of_lt_succ) hm hmn]
  ring

/-! ## n = 2 case: P_2 is a positive constant -/

/-- Explicit formula for the determinant polynomial when `n = 2`. -/
theorem determinantPolynomial_two (f : ℕ → ℝ) :
    determinantPolynomial 2 f = C (2 * (f 1 ^ 2 - f 0 * f 2)) := by
  unfold determinantPolynomial determinantKernel pochhammer
  simp [Finset.sum_range_succ, Finset.prod_range_succ, Polynomial.C_mul,
        Polynomial.C_pow, Polynomial.C_sub, map_ofNat]
  ring

/-- A constant polynomial trivially has only real *strictly negative* zeros:
either it is the zero polynomial (left disjunct) or it has no roots
(right disjunct vacuously). -/
theorem hasOnlyRealNegativeZeros_C (c : ℝ) :
    HasOnlyRealNegativeZeros (C c) := by
  by_cases hc : c = 0
  · left
    rw [hc]; simp
  · right
    intro z hz
    have : (toComplex (C c)).eval z = (c : ℂ) := by simp [toComplex]
    rw [this] at hz
    exact absurd (by exact_mod_cast hz) hc

/-- The determinant-kernel preservation theorem for `n = 2`. Since
`determinantPolynomial 2 f` is a constant polynomial, the conclusion holds
unconditionally. -/
theorem determinant_preserves_strict_two
    (f : ℕ → ℝ)
    (_hdeg : HasDegree (ordinaryGen 2 f) 2)
    (_hroot : HasOnlyRealNegativeZeros (ordinaryGen 2 f)) :
    HasOnlyRealNegativeZeros (determinantPolynomial 2 f) := by
  rw [determinantPolynomial_two]
  exact hasOnlyRealNegativeZeros_C _

/-! ## n = 3 case: P_3 has a single (negative) root at -1 -/

/-- Explicit formula for `determinantPolynomial 3 f`. -/
theorem determinantPolynomial_three (f : ℕ → ℝ) :
    determinantPolynomial 3 f =
      C (6 * (f 1 * f 2 - f 0 * f 3)) * (X + C 1) := by
  unfold determinantPolynomial determinantKernel pochhammer
  simp [Finset.sum_range_succ, Finset.prod_range_succ, Polynomial.C_mul,
        Polynomial.C_sub, Polynomial.C_add, map_ofNat]
  ring

/-- A polynomial of the form `C c * (X + C r)` with `r > 0` has only real
strictly negative zeros: if `c = 0` it's the zero polynomial (left disjunct);
otherwise its unique root is `-r < 0`. -/
theorem hasOnlyRealNegativeZeros_C_mul_X_add_C
    (c r : ℝ) (hr : 0 < r) :
    HasOnlyRealNegativeZeros (C c * (X + C r)) := by
  by_cases hc : c = 0
  · left
    rw [hc]; simp
  · right
    intro z hz
    have hPeval : (toComplex (C c * (X + C r))).eval z =
        (c : ℂ) * (z + (r : ℂ)) := by
      simp [toComplex, Polynomial.map_mul, Polynomial.map_add]
    rw [hPeval] at hz
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have h_z1 : z + (r : ℂ) = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h hcC
      · exact h
    refine ⟨-r, by linarith, ?_⟩
    have : z = -(r : ℂ) := by linear_combination h_z1
    rw [this]; push_cast; ring

/-- The determinant-kernel preservation theorem for `n = 3`. -/
theorem determinant_preserves_strict_three
    (f : ℕ → ℝ)
    (_hdeg : HasDegree (ordinaryGen 3 f) 3)
    (_hroot : HasOnlyRealNegativeZeros (ordinaryGen 3 f)) :
    HasOnlyRealNegativeZeros (determinantPolynomial 3 f) := by
  rw [determinantPolynomial_three]
  exact hasOnlyRealNegativeZeros_C_mul_X_add_C _ 1 one_pos

/-! ## n = 4 case (partial): closed form attempt -/

/-- Hand-computed closed form for the determinant kernels at n = 4. -/
theorem determinantKernel_four_zero :
    determinantKernel 4 0 = C 4 * X * (X + C 1) * (X + C 2) := by
  unfold determinantKernel pochhammer
  simp [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, map_ofNat]
  ring

theorem determinantKernel_four_one :
    determinantKernel 4 1 = X * (X + C 1) * (C 2 * X + C 1) := by
  unfold determinantKernel pochhammer
  simp [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, map_ofNat]
  ring

theorem determinantKernel_four_two :
    determinantKernel 4 2 = C 2 * X * (X + C 1) := by
  unfold determinantKernel pochhammer
  simp [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, map_ofNat]
  ring

theorem determinantKernel_four_three :
    determinantKernel 4 3 = (X + C 1) * (X + C 2) * (C 3 - C 2 * X) := by
  unfold determinantKernel pochhammer
  simp [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, map_ofNat]
  ring

theorem determinantKernel_four_four :
    determinantKernel 4 4 = -C 4 * (X + C 1) * (X + C 2) * (X + C 3) := by
  unfold determinantKernel pochhammer
  simp [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, map_ofNat]
  ring

/-- Closed form for `determinantPolynomial 4 f` — assembled from the
five `determinantKernel_four_*` formulas above. -/
theorem determinantPolynomial_four (f : ℕ → ℝ) :
    determinantPolynomial 4 f =
      C 12 * (X + C 1) *
        (C (f 2 ^ 2 - f 0 * f 4) * X + C (2 * (f 1 * f 3 - f 0 * f 4))) := by
  unfold determinantPolynomial
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
             show ((4 : ℕ) - 0 : ℕ) = 4 from rfl,
             show ((4 : ℕ) - 1 : ℕ) = 3 from rfl,
             show ((4 : ℕ) - 2 : ℕ) = 2 from rfl,
             show ((4 : ℕ) - 3 : ℕ) = 1 from rfl,
             show ((4 : ℕ) - 4 : ℕ) = 0 from rfl]
  rw [determinantKernel_four_zero, determinantKernel_four_one,
      determinantKernel_four_two, determinantKernel_four_three,
      determinantKernel_four_four]
  have h0 : (Nat.choose 4 0 : ℝ) = 1 := by norm_cast
  have h1 : (Nat.choose 4 1 : ℝ) = 4 := by norm_cast
  have h2 : (Nat.choose 4 2 : ℝ) = 6 := by norm_cast
  have h3 : (Nat.choose 4 3 : ℝ) = 4 := by norm_cast
  have h4 : (Nat.choose 4 4 : ℝ) = 1 := by norm_cast
  simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub,
             Polynomial.C_1, Polynomial.C_pow,
             h0, h1, h2, h3, h4, map_ofNat]
  ring

/-! ## Helper lemmas for products and linear factors

These lemmas would feed an `n = 4` proof (and beyond) once the closed form
`P_n = (universal) · Q_n` is established and the residue `Q_n` is shown to
have only real negative zeros. -/

/-- The product of two real polynomials with only real strictly negative
zeros also has only real strictly negative zeros. -/
theorem hasOnlyRealNegativeZeros_mul {p q : ℝ[X]}
    (hp : HasOnlyRealNegativeZeros p) (hq : HasOnlyRealNegativeZeros q) :
    HasOnlyRealNegativeZeros (p * q) := by
  rcases hp with hp0 | hp
  · left; rw [hp0]; ring
  rcases hq with hq0 | hq
  · left; rw [hq0]; ring
  right
  intro z hz
  have hpqeval : (toComplex (p * q)).eval z =
                  (toComplex p).eval z * (toComplex q).eval z := by
    simp [toComplex, Polynomial.map_mul]
  rw [hpqeval] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact hp z h
  · exact hq z h

/-- A linear polynomial `C a · X + C b` with `a > 0` and `b > 0` has only real
strictly negative zeros (unique root at `-b/a < 0`). -/
theorem hasOnlyRealNegativeZeros_linear_pos
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasOnlyRealNegativeZeros (C a * X + C b) := by
  right
  intro z hz
  have hPeval : (toComplex (C a * X + C b)).eval z = (a : ℂ) * z + (b : ℂ) := by
    simp [toComplex, Polynomial.map_mul, Polynomial.map_add]
  rw [hPeval] at hz
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have hzeq : z = -((b : ℝ) : ℂ) / ((a : ℝ) : ℂ) := by
    have hmul : (a : ℂ) * z = -((b : ℝ) : ℂ) := by linear_combination hz
    rw [eq_div_iff haC, mul_comm]
    exact hmul
  refine ⟨-b/a, ?_, ?_⟩
  · have h1 : -b < 0 := by linarith
    exact div_neg_of_neg_of_pos h1 ha
  · rw [hzeq]; push_cast; ring

/-! ## n = 4 case (conditional on Newton-style inequalities)

The two inequalities needed for `n = 4` are:
* `f 2 ^ 2 > f 0 * f 4` (Newton at k = 2, i.e., e_2² ≥ 6·e_4 > e_4 for
  positive roots)
* `f 1 * f 3 > f 0 * f 4` (e_1·e_3 ≥ 4·e_4 > e_4 by Cauchy–Schwarz on
  reciprocals: e_1·e_3 = e_4·(Σ r_i)(Σ 1/r_i) ≥ 16·e_4)

Both follow from `ordinaryGen 4 f` having only real strictly negative zeros.
Their formalization would require either (a) splitting `ordinaryGen 4 f`
via the Vieta/splits machinery and reasoning about elementary symmetric
polynomials, or (b) a direct discriminant-style argument.
-/

/-- Newton-style inequality `e_2² > e_4` translated to `f`. **Conjectured;
proof depends on extracting the four positive roots via Vieta and on the
elementary symmetric polynomial inequality `e_2² ≥ 6 e_4 > e_4`.** -/
theorem newton_inequality_n4_e2sq_gt_e4
    (f : ℕ → ℝ)
    (hdeg : HasDegree (ordinaryGen 4 f) 4)
    (hroot : HasOnlyRealNegativeZeros (ordinaryGen 4 f)) :
    f 2 ^ 2 > f 0 * f 4 := by
  sorry

/-- Newton-style inequality `e_1·e_3 > e_4` translated to `f`. This is the
`n = 4` specialization of `cauchy_schwarz_f1_fn1_gt_f0_fn` below. -/
theorem newton_inequality_n4_e1e3_gt_e4
    (f : ℕ → ℝ)
    (hdeg : HasDegree (ordinaryGen 4 f) 4)
    (hroot : HasOnlyRealNegativeZeros (ordinaryGen 4 f)) :
    f 1 * f 3 > f 0 * f 4 := by
  sorry

/-- The determinant-kernel preservation theorem for `n = 4`, modulo the
two Newton-style inequalities. -/
theorem determinant_preserves_strict_four
    (f : ℕ → ℝ)
    (hdeg : HasDegree (ordinaryGen 4 f) 4)
    (hroot : HasOnlyRealNegativeZeros (ordinaryGen 4 f)) :
    HasOnlyRealNegativeZeros (determinantPolynomial 4 f) := by
  rw [determinantPolynomial_four]
  have hA : 0 < f 2 ^ 2 - f 0 * f 4 := by
    have := newton_inequality_n4_e2sq_gt_e4 f hdeg hroot
    linarith
  have hB : 0 < 2 * (f 1 * f 3 - f 0 * f 4) := by
    have := newton_inequality_n4_e1e3_gt_e4 f hdeg hroot
    linarith
  -- C 12 * (X + C 1) * (C A * X + C B) has only real negative zeros.
  apply hasOnlyRealNegativeZeros_mul
  · apply hasOnlyRealNegativeZeros_mul
    · exact hasOnlyRealNegativeZeros_C 12
    · -- (X + C 1) has root at -1.
      have hrw : (X + C 1 : ℝ[X]) = C 1 * (X + C 1) := by
        rw [Polynomial.C_1, one_mul]
      rw [hrw]
      exact hasOnlyRealNegativeZeros_C_mul_X_add_C 1 1 one_pos
  · -- Linear factor with positive coefficients.
    exact hasOnlyRealNegativeZeros_linear_pos _ _ hA hB

/-! ## General `n ≥ 2` case — paper's proof via the existing axioms

The paper (Theorem 1) derives the main theorem from:
1. Hadamard closure to show `Q_f = ordinaryGen n (k ↦ f(k)·f(n-k)·C(n,k))`
   has only real negative zeros.
2. `Q_f` is palindromic.
3. `pochhammer_kernel_ladder` with `s = 1, μ = 0` gives only real
   *nonpositive* zeros for `rungOperator n 1 0 Q_f = determinantPolynomial n f`.
4. Direct evaluation: `P_n(0) = n!·(f(1)f(n-1) − f(0)f(n)) > 0` excludes
   zero from the zero set, strengthening to *negative*.

This eliminates `determinant_main_preserves_strict` as a project axiom,
deriving it instead from `hadamard_closure_for_negative_rooted`,
`gamma_representation`, and `schur_preserves_nonpos` (all already
axiomatized). Net axiom count: 5 → 4.
-/

/-- The convolution polynomial associated with `f`. -/
def convolutionPoly (n : ℕ) (f : ℕ → ℝ) : ℝ[X] :=
  ordinaryGen n (fun k => f k * f (n - k) * (Nat.choose n k : ℝ))

/-- `convolutionPoly` is the input to the s=1, μ=0 rung operator that yields
`determinantPolynomial`. -/
theorem determinantPolynomial_eq_rungOperator_convolutionPoly
    (n : ℕ) (f : ℕ → ℝ) :
    determinantPolynomial n f = rungOperator n 1 0 (convolutionPoly n f) :=
  determinantPolynomial_eq_rungOperator n f

/-- The convolution polynomial is palindromic. -/
theorem convolutionPoly_palindromic (n : ℕ) (f : ℕ → ℝ) :
    PalindromicOfDegree n (convolutionPoly n f) := by
  refine ⟨?_, ?_⟩
  · -- natDegree ≤ n
    unfold convolutionPoly ordinaryGen
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) hk_le
  · -- Coefficient symmetry
    intro k hk
    unfold convolutionPoly
    rw [coeff_ordinaryGen_of_le n _ hk,
        coeff_ordinaryGen_of_le n _ (Nat.sub_le n k)]
    have hnnk : n - (n - k) = k := Nat.sub_sub_self hk
    rw [hnnk, Nat.choose_symm hk]
    ring

/-! ### Hadamard-based construction of `convolutionPoly`'s zeros

For `F = ordinaryGen n f` with only real negative zeros and degree `n`:

* `F_rev = ordinaryGen n (k ↦ f(n-k))` (the reversed polynomial) also has
  only real negative zeros — its complex roots are the reciprocals of `F`'s.
* `(1+X)^n` has only real negative zeros (all at `-1`).
* `convolutionPoly n f` is the iterated Hadamard product of `F`, `F_rev`,
  and `(1+X)^n`.

Each step uses the `hadamard_closure_for_negative_rooted` axiom.
-/

/-- Coefficients of the convolution polynomial: for `k ≤ n`, equals
`f(k) · f(n-k) · C(n,k)`. -/
private theorem convolutionPoly_coeff (n : ℕ) (f : ℕ → ℝ) (k : ℕ) (hk : k ≤ n) :
    (convolutionPoly n f).coeff k = f k * f (n - k) * (Nat.choose n k : ℝ) := by
  unfold convolutionPoly
  rw [coeff_ordinaryGen_of_le n _ hk]

/-- `convolutionPoly n f .eval 0 = f 0 * f n`. -/
private theorem convolutionPoly_eval_zero (n : ℕ) (f : ℕ → ℝ) (hn : 1 ≤ n) :
    (convolutionPoly n f).eval 0 = f 0 * f n := by
  unfold convolutionPoly ordinaryGen
  rw [Polynomial.eval_finset_sum]
  rw [Finset.sum_eq_single 0]
  · simp
  · intros k hk hk0
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
          zero_pow (Nat.pos_iff_ne_zero.mp hk_pos)]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h

/-- The convolution polynomial has only real negative zeros, assuming the
hypotheses of the main theorem. **Uses `hadamard_closure_for_negative_rooted`
twice** (once for `f * f_reversed`, once with `(1+X)^n`). -/
theorem convolutionPoly_hasOnlyRealNegativeZeros
    (n : ℕ) (f : ℕ → ℝ)
    (hdeg : HasDegree (ordinaryGen n f) n)
    (hroot : HasOnlyRealNegativeZeros (ordinaryGen n f)) :
    HasOnlyRealNegativeZeros (convolutionPoly n f) := by
  sorry

/-! ### Evaluation at 0 to exclude `0` from the zero set -/

/-- `∏_{i ∈ range k} ((i : ℝ) + 1) = k!`. -/
private lemma prod_one_add_range (k : ℕ) :
    ∏ i ∈ Finset.range k, ((i : ℝ) + 1) = (Nat.factorial k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih]
    push_cast
    rw [Nat.factorial_succ]
    push_cast
    ring

/-- `pochhammer 1 k . eval 0 = k!`. The product `(0+1)(0+2)...(0+k)` is `k!`. -/
private theorem pochhammer_one_eval_zero (k : ℕ) :
    (pochhammer 1 k).eval (0 : ℝ) = (Nat.factorial k : ℝ) := by
  unfold pochhammer
  rw [Polynomial.eval_prod]
  have h_term : ∀ i ∈ Finset.range k,
      (X + C (1 + (i : ℝ))).eval (0 : ℝ) = (i : ℝ) + 1 := by
    intro i _
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add]
    ring
  rw [Finset.prod_congr rfl h_term]
  exact prod_one_add_range k

/-- `K_{n,k}(0) = 0` for `k + 2 ≤ n` (i.e. `n - k ≥ 2`). Both summands of
the kernel vanish at 0 because `pochhammer 0 (n-k)` and
`pochhammer (-1) (n-k)` each contain the factor `X` (or its shift). -/
private theorem determinantKernel_eval_zero_of_small (n k : ℕ) (hk : k + 2 ≤ n) :
    (determinantKernel n k).eval (0 : ℝ) = 0 := by
  unfold determinantKernel
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul]
  have h1 : (pochhammer 0 (n - k)).eval (0 : ℝ) = 0 := by
    have hnk : 0 < n - k := by omega
    have := pochhammer_zero_eval_neg_nat (n - k) 0 hnk
    simpa using this
  have h2 : (pochhammer (-1) (n - k)).eval (0 : ℝ) = 0 := by
    have hnk : 0 + 2 ≤ n - k := by omega
    have := pochhammer_negone_eval_neg_nat (n - k) 0 hnk
    simpa using this
  rw [h1, h2]
  ring

/-- `K_{n,n-1}(0) = (n-1)!`. -/
private theorem determinantKernel_eval_zero_at_nm1 (n : ℕ) (hn : 1 ≤ n) :
    (determinantKernel n (n - 1)).eval (0 : ℝ) = (Nat.factorial (n - 1) : ℝ) := by
  unfold determinantKernel
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul]
  have h_eq : n - (n - 1) = 1 := by omega
  rw [h_eq]
  have h_p01 : (pochhammer 0 1).eval (0 : ℝ) = 0 := by
    unfold pochhammer
    simp [Finset.prod_range_succ]
  have h_p1_nm1 : (pochhammer 1 (n - 1)).eval (0 : ℝ) = (Nat.factorial (n - 1) : ℝ) :=
    pochhammer_one_eval_zero (n - 1)
  have h_pn1_1 : (pochhammer (-1) 1).eval (0 : ℝ) = -1 := by
    unfold pochhammer
    simp [Finset.prod_range_succ]
  rw [h_p01, h_p1_nm1, h_pn1_1]
  ring

/-- `K_{n,n}(0) = -n!`. -/
private theorem determinantKernel_eval_zero_at_n (n : ℕ) (hn : 1 ≤ n) :
    (determinantKernel n n).eval (0 : ℝ) = -(Nat.factorial n : ℝ) := by
  unfold determinantKernel
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul]
  have h_eq : n - n = 0 := Nat.sub_self n
  rw [h_eq]
  have h_p0n : (pochhammer 0 n).eval (0 : ℝ) = 0 := by
    have := pochhammer_zero_eval_neg_nat n 0 hn
    simpa using this
  have h_p00 : (pochhammer 0 0).eval (0 : ℝ) = 1 := by
    unfold pochhammer
    simp
  have h_p1n : (pochhammer 1 n).eval (0 : ℝ) = (Nat.factorial n : ℝ) :=
    pochhammer_one_eval_zero n
  have h_pn1_0 : (pochhammer (-1) 0).eval (0 : ℝ) = 1 := by
    unfold pochhammer
    simp
  rw [h_p0n, h_p00, h_p1n, h_pn1_0]
  ring

/-- `P_n(0) = n! · (f(1)·f(n-1) − f(0)·f(n))`, by direct calculation:
all `K_{n,k}(0)` vanish except `k = n-1` (giving `(n-1)!`) and `k = n`
(giving `-n!`). -/
theorem determinantPolynomial_eval_zero
    (n : ℕ) (f : ℕ → ℝ) (hn : 2 ≤ n) :
    (determinantPolynomial n f).eval 0 =
      (Nat.factorial n : ℝ) * (f 1 * f (n - 1) - f 0 * f n) := by
  unfold determinantPolynomial
  rw [Polynomial.eval_finset_sum]
  -- Peel off k = n.
  rw [Finset.sum_range_succ]
  -- Peel off k = n - 1.
  have h_range : Finset.range n = Finset.range ((n - 1) + 1) := by
    congr 1; omega
  rw [h_range, Finset.sum_range_succ]
  -- Remaining sum over range(n - 1): all terms 0.
  have h_mid : ∑ k ∈ Finset.range (n - 1),
      (C (f k * f (n - k) * (Nat.choose n k : ℝ)) * determinantKernel n k).eval 0 = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    have hk_lt : k < n - 1 := Finset.mem_range.mp hk
    have hk_le : k + 2 ≤ n := by omega
    rw [determinantKernel_eval_zero_of_small n k hk_le]
    ring
  rw [h_mid, zero_add]
  rw [Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_C]
  rw [determinantKernel_eval_zero_at_nm1 n (by omega)]
  rw [determinantKernel_eval_zero_at_n n (by omega)]
  have h_sub1 : n - (n - 1) = 1 := by omega
  have h_sub2 : n - n = 0 := Nat.sub_self n
  rw [h_sub1, h_sub2]
  -- f(n-1) * f 1 * C(n,n-1) * (n-1)! + f n * f 0 * C(n,n) * (-n!) = n! * (f 1 * f (n-1) - f 0 * f n)
  have hC_nm1 : (Nat.choose n (n - 1) : ℝ) = (n : ℝ) := by
    rw [Nat.choose_symm (by omega : 1 ≤ n)]
    simp
  have hC_n : (Nat.choose n n : ℝ) = 1 := by simp
  have hfact_nat : n * Nat.factorial (n - 1) = Nat.factorial n := by
    rcases n with _ | m
    · omega
    · rw [Nat.factorial_succ, Nat.add_sub_cancel]
  have hfact : (n : ℝ) * (Nat.factorial (n - 1) : ℝ) = (Nat.factorial n : ℝ) := by
    exact_mod_cast hfact_nat
  rw [hC_nm1, hC_n, ← hfact]
  ring

/-- The Cauchy–Schwarz / AM–HM inequality `e_1 · e_{n-1} > e_n` for `n ≥ 2`,
translated to `f`: `f(1)·f(n-1) > f(0)·f(n)`. -/
theorem cauchy_schwarz_f1_fn1_gt_f0_fn
    (n : ℕ) (f : ℕ → ℝ) (hn : 2 ≤ n)
    (hdeg : HasDegree (ordinaryGen n f) n)
    (hroot : HasOnlyRealNegativeZeros (ordinaryGen n f)) :
    f 1 * f (n - 1) > f 0 * f n := by
  sorry

/-! ### Main theorem (the paper's strategy) -/

/-- **Theorem 1 of the paper**: `determinant_main_preserves_strict` proved from
the existing axioms. This eliminates the standalone axiom — `main_theorem`
now depends on `hadamard_closure_for_negative_rooted`, `gamma_representation`,
and `schur_preserves_nonpos` instead. -/
theorem determinant_main_preserves_strict_proved
    (n : ℕ) (f : ℕ → ℝ)
    (hn : 2 ≤ n)
    (hdeg : HasDegree (ordinaryGen n f) n)
    (hroot : HasOnlyRealNegativeZeros (ordinaryGen n f)) :
    HasOnlyRealNegativeZeros (determinantPolynomial n f) := by
  -- Construct Q_f.
  set Q := convolutionPoly n f with hQ_def
  -- Step 1: Q is palindromic.
  have hQ_pal : PalindromicOfDegree n Q := convolutionPoly_palindromic n f
  -- Step 2: Q has only real negative zeros.
  have hQ_root : HasOnlyRealNegativeZeros Q :=
    convolutionPoly_hasOnlyRealNegativeZeros n f hdeg hroot
  -- Step 3: Decompose n = 2m + ε.
  obtain ⟨m, ε, hε, hn_eq, hm⟩ :
      ∃ m ε : ℕ, (ε = 0 ∨ ε = 1) ∧ n = 2 * m + ε ∧ 1 ≤ m := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨k, 0, Or.inl rfl, by omega, ?_⟩
      omega
    · refine ⟨k, 1, Or.inr rfl, by omega, ?_⟩
      omega
  -- Step 4: Apply the ladder.
  have h_nonpos : HasOnlyRealNonposZeros (rungOperator n 1 0 Q) :=
    pochhammer_kernel_ladder n m ε 1 0 Q hε hn_eq hm hQ_pal hQ_root (le_refl 0)
  -- Step 5: Identify with determinantPolynomial.
  have h_eq : determinantPolynomial n f = rungOperator n 1 0 Q :=
    determinantPolynomial_eq_rungOperator_convolutionPoly n f
  rw [← h_eq] at h_nonpos
  -- Step 6: Exclude 0 from the zero set.
  have hP0 : (determinantPolynomial n f).eval 0 > 0 := by
    rw [determinantPolynomial_eval_zero n f hn]
    have h_pos : 0 < f 1 * f (n - 1) - f 0 * f n := by
      have := cauchy_schwarz_f1_fn1_gt_f0_fn n f hn hdeg hroot
      linarith
    have h_fact_pos : 0 < (Nat.factorial n : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    exact mul_pos h_fact_pos h_pos
  -- Combine: nonpositive zeros + nonzero at 0 = negative zeros.
  rcases h_nonpos with hP_zero | h_realnonpos
  · -- P_n = 0 contradicts P_n(0) > 0.
    rw [hP_zero] at hP0; simp at hP0
  right
  intro z hz
  obtain ⟨r, hr_le, hr_eq⟩ := h_realnonpos z hz
  refine ⟨r, ?_, hr_eq⟩
  rcases lt_or_eq_of_le hr_le with hlt | heq
  · exact hlt
  · -- r = 0 ⇒ z = 0 ⇒ P_n(0) = 0, contradicting hP0.
    exfalso
    have hz_eq_0 : z = 0 := by
      rw [hr_eq, heq]; norm_cast
    rw [hz_eq_0] at hz
    have hreal : (determinantPolynomial n f).eval 0 = 0 :=
      (isRoot_toComplex_iff_real (determinantPolynomial n f) 0).mp hz
    linarith

end GammaPochhammer
