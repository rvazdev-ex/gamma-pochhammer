import Mathlib

/-!
# Gamma operators for Pochhammer kernels

This file gives a Lean/mathlib formal interface for the results in the paper
"Gamma Operators for Pochhammer Kernels".

The polynomial kernels and transforms are defined concretely over `ℝ[X]`.
The assertions about real-rootedness are stated using complex roots of the
image of a real polynomial in `ℂ[X]`.

The current mathlib library does not provide the finite PF/ASW theorem, the
Schur-type transform theorem, or the interlacing/continuity proof package used
in the paper as ready-to-use lemmas.  Those ingredients, plus the long kernel
calculations, are isolated below as explicitly named axioms.  The public
theorems contain no proof placeholders.
-/

noncomputable section

open BigOperators Polynomial

namespace GammaPochhammer

/-! ## Root predicates -/

/-- The complexification of a real polynomial. -/
def toComplex (p : ℝ[X]) : ℂ[X] :=
  p.map (algebraMap ℝ ℂ)

/-- All complex roots of `p` are real and nonpositive. -/
def HasOnlyRealNonposZeros (p : ℝ[X]) : Prop :=
  p = 0 ∨ ∀ z : ℂ, (toComplex p).eval z = 0 → ∃ r : ℝ, r ≤ 0 ∧ z = (r : ℂ)

/-- All complex roots of `p` are real and negative. -/
def HasOnlyRealNegativeZeros (p : ℝ[X]) : Prop :=
  p = 0 ∨ ∀ z : ℂ, (toComplex p).eval z = 0 → ∃ r : ℝ, r < 0 ∧ z = (r : ℂ)

/-- Degree `n`, represented by `natDegree`.  This is meaningful together with
`p ≠ 0`, which is included in the definition. -/
def HasDegree (p : ℝ[X]) (n : ℕ) : Prop :=
  p ≠ 0 ∧ p.natDegree = n

/-! ## Basic polynomial constructions -/

/-- `(z+a)_k` as a polynomial in `z`. -/
def pochhammer (a : ℝ) (k : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range k, (X + C (a + (i : ℝ)))

/-- `(b*z+a)_k` as a polynomial in `z`. -/
def linearPochhammer (b a : ℝ) (k : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range k, (C b * X + C (a + (i : ℝ)))

theorem pochhammer_eq_ascPochhammer_comp (a : ℝ) (k : ℕ) :
    pochhammer a k = (ascPochhammer ℝ k).comp (X + C a) := by
  induction k with
  | zero =>
      simp [pochhammer]
  | succ k ih =>
      rw [pochhammer, Finset.prod_range_succ]
      change (pochhammer a k) * (X + C (a + (k : ℝ))) =
        (ascPochhammer ℝ (k + 1)).comp (X + C a)
      rw [ih, ascPochhammer_succ_right]
      simp [Polynomial.mul_comp, add_comm, add_left_comm]

theorem pochhammer_eval (a z : ℝ) (k : ℕ) :
    (pochhammer a k).eval z = (ascPochhammer ℝ k).eval (z + a) := by
  rw [pochhammer_eq_ascPochhammer_comp, eval_comp]
  simp

theorem linearPochhammer_eval (b a z : ℝ) (k : ℕ) :
    (linearPochhammer b a k).eval z = (ascPochhammer ℝ k).eval (b * z + a) := by
  induction k with
  | zero =>
      simp [linearPochhammer]
  | succ k ih =>
      rw [linearPochhammer, Finset.prod_range_succ, ascPochhammer_succ_right]
      have hprod :
          eval z (∏ x ∈ Finset.range k, (C b * X + C (a + ↑x))) =
            eval (b * z + a) (ascPochhammer ℝ k) := by
        simpa [linearPochhammer] using ih
      simp only [eval_mul, eval_add, eval_C, eval_X]
      rw [hprod]
      simp only [eval_natCast]
      ring

theorem ascPochhammer_eval_eq_prod_range_real (x : ℝ) (k : ℕ) :
    (ascPochhammer ℝ k).eval x = ∏ i ∈ Finset.range k, (x + (i : ℝ)) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [ascPochhammer_succ_right, Finset.prod_range_succ]
      simp [eval_mul, eval_add, ih]

/-- Ordinary generating polynomial of a finite sequence. -/
def ordinaryGen (n : ℕ) (f : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (f k) * X ^ k

theorem coeff_ordinaryGen_of_le (n : ℕ) (f : ℕ → ℝ) {k : ℕ} (hk : k ≤ n) :
    (ordinaryGen n f).coeff k = f k := by
  rw [ordinaryGen, finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b hb hbk
    simp [hbk.symm]
  · intro hknot
    exact False.elim (hknot (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))

theorem coeff_ordinaryGen_of_gt (n : ℕ) (f : ℕ → ℝ) {k : ℕ} (hk : n < k) :
    (ordinaryGen n f).coeff k = 0 := by
  rw [ordinaryGen, finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro b hb
  have hbk : b ≠ k := by
    intro h
    have hb_le : b ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    omega
  simp [hbk.symm]

/-- Hadamard product truncated to degree `n`. -/
def hadamard (n : ℕ) (A B : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (A.coeff k * B.coeff k) * X ^ k

/-- Palindromic with respect to degree `n`. -/
def PalindromicOfDegree (n : ℕ) (Q : ℝ[X]) : Prop :=
  Q.natDegree ≤ n ∧ ∀ k ≤ n, Q.coeff k = Q.coeff (n - k)

/-- The `γ`-basis polynomial `x^j (1+x)^(n-2j)`. -/
def gammaBasis (n j : ℕ) : ℝ[X] :=
  X ^ j * (1 + X) ^ (n - 2 * j)

/-- A `γ`-expansion of `Q` of length `m+1`. -/
def IsGammaExpansion (n m : ℕ) (Q : ℝ[X]) (γ : ℕ → ℝ) : Prop :=
  Q = ∑ j ∈ Finset.range (m + 1), C (γ j) * gammaBasis n j

/-- The `γ`-polynomial attached to a sequence of `γ`-coefficients. -/
def gammaPolynomial (m : ℕ) (γ : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (m + 1), C (γ j) * X ^ j

theorem coeff_gammaBasis (n j k : ℕ) :
    (gammaBasis n j).coeff k =
      if j ≤ k then (Nat.choose (n - 2 * j) (k - j) : ℝ) else 0 := by
  simp [gammaBasis, Polynomial.coeff_X_pow_mul', Polynomial.coeff_one_add_X_pow]

/-! ## Pochhammer determinant kernels -/

/-- The determinant kernel from the main theorem. -/
def determinantKernel (n k : ℕ) : ℝ[X] :=
  pochhammer 0 k * pochhammer 0 (n - k) -
    pochhammer 1 k * pochhammer (-1) (n - k)

/-- The polynomial `P_n` from the paper. -/
def determinantPolynomial (n : ℕ) (f : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (f k * f (n - k) * (Nat.choose n k : ℝ)) * determinantKernel n k

/-! ## Higher rung kernels -/

/-- The coefficients `λ_{s,q}`. -/
def lambda (s q : ℕ) : ℝ :=
  if q = 0 then ((Nat.factorial s : ℝ) ^ 2)⁻¹
  else 2 * (-1 : ℝ) ^ q *
    (((Nat.factorial (s - q) : ℝ) * (Nat.factorial (s + q) : ℝ))⁻¹)

/-- The unsigned A380113 triangle used by the normalized kernels. -/
def A380113 (s q : ℕ) : ℕ :=
  if s = 0 ∧ q = 0 then 1
  else if q = 0 then Nat.choose (2 * s) s / 2
  else Nat.choose (2 * s) (s - q)

/-- The `s`-th rung Pochhammer kernel `K_{n,k}^{[s,μ]}`. -/
def rungKernel (n k s : ℕ) (μ : ℝ) : ℝ[X] :=
  ∑ q ∈ Finset.range (s + 1),
    C (lambda s q) *
      (pochhammer (μ + q) k * pochhammer (μ - q) (n - k))

theorem rungKernel_eval (n k s : ℕ) (μ z : ℝ) :
    (rungKernel n k s μ).eval z =
      ∑ q ∈ Finset.range (s + 1),
        lambda s q *
          ((ascPochhammer ℝ k).eval (z + μ + q) *
            (ascPochhammer ℝ (n - k)).eval (z + μ - q)) := by
  simp [rungKernel, eval_finset_sum, eval_mul, pochhammer_eval, add_assoc, add_comm, add_left_comm,
    sub_eq_add_neg]

/-- The operator induced by the `s`-th rung kernel. -/
def rungOperator (n s : ℕ) (μ : ℝ) (Q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (Q.coeff k) * rungKernel n k s μ

theorem rungOperator_eval (n s : ℕ) (μ z : ℝ) (Q : ℝ[X]) :
    (rungOperator n s μ Q).eval z =
      ∑ k ∈ Finset.range (n + 1), Q.coeff k * (rungKernel n k s μ).eval z := by
  simp [rungOperator, eval_finset_sum, eval_mul]

theorem rungOperator_add (n s : ℕ) (μ : ℝ) (P Q : ℝ[X]) :
    rungOperator n s μ (P + Q) = rungOperator n s μ P + rungOperator n s μ Q := by
  simp [rungOperator, coeff_add, add_mul, Finset.sum_add_distrib]

theorem rungOperator_C_mul (n s : ℕ) (μ c : ℝ) (P : ℝ[X]) :
    rungOperator n s μ (C c * P) = C c * rungOperator n s μ P := by
  simp [rungOperator, coeff_C_mul, mul_assoc, Finset.mul_sum]

theorem rungOperator_sum {ι : Type*} (n s : ℕ) (μ : ℝ) (t : Finset ι) (P : ι → ℝ[X]) :
    rungOperator n s μ (∑ i ∈ t, P i) = ∑ i ∈ t, rungOperator n s μ (P i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [rungOperator]
  | insert a t hat ih =>
      simp [hat, Finset.sum_insert, rungOperator_add, ih]

theorem rungOperator_gammaExpansion
    (n m s : ℕ) (μ : ℝ) (Q : ℝ[X]) (γ : ℕ → ℝ)
    (hγ : IsGammaExpansion n m Q γ) :
    rungOperator n s μ Q =
      ∑ j ∈ Finset.range (m + 1), C (γ j) * rungOperator n s μ (gammaBasis n j) := by
  rw [hγ, rungOperator_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact rungOperator_C_mul n s μ (γ j) (gammaBasis n j)

/-- Schur-type transform `𝓛_{ℓ,α}`. -/
def schurTransform (ell : ℕ) (α : ℝ) (B : ℝ[X]) : ℝ[X] :=
  ∑ r ∈ Finset.range (ell + 1),
    C (B.coeff r) * pochhammer 0 r * pochhammer (r + α) (ell - r)

/-! ## Centered balanced two-product family -/

/-- Centered balanced two-product kernel `K_{n,k}^{a,c}`. -/
def centeredKernel (n k : ℕ) (a c : ℝ) : ℝ[X] :=
  pochhammer a k * pochhammer (-a) (n - k) -
    pochhammer c k * pochhammer (-c) (n - k)

/-- The operator attached to `centeredKernel`. -/
def centeredOperator (n : ℕ) (a c : ℝ) (Q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (Q.coeff k) * centeredKernel n k a c

/-- Universal admissibility on palindromic negative-rooted inputs. -/
def UniversallyAdmissibleCentered (a c : ℝ) : Prop :=
  ∀ n Q, PalindromicOfDegree n Q → HasOnlyRealNegativeZeros Q →
    HasOnlyRealNonposZeros (centeredOperator n a c Q)

theorem centeredKernel_zero_one (n k : ℕ) :
    centeredKernel n k 0 1 = determinantKernel n k := by
  simp [centeredKernel, determinantKernel]

/-! ## Explicit axiom boundary -/

axiom hadamard_closure_for_negative_rooted
    (n : ℕ) (A B : ℝ[X]) :
    (∀ k ≤ n, 0 ≤ A.coeff k) →
    (∀ k ≤ n, 0 ≤ B.coeff k) →
    HasOnlyRealNonposZeros A →
    HasOnlyRealNonposZeros B →
    HasOnlyRealNonposZeros (hadamard n A B)

axiom schur_preserves_nonpos
    (ell : ℕ) {α : ℝ} (hα : 0 < α) (B : ℝ[X]) :
    HasOnlyRealNonposZeros B →
    HasOnlyRealNonposZeros (schurTransform ell α B)

-- `gamma_representation` (Lemma 3 of the paper) is **no longer an axiom**.
-- It is now proved in `GammaPochhammer/GammaRep.lean` as
-- `GammaPochhammer.gamma_representation_proved`, and re-exported there as
-- `GammaPochhammer.gamma_representation`.  The five theorems that consumed
-- this axiom (`gamma_representation_of_palindromic_negative_rooted`,
-- `pochhammer_kernel_ladder`, `pochhammer_kernel_ladder_strict_shift`,
-- `original_kernel_palindromic`, `single_product_kernel`) live in
-- `GammaRep.lean` for the same reason.

private def risingProd (w : ℝ) (j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j, (w + (i : ℝ))

private def centralDifferenceLHS (s j : ℕ) (w : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (s + 1),
    lambda s q * (risingProd (w + q) j * risingProd (w - q) j)

private def centralDifferenceRHS (s j : ℕ) (w : ℝ) : ℝ :=
  (Nat.choose j s : ℝ) * risingProd w (j - s) * risingProd (w + s) (j - s)

private lemma lambda_mul_sq_sub_sq {s q : ℕ} (hs : 0 < s) (hq : q < s) :
    (((s : ℝ) ^ 2 - (q : ℝ) ^ 2) * lambda s q = lambda (s - 1) q) := by
  by_cases hq0 : q = 0
  · subst q
    simp [lambda]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (s - 1))]
    have hs' : s = (s - 1) + 1 := by omega
    rw [hs']
    simp [Nat.factorial_succ]
    ring
  · simp only [lambda, hq0, ↓reduceIte, mul_inv_rev]
    have hsq : s - q = (s - 1 - q) + 1 := by omega
    have hspq : s + q = (s - 1 + q) + 1 := by omega
    rw [hsq, hspq]
    simp [Nat.factorial_succ]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (s - 1 - q)),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (s - 1 + q)),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero ((s - 1 - q) + 1)),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero ((s - 1 + q) + 1))]
    have hqs : q ≤ s - 1 := by omega
    have hcast1 : ((s - 1 - q : ℕ) : ℝ) = (s : ℝ) - 1 - q := by
      rw [Nat.cast_sub hqs, Nat.cast_sub (Nat.succ_le_of_lt hs)]
      ring
    have hcast2 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hs)]
      norm_num
    rw [hcast1, hcast2]
    ring

private lemma lambda_mul_sq_sub_sq_self (s : ℕ) :
    (((s : ℝ) ^ 2 - (s : ℝ) ^ 2) * lambda s s = 0) := by
  ring

private lemma risingProd_succ (w : ℝ) (j : ℕ) :
    risingProd w (j + 1) = risingProd w j * (w + j) := by
  simp [risingProd, Finset.prod_range_succ, mul_comm]

private lemma risingProd_zero (w : ℝ) : risingProd w 0 = 1 := by
  simp [risingProd]

/-- `risingProd x (n+1) = x · risingProd (x+1) n`, peeling off the leading factor. -/
private lemma risingProd_succ_left (x : ℝ) (n : ℕ) :
    risingProd x (n + 1) = x * risingProd (x + 1) n := by
  simp only [risingProd]
  rw [Finset.prod_range_succ']
  have h1 : (∏ k ∈ Finset.range n, (x + ((k + 1 : ℕ) : ℝ))) =
            ∏ k ∈ Finset.range n, (x + 1 + (k : ℝ)) := by
    apply Finset.prod_congr rfl
    intro k _
    push_cast
    ring
  rw [h1]
  simp [mul_comm]

/-! Helpers for proving `central_difference_identity`. -/

private lemma alt_choose_two_mul_sum_zero {s : ℕ} (hs : 0 < s) :
    (∑ k ∈ Finset.range (2 * s + 1), (-1 : ℝ) ^ k * ((2 * s).choose k : ℝ)) = 0 := by
  have h := Int.alternating_sum_range_choose_of_ne (n := 2 * s) (by positivity)
  exact_mod_cast h

private lemma neg_one_pow_two_mul (n : ℕ) : (-1 : ℝ) ^ (2 * n) = 1 := by
  rw [pow_mul]; norm_num

private lemma neg_one_pow_sq (k : ℕ) : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
  rw [← pow_add, ← two_mul, neg_one_pow_two_mul]

private lemma neg_one_pow_two_mul_sub {k n : ℕ} (h : k ≤ 2 * n) :
    (-1 : ℝ) ^ (2 * n - k) = (-1 : ℝ) ^ k := by
  have key : (-1 : ℝ) ^ (2 * n - k) * (-1) ^ k = 1 := by
    rw [← pow_add, Nat.sub_add_cancel h, neg_one_pow_two_mul]
  have hne : (-1 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have eq : (-1 : ℝ) ^ (2 * n - k) * (-1) ^ k = (-1) ^ k * (-1) ^ k := by
    rw [key, neg_one_pow_sq]
  exact mul_right_cancel₀ hne eq

private lemma choose_mul_factorial_sq (s : ℕ) :
    ((2 * s).choose s : ℝ) * (Nat.factorial s : ℝ) * (Nat.factorial s : ℝ) =
      (Nat.factorial (2 * s) : ℝ) := by
  have hle : s ≤ 2 * s := by omega
  have h := Nat.choose_mul_factorial_mul_factorial hle
  have hsub : 2 * s - s = s := by omega
  rw [hsub] at h
  exact_mod_cast h

private lemma choose_mul_factorial_sub_add (s q : ℕ) (hq : q ≤ s) :
    ((2 * s).choose (s - q) : ℝ) *
        (Nat.factorial (s - q) : ℝ) * (Nat.factorial (s + q) : ℝ) =
      (Nat.factorial (2 * s) : ℝ) := by
  have hle : s - q ≤ 2 * s := by omega
  have h := Nat.choose_mul_factorial_mul_factorial hle
  have hsub : 2 * s - (s - q) = s + q := by omega
  rw [hsub] at h
  exact_mod_cast h

private lemma lambda_zero_mul_factorial (s : ℕ) :
    lambda s 0 * (Nat.factorial (2 * s) : ℝ) = ((2 * s).choose s : ℝ) := by
  have hne : (Nat.factorial s : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have key := choose_mul_factorial_sq s
  rw [lambda]
  simp only [↓reduceIte]
  rw [← key]
  field_simp

private lemma lambda_pos_mul_factorial {s q : ℕ} (hq : 0 < q) (hqs : q ≤ s) :
    lambda s q * (Nat.factorial (2 * s) : ℝ) =
      2 * (-1 : ℝ) ^ q * ((2 * s).choose (s - q) : ℝ) := by
  have hq0 : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  have hne1 : (Nat.factorial (s - q) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hne2 : (Nat.factorial (s + q) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have key := choose_mul_factorial_sub_add s q hqs
  rw [lambda]
  simp only [hq0, ↓reduceIte]
  rw [← key]
  field_simp

/-- Core identity: `(∑ q, λ(s,q)) · (2s)! · (-1)^s = ∑ k, (-1)^k · C(2s, k)`. -/
private lemma sum_lambda_key_identity (s : ℕ) :
    (∑ q ∈ Finset.range (s + 1), lambda s q) * (Nat.factorial (2 * s) : ℝ) *
        (-1 : ℝ) ^ s =
      ∑ k ∈ Finset.range (2 * s + 1), (-1 : ℝ) ^ k * ((2 * s).choose k : ℝ) := by
  -- Distribute the products into the sum.
  rw [Finset.sum_mul, Finset.sum_mul]
  -- Peel off q = 0 on the LHS.
  rw [show Finset.range (s + 1) = insert 0 (Finset.Ico 1 (s + 1)) by
        ext x; simp [Finset.mem_range, Finset.mem_Ico]; omega]
  rw [Finset.sum_insert (by simp [Finset.mem_Ico])]
  -- LHS = λ(s,0)·(2s)!·(-1)^s + ∑_{q ∈ Ico 1 (s+1)} λ(s,q)·(2s)!·(-1)^s.
  have hl0 :
      lambda s 0 * (Nat.factorial (2 * s) : ℝ) * (-1 : ℝ) ^ s =
        (-1 : ℝ) ^ s * ((2 * s).choose s : ℝ) := by
    rw [lambda_zero_mul_factorial]; ring
  rw [hl0]
  -- Rewrite each term of the q ∈ Ico 1 (s+1) sum.
  have hsumeq :
      ∀ q ∈ Finset.Ico 1 (s + 1),
        lambda s q * (Nat.factorial (2 * s) : ℝ) * (-1 : ℝ) ^ s =
          2 * (-1 : ℝ) ^ (s + q) * ((2 * s).choose (s - q) : ℝ) := by
    intro q hq
    rw [Finset.mem_Ico] at hq
    rw [lambda_pos_mul_factorial hq.1 (by omega)]
    rw [pow_add]; ring
  rw [Finset.sum_congr rfl hsumeq]
  -- Reindex q ↦ k = s + q : Ico 1 (s+1) ≃ Ico (s+1) (2s+1).
  have hreindex :
      ∑ q ∈ Finset.Ico 1 (s + 1),
          2 * (-1 : ℝ) ^ (s + q) * ((2 * s).choose (s - q) : ℝ) =
        ∑ k ∈ Finset.Ico (s + 1) (2 * s + 1),
          2 * (-1 : ℝ) ^ k * ((2 * s).choose k : ℝ) := by
    refine Finset.sum_nbij' (fun q => s + q) (fun k => k - s) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_Ico] at hq
      change s + q ∈ Finset.Ico (s + 1) (2 * s + 1)
      rw [Finset.mem_Ico]
      omega
    · intro k hk
      rw [Finset.mem_Ico] at hk
      change k - s ∈ Finset.Ico 1 (s + 1)
      rw [Finset.mem_Ico]
      omega
    · intro q hq
      rw [Finset.mem_Ico] at hq
      change s + q - s = q
      omega
    · intro k hk
      rw [Finset.mem_Ico] at hk
      change s + (k - s) = k
      omega
    · intro q hq
      rw [Finset.mem_Ico] at hq
      have hle : s + q ≤ 2 * s := by omega
      have hsubeq : 2 * s - (s + q) = s - q := by omega
      have hsym : ((2 * s).choose (s - q) : ℝ) = ((2 * s).choose (s + q) : ℝ) := by
        have := Nat.choose_symm hle
        rw [hsubeq] at this
        exact_mod_cast this
      rw [hsym]
  rw [hreindex]
  -- Now the LHS reads: (-1)^s · C(2s,s) + ∑_{k ∈ Ico (s+1) (2s+1)} 2 · (-1)^k · C(2s,k).
  -- Split the RHS: range (2s+1) = (range s ∪ {s}) ∪ Ico (s+1) (2s+1).
  have hset :
      Finset.range (2 * s + 1) =
        (Finset.range s ∪ ({s} : Finset ℕ)) ∪ Finset.Ico (s + 1) (2 * s + 1) := by
    ext x
    simp [Finset.mem_range, Finset.mem_Ico, Finset.mem_union]
    omega
  have hdisj1 :
      Disjoint (Finset.range s ∪ ({s} : Finset ℕ)) (Finset.Ico (s + 1) (2 * s + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_singleton] at hx
    rw [Finset.mem_Ico] at hx'
    omega
  have hdisj2 : Disjoint (Finset.range s) ({s} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right, Finset.mem_range]; omega
  rw [hset, Finset.sum_union hdisj1, Finset.sum_union hdisj2, Finset.sum_singleton]
  -- LHS: (-1)^s · C(2s,s) + ∑_{Ico (s+1) (2s+1)} 2 · (-1)^k · C(2s,k)
  -- RHS: (∑_{range s} (-1)^k · C(2s,k) + (-1)^s · C(2s,s)) +
  --      ∑_{Ico (s+1) (2s+1)} (-1)^k · C(2s,k)
  -- Reflection: ∑_{range s} (-1)^k · C(2s,k) = ∑_{Ico (s+1) (2s+1)} (-1)^k · C(2s,k).
  have hreflect :
      ∑ k ∈ Finset.range s, (-1 : ℝ) ^ k * ((2 * s).choose k : ℝ) =
        ∑ k ∈ Finset.Ico (s + 1) (2 * s + 1),
          (-1 : ℝ) ^ k * ((2 * s).choose k : ℝ) := by
    rw [Finset.range_eq_Ico]
    have hreflect_eq := Finset.sum_Ico_reflect
      (fun j => (-1 : ℝ) ^ j * ((2 * s).choose j : ℝ)) 0
      (show s ≤ 2 * s + 1 by omega)
    have h0 : 2 * s + 1 - 0 = 2 * s + 1 := by omega
    have hs1 : 2 * s + 1 - s = s + 1 := by omega
    rw [h0, hs1] at hreflect_eq
    rw [← hreflect_eq]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hle : j ≤ 2 * s := by omega
    change (-1 : ℝ) ^ j * ((2 * s).choose j : ℝ)
        = (-1 : ℝ) ^ (2 * s - j) * ((2 * s).choose (2 * s - j) : ℝ)
    rw [neg_one_pow_two_mul_sub hle]
    congr 1
    exact_mod_cast (Nat.choose_symm hle).symm
  rw [hreflect]
  -- Now both sides involve the same ∑_{Ico (s+1) (2s+1)} factor; the LHS has a factor of 2
  -- (from `2 * (-1)^k * C`) which exactly doubles the corresponding ∑ on the RHS.
  rw [show (∑ k ∈ Finset.Ico (s + 1) (2 * s + 1),
            2 * (-1 : ℝ) ^ k * ((2 * s).choose k : ℝ)) =
          (∑ k ∈ Finset.Ico (s + 1) (2 * s + 1),
            (-1 : ℝ) ^ k * ((2 * s).choose k : ℝ)) +
            ∑ k ∈ Finset.Ico (s + 1) (2 * s + 1),
              (-1 : ℝ) ^ k * ((2 * s).choose k : ℝ) from by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _; ring]
  ring

/-- The LHS recursion: `F(s, j+1) = ((w+j)² - s²) · F(s, j) + F(s-1, j)` for `s ≥ 1`. -/
private lemma centralDifferenceLHS_succ_j {s : ℕ} (hs : 0 < s) (j : ℕ) (w : ℝ) :
    centralDifferenceLHS s (j + 1) w =
      ((w + (j : ℝ)) ^ 2 - (s : ℝ) ^ 2) * centralDifferenceLHS s j w +
        centralDifferenceLHS (s - 1) j w := by
  simp only [centralDifferenceLHS, risingProd_succ]
  -- Reshape each summand to expose ((w+j)² - q²).
  have hreshape :
      ∀ q ∈ Finset.range (s + 1),
        lambda s q *
            (risingProd (w + ↑q) j * (w + ↑q + ↑j) *
              (risingProd (w - ↑q) j * (w - ↑q + ↑j))) =
          ((w + (j : ℝ)) ^ 2 - ((s : ℝ) ^ 2)) *
              (lambda s q * (risingProd (w + ↑q) j * risingProd (w - ↑q) j)) +
            ((s : ℝ) ^ 2 - (↑q : ℝ) ^ 2) * lambda s q *
              (risingProd (w + ↑q) j * risingProd (w - ↑q) j) := by
    intros; ring
  rw [Finset.sum_congr rfl hreshape]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  -- Now reduce ∑_{q ∈ range (s+1)} ((s² - q²) · λ(s, q)) · P+P- to F(s-1, j, w).
  rw [Finset.sum_range_succ]
  -- The q = s term vanishes by `(s² - s²) λ(s, s) = 0`.
  have hlast :
      ((s : ℝ) ^ 2 - (↑s : ℝ) ^ 2) * lambda s s *
          (risingProd (w + ↑s) j * risingProd (w - ↑s) j) = 0 := by
    have : ((s : ℝ) ^ 2 - (↑s : ℝ) ^ 2) = 0 := by ring
    rw [this, zero_mul, zero_mul]
  rw [hlast, add_zero]
  -- F(s-1, j, w) = ∑ q ∈ range ((s-1)+1), λ(s-1, q) · P+P- and (s-1)+1 = s.
  rw [show (s - 1) + 1 = s from by omega]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mem_range] at hq
  have h := lambda_mul_sq_sub_sq hs hq
  rw [← h]

private lemma sum_lambda_eq_zero {s : ℕ} (hs : 0 < s) :
    (∑ q ∈ Finset.range (s + 1), lambda s q) = 0 := by
  have hfact_ne : (Nat.factorial (2 * s) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hneg_ne : (-1 : ℝ) ^ s ≠ 0 := pow_ne_zero _ (by norm_num)
  have hkey := sum_lambda_key_identity s
  have halt : (∑ k ∈ Finset.range (2 * s + 1),
      (-1 : ℝ) ^ k * ((2 * s).choose k : ℝ)) = 0 := alt_choose_two_mul_sum_zero hs
  rw [halt] at hkey
  -- hkey : (∑ q, λ(s,q)) * (2s)! * (-1)^s = 0
  have : (∑ q ∈ Finset.range (s + 1), lambda s q) * (Nat.factorial (2 * s) : ℝ) = 0 := by
    have h := mul_eq_zero.mp hkey
    rcases h with h | h
    · exact h
    · exact absurd h hneg_ne
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h hfact_ne

/-- The RHS recursion: `G(s, j+1) = ((w+j)² - s²) · G(s, j) + G(s-1, j)` for `s ≥ 1`. -/
private lemma centralDifferenceRHS_succ_j {s : ℕ} (hs : 0 < s) (j : ℕ) (w : ℝ) :
    centralDifferenceRHS s (j + 1) w =
      ((w + (j : ℝ)) ^ 2 - (s : ℝ) ^ 2) * centralDifferenceRHS s j w +
        centralDifferenceRHS (s - 1) j w := by
  unfold centralDifferenceRHS
  by_cases hsj : s ≤ j
  · -- Case 1: s ≤ j (standard).
    have hj1s : j + 1 - s = (j - s) + 1 := by omega
    have hjsm1 : j - (s - 1) = (j - s) + 1 := by omega
    have hsm1_real : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hs.ne')]; simp
    have hjs_real : ((j - s : ℕ) : ℝ) = (j : ℝ) - (s : ℝ) := Nat.cast_sub hsj
    rw [hj1s, hjsm1]
    rw [risingProd_succ w (j - s), risingProd_succ (w + (s : ℝ)) (j - s)]
    rw [hsm1_real]
    rw [show (w + ((s : ℝ) - 1)) = w + (s : ℝ) - 1 from by ring]
    rw [risingProd_succ_left (w + (s : ℝ) - 1) (j - s)]
    rw [show (w + (s : ℝ) - 1 + 1) = w + (s : ℝ) from by ring]
    rw [hjs_real]
    -- Pascal: C(j+1, s) = C(j, s) + C(j, s-1)
    have hpascal : (((j + 1).choose s : ℕ) : ℝ) =
        ((j.choose s : ℕ) : ℝ) + ((j.choose (s - 1) : ℕ) : ℝ) := by
      have hss : s - 1 + 1 = s := by omega
      have h := Nat.choose_succ_succ j (s - 1)
      simp only [Nat.succ_eq_add_one] at h
      rw [hss] at h
      have h' : (j + 1).choose s = j.choose s + j.choose (s - 1) := by linarith
      exact_mod_cast h'
    -- Choose identity: s · C(j, s) = (j - s + 1) · C(j, s - 1).
    have hchoose : (s : ℝ) * (j.choose s : ℝ) =
        ((j : ℝ) - (s : ℝ) + 1) * (j.choose (s - 1) : ℝ) := by
      have h := Nat.choose_succ_right_eq j (s - 1)
      have hss : s - 1 + 1 = s := by omega
      rw [hss] at h
      have hcast : ((j - (s - 1) : ℕ) : ℝ) = (j : ℝ) - (s : ℝ) + 1 := by
        rw [show j - (s - 1) = j - s + 1 from by omega, Nat.cast_add, Nat.cast_one, hjs_real]
      have h' : (j.choose s : ℝ) * (s : ℝ) =
          (j.choose (s - 1) : ℝ) * ((j - (s - 1) : ℕ) : ℝ) := by exact_mod_cast h
      rw [hcast] at h'
      linarith
    linear_combination
      (risingProd w (j - s) * risingProd (w + (s : ℝ)) (j - s)) *
        (w + ((j : ℝ) - s)) * (w + (j : ℝ)) * hpascal -
      (risingProd w (j - s) * risingProd (w + (s : ℝ)) (j - s)) *
        (w + ((j : ℝ) - s)) * hchoose
  · -- Case 2: j < s.
    have hsj : j < s := Nat.lt_of_not_le hsj
    have hCjs : (j.choose s : ℝ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt hsj
    rcases Nat.eq_or_lt_of_le (show j ≤ s - 1 by omega) with hje | hje
    · -- Sub-case A: j = s - 1.
      have hj1s : j + 1 - s = 0 := by omega
      have hjsm1 : j - (s - 1) = 0 := by omega
      have hjs : j - s = 0 := by omega
      have hCj1s : (((j + 1).choose s : ℕ) : ℝ) = 1 := by
        have h : (j + 1).choose s = 1 := by
          rw [show j + 1 = s from by omega]; exact Nat.choose_self s
        exact_mod_cast h
      have hCjsm1 : ((j.choose (s - 1) : ℕ) : ℝ) = 1 := by
        have h : j.choose (s - 1) = 1 := by
          rw [hje]; exact Nat.choose_self (s - 1)
        exact_mod_cast h
      rw [hj1s, hjsm1, hjs]
      simp only [risingProd_zero]
      rw [hCj1s, hCjs, hCjsm1]
      ring
    · -- Sub-case B: j < s - 1, so j + 1 < s.
      have hj1s_lt : j + 1 < s := by omega
      have hCj1s : (((j + 1).choose s : ℕ) : ℝ) = 0 := by
        exact_mod_cast Nat.choose_eq_zero_of_lt hj1s_lt
      have hCjsm1 : ((j.choose (s - 1) : ℕ) : ℝ) = 0 := by
        exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : j < s - 1)
      rw [hCj1s, hCjs, hCjsm1]
      ring

/-- The central-difference identity, proved by simultaneous induction on `s` and `j`. -/
private lemma centralDifference_eq (s j : ℕ) (w : ℝ) :
    centralDifferenceLHS s j w = centralDifferenceRHS s j w := by
  induction s generalizing j w with
  | zero =>
    -- F(0, j, w) = λ(0, 0) · risingProd w j · risingProd w j = (w)_j²
    -- G(0, j, w) = C(j, 0) · risingProd w j · risingProd (w + 0) j = (w)_j²
    unfold centralDifferenceLHS centralDifferenceRHS
    have hl00 : lambda 0 0 = 1 := by simp [lambda]
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hl00]
    simp
  | succ s ih =>
    induction j with
    | zero =>
      unfold centralDifferenceLHS centralDifferenceRHS
      have hsum : ∀ q ∈ Finset.range (s + 1 + 1),
          lambda (s + 1) q * (risingProd (w + (q : ℝ)) 0 * risingProd (w - (q : ℝ)) 0) =
          lambda (s + 1) q := by
        intros q _; rw [risingProd_zero, risingProd_zero]; ring
      rw [Finset.sum_congr rfl hsum]
      rw [sum_lambda_eq_zero (Nat.succ_pos s)]
      have hCzero : ((0 : ℕ).choose (s + 1) : ℝ) = 0 := by
        exact_mod_cast Nat.choose_eq_zero_of_lt (Nat.succ_pos s)
      rw [hCzero]; ring
    | succ j inner_ih =>
      have hp : 0 < s + 1 := Nat.succ_pos s
      have hF := centralDifferenceLHS_succ_j (s := s + 1) hp j w
      have hG := centralDifferenceRHS_succ_j (s := s + 1) hp j w
      have hs1 : (s + 1 - 1 : ℕ) = s := by omega
      rw [hs1] at hF hG
      rw [hF, inner_ih, ih j w, ← hG]

theorem central_difference_identity (s j : ℕ) (w : ℝ) :
    (∑ q ∈ Finset.range (s + 1),
      lambda s q *
        ((∏ i ∈ Finset.range j, (w + q + (i : ℝ))) *
         (∏ i ∈ Finset.range j, (w - q + (i : ℝ))))) =
    (Nat.choose j s : ℝ) *
      (∏ i ∈ Finset.range (j - s), (w + (i : ℝ))) *
      (∏ i ∈ Finset.range (j - s), (w + s + (i : ℝ))) := by
  have h := centralDifference_eq s j w
  simp only [centralDifferenceLHS, centralDifferenceRHS, risingProd] at h
  exact h

theorem central_difference_asc
    (s j : ℕ) (w : ℝ) :
    (∑ q ∈ Finset.range (s + 1),
      lambda s q *
        ((ascPochhammer ℝ j).eval (w + q) *
         (ascPochhammer ℝ j).eval (w - q))) =
      (Nat.choose j s : ℝ) *
      (ascPochhammer ℝ (j - s)).eval w *
      (ascPochhammer ℝ (j - s)).eval (w + s) := by
  simpa [ascPochhammer_eval_eq_prod_range_real, add_assoc, add_comm, add_left_comm, sub_eq_add_neg]
    using central_difference_identity s j w

theorem lambda_zero_left (q : ℕ) :
    lambda 0 q =
      if q = 0 then 1 else 2 * (-1 : ℝ) ^ q * ((Nat.factorial q : ℝ)⁻¹) := by
  by_cases hq : q = 0 <;> simp [lambda, hq]

theorem lambda_zero_zero : lambda 0 0 = 1 := by
  simp [lambda]

theorem rungKernel_zero (n k : ℕ) (μ : ℝ) :
    rungKernel n k 0 μ = pochhammer μ k * pochhammer μ (n - k) := by
  simp [rungKernel, lambda]

theorem lambda_one_zero : lambda 1 0 = 1 := by
  norm_num [lambda]

theorem lambda_one_one : lambda 1 1 = -1 := by
  norm_num [lambda]

theorem rungKernel_one_zero (n k : ℕ) :
    rungKernel n k 1 0 = determinantKernel n k := by
  rw [rungKernel, determinantKernel]
  norm_num [lambda, Finset.sum_range_succ]
  rw [sub_eq_add_neg]

theorem determinantPolynomial_eq_rungOperator (n : ℕ) (f : ℕ → ℝ) :
    determinantPolynomial n f =
      rungOperator n 1 0
        (ordinaryGen n fun k => f k * f (n - k) * (Nat.choose n k : ℝ)) := by
  rw [determinantPolynomial, rungOperator]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [coeff_ordinaryGen_of_le n (fun k => f k * f (n - k) * (Nat.choose n k : ℝ)) hk_le,
    rungKernel_one_zero]

theorem centeredOperator_zero_one (n : ℕ) (Q : ℝ[X]) :
    centeredOperator n 0 1 Q = rungOperator n 1 0 Q := by
  simp [centeredOperator, rungOperator, centeredKernel_zero_one, rungKernel_one_zero]

/-- Vandermonde–Chu identity for ascending Pochhammer symbols. -/
private lemma ascPochhammer_vandermonde (a b : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) *
          ((ascPochhammer ℝ k).eval a * (ascPochhammer ℝ (n - k)).eval b) =
      (ascPochhammer ℝ n).eval (a + b) := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
    -- Reduce (ascP (n+1)).eval (a+b) = (ascP n).eval (a+b) * (a+b+n).
    have hRHS : (ascPochhammer ℝ (n + 1)).eval (a + b) =
        (ascPochhammer ℝ n).eval (a + b) * (a + b + (n : ℝ)) := by
      rw [ascPochhammer_succ_right, eval_mul, eval_add, eval_X, eval_natCast]
    rw [hRHS, ← ih a b, Finset.sum_mul]
    -- Distribute (a + b + n) into (a + k) + (b + n - k) and use ascPochhammer_succ_right.
    have hsplit : ∀ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) *
            ((ascPochhammer ℝ k).eval a *
              (ascPochhammer ℝ (n - k)).eval b) *
            (a + b + (n : ℝ)) =
          (Nat.choose n k : ℝ) *
              ((ascPochhammer ℝ (k + 1)).eval a *
                (ascPochhammer ℝ (n - k)).eval b) +
            (Nat.choose n k : ℝ) *
              ((ascPochhammer ℝ k).eval a *
                (ascPochhammer ℝ (n + 1 - k)).eval b) := by
      intros k hk
      rw [Finset.mem_range] at hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp hk
      have h1 : (ascPochhammer ℝ (k + 1)).eval a =
          (ascPochhammer ℝ k).eval a * (a + (k : ℝ)) := by
        rw [ascPochhammer_succ_right, eval_mul, eval_add, eval_X, eval_natCast]
      have h2 : (ascPochhammer ℝ (n + 1 - k)).eval b =
          (ascPochhammer ℝ (n - k)).eval b * (b + ((n - k : ℕ) : ℝ)) := by
        rw [show n + 1 - k = (n - k) + 1 from by omega, ascPochhammer_succ_right,
            eval_mul, eval_add, eval_X, eval_natCast]
      have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hkn
      rw [h1, h2, hcast]; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    -- Reindex the first sum k → k+1 onto Ico 1 (n+2).
    have hreindex :
        ∑ k ∈ Finset.range (n + 1),
            (Nat.choose n k : ℝ) *
              ((ascPochhammer ℝ (k + 1)).eval a *
                (ascPochhammer ℝ (n - k)).eval b) =
          ∑ k ∈ Finset.Ico 1 (n + 2),
            (Nat.choose n (k - 1) : ℝ) *
              ((ascPochhammer ℝ k).eval a *
                (ascPochhammer ℝ (n + 1 - k)).eval b) := by
      refine Finset.sum_nbij' (fun k => k + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
      · intro k hk
        rw [Finset.mem_range] at hk
        change k + 1 ∈ Finset.Ico 1 (n + 2)
        rw [Finset.mem_Ico]; omega
      · intro k hk
        rw [Finset.mem_Ico] at hk
        change k - 1 ∈ Finset.range (n + 1)
        rw [Finset.mem_range]; omega
      · intro k _; change k + 1 - 1 = k; omega
      · intro k hk
        rw [Finset.mem_Ico] at hk
        change k - 1 + 1 = k; omega
      · intro k hk
        rw [Finset.mem_range] at hk
        have hkn : k ≤ n := Nat.lt_succ_iff.mp hk
        change (Nat.choose n k : ℝ) *
              ((ascPochhammer ℝ (k + 1)).eval a *
                (ascPochhammer ℝ (n - k)).eval b) =
            (Nat.choose n (k + 1 - 1) : ℝ) *
              ((ascPochhammer ℝ (k + 1)).eval a *
                (ascPochhammer ℝ (n + 1 - (k + 1))).eval b)
        rw [show k + 1 - 1 = k from by omega,
            show n + 1 - (k + 1) = n - k from by omega]
    rw [hreindex]
    -- Combine LHS_2 with the {0} term and the shifted sum
    -- to match the RHS Pascal.  Convert LHS_2 from range to Ico:
    have hLHS2_ico :
        ∑ k ∈ Finset.range (n + 1),
            (Nat.choose n k : ℝ) *
              ((ascPochhammer ℝ k).eval a *
                (ascPochhammer ℝ (n + 1 - k)).eval b) =
          ∑ k ∈ Finset.Ico 0 (n + 1),
            (Nat.choose n k : ℝ) *
              ((ascPochhammer ℝ k).eval a *
                (ascPochhammer ℝ (n + 1 - k)).eval b) := by
      rw [Finset.range_eq_Ico]
    -- Convert target RHS from range to Ico decomposition.
    have hRHS_split :
        ∑ k ∈ Finset.range (n + 1 + 1),
            (Nat.choose (n + 1) k : ℝ) *
              ((ascPochhammer ℝ k).eval a *
                (ascPochhammer ℝ (n + 1 - k)).eval b) =
          ((ascPochhammer ℝ 0).eval a * (ascPochhammer ℝ (n + 1)).eval b) +
          ∑ k ∈ Finset.Ico 1 (n + 2),
            (Nat.choose (n + 1) k : ℝ) *
              ((ascPochhammer ℝ k).eval a *
                (ascPochhammer ℝ (n + 1 - k)).eval b) := by
      rw [Finset.range_eq_Ico]
      rw [show (n + 1 + 1) = (n + 2) from by ring]
      rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ n + 2)]
      rw [show Finset.Ico 0 1 = {0} from rfl]
      rw [Finset.sum_singleton]
      simp [Nat.choose_zero_right]
    -- For k ∈ Ico 1 (n+2), use Pascal C(n+1, k) = C(n, k-1) + C(n, k).
    have hRHS_pascal :
        ∑ k ∈ Finset.Ico 1 (n + 2),
            (Nat.choose (n + 1) k : ℝ) *
              ((ascPochhammer ℝ k).eval a *
                (ascPochhammer ℝ (n + 1 - k)).eval b) =
          ∑ k ∈ Finset.Ico 1 (n + 2),
              ((Nat.choose n (k - 1) : ℝ) *
                ((ascPochhammer ℝ k).eval a *
                  (ascPochhammer ℝ (n + 1 - k)).eval b)) +
          ∑ k ∈ Finset.Ico 1 (n + 2),
              ((Nat.choose n k : ℝ) *
                ((ascPochhammer ℝ k).eval a *
                  (ascPochhammer ℝ (n + 1 - k)).eval b)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : 1 ≤ k := hk.1
      have hpascal : ((n + 1).choose k : ℝ) =
          (n.choose (k - 1) : ℝ) + (n.choose k : ℝ) := by
        have hkk : (k - 1) + 1 = k := by omega
        have hp := Nat.choose_succ_succ n (k - 1)
        simp only [Nat.succ_eq_add_one] at hp
        rw [hkk] at hp
        have : (n + 1).choose k = n.choose (k - 1) + n.choose k := by linarith
        exact_mod_cast this
      rw [hpascal]; ring
    -- Now extend the second sum (Ico 1 (n+2)) of LHS_2 form to include k = 0,
    -- and the value at k = n+1 is zero (C(n, n+1) = 0).
    have hLHS2_eq : ∑ k ∈ Finset.range (n + 1),
            (Nat.choose n k : ℝ) *
              ((ascPochhammer ℝ k).eval a *
                (ascPochhammer ℝ (n + 1 - k)).eval b) =
          ((ascPochhammer ℝ 0).eval a * (ascPochhammer ℝ (n + 1)).eval b) +
          ∑ k ∈ Finset.Ico 1 (n + 2),
              ((Nat.choose n k : ℝ) *
                ((ascPochhammer ℝ k).eval a *
                  (ascPochhammer ℝ (n + 1 - k)).eval b)) := by
      rw [hLHS2_ico]
      have hext : ∑ k ∈ Finset.Ico 1 (n + 2),
              ((Nat.choose n k : ℝ) *
                ((ascPochhammer ℝ k).eval a *
                  (ascPochhammer ℝ (n + 1 - k)).eval b)) =
            ∑ k ∈ Finset.Ico 1 (n + 1),
              ((Nat.choose n k : ℝ) *
                ((ascPochhammer ℝ k).eval a *
                  (ascPochhammer ℝ (n + 1 - k)).eval b)) := by
        rw [show n + 2 = (n + 1) + 1 from by ring]
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
        have : n.choose (n + 1) = 0 :=
          Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)
        rw [show ((n.choose (n + 1) : ℕ) : ℝ) = 0 from by exact_mod_cast this]
        ring
      rw [hext]
      rw [show Finset.Ico 0 (n + 1) = insert 0 (Finset.Ico 1 (n + 1)) from by
            ext x; simp [Finset.mem_Ico, Finset.mem_insert]; omega]
      rw [Finset.sum_insert (by simp [Finset.mem_Ico])]
      simp [Nat.choose_zero_right]
    rw [hRHS_split, hRHS_pascal, hLHS2_eq]
    ring

/-- Pointwise evaluation of `rungOperator … (gammaBasis n j)` at `z`. -/
private lemma rung_action_eval (n s j : ℕ) (h2j : 2 * j ≤ n) (μ z : ℝ) :
    (rungOperator n s μ (gammaBasis n j)).eval z =
      (Nat.choose j s : ℝ) *
        (ascPochhammer ℝ (j - s)).eval (z + μ) *
        (ascPochhammer ℝ (j - s)).eval (z + μ + s) *
        (ascPochhammer ℝ (n - 2 * j)).eval (2 * z + 2 * μ + 2 * j) := by
  rw [rungOperator_eval]
  simp_rw [rungKernel_eval]
  -- Distribute the (gammaBasis n j).coeff factor over the q-sum, then swap.
  have h_distrib : ∀ k ∈ Finset.range (n + 1),
      (gammaBasis n j).coeff k *
        ∑ q ∈ Finset.range (s + 1),
          lambda s q *
            ((ascPochhammer ℝ k).eval (z + μ + ↑q) *
              (ascPochhammer ℝ (n - k)).eval (z + μ - ↑q)) =
        ∑ q ∈ Finset.range (s + 1),
          ((gammaBasis n j).coeff k * lambda s q) *
            ((ascPochhammer ℝ k).eval (z + μ + ↑q) *
              (ascPochhammer ℝ (n - k)).eval (z + μ - ↑q)) := by
    intros k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros; ring
  rw [Finset.sum_congr rfl h_distrib]
  rw [Finset.sum_comm]
  -- For each q, simplify the inner k-sum.
  have hinner : ∀ q ∈ Finset.range (s + 1),
      ∑ k ∈ Finset.range (n + 1),
          ((gammaBasis n j).coeff k * lambda s q) *
            ((ascPochhammer ℝ k).eval (z + μ + q) *
              (ascPochhammer ℝ (n - k)).eval (z + μ - q)) =
        lambda s q *
          ((ascPochhammer ℝ j).eval (z + μ + q) *
            (ascPochhammer ℝ j).eval (z + μ - q) *
            (ascPochhammer ℝ (n - 2 * j)).eval (2 * z + 2 * μ + 2 * j)) := by
    intros q _
    have h_pullL : ∀ k ∈ Finset.range (n + 1),
        ((gammaBasis n j).coeff k * lambda s q) *
            ((ascPochhammer ℝ k).eval (z + μ + ↑q) *
              (ascPochhammer ℝ (n - k)).eval (z + μ - ↑q)) =
          lambda s q *
            ((gammaBasis n j).coeff k *
              ((ascPochhammer ℝ k).eval (z + μ + ↑q) *
                (ascPochhammer ℝ (n - k)).eval (z + μ - ↑q))) := by
      intros _ _; ring
    rw [Finset.sum_congr rfl h_pullL, ← Finset.mul_sum]
    congr 1
    -- Plug coeff_gammaBasis.
    have h_coeff : ∀ k ∈ Finset.range (n + 1),
        (gammaBasis n j).coeff k *
            ((ascPochhammer ℝ k).eval (z + μ + ↑q) *
              (ascPochhammer ℝ (n - k)).eval (z + μ - ↑q)) =
          (if j ≤ k then ((n - 2 * j).choose (k - j) : ℝ) else 0) *
            ((ascPochhammer ℝ k).eval (z + μ + ↑q) *
              (ascPochhammer ℝ (n - k)).eval (z + μ - ↑q)) := by
      intros k _; rw [coeff_gammaBasis]
    rw [Finset.sum_congr rfl h_coeff]
    -- Push the `if` outside the multiplication.
    have h_if : ∀ k ∈ Finset.range (n + 1),
        (if j ≤ k then ((n - 2 * j).choose (k - j) : ℝ) else 0) *
            ((ascPochhammer ℝ k).eval (z + μ + ↑q) *
              (ascPochhammer ℝ (n - k)).eval (z + μ - ↑q)) =
          if j ≤ k then
            ((n - 2 * j).choose (k - j) : ℝ) *
              ((ascPochhammer ℝ k).eval (z + μ + ↑q) *
                (ascPochhammer ℝ (n - k)).eval (z + μ - ↑q))
          else 0 := by
      intros _ _; split_ifs <;> ring
    rw [Finset.sum_congr rfl h_if]
    rw [← Finset.sum_filter]
    -- range (n+1) ∩ {k | j ≤ k} = Ico j (n + 1).
    rw [show Finset.filter (fun k => j ≤ k) (Finset.range (n + 1)) =
            Finset.Ico j (n + 1) from by
        ext k; simp [Finset.mem_range, Finset.mem_Ico, Finset.mem_filter]; omega]
    -- Reindex k = j + ℓ.
    rw [Finset.sum_Ico_eq_sum_range]
    -- Now sum is over ℓ ∈ range (n + 1 - j), with k replaced by j + ℓ.
    have hℓ : ∀ ℓ ∈ Finset.range (n + 1 - j),
        ((n - 2 * j).choose (j + ℓ - j) : ℝ) *
          ((ascPochhammer ℝ (j + ℓ)).eval (z + μ + ↑q) *
            (ascPochhammer ℝ (n - (j + ℓ))).eval (z + μ - ↑q)) =
        ((n - 2 * j).choose ℓ : ℝ) *
          ((ascPochhammer ℝ (j + ℓ)).eval (z + μ + ↑q) *
            (ascPochhammer ℝ (n - (j + ℓ))).eval (z + μ - ↑q)) := by
      intros ℓ _
      rw [show j + ℓ - j = ℓ from by omega]
    rw [Finset.sum_congr rfl hℓ]
    -- Now truncate the sum to ℓ ∈ range (n - 2j + 1).
    rw [show ∑ ℓ ∈ Finset.range (n + 1 - j),
            ((n - 2 * j).choose ℓ : ℝ) *
              ((ascPochhammer ℝ (j + ℓ)).eval (z + μ + ↑q) *
                (ascPochhammer ℝ (n - (j + ℓ))).eval (z + μ - ↑q)) =
          ∑ ℓ ∈ Finset.range (n - 2 * j + 1),
            ((n - 2 * j).choose ℓ : ℝ) *
              ((ascPochhammer ℝ (j + ℓ)).eval (z + μ + ↑q) *
                (ascPochhammer ℝ (n - (j + ℓ))).eval (z + μ - ↑q)) from by
      rw [show Finset.range (n + 1 - j) =
              Finset.range (n - 2 * j + 1) ∪
                Finset.Ico (n - 2 * j + 1) (n + 1 - j) from by
            ext x
            simp [Finset.mem_range, Finset.mem_Ico, Finset.mem_union]
            omega]
      rw [Finset.sum_union (by
        rw [Finset.disjoint_left]
        intros x hx hx'
        rw [Finset.mem_range] at hx
        rw [Finset.mem_Ico] at hx'
        omega)]
      rw [show ∑ ℓ ∈ Finset.Ico (n - 2 * j + 1) (n + 1 - j),
              ((n - 2 * j).choose ℓ : ℝ) *
                ((ascPochhammer ℝ (j + ℓ)).eval (z + μ + ↑q) *
                  (ascPochhammer ℝ (n - (j + ℓ))).eval (z + μ - ↑q)) = 0 from by
        apply Finset.sum_eq_zero
        intros ℓ hℓ
        rw [Finset.mem_Ico] at hℓ
        have hC0 : (n - 2 * j).choose ℓ = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [show ((n - 2 * j).choose ℓ : ℝ) = 0 from by exact_mod_cast hC0]
        ring]
      rw [add_zero]]
    -- Now apply ascPochhammer_mul to split each (ascP (j+ℓ)) and (ascP (n-(j+ℓ))).
    have hsplit : ∀ ℓ ∈ Finset.range (n - 2 * j + 1),
        ((n - 2 * j).choose ℓ : ℝ) *
          ((ascPochhammer ℝ (j + ℓ)).eval (z + μ + ↑q) *
            (ascPochhammer ℝ (n - (j + ℓ))).eval (z + μ - ↑q)) =
        (ascPochhammer ℝ j).eval (z + μ + ↑q) *
            (ascPochhammer ℝ j).eval (z + μ - ↑q) *
            (((n - 2 * j).choose ℓ : ℝ) *
              ((ascPochhammer ℝ ℓ).eval (z + μ + ↑q + j) *
                (ascPochhammer ℝ (n - 2 * j - ℓ)).eval (z + μ - ↑q + j))) := by
      intros ℓ hℓ
      rw [Finset.mem_range] at hℓ
      have hℓle : ℓ ≤ n - 2 * j := Nat.lt_succ_iff.mp hℓ
      -- (ascP (j + ℓ)).eval (z + μ + q) = (ascP j).eval (z + μ + q) * (ascP ℓ).eval (z + μ + q + j)
      have h1 : (ascPochhammer ℝ (j + ℓ)).eval (z + μ + ↑q) =
          (ascPochhammer ℝ j).eval (z + μ + ↑q) *
            (ascPochhammer ℝ ℓ).eval (z + μ + ↑q + ↑j) := by
        have hmul := ascPochhammer_mul (S := ℝ) j ℓ
        have := congrArg (fun p => (p : ℝ[X]).eval (z + μ + ↑q)) hmul.symm
        simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast] at this
        exact this
      -- (ascP (n - (j + ℓ))).eval (z + μ - q) = ?
      -- n - (j + ℓ) = j + (n - 2j - ℓ), use ascPochhammer_mul:
      -- (ascP (j + (n - 2j - ℓ))).eval (z + μ - q) = (ascP j).eval (z + μ - q) *
      --                                              (ascP (n - 2j - ℓ)).eval (z + μ - q + j)
      have h2 : (ascPochhammer ℝ (n - (j + ℓ))).eval (z + μ - ↑q) =
          (ascPochhammer ℝ j).eval (z + μ - ↑q) *
            (ascPochhammer ℝ (n - 2 * j - ℓ)).eval (z + μ - ↑q + ↑j) := by
        have hcomp : n - (j + ℓ) = j + (n - 2 * j - ℓ) := by omega
        rw [hcomp]
        have hmul := ascPochhammer_mul (S := ℝ) j (n - 2 * j - ℓ)
        have := congrArg (fun p => (p : ℝ[X]).eval (z + μ - ↑q)) hmul.symm
        simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast] at this
        exact this
      rw [h1, h2]
      ring
    rw [Finset.sum_congr rfl hsplit]
    -- Factor (ascP j).eval(z+μ+q) * (ascP j).eval(z+μ-q) out of the ℓ-sum.
    rw [← Finset.mul_sum]
    -- Apply Vandermonde-Chu.
    rw [ascPochhammer_vandermonde]
    -- Now the argument is (z + μ + q + j) + (z + μ - q + j) = 2z + 2μ + 2j.
    congr 2
    ring
  rw [Finset.sum_congr rfl hinner]
  -- Factor (ascP (n - 2j)).eval (2z+2μ+2j) out of the q-sum.
  have h_pullN : ∀ q ∈ Finset.range (s + 1),
      lambda s q *
          ((ascPochhammer ℝ j).eval (z + μ + ↑q) *
            (ascPochhammer ℝ j).eval (z + μ - ↑q) *
            (ascPochhammer ℝ (n - 2 * j)).eval (2 * z + 2 * μ + 2 * ↑j)) =
        (ascPochhammer ℝ (n - 2 * j)).eval (2 * z + 2 * μ + 2 * ↑j) *
          (lambda s q *
            ((ascPochhammer ℝ j).eval (z + μ + ↑q) *
              (ascPochhammer ℝ j).eval (z + μ - ↑q))) := by
    intros _ _; ring
  rw [Finset.sum_congr rfl h_pullN]
  rw [← Finset.mul_sum]
  -- Apply central_difference_asc with w = z + μ.
  rw [central_difference_asc]
  ring

theorem rung_action_on_gamma_basis
    (n m ε s j : ℕ) (μ : ℝ)
    (_hε : ε = 0 ∨ ε = 1) (_hn : n = 2 * m + ε) (h2j : 2 * j ≤ n) :
    rungOperator n s μ (gammaBasis n j) =
      C (Nat.choose j s : ℝ) *
        pochhammer μ (j - s) *
        pochhammer (μ + s) (j - s) *
        linearPochhammer 2 (2 * μ + 2 * j) (n - 2 * j) := by
  apply Polynomial.funext
  intro z
  rw [rung_action_eval n s j h2j μ z]
  -- RHS.eval z = C(j, s) * (ascP (j-s)).eval(z+μ) * (ascP (j-s)).eval(z+μ+s)
  --   * (ascP (n-2j)).eval(2z+2μ+2j)
  rw [eval_mul, eval_mul, eval_mul, eval_C, pochhammer_eval, pochhammer_eval,
      linearPochhammer_eval]
  rw [show (z + (μ + ↑s)) = z + μ + ↑s from by ring]
  simp_rw [ascPochhammer_eval_eq_prod_range_real]
  ring_nf

/-! Helpers for `ladder_formula`. -/

/-- Coefficient of `gammaPolynomial m γ` at index `k ≤ m`. -/
private lemma gammaPolynomial_coeff_of_le (m : ℕ) (γ : ℕ → ℝ) {k : ℕ} (hk : k ≤ m) :
    (gammaPolynomial m γ).coeff k = γ k := by
  rw [gammaPolynomial, finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hbk; simp [hbk.symm]
  · intro hknot
    exact False.elim (hknot (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))

/-- Duplication formula (even case):
`(ascP (2N)).eval (2v) = 4^N · (ascP N).eval v · (ascP N).eval (v+1/2)`. -/
private lemma ascPochhammer_two_mul_eval (N : ℕ) (v : ℝ) :
    (ascPochhammer ℝ (2 * N)).eval (2 * v) =
      (4 : ℝ) ^ N *
        ((ascPochhammer ℝ N).eval v * (ascPochhammer ℝ N).eval (v + 1 / 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    -- (ascP (2(N+1))).eval(2v) = (ascP (2N)).eval(2v) · (2v + 2N) · (2v + 2N + 1).
    have h_eval_step : (ascPochhammer ℝ (2 * (N + 1))).eval (2 * v) =
        (ascPochhammer ℝ (2 * N)).eval (2 * v) *
          (2 * v + (2 * N : ℝ)) * (2 * v + (2 * N : ℝ) + 1) := by
      have hexp : 2 * (N + 1) = (2 * N + 1) + 1 := by ring
      rw [hexp, ascPochhammer_succ_right, eval_mul, eval_add, eval_X, eval_natCast]
      rw [show (2 * N + 1 : ℕ) = 2 * N + 1 from rfl, ascPochhammer_succ_right,
          eval_mul, eval_add, eval_X, eval_natCast]
      push_cast; ring
    rw [h_eval_step, ih]
    have h_eval_Np1 : (ascPochhammer ℝ (N + 1)).eval v =
        (ascPochhammer ℝ N).eval v * (v + (N : ℝ)) := by
      rw [ascPochhammer_succ_right, eval_mul, eval_add, eval_X, eval_natCast]
    have h_eval_Np1_half : (ascPochhammer ℝ (N + 1)).eval (v + 1 / 2) =
        (ascPochhammer ℝ N).eval (v + 1 / 2) * (v + 1 / 2 + (N : ℝ)) := by
      rw [ascPochhammer_succ_right, eval_mul, eval_add, eval_X, eval_natCast]
    rw [h_eval_Np1, h_eval_Np1_half]
    ring

/-- Combined duplication formula for `ε ∈ {0, 1}`. -/
private lemma ascPochhammer_two_mul_add_eps_eval (N ε : ℕ) (hε : ε = 0 ∨ ε = 1) (v : ℝ) :
    (ascPochhammer ℝ (2 * N + ε)).eval (2 * v) =
      (2 : ℝ) ^ ε * (4 : ℝ) ^ N *
        ((ascPochhammer ℝ N).eval v * (ascPochhammer ℝ N).eval (v + 1 / 2)) *
        (ascPochhammer ℝ ε).eval (v + (N : ℝ)) := by
  rcases hε with rfl | rfl
  · simp only [add_zero, pow_zero, one_mul, ascPochhammer_zero, eval_one, mul_one]
    rw [ascPochhammer_two_mul_eval]
  · rw [show (2 * N + 1 : ℕ) = 2 * N + 1 from rfl, ascPochhammer_succ_right,
        eval_mul, eval_add, eval_X, eval_natCast]
    rw [ascPochhammer_two_mul_eval]
    rw [ascPochhammer_one, eval_X]
    push_cast; ring

/-- Simplification of one LHS term in `ladder_formula` after duplication +
`ascPochhammer_mul`. -/
private lemma rung_eval_simplify (n m ε s k : ℕ) (hε : ε = 0 ∨ ε = 1)
    (hn : n = 2 * m + ε) (hsm : s ≤ m) (hkms : k ≤ m - s) (μ z : ℝ) :
    (ascPochhammer ℝ k).eval (z + μ + s) *
        (ascPochhammer ℝ (n - 2 * (k + s))).eval (2 * z + 2 * μ + 2 * (k + s)) =
      (2 : ℝ) ^ ε * (4 : ℝ) ^ (m - s - k) *
        (ascPochhammer ℝ (m - s + ε)).eval (z + μ + s) *
        (ascPochhammer ℝ (m - s - k)).eval (z + μ + k + s + 1 / 2) := by
  have h1 : n - 2 * (k + s) = 2 * (m - s - k) + ε := by rw [hn]; omega
  rw [h1]
  rw [show 2 * z + 2 * μ + 2 * ((k : ℝ) + (s : ℝ)) = 2 * (z + μ + (s : ℝ) + (k : ℝ))
        from by ring]
  rw [ascPochhammer_two_mul_add_eps_eval (m - s - k) ε hε (z + μ + s + k)]
  -- ascPochhammer_mul: (ascP k) * (ascP (m-s-k)).comp(X + k) = ascP (m-s).
  have h3 : (ascPochhammer ℝ k).eval (z + μ + s) *
      (ascPochhammer ℝ (m - s - k)).eval (z + μ + s + (k : ℝ)) =
      (ascPochhammer ℝ (m - s)).eval (z + μ + s) := by
    have hmul := ascPochhammer_mul (S := ℝ) k (m - s - k)
    have hkadd : k + (m - s - k) = m - s := by omega
    rw [hkadd] at hmul
    have heval := congrArg (fun p => (p : ℝ[X]).eval (z + μ + s)) hmul.symm
    simp only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast] at heval
    exact heval.symm
  -- Cast of (m - s - k) as a real.
  have hcast_m :
      (z + μ + (s : ℝ) + (k : ℝ) + ((m - s - k : ℕ) : ℝ)) = z + μ + (m : ℝ) := by
    rw [Nat.cast_sub hkms, Nat.cast_sub hsm]
    ring
  rcases hε with rfl | rfl
  · -- ε = 0.
    simp only [add_zero, pow_zero, one_mul, ascPochhammer_zero, eval_one, mul_one]
    rw [show z + μ + (k : ℝ) + (s : ℝ) + 1 / 2 = z + μ + (s : ℝ) + (k : ℝ) + 1 / 2 from by ring]
    -- Group ascPs to apply h3.
    rw [show (ascPochhammer ℝ k).eval (z + μ + (s : ℝ)) *
        ((4 : ℝ) ^ (m - s - k) *
          ((ascPochhammer ℝ (m - s - k)).eval (z + μ + (s : ℝ) + (k : ℝ)) *
            (ascPochhammer ℝ (m - s - k)).eval (z + μ + (s : ℝ) + (k : ℝ) + 1 / 2))) =
        (4 : ℝ) ^ (m - s - k) *
          ((ascPochhammer ℝ k).eval (z + μ + (s : ℝ)) *
            (ascPochhammer ℝ (m - s - k)).eval (z + μ + (s : ℝ) + (k : ℝ))) *
          (ascPochhammer ℝ (m - s - k)).eval (z + μ + (s : ℝ) + (k : ℝ) + 1 / 2) from by ring]
    rw [h3]
  · -- ε = 1.
    rw [ascPochhammer_one, eval_X]
    rw [hcast_m]
    -- Use (ascP (m-s+1)).eval(z+μ+s) = (ascP (m-s)).eval(z+μ+s) * (z+μ+m).
    have h_mp1 : (ascPochhammer ℝ (m - s + 1)).eval (z + μ + (s : ℝ)) =
        (ascPochhammer ℝ (m - s)).eval (z + μ + (s : ℝ)) * (z + μ + (m : ℝ)) := by
      rw [ascPochhammer_succ_right, eval_mul, eval_add, eval_X, eval_natCast]
      rw [show ((m - s : ℕ) : ℝ) = (m : ℝ) - (s : ℝ) from Nat.cast_sub hsm]
      ring
    rw [h_mp1]
    rw [show z + μ + (k : ℝ) + (s : ℝ) + 1 / 2 = z + μ + (s : ℝ) + (k : ℝ) + 1 / 2 from by ring]
    -- Group ascPs to apply h3.
    linear_combination
      ((2 : ℝ) ^ 1 * (4 : ℝ) ^ (m - s - k) *
        (ascPochhammer ℝ (m - s - k)).eval (z + μ + (s : ℝ) + (k : ℝ) + 1 / 2) *
        (z + μ + (m : ℝ))) * h3

/-- Coefficient computation for the polynomial `B` appearing inside `schurTransform`. -/
private lemma ladder_B_coeff (m s : ℕ) (γ : ℕ → ℝ) (r : ℕ) (hr : r ≤ m - s)
    (hsm : s ≤ m) :
    (C ((4 : ℝ) ^ (m - s)) *
        ((derivative^[s]) (gammaPolynomial m γ)).comp (C ((1 / 4 : ℝ)) * X)).coeff r =
      (4 : ℝ) ^ (m - s - r) * ((r + s).descFactorial s : ℝ) * γ (r + s) := by
  rw [coeff_C_mul, comp_C_mul_X_coeff, coeff_iterate_derivative]
  rw [gammaPolynomial_coeff_of_le m γ (by omega : r + s ≤ m)]
  rw [nsmul_eq_mul]
  -- 4^(m-s) * ((r+s).descFactorial s * γ(r+s)) * (1/4)^r
  -- = 4^(m-s-r) * (r+s).descFactorial s * γ(r+s)
  have h4 : (4 : ℝ) ^ (m - s) * ((1 : ℝ) / 4) ^ r = (4 : ℝ) ^ (m - s - r) := by
    have heq : m - s = r + (m - s - r) := by omega
    calc (4 : ℝ) ^ (m - s) * ((1 : ℝ) / 4) ^ r
        = (4 : ℝ) ^ (r + (m - s - r)) * ((1 : ℝ) / 4) ^ r := by rw [← heq]
      _ = (4 : ℝ) ^ r * (4 : ℝ) ^ (m - s - r) * ((1 : ℝ) / 4) ^ r := by rw [pow_add]
      _ = (4 : ℝ) ^ (m - s - r) * ((4 : ℝ) ^ r * ((1 : ℝ) / 4) ^ r) := by ring
      _ = (4 : ℝ) ^ (m - s - r) * ((4 * (1 / 4) : ℝ) ^ r) := by rw [mul_pow]
      _ = (4 : ℝ) ^ (m - s - r) * 1 ^ r := by norm_num
      _ = (4 : ℝ) ^ (m - s - r) := by ring
  linear_combination
    (((r + s).descFactorial s : ℝ) * γ (r + s)) * h4

theorem ladder_formula
    (n m ε s : ℕ) (μ : ℝ) (Q : ℝ[X]) (γ : ℕ → ℝ)
    (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε)
    (hγ : IsGammaExpansion n m Q γ) :
    rungOperator n s μ Q =
      C ((2 : ℝ) ^ ε / (Nat.factorial s : ℝ)) *
      pochhammer (μ + s) (m - s + ε) *
      (schurTransform (m - s) (s + (1 / 2 : ℝ))
          ((C ((4 : ℝ) ^ (m - s))) *
            ((derivative^[s]) (gammaPolynomial m γ)).comp (C ((1 / 4 : ℝ)) * X))).comp
        (X + C μ) := by
  -- Step 1: expand LHS via γ-expansion of Q and basis action.
  rw [rungOperator_gammaExpansion n m s μ Q γ hγ]
  have h_action : ∀ j ∈ Finset.range (m + 1),
      C (γ j) * rungOperator n s μ (gammaBasis n j) =
      C (γ j) *
        (C ((j.choose s : ℝ)) * pochhammer μ (j - s) *
          pochhammer (μ + s) (j - s) *
          linearPochhammer 2 (2 * μ + 2 * j) (n - 2 * j)) := by
    intros j hj
    rw [Finset.mem_range] at hj
    have h2j : 2 * j ≤ n := by rw [hn]; omega
    rw [rung_action_on_gamma_basis n m ε s j μ hε hn h2j]
  rw [Finset.sum_congr rfl h_action]
  apply Polynomial.funext
  intro z
  -- Step 2: evaluate LHS at z.
  rw [eval_finset_sum]
  have h_LHS_each : ∀ j ∈ Finset.range (m + 1),
      (C (γ j) *
        (C ((j.choose s : ℝ)) * pochhammer μ (j - s) *
          pochhammer (μ + s) (j - s) *
          linearPochhammer 2 (2 * μ + 2 * j) (n - 2 * j))).eval z =
      γ j * ((j.choose s : ℝ)) *
        (ascPochhammer ℝ (j - s)).eval (z + μ) *
        (ascPochhammer ℝ (j - s)).eval (z + μ + s) *
        (ascPochhammer ℝ (n - 2 * j)).eval (2 * z + 2 * μ + 2 * j) := by
    intros j _
    rw [eval_mul, eval_mul, eval_mul, eval_mul, eval_C, eval_C,
        pochhammer_eval, pochhammer_eval, linearPochhammer_eval]
    ring_nf
  rw [Finset.sum_congr rfl h_LHS_each]
  -- Case split on s ≤ m.
  by_cases hsm : s ≤ m
  · -- Normal case.
    -- Restrict LHS sum to j ≥ s.
    rw [show Finset.range (m + 1) =
            Finset.range s ∪ Finset.Ico s (m + 1) from by
      ext x; simp [Finset.mem_range, Finset.mem_Ico, Finset.mem_union]; omega]
    rw [Finset.sum_union (by
      rw [Finset.disjoint_left]
      intros x hx hx'
      rw [Finset.mem_range] at hx
      rw [Finset.mem_Ico] at hx'
      omega)]
    rw [show ∑ j ∈ Finset.range s,
            γ j * ((j.choose s : ℝ)) *
              (ascPochhammer ℝ (j - s)).eval (z + μ) *
              (ascPochhammer ℝ (j - s)).eval (z + μ + s) *
              (ascPochhammer ℝ (n - 2 * j)).eval (2 * z + 2 * μ + 2 * j) = 0 from by
      apply Finset.sum_eq_zero
      intros j hj
      rw [Finset.mem_range] at hj
      have : (j.choose s : ℝ) = 0 :=
        by exact_mod_cast Nat.choose_eq_zero_of_lt hj
      rw [this]; ring]
    rw [zero_add]
    -- Reindex j → k + s on Ico s (m + 1) ≃ range (m - s + 1).
    rw [show ∑ j ∈ Finset.Ico s (m + 1),
            γ j * ((j.choose s : ℝ)) *
              (ascPochhammer ℝ (j - s)).eval (z + μ) *
              (ascPochhammer ℝ (j - s)).eval (z + μ + s) *
              (ascPochhammer ℝ (n - 2 * j)).eval (2 * z + 2 * μ + 2 * j) =
          ∑ k ∈ Finset.range (m - s + 1),
            γ (k + s) * (((k + s).choose s : ℝ)) *
              (ascPochhammer ℝ k).eval (z + μ) *
              (ascPochhammer ℝ k).eval (z + μ + s) *
              (ascPochhammer ℝ (n - 2 * (k + s))).eval (2 * z + 2 * μ + 2 * (k + s)) from by
      refine Finset.sum_nbij' (fun j => j - s) (fun k => k + s) ?_ ?_ ?_ ?_ ?_
      · intros j hj
        rw [Finset.mem_Ico] at hj
        change j - s ∈ Finset.range (m - s + 1)
        rw [Finset.mem_range]; omega
      · intros k hk
        rw [Finset.mem_range] at hk
        change k + s ∈ Finset.Ico s (m + 1)
        rw [Finset.mem_Ico]; omega
      · intros j hj
        rw [Finset.mem_Ico] at hj
        change j - s + s = j
        omega
      · intros k _
        change k + s - s = k
        omega
      · intros j hj
        rw [Finset.mem_Ico] at hj
        simp only []
        have hjs : (j - s) + s = j := by omega
        have hjs_cast : ((j - s : ℕ) : ℝ) + ((s : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
          rw [← Nat.cast_add, hjs]
        rw [hjs, hjs_cast]]
    -- Apply rung_eval_simplify termwise.
    have h_LHS_simp : ∀ k ∈ Finset.range (m - s + 1),
        γ (k + s) * (((k + s).choose s : ℝ)) *
            (ascPochhammer ℝ k).eval (z + μ) *
            (ascPochhammer ℝ k).eval (z + μ + s) *
            (ascPochhammer ℝ (n - 2 * (k + s))).eval (2 * z + 2 * μ + 2 * (k + s)) =
          (2 : ℝ) ^ ε * (ascPochhammer ℝ (m - s + ε)).eval (z + μ + s) *
            (γ (k + s) * ((k + s).choose s : ℝ) * (4 : ℝ) ^ (m - s - k) *
              (ascPochhammer ℝ k).eval (z + μ) *
              (ascPochhammer ℝ (m - s - k)).eval (z + μ + k + s + 1 / 2)) := by
      intros k hk
      rw [Finset.mem_range] at hk
      have hkms : k ≤ m - s := by omega
      have hsimp := rung_eval_simplify n m ε s k hε hn hsm hkms μ z
      linear_combination
        (γ (k + s) * ((k + s).choose s : ℝ) *
          (ascPochhammer ℝ k).eval (z + μ)) * hsimp
    rw [Finset.sum_congr rfl h_LHS_simp]
    -- Factor out the common 2^ε * (ascP (m-s+ε)).eval(z+μ+s).
    rw [← Finset.mul_sum]
    -- Now LHS.eval z = 2^ε * (ascP (m-s+ε)).eval(z+μ+s) *
    --   Σ_k γ(k+s) * (k+s).choose s * 4^(m-s-k) *
    --   (ascP k).eval(z+μ) * (ascP (m-s-k)).eval(z+μ+k+s+1/2)
    -- Evaluate RHS.
    rw [eval_mul, eval_mul, eval_C, pochhammer_eval, eval_comp]
    rw [eval_add, eval_X, eval_C]
    rw [show z + (μ + (s : ℝ)) = z + μ + s from by ring]
    -- Expand schurTransform.
    rw [schurTransform, eval_finset_sum]
    have h_RHS_each : ∀ r ∈ Finset.range (m - s + 1),
        (C ((C ((4 : ℝ) ^ (m - s)) *
              ((derivative^[s]) (gammaPolynomial m γ)).comp (C ((1 / 4 : ℝ)) * X)).coeff r) *
            pochhammer 0 r * pochhammer ((r : ℝ) + (s + 1 / 2)) (m - s - r)).eval (z + μ) =
          (4 : ℝ) ^ (m - s - r) * ((r + s).descFactorial s : ℝ) * γ (r + s) *
            (ascPochhammer ℝ r).eval (z + μ) *
            (ascPochhammer ℝ (m - s - r)).eval (z + μ + r + s + 1 / 2) := by
      intros r hr
      rw [Finset.mem_range] at hr
      have hr_le : r ≤ m - s := by omega
      rw [eval_mul, eval_mul, eval_C, pochhammer_eval, pochhammer_eval]
      rw [ladder_B_coeff m s γ r hr_le hsm]
      rw [show z + μ + (0 : ℝ) = z + μ from by ring]
      rw [show z + μ + ((r : ℝ) + (s + 1 / 2)) = z + μ + (r : ℝ) + s + 1 / 2 from by ring]
    rw [Finset.sum_congr rfl h_RHS_each]
    -- Factor out 2^ε / s!.
    rw [show (2 : ℝ) ^ ε / (Nat.factorial s : ℝ) *
            (ascPochhammer ℝ (m - s + ε)).eval (z + μ + (s : ℝ)) *
            ∑ r ∈ Finset.range (m - s + 1),
              (4 : ℝ) ^ (m - s - r) * ((r + s).descFactorial s : ℝ) * γ (r + s) *
                (ascPochhammer ℝ r).eval (z + μ) *
                (ascPochhammer ℝ (m - s - r)).eval (z + μ + (r : ℝ) + (s : ℝ) + 1 / 2) =
          (2 : ℝ) ^ ε *
            (ascPochhammer ℝ (m - s + ε)).eval (z + μ + (s : ℝ)) *
            ∑ r ∈ Finset.range (m - s + 1),
              ((1 / (Nat.factorial s : ℝ)) *
                ((4 : ℝ) ^ (m - s - r) * ((r + s).descFactorial s : ℝ) * γ (r + s) *
                  (ascPochhammer ℝ r).eval (z + μ) *
                  (ascPochhammer ℝ (m - s - r)).eval (z + μ + (r : ℝ) + (s : ℝ) + 1 / 2))) from by
      rw [← Finset.mul_sum]; ring]
    -- Match LHS and RHS term-wise.
    congr 1
    apply Finset.sum_congr rfl
    intros k _
    -- Equates `γ(k+s) * (k+s).choose s * 4^(m-s-k) * ...` to
    -- `(1/s!) * 4^(m-s-k) * descFactorial(k+s, s) * γ(k+s) * ...`
    -- via (k+s).choose s * s! = descFactorial(k+s, s).
    have hdesc : ((k + s).descFactorial s : ℝ) =
        (Nat.factorial s : ℝ) * ((k + s).choose s : ℝ) := by
      have := Nat.descFactorial_eq_factorial_mul_choose (k + s) s
      exact_mod_cast this
    have hfact_ne : (Nat.factorial s : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [hdesc]
    field_simp
  · -- Edge case: s > m. Both sides reduce to 0.
    have hsm : m < s := Nat.lt_of_not_le hsm
    rw [show ∑ j ∈ Finset.range (m + 1),
            γ j * ((j.choose s : ℝ)) *
              (ascPochhammer ℝ (j - s)).eval (z + μ) *
              (ascPochhammer ℝ (j - s)).eval (z + μ + s) *
              (ascPochhammer ℝ (n - 2 * j)).eval (2 * z + 2 * μ + 2 * j) = 0 from by
      apply Finset.sum_eq_zero
      intros j hj
      rw [Finset.mem_range] at hj
      have hC : (j.choose s : ℝ) = 0 :=
        by exact_mod_cast Nat.choose_eq_zero_of_lt (by omega)
      rw [hC]; ring]
    -- RHS: (derivative^[s]) (gammaPolynomial m γ) = 0 since natDegree < s.
    have hD : (derivative^[s]) (gammaPolynomial m γ) = 0 := by
      apply Polynomial.iterate_derivative_eq_zero
      have hdeg : (gammaPolynomial m γ).natDegree ≤ m := by
        rw [gammaPolynomial]
        apply Polynomial.natDegree_sum_le_of_forall_le (n := m)
        intros j hj
        rw [Finset.mem_range] at hj
        calc (C (γ j) * X ^ j).natDegree
            ≤ (X ^ j).natDegree := Polynomial.natDegree_C_mul_le (γ j) _
          _ = j := Polynomial.natDegree_X_pow j
          _ ≤ m := by omega
      omega
    rw [hD]
    simp [Polynomial.zero_comp, schurTransform]

theorem convex_nonposRealAxis :
    Convex ℝ {z : ℂ | ∃ r : ℝ, r ≤ 0 ∧ z = (r : ℂ)} := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨r, hr, rfl⟩
  rcases hy with ⟨s, hs, rfl⟩
  refine ⟨a * r + b * s, ?_, ?_⟩
  · exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hr)
      (mul_nonpos_of_nonneg_of_nonpos hb hs)
  · simp [Complex.ofReal_add, Complex.ofReal_mul]

theorem derivative_preserves_nonpos_one
    (p : ℝ[X]) :
    HasOnlyRealNonposZeros p →
    HasOnlyRealNonposZeros (derivative p) := by
  intro hp
  rcases hp with rfl | hp
  · left
    simp
  by_cases hder : derivative p = 0
  · left
    exact hder
  right
  intro z hz
  let P : ℂ[X] := toComplex p
  have hmapder : toComplex (derivative p) = derivative P := by
    simp [P, toComplex, Polynomial.derivative_map]
  have hderC : derivative P ≠ 0 := by
    intro h
    apply hder
    have hzmap : toComplex (derivative p) = 0 := by
      rw [hmapder, h]
    exact (Polynomial.map_eq_zero (algebraMap ℝ ℂ)).1 hzmap
  have hPdeg : 0 < P.degree := by
    by_contra hnot
    have hle : P.degree ≤ 0 := le_of_not_gt hnot
    have hconst : P = C (P.coeff 0) := Polynomial.eq_C_of_degree_le_zero hle
    apply hderC
    rw [hconst, derivative_C]
  have hzroot : z ∈ (derivative P).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    refine ⟨hderC, ?_⟩
    simpa [coe_aeval_eq_eval, hmapder] using hz
  have hGL :
      z ∈ convexHull ℝ ((P).rootSet ℂ) :=
    Polynomial.rootSet_derivative_subset_convexHull_rootSet (P := P) hPdeg hzroot
  have hrootSubset :
      (P.rootSet ℂ : Set ℂ) ⊆ {z : ℂ | ∃ r : ℝ, r ≤ 0 ∧ z = (r : ℂ)} := by
    intro x hx
    rw [Polynomial.mem_rootSet] at hx
    exact hp x (by simpa [P, toComplex, coe_aeval_eq_eval] using hx.2)
  exact (convexHull_min hrootSubset convex_nonposRealAxis) hGL

theorem derivative_preserves_nonpos
    (s : ℕ) (p : ℝ[X]) :
    HasOnlyRealNonposZeros p →
    HasOnlyRealNonposZeros ((derivative^[s]) p) := by
  intro hp
  induction s generalizing p with
  | zero =>
      simpa using hp
  | succ s ih =>
      simpa [Function.iterate_succ_apply'] using
        derivative_preserves_nonpos_one ((derivative^[s]) p) (ih p hp)

theorem scale_comp_preserves_nonpos
    (p : ℝ[X]) {a : ℝ} :
    0 < a →
    HasOnlyRealNonposZeros p →
    HasOnlyRealNonposZeros (p.comp (C a * X)) := by
  intro ha hp
  rcases hp with rfl | hp
  · left
    simp
  right
  intro z hz
  have hz' : (toComplex p).eval ((a : ℂ) * z) = 0 := by
    have hmap :
        toComplex (p.comp (C a * X)) =
          (toComplex p).comp (C (a : ℂ) * X) := by
      simp [toComplex, Polynomial.map_comp]
    rw [hmap, eval_comp] at hz
    simpa using hz
  obtain ⟨r, hr, hzr⟩ := hp ((a : ℂ) * z) hz'
  refine ⟨r / a, div_nonpos_of_nonpos_of_nonneg hr ha.le, ?_⟩
  have haC : (a : ℂ) ≠ 0 := by
    have : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
    exact this
  calc
    z = ((a : ℂ) * z) / (a : ℂ) := by field_simp [haC]
    _ = (r : ℂ) / (a : ℂ) := by rw [hzr]
    _ = ((r / a : ℝ) : ℂ) := by norm_num

theorem pochhammer_nonpos
    {a : ℝ} (k : ℕ) :
    0 ≤ a →
    HasOnlyRealNonposZeros (pochhammer a k) := by
  intro ha
  right
  intro z hz
  have hz' : (∏ i ∈ Finset.range k, (z + ((a + (i : ℝ)) : ℂ))) = 0 := by
    simpa [toComplex, pochhammer, eval_prod, eval_add, eval_C, eval_X] using hz
  rw [Finset.prod_eq_zero_iff] at hz'
  obtain ⟨i, hi, hzi⟩ := hz'
  refine ⟨-(a + (i : ℝ)), ?_, ?_⟩
  · have hi0 : 0 ≤ (i : ℝ) := by exact_mod_cast Nat.zero_le i
    linarith
  · simpa using (eq_neg_of_add_eq_zero_left hzi)

theorem pochhammer_negative
    {a : ℝ} (k : ℕ) :
    0 < a →
    HasOnlyRealNegativeZeros (pochhammer a k) := by
  intro ha
  right
  intro z hz
  have hz' : (∏ i ∈ Finset.range k, (z + ((a + (i : ℝ)) : ℂ))) = 0 := by
    simpa [toComplex, pochhammer, eval_prod, eval_add, eval_C, eval_X] using hz
  rw [Finset.prod_eq_zero_iff] at hz'
  obtain ⟨i, hi, hzi⟩ := hz'
  refine ⟨-(a + (i : ℝ)), ?_, ?_⟩
  · have hi0 : 0 ≤ (i : ℝ) := by exact_mod_cast Nat.zero_le i
    linarith
  · simpa using (eq_neg_of_add_eq_zero_left hzi)

theorem mul_preserves_nonpos
    (p q : ℝ[X]) :
    HasOnlyRealNonposZeros p →
    HasOnlyRealNonposZeros q →
    HasOnlyRealNonposZeros (p * q) := by
  intro hp hq
  rcases hp with rfl | hp
  · left
    simp
  rcases hq with rfl | hq
  · left
    simp
  right
  intro z hz
  have hz' : (toComplex p).eval z * (toComplex q).eval z = 0 := by
    simpa [toComplex, eval_mul] using hz
  rcases mul_eq_zero.mp hz' with hpz | hqz
  · exact hp z hpz
  · exact hq z hqz

theorem mul_preserves_negative
    (p q : ℝ[X]) :
    HasOnlyRealNegativeZeros p →
    HasOnlyRealNegativeZeros q →
    HasOnlyRealNegativeZeros (p * q) := by
  intro hp hq
  rcases hp with rfl | hp
  · left
    simp
  rcases hq with rfl | hq
  · left
    simp
  right
  intro z hz
  have hz' : (toComplex p).eval z * (toComplex q).eval z = 0 := by
    simpa [toComplex, eval_mul] using hz
  rcases mul_eq_zero.mp hz' with hpz | hqz
  · exact hp z hpz
  · exact hq z hqz

theorem const_mul_preserves_nonpos
    (c : ℝ) (p : ℝ[X]) :
    HasOnlyRealNonposZeros p →
    HasOnlyRealNonposZeros (C c * p) := by
  intro hp
  rcases hp with rfl | hp
  · left
    simp
  by_cases hc : c = 0
  · left
    simp [hc]
  right
  intro z hz
  have hz' : (c : ℂ) * (toComplex p).eval z = 0 := by
    simpa [toComplex, eval_mul] using hz
  rcases mul_eq_zero.mp hz' with hc' | hpz
  · have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    exact False.elim (hcC hc')
  · exact hp z hpz

theorem const_mul_preserves_negative
    (c : ℝ) (p : ℝ[X]) :
    HasOnlyRealNegativeZeros p →
    HasOnlyRealNegativeZeros (C c * p) := by
  intro hp
  rcases hp with rfl | hp
  · left
    simp
  by_cases hc : c = 0
  · left
    simp [hc]
  right
  intro z hz
  have hz' : (c : ℂ) * (toComplex p).eval z = 0 := by
    simpa [toComplex, eval_mul] using hz
  rcases mul_eq_zero.mp hz' with hc' | hpz
  · have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    exact False.elim (hcC hc')
  · exact hp z hpz

theorem shift_right_preserves_nonpos
    (p : ℝ[X]) {μ : ℝ} :
    0 ≤ μ →
    HasOnlyRealNonposZeros p →
    HasOnlyRealNonposZeros (p.comp (X + C μ)) := by
  intro hμ hp
  rcases hp with rfl | hp
  · left
    simp
  right
  intro z hz
  have hz' : (toComplex p).eval (z + (μ : ℂ)) = 0 := by
    have hmap :
        toComplex (p.comp (X + C μ)) =
          (toComplex p).comp (X + C (μ : ℂ)) := by
      simp [toComplex, Polynomial.map_comp]
    rw [hmap, eval_comp] at hz
    simpa using hz
  obtain ⟨r, hr, hzr⟩ := hp (z + (μ : ℂ)) hz'
  refine ⟨r - μ, by linarith, ?_⟩
  calc
    z = z + (μ : ℂ) - (μ : ℂ) := by ring
    _ = (r : ℂ) - (μ : ℂ) := by rw [hzr]
    _ = ((r - μ : ℝ) : ℂ) := by norm_num

theorem shift_right_preserves_negative
    (p : ℝ[X]) {μ : ℝ} :
    0 < μ →
    HasOnlyRealNonposZeros p →
    HasOnlyRealNegativeZeros (p.comp (X + C μ)) := by
  intro hμ hp
  rcases hp with rfl | hp
  · left
    simp
  right
  intro z hz
  have hz' : (toComplex p).eval (z + (μ : ℂ)) = 0 := by
    have hmap :
        toComplex (p.comp (X + C μ)) =
          (toComplex p).comp (X + C (μ : ℂ)) := by
      simp [toComplex, Polynomial.map_comp]
    rw [hmap, eval_comp] at hz
    simpa using hz
  obtain ⟨r, hr, hzr⟩ := hp (z + (μ : ℂ)) hz'
  refine ⟨r - μ, by linarith, ?_⟩
  calc
    z = z + (μ : ℂ) - (μ : ℂ) := by ring
    _ = (r : ℂ) - (μ : ℂ) := by rw [hzr]
    _ = ((r - μ : ℝ) : ℂ) := by norm_num

/-! **Theorem 1 of the paper** is now proven, not axiomatized. See
`GammaPochhammer.determinant_main_preserves_strict_proved` in `Determinant.lean`
for the proof using Lemmas 1, 2, 3. The wrapper `main_theorem` in
`Determinant.lean` provides the user-facing statement.

`centered_classification_axiom` (Theorem 3 of the paper) is **no longer an
axiom**.  It is now proved in `GammaPochhammer/Classification.lean` as
`GammaPochhammer.centered_classification_proved`, and the user-facing
`centered_balanced_classification` theorem lives there too. -/

/-! ## Theorems corresponding to the paper -/

theorem Hadamard_closure_for_negative_rooted_polynomials
    (n : ℕ) (A B : ℝ[X])
    (hAcoeff : ∀ k ≤ n, 0 ≤ A.coeff k)
    (hBcoeff : ∀ k ≤ n, 0 ≤ B.coeff k)
    (hA : HasOnlyRealNonposZeros A)
    (hB : HasOnlyRealNonposZeros B) :
    HasOnlyRealNonposZeros (hadamard n A B) :=
  hadamard_closure_for_negative_rooted n A B hAcoeff hBcoeff hA hB

theorem schur_transform_preserves_nonpos
    (ell : ℕ) {α : ℝ} (hα : 0 < α) (B : ℝ[X])
    (hB : HasOnlyRealNonposZeros B) :
    HasOnlyRealNonposZeros (schurTransform ell α B) :=
  schur_preserves_nonpos ell hα B hB

-- `gamma_representation_of_palindromic_negative_rooted` is now in
-- `GammaRep.lean`, where Lemma 3 is proven.

theorem central_difference
    (s j : ℕ) (w : ℝ) :
    (∑ q ∈ Finset.range (s + 1),
      lambda s q *
        ((∏ i ∈ Finset.range j, (w + q + (i : ℝ))) *
         (∏ i ∈ Finset.range j, (w - q + (i : ℝ))))) =
    (Nat.choose j s : ℝ) *
      (∏ i ∈ Finset.range (j - s), (w + (i : ℝ))) *
      (∏ i ∈ Finset.range (j - s), (w + s + (i : ℝ))) :=
  central_difference_identity s j w

theorem rung_action
    (n m ε s j : ℕ) (μ : ℝ)
    (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε) (h2j : 2 * j ≤ n) :
    rungOperator n s μ (gammaBasis n j) =
      C (Nat.choose j s : ℝ) *
        pochhammer μ (j - s) *
        pochhammer (μ + s) (j - s) *
        linearPochhammer 2 (2 * μ + 2 * j) (n - 2 * j) :=
  rung_action_on_gamma_basis n m ε s j μ hε hn h2j

theorem pochhammer_kernel_ladder_formula
    (n m ε s : ℕ) (μ : ℝ) (Q : ℝ[X]) (γ : ℕ → ℝ)
    (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε)
    (hγ : IsGammaExpansion n m Q γ) :
    rungOperator n s μ Q =
      C ((2 : ℝ) ^ ε / (Nat.factorial s : ℝ)) *
      pochhammer (μ + s) (m - s + ε) *
      (schurTransform (m - s) (s + (1 / 2 : ℝ))
          ((C ((4 : ℝ) ^ (m - s))) *
            ((derivative^[s]) (gammaPolynomial m γ)).comp (C ((1 / 4 : ℝ)) * X))).comp
        (X + C μ) :=
  ladder_formula n m ε s μ Q γ hε hn hγ

-- `pochhammer_kernel_ladder`, `pochhammer_kernel_ladder_strict_shift`,
-- `original_kernel_palindromic`, and `single_product_kernel` are now in
-- `GammaRep.lean`, since they consume the proved Lemma 3.
--
-- `main_theorem` (Theorem 1 of the paper) is stated and proven in
-- `Determinant.lean`, which has access to the Vieta machinery needed for
-- the proof.

-- `centered_balanced_classification` (Theorem 3 of the paper) is stated and
-- proven in `Classification.lean` as `centered_classification_proved`, and
-- re-exported there as `centered_balanced_classification`.

/-- The normalized unsigned row used in the paper agrees with the stated
closed form of OEIS A380113. -/
theorem A380113_zero_zero : A380113 0 0 = 1 := by
  simp [A380113]

theorem A380113_left_edge (s : ℕ) (hs : s ≠ 0) :
    A380113 s 0 = Nat.choose (2 * s) s / 2 := by
  simp [A380113, hs]

theorem A380113_internal (s q : ℕ) (hq : q ≠ 0) :
    A380113 s q = Nat.choose (2 * s) (s - q) := by
  simp [A380113, hq]

end GammaPochhammer
