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

axiom gamma_representation
    (n m ε : ℕ) (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε)
    (Q : ℝ[X]) :
    PalindromicOfDegree n Q →
    HasOnlyRealNegativeZeros Q →
    ∃ γ : ℕ → ℝ,
      IsGammaExpansion n m Q γ ∧
      HasOnlyRealNonposZeros (gammaPolynomial m γ)

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

axiom central_difference_identity
    (s j : ℕ) (w : ℝ) :
    (∑ q ∈ Finset.range (s + 1),
      lambda s q *
        ((∏ i ∈ Finset.range j, (w + q + (i : ℝ))) *
         (∏ i ∈ Finset.range j, (w - q + (i : ℝ))))) =
    (Nat.choose j s : ℝ) *
      (∏ i ∈ Finset.range (j - s), (w + (i : ℝ))) *
      (∏ i ∈ Finset.range (j - s), (w + s + (i : ℝ)))

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

axiom rung_action_on_gamma_basis
    (n m ε s j : ℕ) (μ : ℝ)
    (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε) :
    rungOperator n s μ (gammaBasis n j) =
      C (Nat.choose j s : ℝ) *
        pochhammer μ (j - s) *
        pochhammer (μ + s) (j - s) *
        linearPochhammer 2 (2 * μ + 2 * j) (n - 2 * j)

axiom ladder_formula
    (n m ε s : ℕ) (μ : ℝ) (Q : ℝ[X]) (γ : ℕ → ℝ)
    (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε)
    (hγ : IsGammaExpansion n m Q γ) :
    rungOperator n s μ Q =
      C ((2 : ℝ) ^ ε / (Nat.factorial s : ℝ)) *
      pochhammer (μ + s) (m - s + ε) *
      (schurTransform (m - s) (s + (1 / 2 : ℝ))
          ((C ((4 : ℝ) ^ (m - s))) *
            ((derivative^[s]) (gammaPolynomial m γ)).comp (C ((1 / 4 : ℝ)) * X))).comp
        (X + C μ)

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

axiom determinant_main_preserves_strict
    (n : ℕ) (f : ℕ → ℝ) :
    2 ≤ n →
    HasDegree (ordinaryGen n f) n →
    HasOnlyRealNegativeZeros (ordinaryGen n f) →
    HasOnlyRealNegativeZeros (determinantPolynomial n f)

axiom centered_classification_axiom
    (a c : ℝ) :
    a ^ 2 ≠ c ^ 2 →
    (UniversallyAdmissibleCentered a c ↔
      ({a ^ 2, c ^ 2} : Set ℝ) = ({0, 1} : Set ℝ))

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

theorem gamma_representation_of_palindromic_negative_rooted
    (n m ε : ℕ) (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε)
    (Q : ℝ[X])
    (hpal : PalindromicOfDegree n Q)
    (hroot : HasOnlyRealNegativeZeros Q) :
    ∃ γ : ℕ → ℝ,
      IsGammaExpansion n m Q γ ∧
      HasOnlyRealNonposZeros (gammaPolynomial m γ) :=
  gamma_representation n m ε hε hn Q hpal hroot

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
    (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε) :
    rungOperator n s μ (gammaBasis n j) =
      C (Nat.choose j s : ℝ) *
        pochhammer μ (j - s) *
        pochhammer (μ + s) (j - s) *
        linearPochhammer 2 (2 * μ + 2 * j) (n - 2 * j) :=
  rung_action_on_gamma_basis n m ε s j μ hε hn

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

theorem pochhammer_kernel_ladder
    (n m ε s : ℕ) (μ : ℝ) (Q : ℝ[X])
    (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε)
    (_hs : s ≤ m)
    (hpal : PalindromicOfDegree n Q)
    (hroot : HasOnlyRealNegativeZeros Q)
    (hμ : 0 ≤ μ) :
    HasOnlyRealNonposZeros (rungOperator n s μ Q) :=
by
  obtain ⟨γ, hγ, hγroot⟩ :=
    gamma_representation n m ε hε hn Q hpal hroot
  rw [ladder_formula n m ε s μ Q γ hε hn hγ]
  apply mul_preserves_nonpos
  · apply const_mul_preserves_nonpos
    apply pochhammer_nonpos
    positivity
  · apply shift_right_preserves_nonpos _ hμ
    apply schur_preserves_nonpos
    · positivity
    · apply const_mul_preserves_nonpos
      apply scale_comp_preserves_nonpos
      · norm_num
      · exact derivative_preserves_nonpos s (gammaPolynomial m γ) hγroot

theorem pochhammer_kernel_ladder_strict_shift
    (n m ε s : ℕ) (μ : ℝ) (Q : ℝ[X])
    (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε)
    (_hs : s ≤ m)
    (hpal : PalindromicOfDegree n Q)
    (hroot : HasOnlyRealNegativeZeros Q)
    (hμ : 0 < μ) :
    HasOnlyRealNegativeZeros (rungOperator n s μ Q) :=
by
  obtain ⟨γ, hγ, hγroot⟩ :=
    gamma_representation n m ε hε hn Q hpal hroot
  rw [ladder_formula n m ε s μ Q γ hε hn hγ]
  apply mul_preserves_negative
  · apply const_mul_preserves_negative
    apply pochhammer_negative
    positivity
  · apply shift_right_preserves_negative _ hμ
    apply schur_preserves_nonpos
    · positivity
    · apply const_mul_preserves_nonpos
      apply scale_comp_preserves_nonpos
      · norm_num
      · exact derivative_preserves_nonpos s (gammaPolynomial m γ) hγroot

theorem original_kernel_palindromic
    (n m ε : ℕ) (Q : ℝ[X])
    (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε)
    (hm : 1 ≤ m)
    (hpal : PalindromicOfDegree n Q)
    (hroot : HasOnlyRealNegativeZeros Q) :
    HasOnlyRealNonposZeros (rungOperator n 1 0 Q) :=
  pochhammer_kernel_ladder n m ε 1 0 Q hε hn hm hpal hroot (le_refl 0)

theorem main_theorem
    (n : ℕ) (f : ℕ → ℝ)
    (hn : 2 ≤ n)
    (hdeg : HasDegree (ordinaryGen n f) n)
    (hroot : HasOnlyRealNegativeZeros (ordinaryGen n f)) :
    HasOnlyRealNegativeZeros (determinantPolynomial n f) :=
  determinant_main_preserves_strict n f hn hdeg hroot

theorem single_product_kernel
    (n m ε : ℕ) (μ : ℝ) (Q : ℝ[X])
    (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε)
    (hpal : PalindromicOfDegree n Q)
    (hroot : HasOnlyRealNegativeZeros Q)
    (hμ : 0 < μ) :
    HasOnlyRealNegativeZeros (rungOperator n 0 μ Q) :=
  pochhammer_kernel_ladder_strict_shift n m ε 0 μ Q hε hn (Nat.zero_le m) hpal hroot hμ

theorem centered_balanced_classification
    (a c : ℝ) (h : a ^ 2 ≠ c ^ 2) :
    UniversallyAdmissibleCentered a c ↔
      ({a ^ 2, c ^ 2} : Set ℝ) = ({0, 1} : Set ℝ) :=
  centered_classification_axiom a c h

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
