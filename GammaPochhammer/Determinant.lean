import GammaPochhammer.Basic

/-!
# Theorem 1 of the paper — derived from Lemmas 1, 2, 3

This module formalizes the path to discharging the project axiom
`GammaPochhammer.determinant_main_preserves_strict` in `Basic.lean`,
following **Theorem 1** of *"Gamma Operators for Pochhammer Kernels"*.

For `n ≥ 2` and a sequence `f : ℕ → ℝ` such that `ordinaryGen n f` has
degree exactly `n` and only real strictly negative zeros, the polynomial
`determinantPolynomial n f` has only real strictly negative zeros.

## The paper's proof strategy

1. Define `convolutionPoly n f = ordinaryGen n (k ↦ f(k)·f(n-k)·C(n,k))`.
2. Show `convolutionPoly` is **palindromic** (direct calculation).
3. Show `convolutionPoly` has only real negative zeros using
   **Lemma 1** (Hadamard closure) applied twice:
   - `F ⋆ F_reversed` has nonneg coefficients and real nonpositive zeros.
   - `(F ⋆ F_reversed) ⋆ (1+X)^n = convolutionPoly`, also real nonpositive.
   - Strict negativity comes from `convolutionPoly(0) = f(0)·f(n) > 0`.
4. Apply **Theorem 2 (the ladder)** with `s = 1`, `μ = 0` (already proven
   in `Basic.lean` as `pochhammer_kernel_ladder`, which uses Lemmas 2, 3):
   `rungOperator n 1 0 (convolutionPoly) = determinantPolynomial n f`
   has only real nonpositive zeros.
5. Compute `P_n(0) = n!·(f(1)·f(n-1) − f(0)·f(n))` directly (paper).
6. Use `e_1·e_{n-1} > e_n` on positive root magnitudes (paper's
   Cauchy-Schwarz argument) to deduce `P_n(0) > 0`, excluding `0` from
   the zero set.

Closing the two remaining `sorry`s below derives Theorem 1 from the
three other axioms (`hadamard_closure_for_negative_rooted`,
`gamma_representation`, `schur_preserves_nonpos`), eliminating
`determinant_main_preserves_strict` as a standalone axiom.
-/

noncomputable section

open BigOperators Polynomial

namespace GammaPochhammer

/-! ## Utility: complex / real root equivalence -/

private theorem isRoot_toComplex_iff_real (p : ℝ[X]) (r : ℝ) :
    (toComplex p).eval (r : ℂ) = 0 ↔ p.eval r = 0 := by
  have hcast : ((r : ℝ) : ℂ) = (algebraMap ℝ ℂ) r := rfl
  have heval : (toComplex p).eval (r : ℂ) = ((p.eval r : ℝ) : ℂ) := by
    rw [hcast]
    unfold toComplex
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rfl
  rw [heval]
  exact_mod_cast Iff.rfl

/-! ## Vieta factorization for real-negative-rooted polynomials

The paper's proof of Theorem 1 uses Vieta in two places:
* "all coefficients f_k are nonzero and have the same sign" (first paragraph)
* `e_1·e_{n-1} > e_n` (last paragraph) where `e_k = e_k(α₁,…,αₙ)` for
  positive root magnitudes.

We formalize both via an inductive factorization:
`p = C(leadingCoeff p) · ∏(X + C α_i)` with `α_i > 0`. -/

private theorem exists_real_negative_root_aux (p : ℝ[X])
    (h : HasOnlyRealNegativeZeros p) (hdeg : 1 ≤ p.natDegree) :
    ∃ r : ℝ, r < 0 ∧ p.eval r = 0 := by
  have hp_ne : p ≠ 0 := fun hp0 => by rw [hp0] at hdeg; simp at hdeg
  have hpc_ne : toComplex p ≠ 0 := by
    intro h0
    apply hp_ne
    unfold toComplex at h0
    exact (Polynomial.map_eq_zero_iff (algebraMap ℝ ℂ).injective).mp h0
  have hpc_natDeg : 1 ≤ (toComplex p).natDegree := by
    unfold toComplex
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
    exact hdeg
  have hpc_deg : 0 < (toComplex p).degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)
  obtain ⟨z, hz⟩ := Complex.exists_root hpc_deg
  rcases h with h0 | hreal
  · exact absurd h0 hp_ne
  obtain ⟨r, hr_neg, hr_eq⟩ := hreal z hz
  refine ⟨r, hr_neg, ?_⟩
  rw [hr_eq] at hz
  exact (isRoot_toComplex_iff_real p r).mp hz

private theorem hasOnlyRealNegativeZeros_factor_quotient {p q : ℝ[X]} {r : ℝ}
    (hp : HasOnlyRealNegativeZeros p) (hpq : p = (X - C r) * q) :
    HasOnlyRealNegativeZeros q := by
  by_cases hq0 : q = 0
  · left; exact hq0
  rcases hp with hp0 | hp
  · rw [hp0] at hpq
    rcases mul_eq_zero.mp hpq.symm with h | h
    · exact absurd h (X_sub_C_ne_zero r)
    · exact absurd h hq0
  right
  intro z hz
  apply hp
  have hmul : toComplex p = toComplex (X - C r) * toComplex q := by
    rw [hpq]; simp [toComplex, Polynomial.map_mul]
  rw [hmul, Polynomial.eval_mul, hz, mul_zero]

/-- Vieta-style factorization: a polynomial with only real strictly negative
zeros factors as `C(leadingCoeff) · ∏(X + α_i)` for positive `α_i`.

Following the paper's first paragraph: "F = C ∏(1 + αᵢx)". -/
private theorem exists_factorization_real_neg (p : ℝ[X])
    (hp : HasOnlyRealNegativeZeros p) :
    ∃ α : Multiset ℝ, α.card = p.natDegree ∧ (∀ a ∈ α, 0 < a) ∧
      p = C p.leadingCoeff * (α.map fun a => X + C a).prod := by
  generalize hn : p.natDegree = n
  induction n using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
    · subst hn0
      refine ⟨∅, by simp, fun a ha => by simp at ha, ?_⟩
      have hp_eq_C : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hn
      have hcoeff : p.coeff 0 = p.leadingCoeff := by
        rw [Polynomial.leadingCoeff, hn]
      simp [hcoeff.symm, ← hp_eq_C]
    · have hdeg : 1 ≤ p.natDegree := by omega
      have hp_ne : p ≠ 0 := fun h => by rw [h] at hn; simp at hn; omega
      obtain ⟨r, hr_neg, hr_root⟩ := exists_real_negative_root_aux p hp hdeg
      obtain ⟨q, hpq⟩ := (Polynomial.dvd_iff_isRoot (p := p) (a := r)).mpr hr_root
      have hq_ne : q ≠ 0 := fun h => by rw [h, mul_zero] at hpq; exact hp_ne hpq
      have hq_deg : q.natDegree = n - 1 := by
        have hnd : ((X - C r) * q).natDegree = q.natDegree + 1 := by
          rw [Polynomial.natDegree_mul (X_sub_C_ne_zero r) hq_ne,
              Polynomial.natDegree_X_sub_C, add_comm]
        rw [← hpq, hn] at hnd; omega
      have hq_lt : q.natDegree < n := by omega
      have hq_root : HasOnlyRealNegativeZeros q :=
        hasOnlyRealNegativeZeros_factor_quotient hp hpq
      have hq_lc : p.leadingCoeff = q.leadingCoeff := by
        rw [hpq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X_sub_C, one_mul]
      obtain ⟨αq, hαq_card, hαq_pos, hαq_eq⟩ := ih q.natDegree hq_lt q hq_root rfl
      refine ⟨(-r) ::ₘ αq, ?_, ?_, ?_⟩
      · rw [Multiset.card_cons, hαq_card, hq_deg]; omega
      · intro a ha
        rcases Multiset.mem_cons.mp ha with ha_neg | ha_in
        · rw [ha_neg]; linarith
        · exact hαq_pos a ha_in
      · rw [hq_lc, Multiset.map_cons, Multiset.prod_cons]
        conv_lhs => rw [hpq, hαq_eq]
        have hxcr : (X - C r : ℝ[X]) = X + C (-r) := by rw [Polynomial.C_neg]; ring
        rw [hxcr]
        ring

/-! ## Pochhammer evaluation at zero (paper §1 — used in `P_n(0)`) -/

/-- `pochhammer 0 k . eval (0:ℝ) = 0` whenever `1 ≤ k`. The product
`X(X+1)…(X+k-1)` contains the factor `X`. -/
private theorem pochhammer_zero_eval_zero_of_pos (k : ℕ) (hk : 1 ≤ k) :
    (pochhammer 0 k).eval (0 : ℝ) = 0 := by
  unfold pochhammer
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr hk)
  simp

/-- `pochhammer (-1) k . eval (0:ℝ) = 0` whenever `2 ≤ k`. The product
`(X-1)·X·(X+1)…` contains the factor `X` at index 1. -/
private theorem pochhammer_negone_eval_zero_of_ge_two (k : ℕ) (hk : 2 ≤ k) :
    (pochhammer (-1) k).eval (0 : ℝ) = 0 := by
  unfold pochhammer
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := 1) (Finset.mem_range.mpr (by omega))
  simp

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

/-- `pochhammer 1 k . eval 0 = k!`. The product `(0+1)(0+2)⋯(0+k)` is `k!`. -/
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

/-! ## The convolution polynomial `Q_f` (paper §1, in the proof of Theorem 1) -/

/-- `Q_f = Σ f(k)·f(n-k)·C(n,k)·x^k`. The palindromic polynomial whose
γ-positive structure drives the paper's proof of Theorem 1. -/
def convolutionPoly (n : ℕ) (f : ℕ → ℝ) : ℝ[X] :=
  ordinaryGen n (fun k => f k * f (n - k) * (Nat.choose n k : ℝ))

/-- `convolutionPoly n f` is the input to the `s = 1, μ = 0` rung operator
that produces `determinantPolynomial`. Reformulation of
`determinantPolynomial_eq_rungOperator` from `Basic.lean`. -/
theorem determinantPolynomial_eq_rungOperator_convolutionPoly
    (n : ℕ) (f : ℕ → ℝ) :
    determinantPolynomial n f = rungOperator n 1 0 (convolutionPoly n f) :=
  determinantPolynomial_eq_rungOperator n f

/-- The convolution polynomial is palindromic of degree `n`. -/
theorem convolutionPoly_palindromic (n : ℕ) (f : ℕ → ℝ) :
    PalindromicOfDegree n (convolutionPoly n f) := by
  refine ⟨?_, ?_⟩
  · unfold convolutionPoly ordinaryGen
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) hk_le
  · intro k hk
    unfold convolutionPoly
    rw [coeff_ordinaryGen_of_le n _ hk,
        coeff_ordinaryGen_of_le n _ (Nat.sub_le n k)]
    have hnnk : n - (n - k) = k := Nat.sub_sub_self hk
    rw [hnnk, Nat.choose_symm hk]
    ring

private theorem convolutionPoly_coeff (n : ℕ) (f : ℕ → ℝ) (k : ℕ) (hk : k ≤ n) :
    (convolutionPoly n f).coeff k = f k * f (n - k) * (Nat.choose n k : ℝ) := by
  unfold convolutionPoly
  rw [coeff_ordinaryGen_of_le n _ hk]

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

/-- **Step (3) of the paper's proof.** The convolution polynomial has only
real strictly negative zeros, given that `ordinaryGen n f` does and has
degree `n`. Paper: two applications of Lemma 1 (Hadamard closure) — once
to `F · F_rev`, once to that result with `(1+X)^n` — followed by
excluding `0` via `convolutionPoly(0) = f(0)·f(n) > 0`. -/
theorem convolutionPoly_hasOnlyRealNegativeZeros
    (n : ℕ) (f : ℕ → ℝ)
    (hdeg : HasDegree (ordinaryGen n f) n)
    (hroot : HasOnlyRealNegativeZeros (ordinaryGen n f)) :
    HasOnlyRealNegativeZeros (convolutionPoly n f) := by
  sorry

/-! ## Evaluation at 0 (paper §1 — concrete `P_n(0)` calculation) -/

/-- `K_{n,k}(0) = 0` when `k + 2 ≤ n` (so `n - k ≥ 2`). Both Pochhammer
summands of the kernel vanish at 0. -/
private theorem determinantKernel_eval_zero_of_small (n k : ℕ) (hk : k + 2 ≤ n) :
    (determinantKernel n k).eval (0 : ℝ) = 0 := by
  unfold determinantKernel
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul]
  have h1 : (pochhammer 0 (n - k)).eval (0 : ℝ) = 0 :=
    pochhammer_zero_eval_zero_of_pos (n - k) (by omega)
  have h2 : (pochhammer (-1) (n - k)).eval (0 : ℝ) = 0 :=
    pochhammer_negone_eval_zero_of_ge_two (n - k) (by omega)
  rw [h1, h2]
  ring

/-- `K_{n,n-1}(0) = (n-1)!`. The first summand vanishes; the second is
`-(n-1)! · (-1) = (n-1)!`. -/
private theorem determinantKernel_eval_zero_at_nm1 (n : ℕ) (hn : 1 ≤ n) :
    (determinantKernel n (n - 1)).eval (0 : ℝ) = (Nat.factorial (n - 1) : ℝ) := by
  unfold determinantKernel
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul]
  have h_eq : n - (n - 1) = 1 := by omega
  rw [h_eq]
  have h_p01 : (pochhammer 0 1).eval (0 : ℝ) = 0 := by
    unfold pochhammer; simp [Finset.prod_range_succ]
  have h_p1_nm1 : (pochhammer 1 (n - 1)).eval (0 : ℝ) = (Nat.factorial (n - 1) : ℝ) :=
    pochhammer_one_eval_zero (n - 1)
  have h_pn1_1 : (pochhammer (-1) 1).eval (0 : ℝ) = -1 := by
    unfold pochhammer; simp [Finset.prod_range_succ]
  rw [h_p01, h_p1_nm1, h_pn1_1]
  ring

/-- `K_{n,n}(0) = -n!`. -/
private theorem determinantKernel_eval_zero_at_n (n : ℕ) (hn : 1 ≤ n) :
    (determinantKernel n n).eval (0 : ℝ) = -(Nat.factorial n : ℝ) := by
  unfold determinantKernel
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul]
  have h_eq : n - n = 0 := Nat.sub_self n
  rw [h_eq]
  have h_p0n : (pochhammer 0 n).eval (0 : ℝ) = 0 :=
    pochhammer_zero_eval_zero_of_pos n hn
  have h_p00 : (pochhammer 0 0).eval (0 : ℝ) = 1 := by
    unfold pochhammer; simp
  have h_p1n : (pochhammer 1 n).eval (0 : ℝ) = (Nat.factorial n : ℝ) :=
    pochhammer_one_eval_zero n
  have h_pn1_0 : (pochhammer (-1) 0).eval (0 : ℝ) = 1 := by
    unfold pochhammer; simp
  rw [h_p0n, h_p00, h_p1n, h_pn1_0]
  ring

/-- **From the paper's proof of Theorem 1:**
`P_n(0) = n! · (f(1)·f(n-1) − f(0)·f(n))`. All `K_{n,k}(0)` vanish except
`k = n-1` (giving `(n-1)!`) and `k = n` (giving `-n!`). -/
theorem determinantPolynomial_eval_zero
    (n : ℕ) (f : ℕ → ℝ) (hn : 2 ≤ n) :
    (determinantPolynomial n f).eval 0 =
      (Nat.factorial n : ℝ) * (f 1 * f (n - 1) - f 0 * f n) := by
  unfold determinantPolynomial
  rw [Polynomial.eval_finset_sum]
  rw [Finset.sum_range_succ]
  have h_range : Finset.range n = Finset.range ((n - 1) + 1) := by
    congr 1; omega
  rw [h_range, Finset.sum_range_succ]
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

/-! ## Vieta inequality (paper's `e_1·e_{n-1} > e_n`) -/

/-- `Multiset.esymm` recursion under `cons`: `(a ::ₘ s).esymm (k+1) = s.esymm (k+1) + a · s.esymm k`. -/
private lemma multiset_esymm_cons (a : ℝ) (s : Multiset ℝ) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map]
  congr 1
  -- ((s.powersetCard k).map (prod ∘ cons a)).sum = a * (s.powersetCard k).map prod .sum
  rw [show (Multiset.prod ∘ Multiset.cons a) = (fun t : Multiset ℝ => a * t.prod) from by
    funext t; simp [Function.comp, Multiset.prod_cons]]
  exact Multiset.sum_map_mul_left

/-- `Multiset.esymm s 1 = s.sum`. -/
private lemma multiset_esymm_one (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_one, Multiset.map_map]
  conv_lhs => rw [show (Multiset.prod ∘ fun (a : ℝ) => ({a} : Multiset ℝ)) = id from by
    funext a; simp [Function.comp, Multiset.prod_singleton]]
  rw [Multiset.map_id]

/-- `(s.powersetCard s.card) = {s}`. -/
private lemma multiset_powersetCard_self_card (s : Multiset ℝ) :
    s.powersetCard s.card = {s} := by
  have h_card : (s.powersetCard s.card).card = 1 := by
    rw [Multiset.card_powersetCard, Nat.choose_self]
  obtain ⟨t, ht⟩ := Multiset.card_eq_one.mp h_card
  have hs_mem : s ∈ s.powersetCard s.card := by
    rw [Multiset.mem_powersetCard]; exact ⟨le_refl s, rfl⟩
  rw [ht] at hs_mem
  have hst : s = t := by
    rw [Multiset.mem_singleton] at hs_mem; exact hs_mem
  rw [ht, hst]

/-- `Multiset.esymm s s.card = s.prod`. -/
private lemma multiset_esymm_card (s : Multiset ℝ) : s.esymm s.card = s.prod := by
  unfold Multiset.esymm
  rw [multiset_powersetCard_self_card]
  simp

/-- **Paper's key inequality**: for a multiset `α` of non-negative reals,
`α.card · α.prod ≤ α.sum · α.esymm (α.card - 1)`. -/
private lemma sum_mul_esymm_pred_card_ge (α : Multiset ℝ) (hα : ∀ a ∈ α, 0 ≤ a) :
    (α.card : ℝ) * α.prod ≤ α.sum * α.esymm (α.card - 1) := by
  induction α using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha_nn : 0 ≤ a := hα a (Multiset.mem_cons_self a s)
    have hs_nn : ∀ b ∈ s, 0 ≤ b := fun b hb => hα b (Multiset.mem_cons_of_mem hb)
    have ih' := ih hs_nn
    have hs_prod : 0 ≤ s.prod := Multiset.prod_nonneg hs_nn
    have hs_sum : 0 ≤ s.sum := Multiset.sum_nonneg hs_nn
    have hs_esymm_nn : 0 ≤ s.esymm (s.card - 1) := by
      unfold Multiset.esymm
      apply Multiset.sum_nonneg
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      apply Multiset.prod_nonneg
      intro b hb
      apply hs_nn
      exact Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hb
    -- Goal: ((a ::ₘ s).card : ℝ) * (a ::ₘ s).prod ≤ (a ::ₘ s).sum * (a ::ₘ s).esymm ((a ::ₘ s).card - 1)
    rw [Multiset.card_cons, Multiset.sum_cons, Multiset.prod_cons]
    rw [show (s.card + 1 - 1 : ℕ) = s.card from by omega]
    -- Goal: ((s.card + 1) : ℝ) * (a * s.prod) ≤ (a + s.sum) * (a ::ₘ s).esymm s.card
    rcases Nat.eq_zero_or_pos s.card with hs0 | hs_pos
    · -- s = ∅
      have hs_empty : s = 0 := Multiset.card_eq_zero.mp hs0
      subst hs_empty
      simp [Multiset.esymm]
    · -- s.card ≥ 1: rewrite (a ::ₘ s).esymm s.card via cons recurrence
      have hsc : s.card = (s.card - 1) + 1 := by omega
      conv_rhs => rw [show ((a ::ₘ s).esymm s.card) = (a ::ₘ s).esymm ((s.card - 1) + 1) from by
        rw [← hsc]]
      rw [multiset_esymm_cons a s (s.card - 1)]
      rw [show s.esymm ((s.card - 1) + 1) = s.esymm s.card from by rw [← hsc]]
      rw [multiset_esymm_card s]
      -- Goal: ((s.card + 1) : ℝ) * (a * s.prod) ≤ (a + s.sum) * (s.prod + a * s.esymm (s.card - 1))
      have ih_step : a * (s.sum * s.esymm (s.card - 1)) ≥ a * ((s.card : ℝ) * s.prod) :=
        mul_le_mul_of_nonneg_left ih' ha_nn
      push_cast
      nlinarith [hs_prod, hs_sum, hs_esymm_nn, ha_nn,
                 mul_nonneg ha_nn ha_nn,
                 mul_nonneg (mul_nonneg ha_nn ha_nn) hs_esymm_nn,
                 mul_nonneg hs_sum hs_prod,
                 ih_step]

/-- For a polynomial with `HasDegree n` and `HasOnlyRealNegativeZeros`, the
key Vieta identity: coefficients are products of leading coefficient and
elementary symmetric polynomials of negated roots. -/
private theorem coeff_eq_lc_mul_esymm
    (p : ℝ[X]) (n : ℕ) (hdeg : HasDegree p n)
    (hroot : HasOnlyRealNegativeZeros p)
    (α : Multiset ℝ) (hα_card : α.card = n)
    (hα_eq : p = C p.leadingCoeff * (α.map fun a => X + C a).prod)
    (k : ℕ) (hk : k ≤ n) :
    p.coeff k = p.leadingCoeff * α.esymm (n - k) := by
  have h1 : p.coeff k = p.leadingCoeff * (α.map fun a => X + C a).prod.coeff k := by
    conv_lhs => rw [hα_eq]
    rw [Polynomial.coeff_C_mul]
  rw [h1, Multiset.prod_X_add_C_coeff α (by rw [hα_card]; exact hk), hα_card]

/-- **From the paper's proof of Theorem 1**, last paragraph:
`f(1)·f(n-1) > f(0)·f(n)`. Writing `F = C·∏(x + α_i)` with `α_i > 0`,
this becomes `e_1·e_{n-1} > e_n` for the multiset `{α₁, …, αₙ}`, which holds
because expanding `(Σαᵢ)·(Σ ∏_{r≠j} αᵢ)` contains the term `∏αᵢ = e_n`
exactly `n` times plus nonnegative cross terms (paper's argument). -/
theorem cauchy_schwarz_f1_fn1_gt_f0_fn
    (n : ℕ) (f : ℕ → ℝ) (hn : 2 ≤ n)
    (hdeg : HasDegree (ordinaryGen n f) n)
    (hroot : HasOnlyRealNegativeZeros (ordinaryGen n f)) :
    f 1 * f (n - 1) > f 0 * f n := by
  -- Extract Vieta factorization.
  obtain ⟨α, hα_card, hα_pos, hα_eq⟩ := exists_factorization_real_neg _ hroot
  rw [hdeg.2] at hα_card
  -- Leading coefficient of ordinaryGen n f is f n.
  have hlc : (ordinaryGen n f).leadingCoeff = f n := by
    rw [Polynomial.leadingCoeff, hdeg.2, coeff_ordinaryGen_of_le n f (le_refl n)]
  have hlc_ne : f n ≠ 0 := by
    intro hf0
    apply hdeg.1
    have : (ordinaryGen n f).leadingCoeff = 0 := by rw [hlc, hf0]
    exact Polynomial.leadingCoeff_eq_zero.mp this
  -- Coefficient formulas via Vieta.
  have hf_eq : ∀ k ≤ n, f k = f n * α.esymm (n - k) := by
    intro k hk
    have := coeff_eq_lc_mul_esymm (ordinaryGen n f) n hdeg hroot α hα_card hα_eq k hk
    rwa [coeff_ordinaryGen_of_le n f hk, hlc] at this
  have hf0 : f 0 = f n * α.prod := by
    rw [hf_eq 0 (Nat.zero_le n), Nat.sub_zero]
    rw [← hα_card, multiset_esymm_card]
  have hfn : f (n - 1) = f n * α.sum := by
    rw [hf_eq (n - 1) (Nat.sub_le n 1)]
    rw [show n - (n - 1) = 1 from by omega]
    rw [multiset_esymm_one]
  have hf1 : f 1 = f n * α.esymm (n - 1) := by
    rw [hf_eq 1 (by omega), show n - 1 = α.card - 1 from by omega]
  -- Substitute.
  rw [hf0, hfn, hf1]
  -- Goal: (f n * α.esymm (n - 1)) * (f n * α.sum) > (f n * α.prod) * f n
  -- = f n² * α.esymm (n - 1) * α.sum > f n² * α.prod
  have hfn_sq : (0 : ℝ) < f n ^ 2 := by
    rw [sq]; exact mul_self_pos.mpr hlc_ne
  -- Need: α.esymm (n - 1) * α.sum > α.prod.
  -- From inequality: α.sum * α.esymm (α.card - 1) ≥ α.card * α.prod = n · α.prod ≥ 2 · α.prod > α.prod (for α.prod > 0).
  have hα_nn : ∀ a ∈ α, 0 ≤ a := fun a ha => le_of_lt (hα_pos a ha)
  have hineq := sum_mul_esymm_pred_card_ge α hα_nn
  rw [hα_card] at hineq
  -- hineq : (n : ℝ) * α.prod ≤ α.sum * α.esymm (n - 1)
  have hα_prod_pos : 0 < α.prod := by
    apply Multiset.prod_pos
    intro a ha
    exact hα_pos a ha
  have hn_cast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- α.sum * α.esymm (n - 1) ≥ n * α.prod ≥ 2 * α.prod > α.prod
  have hstep1 : (2 : ℝ) * α.prod ≤ α.sum * α.esymm (n - 1) := by
    have : (2 : ℝ) * α.prod ≤ (n : ℝ) * α.prod :=
      mul_le_mul_of_nonneg_right hn_cast (le_of_lt hα_prod_pos)
    linarith
  have hstep2 : α.prod < α.sum * α.esymm (n - 1) := by
    have : α.prod < (2 : ℝ) * α.prod := by linarith
    linarith
  -- Now multiply by f n² > 0.
  have hfn_sq_real : 0 < (f n)^2 := by rw [sq]; exact mul_self_pos.mpr hlc_ne
  have := mul_lt_mul_of_pos_left hstep2 hfn_sq_real
  -- this : f n ^ 2 * α.prod < f n ^ 2 * (α.sum * α.esymm (n - 1))
  -- Want: (f n * α.esymm (n - 1)) * (f n * α.sum) > (f n * α.prod) * f n
  nlinarith [this, sq_nonneg (f n)]

/-! ## Main theorem — Theorem 1 of the paper -/

/-- **Theorem 1 of the paper**, proved using Lemmas 1, 2, 3 (axiomatized
in `Basic.lean`) plus the explicit `P_n(0)` calculation and the
`e_1·e_{n-1} > e_n` inequality. Eliminates the standalone axiom
`determinant_main_preserves_strict`; reduces the project axiom count
from 5 to 4. -/
theorem determinant_main_preserves_strict_proved
    (n : ℕ) (f : ℕ → ℝ)
    (hn : 2 ≤ n)
    (hdeg : HasDegree (ordinaryGen n f) n)
    (hroot : HasOnlyRealNegativeZeros (ordinaryGen n f)) :
    HasOnlyRealNegativeZeros (determinantPolynomial n f) := by
  set Q := convolutionPoly n f with hQ_def
  have hQ_pal : PalindromicOfDegree n Q := convolutionPoly_palindromic n f
  have hQ_root : HasOnlyRealNegativeZeros Q :=
    convolutionPoly_hasOnlyRealNegativeZeros n f hdeg hroot
  obtain ⟨m, ε, hε, hn_eq, hm⟩ :
      ∃ m ε : ℕ, (ε = 0 ∨ ε = 1) ∧ n = 2 * m + ε ∧ 1 ≤ m := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨k, 0, Or.inl rfl, by omega, ?_⟩; omega
    · refine ⟨k, 1, Or.inr rfl, by omega, ?_⟩; omega
  have h_nonpos : HasOnlyRealNonposZeros (rungOperator n 1 0 Q) :=
    pochhammer_kernel_ladder n m ε 1 0 Q hε hn_eq hm hQ_pal hQ_root (le_refl 0)
  have h_eq : determinantPolynomial n f = rungOperator n 1 0 Q :=
    determinantPolynomial_eq_rungOperator_convolutionPoly n f
  rw [← h_eq] at h_nonpos
  have hP0 : (determinantPolynomial n f).eval 0 > 0 := by
    rw [determinantPolynomial_eval_zero n f hn]
    have h_pos : 0 < f 1 * f (n - 1) - f 0 * f n := by
      have := cauchy_schwarz_f1_fn1_gt_f0_fn n f hn hdeg hroot
      linarith
    have h_fact_pos : 0 < (Nat.factorial n : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    exact mul_pos h_fact_pos h_pos
  rcases h_nonpos with hP_zero | h_realnonpos
  · rw [hP_zero] at hP0; simp at hP0
  right
  intro z hz
  obtain ⟨r, hr_le, hr_eq⟩ := h_realnonpos z hz
  refine ⟨r, ?_, hr_eq⟩
  rcases lt_or_eq_of_le hr_le with hlt | heq
  · exact hlt
  · exfalso
    have hz_eq_0 : z = 0 := by rw [hr_eq, heq]; norm_cast
    rw [hz_eq_0] at hz
    have hreal : (determinantPolynomial n f).eval 0 = 0 :=
      (isRoot_toComplex_iff_real (determinantPolynomial n f) 0).mp hz
    linarith

end GammaPochhammer
