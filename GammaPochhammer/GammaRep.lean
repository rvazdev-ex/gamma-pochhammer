import GammaPochhammer.Basic

/-!
# Proof of `gamma_representation` (Lemma 3 of the paper)

This module proves the statement currently axiomatized as
`GammaPochhammer.gamma_representation` in `Basic.lean`.  The proof
follows the paper's reciprocal-pair factorization argument.  The
theorem is named `gamma_representation_proved` so it can coexist with
the axiom; the final integration step replaces the axiom in
`Basic.lean`.

## Strategy

For palindromic `Q` of degree `n = 2m + ε` with only real negative
zeros, the γ-representation is constructed by strong induction on `n`:

* `Q = 0`: take `γ ≡ 0`.
* `Q ≠ 0`: necessarily `Q.natDegree = n` (since `Q(0) ≠ 0`).
  - `ε = 1` (odd): `Q(-1) = 0`; factor `Q = (1+X) · R`; recurse on `R`.
  - `ε = 0` (even):
    * `n = 0`: `Q = C (Q.coeff 0)`.
    * `n ≥ 2`: pick a real negative root `-α`.
      - `α = 1`: factor `(1+X)^2`.
      - `α ≠ 1`: `-α⁻¹` is also a root; factor `(X+α)(X+α⁻¹)`,
        which equals `(1+X)^2 + ζ X` with `ζ = (α-1)^2/α ≥ 0`.
      Recurse on the quotient.

For the recursion, the γ for the bigger problem is built from the γ'
for the quotient using a multiplicative coefficient operation:

* odd case: `γ = γ'` (same coefficients, applied at a larger gamma basis).
* even `α = 1`: `γⱼ = γ'ⱼ` for `j < m`, `γₘ = 0`.
* even `α ≠ 1`: γ is the coefficients of `(1 + ζ X) · gammaPolynomial (m-1) γ'`.

In each case `gammaPolynomial m γ = (1 + ζ X) · gammaPolynomial' γ'`
(with `ζ = 0` for the first two cases), preserving the
nonpositive-zero property since `(1 + ζ X)` has root `-1/ζ ≤ 0`
(or no root if `ζ = 0`).
-/

noncomputable section

open BigOperators Polynomial

namespace GammaPochhammer

/-! ## Real–complex root utilities -/

private theorem isRoot_toComplex_iff_real_basic (p : ℝ[X]) (r : ℝ) :
    (toComplex p).eval (r : ℂ) = 0 ↔ p.eval r = 0 := by
  have hcast : ((r : ℝ) : ℂ) = (algebraMap ℝ ℂ) r := rfl
  have heval : (toComplex p).eval (r : ℂ) = ((p.eval r : ℝ) : ℂ) := by
    rw [hcast]
    unfold toComplex
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rfl
  rw [heval]
  exact_mod_cast Iff.rfl

private theorem coeff_zero_ne_zero_of_neg_zeros {Q : ℝ[X]}
    (hQ : Q ≠ 0) (hroot : HasOnlyRealNegativeZeros Q) :
    Q.coeff 0 ≠ 0 := by
  intro h_coeff
  have h_eval : Q.eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]; exact h_coeff
  rcases hroot with rfl | hroot
  · exact hQ rfl
  have h_complex : (toComplex Q).eval (0 : ℂ) = 0 :=
    (isRoot_toComplex_iff_real_basic Q 0).mpr h_eval
  obtain ⟨r, hr_neg, hr_eq⟩ := hroot 0 h_complex
  have hr_zero : r = 0 := by
    have h_eq : ((r : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
      rw [← hr_eq]; simp
    exact_mod_cast h_eq
  linarith

private theorem natDegree_eq_of_palindromic_const_nonzero {Q : ℝ[X]} {n : ℕ}
    (hpal : PalindromicOfDegree n Q) (h0 : Q.coeff 0 ≠ 0) :
    Q.natDegree = n := by
  obtain ⟨h_le, h_pal⟩ := hpal
  refine le_antisymm h_le ?_
  have h_n_ne : Q.coeff n ≠ 0 := by
    have h := h_pal 0 (Nat.zero_le n)
    rw [Nat.sub_zero] at h
    rw [← h]; exact h0
  exact Polynomial.le_natDegree_of_ne_zero h_n_ne

private theorem exists_real_negative_root_basic {p : ℝ[X]}
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
  exact (isRoot_toComplex_iff_real_basic p r).mp hz

private theorem hasOnlyRealNegativeZeros_quotient {Q R : ℝ[X]} {r : ℝ}
    (hQ : HasOnlyRealNegativeZeros Q) (hQR : Q = (X - C r) * R) :
    HasOnlyRealNegativeZeros R := by
  by_cases hR : R = 0
  · left; exact hR
  rcases hQ with hQ0 | hQ
  · rw [hQ0] at hQR
    rcases mul_eq_zero.mp hQR.symm with h | h
    · exact absurd h (X_sub_C_ne_zero r)
    · exact absurd h hR
  right
  intro z hz
  apply hQ
  have hmul : toComplex Q = toComplex (X - C r) * toComplex R := by
    rw [hQR]; simp [toComplex, Polynomial.map_mul]
  rw [hmul, Polynomial.eval_mul, hz, mul_zero]

/-! ## Reflect equivalent of palindromic -/

private theorem reflect_eq_self_of_palindromic {Q : ℝ[X]} {n : ℕ}
    (hpal : PalindromicOfDegree n Q) : Polynomial.reflect n Q = Q := by
  obtain ⟨h_le, h_sym⟩ := hpal
  ext k
  rw [Polynomial.coeff_reflect]
  by_cases h_le_k : k ≤ n
  · rw [Polynomial.revAt_le h_le_k]
    exact (h_sym k h_le_k).symm
  · push_neg at h_le_k
    rw [Polynomial.revAt_eq_self_of_lt h_le_k]

private theorem palindromic_of_reflect_eq {R : ℝ[X]} {n : ℕ}
    (h_nd : R.natDegree ≤ n) (h_refl : Polynomial.reflect n R = R) :
    PalindromicOfDegree n R := by
  refine ⟨h_nd, ?_⟩
  intro k hk
  have h := congr_arg (fun p => Polynomial.coeff p k) h_refl
  simp only at h
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le hk] at h
  exact h.symm

/-! ## gammaBasis identities -/

private lemma one_add_X_mul_gammaBasis_pred (n j : ℕ) (h : 2 * j + 1 ≤ n) :
    (1 + X : ℝ[X]) * gammaBasis (n - 1) j = gammaBasis n j := by
  unfold gammaBasis
  have h1 : n - 1 - 2 * j + 1 = n - 2 * j := by omega
  calc
    (1 + X : ℝ[X]) * (X ^ j * (1 + X) ^ (n - 1 - 2 * j))
        = X ^ j * ((1 + X) ^ (n - 1 - 2 * j) * (1 + X)) := by ring
    _ = X ^ j * (1 + X) ^ (n - 1 - 2 * j + 1) := by rw [← pow_succ]
    _ = X ^ j * (1 + X) ^ (n - 2 * j) := by rw [h1]

private lemma one_add_X_sq_mul_gammaBasis_pred2 (n j : ℕ) (h : 2 * j + 2 ≤ n) :
    ((1 + X : ℝ[X]) ^ 2) * gammaBasis (n - 2) j = gammaBasis n j := by
  unfold gammaBasis
  have h1 : n - 2 - 2 * j + 2 = n - 2 * j := by omega
  calc
    ((1 + X : ℝ[X]) ^ 2) * (X ^ j * (1 + X) ^ (n - 2 - 2 * j))
        = X ^ j * ((1 + X) ^ (n - 2 - 2 * j) * (1 + X) ^ 2) := by ring
    _ = X ^ j * (1 + X) ^ (n - 2 - 2 * j + 2) := by rw [← pow_add]
    _ = X ^ j * (1 + X) ^ (n - 2 * j) := by rw [h1]

private lemma X_mul_gammaBasis_pred2 (n j : ℕ) (h : 2 * (j + 1) ≤ n) :
    (X : ℝ[X]) * gammaBasis (n - 2) j = gammaBasis n (j + 1) := by
  unfold gammaBasis
  have h1 : n - 2 - 2 * j = n - 2 * (j + 1) := by omega
  calc
    (X : ℝ[X]) * (X ^ j * (1 + X) ^ (n - 2 - 2 * j))
        = X ^ (j + 1) * (1 + X) ^ (n - 2 - 2 * j) := by ring
    _ = X ^ (j + 1) * (1 + X) ^ (n - 2 * (j + 1)) := by rw [h1]

/-! ## Palindromicity of the factors -/

private theorem one_add_X_palindromic : PalindromicOfDegree 1 ((1 : ℝ[X]) + X) := by
  refine ⟨?_, ?_⟩
  · rw [add_comm]; rw [Polynomial.natDegree_X_add_C]
  · intro k hk
    interval_cases k
    · simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_one]
    · show Polynomial.coeff ((1 : ℝ[X]) + X) 1 = Polynomial.coeff ((1 : ℝ[X]) + X) 0
      simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_one]

private theorem one_add_X_natDegree : ((1 : ℝ[X]) + X).natDegree = 1 := by
  rw [add_comm]; rw [Polynomial.natDegree_X_add_C]

private theorem one_add_X_ne_zero : ((1 : ℝ[X]) + X) ≠ 0 := by
  intro h
  have : ((1 : ℝ[X]) + X).natDegree = 0 := by rw [h]; simp
  rw [one_add_X_natDegree] at this
  omega

private theorem quadratic_factor_natDegree (ζ : ℝ) :
    ((1 + X : ℝ[X]) ^ 2 + C ζ * X).natDegree = 2 := by
  have h_expand : (1 + X : ℝ[X]) ^ 2 + C ζ * X = C 1 + C (2 + ζ) * X + C 1 * X ^ 2 := by
    ring
  rw [h_expand]
  -- The polynomial is `C 1 + C (2 + ζ) * X + C 1 * X^2`.
  -- Its natDegree is 2 because the coefficient of X^2 is 1 ≠ 0.
  have h_coeff2 : (C 1 + C (2 + ζ) * X + C 1 * X ^ 2 : ℝ[X]).coeff 2 = 1 := by
    simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_X_pow]
  have h_coeff_gt : ∀ k > 2,
      (C 1 + C (2 + ζ) * X + C 1 * X ^ 2 : ℝ[X]).coeff k = 0 := by
    intro k hk
    simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_X_pow]
    refine ⟨?_, ?_, ?_⟩ <;> omega
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    exact h_coeff_gt k hk
  · exact Polynomial.le_natDegree_of_ne_zero (by rw [h_coeff2]; norm_num)

private theorem quadratic_factor_palindromic (ζ : ℝ) :
    PalindromicOfDegree 2 ((1 + X : ℝ[X]) ^ 2 + C ζ * X) := by
  have h_expand : (1 + X : ℝ[X]) ^ 2 + C ζ * X = C 1 + C (2 + ζ) * X + C 1 * X ^ 2 := by
    ring
  have h_coeff : ∀ k,
      ((1 + X : ℝ[X]) ^ 2 + C ζ * X).coeff k =
        if k = 0 then 1 else if k = 1 then 2 + ζ else if k = 2 then 1 else 0 := by
    intro k
    rw [h_expand]
    simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, Polynomial.coeff_X_pow]
    by_cases h0 : k = 0
    · subst h0; simp
    · simp [h0]
      by_cases h1 : k = 1
      · subst h1; simp
      · simp [h1]
        by_cases h2 : k = 2
        · subst h2; simp
        · simp [h2]
  refine ⟨by rw [quadratic_factor_natDegree], ?_⟩
  intro k hk
  interval_cases k
  · rw [h_coeff 0, h_coeff 2]; simp
  · rfl
  · rw [h_coeff 2, h_coeff 0]; simp

private theorem quadratic_factor_ne_zero (ζ : ℝ) :
    ((1 + X : ℝ[X]) ^ 2 + C ζ * X) ≠ 0 := by
  intro h
  have hd := quadratic_factor_natDegree ζ
  rw [h] at hd
  simp at hd

/-! ## Palindromic factorization -/

private theorem palindromic_factor_mul
    {Q P R : ℝ[X]} {n d : ℕ}
    (hpalQ : PalindromicOfDegree n Q) (hQdeg : Q.natDegree = n)
    (hpalP : PalindromicOfDegree d P) (hPdeg : P.natDegree = d)
    (hP_ne : P ≠ 0)
    (hd_le_n : d ≤ n) (hQR : Q = P * R) :
    PalindromicOfDegree (n - d) R ∧ R.natDegree = n - d := by
  by_cases hR : R = 0
  · -- R = 0 case: forces Q = 0, n = 0, d = 0.
    subst hR
    rw [mul_zero] at hQR
    rw [hQR] at hQdeg
    simp at hQdeg
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp
    · intro k hk
      simp
    · simp
  have hR_natDeg : R.natDegree = n - d := by
    have h_eq : Q.natDegree = P.natDegree + R.natDegree := by
      rw [hQR, Polynomial.natDegree_mul hP_ne hR]
    rw [hQdeg, hPdeg] at h_eq
    omega
  have h_refl_Q : Polynomial.reflect n Q = Q := reflect_eq_self_of_palindromic hpalQ
  have h_refl_P : Polynomial.reflect d P = P := reflect_eq_self_of_palindromic hpalP
  have h_eq : n = d + (n - d) := by omega
  have h_refl_mul :
      Polynomial.reflect n Q =
        Polynomial.reflect d P * Polynomial.reflect (n - d) R := by
    conv_lhs => rw [h_eq, hQR]
    refine Polynomial.reflect_mul _ _ ?_ ?_
    · rw [hPdeg]
    · rw [hR_natDeg]
  rw [h_refl_P, h_refl_Q, hQR] at h_refl_mul
  have hR_refl : Polynomial.reflect (n - d) R = R :=
    (mul_left_cancel₀ hP_ne h_refl_mul).symm
  exact ⟨palindromic_of_reflect_eq (by rw [hR_natDeg]) hR_refl, hR_natDeg⟩

/-! ## Palindromic evaluation at `-1` and root inversion -/

private theorem palindromic_eval_neg_one {Q : ℝ[X]} {n : ℕ}
    (hpal : PalindromicOfDegree n Q) :
    Q.eval (-1 : ℝ) = (-1 : ℝ) ^ n * Q.eval (-1 : ℝ) := by
  obtain ⟨hnd, hsym⟩ := hpal
  have hsum : Q.eval (-1 : ℝ) =
      ∑ k ∈ Finset.range (n + 1), Q.coeff k * (-1 : ℝ) ^ k :=
    Polynomial.eval_eq_sum_range' (by omega) _
  conv_lhs => rw [hsum]
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_nbij' (fun k => n - k) (fun k => n - k)
  · intro k hk
    rw [Finset.mem_range] at hk; rw [Finset.mem_range]; omega
  · intro k hk
    rw [Finset.mem_range] at hk; rw [Finset.mem_range]; omega
  · intro k hk
    rw [Finset.mem_range] at hk; show n - (n - k) = k; omega
  · intro k hk
    rw [Finset.mem_range] at hk; show n - (n - k) = k; omega
  · intro k hk
    rw [Finset.mem_range] at hk
    have hk_le : k ≤ n := by omega
    rw [hsym k hk_le]
    have h_pow : (-1 : ℝ) ^ n * (-1 : ℝ) ^ k = (-1 : ℝ) ^ (n - k) := by
      rw [← pow_add]
      rw [show n + k = 2 * k + (n - k) from by omega, pow_add, pow_mul]
      rw [show ((-1 : ℝ)) ^ 2 = 1 from by norm_num, one_pow, one_mul]
    calc
      (-1 : ℝ) ^ n * (Q.coeff (n - k) * (-1 : ℝ) ^ k)
          = Q.coeff (n - k) * ((-1 : ℝ) ^ n * (-1 : ℝ) ^ k) := by ring
      _ = Q.coeff (n - k) * (-1 : ℝ) ^ (n - k) := by rw [h_pow]

private theorem palindromic_eval_neg_one_zero_of_odd {Q : ℝ[X]} {n : ℕ}
    (hpal : PalindromicOfDegree n Q) (hodd : Odd n) :
    Q.eval (-1 : ℝ) = 0 := by
  have h := palindromic_eval_neg_one hpal
  have hp : (-1 : ℝ) ^ n = -1 := Odd.neg_one_pow hodd
  rw [hp] at h
  linarith

private theorem palindromic_root_inversion {Q : ℝ[X]} {n : ℕ}
    (hpal : PalindromicOfDegree n Q)
    {α : ℝ} (hα : α ≠ 0) (hroot : Q.eval (-α) = 0) :
    Q.eval (-α⁻¹) = 0 := by
  obtain ⟨hnd, hsym⟩ := hpal
  have hα_neg_ne : (-α : ℝ) ≠ 0 := neg_ne_zero.mpr hα
  have h_recip : (-α⁻¹ : ℝ) * (-α) = 1 := by field_simp
  have h_key : Q.eval (-α⁻¹) * (-α) ^ n = Q.eval (-α) := by
    have h_eval_inv : Q.eval (-α⁻¹) =
        ∑ k ∈ Finset.range (n + 1), Q.coeff k * (-α⁻¹) ^ k :=
      Polynomial.eval_eq_sum_range' (by omega) _
    have h_eval_α : Q.eval (-α) =
        ∑ k ∈ Finset.range (n + 1), Q.coeff k * (-α) ^ k :=
      Polynomial.eval_eq_sum_range' (by omega) _
    rw [h_eval_inv, h_eval_α, Finset.sum_mul]
    apply Finset.sum_nbij' (fun k => n - k) (fun k => n - k)
    · intro k hk
      rw [Finset.mem_range] at hk; rw [Finset.mem_range]; omega
    · intro k hk
      rw [Finset.mem_range] at hk; rw [Finset.mem_range]; omega
    · intro k hk
      rw [Finset.mem_range] at hk; show n - (n - k) = k; omega
    · intro k hk
      rw [Finset.mem_range] at hk; show n - (n - k) = k; omega
    · intro k hk
      rw [Finset.mem_range] at hk
      have hk_le : k ≤ n := by omega
      rw [← hsym k hk_le]
      have h_pow : (-α⁻¹ : ℝ) ^ k * (-α) ^ n = (-α) ^ (n - k) := by
        have h_id : (-α⁻¹ : ℝ) ^ k * (-α) ^ k = 1 := by
          rw [← mul_pow, h_recip, one_pow]
        calc
          (-α⁻¹ : ℝ) ^ k * (-α) ^ n
              = (-α⁻¹) ^ k * (-α) ^ ((n - k) + k) := by
                rw [show (n - k) + k = n from by omega]
          _ = (-α⁻¹) ^ k * ((-α) ^ (n - k) * (-α) ^ k) := by rw [pow_add]
          _ = ((-α⁻¹) ^ k * (-α) ^ k) * (-α) ^ (n - k) := by ring
          _ = 1 * (-α) ^ (n - k) := by rw [h_id]
          _ = (-α) ^ (n - k) := by ring
      calc
        Q.coeff k * (-α⁻¹) ^ k * (-α) ^ n
            = Q.coeff k * ((-α⁻¹) ^ k * (-α) ^ n) := by ring
        _ = Q.coeff k * (-α) ^ (n - k) := by rw [h_pow]
  rw [hroot] at h_key
  have h_pow_ne : ((-α : ℝ)) ^ n ≠ 0 := pow_ne_zero _ hα_neg_ne
  rcases mul_eq_zero.mp h_key with h | h
  · exact h
  · exact absurd h h_pow_ne

/-! ## The polynomial `1 + ζ X` for `ζ ≥ 0` -/

private theorem one_add_C_mul_X_hasOnlyRealNonposZeros {ζ : ℝ} (hζ : 0 ≤ ζ) :
    HasOnlyRealNonposZeros ((1 : ℝ[X]) + C ζ * X) := by
  by_cases hζ0 : ζ = 0
  · subst hζ0
    right
    intro z hz
    have h_eq : ((1 : ℝ[X]) + C (0 : ℝ) * X) = 1 := by simp
    rw [h_eq] at hz
    have h_complex : toComplex (1 : ℝ[X]) = (1 : ℂ[X]) := by
      unfold toComplex; simp
    rw [h_complex] at hz
    simp at hz
  · have hζ_pos : 0 < ζ := lt_of_le_of_ne hζ (Ne.symm hζ0)
    right
    intro z hz
    have h_complex_map : toComplex ((1 : ℝ[X]) + C ζ * X) = 1 + C (ζ : ℂ) * X := by
      unfold toComplex
      rw [Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul,
          Polynomial.map_C, Polynomial.map_X]
      rfl
    rw [h_complex_map] at hz
    simp at hz
    -- hz : 1 + ζ * z = 0, so z = -1/ζ
    have hζ_C_ne : (ζ : ℂ) ≠ 0 := by exact_mod_cast hζ0
    have h_z_eq : z = -(ζ : ℂ)⁻¹ := by
      have h1 : (ζ : ℂ) * z = -1 := by linarith
      have h2 : z = -1 / (ζ : ℂ) := by
        rw [eq_div_iff hζ_C_ne]
        linear_combination h1
      rw [h2]
      rw [neg_div, one_div]
    refine ⟨-(ζ : ℝ)⁻¹, ?_, ?_⟩
    · have : (0 : ℝ) < (ζ : ℝ)⁻¹ := inv_pos.mpr hζ_pos
      linarith
    · rw [h_z_eq]
      push_cast
      ring

/-! ## Main theorem -/

theorem gamma_representation_proved
    (n m ε : ℕ) (hε : ε = 0 ∨ ε = 1) (hn : n = 2 * m + ε)
    (Q : ℝ[X]) (hpal : PalindromicOfDegree n Q)
    (hroot : HasOnlyRealNegativeZeros Q) :
    ∃ γ : ℕ → ℝ,
      IsGammaExpansion n m Q γ ∧
      HasOnlyRealNonposZeros (gammaPolynomial m γ) := by
  revert hroot hpal Q hn hε ε m
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m ε hε hn Q hpal hroot
    by_cases hQ : Q = 0
    · subst hQ
      refine ⟨fun _ => 0, ?_, ?_⟩
      · unfold IsGammaExpansion; simp
      · left; unfold gammaPolynomial; simp
    have hcoeff0 : Q.coeff 0 ≠ 0 := coeff_zero_ne_zero_of_neg_zeros hQ hroot
    have hQ_deg : Q.natDegree = n :=
      natDegree_eq_of_palindromic_const_nonzero hpal hcoeff0
    rcases hε with hε0 | hε1
    · -- ε = 0
      subst hε0
      have hn_eq : n = 2 * m := by omega
      rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
      · -- m = 0, so n = 0
        subst hm0
        simp at hn_eq
        subst hn_eq
        have hQ_const : Q = C (Q.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero hQ_deg
        refine ⟨fun j => if j = 0 then Q.coeff 0 else 0, ?_, ?_⟩
        · unfold IsGammaExpansion gammaBasis
          rw [hQ_const]; simp
        · right
          intro z hz
          unfold gammaPolynomial at hz
          simp only [Finset.range_one, Finset.sum_singleton, if_pos rfl, pow_zero,
            mul_one] at hz
          have h_complex : toComplex (C (Q.coeff 0)) = C (Q.coeff 0 : ℂ) := by
            unfold toComplex; rw [Polynomial.map_C]; rfl
          rw [h_complex] at hz
          simp at hz
          exact absurd (by exact_mod_cast hz) hcoeff0
      · -- m ≥ 1, n ≥ 2
        have hm : 1 ≤ m := hm_pos
        have hn_ge : 2 ≤ n := by omega
        obtain ⟨negα, h_negα_neg, h_negα_root⟩ :=
          exists_real_negative_root_basic hroot (by omega : 1 ≤ Q.natDegree)
        set α : ℝ := -negα with hα_def
        have hα_pos : 0 < α := by rw [hα_def]; linarith
        have hα_ne : α ≠ 0 := ne_of_gt hα_pos
        have h_α_root : Q.eval (-α) = 0 := by
          rw [hα_def]; simpa using h_negα_root
        by_cases hα1 : α = 1
        · -- α = 1: factor out (1 + X)^2
          subst hα1
          have h_neg1_root : Q.eval (-1 : ℝ) = 0 := h_α_root
          obtain ⟨R₁, hR₁⟩ : (X - C (-1 : ℝ)) ∣ Q :=
            (Polynomial.dvd_iff_isRoot (a := -1)).mpr h_neg1_root
          have hR₁_eq : Q = ((1 : ℝ[X]) + X) * R₁ := by
            rw [hR₁]; rw [Polynomial.C_neg]; ring
          obtain ⟨hR₁_pal, hR₁_deg⟩ :=
            palindromic_factor_mul hpal hQ_deg one_add_X_palindromic
              one_add_X_natDegree one_add_X_ne_zero (by omega) hR₁_eq
          have hR₁_root : HasOnlyRealNegativeZeros R₁ := by
            apply hasOnlyRealNegativeZeros_quotient hroot
            rw [hR₁_eq]
            rw [show ((1 : ℝ[X]) + X) = X - C (-1 : ℝ) from by
              rw [Polynomial.C_neg]; ring]
          have hR₁_odd : Odd (n - 1) := by
            rcases Nat.even_or_odd (n - 1) with h | h
            · exfalso
              obtain ⟨k, hk⟩ := h
              omega
            · exact h
          have h_R₁_neg1 : R₁.eval (-1 : ℝ) = 0 :=
            palindromic_eval_neg_one_zero_of_odd hR₁_pal hR₁_odd
          obtain ⟨S, hS⟩ : (X - C (-1 : ℝ)) ∣ R₁ :=
            (Polynomial.dvd_iff_isRoot (a := -1)).mpr h_R₁_neg1
          have hS_eq : R₁ = ((1 : ℝ[X]) + X) * S := by
            rw [hS]; rw [Polynomial.C_neg]; ring
          have hQ_S : Q = ((1 + X : ℝ[X]) ^ 2) * S := by
            rw [hR₁_eq, hS_eq]; ring
          have hQ_S_pair : Q = (((1 + X : ℝ[X]) ^ 2) + C 0 * X) * S := by
            rw [hQ_S]; simp
          obtain ⟨hS_pal, hS_deg⟩ :=
            palindromic_factor_mul hpal hQ_deg (quadratic_factor_palindromic 0)
              (quadratic_factor_natDegree 0) (quadratic_factor_ne_zero 0)
              (by omega) hQ_S_pair
          have hS_root : HasOnlyRealNegativeZeros S := by
            apply hasOnlyRealNegativeZeros_quotient hR₁_root
            rw [hS_eq]
            rw [show ((1 : ℝ[X]) + X) = X - C (-1 : ℝ) from by
              rw [Polynomial.C_neg]; ring]
          have hn_2 : n - 2 = 2 * (m - 1) + 0 := by omega
          have h_lt : n - 2 < n := by omega
          obtain ⟨γ', hγ'_exp, hγ'_root⟩ :=
            ih (n - 2) h_lt (m - 1) 0 (Or.inl rfl) hn_2 S hS_pal hS_root
          refine ⟨fun j => if j ≤ m - 1 then γ' j else 0, ?_, ?_⟩
          · unfold IsGammaExpansion at hγ'_exp ⊢
            rw [hQ_S, hγ'_exp, Finset.mul_sum]
            -- LHS = ∑_{j ∈ range m} (1+X)^2 * (C γ'_j * gammaBasis (n-2) j)
            -- RHS = ∑_{j ∈ range (m+1)} C (γ_j) * gammaBasis n j
            -- where γ_j = γ'_j for j ≤ m-1, γ_m = 0.
            have h_m_eq : m + 1 = (m - 1 + 1) + 1 := by omega
            rw [show Finset.range (m + 1) = Finset.range ((m - 1 + 1) + 1) from by
              rw [h_m_eq]]
            rw [Finset.sum_range_succ]
            have h_top_zero :
                C (if (m - 1 + 1) ≤ m - 1 then γ' (m - 1 + 1) else 0) *
                  gammaBasis n (m - 1 + 1) = 0 := by
              rw [if_neg (by omega : ¬ (m - 1 + 1) ≤ m - 1)]
              simp
            rw [h_top_zero, add_zero]
            rw [show (m - 1 + 1) = m from by omega]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mem_range] at hj
            have hj_le : j ≤ m - 1 := Nat.lt_succ_iff.mp hj
            have h2j : 2 * j + 2 ≤ n := by omega
            rw [if_pos hj_le]
            rw [show ((1 + X : ℝ[X]) ^ 2) * (C (γ' j) * gammaBasis (n - 2) j) =
                C (γ' j) * ((1 + X : ℝ[X]) ^ 2 * gammaBasis (n - 2) j) from by ring]
            rw [one_add_X_sq_mul_gammaBasis_pred2 n j h2j]
          · -- gammaPolynomial m γ has only real nonpos zeros.
            have h_poly_eq :
                gammaPolynomial m (fun j => if j ≤ m - 1 then γ' j else 0) =
                  gammaPolynomial (m - 1) γ' := by
              unfold gammaPolynomial
              rw [show m + 1 = ((m - 1) + 1) + 1 from by omega]
              rw [Finset.sum_range_succ]
              have h_top :
                  C (if ((m - 1) + 1) ≤ m - 1 then γ' ((m - 1) + 1) else 0) *
                    X ^ ((m - 1) + 1) = 0 := by
                rw [if_neg (by omega : ¬ ((m - 1) + 1) ≤ m - 1)]
                simp
              rw [h_top, add_zero]
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.mem_range] at hj
              have hj_le : j ≤ m - 1 := Nat.lt_succ_iff.mp hj
              rw [if_pos hj_le]
            rw [h_poly_eq]
            exact hγ'_root
        · -- α ≠ 1: factor out (X + α)(X + α⁻¹)
          have hα_inv_root : Q.eval (-α⁻¹ : ℝ) = 0 :=
            palindromic_root_inversion hpal hα_ne h_α_root
          obtain ⟨R₁, hR₁⟩ : (X - C (-α : ℝ)) ∣ Q :=
            (Polynomial.dvd_iff_isRoot (a := -α)).mpr h_α_root
          have hR₁_eq : Q = (X + C α : ℝ[X]) * R₁ := by
            rw [hR₁]; rw [Polynomial.C_neg]; ring
          -- R₁(-α⁻¹) = 0 since (X + C α) at -α⁻¹ is α - α⁻¹ ≠ 0.
          have h_eval_factor : ((X + C α : ℝ[X]).eval (-α⁻¹ : ℝ)) = α - α⁻¹ := by
            simp [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
            ring
          have h_α_minus_inv_ne : α - α⁻¹ ≠ 0 := by
            intro h_eq
            have h_α_eq_inv : α = α⁻¹ := by linarith
            have h_α_sq : α * α = 1 := by
              have : α * α⁻¹ = 1 := mul_inv_cancel₀ hα_ne
              rw [← h_α_eq_inv] at this
              exact this
            have h_α_sq' : α ^ 2 = 1 := by rw [sq]; exact h_α_sq
            -- α > 0 and α² = 1 implies α = 1 or α = -1; α > 0 excludes α = -1.
            have h_or : α = 1 ∨ α = -1 := by
              have h_factor : (α - 1) * (α + 1) = 0 := by ring_nf; linarith
              rcases mul_eq_zero.mp h_factor with h | h
              · left; linarith
              · right; linarith
            rcases h_or with h | h
            · exact hα1 h
            · linarith
          have hR₁_root : R₁.eval (-α⁻¹ : ℝ) = 0 := by
            have h_Q_eval := hα_inv_root
            rw [hR₁_eq, Polynomial.eval_mul, h_eval_factor] at h_Q_eval
            rcases mul_eq_zero.mp h_Q_eval with h | h
            · exact absurd h h_α_minus_inv_ne
            · exact h
          obtain ⟨S, hS⟩ : (X - C (-α⁻¹ : ℝ)) ∣ R₁ :=
            (Polynomial.dvd_iff_isRoot (a := -α⁻¹)).mpr hR₁_root
          have hS_eq : R₁ = (X + C α⁻¹ : ℝ[X]) * S := by
            rw [hS]; rw [Polynomial.C_neg]; ring
          -- (X+α)(X+α⁻¹) = (1+X)^2 + (α + α⁻¹ - 2) X
          set ζ : ℝ := α + α⁻¹ - 2 with hζ_def
          have hζ_nn : 0 ≤ ζ := by
            have h_eq : ζ = (α - 1)^2 / α := by
              rw [hζ_def]; field_simp; ring
            rw [h_eq]
            exact div_nonneg (sq_nonneg _) (le_of_lt hα_pos)
          have h_quad_eq :
              ((X + C α : ℝ[X]) * (X + C α⁻¹)) = (1 + X)^2 + C ζ * X := by
            have h_α_inv_α : α * α⁻¹ = 1 := mul_inv_cancel₀ hα_ne
            have h_CC : (C α : ℝ[X]) * (C α⁻¹) = C 1 := by
              rw [← Polynomial.C_mul, h_α_inv_α]
            calc
              (X + C α : ℝ[X]) * (X + C α⁻¹)
                  = X^2 + (C α + C α⁻¹) * X + (C α * C α⁻¹) := by ring
              _ = X^2 + C (α + α⁻¹) * X + C 1 := by
                    rw [← Polynomial.C_add, h_CC]
              _ = X^2 + C (ζ + 2) * X + C 1 := by
                    rw [show α + α⁻¹ = ζ + 2 from by rw [hζ_def]; ring]
              _ = (1 + X)^2 + C ζ * X := by
                    rw [Polynomial.C_add, Polynomial.C_one]
                    ring
          have hQ_pair_eq : Q = ((1 + X : ℝ[X])^2 + C ζ * X) * S := by
            rw [hR₁_eq, hS_eq, ← h_quad_eq]; ring
          obtain ⟨hS_pal, hS_deg⟩ :=
            palindromic_factor_mul hpal hQ_deg (quadratic_factor_palindromic ζ)
              (quadratic_factor_natDegree ζ) (quadratic_factor_ne_zero ζ)
              (by omega) hQ_pair_eq
          have hS_root : HasOnlyRealNegativeZeros S := by
            have hR₁_neg : HasOnlyRealNegativeZeros R₁ := by
              apply hasOnlyRealNegativeZeros_quotient hroot
              rw [hR₁_eq]
              rw [show (X + C α : ℝ[X]) = X - C (-α) from by
                rw [Polynomial.C_neg]; ring]
            apply hasOnlyRealNegativeZeros_quotient hR₁_neg
            rw [hS_eq]
            rw [show (X + C α⁻¹ : ℝ[X]) = X - C (-α⁻¹) from by
              rw [Polynomial.C_neg]; ring]
          have hn_2 : n - 2 = 2 * (m - 1) + 0 := by omega
          have h_lt : n - 2 < n := by omega
          obtain ⟨γ', hγ'_exp, hγ'_root⟩ :=
            ih (n - 2) h_lt (m - 1) 0 (Or.inl rfl) hn_2 S hS_pal hS_root
          -- Define γ explicitly via the recursive formula.
          -- γ̃ truncates γ' to indices ≤ m - 1; γ adds the ζ-shifted term.
          refine ⟨fun j =>
              (if j ≤ m - 1 then γ' j else 0) +
              (if 0 < j then ζ * (if j - 1 ≤ m - 1 then γ' (j - 1) else 0) else 0),
            ?_, ?_⟩
          · -- IsGammaExpansion proof.
            unfold IsGammaExpansion at hγ'_exp ⊢
            rw [hQ_pair_eq, hγ'_exp, add_mul, Finset.mul_sum, Finset.mul_sum]
            -- Rewrite each summand on LHS using gammaBasis identities.
            have h_sq : ∀ j ∈ Finset.range m,
                ((1 + X : ℝ[X]) ^ 2) * (C (γ' j) * gammaBasis (n - 2) j) =
                  C (γ' j) * gammaBasis n j := by
              intro j hj
              rw [Finset.mem_range] at hj
              have h2j : 2 * j + 2 ≤ n := by omega
              calc ((1 + X : ℝ[X]) ^ 2) * (C (γ' j) * gammaBasis (n - 2) j)
                  = C (γ' j) * ((1 + X : ℝ[X]) ^ 2 * gammaBasis (n - 2) j) := by ring
                _ = C (γ' j) * gammaBasis n j := by
                  rw [one_add_X_sq_mul_gammaBasis_pred2 n j h2j]
            have h_X : ∀ j ∈ Finset.range m,
                (C ζ * X : ℝ[X]) * (C (γ' j) * gammaBasis (n - 2) j) =
                  C (ζ * γ' j) * gammaBasis n (j + 1) := by
              intro j hj
              rw [Finset.mem_range] at hj
              have h2j1 : 2 * (j + 1) ≤ n := by omega
              calc (C ζ * X : ℝ[X]) * (C (γ' j) * gammaBasis (n - 2) j)
                  = C (ζ * γ' j) * (X * gammaBasis (n - 2) j) := by
                    rw [Polynomial.C_mul]; ring
                _ = C (ζ * γ' j) * gammaBasis n (j + 1) := by
                    rw [X_mul_gammaBasis_pred2 n j h2j1]
            rw [Finset.sum_congr rfl h_sq, Finset.sum_congr rfl h_X]
            -- LHS: Σ_{j ∈ range m} C γ'_j * gB n j + Σ_{j ∈ range m} C (ζ γ'_j) * gB n (j+1)
            -- Reindex second sum.
            rw [show (∑ j ∈ Finset.range m, C (ζ * γ' j) * gammaBasis n (j + 1)) =
                (∑ k ∈ Finset.Ico 1 (m + 1), C (ζ * γ' (k - 1)) * gammaBasis n k) from by
              apply Finset.sum_nbij' (fun j _ => j + 1) (fun k _ => k - 1)
              · intro j hj
                rw [Finset.mem_range] at hj; rw [Finset.mem_Ico]; omega
              · intro k hk
                rw [Finset.mem_Ico] at hk; rw [Finset.mem_range]; omega
              · intro j _; rfl
              · intro k hk
                rw [Finset.mem_Ico] at hk; show k - 1 + 1 = k; omega
              · intro j hj
                rw [Finset.mem_range] at hj
                show C (ζ * γ' j) * gammaBasis n (j + 1) =
                    C (ζ * γ' (j + 1 - 1)) * gammaBasis n (j + 1)
                rw [show j + 1 - 1 = j from by omega]]
            -- Now both LHS pieces are sums over range (m+1) (after extending first).
            rw [show (∑ j ∈ Finset.range m, C (γ' j) * gammaBasis n j) =
                (∑ j ∈ Finset.range (m + 1),
                  C (if j ≤ m - 1 then γ' j else 0) * gammaBasis n j) from by
              rw [show m + 1 = m - 1 + 1 + 1 from by omega]
              rw [Finset.sum_range_succ]
              rw [show m - 1 + 1 = m from by omega]
              have h_top :
                  C (if m ≤ m - 1 then γ' m else 0) * gammaBasis n m = 0 := by
                rw [if_neg (by omega : ¬ m ≤ m - 1)]; simp
              rw [h_top, add_zero]
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.mem_range] at hj
              have hj_le : j ≤ m - 1 := Nat.lt_succ_iff.mp hj
              rw [if_pos hj_le]]
            rw [show (∑ k ∈ Finset.Ico 1 (m + 1), C (ζ * γ' (k - 1)) * gammaBasis n k) =
                (∑ k ∈ Finset.range (m + 1),
                  C (if 0 < k then ζ * (if k - 1 ≤ m - 1 then γ' (k - 1) else 0) else 0) *
                  gammaBasis n k) from by
              rw [show Finset.range (m + 1) =
                  insert 0 (Finset.Ico 1 (m + 1)) from by
                ext x
                simp [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
                omega]
              rw [Finset.sum_insert (by simp [Finset.mem_Ico])]
              rw [show C (if 0 < (0 : ℕ) then
                    ζ * (if (0 : ℕ) - 1 ≤ m - 1 then γ' ((0 : ℕ) - 1) else 0) else 0)
                  * gammaBasis n 0 = 0 from by simp]
              rw [zero_add]
              apply Finset.sum_congr rfl
              intro k hk
              rw [Finset.mem_Ico] at hk
              have hk_pos : 0 < k := hk.1
              have hk_m : k - 1 ≤ m - 1 := by omega
              rw [if_pos hk_pos, if_pos hk_m]]
            -- Combine the two sums.
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [← Polynomial.C_add]
            ring_nf
          · -- gammaPolynomial m γ has only real nonpos zeros.
            have h_poly_eq :
                gammaPolynomial m
                  (fun j => (if j ≤ m - 1 then γ' j else 0) +
                    (if 0 < j then
                      ζ * (if j - 1 ≤ m - 1 then γ' (j - 1) else 0) else 0)) =
                  ((1 : ℝ[X]) + C ζ * X) * gammaPolynomial (m - 1) γ' := by
              unfold gammaPolynomial
              rw [show ((1 : ℝ[X]) + C ζ * X) *
                  ∑ j ∈ Finset.range (m - 1 + 1), C (γ' j) * X ^ j =
                  ∑ j ∈ Finset.range (m - 1 + 1), C (γ' j) * X ^ j +
                  (C ζ * X) *
                    ∑ j ∈ Finset.range (m - 1 + 1), C (γ' j) * X ^ j from by ring]
              -- RHS = gP_{m-1} γ' + Cζ X · gP_{m-1} γ'
              rw [Finset.mul_sum]
              -- Cζ X * (C γ'_j * X^j) = C (ζ γ'_j) * X^{j+1}
              have h_Xterm : ∀ j ∈ Finset.range (m - 1 + 1),
                  (C ζ * X : ℝ[X]) * (C (γ' j) * X ^ j) =
                    C (ζ * γ' j) * X ^ (j + 1) := by
                intro j _
                rw [show (C ζ * X : ℝ[X]) * (C (γ' j) * X ^ j) =
                    C (ζ * γ' j) * (X ^ j * X) from by
                  rw [Polynomial.C_mul]; ring]
                rw [← pow_succ]
              rw [Finset.sum_congr rfl h_Xterm]
              -- Reindex the second sum.
              rw [show ∑ j ∈ Finset.range (m - 1 + 1), C (ζ * γ' j) * X ^ (j + 1) =
                  ∑ k ∈ Finset.Ico 1 (m + 1), C (ζ * γ' (k - 1)) * X ^ k from by
                apply Finset.sum_nbij' (fun j _ => j + 1) (fun k _ => k - 1)
                · intro j hj
                  rw [Finset.mem_range] at hj
                  rw [Finset.mem_Ico]; omega
                · intro k hk
                  rw [Finset.mem_Ico] at hk
                  rw [Finset.mem_range]; omega
                · intro j _; rfl
                · intro k hk
                  rw [Finset.mem_Ico] at hk; show k - 1 + 1 = k; omega
                · intro j hj
                  rw [Finset.mem_range] at hj
                  show C (ζ * γ' j) * X ^ (j + 1) =
                      C (ζ * γ' (j + 1 - 1)) * X ^ (j + 1)
                  rw [show j + 1 - 1 = j from by omega]]
              -- Convert range (m-1+1) on the first part to range (m+1) and Ico on second.
              rw [show (m - 1 + 1) = m from by omega]
              rw [show ∑ j ∈ Finset.range m, C (γ' j) * X ^ j =
                  ∑ j ∈ Finset.range (m + 1),
                    C (if j ≤ m - 1 then γ' j else 0) * X ^ j from by
                rw [show m + 1 = m + 1 from rfl]
                rw [show (Finset.range (m + 1)) = insert m (Finset.range m) from by
                  ext x; simp [Finset.mem_range, Finset.mem_insert]; omega]
                rw [Finset.sum_insert (by simp [Finset.mem_range])]
                rw [if_neg (by omega : ¬ m ≤ m - 1)]
                simp
                apply Finset.sum_congr rfl
                intro j hj
                rw [Finset.mem_range] at hj
                rw [if_pos (by omega : j ≤ m - 1)]]
              rw [show ∑ k ∈ Finset.Ico 1 (m + 1), C (ζ * γ' (k - 1)) * X ^ k =
                  ∑ k ∈ Finset.range (m + 1),
                    C (if 0 < k then ζ *
                       (if k - 1 ≤ m - 1 then γ' (k - 1) else 0) else 0) * X ^ k from by
                rw [show Finset.range (m + 1) = insert 0 (Finset.Ico 1 (m + 1)) from by
                  ext x
                  simp [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
                  omega]
                rw [Finset.sum_insert (by simp [Finset.mem_Ico])]
                rw [show C (if 0 < (0 : ℕ) then ζ *
                       (if (0 : ℕ) - 1 ≤ m - 1 then γ' ((0 : ℕ) - 1) else 0) else 0) *
                      X ^ 0 = 0 from by simp]
                rw [zero_add]
                apply Finset.sum_congr rfl
                intro k hk
                rw [Finset.mem_Ico] at hk
                rw [if_pos hk.1, if_pos (by omega : k - 1 ≤ m - 1)]]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j _
              rw [← Polynomial.C_add]
              ring_nf
            rw [h_poly_eq]
            apply mul_preserves_nonpos
            · exact one_add_C_mul_X_hasOnlyRealNonposZeros hζ_nn
            · exact hγ'_root
    · -- ε = 1
      subst hε1
      have hn_odd : Odd n := by
        refine ⟨m, ?_⟩; omega
      have hn_ge_1 : 1 ≤ n := by omega
      have h_neg1_root : Q.eval (-1 : ℝ) = 0 :=
        palindromic_eval_neg_one_zero_of_odd hpal hn_odd
      obtain ⟨R, hR⟩ : (X - C (-1 : ℝ)) ∣ Q :=
        (Polynomial.dvd_iff_isRoot (a := -1)).mpr h_neg1_root
      have hR_eq : Q = ((1 : ℝ[X]) + X) * R := by
        rw [hR]; rw [Polynomial.C_neg]; ring
      obtain ⟨hR_pal, hR_deg⟩ :=
        palindromic_factor_mul hpal hQ_deg one_add_X_palindromic
          one_add_X_natDegree one_add_X_ne_zero (by omega) hR_eq
      have hR_root : HasOnlyRealNegativeZeros R := by
        apply hasOnlyRealNegativeZeros_quotient hroot
        rw [hR_eq]
        rw [show ((1 : ℝ[X]) + X) = X - C (-1 : ℝ) from by
          rw [Polynomial.C_neg]; ring]
      have hn1 : n - 1 = 2 * m + 0 := by omega
      have h_lt : n - 1 < n := by omega
      obtain ⟨γ', hγ'_exp, hγ'_root⟩ :=
        ih (n - 1) h_lt m 0 (Or.inl rfl) hn1 R hR_pal hR_root
      refine ⟨γ', ?_, hγ'_root⟩
      unfold IsGammaExpansion at hγ'_exp ⊢
      rw [hR_eq, hγ'_exp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have hj_le : j ≤ m := Nat.lt_succ_iff.mp hj
      have h2j : 2 * j + 1 ≤ n := by omega
      rw [show ((1 + X : ℝ[X])) * (C (γ' j) * gammaBasis (n - 1) j) =
          C (γ' j) * ((1 + X : ℝ[X]) * gammaBasis (n - 1) j) from by ring]
      rw [one_add_X_mul_gammaBasis_pred n j h2j]

end GammaPochhammer
