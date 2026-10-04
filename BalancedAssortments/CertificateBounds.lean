import Mathlib

/-! Polynomial binary-size bounds for Cramer determinants. These results cover
integer square systems with a nonsingular basis, not existence of a small LP
vertex or polynomial-time LP optimization. -/
namespace BalancedAssortments.CertificateBounds
open scoped BigOperators

lemma abs_sign {n : ℕ} (σ : Equiv.Perm (Fin n)) : |((Equiv.Perm.sign σ : ℤˣ) : ℤ)| = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- Elementary Leibniz determinant bound, exact over integers. -/
theorem det_abs_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {M : ℤ}
    (hM : 0 ≤ M) (hA : ∀ i j, |A i j| ≤ M) :
    |A.det| ≤ (n.factorial : ℤ) * M ^ n := by
  rw [Matrix.det_apply']
  calc
    |∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i| ≤
        ∑ σ : Equiv.Perm (Fin n), |(Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), M ^ n := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, abs_sign, one_mul, Finset.abs_prod]
      simpa using Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => abs_nonneg (A (σ i) i))
        (fun i (_ : i ∈ Finset.univ) => hA (σ i) i)
    _ = (n.factorial : ℤ) * M ^ n := by simp [Fintype.card_perm]

lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp : 0 < 2 ^ n := Nat.two_pow_pos n
    omega

lemma factorial_le_two_pow_square (n : ℕ) : n.factorial ≤ 2 ^ (n * n) := by
  calc n.factorial ≤ n ^ n := Nat.factorial_le_pow n
       _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (nat_le_two_pow n) n
       _ = 2 ^ (n * n) := by rw [pow_mul]

/-- B-bit integer entries have determinants of at most n(B+n)+1 bits. -/
theorem det_abs_le_two_pow {n B : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, |A i j| ≤ (2 : ℤ) ^ B) :
    |A.det| ≤ (2 : ℤ) ^ (n * (B + n)) := by
  have hd := det_abs_le A (by positivity : (0 : ℤ) ≤ 2 ^ B) hA
  have hf : (n.factorial : ℤ) ≤ (2 : ℤ) ^ (n * n) := by
    exact_mod_cast factorial_le_two_pow_square n
  calc |A.det| ≤ (n.factorial : ℤ) * (2 ^ B) ^ n := hd
       _ ≤ 2 ^ (n * n) * (2 ^ B) ^ n := mul_le_mul_of_nonneg_right hf (by positivity)
       _ = 2 ^ (n * (B + n)) := by rw [← pow_mul, ← pow_add]; congr 1 <;> ring

/-- The ordinary unsigned binary size of the determinant has a polynomial bound. -/
theorem det_binary_size {n B : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, |A i j| ≤ (2 : ℤ) ^ B) :
    A.det.natAbs.size ≤ n * (B + n) + 1 := by
  apply Nat.size_le.mpr
  have h := det_abs_le_two_pow A hA
  have hn : A.det.natAbs ≤ 2 ^ (n * (B + n)) := by
    have hcast : (A.det.natAbs : ℤ) ≤ (2 : ℤ) ^ (n * (B + n)) := by simpa using h
    exact_mod_cast hcast
  have hp : 0 < 2 ^ (n * (B + n)) := Nat.two_pow_pos _
  rw [pow_succ]
  omega

/-- Casting commutes with the determinant, explicitly over the integer input matrix. -/
lemma cast_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (A.det : ℚ) = (A.map (fun z : ℤ => (z : ℚ))).det := by
  exact (Int.castRingHom ℚ).map_det A

lemma cast_updateCol {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ)
    (i : Fin n) :
    (A.updateCol i b).map (fun z : ℤ => (z : ℚ)) =
      (A.map (fun z : ℤ => (z : ℚ))).updateCol i (fun j => (b j : ℚ)) := by
  ext j k
  simp only [Matrix.map_apply, Matrix.updateCol_apply]
  split_ifs <;> rfl

/-- An existing solution of a nonsingular integer system has an exact Cramer
representation with the original integer determinants. -/
theorem cramer_representation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n → ℤ) (x : Fin n → ℚ) (hdet : A.det ≠ 0)
    (hsol : (A.map (fun z : ℤ => (z : ℚ))).mulVec x = fun j => (b j : ℚ))
    (i : Fin n) : x i = ((A.updateCol i b).det : ℚ) / (A.det : ℚ) := by
  let Ar := A.map (fun z : ℤ => (z : ℚ))
  have hc : Ar.cramer (fun j => (b j : ℚ)) = Ar.det • x := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hsol, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hi := congr_fun hc i
  simp only [Matrix.cramer_apply, Pi.smul_apply, smul_eq_mul] at hi
  have hd : (A.det : ℚ) ≠ 0 := by exact_mod_cast hdet
  have he : ((A.updateCol i b).det : ℚ) = (A.det : ℚ) * x i := by
    rw [cast_det, cast_updateCol, cast_det]
    exact hi
  apply (eq_div_iff hd).mpr
  linarith

/-- Each numerator and the shared nonzero denominator has polynomial binary size.
This does not assume the requested small-size conclusion as a premise. -/
theorem small_cramer_certificate {n B : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n → ℤ) (x : Fin n → ℚ) (hdet : A.det ≠ 0)
    (hA : ∀ i j, |A i j| ≤ (2 : ℤ) ^ B) (hb : ∀ i, |b i| ≤ (2 : ℤ) ^ B)
    (hsol : (A.map (fun z : ℤ => (z : ℚ))).mulVec x = fun j => (b j : ℚ)) :
    ∃ (p : Fin n → ℤ) (q : ℤ), q ≠ 0 ∧
      q.natAbs.size ≤ n * (B + n) + 1 ∧
      (∀ i, (p i).natAbs.size ≤ n * (B + n) + 1) ∧
      (∀ i, x i = (p i : ℚ) / q) := by
  refine ⟨fun i => (A.updateCol i b).det, A.det, hdet, det_binary_size A hA, ?_, ?_⟩
  · intro i
    apply det_binary_size
    intro j k
    simp only [Matrix.updateCol_apply]
    split_ifs
    · exact hb j
    · exact hA j k
  · intro i
    exact cramer_representation A b x hdet hsol i

end BalancedAssortments.CertificateBounds
