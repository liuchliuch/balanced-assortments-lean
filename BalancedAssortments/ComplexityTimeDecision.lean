import BalancedAssortments.ComplexityTimeMatrix
import BalancedAssortments.DecisionCertificates

/-! Actual source-language certificates accepted by the concrete binary system
checker. Cost here covers checking already constructed integer rows; bit-time
for constructing/clearing the source rows is intentionally a separate obligation. -/
noncomputable section
namespace BalancedAssortments.ComplexityTimeVerifier
open PolyhedralBasis DecisionPolyhedron

/-- Reindexing rows is semantic only and preserves the verifier exactly. -/
theorem binary_verifier_agrees_indexed {I : Type*} [Fintype I] [DecidableEq I] {m n : ℕ}
    (e : Fin m ≃ I) (A : Matrix I (Fin n) ℤ) (b : I → ℤ) (p : Fin n → ℤ) (q : ℤ) :
    (checkSystem (encodedNumerators p) (zencode q)
      (encodedRows (fun i j => A (e i) j) (fun i => b (e i)))).1 = verifyInteger A b p q := by
  rw [binary_verifier_agrees]
  apply Bool.eq_iff_iff.mpr
  simp only [verifyInteger, decide_eq_true_eq]
  constructor
  · rintro ⟨hq, h⟩
    exact ⟨hq, fun i => by simpa using h (e.symm i)⟩
  · rintro ⟨hq, h⟩
    exact ⟨hq, fun i => h (e i)⟩

/-- The raw bit-list input supplied to the integer verifier for a guessed support.
This specifies encoded data, rather than charging row-construction as free work. -/
def sourceBinaryCheck {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (A : Finset (Fin n)) (p : Fin n → ℤ) (q : ℤ) : Bool × ℕ :=
  let M := integerMatrix (coefficient v r α H A) (bound v K H)
  let b := integerRhs (coefficient v r α H A) (bound v K H)
  let e := (Fintype.equivFin (Row n)).symm
  checkSystem (encodedNumerators p) (zencode q)
    (encodedRows (fun i j => M (e i) j) (fun i => b (e i)))

theorem sourceBinaryCheck_agrees {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (A : Finset (Fin n)) (p : Fin n → ℤ) (q : ℤ) :
    (sourceBinaryCheck v r α H K A p q).1 = verifyDecision v r α H K A p q := by
  exact binary_verifier_agrees_indexed (Fintype.equivFin (Row n)).symm _ _ p q

/-- The original real sales-space yes-instances have exactly the accepted short
certificates of the explicit bitwise checker, including endogenous support. -/
theorem source_iff_binary_certificate {n B : ℕ}
    (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (hv : ∀ i, CoeffBound B (v i)) (hr : ∀ i, CoeffBound B (r i))
    (hα : CoeffBound B α) (hH : CoeffBound B H) (hK : CoeffBound B (K : ℚ)) :
    (∃ x : Fin n → ℝ,
      Sales.CompactFeasible (fun i => (v i : ℝ)) x K ∧ Sales.Balanced (α : ℝ) x ∧
        (H : ℝ) ≤ Sales.objective (fun i => (r i : ℝ)) x) ↔
    ∃ (A : Finset (Fin n)) (p : Fin n → ℤ) (q : ℤ),
      (sourceBinaryCheck v r α H K A p q).1 = true ∧
      q.natAbs.size ≤ n*((B+B+1)*(n+1)+n)+1 ∧
      ∀ j, (p j).natAbs.size ≤ n*((B+B+1)*(n+1)+n)+1 := by
  simp only [sourceBinaryCheck_agrees]
  exact source_iff_short_verified_certificate v r α H K hv hr hα hH hK

lemma size_of_abs_bound (z : ℤ) (D : ℕ) (h : |z| ≤ (2:ℤ)^D) : z.natAbs.size ≤ D+1 := by
  apply Nat.size_le.mpr
  have hh : z.natAbs ≤ 2^D := by
    have hcast : (z.natAbs : ℤ) ≤ (2:ℤ)^D := by simpa using h
    exact_mod_cast hcast
  rw [pow_succ]
  have hp := Nat.two_pow_pos D
  omega

def sourceWidth (n B : ℕ) : ℕ :=
  n*((B+B+1)*(n+1)+n)+(B+B+1)*(n+1)+2

/-- Explicit polynomial checking time after rational-row construction. Its
parameters are the original source dimension and coefficient bit bound. -/
theorem sourceBinaryCheck_cost {n B : ℕ}
    (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ) (A : Finset (Fin n))
    (p : Fin n → ℤ) (q : ℤ)
    (hv : ∀ i, CoeffBound B (v i)) (hr : ∀ i, CoeffBound B (r i))
    (hα : CoeffBound B α) (hH : CoeffBound B H) (hK : CoeffBound B (K : ℚ))
    (hp : ∀ j, (p j).natAbs.size ≤ n*((B+B+1)*(n+1)+n)+1)
    (hq : q.natAbs.size ≤ n*((B+B+1)*(n+1)+n)+1) :
    (sourceBinaryCheck v r α H K A p q).2 ≤
      (n*n+3*n+2)*(rowBudget n (sourceWidth n B)+4)+48*sourceWidth n B+27 := by
  have hM := coefficient_bit_bound v r α H A hv hr hα hH
  have hb := rhs_bit_bound v K H hv hK hH
  have hi (i : Row n) (j : Option (Fin n)) :
      (integerCoefficient (coefficient v r α H A) (bound v K H) i j).natAbs.size ≤ sourceWidth n B := by
    have h := size_of_abs_bound _ _ (integerCoefficient_bound _ _ hM hb i j)
    unfold sourceWidth
    nlinarith
  have hpp : ∀ j, (p j).natAbs.size ≤ sourceWidth n B := by
    intro j
    have h := hp j
    unfold sourceWidth
    nlinarith
  have hqq : q.natAbs.size ≤ sourceWidth n B := by unfold sourceWidth; nlinarith
  have h := binary_matrix_verifier_cost
    (fun i j => integerMatrix (coefficient v r α H A) (bound v K H)
      ((Fintype.equivFin (Row n)).symm i) j)
    (fun i => integerRhs (coefficient v r α H A) (bound v K H)
      ((Fintype.equivFin (Row n)).symm i)) p q
    (fun i j => hi _ (some j)) (fun i => hi _ none) hpp hqq
  simpa only [sourceBinaryCheck, row_count] using h

end BalancedAssortments.ComplexityTimeVerifier
