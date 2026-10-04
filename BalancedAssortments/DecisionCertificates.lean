import BalancedAssortments.DecisionPolyhedron
import BalancedAssortments.PolyhedralBasisCoefficientBounds
import BalancedAssortments.PolyhedralBasisVerifier

/-! Source-model polynomial-size rational revenue-threshold certificates.
This composes exact guessed-support rows with the proved rational-polyhedron
certificate theorem. It is not itself a formal machine-complexity class theorem. -/
namespace BalancedAssortments.DecisionPolyhedron
open PolyhedralBasis

lemma coefficient_bit_bound {n B : ℕ} (v r : Fin n → ℚ) (α H : ℚ)
    (A : Finset (Fin n)) (hv : ∀ i, CoeffBound B (v i)) (hr : ∀ i, CoeffBound B (r i))
    (hα : CoeffBound B α) (hH : CoeffBound B H) (row : Row n) (j : Fin n) :
    CoeffBound (B+B+1) (coefficient v r α H A row j) := by
  have hmono : B ≤ B+B+1 := by omega
  cases row with
  | nonnegative i =>
    simp only [coefficient]
    split_ifs
    · exact (CoeffBound.one B).neg.mono hmono
    · exact CoeffBound.zero _
  | cap i =>
    simp only [coefficient]
    split_ifs
    · exact CoeffBound.one _
    · exact CoeffBound.zero _
  | rank =>
    simpa only [coefficient, one_div] using (hv j).inv.mono hmono
  | balance i k =>
    simp only [coefficient]
    by_cases h : i ∈ A ∧ k ∈ A
    · rw [if_pos h]
      have hleft : CoeffBound B (α * (if j = k then 1 else 0)) := by
        split_ifs
        · simpa using hα
        · simpa using CoeffBound.zero B
      have hright : CoeffBound B (if j = i then 1 else 0) := by
        split_ifs
        · exact CoeffBound.one B
        · exact CoeffBound.zero B
      exact hleft.sub hright
    · rw [if_neg h]
      exact CoeffBound.zero _
  | offsupport i =>
    simp only [coefficient]
    split_ifs
    · exact CoeffBound.zero _
    · exact CoeffBound.one _
    · exact CoeffBound.zero _
  | target => exact hH.sub (hr j)

lemma rhs_bit_bound {n B : ℕ} (v : Fin n → ℚ) (K : ℕ) (H : ℚ)
    (hv : ∀ i, CoeffBound B (v i)) (hK : CoeffBound B (K : ℚ)) (hH : CoeffBound B H)
    (row : Row n) : CoeffBound (B+B+1) (bound v K H row) := by
  have hm : B ≤ B+B+1 := by omega
  cases row with
  | nonnegative _ => exact CoeffBound.zero _
  | cap i => exact (hv i).mono hm
  | rank => exact hK.mono hm
  | balance _ _ => exact CoeffBound.zero _
  | offsupport _ => exact CoeffBound.zero _
  | target => exact hH.neg.mono hm

/-- Every yes-instance in the original real compact model has an actual rational
certificate with a uniform polynomial bound in the original coefficient bit size.
The support, nonsingular basis and rational witness are all obtained in the proof. -/
theorem source_short_rational_certificate {n B : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (hv : ∀ i, CoeffBound B (v i)) (hr : ∀ i, CoeffBound B (r i))
    (hα : CoeffBound B α) (hH : CoeffBound B H) (hK : CoeffBound B (K : ℚ))
    (hyes : ∃ x : Fin n → ℝ,
      Sales.CompactFeasible (fun i => (v i : ℝ)) x K ∧ Sales.Balanced (α : ℝ) x ∧
        (H : ℝ) ≤ Sales.objective (fun i => (r i : ℝ)) x) :
    ∃ (w : Fin n → ℚ) (p : Fin n → ℤ) (q : ℤ), q ≠ 0 ∧
      q.natAbs.size ≤ n * ((B+B+1) * (n+1) + n) + 1 ∧
      (∀ j, (p j).natAbs.size ≤ n * ((B+B+1) * (n+1) + n) + 1) ∧
      (∀ j, w j = (p j : ℚ) / q) ∧
      Sales.CompactFeasible (fun i => (v i : ℝ)) (fun j => (w j : ℝ)) K ∧
      Sales.Balanced (α : ℝ) (fun j => (w j : ℝ)) ∧
      (H : ℝ) ≤ Sales.objective (fun i => (r i : ℝ)) (fun j => (w j : ℝ)) := by
  obtain ⟨A, hn⟩ := (source_decision_iff v r α H K).1 hyes
  have hbound : ∀ x ∈ PolyhedralBasis.polyhedron (realMatrix v r α H A) (realBound v K H),
      ∀ j, (0 : ℝ) ≤ x j ∧ x j ≤ (v j : ℝ) := by
    intro x hx j
    exact ((rows_iff v r α H K A x).1 hx).1 j
  obtain ⟨w, p, q, hq, hqs, hps, he, hf⟩ := bounded_rational_polyhedron_certificate
    (coefficient v r α H A) (bound v K H) (fun _ => 0) (fun j => (v j : ℝ))
    (coefficient_bit_bound v r α H A hv hr hα hH) (rhs_bit_bound v K H hv hK hH)
    hbound hn
  exact ⟨w, p, q, hq, hqs, hps, he, rows_source_sound v r α H K A _ hf⟩

/-- Exact finite certificate checker for an input and a guessed support. -/
def verifyDecision {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (A : Finset (Fin n)) (p : Fin n → ℤ) (q : ℤ) : Bool :=
  let M := coefficient v r α H A
  let b := bound v K H
  verifyInteger (integerMatrix M b) (integerRhs M b) p q

/-- Acceptance entails actual source feasibility and the original fractional
revenue target. This direction has no bit-bound or input-legality premise. -/
theorem verifyDecision_sound {n : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (A : Finset (Fin n)) (p : Fin n → ℤ) (q : ℤ)
    (hvfy : verifyDecision v r α H K A p q = true) :
    0 < q ∧
    Sales.CompactFeasible (fun i => (v i : ℝ)) (fun j => (p j : ℝ) / q) K ∧
      Sales.Balanced (α : ℝ) (fun j => (p j : ℝ) / q) ∧
      (H : ℝ) ≤ Sales.objective (fun i => (r i : ℝ)) (fun j => (p j : ℝ) / q) := by
  obtain ⟨hq, hf⟩ := (verifyInteger_iff _ _ _ _).1 hvfy
  rw [integer_polyhedron_eq] at hf
  exact ⟨hq, rows_source_sound v r α H K A _ hf⟩

/-- Every actual yes-instance has an accepted, polynomial-size certificate for
the executable checker, including a normalized positive denominator. -/
theorem source_short_verified_certificate {n B : ℕ} (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (hv : ∀ i, CoeffBound B (v i)) (hr : ∀ i, CoeffBound B (r i))
    (hα : CoeffBound B α) (hH : CoeffBound B H) (hK : CoeffBound B (K : ℚ))
    (hyes : ∃ x : Fin n → ℝ,
      Sales.CompactFeasible (fun i => (v i : ℝ)) x K ∧ Sales.Balanced (α : ℝ) x ∧
        (H : ℝ) ≤ Sales.objective (fun i => (r i : ℝ)) x) :
    ∃ (A : Finset (Fin n)) (p : Fin n → ℤ) (q : ℤ),
      verifyDecision v r α H K A p q = true ∧
      q.natAbs.size ≤ n * ((B+B+1) * (n+1) + n) + 1 ∧
      ∀ j, (p j).natAbs.size ≤ n * ((B+B+1) * (n+1) + n) + 1 := by
  obtain ⟨A, hn⟩ := (source_decision_iff v r α H K).1 hyes
  have hbound : ∀ x ∈ PolyhedralBasis.polyhedron (realMatrix v r α H A) (realBound v K H),
      ∀ j, (0 : ℝ) ≤ x j ∧ x j ≤ (v j : ℝ) := by
    intro x hx j
    exact ((rows_iff v r α H K A x).1 hx).1 j
  obtain ⟨p, q, hvfy, hqs, hps⟩ := exists_short_verified_rational_certificate
    (coefficient v r α H A) (bound v K H) (fun _ => 0) (fun j => (v j : ℝ))
    (coefficient_bit_bound v r α H A hv hr hα hH) (rhs_bit_bound v K H hv hK hH)
    hbound hn
  exact ⟨A, p, q, hvfy, hqs, hps⟩

/-- Exact verifier characterization, with the full mathematical source language
on the left and bounded accepted certificates on the right. -/
theorem source_iff_short_verified_certificate {n B : ℕ}
    (v r : Fin n → ℚ) (α H : ℚ) (K : ℕ)
    (hv : ∀ i, CoeffBound B (v i)) (hr : ∀ i, CoeffBound B (r i))
    (hα : CoeffBound B α) (hH : CoeffBound B H) (hK : CoeffBound B (K : ℚ)) :
    (∃ x : Fin n → ℝ,
      Sales.CompactFeasible (fun i => (v i : ℝ)) x K ∧ Sales.Balanced (α : ℝ) x ∧
        (H : ℝ) ≤ Sales.objective (fun i => (r i : ℝ)) x) ↔
    ∃ (A : Finset (Fin n)) (p : Fin n → ℤ) (q : ℤ),
      verifyDecision v r α H K A p q = true ∧
      q.natAbs.size ≤ n * ((B+B+1) * (n+1) + n) + 1 ∧
      ∀ j, (p j).natAbs.size ≤ n * ((B+B+1) * (n+1) + n) + 1 := by
  constructor
  · exact source_short_verified_certificate v r α H K hv hr hα hH hK
  · rintro ⟨A, p, q, hvfy, _, _⟩
    exact ⟨_, (verifyDecision_sound v r α H K A p q hvfy).2⟩

end BalancedAssortments.DecisionPolyhedron
