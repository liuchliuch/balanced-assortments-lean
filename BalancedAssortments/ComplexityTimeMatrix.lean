import BalancedAssortments.ComplexityTimeSystem
import BalancedAssortments.PolyhedralBasisVerifier

/-! Semantic bridge between the concrete bit-list system checker and the
integer matrices occurring in small rational LP certificates. Encoding here
specifies the input representation; it is not an uncharged arithmetic step of
the checker, whose executable body only processes the supplied bit lists. -/
namespace BalancedAssortments.ComplexityTimeVerifier
open ComplexityTimeBinary

/-- Canonical signed-integer representation as a difference of bit strings. -/
def zencode (z : ℤ) : ZBits :=
  if z < 0 then ([],z.natAbs.bits) else (z.natAbs.bits,[])

@[simp] theorem zencode_value (z : ℤ) : zvalue (zencode z) = z := by
  unfold zencode
  split_ifs with h
  · simp [zvalue, value, Int.natCast_natAbs, abs_of_neg h]
  · simp [zvalue, value, Int.natCast_natAbs, abs_of_nonneg (le_of_not_gt h)]

@[simp] theorem zencode_width (z : ℤ) : width (zencode z) = z.natAbs.size := by
  unfold zencode
  split_ifs <;> simp [width, Nat.size_eq_bits_len]

theorem zip_ofFn {α β : Type*} {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun i => (f i,g i)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

def encodedNumerators {n : ℕ} (p : Fin n → ℤ) : List ZBits := List.ofFn (fun j => zencode (p j))

def encodedRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    List (List ZBits × ZBits) :=
  List.ofFn (fun i => (List.ofFn (fun j => zencode (A i j)),zencode (b i)))

theorem encoded_row_holds {n : ℕ} (A p : Fin n → ℤ) (b q : ℤ) :
    RowHolds (List.ofFn (fun j => zencode (A j))) (encodedNumerators p) (zencode b) (zencode q) ↔
      (∑ j, A j*p j) ≤ b*q := by
  simp [RowHolds, encodedNumerators, zip_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- Exact agreement with the division-free integer verifier used by the vertex
certificate theorem. No bit-level predicate is substituted for a mathematical LP. -/
theorem binary_verifier_agrees {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (p : Fin n → ℤ) (q : ℤ) :
    (checkSystem (encodedNumerators p) (zencode q) (encodedRows A b)).1 =
      PolyhedralBasis.verifyInteger A b p q := by
  apply Bool.eq_iff_iff.mpr
  rw [checkSystem_correct]
  simp only [PolyhedralBasis.verifyInteger, decide_eq_true_eq, zencode_value, encodedRows,
    List.forall_mem_ofFn_iff, encoded_row_holds]

/-- Polynomial bit/list-operation complexity for the actual matrix certificate
checker, including all dimension checks and common-denominator verification. -/
theorem binary_matrix_verifier_cost {m n L : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (p : Fin n → ℤ) (q : ℤ)
    (hA : ∀ i j, (A i j).natAbs.size ≤ L) (hb : ∀ i, (b i).natAbs.size ≤ L)
    (hp : ∀ j, (p j).natAbs.size ≤ L) (hq : q.natAbs.size ≤ L) :
    (checkSystem (encodedNumerators p) (zencode q) (encodedRows A b)).2 ≤
      m*(rowBudget n L+4)+48*L+27 := by
  have hn : (encodedNumerators p).length ≤ n := by simp [encodedNumerators]
  have hpp : ∀ x ∈ encodedNumerators p, width x ≤ L := by
    simp only [encodedNumerators, List.forall_mem_ofFn_iff, zencode_width]
    exact hp
  have hqq : width (zencode q) ≤ L := by simpa using hq
  have hr : ∀ row ∈ encodedRows A b,
      row.1.length ≤ n ∧ (∀ a ∈ row.1, width a ≤ L) ∧ width row.2 ≤ L := by
    simp only [encodedRows, List.forall_mem_ofFn_iff, List.length_ofFn, zencode_width]
    intro i
    exact ⟨le_rfl, hA i, hb i⟩
  simpa only [encodedRows, List.length_ofFn] using
    checkSystem_cost (encodedNumerators p) (zencode q) (encodedRows A b) n L hn hpp hqq hr

end BalancedAssortments.ComplexityTimeVerifier
