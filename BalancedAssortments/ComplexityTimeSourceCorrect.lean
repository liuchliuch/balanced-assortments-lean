import BalancedAssortments.ComplexityTimeSourcePipeline
import BalancedAssortments.ComplexityTimeRawSemantics
import BalancedAssortments.DecisionCertificates

/-! Actual raw source verification agrees with the source decision polyhedron.
Row construction, denominator clearing, and bitwise checking all participate. -/
namespace BalancedAssortments.ComplexityTimeSourcePipeline
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions
open ComplexityTimeSourceRows DecisionPolyhedron
open scoped BigOperators

def decodedValues {n : ℕ} (xs : List Fraction) : Fin n → ℚ :=
  fun j => decode (lookup zero xs j.val).1

theorem compiledRow_correct {n : ℕ} (v r : List Fraction) (α H : Fraction)
    (K mask : List Bool)
    (hv : ∀ j : Fin n, Valid (lookup zero v j.val).1 ∧ 0 < decode (lookup zero v j.val).1)
    (hr : ∀ j : Fin n, Valid (lookup zero r j.val).1) (hα : Valid α) (hH : Valid H)
    (row : Row n) (p : Fin n → ℤ) (q : ℤ) (hq : 0 < q) :
    (checkCoefficientRow (compiledRow v r α H K mask row).1.1 (encodedNumerators p)
      (compiledRow v r α H K mask row).1.2 (zencode q)).1 = true ↔
    (∑ j, coefficient (decodedValues v) (decodedValues r) (decode α) (decode H)
      (support mask n) row j * (p j : ℚ) / (q : ℚ)) ≤
      bound (decodedValues v) (value K) (decode H) row := by
  have hcs := fun j => coefficientRaw_spec v r α H mask hv hr hα hH row j
  have hbs := boundRaw_spec v K H (fun j => (hv j).1) hH row
  have hh := checkRawCoefficientRow_correct
    (fun j => (coefficientRaw v r α H mask row j).1) (boundRaw v K H row).1
    (fun j => (hcs j).1) hbs.1 p q hq
  simp_rw [(hcs _).2, hbs.2] at hh
  simpa only [compiledRow, rowEntries_data, decodedValues] using hh

/-- Exact acceptance characterization for a specified raw support mask and
shared-denominator integer certificate. -/
theorem verifySourceSized_correct {n : ℕ} (v r : List Fraction) (α H : Fraction)
    (K mask : List Bool)
    (hv : ∀ j : Fin n, Valid (lookup zero v j.val).1 ∧ 0 < decode (lookup zero v j.val).1)
    (hr : ∀ j : Fin n, Valid (lookup zero r j.val).1) (hα : Valid α) (hH : Valid H)
    (p : Fin n → ℤ) (q : ℤ) :
    (verifySourceSized n v r α H K mask (encodedNumerators p) (zencode q)).1 = true ↔
      0 < q ∧ (fun j => (p j : ℝ)/(q : ℝ)) ∈ PolyhedralBasis.polyhedron
        (realMatrix (decodedValues v) (decodedValues r) (decode α) (decode H) (support mask n))
        (realBound (decodedValues v) (value K) (decode H)) := by
  change (checkSystem (encodedNumerators p) (zencode q)
    (compileRows v r α H K mask (rowList n)).1).1 = true ↔ _
  rw [checkSystem_correct, zencode_value, compileRows_data]
  constructor
  · rintro ⟨hq, hs⟩
    refine ⟨hq, ?_⟩
    intro row
    have hrow := hs (compiledRow v r α H K mask row).1
      (List.mem_map.mpr ⟨row, rowList_complete row, rfl⟩)
    have ha := (checkCoefficientRow_correct _ _ _ _).2 hrow
    have hh := (compiledRow_correct v r α H K mask hv hr hα hH row p q hq).1 ha
    have hh' : (∑ j, coefficient (decodedValues v) (decodedValues r) (decode α) (decode H)
        (support mask n) row j * ((p j : ℚ)/(q : ℚ))) ≤
        bound (decodedValues v) (value K) (decode H) row := by
      simpa only [mul_div_assoc] using hh
    change (∑ j, (coefficient (decodedValues v) (decodedValues r) (decode α) (decode H)
      (support mask n) row j : ℝ) * ((p j : ℝ)/(q : ℝ))) ≤
      (bound (decodedValues v) (value K) (decode H) row : ℝ)
    exact_mod_cast hh'
  · rintro ⟨hq, hs⟩
    refine ⟨hq, ?_⟩
    intro encoded he
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp he
    apply (checkCoefficientRow_correct _ _ _ _).1
    apply (compiledRow_correct v r α H K mask hv hr hα hH row p q hq).2
    have hh := hs row
    change (∑ j, (coefficient (decodedValues v) (decodedValues r) (decode α) (decode H)
      (support mask n) row j : ℝ) * ((p j : ℝ)/(q : ℝ))) ≤
      (bound (decodedValues v) (value K) (decode H) row : ℝ) at hh
    have hh' : (∑ j, coefficient (decodedValues v) (decodedValues r) (decode α) (decode H)
        (support mask n) row j * ((p j : ℚ)/(q : ℚ))) ≤
        bound (decodedValues v) (value K) (decode H) row := by exact_mod_cast hh
    simpa only [mul_div_assoc] using hh'

/-- The complete raw verifier's accepted witness satisfies the original compact
caps, rank, balance, and fractional objective threshold. -/
theorem verifySourceSized_sound {n : ℕ} (v r : List Fraction) (α H : Fraction)
    (K mask : List Bool)
    (hv : ∀ j : Fin n, Valid (lookup zero v j.val).1 ∧ 0 < decode (lookup zero v j.val).1)
    (hr : ∀ j : Fin n, Valid (lookup zero r j.val).1) (hα : Valid α) (hH : Valid H)
    (p : Fin n → ℤ) (q : ℤ)
    (ha : (verifySourceSized n v r α H K mask (encodedNumerators p) (zencode q)).1 = true) :
    Sales.CompactFeasible (fun j => (decodedValues v j : ℝ)) (fun j => (p j : ℝ)/(q : ℝ)) (value K) ∧
      Sales.Balanced (decode α : ℝ) (fun j => (p j : ℝ)/(q : ℝ)) ∧
      (decode H : ℝ) ≤ Sales.objective (fun j => (decodedValues r j : ℝ))
        (fun j => (p j : ℝ)/(q : ℝ)) := by
  have hh := (verifySourceSized_correct v r α H K mask hv hr hα hH p q).1 ha
  exact rows_source_sound _ _ _ _ _ _ _ hh.2

/-- The public entry point merely obtains n from the actual attraction list. -/
theorem verifySource_correct (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (hv : ∀ j : Fin v.length, Valid (lookup zero v j.val).1 ∧ 0 < decode (lookup zero v j.val).1)
    (hr : ∀ j : Fin v.length, Valid (lookup zero r j.val).1) (hα : Valid α) (hH : Valid H)
    (p : Fin v.length → ℤ) (q : ℤ) :
    (verifySource v r α H K mask (encodedNumerators p) (zencode q)).1 = true ↔
      0 < q ∧ (fun j => (p j : ℝ)/(q : ℝ)) ∈ PolyhedralBasis.polyhedron
        (realMatrix (decodedValues v) (decodedValues r) (decode α) (decode H) (support mask v.length))
        (realBound (decodedValues v) (value K) (decode H)) :=
  verifySourceSized_correct v r α H K mask hv hr hα hH p q


def encodeSupport {n : ℕ} (A : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i => decide (i ∈ A))

@[simp] theorem encodeSupport_length {n : ℕ} (A : Finset (Fin n)) :
    (encodeSupport A).length = n := by simp [encodeSupport]

@[simp] theorem support_encodeSupport {n : ℕ} (A : Finset (Fin n)) :
    support (encodeSupport A) n = A := by
  ext i
  simp [support, encodeSupport, lookup_value, List.getD, i.isLt]

/-- Every source yes-instance has a polynomial-size certificate accepted by the
actual raw source verifier. The support mask and positive-denominator witness
are constructed in the proof rather than assumed. -/
theorem verifySourceSized_complete_short {n B : ℕ} (v r : List Fraction) (α H : Fraction)
    (K : List Bool)
    (hv : ∀ j : Fin n, Valid (lookup zero v j.val).1 ∧ 0 < decode (lookup zero v j.val).1)
    (hr : ∀ j : Fin n, Valid (lookup zero r j.val).1) (hα : Valid α) (hH : Valid H)
    (bv : ∀ j : Fin n, PolyhedralBasis.CoeffBound B (decodedValues v j))
    (br : ∀ j : Fin n, PolyhedralBasis.CoeffBound B (decodedValues r j))
    (bα : PolyhedralBasis.CoeffBound B (decode α))
    (bH : PolyhedralBasis.CoeffBound B (decode H))
    (bK : PolyhedralBasis.CoeffBound B (value K : ℚ))
    (hyes : ∃ x : Fin n → ℝ,
      Sales.CompactFeasible (fun j => (decodedValues v j : ℝ)) x (value K) ∧
      Sales.Balanced (decode α : ℝ) x ∧
      (decode H : ℝ) ≤ Sales.objective (fun j => (decodedValues r j : ℝ)) x) :
    ∃ (mask : List Bool) (p : Fin n → ℤ) (q : ℤ), mask.length = n ∧
      (verifySourceSized n v r α H K mask (encodedNumerators p) (zencode q)).1 = true ∧
      q.natAbs.size ≤ n*((B+B+1)*(n+1)+n)+1 ∧
      ∀ j, (p j).natAbs.size ≤ n*((B+B+1)*(n+1)+n)+1 := by
  obtain ⟨w, p, q, hq, hqs, hps, he, hc, hb, ht⟩ :=
    source_short_rational_certificate (decodedValues v) (decodedValues r) (decode α) (decode H)
      (value K) bv br bα bH bK hyes
  obtain ⟨p', q', hq', hqq, hpp, heq⟩ := PolyhedralBasis.normalize_denominator p q hq
  have hvec : (fun j => (p' j : ℝ)/(q' : ℝ)) = fun j => (w j : ℝ) := by
    funext j
    rw [heq j, he j]
    simp only [Rat.cast_div, Rat.cast_intCast]
  obtain ⟨A, hA⟩ := source_rows_complete (decodedValues v) (decodedValues r) (decode α) (decode H)
    (value K) (fun j => (w j : ℝ)) hc hb ht
  refine ⟨encodeSupport A, p', q', encodeSupport_length A, ?_, ?_, ?_⟩
  · apply (verifySourceSized_correct v r α H K (encodeSupport A) hv hr hα hH p' q').2
    refine ⟨hq', ?_⟩
    rw [support_encodeSupport, hvec]
    exact hA
  · simpa only [hqq] using hqs
  · intro j
    simpa only [hpp j] using hps j

end BalancedAssortments.ComplexityTimeSourcePipeline
