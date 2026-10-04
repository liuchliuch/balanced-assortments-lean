import BalancedAssortments.PolyhedralBasisRational

/-! Exact integer certificate verifier: no floating-point comparisons or division
are needed to check a shared-denominator feasibility certificate. -/
namespace BalancedAssortments.PolyhedralBasis
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

/-- Evaluate all integer cross-multiplied inequalities, insisting on a positive
shared denominator. The finite verifier is executable. -/
def verifyInteger (A : Matrix I (Fin n) ℤ) (b : I → ℤ) (p : Fin n → ℤ) (q : ℤ) : Bool :=
  decide (0 < q ∧ ∀ i, (∑ j, A i j * p j) ≤ b i * q)

theorem verifyInteger_iff (A : Matrix I (Fin n) ℤ) (b : I → ℤ) (p : Fin n → ℤ) (q : ℤ) :
    verifyInteger A b p q = true ↔ 0 < q ∧
      (fun j => (p j : ℝ) / q) ∈ polyhedron
        (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ)) := by
  simp only [verifyInteger, decide_eq_true_eq]
  constructor
  · rintro ⟨hq, hi⟩
    refine ⟨hq, fun i => ?_⟩
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    have he : evaluate (A.map (fun z : ℤ => (z : ℝ))) (fun j => (p j : ℝ) / q) i =
        ((∑ j, A i j * p j : ℤ) : ℝ) / q := by
      simp only [evaluate, Matrix.map_apply, ← mul_div_assoc, ← Finset.sum_div]
      congr 1
      push_cast
      rfl
    rw [he]
    apply (div_le_iff₀ hqr).2
    change ((∑ j, A i j * p j : ℤ) : ℝ) ≤ (b i : ℝ) * (q : ℝ)
    exact_mod_cast hi i
  · rintro ⟨hq, hi⟩
    refine ⟨hq, fun i => ?_⟩
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    have h := hi i
    change (∑ j, (A i j : ℝ) * ((p j : ℝ) / q)) ≤ (b i : ℝ) at h
    simp only [← mul_div_assoc, ← Finset.sum_div] at h
    have hh := (div_le_iff₀ hqr).1 h
    exact_mod_cast hh

/-- Turning a possibly negative shared denominator positive preserves every
represented rational and both magnitude bounds. -/
theorem normalize_denominator (p : Fin n → ℤ) (q : ℤ) (hq : q ≠ 0) :
    ∃ (p' : Fin n → ℤ) (q' : ℤ), 0 < q' ∧ q'.natAbs = q.natAbs ∧
      (∀ j, (p' j).natAbs = (p j).natAbs) ∧
      (∀ j, (p' j : ℝ) / q' = (p j : ℝ) / q) := by
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · refine ⟨fun j => -p j, -q, by omega, by simp, fun _ => by simp, ?_⟩
    intro j
    push_cast
    simp
  · exact ⟨p, q, hpos, rfl, fun _ => rfl, fun _ => rfl⟩

/-- General bounded integer feasibility has a short certificate accepted by the
actual division-free verifier, not merely by a proposition-level oracle. -/
theorem exists_short_verified_integer_certificate {B : ℕ}
    (A : Matrix I (Fin n) ℤ) (b : I → ℤ) (lo hi : Fin n → ℝ)
    (hA : ∀ i j, |A i j| ≤ (2 : ℤ) ^ B) (hb : ∀ i, |b i| ≤ (2 : ℤ) ^ B)
    (hbound : ∀ x ∈ polyhedron (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ)),
      ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hn : (polyhedron (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ))).Nonempty) :
    ∃ (p : Fin n → ℤ) (q : ℤ), verifyInteger A b p q = true ∧
      q.natAbs.size ≤ n * (B + n) + 1 ∧
      ∀ j, (p j).natAbs.size ≤ n * (B + n) + 1 := by
  obtain ⟨w, p, q, hq, hqs, hps, he, hf⟩ :=
    bounded_integer_polyhedron_certificate A b lo hi hA hb hbound hn
  obtain ⟨p', q', hq', hqq, hpp, heq⟩ := normalize_denominator p q hq
  refine ⟨p', q', (verifyInteger_iff A b p' q').2 ⟨hq', ?_⟩, ?_, ?_⟩
  · have hw : (fun j => (p' j : ℝ) / q') = fun j => (w j : ℝ) := by
      funext j
      rw [heq j, he j]
      simp only [Rat.cast_div, Rat.cast_intCast]
    rw [hw]
    exact hf
  · simpa only [hqq] using hqs
  · intro j
    simpa only [hpp j] using hps j

/-- The integer verifier also provides complete short certificates for arbitrary
bounded rational rows after exact denominator clearing. -/
theorem exists_short_verified_rational_certificate {B : ℕ}
    (A : Matrix I (Fin n) ℚ) (b : I → ℚ) (lo hi : Fin n → ℝ)
    (hA : ∀ i j, CoeffBound B (A i j)) (hb : ∀ i, CoeffBound B (b i))
    (hbound : ∀ x ∈ polyhedron (A.map (fun z : ℚ => (z : ℝ))) (fun i => (b i : ℝ)),
      ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hn : (polyhedron (A.map (fun z : ℚ => (z : ℝ))) (fun i => (b i : ℝ))).Nonempty) :
    ∃ (p : Fin n → ℤ) (q : ℤ), verifyInteger (integerMatrix A b) (integerRhs A b) p q = true ∧
      q.natAbs.size ≤ n * (B * (n+1) + n) + 1 ∧
      ∀ j, (p j).natAbs.size ≤ n * (B * (n+1) + n) + 1 := by
  have hAi : ∀ i j, |integerMatrix A b i j| ≤ (2 : ℤ) ^ (B * (n+1)) :=
    fun i j => integerCoefficient_bound A b hA hb i (some j)
  have hbi : ∀ i, |integerRhs A b i| ≤ (2 : ℤ) ^ (B * (n+1)) :=
    fun i => integerCoefficient_bound A b hA hb i none
  have hbounds : ∀ x ∈ polyhedron ((integerMatrix A b).map (fun z : ℤ => (z : ℝ)))
      (fun i => (integerRhs A b i : ℝ)), ∀ j, lo j ≤ x j ∧ x j ≤ hi j := by
    rw [integer_polyhedron_eq]
    exact hbound
  have hne : (polyhedron ((integerMatrix A b).map (fun z : ℤ => (z : ℝ)))
      (fun i => (integerRhs A b i : ℝ))).Nonempty := by
    rw [integer_polyhedron_eq]
    exact hn
  exact exists_short_verified_integer_certificate (integerMatrix A b) (integerRhs A b)
    lo hi hAi hbi hbounds hne

end BalancedAssortments.PolyhedralBasis
