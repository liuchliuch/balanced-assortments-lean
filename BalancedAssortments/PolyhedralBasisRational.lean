import BalancedAssortments.PolyhedralBasisCertificates
import BalancedAssortments.RationalClearing

/-! Polynomial-size rational witnesses for nonempty bounded rational polyhedra.
No LP vertex or rational-witness existence hypothesis is assumed. -/
noncomputable section
namespace BalancedAssortments.PolyhedralBasis
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

def augmentedRow (A : Matrix I (Fin n) ℚ) (b : I → ℚ) (i : I) : Option (Fin n) → ℚ
  | none => b i
  | some j => A i j

def rowDenominator (A : Matrix I (Fin n) ℚ) (b : I → ℚ) (i : I) : ℕ :=
  RationalClearing.commonDenominator (fun j => (augmentedRow A b i j).den)

def integerCoefficient (A : Matrix I (Fin n) ℚ) (b : I → ℚ) (i : I)
    (j : Option (Fin n)) : ℤ :=
  RationalClearing.clearedNumerator (fun k => (augmentedRow A b i k).num)
    (fun k => (augmentedRow A b i k).den) j

def integerMatrix (A : Matrix I (Fin n) ℚ) (b : I → ℚ) : Matrix I (Fin n) ℤ :=
  fun i j => integerCoefficient A b i (some j)

def integerRhs (A : Matrix I (Fin n) ℚ) (b : I → ℚ) : I → ℤ :=
  fun i => integerCoefficient A b i none

lemma rowDenominator_positive (A : Matrix I (Fin n) ℚ) (b : I → ℚ) (i : I) :
    0 < rowDenominator A b i :=
  RationalClearing.commonDenominator_pos _ (fun j => Rat.den_pos _)

lemma integerCoefficient_real (A : Matrix I (Fin n) ℚ) (b : I → ℚ) (i : I)
    (j : Option (Fin n)) :
    (integerCoefficient A b i j : ℝ) =
      (rowDenominator A b i : ℝ) * (augmentedRow A b i j : ℝ) := by
  have h := (RationalClearing.rational_clearing_identity (augmentedRow A b i) j).symm
  exact_mod_cast h

/-- Row-wise denominator clearing preserves the whole real feasible set exactly. -/
theorem integer_polyhedron_eq (A : Matrix I (Fin n) ℚ) (b : I → ℚ) :
    polyhedron ((integerMatrix A b).map (fun z : ℤ => (z : ℝ)))
      (fun i => (integerRhs A b i : ℝ)) =
    polyhedron (A.map (fun z : ℚ => (z : ℝ))) (fun i => (b i : ℝ)) := by
  ext x
  apply forall_congr'
  intro i
  have hD : (0 : ℝ) < rowDenominator A b i := by exact_mod_cast rowDenominator_positive A b i
  have he : evaluate ((integerMatrix A b).map (fun z : ℤ => (z : ℝ))) x i =
      (rowDenominator A b i : ℝ) * evaluate (A.map (fun z : ℚ => (z : ℝ))) x i := by
    unfold evaluate integerMatrix
    simp only [Matrix.map_apply, integerCoefficient_real, augmentedRow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change evaluate ((integerMatrix A b).map (fun z : ℤ => (z : ℝ))) x i ≤
    (integerCoefficient A b i none : ℝ) ↔ _
  rw [he, integerCoefficient_real]
  exact mul_le_mul_iff_right₀ hD

/-- A canonical per-coefficient binary magnitude bound. -/
def CoeffBound (B : ℕ) (a : ℚ) : Prop :=
  |a.num| ≤ (2 : ℤ) ^ B ∧ (a.den : ℤ) ≤ (2 : ℤ) ^ B

lemma integerCoefficient_bound {B : ℕ} (A : Matrix I (Fin n) ℚ) (b : I → ℚ)
    (hA : ∀ i j, CoeffBound B (A i j)) (hb : ∀ i, CoeffBound B (b i))
    (i : I) (j : Option (Fin n)) :
    |integerCoefficient A b i j| ≤ (2 : ℤ) ^ (B * (n + 1)) := by
  have hrow : ∀ k, CoeffBound B (augmentedRow A b i k) := by
    intro k
    cases k with
    | none => exact hb i
    | some k => exact hA i k
  have h := RationalClearing.cleared_abs_le
    (fun k => (augmentedRow A b i k).num) (fun k => (augmentedRow A b i k).den)
    (fun k => (hrow k).1) (fun k => (hrow k).2) j
  simpa [integerCoefficient, Fintype.card_option] using h

/-- Nonempty bounded rational systems have polynomial-size rational certificates.
The explicit bound includes denominator clearing and the derived active basis. -/
theorem bounded_rational_polyhedron_certificate {B : ℕ}
    (A : Matrix I (Fin n) ℚ) (b : I → ℚ) (lo hi : Fin n → ℝ)
    (hA : ∀ i j, CoeffBound B (A i j)) (hb : ∀ i, CoeffBound B (b i))
    (hbound : ∀ x ∈ polyhedron (A.map (fun z : ℚ => (z : ℝ))) (fun i => (b i : ℝ)),
      ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hn : (polyhedron (A.map (fun z : ℚ => (z : ℝ))) (fun i => (b i : ℝ))).Nonempty) :
    ∃ (w : Fin n → ℚ) (p : Fin n → ℤ) (q : ℤ), q ≠ 0 ∧
      q.natAbs.size ≤ n * (B * (n + 1) + n) + 1 ∧
      (∀ j, (p j).natAbs.size ≤ n * (B * (n + 1) + n) + 1) ∧
      (∀ j, w j = (p j : ℚ) / q) ∧
      (fun j => (w j : ℝ)) ∈ polyhedron
        (A.map (fun z : ℚ => (z : ℝ))) (fun i => (b i : ℝ)) := by
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
  obtain ⟨w, p, q, hq, hqs, hps, he, hf⟩ := bounded_integer_polyhedron_certificate
    (integerMatrix A b) (integerRhs A b) lo hi hAi hbi hbounds hne
  rw [integer_polyhedron_eq] at hf
  exact ⟨w, p, q, hq, hqs, hps, he, hf⟩

end BalancedAssortments.PolyhedralBasis
