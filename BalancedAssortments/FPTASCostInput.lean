import BalancedAssortments.FPTASCostItems

/-! Instantiate the outer bounds using an explicit sum of canonical binary
input field lengths; this is polynomially equivalent to a standard self-delimiting
serialization and includes the accuracy parameter. -/
namespace BalancedAssortments.FPTASCost
open FPTAS PolyhedralBasis
open scoped BigOperators

def rationalBits (a : ℚ) : ℕ := a.num.natAbs.size + a.den.size

def inputBits {n : ℕ} (d : Input n) (ε : ℚ) : ℕ :=
  (n+1).size + d.K.size + rationalBits d.α + rationalBits ε +
    ∑ i, (rationalBits (d.r i) + rationalBits (d.v i))

lemma coefficient_from_bits (a : ℚ) : CoeffBound (rationalBits a) a :=
  CoeffBound.of_sizes (by unfold rationalBits; omega) (by unfold rationalBits; omega)

lemma nat_coefficient_from_size (k : ℕ) : CoeffBound k.size (k : ℚ) := by
  constructor
  · simpa using (show (k : ℤ) ≤ (2 : ℤ) ^ k.size by exact_mod_cast (Nat.lt_size_self k).le)
  · simp
    exact one_le_pow₀ (by norm_num)

lemma input_field_bounds {n : ℕ} (d : Input n) (ε : ℚ) :
    (∀ i, CoeffBound (inputBits d ε) (d.r i)) ∧
    (∀ i, CoeffBound (inputBits d ε) (d.v i)) ∧
    CoeffBound (inputBits d ε) d.α ∧ CoeffBound (inputBits d ε) ε ∧
    CoeffBound (inputBits d ε) (n+1 : ℚ) := by
  have hterm : ∀ i, rationalBits (d.r i) + rationalBits (d.v i) ≤
      ∑ j, (rationalBits (d.r j) + rationalBits (d.v j)) := fun i =>
    Finset.single_le_sum (f := fun j => rationalBits (d.r j) + rationalBits (d.v j))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply (coefficient_from_bits (d.r i)).mono
    have hh := hterm i
    unfold inputBits; omega
  · intro i
    apply (coefficient_from_bits (d.v i)).mono
    have hh := hterm i
    unfold inputBits; omega
  · apply (coefficient_from_bits d.α).mono
    unfold inputBits; omega
  · apply (coefficient_from_bits ε).mono
    unfold inputBits; omega
  · have hh := (nat_coefficient_from_size (n+1)).mono
      (show (n+1).size ≤ inputBits d ε by unfold inputBits; omega)
    simpa using hh

/-- The internal δ=ε/10 increases the input magnitude budget by only four bits. -/
theorem actual_input_bound {n : ℕ} (d : Input n) (ε : ℚ) :
    InputBitBound d (ε/10) (inputBits d ε + 4) := by
  obtain ⟨hr, hv, ha, he, hn⟩ := input_field_bounds d ε
  have hm : inputBits d ε ≤ inputBits d ε+4 := by omega
  have hten : CoeffBound 4 (10 : ℚ) := by norm_num [CoeffBound]
  exact ⟨fun i => (hr i).mono hm, fun i => (hv i).mono hm, ha.mono hm,
    he.div hten, hn.mono hm⟩

/-- The number of products is bounded by the summed actual input field length. -/
theorem product_count_le_inputBits {n : ℕ} (d : Input n) (ε : ℚ) :
    n+1 ≤ inputBits d ε := by
  have hterm : ∀ i : Fin (n+1), 1 ≤ rationalBits (d.r i) + rationalBits (d.v i) := by
    intro i
    have hp : 0 < (d.v i).den.size := Nat.size_pos.mpr (d.v i).den_pos
    unfold rationalBits
    omega
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hh
  unfold inputBits
  omega

lemma precision_parameter (ε : ℚ) : GridBounds.blockLength (ε/10) = ⌈10/ε⌉₊ := by
  unfold GridBounds.blockLength
  congr 1
  by_cases he : ε = 0
  · simp [he]
  · field_simp

/-- Initial field-width hypotheses for the actual DP calls are derived directly
from input bit lengths and reciprocal accuracy, not supplied externally. -/
theorem actual_call_field_widths {n : ℕ} (d : Input n) (ε : ℚ)
    {τ ρ : ℚ} (hτ : τ ∈ scales d (ε/10)) (hρ : ρ ∈ revenues d (ε/10)) :
    (KnapsackCostRational.encode
      ((ε/10) * maxList (((groups d (ε/10) τ ρ).flatten).map Knapsack.Item.profit) / (n+1))).Width
        (itemWidth (inputBits d ε+4) ⌈10/ε⌉₊) ∧
    ∀ g ∈ groups d (ε/10) τ ρ, ∀ it ∈ g,
      (KnapsackCostRational.encode it.value).Width (itemWidth (inputBits d ε+4) ⌈10/ε⌉₊) ∧
      (KnapsackCostRational.encode it.weight).Width (itemWidth (inputBits d ε+4) ⌈10/ε⌉₊) ∧
      (KnapsackCostRational.encode it.profit).Width (itemWidth (inputBits d ε+4) ⌈10/ε⌉₊) := by
  simpa only [precision_parameter] using call_field_widths d (ε/10) (actual_input_bound d ε) hτ hρ

end BalancedAssortments.FPTASCost
