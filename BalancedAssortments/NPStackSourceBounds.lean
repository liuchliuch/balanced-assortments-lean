import BalancedAssortments.NPStackSourceRead

namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros ComplexityTimeBinary ComplexityTimeReduction ComplexitySourceModel

lemma bits_length_le_self (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr n.lt_two_pow_self
lemma canonical_width (bits : List Bool) : (value bits).bits.length≤bits.length := by
  simpa [normalize_standard] using normalize_length bits
lemma triple_width (B : ℕ) : (3*B).bits.length≤B.bits.length+2 := by
  have hn := normalize_length (addCarry B.bits (false::B.bits) false).1
  rw [triple_normalized,value_bits] at hn
  have hl := addCarry_length B.bits (false::B.bits) false
  simp only [List.length_cons] at hl
  omega
lemma quintuple_width (B : ℕ) : (5*B).bits.length≤B.bits.length+3 := by
  have hn := normalize_length (addCarry B.bits (false::false::B.bits) false).1
  rw [quintuple_normalized,value_bits] at hn
  have hl := addCarry_length B.bits (false::false::B.bits) false
  simp only [List.length_cons] at hl
  omega
lemma price_width (B a : ℕ) : (3*B+a).bits.length≤B.bits.length+a.bits.length+3 := by
  have hn := normalize_length (addCarry (3*B).bits a.bits false).1
  rw [normalize_sum,value_bits,value_bits] at hn
  have hl := addCarry_length (3*B).bits a.bits false
  have ht := triple_width B
  omega

lemma itemFields_width (B a L : ℕ) (hB : B.bits.length≤L) (ha : a.bits.length≤L) :
    ∀ x ∈ itemNatFields B a,x.size≤2*L+3 := by
  have hp := price_width B a
  intro x hx
  simp only [itemNatFields,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← Nat.size_eq_bits_len];omega
  · simp
  · simp
  · rw [← Nat.size_eq_bits_len];omega
  · simp
  · rw [← Nat.size_eq_bits_len];omega

lemma bodyFields_length (B : ℕ) (done : List ℕ) :
    (done.flatMap (itemNatFields B)).length=6*done.length := by
  induction done <;> simp_all [itemNatFields] <;> omega

lemma bodyWire_bound (B : ℕ) (done : List ℕ) (L : ℕ)
    (hB : B.bits.length≤L) (ha : ∀ a∈done,a.bits.length≤L) :
    (bodyWire B done).length≤6*done.length*(4*L+7) := by
  have hh := ComplexityEncoding.encodeFields_length_le (done.flatMap (itemNatFields B)) (2*L+3) (by
    intro x hx
    obtain ⟨a,ha',hx⟩ := List.mem_flatMap.mp hx
    exact itemFields_width B a L hB (ha a ha') x hx)
  rw [bodyFields_length] at hh
  have he : 2*(2*L+3)+1=4*L+7 := by omega
  rw [he] at hh
  exact hh

/-- Binary count increment, price construction and all six signed product
fields are executed, with the old product records retained as a suffix. -/
theorem item_work_run (B a : ℕ) (done : List ℕ) (wi : List Bool) :
    ∃ cost≤1000*(B.bits.length+a.bits.length+done.length+5),Run program cost
      (cfg .countOne (store wi (bodyWire B done) B.bits a.bits (3*B).bits (5*B).bits
        (done.length+1).bits [] [] [] []))
      (cfg (.probe true) (stable wi (bodyWire B (a::done)) B.bits (3*B).bits (5*B).bits
        ((a::done).length+1).bits)) := by
  obtain ⟨t1,ht1,h1⟩ := count_increment_run wi (bodyWire B done) B.bits a.bits (3*B).bits (5*B).bits (done.length+1).bits
  simp only [value_bits] at h1
  obtain ⟨t2,ht2,h2⟩ := price_run wi (bodyWire B done) B.bits a.bits (3*B).bits (5*B).bits (done.length+1+1).bits
  simp only [value_bits] at h2
  have h3 := emit_item_run wi (bodyWire B done) B.bits a.bits (3*B).bits (5*B).bits (done.length+1+1).bits (3*B+a).bits
  have hh := (h1.trans h2).trans h3
  have hct := bits_length_le_self (done.length+1)
  have htr := triple_width B
  have hpr := price_width B a
  refine ⟨t1+t2+(7*a.bits.length+12*B.bits.length+7*(3*B+a).bits.length+48),?_,?_⟩
  · omega
  · simpa [List.length_cons,bodyWire_cons] using hh

def loopConstant : ℕ := fixedNoSource.length+10000
def loopBudget (L remaining : ℕ) : ℕ := (remaining+1)*loopConstant*(L+5)^2

lemma loopConstant_large : 10000≤loopConstant := by unfold loopConstant;omega

end BalancedAssortments.NPStackSourceReduction
