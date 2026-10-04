import BalancedAssortments.NPSATSubsetSumCorrect
import BalancedAssortments.ComplexityEncoding

/-! Positivity and genuine binary-size bounds for the indexed digit gadget.
The empty true instance has an explicit positive-target, positive-item image. -/
namespace BalancedAssortments.NPSATSubsetSum

lemma itemValue_pos {n m : ℕ} (F : IndexedFormula n m) (item : Item n m) :
    0 < itemValue F item := by
  unfold itemValue
  cases item with
  | inl v =>
    rcases v with ⟨i,b⟩
    apply pack_pos _ (finSumFinEquiv (Sum.inl i))
    simp only [Equiv.symm_apply_apply,digit]
    cases b <;> simp
  | inr v =>
    rcases v with ⟨j,b⟩
    apply pack_pos _ (finSumFinEquiv (Sum.inr j))
    simp only [Equiv.symm_apply_apply,digit,variableContribution]
    cases b <;> simp

lemma targetValue_pos {n m : ℕ} (h : 0 < n+m) : 0 < targetValue n m := by
  unfold targetValue
  apply pack_pos _ ⟨0,h⟩
  cases finSumFinEquiv.symm (⟨0,h⟩ : Fin (n+m)) <;> norm_num [targetDigit]

lemma pack_lt_ten_pow {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i,d i < 10) :
    pack d < 10^n := by
  apply (Nat.ofDigits_lt_base_pow_length (by decide : 1<10) ?_).trans_eq (by simp)
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact hd i

lemma pack_bit_size {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i,d i < 10) :
    (pack d).size ≤ 4*n := by
  apply Nat.size_le.mpr
  have hp : (10 : ℕ)^n ≤ (2^4)^n := Nat.pow_le_pow_left (by decide) n
  have he : ((2:ℕ)^4)^n = 2^(4*n) := (pow_mul _ _ _).symm
  exact (pack_lt_ten_pow d hd).trans_le (hp.trans_eq he)

lemma itemValue_bit_size {n m : ℕ} (F : IndexedFormula n m)
    (hF : ∀ j,(F j).length ≤ 3) (item : Item n m) :
    (itemValue F item).size ≤ 4*(n+m) := by
  apply pack_bit_size
  intro i
  simpa using selected_digits_lt_ten F hF {item} (finSumFinEquiv.symm i)

lemma targetValue_bit_size (n m : ℕ) : (targetValue n m).size ≤ 4*(n+m) := by
  apply pack_bit_size
  intro i
  cases finSumFinEquiv.symm i <;> norm_num [targetDigit]

/-- The entire self-delimiting target-plus-items bit string is polynomial in
the number of actual catalogued variables and clauses, not the largest label. -/
theorem serialized_gadget_size {n m : ℕ} (F : IndexedFormula n m)
    (hF : ∀ j,(F j).length ≤ 3) (items : List (Item n m)) (hlen : items.length ≤ 2*(n+m)) :
    (ComplexityEncoding.encodeFields (targetValue n m :: items.map (itemValue F))).length ≤
      16*(n+m)^2+10*(n+m)+1 := by
  have hb : ∀ x ∈ targetValue n m :: items.map (itemValue F), x.size ≤ 4*(n+m) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact targetValue_bit_size n m
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact itemValue_bit_size F hF i
  have hh := ComplexityEncoding.encodeFields_length_le _ (4*(n+m)) hb
  simp only [List.length_cons,List.length_map] at hh
  have hm := Nat.mul_le_mul_right (2*(4*(n+m))+1) (Nat.add_le_add_right hlen 1)
  nlinarith

lemma empty_formula_sat (F : IndexedFormula 0 0) : IndexedSat F := by
  exact ⟨fun i => i.elim0,fun j => j.elim0⟩

/-- Fixed positive yes-instance for an empty catalog/formula. -/
def emptyTarget : ℕ := 1
def emptyItems : Fin 1 → ℕ := fun _ => 1

theorem empty_positive_yes : 0 < emptyTarget ∧ (∀ i,0 < emptyItems i) ∧
    ∃ s : Finset (Fin 1), (∑ i ∈ s,emptyItems i) = emptyTarget := by
  refine ⟨by decide,fun i => by norm_num [emptyItems],Finset.univ,?_⟩
  norm_num [emptyItems,emptyTarget]

theorem empty_mapping_correct (F : IndexedFormula 0 0) :
    IndexedSat F ↔ ∃ s : Finset (Fin 1),(∑ i ∈ s,emptyItems i)=emptyTarget := by
  exact iff_of_true (empty_formula_sat F) empty_positive_yes.2.2

/-- A malformed source can be mapped to this fixed positive no-instance. -/
theorem fixed_positive_no :
    ¬ ∃ s : Finset (Fin 1),(∑ _i ∈ s,(2 : ℕ))=1 := by
  intro h
  obtain ⟨s,hs⟩ := h
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  omega
end BalancedAssortments.NPSATSubsetSum
