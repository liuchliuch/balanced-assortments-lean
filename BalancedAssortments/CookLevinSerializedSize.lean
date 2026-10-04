import BalancedAssortments.CookLevinClauseWidth

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary

lemma bits_length_le_self (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.lt_two_pow_self

def tableauVariableCount (M : Machine) (n T : ℕ) : ℕ :=
  variableCount (M.stateExtra+1) (M.symbolExtra+3) (n+2*T+1) T (M.rules.length+1)

def tableauMeasureBudget (M : Machine) (n T : ℕ) : ℕ :=
  let V := tableauVariableCount M n T
  let C := clauseBudget M n T
  let L := clauseWidthBudget M (n+2*T+1)
  (V+3)*(V+C*L)+3*C+4

lemma rawTableau_measure (M : Machine) (word : List Bool) (T : ℕ) :
    Encoding.rawMeasure (rawTableau M word T) ≤ tableauMeasureBudget M word.length T := by
  let V := tableauVariableCount M word.length T
  have hv : ∀ x ∈ (rawTableau M word T).catalog,x.length≤V := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact (bits_length_le_self i).trans (Nat.le_of_lt (List.mem_range.mp hi))
  have hf : ∀ c ∈ (rawTableau M word T).formula,∀ l ∈ c,l.labelBits.length≤V := by
    intro c hc l hl
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hl
    exact (bits_length_le_self a.var).trans (Nat.le_of_lt (tableau_variables_bounded M word T d hd a ha))
  have hm := Encoding.rawMeasure_bound hv hf
  have hc := tableau_clause_count M word T
  have hl := tableau_literal_count M word T
  have hcat : (rawTableau M word T).catalog.length=V := by simp [rawTableau,V,tableauVariableCount,windowWidth]
  have hcl : (rawTableau M word T).formula.length=(tableauFormula M word T).length := by simp [rawTableau,encodeFormula]
  have hli : Encoding.bitLiteralCount (rawTableau M word T).formula=literalCount (tableauFormula M word T) := by
    simp [rawTableau,encodeFormula,Encoding.bitLiteralCount,literalCount,List.map_map,Function.comp_def]
  rw [hcat,hcl,hli] at hm
  have hh := Nat.mul_le_mul_left (V+3) (Nat.add_le_add_left hl V)
  change _≤(V+3)*(V+clauseBudget M word.length T*clauseWidthBudget M (windowWidth word T))+3*clauseBudget M word.length T+4
  omega

/-- Polynomial flat binary output size for the actual self-delimiting CNF. -/
theorem tableauBits_length (M : Machine) (word : List Bool) (T : ℕ) :
    (tableauBits M word T).length≤2*tableauMeasureBudget M word.length T := by
  have hh := Encoding.emit_length (rawTableau M word T)
  rw [Encoding.emit_eq] at hh
  exact hh.trans (Nat.mul_le_mul_left 2 (rawTableau_measure M word T))

/-- Only the emission stage is charged here. Constructing rawTableau and its
indices is not silently included in this bound. -/
theorem tableau_emission_cost (M : Machine) (word : List Bool) (T : ℕ) :
    (Encoding.emit (rawTableau M word T)).2≤32*(tableauMeasureBudget M word.length T+1) :=
  (Encoding.emit_cost _).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (rawTableau_measure M word T) 1))

end BalancedAssortments.CookLevin
