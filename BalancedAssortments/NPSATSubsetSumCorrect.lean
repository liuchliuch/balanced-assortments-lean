import BalancedAssortments.NPSATSubsetSumGadget

namespace BalancedAssortments.NPSATSubsetSum

def IndexedSat {n m : ℕ} (F : IndexedFormula n m) : Prop :=
  ∃ assignment : Fin n → Bool,∀ j,∃ l ∈ F j,assignment l.1=l.2

lemma chosenCount_pos_iff {n m : ℕ} (s : Finset (Item n m)) (c : List (IndexedLiteral n)) :
    0<chosenCount s c ↔ ∃ l ∈ c,Sum.inl l ∈ s := by
  induction c with
  | nil => simp [chosenCount]
  | cons l c ih =>
    simp only [chosenCount,List.map_cons,List.sum_cons] at *
    by_cases hl : Sum.inl l ∈ s
    · simp [hl]
    · simp [hl,ih]

theorem digit_solution_sound {n m : ℕ} (F : IndexedFormula n m) (s : Finset (Item n m))
    (h : ∀ col,(∑ item ∈ s,digit F item col)=targetDigit col) : IndexedSat F := by
  let assignment : Fin n → Bool := fun i => decide (Sum.inl (i,true) ∈ s)
  refine ⟨assignment,?_⟩
  intro j
  have hc := h (.inr j)
  rw [sum_clause_digit] at hc
  simp only [targetDigit] at hc
  have hpos : 0<chosenCount s (F j) := by split_ifs at hc <;> omega
  obtain ⟨l,hl,hchosen⟩ := (chosenCount_pos_iff s (F j)).mp hpos
  refine ⟨l,hl,?_⟩
  have hv := h (.inl l.1)
  rw [sum_variable_digit] at hv
  simp only [targetDigit] at hv
  rcases l with ⟨i,b⟩
  cases b with
  | true => simpa [assignment] using hchosen
  | false =>
    have hn : Sum.inl (i,true) ∉ s := by
      intro ht
      simp only [hchosen,ht,↓reduceIte] at hv
      omega
    simp [assignment,hn]

def truthCount {n : ℕ} (assignment : Fin n → Bool) (c : List (IndexedLiteral n)) : ℕ :=
  (c.map (fun l => if assignment l.1=l.2 then 1 else 0)).sum

noncomputable def witnessSubset {n m : ℕ} (F : IndexedFormula n m) (assignment : Fin n → Bool) : Finset (Item n m) := by
  classical
  exact Finset.univ.filter (fun item => match item with
    | .inl (i,b) => assignment i=b
    | .inr (j,b) => if b then truthCount assignment (F j) ≤ 2
        else truthCount assignment (F j)=1 ∨ truthCount assignment (F j)=3)

lemma chosenCount_witness {n m : ℕ} (F : IndexedFormula n m) (assignment : Fin n → Bool)
    (c : List (IndexedLiteral n)) : chosenCount (witnessSubset F assignment) c=truthCount assignment c := by
  simp [chosenCount,truthCount,witnessSubset]

lemma truthCount_le_length {n : ℕ} (assignment : Fin n → Bool) (c : List (IndexedLiteral n)) :
    truthCount assignment c≤c.length := by
  induction c with
  | nil => simp [truthCount]
  | cons l c ih => simp only [truthCount,List.map_cons,List.sum_cons,List.length_cons] at *; split_ifs <;> omega

lemma truthCount_pos_iff {n : ℕ} (assignment : Fin n → Bool) (c : List (IndexedLiteral n)) :
    0<truthCount assignment c ↔ ∃ l ∈ c,assignment l.1=l.2 := by
  induction c with
  | nil => simp [truthCount]
  | cons l c ih =>
    simp only [truthCount,List.map_cons,List.sum_cons] at *
    by_cases hl : assignment l.1=l.2
    · simp [hl]
    · simp [hl,ih]

theorem digit_solution_complete {n m : ℕ} (F : IndexedFormula n m)
    (hF : ∀ j,(F j).length≤3) (assignment : Fin n → Bool)
    (hsat : ∀ j,∃ l ∈ F j,assignment l.1=l.2) :
    ∀ col,(∑ item ∈ witnessSubset F assignment,digit F item col)=targetDigit col := by
  intro col
  cases col with
  | inl i =>
    rw [sum_variable_digit]
    cases ha : assignment i <;> simp [witnessSubset,ha,targetDigit]
  | inr j =>
    rw [sum_clause_digit,chosenCount_witness]
    have hp := (truthCount_pos_iff assignment (F j)).mpr (hsat j)
    have hu := (truthCount_le_length assignment (F j)).trans (hF j)
    simp only [witnessSubset,Finset.mem_filter,Finset.mem_univ,true_and,targetDigit,Bool.false_eq_true,↓reduceIte]
    split_ifs <;> omega

/-- The complete semantic reduction for indexed clauses of length at most three,
including repeated literals and empty clauses. -/
theorem indexed_sat_iff_subset_sum {n m : ℕ} (F : IndexedFormula n m)
    (hF : ∀ j,(F j).length≤3) :
    IndexedSat F ↔ ∃ s : Finset (Item n m),(∑ item ∈ s,itemValue F item)=targetValue n m := by
  constructor
  · rintro ⟨assignment,hsat⟩
    exact ⟨witnessSubset F assignment,(subset_sum_iff_digits F hF _).mpr
      (digit_solution_complete F hF assignment hsat)⟩
  · rintro ⟨s,hs⟩
    exact digit_solution_sound F s ((subset_sum_iff_digits F hF s).mp hs)

end BalancedAssortments.NPSATSubsetSum
