import BalancedAssortments.NPSATSubsetSumDigits

namespace BalancedAssortments.NPSATSubsetSum

abbrev IndexedLiteral (n : ℕ) := Fin n × Bool
abbrev IndexedFormula (n m : ℕ) := Fin m → List (IndexedLiteral n)
abbrev Item (n m : ℕ) := (Fin n × Bool) ⊕ (Fin m × Bool)
abbrev Column (n m : ℕ) := Fin n ⊕ Fin m

def variableContribution {n m : ℕ} (c : List (IndexedLiteral n)) : Item n m → ℕ
  | .inl l => c.count l
  | .inr _ => 0

def digit {n m : ℕ} (F : IndexedFormula n m) (item : Item n m) : Column n m → ℕ
  | .inl i => (if item = .inl (i,false) then 1 else 0)+(if item = .inl (i,true) then 1 else 0)
  | .inr j => variableContribution (F j) item+
      (if item = .inr (j,false) then 1 else 0)+(if item = .inr (j,true) then 2 else 0)

def targetDigit {n m : ℕ} : Column n m → ℕ
  | .inl _ => 1
  | .inr _ => 4

def chosenCount {n m : ℕ} (s : Finset (Item n m)) (c : List (IndexedLiteral n)) : ℕ :=
  (c.map (fun l => if Sum.inl l ∈ s then 1 else 0)).sum

lemma contribution_cons {n m : ℕ} (l : IndexedLiteral n) (c : List (IndexedLiteral n))
    (item : Item n m) : variableContribution (l::c) item =
      (if item = .inl l then 1 else 0)+variableContribution c item := by
  cases item with
  | inl x => simp [variableContribution,List.count_cons]; split_ifs <;> simp_all <;> omega
  | inr x => simp [variableContribution]

lemma sum_contribution {n m : ℕ} (s : Finset (Item n m)) (c : List (IndexedLiteral n)) :
    ∑ item ∈ s,variableContribution c item = chosenCount s c := by
  induction c with
  | nil => simp [variableContribution,chosenCount]
  | cons l c ih =>
    simp only [contribution_cons,Finset.sum_add_distrib,ih,chosenCount,List.map_cons,List.sum_cons]
    simp

lemma chosenCount_le_length {n m : ℕ} (s : Finset (Item n m)) (c : List (IndexedLiteral n)) :
    chosenCount s c ≤ c.length := by
  induction c with
  | nil => simp [chosenCount]
  | cons l c ih => simp only [chosenCount,List.map_cons,List.sum_cons,List.length_cons] at *; split_ifs <;> omega

lemma sum_variable_digit {n m : ℕ} (F : IndexedFormula n m) (s : Finset (Item n m)) (i : Fin n) :
    (∑ item ∈ s,digit F item (.inl i)) =
      (if Sum.inl (i,false) ∈ s then 1 else 0)+(if Sum.inl (i,true) ∈ s then 1 else 0) := by
  simp [digit,Finset.sum_add_distrib]

lemma sum_clause_digit {n m : ℕ} (F : IndexedFormula n m) (s : Finset (Item n m)) (j : Fin m) :
    (∑ item ∈ s,digit F item (.inr j)) = chosenCount s (F j)+
      (if Sum.inr (j,false) ∈ s then 1 else 0)+(if Sum.inr (j,true) ∈ s then 2 else 0) := by
  simp [digit,Finset.sum_add_distrib,sum_contribution]

def itemValue {n m : ℕ} (F : IndexedFormula n m) (item : Item n m) : ℕ :=
  pack (fun i => digit F item (finSumFinEquiv.symm i))
def targetValue (n m : ℕ) : ℕ := pack (fun i : Fin (n+m) => targetDigit (finSumFinEquiv.symm i))

lemma selected_digits_lt_ten {n m : ℕ} (F : IndexedFormula n m) (hF : ∀ j,(F j).length ≤ 3)
    (s : Finset (Item n m)) (col : Column n m) : (∑ item ∈ s,digit F item col)<10 := by
  cases col with
  | inl i => rw [sum_variable_digit]; split_ifs <;> omega
  | inr j =>
    rw [sum_clause_digit]
    have h := chosenCount_le_length s (F j)
    have hh := hF j
    split_ifs <;> omega

theorem subset_sum_iff_digits {n m : ℕ} (F : IndexedFormula n m) (hF : ∀ j,(F j).length ≤ 3)
    (s : Finset (Item n m)) : (∑ item ∈ s,itemValue F item)=targetValue n m ↔
      ∀ col, (∑ item ∈ s,digit F item col)=targetDigit col := by
  unfold itemValue targetValue
  rw [subset_packed_iff _ _ _ (fun j => selected_digits_lt_ten F hF s _)
    (fun j => by cases finSumFinEquiv.symm j <;> simp [targetDigit])]
  constructor
  · intro h col
    simpa using h (finSumFinEquiv col)
  · intro h i; exact h _

end BalancedAssortments.NPSATSubsetSum
