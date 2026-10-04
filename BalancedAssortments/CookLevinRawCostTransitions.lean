import BalancedAssortments.CookLevinRawCostRule

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary

def bodyProfile (N b : ℕ) : CostProfile :=
  ⟨(haltProfile N b).len+(ruleProfile N b).len,(haltProfile N b).cost+(ruleProfile N b).cost⟩
def choicesProfile (N b : ℕ) : CostProfile := CostProfile.loop N ((bodyProfile N b).guarded b)
def transitionProfile (N b : ℕ) : CostProfile :=
  CostProfile.loop N ⟨(choicesProfile N b).len,16*b+1+(choicesProfile N b).cost+2*N+8⟩

lemma rawTransitions_bound {N b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    (steps states cells symbols accepting choices : List (List Bool)) (rules : List RawRule)
    (nt : steps.length≤N) (ns : states.length≤N) (nc : cells.length≤N)
    (na : symbols.length≤N) (nacc : accepting.length≤N) (nch : choices.length≤N) (nr : rules.length≤N)
    (ht : ListWidths b steps) (hs : ListWidths b states) (hc : ListWidths b cells)
    (ha : ListWidths b symbols) (hacc : ListWidths b accepting) (hch : ListWidths b choices)
    (hr : ∀ r∈rules,RuleWidths b r)
    (hnext : ∀ t∈steps,(addCarry t [] true).1.length≤b) :
    CodeBound (transitionProfile N b).len (transitionProfile N b).cost
      (rawTransitions d steps states cells symbols accepting choices rules) := by
  apply bound_flatMap steps _ nt
  intro old hold
  have ho := ht old hold
  have hn := hnext old hold
  let next := (addCarry old [] true).1
  let f := fun entry : List Bool × Option RawRule =>
    let body := match entry.2 with
      | none => rawHaltBody d old next states cells symbols accepting
      | some rule => rawRuleBody d old next cells symbols rule
    rawGuardComputed true (choiceLabel d old entry.1) body
  have hf : ∀ entry∈choices.zip (none::rules.map some),
      CodeBound ((bodyProfile N b).guarded b).len ((bodyProfile N b).guarded b).cost (f entry) := by
    intro entry he
    have hp := List.of_mem_zip he
    have hl := (choiceLabel_bounds hd ho (hch entry.1 hp.1)).2
    apply bound_guard true hl
    cases hh : entry.2 with
    | none =>
      exact (rawHaltBody_bound hd ho hn states cells symbols accepting ns nc na nacc hs hc ha hacc).mono
        (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    | some r =>
      have hrmem : r∈rules := by simpa [hh] using hp.2
      exact (rawRuleBody_bound hd ho hn cells symbols nc na hc ha r (hr r hrmem)).mono
        (Nat.le_add_left _ _) (Nat.le_add_left _ _)
  have hzip : (choices.zip (none::rules.map some)).length≤N := by
    simpa only [List.length_zip] using (Nat.min_le_left choices.length (none::rules.map some).length).trans nch
  have hb := bound_flatMap _ f hzip hf
  have hu : (addCarry old [] true).2≤16*b+1 := by simp only [addCarry_cost,List.length_nil,Nat.max_zero];omega
  constructor
  · exact hb.length_le
  · change (addCarry old [] true).2+(rawFlatMap f (choices.zip (none::rules.map some))).2+rules.length+choices.length+8≤_
    have hh := hb.cost_le
    change _≤16*b+1+(choicesProfile N b).cost+2*N+8
    change (rawFlatMap f (choices.zip (none::rules.map some))).2≤(choicesProfile N b).cost at hh
    omega

def formulaProfile (N b : ℕ) : CostProfile :=
  (shapeProfile N b).append ((initialProfile N b).append ((acceptProfile N b).append (transitionProfile N b)))

end BalancedAssortments.CookLevin
