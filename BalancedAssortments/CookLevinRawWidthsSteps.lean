import BalancedAssortments.CookLevinRawWidths

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary

lemma rawHaltBody_width {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {old next : List Bool} (ho : old.length≤b) (hn : next.length≤b)
    (states cells symbols accepting : List (List Bool))
    (hs : ListWidths b states) (hc : ListWidths b cells) (ha : ListWidths b symbols) (hacc : ListWidths b accepting) :
    FormulaWidths (labelWidth b) (rawHaltBody d old next states cells symbols accepting).1 := by
  apply widths_rawAppend (rawAccept_width hd ho accepting hacc)
  apply widths_rawAppend
  · apply widths_rawFlatMap states
    intro s h
    exact widths_rawCopy (stateLabel_bounds hd ho (hs s h)).1 (stateLabel_bounds hd hn (hs s h)).1
  · apply widths_rawAppend
    · apply widths_rawFlatMap cells
      intro p h
      exact widths_rawCopy (headLabel_bounds hd ho (hc p h)).1 (headLabel_bounds hd hn (hc p h)).1
    · apply widths_rawFlatMap cells
      intro p hp
      apply widths_rawFlatMap symbols
      intro a haa
      exact widths_rawCopy (tapeLabel_bounds hd ho (hc p hp) (ha a haa)).1 (tapeLabel_bounds hd hn (hc p hp) (ha a haa)).1

lemma rawHeadTarget_width {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {next : List Bool} (hn : next.length≤b) (old : List Bool) (m : Move)
    (cells : List (List Bool)) (hc : ListWidths b cells) :
    FormulaWidths (labelWidth b) (rawHeadTarget d next old m cells).1 := by
  apply widths_rawSingle
  intro x hx
  rw [rawFlatMap_eq] at hx
  obtain ⟨cell,hcell,hx⟩ := List.mem_flatMap.mp hx
  dsimp only at hx
  split at hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact (headLabel_bounds hd hn (hc cell hcell)).1
  · simp at hx

lemma rawRuleBody_width {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {old next : List Bool} (ho : old.length≤b) (hn : next.length≤b)
    (cells symbols : List (List Bool)) (hc : ListWidths b cells) (ha : ListWidths b symbols)
    (r : RawRule) (hr : RuleWidths b r) :
    FormulaWidths (labelWidth b) (rawRuleBody d old next cells symbols r).1 := by
  apply widths_rawAppend (widths_rawForce (stateLabel_bounds hd ho hr.source).1)
  apply widths_rawAppend (widths_rawForce (stateLabel_bounds hd hn hr.target).1)
  apply widths_rawAppend
  · apply widths_rawFlatMap cells
    intro p hp
    apply widths_guardComputed true (headLabel_bounds hd ho (hc p hp)).1
    apply widths_rawAppend (widths_rawForce (tapeLabel_bounds hd ho (hc p hp) hr.read).1)
    exact widths_rawAppend (widths_rawForce (tapeLabel_bounds hd hn (hc p hp) hr.write).1)
      (rawHeadTarget_width hd hn p r.move cells hc)
  · apply widths_rawFlatMap cells
    intro p hp
    apply widths_guardComputed false (headLabel_bounds hd ho (hc p hp)).1
    apply widths_rawFlatMap symbols
    intro a haa
    exact widths_rawCopy (tapeLabel_bounds hd ho (hc p hp) (ha a haa)).1
      (tapeLabel_bounds hd hn (hc p hp) (ha a haa)).1

lemma rawTransitions_width {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    (steps states cells symbols accepting choices : List (List Bool)) (rules : List RawRule)
    (ht : ListWidths b steps) (hs : ListWidths b states) (hc : ListWidths b cells)
    (ha : ListWidths b symbols) (hacc : ListWidths b accepting) (hch : ListWidths b choices)
    (hr : ∀ r∈rules,RuleWidths b r)
    (hnext : ∀ t∈steps,(addCarry t [] true).1.length≤b) :
    FormulaWidths (labelWidth b) (rawTransitions d steps states cells symbols accepting choices rules).1 := by
  apply widths_rawFlatMap steps
  intro old hold
  have ho := ht old hold
  have hn := hnext old hold
  apply widths_rawFlatMap (choices.zip (none::rules.map some))
  intro entry he
  have hp := List.of_mem_zip he
  apply widths_guardComputed true (choiceLabel_bounds hd ho (hch entry.1 hp.1)).1
  cases hh : entry.2 with
  | none => exact rawHaltBody_width hd ho hn states cells symbols accepting hs hc ha hacc
  | some r =>
    have hrmem : r∈rules := by simpa [hh] using hp.2
    exact rawRuleBody_width hd ho hn cells symbols hc ha r (hr r hrmem)

end BalancedAssortments.CookLevin
