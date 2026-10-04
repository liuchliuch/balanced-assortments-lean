import BalancedAssortments.CookLevinRawInputBounds

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary

lemma builtFormula_analysis (M : Machine) (word : List Bool) (clock : List Unit) :
    let N := sourceBound M word.length clock.length
    CodeBound (formulaProfile N N).len (formulaProfile N N).cost (builtFormula M word clock) ∧
      FormulaWidths (labelWidth N) (builtFormula M word clock).1 := by
  let N := sourceBound M word.length clock.length
  let c := machineConstants M
  let d := builtDimensions M word clock
  let cells := (enumerateBits (rawWindowFuel word clock).1).1
  let steps := (enumerateBits clock).1
  let times := (enumerateBits (()::clock)).1
  let initial := (rawInputCells word clock).1
  have cb := machineConstants_bound M word.length clock.length
  have hd := builtDimensions_width M word clock
  have htN : clock.length+2≤N := sourceBound_clock M word clock
  have hwN : windowWidth word clock.length+2≤N := sourceBound_window M word clock
  have nt : times.length≤N := by
    change (enumerateFrom [] (()::clock)).1.length≤N
    rw [enumerateFrom_length]
    simp only [List.length_cons]
    omega
  have ns : steps.length≤N := by
    change (enumerateFrom [] clock).1.length≤N
    rw [enumerateFrom_length]
    omega
  have nc : cells.length≤N := by
    change (enumerateFrom [] (rawWindowFuel word clock).1).1.length≤N
    rw [enumerateFrom_length,rawWindowFuel_length]
    omega
  have wt : ListWidths N times := enumerateBits_width (()::clock) (by simp;omega)
  have ws : ListWidths N steps := enumerateBits_width clock (by omega)
  have wc : ListWidths N cells := enumerateBits_width _ (by rw [rawWindowFuel_length];omega)
  have wi : ListWidths N initial := fun x hx => (rawInputCells_width word clock x hx).trans (by omega)
  have wn : ∀ t∈steps,(addCarry t [] true).1.length≤N := by
    intro t ht
    have hh := enumerateFrom_width [] clock t ht
    simp only [List.length_nil,Nat.zero_add] at hh
    rw [addCarry_length]
    simp only [List.length_nil,Nat.max_zero]
    omega
  constructor
  · change CodeBound (formulaProfile N N).len (formulaProfile N N).cost
      (rawAppend (rawShape d times steps c.states cells c.symbols c.choices)
        (rawAppend (rawInitial d c.start cells initial)
          (rawAppend (rawAccept d d.t c.accepting)
            (rawTransitions d steps c.states cells c.symbols c.accepting c.choices c.rules))))
    apply bound_append (rawShape_bound hd times steps c.states cells c.symbols c.choices nt ns cb.states_length nc cb.symbols_length
      cb.choices_length wt ws cb.states_width wc cb.symbols_width cb.choices_width)
    apply bound_append (rawInitial_bound hd cb.start_width cells initial nc wc wi)
    apply bound_append (rawAccept_bound hd hd.t c.accepting cb.accepting_length cb.accepting_width)
    exact rawTransitions_bound hd steps c.states cells c.symbols c.accepting c.choices c.rules
      ns cb.states_length nc cb.symbols_length cb.accepting_length cb.choices_length cb.rules_length
      ws cb.states_width wc cb.symbols_width cb.accepting_width cb.choices_width cb.rules_width wn
  · change FormulaWidths (labelWidth N)
      (rawAppend (rawShape d times steps c.states cells c.symbols c.choices)
        (rawAppend (rawInitial d c.start cells initial)
          (rawAppend (rawAccept d d.t c.accepting)
            (rawTransitions d steps c.states cells c.symbols c.accepting c.choices c.rules)))).1
    apply widths_rawAppend (rawShape_width hd times steps c.states cells c.symbols c.choices
      wt ws cb.states_width wc cb.symbols_width cb.choices_width)
    apply widths_rawAppend (rawInitial_width hd cb.start_width cells initial wc wi)
    apply widths_rawAppend (rawAccept_width hd hd.t c.accepting cb.accepting_width)
    exact rawTransitions_width hd steps c.states cells c.symbols c.accepting c.choices c.rules
      ws cb.states_width wc cb.symbols_width cb.accepting_width cb.choices_width cb.rules_width wn

end BalancedAssortments.CookLevin
