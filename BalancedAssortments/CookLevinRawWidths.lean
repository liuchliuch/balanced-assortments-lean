import BalancedAssortments.CookLevinRawCostTransitions

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary
open NPCNF.Encoding (BitLiteral BitClause BitFormula)

def FormulaWidths (b : ℕ) (F : BitFormula) : Prop := ∀ c∈F,∀ l∈c,l.labelBits.length≤b
lemma widths_append {b : ℕ} {F G : BitFormula} (hF : FormulaWidths b F) (hG : FormulaWidths b G) :
    FormulaWidths b (F++G) := by
  intro c hc l hl
  rcases List.mem_append.mp hc with hc|hc
  · exact hF c hc l hl
  · exact hG c hc l hl
lemma widths_rawAppend {b : ℕ} {F G : BitFormula × ℕ} (hF : FormulaWidths b F.1) (hG : FormulaWidths b G.1) :
    FormulaWidths b (rawAppend F G).1 := widths_append hF hG
lemma widths_rawFlatMap {α : Type*} {b : ℕ} (xs : List α) (f : α → BitFormula × ℕ)
    (h : ∀ x∈xs,FormulaWidths b (f x).1) : FormulaWidths b (rawFlatMap f xs).1 := by
  rw [rawFlatMap_eq]
  intro c hc l hl
  obtain ⟨x,hx,hc⟩ := List.mem_flatMap.mp hc
  exact h x hx c hc l hl
lemma widths_rawForce {b : ℕ} {label : List Bool × ℕ} (h : label.1.length≤b) : FormulaWidths b (rawForce label).1 := by
  intro c hc l hl
  simp only [rawForce,List.mem_singleton] at hc
  subst c
  simp only [List.mem_singleton] at hl
  subst l
  exact h
lemma widths_rawCopy {b : ℕ} {old next : List Bool × ℕ} (ho : old.1.length≤b) (hn : next.1.length≤b) :
    FormulaWidths b (rawCopy old next).1 := by
  intro c hc l hl
  simp only [rawCopy,List.mem_singleton] at hc
  subst c
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl|rfl
  · exact ho
  · exact hn
lemma widths_rawGuard {b : ℕ} {label : BitLiteral} {F : BitFormula}
    (hl : label.labelBits.length≤b) (hf : FormulaWidths b F) : FormulaWidths b (rawGuard label F).1 := by
  simp only [rawGuard,rawMap_eq]
  intro c hc l hll
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  rcases List.mem_cons.mp hll with rfl|hll
  · exact hl
  · exact hf d hd l hll
lemma widths_guardComputed {b : ℕ} (sign : Bool) {label : List Bool × ℕ} {body : BitFormula × ℕ}
    (hl : label.1.length≤b) (hb : FormulaWidths b body.1) :
    FormulaWidths b (rawGuardComputed sign label body).1 := widths_rawGuard hl hb
lemma widths_rawSingle {b : ℕ} {labels : List (List Bool) × ℕ}
    (hl : ListWidths b labels.1) : FormulaWidths b (rawSingle labels).1 := by
  intro c hc l hll
  simp only [rawSingle,List.mem_singleton] at hc
  subst c
  rw [rawMap_eq] at hll
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hll
  exact hl x hx
lemma widths_rawPair {b : ℕ} {x y : List Bool} (hx : x.length≤b) (hy : y.length≤b) :
    FormulaWidths b (rawPair x y).1 := by
  intro c hc l hl
  simp only [rawPair] at hc
  split at hc
  · simp at hc
  · simp only [List.mem_singleton] at hc
    subst c
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl|rfl
    · exact hx
    · exact hy
lemma widths_rawExactlyOne {b : ℕ} {labels : List (List Bool)} (h : ListWidths b labels) :
    FormulaWidths b (rawExactlyOne labels).1 := by
  intro c hc l hl
  simp only [rawExactlyOne,List.mem_cons] at hc
  rcases hc with rfl|hc
  · rw [rawMap_eq] at hl
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hl
    exact h x hx
  · exact widths_rawFlatMap labels _ (fun x hx => widths_rawFlatMap labels _
      (fun y hy => widths_rawPair (h x hx) (h y hy))) c hc l hl
lemma widths_family {b : ℕ} (xs : List (List Bool)) (f : List Bool → List Bool × ℕ)
    (h : ∀ x∈xs,(f x).1.length≤b) : FormulaWidths b (rawExactlyOne (rawMap f xs).1).1 := by
  apply widths_rawExactlyOne
  intro x hx
  rw [rawMap_eq] at hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  exact h y hy

lemma rawShape_width {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    (times steps states cells symbols rules : List (List Bool))
    (ht : ListWidths b times) (hs : ListWidths b steps) (hq : ListWidths b states)
    (hw : ListWidths b cells) (hg : ListWidths b symbols) (hr : ListWidths b rules) :
    FormulaWidths (labelWidth b) (rawShape d times steps states cells symbols rules).1 := by
  apply widths_rawAppend
  · apply widths_rawFlatMap times
    intro time htime
    apply widths_rawAppend
    · exact widths_family states _ (fun s h => (stateLabel_bounds hd (ht time htime) (hq s h)).1)
    · apply widths_rawAppend
      · exact widths_family cells _ (fun p h => (headLabel_bounds hd (ht time htime) (hw p h)).1)
      · apply widths_rawFlatMap cells
        intro cell hcell
        exact widths_family symbols _ (fun a h => (tapeLabel_bounds hd (ht time htime) (hw cell hcell) (hg a h)).1)
  · apply widths_rawFlatMap steps
    intro time htime
    exact widths_family rules _ (fun r h => (choiceLabel_bounds hd (hs time htime) (hr r h)).1)

lemma rawAccept_width {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {time : List Bool} (ht : time.length≤b) (accepting : List (List Bool)) (ha : ListWidths b accepting) :
    FormulaWidths (labelWidth b) (rawAccept d time accepting).1 := by
  apply widths_rawSingle
  intro x hx
  rw [rawMap_eq] at hx
  obtain ⟨a,haa,rfl⟩ := List.mem_map.mp hx
  exact (stateLabel_bounds hd ht (ha a haa)).1

lemma rawInitial_width {b : ℕ} {d : RawDimensions} (hd : DimensionWidths b d)
    {start : List Bool} (hs : start.length≤b) (cells symbols : List (List Bool))
    (hc : ListWidths b cells) (ha : ListWidths b symbols) :
    FormulaWidths (labelWidth b) (rawInitial d start cells symbols).1 := by
  apply widths_rawAppend (widths_rawForce (stateLabel_bounds hd (Nat.zero_le _) hs).1)
  apply widths_rawAppend (widths_rawForce (headLabel_bounds hd (Nat.zero_le _) hd.t).1)
  apply widths_rawFlatMap (cells.zip symbols)
  intro pair hpair
  have hp := List.of_mem_zip hpair
  exact widths_rawForce (tapeLabel_bounds hd (Nat.zero_le _) (hc pair.1 hp.1) (ha pair.2 hp.2)).1

end BalancedAssortments.CookLevin
