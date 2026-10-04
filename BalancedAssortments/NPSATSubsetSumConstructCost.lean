import BalancedAssortments.NPSATSubsetSumConstruct
import BalancedAssortments.NPCNFMeasure

namespace BalancedAssortments.NPSATSubsetSum
open ComplexityTimeBinary NPCNF.Encoding

lemma variableColumns_length (label : List Bool) (catalog : List (List Bool)) :
    (variableColumns label catalog).1.length = catalog.length := by
  induction catalog <;> simp_all [variableColumns]
lemma variableColumns_width (label : List Bool) (catalog : List (List Bool)) :
    ∀ d ∈ (variableColumns label catalog).1,d.length ≤ 1 := by
  induction catalog with
  | nil => simp [variableColumns]
  | cons x xs ih =>
    intro d hd
    simp only [variableColumns,List.mem_cons] at hd
    rcases hd with rfl | hd
    · split_ifs <;> simp
    · exact ih d hd
lemma variableColumns_cost {label : List Bool} {catalog : List (List Bool)} {b : ℕ}
    (hl : label.length ≤ b) (hc : ∀ x ∈ catalog,x.length ≤ b) :
    (variableColumns label catalog).2 ≤ catalog.length*(24*(b+1))+1 := by
  induction catalog with
  | nil => simp [variableColumns]
  | cons x xs ih =>
    have hm : max x.length label.length ≤ b := max_le (hc x (by simp)) hl
    have ht := ih (fun y hy => hc y (by simp [hy]))
    simp only [variableColumns,compareBits_cost,List.length_cons]
    nlinarith

lemma clauseColumns_length (label : List Bool) (polarity : Bool) (F : BitFormula) :
    (clauseColumns label polarity F).1.length = F.length := by
  induction F <;> simp_all [clauseColumns]
lemma clauseColumns_width (label : List Bool) (polarity : Bool) (F : BitFormula) {L : ℕ}
    (hc : ∀ c ∈ F,c.length ≤ L) : ∀ d ∈ (clauseColumns label polarity F).1,d.length ≤ L+1 := by
  induction F with
  | nil => simp [clauseColumns]
  | cons c cs ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact (occurrenceBits_length label polarity c).trans (Nat.add_le_add_right (hc c (by simp)) 1)
    · exact ih (fun c hc' => hc c (by simp [hc'])) d hd
lemma clauseColumns_cost (label : List Bool) (polarity : Bool) (F : BitFormula) {L : ℕ}
    (hl : label.length ≤ L) (hc : ∀ c ∈ F,c.length ≤ L ∧ ∀ l ∈ c,l.labelBits.length ≤ L) :
    (clauseColumns label polarity F).2 ≤ F.length*(64*(L+1)^3+4)+1 := by
  induction F with
  | nil => simp [clauseColumns]
  | cons c cs ih =>
    have hh := hc c (by simp)
    have ho := occurrenceBits_cost label polarity c L hl hh.2
    have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hh.1 1) 2
    have hmul := Nat.mul_le_mul_right (L+1) (Nat.mul_le_mul_left 64 hsq)
    have ht := ih (fun c hc' => hc c (by simp [hc']))
    simp only [clauseColumns,List.length_cons]
    nlinarith

def packingBudget (L : ℕ) : ℕ := 4096*(2*L+1)^2*(L+13)^2
def integerWidth (L : ℕ) : ℕ := 2*L*(L+12)
def itemBudget (L : ℕ) : ℕ := L*(24*(L+1))+L*(64*(L+1)^3+4)+packingBudget L+L+8

lemma packing_bounds {digits : List (List Bool)} {L : ℕ}
    (hlen : digits.length ≤ 2*L) (hw : ∀ d ∈ digits,d.length ≤ L+3) :
    (packBits digits).1.length ≤ integerWidth L ∧ (packBits digits).2 ≤ packingBudget L := by
  have hl := packBits_length digits (L+3) hw
  have hc := packBits_cost digits (L+3) hw
  have hmul := Nat.mul_le_mul_right (L+12) hlen
  have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) 2
  have hprod := Nat.mul_le_mul_right ((L+13)^2) (Nat.mul_le_mul_left 4096 hsq)
  simp only [show L+3+9=L+12 by omega] at hl
  simp only [show L+3+10=L+13 by omega] at hc
  exact ⟨hl.trans hmul,hc.trans hprod⟩

lemma list_nat_le_sum {xs : List ℕ} {x : ℕ} (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have hh := ih h
      simp only [List.sum_cons]
      omega

lemma raw_clause_length {input : Raw} {c : BitClause} (hc : c ∈ input.formula) : c.length ≤ rawMeasure input := by
  have hm : c.length ∈ input.formula.map List.length := List.mem_map.mpr ⟨c,hc,rfl⟩
  have hh : c.length ≤ bitLiteralCount input.formula := by
    exact list_nat_le_sum hm
  exact hh.trans (rawMeasure_counts input).2.2

lemma variableItem_bounds (input : Raw) {label : List Bool} (hl : label ∈ input.catalog) (polarity : Bool) :
    (variableItem input.catalog input.formula label polarity).1.length ≤ integerWidth (rawMeasure input) ∧
    (variableItem input.catalog input.formula label polarity).2 ≤ itemBudget (rawMeasure input) := by
  let L := rawMeasure input
  have hw := rawMeasure_widths input
  have hn := rawMeasure_counts input
  have hlabel := hw.1 label hl
  have hvars := variableColumns_cost hlabel hw.1
  have hclauses := clauseColumns_cost label polarity input.formula hlabel
    (fun c hc => ⟨raw_clause_length hc,hw.2 c hc⟩)
  have hdigitslen : ((variableColumns label input.catalog).1++(clauseColumns label polarity input.formula).1).length ≤ 2*L := by
    simp only [List.length_append,variableColumns_length,clauseColumns_length]
    omega
  have hdigitswidth : ∀ d ∈ (variableColumns label input.catalog).1++(clauseColumns label polarity input.formula).1,
      d.length ≤ L+3 := by
    intro d hd
    rcases List.mem_append.mp hd with hv | hc
    · exact (variableColumns_width label input.catalog d hv).trans (by omega)
    · exact (clauseColumns_width label polarity input.formula (fun c hc => raw_clause_length hc) d hc).trans (by omega)
  obtain ⟨hpw,hpc⟩ := packing_bounds hdigitslen hdigitswidth
  refine ⟨hpw,?_⟩
  have hm₁ := Nat.mul_le_mul_right (24*(L+1)) hn.1
  have hm₂ := Nat.mul_le_mul_right (64*(L+1)^3+4) hn.2.1
  simp only [variableItem,variableColumns_length,itemBudget]
  change (variableColumns label input.catalog).2 ≤ input.catalog.length*(24*(L+1))+1 at hvars
  change (clauseColumns label polarity input.formula).2 ≤ input.formula.length*(64*(L+1)^3+4)+1 at hclauses
  dsimp only [L] at *
  omega

lemma variableItems_length (catalog : List (List Bool)) (F : BitFormula) (labels : List (List Bool)) :
    (variableItems catalog F labels).1.length = 2*labels.length := by
  induction labels <;> simp_all [variableItems] <;> omega

lemma variableItems_bounds (input : Raw) (labels : List (List Bool))
    (hl : ∀ label ∈ labels,label ∈ input.catalog) :
    (∀ x ∈ (variableItems input.catalog input.formula labels).1,x.length ≤ integerWidth (rawMeasure input)) ∧
    (variableItems input.catalog input.formula labels).2 ≤ labels.length*(2*itemBudget (rawMeasure input)+6)+1 := by
  induction labels with
  | nil => simp [variableItems]
  | cons label labels ih =>
    have hno := variableItem_bounds input (hl label (by simp)) false
    have hyes := variableItem_bounds input (hl label (by simp)) true
    obtain ⟨htw,htc⟩ := ih (fun l hl' => hl l (by simp [hl']))
    constructor
    · intro x hx
      simp only [variableItems,List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hno.1
      · exact hyes.1
      · exact htw x hx
    · simp only [variableItems,List.length_cons]
      nlinarith

lemma prependZero_cost (rows : List (List (List Bool))) : (prependZero rows).2 = 4*rows.length+1 := by
  induction rows <;> simp_all [prependZero] <;> omega
lemma slackColumns_length {α : Type*} (xs : List α) : (slackColumns xs).1.length = 2*xs.length := by
  induction xs <;> simp_all [slackColumns,prependZero_eq] <;> omega

lemma slackColumns_shape {α : Type*} (xs : List α) :
    ∀ row ∈ (slackColumns xs).1,row.length = xs.length ∧ ∀ digit ∈ row,digit.length ≤ 2 := by
  induction xs with
  | nil => simp [slackColumns]
  | cons x xs ih =>
    intro row hrow
    simp only [slackColumns,List.mem_cons,prependZero_eq,List.mem_map] at hrow
    rcases hrow with rfl | rfl | ⟨tail,htail,rfl⟩
    · simp [zeroColumns_eq]
    · simp [zeroColumns_eq]
    · obtain ⟨hlen,hw⟩ := ih tail htail
      exact ⟨by simp [hlen],by intro d hd; rcases List.mem_cons.mp hd with rfl | hd; simp; exact hw d hd⟩

lemma slackColumns_cost {α : Type*} (xs : List α) : (slackColumns xs).2 ≤ 16*(xs.length+1)^2 := by
  induction xs with
  | nil => simp [slackColumns]
  | cons x xs ih =>
    simp only [slackColumns,zeroColumns_cost,prependZero_cost,slackColumns_length,List.length_cons]
    nlinarith

lemma packSlack_length (padding : List (List Bool)) (rows : List (List (List Bool))) :
    (packSlack padding rows).1.length = rows.length := by
  induction rows <;> simp_all [packSlack]

lemma packSlack_bounds {padding : List (List Bool)} {rows : List (List (List Bool))} {L : ℕ}
    (hpl : padding.length ≤ L) (hpw : ∀ d ∈ padding,d.length ≤ L+3)
    (hr : ∀ row ∈ rows,row.length ≤ L ∧ ∀ d ∈ row,d.length ≤ L+3) :
    (∀ x ∈ (packSlack padding rows).1,x.length ≤ integerWidth L) ∧
    (packSlack padding rows).2 ≤ rows.length*(packingBudget L+L+4)+1 := by
  induction rows with
  | nil => simp [packSlack]
  | cons row rows ih =>
    have hrow := hr row (by simp)
    have hh := packing_bounds (L := L) (digits := padding++row)
      (by simp only [List.length_append];omega)
      (by intro d hd; exact (List.mem_append.mp hd).elim (hpw d) (hrow.2 d))
    obtain ⟨htw,htc⟩ := ih (fun r hr' => hr r (by simp [hr']))
    constructor
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hh.1
      · exact htw x hx
    · simp only [packSlack,List.length_cons]
      nlinarith

def constructBudget (L : ℕ) : ℕ :=
  (L*(2*itemBudget L+6)+1)+(3*L+1)+16*(L+1)^2+
    (2*L*(packingBudget L+L+4)+1)+(5*L+4)+packingBudget L+2*L+12

/-- Complete raw binary gadget bounds. Numeric variable-label magnitudes are
absent: only the serialized structural/bit measure controls the construction. -/
theorem construct_bounds (input : Raw) :
    (construct input).1.1.length ≤ integerWidth (rawMeasure input) ∧
    (construct input).1.2.length ≤ 4*rawMeasure input ∧
    (∀ x ∈ (construct input).1.2,x.length ≤ integerWidth (rawMeasure input)) ∧
    (construct input).2 ≤ constructBudget (rawMeasure input) := by
  let L := rawMeasure input
  have hn := rawMeasure_counts input
  have hv := variableItems_bounds input input.catalog (fun _ h => h)
  have hzero : (zeroColumns input.catalog).1.length ≤ L := by simpa [zeroColumns_eq] using hn.1
  have hzwidth : ∀ d ∈ (zeroColumns input.catalog).1,d.length ≤ L+3 := by
    intro d hd
    simp only [zeroColumns_eq,List.mem_replicate] at hd
    rcases hd with ⟨_,rfl⟩
    simp
  have hsrows := slackColumns_shape input.formula
  have hsp : ∀ row ∈ (slackColumns input.formula).1,row.length ≤ L ∧ ∀ d ∈ row,d.length ≤ L+3 := by
    intro row hr
    obtain ⟨hlen,hwidth⟩ := hsrows row hr
    refine ⟨?_,fun d hd => (hwidth d hd).trans (by omega)⟩
    rw [hlen]
    exact hn.2.1
  obtain ⟨hpackedWidth,hpackedCost⟩ := packSlack_bounds hzero hzwidth hsp
  have htargetLen : (targetColumns input.catalog input.formula).1.length ≤ 2*L := by
    simp only [targetColumns,List.length_append,List.length_map]
    omega
  have htargetWidth : ∀ d ∈ (targetColumns input.catalog input.formula).1,d.length ≤ L+3 := by
    intro d hd
    simp only [targetColumns,List.mem_append,List.mem_map] at hd
    rcases hd with ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩ <;> simp <;> omega
  obtain ⟨htw,htc⟩ := packing_bounds htargetLen htargetWidth
  refine ⟨htw,?_,?_,?_⟩
  · simp only [construct,List.length_append,variableItems_length,packSlack_length,slackColumns_length]
    omega
  · intro x hx
    simp only [construct,List.mem_append] at hx
    exact hx.elim (hv.1 x) (hpackedWidth x)
  · have hvar := Nat.mul_le_mul_right (2*itemBudget L+6) hn.1
    have hzeroCost := zeroColumns_cost input.catalog
    have hslackCost := slackColumns_cost input.formula
    have hslackSq := Nat.pow_le_pow_left (Nat.add_le_add_right hn.2.1 1) 2
    rw [slackColumns_length] at hpackedCost
    have hpack := Nat.mul_le_mul_right (packingBudget L+L+4) (Nat.mul_le_mul_left 2 hn.2.1)
    simp only [construct,targetColumns,variableItems_length,constructBudget]
    have hvc := hv.2
    simp only [targetColumns] at htc
    change (variableItems input.catalog input.formula input.catalog).2 ≤ input.catalog.length*(2*itemBudget L+6)+1 at hvc
    dsimp only [L] at *
    omega

lemma construct_cost (input : Raw) : (construct input).2 ≤ constructBudget (rawMeasure input) :=
  (construct_bounds input).2.2.2
lemma construct_target_width (input : Raw) : (construct input).1.1.length ≤ integerWidth (rawMeasure input) :=
  (construct_bounds input).1
lemma construct_items_width (input : Raw) :
    ∀ x ∈ (construct input).1.2,x.length ≤ integerWidth (rawMeasure input) :=
  (construct_bounds input).2.2.1
lemma construct_items_length (input : Raw) : (construct input).1.2.length ≤ 4*rawMeasure input :=
  (construct_bounds input).2.1

lemma constructBudget_mono {L M : ℕ} (h : L ≤ M) : constructBudget L ≤ constructBudget M := by
  dsimp only [constructBudget,itemBudget,packingBudget]
  gcongr
lemma integerWidth_mono {L M : ℕ} (h : L ≤ M) : integerWidth L ≤ integerWidth M := by
  unfold integerWidth
  gcongr

/-- After parsing, the gadget's time is bounded by an explicit fifth-degree
polynomial expression in the original bitstring length, without input promises. -/
theorem construct_cost_of_parse {bits : List Bool} {input : Raw}
    (h : (NPCNF.Encoding.parse bits).1 = some input) : (construct input).2 ≤ constructBudget bits.length :=
  (construct_cost input).trans (constructBudget_mono (parsed_rawMeasure_bound h))

end BalancedAssortments.NPSATSubsetSum

