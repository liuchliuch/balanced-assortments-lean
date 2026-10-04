import BalancedAssortments.NPCNFStackValidateCorrect
import BalancedAssortments.NPCNFMeasure
import BalancedAssortments.NPStackFieldsEncode

namespace BalancedAssortments.NPCNF.StackValidate
open NPStackFields (dataFields tagBits)
open Encoding

lemma fieldVolume_le_tagged (fs : List (List Bool)) : fieldVolume fs ≤ (dataFields fs).length := by
  induction fs with
  | nil => rfl
  | cons x xs ih =>
    simp only [fieldVolume,List.map_cons,List.sum_cons,dataFields,List.flatMap_cons,List.length_append,
      List.length_singleton,NPStackFieldData.tagBits_length] at *
    omega

lemma tagged_le_twice_fieldVolume (fs : List (List Bool)) : (dataFields fs).length ≤ 2*fieldVolume fs := by
  induction fs with
  | nil => rfl
  | cons x xs ih =>
    simp only [fieldVolume,List.map_cons,List.sum_cons,dataFields,List.flatMap_cons,List.length_append,
      List.length_singleton,NPStackFieldData.tagBits_length] at *
    omega

lemma measure_le_input (raw : Raw) : rawMeasure raw ≤ (dataFields (fields raw)).length := fieldVolume_le_tagged _

lemma memberCost_uniform (q : List Bool) (labels : List (List Bool)) {N : ℕ}
    (hq : q.length ≤ N) (hn : labels.length ≤ N) (hw : ∀ x∈labels,x.length ≤ N) :
    NPStackCatalogueMember.memberCost q labels ≤ 100*(N+1)^2 := by
  have hsum : (labels.map List.length).sum ≤ labels.length*N := by
    induction labels with
    | nil => simp
    | cons x xs ih =>
      have hx := hw x (by simp)
      have ht := ih (by simp at hn;omega) (fun y hy => hw y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  have hb := NPStackCatalogueMember.memberCost_bound q labels
  have hprod : labels.length*N ≤ N*N := Nat.mul_le_mul_right N hn
  have hprod' : labels.length*(7*q.length+36) ≤ N*(7*N+36) := Nat.mul_le_mul hn (by omega)
  nlinarith

lemma literalCost_uniform (l : BitLiteral) (labels : List (List Bool)) {N : ℕ}
    (hl : l.labelBits.length ≤ N) (hn : labels.length ≤ N) (hw : ∀ x∈labels,x.length ≤ N) :
    literalCost l labels ≤ 200*(N+1)^2 := by
  have hh := memberCost_uniform l.labelBits labels hl hn hw
  unfold literalCost
  nlinarith

lemma clauseCost_uniform (clause : BitClause) (labels : List (List Bool)) {N : ℕ}
    (hl : ∀ l∈clause,l.labelBits.length ≤ N) (hn : labels.length ≤ N) (hw : ∀ x∈labels,x.length ≤ N) :
    clauseCost clause labels ≤ clause.length*(200*(N+1)^2)+5 := by
  induction clause with
  | nil => simp [clauseCost]
  | cons l ls ih =>
    have hhead := literalCost_uniform l labels (hl l (by simp)) hn hw
    have htail := ih (fun x hx => hl x (by simp [hx]))
    simp only [clauseCost,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

lemma formulaCost_uniform (formula : BitFormula) (labels : List (List Bool)) {N : ℕ}
    (hl : ∀ c∈formula,∀ l∈c,l.labelBits.length ≤ N) (hn : labels.length ≤ N)
    (hw : ∀ x∈labels,x.length ≤ N) :
    formulaCost formula labels ≤ bitLiteralCount formula*(200*(N+1)^2)+16*formula.length+12 := by
  induction formula with
  | nil => simp [formulaCost,bitLiteralCount]
  | cons c cs ih =>
    have hhead := clauseCost_uniform c labels (hl c (by simp)) hn hw
    have htail := ih (fun d hd l hl' => hl d (by simp [hd]) l hl')
    simp only [formulaCost,List.map_cons,List.sum_cons,List.length_cons,bitLiteralCount] at *
    nlinarith

def prepBudget (N : ℕ) : ℕ := 1000*(N+1)^3

/-- A clock depending only on actual tagged input length. All arithmetic,
comparison, copying, nested membership scans, parsing, and fresh generation
are already charged by preparationCost. No label value controls this clock. -/
theorem preparationCost_bound (raw : Raw) : preparationCost raw ≤ prepBudget (dataFields (fields raw)).length := by
  let N := (dataFields (fields raw)).length
  have hmeasure : rawMeasure raw ≤ N := measure_le_input raw
  have hcount := rawMeasure_counts raw
  have hwidth := rawMeasure_widths raw
  have hcat : raw.catalog.length ≤ N := hcount.1.trans hmeasure
  have hfcount : raw.formula.length ≤ N := hcount.2.1.trans hmeasure
  have hlcount : bitLiteralCount raw.formula ≤ N := hcount.2.2.trans hmeasure
  have hcatwidth : ∀ x∈raw.catalog,x.length ≤ N := fun x hx => (hwidth.1 x hx).trans hmeasure
  have hformwidth : ∀ c∈raw.formula,∀ l∈c,l.labelBits.length ≤ N :=
    fun c hc l hl => (hwidth.2 c hc l hl).trans hmeasure
  have hheader := StackCatalogue.catalogueCost_bound raw.catalog [] [] (N:=N) (B:=N)
    hcatwidth (by simp) (by simp) (by simpa using hcat)
  have hformula := formulaCost_uniform raw.formula raw.catalog.reverse hformwidth
    (by simpa using hcat) (by simpa using hcatwidth)
  have hformVolume : fieldVolume (formulaFields raw.formula) ≤ rawMeasure raw := by
    simp only [rawMeasure,fields,fieldVolume_append]
    omega
  have hcopy : (dataFields (formulaFields raw.formula)).length ≤ 2*N :=
    (tagged_le_twice_fieldVolume _).trans (by omega)
  have hhp : raw.catalog.length*(100*(N+1)*(N+1)) ≤ N*(100*(N+1)*(N+1)) :=
    Nat.mul_le_mul_right _ hcat
  have hfp : bitLiteralCount raw.formula*(200*(N+1)^2) ≤ N*(200*(N+1)^2) :=
    Nat.mul_le_mul_right _ hlcount
  unfold preparationCost prepBudget
  change _ ≤ 1000*(N+1)^3
  nlinarith

lemma freshBits_length_bound (raw : Raw) : (freshBits raw.catalog).length ≤ (dataFields (fields raw)).length+1 := by
  have hw := (rawMeasure_widths raw).1
  have hm := measure_le_input raw
  exact StackCatalogue.fresh_length raw.catalog (fun x hx => (hw x hx).trans hm)

lemma tagged_reverse_length (labels : List (List Bool)) : (dataFields labels.reverse).length=(dataFields labels).length := by
  simp [NPStackFieldsEncode.dataFields_length,NPStackFieldsEncode.volume,List.map_reverse]

lemma catalog_tagged_length (labels : List (List Bool)) :
    (dataFields (catalogFields labels)).length=(dataFields labels).length+3*labels.length+3 := by
  induction labels with
  | nil => rfl
  | cons x xs ih =>
    simp only [catalogFields,dataFields,List.flatMap_cons,List.length_append,List.length_singleton,
      List.length_cons,NPStackFieldData.tagBits_length] at *
    norm_num at *
    omega

/-- Retained formula and raw catalogue fit inside the original tagged input;
freshness adds at most one bit beyond the original maximum label width. -/
theorem output_size_bound (raw : Raw) :
    (dataFields (formulaFields raw.formula)).length+(dataFields raw.catalog.reverse).length+
      (freshBits raw.catalog).length ≤ 2*(dataFields (fields raw)).length+1 := by
  have hf := freshBits_length_bound raw
  have hc := catalog_tagged_length raw.catalog
  rw [tagged_reverse_length]
  simp only [fields,dataFields,List.flatMap_append,List.length_append] at hf ⊢
  change (dataFields (formulaFields raw.formula)).length+(dataFields raw.catalog).length+
    (freshBits raw.catalog).length ≤ 2*((dataFields (catalogFields raw.catalog)).length+
      (dataFields (formulaFields raw.formula)).length)+1
  change (freshBits raw.catalog).length ≤ (dataFields (catalogFields raw.catalog)).length+
    (dataFields (formulaFields raw.formula)).length+1 at hf
  omega

end BalancedAssortments.NPCNF.StackValidate
