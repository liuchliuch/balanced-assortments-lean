import BalancedAssortments.NPCNFEmission
import BalancedAssortments.NPCNFThreeProgram
import BalancedAssortments.NPCNFParsingBounds

namespace BalancedAssortments.NPCNF.Encoding

lemma catalogFields_length (catalog : List (List Bool)) : (catalogFields catalog).length = 2*catalog.length+1 := by
  induction catalog <;> simp_all [catalogFields] <;> omega

lemma rawMeasure_counts (input : Raw) :
    input.catalog.length ≤ rawMeasure input ∧ input.formula.length ≤ rawMeasure input ∧
      bitLiteralCount input.formula ≤ rawMeasure input := by
  have hh := field_count_le_volume (fields input)
  simp only [fields,List.length_append,catalogFields_length,formulaFields_length] at hh
  dsimp only [rawMeasure,bitLiteralCount,fields]
  omega

lemma catalog_payload_mem {catalog : List (List Bool)} {x : List Bool} (hx : x ∈ catalog) : x ∈ catalogFields catalog := by
  induction catalog with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [catalogFields]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hx))

lemma clause_payload_mem {c : BitClause} {l : BitLiteral} (hl : l ∈ c) : l.labelBits ∈ clauseFields c := by
  induction c with
  | nil => simp at hl
  | cons a as ih =>
    rcases List.mem_cons.mp hl with rfl | hl
    · simp [clauseFields]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hl))

lemma formula_payload_mem {F : BitFormula} {c : BitClause} {l : BitLiteral} (hc : c ∈ F) (hl : l ∈ c) :
    l.labelBits ∈ formulaFields F := by
  induction F with
  | nil => simp at hc
  | cons d ds ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (clause_payload_mem hl)))
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (ih hc)))

lemma field_length_bound {fields : List (List Bool)} {x : List Bool} (hx : x ∈ fields) :
    x.length ≤ fieldVolume fields := by
  induction fields with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [fieldVolume,List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have hh := ih hx;change x.length ≤ y.length+1+fieldVolume ys;omega

lemma rawMeasure_widths (input : Raw) :
    (∀ x ∈ input.catalog,x.length ≤ rawMeasure input) ∧
    (∀ c ∈ input.formula,∀ l ∈ c,l.labelBits.length ≤ rawMeasure input) := by
  constructor
  · intro x hx
    exact field_length_bound (List.mem_append.mpr (Or.inl (catalog_payload_mem hx)))
  · intro c hc l hl
    exact field_length_bound (List.mem_append.mpr (Or.inr (formula_payload_mem hc hl)))

lemma catalogVolume_bound {catalog : List (List Bool)} {b : ℕ} (h : ∀ x ∈ catalog,x.length ≤ b) :
    fieldVolume (catalogFields catalog) ≤ (b+3)*catalog.length+2 := by
  induction catalog with
  | nil => simp [catalogFields,fieldVolume]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [catalogFields,fieldVolume,List.map_cons,List.sum_cons,List.length_cons,List.length_nil] at *
    nlinarith

lemma clauseVolume_bound {c : BitClause} {b : ℕ} (h : ∀ l ∈ c,l.labelBits.length ≤ b) :
    fieldVolume (clauseFields c) ≤ (b+3)*c.length+1 := by
  induction c with
  | nil => simp [clauseFields,fieldVolume]
  | cons l ls ih =>
    have hx := h l (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [clauseFields,fieldVolume,List.map_cons,List.sum_cons,List.length_cons,List.length_nil] at *
    nlinarith

lemma formulaVolume_bound {F : BitFormula} {b : ℕ} (h : ∀ c ∈ F,∀ l ∈ c,l.labelBits.length ≤ b) :
    fieldVolume (formulaFields F) ≤ (b+3)*bitLiteralCount F+3*F.length+2 := by
  induction F with
  | nil => simp [formulaFields,fieldVolume,bitLiteralCount]
  | cons c cs ih =>
    have hc := clauseVolume_bound (h c (by simp))
    have ht := ih (fun d hd l hl => h d (by simp [hd]) l hl)
    simp only [formulaFields,fieldVolume_append,List.length_cons]
    change 2+fieldVolume (clauseFields c++formulaFields cs) ≤ _
    rw [fieldVolume_append]
    simp only [bitLiteralCount,List.map_cons,List.sum_cons] at *
    nlinarith

lemma rawMeasure_bound {input : Raw} {b : ℕ}
    (hc : ∀ x ∈ input.catalog,x.length ≤ b)
    (hf : ∀ c ∈ input.formula,∀ l ∈ c,l.labelBits.length ≤ b) :
    rawMeasure input ≤ (b+3)*(input.catalog.length+bitLiteralCount input.formula)+3*input.formula.length+4 := by
  have h₁ := catalogVolume_bound hc
  have h₂ := formulaVolume_bound hf
  simp only [rawMeasure,fields,fieldVolume_append]
  nlinarith

theorem parsed_rawMeasure_bound {bits : List Bool} {input : Raw} (h : (parse bits).1 = some input) :
    rawMeasure input ≤ bits.length := parse_measure bits input h

end BalancedAssortments.NPCNF.Encoding
