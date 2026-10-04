import BalancedAssortments.NPCNFEncoding

namespace BalancedAssortments.NPCNF.Encoding

def fieldVolume (xs : List (List Bool)) : ℕ := (xs.map (fun x => x.length+1)).sum

lemma fieldVolume_append (xs ys : List (List Bool)) : fieldVolume (xs++ys) = fieldVolume xs+fieldVolume ys := by
  simp [fieldVolume,List.map_append,List.sum_append]

lemma field_count_le_volume (xs : List (List Bool)) : xs.length ≤ fieldVolume xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [fieldVolume,List.map_cons,List.sum_cons,List.length_cons] at *;omega

def rawMeasure (input : Raw) : ℕ := fieldVolume (fields input)

def catalogFieldsExec : List (List Bool) → List (List Bool) × ℕ
  | [] => ([[false]],4)
  | x::xs => let tail := catalogFieldsExec xs; ([true]::x::tail.1,tail.2+8)

def clauseFieldsExec : BitClause → List (List Bool) × ℕ
  | [] => ([[]],4)
  | l::ls => let tail := clauseFieldsExec ls; ([l.positive]::l.labelBits::tail.1,tail.2+8)

def formulaFieldsExec : BitFormula → List (List Bool) × ℕ
  | [] => ([[false]],4)
  | c::cs =>
      let head := clauseFieldsExec c
      let tail := formulaFieldsExec cs
      ([true]::(head.1++tail.1),head.2+tail.2+head.1.length+8)

def fieldsExec (input : Raw) : List (List Bool) × ℕ :=
  let vars := catalogFieldsExec input.catalog
  let formula := formulaFieldsExec input.formula
  (vars.1++formula.1,vars.2+formula.2+vars.1.length+4)

@[simp] lemma catalogFieldsExec_eq (xs : List (List Bool)) : (catalogFieldsExec xs).1 = catalogFields xs := by
  induction xs <;> simp_all [catalogFieldsExec,catalogFields]
@[simp] lemma clauseFieldsExec_eq (c : BitClause) : (clauseFieldsExec c).1 = clauseFields c := by
  induction c <;> simp_all [clauseFieldsExec,clauseFields]
@[simp] lemma formulaFieldsExec_eq (F : BitFormula) : (formulaFieldsExec F).1 = formulaFields F := by
  induction F <;> simp_all [formulaFieldsExec,formulaFields]
@[simp] lemma fieldsExec_eq (input : Raw) : (fieldsExec input).1 = fields input := by simp [fieldsExec,fields]

lemma catalogFieldsExec_cost (xs : List (List Bool)) : (catalogFieldsExec xs).2 = 4*(catalogFields xs).length := by
  induction xs <;> simp_all [catalogFieldsExec,catalogFields] <;> omega
lemma clauseFieldsExec_cost (c : BitClause) : (clauseFieldsExec c).2 = 4*(clauseFields c).length := by
  induction c <;> simp_all [clauseFieldsExec,clauseFields] <;> omega
lemma formulaFieldsExec_cost (F : BitFormula) : (formulaFieldsExec F).2 ≤ 8*(formulaFields F).length := by
  induction F with
  | nil => simp [formulaFieldsExec,formulaFields]
  | cons c cs ih =>
    simp only [formulaFieldsExec,clauseFieldsExec_eq,clauseFieldsExec_cost,formulaFields,List.length_cons,List.length_append]
    omega
lemma fieldsExec_cost (input : Raw) : (fieldsExec input).2 ≤ 8*(fields input).length+4 := by
  have hc := catalogFieldsExec_cost input.catalog
  have hf := formulaFieldsExec_cost input.formula
  simp only [fieldsExec,catalogFieldsExec_eq,fields,List.length_append]
  omega

/-- Build the unary length prefix by traversing the actual payload. -/
def header : List Bool → List Bool × ℕ
  | [] => ([],1)
  | _::bs => let tail := header bs; (true::tail.1,tail.2+4)

lemma header_eq (bs : List Bool) : (header bs).1 = List.replicate bs.length true := by
  induction bs <;> simp_all [header,List.replicate_succ]
lemma header_cost (bs : List Bool) : (header bs).2 = 4*bs.length+1 := by
  induction bs <;> simp_all [header] <;> omega

def frame (bs : List Bool) : List Bool × ℕ :=
  let pre := header bs
  (pre.1++false::bs,pre.2+pre.1.length+4)

lemma frame_eq (bs : List Bool) : (frame bs).1 = encodePayload bs := by simp [frame,header_eq,encodePayload]
lemma frame_cost (bs : List Bool) : (frame bs).2 = 5*bs.length+5 := by simp [frame,header_cost,header_eq];omega

def emitFields : List (List Bool) → List Bool × ℕ
  | [] => ([],1)
  | x::xs =>
      let head := frame x
      let tail := emitFields xs
      (head.1++tail.1,head.2+tail.2+head.1.length+4)

lemma emitFields_eq (xs : List (List Bool)) : (emitFields xs).1 = encodeFields xs := by
  induction xs <;> simp_all [emitFields,encodeFields,frame_eq]

lemma emitFields_cost (xs : List (List Bool)) : (emitFields xs).2 ≤ 12*fieldVolume xs+1 := by
  induction xs with
  | nil => simp [emitFields,fieldVolume]
  | cons x xs ih =>
    simp only [emitFields,frame_eq,frame_cost,encodePayload_length]
    simp only [fieldVolume,List.map_cons,List.sum_cons] at *
    omega

lemma encoded_length_le_volume (xs : List (List Bool)) : (encodeFields xs).length ≤ 2*fieldVolume xs := by
  rw [encodeFields_length]
  induction xs <;> simp_all [fieldVolume] <;> omega

def emit (input : Raw) : List Bool × ℕ :=
  let records := fieldsExec input
  let result := emitFields records.1
  (result.1,records.2+result.2+4)

@[simp] theorem emit_eq (input : Raw) : (emit input).1 = encode input := by simp [emit,emitFields_eq,encode]

theorem emit_cost (input : Raw) : (emit input).2 ≤ 32*(rawMeasure input+1) := by
  have hf := fieldsExec_cost input
  have he := emitFields_cost (fields input)
  have hl := field_count_le_volume (fields input)
  simp only [emit,fieldsExec_eq,rawMeasure]
  omega

theorem emit_length (input : Raw) : (emit input).1.length ≤ 2*rawMeasure input := by
  rw [emit_eq]
  exact encoded_length_le_volume _

end BalancedAssortments.NPCNF.Encoding
