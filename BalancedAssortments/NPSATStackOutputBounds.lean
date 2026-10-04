import BalancedAssortments.NPSATStackBounds
import BalancedAssortments.NPSATStackSlackLoop

namespace BalancedAssortments.NPSATStackOutputBounds
open NPCNF.Encoding NPStackFields

lemma variableFields_length (catalog : List (List Bool)) (F : BitFormula) (labels : List (List Bool)) :
    (NPSATStackVariables.variableFields catalog F labels).length=2*labels.length := by
  induction labels <;> simp [NPSATStackVariables.variableFields, *,Nat.mul_add,Nat.add_assoc]

lemma variableFields_width (catalog : List (List Bool)) (F : BitFormula) (labels : List (List Bool)) :
    ∀bits∈NPSATStackVariables.variableFields catalog F labels,bits.length≤12*(catalog.length+F.length) := by
  induction labels with
  | nil => simp [NPSATStackVariables.variableFields]
  | cons label labels ih =>
    intro bits h
    simp only [NPSATStackVariables.variableFields,List.mem_cons] at h
    rcases h with rfl|rfl|h
    · exact NPSATStackItem.itemBits_length _ _ _ _
    · exact NPSATStackItem.itemBits_length _ _ _ _
    · exact ih bits h

lemma serialize_length (bits : List Bool) : (FPTASCostProgram.serializeBits bits).length=2*bits.length+1 := by
  simp [FPTASCostProgram.serializeBits];omega

lemma variable_output_length (catalog : List (List Bool)) (F : BitFormula) (labels : List (List Bool)) :
    (NPSATStackVariables.output catalog F labels []).length≤2*labels.length*(24*(catalog.length+F.length)+1) := by
  rw [NPSATStackVariables.output_fields,List.append_nil,List.length_flatMap]
  have hh := NPSATStackBounds.map_sum_le (NPSATStackVariables.variableFields catalog F labels).reverse
    (fun bits=>(FPTASCostProgram.serializeBits bits).length) (24*(catalog.length+F.length)+1) (by
      intro bits h
      have hw := variableFields_width catalog F labels bits (by simpa using h)
      dsimp only
      rw [serialize_length]
      omega)
  simpa [variableFields_length] using hh

lemma variable_output_polynomial (catalog : List (List Bool)) (F : BitFormula) (L : ℕ)
    (hn : catalog.length≤L) (hm : F.length≤L) :
    (NPSATStackVariables.output catalog F catalog []).length≤100*(L+1)^2 := by
  have h := variable_output_length catalog F catalog
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn)
    (show 24*(catalog.length+F.length)+1≤48*(L+1) by omega)
  nlinarith

end BalancedAssortments.NPSATStackOutputBounds
