import BalancedAssortments.NPCNFStackFormulaSound
import BalancedAssortments.NPCNFThreeAppendCatalog

namespace BalancedAssortments.NPCNF.StackFormula
open NPStackFields Encoding StackChain ComplexityTimeBinary

def chainLabels (next : List Bool) : BitClause → List (List Bool)
  | [] => []
  | _::bs => next::chainLabels (nextBits next) bs

def clauseLabels (next : List Bool) : BitClause → List (List Bool)
  | [] => []
  | _::bs => chainLabels next bs

def formulaLabels (next : List Bool) : BitFormula → List (List Bool)
  | [] => []
  | c::cs => clauseLabels next c++formulaLabels (bitClause next c).1.2 cs

lemma chainAllocated_fields (next : List Bool) (rest : BitClause) :
    chainAllocated next rest=dataFields (chainLabels next rest).reverse := by
  induction rest generalizing next with
  | nil => rfl
  | cons b bs ih => simp [chainAllocated,chainLabels,ih,List.reverse_cons,dataFields,List.flatMap_append,List.append_assoc]

lemma clauseAllocated_fields (next : List Bool) (c : BitClause) :
    clauseAllocated next c=dataFields (clauseLabels next c).reverse := by
  cases c <;> simp [clauseAllocated,clauseLabels,chainAllocated_fields,dataFields]

lemma formulaAllocated_fields (next : List Bool) (F : BitFormula) :
    formulaAllocated next F=dataFields (formulaLabels next F).reverse := by
  induction F generalizing next with
  | nil => rfl
  | cons c cs ih => simp [formulaAllocated,formulaLabels,ih,clauseAllocated_fields,List.reverse_append,dataFields,List.flatMap_append]

lemma nextBits_value (next : List Bool) : value (nextBits next)=value next+1 := by
  simp [nextBits,addCarry_value,value]

lemma allocatedLabels_succ (next n : ℕ) : allocatedLabels next (n+1)=next::allocatedLabels (next+1) n := by
  simp only [allocatedLabels,← List.range'_eq_map_range,List.range'_succ,Nat.mul_one]

lemma allocatedLabels_append (next a b : ℕ) :
    allocatedLabels next a++allocatedLabels (next+a) b=allocatedLabels next (a+b) := by
  simp only [allocatedLabels,← List.range'_eq_map_range,List.range'_append_1]

lemma chainLabels_values (next : List Bool) (rest : BitClause) :
    (chainLabels next rest).map value=allocatedLabels (value next) rest.length := by
  induction rest generalizing next with
  | nil => rfl
  | cons b bs ih => simp [chainLabels,ih,nextBits_value,allocatedLabels_succ]

lemma clauseLabels_values (next : List Bool) (c : BitClause) :
    (clauseLabels next c).map value=allocatedLabels (value next) c.length.pred := by
  cases c <;> simp [clauseLabels,chainLabels_values,allocatedLabels]

lemma formulaLabels_values (next : List Bool) (F : BitFormula) :
    (formulaLabels next F).map value=allocatedLabels (value next) (freshCount (F.map (List.map BitLiteral.decode))) := by
  induction F generalizing next with
  | nil => rfl
  | cons c cs ih =>
    have hcounter := congrArg Prod.snd (bitClause_decode next c)
    simp only [clauseToThree_next,List.length_map] at hcounter
    simp only [formulaLabels,List.map_append,clauseLabels_values,ih,hcounter,List.map_cons,
      freshCount,List.map_cons,List.sum_cons,List.length_map]
    exact allocatedLabels_append _ _ _

end BalancedAssortments.NPCNF.StackFormula
