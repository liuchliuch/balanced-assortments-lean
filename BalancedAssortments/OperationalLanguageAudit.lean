import BalancedAssortments.NPStackSourceFixedMembership
import BalancedAssortments.NPSATStackReductionSemantics

namespace BalancedAssortments.OperationalLanguageAudit
open NPCNF NPCNF.Encoding NPSATSubsetSum
open ComplexityTimeSourceParsing

/-- Literal malformed framing is outside both source decision languages. -/
example : ¬FixedSourceLanguage [] := by
  rintro ⟨⟨s,hparse,_⟩,_⟩
  cases hparse
example : NPSATStackReduction.reduction []=fixedNo := by rfl

def emptyFormula : Raw := ⟨[],[]⟩
def emptyClause : Raw := ⟨[],[[]]⟩
def paddedDuplicate : Raw := ⟨[[],[false]],[]⟩

example : NPSATStackReduction.reduction (encode emptyFormula)=fixedYes := by rfl
example : NPSATStackReduction.reduction (encode paddedDuplicate)=fixedNo := by
  apply NPSATStackReduction.reduction_of_not_good
  rintro ⟨raw,hp,hv,_⟩
  rw [parse_encode] at hp
  have he := Option.some.inj hp
  subst raw
  have hn:=hv.1
  simp [paddedDuplicate,Raw.decode,ComplexityTimeBinary.value] at hn

lemma emptyClause_not_sat : ¬emptyClause.decode.Sat := by
  rintro ⟨σ,hσ⟩
  simp [emptyClause,Raw.decode,formulaEval,clauseEval] at hσ

example : ¬PositiveSubsetSumLanguage (NPSATStackReduction.reduction (encode emptyClause)) := by
  rw [NPSATStackReduction.reduction_correct]
  rintro ⟨raw,hp,_,_,hs⟩
  rw [parse_encode] at hp
  have he := Option.some.inj hp
  subst raw
  exact emptyClause_not_sat hs

end BalancedAssortments.OperationalLanguageAudit
