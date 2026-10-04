import BalancedAssortments.NPSATStackPolynomialReduction

/-! The structured finite-table enumeration uses `Fintype.equivFin`, so it is
not Lean VM executable. These are kernel-checked actual transition witnesses,
plus hard executable semantic-output assertions; they are not VM traces. -/
namespace BalancedAssortments.NPSATStackReduction
open NPStack NPCNF NPCNF.Encoding

private def emptyFormula : Raw := ⟨[],[]⟩
private def emptyClause : Raw := ⟨[],[[]]⟩
private def paddedUnit : Raw := ⟨[[false,false]],[[⟨[],true⟩]]⟩

#guard reduction (encode emptyFormula)=NPSATSubsetSum.fixedYes
#guard reduction []=NPSATSubsetSum.fixedNo
#guard reduction (encode (⟨[[],[false]],[]⟩ : Raw))=NPSATSubsetSum.fixedNo
#guard reduction (encode (⟨[],[[⟨[],true⟩]]⟩ : Raw))=NPSATSubsetSum.fixedNo
#guard reduction (encode (⟨[[]],[[⟨[],true⟩,⟨[],true⟩,⟨[],true⟩,⟨[],true⟩]]⟩ : Raw))=NPSATSubsetSum.fixedNo

private lemma empty_valid : emptyFormula.decode.Valid := by
  simp [emptyFormula,Raw.decode,Catalogued.Valid]
private lemma emptyClause_valid : emptyClause.decode.Valid := by
  simp [emptyClause,Raw.decode,Catalogued.Valid]
private lemma paddedUnit_valid : paddedUnit.decode.Valid := by
  simp [paddedUnit,Raw.decode,Catalogued.Valid,BitLiteral.decode,ComplexityTimeBinary.value]

example : ∃t ≤ successBudget emptyFormula,Run program t (initial program (encode emptyFormula))
    ⟨.accept,finalStore emptyFormula⟩ := valid_run emptyFormula empty_valid (by simp [ThreeCNF,emptyFormula,Raw.decode])
example : ∃t ≤ successBudget emptyClause,Run program t (initial program (encode emptyClause))
    ⟨.accept,finalStore emptyClause⟩ := valid_run emptyClause emptyClause_valid (by simp [ThreeCNF,emptyClause,Raw.decode])
example : ∃t ≤ successBudget paddedUnit,Run program t (initial program (encode paddedUnit))
    ⟨.accept,finalStore paddedUnit⟩ := valid_run paddedUnit paddedUnit_valid (by simp [ThreeCNF,paddedUnit,Raw.decode])
example : ∃t s,Run program t (initial program []) ⟨.reject,s⟩ := by
  apply bad_reject
  rintro ⟨raw,hp,_,_⟩
  have hn : (parse []).1=none := by decide +kernel
  rw [hn] at hp
  cases hp

end BalancedAssortments.NPSATStackReduction
