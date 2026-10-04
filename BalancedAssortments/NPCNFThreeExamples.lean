import BalancedAssortments.NPCNFThreeReduction

/-! Kernel-reduced executable regression checks for degenerate and malformed
CNF inputs. No native_decide/trusted evaluator extension is used. -/
namespace BalancedAssortments.NPCNF.Encoding

def emptyRaw : Raw := ⟨[],[]⟩
def paddedDuplicateRaw : Raw := ⟨[[true],[true,false]],[]⟩
def missingCatalogRaw : Raw := ⟨[],[[⟨[true],true⟩]]⟩

theorem malformed_empty_bits : (reduceBits []).1 = encode unsatRaw := by decide +kernel

theorem empty_formula_execution : (reduceBits (encode emptyRaw)).1 = encode emptyRaw := by decide +kernel

theorem padded_duplicates_rejected :
    (reduceBits (encode paddedDuplicateRaw)).1 = encode unsatRaw := by
  have h : (validate paddedDuplicateRaw).1 = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hv := (validate_correct paddedDuplicateRaw).mp ht
    norm_num [paddedDuplicateRaw,Raw.decode,Catalogued.Valid,ComplexityTimeBinary.value] at hv
  simp [reduceBits,parse_encode,h,emit_eq]

theorem missing_variable_rejected :
    (reduceBits (encode missingCatalogRaw)).1 = encode unsatRaw := by
  have h : (validate missingCatalogRaw).1 = false := by decide +kernel
  simp [reduceBits,parse_encode,h,emit_eq]

theorem empty_formula_language : ThreeCNFLanguage (reduceBits (encode emptyRaw)).1 := by
  rw [reduceBits_correct,CNFLanguage_encode]
  exact ⟨by simp [emptyRaw,Raw.decode,Catalogued.Valid],empty_formula_sat⟩

theorem empty_clause_language : ¬ ThreeCNFLanguage (reduceBits (encode unsatRaw)).1 := by
  rw [reduceBits_correct,CNFLanguage_encode]
  exact fun h => unsatRaw_unsat h.2

/-- A four-literal clause creates three OR gates and a final unit clause. -/
theorem repeated_literal_chain :
    (toThree 2 [[positive 1,positive 1,positive 1,positive 1]]).1.length = 10 := by decide +kernel

theorem repeated_literal_certificate :
    formulaEval (fun _ => true) (toThree 2 [[positive 1,positive 1,positive 1,positive 1]]).1 = true := by
  decide +kernel

end BalancedAssortments.NPCNF.Encoding
