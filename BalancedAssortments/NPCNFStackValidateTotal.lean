import BalancedAssortments.NPCNFStackValidateCorrect

/-! Total termination of the actual validation code. No uniform negative-path
clock is asserted here; the enclosing real timeout supplies that requirement. -/
namespace BalancedAssortments.NPCNF.StackValidate
open NPStack NPStack.Macros NPStackFields Encoding ComplexityTimeBinary

lemma formula_total_halts (fs labels : List (List Bool)) (o fresh : List Bool) :
    ∃ t d b,Run program t (cfg .readHeader (store (dataFields fs) o fresh (dataFields labels) [] [] [])) d ∧
      program.code d.pc=.halt b := by
  cases hp : (parseFormula fs fs).1 with
  | none =>
    obtain ⟨t,d,hr,hd⟩ := reject_parseFormula fs fs labels o fresh le_rfl hp
    exact ⟨t,d,false,hr,hd⟩
  | some pair =>
    rcases pair with ⟨formula,rest⟩
    have hfields := Encoding.parseFormula_sound fs fs formula rest hp
    have hdata : dataFields fs=dataFields (formulaFields formula)++dataFields rest := by
      rw [← hfields];simp [dataFields,List.flatMap_append]
    rw [hdata]
    cases rest with
    | nil =>
      simp only [dataFields,List.flatMap_nil,List.append_nil]
      by_cases hm : Members formula labels
      · exact ⟨formulaCost formula labels,cfg .accept (store [] o fresh (dataFields labels) [] [] []),true,
          formula_run formula labels o fresh hm,rfl⟩
      · obtain ⟨t,d,hr,hd⟩ := reject_formula_members formula labels [] o fresh hm
        simp only [List.append_nil] at hr
        exact ⟨t,d,false,hr,hd⟩
    | cons x xs =>
      have hn : dataFields (x::xs)≠[] := by simp [dataFields]
      obtain ⟨b,bs,hbs⟩ := List.exists_cons_of_ne_nil hn
      rw [hbs]
      obtain ⟨t,d,hr,hd⟩ := reject_extra_formula formula labels b bs o fresh
      exact ⟨t,d,false,hr,hd⟩

/-- Every arbitrary parsed field stream has a real finite accepting or rejecting
preparation run. This theorem does not hide a machine in a semantic predicate. -/
theorem prepare_total_halts (fs : List (List Bool)) :
    ∃ t d b,Run program t ⟨program.start,store (dataFields fs) [] [] [] [] [] []⟩ d ∧
      program.code d.pc=.halt b := by
  cases hp : (parseCatalog fs).1 with
  | none =>
    obtain ⟨t,d,hr,hd⟩ := StackCatalogue.reject_parseCatalog fs [] [] hp
    obtain ⟨d',hr',hd'⟩ := lift_header_reject (dataFields fs) hr hd
    exact ⟨t,d',false,hr',hd'⟩
  | some pair =>
    rcases pair with ⟨labels,rest⟩
    have hfields := Encoding.parseCatalog_sound fs labels rest hp
    have hdata : dataFields fs=dataFields (catalogFields labels)++dataFields rest := by
      rw [← hfields];simp [dataFields,List.flatMap_append]
    by_cases hn : (labels.map value).Nodup
    · have hhead := header_run labels (dataFields rest) hn
      rw [← hdata] at hhead
      have hpre := hhead.trans (save_formula_call (dataFields rest) (freshBits labels) (dataFields labels.reverse))
      obtain ⟨t,d,b,hr,hd⟩ := formula_total_halts rest labels.reverse (dataFields rest) (freshBits labels)
      exact ⟨_,d,b,hpre.trans hr,hd⟩
    · obtain ⟨t,_,d,hr,hd⟩ := StackCatalogue.reject_duplicates labels [] (dataFields rest) [] (by simp) (by simpa using hn)
      simp only [dataFields,List.flatMap_nil] at hr
      change Run StackCatalogue.program t
        (StackCatalogue.cfg .readTag (StackCatalogue.store (dataFields (catalogFields labels)++dataFields rest) [] [] [] [] [] [] [] [])) d at hr
      rw [← hdata] at hr
      obtain ⟨d',hr',hd'⟩ := lift_header_reject (dataFields fs) hr hd
      exact ⟨t,d',false,hr',hd'⟩

end BalancedAssortments.NPCNF.StackValidate
