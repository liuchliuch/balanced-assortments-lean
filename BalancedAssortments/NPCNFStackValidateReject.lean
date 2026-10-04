import BalancedAssortments.NPCNFStackValidateRun

namespace BalancedAssortments.NPCNF.StackValidate
open NPStack NPStack.Macros
open NPStackFields (tagBits dataFields)
open ComplexityTimeBinary
open Encoding

lemma program_noChoice : NoChoice program := by
  have hout (q : Label Main) (a b : State) :
      (Macros.code macroCode q).rename id State.outer≠.choice a b :=
    rename_not_choice _ id State.outer (compile_noChoice macroCode .saveFormula input original q) a b
  have hmem (q : NPStackCatalogueMember.State) (a b : State) :
      (NPStackCatalogueMember.program.code q).rename (Sum.inl : NPStackCatalogueMember.Register → Register) State.member≠.choice a b :=
    rename_not_choice _ (Sum.inl : NPStackCatalogueMember.Register → Register) State.member (NPStackCatalogueMember.program_noChoice q) a b
  have hhead (q : StackCatalogue.State) (a b : State) :
      (StackCatalogue.program.code q).rename headerMap State.header≠.choice a b :=
    rename_not_choice _ headerMap State.header (StackCatalogue.program_noChoice q) a b
  intro q a b
  cases q with
  | outer q =>
    cases q with
    | main q => cases q <;> simp only [program,code] <;> first | exact hout _ a b | simp
    | «local» q st => exact hout _ a b
  | member q =>
    cases q with
    | outer q => cases q with
      | main q => cases q <;> simp only [program,code] <;> first | exact hmem _ a b | simp
      | «local» q st => exact hmem _ a b
    | equal f q => exact hmem _ a b
  | header q =>
    cases q with
    | outer q => cases q with
      | main q => cases q <;> simp only [program,code] <;> first | exact hhead _ a b | simp
      | «local» q st => exact hhead _ a b
    | member q => exact hhead _ a b

lemma program_deterministic : Deterministic program := noChoice_deterministic program_noChoice

lemma reject_literal (l : BitLiteral) (labels : List (List Bool)) (rest o f : List Bool)
    (hm : value l.labelBits∉labels.map value) :
    ∃ t d,Run program t
      (cfg .readSign (store (tagBits [l.positive]++false::(tagBits l.labelBits++false::rest)) o f (dataFields labels) [] [] [])) d ∧
      program.code d.pc=.halt false := by
  have hmem := member_call l.labelBits rest o f labels
  simp only [hm,decide_false] at hmem
  have hh := (sign_call l.positive (tagBits l.labelBits++false::rest) o f (dataFields labels)).trans
    ((literal_read_call l.labelBits rest o f (dataFields labels)).trans (hmem.trans
      (.one (member_check false l.labelBits rest o f (dataFields labels)))))
  exact ⟨_,_,hh,rfl⟩

lemma reject_clause_members (clause : BitClause) (labels : List (List Bool)) (rest o f : List Bool)
    (hm : ¬∀ l∈clause,value l.labelBits∈labels.map value) :
    ∃ t d,Run program t
      (cfg .readSign (store (dataFields (clauseFields clause)++rest) o f (dataFields labels) [] [] [])) d ∧
      program.code d.pc=.halt false := by
  induction clause with
  | nil => simp at hm
  | cons l ls ih =>
    by_cases hl : value l.labelBits∈labels.map value
    · obtain ⟨t,d,hr,hd⟩ := ih (by
        intro ht;apply hm;intro x hx
        rcases List.mem_cons.mp hx with rfl|hx
        · exact hl
        · exact ht x hx)
      have hh := (literal_run l labels (dataFields (clauseFields ls)++rest) o f hl).trans hr
      exact ⟨_,d,by simpa [clauseFields,dataFields,List.append_assoc] using hh,hd⟩
    · obtain ⟨t,d,hr,hd⟩ := reject_literal l labels (dataFields (clauseFields ls)++rest) o f hl
      exact ⟨t,d,by simpa [clauseFields,dataFields,List.append_assoc] using hr,hd⟩

lemma reject_formula_members (formula : BitFormula) (labels : List (List Bool)) (rest o f : List Bool)
    (hm : ¬Members formula labels) :
    ∃ t d,Run program t
      (cfg .readHeader (store (dataFields (formulaFields formula)++rest) o f (dataFields labels) [] [] [])) d ∧
      program.code d.pc=.halt false := by
  induction formula with
  | nil => simp [Members] at hm
  | cons c cs ih =>
    have hhead := header_call true (dataFields (clauseFields c)++(dataFields (formulaFields cs)++rest)) o f (dataFields labels)
    by_cases hc : ∀ l∈c,value l.labelBits∈labels.map value
    · obtain ⟨t,d,hr,hd⟩ := ih (by
        intro ht;apply hm;intro d hd
        rcases List.mem_cons.mp hd with rfl|hd
        · exact hc
        · exact ht d hd)
      have hh := hhead.trans ((clause_run c labels (dataFields (formulaFields cs)++rest) o f hc).trans hr)
      exact ⟨_,d,by simpa [formulaFields,dataFields,List.flatMap_append,List.append_assoc] using hh,hd⟩
    · obtain ⟨t,d,hr,hd⟩ := reject_clause_members c labels (dataFields (formulaFields cs)++rest) o f hc
      have hh := hhead.trans hr
      exact ⟨_,d,by simpa [formulaFields,dataFields,List.flatMap_append,List.append_assoc] using hh,hd⟩

lemma formula_scan (formula : BitFormula) (labels : List (List Bool)) (rest o f : List Bool)
    (hm : Members formula labels) :
    ∃ t,Run program t
      (cfg .readHeader (store (dataFields (formulaFields formula)++rest) o f (dataFields labels) [] [] []))
      (cfg .checkEnd (store rest o f (dataFields labels) [] [] [])) := by
  induction formula with
  | nil => exact ⟨11,by simpa [formulaFields,dataFields,List.append_assoc] using header_call false rest o f (dataFields labels)⟩
  | cons c cs ih =>
    obtain ⟨t,hr⟩ := ih (fun d hd => hm d (by simp [hd]))
    have hh := (header_call true (dataFields (clauseFields c)++(dataFields (formulaFields cs)++rest)) o f (dataFields labels)).trans
      ((clause_run c labels (dataFields (formulaFields cs)++rest) o f (hm c (by simp))).trans hr)
    exact ⟨_,by simpa [formulaFields,dataFields,List.flatMap_append,List.append_assoc] using hh⟩

lemma reject_extra_formula (formula : BitFormula) (labels : List (List Bool)) (b : Bool) (rest o f : List Bool) :
    ∃ t d,Run program t
      (cfg .readHeader (store (dataFields (formulaFields formula)++b::rest) o f (dataFields labels) [] [] [])) d ∧
      program.code d.pc=.halt false := by
  by_cases hm : Members formula labels
  · obtain ⟨t,hr⟩ := formula_scan formula labels (b::rest) o f hm
    have hs : Step program (cfg .checkEnd (store (b::rest) o f (dataFields labels) [] [] []))
        (cfg .reject (store rest o f (dataFields labels) [] [] [])) := by
      cases b <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,input] <;>
        funext k <;> cases k with
        | inl r => cases r <;> simp [store]
        | inr r => cases r <;> simp [store]
    exact ⟨_,_,hr.trans (.one hs),rfl⟩
  · exact reject_formula_members formula labels (b::rest) o f hm

end BalancedAssortments.NPCNF.StackValidate
