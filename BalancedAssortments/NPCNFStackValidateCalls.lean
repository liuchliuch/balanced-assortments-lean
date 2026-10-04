import BalancedAssortments.NPCNFStackValidateProgram

namespace BalancedAssortments.NPCNF.StackValidate
open NPStack NPStack.Macros
open NPStackFields (tagBits dataFields)
open ComplexityTimeBinary

lemma save_formula_call (bits f cat : List Bool) :
    Run program (5*bits.length+4) (cfg .saveFormula (store bits [] f cat [] [] []))
      (cfg .readHeader (store bits bits f cat [] [] [])) := by
  have h := outer_run (copy_call_store macroCode .saveFormula input original (q:=.saveFormula)
    rfl (by decide) (by decide) (by decide) (store bits [] f cat [] [] []) rfl)
  convert h using 1
  congr 1
  funext k;cases k with
  | inl r => cases r <;> simp [store,input,original]
  | inr r => cases r <;> simp [store,input,original]

lemma tag_read_call (phase next : Main) (hm : macroCode phase=.taggedRead input scratch tag next .reject)
    (bits rest o f cat : List Bool) :
    Run program (5*bits.length+4)
      (cfg phase (store (tagBits bits++false::rest) o f cat [] [] []))
      (cfg next (store rest o f cat [] bits [])) := by
  have h := outer_run (taggedRead_call macroCode .saveFormula input original (q:=phase)
    hm (by decide) (by decide) (by decide) (store (tagBits bits++false::rest) o f cat [] [] []) bits rest rfl rfl)
  convert h using 1
  congr 1
  funext k;cases k with
  | inl r => cases r <;> simp [store,input,tag]
  | inr r => cases r <;> simp [store,input,tag]

lemma header_check (more : Bool) (rest o f cat : List Bool) :
    Run program 2 (cfg .inspectHeader (store rest o f cat [] [more] []))
      (cfg (if more then .readSign else .checkEnd) (store rest o f cat [] [] [])) := by
  have hs : Step program (cfg .inspectHeader (store rest o f cat [] [more] []))
      (cfg (.checkHeaderEnd more) (store rest o f cat [] [] [])) := by
    cases more <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag] <;>
      funext k <;> cases k with
      | inl r => cases r <;> simp [store]
      | inr r => cases r <;> simp [store]
  have he : Step program (cfg (.checkHeaderEnd more) (store rest o f cat [] [] []))
      (cfg (if more then .readSign else .checkEnd) (store rest o f cat [] [] [])) := by
    cases more <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag]
  exact .succ hs (.one he)

lemma header_call (more : Bool) (rest o f cat : List Bool) :
    Run program 11 (cfg .readHeader (store (tagBits [more]++false::rest) o f cat [] [] []))
      (cfg (if more then .readSign else .checkEnd) (store rest o f cat [] [] [])) :=
  (tag_read_call .readHeader .inspectHeader rfl [more] rest o f cat).trans (header_check more rest o f cat)

lemma sign_check (sign : Bool) (rest o f cat : List Bool) :
    Run program 2 (cfg .inspectSign (store rest o f cat [] [sign] []))
      (cfg .readLiteral (store rest o f cat [] [] [])) := by
  have hs : Step program (cfg .inspectSign (store rest o f cat [] [sign] []))
      (cfg .checkSignEnd (store rest o f cat [] [] [])) := by
    cases sign <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag] <;>
      funext k <;> cases k with
      | inl r => cases r <;> simp [store]
      | inr r => cases r <;> simp [store]
  have he : Step program (cfg .checkSignEnd (store rest o f cat [] [] []))
      (cfg .readLiteral (store rest o f cat [] [] [])) := by
    simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag]
  exact .succ hs (.one he)

lemma sign_call (sign : Bool) (rest o f cat : List Bool) :
    Run program 11 (cfg .readSign (store (tagBits [sign]++false::rest) o f cat [] [] []))
      (cfg .readLiteral (store rest o f cat [] [] [])) :=
  (tag_read_call .readSign .inspectSign rfl [sign] rest o f cat).trans (sign_check sign rest o f cat)

lemma clause_end_call (rest o f cat : List Bool) :
    Run program 5 (cfg .readSign (store (false::rest) o f cat [] [] []))
      (cfg .readHeader (store rest o f cat [] [] [])) := by
  have h := tag_read_call .readSign .inspectSign rfl [] rest o f cat
  have hs : Step program (cfg .inspectSign (store rest o f cat [] [] []))
      (cfg .readHeader (store rest o f cat [] [] [])) := by
    simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag]
  exact h.trans (.one hs)

lemma literal_read_call (bits rest o f cat : List Bool) :
    Run program (5*bits.length+4)
      (cfg .readLiteral (store (tagBits bits++false::rest) o f cat [] [] []))
      (cfg .invokeMember (store rest o f cat bits [] [])) := by
  have h := outer_run (taggedRead_call macroCode .saveFormula input original (q:=.readLiteral)
    rfl (by decide) (by decide) (by decide) (store (tagBits bits++false::rest) o f cat [] [] []) bits rest rfl rfl)
  convert h using 1
  congr 1
  funext k;cases k with
  | inl r => cases r <;> simp [store,input,query]
  | inr r => cases r <;> simp [store,input,query]

lemma member_call (label rest o f : List Bool) (labels : List (List Bool)) :
    Run program (NPStackCatalogueMember.memberCost label labels+2)
      (cfg .invokeMember (store rest o f (dataFields labels) label [] []))
      (cfg .inspectMember (store rest o f (dataFields labels) label [] [decide (value label∈labels.map value)])) := by
  apply Macros.call_run Sum.inl State.member Sum.inl_injective member_extends
    (NPStackCatalogueMember.member_run label labels []) (.outer (.main .invokeMember)) (.outer (.main .inspectMember))
    (store rest o f (dataFields labels) label [] [])
    (store rest o f (dataFields labels) label [] [decide (value label∈labels.map value)])
  · rfl
  · rfl
  · intro k;cases k <;> rfl
  · intro k;cases k <;> rfl
  · intro k hk;cases k with
    | inl r => exact (hk r rfl).elim
    | inr r => cases r <;> rfl

lemma member_check (b : Bool) (label rest o f cat : List Bool) :
    Step program (cfg .inspectMember (store rest o f cat label [] [b]))
      (cfg (if b then .clearQuery else .reject) (store rest o f cat label [] [])) := by
  cases b <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,result] <;>
    funext k <;> cases k with
    | inl r => cases r <;> simp [store]
    | inr r => cases r <;> simp [store]

lemma clear_query_call (label rest o f cat : List Bool) :
    Run program (label.length+1) (cfg .clearQuery (store rest o f cat label [] []))
      (cfg .readSign (store rest o f cat [] [] [])) := by
  have h := outer_run (clear_loop macroCode .saveFormula input original .clearQuery .readSign query rfl
    (store rest o f cat label [] []))
  convert h using 1
  congr 1
  funext k;cases k with
  | inl r => cases r <;> simp [store,query]
  | inr r => cases r <;> simp [store,query]

lemma check_end_empty (o f cat : List Bool) :
    Step program (cfg .checkEnd (store [] o f cat [] [] [])) (cfg .accept (store [] o f cat [] [] [])) := by
  simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,input]

end BalancedAssortments.NPCNF.StackValidate
