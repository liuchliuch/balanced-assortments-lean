import BalancedAssortments.NPCNFStackValidateReject

namespace BalancedAssortments.NPCNF.StackValidate
open NPStack NPStack.Macros
open NPStackFields (tagBits dataFields)
open ComplexityTimeBinary
open Encoding

lemma empty_read_call (phase success : Main) (target : Register)
    (hm : macroCode phase=.taggedRead input scratch target success .reject)
    (hi : Function.Injective (dataMap input scratch target)) (s : Register → List Bool)
    (hinput : s input=[]) (hscratch : s scratch=[]) (htarget : s target=[]) :
    Run program 3 (cfg phase s) (cfg .reject s) := by
  have h := Macros.call_run (R := Macros.compile macroCode .saveFormula input original)
    (dataMap input scratch target) (fun st => Label.local phase (.taggedRead st)) hi
    (taggedRead_extends macroCode .saveFormula input original hm)
    (NPStackFieldData.reject_missing_terminator [] []) (.main phase) (.main .reject) s s
    (by simp [Macros.compile,Macros.code,returnCode,hm,NPStackFieldData.readConfig,NPStackFieldData.readProgram])
    (by simp [Macros.compile,Macros.code,returnCode,hm,NPStackFieldData.readConfig,NPStackFieldData.readProgram])
    (by intro k;cases k <;> simp [dataMap,NPStackFieldData.readConfig,NPStackFieldData.dataStacks,tagBits,hinput,hscratch,htarget])
    (by intro k;cases k <;> simp [dataMap,NPStackFieldData.readConfig,NPStackFieldData.dataStacks,tagBits,hinput,hscratch,htarget])
    (fun _ _ => rfl)
  exact outer_run h

lemma reject_no_header (o f cat : List Bool) :
    Run program 3 (cfg .readHeader (store [] o f cat [] [] [])) (cfg .reject (store [] o f cat [] [] [])) :=
  empty_read_call .readHeader .inspectHeader tag rfl
    (by intro a b h;cases a <;> cases b <;> simp_all [dataMap,input,scratch,tag]) _ rfl rfl rfl
lemma reject_no_sign (o f cat : List Bool) :
    Run program 3 (cfg .readSign (store [] o f cat [] [] [])) (cfg .reject (store [] o f cat [] [] [])) :=
  empty_read_call .readSign .inspectSign tag rfl
    (by intro a b h;cases a <;> cases b <;> simp_all [dataMap,input,scratch,tag]) _ rfl rfl rfl
lemma reject_no_literal (o f cat : List Bool) :
    Run program 3 (cfg .readLiteral (store [] o f cat [] [] [])) (cfg .reject (store [] o f cat [] [] [])) :=
  empty_read_call .readLiteral .invokeMember query rfl
    (by intro a b h;cases a <;> cases b <;> simp_all [dataMap,input,scratch,query]) _ rfl rfl rfl

lemma reject_bad_header (bits rest o f cat : List Bool) (hf : bits≠[false]) (ht : bits≠[true]) :
    ∃ t d,Run program t (cfg .readHeader (store (tagBits bits++false::rest) o f cat [] [] [])) d ∧
      program.code d.pc=.halt false := by
  have hr := tag_read_call .readHeader .inspectHeader rfl bits rest o f cat
  cases bits with
  | nil =>
    have hs : Step program (cfg .inspectHeader (store rest o f cat [] [] []))
        (cfg .reject (store rest o f cat [] [] [])) := by
      simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag]
    exact ⟨_,_,hr.trans (.one hs),rfl⟩
  | cons b bs =>
    cases bs with
    | nil => cases b <;> contradiction
    | cons c cs =>
      have hs : Step program (cfg .inspectHeader (store rest o f cat [] (b::c::cs) []))
          (cfg (.checkHeaderEnd b) (store rest o f cat [] (c::cs) [])) := by
        cases b <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag] <;>
          funext k <;> cases k with
          | inl r => cases r <;> simp [store]
          | inr r => cases r <;> simp [store]
      have he : Step program (cfg (.checkHeaderEnd b) (store rest o f cat [] (c::cs) []))
          (cfg .reject (store rest o f cat [] cs [])) := by
        cases c <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag] <;>
          funext k <;> cases k with
          | inl r => cases r <;> simp [store]
          | inr r => cases r <;> simp [store]
      exact ⟨_,_,hr.trans (.succ hs (.one he)),rfl⟩

lemma reject_bad_sign (b c : Bool) (bits rest o f cat : List Bool) :
    ∃ t d,Run program t (cfg .readSign (store (tagBits (b::c::bits)++false::rest) o f cat [] [] [])) d ∧
      program.code d.pc=.halt false := by
  have hr := tag_read_call .readSign .inspectSign rfl (b::c::bits) rest o f cat
  have hs : Step program (cfg .inspectSign (store rest o f cat [] (b::c::bits) []))
      (cfg .checkSignEnd (store rest o f cat [] (c::bits) [])) := by
    cases b <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag] <;>
      funext k <;> cases k with
      | inl r => cases r <;> simp [store]
      | inr r => cases r <;> simp [store]
  have he : Step program (cfg .checkSignEnd (store rest o f cat [] (c::bits) []))
      (cfg .reject (store rest o f cat [] bits [])) := by
    cases c <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag] <;>
      funext k <;> cases k with
      | inl r => cases r <;> simp [store]
      | inr r => cases r <;> simp [store]
  exact ⟨_,_,hr.trans (.succ hs (.one he)),rfl⟩

lemma reject_parseClause (fields labels : List (List Bool)) (o f : List Bool)
    (hb : (parseClause fields).1=none) :
    ∃ t d,Run program t (cfg .readSign (store (dataFields fields) o f (dataFields labels) [] [] [])) d ∧
      program.code d.pc=.halt false := by
  fun_induction parseClause fields
  · simp_all
  · rename_i sign x rest tail ih
    subst tail
    by_cases hx : value x∈labels.map value
    · have hh : (parseClause rest).1=none := by simpa using hb
      obtain ⟨t,d,hr,hd⟩ := ih hh
      have hrun := (literal_run ⟨x,sign⟩ labels (dataFields rest) o f hx).trans hr
      exact ⟨_,d,by simpa [dataFields,List.append_assoc] using hrun,hd⟩
    · obtain ⟨t,d,hr,hd⟩ := reject_literal ⟨x,sign⟩ labels (dataFields rest) o f hx
      exact ⟨t,d,by simpa [dataFields,List.append_assoc] using hr,hd⟩
  · rename_i fields hempty hsign
    cases fields with
    | nil => exact ⟨3,_,reject_no_sign o f (dataFields labels),rfl⟩
    | cons bits rest =>
      cases bits with
      | nil => exact (hempty rest rfl).elim
      | cons b bs =>
        cases bs with
        | nil =>
          cases rest with
          | cons x xs => exact (hsign b x xs rfl).elim
          | nil =>
            have hh := (sign_call b [] o f (dataFields labels)).trans (reject_no_literal o f (dataFields labels))
            exact ⟨_,_,by simpa [dataFields] using hh,rfl⟩
        | cons c cs =>
          obtain ⟨t,d,hr,hd⟩ := reject_bad_sign b c cs (dataFields rest) o f (dataFields labels)
          exact ⟨t,d,by simpa [dataFields,List.append_assoc] using hr,hd⟩

lemma reject_parseFormula (fuel fields labels : List (List Bool)) (o f : List Bool)
    (hf : fields.length ≤ fuel.length) (hb : (parseFormula fuel fields).1=none) :
    ∃ t d,Run program t (cfg .readHeader (store (dataFields fields) o f (dataFields labels) [] [] [])) d ∧
      program.code d.pc=.halt false := by
  induction fuel generalizing fields with
  | nil =>
    have he : fields=[] := List.eq_nil_of_length_eq_zero (by simpa using hf)
    subst fields
    exact ⟨3,_,reject_no_header o f (dataFields labels),rfl⟩
  | cons fuelHead fuel ih =>
    cases fields with
    | nil => exact ⟨3,_,reject_no_header o f (dataFields labels),rfl⟩
    | cons bits rest =>
      by_cases hfalse : bits=[false]
      · subst bits;simp [parseFormula] at hb
      by_cases htrue : bits=[true]
      · subst bits
        have hheader := header_call true (dataFields rest) o f (dataFields labels)
        cases hp : (parseClause rest).1 with
        | none =>
          obtain ⟨t,d,hr,hd⟩ := reject_parseClause rest labels o f hp
          exact ⟨_,d,by simpa [dataFields,List.append_assoc] using hheader.trans hr,hd⟩
        | some p =>
          rcases p with ⟨clause,remaining⟩
          have hc := Encoding.parseClause_sound rest clause remaining hp
          have hcdata : dataFields rest=dataFields (clauseFields clause)++dataFields remaining := by
            rw [←hc];simp [dataFields,List.flatMap_append]
          by_cases hm : ∀ l∈clause,value l.labelBits∈labels.map value
          · have hf' : remaining.length ≤ fuel.length := by
              have hlen := congrArg List.length hc
              simp only [List.length_append] at hlen
              simp only [List.length_cons] at hf
              omega
            have hb' : (parseFormula fuel remaining).1=none := by simpa [parseFormula,hp] using hb
            obtain ⟨t,d,hr,hd⟩ := ih remaining hf' hb'
            have hclause := clause_run clause labels (dataFields remaining) o f hm
            rw [←hcdata] at hclause
            have hh := hheader.trans (hclause.trans hr)
            exact ⟨_,d,by simpa [dataFields,List.append_assoc] using hh,hd⟩
          · obtain ⟨t,d,hr,hd⟩ := reject_clause_members clause labels (dataFields remaining) o f hm
            rw [←hcdata] at hr
            exact ⟨_,d,by simpa [dataFields,List.append_assoc] using hheader.trans hr,hd⟩
      · obtain ⟨t,d,hr,hd⟩ := reject_bad_header bits (dataFields rest) o f (dataFields labels) hfalse htrue
        exact ⟨t,d,by simpa [dataFields,List.append_assoc] using hr,hd⟩

/-- Total formula parser and membership soundness for every parsed field list,
not just pre-assumed well-formed formulas. -/
theorem formula_accepting_result (fields labels : List (List Bool)) (o f : List Bool)
    {T : ℕ} {d : Config Register State}
    (hr : Run program T (cfg .readHeader (store (dataFields fields) o f (dataFields labels) [] [] [])) d)
    (ha : accepts program d) :
    ∃ formula,(parseFormula fields fields).1=some (formula,[]) ∧ Members formula labels ∧
      d=cfg .accept (store [] o f (dataFields labels) [] [] []) ∧ T=formulaCost formula labels := by
  cases hp : (parseFormula fields fields).1 with
  | none =>
    obtain ⟨t,e,he,hh⟩ := reject_parseFormula fields fields labels o f le_rfl hp
    exact False.elim (rejecting_run_excludes_acceptance program_deterministic he hh hr ha)
  | some p =>
    rcases p with ⟨formula,rest⟩
    have hfields := Encoding.parseFormula_sound fields fields formula rest hp
    have hdata : dataFields fields=dataFields (formulaFields formula)++dataFields rest := by
      rw [←hfields];simp [dataFields,List.flatMap_append]
    rw [hdata] at hr
    cases rest with
    | nil =>
      simp only [dataFields,List.flatMap_nil,List.append_nil] at hr
      have hm : Members formula labels := by
        by_contra hn
        obtain ⟨t,e,he,hh⟩ := reject_formula_members formula labels [] o f hn
        simp only [List.append_nil] at he
        exact rejecting_run_excludes_acceptance program_deterministic he hh hr ha
      have he := (formula_run formula labels o f hm).halted_unique program_deterministic hr rfl ha
      exact ⟨formula,rfl,hm,he.2.symm,he.1.symm⟩
    | cons x xs =>
      have hn : dataFields (x::xs)≠[] := by simp [dataFields]
      obtain ⟨b,bs,hbs⟩ := List.exists_cons_of_ne_nil hn
      rw [hbs] at hr
      obtain ⟨t,e,he,hh⟩ := reject_extra_formula formula labels b bs o f
      exact False.elim (rejecting_run_excludes_acceptance program_deterministic he hh hr ha)

end BalancedAssortments.NPCNF.StackValidate
