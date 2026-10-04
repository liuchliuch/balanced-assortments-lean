import BalancedAssortments.NPCNFStackCatalogueCorrect
import BalancedAssortments.NPCNFParsingBounds

namespace BalancedAssortments.NPCNF.StackCatalogue
open NPStack NPStack.Macros
open NPStackFields (tagBits dataFields)
open ComplexityTimeBinary
open Encoding (catalogFields parseCatalog)

lemma empty_read_call (phase success : Main) (target : Register)
    (hm : macroCode phase=.taggedRead input scratch target success .reject)
    (hi : Function.Injective (dataMap input scratch target)) (s : Register → List Bool)
    (hinput : s input=[]) (hscratch : s scratch=[]) (htarget : s target=[]) :
    Run program 3 (cfg phase s) (cfg .reject s) := by
  have h := Macros.call_run (R := Macros.compile macroCode .readTag input fresh)
    (dataMap input scratch target) (fun st => Label.local phase (.taggedRead st)) hi
    (taggedRead_extends macroCode .readTag input fresh hm)
    (NPStackFieldData.reject_missing_terminator [] []) (.main phase) (.main .reject) s s
    (by simp [Macros.compile,Macros.code,returnCode,hm,NPStackFieldData.readConfig,NPStackFieldData.readProgram])
    (by simp [Macros.compile,Macros.code,returnCode,hm,NPStackFieldData.readConfig,NPStackFieldData.readProgram])
    (by intro k;cases k <;> simp [dataMap,NPStackFieldData.readConfig,NPStackFieldData.dataStacks,tagBits,hinput,hscratch,htarget])
    (by intro k;cases k <;> simp [dataMap,NPStackFieldData.readConfig,NPStackFieldData.dataStacks,tagBits,hinput,hscratch,htarget])
    (fun _ _ => rfl)
  exact outer_run h

lemma reject_no_header (m cat : List Bool) :
    Run program 3 (cfg .readTag (store [] m [] [] [] cat [] [] []))
      (cfg .reject (store [] m [] [] [] cat [] [] [])) :=
  empty_read_call .readTag .inspectTag tag rfl
    (by intro a b h;cases a <;> cases b <;> simp_all [dataMap,input,scratch,tag]) _ rfl rfl rfl

lemma reject_no_label (m cat : List Bool) :
    Run program 3 (cfg .readLabel (store [] m [] [] [] cat [] [] []))
      (cfg .reject (store [] m [] [] [] cat [] [] [])) :=
  empty_read_call .readLabel .invokeMember query rfl
    (by intro a b h;cases a <;> cases b <;> simp_all [dataMap,input,scratch,query]) _ rfl rfl rfl

lemma reject_bad_header (bits rest m cat : List Bool) (hf : bits≠[false]) (ht : bits≠[true]) :
    ∃ t d,Run program t (cfg .readTag (store (tagBits bits++false::rest) m [] [] [] cat [] [] [])) d ∧
      program.code d.pc=.halt false := by
  have hr := read_tag_call bits rest m cat
  cases bits with
  | nil =>
    have hs : Step program (cfg .inspectTag (store rest m [] [] [] cat [] [] []))
        (cfg .reject (store rest m [] [] [] cat [] [] [])) := by
      simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag]
    exact ⟨_,_,hr.trans (.one hs),rfl⟩
  | cons b bs =>
    cases bs with
    | nil => cases b <;> contradiction
    | cons c cs =>
      have hs : Step program (cfg .inspectTag (store rest m [] [] (b::c::cs) cat [] [] []))
          (cfg (.checkTagEnd b) (store rest m [] [] (c::cs) cat [] [] [])) := by
        cases b <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag] <;>
          funext k <;> cases k with
          | inl r => cases r <;> simp [store]
          | inr r => cases r <;> simp [store]
      have he : Step program (cfg (.checkTagEnd b) (store rest m [] [] (c::cs) cat [] [] []))
          (cfg .reject (store rest m [] [] cs cat [] [] [])) := by
        cases c <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,tag] <;>
          funext k <;> cases k with
          | inl r => cases r <;> simp [store]
          | inr r => cases r <;> simp [store]
      exact ⟨_,_,hr.trans (.succ hs (.one he)),rfl⟩

/-- Malformed catalog framing is rejected, even if duplicate detection rejects
an earlier otherwise well-framed label. -/
theorem reject_parseCatalog (fields seen : List (List Bool)) (m : List Bool)
    (hb : (parseCatalog fields).1=none) :
    ∃ t d,Run program t (cfg .readTag (store (dataFields fields) m [] [] [] (dataFields seen) [] [] [])) d ∧
      program.code d.pc=.halt false := by
  fun_induction parseCatalog fields generalizing seen m
  · simp_all
  · rename_i x rest tail ih
    subst tail
    by_cases hx : value x∈seen.map value
    · obtain ⟨t,_,d,hr,hd⟩ := duplicate_record x (dataFields rest) m seen hx
      exact ⟨t,d,by simpa [dataFields,List.append_assoc] using hr,hd⟩
    · have hh : (parseCatalog rest).1=none := by simpa [parseCatalog] using hb
      obtain ⟨t,d,hr,hd⟩ := ih (x::seen) (chooseMaximum x m) hh
      have hrun := (record_run x (dataFields rest) m seen hx).trans hr
      exact ⟨_,d,by simpa [dataFields,List.append_assoc] using hrun,hd⟩
  · rename_i fields hfalse htrue
    cases fields with
    | nil => exact ⟨3,_,reject_no_header m (dataFields seen),rfl⟩
    | cons bits rest =>
      have hf : bits≠[false] := by intro he;subst bits;exact hfalse rest rfl
      by_cases ht : bits=[true]
      · subst bits
        cases rest with
        | cons x xs => exact (htrue x xs rfl).elim
        | nil =>
          have hh := (header_call true [] m (dataFields seen)).trans (reject_no_label m (dataFields seen))
          exact ⟨_,_,by simpa [dataFields] using hh,rfl⟩
      · obtain ⟨t,d,hr,hd⟩ := reject_bad_header bits (dataFields rest) m (dataFields seen) hf ht
        exact ⟨t,d,by simpa [dataFields,List.append_assoc] using hr,hd⟩

/-- Total catalog-header semantics on every parsed field stream. Successful
execution witnesses the original parser's exact header/suffix decomposition. -/
theorem header_accepting_result (fields : List (List Bool)) {t : ℕ} {d : Config Register State}
    (hr : Run program t (cfg .readTag (store (dataFields fields) [] [] [] [] [] [] [] [])) d)
    (ha : accepts program d) :
    ∃ labels suffix,(parseCatalog fields).1=some (labels,suffix) ∧ (labels.map value).Nodup ∧
      d=cfg .accept (store (dataFields suffix) [] (addCarry (selectedMaximum labels []) [] true).1 [] []
        (dataFields labels.reverse) [] [] []) ∧ t=catalogueCost labels [] [] := by
  cases hp : (parseCatalog fields).1 with
  | none =>
    obtain ⟨u,e,he,hh⟩ := reject_parseCatalog fields [] [] hp
    exact False.elim (rejecting_run_excludes_acceptance program_deterministic he hh hr ha)
  | some p =>
    rcases p with ⟨labels,suffix⟩
    have hfields := Encoding.parseCatalog_sound fields labels suffix hp
    have hinput : dataFields fields=dataFields (catalogFields labels)++dataFields suffix := by
      rw [←hfields];simp [dataFields,List.flatMap_append]
    rw [hinput] at hr
    obtain ⟨hn,hd,ht⟩ := accepting_result labels (dataFields suffix) hr ha
    exact ⟨labels,suffix,rfl,hn,hd,ht⟩

end BalancedAssortments.NPCNF.StackCatalogue
