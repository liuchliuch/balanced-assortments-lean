import BalancedAssortments.NPStackCatalogueMember

namespace BalancedAssortments.NPStackCatalogueMember
open NPStack NPStack.Macros
open NPStackFields (tagBits dataFields)
open ComplexityTimeBinary (value)

def rowCost (query label : List Bool) : ℕ := 15*label.length+5*query.length+2*max query.length label.length+25

def scanCost (query : List Bool) (labels : List (List Bool)) : ℕ := (labels.map (rowCost query)).sum

def foundResult : Bool → List Bool → List (List Bool) → Bool
  | f,_,[] => f
  | f,q,x::xs => foundResult (f||decide (value q=value x)) q xs

lemma first_record (f : Bool) (query label rest saved out : List Bool) :
    Run program (rowCost query label)
      (cfg (.probe f) (store query (tagBits label++false::rest) [] [] [] [] saved [] out))
      (cfg (.probe (f||decide (value query=value label)))
        (store query rest [] [] [] [] (tagBits label++false::saved) [] out)) := by
  have hp : Run program 2
      (cfg (.probe f) (store query (tagBits label++false::rest) [] [] [] [] saved [] out))
      (cfg (.readLabel f) (store query (tagBits label++false::rest) [] [] [] [] saved [] out)) := by
    cases label with
    | nil => simpa [tagBits] using probe_call f false query rest saved out
    | cons b bs => simpa [tagBits] using probe_call f true query (b::(tagBits bs++false::rest)) saved out
  have hh := hp.trans ((read_label_call f query label rest saved out).trans
    ((copy_query_call f query label rest saved out).trans ((copy_label_call f query label rest saved out).trans
      ((save_label_call f query label rest saved out).trans ((equal_call f query label rest (tagBits label++false::saved) out).trans
        (.one (inspect_result f (decide (value query=value label)) query rest (tagBits label++false::saved) out)))))))
  convert hh using 1 <;> unfold rowCost <;> omega

lemma first_pass (f : Bool) (query : List Bool) (labels : List (List Bool)) (saved out : List Bool) :
    Run program (scanCost query labels+1)
      (cfg (.probe f) (store query (dataFields labels) [] [] [] [] saved [] out))
      (cfg (.restoreProbe (foundResult f query labels))
        (store query [] [] [] [] [] (dataFields labels.reverse++saved) [] out)) := by
  induction labels generalizing f saved with
  | nil =>
    apply Run.one
    simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store,dataFields,scanCost,foundResult]
  | cons label labels ih =>
    have hh := (first_record f query label (dataFields labels) saved out).trans
      (ih (f||decide (value query=value label)) (tagBits label++false::saved))
    convert hh using 1 <;> simp [scanCost,dataFields,foundResult,List.reverse_cons,List.flatMap_append,List.append_assoc] <;> omega

lemma restore_probe (f b : Bool) (query catalogue rest out : List Bool) :
    Run program 2 (cfg (.restoreProbe f) (store query catalogue [] [] [] [] (b::rest) [] out))
      (cfg (.readSaved f) (store query catalogue [] [] [] [] (b::rest) [] out)) := by
  have hs : Step program (cfg (.restoreProbe f) (store query catalogue [] [] [] [] (b::rest) [] out))
      (cfg (.restoreSavedHead f b) (store query catalogue [] [] [] [] rest [] out)) := by
    cases b <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store] <;>
      funext k <;> cases k <;> simp [store]
  have he : Step program (cfg (.restoreSavedHead f b) (store query catalogue [] [] [] [] rest [] out))
      (cfg (.readSaved f) (store query catalogue [] [] [] [] (b::rest) [] out)) := by
    simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store]
    funext k;cases k <;> simp [store]
  exact .succ hs (.one he)

lemma read_saved_call (f : Bool) (query catalogue label rest out : List Bool) :
    Run program (5*label.length+4)
      (cfg (.readSaved f) (store query catalogue [] [] [] [] (tagBits label++false::rest) [] out))
      (cfg (.emitSaved f) (store query catalogue label [] [] [] rest [] out)) := by
  have h := outer_run (taggedRead_call macroCode (.probe false) Register.catalogue Register.output
    (q:=.readSaved f) (by rfl) (by decide) (by decide) (by decide)
    (store query catalogue [] [] [] [] (tagBits label++false::rest) [] out) label rest rfl rfl)
  convert h using 1
  congr 1
  funext k;cases k <;> simp [store]

lemma emit_saved_call (f : Bool) (query catalogue label rest out : List Bool) :
    Run program (5*label.length+5)
      (cfg (.emitSaved f) (store query catalogue label [] [] [] rest [] out))
      (cfg (.restoreProbe f) (store query (tagBits label++false::catalogue) [] [] [] [] rest [] out)) := by
  have h := outer_run (taggedEmit_call macroCode (.probe false) Register.catalogue Register.output
    (q:=.emitSaved f) (by rfl) (by decide) (by decide) (by decide)
    (store query catalogue label [] [] [] rest [] out) rfl)
  convert h using 1
  congr 1
  funext k;cases k <;> simp [store]

lemma restore_record (f : Bool) (query catalogue label rest out : List Bool) :
    Run program (10*label.length+11)
      (cfg (.restoreProbe f) (store query catalogue [] [] [] [] (tagBits label++false::rest) [] out))
      (cfg (.restoreProbe f) (store query (tagBits label++false::catalogue) [] [] [] [] rest [] out)) := by
  have hp : Run program 2
      (cfg (.restoreProbe f) (store query catalogue [] [] [] [] (tagBits label++false::rest) [] out))
      (cfg (.readSaved f) (store query catalogue [] [] [] [] (tagBits label++false::rest) [] out)) := by
    cases label with
    | nil => simpa [tagBits] using restore_probe f false query catalogue rest out
    | cons b bs => simpa [tagBits] using restore_probe f true query catalogue (b::(tagBits bs++false::rest)) out
  have hh := hp.trans ((read_saved_call f query catalogue label rest out).trans (emit_saved_call f query catalogue label rest out))
  convert hh using 1 <;> omega

def restoreCost (labels : List (List Bool)) : ℕ := (labels.map (fun x => 10*x.length+11)).sum

lemma restore_pass (f : Bool) (query catalogue : List Bool) (labels : List (List Bool)) (out : List Bool) :
    Run program (restoreCost labels+2)
      (cfg (.restoreProbe f) (store query catalogue [] [] [] [] (dataFields labels) [] out))
      (cfg .accept (store query (dataFields labels.reverse++catalogue) [] [] [] [] [] [] (f::out))) := by
  induction labels generalizing catalogue with
  | nil =>
    have hs : Step program (cfg (.restoreProbe f) (store query catalogue [] [] [] [] [] [] out))
        (cfg (.emitResult f) (store query catalogue [] [] [] [] [] [] out)) := by
      simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store]
    have he : Step program (cfg (.emitResult f) (store query catalogue [] [] [] [] [] [] out))
        (cfg .accept (store query catalogue [] [] [] [] [] [] (f::out))) := by
      simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store]
      funext k;cases k <;> simp [store]
    simpa [restoreCost,dataFields] using Run.succ hs (.one he)
  | cons label labels ih =>
    have hh := (restore_record f query catalogue label (dataFields labels) out).trans
      (ih (tagBits label++false::catalogue))
    convert hh using 1 <;> simp [restoreCost,dataFields,List.reverse_cons,List.flatMap_append,List.append_assoc] <;> omega

lemma foundResult_correct (f : Bool) (query : List Bool) (labels : List (List Bool)) :
    foundResult f query labels = (f||decide (value query∈labels.map value)) := by
  induction labels generalizing f with
  | nil => simp [foundResult]
  | cons x xs ih =>
    simp only [foundResult,ih,List.map_cons,List.mem_cons]
    cases f <;> by_cases he : value query=value x <;> by_cases hm : value query∈xs.map value <;> simp [he,hm]

def memberCost (query : List Bool) (labels : List (List Bool)) : ℕ := scanCost query labels+restoreCost labels+3

/-- Exact numeric membership, restoring both the query and the complete
catalogue byte-for-byte, even for noncanonical padded binary labels. -/
theorem member_run (query : List Bool) (labels : List (List Bool)) (out : List Bool) :
    Run program (memberCost query labels)
      (cfg (.probe false) (store query (dataFields labels) [] [] [] [] [] [] out))
      (cfg .accept (store query (dataFields labels) [] [] [] [] [] []
        (decide (value query∈labels.map value)::out))) := by
  have h1 := first_pass false query labels [] out
  simp only [List.append_nil] at h1
  have hh := h1.trans (restore_pass (foundResult false query labels) query [] labels.reverse out)
  simp only [List.reverse_reverse,List.append_nil] at hh
  have hc : restoreCost labels.reverse=restoreCost labels := by simp [restoreCost,List.map_reverse]
  rw [hc,foundResult_correct] at hh
  convert hh using 1 <;> simp [memberCost] <;> omega

lemma memberCost_bound (query : List Bool) (labels : List (List Bool)) :
    memberCost query labels ≤ 27*(labels.map List.length).sum+labels.length*(7*query.length+36)+3 := by
  unfold memberCost
  have hh : scanCost query labels+restoreCost labels ≤
      27*(labels.map List.length).sum+labels.length*(7*query.length+36) := by
    induction labels with
    | nil => simp [scanCost,restoreCost]
    | cons x xs ih =>
      have hm : max query.length x.length ≤ query.length+x.length := max_le (by omega) (by omega)
      simp only [scanCost,restoreCost,List.map_cons,List.sum_cons,List.length_cons,rowCost] at *
      nlinarith
  omega

end BalancedAssortments.NPStackCatalogueMember
