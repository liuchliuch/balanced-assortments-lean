import BalancedAssortments.NPStackLabelEqual
import BalancedAssortments.NPStackMacroDataRuns

namespace BalancedAssortments.NPStackCatalogueMember
open NPStack NPStack.Macros
open NPStackFields (tagBits dataFields)
open ComplexityTimeBinary (value)

inductive Register | query | catalogue | label | left | right | flag | saved | scratch | output
  deriving DecidableEq,Fintype
inductive Main | probe (found : Bool) | restoreHead (found bit : Bool) | readLabel (found : Bool) |
  copyQuery (found : Bool) | copyLabel (found : Bool) | saveLabel (found : Bool) | invoke (found : Bool) |
  inspect (found : Bool) | restoreProbe (found : Bool) | restoreSavedHead (found bit : Bool) |
  readSaved (found : Bool) | emitSaved (found : Bool) | emitResult (found : Bool) | accept | reject
  deriving DecidableEq,Fintype
inductive State | outer (q : Label Main) | equal (found : Bool) (q : CompareState)
  deriving DecidableEq,Fintype

def equalMap : CompareStack → Register | .left => .left | .right => .right | .result => .flag

def macroCode : Main → Macro Register Main
  | .probe f => .pop .catalogue (.restoreProbe f) (.restoreHead f false) (.restoreHead f true)
  | .restoreHead f b => .push .catalogue b (.readLabel f)
  | .readLabel f => .taggedRead .catalogue .scratch .label (.copyQuery f) .reject
  | .copyQuery f => .copy .query .scratch .left (.copyLabel f)
  | .copyLabel f => .copy .label .scratch .right (.saveLabel f)
  | .saveLabel f => .taggedEmit .label .scratch .saved (.invoke f)
  | .invoke _ => .halt false
  | .inspect f => .pop .flag .reject (.probe f) (.probe true)
  | .restoreProbe f => .pop .saved (.emitResult f) (.restoreSavedHead f false) (.restoreSavedHead f true)
  | .restoreSavedHead f b => .push .saved b (.readSaved f)
  | .readSaved f => .taggedRead .saved .scratch .label (.emitSaved f) .reject
  | .emitSaved f => .taggedEmit .label .scratch .catalogue (.restoreProbe f)
  | .emitResult f => .push .output f .accept
  | .accept => .halt true
  | .reject => .halt false

def code : State → Instr Register State
  | .outer (.main (.invoke f)) => .jump (.equal f (.readLeft .eq))
  | .outer q => (Macros.code macroCode q).rename id State.outer
  | .equal f .done => .jump (.outer (.main (.inspect f)))
  | .equal f q => (NPStackLabelEqual.program.code q).rename equalMap (.equal f)

def program : NPStack.Program Register State :=
  ⟨code,.outer (.main (.probe false)),.catalogue,.output⟩

def store (query catalogue label left right flag saved scratch output : List Bool) : Register → List Bool
  | .query => query | .catalogue => catalogue | .label => label | .left => left | .right => right
  | .flag => flag | .saved => saved | .scratch => scratch | .output => output

def cfg (q : Main) (s : Register → List Bool) : Config Register State := ⟨.outer (.main q),s⟩

lemma outer_extends : CodeExtends (Macros.compile macroCode (.probe false) Register.catalogue Register.output)
    program id State.outer := by
  intro q h
  cases q with
  | main q => cases q <;> first | exact False.elim (h false rfl) | rfl
  | «local» q st => rfl

lemma equal_extends (f : Bool) : CodeExtends NPStackLabelEqual.program program equalMap (.equal f) := by
  intro q h;cases q <;> simp_all [program,code,NPStackLabelEqual.program]

lemma outer_run {t : ℕ} {q q' : Label Main} {s s' : Register → List Bool}
    (h : Run (Macros.compile macroCode (.probe false) Register.catalogue Register.output) t ⟨q,s⟩ ⟨q',s'⟩) :
    Run program t ⟨.outer q,s⟩ ⟨.outer q',s'⟩ :=
  h.relocate_exact id State.outer (fun _ _ h=>h) outer_extends
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩ (fun k hk=>False.elim (hk k rfl))

lemma read_label_call (f : Bool) (query label rest saved out : List Bool) :
    Run program (5*label.length+4)
      (cfg (.readLabel f) (store query (tagBits label++false::rest) [] [] [] [] saved [] out))
      (cfg (.copyQuery f) (store query rest label [] [] [] saved [] out)) := by
  have h := outer_run (taggedRead_call macroCode (.probe false) Register.catalogue Register.output
    (q:=.readLabel f) (by rfl) (by decide) (by decide) (by decide)
    (store query (tagBits label++false::rest) [] [] [] [] saved [] out) label rest rfl rfl)
  convert h using 1
  congr 1
  funext k;cases k <;> simp [store]

lemma copy_query_call (f : Bool) (query label rest saved out : List Bool) :
    Run program (5*query.length+4)
      (cfg (.copyQuery f) (store query rest label [] [] [] saved [] out))
      (cfg (.copyLabel f) (store query rest label query [] [] saved [] out)) := by
  have h := outer_run (copy_call_store macroCode (.probe false) Register.catalogue Register.output
    (q:=.copyQuery f) (by rfl) (by decide) (by decide) (by decide)
    (store query rest label [] [] [] saved [] out) rfl)
  convert h using 1
  congr 1
  funext k;cases k <;> simp [store]

lemma copy_label_call (f : Bool) (query label rest saved out : List Bool) :
    Run program (5*label.length+4)
      (cfg (.copyLabel f) (store query rest label query [] [] saved [] out))
      (cfg (.saveLabel f) (store query rest label query label [] saved [] out)) := by
  have h := outer_run (copy_call_store macroCode (.probe false) Register.catalogue Register.output
    (q:=.copyLabel f) (by rfl) (by decide) (by decide) (by decide)
    (store query rest label query [] [] saved [] out) rfl)
  convert h using 1
  congr 1
  funext k;cases k <;> simp [store]

lemma save_label_call (f : Bool) (query label rest saved out : List Bool) :
    Run program (5*label.length+5)
      (cfg (.saveLabel f) (store query rest label query label [] saved [] out))
      (cfg (.invoke f) (store query rest [] query label [] (tagBits label++false::saved) [] out)) := by
  have h := outer_run (taggedEmit_call macroCode (.probe false) Register.catalogue Register.output
    (q:=.saveLabel f) (by rfl) (by decide) (by decide) (by decide)
    (store query rest label query label [] saved [] out) rfl)
  convert h using 1
  congr 1
  funext k;cases k <;> simp [store]

lemma equal_call (f : Bool) (query label rest saved out : List Bool) :
    Run program (2*max query.length label.length+5)
      (cfg (.invoke f) (store query rest [] query label [] saved [] out))
      (cfg (.inspect f) (store query rest [] [] [] [decide (value query=value label)] saved [] out)) := by
  have h := (NPStackLabelEqual.equal_run query label []).relocate_exact equalMap (State.equal f)
    (by intro a b h;cases a <;> cases b <;> simp_all [equalMap]) (equal_extends f)
    (c' := ⟨.equal f (.readLeft .eq),store query rest [] query label [] saved [] out⟩)
    (d' := ⟨.equal f .done,store query rest [] [] [] [decide (value query=value label)] saved [] out⟩)
    ⟨rfl,by intro k;cases k <;> rfl⟩ ⟨rfl,by intro k;cases k <;> rfl⟩
    (by intro k hk;cases k <;> simp [store] <;>
      first | exact (hk .left rfl).elim | exact (hk .right rfl).elim | exact (hk .result rfl).elim)
  have hs : Step program (cfg (.invoke f) (store query rest [] query label [] saved [] out))
      ⟨.equal f (.readLeft .eq),store query rest [] query label [] saved [] out⟩ := by simp [Step,successors,program,code,cfg]
  have he : Step program ⟨.equal f .done,store query rest [] [] [] [decide (value query=value label)] saved [] out⟩
      (cfg (.inspect f) (store query rest [] [] [] [decide (value query=value label)] saved [] out)) := by simp [Step,successors,program,code,cfg]
  have hh := Run.succ hs (h.trans (.one he))
  convert hh using 1 <;> omega

lemma inspect_result (f b : Bool) (query rest saved out : List Bool) :
    Step program (cfg (.inspect f) (store query rest [] [] [] [b] saved [] out))
      (cfg (.probe (f||b)) (store query rest [] [] [] [] saved [] out)) := by
  cases b <;> cases f <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store] <;>
    funext k <;> cases k <;> simp [store]

lemma probe_call (f b : Bool) (query rest saved out : List Bool) :
    Run program 2 (cfg (.probe f) (store query (b::rest) [] [] [] [] saved [] out))
      (cfg (.readLabel f) (store query (b::rest) [] [] [] [] saved [] out)) := by
  have hs : Step program (cfg (.probe f) (store query (b::rest) [] [] [] [] saved [] out))
      (cfg (.restoreHead f b) (store query rest [] [] [] [] saved [] out)) := by
    cases b <;> simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store] <;>
      funext k <;> cases k <;> simp [store]
  have he : Step program (cfg (.restoreHead f b) (store query rest [] [] [] [] saved [] out))
      (cfg (.readLabel f) (store query (b::rest) [] [] [] [] saved [] out)) := by
    simp [Step,successors,program,code,Macros.code,macroCode,Instr.rename,cfg,store]
    funext k;cases k <;> simp [store]
  exact .succ hs (.one he)

end BalancedAssortments.NPStackCatalogueMember
