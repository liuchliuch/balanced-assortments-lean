import BalancedAssortments.NPStackMacroDataRuns
import BalancedAssortments.NPStackFiniteExec
import BalancedAssortments.NPCNFEncoding

/-! Assemble a valid catalogue prefix from preserved original labels and the
reverse-allocation list produced by the formula transformer. Each tagged label
is read and re-emitted by actual finite Boolean-stack instructions. -/
namespace BalancedAssortments.NPCNF.StackCatalogueOutput
open NPStack NPStack.Macros NPStackFields Encoding

inductive Register | original | allocated | output | scratchRead | scratchEmit | label
  deriving DecidableEq,Fintype
inductive Phase | allocated | original deriving DecidableEq,Fintype
inductive State | marker0 | marker1 | marker2 | probe (p : Phase) | restoreHead (p : Phase) (b : Bool) |
  read (p : Phase) | emit (p : Phase) | header0 (p : Phase) | header1 (p : Phase) | header2 (p : Phase) |
  accept | reject
  deriving DecidableEq,Fintype

def source : Phase → Register | .allocated => .allocated | .original => .original
def afterPhase : Phase → State | .allocated => .probe .original | .original => .accept

def macroCode : State → Macro Register State
  | .marker0 => .push .output false .marker1
  | .marker1 => .push .output false .marker2
  | .marker2 => .push .output true (.probe .allocated)
  | .probe p => .pop (source p) (afterPhase p) (.restoreHead p false) (.restoreHead p true)
  | .restoreHead p b => .push (source p) b (.read p)
  | .read p => .taggedRead (source p) .scratchRead .label (.emit p) .reject
  | .emit p => .taggedEmit .label .scratchEmit .output (.header0 p)
  | .header0 p => .push .output false (.header1 p)
  | .header1 p => .push .output true (.header2 p)
  | .header2 p => .push .output true (.probe p)
  | .accept => .halt true
  | .reject => .halt false

def program : Program Register (Label State) := Macros.compile macroCode .marker0 .original .output

def store (original allocated out : List Bool) : Register → List Bool
  | .original => original | .allocated => allocated | .output => out | _ => []

@[simp] lemma update_store_output (original allocated out out' : List Bool) :
    Function.update (store original allocated out) .output out'=store original allocated out' := by
  funext k;cases k <;> simp [store]

def cfg (q : State) (s : Register → List Bool) : Config Register (Label State) := ⟨.main q,s⟩

def phaseStore : Phase → List Bool → List Bool → List Bool → Register → List Bool
  | .allocated,xs,other,out => store other xs out
  | .original,xs,other,out => store xs other out

@[simp] lemma phaseStore_source (p : Phase) (xs other out : List Bool) : phaseStore p xs other out (source p)=xs := by cases p <;> rfl
@[simp] lemma phaseStore_output (p : Phase) (xs other out : List Bool) : phaseStore p xs other out .output=out := by cases p <;> rfl
@[simp] lemma phaseStore_label (p : Phase) (xs other out : List Bool) : phaseStore p xs other out .label=[] := by cases p <;> rfl
@[simp] lemma phaseStore_read (p : Phase) (xs other out : List Bool) : phaseStore p xs other out .scratchRead=[] := by cases p <;> rfl
@[simp] lemma phaseStore_emit (p : Phase) (xs other out : List Bool) : phaseStore p xs other out .scratchEmit=[] := by cases p <;> rfl

lemma probe_cons (p : Phase) (b : Bool) (xs other out : List Bool) :
    Run program 2 (cfg (.probe p) (phaseStore p (b::xs) other out))
      (cfg (.read p) (phaseStore p (b::xs) other out)) := by
  apply firstRun_sound
  cases p <;> cases b <;> simp [firstRun,successors,program,Macros.compile,code,macroCode,cfg,phaseStore,store,source]

lemma label_run (p : Phase) (label rest other out : List Bool) :
    Run program (10*label.length+14)
      (cfg (.probe p) (phaseStore p (tagBits label++false::rest) other out))
      (cfg (.probe p) (phaseStore p rest other (tagBits [true]++false::(tagBits label++false::out)))) := by
  let input := tagBits label++false::rest
  let s0 := phaseStore p input other out
  let s1 := Function.update (phaseStore p rest other out) .label label
  let s2 := phaseStore p rest other (tagBits label++false::out)
  have h0 : Run program 2 (cfg (.probe p) s0) (cfg (.read p) s0) := by
    cases label with
    | nil => exact probe_cons p false rest other out
    | cons b bs => exact probe_cons p true (b::tagBits bs++false::rest) other out
  have h1 := taggedRead_call macroCode .marker0 .original .output
    (q := .read p) (yes := .emit p) (no := .reject) rfl
    (by cases p <;> decide) (by cases p <;> decide) (by decide) s0 label rest (by simp [s0,input]) (by simp [s0])
  have he1 : Function.update (Function.update s0 (source p) rest) .label (label++s0 .label)=s1 := by
    funext k;cases p <;> cases k <;> simp [s0,s1,input,phaseStore,store,source]
  rw [he1] at h1
  have h2 := taggedEmit_call macroCode .marker0 .original .output
    (q := .emit p) (next := .header0 p) rfl (by decide) (by decide) (by decide) s1 (by simp [s1])
  have he2 : Function.update (Function.update s1 .label []) .output (tagBits (s1 .label)++false::s1 .output)=s2 := by
    funext k;cases p <;> cases k <;> simp [s1,s2,phaseStore,store]
  rw [he2] at h2
  have h3 : Run program 3 (cfg (.header0 p) s2)
      (cfg (.probe p) (phaseStore p rest other (tagBits [true]++false::(tagBits label++false::out)))) := by
    apply firstRun_sound
    cases p <;> simp [firstRun,successors,program,Macros.compile,code,macroCode,cfg,s2,phaseStore,store,tagBits]
  have hh := h0.trans (h1.trans (h2.trans h3))
  convert hh using 1 <;> simp [s1] <;> omega

def catalogueBody (labels : List (List Bool)) : List (List Bool) := labels.flatMap (fun label=>[[true],label])
def recordsCost (labels : List (List Bool)) : ℕ := (labels.map (fun label=>10*label.length+14)).sum+1

lemma loop_run (p : Phase) (labels : List (List Bool)) (other out : List Bool) :
    Run program (recordsCost labels) (cfg (.probe p) (phaseStore p (dataFields labels) other out))
      (cfg (afterPhase p) (phaseStore p [] other (dataFields (catalogueBody labels.reverse)++out))) := by
  induction labels generalizing out with
  | nil =>
    apply Run.one
    cases p <;> simp [Step,successors,program,Macros.compile,code,macroCode,cfg,phaseStore,store,
      source,afterPhase,dataFields,catalogueBody]
  | cons label labels ih =>
    have h1 := label_run p label (dataFields labels) other out
    have h2 := ih (tagBits [true]++false::(tagBits label++false::out))
    have hh := h1.trans h2
    simpa [recordsCost,dataFields,catalogueBody,tagBits,List.reverse_cons,List.flatMap_append,
      List.append_assoc,Nat.add_assoc] using hh

lemma catalogFields_body (labels : List (List Bool)) : catalogFields labels=catalogueBody labels++[[false]] := by
  induction labels <;> simp_all [catalogFields,catalogueBody]

/-- Complete actual catalogue-prefix assembly. Input record order is reversed
by prepending; the generated allocation stream is already reverse-chronological,
so its emitted order is chronological. -/
theorem catalogue_run (original allocated : List (List Bool)) (formula : List Bool) :
    Run program (recordsCost original+recordsCost allocated+3)
      (cfg .marker0 (store (dataFields original) (dataFields allocated) formula))
      (cfg .accept (store [] [] (dataFields (catalogFields (original.reverse++allocated.reverse))++formula))) := by
  have h0 : Run program 3 (cfg .marker0 (store (dataFields original) (dataFields allocated) formula))
      (cfg (.probe .allocated) (store (dataFields original) (dataFields allocated) (tagBits [false]++false::formula))) := by
    apply firstRun_sound
    simp [firstRun,successors,program,Macros.compile,code,macroCode,cfg,store,tagBits]
  have h1 := loop_run .allocated allocated (dataFields original) (tagBits [false]++false::formula)
  have h2 := loop_run .original original []
    (dataFields (catalogueBody allocated.reverse)++(tagBits [false]++false::formula))
  have hh := h0.trans (h1.trans h2)
  simpa [catalogFields_body,catalogueBody,dataFields,phaseStore,afterPhase,tagBits,List.flatMap_append,
    List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

end BalancedAssortments.NPCNF.StackCatalogueOutput
