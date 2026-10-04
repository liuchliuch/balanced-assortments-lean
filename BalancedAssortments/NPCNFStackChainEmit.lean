import BalancedAssortments.NPCNFStackChainProgram
import BalancedAssortments.NPStackMacroDataRuns

namespace BalancedAssortments.NPCNF.StackChain
open NPStack NPStack.Macros StackTemplate StackGate NPStackFields

def cfg (q : State) (s : Register → List Bool) : Config Register (Label State) := ⟨.main q,s⟩

def WorkEmpty (s : Register → List Bool) : Prop :=
  s .scratchRead=[] ∧ s .scratchCopy=[] ∧ s .temporary=[]

def regs (s : Register → List Bool) : StackGate.Register → List Bool := fun k=>s (labelRegister k)

def emitted (s : Register → List Bool) (out : List Bool) : Register → List Bool := Function.update s .output out

lemma work_emitted (s : Register → List Bool) (out : List Bool) (h : WorkEmpty s) : WorkEmpty (emitted s out) := by
  simpa [WorkEmpty,emitted] using h
@[simp] lemma regs_emitted (s : Register → List Bool) (out : List Bool) : regs (emitted s out)=regs s := by
  funext k;cases k <;> rfl

lemma emit_bit (initialSign : Bool) (block : Block) (pc : Fin 41) (b : Bool)
    (h : (blockJobs block)[pc.val]?=some (.bit b)) (s : Register → List Bool) :
    Run (program initialSign) 1 (cfg (.emit block pc) s)
      (cfg (.emit block (nextJob pc)) (emitted s (b::s .output))) := by
  apply Run.one
  simp [Step,successors,program,Macros.compile,Macros.code,macroCode,h,cfg,emitted]

lemma emit_field (initialSign : Bool) (block : Block) (pc : Fin 41) (k : StackGate.Register)
    (h : (blockJobs block)[pc.val]?=some (.field k)) (s : Register → List Bool) (hw : WorkEmpty s) :
    Run (program initialSign) (10*(regs s k).length+9) (cfg (.emit block pc) s)
      (cfg (.emit block (nextJob pc)) (emitted s (tagBits (regs s k)++false::s .output))) := by
  have hm : macroCode (.emit block pc)=.copy (labelRegister k) .scratchCopy .temporary (.emitField block pc) := by
    simp [macroCode,h]
  have hcopy := copy_call_store macroCode (.readSign initialSign) .input .output hm
    (by cases k <;> decide) (by cases k <;> decide) (by decide) s hw.2.1
  simp only [hw.2.2,List.append_nil] at hcopy
  let s' := Function.update s .temporary (regs s k)
  have hread : s' .scratchRead=[] := by simpa [s'] using hw.1
  have hemit := taggedEmit_call macroCode (.readSign initialSign) .input .output
    (q := .emitField block pc) (next := .emit block (nextJob pc)) rfl
    (by decide) (by decide) (by decide) s' hread
  have hfinal : Function.update (Function.update s' .temporary []) .output
      (tagBits (s' .temporary)++false::s' .output) = emitted s (tagBits (regs s k)++false::s .output) := by
    funext r
    cases r <;> simp [s',emitted,hw.2.2]
  rw [hfinal] at hemit
  have hh := hcopy.trans hemit
  change Run (program initialSign) _ _ _ at hh
  simp only [s',Function.update_self] at hh
  convert hh using 1 <;> dsimp [regs] <;> omega

lemma emit_done (initialSign : Bool) (block : Block) (pc : Fin 41)
    (h : (blockJobs block)[pc.val]?=none) (s : Register → List Bool) :
    Run (program initialSign) 1 (cfg (.emit block pc) s) (cfg (.restoreOutput block) s) := by
  apply Run.one
  simp [Step,successors,program,Macros.compile,Macros.code,macroCode,h,cfg]

@[simp] lemma emitted_output (s : Register → List Bool) (out : List Bool) : (emitted s out) .output=out := by simp [emitted]
@[simp] lemma emitted_emitted (s : Register → List Bool) (a b : List Bool) : emitted (emitted s a) b=emitted s b := by simp [emitted]

def emitJobCost (s : Register → List Bool) : Job StackGate.Register → ℕ
  | .bit _ => 1
  | .field k => 10*(regs s k).length+9

@[simp] lemma emitJobCost_emitted (s : Register → List Bool) (out : List Bool) :
    emitJobCost (emitted s out)=emitJobCost s := by
  funext job;cases job <;> simp [emitJobCost]

def emitCost (s : Register → List Bool) (jobs : List (Job StackGate.Register)) : ℕ :=
  (jobs.map (emitJobCost s)).sum

@[simp] lemma emitCost_emitted (s : Register → List Bool) (out : List Bool) (jobs : List (Job StackGate.Register)) :
    emitCost (emitted s out) jobs=emitCost s jobs := by
  have he : emitJobCost (emitted s out)=emitJobCost s := by funext job; cases job <;> simp [emitJobCost]
  simp [emitCost,he]

lemma emit_suffix (initialSign : Bool) (block : Block) (rest pre : List (Job StackGate.Register))
    (hsplit : pre++rest=blockJobs block) (s : Register → List Bool) (hw : WorkEmpty s) :
    Run (program initialSign) (emitCost s rest+1)
      (cfg (.emit block ⟨pre.length,by have hh := congrArg List.length hsplit;have hl:=blockJobs_length block;simp only [List.length_append] at hh;omega⟩) s)
      (cfg (.restoreOutput block) (emitted s (applyJobs (regs s) rest (s .output)))) := by
  induction rest generalizing pre s with
  | nil =>
    have hp : pre=blockJobs block := by simpa using hsplit
    subst pre
    have hh := emit_done initialSign block ⟨(blockJobs block).length,by have := blockJobs_length block;omega⟩
      (by simp) s
    simpa [emitCost,applyJobs,emitted] using hh
  | cons job rest ih =>
    have hlen : pre.length+1+rest.length=(blockJobs block).length := by
      have hh := congrArg List.length hsplit
      simp only [List.length_append,List.length_cons] at hh;omega
    have hlimit := blockJobs_length block
    let i : Fin 41 := ⟨pre.length,by omega⟩
    let next : Fin 41 := ⟨(pre++[job]).length,by simp;omega⟩
    have hi : (blockJobs block)[i.val]?=some job := by
      dsimp only [i]
      rw [← hsplit,List.getElem?_append_right (by omega)];simp
    have hn : nextJob i=next := by
      apply Fin.ext
      simp only [nextJob,i,next,List.length_append,List.length_cons,List.length_nil];omega
    have hsplit' : (pre++[job])++rest=blockJobs block := by simpa [List.append_assoc] using hsplit
    let s' := emitted s (applyJob (regs s) job (s .output))
    have hr := ih (pre++[job]) hsplit' s' (work_emitted s _ hw)
    change Run (program initialSign) (emitCost s' rest+1) (cfg (.emit block next) s') _ at hr
    change Run (program initialSign) (emitCost s (job::rest)+1) (cfg (.emit block i) s) _
    cases job with
    | bit b =>
      have hs := emit_bit initialSign block i b hi s
      rw [hn] at hs
      have hh := hs.trans hr
      simpa [s',emitCost,emitJobCost,applyJobs,applyJob,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    | field k =>
      have hs := emit_field initialSign block i k hi s hw
      rw [hn] at hs
      have hh := hs.trans hr
      simpa [s',emitCost,emitJobCost,applyJobs,applyJob,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Full fixed-block emission inside the actual streaming chain program. -/
theorem emit_block (initialSign : Bool) (block : Block) (s : Register → List Bool) (hw : WorkEmpty s) :
    Run (program initialSign) (emitCost s (blockJobs block)+1) (cfg (.emit block 0) s)
      (cfg (.restoreOutput block) (emitted s (dataFields ((blockSpecs block).map (fieldValue (regs s)))++s .output))) := by
  have hh := emit_suffix initialSign block (blockJobs block) [] rfl s hw
  rw [show applyJobs (regs s) (blockJobs block) (s .output)=_ from fieldsJobs_apply (regs s) (blockSpecs block) (s .output)] at hh
  exact hh

end BalancedAssortments.NPCNF.StackChain
