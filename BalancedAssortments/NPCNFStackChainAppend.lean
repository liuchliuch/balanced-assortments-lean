import BalancedAssortments.NPCNFStackChainEmit

namespace BalancedAssortments.NPCNF.StackChain
open NPStack NPStack.Macros StackTemplate StackGate NPStackFields

def afterBlock : Block → State | .unit _ => .accept | .gate _ _ => .clearLeft

def ioStore (s : Register → List Bool) (out saved : List Bool) : Register → List Bool :=
  Function.update (Function.update s .output out) .savedOutput saved

@[simp] lemma io_output (s : Register → List Bool) (out saved : List Bool) : ioStore s out saved .output=out := by simp [ioStore]
@[simp] lemma io_saved (s : Register → List Bool) (out saved : List Bool) : ioStore s out saved .savedOutput=saved := by simp [ioStore]
@[simp] lemma io_update_output (s : Register → List Bool) (out saved xs : List Bool) :
    Function.update (ioStore s out saved) .output xs=ioStore s xs saved := by funext k;cases k <;> simp [ioStore]
@[simp] lemma io_update_saved (s : Register → List Bool) (out saved xs : List Bool) :
    Function.update (ioStore s out saved) .savedOutput xs=ioStore s out xs := by simp [ioStore]
@[simp] lemma io_regs (s : Register → List Bool) (out saved : List Bool) : regs (ioStore s out saved)=regs s := by
  funext k;cases k <;> rfl
lemma io_work (s : Register → List Bool) (out saved : List Bool) (hw : WorkEmpty s) : WorkEmpty (ioStore s out saved) := by
  simpa [WorkEmpty,ioStore] using hw
@[simp] lemma emitted_io (s : Register → List Bool) (out saved xs : List Bool) :
    emitted (ioStore s out saved) xs=ioStore s xs saved := by simp [emitted]
@[simp] lemma io_cost (s : Register → List Bool) (out saved : List Bool) (jobs : List (Job StackGate.Register)) :
    emitCost (ioStore s out saved) jobs=emitCost s jobs := by
  unfold emitCost
  congr 1
  apply List.map_congr_left
  intro job hj
  cases job <;> simp [emitJobCost]

lemma save_run (initialSign : Bool) (block : Block) (s : Register → List Bool) (xs ys : List Bool) :
    Run (program initialSign) (2*xs.length+1) (cfg (.saveOutput block) (ioStore s xs ys))
      (cfg (.emit block 0) (ioStore s [] (xs.reverse++ys))) := by
  induction xs generalizing ys with
  | nil => apply Run.one;simp [Step,successors,program,Macros.compile,Macros.code,macroCode,cfg]
  | cons b bs ih =>
    have h1 : Step (program initialSign) (cfg (.saveOutput block) (ioStore s (b::bs) ys))
        (cfg (.saveOutputBit block b) (ioStore s bs ys)) := by
      cases b <;> simp [Step,successors,program,Macros.compile,Macros.code,macroCode,cfg]
    have h2 : Step (program initialSign) (cfg (.saveOutputBit block b) (ioStore s bs ys))
        (cfg (.saveOutput block) (ioStore s bs (b::ys))) := by
      simp [Step,successors,program,Macros.compile,Macros.code,macroCode,cfg]
    have hh := Run.succ h1 (Run.succ h2 (ih (b::ys)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

lemma restore_run (initialSign : Bool) (block : Block) (s : Register → List Bool) (xs ys : List Bool) :
    Run (program initialSign) (2*xs.length+1) (cfg (.restoreOutput block) (ioStore s ys xs))
      (cfg (afterBlock block) (ioStore s (xs.reverse++ys) [])) := by
  induction xs generalizing ys with
  | nil => apply Run.one;cases block <;> simp [Step,successors,program,Macros.compile,Macros.code,macroCode,cfg,afterBlock]
  | cons b bs ih =>
    have h1 : Step (program initialSign) (cfg (.restoreOutput block) (ioStore s ys (b::bs)))
        (cfg (.restoreOutputBit block b) (ioStore s ys bs)) := by
      cases b <;> simp [Step,successors,program,Macros.compile,Macros.code,macroCode,cfg]
    have h2 : Step (program initialSign) (cfg (.restoreOutputBit block b) (ioStore s ys bs))
        (cfg (.restoreOutput block) (ioStore s (b::ys) bs)) := by
      simp [Step,successors,program,Macros.compile,Macros.code,macroCode,cfg]
    have hh := Run.succ h1 (Run.succ h2 (ih (b::ys)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

def blockData (s : Register → List Bool) (block : Block) : List Bool :=
  dataFields ((blockSpecs block).map (fieldValue (regs s)))

/-- Append a complete clause block in the correct forward order, paying for
both traversals of the existing output instead of treating append as free. -/
theorem append_block (initialSign : Bool) (block : Block) (s : Register → List Bool)
    (hw : WorkEmpty s) (hs : s .savedOutput=[]) :
    Run (program initialSign) (4*(s .output).length+emitCost s (blockJobs block)+3)
      (cfg (.saveOutput block) s) (cfg (afterBlock block) (emitted s (s .output++blockData s block))) := by
  have h1 := save_run initialSign block s (s .output) []
  have he : ioStore s (s .output) []=s := by simp [ioStore,← hs]
  rw [he] at h1
  simp only [List.append_nil] at h1
  have h2 := emit_block initialSign block (ioStore s [] (s .output).reverse) (io_work s _ _ hw)
  simp only [io_cost,io_regs,io_output,List.append_nil,emitted_io] at h2
  have h3 := restore_run initialSign block s (s .output).reverse (blockData s block)
  simp only [List.length_reverse,List.reverse_reverse] at h3
  have hh := h1.trans (h2.trans h3)
  have he' : ioStore s (s .output++blockData s block) []=emitted s (s .output++blockData s block) := by
    funext k;cases k <;> simp [ioStore,emitted,hs]
  rw [he'] at hh
  convert hh using 1 <;> omega

end BalancedAssortments.NPCNF.StackChain
