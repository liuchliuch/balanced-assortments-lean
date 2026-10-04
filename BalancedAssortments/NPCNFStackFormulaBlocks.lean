import BalancedAssortments.NPCNFStackFormulaProgram
import BalancedAssortments.NPStackFiniteExec

namespace BalancedAssortments.NPCNF.StackFormula
open NPStack NPStack.Macros StackChain

lemma outer_run {t : ℕ} {q q' : Label Main} {s s' : Register → List Bool}
    (h : Run (Macros.compile macroCode .readHeader StackChain.Register.input StackChain.Register.output) t ⟨q,s⟩ ⟨q',s'⟩) :
    Run program t ⟨.outer q,s⟩ ⟨.outer q',s'⟩ := by
  exact h.relocate_exact id State.outer (fun _ _ h=>h) outer_extends
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩ (fun k hk=>False.elim (hk k rfl))

lemma chain_run_embedded {t : ℕ} {q q' : Label StackChain.State} {s s' : Register → List Bool}
    (h : Run (StackChain.program false) t ⟨q,s⟩ ⟨q',s'⟩) :
    Run program t ⟨.chain q,s⟩ ⟨.chain q',s'⟩ := by
  exact h.relocate_exact id State.chain (fun _ _ h=>h) chain_extends
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩ (fun k hk=>False.elim (hk k rfl))

def afterConstant : ConstantBlock → Main | .emptyClause => .readHeader | .formulaEnd => .accept

lemma save_run (block : ConstantBlock) (s : Register → List Bool) (xs ys : List Bool) :
    Run program (2*xs.length+1) (cfg (.saveOutput block) (ioStore s xs ys))
      (cfg (.emitConstant block 0) (ioStore s [] (xs.reverse++ys))) := by
  induction xs generalizing ys with
  | nil => apply Run.one;simp [Step,successors,program,code,Macros.code,macroCode,cfg,Instr.rename]
  | cons b bs ih =>
    have h1 : Step program (cfg (.saveOutput block) (ioStore s (b::bs) ys))
        (cfg (.saveOutputBit block b) (ioStore s bs ys)) := by
      cases b <;> simp [Step,successors,program,code,Macros.code,macroCode,cfg,Instr.rename]
    have h2 : Step program (cfg (.saveOutputBit block b) (ioStore s bs ys))
        (cfg (.saveOutput block) (ioStore s bs (b::ys))) := by
      simp [Step,successors,program,code,Macros.code,macroCode,cfg,Instr.rename]
    have hh := Run.succ h1 (Run.succ h2 (ih (b::ys)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

lemma restore_run (block : ConstantBlock) (s : Register → List Bool) (xs ys : List Bool) :
    Run program (2*xs.length+1) (cfg (.restoreOutput block) (ioStore s ys xs))
      (cfg (afterConstant block) (ioStore s (xs.reverse++ys) [])) := by
  induction xs generalizing ys with
  | nil => apply Run.one;cases block <;> simp [Step,successors,program,code,Macros.code,macroCode,cfg,afterConstant,Instr.rename]
  | cons b bs ih =>
    have h1 : Step program (cfg (.restoreOutput block) (ioStore s ys (b::bs)))
        (cfg (.restoreOutputBit block b) (ioStore s ys bs)) := by
      cases b <;> simp [Step,successors,program,code,Macros.code,macroCode,cfg,Instr.rename]
    have h2 : Step program (cfg (.restoreOutputBit block b) (ioStore s ys bs))
        (cfg (.restoreOutput block) (ioStore s (b::ys) bs)) := by
      simp [Step,successors,program,code,Macros.code,macroCode,cfg,Instr.rename]
    have hh := Run.succ h1 (Run.succ h2 (ih (b::ys)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

lemma emit_constant (block : ConstantBlock) (s : Register → List Bool) (out saved : List Bool) :
    Run program ((blockBits block).length+1) (cfg (.emitConstant block 0) (ioStore s out saved))
      (cfg (.restoreOutput block) (ioStore s (blockBits block++out) saved)) := by
  apply firstRun_sound
  cases block <;> simp [firstRun,successors,program,code,Macros.code,macroCode,cfg,Instr.rename,
    blockBits,nextConstant]

/-- Exact bounded append of the empty clause or final formula marker. -/
lemma append_constant (block : ConstantBlock) (s : Register → List Bool) (hs : s .savedOutput=[]) :
    Run program (4*(s .output).length+(blockBits block).length+3)
      (cfg (.saveOutput block) s) (cfg (afterConstant block) (emitted s (s .output++blockBits block))) := by
  have h1 := save_run block s (s .output) []
  have he : ioStore s (s .output) []=s := by simp [ioStore,← hs]
  rw [he] at h1
  simp only [List.append_nil] at h1
  have h2 := emit_constant block s [] (s .output).reverse
  simp only [List.append_nil] at h2
  have h3 := restore_run block s (s .output).reverse (blockBits block)
  simp only [List.length_reverse,List.reverse_reverse] at h3
  have hh := h1.trans (h2.trans h3)
  have he' : ioStore s (s .output++blockBits block) []=emitted s (s .output++blockBits block) := by
    funext k;cases k <;> simp [ioStore,emitted,hs]
  rw [he'] at hh
  convert hh using 1 <;> omega

end BalancedAssortments.NPCNF.StackFormula
