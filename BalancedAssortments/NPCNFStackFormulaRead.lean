import BalancedAssortments.NPCNFStackFormulaBlocks

namespace BalancedAssortments.NPCNF.StackFormula
open NPStack NPStack.Macros StackChain NPStackFields Encoding

lemma header_run (flag : Bool) (rest z out allocated : List Bool) :
    Run program 11 (cfg .readHeader (store (tagBits [flag]++false::rest) [] [] z out allocated))
      (cfg (if flag then .readFirstSign else .checkInputEnd) (store rest [] [] z out allocated)) := by
  let s := store (tagBits [flag]++false::rest) [] [] z out allocated
  let s' := Function.update (store rest [] [] z out allocated) .tag [flag]
  have hread := taggedRead_call macroCode .readHeader .input .output
    (q := .readHeader) (yes := .inspectHeader) (no := .reject) rfl
    (by decide) (by decide) (by decide) s [flag] rest rfl rfl
  have he : Function.update (Function.update s .input rest) .tag ([flag]++s .tag)=s' := by
    funext k;cases k <;> simp [s,s',store]
  rw [he] at hread
  have h1 := outer_run hread
  have h2 : Run program 2 (cfg .inspectHeader s')
      (cfg (if flag then .readFirstSign else .checkInputEnd) (store rest [] [] z out allocated)) := by
    apply firstRun_sound
    cases flag <;> simp [firstRun,successors,program,code,Macros.code,macroCode,cfg,Instr.rename,s',store]
    all_goals funext k;cases k <;> simp [store]
  exact h1.trans h2

lemma first_empty (rest z out allocated : List Bool) :
    Run program 5 (cfg .readFirstSign (store (false::rest) [] [] z out allocated))
      (cfg (.saveOutput .emptyClause) (store rest [] [] z out allocated)) := by
  let s := store (false::rest) [] [] z out allocated
  have hread := taggedRead_call macroCode .readHeader .input .output
    (q := .readFirstSign) (yes := .inspectFirstSign) (no := .reject) rfl
    (by decide) (by decide) (by decide) s [] rest rfl rfl
  have he : Function.update (Function.update s .input rest) .tag ([]++s .tag)=store rest [] [] z out allocated := by
    funext k;cases k <;> simp [s,store]
  rw [he] at hread
  have h1 := outer_run hread
  have h2 : Step program (cfg .inspectFirstSign (store rest [] [] z out allocated))
      (cfg (.saveOutput .emptyClause) (store rest [] [] z out allocated)) := by
    simp [Step,successors,program,code,Macros.code,macroCode,cfg,Instr.rename,store]
  exact h1.trans (Run.one h2)

lemma first_literal (sign : Bool) (rest a z out allocated : List Bool) :
    Run program (5*a.length+15)
      (cfg .readFirstSign (store (tagBits [sign]++false::(tagBits a++false::rest)) [] [] z out allocated))
      (cfg (.invoke sign) (store rest a [] z out allocated)) := by
  let s0 := store (tagBits [sign]++false::(tagBits a++false::rest)) [] [] z out allocated
  let s1 := Function.update (store (tagBits a++false::rest) [] [] z out allocated) .tag [sign]
  let s2 := store (tagBits a++false::rest) [] [] z out allocated
  have hr := taggedRead_call macroCode .readHeader .input .output
    (q := .readFirstSign) (yes := .inspectFirstSign) (no := .reject) rfl
    (by decide) (by decide) (by decide) s0 [sign] (tagBits a++false::rest) rfl rfl
  have he1 : Function.update (Function.update s0 .input (tagBits a++false::rest)) .tag ([sign]++s0 .tag)=s1 := by
    funext k;cases k <;> simp [s0,s1,store]
  rw [he1] at hr
  have h1 := outer_run hr
  have h2 : Run program 2 (cfg .inspectFirstSign s1) (cfg (.readFirstLabel sign) s2) := by
    apply firstRun_sound
    cases sign <;> simp [firstRun,successors,program,code,Macros.code,macroCode,cfg,Instr.rename,s1,s2,store]
    all_goals funext k;cases k <;> simp [store]
  have hr' := taggedRead_call macroCode .readHeader .input .output
    (q := .readFirstLabel sign) (yes := .invoke sign) (no := .reject) rfl
    (by decide) (by decide) (by decide) s2 a rest rfl rfl
  have he2 : Function.update (Function.update s2 .input rest) .left (a++s2 .left)=store rest a [] z out allocated := by
    funext k;cases k <;> simp [s2,store]
  rw [he2] at hr'
  have h3 := outer_run hr'
  have hh := h1.trans (h2.trans h3)
  convert hh using 1 <;> simp <;> omega

lemma invoke_chain (next : List Bool) (a : BitLiteral) (rest : BitClause) (suffix out allocated : List Bool) :
    Run program (chainCost next a rest out+2)
      (cfg (.invoke a.positive) (store (dataFields (clauseFields rest)++suffix) a.labelBits [] next out allocated))
      (cfg .clearLeft (store suffix (chainLast next a rest) [] (bitChain next a rest).1.2
        (out++bodyData (bitChain next a rest).1.1) (chainAllocated next rest++allocated))) := by
  have hs := chain_run_embedded (chain_run false next a rest suffix out allocated)
  have h1 : Step program
      (cfg (.invoke a.positive) (store (dataFields (clauseFields rest)++suffix) a.labelBits [] next out allocated))
      ⟨.chain (.main (.readSign a.positive)),store (dataFields (clauseFields rest)++suffix) a.labelBits [] next out allocated⟩ := by
    simp [Step,successors,program,code,cfg]
  have h2 : Step program
      ⟨.chain (.main .accept),store suffix (chainLast next a rest) [] (bitChain next a rest).1.2
        (out++bodyData (bitChain next a rest).1.1) (chainAllocated next rest++allocated)⟩
      (cfg .clearLeft (store suffix (chainLast next a rest) [] (bitChain next a rest).1.2
        (out++bodyData (bitChain next a rest).1.1) (chainAllocated next rest++allocated))) := by
    simp [Step,successors,program,code,cfg]
  convert Run.succ h1 (hs.trans (Run.one h2)) using 1 <;> omega

lemma clear_left (i a z out allocated : List Bool) :
    Run program (a.length+1) (cfg .clearLeft (store i a [] z out allocated))
      (cfg .readHeader (store i [] [] z out allocated)) := by
  have hr := clear_loop macroCode .readHeader .input .output .clearLeft .readHeader .left rfl (store i a [] z out allocated)
  have h := outer_run hr
  have he : Function.update (store i a [] z out allocated) .left []=store i [] [] z out allocated := by
    funext k;cases k <;> simp [store]
  rw [he] at h
  exact h

end BalancedAssortments.NPCNF.StackFormula
