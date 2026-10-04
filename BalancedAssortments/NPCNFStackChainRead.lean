import BalancedAssortments.NPCNFStackChainReset

namespace BalancedAssortments.NPCNF.StackChain
open NPStack NPStack.Macros StackTemplate StackGate NPStackFields Encoding

lemma read_end (initialSign sa : Bool) (rest a z out allocated : List Bool) :
    Run (program initialSign) 5
      (cfg (.readSign sa) (store (false::rest) a [] z out allocated))
      (cfg (.saveOutput (.unit sa)) (store rest a [] z out allocated)) := by
  let s := store (false::rest) a [] z out allocated
  have hr := taggedRead_call macroCode (.readSign initialSign) .input .output
    (q := .readSign sa) (yes := .inspectSign sa) (no := .reject) rfl
    (by decide) (by decide) (by decide) s [] rest (by rfl) (by rfl)
  have hs : Function.update (Function.update s .input rest) .tag ([]++s .tag)=store rest a [] z out allocated := by
    funext k;cases k <;> simp [s,store]
  rw [hs] at hr
  have hstep : Step (program initialSign) (cfg (.inspectSign sa) (store rest a [] z out allocated))
      (cfg (.saveOutput (.unit sa)) (store rest a [] z out allocated)) := by
    simp [Step,successors,program,Macros.compile,Macros.code,macroCode,cfg,store]
  exact hr.trans (Run.one hstep)

lemma read_literal (initialSign sa sb : Bool) (rest a b z out allocated : List Bool) :
    Run (program initialSign) (5*b.length+15)
      (cfg (.readSign sa) (store (tagBits [sb]++false::(tagBits b++false::rest)) a [] z out allocated))
      (cfg (.saveOutput (.gate sa sb)) (store rest a b z out allocated)) := by
  let s0 := store (tagBits [sb]++false::(tagBits b++false::rest)) a [] z out allocated
  let s1 := Function.update (store (tagBits b++false::rest) a [] z out allocated) .tag [sb]
  let s2 := store (tagBits b++false::rest) a [] z out allocated
  have h1 := taggedRead_call macroCode (.readSign initialSign) .input .output
    (q := .readSign sa) (yes := .inspectSign sa) (no := .reject) rfl
    (by decide) (by decide) (by decide) s0 [sb] (tagBits b++false::rest) rfl rfl
  have he1 : Function.update (Function.update s0 .input (tagBits b++false::rest)) .tag ([sb]++s0 .tag)=s1 := by
    funext k;cases k <;> simp [s0,s1,store]
  rw [he1] at h1
  have h2 : Step (program initialSign) (cfg (.inspectSign sa) s1) (cfg (.checkSignEnd sa sb) s2) := by
    cases sb <;> simp [Step,successors,program,Macros.compile,Macros.code,macroCode,cfg,s1,s2,store]
    all_goals funext k;cases k <;> simp [store]
  have h3 : Step (program initialSign) (cfg (.checkSignEnd sa sb) s2) (cfg (.readRight sa sb) s2) := by
    simp [Step,successors,program,Macros.compile,Macros.code,macroCode,cfg,s2,store]
  have h4 := taggedRead_call macroCode (.readSign initialSign) .input .output
    (q := .readRight sa sb) (yes := .saveOutput (.gate sa sb)) (no := .reject) rfl
    (by decide) (by decide) (by decide) s2 b rest rfl rfl
  have he4 : Function.update (Function.update s2 .input rest) .right (b++s2 .right)=store rest a b z out allocated := by
    funext k;cases k <;> simp [s2,store]
  rw [he4] at h4
  have hh := h1.trans (Run.succ h2 (Run.succ h3 h4))
  convert hh using 1 <;> simp <;> omega

end BalancedAssortments.NPCNF.StackChain
