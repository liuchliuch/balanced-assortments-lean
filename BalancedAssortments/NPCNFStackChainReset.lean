import BalancedAssortments.NPCNFStackChainAppend
import BalancedAssortments.NPStackMacroLoops
import BalancedAssortments.NPStackMacroData

namespace BalancedAssortments.NPCNF.StackChain
open NPStack NPStack.Macros StackTemplate StackGate NPStackFields ComplexityTimeBinary

def store (input left right fresh output allocated : List Bool) : Register → List Bool
  | .input => input | .left => left | .right => right | .fresh => fresh
  | .output => output | .allocated => allocated | _ => []

lemma store_work (i a b z o c : List Bool) : WorkEmpty (store i a b z o c) := by simp [WorkEmpty,store]

def nextBits (z : List Bool) : List Bool := (addCarry z [true] false).1

def resetCost (a b z : List Bool) : ℕ :=
  a.length+b.length+15*z.length+5*max z.length 1+6*(nextBits z).length+29

/-- After emitting one gate, preserve the old fresh variable as the next
chain literal, record its catalogue field, and increment using actual binary
addition. All temporary registers are restored to empty. -/
theorem reset_after_gate (initialSign : Bool) (i a b z o c : List Bool) :
    Run (program initialSign) (resetCost a b z)
      (cfg .clearLeft (store i a b z o c))
      (cfg (.readSign true) (store i z [] (nextBits z) o (tagBits z++false::c))) := by
  let s0 := store i a b z o c
  let s1 := Function.update s0 .left []
  let s2 := Function.update s1 .left z
  let s3 := Function.update s2 .temporary z
  let s4 := Function.update (Function.update s3 .temporary []) .allocated (tagBits z++false::c)
  let s5 := Function.update s4 .right []
  let s6 := Function.update s5 .one [true]
  let s7 := writes s6 [(.fresh,[]),(.one,[]),(.nextFresh,nextBits z)]
  let s8 := Function.update s7 .fresh (nextBits z)
  let s9 := Function.update s8 .nextFresh []
  have h1 := clear_loop macroCode (.readSign initialSign) .input .output .clearLeft .copyFreshLeft .left rfl s0
  have h2 := copy_call_store macroCode (.readSign initialSign) .input .output
    (q := .copyFreshLeft) (next := .copyFreshCatalog) rfl (by decide) (by decide) (by decide) s1 (by simp [s1,s0,store])
  have h3 := copy_call_store macroCode (.readSign initialSign) .input .output
    (q := .copyFreshCatalog) (next := .emitFreshCatalog) rfl (by decide) (by decide) (by decide) s2 (by simp [s2,s1,s0,store])
  have h4 := taggedEmit_call macroCode (.readSign initialSign) .input .output
    (q := .emitFreshCatalog) (next := .clearRight) rfl (by decide) (by decide) (by decide) s3 (by simp [s3,s2,s1,s0,store])
  have h5 := clear_loop macroCode (.readSign initialSign) .input .output .clearRight .makeOne .right rfl s4
  have h6 : Step (program initialSign) (cfg .makeOne s5) (cfg .increment s6) := by
    simp [Step,successors,program,Macros.compile,Macros.code,macroCode,cfg,s6,s5,s4,s3,s2,s1,s0,store]
  have hadd := add_call macroCode (.readSign initialSign) .input .output
    (q := .increment) (next := .installFresh) rfl
    (by intro x y h;cases x <;> cases y <;> simp_all [addMap]) s6
    (by simp [s6,s5,s4,s3,s2,s1,s0,store]) (by simp [s6,s5,s4,s3,s2,s1,s0,store])
  have h8 := copy_call_store macroCode (.readSign initialSign) .input .output
    (q := .installFresh) (next := .clearNextFresh) rfl (by decide) (by decide) (by decide) s7
    (by simp [s7,writes,s6,s5,s4,s3,s2,s1,s0,store])
  have h9 := clear_loop macroCode (.readSign initialSign) .input .output .clearNextFresh (.readSign true) .nextFresh rfl s8
  have h1' : Run (program initialSign) (a.length+1) (cfg .clearLeft s0) (cfg .copyFreshLeft s1) := h1
  have h2' : Run (program initialSign) (5*z.length+4) (cfg .copyFreshLeft s1) (cfg .copyFreshCatalog s2) := by
    simpa [s9,s8,s7,writes,s6,s5,s4,s3,s2,s1,s0,store,cfg,program,nextBits] using h2
  have h3' : Run (program initialSign) (5*z.length+4) (cfg .copyFreshCatalog s2) (cfg .emitFreshCatalog s3) := by
    simpa [s9,s8,s7,writes,s6,s5,s4,s3,s2,s1,s0,store,cfg,program,nextBits] using h3
  have h4' : Run (program initialSign) (5*z.length+5) (cfg .emitFreshCatalog s3) (cfg .clearRight s4) := by
    simpa [s9,s8,s7,writes,s6,s5,s4,s3,s2,s1,s0,store,cfg,program,nextBits] using h4
  have h5' : Run (program initialSign) (b.length+1) (cfg .clearRight s4) (cfg .makeOne s5) := by
    simpa [s9,s8,s7,writes,s6,s5,s4,s3,s2,s1,s0,store,cfg,program,nextBits] using h5
  have h7' : Run (program initialSign) (5*max z.length 1+8) (cfg .increment s6) (cfg .installFresh s7) := by
    simpa [s9,s8,s7,writes,s6,s5,s4,s3,s2,s1,s0,store,cfg,program,nextBits] using hadd
  have h8' : Run (program initialSign) (5*(nextBits z).length+4) (cfg .installFresh s7) (cfg .clearNextFresh s8) := by
    simpa [s9,s8,s7,writes,s6,s5,s4,s3,s2,s1,s0,store,cfg,program,nextBits] using h8
  have h9' : Run (program initialSign) ((nextBits z).length+1) (cfg .clearNextFresh s8) (cfg (.readSign true) s9) := by
    simpa [s9,s8,s7,writes,s6,s5,s4,s3,s2,s1,s0,store,cfg,program,nextBits] using h9
  have hfinal : s9=store i z [] (nextBits z) o (tagBits z++false::c) := by
    funext k;cases k <;> simp [s9,s8,s7,writes,s6,s5,s4,s3,s2,s1,s0,store]
  have hh := h1'.trans (h2'.trans (h3'.trans (h4'.trans (h5'.trans
    ((Run.one h6).trans (h7'.trans (h8'.trans h9')))))))
  rw [hfinal] at hh
  convert hh using 1 <;> dsimp only [resetCost] <;> omega

end BalancedAssortments.NPCNF.StackChain
