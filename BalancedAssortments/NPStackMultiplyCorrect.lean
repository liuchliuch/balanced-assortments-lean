import BalancedAssortments.NPStackMultiply

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary

def multiplyStep (factor acc : List Bool) (b : Bool) : List Bool :=
  if b then (addCarry factor (false::acc) false).1 else false::acc

lemma multiplyLoopResult_fold (flag : Bool) (pending factor acc : List Bool) :
    (multiplyLoopResult flag pending factor acc).2=pending.foldl (multiplyStep factor) acc := by
  induction pending generalizing flag acc with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [multiplyLoopResult,multiplyStep,ih]

lemma mulBits_fold (xs factor : List Bool) :
    (mulBits xs factor).1=xs.foldr (fun b acc => multiplyStep factor acc b) [] := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [mulBits,multiplyStep,ih]

lemma multiplyLoopResult_refines (flag : Bool) (xs factor : List Bool) :
    (multiplyLoopResult flag xs.reverse factor []).2=(mulBits xs factor).1 := by
  rw [multiplyLoopResult_fold,List.foldl_reverse,mulBits_fold]

def multiplicationInput (xs factor : List Bool) : Config MulStack MulState :=
  ⟨.initial .read,mulStacks xs [] factor [] [] []⟩

def multiplicationOutput (factor result : List Bool) : Config MulStack MulState :=
  ⟨.done,fun k => match k with | .factor => factor | .output => result | _ => []⟩

theorem multiplication_initialize (xs factor : List Bool) :
    Run multiplyProgram (2*xs.length+2) (multiplicationInput xs factor)
      (loopConfig (.read false) false xs.reverse factor []) := by
  let reversed := loopConfig (.initial .done) false xs.reverse factor []
  have h := (reverse_run xs []).relocate_exact initialStack MulState.initial initialStack_injective initial_code
    (c' := multiplicationInput xs factor) (d' := reversed)
    (by constructor; rfl; intro k; cases k <;> rfl)
    (by constructor; rfl; intro k; cases k <;> simp [reversed,loopConfig,mulStacks,initialStack,reverseConfig,twoStacks])
    (by intro k hk; have h1:=hk false;have h2:=hk true;cases k <;>
        simp_all [initialStack,multiplicationInput,reversed,loopConfig,mulStacks])
  have hs : Step multiplyProgram reversed (loopConfig (.read false) false xs.reverse factor []) := by
    simp [Step,successors,multiplyProgram,reversed,loopConfig]
  convert h.trans (Run.one hs) using 1 <;> omega

theorem multiplication_finish (flag : Bool) (factor acc : List Bool) :
    Run multiplyProgram (4*acc.length+5) (loopConfig (.read flag) flag [] factor acc)
      (multiplicationOutput factor acc) := by
  let firstStart := loopConfig (.finalFirst flag .read) flag [] factor acc
  let firstEnd : Config MulStack MulState :=
    ⟨.finalFirst flag .done,Function.update (multiplicationOutput factor []).stk .finalScratch acc.reverse⟩
  let secondStart : Config MulStack MulState := ⟨.finalSecond .read,firstEnd.stk⟩
  let secondEnd : Config MulStack MulState := ⟨.finalSecond .done,(multiplicationOutput factor acc).stk⟩
  have hpop : Step multiplyProgram (loopConfig (.read flag) flag [] factor acc) firstStart := by
    simp [Step,successors,multiplyProgram,firstStart,loopConfig,mulStacks]
  have hfirst := (reverse_run acc []).relocate_exact (finalFirstStack flag) (MulState.finalFirst flag)
    (finalFirstStack_injective flag) (finalFirst_code flag) (c' := firstStart) (d' := firstEnd)
    (by constructor; rfl; intro k; cases flag <;> cases k <;> rfl)
    (by constructor; rfl; intro k; cases flag <;> cases k <;>
        simp [firstEnd,finalFirstStack,currentAccumulator,multiplicationOutput,reverseConfig,twoStacks])
    (by intro k hk;have h1:=hk false;have h2:=hk true;cases flag <;> cases k <;>
        simp_all [finalFirstStack,currentAccumulator,firstStart,firstEnd,multiplicationOutput,loopConfig,mulStacks])
  have hcall : Step multiplyProgram firstEnd secondStart := by
    simp [Step,successors,multiplyProgram,firstEnd,secondStart]
  have hsecond := (reverse_run acc.reverse []).relocate_exact finalSecondStack MulState.finalSecond
    finalSecondStack_injective finalSecond_code (c' := secondStart) (d' := secondEnd)
    (by constructor; rfl; intro k; cases k <;> simp [secondStart,firstEnd,finalSecondStack,multiplicationOutput,reverseConfig,twoStacks])
    (by constructor; rfl; intro k; cases k <;> simp [secondEnd,finalSecondStack,multiplicationOutput,reverseConfig,twoStacks])
    (by intro k hk;have h1:=hk false;have h2:=hk true;cases k <;>
        simp_all [finalSecondStack,secondStart,secondEnd,firstEnd,multiplicationOutput])
  have hreturn : Step multiplyProgram secondEnd (multiplicationOutput factor acc) := by
    simp [Step,successors,multiplyProgram,secondEnd,multiplicationOutput]
  have hh := Run.succ hpop (hfirst.trans (Run.succ hcall (hsecond.trans (Run.one hreturn))))
  simp only [List.length_reverse] at hh
  convert hh using 1 <;> omega

def multiplicationBudget (n m : ℕ) : ℕ :=
  n*(10*(2*n+m)+12)+2*n+4*(2*n+m)+7

/-- Complete finite-stack operational multiplication: exact old bit-list
output, preserved factor and polynomial number of concrete transitions. -/
theorem multiplication_run (xs factor : List Bool) :
    ∃ t ≤ multiplicationBudget xs.length factor.length,
      Run multiplyProgram t (multiplicationInput xs factor)
        (multiplicationOutput factor (mulBits xs factor).1) := by
  have hi := multiplication_initialize xs factor
  obtain ⟨t,ht,hr,hw⟩ := multiply_loop_run false xs.reverse factor [] (2*xs.length+factor.length) (by simp;omega)
  rw [multiplyLoopResult_refines] at hr hw
  have hf := multiplication_finish (multiplyLoopResult false xs.reverse factor []).1 factor (mulBits xs factor).1
  refine ⟨(2*xs.length+2)+t+(4*(mulBits xs factor).1.length+5),?_,(hi.trans hr).trans hf⟩
  simp only [List.length_reverse] at ht
  unfold multiplicationBudget
  omega

theorem multiplication_run_value (xs factor : List Bool) :
    ∃ t ≤ multiplicationBudget xs.length factor.length,∃ result,
      Run multiplyProgram t (multiplicationInput xs factor) (multiplicationOutput factor result) ∧
      value result=value xs*value factor := by
  obtain ⟨t,ht,hr⟩ := multiplication_run xs factor
  exact ⟨t,ht,(mulBits xs factor).1,hr,mulBits_value xs factor⟩

def finiteMultiply : FiniteProgram where
  K := MulStack
  Q := MulState
  program := multiplyProgram

end BalancedAssortments.NPStack
