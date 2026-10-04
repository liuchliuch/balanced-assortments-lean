import BalancedAssortments.NPStackAdd
import BalancedAssortments.NPStackCopy
import BalancedAssortments.NPStackEmbedding

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary

inductive MulStack
  | input | pending | factor | copyScratch | copyOut | accA | accB | addScratch | finalScratch | output
  deriving DecidableEq, Fintype
inductive MulState
  | initial (q : ReverseState)
  | read (flag : Bool)
  | shift (flag bit : Bool)
  | copy (flag : Bool) (q : CopyState)
  | add (flag : Bool) (q : AddState)
  | finalFirst (flag : Bool) (q : ReverseState)
  | finalSecond (q : ReverseState)
  | done
  deriving DecidableEq, Fintype

def currentAccumulator (flag : Bool) : MulStack := if flag then .accB else .accA

def initialStack : Bool → MulStack | false => .input | true => .pending

def copyStack : CopyStack → MulStack
  | .source => .factor | .scratch => .copyScratch | .target => .copyOut

def additionStack (flag : Bool) : AddStack → MulStack
  | .left => .copyOut | .right => currentAccumulator flag
  | .scratch => .addScratch | .output => currentAccumulator (!flag)

def finalFirstStack (flag : Bool) : Bool → MulStack
  | false => currentAccumulator flag | true => .finalScratch

def finalSecondStack : Bool → MulStack | false => .finalScratch | true => .output

/-- Schoolbook multiplication assembled from genuine finite copy, ripple-add
and reversal bytecode. All control flags and carried values are finite. -/
def multiplyProgram : Program MulStack MulState where
  code
    | .initial .done => .jump (.read false)
    | .initial q => (reverseProgram.code q).rename initialStack MulState.initial
    | .read flag => .pop .pending (.finalFirst flag .read) (.shift flag false) (.shift flag true)
    | .shift flag bit => .push (currentAccumulator flag) false
        (if bit then .copy flag .readSource else .read flag)
    | .copy flag .done => .jump (.add flag (.readX false))
    | .copy flag q => (copyProgram.code q).rename copyStack (MulState.copy flag)
    | .add flag .done => .jump (.read (!flag))
    | .add flag q => (addProgram.code q).rename (additionStack flag) (MulState.add flag)
    | .finalFirst flag .done => .jump (.finalSecond .read)
    | .finalFirst flag q => (reverseProgram.code q).rename (finalFirstStack flag) (MulState.finalFirst flag)
    | .finalSecond .done => .jump .done
    | .finalSecond q => (reverseProgram.code q).rename finalSecondStack MulState.finalSecond
    | .done => .halt true
  start := .initial .read
  inputStack := .input
  outputStack := .output

lemma initialStack_injective : Function.Injective initialStack := by intro a b h; cases a <;> cases b <;> simp_all [initialStack]
lemma copyStack_injective : Function.Injective copyStack := by intro a b h; cases a <;> cases b <;> simp_all [copyStack]
lemma additionStack_injective (flag : Bool) : Function.Injective (additionStack flag) := by
  intro a b h
  cases flag <;> cases a <;> cases b <;> simp_all [additionStack,currentAccumulator]
lemma finalFirstStack_injective (flag : Bool) : Function.Injective (finalFirstStack flag) := by
  intro a b h
  cases flag <;> cases a <;> cases b <;> simp_all [finalFirstStack,currentAccumulator]
lemma finalSecondStack_injective : Function.Injective finalSecondStack := by intro a b h; cases a <;> cases b <;> simp_all [finalSecondStack]

lemma initial_code : CodeExtends reverseProgram multiplyProgram initialStack MulState.initial := by
  intro q h
  cases q <;> simp [multiplyProgram,reverseProgram]
  exact False.elim (h true rfl)
lemma copy_code (flag : Bool) : CodeExtends copyProgram multiplyProgram copyStack (MulState.copy flag) := by
  intro q h
  cases q <;> simp [multiplyProgram,copyProgram]
  exact False.elim (h true rfl)
lemma addition_code (flag : Bool) : CodeExtends addProgram multiplyProgram (additionStack flag) (MulState.add flag) := by
  intro q h
  cases q <;> simp [multiplyProgram,addProgram]
  exact False.elim (h true rfl)
lemma finalFirst_code (flag : Bool) : CodeExtends reverseProgram multiplyProgram (finalFirstStack flag) (MulState.finalFirst flag) := by
  intro q h
  cases q <;> simp [multiplyProgram,reverseProgram]
  exact False.elim (h true rfl)
lemma finalSecond_code : CodeExtends reverseProgram multiplyProgram finalSecondStack MulState.finalSecond := by
  intro q h
  cases q <;> simp [multiplyProgram,reverseProgram]
  exact False.elim (h true rfl)

def mulStacks (input pending factor accA accB copyOut : List Bool) : MulStack → List Bool
  | .input => input | .pending => pending | .factor => factor | .accA => accA | .accB => accB
  | .copyOut => copyOut | _ => []

def loopConfig (q : MulState) (flag : Bool) (pending factor acc : List Bool) : Config MulStack MulState :=
  ⟨q,mulStacks [] pending factor (if flag then [] else acc) (if flag then acc else []) []⟩

/-- One full multiplication iteration for a set bit, including actual copy and
actual ripple-add subroutine calls and both return jumps. -/
theorem multiply_true_iteration (flag : Bool) (pending factor acc : List Bool) :
    Run multiplyProgram (5*factor.length+5*max factor.length (acc.length+1)+12)
      (loopConfig (.read flag) flag (true::pending) factor acc)
      (loopConfig (.read (!flag)) (!flag) pending factor (addCarry factor (false::acc) false).1) := by
  let shifted := loopConfig (.copy flag .readSource) flag pending factor (false::acc)
  let copied : Config MulStack MulState :=
    ⟨.copy flag .done,mulStacks [] pending factor (if flag then [] else false::acc) (if flag then false::acc else []) factor⟩
  have hpop : Step multiplyProgram (loopConfig (.read flag) flag (true::pending) factor acc)
      (loopConfig (.shift flag true) flag pending factor acc) := by
    cases flag <;> simp [Step,successors,multiplyProgram,loopConfig,mulStacks] <;> funext k <;> cases k <;> simp [Function.update,mulStacks]
  have hshift : Step multiplyProgram (loopConfig (.shift flag true) flag pending factor acc) shifted := by
    cases flag <;> simp [Step,successors,multiplyProgram,shifted,loopConfig,mulStacks,currentAccumulator] <;> funext k <;> cases k <;> simp [Function.update,mulStacks]
  have hcopy := (copy_run factor []).relocate_exact copyStack (MulState.copy flag) copyStack_injective (copy_code flag)
    (c' := shifted) (d' := copied)
    (by constructor; rfl; intro k; cases flag <;> cases k <;> rfl)
    (by constructor; rfl; intro k; cases flag <;> cases k <;> simp [copied,copyConfig,copyStacks,copyStack,mulStacks])
    (by intro k hk; have h1 := hk .source; have h2 := hk .scratch; have h3 := hk .target
        cases flag <;> cases k <;> simp_all [copyStack,copied,shifted,loopConfig,mulStacks])
  let addStart : Config MulStack MulState := ⟨.add flag (.readX false),copied.stk⟩
  let addEnd := loopConfig (.add flag .done) (!flag) pending factor (addCarry factor (false::acc) false).1
  have hcall : Step multiplyProgram copied addStart := by simp [Step,successors,multiplyProgram,copied,addStart]
  have hadd := (add_run factor (false::acc) false).relocate_exact (additionStack flag) (MulState.add flag)
    (additionStack_injective flag) (addition_code flag) (c' := addStart) (d' := addEnd)
    (by constructor; rfl; intro k; cases flag <;> cases k <;> rfl)
    (by constructor; rfl; intro k; cases flag <;> cases k <;> rfl)
    (by intro k hk; have h1 := hk .left; have h2 := hk .right; have h3 := hk .scratch; have h4 := hk .output
        cases flag <;> cases k <;> simp_all [additionStack,currentAccumulator,addStart,addEnd,copied,loopConfig,mulStacks])
  have hreturn : Step multiplyProgram addEnd
      (loopConfig (.read (!flag)) (!flag) pending factor (addCarry factor (false::acc) false).1) := by
    simp [Step,successors,multiplyProgram,addEnd,loopConfig]
  have hh := Run.succ hpop (Run.succ hshift (hcopy.trans (Run.succ hcall (hadd.trans (Run.one hreturn)))))
  simp only [List.length_cons] at hh
  convert hh using 1 <;> omega

theorem multiply_false_iteration (flag : Bool) (pending factor acc : List Bool) :
    Run multiplyProgram 2 (loopConfig (.read flag) flag (false::pending) factor acc)
      (loopConfig (.read flag) flag pending factor (false::acc)) := by
  have hpop : Step multiplyProgram (loopConfig (.read flag) flag (false::pending) factor acc)
      (loopConfig (.shift flag false) flag pending factor acc) := by
    cases flag <;> simp [Step,successors,multiplyProgram,loopConfig,mulStacks] <;>
      funext k <;> cases k <;> simp [Function.update,mulStacks]
  have hshift : Step multiplyProgram (loopConfig (.shift flag false) flag pending factor acc)
      (loopConfig (.read flag) flag pending factor (false::acc)) := by
    cases flag <;> simp [Step,successors,multiplyProgram,loopConfig,mulStacks,currentAccumulator] <;>
      funext k <;> cases k <;> simp [Function.update,mulStacks]
  exact Run.succ hpop (Run.succ hshift (.zero _))

def multiplyLoopResult : Bool → List Bool → List Bool → List Bool → Bool × List Bool
  | flag,[],_,acc => (flag,acc)
  | flag,b::bs,factor,acc =>
    if b then multiplyLoopResult (!flag) bs factor (addCarry factor (false::acc) false).1
    else multiplyLoopResult flag bs factor (false::acc)

/-- Polynomial transition bound for the actual repeated-copy/add main loop.
The supplied width is a mathematical invariant, never an executable register. -/
theorem multiply_loop_run (flag : Bool) (pending factor acc : List Bool) (W : ℕ)
    (hw : max acc.length factor.length+2*pending.length≤W) :
    ∃ t≤pending.length*(10*W+12),
      Run multiplyProgram t (loopConfig (.read flag) flag pending factor acc)
        (loopConfig (.read (multiplyLoopResult flag pending factor acc).1)
          (multiplyLoopResult flag pending factor acc).1 [] factor (multiplyLoopResult flag pending factor acc).2) ∧
      (multiplyLoopResult flag pending factor acc).2.length≤W := by
  induction pending generalizing flag acc with
  | nil => exact ⟨0,by simp,.zero _,by simpa [multiplyLoopResult] using (le_max_left acc.length factor.length).trans (by simpa using hw)⟩
  | cons b bs ih =>
    have hacc : acc.length+2*bs.length+2≤W := by simp only [List.length_cons] at hw; omega
    have hfactor : factor.length+2*bs.length+2≤W := by simp only [List.length_cons] at hw; omega
    cases b with
    | false =>
      obtain ⟨t,ht,hr,hlen⟩ := ih flag (false::acc) (by simp only [List.length_cons]; omega)
      refine ⟨2+t,?_,?_,hlen⟩
      · simp only [List.length_cons]; nlinarith
      · exact (multiply_false_iteration flag bs factor acc).trans hr
    | true =>
      have hwidth := addCarry_length factor (false::acc) false
      simp only [List.length_cons] at hwidth
      obtain ⟨t,ht,hr,hlen⟩ := ih (!flag) (addCarry factor (false::acc) false).1 (by omega)
      refine ⟨(5*factor.length+5*max factor.length (acc.length+1)+12)+t,?_,?_,hlen⟩
      · have hm : max factor.length (acc.length+1)≤W := by omega
        simp only [List.length_cons]
        nlinarith
      · exact (multiply_true_iteration flag bs factor acc).trans hr

end BalancedAssortments.NPStack
