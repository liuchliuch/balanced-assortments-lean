import BalancedAssortments.NPStackReverse
import BalancedAssortments.ComplexityTimeBinary

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary

inductive AddStack | left | right | scratch | output deriving DecidableEq, Fintype
inductive AddState
  | readX (carry : Bool)
  | readY (a : Option Bool) (carry : Bool)
  | emit (bit carry : Bool)
  | finish (carry : Bool)
  | reverseRead
  | reversePush (bit : Bool)
  | done
  deriving DecidableEq, Fintype

def sumState (a b c : Bool) : AddState := .emit (fullAdd a b c).1 (fullAdd a b c).2

def addProgram : Program AddStack AddState where
  code
    | .readX c => .pop .left (.readY none c) (.readY (some false) c) (.readY (some true) c)
    | .readY a c => .pop .right
        (match a with | none => .finish c | some x => sumState x false c)
        (sumState (a.getD false) false c) (sumState (a.getD false) true c)
    | .emit b c => .push .scratch b (.readX c)
    | .finish c => .push .scratch c .reverseRead
    | .reverseRead => .pop .scratch .done (.reversePush false) (.reversePush true)
    | .reversePush b => .push .output b .reverseRead
    | .done => .halt true
  start := .readX false
  inputStack := .left
  outputStack := .output

def fourStacks (xs ys zs ws : List Bool) : AddStack → List Bool
  | .left => xs
  | .right => ys
  | .scratch => zs
  | .output => ws

def addConfig (q : AddState) (xs ys zs ws : List Bool) : Config AddStack AddState :=
  ⟨q,fourStacks xs ys zs ws⟩

@[simp] lemma update_left (xs ys zs ws vs : List Bool) :
    Function.update (fourStacks xs ys zs ws) .left vs=fourStacks vs ys zs ws := by
  funext k; cases k <;> simp [fourStacks]
@[simp] lemma update_right (xs ys zs ws vs : List Bool) :
    Function.update (fourStacks xs ys zs ws) .right vs=fourStacks xs vs zs ws := by
  funext k; cases k <;> simp [fourStacks]
@[simp] lemma update_scratch (xs ys zs ws vs : List Bool) :
    Function.update (fourStacks xs ys zs ws) .scratch vs=fourStacks xs ys vs ws := by
  funext k; cases k <;> simp [fourStacks]
@[simp] lemma update_output (xs ys zs ws vs : List Bool) :
    Function.update (fourStacks xs ys zs ws) .output vs=fourStacks xs ys zs vs := by
  funext k; cases k <;> simp [fourStacks]

lemma add_readX_nil (c : Bool) (ys zs ws : List Bool) :
    Step addProgram (addConfig (.readX c) [] ys zs ws) (addConfig (.readY none c) [] ys zs ws) := by
  simp [Step,successors,addProgram,addConfig,fourStacks]
lemma add_readX_cons (a c : Bool) (xs ys zs ws : List Bool) :
    Step addProgram (addConfig (.readX c) (a::xs) ys zs ws) (addConfig (.readY (some a) c) xs ys zs ws) := by
  cases a <;> simp [Step,successors,addProgram,addConfig,fourStacks,Function.update]
lemma add_readY_nil (a : Option Bool) (c : Bool) (xs zs ws : List Bool) :
    Step addProgram (addConfig (.readY a c) xs [] zs ws)
      (addConfig (match a with | none => .finish c | some x => sumState x false c) xs [] zs ws) := by
  simp [Step,successors,addProgram,addConfig,fourStacks]
lemma add_readY_cons (a : Option Bool) (b c : Bool) (xs ys zs ws : List Bool) :
    Step addProgram (addConfig (.readY a c) xs (b::ys) zs ws)
      (addConfig (sumState (a.getD false) b c) xs ys zs ws) := by
  cases b <;> simp [Step,successors,addProgram,addConfig,fourStacks,Function.update]
lemma add_emit (a b c : Bool) (xs ys zs ws : List Bool) :
    Step addProgram (addConfig (sumState a b c) xs ys zs ws)
      (addConfig (.readX (fullAdd a b c).2) xs ys ((fullAdd a b c).1::zs) ws) := by
  simp [Step,successors,addProgram,addConfig,sumState,fourStacks,Function.update]
lemma add_finish (c : Bool) (xs ys zs ws : List Bool) :
    Step addProgram (addConfig (.finish c) xs ys zs ws)
      (addConfig .reverseRead xs ys (c::zs) ws) := by
  simp [Step,successors,addProgram,addConfig,fourStacks,Function.update]

/-- Every arithmetic recursion is implemented by exactly three finite-control
transitions. The accumulated stack contains the reversed actual ripple result. -/
theorem add_core_run (xs ys zs ws : List Bool) (c : Bool) :
    Run addProgram (3*max xs.length ys.length+3) (addConfig (.readX c) xs ys zs ws)
      (addConfig .reverseRead [] [] ((addCarry xs ys c).1.reverse++zs) ws) := by
  induction xs generalizing ys zs ws c with
  | nil =>
    induction ys generalizing zs ws c with
    | nil =>
      simpa [addCarry] using Run.succ (add_readX_nil c [] zs ws)
        (Run.succ (add_readY_nil none c [] zs ws)
          (Run.succ (add_finish c [] [] zs ws) (.zero _)))
    | cons b ys ih =>
      have hh := Run.succ (add_readX_nil c (b::ys) zs ws)
        (Run.succ (add_readY_cons none b c [] ys zs ws)
          (Run.succ (add_emit false b c [] ys zs ws)
            (ih ((fullAdd false b c).1::zs) ws (fullAdd false b c).2)))
      simpa [addCarry,List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh
  | cons a xs ih =>
    cases ys with
    | nil =>
      have hh := Run.succ (add_readX_cons a c xs [] zs ws)
        (Run.succ (add_readY_nil (some a) c xs zs ws)
          (Run.succ (add_emit a false c xs [] zs ws)
            (ih [] ((fullAdd a false c).1::zs) ws (fullAdd a false c).2)))
      simpa [addCarry,List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh
    | cons b ys =>
      have hh := Run.succ (add_readX_cons a c xs (b::ys) zs ws)
        (Run.succ (add_readY_cons (some a) b c xs ys zs ws)
          (Run.succ (add_emit a b c xs ys zs ws)
            (ih ys ((fullAdd a b c).1::zs) ws (fullAdd a b c).2)))
      simpa [addCarry,List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc,Nat.succ_max_succ] using hh

lemma add_reverse_run (xs ys zs ws : List Bool) :
    Run addProgram (2*zs.length+1) (addConfig .reverseRead xs ys zs ws)
      (addConfig .done xs ys [] (zs.reverse++ws)) := by
  induction zs generalizing ws with
  | nil =>
    apply Run.one
    simp [Step,successors,addProgram,addConfig,fourStacks]
  | cons b zs ih =>
    have h1 : Step addProgram (addConfig .reverseRead xs ys (b::zs) ws)
        (addConfig (.reversePush b) xs ys zs ws) := by
      cases b <;> simp [Step,successors,addProgram,addConfig,fourStacks,Function.update]
    have h2 : Step addProgram (addConfig (.reversePush b) xs ys zs ws)
        (addConfig .reverseRead xs ys zs (b::ws)) := by
      simp [Step,successors,addProgram,addConfig,fourStacks,Function.update]
    have hh := Run.succ h1 (Run.succ h2 (ih (b::ws)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

/-- The actual finite program computes exactly the bit-list result used by every
existing ripple-carry cost/refinement theorem, with no arithmetic oracle. -/
theorem add_run (xs ys : List Bool) (c : Bool) :
    Run addProgram (5*max xs.length ys.length+6) (addConfig (.readX c) xs ys [] [])
      (addConfig .done [] [] [] (addCarry xs ys c).1) := by
  have h1 := add_core_run xs ys [] [] c
  have h2 := add_reverse_run [] [] (addCarry xs ys c).1.reverse []
  simp only [List.append_nil] at h1
  have hh := h1.trans h2
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil,addCarry_length] at hh
  convert hh using 1 <;> omega

/-- Arithmetic correctness of the concrete operational result. -/
theorem add_run_value (xs ys : List Bool) (c : Bool) :
    ∃ out,Run addProgram (5*max xs.length ys.length+6)
      (addConfig (.readX c) xs ys [] []) (addConfig .done [] [] [] out) ∧
      value out=value xs+value ys+c.toNat :=
  ⟨(addCarry xs ys c).1,add_run xs ys c,addCarry_value xs ys c⟩

def finiteAdd : FiniteProgram where
  K := AddStack
  Q := AddState
  program := addProgram

end BalancedAssortments.NPStack
