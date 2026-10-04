import BalancedAssortments.NPStackMachine
import BalancedAssortments.ComplexityTimeBinary

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary

inductive CompareStack | left | right | result
  deriving DecidableEq, Fintype
inductive CompareState
  | readLeft (carry : Ordering)
  | readRight (carry : Ordering) (leftBit : Option Bool)
  | emit (answer : Bool)
  | done
  deriving DecidableEq, Fintype

def highCompare (o : Ordering) (a b : Bool) : Ordering :=
  if a=b then o else if a then .gt else .lt

def compareNext (o : Ordering) (a b : Option Bool) : CompareState :=
  match a,b with
  | none,none => .emit (o != .gt)
  | _,_ => .readLeft (highCompare o (a.getD false) (b.getD false))

def compareProgram : Program CompareStack CompareState where
  code
    | .readLeft o => .pop .left (.readRight o none) (.readRight o (some false)) (.readRight o (some true))
    | .readRight o a => .pop .right (compareNext o a none) (compareNext o a (some false)) (compareNext o a (some true))
    | .emit b => .push .result b .done
    | .done => .halt true
  start := .readLeft .eq
  inputStack := .left
  outputStack := .result

def compareStacks (xs ys zs : List Bool) : CompareStack→List Bool
  | .left => xs | .right => ys | .result => zs

def compareConfig (q : CompareState) (xs ys zs : List Bool) : Config CompareStack CompareState :=
  ⟨q,compareStacks xs ys zs⟩

@[simp] theorem compareStacks_left (xs ys zs : List Bool) : compareStacks xs ys zs .left=xs := rfl
@[simp] theorem compareStacks_right (xs ys zs : List Bool) : compareStacks xs ys zs .right=ys := rfl
@[simp] theorem compareStacks_result (xs ys zs : List Bool) : compareStacks xs ys zs .result=zs := rfl
@[simp] theorem update_compare_left (xs ys zs ws : List Bool) :
    Function.update (compareStacks xs ys zs) .left ws=compareStacks ws ys zs := by
  funext k;cases k <;> simp [compareStacks,Function.update]
@[simp] theorem update_compare_right (xs ys zs ws : List Bool) :
    Function.update (compareStacks xs ys zs) .right ws=compareStacks xs ws zs := by
  funext k;cases k <;> simp [compareStacks,Function.update]
@[simp] theorem update_compare_result (xs ys zs ws : List Bool) :
    Function.update (compareStacks xs ys zs) .result ws=compareStacks xs ys ws := by
  funext k;cases k <;> simp [compareStacks,Function.update]

/-- Semantic accumulator for the finite three-way control state. -/
def compareScan (o : Ordering) : List Bool→List Bool→Ordering
  | [],[] => o
  | a::xs,[] => compareScan (highCompare o a false) xs []
  | [],b::ys => compareScan (highCompare o false b) [] ys
  | a::xs,b::ys => compareScan (highCompare o a b) xs ys

lemma compareScan_correct (o : Ordering) (xs ys : List Bool) :
    compareScan o xs ys = if (compareBits xs ys).1=.eq then o else (compareBits xs ys).1 := by
  induction xs generalizing o ys with
  | nil =>
    induction ys generalizing o with
    | nil => simp [compareScan,compareBits]
    | cons b ys ih =>
      rw [compareScan,ih]
      cases h : (compareBits [] ys).1 <;> cases o <;> cases b <;>
        simp [compareBits,h,highCompare,lowCompare]
  | cons a xs ih =>
    cases ys with
    | nil =>
      rw [compareScan,ih]
      cases h : (compareBits xs []).1 <;> cases o <;> cases a <;>
        simp [compareBits,h,highCompare,lowCompare]
    | cons b ys =>
      rw [compareScan,ih]
      cases h : (compareBits xs ys).1 <;> cases o <;> cases a <;> cases b <;>
        simp [compareBits,h,highCompare,lowCompare]

lemma compare_read_left (o : Ordering) (xs ys zs : List Bool) :
    Step compareProgram (compareConfig (.readLeft o) xs ys zs)
      (compareConfig (.readRight o xs.head?) xs.tail ys zs) := by
  cases xs with
  | nil => simp [Step,successors,compareProgram,compareConfig]
  | cons b xs => cases b <;> simp [Step,successors,compareProgram,compareConfig]

lemma compare_read_right (o : Ordering) (a : Option Bool) (xs ys zs : List Bool) :
    Step compareProgram (compareConfig (.readRight o a) xs ys zs)
      (compareConfig (compareNext o a ys.head?) xs ys.tail zs) := by
  cases ys with
  | nil => simp [Step,successors,compareProgram,compareConfig]
  | cons b ys => cases b <;> simp [Step,successors,compareProgram,compareConfig]

lemma compare_emit (b : Bool) (zs : List Bool) :
    Step compareProgram (compareConfig (.emit b) [] [] zs)
      (compareConfig .done [] [] (b::zs)) := by
  simp [Step,successors,compareProgram,compareConfig]

/-- Exactly two input-cell tests per position and three terminal transitions.
No decoded integer is stored or inspected by this finite bytecode. -/
theorem compare_run (o : Ordering) (xs ys zs : List Bool) :
    Run compareProgram (2*max xs.length ys.length+3)
      (compareConfig (.readLeft o) xs ys zs)
      (compareConfig .done [] [] ((compareScan o xs ys != .gt)::zs)) := by
  induction xs generalizing o ys with
  | nil =>
    induction ys generalizing o with
    | nil =>
      exact Run.succ (compare_read_left o [] [] zs)
        (Run.succ (compare_read_right o none [] [] zs) (by
          simpa [compareNext,compareScan] using Run.one (compare_emit (o != .gt) zs)))
    | cons b ys ih =>
      have hh := Run.succ (compare_read_left o [] (b::ys) zs)
        (Run.succ (compare_read_right o none [] (b::ys) zs) (ih (highCompare o false b)))
      simpa [compareNext,compareScan,Nat.mul_add,Nat.add_assoc] using hh
  | cons a xs ih =>
    cases ys with
    | nil =>
      have hh := Run.succ (compare_read_left o (a::xs) [] zs)
        (Run.succ (compare_read_right o (some a) xs [] zs) (ih (highCompare o a false) []))
      simpa [compareNext,compareScan,Nat.mul_add,Nat.add_assoc] using hh
    | cons b ys =>
      have hh := Run.succ (compare_read_left o (a::xs) (b::ys) zs)
        (Run.succ (compare_read_right o (some a) xs (b::ys) zs) (ih (highCompare o a b) ys))
      simpa [compareNext,compareScan,Nat.mul_add,Nat.add_assoc,max_add_add_right] using hh

/-- Exact operational refinement of the already-certified binary comparator. -/
theorem compare_leBits_run (xs ys zs : List Bool) :
    Run compareProgram (2*max xs.length ys.length+3)
      (compareConfig (.readLeft .eq) xs ys zs)
      (compareConfig .done [] [] (leBits xs ys::zs)) := by
  have hh := compare_run .eq xs ys zs
  rw [compareScan_correct] at hh
  by_cases he : (compareBits xs ys).1=.eq <;> simpa [he,leBits] using hh

def finiteCompare : FiniteProgram where
  K := CompareStack
  Q := CompareState
  program := compareProgram

end BalancedAssortments.NPStack
