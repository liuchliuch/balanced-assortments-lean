import BalancedAssortments.NPStackCompare
import BalancedAssortments.NPStackDeterministic
import BalancedAssortments.NPCNFValidation

namespace BalancedAssortments.NPStackLabelEqual
open NPStack ComplexityTimeBinary

def next (o : Ordering) (a b : Option Bool) : CompareState :=
  match a,b with
  | none,none => .emit (o == .eq)
  | _,_ => .readLeft (highCompare o (a.getD false) (b.getD false))

def program : Program CompareStack CompareState where
  code
    | .readLeft o => .pop .left (.readRight o none) (.readRight o (some false)) (.readRight o (some true))
    | .readRight o a => .pop .right (next o a none) (next o a (some false)) (next o a (some true))
    | .emit b => .push .result b .done
    | .done => .halt true
  start := .readLeft .eq
  inputStack := .left
  outputStack := .result
lemma compare_read_left (o : Ordering) (xs ys zs : List Bool) :
    Step program (compareConfig (.readLeft o) xs ys zs)
      (compareConfig (.readRight o xs.head?) xs.tail ys zs) := by
  cases xs with
  | nil => simp [Step,successors,program,compareConfig]
  | cons b xs => cases b <;> simp [Step,successors,program,compareConfig]

lemma compare_read_right (o : Ordering) (a : Option Bool) (xs ys zs : List Bool) :
    Step program (compareConfig (.readRight o a) xs ys zs)
      (compareConfig (next o a ys.head?) xs ys.tail zs) := by
  cases ys with
  | nil => simp [Step,successors,program,compareConfig]
  | cons b ys => cases b <;> simp [Step,successors,program,compareConfig]

lemma compare_emit (b : Bool) (zs : List Bool) :
    Step program (compareConfig (.emit b) [] [] zs)
      (compareConfig .done [] [] (b::zs)) := by
  simp [Step,successors,program,compareConfig]

/-- Exactly two input-cell tests per position and three terminal transitions.
No decoded integer is stored or inspected by this finite bytecode. -/
theorem compare_run (o : Ordering) (xs ys zs : List Bool) :
    Run program (2*max xs.length ys.length+3)
      (compareConfig (.readLeft o) xs ys zs)
      (compareConfig .done [] [] ((compareScan o xs ys == .eq)::zs)) := by
  induction xs generalizing o ys with
  | nil =>
    induction ys generalizing o with
    | nil =>
      exact Run.succ (compare_read_left o [] [] zs)
        (Run.succ (compare_read_right o none [] [] zs) (by
          simpa [next,compareScan] using Run.one (compare_emit (o == .eq) zs)))
    | cons b ys ih =>
      have hh := Run.succ (compare_read_left o [] (b::ys) zs)
        (Run.succ (compare_read_right o none [] (b::ys) zs) (ih (highCompare o false b)))
      simpa [next,compareScan,Nat.mul_add,Nat.add_assoc] using hh
  | cons a xs ih =>
    cases ys with
    | nil =>
      have hh := Run.succ (compare_read_left o (a::xs) [] zs)
        (Run.succ (compare_read_right o (some a) xs [] zs) (ih (highCompare o a false) []))
      simpa [next,compareScan,Nat.mul_add,Nat.add_assoc] using hh
    | cons b ys =>
      have hh := Run.succ (compare_read_left o (a::xs) (b::ys) zs)
        (Run.succ (compare_read_right o (some a) xs (b::ys) zs) (ih (highCompare o a b) ys))
      simpa [next,compareScan,Nat.mul_add,Nat.add_assoc,max_add_add_right] using hh

/-- Padded little-endian labels are compared by numeric value using only
finite control and one-bit stack operations. -/
theorem equal_run (xs ys out : List Bool) :
    Run program (2*max xs.length ys.length+3)
      (compareConfig (.readLeft .eq) xs ys out)
      (compareConfig .done [] [] (decide (value xs=value ys)::out)) := by
  have h := compare_run .eq xs ys out
  rw [compareScan_correct] at h
  have he := NPCNF.Encoding.compare_eq_iff xs ys
  by_cases hc : (compareBits xs ys).1=.eq
  · have hv := he.mp hc
    simpa [hc,hv] using h
  · have hv : value xs≠value ys := fun hh => hc (he.mpr hh)
    cases hcmp : (compareBits xs ys).1 <;> simp_all

lemma program_noChoice : NoChoice program := by
  intro q a b;cases q <;> simp [program]

lemma program_deterministic : Deterministic program := noChoice_deterministic program_noChoice

theorem accepting_result (xs ys out : List Bool) {t : ℕ} {d : Config CompareStack CompareState}
    (hr : Run program t (compareConfig (.readLeft .eq) xs ys out) d) (ha : accepts program d) :
    d=compareConfig .done [] [] (decide (value xs=value ys)::out) ∧ t=2*max xs.length ys.length+3 := by
  have hh := (equal_run xs ys out).halted_unique program_deterministic hr rfl ha
  exact ⟨hh.2.symm,hh.1.symm⟩

end BalancedAssortments.NPStackLabelEqual
