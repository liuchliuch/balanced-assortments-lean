import BalancedAssortments.NPStackCompare
import BalancedAssortments.ComplexityTimeReduction

namespace BalancedAssortments.NPStack
open ComplexityTimeReduction

inductive NormalizeState
  | sourceRead | pushScratch (b : Bool) | trim | scratchRead | pushOut (b : Bool) | done
  deriving DecidableEq, Fintype

def normalizeProgram : Program CompareStack NormalizeState where
  code
    | .sourceRead => .pop .left .trim (.pushScratch false) (.pushScratch true)
    | .pushScratch b => .push .right b .sourceRead
    | .trim => .pop .right .done .trim (.pushOut true)
    | .scratchRead => .pop .right .done (.pushOut false) (.pushOut true)
    | .pushOut b => .push .result b .scratchRead
    | .done => .halt true
  start := .sourceRead
  inputStack := .left
  outputStack := .result

def normalizeConfig (q : NormalizeState) (xs ys zs : List Bool) : Config CompareStack NormalizeState :=
  ⟨q,compareStacks xs ys zs⟩

def trimHigh : List Bool→List Bool
  | [] => []
  | false::xs => trimHigh xs
  | true::xs => true::xs

private theorem trimHigh_append (xs ys : List Bool) :
    trimHigh (xs++ys)=if trimHigh xs=[] then trimHigh ys else trimHigh xs++ys := by
  induction xs with
  | nil => simp [trimHigh]
  | cons b xs ih => cases b <;> simp [trimHigh,ih]

lemma normalize_eq_trim (xs : List Bool) :
    (normalize xs).1=(trimHigh xs.reverse).reverse := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [ComplexityTimeReduction.normalize,ih,List.reverse_cons,trimHigh_append]
    by_cases he : trimHigh xs.reverse=[] <;> cases b <;> simp [he,trimHigh]

lemma normalize_source_step (xs ys zs : List Bool) :
    Step normalizeProgram (normalizeConfig .sourceRead xs ys zs)
      (normalizeConfig (match xs.head? with | none => .trim | some b => .pushScratch b) xs.tail ys zs) := by
  cases xs with
  | nil => simp [Step,successors,normalizeProgram,normalizeConfig]
  | cons b xs => cases b <;> simp [Step,successors,normalizeProgram,normalizeConfig]

lemma normalize_scratch_push (b : Bool) (xs ys zs : List Bool) :
    Step normalizeProgram (normalizeConfig (.pushScratch b) xs ys zs)
      (normalizeConfig .sourceRead xs (b::ys) zs) := by
  simp [Step,successors,normalizeProgram,normalizeConfig]

lemma normalize_output_push (b : Bool) (ys zs : List Bool) :
    Step normalizeProgram (normalizeConfig (.pushOut b) [] ys zs)
      (normalizeConfig .scratchRead [] ys (b::zs)) := by
  simp [Step,successors,normalizeProgram,normalizeConfig]

lemma normalize_scratch_step (ys zs : List Bool) :
    Step normalizeProgram (normalizeConfig .scratchRead [] ys zs)
      (normalizeConfig (match ys.head? with | none => .done | some b => .pushOut b) [] ys.tail zs) := by
  cases ys with
  | nil => simp [Step,successors,normalizeProgram,normalizeConfig]
  | cons b ys => cases b <;> simp [Step,successors,normalizeProgram,normalizeConfig]

lemma normalize_source_run (xs ys zs : List Bool) :
    Run normalizeProgram (2*xs.length+1) (normalizeConfig .sourceRead xs ys zs)
      (normalizeConfig .trim [] (xs.reverse++ys) zs) := by
  induction xs generalizing ys with
  | nil => simpa using Run.one (normalize_source_step [] ys zs)
  | cons b xs ih =>
    have hh := Run.succ (normalize_source_step (b::xs) ys zs)
      (Run.succ (normalize_scratch_push b xs ys zs) (ih (b::ys)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

lemma normalize_output_run (ys zs : List Bool) :
    Run normalizeProgram (2*ys.length+1) (normalizeConfig .scratchRead [] ys zs)
      (normalizeConfig .done [] [] (ys.reverse++zs)) := by
  induction ys generalizing zs with
  | nil => simpa using Run.one (normalize_scratch_step [] zs)
  | cons b ys ih =>
    have hh := Run.succ (normalize_scratch_step (b::ys) zs)
      (Run.succ (normalize_output_push b ys zs) (ih (b::zs)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

lemma normalize_trim_run (ys zs : List Bool) :
    ∃ t≤2*ys.length+1, Run normalizeProgram t (normalizeConfig .trim [] ys zs)
      (normalizeConfig .done [] [] ((trimHigh ys).reverse++zs)) := by
  induction ys with
  | nil =>
    refine ⟨1,by simp,Run.one ?_⟩
    simp [Step,successors,normalizeProgram,normalizeConfig,trimHigh]
  | cons b ys ih =>
    cases b with
    | false =>
      obtain ⟨t,ht,hr⟩ := ih
      refine ⟨t+1,by simp only [List.length_cons];omega,Run.succ ?_ hr⟩
      simp [Step,successors,normalizeProgram,normalizeConfig]
    | true =>
      have hh := Run.succ (normalize_output_push true ys zs) (normalize_output_run ys (true::zs))
      refine ⟨(2*ys.length+1)+1+1,by simp;omega,Run.succ (d := normalizeConfig (.pushOut true) [] ys zs) ?_ ?_⟩
      · simp [Step,successors,normalizeProgram,normalizeConfig]
      · simpa [trimHigh,List.reverse_cons,List.append_assoc] using hh

/-- Finite Boolean-stack normalization, including both reversals and every
leading-zero test. Both consumed input and scratch stacks are empty at exit. -/
theorem normalize_run (xs zs : List Bool) :
    ∃ t≤4*xs.length+2, Run normalizeProgram t (normalizeConfig .sourceRead xs [] zs)
      (normalizeConfig .done [] [] ((normalize xs).1++zs)) := by
  obtain ⟨t,ht,hr⟩ := normalize_trim_run xs.reverse zs
  have hs := normalize_source_run xs [] zs
  simp only [List.append_nil] at hs
  refine ⟨2*xs.length+1+t,?_,?_⟩
  · simp only [List.length_reverse] at ht
    omega
  · rw [normalize_eq_trim]
    exact hs.trans hr

lemma normalize_initial (xs : List Bool) : initial normalizeProgram xs=normalizeConfig .sourceRead xs [] [] := by
  unfold initial normalizeConfig normalizeProgram
  congr 1
  funext k
  cases k <;> simp [compareStacks,Function.update]

theorem normalize_outputs (xs : List Bool) :
    OutputsIn normalizeProgram xs (normalize xs).1 (4*xs.length+2) := by
  obtain ⟨t,ht,hr⟩ := normalize_run xs []
  refine ⟨t,ht,normalizeConfig .done [] [] (normalize xs).1,?_,rfl,rfl⟩
  rw [normalize_initial]
  simpa using hr

def finiteNormalize : FiniteProgram where
  K := CompareStack
  Q := NormalizeState
  program := normalizeProgram

end BalancedAssortments.NPStack
