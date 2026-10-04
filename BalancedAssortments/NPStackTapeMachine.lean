import BalancedAssortments.NPMachineLocal
import BalancedAssortments.NPStackMachine

/-! Actual finite-control, finite-alphabet one-tape implementation of Boolean
stack operations. Tracks grow to the right; each stack is stored bottom first.
The symbolic table compiles exactly to NPMachine via NPMachineFiniteBridge.
Input layout initialization is deliberately separate from the operational core. -/
noncomputable section
namespace BalancedAssortments.NPStack.TapeMachine
open NPMachine NPMachine.FiniteBridge

inductive Control (K Q : Type*)
  | normal (pc : Q)
  | seekPush (stack : K) (bit : Bool) (next : Q)
  | seekPop (stack : K) (empty onFalse onTrue : Q)
  | popAt (stack : K) (onFalse onTrue : Q)
  | back (next : Q)
  deriving DecidableEq, Fintype

abbrev Cell (K : Type*) := Bool × (K → Option Bool)
abbrev Tape (K : Type*) := ℤ → Symbol (Cell K)

variable {K Q : Type*} [Fintype K] [Fintype Q] [DecidableEq K]

def readCell : Symbol (Cell K) → Cell K
  | .work c => c
  | _ => (false,fun _ => none)

def writeTrack (a : Symbol (Cell K)) (k : K) (b : Option Bool) : Symbol (Cell K) :=
  .work ((readCell a).1,Function.update (readCell a).2 k b)

def actions (P : NPStack.Program K Q) : Control K Q → Symbol (Cell K) →
    List (Action (Control K Q) (Cell K))
  | .normal q,a => match P.code q with
    | .halt _ => []
    | .jump q' => [(.normal q',a,.stay)]
    | .push k b q' => [(.seekPush k b q',a,.stay)]
    | .pop k qe qf qt => [(.seekPop k qe qf qt,a,.stay)]
    | .choice q' q'' => [(.normal q',a,.stay),(.normal q'',a,.stay)]
  | .seekPush k b q,a => match (readCell a).2 k with
    | some _ => [(.seekPush k b q,a,.right)]
    | none => [(.back q,writeTrack a k (some b),.stay)]
  | .seekPop k qe qf qt,a => match (readCell a).2 k with
    | some _ => [(.seekPop k qe qf qt,a,.right)]
    | none => if (readCell a).1 then [(.normal qe,a,.stay)] else [(.popAt k qf qt,a,.left)]
  | .popAt k qf qt,a => match (readCell a).2 k with
    | none => []
    | some b => [(.back (if b then qt else qf),writeTrack a k none,.stay)]
  | .back q,a => if (readCell a).1 then [(.normal q,a,.stay)] else [(.back q,a,.left)]

def accepting (P : NPStack.Program K Q) : Control K Q → Bool
  | .normal q => match P.code q with | .halt b => b | _ => false
  | _ => false

def core (P : NPStack.Program K Q) : FiniteBridge.Program (Control K Q) (Cell K) :=
  tableProgram (.normal P.start) (accepting P) (actions P)

def machine (P : NPStack.Program K Q) : NPMachine.Machine := compile (core P)

def cfgAt (tape : Tape K) (q : Control K Q) (p : ℤ) : Configuration (Control K Q) (Cell K) :=
  ⟨q,p,tape⟩

lemma action_step (P : NPStack.Program K Q) (tape : Tape K) (q q' : Control K Q)
    (p : ℤ) (a : Symbol (Cell K)) (m : Move)
    (ha : (q',a,m) ∈ actions P q (tape p)) :
    FiniteBridge.Step (core P) (cfgAt tape q p)
      (cfgAt (Function.update tape p a) q' (p+m.displacement)) :=
  (table_step _ _ _ _ _).2 ⟨(q',a,m),ha,rfl⟩

lemma unchanged_step (P : NPStack.Program K Q) (tape : Tape K) (q q' : Control K Q)
    (p : ℤ) (m : Move) (ha : (q',tape p,m) ∈ actions P q (tape p)) :
    FiniteBridge.Step (core P) (cfgAt tape q p) (cfgAt tape q' (p+m.displacement)) := by
  have hh := action_step P tape q q' p (tape p) m ha
  simpa only [Function.update_eq_self] using hh

/-- Representation invariant permits inert empty work cells left by popping.
Every track nevertheless has exactly the source stack's bottom-to-top content. -/
def Represents (stk : K → List Bool) (tape : Tape K) : Prop :=
  (∀ p,(readCell (tape p)).1=decide (p=0)) ∧
  ∀ k p,(readCell (tape p)).2 k = if 0≤p then (stk k).reverse[p.toNat]? else none

lemma represents_at (stk : K → List Bool) (tape : Tape K) (h : Represents stk tape) (k : K) (j : ℕ) :
    (readCell (tape j)).2 k=(stk k).reverse[j]? := by
  simpa using h.2 k j

lemma represents_bottom (stk : K → List Bool) (tape : Tape K) (h : Represents stk tape) (j : ℕ) :
    (readCell (tape j)).1=decide (j=0) := by simpa using h.1 j

lemma back_run (P : NPStack.Program K Q) (tape : Tape K) (q : Q)
    (bottom : ∀ j : ℕ,(readCell (tape j)).1=decide (j=0)) (j : ℕ) :
    FiniteBridge.Run (core P) (j+1) (cfgAt tape (.back q) j) (cfgAt tape (.normal q) 0) := by
  induction j with
  | zero =>
    apply FiniteBridge.Run.one
    have hh := unchanged_step P tape (.back q) (.normal q) 0 .stay
      (by
        have h0 : (readCell (tape 0)).1=true := by simpa using bottom 0
        simp [actions,h0])
    simpa [Move.displacement] using hh
  | succ j ih =>
    have hh := unchanged_step P tape (.back q) (.back q) (j+1) .left
      (by simp [actions,show (readCell (tape (j+1))).1=false from by simpa using bottom (j+1)])
    have he : (j+1 : ℕ) = j+1 := rfl
    have hs : FiniteBridge.Step (core P) (cfgAt tape (.back q) (j+1)) (cfgAt tape (.back q) j) := by
      simpa [Move.displacement] using hh
    exact FiniteBridge.Run.succ hs ih

lemma scan_run (P : NPStack.Program K Q) (tape : Tape K) (q : Control K Q) (j : ℕ)
    (ha : ∀ i<j,(q,tape i,Move.right) ∈ actions P q (tape i)) :
    FiniteBridge.Run (core P) j (cfgAt tape q 0) (cfgAt tape q j) := by
  induction j with
  | zero => exact FiniteBridge.Run.zero _
  | succ j ih =>
    have hr := ih (fun i hi => ha i (by omega))
    have hh := unchanged_step P tape q q j .right (ha j (by omega))
    have hs : FiniteBridge.Step (core P) (cfgAt tape q j) (cfgAt tape q (j+1)) := by
      simpa [Move.displacement] using hh
    exact hr.trans (FiniteBridge.Run.one hs)

lemma push_scan (P : NPStack.Program K Q) (tape : Tape K) (stk : K → List Bool)
    (h : Represents stk tape) (k : K) (b : Bool) (q : Q) :
    FiniteBridge.Run (core P) (stk k).length (cfgAt tape (.seekPush k b q) 0)
      (cfgAt tape (.seekPush k b q) (stk k).length) := by
  apply scan_run
  intro i hi
  have hget : ∃ z,(stk k).reverse[i]?=some z := by
    have hi' : i < (stk k).reverse.length := by simpa using hi
    exact ⟨(stk k).reverse[i],List.getElem?_eq_getElem hi'⟩
  obtain ⟨z,hz⟩ := hget
  simp [actions,represents_at stk tape h k i,hz]

end BalancedAssortments.NPStack.TapeMachine
