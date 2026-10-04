import BalancedAssortments.CookLevinRawCombinators
import BalancedAssortments.FPTASCostInputSeeds

/-! Executable raw-bit tableau construction. All variable-sized loop bounds are
actual lists; addresses are binary straight-line circuits. Machine states, tape
symbols, and rules are fixed finite constants for each reduction. Refinement and
whole-constructor polynomial bounds are proved separately. -/
namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary
open NPCNF.Encoding (BitLiteral BitClause BitFormula bitPositive bitNegative)

structure RawDimensions where
  q : List Bool
  g : List Bool
  w : List Bool
  t : List Bool
  r : List Bool

def RawDimensions.inputs (d : RawDimensions) (time cell symbol rule : List Bool) : Fin 9 → List Bool :=
  ![d.q,d.g,d.w,d.t,d.r,time,cell,symbol,rule]
def stateLabel (d : RawDimensions) (time state : List Bool) : List Bool × ℕ :=
  stateIndexExpr.run (d.inputs time [] state [])
def headLabel (d : RawDimensions) (time cell : List Bool) : List Bool × ℕ :=
  headIndexExpr.run (d.inputs time cell [] [])
def tapeLabel (d : RawDimensions) (time cell symbol : List Bool) : List Bool × ℕ :=
  tapeIndexExpr.run (d.inputs time cell symbol [])
def choiceLabel (d : RawDimensions) (time rule : List Bool) : List Bool × ℕ :=
  choiceIndexExpr.run (d.inputs time [] [] rule)

def rawAppend (F G : BitFormula × ℕ) : BitFormula × ℕ :=
  (F.1++G.1,F.2+G.2+F.1.length+4)
def rawForce (label : List Bool × ℕ) : BitFormula × ℕ :=
  ([[bitPositive label.1]],label.2+6)
def rawSingle (labels : List (List Bool) × ℕ) : BitFormula × ℕ :=
  let literals := rawMap (fun x => (bitPositive x,2)) labels.1
  ([literals.1],labels.2+literals.2+4)
def rawGuardComputed (positive : Bool) (label : List Bool × ℕ) (body : BitFormula × ℕ) : BitFormula × ℕ :=
  let result := rawGuard ⟨label.1,positive⟩ body.1
  (result.1,label.2+body.2+result.2+4)
def rawCopy (old next : List Bool × ℕ) : BitFormula × ℕ :=
  ([[bitNegative old.1,bitPositive next.1]],old.2+next.2+8)

def rawShape (d : RawDimensions) (times steps states cells symbols rules : List (List Bool)) : BitFormula × ℕ :=
  rawAppend
    (rawFlatMap (fun time => rawAppend
      (let labels := rawMap (stateLabel d time) states
       let clauses := rawExactlyOne labels.1
       (clauses.1,labels.2+clauses.2+4))
      (rawAppend
        (let labels := rawMap (headLabel d time) cells
         let clauses := rawExactlyOne labels.1
         (clauses.1,labels.2+clauses.2+4))
        (rawFlatMap (fun cell =>
          let labels := rawMap (tapeLabel d time cell) symbols
          let clauses := rawExactlyOne labels.1
          (clauses.1,labels.2+clauses.2+4)) cells))) times)
    (rawFlatMap (fun time =>
      let labels := rawMap (choiceLabel d time) rules
      let clauses := rawExactlyOne labels.1
      (clauses.1,labels.2+clauses.2+4)) steps)

def rawAccept (d : RawDimensions) (time : List Bool) (accepting : List (List Bool)) : BitFormula × ℕ :=
  rawSingle (rawMap (stateLabel d time) accepting)

def rawInitial (d : RawDimensions) (start : List Bool)
    (cells symbols : List (List Bool)) : BitFormula × ℕ :=
  rawAppend (rawForce (stateLabel d [] start))
    (rawAppend (rawForce (headLabel d [] d.t))
      (rawFlatMap (fun pair => rawForce (tapeLabel d [] pair.1 pair.2)) (cells.zip symbols)))

/-- Each direction compares binary positions without decoded integer arithmetic. -/
def rawMoveMatch (move : Move) (old next : List Bool) : Bool × ℕ :=
  match move with
  | .stay => let cmp := compareBits next old; (cmp.1 == .eq,cmp.2+2)
  | .right => let step := addCarry old [] true; let cmp := compareBits next step.1
              (cmp.1 == .eq,step.2+cmp.2+4)
  | .left => let step := addCarry next [] true; let cmp := compareBits step.1 old
             (cmp.1 == .eq,step.2+cmp.2+4)

def rawHeadTarget (d : RawDimensions) (next old : List Bool) (move : Move)
    (cells : List (List Bool)) : BitFormula × ℕ :=
  let labels := rawFlatMap (fun cell =>
    let test := rawMoveMatch move old cell
    let label := headLabel d next cell
    (if test.1 then [label.1] else [],test.2+label.2+4)) cells
  rawSingle labels

structure RawRule where
  source : List Bool
  target : List Bool
  read : List Bool
  write : List Bool
  move : Move

def rawRuleBody (d : RawDimensions) (old next : List Bool) (cells symbols : List (List Bool))
    (rule : RawRule) : BitFormula × ℕ :=
  rawAppend (rawForce (stateLabel d old rule.source))
    (rawAppend (rawForce (stateLabel d next rule.target))
      (rawAppend
        (rawFlatMap (fun cell => rawGuardComputed true (headLabel d old cell)
          (rawAppend (rawForce (tapeLabel d old cell rule.read))
            (rawAppend (rawForce (tapeLabel d next cell rule.write))
              (rawHeadTarget d next cell rule.move cells)))) cells)
        (rawFlatMap (fun cell => rawGuardComputed false (headLabel d old cell)
          (rawFlatMap (fun symbol => rawCopy (tapeLabel d old cell symbol)
            (tapeLabel d next cell symbol)) symbols)) cells)))

def rawHaltBody (d : RawDimensions) (old next : List Bool)
    (states cells symbols accepting : List (List Bool)) : BitFormula × ℕ :=
  rawAppend (rawAccept d old accepting)
    (rawAppend (rawFlatMap (fun s => rawCopy (stateLabel d old s) (stateLabel d next s)) states)
      (rawAppend (rawFlatMap (fun p => rawCopy (headLabel d old p) (headLabel d next p)) cells)
        (rawFlatMap (fun p => rawFlatMap (fun a => rawCopy (tapeLabel d old p a)
          (tapeLabel d next p a)) symbols) cells)))

def rawTransitions (d : RawDimensions) (steps states cells symbols accepting choices : List (List Bool))
    (rules : List RawRule) : BitFormula × ℕ :=
  rawFlatMap (fun old =>
    let next := addCarry old [] true
    let bodies := rawFlatMap (fun entry =>
      let body := match entry.2 with
        | none => rawHaltBody d old next.1 states cells symbols accepting
        | some rule => rawRuleBody d old next.1 cells symbols rule
      rawGuardComputed true (choiceLabel d old entry.1) body)
      (choices.zip (none::rules.map some))
    (bodies.1,next.2+bodies.2+rules.length+choices.length+8)) steps

/-- Fixed machine constants, compiled once for each machine-specific reduction.
Their storage size contributes a machine-dependent constant to the cost bound. -/
structure MachineConstants where
  states : List (List Bool)
  symbols : List (List Bool)
  choices : List (List Bool)
  accepting : List (List Bool)
  rules : List RawRule
  start : List Bool
  q : List Bool
  g : List Bool
  r : List Bool

def machineConstants (M : Machine) : MachineConstants where
  states := (List.range (M.stateExtra+1)).map Nat.bits
  symbols := (List.range (M.symbolExtra+3)).map Nat.bits
  choices := (List.range (M.rules.length+1)).map Nat.bits
  accepting := ((List.finRange (M.stateExtra+1)).filter M.accepting).map (fun s => s.val.bits)
  rules := M.rules.map (fun rule => ⟨rule.source.val.bits,rule.target.val.bits,rule.read.val.bits,rule.write.val.bits,rule.move⟩)
  start := M.start.val.bits
  q := (M.stateExtra+1).bits
  g := (M.symbolExtra+3).bits
  r := (M.rules.length+1).bits

/-- Actual input cells; the two blank margins are formed by traversing supplied
clock fuel. Input bits use the reserved 0/1 symbols, blank is reserved symbol 2. -/
def rawInputCells (word : List Bool) (clock : List Unit) : List (List Bool) × ℕ :=
  let blanks := rawMap (fun _ : Unit => ([false,true],3)) clock
  let input := rawMap (fun b => (if b then [true] else [],3)) word
  (blanks.1++input.1++blanks.1++[[false,true]],
    blanks.2+input.2+3*blanks.1.length+2*input.1.length+8)

def rawWindowFuel (word : List Bool) (clock : List Unit) : List Unit × ℕ :=
  let input := rawMap (fun _ : Bool => ((),2)) word
  (input.1++clock++clock++[()],input.2+3*input.1.length+3*clock.length+8)

/-- The executable constructor takes unary clock fuel. Its construction from a
fixed polynomial of input length is a separate charged front-end obligation. -/
def constructRaw (constants : MachineConstants) (word : List Bool) (clock : List Unit) : Encoding.Raw × ℕ :=
  let t := FPTASCostSeeds.countBits clock
  let wfuel := rawWindowFuel word clock
  let w := FPTASCostSeeds.countBits wfuel.1
  let rows := enumerateBits (()::clock)
  let steps := enumerateBits clock
  let cells := enumerateBits wfuel.1
  let initialCells := rawInputCells word clock
  let d : RawDimensions := ⟨constants.q,constants.g,w.1,t.1,constants.r⟩
  let formula := rawAppend (rawShape d rows.1 steps.1 constants.states cells.1 constants.symbols constants.choices)
    (rawAppend (rawInitial d constants.start cells.1 initialCells.1)
      (rawAppend (rawAccept d t.1 constants.accepting)
        (rawTransitions d steps.1 constants.states cells.1 constants.symbols constants.accepting constants.choices constants.rules)))
  let catalogued := Encoding.catalogueBits formula.1
  (catalogued.1,t.2+wfuel.2+w.2+rows.2+steps.2+cells.2+initialCells.2+formula.2+catalogued.2+32)

def constructBits (constants : MachineConstants) (word : List Bool) (clock : List Unit) : List Bool × ℕ :=
  let raw := constructRaw constants word clock
  let output := Encoding.emit raw.1
  (output.1,raw.2+output.2+4)

end BalancedAssortments.CookLevin
