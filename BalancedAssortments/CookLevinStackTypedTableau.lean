import BalancedAssortments.CookLevinStackTyped

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau.Typed
open NPMachine NPCNF

def literals : List L → ClauseCode
  | [] => .empty
  | l::ls => .seq (literals ls) (.literal l)
def clause (ls : List L) : FormulaCode := .clause (literals ls)
def dynamicClause (p : ClauseCode) : FormulaCode := .clause p
def all : List FormulaCode → FormulaCode
  | [] => .empty
  | b::bs => .seq b (all bs)
def loop (i : Fin 9) (fuel : ℕ) (p : FormulaCode) : FormulaCode := .each i fuel p p
def cloop (i : Fin 9) (fuel : ℕ) (p : ClauseCode) : ClauseCode := .each i fuel p p
def eqBranch (a b : E) (yes no : ClauseCode) : ClauseCode := .branch a b (.branch b a yes no) no
def fixedExactlyOne (es : List E) : FormulaCode :=
  .seq (clause (es.map (fun e => (e,true))))
    (all (es.zipIdx |>.flatMap (fun pair =>
      (es.drop (pair.2+1)).map (fun e => clause [(pair.1,false),(e,false)]))))

def shape (M : Machine) : FormulaCode :=
  .seq
    (loop 5 12 (all [
      fixedExactlyOne ((List.range (M.stateExtra+1)).map (fun s => state (x 5) (c s))),
      dynamicClause (cloop 6 13 (.literal (head (x 5) (x 6),true))),
      loop 6 13 (loop 8 13 (.branch (succ (x 6)) (x 8)
        (clause [(head (x 5) (x 6),false),(head (x 5) (x 8),false)]) .empty)),
      loop 6 13 (fixedExactlyOne ((List.range (M.symbolExtra+3)).map
        (fun a => tape (x 5) (x 6) (c a))))]))
    (loop 5 11 (fixedExactlyOne ((List.range (M.rules.length+1)).map
      (fun r => choice (x 5) (c r)))))

def accepting (M : Machine) (t : E) : List L :=
  ((List.finRange (M.stateExtra+1)).filter M.accepting).map (fun s => (state t (c s.val),true))
def initial (M : Machine) : FormulaCode := all [
  clause [(state (c 0) (c M.start.val),true)],
  clause [(head (c 0) (x 3),true)],
  loop 6 11 (clause [(tape (c 0) (x 6) (c 2),true)]),
  .each 8 9 (clause [(tape (c 0) (plus (x 3) (x 8)) (c 0),true)])
    (clause [(tape (c 0) (plus (x 3) (x 8)) (c 1),true)]),
  loop 6 12 (clause [(tape (c 0) (plus (plus (x 3) (x 7)) (x 6)) (c 2),true)])]

def moveTarget (m : Move) : ClauseCode :=
  let emit : ClauseCode := .literal (head (succ (x 5)) (x 8),true)
  match m with
  | .stay => eqBranch (x 8) (x 6) emit .empty
  | .right => eqBranch (x 8) (succ (x 6)) emit .empty
  | .left => eqBranch (succ (x 8)) (x 6) emit .empty

def ruleBody (M : Machine) (j : ℕ) (r : Rule M.stateExtra M.symbolExtra) : FormulaCode :=
  let guard : L := (choice (x 5) (c (j+1)),false)
  all [clause [guard,(state (x 5) (c r.source.val),true)],
    clause [guard,(state (succ (x 5)) (c r.target.val),true)],
    loop 6 13 (all [
      clause [guard,(head (x 5) (x 6),false),(tape (x 5) (x 6) (c r.read.val),true)],
      clause [guard,(head (x 5) (x 6),false),(tape (succ (x 5)) (x 6) (c r.write.val),true)],
      dynamicClause (.seq (cloop 8 13 (moveTarget r.move))
        (literals [guard,(head (x 5) (x 6),false)]))]),
    loop 6 13 (all ((List.range (M.symbolExtra+3)).map (fun a =>
      clause [guard,(head (x 5) (x 6),true),(tape (x 5) (x 6) (c a),false),
        (tape (succ (x 5)) (x 6) (c a),true)])))]

def haltBody (M : Machine) : FormulaCode :=
  let guard : L := (choice (x 5) (c 0),false)
  all [clause (guard::accepting M (x 5)),
    all ((List.range (M.stateExtra+1)).map (fun s =>
      clause [guard,(state (x 5) (c s),false),(state (succ (x 5)) (c s),true)])),
    loop 6 13 (clause [guard,(head (x 5) (x 6),false),(head (succ (x 5)) (x 6),true)]),
    loop 6 13 (all ((List.range (M.symbolExtra+3)).map (fun a =>
      clause [guard,(tape (x 5) (x 6) (c a),false),(tape (succ (x 5)) (x 6) (c a),true)])))]

def transitions (M : Machine) : FormulaCode :=
  loop 5 11 (.seq (haltBody M) (all (M.rules.zipIdx.map (fun r => ruleBody M r.2 r.1))))

def formula (M : Machine) : FormulaCode := all [shape M,initial M,clause (accepting M (x 3)),transitions M]


end BalancedAssortments.CookLevin.StackTableau.Typed
