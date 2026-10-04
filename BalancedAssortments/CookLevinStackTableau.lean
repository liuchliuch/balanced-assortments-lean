import BalancedAssortments.CookLevinStackBuilder
import BalancedAssortments.CookLevinRawConstructor

/-! Fixed finite tableau templates. All varying indices are physical counted
loops; fixed machine alphabets and transition tables are unrolled in the code. -/
noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPMachine NPCNF StackBuilder
abbrev E := BitExpr 9
abbrev B := Builder 9
abbrev L := E × Bool

def c (n : ℕ) : E := .constant n.bits
def x (i : Fin 9) : E := .input i
def plus (a b : E) : E := .add a b
def times (a b : E) : E := .mul a b
def succ (a : E) : E := plus a (c 1)
def state (t s : E) : E := plus s (times (x 0) t)
def head (t p : E) : E := plus (times (succ (x 3)) (x 0)) (plus p (times (x 2) t))
def tape (t p a : E) : E :=
  plus (plus (times (succ (x 3)) (x 0)) (times (succ (x 3)) (x 2)))
    (plus (plus a (times (x 1) p)) (times (times (x 2) (x 1)) t))
def choice (t r : E) : E :=
  plus (plus (times (succ (x 3)) (x 0)) (times (succ (x 3)) (x 2)))
    (plus (times (succ (x 3)) (times (x 2) (x 1))) (plus r (times (x 4) t)))

/-- Executed in reverse order to retain the displayed literal order. -/
def literals : List L → B
  | [] => .skip
  | l::ls => .seq (literals ls) (.literal l.1 l.2)
def clause (ls : List L) : B := .seq (.field []) (.seq (literals ls) (.field [true]))
def dynamicClause (body : B) : B := .seq (.field []) (.seq body (.field [true]))
def all : List B → B
  | [] => .skip
  | b::bs => .seq b (all bs)
def loop (i : Fin 9) (fuel : ℕ) (body : B) : B := .each i fuel body body

def eqBranch (a b : E) (yes no : B) : B := .branch a b (.branch b a yes no) no

def fixedExactlyOne (es : List E) : B :=
  .seq (clause (es.map (fun e => (e,true))))
    (all (es.zipIdx |>.flatMap (fun pair =>
      (es.drop (pair.2+1)).map (fun e => clause [(pair.1,false),(e,false)]))))

def shape (M : Machine) : B :=
  .seq
    (loop 5 12 (all [
      fixedExactlyOne ((List.range (M.stateExtra+1)).map (fun s => state (x 5) (c s))),
      dynamicClause (loop 6 13 (.literal (head (x 5) (x 6)) true)),
      loop 6 13 (loop 8 13 (.branch (succ (x 6)) (x 8)
        (clause [(head (x 5) (x 6),false),(head (x 5) (x 8),false)]) .skip)),
      loop 6 13 (fixedExactlyOne ((List.range (M.symbolExtra+3)).map
        (fun a => tape (x 5) (x 6) (c a))))]))
    (loop 5 11 (fixedExactlyOne ((List.range (M.rules.length+1)).map
      (fun r => choice (x 5) (c r)))))

def accepting (M : Machine) (t : E) : List L :=
  ((List.finRange (M.stateExtra+1)).filter M.accepting).map (fun s => (state t (c s.val),true))
def initial (M : Machine) : B := all [
  clause [(state (c 0) (c M.start.val),true)],
  clause [(head (c 0) (x 3),true)],
  loop 6 11 (clause [(tape (c 0) (x 6) (c 2),true)]),
  .each 8 9 (clause [(tape (c 0) (plus (x 3) (x 8)) (c 0),true)])
    (clause [(tape (c 0) (plus (x 3) (x 8)) (c 1),true)]),
  loop 6 12 (clause [(tape (c 0) (plus (plus (x 3) (x 7)) (x 6)) (c 2),true)])]

def moveTarget (m : Move) : B :=
  let emit := .literal (head (succ (x 5)) (x 8)) true
  match m with
  | .stay => eqBranch (x 8) (x 6) emit .skip
  | .right => eqBranch (x 8) (succ (x 6)) emit .skip
  | .left => eqBranch (succ (x 8)) (x 6) emit .skip

def ruleBody (M : Machine) (j : ℕ) (r : Rule M.stateExtra M.symbolExtra) : B :=
  let guard : L := (choice (x 5) (c (j+1)),false)
  all [clause [guard,(state (x 5) (c r.source.val),true)],
    clause [guard,(state (succ (x 5)) (c r.target.val),true)],
    loop 6 13 (all [
      clause [guard,(head (x 5) (x 6),false),(tape (x 5) (x 6) (c r.read.val),true)],
      clause [guard,(head (x 5) (x 6),false),(tape (succ (x 5)) (x 6) (c r.write.val),true)],
      dynamicClause (.seq (loop 8 13 (moveTarget r.move))
        (literals [guard,(head (x 5) (x 6),false)]))]),
    loop 6 13 (all ((List.range (M.symbolExtra+3)).map (fun a =>
      clause [guard,(head (x 5) (x 6),true),(tape (x 5) (x 6) (c a),false),
        (tape (succ (x 5)) (x 6) (c a),true)])))]

def haltBody (M : Machine) : B :=
  let guard : L := (choice (x 5) (c 0),false)
  all [clause (guard::accepting M (x 5)),
    all ((List.range (M.stateExtra+1)).map (fun s =>
      clause [guard,(state (x 5) (c s),false),(state (succ (x 5)) (c s),true)])),
    loop 6 13 (clause [guard,(head (x 5) (x 6),false),(head (succ (x 5)) (x 6),true)]),
    loop 6 13 (all ((List.range (M.symbolExtra+3)).map (fun a =>
      clause [guard,(tape (x 5) (x 6) (c a),false),(tape (succ (x 5)) (x 6) (c a),true)])))]

def transitions (M : Machine) : B :=
  loop 5 11 (.seq (haltBody M) (all (M.rules.zipIdx.map (fun r => ruleBody M r.2 r.1))))

def formula (M : Machine) : B := all [shape M,initial M,clause (accepting M (x 3)),transitions M]

/-- Full raw grammar: explicit catalogue, separator, clauses, terminator.
Catalogue order is descending because emissions prepend; numeric labels remain
exactly the distinct interval [0,V). -/
def program (M : Machine) : B :=
  .seq (.field [false]) (.seq (formula M) (.seq (.field [false])
    (loop 8 14 (.seq (.literal (x 8) true) .skip))))

end BalancedAssortments.CookLevin.StackTableau
