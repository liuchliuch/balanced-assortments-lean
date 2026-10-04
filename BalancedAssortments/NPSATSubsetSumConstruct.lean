import BalancedAssortments.NPSATSubsetSumBits

namespace BalancedAssortments.NPSATSubsetSum
open ComplexityTimeBinary NPCNF.Encoding

/-- One bit-vector digit per actual catalog cell, with semantic binary equality. -/
def variableColumns (label : List Bool) : List (List Bool) → List (List Bool) × ℕ
  | [] => ([],1)
  | x::xs =>
    let eq := compareBits x label
    let tail := variableColumns label xs
    ((if eq.1=.eq then [true] else [])::tail.1,eq.2+tail.2+6)

lemma variableColumns_value (label : List Bool) (xs : List (List Bool)) :
    (variableColumns label xs).1.map value = xs.map (fun x => if value x=value label then 1 else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [variableColumns,List.map_cons,ih]
    congr 1
    by_cases h : (compareBits x label).1=.eq
    · simp [h,(compare_eq_iff _ _).mp h,value]
    · have hn : value x≠value label := fun he => h ((compare_eq_iff _ _).mpr he)
      simp [h,hn,value]

/-- Clause digits count occurrences, including repetitions. -/
def clauseColumns (label : List Bool) (polarity : Bool) : BitFormula → List (List Bool) × ℕ
  | [] => ([],1)
  | c::cs =>
    let digit := occurrenceBits label polarity c
    let tail := clauseColumns label polarity cs
    (digit.1::tail.1,digit.2+tail.2+4)

lemma clauseColumns_value (label : List Bool) (polarity : Bool) (F : BitFormula) :
    (clauseColumns label polarity F).1.map value = F.map (occurrenceCount (value label) polarity) := by
  induction F <;> simp [clauseColumns,occurrenceBits_value, *]

def variableItem (catalog : List (List Bool)) (F : BitFormula) (label : List Bool) (polarity : Bool) :
    List Bool × ℕ :=
  let vars := variableColumns label catalog
  let clauses := clauseColumns label polarity F
  let packed := packBits (vars.1++clauses.1)
  (packed.1,vars.2+clauses.2+packed.2+vars.1.length+6)

lemma variableItem_value (catalog : List (List Bool)) (F : BitFormula) (label : List Bool) (polarity : Bool) :
    value (variableItem catalog F label polarity).1 = Nat.ofDigits 10
      (catalog.map (fun x => if value x=value label then 1 else 0)++F.map (occurrenceCount (value label) polarity)) := by
  simp only [variableItem,packBits_value,List.map_append,variableColumns_value,clauseColumns_value]

def variableItems (catalog : List (List Bool)) (F : BitFormula) : List (List Bool) → List (List Bool) × ℕ
  | [] => ([],1)
  | label::labels =>
    let no := variableItem catalog F label false
    let yes := variableItem catalog F label true
    let tail := variableItems catalog F labels
    (no.1::yes.1::tail.1,no.2+yes.2+tail.2+6)

lemma variableItems_value (catalog : List (List Bool)) (F : BitFormula) (labels : List (List Bool)) :
    (variableItems catalog F labels).1.map value = labels.flatMap (fun label =>
      [value (variableItem catalog F label false).1,value (variableItem catalog F label true).1]) := by
  induction labels <;> simp [variableItems, *]

/-- Structural zero padding. It never expands a numeric header. -/
def zeroColumns {α : Type*} : List α → List (List Bool) × ℕ
  | [] => ([],1)
  | _::xs => let tail := zeroColumns xs; ([]::tail.1,tail.2+3)

lemma zeroColumns_eq {α : Type*} (xs : List α) : (zeroColumns xs).1 = List.replicate xs.length [] := by
  induction xs <;> simp [zeroColumns,List.replicate_succ, *]
lemma zeroColumns_cost {α : Type*} (xs : List α) : (zeroColumns xs).2=3*xs.length+1 := by
  induction xs <;> simp [zeroColumns,List.replicate_succ, *] <;> omega

def prependZero : List (List (List Bool)) → List (List (List Bool)) × ℕ
  | [] => ([],1)
  | row::rows => let tail := prependZero rows; (([]::row)::tail.1,tail.2+4)

lemma prependZero_eq (rows : List (List (List Bool))) : (prependZero rows).1=rows.map ([]::·) := by
  induction rows <;> simp [prependZero, *]

/-- Two slack rows per actual clause, carrying clause digits one and two. -/
def slackColumns {α : Type*} : List α → List (List (List Bool)) × ℕ
  | [] => ([],1)
  | _::xs =>
    let zeroes := zeroColumns xs
    let tail := slackColumns xs
    let shifted := prependZero tail.1
    (([true]::zeroes.1)::([false,true]::zeroes.1)::shifted.1,
      zeroes.2+tail.2+shifted.2+8)

/-- Add the variable-column zero padding and pack every clause slack row. -/
def packSlack (padding : List (List Bool)) : List (List (List Bool)) → List (List Bool) × ℕ
  | [] => ([],1)
  | row::rows =>
    let packed := packBits (padding++row)
    let tail := packSlack padding rows
    (packed.1::tail.1,packed.2+tail.2+padding.length+4)

lemma packSlack_value (padding : List (List Bool)) (rows : List (List (List Bool))) :
    (packSlack padding rows).1.map value = rows.map (fun row => Nat.ofDigits 10 ((padding++row).map value)) := by
  induction rows <;> simp [packSlack,packBits_value, *]

def targetColumns {α β : Type*} (catalog : List α) (F : List β) : List (List Bool) × ℕ :=
  (catalog.map (fun _ => [true])++F.map (fun _ => [false,false,true]),3*catalog.length+2*F.length+4)

/-- Full raw integer gadget. The empty zero-dimensional case is handled by the
outer total reduction, which emits the fixed positive yes-instance. -/
def construct (input : Raw) : (List Bool × List (List Bool)) × ℕ :=
  let vars := variableItems input.catalog input.formula input.catalog
  let zeroes := zeroColumns input.catalog
  let slack := slackColumns input.formula
  let packed := packSlack zeroes.1 slack.1
  let target := targetColumns input.catalog input.formula
  let total := packBits target.1
  ((total.1,vars.1++packed.1),vars.2+zeroes.2+slack.2+packed.2+target.2+total.2+vars.1.length+12)

end BalancedAssortments.NPSATSubsetSum
