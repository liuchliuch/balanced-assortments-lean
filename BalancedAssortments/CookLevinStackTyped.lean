import BalancedAssortments.CookLevinStackTableauFields

/-! Typed clause/formula templates with exact byte-stream denotation. -/
noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF StackBuilder

inductive ClauseCode
  | empty
  | literal (l : L)
  | seq (a b : ClauseCode)
  | branch (a b : E) (yes no : ClauseCode)
  | each (i : Fin 9) (fuel : ℕ) (f t : ClauseCode)
inductive FormulaCode
  | empty
  | clause (c : ClauseCode)
  | seq (a b : FormulaCode)
  | branch (a b : E) (yes no : FormulaCode)
  | each (i : Fin 9) (fuel : ℕ) (f t : FormulaCode)

def collect {α : Type*} (f : ℕ → Bool → List α) : ℕ → List Bool → List α
  | _,[] => []
  | i,b::bs => collect f (i+1) bs++f i b

def ClauseCode.lower : ClauseCode → B
  | .empty => .skip
  | .literal l => .literal l.1 l.2
  | .seq a b => .seq a.lower b.lower
  | .branch a b y n => .branch a b y.lower n.lower
  | .each i f a b => .each i f a.lower b.lower

def ClauseCode.eval : ClauseCode → (Fin 9 → List Bool) → (ℕ → List Bool) → Encoding.BitClause
  | .empty,_,_ => []
  | .literal l,e,_ => [evalLiteral e l]
  | .seq a b,e,f => b.eval e f++a.eval e f
  | .branch a b y n,e,f => if ComplexityTimeBinary.value (a.run e).1≤ComplexityTimeBinary.value (b.run e).1 then y.eval e f else n.eval e f
  | .each i src a b,e,f => collect (fun j (bit : Bool) => if bit then b.eval (Function.update e i (StackCount.counterBits j)) f else a.eval (Function.update e i (StackCount.counterBits j)) f) 0 (f src)

def FormulaCode.lower : FormulaCode → B
  | .empty => .skip
  | .clause c => dynamicClause c.lower
  | .seq a b => .seq a.lower b.lower
  | .branch a b y n => .branch a b y.lower n.lower
  | .each i f a b => .each i f a.lower b.lower

def FormulaCode.eval : FormulaCode → (Fin 9 → List Bool) → (ℕ → List Bool) → Encoding.BitFormula
  | .empty,_,_ => []
  | .clause c,e,f => [c.eval e f]
  | .seq a b,e,f => b.eval e f++a.eval e f
  | .branch a b y n,e,f => if ComplexityTimeBinary.value (a.run e).1≤ComplexityTimeBinary.value (b.run e).1 then y.eval e f else n.eval e f
  | .each i src a b,e,f => collect (fun j (bit : Bool) => if bit then b.eval (Function.update e i (StackCount.counterBits j)) f else a.eval (Function.update e i (StackCount.counterBits j)) f) 0 (f src)

def literalFields (ls : Encoding.BitClause) : List (List Bool) :=
  ls.flatMap (fun l => [[l.positive],l.labelBits])
def formulaPrefix (F : Encoding.BitFormula) : List (List Bool) :=
  F.flatMap (fun c => [true]::Encoding.clauseFields c)
lemma literalFields_append (a b : Encoding.BitClause) : literalFields (a++b)=literalFields a++literalFields b := by simp [literalFields]
lemma formulaPrefix_append (a b : Encoding.BitFormula) : formulaPrefix (a++b)=formulaPrefix a++formulaPrefix b := by simp [formulaPrefix]
lemma literalFields_clause (c : Encoding.BitClause) : literalFields c++[[]]=Encoding.clauseFields c := by
  induction c with
  | nil => rfl
  | cons l ls ih => simpa [literalFields,Encoding.clauseFields,List.append_assoc] using congrArg (fun xs => [l.positive]::l.labelBits::xs) ih
lemma formulaPrefix_formula (F : Encoding.BitFormula) : formulaPrefix F++[[false]]=Encoding.formulaFields F := by
  induction F with
  | nil => rfl
  | cons c cs ih => simp [formulaPrefix,Encoding.formulaFields,List.append_assoc,← ih]

lemma fields_collect {α : Type*} (emit : List α → List (List Bool))
    (h0 : emit []=[]) (hadd : ∀ a b,emit (a++b)=emit a++emit b)
    (f : ℕ → Bool → List α) (i : ℕ) (bs : List Bool) :
    loopFields (fun j b => emit (f j b)) i bs=emit (collect f i bs) := by
  induction bs generalizing i with
  | nil => exact h0.symm
  | cons b bs ih => simp [loopFields,collect,ih,hadd]

theorem ClauseCode.fields_lower (p : ClauseCode) (e : Fin 9 → List Bool) (f : ℕ → List Bool) :
    fields p.lower e f=literalFields (p.eval e f) := by
  induction p generalizing e with
  | empty => rfl
  | literal l => simp [lower,fields,eval,literalFields,evalLiteral]
  | seq a b iha ihb => simp [lower,fields,eval,iha,ihb,literalFields_append]
  | branch a b y n ihy ihn => simp only [lower,fields,eval];split <;> simp_all
  | each i src a b iha ihb =>
    simp only [lower,fields,eval]
    have he : (fun j (bit : Bool) => if bit then fields b.lower (Function.update e i (StackCount.counterBits j)) f else fields a.lower (Function.update e i (StackCount.counterBits j)) f)=
      (fun j (bit : Bool) => literalFields (if bit then b.eval (Function.update e i (StackCount.counterBits j)) f else a.eval (Function.update e i (StackCount.counterBits j)) f)) := by funext j bit;cases bit <;> simp [iha,ihb]
    rw [he]
    exact fields_collect literalFields rfl literalFields_append _ _ _

theorem FormulaCode.fields_lower (p : FormulaCode) (e : Fin 9 → List Bool) (f : ℕ → List Bool) :
    fields p.lower e f=formulaPrefix (p.eval e f) := by
  induction p generalizing e with
  | empty => rfl
  | clause c => simp [lower,dynamicClause,fields,ClauseCode.fields_lower,eval,formulaPrefix,literalFields_clause]
  | seq a b iha ihb => simp [lower,fields,eval,iha,ihb,formulaPrefix_append]
  | branch a b y n ihy ihn => simp only [lower,fields,eval];split <;> simp_all
  | each i src a b iha ihb =>
    simp only [lower,fields,eval]
    have he : (fun j (bit : Bool) => if bit then fields b.lower (Function.update e i (StackCount.counterBits j)) f else fields a.lower (Function.update e i (StackCount.counterBits j)) f)=
      (fun j (bit : Bool) => formulaPrefix (if bit then b.eval (Function.update e i (StackCount.counterBits j)) f else a.eval (Function.update e i (StackCount.counterBits j)) f)) := by funext j bit;cases bit <;> simp [iha,ihb]
    rw [he]
    exact fields_collect formulaPrefix rfl formulaPrefix_append _ _ _

end BalancedAssortments.CookLevin.StackTableau
