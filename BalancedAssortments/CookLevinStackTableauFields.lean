import BalancedAssortments.CookLevinStackTableau

/-! Exact field-stream meaning of the finite template language. This layer
accounts for prepend order before identifying the resulting logical clauses. -/
noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF StackBuilder

def loopFields (f : ℕ → Bool → List (List Bool)) : ℕ → List Bool → List (List Bool)
  | _,[] => []
  | i,b::bs => loopFields f (i+1) bs++f i b

def fields : B → (Fin 9 → List Bool) → (ℕ → List Bool) → List (List Bool)
  | .skip,_,_ => []
  | .field bits,_,_ => [bits]
  | .literal e sign,env,_ => [[sign],(e.run env).1]
  | .seq a b,env,fuel => fields b env fuel++fields a env fuel
  | .branch a b yes no,env,fuel =>
    if ComplexityTimeBinary.value (a.run env).1≤ComplexityTimeBinary.value (b.run env).1
    then fields yes env fuel else fields no env fuel
  | .each index source f t,env,fuel =>
    loopFields (fun i bit => if bit then fields t (Function.update env index (StackCount.counterBits i)) fuel
      else fields f (Function.update env index (StackCount.counterBits i)) fuel) 0 (fuel source)

lemma encode_loopFields (f : ℕ → Bool → List (List Bool)) (i : ℕ) (bs : List Bool) :
    Encoding.encodeFields (loopFields f i bs)=
      loopValue (fun j b => Encoding.encodeFields (f j b)) i bs := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih => simp [loopFields,loopValue,StackEmit.encodeFields_append,ih]

theorem value_fields (p : B) (env : Fin 9 → List Bool) (fuel : ℕ → List Bool) :
    value p env fuel=Encoding.encodeFields (fields p env fuel) := by
  induction p generalizing env with
  | skip => rfl
  | field bits => simp [value,fields,Encoding.encodeFields]
  | literal e sign => simp [value,fields,Encoding.encodeFields]
  | seq a b iha ihb => simp [value,fields,iha,ihb,StackEmit.encodeFields_append]
  | branch a b y n ihy ihn => simp only [value,fields];split <;> simp_all
  | each index source f t ihf iht =>
    simp only [value,fields,encode_loopFields]
    congr 1
    funext j bit
    cases bit <;> simp [ihf,iht]

def evalLiteral (env : Fin 9 → List Bool) (l : L) : Encoding.BitLiteral :=
  ⟨(l.1.run env).1,l.2⟩
lemma literals_fields (ls : List L) (env : Fin 9 → List Bool) (fuel : ℕ → List Bool) :
    fields (literals ls) env fuel=(ls.map (evalLiteral env)).flatMap
      (fun l => [[l.positive],l.labelBits]) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [literals,fields,ih,evalLiteral,List.append_assoc]
lemma clause_fields (ls : List L) (env : Fin 9 → List Bool) (fuel : ℕ → List Bool) :
    fields (clause ls) env fuel=[true]::Encoding.clauseFields (ls.map (evalLiteral env)) := by
  simp only [clause,fields,literals_fields]
  have h : ∀ cs : Encoding.BitClause,cs.flatMap (fun l => [[l.positive],l.labelBits])++[[]]=Encoding.clauseFields cs := by
    intro cs
    induction cs with
    | nil => rfl
    | cons l cs ih => simpa [Encoding.clauseFields,List.append_assoc] using congrArg (fun xs => [l.positive]::l.labelBits::xs) ih
  simpa only [List.singleton_append,List.append_assoc] using congrArg (fun xs => [true]::xs) (h (ls.map (evalLiteral env)))

lemma loopFields_replicate (f : ℕ → Bool → List (List Bool)) (i n : ℕ) (b : Bool) :
    loopFields f i (List.replicate n b)=((List.range n).reverse.flatMap (fun j => f (i+j) b)) := by
  induction n generalizing i with
  | zero => simp [loopFields]
  | succ n ih =>
    simp only [List.replicate_succ,loopFields,ih,List.range_succ_eq_map,List.reverse_cons,
      ← List.map_reverse,List.flatMap_append,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    congr 1
    congr 1
    funext j
    congr 1
    omega

end BalancedAssortments.CookLevin.StackTableau
