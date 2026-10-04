import BalancedAssortments.CookLevinStackClauses
import BalancedAssortments.CookLevinStackTest
import BalancedAssortments.CookLevinStackCount

/-! A finite streaming-CNF builder language. Loops lexically bind one binary
index and restore it afterwards. Every constructor compiles to the already
checked primitive stack control graphs; full compiler correctness is separate. -/
noncomputable section
namespace BalancedAssortments.CookLevin.StackBuilder
open NPCNF NPStack NPStack.Structured ComplexityTimeBinary

inductive Builder (n : ℕ)
  | skip
  | field (bits : List Bool)
  | literal (address : BitExpr n) (sign : Bool)
  | seq (a b : Builder n)
  | branch (a b : BitExpr n) (yes no : Builder n)
  | each (index : Fin n) (fuel : ℕ) (onFalse onTrue : Builder n)

/-- Prefix produced by iterating a physical Boolean fuel list. Later emissions
are prepended, so no uncharged traversal of an existing output suffix occurs. -/
def loopValue (f : ℕ → Bool → List Bool) : ℕ → List Bool → List Bool
  | _,[] => []
  | i,b::bs => loopValue f (i+1) bs++f i b

def value {n : ℕ} : Builder n → (Fin n → List Bool) → (ℕ → List Bool) → List Bool
  | .skip,_,_ => []
  | .field bits,_,_ => Encoding.encodePayload bits
  | .literal e sign,env,_ => Encoding.encodePayload [sign]++Encoding.encodePayload (e.run env).1
  | .seq a b,env,fuel => value b env fuel++value a env fuel
  | .branch a b yes no,env,fuel =>
    if ComplexityTimeBinary.value (a.run env).1≤ComplexityTimeBinary.value (b.run env).1
    then value yes env fuel else value no env fuel
  | .each index source f t,env,fuel =>
    loopValue (fun i bit => if bit then value t (Function.update env index (StackCount.counterBits i)) fuel
      else value f (Function.update env index (StackCount.counterBits i)) fuel) 0 (fuel source)

def depth {n : ℕ} : Builder n → ℕ
  | .skip => 0
  | .field _ => 0
  | .literal _ _ => 0
  | .seq a b => max (depth a) (depth b)
  | .branch _ _ a b => max (depth a) (depth b)
  | .each _ _ a b => 1+max (depth a) (depth b)

def workSize {n : ℕ} : Builder n → ℕ
  | .skip => 3
  | .field _ => 3
  | .literal e _ => StackIndices.slots e
  | .seq a b => max (workSize a) (workSize b)
  | .branch a b yes no => max (StackTest.testSlots a b) (max (workSize yes) (workSize no))
  | .each i _ a b => max (StackIndices.slots (StackAssign.incrementExpr i)) (max (workSize a) (workSize b))

def fuelRefs {n : ℕ} : Builder n → List ℕ
  | .skip => []
  | .field _ => []
  | .literal _ _ => []
  | .seq a b => fuelRefs a++fuelRefs b
  | .branch _ _ a b => fuelRefs a++fuelRefs b
  | .each _ source a b => source::(fuelRefs a++fuelRefs b)

def lexicalFor {n : ℕ} (work privateBase : ℕ) (index : Fin n) (fuel : ℕ)
    (bodyFalse bodyTrue : Block ℕ) : Block ℕ :=
  .seq (.atom (copyAtom index.val (privateBase+1) (privateBase+2)))
    (.seq (clearStack index.val)
      (.seq (.atom (copyAtom fuel (privateBase+1) privateBase))
        (.seq (.loop privateBase (.seq bodyFalse (StackAssign.increment work index))
          (.seq bodyTrue (StackAssign.increment work index)))
          (.seq (clearStack index.val)
            (.seq (.atom (copyAtom (privateBase+2) (privateBase+1) index.val))
              (clearStack (privateBase+2)))))))

def compile {n : ℕ} (work privateBase out : ℕ) : Builder n → Block ℕ
  | .skip => .skip
  | .field bits => StackEmit.emitConst work out bits
  | .literal e sign => StackEmit.emitLiteral work out e sign
  | .seq a b => .seq (compile work privateBase out a) (compile work privateBase out b)
  | .branch a b yes no => StackTest.ifLE work a b (compile work privateBase out yes) (compile work privateBase out no)
  | .each index fuel f t => lexicalFor work privateBase index fuel
      (compile work (privateBase+3) out f) (compile work (privateBase+3) out t)

noncomputable def timePolynomial {n : ℕ} : Builder n → Polynomial ℕ
  | .skip => 1
  | .field bits => Polynomial.C (9*bits.length+8)
  | .literal e _ => StackEmit.emitLiteralTime e
  | .seq a b => timePolynomial a+timePolynomial b+1
  | .branch a b yes no => StackTest.testTime a b+timePolynomial yes+timePolynomial no+3
  | .each i _ a b =>
    Polynomial.X*(timePolynomial a+timePolynomial b+StackAssign.assignTime (StackAssign.incrementExpr i)+16)+
      64*(Polynomial.X+1)+64

/-- Read-only fuel references are outside scalar fields/output and below all
private loop registers. These static checks will be discharged for the tableau. -/
def GoodFuel {n : ℕ} (p : Builder n) (privateBase out : ℕ) : Prop :=
  ∀ r∈fuelRefs p,n≤r ∧ r<privateBase ∧ r≠out

def fuelBounds {n : ℕ} (p : Builder n) (fuel : ℕ → List Bool) (B : ℕ) : Prop :=
  ∀ r∈fuelRefs p,(fuel r).length+1≤B

lemma value_congr {n : ℕ} (p : Builder n) {env env' : Fin n → List Bool} {fuel fuel' : ℕ → List Bool}
    (he : env=env') (hf : ∀ r∈fuelRefs p,fuel r=fuel' r) : value p env fuel=value p env' fuel' := by
  subst env'
  induction p generalizing env with
  | skip => rfl
  | field bits => rfl
  | literal e sign => rfl
  | seq a b iha ihb =>
    simp only [value]
    rw [iha (fun r hr => hf r (List.mem_append_left _ hr)),ihb (fun r hr => hf r (List.mem_append_right _ hr))]
  | branch a b yes no ihy ihn =>
    simp only [value]
    split
    · exact ihy (fun r hr => hf r (List.mem_append_left _ hr))
    · exact ihn (fun r hr => hf r (List.mem_append_right _ hr))
  | each i source a b iha ihb =>
    simp only [value]
    rw [hf source (by simp [fuelRefs])]
    congr 1
    funext j bit
    cases bit
    · exact iha (fun r hr => hf r (by simp [fuelRefs,hr]))
    · exact ihb (fun r hr => hf r (by simp [fuelRefs,hr]))

end BalancedAssortments.CookLevin.StackBuilder
