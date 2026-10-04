import BalancedAssortments.CookLevinSerializedSize

/-! Binary labels and structural unary loop fuel for a charged tableau generator.
Decoded natural values appear only in refinement theorems. -/
namespace BalancedAssortments.CookLevin
open NPCNF NPMachine ComplexityTimeBinary

@[simp] lemma index_state {q g W T R : ℕ} (t : Fin (T+1)) (s : Fin q) :
    index (Var.state t s : Var q g W T R)=s.val+q*t.val := rfl
@[simp] lemma index_head {q g W T R : ℕ} (t : Fin (T+1)) (p : Fin W) :
    index (Var.head t p : Var q g W T R)=(T+1)*q+(p.val+W*t.val) := rfl
@[simp] lemma index_tape {q g W T R : ℕ} (t : Fin (T+1)) (p : Fin W) (a : Fin g) :
    index (Var.tape t p a : Var q g W T R)=
      ((T+1)*q+(T+1)*W)+(a.val+g*p.val+(W*g)*t.val) := rfl
@[simp] lemma index_choice {q g W T R : ℕ} (t : Fin T) (r : Fin R) :
    index (Var.choice t r : Var q g W T R)=
      ((T+1)*q+(T+1)*W)+((T+1)*(W*g)+(r.val+R*t.val)) := rfl

/-- Structural enumeration. Each successor label is formed by the actual ripple
carry circuit. Padded encodings remain valid binary labels. -/
def enumerateFrom (start : List Bool) : List Unit → List (List Bool) × ℕ
  | [] => ([],1)
  | _::fuel =>
    let next := addCarry start [] true
    let tail := enumerateFrom next.1 fuel
    (start::tail.1,next.2+tail.2+4)

lemma enumerateFrom_decode (start : List Bool) (fuel : List Unit) :
    (enumerateFrom start fuel).1.map value=(List.range fuel.length).map (fun i => value start+i) := by
  induction fuel generalizing start with
  | nil => simp [enumerateFrom]
  | cons u fuel ih =>
    simp only [enumerateFrom,List.map_cons,ih,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [addCarry_value,value,Bool.toNat_true,Nat.add_zero,Nat.zero_add]
    congr 1
    apply List.map_congr_left
    intro i hi
    simp [Function.comp_def]
    omega

lemma enumerateFrom_length (start : List Bool) (fuel : List Unit) :
    (enumerateFrom start fuel).1.length=fuel.length := by
  induction fuel generalizing start <;> simp_all [enumerateFrom]

lemma enumerateFrom_width (start : List Bool) (fuel : List Unit) :
    ∀ x∈(enumerateFrom start fuel).1,x.length≤start.length+fuel.length := by
  induction fuel generalizing start with
  | nil => simp [enumerateFrom]
  | cons u fuel ih =>
    intro x hx
    simp only [enumerateFrom,List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have hh := ih (addCarry start [] true).1 x hx
      simp only [addCarry_length,List.length_nil,Nat.max_zero,List.length_cons] at *
      omega

lemma enumerateFrom_cost (start : List Bool) (fuel : List Unit) :
    (enumerateFrom start fuel).2≤fuel.length*(16*(start.length+fuel.length)+5)+1 := by
  induction fuel generalizing start with
  | nil => simp [enumerateFrom]
  | cons u fuel ih =>
    have hh := ih (addCarry start [] true).1
    simp only [enumerateFrom,addCarry_cost,addCarry_length,List.length_nil,Nat.max_zero,List.length_cons] at *
    nlinarith

def enumerateBits (fuel : List Unit) : List (List Bool) × ℕ := enumerateFrom [] fuel
lemma enumerateBits_decode (fuel : List Unit) :
    (enumerateBits fuel).1.map value=List.range fuel.length := by
  simpa [enumerateBits,value] using enumerateFrom_decode [] fuel
lemma enumerateBits_cost (fuel : List Unit) :
    (enumerateBits fuel).2≤fuel.length*(16*fuel.length+5)+1 := by
  simpa [enumerateBits] using enumerateFrom_cost [] fuel

/-- A fixed straight-line bit expression. No decoded arithmetic is executed. -/
inductive BitExpr (n : ℕ)
  | input (i : Fin n)
  | constant (bits : List Bool)
  | add (x y : BitExpr n)
  | mul (x y : BitExpr n)

def BitExpr.run {n : ℕ} (inputs : Fin n → List Bool) : BitExpr n → List Bool × ℕ
  | .input i => (inputs i,1)
  | .constant bits => (bits,bits.length+1)
  | .add x y =>
    let a := x.run inputs
    let b := y.run inputs
    let c := addCarry a.1 b.1 false
    (c.1,a.2+b.2+c.2+4)
  | .mul x y =>
    let a := x.run inputs
    let b := y.run inputs
    let c := mulBits a.1 b.1
    (c.1,a.2+b.2+c.2+4)

def BitExpr.meaning {n : ℕ} (inputs : Fin n → ℕ) : BitExpr n → ℕ
  | .input i => inputs i
  | .constant bits => value bits
  | .add x y => x.meaning inputs+y.meaning inputs
  | .mul x y => x.meaning inputs*y.meaning inputs
lemma BitExpr.run_correct {n : ℕ} (inputs : Fin n → List Bool) (e : BitExpr n) :
    value (e.run inputs).1=e.meaning (fun i => value (inputs i)) := by
  induction e with
  | input i => rfl
  | constant bits => rfl
  | add x y hx hy => simp [run,meaning,addCarry_value,hx,hy]
  | mul x y hx hy => simp [run,meaning,mulBits_value,hx,hy]

noncomputable def BitExpr.widthPoly {n : ℕ} : BitExpr n → Polynomial ℕ
  | .input _ => Polynomial.X
  | .constant bits => Polynomial.C bits.length
  | .add x y => x.widthPoly+y.widthPoly+1
  | .mul x y => 2*x.widthPoly+y.widthPoly

noncomputable def BitExpr.costPoly {n : ℕ} : BitExpr n → Polynomial ℕ
  | .input _ => 1
  | .constant bits => Polynomial.C (bits.length+1)
  | .add x y => x.costPoly+y.costPoly+16*(x.widthPoly+y.widthPoly)+5
  | .mul x y => x.costPoly+y.costPoly+64*x.widthPoly*(x.widthPoly+y.widthPoly+1)+5

lemma BitExpr.run_width {n b : ℕ} (inputs : Fin n → List Bool)
    (h : ∀ i,(inputs i).length≤b) (e : BitExpr n) :
    (e.run inputs).1.length≤e.widthPoly.eval b := by
  induction e with
  | input i => simpa [run,widthPoly] using h i
  | constant bits => simp [run,widthPoly]
  | add x y hx hy =>
    simp only [run,addCarry_length,widthPoly,Polynomial.eval_add,Polynomial.eval_one]
    omega
  | mul x y hx hy =>
    have hh := mulBits_length (x.run inputs).1 (y.run inputs).1
    simp only [run,widthPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    omega

lemma BitExpr.run_cost {n b : ℕ} (inputs : Fin n → List Bool)
    (h : ∀ i,(inputs i).length≤b) (e : BitExpr n) :
    (e.run inputs).2≤e.costPoly.eval b := by
  induction e with
  | input i => simp [run,costPoly]
  | constant bits => simp [run,costPoly]
  | add x y hx hy =>
    have wx := x.run_width inputs h
    have wy := y.run_width inputs h
    simp only [run,addCarry_cost,costPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    omega
  | mul x y hx hy =>
    have wx := x.run_width inputs h
    have wy := y.run_width inputs h
    have hm := mulBits_cost (x.run inputs).1 (y.run inputs).1
    have hprod := Nat.mul_le_mul wx (Nat.add_le_add_right (Nat.add_le_add wx wy) 1)
    simp only [run,costPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    nlinarith

/-- Label inputs are q,g,W,T,R,t,p,a,r. This small fixed register tuple has
constant access cost; all variable-sized arithmetic uses bit circuits. -/
def stateIndexExpr : BitExpr 9 := .add (.input 7) (.mul (.input 0) (.input 5))
def headIndexExpr : BitExpr 9 :=
  .add (.mul (.add (.input 3) (.constant [true])) (.input 0))
    (.add (.input 6) (.mul (.input 2) (.input 5)))
def tapeIndexExpr : BitExpr 9 :=
  .add (.add (.mul (.add (.input 3) (.constant [true])) (.input 0))
    (.mul (.add (.input 3) (.constant [true])) (.input 2)))
    (.add (.add (.input 7) (.mul (.input 1) (.input 6)))
      (.mul (.mul (.input 2) (.input 1)) (.input 5)))
def choiceIndexExpr : BitExpr 9 :=
  .add (.add (.mul (.add (.input 3) (.constant [true])) (.input 0))
    (.mul (.add (.input 3) (.constant [true])) (.input 2)))
    (.add (.mul (.add (.input 3) (.constant [true])) (.mul (.input 2) (.input 1)))
      (.add (.input 8) (.mul (.input 4) (.input 5))))

lemma stateIndexExpr_meaning (x : Fin 9 → ℕ) : stateIndexExpr.meaning x=x 7+x 0*x 5 := rfl
lemma headIndexExpr_meaning (x : Fin 9 → ℕ) :
    headIndexExpr.meaning x=(x 3+1)*x 0+(x 6+x 2*x 5) := by simp [headIndexExpr,BitExpr.meaning,value]
lemma tapeIndexExpr_meaning (x : Fin 9 → ℕ) :
    tapeIndexExpr.meaning x=((x 3+1)*x 0+(x 3+1)*x 2)+(x 7+x 1*x 6+(x 2*x 1)*x 5) := by
  simp [tapeIndexExpr,BitExpr.meaning,value]
lemma choiceIndexExpr_meaning (x : Fin 9 → ℕ) :
    choiceIndexExpr.meaning x=((x 3+1)*x 0+(x 3+1)*x 2)+((x 3+1)*(x 2*x 1)+(x 8+x 4*x 5)) := by
  simp [choiceIndexExpr,BitExpr.meaning,value]

end BalancedAssortments.CookLevin
