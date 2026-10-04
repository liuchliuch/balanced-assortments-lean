import BalancedAssortments.CookLevinStackClockCorrect
import BalancedAssortments.NPStackStructuredBinaryAtoms
import BalancedAssortments.CookLevinBitIndices

noncomputable section
namespace BalancedAssortments.CookLevin.StackIndices
open NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)

def pushBits {K : Type*} (target : K) : List Bool → Block K
  | [] => .skip
  | b::bs => .seq (pushBits target bs) (.push target b)
lemma pushBits_exec {K : Type*} [DecidableEq K] (target : K) (bits : List Bool) (s : Store K) :
    Exec (pushBits target bits) s (Function.update s target (bits++s target)) (2*bits.length+1) := by
  induction bits generalizing s with
  | nil => simpa [pushBits] using Exec.skip s
  | cons b bs ih =>
    have h1 := ih s
    have h2 := Exec.push (Function.update s target (bs++s target)) target b
    have he : Function.update (Function.update s target (bs++s target)) target
        (b::(Function.update s target (bs++s target)) target)=Function.update s target ((b::bs)++s target) := by simp
    rw [he] at h2
    have hh := Exec.seq h1 h2
    convert hh using 1 <;> simp only [List.length_cons] <;> omega

def slots {n : ℕ} : BitExpr n → ℕ
  | .input _ => 8
  | .constant _ => 8
  | .add a b => 8+slots a+slots b
  | .mul a b => 8+slots a+slots b
lemma slots_lower {n : ℕ} (e : BitExpr n) : 8≤slots e := by cases e <;> simp only [slots] <;> omega

def mulMap (base left right : ℕ) : MulStack → ℕ
  | .input => left
  | .pending => base+1
  | .factor => right
  | .copyScratch => base+2
  | .copyOut => base+3
  | .accA => base+4
  | .accB => base+5
  | .addScratch => base+6
  | .finalScratch => base+7
  | .output => base

lemma mulMap_injective {base left right : ℕ} (hl : base+8≤left) (hr : left<right) :
    Function.Injective (mulMap base left right) := by
  intro i j he
  cases i <;> cases j <;> simp only [mulMap] at he <;> first | rfl | omega

def compile {n : ℕ} (base : ℕ) : BitExpr n → Block ℕ
  | .input i => .atom (copyAtom i.val (base+1) base)
  | .constant bits => pushBits base bits
  | .add a b =>
    .seq (compile (base+8) a)
      (.seq (compile (base+8+slots a) b)
        (.atom (addAtom (base+8) (base+8+slots a) (base+1) base)))
  | .mul a b =>
    .seq (compile (base+8) a)
      (.seq (compile (base+8+slots a) b)
        (.seq (.atom (multiplyAtom (mulMap base (base+8) (base+8+slots a))))
          (clearStack (base+8+slots a))))

noncomputable def timePolynomial {n : ℕ} : BitExpr n → Polynomial ℕ
  | .input _ => 5*Polynomial.X+2
  | .constant bits => Polynomial.C (2*bits.length+1)
  | .add a b => timePolynomial a+timePolynomial b+5*(a.widthPoly+b.widthPoly)+10
  | .mul a b =>
    let x := a.widthPoly
    let y := b.widthPoly
    timePolynomial a+timePolynomial b+(x*(10*(2*x+y)+12)+2*x+4*(2*x+y)+7)+3*y+4

def inputView (n : ℕ) (s : Store ℕ) : Fin n → List Bool := fun i => s i.val
lemma inputView_update (n key : ℕ) (s : Store ℕ) (bits : List Bool) (h : n≤key) :
    inputView n (Function.update s key bits)=inputView n s := by
  funext i
  have hi : i.val≠key := by have := i.isLt;omega
  simp [inputView,Function.update,hi]

lemma add_two (s : Store ℕ) (left right out : ℕ) (xs ys zs : List Bool)
    (hlr : left≠right) (hlo : left≠out) (hro : right≠out) (hl : s left=[]) (hr : s right=[]) :
    Macros.writes (Function.update (Function.update s left xs) right ys) [(left,[]),(right,[]),(out,zs)]=
      Function.update s out zs := by
  funext k
  by_cases hko : k=out
  · subst k;simp [Macros.writes]
  · by_cases hkl : k=left
    · subst k;simp [Macros.writes,Function.update,hlo,hlr,hl]
    · by_cases hkr : k=right
      · subst k;simp [Macros.writes,Function.update,hro,hr]
      · simp [Macros.writes,Function.update,hko,hkl,hkr]
lemma mul_two (s : Store ℕ) (left right out : ℕ) (xs ys zs : List Bool)
    (hlr : left≠right) (hlo : left≠out) (hro : right≠out) (hl : s left=[]) :
    Function.update (Function.update (Function.update (Function.update s left xs) right ys) left []) out zs=
      Function.update (Function.update s right ys) out zs := by
  funext k
  by_cases hko : k=out
  · subst k;simp
  · by_cases hkl : k=left
    · subst k;simp [Function.update,hlo,hlr,hl]
    · by_cases hkr : k=right
      · subst k;simp [Function.update,hro,Ne.symm hlr]
      · simp [Function.update,hko,hkl,hkr]

lemma multiplicationBudget_mono {n m N M : ℕ} (hn : n≤N) (hm : m≤M) :
    multiplicationBudget n m≤ multiplicationBudget N M := by
  have hh := Nat.mul_le_mul hn (show 10*(2*n+m)+12≤10*(2*N+M)+12 by omega)
  unfold multiplicationBudget
  omega

end BalancedAssortments.CookLevin.StackIndices
