import BalancedAssortments.NPStackStructuredUnaryMultiply
import BalancedAssortments.NPStackStructuredFinite
import BalancedAssortments.CookLevinClockFuel

/-! Static-register operational compiler for polynomial unary clock expressions.
Register zero retains the original input. Every syntax node receives a disjoint
fixed register interval; source lengths never choose register names. -/
noncomputable section
namespace BalancedAssortments.CookLevin.StackClock
open NPStack NPStack.Structured

def slots : FuelExpr → ℕ
  | .input => 3
  | .constant _ => 3
  | .add a b => 3+slots a+slots b
  | .mul a b => 3+slots a+slots b
lemma slots_lower (e : FuelExpr) : 3≤slots e := by cases e <;> simp only [slots] <;> omega

def compile (base : ℕ) : FuelExpr → Block ℕ
  | .input => unaryCount 0 (base+1) (base+2) base
  | .constant tokens => pushZeros tokens.length base
  | .add a b =>
    .seq (compile (base+3) a)
      (.seq (compile (base+3+slots a) b)
        (.seq (unaryDrain (base+3) base) (unaryDrain (base+3+slots a) base)))
  | .mul a b =>
    .seq (compile (base+3) a)
      (.seq (compile (base+3+slots a) b)
        (.seq (unaryMultiply ⟨base+3,base+3+slots a,base+1,base+2,base⟩)
          (clearStack (base+3+slots a))))

noncomputable def timePolynomial : FuelExpr → Polynomial ℕ
  | .input => 8*Polynomial.X+4
  | .constant tokens => Polynomial.C (2*tokens.length+1)
  | .add a b => timePolynomial a+timePolynomial b+3*a.polynomial+3*b.polynomial+5
  | .mul a b => timePolynomial a+timePolynomial b+(8*b.polynomial+6)*a.polynomial+3*b.polynomial+5

def Fresh (s : Store ℕ) (base count : ℕ) : Prop := ∀ k,base≤k → k<base+count → s k=[]
lemma Fresh.subrange {s : Store ℕ} {base count child count' : ℕ} (h : Fresh s base count)
    (hl : base≤child) (hr : child+count'≤base+count) : Fresh s child count' := by
  intro k hkl hkr
  exact h k (by omega) (by omega)
lemma Fresh.update_outside {s : Store ℕ} {base count key : ℕ} (h : Fresh s base count)
    (hk : key<base ∨ base+count≤key) (bits : List Bool) : Fresh (Function.update s key bits) base count := by
  intro k hkl hkr
  have hn : k≠key := by omega
  simpa [Function.update,hn] using h k hkl hkr

lemma drain_two (s : Store ℕ) (left right out n : ℕ) (xs ys : List Bool)
    (hlr : left≠right) (hlo : left≠out) (hro : right≠out) (hl : s left=[]) :
    drainStore (Function.update (Function.update s left xs) right ys) left out n=
      Function.update (Function.update s right ys) out (List.replicate n false++s out) := by
  funext k
  by_cases hko : k=out
  · subst k;simp [drainStore,Function.update,Ne.symm hlo,Ne.symm hro]
  · by_cases hkl : k=left
    · subst k;simp [drainStore,Function.update,hlo,hlr,hl]
    · by_cases hkr : k=right
      · subst k;simp [drainStore,Function.update,hro,Ne.symm hlr]
      · simp [drainStore,Function.update,hko,hkl,hkr]

lemma drain_accumulate (s : Store ℕ) (source out n : ℕ) (xs ys : List Bool)
    (hne : source≠out) (hs : s source=[]) :
    drainStore (Function.update (Function.update s source xs) out ys) source out n=
      Function.update s out (List.replicate n false++ys) := by
  funext k
  by_cases hko : k=out
  · subst k;simp [drainStore]
  · by_cases hks : k=source
    · subst k;simp [drainStore,Function.update,hne,hs]
    · simp [drainStore,Function.update,hko,hks]

lemma clear_accumulate (s : Store ℕ) (source out : ℕ) (xs ys : List Bool)
    (hne : source≠out) (hs : s source=[]) :
    Function.update (Function.update (Function.update s source xs) out ys) source []=
      Function.update s out ys := by
  funext k
  by_cases hks : k=source
  · subst k;simp [Function.update,hne,hs]
  · by_cases hko : k=out
    · subst k;simp [Function.update,Ne.symm hne]
    · simp [Function.update,hks,hko]

end BalancedAssortments.CookLevin.StackClock
