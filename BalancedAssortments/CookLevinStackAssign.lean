import BalancedAssortments.CookLevinStackIndicesCorrect

noncomputable section
namespace BalancedAssortments.CookLevin.StackAssign
open NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)
open StackIndices (inputView)

def assignExpr {n : ℕ} (base : ℕ) (dest : Fin n) (e : BitExpr n) : Block ℕ :=
  .seq (StackIndices.compile base e)
    (.seq (clearStack dest.val)
      (.seq (.atom (copyAtom base (base+1) dest.val)) (clearStack base)))
noncomputable def assignTime {n : ℕ} (e : BitExpr n) : Polynomial ℕ :=
  StackIndices.timePolynomial e+3*Polynomial.X+8*e.widthPoly+7

lemma assignExpr_exec {n : ℕ} (base : ℕ) (dest : Fin n) (e : BitExpr n) (s : Store ℕ) (w : ℕ)
    (hb : n≤base) (hf : Fresh s base (StackIndices.slots e))
    (hw : ∀ i : Fin n,(s i.val).length≤w) :
    ∃ t≤(assignTime e).eval w,
      Exec (assignExpr base dest e) s
        (Function.update s dest.val (e.run (inputView n s)).1) t := by
  have hd := dest.isLt
  have hne : dest.val≠base := by omega
  have hslots := StackIndices.slots_lower e
  have h0 : s base=[] := hf base (by omega) (by omega)
  have h1 : s (base+1)=[] := hf (base+1) (by omega) (by omega)
  obtain ⟨ta,hta,ha⟩ := StackIndices.compile_exec e base s w hb hf hw
  let bits := (e.run (inputView n s)).1
  let u := Function.update s base bits
  let v := Function.update u dest.val []
  have hu : u base=bits := by simp [u]
  have hud : u dest.val=s dest.val := by simp [u,Function.update,hne]
  have hbclear := clearStack_exec dest.val u
  rw [hud] at hbclear
  have hv0 : v base=bits := by simp [v,Function.update,Ne.symm hne,hu]
  have hvd : v dest.val=[] := by simp [v]
  have hv1 : v (base+1)=[] := by
    simp [v,u,Function.update,h1,show base+1≠dest.val by omega]
  have hi : Function.Injective (Macros.copyMap base (base+1) dest.val) := by
    intro i j he
    cases i <;> cases j <;> simp only [Macros.copyMap] at he <;> first | rfl | omega
  have hc := copyAtom_run base (base+1) dest.val hi v hv1
  rw [hv0,hvd,List.append_nil] at hc
  have hvout : Function.update v dest.val bits=Function.update u dest.val bits := by simp [v]
  rw [hvout] at hc
  let last := Function.update u dest.val bits
  have hlast : last base=bits := by simp [last,Function.update,Ne.symm hne,hu]
  have he := clearStack_exec base last
  rw [hlast] at he
  have hfinal : Function.update last base []=Function.update s dest.val bits :=
    StackClock.clear_accumulate s base dest.val bits bits (Ne.symm hne) h0
  rw [hfinal] at he
  have hwidth := e.run_width (inputView n s) hw
  have hdwidth := hw dest
  refine ⟨ta+((3*(s dest.val).length+1)+((5*bits.length+2)+(3*bits.length+1)+1)+1)+1,?_,
    Exec.seq ha (Exec.seq hbclear (Exec.seq hc he))⟩
  simp only [assignTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change bits.length≤_ at hwidth
  omega

def incrementExpr {n : ℕ} (dest : Fin n) : BitExpr n := .add (.input dest) (.constant [true])
def increment {n : ℕ} (base : ℕ) (dest : Fin n) : Block ℕ := assignExpr base dest (incrementExpr dest)

lemma increment_result {n : ℕ} (dest : Fin n) (s : Store ℕ) :
    ((incrementExpr dest).run (inputView n s)).1=(addCarry (s dest.val) [true] false).1 := rfl
lemma increment_value {n : ℕ} (dest : Fin n) (s : Store ℕ) :
    value ((incrementExpr dest).run (inputView n s)).1=value (s dest.val)+1 := by
  simp [increment_result,addCarry_value,value]
lemma increment_width {n : ℕ} (dest : Fin n) (s : Store ℕ) :
    ((incrementExpr dest).run (inputView n s)).1.length≤(s dest.val).length+2 := by
  rw [increment_result,addCarry_length]
  simp only [List.length_cons,List.length_nil]
  omega

end BalancedAssortments.CookLevin.StackAssign
