import BalancedAssortments.CookLevinStackIndicesCorrect
import BalancedAssortments.NPStackStructuredCompareAtom

noncomputable section
namespace BalancedAssortments.CookLevin.StackTest
open NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)
open StackIndices (inputView)

def testSlots {n : ℕ} (a b : BitExpr n) : ℕ := 1+StackIndices.slots a+StackIndices.slots b
def testLE {n : ℕ} (base : ℕ) (a b : BitExpr n) : Block ℕ :=
  .seq (StackIndices.compile (base+1) a)
    (.seq (StackIndices.compile (base+1+StackIndices.slots a) b)
      (.atom (compareAtom (base+1) (base+1+StackIndices.slots a) base)))
noncomputable def testTime {n : ℕ} (a b : BitExpr n) : Polynomial ℕ :=
  StackIndices.timePolynomial a+StackIndices.timePolynomial b+2*(a.widthPoly+b.widthPoly)+5

def truthLE {n : ℕ} (a b : BitExpr n) (s : Store ℕ) : Bool :=
  decide (value (a.run (inputView n s)).1≤value (b.run (inputView n s)).1)

lemma testLE_exec {n : ℕ} (base : ℕ) (a b : BitExpr n) (s : Store ℕ) (w : ℕ)
    (hb : n≤base) (hf : Fresh s base (testSlots a b))
    (hw : ∀ i : Fin n,(s i.val).length≤w) :
    ∃ t≤(testTime a b).eval w,
      Exec (testLE base a b) s (Function.update s base [truthLE a b s]) t := by
  let left := base+1
  let right := base+1+StackIndices.slots a
  let X := (a.run (inputView n s)).1
  let Y := (b.run (inputView n s)).1
  have ha8 := StackIndices.slots_lower a
  have hb8 := StackIndices.slots_lower b
  have hfl : Fresh s left (StackIndices.slots a) := hf.subrange (by dsimp [left];omega) (by dsimp [left];unfold testSlots;omega)
  have hfr : Fresh s right (StackIndices.slots b) := hf.subrange (by dsimp [right];omega) (by dsimp [right];unfold testSlots;omega)
  have ho : s base=[] := hf base (by omega) (by unfold testSlots;omega)
  have hl : s left=[] := hfl left (by omega) (by omega)
  have hr : s right=[] := hfr right (by omega) (by omega)
  have hlr : left≠right := by dsimp [left,right];omega
  have hlo : left≠base := by dsimp [left];omega
  have hro : right≠base := by dsimp [right];omega
  let s1 := Function.update s left X
  let s2 := Function.update s1 right Y
  obtain ⟨ta,hta,ha⟩ := StackIndices.compile_exec a left s w (by dsimp [left];omega) hfl hw
  have hfb : Fresh s1 right (StackIndices.slots b) := hfr.update_outside (Or.inl (by dsimp [left,right];omega)) _
  have hview : inputView n s1=inputView n s := StackIndices.inputView_update n left s X (by dsimp [left];omega)
  have hw1 : ∀ i : Fin n,(s1 i.val).length≤w := by
    intro i;change (inputView n s1 i).length≤w;rw [hview];exact hw i
  obtain ⟨tb,htb,hb⟩ := StackIndices.compile_exec b right s1 w (by dsimp [right];omega) hfb hw1
  rw [hview] at hb
  have h2l : s2 left=X := by simp [s2,s1,Function.update,hlr]
  have h2r : s2 right=Y := by simp [s2]
  have h2o : s2 base=[] := by simp [s2,s1,Function.update,Ne.symm hlo,Ne.symm hro,ho]
  have hi : Function.Injective (Macros.normalizeMap left right base) := by
    intro i j he
    cases i <;> cases j <;> simp only [Macros.normalizeMap] at he <;> first | rfl | omega
  have hc := compareAtom_exec left right base hi s2
  rw [h2l,h2r,h2o] at hc
  have hec : Macros.writes s2 [(left,[]),(right,[]),(base,[decide (value X≤value Y)])]=
      Function.update s base [truthLE a b s] := StackIndices.add_two s left right base X Y _ hlr hlo hro hl hr
  rw [hec] at hc
  have wx := a.run_width (inputView n s) hw
  have wy := b.run_width (inputView n s) hw
  refine ⟨ta+(tb+(2*max X.length Y.length+3)+1)+1,?_,Exec.seq ha (Exec.seq hb hc)⟩
  simp only [testTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  change X.length≤_ at wx
  change Y.length≤_ at wy
  omega

def ifLE {n : ℕ} (base : ℕ) (a b : BitExpr n) (yes no : Block ℕ) : Block ℕ :=
  .seq (testLE base a b) (.branch base .skip no yes)

/-- The tested Boolean is produced by real bit comparison, then physically
popped before the chosen finite branch. Test work and the flag are restored. -/
lemma ifLE_exec {n : ℕ} (base : ℕ) (a b : BitExpr n) (yes no : Block ℕ)
    (s t : Store ℕ) (w m : ℕ) (hb : n≤base) (hf : Fresh s base (testSlots a b))
    (hw : ∀ i : Fin n,(s i.val).length≤w)
    (hbody : Exec (if truthLE a b s then yes else no) s t m) :
    ∃ k≤(testTime a b).eval w+m+3,Exec (ifLE base a b yes no) s t k := by
  obtain ⟨k,hk,hr⟩ := testLE_exec base a b s w hb hf hw
  have h0 : s base=[] := hf base (by omega) (by unfold testSlots;have := StackIndices.slots_lower a;omega)
  have hclear (bit : Bool) : Function.update (Function.update s base [bit]) base []=s := by
    rw [Function.update_idem,← h0];exact Function.update_eq_self base s
  have hbranch : Exec (.branch base .skip no yes) (Function.update s base [truthLE a b s]) t (m+2) := by
    cases ht : truthLE a b s
    · simp only [ht,Bool.false_eq_true,ite_false] at hbody
      apply Exec.branch_false (bs := []) (by simp)
      rw [hclear false]
      exact hbody
    · simp only [ht,ite_true] at hbody
      apply Exec.branch_true (bs := []) (by simp)
      rw [hclear true]
      exact hbody
  exact ⟨k+(m+2)+1,by omega,Exec.seq hr hbranch⟩

end BalancedAssortments.CookLevin.StackTest
