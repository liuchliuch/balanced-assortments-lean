import BalancedAssortments.CookLevinStackClock

noncomputable section
namespace BalancedAssortments.CookLevin.StackClock
open NPStack NPStack.Structured

/-- The clock expression executes with its original input preserved and all
allocated work registers restored to empty; only its output register changes. -/
theorem compile_exec (e : FuelExpr) (base : ℕ) (s : Store ℕ) (hb : 0<base)
    (hf : Fresh s base (slots e)) :
    Exec (compile base e) s
      (Function.update s base (List.replicate (e.polynomial.eval (s 0).length) false))
      ((timePolynomial e).eval (s 0).length) := by
  induction e generalizing base s with
  | input =>
    have ho : s base=[] := hf base (by omega) (by simp [slots])
    have hx : s (base+1)=[] := hf (base+1) (by omega) (by simp only [slots];omega)
    have hw : s (base+2)=[] := hf (base+2) (by omega) (by simp only [slots];omega)
    have hi : Function.Injective (Macros.copyMap 0 (base+2) (base+1)) := by
      intro a b he
      cases a <;> cases b <;> simp_all [Macros.copyMap] <;> omega
    have hh := unaryCount_exec 0 (base+1) (base+2) base hi (by omega) (by omega) (by omega) s hx hw
    simpa [compile,timePolynomial,FuelExpr.polynomial,ho] using hh
  | constant tokens =>
    have ho : s base=[] := hf base (by omega) (by simp [slots])
    simpa [compile,timePolynomial,FuelExpr.polynomial,ho] using pushZeros_exec tokens.length base s
  | add a b iha ihb =>
    let left := base+3
    let right := base+3+slots a
    let A := a.polynomial.eval (s 0).length
    let B := b.polynomial.eval (s 0).length
    have ha3 := slots_lower a
    have hb3 := slots_lower b
    have hfl : Fresh s left (slots a) := hf.subrange (by dsimp [left];omega) (by dsimp [left];simp only [slots];omega)
    have hfr : Fresh s right (slots b) := hf.subrange (by dsimp [right];omega) (by dsimp [right];simp only [slots];omega)
    have ho : s base=[] := hf base (by omega) (by simp only [slots];omega)
    have hl : s left=[] := hfl left (by omega) (by omega)
    have hr : s right=[] := hfr right (by omega) (by omega)
    have hln : left≠base := by dsimp [left];omega
    have hrn : right≠base := by dsimp [right];omega
    have hlr : left≠right := by dsimp [left,right];omega
    let s1 := Function.update s left (List.replicate A false)
    let s2 := Function.update s1 right (List.replicate B false)
    have ea := iha left s (by dsimp [left];omega) hfl
    have hfb : Fresh s1 right (slots b) := hfr.update_outside (Or.inl (by dsimp [left,right];omega)) _
    have h10 : s1 0=s 0 := by simp [s1,Function.update,show 0≠left by dsimp [left];omega]
    have eb := ihb right s1 (by dsimp [right];omega) hfb
    rw [h10] at eb
    have h2l : s2 left=List.replicate A false := by simp [s2,s1,Function.update,hlr]
    have ec := unaryDrain_exec left base hln s2
    rw [h2l,List.length_replicate] at ec
    have hec : drainStore s2 left base A=Function.update (Function.update s right (List.replicate B false)) base (List.replicate A false) := by
      simpa [s2,s1,ho] using drain_two s left right base A (List.replicate A false) (List.replicate B false) hlr hln hrn hl
    rw [hec] at ec
    let s3 := Function.update (Function.update s right (List.replicate B false)) base (List.replicate A false)
    have h3r : s3 right=List.replicate B false := by simp [s3,Function.update,hrn]
    have ed := unaryDrain_exec right base hrn s3
    rw [h3r,List.length_replicate] at ed
    have hed : drainStore s3 right base B=Function.update s base (List.replicate (A+B) false) := by
      rw [show s3=Function.update (Function.update s right (List.replicate B false)) base (List.replicate A false) from rfl,
        drain_accumulate s right base B _ _ hrn hr]
      rw [← List.replicate_add,Nat.add_comm B A]
    rw [hed] at ed
    have hh := Exec.seq ea (Exec.seq eb (Exec.seq ec ed))
    convert hh using 1 <;> simp only [compile,timePolynomial,FuelExpr.polynomial,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat] <;> dsimp [A,B,left,right,s1,s2,s3] <;> omega
  | mul a b iha ihb =>
    let left := base+3
    let right := base+3+slots a
    let A := a.polynomial.eval (s 0).length
    let B := b.polynomial.eval (s 0).length
    have ha3 := slots_lower a
    have hb3 := slots_lower b
    have hfl : Fresh s left (slots a) := hf.subrange (by dsimp [left];omega) (by dsimp [left];simp only [slots];omega)
    have hfr : Fresh s right (slots b) := hf.subrange (by dsimp [right];omega) (by dsimp [right];simp only [slots];omega)
    have ho : s base=[] := hf base (by omega) (by simp only [slots];omega)
    have hx : s (base+1)=[] := hf (base+1) (by omega) (by simp only [slots];omega)
    have hw : s (base+2)=[] := hf (base+2) (by omega) (by simp only [slots];omega)
    have hl : s left=[] := hfl left (by omega) (by omega)
    have hr : s right=[] := hfr right (by omega) (by omega)
    have hln : left≠base := by dsimp [left];omega
    have hrn : right≠base := by dsimp [right];omega
    have hlr : left≠right := by dsimp [left,right];omega
    let s1 := Function.update s left (List.replicate A false)
    let s2 := Function.update s1 right (List.replicate B false)
    have ea := iha left s (by dsimp [left];omega) hfl
    have hfb : Fresh s1 right (slots b) := hfr.update_outside (Or.inl (by dsimp [left,right];omega)) _
    have h10 : s1 0=s 0 := by simp [s1,Function.update,show 0≠left by dsimp [left];omega]
    have eb := ihb right s1 (by dsimp [right];omega) hfb
    rw [h10] at eb
    have h2l : s2 left=List.replicate A false := by simp [s2,s1,Function.update,hlr]
    have h2r : s2 right=List.replicate B false := by simp [s2]
    have h2x : s2 (base+1)=[] := by simp [s2,s1,Function.update,left,right,hx];omega
    have h2w : s2 (base+2)=[] := by simp [s2,s1,Function.update,left,right,hw];omega
    let regs : UnaryRegisters ℕ := ⟨left,right,base+1,base+2,base⟩
    have hi : Function.Injective regs.map := by
      intro i j he
      fin_cases i <;> fin_cases j <;> norm_num [UnaryRegisters.map,regs,left,right] at he <;> omega
    have ec := unaryMultiply_exec regs hi s2 h2x h2w
    change Exec (unaryMultiply regs) s2 (drainStore s2 left base ((s2 left).length*(s2 right).length))
      ((8*(s2 right).length+6)*(s2 left).length+1) at ec
    rw [h2l,h2r,List.length_replicate,List.length_replicate] at ec
    have hec : drainStore s2 left base (A*B)=Function.update (Function.update s right (List.replicate B false)) base (List.replicate (A*B) false) := by
      simpa [s2,s1,ho] using drain_two s left right base (A*B) (List.replicate A false) (List.replicate B false) hlr hln hrn hl
    rw [hec] at ec
    let s3 := Function.update (Function.update s right (List.replicate B false)) base (List.replicate (A*B) false)
    have h3r : s3 right=List.replicate B false := by simp [s3,Function.update,hrn]
    have ed := clearStack_exec right s3
    rw [h3r,List.length_replicate] at ed
    have hed : Function.update s3 right []=Function.update s base (List.replicate (A*B) false) :=
      clear_accumulate s right base _ _ hrn hr
    rw [hed] at ed
    have hh := Exec.seq ea (Exec.seq eb (Exec.seq ec ed))
    convert hh using 1 <;> simp only [compile,timePolynomial,FuelExpr.polynomial,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat] <;> dsimp [A,B,left,right,s1,s2,s3,regs] <;> omega

end BalancedAssortments.CookLevin.StackClock
