import BalancedAssortments.CookLevinStackIndices

noncomputable section
namespace BalancedAssortments.CookLevin.StackIndices
open NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)

/-- Exact bit-string refinement of binary straight-line expressions by genuine
finite stack bytecode. Inputs are preserved; fresh work registers are cleared. -/
theorem compile_exec {n : ℕ} (e : BitExpr n) (base : ℕ) (s : Store ℕ) (w : ℕ)
    (hb : n≤base) (hf : Fresh s base (slots e)) (hw : ∀ i : Fin n,(s i.val).length≤w) :
    ∃ t≤(timePolynomial e).eval w,
      Exec (compile base e) s (Function.update s base (e.run (inputView n s)).1) t := by
  induction e generalizing base s with
  | input i =>
    have hi0 := i.isLt
    have ho : s base=[] := hf base (by omega) (by simp only [slots];omega)
    have hx : s (base+1)=[] := hf (base+1) (by omega) (by simp only [slots];omega)
    have hi : Function.Injective (Macros.copyMap i.val (base+1) base) := by
      intro a b he
      cases a <;> cases b <;> simp_all [Macros.copyMap] <;> omega
    have hh := copyAtom_run i.val (base+1) base hi s hx
    rw [ho,List.append_nil] at hh
    refine ⟨5*(s i.val).length+2,?_,hh⟩
    have := hw i
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  | constant bits =>
    have ho : s base=[] := hf base (by omega) (by simp only [slots];omega)
    refine ⟨2*bits.length+1,by simp [timePolynomial],?_⟩
    simpa only [ho,List.append_nil] using pushBits_exec base bits s
  | add a b iha ihb =>
    let left := base+8
    let right := base+8+slots a
    let X := (a.run (inputView n s)).1
    let Y := (b.run (inputView n s)).1
    have ha8 := slots_lower a
    have hb8 := slots_lower b
    have hfl : Fresh s left (slots a) := hf.subrange (by dsimp [left];omega) (by dsimp [left];simp only [slots];omega)
    have hfr : Fresh s right (slots b) := hf.subrange (by dsimp [right];omega) (by dsimp [right];simp only [slots];omega)
    have ho : s base=[] := hf base (by omega) (by simp only [slots];omega)
    have hx : s (base+1)=[] := hf (base+1) (by omega) (by simp only [slots];omega)
    have hl : s left=[] := hfl left (by omega) (by omega)
    have hr : s right=[] := hfr right (by omega) (by omega)
    have hlr : left≠right := by dsimp [left,right];omega
    have hlo : left≠base := by dsimp [left];omega
    have hro : right≠base := by dsimp [right];omega
    let s1 := Function.update s left X
    let s2 := Function.update s1 right Y
    obtain ⟨ta,hta,ea⟩ := iha left s (by dsimp [left];omega) hfl hw
    have hfb : Fresh s1 right (slots b) := hfr.update_outside (Or.inl (by dsimp [left,right];omega)) _
    have hview : inputView n s1=inputView n s := inputView_update n left s X (by dsimp [left];omega)
    have hw1 : ∀ i : Fin n,(s1 i.val).length≤w := by
      intro i;change (inputView n s1 i).length≤w;rw [hview];exact hw i
    obtain ⟨tb,htb,eb⟩ := ihb right s1 (by dsimp [right];omega) hfb hw1
    rw [hview] at eb
    have h2l : s2 left=X := by simp [s2,s1,Function.update,hlr]
    have h2r : s2 right=Y := by simp [s2]
    have hlow : ∀ k,k<left → s2 k=s k := by
      intro k hk
      have hk1 : k≠left := by omega
      have hk2 : k≠right := by dsimp [left,right] at *;omega
      simp [s2,s1,Function.update,hk1,hk2]
    have h2o : s2 base=[] := by rw [hlow base (by dsimp [left];omega),ho]
    have h2x : s2 (base+1)=[] := by rw [hlow (base+1) (by dsimp [left];omega),hx]
    have hi : Function.Injective (Macros.addMap left right (base+1) base) := by
      intro i j he
      cases i <;> cases j <;> simp only [Macros.addMap,left,right] at he <;> first | rfl | omega
    have ec := addAtom_exec left right (base+1) base hi s2 h2x h2o
    rw [h2l,h2r] at ec
    have hec : Macros.writes s2 [(left,[]),(right,[]),(base,(addCarry X Y false).1)]=
        Function.update s base (addCarry X Y false).1 := add_two s left right base X Y _ hlr hlo hro hl hr
    rw [hec] at ec
    have wx := a.run_width (inputView n s) hw
    have wy := b.run_width (inputView n s) hw
    refine ⟨ta+(tb+(5*max X.length Y.length+8)+1)+1,?_,Exec.seq ea (Exec.seq eb ec)⟩
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    change X.length≤_ at wx
    change Y.length≤_ at wy
    omega
  | mul a b iha ihb =>
    let left := base+8
    let right := base+8+slots a
    let X := (a.run (inputView n s)).1
    let Y := (b.run (inputView n s)).1
    have ha8 := slots_lower a
    have hb8 := slots_lower b
    have hfl : Fresh s left (slots a) := hf.subrange (by dsimp [left];omega) (by dsimp [left];simp only [slots];omega)
    have hfr : Fresh s right (slots b) := hf.subrange (by dsimp [right];omega) (by dsimp [right];simp only [slots];omega)
    have hl : s left=[] := hfl left (by omega) (by omega)
    have hr : s right=[] := hfr right (by omega) (by omega)
    have hlr : left≠right := by dsimp [left,right];omega
    have hlo : left≠base := by dsimp [left];omega
    have hro : right≠base := by dsimp [right];omega
    let s1 := Function.update s left X
    let s2 := Function.update s1 right Y
    obtain ⟨ta,hta,ea⟩ := iha left s (by dsimp [left];omega) hfl hw
    have hfb : Fresh s1 right (slots b) := hfr.update_outside (Or.inl (by dsimp [left,right];omega)) _
    have hview : inputView n s1=inputView n s := inputView_update n left s X (by dsimp [left];omega)
    have hw1 : ∀ i : Fin n,(s1 i.val).length≤w := by
      intro i;change (inputView n s1 i).length≤w;rw [hview];exact hw i
    obtain ⟨tb,htb,eb⟩ := ihb right s1 (by dsimp [right];omega) hfb hw1
    rw [hview] at eb
    have h2l : s2 left=X := by simp [s2,s1,Function.update,hlr]
    have h2r : s2 right=Y := by simp [s2]
    have hlow : ∀ k,base≤k → k<left → s2 k=[] := by
      intro k hk hk'
      have hk1 : k≠left := by omega
      have hk2 : k≠right := by dsimp [left,right] at *;omega
      simp only [s2,s1,Function.update_of_ne hk2,Function.update_of_ne hk1]
      exact hf k hk (by dsimp [left] at hk';simp only [slots];omega)
    have hi : Function.Injective (mulMap base left right) := mulMap_injective (by rfl) (by dsimp [left,right];omega)
    have hz : ∀ k,k≠MulStack.input → k≠MulStack.factor → s2 (mulMap base left right k)=[] := by
      intro k hki hkf
      cases k <;> simp only [mulMap] at * <;> first | contradiction | apply hlow <;> dsimp [left] <;> omega
    obtain ⟨tm,htm,ec⟩ := multiplyAtom_exec (mulMap base left right) hi s2 hz
    change tm≤ multiplicationBudget (s2 left).length (s2 right).length at htm
    change Exec (.atom (multiplyAtom (mulMap base left right))) s2
      (Function.update (Function.update s2 left []) base (mulBits (s2 left) (s2 right)).1) tm at ec
    rw [h2l,h2r] at htm ec
    have hec : Function.update (Function.update s2 left []) base (mulBits X Y).1=
        Function.update (Function.update s right Y) base (mulBits X Y).1 := mul_two s left right base X Y _ hlr hlo hro hl
    rw [hec] at ec
    let s3 := Function.update (Function.update s right Y) base (mulBits X Y).1
    have h3r : s3 right=Y := by simp [s3,Function.update,hro]
    have ed := clearStack_exec right s3
    rw [h3r] at ed
    have hed : Function.update s3 right []=Function.update s base (mulBits X Y).1 := StackClock.clear_accumulate s right base _ _ hro hr
    rw [hed] at ed
    have wx := a.run_width (inputView n s) hw
    have wy := b.run_width (inputView n s) hw
    change X.length≤_ at wx
    change Y.length≤_ at wy
    have hm := multiplicationBudget_mono wx wy
    refine ⟨ta+(tb+(tm+(3*Y.length+1)+1)+1)+1,?_,Exec.seq ea (Exec.seq eb (Exec.seq ec ed))⟩
    dsimp only [timePolynomial]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    unfold multiplicationBudget at hm htm
    omega

end BalancedAssortments.CookLevin.StackIndices
