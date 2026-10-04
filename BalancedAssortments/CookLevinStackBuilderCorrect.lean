import BalancedAssortments.CookLevinStackBuilderScope

noncomputable section
namespace BalancedAssortments.CookLevin.StackBuilder
open NPCNF NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)
open StackIndices (inputView)

lemma workSize_three {n : ℕ} (p : Builder n) : 3≤workSize p := by
  induction p with
  | skip => rfl
  | field bits => rfl
  | literal e sign => exact (by decide : 3≤8).trans (StackIndices.slots_lower e)
  | seq a b ha hb => exact ha.trans (Nat.le_max_left _ _)
  | branch a b yes no hy hn => exact hy.trans ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  | each i f a b ha hb => exact (by decide : 3≤8).trans ((StackIndices.slots_lower _).trans (Nat.le_max_left _ _))

/-- Compiler correctness for a finite streaming builder. Only the output stack
changes, including across lexically scoped index loops. The bound counts real
primitive Boolean-stack steps and is a fixed natural polynomial in B. -/
theorem compile_exec {n : ℕ} (p : Builder n) (work privateBase out : ℕ) (s : Store ℕ) (B : ℕ)
    (ho : n≤out) (hp : out<privateBase) (hlayout : privateBase+3*depth p≤work)
    (hclean : ∀ k,privateBase≤k → k<work+workSize p → s k=[])
    (hgood : GoodFuel p privateBase out) (hfuels : fuelBounds p s B)
    (hfields : ∀ i : Fin n,(s i.val).length≤B) :
    ∃ t≤(timePolynomial p).eval B,
      Exec (compile work privateBase out p) s
        (Function.update s out (value p (inputView n s) s++s out)) t := by
  induction p generalizing privateBase s with
  | skip =>
    refine ⟨1,by simp [timePolynomial],?_⟩
    simpa [compile,value] using Exec.skip s
  | field bits =>
    have hw : Fresh s work 3 := fun k hk hkr => hclean k (by simp only [depth] at hlayout;omega) hkr
    have hh := StackEmit.emitConst_exec work out bits s (by simp only [depth] at hlayout;omega) hw
    exact ⟨9*bits.length+8,by simp [timePolynomial],hh⟩
  | literal e sign =>
    have hw : Fresh s work (StackIndices.slots e) := fun k hk hkr => hclean k (by simp only [depth] at hlayout;omega) hkr
    obtain ⟨t,ht,hr⟩ := StackEmit.emitLiteral_exec work out e sign s B (by simp only [depth] at hlayout;omega)
      (by simp only [depth] at hlayout;omega) hw hfields
    refine ⟨t,ht,?_⟩
    simpa only [value,List.append_assoc] using hr
  | seq a b iha ihb =>
    have hda : privateBase+3*depth a≤work := by have := Nat.le_max_left (depth a) (depth b);simp only [depth] at hlayout;omega
    have hdb : privateBase+3*depth b≤work := by have := Nat.le_max_right (depth a) (depth b);simp only [depth] at hlayout;omega
    have hwa : workSize a≤workSize (.seq a b) := Nat.le_max_left _ _
    have hwb : workSize b≤workSize (.seq a b) := Nat.le_max_right _ _
    have hga : GoodFuel a privateBase out := fun r hr => hgood r (List.mem_append_left _ hr)
    have hgb : GoodFuel b privateBase out := fun r hr => hgood r (List.mem_append_right _ hr)
    have hfa : fuelBounds a s B := fun r hr => hfuels r (List.mem_append_left _ hr)
    have hfb : fuelBounds b s B := fun r hr => hfuels r (List.mem_append_right _ hr)
    obtain ⟨ta,hta,ha⟩ := iha privateBase s hp hda (fun k hk hkr => hclean k hk (by omega)) hga hfa hfields
    let u := Function.update s out (value a (inputView n s) s++s out)
    have hview : inputView n u=inputView n s := StackIndices.inputView_update n out s _ ho
    have huclean : ∀ k,privateBase≤k → k<work+workSize b → u k=[] := by
      intro k hk hkr
      have hko : k≠out := by omega
      simpa [u,Function.update,hko] using hclean k hk (by omega)
    have hufuel : ∀ r∈fuelRefs b,u r=s r := by
      intro r hr;exact Function.update_of_ne (hgb r hr).2.2 _ _
    have hufields : ∀ i : Fin n,(u i.val).length≤B := by
      intro i;change (inputView n u i).length≤B;rw [hview];exact hfields i
    have hufbounds : fuelBounds b u B := fun r hr => by rw [hufuel r hr];exact hfb r hr
    obtain ⟨tb,htb,hb⟩ := ihb privateBase u hp hdb huclean hgb hufbounds hufields
    have hval : value b (inputView n u) u=value b (inputView n s) s := value_congr b hview hufuel
    rw [hval] at hb
    have he : Function.update u out (value b (inputView n s) s++u out)=
        Function.update s out (value (.seq a b) (inputView n s) s++s out) := by
      simp [u,value,List.append_assoc]
    rw [he] at hb
    exact ⟨ta+tb+1,by simpa only [timePolynomial,Polynomial.eval_add,Polynomial.eval_one] using Nat.add_le_add_right (Nat.add_le_add hta htb) 1,Exec.seq ha hb⟩
  | branch a b yes no ihy ihn =>
    have hdy : privateBase+3*depth yes≤work := by have := Nat.le_max_left (depth yes) (depth no);simp only [depth] at hlayout;omega
    have hdn : privateBase+3*depth no≤work := by have := Nat.le_max_right (depth yes) (depth no);simp only [depth] at hlayout;omega
    have hwy : workSize yes≤workSize (.branch a b yes no) := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    have hwn : workSize no≤workSize (.branch a b yes no) := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    have hwt : StackTest.testSlots a b≤workSize (.branch a b yes no) := Nat.le_max_left _ _
    have hfTest : Fresh s work (StackTest.testSlots a b) := fun k hk hkr => hclean k (by omega) (by omega)
    have hgy : GoodFuel yes privateBase out := fun r hr => hgood r (List.mem_append_left _ hr)
    have hgn : GoodFuel no privateBase out := fun r hr => hgood r (List.mem_append_right _ hr)
    have hfy : fuelBounds yes s B := fun r hr => hfuels r (List.mem_append_left _ hr)
    have hfn : fuelBounds no s B := fun r hr => hfuels r (List.mem_append_right _ hr)
    by_cases htest : ComplexityTimeBinary.value (a.run (inputView n s)).1≤ComplexityTimeBinary.value (b.run (inputView n s)).1
    · obtain ⟨t,ht,hr⟩ := ihy privateBase s hp hdy (fun k hk hkr => hclean k hk (by omega)) hgy hfy hfields
      obtain ⟨u,hu,he⟩ := StackTest.ifLE_exec work a b (compile work privateBase out yes) (compile work privateBase out no)
        s _ B t (by omega) hfTest hfields (by simpa [StackTest.truthLE,htest] using hr)
      refine ⟨u,?_,?_⟩
      · simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_ofNat];omega
      · simpa only [value,if_pos htest] using he
    · obtain ⟨t,ht,hr⟩ := ihn privateBase s hp hdn (fun k hk hkr => hclean k hk (by omega)) hgn hfn hfields
      obtain ⟨u,hu,he⟩ := StackTest.ifLE_exec work a b (compile work privateBase out yes) (compile work privateBase out no)
        s _ B t (by omega) hfTest hfields (by simpa [StackTest.truthLE,htest] using hr)
      refine ⟨u,?_,?_⟩
      · simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_ofNat];omega
      · simpa only [value,if_neg htest] using he
  | each index fuel a b iha ihb =>
    have hcurr := hgood fuel (by simp [fuelRefs])
    have hlen := hfuels fuel (by simp [fuelRefs])
    have hdepth : privateBase+3≤work := by simp only [depth] at hlayout;omega
    have hda : privateBase+3+3*depth a≤work := by have := Nat.le_max_left (depth a) (depth b);simp only [depth] at hlayout;omega
    have hdb : privateBase+3+3*depth b≤work := by have := Nat.le_max_right (depth a) (depth b);simp only [depth] at hlayout;omega
    have hwa : workSize a≤workSize (.each index fuel a b) := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    have hwb : workSize b≤workSize (.each index fuel a b) := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    have hwi : StackIndices.slots (StackAssign.incrementExpr index)≤workSize (.each index fuel a b) := Nat.le_max_left _ _
    have hprivate : Fresh s privateBase 3 := fun k hk hkr => hclean k hk (by have := workSize_three (.each index fuel a b);omega)
    have hincrement : Fresh s work (StackIndices.slots (StackAssign.incrementExpr index)) := fun k hk hkr => hclean k (by omega) (by omega)
    let pref := fun i (bit : Bool) => if bit then value b (Function.update (inputView n s) index (StackCount.counterBits i)) s
      else value a (Function.update (inputView n s) index (StackCount.counterBits i)) s
    let C := (timePolynomial a).eval B+(timePolynomial b).eval B
    have hbody : ∀ i,i≤(s fuel).length → ∀ (bit : Bool) rest acc,
        ∃ t≤C,Exec (if bit then compile work (privateBase+3) out b else compile work (privateBase+3) out a)
          (loopState s index privateBase out (StackCount.counterBits i) rest acc)
          (loopState s index privateBase out (StackCount.counterBits i) rest (pref i bit++acc)) t := by
      intro i hi bit rest acc
      let u := loopState s index privateBase out (StackCount.counterBits i) rest acc
      have hv : inputView n u=Function.update (inputView n s) index (StackCount.counterBits i) :=
        loopState_view s index privateBase out _ _ _ ho hp
      have hbits : (StackCount.counterBits i).length≤B := (StackCount.counterBits_width i).trans (by omega)
      have huwidth : ∀ j : Fin n,(u j.val).length≤B := loopState_width s index privateBase out _ _ _ B ho hp hbits hfields
      have huf (r : ℕ) (hr : r∈fuelRefs a++fuelRefs b) : u r=s r := by
        have hg := hgood r (List.mem_cons_of_mem fuel hr)
        exact loopState_low s index privateBase out _ _ _ r hg.2.1 (by have := index.isLt;omega) hg.2.2
      cases bit
      · have hg : GoodFuel a (privateBase+3) out := by
          intro r hr;have hh := hgood r (List.mem_cons_of_mem fuel (List.mem_append_left _ hr));exact ⟨hh.1,by omega,hh.2.2⟩
        have hfb : fuelBounds a u B := by
          intro r hr;rw [huf r (List.mem_append_left _ hr)];exact hfuels r (List.mem_cons_of_mem fuel (List.mem_append_left _ hr))
        have huclean : ∀ k,privateBase+3≤k → k<work+workSize a → u k=[] := by
          intro k hk hkr;dsimp only [u];rw [loopState_high s index privateBase out _ _ _ ho hp k hk];exact hclean k (by omega) (by omega)
        obtain ⟨t,ht,hr⟩ := iha (privateBase+3) u (by omega) hda huclean hg hfb huwidth
        have hval := value_congr a hv (fun r hr => huf r (List.mem_append_left _ hr))
        rw [hval] at hr
        dsimp only [u] at hr
        rw [loopState_out s index privateBase out _ _ _,loopState_update_out s index privateBase out _ _ _ _] at hr
        exact ⟨t,ht.trans (Nat.le_add_right _ _),hr⟩
      · have hg : GoodFuel b (privateBase+3) out := by
          intro r hr;have hh := hgood r (List.mem_cons_of_mem fuel (List.mem_append_right _ hr));exact ⟨hh.1,by omega,hh.2.2⟩
        have hfb : fuelBounds b u B := by
          intro r hr;rw [huf r (List.mem_append_right _ hr)];exact hfuels r (List.mem_cons_of_mem fuel (List.mem_append_right _ hr))
        have huclean : ∀ k,privateBase+3≤k → k<work+workSize b → u k=[] := by
          intro k hk hkr;dsimp only [u];rw [loopState_high s index privateBase out _ _ _ ho hp k hk];exact hclean k (by omega) (by omega)
        obtain ⟨t,ht,hr⟩ := ihb (privateBase+3) u (by omega) hdb huclean hg hfb huwidth
        have hval := value_congr b hv (fun r hr => huf r (List.mem_append_right _ hr))
        rw [hval] at hr
        dsimp only [u] at hr
        rw [loopState_out s index privateBase out _ _ _,loopState_update_out s index privateBase out _ _ _ _] at hr
        exact ⟨t,ht.trans (Nat.le_add_left _ _),hr⟩
    obtain ⟨t,ht,hr⟩ := lexicalFor_exec work privateBase out fuel index s
      (compile work (privateBase+3) out a) (compile work (privateBase+3) out b) pref B C
      ho hp hdepth hcurr.1 hcurr.2.1 hcurr.2.2 hprivate hincrement hfields hlen hbody
    refine ⟨t,?_,hr⟩
    simpa only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,C] using ht

end BalancedAssortments.CookLevin.StackBuilder
