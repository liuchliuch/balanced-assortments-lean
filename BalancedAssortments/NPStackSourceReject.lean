import BalancedAssortments.NPStackSourceReduction

namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros ComplexitySourceModel

def cfg (q : Stage) (s : Reg → List Bool) : Config Reg (Label Stage) := ⟨.main q,s⟩

lemma clear_output_run (s : Reg → List Bool) :
    Run program ((s .wireOut).length+1) (cfg .badClear s)
      (cfg (.badEmit 0) (Function.update s .wireOut [])) := by
  generalize hx : s .wireOut=xs
  induction xs generalizing s with
  | nil =>
    apply Run.one
    have hu : Function.update s Reg.wireOut []=s := by rw [← hx];exact Function.update_eq_self _ _
    simp [Step,successors,program,compile,code,table,cfg,hx,hu]
  | cons b bs ih =>
    let next := Function.update s Reg.wireOut bs
    have hs : Step program (cfg .badClear s) (cfg .badClear next) := by
      cases b <;> simp [Step,successors,program,compile,code,table,cfg,hx,next]
    have ht := ih next (by simp [next])
    have hh := Run.succ hs ht
    simpa [next,Function.update_idem] using hh

lemma emit_fixed_run (i : Fin (fixedNoSource.length+1)) (s : Reg → List Bool) :
    Run program (fixedNoSource.length-i.val) (cfg (.badEmit i) s)
      (cfg (.badEmit ⟨fixedNoSource.length,by omega⟩)
        (Function.update s .wireOut ((fixedNoSource.reverse.drop i.val).reverse++s .wireOut))) := by
  generalize hrem : fixedNoSource.length-i.val=n
  induction n using Nat.strong_induction_on generalizing i s with
  | h n ih =>
    by_cases hi : i.val<fixedNoSource.length
    · let j : Fin (fixedNoSource.length+1) := ⟨i.val+1,by omega⟩
      let bit := fixedNoSource.reverse.get ⟨i.val,by simpa using hi⟩
      let next := Function.update s Reg.wireOut (bit::s .wireOut)
      have hs : Step program (cfg (.badEmit i) s) (cfg (.badEmit j) next) := by
        simp [Step,successors,program,compile,code,table,cfg,hi,j,next,bit]
      have hsmall : fixedNoSource.length-j.val<n := by dsimp [j];omega
      have ht := ih _ hsmall j next rfl
      have hh := Run.succ hs ht
      have hdrop := List.drop_eq_getElem_cons (l := fixedNoSource.reverse) (by simpa using hi)
      have he : fixedNoSource.length-j.val+1=n := by dsimp [j];omega
      rw [he] at hh
      convert hh using 1
      congr 1
      rw [hdrop,List.reverse_cons,List.append_assoc]
      simp [next,Function.update_idem,j,bit]
    · have he : i.val=fixedNoSource.length := by omega
      have hi' : i=⟨fixedNoSource.length,by omega⟩ := Fin.ext he
      have hn : n=0 := by omega
      rw [hn]
      have hu : Function.update s Reg.wireOut (s .wireOut)=s := Function.update_eq_self _ _
      have hd : fixedNoSource.reverse.drop fixedNoSource.length=[] := by simp
      simpa [hi',hd,hu] using (Run.zero (P := program) (cfg (.badEmit ⟨fixedNoSource.length,by omega⟩) s))

/-- Any failure path emits the same legal no-instance, even after it has already
constructed part of an output or left parser scratch data behind. -/
theorem fixed_no_run (s : Reg → List Bool) :
    ∃ out,Run program ((s .wireOut).length+1+fixedNoSource.length) (cfg .badClear s) out ∧
      accepts program out ∧ out.stk .wireOut=fixedNoSource := by
  have h1 := clear_output_run s
  have h2 := emit_fixed_run 0 (Function.update s Reg.wireOut [])
  simp only [Fin.val_zero,Nat.sub_zero,List.drop_zero,List.reverse_reverse,
    Function.update_self,List.append_nil,Function.update_idem] at h2
  refine ⟨_,h1.trans h2,?_,by simp [cfg]⟩
  simp [accepts,program,compile,code,table,cfg]

end BalancedAssortments.NPStackSourceReduction
