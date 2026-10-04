import BalancedAssortments.NPStackClockedProgram

namespace BalancedAssortments.NPStack.Clocked
open NPStack NPStack.Macros

lemma clear_run (P C : FiniteProgram) (fallback : List Bool) (s : Stack P.K C.K → List Bool) :
    Run (program P C fallback) ((s (output P C)).length+1) ⟨.clear,s⟩
      ⟨.emit 0,Function.update s (output P C) []⟩ := by
  generalize he : s (output P C)=xs
  induction xs generalizing s with
  | nil =>
    apply Run.one
    have hh : Function.update s (output P C) []=s := by rw [← he,Function.update_eq_self]
    simp [Step,successors,program,code,he,hh]
  | cons b bs ih =>
    have hs : Step (program P C fallback) ⟨.clear,s⟩ ⟨.clear,Function.update s (output P C) bs⟩ := by
      cases b <;> simp [Step,successors,program,code,he]
    have ht := ih (Function.update s (output P C) bs) (by simp)
    simpa using Run.succ hs ht

lemma emit_suffix (P C : FiniteProgram) (fallback : List Bool) (rest pre : List Bool)
    (hsplit : pre++rest=fallback.reverse) (s : Stack P.K C.K → List Bool) (out : List Bool) :
    Run (program P C fallback) (rest.length+1)
      ⟨.emit ⟨pre.length,by have hh:=congrArg List.length hsplit;simp only [List.length_append,List.length_reverse] at hh;omega⟩,
        Function.update s (output P C) out⟩
      ⟨.accept,Function.update s (output P C) (rest.reverse++out)⟩ := by
  induction rest generalizing pre out with
  | nil =>
    have hp : pre=fallback.reverse := by simpa using hsplit
    subst pre
    apply Run.one
    simp [Step,successors,program,code]
  | cons b bs ih =>
    have hlen : pre.length+1+bs.length=fallback.length := by
      have hh:=congrArg List.length hsplit
      simp only [List.length_append,List.length_cons,List.length_reverse] at hh;omega
    let i : Fin (fallback.length+1) := ⟨pre.length,by omega⟩
    let next : Fin (fallback.length+1) := ⟨(pre++[b]).length,by simp;omega⟩
    have hi : fallback.reverse[i.val]?=some b := by
      dsimp only [i]
      rw [← hsplit,List.getElem?_append_right (by omega)];simp
    have hn : nextIndex i=next := by
      apply Fin.ext
      simp only [nextIndex,i,next,List.length_append,List.length_cons,List.length_nil];omega
    have hsplit' : (pre++[b])++bs=fallback.reverse := by simpa [List.append_assoc] using hsplit
    have hs : Step (program P C fallback) ⟨.emit i,Function.update s (output P C) out⟩
        ⟨.emit next,Function.update s (output P C) (b::out)⟩ := by
      simp [Step,successors,program,code,hi,hn]
    have hr := ih (pre++[b]) hsplit' (b::out)
    have hh := Run.succ hs hr
    simpa [List.reverse_cons,List.append_assoc] using hh

theorem fallback_run (P C : FiniteProgram) (fallback : List Bool) (s : Stack P.K C.K → List Bool) :
    Run (program P C fallback) ((s (output P C)).length+fallback.length+2) ⟨.clear,s⟩
      ⟨.accept,Function.update s (output P C) fallback⟩ := by
  have h1 := clear_run P C fallback s
  have h2 := emit_suffix P C fallback fallback.reverse [] rfl s []
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h2
  have hh := h1.trans h2
  convert hh using 1 <;> omega

end BalancedAssortments.NPStack.Clocked
