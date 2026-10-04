import BalancedAssortments.CookLevinStackBuilderLoop

noncomputable section
namespace BalancedAssortments.CookLevin.StackBuilder
open NPCNF NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)
open StackAssign

lemma loopState_enter {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ) (xs : List Bool)
    (ho : n≤out) (hp : out<p) :
    Function.update (Function.update (Function.update s (p+2) (s index.val)) index.val []) p xs=
      loopState s index p out [] xs (s out) := by
  have hi := index.isLt
  have hio : index.val≠out := by omega
  have hip : index.val≠p := by omega
  funext k
  by_cases hk : k=out
  · subst k;simp [loopState,Function.update,Ne.symm hio,show out≠p by omega,show out≠p+2 by omega]
  · by_cases hki : k=index.val
    · subst k;simp [loopState,Function.update,hio,hip]
    · by_cases hkp : k=p
      · subst k;simp [loopState,Function.update,show p≠out by omega,Ne.symm hip]
      · by_cases hks : k=p+2
        · subst k;simp [loopState,Function.update,show p+2≠out by omega,show p+2≠index.val by omega]
        · simp [loopState,Function.update,hk,hki,hkp,hks]

lemma loopState_leave {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ) (acc : List Bool)
    (ho : n≤out) (hp : out<p) (hc : s p=[]) (hs : s (p+2)=[]) :
    Function.update (loopState s index p out (s index.val) [] acc) (p+2) []=Function.update s out acc := by
  have hi := index.isLt
  funext k
  by_cases hk : k=out
  · subst k;simp [loopState,Function.update,show out≠p+2 by omega]
  · by_cases hki : k=index.val
    · subst k;simp [loopState,Function.update,show index.val≠out by omega,show index.val≠p+2 by omega]
    · by_cases hkp : k=p
      · subst k;simp [loopState,Function.update,show p≠out by omega,show p≠index.val by omega,hc]
      · by_cases hks : k=p+2
        · subst k;simp [Function.update,show p+2≠out by omega,hs]
        · simp [loopState,Function.update,hk,hki,hkp,hks]

/-- Full lexical loop realization: save/restore the bound index, preserve the
read-only fuel, and restore every private counter/scratch register. -/
theorem lexicalFor_exec {n : ℕ} (work p out fuel : ℕ) (index : Fin n) (s : Store ℕ)
    (bodyFalse bodyTrue : Block ℕ) (pref : ℕ → Bool → List Bool) (B C : ℕ)
    (ho : n≤out) (hp : out<p) (hwp : p+3≤work)
    (hfn : n≤fuel) (hfp : fuel<p) (hfo : fuel≠out)
    (hprivate : Fresh s p 3) (hwork : Fresh s work (StackIndices.slots (incrementExpr index)))
    (hs : ∀ j : Fin n,(s j.val).length≤B) (hfB : (s fuel).length+1≤B)
    (hbody : ∀ i,i≤(s fuel).length → ∀ bit rest acc,
      ∃ t≤C,Exec (if bit then bodyTrue else bodyFalse)
        (loopState s index p out (StackCount.counterBits i) rest acc)
        (loopState s index p out (StackCount.counterBits i) rest (pref i bit++acc)) t) :
    ∃ t≤B*(C+(assignTime (incrementExpr index)).eval B+16)+64*(B+1)+64,
      Exec (lexicalFor work p index fuel bodyFalse bodyTrue) s
        (Function.update s out (loopValue pref 0 (s fuel)++s out)) t := by
  have hid := index.isLt
  have hidxp : index.val<p := by omega
  have hidxfuel : index.val≠fuel := by omega
  have h0 : s p=[] := hprivate p (by omega) (by omega)
  have h1 : s (p+1)=[] := hprivate (p+1) (by omega) (by omega)
  have h2 : s (p+2)=[] := hprivate (p+2) (by omega) (by omega)
  have hiSave : Function.Injective (Macros.copyMap index.val (p+1) (p+2)) := by
    intro a b he;cases a <;> cases b <;> simp only [Macros.copyMap] at he <;> first | rfl | omega
  have hsave := copyAtom_run index.val (p+1) (p+2) hiSave s h1
  rw [h2,List.append_nil] at hsave
  let a := Function.update s (p+2) (s index.val)
  have hai : a index.val=s index.val := by simp [a,Function.update,show index.val≠p+2 by omega]
  have hclear := clearStack_exec index.val a
  rw [hai] at hclear
  let b := Function.update a index.val []
  have hbf : b fuel=s fuel := by simp [b,a,Function.update,Ne.symm hidxfuel,show fuel≠p+2 by omega]
  have hb0 : b p=[] := by simp [b,a,Function.update,show p≠index.val by omega,h0]
  have hb1 : b (p+1)=[] := by simp [b,a,Function.update,show p+1≠index.val by omega,h1]
  have hiFuel : Function.Injective (Macros.copyMap fuel (p+1) p) := by
    intro a b he;cases a <;> cases b <;> simp only [Macros.copyMap] at he <;> first | rfl | omega
  have hcopy := copyAtom_run fuel (p+1) p hiFuel b hb1
  rw [hbf,hb0,List.append_nil] at hcopy
  rw [loopState_enter s index p out (s fuel) ho hp] at hcopy
  obtain ⟨tc,htc,hcore⟩ := coreLoop_exec work p out index s bodyFalse bodyTrue pref (s fuel).length B C
    ho hp hwp hwork hs hfB hbody (s fuel) 0 (s out) (by omega)
  simp only [Nat.zero_add,StackCount.counterBits_zero] at hcore
  let acc := loopValue pref 0 (s fuel)++s out
  let last := loopState s index p out (StackCount.counterBits (s fuel).length) [] acc
  have hlasti : last index.val=StackCount.counterBits (s fuel).length := loopState_index s index p out _ _ _ ho
  have hfinishClear := clearStack_exec index.val last
  rw [hlasti,loopState_update_index s index p out _ [] [] acc ho] at hfinishClear
  let c := loopState s index p out [] [] acc
  have hcs : c (p+2)=s index.val := loopState_saved s index p out _ _ _ ho hp
  have hci : c index.val=[] := loopState_index s index p out _ _ _ ho
  have hc1 : c (p+1)=[] := (loopState_scratch s index p out _ _ _ ho hp).trans h1
  have hiRestore : Function.Injective (Macros.copyMap (p+2) (p+1) index.val) := by
    intro a b he;cases a <;> cases b <;> simp only [Macros.copyMap] at he <;> first | rfl | omega
  have hrestore := copyAtom_run (p+2) (p+1) index.val hiRestore c hc1
  rw [hcs,hci,List.append_nil,loopState_update_index s index p out [] (s index.val) [] acc ho] at hrestore
  let d := loopState s index p out (s index.val) [] acc
  have hds : d (p+2)=s index.val := loopState_saved s index p out _ _ _ ho hp
  have hfinish := clearStack_exec (p+2) d
  rw [hds,loopState_leave s index p out acc ho hp h0 h2] at hfinish
  have hh := Exec.seq hsave (Exec.seq hclear (Exec.seq hcopy (Exec.seq hcore
    (Exec.seq hfinishClear (Exec.seq hrestore hfinish)))))
  refine ⟨_,?_,hh⟩
  have hiB := hs index
  have hmB := (StackCount.counterBits_width (s fuel).length).trans hfB
  have hmul := Nat.mul_le_mul_right (C+(assignTime (incrementExpr index)).eval B+3)
    (show (s fuel).length≤B by omega)
  nlinarith

end BalancedAssortments.CookLevin.StackBuilder
