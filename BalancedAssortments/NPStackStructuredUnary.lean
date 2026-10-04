import BalancedAssortments.NPStackStructuredAtoms

/-! Concrete reusable unary stack routines, compiled by the structured finite
control-graph compiler. Input-dependent iteration always pops an actual stack. -/
namespace BalancedAssortments.NPStack.Structured
open NPStack
variable {K : Type*} [DecidableEq K]

def unaryDrain (source target : K) : Block K :=
  .loop source (.push target false) (.push target false)

def drainStore (s : Store K) (source target : K) (n : ℕ) : Store K :=
  Function.update (Function.update s source []) target (List.replicate n false++s target)

lemma unaryDrain_exec (source target : K) (hne : source≠target) (s : Store K) :
    Exec (unaryDrain source target) s (drainStore s source target (s source).length)
      (3*(s source).length+1) := by
  generalize he : s source=xs
  induction xs generalizing s with
  | nil =>
    have hh : drainStore s source target 0=s := by
      funext k
      by_cases hk : k=source
      · subst k;simp [drainStore,Function.update,hne,he]
      · by_cases ht : k=target
        · subst k;simp [drainStore]
        · simp [drainStore,Function.update,hk,ht]
    simp only [List.length_nil,Nat.mul_zero,Nat.zero_add]
    rw [hh]
    exact Exec.loop_nil he
  | cons b bs ih =>
    let u := Function.update s source bs
    let v := Function.update u target (false::u target)
    have hu : u target=s target := Function.update_of_ne (Ne.symm hne) _ _
    have hv : v source=bs := by simp [v,u,Function.update,hne]
    have hi := ih v hv
    have hend : drainStore v source target bs.length=drainStore s source target (bs.length+1) := by
      funext k
      by_cases ht : k=target
      · subst k
        simp [drainStore,v,hu,List.replicate_succ',List.append_assoc]
      · by_cases hk : k=source
        · subst k;simp [drainStore,Function.update,hne]
        · simp [drainStore,v,u,Function.update,ht,hk]
    rw [hend] at hi
    have hb : Exec (.push target false) u v 1 := Exec.push u target false
    have hh : Exec (unaryDrain source target) s (drainStore s source target (bs.length+1)) (1+(3*bs.length+1)+2) := by
      cases b
      · exact Exec.loop_false he hb hi
      · exact Exec.loop_true he hb hi
    simpa only [List.length_cons] using (show Exec (unaryDrain source target) s
      (drainStore s source target (bs.length+1)) (3*(bs.length+1)+1) from by convert hh using 1 <;> omega)

noncomputable def unaryCount (source scratch work target : K) : Block K :=
  .seq (.atom (copyAtom source work scratch)) (unaryDrain scratch target)

lemma unaryCount_exec (source scratch work target : K)
    (hcopy : Function.Injective (Macros.copyMap source work scratch))
    (hws : work≠scratch) (hst : scratch≠target) (hss : source≠scratch)
    (s : Store K) (hs : s scratch=[]) (hw : s work=[]) :
    Exec (unaryCount source scratch work target) s
      (Function.update s target (List.replicate (s source).length false++s target))
      (8*(s source).length+4) := by
  have hc := copyAtom_run source work scratch hcopy s hw
  simp only [hs,List.append_nil] at hc
  let u := Function.update s scratch (s source)
  have hu : u scratch=s source := by simp [u]
  have hd := unaryDrain_exec scratch target hst u
  rw [hu] at hd
  have he : drainStore u scratch target (s source).length=
      Function.update s target (List.replicate (s source).length false++s target) := by
    funext k
    by_cases ht : k=target
    · subst k;simp [drainStore,u,Function.update,hst,Ne.symm hst]
    · by_cases hk : k=scratch
      · subst k;simp [drainStore,u,Function.update,hst,hs]
      · simp [drainStore,u,Function.update,ht,hk,hst,Ne.symm hst]
  rw [he] at hd
  have hh := Exec.seq hc hd
  change Exec (unaryCount source scratch work target) s _ _ at hh
  convert hh using 1 <;> omega

def clearStack (k : K) : Block K := .loop k .skip .skip
lemma clearStack_exec (k : K) (s : Store K) :
    Exec (clearStack k) s (Function.update s k []) (3*(s k).length+1) := by
  generalize he : s k=xs
  induction xs generalizing s with
  | nil =>
    have hh : Function.update s k []=s := by rw [← he];exact Function.update_eq_self k s
    rw [hh]
    exact Exec.loop_nil he
  | cons b bs ih =>
    let u := Function.update s k bs
    have hu : u k=bs := by simp [u]
    have hr := ih u hu
    have hh : Function.update u k []=Function.update s k [] := by simp [u]
    rw [hh] at hr
    have hstep : Exec .skip u u 1 := Exec.skip u
    have hall : Exec (clearStack k) s (Function.update s k []) (1+(3*bs.length+1)+2) := by
      cases b
      · exact Exec.loop_false he hstep hr
      · exact Exec.loop_true he hstep hr
    convert hall using 1 <;> simp only [List.length_cons] <;> omega

end BalancedAssortments.NPStack.Structured
