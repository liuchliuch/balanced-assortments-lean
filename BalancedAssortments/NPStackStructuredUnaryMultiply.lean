import BalancedAssortments.NPStackStructuredUnary

namespace BalancedAssortments.NPStack.Structured
open NPStack
variable {K : Type*} [DecidableEq K]

def pushZeros (n : ℕ) (target : K) : Block K :=
  match n with
  | 0 => .skip
  | n+1 => .seq (.push target false) (pushZeros n target)
lemma pushZeros_exec (n : ℕ) (target : K) (s : Store K) :
    Exec (pushZeros n target) s (Function.update s target (List.replicate n false++s target)) (2*n+1) := by
  induction n generalizing s with
  | zero => simpa [pushZeros] using Exec.skip s
  | succ n ih =>
    let u := Function.update s target (false::s target)
    have hr := ih u
    have he : Function.update u target (List.replicate n false++u target)=
        Function.update s target (List.replicate (n+1) false++s target) := by
      simp [u,List.replicate_succ',List.append_assoc]
    rw [he] at hr
    have hh := Exec.seq (Exec.push s target false) hr
    convert hh using 1 <;> omega

structure UnaryRegisters (K : Type*) where
  counter : K
  source : K
  scratch : K
  work : K
  target : K

def UnaryRegisters.map (r : UnaryRegisters K) : Fin 5 → K :=
  ![r.counter,r.source,r.scratch,r.work,r.target]
noncomputable def unaryMultiply (r : UnaryRegisters K) : Block K :=
  let body := unaryCount r.source r.scratch r.work r.target
  .loop r.counter body body

lemma unaryMultiply_exec (r : UnaryRegisters K) (hi : Function.Injective r.map) (s : Store K)
    (hs : s r.scratch=[]) (hw : s r.work=[]) :
    Exec (unaryMultiply r) s
      (drainStore s r.counter r.target ((s r.counter).length*(s r.source).length))
      ((8*(s r.source).length+6)*(s r.counter).length+1) := by
  have hneq (i j : Fin 5) (h : i≠j) : r.map i≠r.map j := fun he => h (hi he)
  have hcs : r.counter≠r.source := hneq 0 1 (by decide)
  have hcw : r.counter≠r.work := hneq 0 3 (by decide)
  have hcx : r.counter≠r.scratch := hneq 0 2 (by decide)
  have hct : r.counter≠r.target := hneq 0 4 (by decide)
  have hsx : r.source≠r.scratch := hneq 1 2 (by decide)
  have hsw : r.source≠r.work := hneq 1 3 (by decide)
  have hst : r.source≠r.target := hneq 1 4 (by decide)
  have hxw : r.scratch≠r.work := hneq 2 3 (by decide)
  have hxt : r.scratch≠r.target := hneq 2 4 (by decide)
  have hwt : r.work≠r.target := hneq 3 4 (by decide)
  have hcopy : Function.Injective (Macros.copyMap r.source r.work r.scratch) := by
    intro a b hab
    cases a <;> cases b <;> simp_all [Macros.copyMap]
  generalize he : s r.counter=xs
  induction xs generalizing s with
  | nil =>
    have hend : drainStore s r.counter r.target (0*(s r.source).length)=s := by
      funext k
      by_cases hk : k=r.counter
      · subst k;simp [drainStore,Function.update,hct,he]
      · by_cases ht : k=r.target
        · subst k;simp [drainStore]
        · simp [drainStore,Function.update,hk,ht]
    simp only [List.length_nil,Nat.mul_zero]
    rw [hend]
    exact Exec.loop_nil he
  | cons b bs ih =>
    let u := Function.update s r.counter bs
    let v := Function.update u r.target (List.replicate (u r.source).length false++u r.target)
    have us : u r.source=s r.source := Function.update_of_ne (Ne.symm hcs) _ _
    have ux : u r.scratch=[] := by simp [u,Function.update,Ne.symm hcx,hs]
    have uw : u r.work=[] := by simp [u,Function.update,Ne.symm hcw,hw]
    have vc : v r.counter=bs := by simp [v,u,Function.update,hct]
    have vs : v r.source=s r.source := by simp [v,Function.update,hst,us]
    have vx : v r.scratch=[] := by simp [v,Function.update,hxt,ux]
    have vw : v r.work=[] := by simp [v,Function.update,hwt,uw]
    have hb := unaryCount_exec r.source r.scratch r.work r.target hcopy (Ne.symm hxw) hxt hsx u ux uw
    change Exec (unaryCount r.source r.scratch r.work r.target) u v (8*(u r.source).length+4) at hb
    have hr := ih v vx vw vc
    rw [vs] at hr
    rw [us] at hb
    have hend : drainStore v r.counter r.target (bs.length*(s r.source).length)=
        drainStore s r.counter r.target ((bs.length+1)*(s r.source).length) := by
      funext k
      by_cases ht : k=r.target
      · subst k
        simp [drainStore,v,u,Function.update,Ne.symm hct,Ne.symm hcs,Nat.add_mul,List.replicate_add,List.append_assoc,-List.replicate_append_replicate]
      · by_cases hk : k=r.counter
        · subst k;simp [drainStore,Function.update,hct]
        · simp [drainStore,v,u,Function.update,ht,hk]
    rw [hend] at hr
    have hall : Exec (unaryMultiply r) s
        (drainStore s r.counter r.target ((bs.length+1)*(s r.source).length))
        ((8*(s r.source).length+4)+((8*(s r.source).length+6)*bs.length+1)+2) := by
      cases b
      · exact Exec.loop_false he hb hr
      · exact Exec.loop_true he hb hr
    convert hall using 1 <;> simp only [List.length_cons,Nat.mul_add,Nat.mul_one] <;> omega

end BalancedAssortments.NPStack.Structured
