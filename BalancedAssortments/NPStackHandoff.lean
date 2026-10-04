import BalancedAssortments.NPStackEmbeddingReflect

namespace BalancedAssortments.NPStack.Handoff
open NPStack
variable {K Q K' Q' : Type*} [DecidableEq K] [DecidableEq K']

/-- Expand a finite subprogram, changing only successful halt into a real
return jump. Failure remains a failing halt. -/
def code (fk : K→K') (fq : Q→Q') (next : Q') : Instr K Q → Instr K' Q'
  | .halt true => .jump next
  | .halt false => .halt false
  | i => i.rename fk fq

lemma nonhalt (fk : K→K') (fq : Q→Q') (next : Q') (i : Instr K Q)
    (h : ∀ b,i≠.halt b) : code fk fq next i=i.rename fk fq := by
  cases i with
  | halt b => exact (h b rfl).elim
  | jump | push | pop | choice => rfl

lemma not_accepting (fk : K→K') (fq : Q→Q') (next : Q') (i : Instr K Q) :
    code fk fq next i≠.halt true := by
  cases i <;> simp [code,Instr.rename]
  rename_i b;cases b <;> simp [code]

lemma code_extends {P : Program K Q} {R : Program K' Q'} (fk : K→K') (fq : Q→Q') (next : Q')
    (hc : ∀ q,R.code (fq q)=code fk fq next (P.code q)) : CodeExtends P R fk fq := by
  intro q hn
  rw [hc,nonhalt fk fq next _ hn]

lemma run {P : Program K Q} {R : Program K' Q'} (fk : K→K') (fq : Q→Q') (next : Q')
    (hinj : Function.Injective fk) (hc : ∀ q,R.code (fq q)=code fk fq next (P.code q))
    {t : ℕ} {c e : Config K Q} {before after : Config K' Q'}
    (hr : Run P t c e) (ha : accepts P e) (hbefore : Relocated fk fq c before)
    (hafter : Relocated fk fq e after) (hf : Frame fk before after) :
    Run R (t+1) before ⟨next,after.stk⟩ := by
  have hsub := hr.relocate_exact fk fq hinj (code_extends fk fq next hc) hbefore hafter hf
  have hj : R.code after.pc=.jump next := by rw [hafter.1,hc,ha];rfl
  have hs : Step R after ⟨next,after.stk⟩ := by simp [Step,successors,hj]
  exact hsub.trans (.one hs)

/-- Every accepting caller execution must complete an actual accepting source
subprogram run before its return jump. Nondeterministic instructions and
arbitrary untouched caller registers are fully preserved. -/
theorem accepting_segment {P : Program K Q} {R : Program K' Q'}
    (fk : K→K') (fq : Q→Q') (next : Q') (hinj : Function.Injective fk)
    (hc : ∀ q,R.code (fq q)=code fk fq next (P.code q))
    {T : ℕ} {c : Config K Q} {before out : Config K' Q'}
    (hrel : Relocated fk fq c before) (hr : Run R T before out) (ha : accepts R out) :
    ∃ u v e after,Run P u c e ∧ accepts P e ∧ Relocated fk fq e after ∧ Frame fk before after ∧
      Run R v ⟨next,after.stk⟩ out ∧ u+1+v=T := by
  induction T generalizing c before with
  | zero =>
    cases hr
    have hh : R.code out.pc≠.halt true := by
      rw [hrel.1,hc]
      exact not_accepting fk fq next (P.code c.pc)
    exact False.elim (hh ha)
  | succ T ih =>
    cases hr with
    | @succ _ _ middle _ hs hrest =>
      by_cases hh : ∃ b,P.code c.pc=.halt b
      · obtain ⟨b,hb⟩ := hh
        cases b with
        | false =>
          have hf : R.code before.pc=.halt false := by rw [hrel.1,hc,hb];rfl
          exact False.elim (halted_no_step hf hs)
        | true =>
          have hj : R.code before.pc=.jump next := by rw [hrel.1,hc,hb];rfl
          have hm : middle=⟨next,before.stk⟩ := by simpa [Step,successors,hj] using hs
          rw [hm] at hrest
          exact ⟨0,T,c,before,.zero _,hb,hrel,(fun _ _ => rfl),hrest,by omega⟩
      · have hn : ∀ b,P.code c.pc≠.halt b := by simpa using hh
        obtain ⟨d,hd,hm,hframe⟩ := hs.reflect fk fq hinj (code_extends fk fq next hc) hrel hn
        obtain ⟨u,v,e,after,he,haccept,hend,hf,hremaining,ht⟩ := ih hm hrest
        refine ⟨u+1,v,e,after,.succ hd he,haccept,hend,?_,hremaining,by omega⟩
        intro k hk
        exact (hf k hk).trans (hframe k hk)

end BalancedAssortments.NPStack.Handoff
