import BalancedAssortments.NPStackEmbedding
import BalancedAssortments.NPStackDeterministic

namespace BalancedAssortments.NPStack
variable {K Q K' Q' : Type*} [DecidableEq K] [DecidableEq K']

/-- Reflect one actual target instruction inside an embedded nonhalting
subroutine. Choices may be nondeterministic; no global determinism is assumed. -/
theorem Step.reflect {P : Program K Q} {R : Program K' Q'}
    (fk : K→K') (fq : Q→Q') (hinj : Function.Injective fk) (hcode : CodeExtends P R fk fq)
    {c : Config K Q} {c' d' : Config K' Q'} (hc : Relocated fk fq c c')
    (hn : ∀ b,P.code c.pc≠.halt b) (h : Step R c' d') :
    ∃ d,Step P c d ∧ Relocated fk fq d d' ∧ Frame fk c' d' := by
  have hi := hcode c.pc hn
  rw [← hc.1] at hi
  unfold Step successors at h
  rw [hi] at h
  cases hp : P.code c.pc with
  | halt b => exact False.elim (hn b hp)
  | jump q =>
    simp only [hp,Instr.rename,List.mem_singleton] at h
    subst d'
    exact ⟨⟨q,c.stk⟩,by simp [Step,successors,hp],⟨rfl,hc.2⟩,fun _ _ => rfl⟩
  | push k b q =>
    simp only [hp,Instr.rename,List.mem_singleton] at h
    subst d'
    refine ⟨⟨q,Function.update c.stk k (b::c.stk k)⟩,by simp [Step,successors,hp],⟨rfl,?_⟩,?_⟩
    · rw [hc.2 k]
      exact update_relocated fk hinj _ _ hc.2 k _
    · exact update_frame fk _ k _
  | pop k qe qf qt =>
    cases hs : c.stk k with
    | nil =>
      simp only [hp,Instr.rename,hc.2 k,hs,List.mem_singleton] at h
      subst d'
      exact ⟨⟨qe,c.stk⟩,by simp [Step,successors,hp,hs],⟨rfl,hc.2⟩,fun _ _ => rfl⟩
    | cons b bs =>
      simp only [hp,Instr.rename,hc.2 k,hs,List.mem_singleton] at h
      subst d'
      refine ⟨⟨if b then qt else qf,Function.update c.stk k bs⟩,?_,⟨?_,?_⟩,?_⟩
      · simp [Step,successors,hp,hs]
      · cases b <;> rfl
      · exact update_relocated fk hinj _ _ hc.2 k bs
      · exact update_frame fk _ k bs
  | choice q r =>
    simp only [hp,Instr.rename,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at h
    rcases h with rfl | rfl
    · exact ⟨⟨q,c.stk⟩,by simp [Step,successors,hp],⟨rfl,hc.2⟩,fun _ _ => rfl⟩
    · exact ⟨⟨r,c.stk⟩,by simp [Step,successors,hp],⟨rfl,hc.2⟩,fun _ _ => rfl⟩

/-- Local instruction determinism, without a global restriction on other
phases of the enclosing program. -/
def UniqueStep (P : Program K Q) (c : Config K Q) : Prop :=
  ∀ d e,Step P c d → Step P c e → d=e

lemma uniqueStep_of_code {P : Program K Q} {c : Config K Q}
    (hn : ∀ a b,P.code c.pc≠.choice a b) : UniqueStep P c := by
  intro d e hd he
  unfold Step successors at hd he
  cases hi : P.code c.pc with
  | halt b => simp [hi] at hd
  | jump q => simp only [hi,List.mem_singleton] at hd he; exact hd.trans he.symm
  | push k b q => simp only [hi,List.mem_singleton] at hd he; exact hd.trans he.symm
  | pop k qe qf qt =>
    cases hs : c.stk k <;> simp only [hi,hs,List.mem_singleton] at hd he <;> exact hd.trans he.symm
  | choice a b => exact False.elim (hn a b hi)

inductive DeterministicRun (P : Program K Q) : ℕ → Config K Q → Config K Q → Prop
  | zero (c) : DeterministicRun P 0 c c
  | succ {t c d e} : UniqueStep P c → Step P c d → DeterministicRun P t d e → DeterministicRun P (t+1) c e

lemma DeterministicRun.toRun {P : Program K Q} {t : ℕ} {c d : Config K Q}
    (h : DeterministicRun P t c d) : Run P t c d := by
  induction h with
  | zero c => exact .zero c
  | succ _ hs _ ih => exact .succ hs ih

lemma DeterministicRun.trans {P : Program K Q} {a b : ℕ} {c d e : Config K Q}
    (h : DeterministicRun P a c d) (g : DeterministicRun P b d e) : DeterministicRun P (a+b) c e := by
  induction h with
  | zero => simpa using g
  | succ hu hs hr ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using DeterministicRun.succ hu hs (ih g)

lemma DeterministicRun.prefix {P : Program K Q} {a b : ℕ} {c d e : Config K Q}
    (h : DeterministicRun P a c d) (g : Run P b c e) (hab : a≤b) :
    ∃ t,b=a+t ∧ Run P t d e := by
  induction h generalizing b e with
  | zero => exact ⟨b,by omega,g⟩
  | @succ a c next d hu hs hr ih =>
    cases g with
    | zero => omega
    | @succ b _ next' e gs gr =>
      have he := hu next next' hs gs
      subst next'
      obtain ⟨t,ht,hrest⟩ := ih gr (by omega)
      exact ⟨t,by omega,hrest⟩

lemma DeterministicRun.after_shorter {P : Program K Q} {a b : ℕ} {c d e : Config K Q}
    (h : DeterministicRun P a c d) (g : Run P b c e) (hab : b≤a) :
    ∃ t,a=b+t ∧ DeterministicRun P t e d := by
  induction g generalizing a d with
  | zero => exact ⟨a,by omega,h⟩
  | @succ b c next e gs gr ih =>
    cases h with
    | zero => omega
    | @succ a _ next' d hu hs hr =>
      have he := hu next next' gs hs
      subst next'
      obtain ⟨t,ht,hrest⟩ := ih hr (by omega)
      exact ⟨t,by omega,hrest⟩

/-- Any accepting enclosing run must finish the complete deterministic
subroutine prefix. Nondeterminism after its return is unrestricted. -/
theorem DeterministicRun.factor_halted {P : Program K Q} {a b : ℕ} {c d e : Config K Q} {accepted : Bool}
    (h : DeterministicRun P a c d) (g : Run P b c e) (he : P.code e.pc=.halt accepted) :
    ∃ t,b=a+t ∧ Run P t d e := by
  by_cases hab : a≤b
  · exact h.prefix g hab
  · obtain ⟨t,ht,hr⟩ := h.after_shorter g (by omega)
    have hz := hr.toRun.from_halted he
    omega

end BalancedAssortments.NPStack
