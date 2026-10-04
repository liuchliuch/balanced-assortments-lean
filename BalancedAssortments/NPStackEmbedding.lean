import BalancedAssortments.NPStackMachine

namespace BalancedAssortments.NPStack

/-- Relocate finite stack/register and instruction labels. -/
def Instr.rename {K Q K' Q' : Type*} (fk : K → K') (fq : Q → Q') : Instr K Q → Instr K' Q'
  | .halt b => .halt b
  | .jump q => .jump (fq q)
  | .push k b q => .push (fk k) b (fq q)
  | .pop k qe qf qt => .pop (fk k) (fq qe) (fq qf) (fq qt)
  | .choice q r => .choice (fq q) (fq r)

variable {K Q K' Q' : Type*} [DecidableEq K] [DecidableEq K']

def Relocated (fk : K → K') (fq : Q → Q') (c : Config K Q) (d : Config K' Q') : Prop :=
  d.pc=fq c.pc ∧ ∀ k,d.stk (fk k)=c.stk k

def Frame (fk : K → K') (before after : Config K' Q') : Prop :=
  ∀ k,(∀ old,fk old≠k) → after.stk k=before.stk k

/-- Halt labels may be replaced by return jumps by the enclosing program.
Only instructions that actually take a source step need to be copied. -/
def CodeExtends (P : Program K Q) (R : Program K' Q') (fk : K → K') (fq : Q → Q') : Prop :=
  ∀ q,(∀ b,P.code q≠.halt b) → R.code (fq q)=(P.code q).rename fk fq

lemma update_relocated (fk : K → K') (hinj : Function.Injective fk)
    (s : K → List Bool) (t : K' → List Bool) (h : ∀ k,t (fk k)=s k)
    (k : K) (bits : List Bool) :
    ∀ j,(Function.update t (fk k) bits) (fk j)=(Function.update s k bits) j := by
  intro j
  by_cases he : j=k
  · subst j; simp
  · have hn : fk j≠fk k := fun hh => he (hinj hh)
    simp [Function.update,he,hn,h]

lemma update_frame (fk : K → K') (t : K' → List Bool) (k : K) (bits : List Bool) :
    ∀ j,(∀ old,fk old≠j) → (Function.update t (fk k) bits) j=t j := by
  intro j hj
  exact Function.update_of_ne (Ne.symm (hj k)) _ _

/-- One real source transition becomes one real target transition. The target
may contain other finite subroutines and arbitrary untouched work stacks. -/
theorem Step.relocate {P : Program K Q} {R : Program K' Q'}
    (fk : K → K') (fq : Q → Q') (hinj : Function.Injective fk) (hcode : CodeExtends P R fk fq)
    {c d : Config K Q} {c' : Config K' Q'} (h : Step P c d) (hc : Relocated fk fq c c') :
    ∃ d',Step R c' d' ∧ Relocated fk fq d d' ∧ Frame fk c' d' := by
  have hnh : ∀ b,P.code c.pc≠.halt b := fun b he => halted_no_step he h
  have hi := hcode c.pc hnh
  rw [← hc.1] at hi
  unfold Step successors at h
  cases hp : P.code c.pc with
  | halt b => exact False.elim (hnh b hp)
  | jump q =>
    simp only [hp,List.mem_singleton] at h
    subst d
    refine ⟨⟨fq q,c'.stk⟩,?_,⟨rfl,hc.2⟩,fun _ _ => rfl⟩
    simp [Step,successors,hi,hp,Instr.rename]
  | push k b q =>
    simp only [hp,List.mem_singleton] at h
    subst d
    refine ⟨⟨fq q,Function.update c'.stk (fk k) (b::c.stk k)⟩,?_,
      ⟨rfl,update_relocated fk hinj _ _ hc.2 k _⟩,update_frame fk _ k _⟩
    simp [Step,successors,hi,hp,Instr.rename,hc.2]
  | pop k qe qf qt =>
    cases hs : c.stk k with
    | nil =>
      simp only [hp,hs,List.mem_singleton] at h
      subst d
      refine ⟨⟨fq qe,c'.stk⟩,?_,⟨rfl,hc.2⟩,fun _ _ => rfl⟩
      simp [Step,successors,hi,hp,Instr.rename,hc.2,hs]
    | cons b bs =>
      simp only [hp,hs,List.mem_singleton] at h
      subst d
      refine ⟨⟨fq (if b then qt else qf),Function.update c'.stk (fk k) bs⟩,?_,
        ⟨rfl,update_relocated fk hinj _ _ hc.2 k _⟩,update_frame fk _ k _⟩
      cases b <;> simp [Step,successors,hi,hp,Instr.rename,hc.2,hs]
  | choice q r =>
    simp only [hp,List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with rfl | rfl
    · refine ⟨⟨fq q,c'.stk⟩,?_,⟨rfl,hc.2⟩,fun _ _ => rfl⟩
      simp [Step,successors,hi,hp,Instr.rename]
    · refine ⟨⟨fq r,c'.stk⟩,?_,⟨rfl,hc.2⟩,fun _ _ => rfl⟩
      simp [Step,successors,hi,hp,Instr.rename]

/-- Exact-count subroutine embedding; hidden work stacks are preserved. -/
theorem Run.relocate {P : Program K Q} {R : Program K' Q'}
    (fk : K → K') (fq : Q → Q') (hinj : Function.Injective fk) (hcode : CodeExtends P R fk fq)
    {t : ℕ} {c d : Config K Q} {c' : Config K' Q'} (h : Run P t c d) (hc : Relocated fk fq c c') :
    ∃ d',Run R t c' d' ∧ Relocated fk fq d d' ∧ Frame fk c' d' := by
  induction h generalizing c' with
  | zero => exact ⟨c',.zero _,hc,fun _ _ => rfl⟩
  | succ hs hr ih =>
    obtain ⟨next,hn,hrel,hframe⟩ := hs.relocate fk fq hinj hcode hc
    obtain ⟨last,hl,hlrel,hlframe⟩ := ih hrel
    exact ⟨last,.succ hn hl,hlrel,fun k hk => (hlframe k hk).trans (hframe k hk)⟩

lemma relocated_frame_unique (fk : K → K') (fq : Q → Q')
    {c : Config K Q} {before a b : Config K' Q'}
    (ha : Relocated fk fq c a) (hb : Relocated fk fq c b)
    (fa : Frame fk before a) (fb : Frame fk before b) : a=b := by
  have hp : a.pc=b.pc := ha.1.trans hb.1.symm
  have hs : a.stk=b.stk := by
    funext k
    by_cases hk : ∃ old,fk old=k
    · obtain ⟨old,rfl⟩ := hk
      exact (ha.2 old).trans (hb.2 old).symm
    · have hn : ∀ old,fk old≠k := by simpa using hk
      exact (fa k hn).trans (fb k hn).symm
  cases a; cases b; simp_all

/-- Convenient concrete-target form of exact-count subroutine relocation. -/
theorem Run.relocate_exact {P : Program K Q} {R : Program K' Q'}
    (fk : K → K') (fq : Q → Q') (hinj : Function.Injective fk) (hcode : CodeExtends P R fk fq)
    {t : ℕ} {c d : Config K Q} {c' d' : Config K' Q'} (h : Run P t c d)
    (hc : Relocated fk fq c c') (hd : Relocated fk fq d d') (hf : Frame fk c' d') :
    Run R t c' d' := by
  obtain ⟨out,hr,hrel,hframe⟩ := h.relocate fk fq hinj hcode hc
  rwa [relocated_frame_unique fk fq hrel hd hframe hf] at hr

end BalancedAssortments.NPStack
