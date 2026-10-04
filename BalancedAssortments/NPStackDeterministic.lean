import BalancedAssortments.NPStackMachine

namespace BalancedAssortments.NPStack
variable {K Q : Type*} [DecidableEq K]

def NoChoice (P : Program K Q) : Prop := ∀ q a b,P.code q≠Instr.choice a b

def Deterministic (P : Program K Q) : Prop :=
  ∀ c d e,Step P c d → Step P c e → d=e

lemma noChoice_deterministic {P : Program K Q} (h : NoChoice P) : Deterministic P := by
  intro c d e hd he
  unfold Step successors at hd he
  cases hi : P.code c.pc with
  | halt b => simp [hi] at hd
  | jump q => simp only [hi,List.mem_singleton] at hd he; exact hd.trans he.symm
  | push k b q => simp only [hi,List.mem_singleton] at hd he; exact hd.trans he.symm
  | pop k qe qf qt =>
    cases hs : c.stk k <;> simp only [hi,hs,List.mem_singleton] at hd he <;> exact hd.trans he.symm
  | choice a b => exact False.elim (h c.pc a b hi)

lemma Run.prefix {P : Program K Q} (hdet : Deterministic P) {a b : ℕ} {c d e : Config K Q}
    (h : Run P a c d) (g : Run P b c e) (hab : a≤b) : ∃ t, b=a+t ∧ Run P t d e := by
  induction h generalizing b e with
  | zero => exact ⟨b,by omega,g⟩
  | @succ a c next d hs hr ih =>
    cases g with
    | zero => omega
    | @succ b _ next' e gs gr =>
      have heq := hdet c next next' hs gs
      subst next'
      obtain ⟨t,ht,hrest⟩ := ih gr (by omega)
      exact ⟨t,by omega,hrest⟩

lemma Run.from_halted {P : Program K Q} {n : ℕ} {c d : Config K Q} {b : Bool}
    (h : Run P n c d) (hc : P.code c.pc=.halt b) : n=0 ∧ c=d := by
  cases h with
  | zero => exact ⟨rfl,rfl⟩
  | succ hs hr => exact False.elim (halted_no_step hc hs)

/-- No deterministic execution can bypass a proved halting result. Both the
terminal configuration and its exact transition count are unique. -/
theorem Run.halted_unique {P : Program K Q} (hdet : Deterministic P)
    {a b : ℕ} {c d e : Config K Q} {x y : Bool}
    (h : Run P a c d) (g : Run P b c e) (hd : P.code d.pc=.halt x) (he : P.code e.pc=.halt y) :
    a=b ∧ d=e := by
  by_cases hab : a≤b
  · obtain ⟨t,ht,hr⟩ := h.prefix hdet g hab
    have hz := hr.from_halted hd
    exact ⟨by omega,hz.2⟩
  · obtain ⟨t,ht,hr⟩ := g.prefix hdet h (by omega)
    have hz := hr.from_halted he
    exact ⟨by omega,hz.2.symm⟩

theorem rejecting_run_excludes_acceptance {P : Program K Q} (hdet : Deterministic P)
    {a b : ℕ} {c d e : Config K Q} (h : Run P a c d) (hd : P.code d.pc=.halt false)
    (g : Run P b c e) : ¬ accepts P e := by
  intro he
  have hh := h.halted_unique hdet g hd he
  rw [hh.2] at hd
  rw [he] at hd
  cases hd

end BalancedAssortments.NPStack
