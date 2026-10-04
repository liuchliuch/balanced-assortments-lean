import BalancedAssortments.NPMachineFiniteBridge

/-! Finite local transition tables and exact counted symbolic runs. -/
noncomputable section
namespace BalancedAssortments.NPMachine.FiniteBridge
variable {Q A : Type*} [Fintype Q] [Fintype A]

abbrev Action (Q A : Type*) := Q × Symbol A × Move

def tableRules (next : Q → Symbol A → List (Action Q A)) : List (Transition Q A) := by
  classical
  exact (Finset.univ.toList : List Q).flatMap fun q =>
    (Finset.univ.toList : List (Symbol A)).flatMap fun a =>
      (next q a).map fun x => ⟨q,a,x.1,x.2.1,x.2.2⟩

def tableProgram (start : Q) (accept : Q → Bool)
    (next : Q → Symbol A → List (Action Q A)) : Program Q A :=
  ⟨start,accept,tableRules next⟩

lemma mem_tableRules (next : Q → Symbol A → List (Action Q A)) (r : Transition Q A) :
    r ∈ tableRules next ↔ (r.target,r.write,r.move) ∈ next r.source r.read := by
  classical
  unfold tableRules
  simp only [List.mem_flatMap,List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨q,a,x,hx,rfl⟩
    exact hx
  · intro h
    exact ⟨r.source,r.read,(r.target,r.write,r.move),h,by cases r;rfl⟩

lemma table_step (start : Q) (accept : Q → Bool)
    (next : Q → Symbol A → List (Action Q A)) (c d : Configuration Q A) :
    Step (tableProgram start accept next) c d ↔
      ∃ x ∈ next c.state (c.tape c.head),
        d=⟨x.1,c.head+x.2.2.displacement,Function.update c.tape c.head x.2.1⟩ := by
  constructor
  · rintro ⟨r,hr,hs,ht,rfl⟩
    have hm := (mem_tableRules next r).1 hr
    rw [← hs,← ht] at hm
    exact ⟨(r.target,r.write,r.move),hm,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨⟨c.state,c.tape c.head,x.1,x.2.1,x.2.2⟩,?_,rfl,rfl,rfl⟩
    exact (mem_tableRules next _).2 hx

lemma Run.trans {P : Program Q A} {s t : ℕ} {a b c : Configuration Q A}
    (h : Run P s a b) (g : Run P t b c) : Run P (s+t) a c := by
  induction h with
  | zero => simpa using g
  | succ hs hr ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Run.succ hs (ih g)

lemma Run.one {P : Program Q A} {a b : Configuration Q A} (h : Step P a b) : Run P 1 a b :=
  .succ h (.zero b)

end BalancedAssortments.NPMachine.FiniteBridge
