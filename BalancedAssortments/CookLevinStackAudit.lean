import BalancedAssortments.CookLevinStackTableauProgram
import BalancedAssortments.CookLevinStackTypedCorrect
import BalancedAssortments.CookLevinStackTypedValid

/-! Independent boundary regressions for the operational Cook–Levin path.
These are kernel-checked consequences of the literal machine semantics. -/
namespace BalancedAssortments.CookLevin.StackTableau.Audit
open NPCNF NPMachine

def acceptNoRules : Machine := ⟨0,0,0,fun _=>true,[]⟩
def rejectNoRules : Machine := ⟨0,0,0,fun _=>false,[]⟩

lemma accepting_zero_rules (word : List Bool) (T : ℕ) : Sat (raw acceptNoRules word T).decode.formula := by
  rw [raw_satisfiable_iff]
  exact ⟨0,Nat.zero_le T,_,.zero _,rfl⟩

lemma rejecting_zero_rules (word : List Bool) (T : ℕ) : ¬Sat (raw rejectNoRules word T).decode.formula := by
  rw [raw_satisfiable_iff]
  rintro ⟨t,ht,c,hr,hc⟩
  exact Bool.false_ne_true hc

example : Sat (raw acceptNoRules [] 0).decode.formula := accepting_zero_rules [] 0
example : ¬Sat (raw rejectNoRules [] 0).decode.formula := rejecting_zero_rules [] 0
example : Sat (raw acceptNoRules [false,true] 0).decode.formula := accepting_zero_rules _ _
example : (raw rejectNoRules [] 0).decode.Valid := raw_valid _ _ _
example : (raw acceptNoRules [] 0).catalog.length=5 := by decide

example (M : Machine) : ((windowInitial M [false,true] 0).tape ⟨0,by simp [windowWidth]⟩).val=0 :=
  initial_hm M [false,true] 0 ⟨0,by decide⟩
example (M : Machine) : ((windowInitial M [false,true] 0).tape ⟨1,by simp [windowWidth]⟩).val=1 :=
  initial_hm M [false,true] 0 ⟨1,by decide⟩
example (M : Machine) : ((windowInitial M [false,true] 0).tape ⟨2,by simp [windowWidth]⟩).val=2 :=
  initial_hr M [false,true] 0 ⟨0,by decide⟩

end BalancedAssortments.CookLevin.StackTableau.Audit
