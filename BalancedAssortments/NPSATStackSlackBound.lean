import BalancedAssortments.NPSATStackSlackLoop
import BalancedAssortments.NPPolynomialPrograms

noncomputable section
namespace BalancedAssortments.NPSATStackSlack
open NPStack NPStack.Structured

def totalBudget (N : ℕ) : ℕ := slackBudget N N+emitBudget N+40*N+30
lemma buildBudget_bound (n m : ℕ) : buildBudget n m≤totalBudget (n+m) := by
  have h:=Nat.mul_le_mul_right (2*itemBudget (n+m)+10) (show m≤n+m by omega)
  unfold buildBudget totalBudget slackBudget
  omega

def runtimePolynomial : Polynomial ℕ :=
  let x : Polynomial ℕ := Polynomial.X
  let e := fun z : Polynomial ℕ => 1100*(z+1)*(z*12+4)+84*z+7
  let i := e (x+1)+5*x+25
  x*(2*i+10)+1+e x+40*x+30

lemma runtimePolynomial_eval (N : ℕ) : runtimePolynomial.eval N=totalBudget N := by
  simp [runtimePolynomial,totalBudget,slackBudget,itemBudget,emitBudget]

theorem build_run_polynomial (n m : ℕ) (wire : List Bool) :
    ∃t≤runtimePolynomial.eval (n+m),Run program t
      ⟨entry build,store (List.replicate n false) (List.replicate m false) [] [] [] [] [] wire⟩
      ⟨finish build,store (List.replicate n false) (List.replicate m false) [] [] [] [] [] (resultWire n m wire)⟩ := by
  obtain ⟨t,ht,hr⟩ := build_run n m wire
  exact ⟨t,ht.trans (by rw [runtimePolynomial_eval];exact buildBudget_bound n m),hr⟩

theorem resultWire_length (n m : ℕ) (wire : List Bool) :
    (resultWire n m wire).length≤wire.length+runtimePolynomial.eval (n+m) := by
  obtain ⟨t,ht,hr⟩ := build_run_polynomial n m wire
  have h:=hr.stack_length (.inr .wire)
  simp only [store] at h
  omega

end BalancedAssortments.NPSATStackSlack
