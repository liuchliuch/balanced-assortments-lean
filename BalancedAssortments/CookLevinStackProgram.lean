import BalancedAssortments.CookLevinStackInitializeProgram
import BalancedAssortments.CookLevinStackBuilderCorrect

/-! Actual finite primitive-stack realization of any fixed well-formed streaming
schema on the fully constructed tableau environment. Only the final formula
semantics remains schema-specific. -/
noncomputable section
namespace BalancedAssortments.CookLevin.StackInitialize
open NPCNF NPMachine NPStack NPStack.Structured

lemma polynomial_compose_eval (p : Polynomial ℕ) {f : ℕ → ℕ} (hf : NatPolynomial f) :
    NatPolynomial (fun n => p.eval (f n)) := by
  obtain ⟨q,hq⟩ := hf
  exact ⟨p.comp q,by intro n;simp [hq,Polynomial.eval_comp]⟩

lemma countBatchBudget_polynomial (bs : List (Fin 9 × ℕ)) {f : ℕ → ℕ} (hf : NatPolynomial f) :
    NatPolynomial (fun n => countBatchBudget (f n) bs) := by
  induction bs with
  | nil => exact polynomial_constant 1
  | cons b bs ih =>
    have hp := polynomial_compose_eval (StackAssign.assignTime (StackAssign.incrementExpr b.1)) hf
    dsimp only [countBatchBudget,StackCount.countBudget]
    close_poly

lemma initializeBudget_polynomial (M : Machine) (e : FuelExpr) :
    NatPolynomial (initializeBudget M e) := by
  have hp := countBatchBudget_polynomial counts (bound_polynomial M e.polynomial)
  change NatPolynomial (fun n => initializeBudget M e n)
  dsimp only [initializeBudget]
  close_poly

namespace InitializedBuilder
open StackBuilder

def fuelAllowed (p : Builder 9) : Prop :=
  ∀ r∈fuelRefs p,r∈([9,11,12,13,14,15] : List ℕ)

def output (M : Machine) (e : FuelExpr) (p : Builder 9) (word : List Bool) : List Bool :=
  value p (scalarEnv M word (e.polynomial.eval word.length)) (specStore M word (e.polynomial.eval word.length))

def code (M : Machine) (e : FuelExpr) (p : Builder 9) : Block ℕ :=
  .seq (initializeBlock M e) (compile (50+3*depth p) 50 10 p)
def budget (M : Machine) (e : FuelExpr) (p : Builder 9) (n : ℕ) : ℕ :=
  initializeBudget M e n+(timePolynomial p).eval (bound M n (e.polynomial.eval n))+1

lemma budget_polynomial (M : Machine) (e : FuelExpr) (p : Builder 9) : NatPolynomial (budget M e p) := by
  have hi := initializeBudget_polynomial M e
  have hb := polynomial_compose_eval (timePolynomial p) (bound_polynomial M e.polynomial)
  change NatPolynomial (fun n => budget M e p n)
  dsimp only [budget]
  close_poly

lemma code_exec (M : Machine) (e : FuelExpr) (p : Builder 9) (hp : fuelAllowed p) (word : List Bool) :
    ∃ t≤budget M e p word.length,
      Exec (code M e p) (inputStore word)
        (Function.update (specStore M word (e.polynomial.eval word.length)) 10 (output M e p word)) t := by
  obtain ⟨t,ht,hr⟩ := initialize_exec M e word
  have hg : GoodFuel p 50 10 := by
    intro r h
    have hh := hp r h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have hb : fuelBounds p (specStore M word (e.polynomial.eval word.length)) (bound M word.length (e.polynomial.eval word.length)) := by
    intro r h
    exact specStore_fuel_width M word _ r (hp r h)
  obtain ⟨t',ht',hr'⟩ := compile_exec p (50+3*depth p) 50 10 (specStore M word (e.polynomial.eval word.length))
    (bound M word.length (e.polynomial.eval word.length)) (by omega) (by omega) (by omega)
    (fun k hk _ => specStore_high M word _ k (by omega)) hg hb (specStore_field_width M word _)
  simp only [specStore_output,List.append_nil] at hr'
  refine ⟨t+t'+1,?_,Exec.seq hr hr'⟩
  unfold budget
  omega

def finiteProgram (M : Machine) (e : FuelExpr) (p : Builder 9) : FiniteProgram :=
  finiteBlock (code M e p) 0 10
lemma finiteProgram_noChoice (M : Machine) (e : FuelExpr) (p : Builder 9) : NoChoice (finiteProgram M e p).program :=
  restrictProgram_noChoice (program (code M e p) 0 10) _
    (finiteRegisterBound_code _) (finiteRegisterBound_input _) (finiteRegisterBound_output _) (program_noChoice _ _ _)

lemma finiteProgram_outputs (M : Machine) (e : FuelExpr) (p : Builder 9) (hp : fuelAllowed p) (word : List Bool) :
    OutputsIn (finiteProgram M e p).program word (output M e p word) (budget M e p word.length) := by
  obtain ⟨t,ht,hr⟩ := code_exec M e p hp word
  apply finitelyNamed_outputs (program (code M e p) 0 10)
  refine ⟨t,ht,⟨finish (code M e p),Function.update (specStore M word (e.polynomial.eval word.length)) 10 (output M e p word)⟩,?_,?_,?_⟩
  · exact hr.compiles 0 10
  · exact code_finish _
  · simp [program]

/-- The code field is a real finite primitive Boolean-stack graph. The clock
witness is a proved bound on its actual Runs, not a semantic oracle instruction. -/
def polynomialProgram (M : Machine) (e : FuelExpr) (p : Builder 9) (hp : fuelAllowed p) :
    PolynomialProgram (output M e p) where
  code := finiteProgram M e p
  noChoice := finiteProgram_noChoice M e p
  clock := (budget_polynomial M e p).choose
  computes := by
    intro word
    rw [← (budget_polynomial M e p).choose_spec word.length]
    exact finiteProgram_outputs M e p hp word

end InitializedBuilder
end BalancedAssortments.CookLevin.StackInitialize
