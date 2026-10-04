import BalancedAssortments.CookLevinRawCorrect

/-! Fixed polynomial clocks are evaluated as structural unary list programs.
The semantic polynomial is never evaluated by the executable program. -/
namespace BalancedAssortments.CookLevin
open NPCNF NPMachine

def multiplyFuel (ys : List Unit) : List Unit → List Unit × ℕ
  | [] => ([],1)
  | _::xs => let tail := multiplyFuel ys xs; (ys++tail.1,tail.2+ys.length+4)
lemma multiplyFuel_length (ys xs : List Unit) : (multiplyFuel ys xs).1.length=xs.length*ys.length := by
  induction xs <;> simp_all [multiplyFuel,Nat.add_mul] <;> omega
lemma multiplyFuel_cost (ys xs : List Unit) : (multiplyFuel ys xs).2=xs.length*(ys.length+4)+1 := by
  induction xs <;> simp_all [multiplyFuel,Nat.add_mul] <;> omega

inductive FuelExpr
  | input
  | constant (tokens : List Unit)
  | add (x y : FuelExpr)
  | mul (x y : FuelExpr)

def FuelExpr.run (input : List Unit) : FuelExpr → List Unit × ℕ
  | .input => (input,1)
  | .constant tokens => (tokens,tokens.length+1)
  | .add x y =>
    let a := x.run input
    let b := y.run input
    (a.1++b.1,a.2+b.2+a.1.length+4)
  | .mul x y =>
    let a := x.run input
    let b := y.run input
    let c := multiplyFuel b.1 a.1
    (c.1,a.2+b.2+c.2+4)

noncomputable def FuelExpr.polynomial : FuelExpr → Polynomial ℕ
  | .input => Polynomial.X
  | .constant tokens => Polynomial.C tokens.length
  | .add x y => x.polynomial+y.polynomial
  | .mul x y => x.polynomial*y.polynomial
noncomputable def FuelExpr.costPolynomial : FuelExpr → Polynomial ℕ
  | .input => 1
  | .constant tokens => Polynomial.C (tokens.length+1)
  | .add x y => x.costPolynomial+y.costPolynomial+x.polynomial+4
  | .mul x y => x.costPolynomial+y.costPolynomial+x.polynomial*(y.polynomial+4)+5

lemma FuelExpr.run_length (e : FuelExpr) (input : List Unit) :
    (e.run input).1.length=e.polynomial.eval input.length := by
  induction e <;> simp_all [run,polynomial,multiplyFuel_length]
lemma FuelExpr.run_cost (e : FuelExpr) (input : List Unit) :
    (e.run input).2=e.costPolynomial.eval input.length := by
  induction e <;> simp_all [run,costPolynomial,multiplyFuel_cost,run_length] <;> omega

def FuelExpr.power : ℕ → FuelExpr
  | 0 => .constant [()]
  | n+1 => .mul .input (power n)
lemma FuelExpr.power_polynomial (n : ℕ) : (power n).polynomial=Polynomial.X^n := by
  induction n <;> simp_all [power,polynomial,pow_succ']

/-- Every natural-coefficient polynomial has a finite, concrete list-processing
program. The coefficients and exponent are fixed program constants. -/
theorem polynomial_has_fuel_program (p : Polynomial ℕ) : ∃ e : FuelExpr,e.polynomial=p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨e,rfl⟩ := hp
    obtain ⟨f,rfl⟩ := hq
    exact ⟨.add e f,rfl⟩
  | monomial n a =>
    refine ⟨.mul (.constant (List.replicate a ())) (FuelExpr.power n),?_⟩
    simp only [FuelExpr.polynomial,FuelExpr.power_polynomial,List.length_replicate]
    exact Polynomial.C_mul_X_pow_eq_monomial

def makeClock (e : FuelExpr) (word : List Bool) : List Unit × ℕ :=
  let input := rawMap (fun _ : Bool => ((),2)) word
  let result := e.run input.1
  (result.1,input.2+result.2+4)
lemma makeClock_length (e : FuelExpr) (word : List Bool) :
    (makeClock e word).1.length=e.polynomial.eval word.length := by
  simp [makeClock,FuelExpr.run_length,rawMap_eq]
lemma makeClock_cost (e : FuelExpr) (word : List Bool) :
    (makeClock e word).2≤e.costPolynomial.eval word.length+6*word.length+5 := by
  have hh := rawMap_cost (fun _ : Bool => ((),2)) word 2 (by simp)
  simp only [makeClock,FuelExpr.run_cost,rawMap_eq,List.length_map]
  omega

def reduceMachine (constants : MachineConstants) (e : FuelExpr) (word : List Bool) : List Bool × ℕ :=
  let clock := makeClock e word
  let output := constructBits constants word clock.1
  (output.1,clock.2+output.2+4)

theorem reduceMachine_correct (M : Machine) (e : FuelExpr) (word : List Bool) :
    Encoding.CNFLanguage (reduceMachine (machineConstants M) e word).1 ↔
      AcceptsWithin M word (e.polynomial.eval word.length) := by
  simp only [reduceMachine,constructBits_correct,makeClock_length]

/-- Every clocked-machine NP language has an explicit bit/list program with
exact membership equivalence. The whole constructor cost and finite-stack
lowering are still separate requirements for polynomial-time hardness. -/
theorem np_has_explicit_cnf_map (L : Set (List Bool)) (hL : InNP L) :
    ∃ M : Machine, ∃ e : FuelExpr, ∀ word,
      Encoding.CNFLanguage (reduceMachine (machineConstants M) e word).1 ↔ word∈L := by
  obtain ⟨M,p,h⟩ := hL
  obtain ⟨e,he⟩ := polynomial_has_fuel_program p
  refine ⟨M,e,fun word => ?_⟩
  rw [reduceMachine_correct,he]
  exact (h word).symm

end BalancedAssortments.CookLevin
