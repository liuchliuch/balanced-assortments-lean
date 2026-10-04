import BalancedAssortments.CookLevinRawBudget

/-! Polynomial cost in original input length for the actual Cook–Levin bit/list
program. The remaining machine-class obligation is operational program lowering. -/
namespace BalancedAssortments.CookLevin
open NPCNF NPMachine

/-- Exact natural-coefficient polynomial representation; only a mathematical
closure predicate, never a computational complexity class. -/
def NatPolynomial (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ,∀ n,f n=p.eval n
lemma polynomial_constant (a : ℕ) : NatPolynomial (fun _ => a) := ⟨Polynomial.C a,by simp⟩
lemma polynomial_identity : NatPolynomial (fun n => n) := ⟨Polynomial.X,by simp⟩
lemma polynomial_eval (p : Polynomial ℕ) : NatPolynomial (fun n => p.eval n) := ⟨p,by simp⟩
lemma polynomial_add {f g : ℕ → ℕ} (hf : NatPolynomial f) (hg : NatPolynomial g) :
    NatPolynomial (fun n => f n+g n) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,by intro n;simp [hp,hq]⟩
lemma polynomial_mul {f g : ℕ → ℕ} (hf : NatPolynomial f) (hg : NatPolynomial g) :
    NatPolynomial (fun n => f n*g n) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,by intro n;simp [hp,hq]⟩
lemma polynomial_pow {f : ℕ → ℕ} (k : ℕ) (hf : NatPolynomial f) :
    NatPolynomial (fun n => (f n)^k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k,by intro n;simp [hp]⟩

macro "close_poly" : tactic => `(tactic|
  with_reducible repeat first
    | assumption
    | exact polynomial_identity
    | exact polynomial_eval _
    | exact polynomial_constant _
    | apply polynomial_add
    | apply polynomial_mul
    | apply polynomial_pow)

def ProfilePolynomial (f : ℕ → CostProfile) : Prop :=
  NatPolynomial (fun n => (f n).len) ∧ NatPolynomial (fun n => (f n).cost)
lemma profile_append_poly {f g : ℕ → CostProfile} (hf : ProfilePolynomial f) (hg : ProfilePolynomial g) :
    ProfilePolynomial (fun n => (f n).append (g n)) := by
  rcases hf with ⟨hfL,hfC⟩
  rcases hg with ⟨hgL,hgC⟩
  constructor <;> dsimp only [CostProfile.append] <;> close_poly
lemma profile_loop_poly {f : ℕ → ℕ} {g : ℕ → CostProfile} (hf : NatPolynomial f) (hg : ProfilePolynomial g) :
    ProfilePolynomial (fun n => CostProfile.loop (f n) (g n)) := by
  rcases hg with ⟨hgL,hgC⟩
  constructor <;> dsimp only [CostProfile.loop] <;> close_poly
lemma profile_guard_poly {f : ℕ → ℕ} {g : ℕ → CostProfile} (hf : NatPolynomial f) (hg : ProfilePolynomial g) :
    ProfilePolynomial (fun n => (g n).guarded (f n)) := by
  rcases hg with ⟨hgL,hgC⟩
  constructor <;> dsimp only [CostProfile.guarded,labelCost] <;> close_poly
lemma familyProfile_poly {f g : ℕ → ℕ} (hf : NatPolynomial f) (hg : NatPolynomial g) :
    ProfilePolynomial (fun n => familyProfile (f n) (g n)) := by
  constructor <;> dsimp only [familyProfile,familyLength,familyCost,labelCost,labelWidth] <;> close_poly
lemma forceProfile_poly {f : ℕ → ℕ} (hf : NatPolynomial f) : ProfilePolynomial (fun n => forceProfile (f n)) := by
  constructor <;> dsimp only [forceProfile,labelCost] <;> close_poly
lemma copyProfile_poly {f : ℕ → ℕ} (hf : NatPolynomial f) : ProfilePolynomial (fun n => copyProfile (f n)) := by
  constructor <;> dsimp only [copyProfile,labelCost] <;> close_poly
lemma acceptProfile_poly {f g : ℕ → ℕ} (hf : NatPolynomial f) (hg : NatPolynomial g) :
    ProfilePolynomial (fun n => acceptProfile (f n) (g n)) := by
  constructor <;> dsimp only [acceptProfile,labelCost] <;> close_poly
lemma targetProfile_poly {f g : ℕ → ℕ} (hf : NatPolynomial f) (hg : NatPolynomial g) :
    ProfilePolynomial (fun n => targetProfile (f n) (g n)) := by
  constructor <;> dsimp only [targetProfile,labelCost,moveCost] <;> close_poly
lemma shapeProfile_poly {f g : ℕ → ℕ} (hf : NatPolynomial f) (hg : NatPolynomial g) :
    ProfilePolynomial (fun n => shapeProfile (f n) (g n)) := by
  exact profile_append_poly
    (profile_loop_poly hf (profile_append_poly (familyProfile_poly hf hg)
      (profile_append_poly (familyProfile_poly hf hg) (profile_loop_poly hf (familyProfile_poly hf hg)))))
    (profile_loop_poly hf (familyProfile_poly hf hg))
lemma initialProfile_poly {f g : ℕ → ℕ} (hf : NatPolynomial f) (hg : NatPolynomial g) :
    ProfilePolynomial (fun n => initialProfile (f n) (g n)) :=
  profile_append_poly (forceProfile_poly hg) (profile_append_poly (forceProfile_poly hg)
    (profile_loop_poly hf (forceProfile_poly hg)))
lemma haltProfile_poly {f g : ℕ → ℕ} (hf : NatPolynomial f) (hg : NatPolynomial g) :
    ProfilePolynomial (fun n => haltProfile (f n) (g n)) :=
  profile_append_poly (acceptProfile_poly hf hg) (profile_append_poly (profile_loop_poly hf (copyProfile_poly hg))
    (profile_append_poly (profile_loop_poly hf (copyProfile_poly hg)) (profile_loop_poly hf (profile_loop_poly hf (copyProfile_poly hg)))))
lemma ruleProfile_poly {f g : ℕ → ℕ} (hf : NatPolynomial f) (hg : NatPolynomial g) :
    ProfilePolynomial (fun n => ruleProfile (f n) (g n)) :=
  profile_append_poly (forceProfile_poly hg) (profile_append_poly (forceProfile_poly hg)
    (profile_append_poly
      (profile_loop_poly hf (profile_guard_poly hg (profile_append_poly (forceProfile_poly hg)
        (profile_append_poly (forceProfile_poly hg) (targetProfile_poly hf hg)))))
      (profile_loop_poly hf (profile_guard_poly hg (profile_loop_poly hf (copyProfile_poly hg))))))
lemma bodyProfile_poly {f g : ℕ → ℕ} (hf : NatPolynomial f) (hg : NatPolynomial g) :
    ProfilePolynomial (fun n => bodyProfile (f n) (g n)) := by
  obtain ⟨h1,h2⟩ := haltProfile_poly hf hg
  obtain ⟨h3,h4⟩ := ruleProfile_poly hf hg
  constructor <;> dsimp only [bodyProfile] <;> close_poly
lemma transitionProfile_poly {f g : ℕ → ℕ} (hf : NatPolynomial f) (hg : NatPolynomial g) :
    ProfilePolynomial (fun n => transitionProfile (f n) (g n)) := by
  have hp := profile_loop_poly hf (profile_guard_poly hg (bodyProfile_poly hf hg))
  change ProfilePolynomial (fun n => choicesProfile (f n) (g n)) at hp
  obtain ⟨hL,hC⟩ := hp
  apply profile_loop_poly hf
  constructor <;> dsimp only <;> close_poly
lemma formulaProfile_poly {f g : ℕ → ℕ} (hf : NatPolynomial f) (hg : NatPolynomial g) :
    ProfilePolynomial (fun n => formulaProfile (f n) (g n)) :=
  profile_append_poly (shapeProfile_poly hf hg) (profile_append_poly (initialProfile_poly hf hg)
    (profile_append_poly (acceptProfile_poly hf hg) (transitionProfile_poly hf hg)))

lemma sourceBound_poly (M : Machine) (p : Polynomial ℕ) :
    NatPolynomial (fun n => sourceBound M n (p.eval n)) := by unfold sourceBound;close_poly
lemma clauseBudget_poly (M : Machine) (p : Polynomial ℕ) :
    NatPolynomial (fun n => clauseBudget M n (p.eval n)) := by
  dsimp only [clauseBudget,shapeClauseBudget,bodyClauseBudget]
  close_poly
lemma literalBudget_poly (M : Machine) (p : Polynomial ℕ) :
    NatPolynomial (fun n => literalBudget M n (p.eval n)) := by
  have hc := clauseBudget_poly M p
  dsimp only [literalBudget,clauseWidthBudget]
  close_poly
lemma catalogueBudget_poly (M : Machine) (p : Polynomial ℕ) :
    NatPolynomial (fun n => catalogueBudget M n (p.eval n)) := by
  have hc := clauseBudget_poly M p
  have ha := literalBudget_poly M p
  have hn := sourceBound_poly M p
  dsimp only [catalogueBudget,labelWidth]
  close_poly
lemma outputMeasureBudget_poly (M : Machine) (p : Polynomial ℕ) :
    NatPolynomial (fun n => outputMeasureBudget M n (p.eval n)) := by
  have hc := clauseBudget_poly M p
  have ha := literalBudget_poly M p
  have hn := sourceBound_poly M p
  dsimp only [outputMeasureBudget,labelWidth]
  close_poly
lemma bitConstructorBudget_polynomial (M : Machine) (p : Polynomial ℕ) :
    NatPolynomial (fun n => bitConstructorBudget M n (p.eval n)) := by
  have hn := sourceBound_poly M p
  have hf := (formulaProfile_poly hn hn).2
  have hc := catalogueBudget_poly M p
  have hm := outputMeasureBudget_poly M p
  dsimp only [bitConstructorBudget,constructorBudget]
  close_poly

/-- Exact clock generation, construction and emission are charged. The bound is
in the original input bitstring length, with a fixed polynomial per machine and
clock program; no unary clock is provided by the input or assumed for free. -/
theorem reduceMachine_polynomial_cost (M : Machine) (e : FuelExpr) :
    ∃ P : Polynomial ℕ, ∀ word : List Bool,
      (reduceMachine (machineConstants M) e word).2≤P.eval word.length := by
  obtain ⟨p,hp⟩ := bitConstructorBudget_polynomial M e.polynomial
  refine ⟨e.costPolynomial+6*Polynomial.X+9+p,?_⟩
  intro word
  have hc := makeClock_cost e word
  have hb := constructBits_cost M word (makeClock e word).1
  rw [makeClock_length] at hb
  have hpeq := hp word.length
  dsimp only at hpeq
  rw [hpeq] at hb
  simp only [reduceMachine,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

/-- Every language accepted by a fixed finite NDTM in polynomial time has a
concrete, polynomial-cost bit/list reduction to the total encoded CNF language.
This theorem does not identify the bit/list cost model with a Turing machine. -/
theorem np_has_polynomial_bit_cnf_map (L : Set (List Bool)) (hL : InNP L) :
    ∃ M : Machine, ∃ e : FuelExpr, ∃ P : Polynomial ℕ, ∀ word,
      (Encoding.CNFLanguage (reduceMachine (machineConstants M) e word).1 ↔ word∈L) ∧
      (reduceMachine (machineConstants M) e word).2≤P.eval word.length := by
  obtain ⟨M,e,h⟩ := np_has_explicit_cnf_map L hL
  obtain ⟨P,hP⟩ := reduceMachine_polynomial_cost M e
  exact ⟨M,e,P,fun word => ⟨h word,hP word⟩⟩

end BalancedAssortments.CookLevin
