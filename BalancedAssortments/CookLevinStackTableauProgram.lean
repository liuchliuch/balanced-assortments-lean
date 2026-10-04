import BalancedAssortments.CookLevinStackProgram
import BalancedAssortments.CookLevinStackTableau

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPMachine NPCNF StackBuilder
open StackInitialize.InitializedBuilder

@[simp] lemma allowed_skip : fuelAllowed (.skip : B) := by simp [fuelAllowed,fuelRefs]
@[simp] lemma allowed_field (bits : List Bool) : fuelAllowed (.field bits : B) := by simp [fuelAllowed,fuelRefs]
@[simp] lemma allowed_literal (e : E) (sign : Bool) : fuelAllowed (.literal e sign : B) := by simp [fuelAllowed,fuelRefs]
@[simp] lemma allowed_seq (a b : B) : fuelAllowed (.seq a b)↔fuelAllowed a ∧ fuelAllowed b := by simp [fuelAllowed,fuelRefs,or_imp,forall_and]
@[simp] lemma allowed_branch (e f : E) (a b : B) : fuelAllowed (.branch e f a b)↔fuelAllowed a ∧ fuelAllowed b := by simp [fuelAllowed,fuelRefs,or_imp,forall_and]
@[simp] lemma allowed_each (i : Fin 9) (fuel : ℕ) (a b : B) :
    fuelAllowed (.each i fuel a b)↔fuel∈([9,11,12,13,14,15] : List ℕ) ∧ fuelAllowed a ∧ fuelAllowed b := by
  simp [fuelAllowed,fuelRefs,or_imp,forall_and,and_assoc]
@[simp] lemma allowed_literals (ls : List L) : fuelAllowed (literals ls) := by
  induction ls with
  | nil => exact allowed_skip
  | cons l ls ih => simp [literals,ih]
@[simp] lemma allowed_clause (ls : List L) : fuelAllowed (clause ls) := by simp [clause]
@[simp] lemma allowed_dynamic (body : B) : fuelAllowed (dynamicClause body)↔fuelAllowed body := by simp [dynamicClause]
@[simp] lemma allowed_all (bs : List B) : fuelAllowed (all bs)↔∀ b∈bs,fuelAllowed b := by
  induction bs with
  | nil => simp [all]
  | cons b bs ih => simp [all,ih]
@[simp] lemma allowed_loop (i : Fin 9) (fuel : ℕ) (body : B) :
    fuelAllowed (loop i fuel body)↔fuel∈([9,11,12,13,14,15] : List ℕ) ∧ fuelAllowed body := by simp [loop]
@[simp] lemma allowed_eqBranch (e f : E) (a b : B) : fuelAllowed (eqBranch e f a b)↔fuelAllowed a ∧ fuelAllowed b := by simp [eqBranch,and_assoc]
@[simp] lemma allowed_fixedExactlyOne (es : List E) : fuelAllowed (fixedExactlyOne es) := by
  simp only [fixedExactlyOne,allowed_seq,allowed_clause,true_and,allowed_all]
  intro b hb
  obtain ⟨pair,_,hm⟩ := List.mem_flatMap.mp hb
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hm
  exact allowed_clause _
@[simp] lemma allowed_shape (M : Machine) : fuelAllowed (shape M) := by simp [shape]
@[simp] lemma allowed_initial (M : Machine) : fuelAllowed (initial M) := by simp [initial]
@[simp] lemma allowed_moveTarget (m : Move) : fuelAllowed (moveTarget m) := by cases m <;> simp [moveTarget]
@[simp] lemma allowed_ruleBody (M : Machine) (j : ℕ) (r : Rule M.stateExtra M.symbolExtra) : fuelAllowed (ruleBody M j r) := by simp [ruleBody]
@[simp] lemma allowed_haltBody (M : Machine) : fuelAllowed (haltBody M) := by simp [haltBody]
@[simp] lemma allowed_transitions (M : Machine) : fuelAllowed (transitions M)  := by
  simp only [transitions,allowed_loop,allowed_seq,allowed_haltBody,true_and,allowed_all]
  constructor
  · simp
  · intro b hb
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hb
    exact allowed_ruleBody _ _ _
@[simp] lemma allowed_formula (M : Machine) : fuelAllowed (formula M) := by simp [formula]

theorem program_fuelAllowed (M : Machine) : fuelAllowed (program M) := by simp [program]

/-- Genuine polynomial-clock finite Boolean-stack transducer for the complete
fixed machine tableau schema, including initialization and full bit framing.
Its semantic CNF correctness is proved in the separate typed tableau modules. -/
def tableauPolynomialProgram (M : Machine) (e : FuelExpr) :
    NPStack.PolynomialProgram (output M e (program M)) :=
  polynomialProgram M e (program M) (program_fuelAllowed M)

end BalancedAssortments.CookLevin.StackTableau
