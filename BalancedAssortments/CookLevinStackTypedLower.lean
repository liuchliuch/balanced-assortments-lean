import BalancedAssortments.CookLevinStackTypedTableau

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau.Typed
open NPMachine NPCNF
@[simp] lemma literals_lower (ls : List L) : (literals ls).lower=StackTableau.literals ls := by
  induction ls <;> simp_all [literals,ClauseCode.lower,StackTableau.literals]
@[simp] lemma clause_lower (ls : List L) : (clause ls).lower=StackTableau.clause ls := by
  simp [clause,FormulaCode.lower,StackTableau.dynamicClause,StackTableau.clause]
@[simp] lemma all_lower (ps : List FormulaCode) : (all ps).lower=StackTableau.all (ps.map FormulaCode.lower) := by
  induction ps <;> simp_all [all,FormulaCode.lower,StackTableau.all]
@[simp] lemma loop_lower (i : Fin 9) (fuel : ℕ) (p : FormulaCode) :
    (loop i fuel p).lower=StackTableau.loop i fuel p.lower := rfl
@[simp] lemma cloop_lower (i : Fin 9) (fuel : ℕ) (p : ClauseCode) :
    (cloop i fuel p).lower=StackTableau.loop i fuel p.lower := rfl
@[simp] lemma eqBranch_lower (a b : E) (y n : ClauseCode) :
    (eqBranch a b y n).lower=StackTableau.eqBranch a b y.lower n.lower := rfl
@[simp] lemma dynamicClause_lower (p : ClauseCode) :
    (dynamicClause p).lower=StackTableau.dynamicClause p.lower := rfl
@[simp] lemma fixedExactlyOne_lower (es : List E) :
    (fixedExactlyOne es).lower=StackTableau.fixedExactlyOne es := by
  simp [fixedExactlyOne,StackTableau.fixedExactlyOne,FormulaCode.lower,List.map_flatMap,List.map_map,Function.comp_def]
@[simp] lemma shape_lower (M : Machine) : (shape M).lower=StackTableau.shape M := by
  simp [shape,StackTableau.shape,FormulaCode.lower,ClauseCode.lower]
@[simp] lemma initial_lower (M : Machine) : (initial M).lower=StackTableau.initial M := by
  simp [initial,StackTableau.initial,FormulaCode.lower]
@[simp] lemma moveTarget_lower (m : Move) : (moveTarget m).lower=StackTableau.moveTarget m := by
  cases m <;> simp [moveTarget,StackTableau.moveTarget,ClauseCode.lower]
@[simp] lemma ruleBody_lower (M : Machine) (j : ℕ) (r : Rule M.stateExtra M.symbolExtra) :
    (ruleBody M j r).lower=StackTableau.ruleBody M j r := by
  simp [ruleBody,StackTableau.ruleBody,ClauseCode.lower,List.map_map,Function.comp_def]
@[simp] lemma haltBody_lower (M : Machine) : (haltBody M).lower=StackTableau.haltBody M := by
  simp [haltBody,StackTableau.haltBody,accepting,StackTableau.accepting,List.map_map,Function.comp_def]
@[simp] lemma transitions_lower (M : Machine) : (transitions M).lower=StackTableau.transitions M := by
  simp [transitions,StackTableau.transitions,FormulaCode.lower,List.map_map,Function.comp_def]
theorem formula_lower (M : Machine) : (formula M).lower=StackTableau.formula M := by
  simp [formula,StackTableau.formula,accepting,StackTableau.accepting]
end BalancedAssortments.CookLevin.StackTableau.Typed
