import BalancedAssortments.CookLevinSize

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine

lemma bounded_append {n : ℕ} {F G : Formula} (hF : variablesBounded n F) (hG : variablesBounded n G) :
    variablesBounded n (F++G) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hF c hc
  · exact hG c hc

lemma bounded_allFin {n k : ℕ} (f : Fin k → Formula) (h : ∀ i,variablesBounded n (f i)) :
    variablesBounded n (allFin f) := by
  intro c hc
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hc
  exact h i c hi

lemma bounded_pos {q g W T R : ℕ} (v : Var q g W T R) :
    (pos v).var<variableCount q g W T R := index_lt v
lemma bounded_neg {q g W T R : ℕ} (v : Var q g W T R) :
    (neg v).var<variableCount q g W T R := index_lt v

lemma bounded_force {q g W T R : ℕ} (v : Var q g W T R) :
    variablesBounded (variableCount q g W T R) (force v) := by
  intro c hc l hl
  simp only [force,List.mem_singleton] at hc
  subst c
  simp only [List.mem_singleton] at hl
  subst l
  exact bounded_pos v

lemma bounded_guardLiteral {n : ℕ} (l : Literal) (F : Formula)
    (hl : l.var<n) (hF : variablesBounded n F) : variablesBounded n (guardLiteral l F) := by
  intro c hc a ha
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  rcases List.mem_cons.mp ha with he | he
  · subst a; exact hl
  · exact hF d hd a he

lemma bounded_guard {q g W T R : ℕ} (v : Var q g W T R) (F : Formula)
    (hF : variablesBounded (variableCount q g W T R) F) :
    variablesBounded (variableCount q g W T R) (guard v F) :=
  bounded_guardLiteral _ _ (bounded_pos v) hF

lemma bounded_copyFamily {q g W T R n : ℕ} (f k : Fin n → Var q g W T R) :
    variablesBounded (variableCount q g W T R) (copyFamily f k) := by
  apply bounded_allFin
  intro i c hc l hl
  simp only [List.mem_singleton] at hc
  subst c
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl
  · exact bounded_neg _
  · exact bounded_pos _

lemma bounded_exactlyOne {q g W T R n : ℕ} (f : Fin n → Var q g W T R) :
    variablesBounded (variableCount q g W T R) (exactlyOne f) := by
  apply bounded_append
  · intro c hc l hl
    simp only [List.mem_singleton] at hc
    subst c
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hl
    exact bounded_pos _
  · apply bounded_allFin
    intro i
    apply bounded_allFin
    intro j
    by_cases he : i=j
    · simp only [he,↓reduceIte]
      intro c hc; simp at hc
    · simp only [if_neg he]
      intro c hc l hl
      simp only [List.mem_singleton] at hc
      subst c
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      rcases hl with rfl | rfl <;> exact bounded_neg _

lemma bounded_shapeFormula (M : Machine) (W T : ℕ) :
    variablesBounded (variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1))
      (shapeFormula M W T) := by
  apply bounded_append
  · apply bounded_allFin
    intro t
    exact bounded_append (bounded_exactlyOne _) (bounded_append (bounded_exactlyOne _)
      (bounded_allFin _ (fun _ => bounded_exactlyOne _)))
  · exact bounded_allFin _ (fun _ => bounded_exactlyOne _)

lemma bounded_acceptFormula (M : Machine) {W T : ℕ} (t : Fin (T+1)) :
    variablesBounded (variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1))
      (acceptFormula M (W := W) t) := by
  intro c hc l hl
  simp only [acceptFormula,List.mem_singleton] at hc
  subst c
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hl
  exact bounded_pos _

lemma bounded_initialFormula (M : Machine) (W T : ℕ) (c : WindowConfig M W) :
    variablesBounded (variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1))
      (initialFormula M W T c) :=
  bounded_append (bounded_force _) (bounded_append (bounded_force _) (bounded_allFin _ (fun _ => bounded_force _)))

lemma bounded_headTarget (M : Machine) {W T : ℕ} (t : Fin T) (p : Fin W) (m : Move) :
    variablesBounded (variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1))
      (headTarget M t p m) := by
  intro c hc l hl
  simp only [headTarget,List.mem_singleton] at hc
  subst c
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hl
  exact bounded_pos _

lemma bounded_haltBody (M : Machine) {W T : ℕ} (t : Fin T) :
    variablesBounded (variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1))
      (haltBody M (W := W) t) :=
  bounded_append (bounded_acceptFormula _ _) (bounded_append (bounded_copyFamily _ _)
    (bounded_append (bounded_copyFamily _ _) (bounded_allFin _ (fun _ => bounded_copyFamily _ _))))

lemma bounded_ruleBody (M : Machine) {W T : ℕ} (t : Fin T) (r : Rule M.stateExtra M.symbolExtra) :
    variablesBounded (variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1))
      (ruleBody M (W := W) t r) := by
  apply bounded_append (bounded_force _)
  apply bounded_append (bounded_force _)
  apply bounded_append
  · apply bounded_allFin
    intro p
    exact bounded_guard _ _ (bounded_append (bounded_force _) (bounded_append (bounded_force _) (bounded_headTarget _ _ _ _)))
  · apply bounded_allFin
    intro p
    exact bounded_guardLiteral _ _ (bounded_neg _) (bounded_copyFamily _ _)

lemma bounded_choiceBody (M : Machine) {W T : ℕ} (t : Fin T) (r : Fin (M.rules.length+1)) :
    variablesBounded (variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1))
      (choiceBody M (W := W) t r) := by
  refine Fin.cases (bounded_haltBody M t) (fun i => bounded_ruleBody M t M.rules[i.val]) r

lemma bounded_transitionFormula (M : Machine) (W T : ℕ) :
    variablesBounded (variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1))
      (transitionFormula M W T) :=
  bounded_allFin _ (fun t => bounded_allFin _ (fun r => bounded_guard _ _ (bounded_choiceBody M t r)))

theorem tableau_variables_bounded (M : Machine) (word : List Bool) (T : ℕ) :
    variablesBounded (variableCount (M.stateExtra+1) (M.symbolExtra+3) (windowWidth word T) T (M.rules.length+1))
      (tableauFormula M word T) :=
  bounded_append (bounded_shapeFormula _ _ _) (bounded_append (bounded_initialFormula _ _ _ _)
    (bounded_append (bounded_acceptFormula _ _) (bounded_transitionFormula _ _ _)))

end BalancedAssortments.CookLevin
