import BalancedAssortments.CookLevinSerialized

namespace BalancedAssortments.CookLevin
open NPCNF NPMachine

def WidthBound (L : ℕ) (F : Formula) : Prop := ∀ c ∈ F,c.length≤L
lemma width_mono {L K : ℕ} {F : Formula} (h : WidthBound L F) (hLK : L≤K) : WidthBound K F :=
  fun c hc => (h c hc).trans hLK
lemma width_append {L : ℕ} {F G : Formula} (hF : WidthBound L F) (hG : WidthBound L G) :
    WidthBound L (F++G) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hF c hc
  · exact hG c hc
lemma width_allFin {L n : ℕ} (f : Fin n → Formula) (h : ∀ i,WidthBound L (f i)) : WidthBound L (allFin f) := by
  intro c hc
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hc
  exact h i c hi
lemma width_guardLiteral {L : ℕ} (l : Literal) (F : Formula) (h : WidthBound L F) :
    WidthBound (L+1) (guardLiteral l F) := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  simpa only [List.length_cons] using Nat.add_le_add_right (h d hd) 1
lemma width_guard {q g W T R L : ℕ} (v : Var q g W T R) (F : Formula) (h : WidthBound L F) :
    WidthBound (L+1) (guard v F) := width_guardLiteral _ _ h
lemma width_force {q g W T R : ℕ} (v : Var q g W T R) : WidthBound 1 (force v) := by
  intro c hc
  simp only [force,List.mem_singleton] at hc
  subst c; rfl
lemma width_copyFamily {q g W T R n : ℕ} (f k : Fin n → Var q g W T R) :
    WidthBound 2 (copyFamily f k) := by
  apply width_allFin
  intro i c hc
  simp only [List.mem_singleton] at hc
  subst c; rfl
lemma width_exactlyOne {q g W T R n L : ℕ} (f : Fin n → Var q g W T R)
    (hn : n≤L) (h2 : 2≤L) : WidthBound L (exactlyOne f) := by
  apply width_append
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst c; simpa using hn
  · apply width_allFin
    intro i
    apply width_allFin
    intro j c hc
    split at hc
    · simp at hc
    · simp only [List.mem_singleton] at hc
      subst c; exact h2
lemma width_acceptFormula (M : Machine) {W T : ℕ} (t : Fin (T+1)) :
    WidthBound (M.stateExtra+1) (acceptFormula M (W := W) t) := by
  intro c hc
  simp only [acceptFormula,List.mem_singleton] at hc
  subst c
  simp only [List.length_map]
  exact (List.length_filter_le _ _).trans_eq List.length_finRange
lemma width_headTarget (M : Machine) {W T : ℕ} (t : Fin T) (p : Fin W) (m : Move) :
    WidthBound W (headTarget M t p m) := by
  intro c hc
  simp only [headTarget,List.mem_singleton] at hc
  subst c
  simp only [List.length_map]
  exact (List.length_filter_le _ _).trans_eq List.length_finRange
lemma width_initialFormula (M : Machine) (W T : ℕ) (c : WindowConfig M W) :
    WidthBound 1 (initialFormula M W T c) :=
  width_append (width_force _) (width_append (width_force _) (width_allFin _ (fun _ => width_force _)))
lemma width_haltBody (M : Machine) {W T : ℕ} (t : Fin T) :
    WidthBound (M.stateExtra+3) (haltBody M (W := W) t) := by
  apply width_append (width_mono (width_acceptFormula M t.castSucc) (by omega))
  apply width_append (width_mono (width_copyFamily _ _) (by omega))
  apply width_append (width_mono (width_copyFamily _ _) (by omega))
  exact width_allFin _ (fun _ => width_mono (width_copyFamily _ _) (by omega))
lemma width_ruleBody (M : Machine) {W T : ℕ} (t : Fin T) (r : Rule M.stateExtra M.symbolExtra) :
    WidthBound (W+3) (ruleBody M (W := W) t r) := by
  apply width_append (width_mono (width_force _) (by omega))
  apply width_append (width_mono (width_force _) (by omega))
  apply width_append
  · apply width_allFin
    intro p
    apply width_guard
    apply width_append (width_mono (width_force _) (by omega))
    apply width_append (width_mono (width_force _) (by omega))
    exact width_mono (width_headTarget M t p r.move) (by omega)
  · apply width_allFin
    intro p
    exact width_mono (width_guardLiteral _ _ (width_copyFamily _ _)) (by omega)
lemma width_choiceBody (M : Machine) {W T : ℕ} (t : Fin T) (r : Fin (M.rules.length+1)) :
    WidthBound (M.stateExtra+W+3) (choiceBody M (W := W) t r) := by
  refine Fin.cases ?_ (fun i => ?_) r
  · exact width_mono (width_haltBody M t) (by omega)
  · exact width_mono (width_ruleBody M t M.rules[i.val]) (by omega)

def clauseWidthBudget (M : Machine) (W : ℕ) : ℕ :=
  M.stateExtra+W+M.symbolExtra+M.rules.length+10
lemma width_shapeFormula (M : Machine) (W T : ℕ) :
    WidthBound (clauseWidthBudget M W) (shapeFormula M W T) := by
  unfold clauseWidthBudget
  apply width_append
  · apply width_allFin
    intro t
    apply width_append (width_exactlyOne _ (by omega) (by omega))
    apply width_append (width_exactlyOne _ (by omega) (by omega))
    exact width_allFin _ (fun _ => width_exactlyOne _ (by omega) (by omega))
  · exact width_allFin _ (fun _ => width_exactlyOne _ (by omega) (by omega))
lemma width_transitionFormula (M : Machine) (W T : ℕ) :
    WidthBound (clauseWidthBudget M W) (transitionFormula M W T) := by
  apply width_allFin
  intro t
  apply width_allFin
  intro r
  exact width_mono (width_guard _ _ (width_choiceBody M t r)) (by unfold clauseWidthBudget; omega)
theorem tableau_clause_width (M : Machine) (word : List Bool) (T : ℕ) :
    WidthBound (clauseWidthBudget M (windowWidth word T)) (tableauFormula M word T) := by
  apply width_append (width_shapeFormula _ _ _)
  apply width_append (width_mono (width_initialFormula _ _ _ _) (by unfold clauseWidthBudget; omega))
  exact width_append (width_mono (width_acceptFormula _ _) (by unfold clauseWidthBudget; omega))
    (width_transitionFormula _ _ _)

lemma sum_lengths_le (F : Formula) (L : ℕ) (h : WidthBound L F) : literalCount F≤F.length*L := by
  induction F with
  | nil => simp [literalCount]
  | cons c F ih =>
    have hc := h c (by simp)
    have ht := ih (fun d hd => h d (by simp [hd]))
    simp only [literalCount,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul] at *
    omega

theorem tableau_literal_count (M : Machine) (word : List Bool) (T : ℕ) :
    literalCount (tableauFormula M word T) ≤
      clauseBudget M word.length T*clauseWidthBudget M (windowWidth word T) :=
  (sum_lengths_le _ _ (tableau_clause_width M word T)).trans
    (Nat.mul_le_mul_right _ (tableau_clause_count M word T))

end BalancedAssortments.CookLevin
