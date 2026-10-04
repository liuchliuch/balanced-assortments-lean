import BalancedAssortments.CookLevinTableau

/-! Soundness and completeness of each globally selected transition body. -/
noncomputable section
namespace BalancedAssortments.CookLevin
open NPCNF NPMachine

lemma eval_headTarget {M : Machine} {W T : ℕ} {σ : Assignment} (h : ShapeHolds M W T σ)
    (t : Fin T) (p : Fin W) (m : Move) :
    formulaEval σ (headTarget M t p m)=true ↔
      ((decodeRow h t.succ).head.val : ℤ)=(p.val : ℤ)+m.displacement := by
  simp only [headTarget,formulaEval_cons,formulaEval_nil,Bool.and_true,clauseEval_eq_true_iff,
    List.mem_map,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
  constructor
  · rintro ⟨l,⟨k,hk,rfl⟩,hbit⟩
    have he := selected_unique (h.heads t.succ) k hbit
    change ((selected (h.heads t.succ)).val : ℤ)=_
    rwa [← he]
  · intro hp
    exact ⟨pos (.head t.succ (decodeRow h t.succ).head),
      ⟨(decodeRow h t.succ).head,hp,rfl⟩,selected_true (h.heads t.succ)⟩

lemma eval_haltBody {M : Machine} {W T : ℕ} {σ : Assignment} (h : ShapeHolds M W T σ)
    (t : Fin T) : formulaEval σ (haltBody M (W := W) t)=true ↔
      WindowAccepts M (decodeRow h t.castSucc) ∧ decodeRow h t.succ=decodeRow h t.castSucc := by
  simp only [haltBody,formulaEval_append,Bool.and_eq_true,eval_allFin,
    eval_accept h,eval_copy_selected (h.states t.castSucc) (h.states t.succ),
    eval_copy_selected (h.heads t.castSucc) (h.heads t.succ),
    eval_copy_selected (h.tapes t.castSucc _) (h.tapes t.succ _)]
  constructor
  · rintro ⟨ha,hs,hh,ht⟩
    refine ⟨ha,?_⟩
    apply WindowConfig.ext
    · exact hs.symm
    · exact hh.symm
    · funext p; exact (ht p).symm
  · rintro ⟨ha,he⟩
    exact ⟨ha,(congrArg WindowConfig.state he).symm,(congrArg WindowConfig.head he).symm,
      fun p => (congrArg (fun c => c.tape p) he).symm⟩

def RuleRealizes {M : Machine} {W : ℕ} (x y : WindowConfig M W)
    (r : Rule M.stateExtra M.symbolExtra) : Prop :=
  x.state=r.source ∧ x.tape x.head=r.read ∧ y.state=r.target ∧
    (y.head.val : ℤ)=(x.head.val : ℤ)+r.move.displacement ∧
    y.tape=Function.update x.tape x.head r.write

lemma eval_ruleBody {M : Machine} {W T : ℕ} {σ : Assignment} (h : ShapeHolds M W T σ)
    (t : Fin T) (r : Rule M.stateExtra M.symbolExtra) :
    formulaEval σ (ruleBody M (W := W) t r)=true ↔
      RuleRealizes (decodeRow h t.castSucc) (decodeRow h t.succ) r := by
  simp only [ruleBody,formulaEval_append,Bool.and_eq_true,eval_force,eval_allFin,eval_guard,eval_guardLiteral]
  constructor
  · rintro ⟨hs,ht,hheads,hothers⟩
    have hh := hheads (selected (h.heads t.castSucc)) (selected_true (h.heads t.castSucc))
    obtain ⟨hread,hwrite,hmove⟩ := hh
    refine ⟨(selected_unique (h.states t.castSucc) _ hs).symm,
      (selected_unique (h.tapes t.castSucc _) _ hread).symm,
      (selected_unique (h.states t.succ) _ ht).symm,
      (eval_headTarget h t _ r.move).1 hmove,?_⟩
    funext p
    by_cases hp : p=(decodeRow h t.castSucc).head
    · subst p
      rw [Function.update_self]
      exact (selected_unique (h.tapes t.succ _) _ hwrite).symm
    · rw [Function.update_of_ne hp]
      have hfalse : σ (index (Var.head t.castSucc p : TVar M W T))=false :=
        (selected_false_iff (h.heads t.castSucc) p).2 hp
      have hneg : literalEval σ (neg (Var.head t.castSucc p : TVar M W T))=true := by
        rw [eval_neg,hfalse]; rfl
      have hc := (eval_copy_selected (h.tapes t.castSucc p) (h.tapes t.succ p)).1 (hothers p hneg)
      exact hc.symm
  · rintro ⟨hs,hread,ht,hmove,htape⟩
    refine ⟨(selected_true_iff (h.states t.castSucc) _).2 hs.symm,
      (selected_true_iff (h.states t.succ) _).2 ht.symm,?_,?_⟩
    · intro p hp
      have he := selected_unique (h.heads t.castSucc) p hp
      subst p
      refine ⟨(selected_true_iff (h.tapes t.castSucc _) _).2 hread.symm,?_,
        (eval_headTarget h t _ r.move).2 hmove⟩
      have hw : (decodeRow h t.succ).tape (decodeRow h t.castSucc).head=r.write := by
        rw [htape,Function.update_self]
      exact (selected_true_iff (h.tapes t.succ _) _).2 hw.symm
    · intro p hp
      have hne : p≠(decodeRow h t.castSucc).head := by
        intro he
        subst p
        have hbit : σ (index (Var.head t.castSucc (decodeRow h t.castSucc).head : TVar M W T))=true :=
          selected_true (h.heads t.castSucc)
        simp only [eval_neg,hbit,Bool.not_true,Bool.false_eq_true] at hp
      apply (eval_copy_selected (h.tapes t.castSucc p) (h.tapes t.succ p)).2
      have hh := congrFun htape p
      rw [Function.update_of_ne hne] at hh
      exact hh.symm

def ChoiceRealizes {M : Machine} {W : ℕ} (x y : WindowConfig M W)
    (r : Fin (M.rules.length+1)) : Prop :=
  Fin.cases (WindowAccepts M x ∧ y=x) (fun i => RuleRealizes x y M.rules[i.val]) r

lemma eval_choiceBody {M : Machine} {W T : ℕ} {σ : Assignment} (h : ShapeHolds M W T σ)
    (t : Fin T) (r : Fin (M.rules.length+1)) :
    formulaEval σ (choiceBody M (W := W) t r)=true ↔
      ChoiceRealizes (decodeRow h t.castSucc) (decodeRow h t.succ) r := by
  refine Fin.cases ?_ (fun i => ?_) r
  · exact eval_haltBody h t
  · exact eval_ruleBody h t M.rules[i.val]

lemma choiceRealizes_iff_step {M : Machine} {W : ℕ} (x y : WindowConfig M W) :
    (∃ r,ChoiceRealizes x y r) ↔ WindowPaddedStep M x y := by
  constructor
  · rintro ⟨r,hr⟩
    revert hr
    refine Fin.cases ?_ (fun i => ?_) r
    · exact fun h => Or.inr h
    · intro h
      exact Or.inl ⟨M.rules[i.val],List.getElem_mem i.isLt,h⟩
  · rintro (⟨r,hr,h⟩ | h)
    · obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hr
      refine ⟨(⟨i,hi⟩ : Fin M.rules.length).succ,?_⟩
      change RuleRealizes x y M.rules[i]
      rw [he]
      exact h
    · exact ⟨0,h⟩

/-- All transition CNF clauses enforce one coherent original transition at each
time. The unique global choice is read once for all tape and head constraints. -/
lemma eval_transitions_sound {M : Machine} {W T : ℕ} {σ : Assignment} (h : ShapeHolds M W T σ)
    (hf : formulaEval σ (transitionFormula M W T)=true) :
    ∀ t : Fin T, WindowPaddedStep M (decodeRow h t.castSucc) (decodeRow h t.succ) := by
  simp only [transitionFormula,eval_allFin,eval_guard] at hf
  intro t
  let r := selected (h.choices t)
  have hh := hf t r (selected_true (h.choices t))
  exact (choiceRealizes_iff_step _ _).1 ⟨r,(eval_choiceBody h t r).1 hh⟩

end BalancedAssortments.CookLevin
