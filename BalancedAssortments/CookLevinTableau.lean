import BalancedAssortments.CookLevinEncoding
import BalancedAssortments.NPMachineTableauSemantics

/-! Polynomially indexed, one-hot CNF tableau. A single global rule-choice
family at each time controls the entire next configuration, including every
unchanged tape cell. No independently mixed nondeterministic local choices occur. -/
namespace BalancedAssortments.CookLevin
open NPCNF NPMachine

abbrev TVar (M : Machine) (W T : ℕ) := Var (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1)

noncomputable def selected {q g W T R n : ℕ} {σ : Assignment} {f : Fin n → Var q g W T R}
    (h : OneHot σ f) : Fin n := Classical.choose h
lemma selected_true {q g W T R n : ℕ} {σ : Assignment} {f : Fin n → Var q g W T R}
    (h : OneHot σ f) : σ (index (f (selected h)))=true := (Classical.choose_spec h).1
lemma selected_unique {q g W T R n : ℕ} {σ : Assignment} {f : Fin n → Var q g W T R}
    (h : OneHot σ f) (i : Fin n) (hi : σ (index (f i))=true) : i=selected h :=
  (Classical.choose_spec h).2 i hi
lemma selected_true_iff {q g W T R n : ℕ} {σ : Assignment} {f : Fin n → Var q g W T R}
    (h : OneHot σ f) (i : Fin n) : σ (index (f i))=true ↔ i=selected h :=
  ⟨selected_unique h i,by rintro rfl; exact selected_true h⟩
lemma selected_false_iff {q g W T R n : ℕ} {σ : Assignment} {f : Fin n → Var q g W T R}
    (h : OneHot σ f) (i : Fin n) : σ (index (f i))=false ↔ i≠selected h := by
  rw [← Bool.not_eq_true,selected_true_iff h i]

lemma eval_copy_selected {q g W T R n : ℕ} {σ : Assignment}
    {f k : Fin n → Var q g W T R} (hf : OneHot σ f) (hk : OneHot σ k) :
    formulaEval σ (copyFamily f k)=true ↔ selected hf=selected hk := by
  rw [eval_copyFamily]
  constructor
  · intro h
    exact selected_unique hk (selected hf) (h _ (selected_true hf))
  · intro he i hi
    have hif := selected_unique hf i hi
    rw [hif,he]
    exact selected_true hk

structure ShapeHolds (M : Machine) (W T : ℕ) (σ : Assignment) : Prop where
  states : ∀ t : Fin (T+1), OneHot σ (fun s => (Var.state t s : TVar M W T))
  heads : ∀ t : Fin (T+1), OneHot σ (fun p => (Var.head t p : TVar M W T))
  tapes : ∀ t : Fin (T+1), ∀ p : Fin W, OneHot σ (fun a => (Var.tape t p a : TVar M W T))
  choices : ∀ t : Fin T, OneHot σ (fun r => (Var.choice t r : TVar M W T))

def shapeFormula (M : Machine) (W T : ℕ) : Formula :=
  allFin (fun t : Fin (T+1) => exactlyOne (fun s => (Var.state t s : TVar M W T)) ++
    (exactlyOne (fun p => (Var.head t p : TVar M W T)) ++
      allFin (fun p : Fin W => exactlyOne (fun a => (Var.tape t p a : TVar M W T))))) ++
  allFin (fun t : Fin T => exactlyOne (fun r => (Var.choice t r : TVar M W T)))

lemma eval_shape (M : Machine) (W T : ℕ) (σ : Assignment) :
    formulaEval σ (shapeFormula M W T)=true ↔ ShapeHolds M W T σ := by
  simp only [shapeFormula,formulaEval_append,Bool.and_eq_true,eval_allFin,eval_exactlyOne]
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨fun t => (h t).1,fun t => (h t).2.1,fun t => (h t).2.2,hc⟩
  · rintro ⟨hs,hh,ht,hc⟩
    exact ⟨fun t => ⟨hs t,hh t,ht t⟩,hc⟩

noncomputable def decodeRow {M : Machine} {W T : ℕ} {σ : Assignment}
    (h : ShapeHolds M W T σ) (t : Fin (T+1)) : WindowConfig M W :=
  ⟨selected (h.states t),selected (h.heads t),fun p => selected (h.tapes t p)⟩

def acceptFormula (M : Machine) {W T : ℕ} (t : Fin (T+1)) : Formula :=
  [(((List.finRange (M.stateExtra+1)).filter fun s => M.accepting s).map
    fun s => pos (Var.state t s : TVar M W T))]

lemma eval_accept_formula (M : Machine) {W T : ℕ} (σ : Assignment) (t : Fin (T+1)) :
    formulaEval σ (acceptFormula M (W := W) t)=true ↔
      ∃ s,M.accepting s=true ∧ σ (index (Var.state t s : TVar M W T))=true := by
  simp only [acceptFormula,formulaEval_cons,formulaEval_nil,Bool.and_true,clauseEval_eq_true_iff,
    List.mem_map,List.mem_filter,List.mem_finRange,true_and]
  constructor
  · rintro ⟨l,⟨s,hs,rfl⟩,hl⟩; exact ⟨s,hs,hl⟩
  · rintro ⟨s,hs,hl⟩; exact ⟨pos (.state t s),⟨s,hs,rfl⟩,hl⟩

lemma eval_accept {M : Machine} {W T : ℕ} {σ : Assignment} (h : ShapeHolds M W T σ)
    (t : Fin (T+1)) : formulaEval σ (acceptFormula M (W := W) t)=true ↔
      WindowAccepts M (decodeRow h t) := by
  rw [eval_accept_formula]
  constructor
  · rintro ⟨s,hs,hbit⟩
    have he := selected_unique (h.states t) s hbit
    change M.accepting (selected (h.states t))=true
    rwa [← he]
  · intro hs
    exact ⟨selected (h.states t),hs,selected_true (h.states t)⟩

def initialFormula (M : Machine) (W T : ℕ) (c : WindowConfig M W) : Formula :=
  force (Var.state 0 c.state : TVar M W T) ++
    (force (Var.head 0 c.head : TVar M W T) ++
      allFin (fun p => force (Var.tape 0 p (c.tape p) : TVar M W T)))

lemma eval_initial {M : Machine} {W T : ℕ} {σ : Assignment} (h : ShapeHolds M W T σ)
    (c : WindowConfig M W) : formulaEval σ (initialFormula M W T c)=true ↔ decodeRow h 0=c := by
  simp only [initialFormula,formulaEval_append,Bool.and_eq_true,eval_force,eval_allFin,
    selected_true_iff (h.states 0),selected_true_iff (h.heads 0),selected_true_iff (h.tapes 0 _)]
  constructor
  · rintro ⟨hs,hh,ht⟩
    apply WindowConfig.ext
    · exact hs.symm
    · exact hh.symm
    · funext p; exact (ht p).symm
  · intro he
    refine ⟨?_,?_,?_⟩
    · exact (congrArg WindowConfig.state he).symm
    · exact (congrArg WindowConfig.head he).symm
    · intro p; exact (congrArg (fun c => c.tape p) he).symm

def headTarget (M : Machine) {W T : ℕ} (t : Fin T) (p : Fin W) (m : Move) : Formula :=
  [(((List.finRange W).filter fun k => (k.val : ℤ)=(p.val : ℤ)+m.displacement).map
    fun k => pos (Var.head t.succ k : TVar M W T))]

def haltBody (M : Machine) {W T : ℕ} (t : Fin T) : Formula :=
  acceptFormula M (W := W) t.castSucc ++
    (copyFamily (fun s => (Var.state t.castSucc s : TVar M W T)) (fun s => .state t.succ s) ++
      (copyFamily (fun p => (Var.head t.castSucc p : TVar M W T)) (fun p => .head t.succ p) ++
        allFin (fun p : Fin W => copyFamily
          (fun a => (Var.tape t.castSucc p a : TVar M W T)) (fun a => .tape t.succ p a))))

def ruleBody (M : Machine) {W T : ℕ} (t : Fin T) (r : Rule M.stateExtra M.symbolExtra) : Formula :=
  force (Var.state t.castSucc r.source : TVar M W T) ++
    (force (Var.state t.succ r.target : TVar M W T) ++
      (allFin (fun p : Fin W => guard (Var.head t.castSucc p : TVar M W T)
        (force (Var.tape t.castSucc p r.read : TVar M W T) ++
          (force (Var.tape t.succ p r.write : TVar M W T) ++ headTarget M t p r.move))) ++
        allFin (fun p : Fin W => guardLiteral (neg (Var.head t.castSucc p : TVar M W T))
          (copyFamily (fun a => (Var.tape t.castSucc p a : TVar M W T)) (fun a => .tape t.succ p a)))))

def choiceBody (M : Machine) {W T : ℕ} (t : Fin T) (r : Fin (M.rules.length+1)) : Formula :=
  Fin.cases (haltBody M (W := W) t) (fun j => ruleBody M (W := W) t M.rules[j.val]) r

def transitionFormula (M : Machine) (W T : ℕ) : Formula :=
  allFin (fun t : Fin T => allFin (fun r : Fin (M.rules.length+1) =>
    guard (Var.choice t r : TVar M W T) (choiceBody M (W := W) t r)))

def tableauFormula (M : Machine) (word : List Bool) (T : ℕ) : Formula :=
  let W := windowWidth word T
  shapeFormula M W T ++ (initialFormula M W T (windowInitial M word T) ++
    (acceptFormula M (W := W) (Fin.last T) ++ transitionFormula M W T))

end BalancedAssortments.CookLevin
