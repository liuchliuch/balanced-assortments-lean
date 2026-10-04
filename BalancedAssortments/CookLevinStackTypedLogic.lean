import BalancedAssortments.CookLevinStackTypedSemantics

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF ComplexityTimeBinary

def denote (e : Fin 9 → List Bool) (a : E) : ℕ := a.meaning (fun i => value (e i))
@[simp] lemma denote_x (e) (i : Fin 9) : denote e (x i)=value (e i) := rfl
@[simp] lemma denote_c (e) (n : ℕ) : denote e (c n)=n := by simp [denote,c,BitExpr.meaning]
@[simp] lemma denote_plus (e) (a b : E) : denote e (plus a b)=denote e a+denote e b := rfl
@[simp] lemma denote_times (e) (a b : E) : denote e (times a b)=denote e a*denote e b := rfl
@[simp] lemma denote_succ (e) (a : E) : denote e (succ a)=denote e a+1 := by simp [succ]
@[simp] lemma denote_state (e) (t s : E) : denote e (state t s)=denote e s+value (e 0)*denote e t := rfl
@[simp] lemma denote_head (e) (t p : E) :
    denote e (head t p)=(value (e 3)+1)*value (e 0)+(denote e p+value (e 2)*denote e t) := by simp [head]
@[simp] lemma denote_tape (e) (t p a : E) :
    denote e (tape t p a)=((value (e 3)+1)*value (e 0)+(value (e 3)+1)*value (e 2))+
      (denote e a+value (e 1)*denote e p+value (e 2)*value (e 1)*denote e t) := by simp [tape]
@[simp] lemma denote_choice (e) (t r : E) :
    denote e (choice t r)=((value (e 3)+1)*value (e 0)+(value (e 3)+1)*value (e 2))+
      ((value (e 3)+1)*(value (e 2)*value (e 1))+(denote e r+value (e 4)*denote e t)) := by simp [choice]
@[simp] lemma evalLiteral_true (σ : Assignment) (e) (a : E) :
    literalEval σ (evalLiteral e (a,true)).decode=σ (denote e a) := by
  simp [evalLiteral,Encoding.BitLiteral.decode,literalEval,BitExpr.run_correct,denote]
@[simp] lemma evalLiteral_false (σ : Assignment) (e) (a : E) :
    literalEval σ (evalLiteral e (a,false)).decode= !σ (denote e a) := by
  simp [evalLiteral,Encoding.BitLiteral.decode,literalEval,BitExpr.run_correct,denote]

@[simp] theorem cholds_literals (σ : Assignment) (e f) (ls : List L) :
    cholds σ (Typed.literals ls) e f ↔ ∃ l∈ls,literalEval σ (evalLiteral e l).decode=true := by
  induction ls with
  | nil => simp [Typed.literals]
  | cons l ls ih => simp [Typed.literals,ih,or_comm]
@[simp] theorem fholds_typed_clause (σ : Assignment) (e f) (ls : List L) :
    fholds σ (Typed.clause ls) e f ↔ ∃ l∈ls,literalEval σ (evalLiteral e l).decode=true := by
  simp [Typed.clause]
@[simp] theorem fholds_all (σ : Assignment) (e f) (ps : List FormulaCode) :
    fholds σ (Typed.all ps) e f ↔ ∀ p∈ps,fholds σ p e f := by
  induction ps with
  | nil => simp [Typed.all]
  | cons p ps ih => simp [Typed.all,ih]
@[simp] theorem fholds_loop (σ : Assignment) (e f) (i : Fin 9) (src : ℕ) (p : FormulaCode) :
    fholds σ (Typed.loop i src p) e f ↔ ∀ j : Fin (f src).length,
      fholds σ p (Function.update e i (StackCount.counterBits j.val)) f := by
  simp [Typed.loop,fholds_each]
@[simp] theorem cholds_cloop (σ : Assignment) (e f) (i : Fin 9) (src : ℕ) (p : ClauseCode) :
    cholds σ (Typed.cloop i src p) e f ↔ ∃ j : Fin (f src).length,
      cholds σ p (Function.update e i (StackCount.counterBits j.val)) f := by
  simp [Typed.cloop,cholds_each]
@[simp] theorem cholds_branch (σ : Assignment) (e f) (a b : E) (y n : ClauseCode) :
    cholds σ (.branch a b y n) e f ↔ if denote e a≤denote e b then cholds σ y e f else cholds σ n e f := by
  simp only [cholds,ClauseCode.eval,BitExpr.run_correct,denote]
  split <;> rfl
@[simp] theorem fholds_branch (σ : Assignment) (e f) (a b : E) (y n : FormulaCode) :
    fholds σ (.branch a b y n) e f ↔ if denote e a≤denote e b then fholds σ y e f else fholds σ n e f := by
  simp only [fholds,FormulaCode.eval,BitExpr.run_correct,denote]
  split <;> rfl
@[simp] theorem cholds_eqBranch (σ : Assignment) (e f) (a b : E) (y n : ClauseCode) :
    cholds σ (Typed.eqBranch a b y n) e f ↔ if denote e a=denote e b then cholds σ y e f else cholds σ n e f := by
  simp only [Typed.eqBranch,cholds_branch]
  split_ifs <;> first | rfl | omega
end BalancedAssortments.CookLevin.StackTableau
