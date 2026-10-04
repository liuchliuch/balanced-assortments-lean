import BalancedAssortments.NPCNFBasic

/-! Explicit finite tableau variables and ordinary CNF constructors. Variable
labels use a computable sum/product bijection to an initial natural segment. -/
namespace BalancedAssortments.CookLevin
open NPCNF

inductive Var (q g W T R : ℕ)
  | state (t : Fin (T+1)) (s : Fin q)
  | head (t : Fin (T+1)) (p : Fin W)
  | tape (t : Fin (T+1)) (p : Fin W) (a : Fin g)
  | choice (t : Fin T) (r : Fin R)
  deriving DecidableEq

abbrev Shape (q g W T R : ℕ) :=
  ((Fin (T+1) × Fin q) ⊕ (Fin (T+1) × Fin W)) ⊕
  ((Fin (T+1) × (Fin W × Fin g)) ⊕ (Fin T × Fin R))

def shapeEquiv (q g W T R : ℕ) : Var q g W T R ≃ Shape q g W T R where
  toFun
    | .state t s => .inl (.inl (t,s))
    | .head t p => .inl (.inr (t,p))
    | .tape t p a => .inr (.inl (t,p,a))
    | .choice t r => .inr (.inr (t,r))
  invFun
    | .inl (.inl (t,s)) => .state t s
    | .inl (.inr (t,p)) => .head t p
    | .inr (.inl (t,p,a)) => .tape t p a
    | .inr (.inr (t,r)) => .choice t r
  left_inv := by intro v; cases v <;> rfl
  right_inv := by intro v; rcases v with (⟨t,s⟩|⟨t,p⟩) | (⟨t,p,a⟩|⟨t,r⟩) <;> rfl

def variableCount (q g W T R : ℕ) : ℕ :=
  (T+1)*q+(T+1)*W+((T+1)*(W*g)+T*R)

def indexEquiv (q g W T R : ℕ) : Var q g W T R ≃ Fin (variableCount q g W T R) :=
  (shapeEquiv q g W T R).trans
    ((Equiv.sumCongr
      ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)
      ((Equiv.sumCongr
        ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)
        finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv)

variable {q g W T R : ℕ}

def index (v : Var q g W T R) : ℕ := (indexEquiv q g W T R v).val
lemma index_lt (v : Var q g W T R) : index v < variableCount q g W T R :=
  (indexEquiv q g W T R v).isLt
lemma index_injective : Function.Injective (index : Var q g W T R → ℕ) :=
  Fin.val_injective.comp (indexEquiv q g W T R).injective

def extendAssignment (a : Var q g W T R → Bool) : Assignment := fun k =>
  if h : k < variableCount q g W T R then a ((indexEquiv q g W T R).symm ⟨k,h⟩) else false

lemma extendAssignment_apply (a : Var q g W T R → Bool) (v : Var q g W T R) :
    extendAssignment a (index v)=a v := by
  rw [extendAssignment,dif_pos (index_lt v)]
  change a ((indexEquiv q g W T R).symm (indexEquiv q g W T R v))=a v
  rw [Equiv.symm_apply_apply]

def pos (v : Var q g W T R) : Literal := NPCNF.positive (index v)
def neg (v : Var q g W T R) : Literal := NPCNF.negative (index v)

@[simp] lemma eval_pos (σ : Assignment) (v : Var q g W T R) : literalEval σ (pos v)=σ (index v) := rfl
@[simp] lemma eval_neg (σ : Assignment) (v : Var q g W T R) : literalEval σ (neg v)=!σ (index v) := rfl

def allFin {n : ℕ} (f : Fin n → Formula) : Formula := (List.finRange n).flatMap f

lemma eval_allFin (σ : Assignment) {n : ℕ} (f : Fin n → Formula) :
    formulaEval σ (allFin f)=true ↔ ∀ i,formulaEval σ (f i)=true := by
  simp only [formulaEval_eq_true_iff]
  constructor
  · intro h i c hc
    exact h c (List.mem_flatMap.mpr ⟨i,by simp,hc⟩)
  · intro h c hc
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hc
    exact h i c hi

def force (v : Var q g W T R) : Formula := [[pos v]]
lemma eval_force (σ : Assignment) (v : Var q g W T R) :
    formulaEval σ (force v)=true ↔ σ (index v)=true := by simp [force]

lemma eval_implication (σ : Assignment) (a b : Var q g W T R) :
    clauseEval σ [neg a,pos b]=true ↔ (σ (index a)=true → σ (index b)=true) := by
  cases ha : σ (index a) <;> cases hb : σ (index b) <;> simp [ha,hb]

def guardLiteral (l : Literal) (F : Formula) : Formula := F.map (fun c => l.neg::c)
lemma eval_guardLiteral (σ : Assignment) (l : Literal) (F : Formula) :
    formulaEval σ (guardLiteral l F)=true ↔ (literalEval σ l=true → formulaEval σ F=true) := by
  cases he : literalEval σ l <;>
    simp [guardLiteral,formulaEval,List.all_map,clauseEval_cons,literalEval_neg,he]

def guard (v : Var q g W T R) (F : Formula) : Formula := guardLiteral (pos v) F
lemma eval_guard (σ : Assignment) (v : Var q g W T R) (F : Formula) :
    formulaEval σ (guard v F)=true ↔ (σ (index v)=true → formulaEval σ F=true) := by
  exact eval_guardLiteral σ (pos v) F

def copyFamily {n : ℕ} (f h : Fin n → Var q g W T R) : Formula :=
  allFin fun i => [[neg (f i),pos (h i)]]
lemma eval_copyFamily (σ : Assignment) {n : ℕ} (f h : Fin n → Var q g W T R) :
    formulaEval σ (copyFamily f h)=true ↔ ∀ i,σ (index (f i))=true → σ (index (h i))=true := by
  rw [copyFamily,eval_allFin]
  simp only [formulaEval_cons,formulaEval_nil,Bool.and_true,eval_implication]

def exactlyOne {n : ℕ} (f : Fin n → Var q g W T R) : Formula :=
  [((List.finRange n).map fun i => pos (f i))] ++
    allFin (fun i => allFin (fun j => if i=j then [] else [[neg (f i),neg (f j)]]))

def OneHot {n : ℕ} (σ : Assignment) (f : Fin n → Var q g W T R) : Prop :=
  ∃ k, σ (index (f k))=true ∧ ∀ i,σ (index (f i))=true → i=k

lemma eval_negative_pair (σ : Assignment) (a b : Var q g W T R) :
    clauseEval σ [neg a,neg b]=true ↔ ¬(σ (index a)=true ∧ σ (index b)=true) := by
  cases ha : σ (index a) <;> cases hb : σ (index b) <;> simp [ha,hb]

lemma eval_atLeast (σ : Assignment) {n : ℕ} (f : Fin n → Var q g W T R) :
    clauseEval σ ((List.finRange n).map fun i => pos (f i))=true ↔ ∃ i,σ (index (f i))=true := by
  rw [clauseEval_eq_true_iff]
  simp only [List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨l,⟨i,rfl⟩,hi⟩; exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩; exact ⟨pos (f i),⟨i,rfl⟩,hi⟩

lemma eval_exactlyOne (σ : Assignment) {n : ℕ} (f : Fin n → Var q g W T R) :
    formulaEval σ (exactlyOne f)=true ↔ OneHot σ f := by
  rw [exactlyOne,formulaEval_append,Bool.and_eq_true]
  simp only [formulaEval_cons,formulaEval_nil,Bool.and_true,eval_atLeast,eval_allFin]
  constructor
  · rintro ⟨⟨k,hk⟩,hall⟩
    refine ⟨k,hk,?_⟩
    intro i hi
    by_contra hne
    have hh := hall i k
    simp only [if_neg hne,formulaEval_cons,formulaEval_nil,Bool.and_true,eval_negative_pair] at hh
    exact hh ⟨hi,hk⟩
  · rintro ⟨k,hk,hu⟩
    refine ⟨⟨k,hk⟩,?_⟩
    intro i j
    by_cases he : i=j
    · simp [he]
    · simp only [if_neg he,formulaEval_cons,formulaEval_nil,Bool.and_true,eval_negative_pair]
      rintro ⟨hi,hj⟩
      exact he ((hu i hi).trans (hu j hj).symm)

end BalancedAssortments.CookLevin
