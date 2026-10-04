import BalancedAssortments.CookLevinStackTypedAddresses
import BalancedAssortments.CookLevinStackTableauRaw

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine ComplexityTimeBinary

def cbounded (V : ℕ) (p : ClauseCode) (e : Fin 9 → List Bool) (f : ℕ → List Bool) : Prop :=
  ∀ l∈p.eval e f,value l.labelBits<V
def fbounded (V : ℕ) (p : FormulaCode) (e : Fin 9 → List Bool) (f : ℕ → List Bool) : Prop :=
  ∀ c∈p.eval e f,∀ l∈c,value l.labelBits<V

lemma forall_mem_collect {α : Type*} (p : α → Prop) (g : ℕ → Bool → List α) (i : ℕ) (bs : List Bool) :
    (∀ a∈collect g i bs,p a) ↔ ∀ j : Fin bs.length,∀ a∈g (i+j.val) bs[j.val],p a := by
  constructor
  · intro h j a ha
    exact h a ((mem_collect _ _ _ _).mpr ⟨j,ha⟩)
  · intro h a ha
    obtain ⟨j,hj⟩ := (mem_collect _ _ _ _).mp ha
    exact h j a hj

@[simp] lemma cbounded_empty (V e f) : cbounded V .empty e f := by simp [cbounded,ClauseCode.eval]
@[simp] lemma cbounded_literal (V e f) (l : L) : cbounded V (.literal l) e f ↔ denote e l.1<V := by
  simp [cbounded,ClauseCode.eval,evalLiteral,BitExpr.run_correct,denote]
@[simp] lemma cbounded_seq (V e f) (a b : ClauseCode) : cbounded V (.seq a b) e f ↔ cbounded V a e f ∧ cbounded V b e f := by
  simp [cbounded,ClauseCode.eval,or_imp,forall_and,and_comm]
@[simp] lemma cbounded_branch (V e f) (a b : E) (y n : ClauseCode) :
    cbounded V (.branch a b y n) e f ↔ if denote e a≤denote e b then cbounded V y e f else cbounded V n e f := by
  simp only [cbounded,ClauseCode.eval,BitExpr.run_correct,denote]
  split <;> rfl
@[simp] lemma cbounded_each (V e f) (i : Fin 9) (src : ℕ) (a b : ClauseCode) :
    cbounded V (.each i src a b) e f ↔ ∀ j : Fin (f src).length,
      cbounded V (if (f src)[j.val] then b else a) (Function.update e i (StackCount.counterBits j.val)) f := by
  simp only [cbounded,ClauseCode.eval,forall_mem_collect,Nat.zero_add]
  apply forall_congr';intro j;split <;> rfl
@[simp] lemma fbounded_empty (V e f) : fbounded V .empty e f := by simp [fbounded,FormulaCode.eval]
@[simp] lemma fbounded_clause (V e f) (c : ClauseCode) : fbounded V (.clause c) e f ↔ cbounded V c e f := by simp [fbounded,cbounded,FormulaCode.eval]
@[simp] lemma fbounded_seq (V e f) (a b : FormulaCode) : fbounded V (.seq a b) e f ↔ fbounded V a e f ∧ fbounded V b e f := by
  simp [fbounded,FormulaCode.eval,or_imp,forall_and,and_comm]
@[simp] lemma fbounded_branch (V e f) (a b : E) (y n : FormulaCode) :
    fbounded V (.branch a b y n) e f ↔ if denote e a≤denote e b then fbounded V y e f else fbounded V n e f := by
  simp only [fbounded,FormulaCode.eval,BitExpr.run_correct,denote]
  split <;> rfl
@[simp] lemma fbounded_each (V e f) (i : Fin 9) (src : ℕ) (a b : FormulaCode) :
    fbounded V (.each i src a b) e f ↔ ∀ j : Fin (f src).length,
      fbounded V (if (f src)[j.val] then b else a) (Function.update e i (StackCount.counterBits j.val)) f := by
  simp only [fbounded,FormulaCode.eval,forall_mem_collect,Nat.zero_add]
  apply forall_congr';intro j;split <;> rfl
@[simp] lemma cbounded_literals (V e f) (ls : List L) : cbounded V (Typed.literals ls) e f ↔ ∀ l∈ls,denote e l.1<V := by
  induction ls with
  | nil => simp [Typed.literals]
  | cons l ls ih => simp [Typed.literals,ih,and_comm]
@[simp] lemma fbounded_typed_clause (V e f) (ls : List L) : fbounded V (Typed.clause ls) e f ↔ ∀ l∈ls,denote e l.1<V := by simp [Typed.clause]
@[simp] lemma fbounded_all (V e f) (ps : List FormulaCode) : fbounded V (Typed.all ps) e f ↔ ∀ p∈ps,fbounded V p e f := by
  induction ps with
  | nil => simp [Typed.all]
  | cons p ps ih => simp [Typed.all,ih]
@[simp] lemma fbounded_loop (V e f) (i : Fin 9) (src : ℕ) (p : FormulaCode) :
    fbounded V (Typed.loop i src p) e f ↔ ∀ j : Fin (f src).length,
      fbounded V p (Function.update e i (StackCount.counterBits j.val)) f := by simp [Typed.loop]
@[simp] lemma cbounded_cloop (V e f) (i : Fin 9) (src : ℕ) (p : ClauseCode) :
    cbounded V (Typed.cloop i src p) e f ↔ ∀ j : Fin (f src).length,
      cbounded V p (Function.update e i (StackCount.counterBits j.val)) f := by simp [Typed.cloop]

lemma fixedExactlyOne_bounded (V e f) (es : List E) (h : ∀ a∈es,denote e a<V) :
    fbounded V (Typed.fixedExactlyOne es) e f := by
  rw [Typed.fixedExactlyOne,fbounded_seq]
  constructor
  · simpa using h
  · rw [fbounded_all]
    intro p hp
    obtain ⟨pair,hpair,hm⟩ := List.mem_flatMap.mp hp
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hm
    rw [fbounded_typed_clause]
    intro l hl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl|rfl
    · exact h _ (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hpair))
    · exact h _ (List.mem_of_mem_drop hb)

lemma state_bound {M : Machine} {W T : ℕ} {e : Fin 9 → List Bool} (h : Dimensions M W T e)
    (a b : E) (ht : denote e a<T+1) (hs : denote e b<M.stateExtra+1) :
    denote e (state a b)<variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1) := by
  rw [address_state h a b ⟨_,ht⟩ ⟨_,hs⟩ rfl rfl]
  exact index_lt _
lemma head_bound {M : Machine} {W T : ℕ} {e : Fin 9 → List Bool} (h : Dimensions M W T e)
    (a b : E) (ht : denote e a<T+1) (hp : denote e b<W) :
    denote e (head a b)<variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1) := by
  rw [address_head h a b ⟨_,ht⟩ ⟨_,hp⟩ rfl rfl]
  exact index_lt _
lemma tape_bound {M : Machine} {W T : ℕ} {e : Fin 9 → List Bool} (h : Dimensions M W T e)
    (a b c : E) (ht : denote e a<T+1) (hp : denote e b<W) (hs : denote e c<M.symbolExtra+3) :
    denote e (tape a b c)<variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1) := by
  rw [address_tape h a b c ⟨_,ht⟩ ⟨_,hp⟩ ⟨_,hs⟩ rfl rfl rfl]
  exact index_lt _
lemma choice_bound {M : Machine} {W T : ℕ} {e : Fin 9 → List Bool} (h : Dimensions M W T e)
    (a b : E) (ht : denote e a<T) (hr : denote e b<M.rules.length+1) :
    denote e (choice a b)<variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1) := by
  rw [address_choice h a b ⟨_,ht⟩ ⟨_,hr⟩ rfl rfl]
  exact index_lt _

end BalancedAssortments.CookLevin.StackTableau
