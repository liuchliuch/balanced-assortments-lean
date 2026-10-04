import BalancedAssortments.CookLevinStackTypedTableau

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF

def cholds (σ : Assignment) (p : ClauseCode) (e : Fin 9 → List Bool) (f : ℕ → List Bool) : Prop :=
  clauseEval σ ((p.eval e f).map Encoding.BitLiteral.decode)=true
def fholds (σ : Assignment) (p : FormulaCode) (e : Fin 9 → List Bool) (f : ℕ → List Bool) : Prop :=
  formulaEval σ ((p.eval e f).map (List.map Encoding.BitLiteral.decode))=true

theorem collect_mapIdx {α : Type*} (f : ℕ → Bool → List α) (i : ℕ) (bs : List Bool) :
    collect f i bs=(bs.mapIdx (fun j b => f (i+j) b)).reverse.flatten := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih =>
    simp only [collect,ih,List.mapIdx_cons,List.reverse_cons,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem mem_collect {α : Type*} (f : ℕ → Bool → List α) (i : ℕ) (bs : List Bool) (a : α) :
    a∈collect f i bs ↔ ∃ j : Fin bs.length,a∈f (i+j.val) bs[j.val] := by
  rw [collect_mapIdx]
  simp only [List.mem_flatten,List.mem_reverse,List.mem_mapIdx]
  constructor
  · rintro ⟨l,⟨j,hj,rfl⟩,ha⟩
    exact ⟨⟨j,hj⟩,ha⟩
  · rintro ⟨j,ha⟩
    exact ⟨_,⟨j.val,j.isLt,rfl⟩,ha⟩

@[simp] theorem cholds_empty (σ : Assignment) (e f) : ¬cholds σ .empty e f := by simp [cholds,ClauseCode.eval]
@[simp] theorem cholds_literal (σ : Assignment) (e f) (l : L) :
    cholds σ (.literal l) e f ↔ literalEval σ (evalLiteral e l).decode=true := by simp [cholds,ClauseCode.eval]
@[simp] theorem cholds_seq (σ : Assignment) (e f) (a b : ClauseCode) :
    cholds σ (.seq a b) e f ↔ cholds σ a e f ∨ cholds σ b e f := by
  simp [cholds,ClauseCode.eval,clauseEval,List.any_append,or_comm]
@[simp] theorem fholds_empty (σ : Assignment) (e f) : fholds σ .empty e f := by simp [fholds,FormulaCode.eval]
@[simp] theorem fholds_clause (σ : Assignment) (e f) (p : ClauseCode) :
    fholds σ (.clause p) e f ↔ cholds σ p e f := by simp [fholds,cholds,FormulaCode.eval]
@[simp] theorem fholds_seq (σ : Assignment) (e f) (a b : FormulaCode) :
    fholds σ (.seq a b) e f ↔ fholds σ a e f ∧ fholds σ b e f := by
  simp [fholds,FormulaCode.eval,and_comm]

theorem cholds_each (σ : Assignment) (e f) (i : Fin 9) (src : ℕ) (a b : ClauseCode) :
    cholds σ (.each i src a b) e f ↔ ∃ j : Fin (f src).length,
      cholds σ (if (f src)[j.val] then b else a) (Function.update e i (StackCount.counterBits j.val)) f := by
  simp only [cholds,ClauseCode.eval,clauseEval_eq_true_iff,List.mem_map]
  constructor
  · rintro ⟨l,⟨raw,hm,rfl⟩,hl⟩
    obtain ⟨j,hj⟩ := (mem_collect _ _ _ _).mp hm
    simp only [Nat.zero_add] at hj
    refine ⟨j,raw.decode,⟨raw,?_,rfl⟩,hl⟩
    split at hj <;> simp_all
  · rintro ⟨j,l,⟨raw,hm,rfl⟩,hl⟩
    refine ⟨raw.decode,⟨raw,(mem_collect _ _ _ _).mpr ⟨j,?_⟩,rfl⟩,hl⟩
    simp only [Nat.zero_add]
    split <;> simp_all

theorem fholds_each (σ : Assignment) (e f) (i : Fin 9) (src : ℕ) (a b : FormulaCode) :
    fholds σ (.each i src a b) e f ↔ ∀ j : Fin (f src).length,
      fholds σ (if (f src)[j.val] then b else a) (Function.update e i (StackCount.counterBits j.val)) f := by
  simp only [fholds,FormulaCode.eval,formulaEval_eq_true_iff,List.mem_map]
  constructor
  · intro h j c hc
    obtain ⟨raw,hr,rfl⟩ := hc
    apply h _ ⟨raw,(mem_collect _ _ _ _).mpr ⟨j,?_⟩,rfl⟩
    simp only [Nat.zero_add]
    split <;> simp_all
  · intro h c hc
    obtain ⟨raw,hr,rfl⟩ := hc
    obtain ⟨j,hj⟩ := (mem_collect _ _ _ _).mp hr
    apply h j _ ⟨raw,?_,rfl⟩
    simp only [Nat.zero_add] at hj
    split at hj <;> simp_all

end BalancedAssortments.CookLevin.StackTableau
