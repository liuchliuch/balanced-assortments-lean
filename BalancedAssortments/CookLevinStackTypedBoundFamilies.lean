import BalancedAssortments.CookLevinStackTypedBounds
import BalancedAssortments.CookLevinStackTypedShape

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine ComplexityTimeBinary

def V (M : Machine) (W T : ℕ) := variableCount (M.stateExtra+1) (M.symbolExtra+3) W T (M.rules.length+1)

lemma fixed_range_bounded (v e f n) (a : ℕ → E) (h : ∀ i<n,denote e (a i)<v) :
    fbounded v (Typed.fixedExactlyOne ((List.range n).map a)) e f := by
  apply fixedExactlyOne_bounded
  intro b hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  exact h i (List.mem_range.mp hi)
lemma state_family_bounded {M : Machine} {W T : ℕ} {e f} (hd : Dimensions M W T e)
    (ht : value (e 5)<T+1) :
    fbounded (V M W T) (Typed.fixedExactlyOne ((List.range (M.stateExtra+1)).map (fun s => state (x 5) (c s)))) e f := by
  apply fixed_range_bounded
  intro i hi
  exact state_bound hd _ _ ht (by simpa using hi)
lemma tape_family_bounded {M : Machine} {W T : ℕ} {e f} (hd : Dimensions M W T e)
    (ht : value (e 5)<T+1) (hp : value (e 6)<W) :
    fbounded (V M W T) (Typed.fixedExactlyOne ((List.range (M.symbolExtra+3)).map (fun a => tape (x 5) (x 6) (c a)))) e f := by
  apply fixed_range_bounded
  intro i hi
  exact tape_bound hd _ _ _ ht hp (by simpa using hi)
lemma choice_family_bounded {M : Machine} {W T : ℕ} {e f} (hd : Dimensions M W T e)
    (ht : value (e 5)<T) :
    fbounded (V M W T) (Typed.fixedExactlyOne ((List.range (M.rules.length+1)).map (fun r => choice (x 5) (c r)))) e f := by
  apply fixed_range_bounded
  intro i hi
  exact choice_bound hd _ _ ht (by simpa using hi)

lemma accepting_bounded {M : Machine} {W T : ℕ} {e} (hd : Dimensions M W T e)
    (a : E) (ht : denote e a<T+1) : ∀ l∈Typed.accepting M a,denote e l.1<V M W T := by
  intro l hl
  obtain ⟨s,_,rfl⟩ := List.mem_map.mp hl
  exact state_bound hd _ _ ht (by simpa using s.isLt)

lemma cbounded_branch_of (v e f) (a b : E) (y n : ClauseCode)
    (hy : cbounded v y e f) (hn : cbounded v n e f) : cbounded v (.branch a b y n) e f := by
  rw [cbounded_branch];split <;> assumption
lemma fbounded_branch_of (v e f) (a b : E) (y n : FormulaCode)
    (hy : fbounded v y e f) (hn : fbounded v n e f) : fbounded v (.branch a b y n) e f := by
  rw [fbounded_branch];split <;> assumption
lemma cbounded_eqBranch_of (v e f) (a b : E) (y n : ClauseCode)
    (hy : cbounded v y e f) (hn : cbounded v n e f) : cbounded v (Typed.eqBranch a b y n) e f := by
  exact cbounded_branch_of _ _ _ _ _ _ _ (cbounded_branch_of _ _ _ _ _ _ _ hy hn) hn

lemma move_bounded {M : Machine} {W T : ℕ} {e f} (hd : Dimensions M W T e)
    (ht : value (e 5)<T) (hp : value (e 8)<W) (m : Move) :
    cbounded (V M W T) (Typed.moveTarget m) e f := by
  have hh : cbounded (V M W T) (.literal (head (succ (x 5)) (x 8),true)) e f := by
    rw [cbounded_literal]
    exact head_bound hd _ _ (by simp;omega) hp
  cases m <;> exact cbounded_eqBranch_of _ _ _ _ _ _ _ hh (cbounded_empty _ _ _)

lemma shape_row_bounded {M : Machine} {W T : ℕ} {e f} (hd : Dimensions M W T e)
    (ht : value (e 5)<T+1) (hf : (f 13).length=W) : fbounded (V M W T) (shapeRow M) e f := by
  simp only [shapeRow,fbounded_all,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  refine ⟨state_family_bounded hd ht,?_,?_,?_⟩
  · simp only [headAtLeast,Typed.dynamicClause,fbounded_clause,cbounded_cloop,cbounded_literal]
    intro j
    exact head_bound (hd.update 6 (by decide) _) _ _
      (by simpa [Function.update] using ht) (by simp [StackCount.counterBits_value];simpa [hf] using j.isLt)
  · simp only [headAtMost,fbounded_loop]
    intro i j
    apply fbounded_branch_of
    · rw [fbounded_typed_clause]
      intro l hl
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      rcases hl with rfl|rfl
      all_goals apply head_bound ((hd.update 6 (by decide) _).update 8 (by decide) _)
      all_goals simp [Function.update,StackCount.counterBits_value]
      · exact ht
      · simpa [hf] using i.isLt
      · exact ht
      · simpa [hf] using j.isLt
    · exact fbounded_empty _ _ _
  · rw [fbounded_loop]
    intro p
    exact tape_family_bounded (hd.update 6 (by decide) _)
      (by simpa [Function.update] using ht) (by simp [StackCount.counterBits_value];simpa [hf] using p.isLt)

lemma shape_bounded (M : Machine) (word : List Bool) (T : ℕ) :
    fbounded (tableauVariableCount M word.length T) (Typed.shape M)
      (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T) := by
  change fbounded (V M (windowWidth word T) T)
    (.seq (Typed.loop 5 12 (shapeRow M)) (Typed.loop 5 11 (Typed.fixedExactlyOne
      ((List.range (M.rules.length+1)).map (fun r => choice (x 5) (c r)))))) _ _
  rw [fbounded_seq]
  constructor
  · rw [fbounded_loop]
    intro t
    apply shape_row_bounded ((dimensions_scalar M word T).update 5 (by decide) _)
    · simp [StackCount.counterBits_value];simpa using t.isLt
    · simp
  · rw [fbounded_loop]
    intro t
    apply choice_family_bounded ((dimensions_scalar M word T).update 5 (by decide) _)
    simp [StackCount.counterBits_value];simpa using t.isLt

end BalancedAssortments.CookLevin.StackTableau
