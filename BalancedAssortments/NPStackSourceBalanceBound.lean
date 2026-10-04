import BalancedAssortments.NPStackSourceBalanceCorrect
import BalancedAssortments.NPStackVerifierControlBound

namespace BalancedAssortments.NPStack.SourceVerifier.Balance
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl NPStackFields

def WidthInvariant (s : Registers) (L : ℕ) : Prop :=
  (∀ k,width (s k)≤3*L+1) ∧ width (s .alpha)≤L ∧ width (s .alphaDen)≤L ∧ width (s .maximum)≤L

lemma initial_widthInvariant (s : Registers) (L : ℕ) (hs : ∀ k,width (s k)≤L) : WidthInvariant s L := by
  exact ⟨fun k=>(hs k).trans (by omega),hs _,hs _,hs _⟩

lemma loaded_width (s : Registers) (x : Triple) (B : ℕ)
    (hs : ∀ k,width (s k)≤B) (hx : ∀ i,(x i).length≤B) : ∀ k,width (loaded s x k)≤B := by
  intro k
  have hk := hs k
  have h1:=hx 1;have h2:=hx 2
  cases k <;> simp [loaded,width] at * <;> omega

lemma next_widthInvariant (s : Registers) (x : Triple) (active : Bool) (L : ℕ)
    (hs : WidthInvariant s L) (hx : ∀ i,(x i).length≤L) : WidthInvariant (effect active (loaded s x)) L := by
  have hl := loaded_width s x (3*L+1) hs.1 (fun i=>(hx i).trans (by omega))
  have hn : width (loaded s x .numerator)≤L := by simp [loaded,width];exact ⟨hx 1,hx 2⟩
  have ha : width (loaded s x .alpha)≤L := hs.2.1
  have hd : width (loaded s x .alphaDen)≤L := hs.2.2.1
  have hm : width (loaded s x .maximum)≤L := hs.2.2.2
  have ht:=zmul_width (loaded s x .alpha) (loaded s x .maximum)
  have hp:=zmul_width (loaded s x .alphaDen) (loaded s x .numerator)
  refine ⟨?_,?_,?_,?_⟩
  · intro k
    have hk:=hl k
    cases active with
    | false => exact hk
    | true =>
      cases k <;> simp only [effect,VerifierCommands.balanceCommand,ite_true,VerifierCommands.eval_script,VerifierCommands.guardLE,eval]
      all_goals split_ifs <;> simp [evalAssignments,balanceAssignments,evalAssignment,Function.update] <;> omega
  all_goals
    rw [show effect active (loaded s x) _=(loaded s x) _ from VerifierCommands.balance_preserves _ _ _ (by decide) (by decide)]
    assumption

lemma packed_rows_width (s : Registers) (B : ℕ) (hs : ∀ k,width (s k)≤B) :
    ∀ k∈(ClearRows.rowKeys (W:=Workspace)),(packedStore s [] [] k).length≤B := by
  intro k hk
  simp only [ClearRows.rowKeys,List.mem_map] at hk
  obtain ⟨i,_,rfl⟩ := hk
  have h0:=hs .price;have h1:=hs .priceDen;have h2:=hs .attraction;have h3:=hs .attractionDen;have h4:=hs .numerator
  simp only [width] at h0 h1 h2 h3 h4
  fin_cases i <;> simp [packedStore,arithmeticInverse,arithmeticMap,extraStore,SignedAssignment.initialStore,SignedAssignment.store] <;> omega

lemma row_clear_bound (s : Registers) (B : ℕ) (hs : ∀ k,width (s k)≤B) :
    ClearRows.clearCost ClearRows.rowKeys (packedStore s [] [])≤9*(B+1) := by
  have h:=ClearRows.clearCost_bound ClearRows.rowKeys (packedStore s [] []) (packed_rows_width s B hs)
  simpa [ClearRows.rowKeys] using h

def rowBound (L : ℕ) : ℕ := 44*(L+1)+
  (costCoefficient (VerifierCommands.balanceCommand false)+costCoefficient (VerifierCommands.balanceCommand true))*(3*L+2)^2

lemma rowCost_bound (s : Registers) (x : Triple) (active : Bool) (L : ℕ)
    (hs : WidthInvariant s L) (hx : ∀ i,(x i).length≤L) : rowCost s x active≤rowBound L := by
  have hl:=loaded_width s x (3*L+1) hs.1 (fun i=>(hx i).trans (by omega))
  have hb:=budget_quadratic (VerifierCommands.balanceCommand active) (loaded s x) (L:=3*L+2)
    (fun k=>by have h:=hl k;omega)
  have hc:=row_clear_bound (effect active (loaded s x)) (3*L+1) (next_widthInvariant s x active L hs hx).1
  have hx0:=hx 0;have hx1:=hx 1;have hx2:=hx 2
  have hr : NPStackSourceRecords.recordCost (List.ofFn x)≤15*L+9 := by
    simp [NPStackSourceRecords.recordCost,List.ofFn_succ];omega
  have hcoef : costCoefficient (VerifierCommands.balanceCommand active)≤
      costCoefficient (VerifierCommands.balanceCommand false)+costCoefficient (VerifierCommands.balanceCommand true) := by
    cases active <;> omega
  have hb' := hb.trans (Nat.mul_le_mul_right _ hcoef)
  unfold rowCost rowBound
  omega

theorem loopCost_bound (s : Registers) (xs : List Triple) (L : ℕ)
    (hs : WidthInvariant s L) (hx : ∀ x∈xs,∀ i,(x i).length≤L) :
    loopCost s xs≤xs.length*rowBound L+1 := by
  induction xs generalizing s with
  | nil => simp [loopCost]
  | cons x xs ih =>
    have hxx:=hx x (by simp)
    cases hm : NPStackMask.maskValue (x 0) with
    | none => simp [loopCost,hm]
    | some active =>
      have hn:=next_widthInvariant s x active L hs hxx
      have ht:=ih _ hn (by intro y hy;exact hx y (by simp [hy]))
      have hr:=rowCost_bound s x active L hs hxx
      simp only [loopCost,hm,List.length_cons,Nat.add_mul]
      omega

theorem loop_success_polynomial (s u : Registers) (xs : List Triple) (L : ℕ)
    (hs : ∀ k,width (s k)≤L) (hx : ∀ x∈xs,∀ i,(x i).length≤L)
    (h : loopValue s xs=some u) :
    ∃ t≤xs.length*rowBound L+1,Run loopProgram t ⟨.probe,stable s (stream xs)⟩ ⟨.accept,stable u []⟩ := by
  obtain ⟨t,ht,hr⟩ := loop_success s u xs h
  exact ⟨t,ht.trans (loopCost_bound s xs L (initial_widthInvariant s L hs) hx),hr⟩

end BalancedAssortments.NPStack.SourceVerifier.Balance
