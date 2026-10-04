import BalancedAssortments.NPStackSourceVerifierFinalBound
import BalancedAssortments.NPStackSourceVerifierProgramComplete
import BalancedAssortments.NPStackSourceVerifierFieldBounds

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

lemma witness_triple_width (x : WitnessRecord) (B : ℕ) (hx : recordWidth x≤B) :
    ∀i,(Balance.witnessTriple x i).length≤B+1 := by
  unfold recordWidth width at hx
  intro i;fin_cases i <;> simp [Balance.witnessTriple] <;> omega

lemma fields_length_sum (fs : List (List Bool)) (B : ℕ) (hf : ∀f∈fs,f.length≤B) :
    (fs.map List.length).sum≤fs.length*B := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    have hh:=hf f (by simp)
    have ht:=ih (by intro x hx;exact hf x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul]
    omega

lemma header_cost_bound (s : Fin 8→List Bool) (c : Fin 2→List Bool) (B : ℕ)
    (hs : ∀i,(s i).length≤B) (hc : ∀i,(c i).length≤B) : Header.headerCost s c≤50*B+35 := by
  have h1:=fields_length_sum (List.ofFn s) B (by intro f hf;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hf;exact hs i)
  have h2:=fields_length_sum (List.ofFn c) B (by intro f hf;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hf;exact hc i)
  simp only [List.length_ofFn] at h1 h2
  rw [Header.headerCost_formula]
  omega

def endWidth (n B : ℕ) : ℕ := B+n*(6*B+5)
def remainingBudget (n B : ℕ) : ℕ :=
  50*B+43+scalarBudget (endWidth n B)+n*Balance.rowBound (finalWidth (endWidth n B)+(B+1))

lemma remaining_cost_bound (s : Fin 8→List Bool) (c : Fin 2→List Bool)
    (rs : List NPStackSourcePairing.PairRecord) (B : ℕ)
    (hs : ∀i,(s i).length≤B) (hc : ∀i,(c i).length≤B)
    (hB : 1≤B) (hr : ∀r∈rs,recordWidth (decodeRecord r)≤B) :
    Whole.remainingCost s c rs≤remainingBudget rs.length B := by
  have hw : ∀ k,width ((Whole.rowEnd s c rs).1 k)≤endWidth rs.length B := by
    have h:=trace_width (rs.map decodeRow) (Whole.initialRegisters s c) [] (A:=B) (B:=B)
      (le_refl _) (initial_width s c hB hs hc) (by simpa [Whole.initialRegisters,zOne,width] using hB)
      (by intro r hr';obtain ⟨rr,hrr,rfl⟩:=List.mem_map.mp hr';exact hr rr hrr)
    simpa only [Whole.rowEnd,endWidth,List.length_map] using h
  have hh:=header_cost_bound s c B hs hc
  have hsc:=scalar_budget_bound (Whole.rowEnd s c rs).1 (endWidth rs.length B) hw
  have hf:=final_width (Whole.rowEnd s c rs).1 (endWidth rs.length B) hw
  have hbal := Balance.loopCost_bound (finalRegisters (Whole.rowEnd s c rs).1) (Whole.balanceTriples rs)
    (finalWidth (endWidth rs.length B)+(B+1))
    (Balance.initial_widthInvariant _ _ (fun k=>(hf k).trans (by omega)))
    (by
      intro x hx i
      obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
      obtain ⟨r,hr',rfl⟩:=List.mem_map.mp (List.mem_reverse.mp hv)
      exact (witness_triple_width (decodeRecord r) B (hr r hr') i).trans (by omega))
  have haf : Whole.afterRevenue (Whole.scalarStart s c rs)=finalRegisters (Whole.rowEnd s c rs).1 := by
    simp [Whole.afterRevenue,Whole.afterRank,Whole.afterHeader,Whole.scalarStart,header_effect,finalRegisters]
  simp only [Whole.balanceTriples,List.length_map,List.length_reverse] at hbal
  unfold Whole.remainingCost
  rw [haf]
  simp only [Whole.afterRank,Whole.afterHeader,header_effect,Whole.scalarStart]
  unfold remainingBudget Whole.balanceTriples
  omega

end BalancedAssortments.NPStack.SourceVerifier
