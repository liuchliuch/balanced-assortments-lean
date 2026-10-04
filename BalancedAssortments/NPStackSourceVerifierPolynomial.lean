import BalancedAssortments.NPStackSourceVerifierRemainingBound
import BalancedAssortments.NPStackSourceVerifierWitness

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier ComplexityTimeSourceParsing VerifierControl

def wholeBudget (n B : ℕ) : ℕ :=
  n*(45*B+32+rowBudget (endWidth n B) B)+remainingBudget n B

lemma wholeBudget_mono_n {n m B : ℕ} (h : n ≤ m) : wholeBudget n B≤wholeBudget m B := by
  unfold wholeBudget remainingBudget rowBudget endWidth scalarBudget rankWidth finalWidth Balance.rowBound
  gcongr <;> unfold rankWidth <;> gcongr

noncomputable def wholePolynomial : Polynomial ℕ :=
  let X : Polynomial ℕ := Polynomial.X
  let W := X+X*(6*X+5)
  let R := Polynomial.C (widthCoefficient VerifierCommands.rankCommand)*(W+1)
  let F := Polynomial.C (widthCoefficient VerifierCommands.revenueCommand)*R
  X*(45*X+32+(Polynomial.C rowCoefficient*(W+1)^2+X+100*(W+6*X+6)))+
    (50*X+43+
      (Polynomial.C (costCoefficient VerifierCommands.headerCommand+costCoefficient VerifierCommands.rankCommand)*(W+1)^2+
        Polynomial.C (costCoefficient VerifierCommands.revenueCommand)*R^2)+
      X*(44*(F+(X+1)+1)+Polynomial.C (costCoefficient (VerifierCommands.balanceCommand false)+
        costCoefficient (VerifierCommands.balanceCommand true))*(3*(F+(X+1))+2)^2))

lemma wholePolynomial_eval (B : ℕ) : wholePolynomial.eval B=wholeBudget B B := by
  simp [wholePolynomial,wholeBudget,rowBudget,endWidth,remainingBudget,scalarBudget,rankWidth,finalWidth,Balance.rowBound]
  left; rfl

theorem conditions_bounded (sh : Fin 8→List Bool) (ch : Fin 2→List Bool)
    (rs : List NPStackSourcePairing.PairRecord) (B : ℕ)
    (hB : 1≤B) (hs : ∀ i,(sh i).length≤B) (hc : ∀ i,(ch i).length≤B)
    (hx : ∀ r∈rs,recordWidth (decodeRecord r)≤B ∧ (r.2 0).length≤B)
    (h : semanticConditions sh ch rs) :
    ∃ T≤wholeBudget rs.length B,∃ out,
      Run Whole.concreteProgram T ⟨Whole.concreteProgram.start,Whole.inputStore sh ch rs⟩ out ∧ accepts Whole.concreteProgram out := by
  have h' : RowsValid (rs.map decodeRow) (Whole.initialRegisters sh ch) ∧
      (eval VerifierCommands.headerCommand (Whole.scalarStart sh ch rs)).1=true ∧
      (eval VerifierCommands.rankCommand (Whole.afterHeader (Whole.scalarStart sh ch rs))).1=true ∧
      (eval VerifierCommands.revenueCommand (Whole.afterRank (Whole.scalarStart sh ch rs))).1=true ∧
      ∃ finish,Balance.loopValue (Whole.afterRevenue (Whole.scalarStart sh ch rs)) (Whole.balanceTriples rs)=some finish := by
    simpa only [semanticConditions,Whole.scalarStart,Whole.rowEnd,Whole.afterHeader,Whole.afterRank,
      Whole.afterRevenue,Whole.balanceTriples,header_effect,finalRegisters] using h
  obtain ⟨hv,h1,h2,h3,finish,hbal⟩:=h'
  have hxs : ∀ r∈rs.map decodeRow,recordWidth r.1≤B ∧ r.2.length≤B := by
    intro r hr;obtain ⟨x,hx',rfl⟩:=List.mem_map.mp hr;exact hx x hx'
  have hb:=trace_bounded (rs.map decodeRow) (Whole.initialRegisters sh ch) [] (A:=B) (B:=B)
    (M:=endWidth rs.length B) (le_refl _) (by simp [endWidth])
    (initial_width sh ch hB hs hc) (by simpa [Whole.initialRegisters,zOne,width] using hB)
    rfl rfl hxs hv
  obtain ⟨tr,htr,htrace⟩:=NPStackSourcePairing.bounded_trace SourceVerifier.bodyProgram _ hb
  have hmap : (rs.map decodeRow).map (fun r=>pairRecord r.1 r.2)=rs := by
    simp only [List.map_map,Function.comp_def,decodeRow,decodeRecord_pair];exact List.map_id rs
  have hov:=overhead_sum_bound (rs.map decodeRow) hxs
  rw [hmap] at htrace htr hov
  simp only [List.length_map] at htr hov
  obtain ⟨T,hT,out,hr,ha⟩:=Whole.complete_from_trace sh ch rs htrace h1 h2 h3 hbal
  have hrem:=remaining_cost_bound sh ch rs B hs hc hB (fun r hr=>(hx r hr).1)
  refine ⟨T,?_,out,hr,ha⟩
  unfold wholeBudget
  nlinarith

end BalancedAssortments.NPStack.SourceVerifier
