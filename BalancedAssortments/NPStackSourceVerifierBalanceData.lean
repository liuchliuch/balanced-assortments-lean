import BalancedAssortments.NPStackSourceVerifierTraceSemantics

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

def witnessBalanceFields (x : WitnessRecord) : List (List Bool) := [[x.active],x.numerator.1,x.numerator.2]

lemma nextBalance_exact (s : Registers) (x : WitnessRecord) (balance : List Bool) :
    nextBalance s x balance=NPStackFields.dataFields (witnessBalanceFields x)++balance := by
  have hn : nextRegisters s x .numerator=x.numerator := by
    rw [nextRegisters,rowEffect_readonly _ .numerator (by simp)];rfl
  simp only [nextBalance,balanceRecord,hn,witnessBalanceFields]

lemma trace_balance (rows : List InputRow) (s : Registers) (balance : List Bool) :
    (traceEnd rows s balance).2=
      NPStackFields.dataFields (rows.reverse.flatMap (fun r=>witnessBalanceFields r.1))++balance := by
  induction rows generalizing s balance with
  | nil => simp [traceEnd,NPStackFields.dataFields]
  | cons r rows ih =>
    simp only [traceEnd,ih,nextBalance_exact,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    simp [NPStackFields.dataFields,List.flatMap_append,List.append_assoc]

lemma RowsValid_local (rows : List InputRow) (s : Registers) (hv : RowsValid rows s)
    (hz : s .zero=zzero) :
    ∀ r∈rows,recordLegal r.1=true ∧ checkBasic (s .q) r.1=true := by
  induction rows generalizing s with
  | nil => simp
  | cons r rows ih =>
    rcases hv with ⟨hm,ha,hrest⟩
    have hh := VerifierCommands.rowCommand_accepts (loadRecord s r.1) r.1 (loadRecord_holds _ _)
      (by simpa [loadRecord] using hz)
    rw [hh] at ha
    have hc : recordLegal r.1=true ∧ checkBasic (s .q) r.1=true := by simpa [loadRecord] using ha
    have htail := ih (nextRegisters s r.1) hrest ((next_readonly s r.1 .zero (by simp)).trans hz)
    intro x hx
    rcases List.mem_cons.mp hx with h|h
    · subst x;exact hc
    · simpa only [next_readonly s r.1 .q (by simp)] using htail x h

lemma RowsValid_of_local (rows : List InputRow) (s : Registers) (hz : s .zero=zzero)
    (hm : ∀ r∈rows,NPStackMask.maskValue r.2=some r.1.active)
    (hc : ∀ r∈rows,recordLegal r.1=true ∧ checkBasic (s .q) r.1=true) : RowsValid rows s := by
  induction rows generalizing s with
  | nil => trivial
  | cons r rows ih =>
    have hh:=hc r (by simp)
    refine ⟨hm r (by simp),?_,?_⟩
    · rw [VerifierCommands.rowCommand_accepts _ _ (loadRecord_holds _ _) (by simpa [loadRecord] using hz)]
      simpa [loadRecord] using hh
    · apply ih (nextRegisters s r.1) ((next_readonly s r.1 .zero (by simp)).trans hz)
      · intro x hx;exact hm x (by simp [hx])
      · intro x hx
        simpa only [next_readonly s r.1 .q (by simp)] using hc x (by simp [hx])

end BalancedAssortments.NPStack.SourceVerifier
