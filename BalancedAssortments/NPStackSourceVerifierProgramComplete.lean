import BalancedAssortments.NPStackSourceVerifierProgramCorrect

namespace BalancedAssortments.NPStack.SourceVerifier.Whole
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl
open NPStackFields (dataFields)

def inputStore (s : Fin 8→List Bool) (c : Fin 2→List Bool) (rs : List NPStackSourcePairing.PairRecord) : SourceVerifier.Stack→List Bool :=
  Header.store (dataFields (List.ofFn s)++NPStackSourcePairing.sourceStream rs)
    (dataFields (List.ofFn c)++NPStackSourcePairing.certificateStream rs) (fun _=>[])

def remainingCost (s : Fin 8→List Bool) (c : Fin 2→List Bool) (rs : List NPStackSourcePairing.PairRecord) : ℕ :=
  Header.headerCost s c +
  budget VerifierCommands.compareTime VerifierCommands.headerCommand (scalarStart s c rs) +
  budget VerifierCommands.compareTime VerifierCommands.rankCommand (afterHeader (scalarStart s c rs)) +
  budget VerifierCommands.compareTime VerifierCommands.revenueCommand (afterRank (scalarStart s c rs)) +
  Balance.loopCost (afterRevenue (scalarStart s c rs)) (balanceTriples rs)+7

/-- Composition preserves the actual first-pass transition count and charges all
header, final-guard, balance-loop, and handoff transitions explicitly. -/
theorem complete_from_trace (s : Fin 8→List Bool) (c : Fin 2→List Bool) (rs : List NPStackSourcePairing.PairRecord)
    {tr : ℕ} (htrace : NPStackSourcePairing.BodyRuns bodyProgram rs
      (workspaceStore (initialRegisters s c) [])
      (workspaceStore (rowEnd s c rs).1 (rowEnd s c rs).2) tr)
    (h₁ : (eval VerifierCommands.headerCommand (scalarStart s c rs)).1=true)
    (h₂ : (eval VerifierCommands.rankCommand (afterHeader (scalarStart s c rs))).1=true)
    (h₃ : (eval VerifierCommands.revenueCommand (afterRank (scalarStart s c rs))).1=true)
    {finish : Registers} (hb : Balance.loopValue (afterRevenue (scalarStart s c rs)) (balanceTriples rs)=some finish) :
    ∃ T ≤ tr+remainingCost s c rs, ∃ out,
      Run concreteProgram T ⟨concreteProgram.start,inputStore s c rs⟩ out ∧ accepts concreteProgram out := by
  let hs := Header.store (NPStackSourcePairing.sourceStream rs) (NPStackSourcePairing.certificateStream rs) (Header.preparedValues s c)
  have hhead : StageRun Header.program id (inputStore s c rs) hs (Header.headerCost s c) := by
    apply stage_mk Header.program id _ _ (Header.header_run s c _ _) (by rfl)
    · intro k; rfl
    · intro k; rfl
    · intro k hk; exact False.elim (hk k rfl)
  have hd := trace_denominators (rs.map decodeRow) (initialRegisters s c) [] rfl rfl
  have hrows : StageRun rowsProgram id hs (globalStore (scalarStart s c rs) (rowEnd s c rs).2) (tr+2) := by
    apply stage_mk rowsProgram id _ _ (NPStackSourcePairing.loop_run bodyProgram htrace) (by rfl)
    · intro k
      exact congrFun (prepared_global_store s c _ _) k
    · intro k
      exact (congrFun (rows_to_globalStore (rowEnd s c rs).1 (rowEnd s c rs).2 hd.1 hd.2) k).symm
    · intro k hk; exact False.elim (hk k rfl)
  obtain ⟨t₁,ht₁,hg₁⟩ := command_stage_complete _ _ (rowEnd s c rs).2 h₁
  obtain ⟨t₂,ht₂,hg₂⟩ := command_stage_complete _ _ (rowEnd s c rs).2 h₂
  obtain ⟨t₃,ht₃,hg₃⟩ := command_stage_complete _ _ (rowEnd s c rs).2 h₃
  obtain ⟨tb,htb,hrb⟩ := Balance.loop_success _ _ _ hb
  have hc : Clean (afterRevenue (scalarStart s c rs)) := by
    apply revenue_clean
    apply rank_clean
    rw [afterHeader,header_state]
    exact cleanRegisters_clean _
  let finalStore := Header.store [] [] (Balance.stable finish [])
  have hbal : StageRun Balance.loopProgram NPStackSourcePairing.Stack.body
      (globalStore (afterRevenue (scalarStart s c rs)) (rowEnd s c rs).2) finalStore tb := by
    apply stage_mk Balance.loopProgram NPStackSourcePairing.Stack.body _ _ hrb (by rfl)
    · intro k
      rw [←saved_balance_stream s c rs]
      exact congrFun (balance_projection _ _ hc) k
    · intro k; rfl
    · intro k hk
      cases k with
      | source => rfl
      | certificate => rfl
      | scratch => rfl
      | body k => exact False.elim (hk k rfl)
  have he : Execution Balance.loopProgram (inputStore s c rs) finalStore
      (Header.headerCost s c+(tr+2)+t₁+t₂+t₃+tb+5) :=
    ⟨hs,_,_,_,_,_,_,_,_,_,_,hhead,hrows,hg₁,hg₂,hg₃,hbal,rfl⟩
  obtain ⟨out,hr,ha,_⟩ := execution_complete Balance.loopProgram he
  refine ⟨_,?_,out,hr,ha⟩
  unfold remainingCost
  omega

/-- The exact finite program accepts every successful semantic execution of the
same raw records, including padded masks and unreduced signed integers. -/
theorem conditions_complete (s : Fin 8→List Bool) (c : Fin 2→List Bool) (rs : List NPStackSourcePairing.PairRecord)
    (hv : RowsValid (rs.map decodeRow) (initialRegisters s c))
    (h₁ : (eval VerifierCommands.headerCommand (scalarStart s c rs)).1=true)
    (h₂ : (eval VerifierCommands.rankCommand (afterHeader (scalarStart s c rs))).1=true)
    (h₃ : (eval VerifierCommands.revenueCommand (afterRank (scalarStart s c rs))).1=true)
    {finish : Registers} (hb : Balance.loopValue (afterRevenue (scalarStart s c rs)) (balanceTriples rs)=some finish) :
    ∃ T out, Run concreteProgram T ⟨concreteProgram.start,inputStore s c rs⟩ out ∧ accepts concreteProgram out := by
  obtain ⟨tr,hr⟩ := trace_run (rs.map decodeRow) (initialRegisters s c) [] rfl rfl hv
  have hm : (rs.map decodeRow).map (fun r=>pairRecord r.1 r.2)=rs := by
    simp only [List.map_map,Function.comp_def,decodeRow,decodeRecord_pair]
    exact List.map_id rs
  rw [hm] at hr
  obtain ⟨T,_,out,hout,ha⟩ := complete_from_trace s c rs hr h₁ h₂ h₃ hb
  exact ⟨T,out,hout,ha⟩

end BalancedAssortments.NPStack.SourceVerifier.Whole
